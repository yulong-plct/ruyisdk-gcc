/* Code for GIMPLE range related routines.
   Copyright (C) 2019-2023 Free Software Foundation, Inc.
   Contributed by Andrew MacLeod <amacleod@redhat.com>
   and Aldy Hernandez <aldyh@redhat.com>.

This file is part of GCC.

GCC is free software; you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation; either version 3, or (at your option)
any later version.

GCC is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with GCC; see the file COPYING3.  If not see
<http://www.gnu.org/licenses/>.  */

#include "config.h"
#include "system.h"
#include "coretypes.h"
#include "backend.h"
#include "tree.h"
#include "gimple.h"
#include "ssa.h"
#include "gimple-pretty-print.h"
#include "gimple-iterator.h"
#include "tree-cfg.h"
#include "fold-const.h"
#include "tree-cfg.h"
#include "cfgloop.h"
#include "tree-scalar-evolution.h"
#include "gimple-range.h"

gimple_ranger::gimple_ranger ()
{
  // If the cache has a relation oracle, use it.
  m_oracle = m_cache.oracle ();
}

bool
gimple_ranger::range_of_expr (irange &r, tree expr, gimple *stmt)
{
  if (!gimple_range_ssa_p (expr))
    return get_tree_range (r, expr);

  // If there is no statement, just get the global value.
  if (!stmt || is_gimple_debug (stmt))
    {
      if (!m_cache.get_global_range (r, expr))
        r = gimple_range_global (expr);
      return true;
    }

  basic_block bb = gimple_bb (stmt);
  gimple *def_stmt = SSA_NAME_DEF_STMT (expr);

  // If name is defined in this block, try to get an range from S.
  if (def_stmt && gimple_bb (def_stmt) == bb)
    return range_of_stmt (r, def_stmt, expr);

  // Otherwise OP comes from outside this block, use range on entry.
  range_on_entry (r, bb, expr);
  // Check for non-null in the predecessor if dominators are available.
  if (!dom_info_available_p (CDI_DOMINATORS))
    return true;
  basic_block dom_bb = get_immediate_dominator (CDI_DOMINATORS, bb);

  // No range yet, see if there is a dereference in the block.
  // We don't care if it's between the def and a use within a block
  // because the entire block must be executed anyway.
  // FIXME:?? For non-call exceptions we could have a statement throw
  // which causes an early block exit.
  // in which case we may need to walk from S back to the def/top of block
  // to make sure the deref happens between S and there before claiming
  // there is a deref.   Punt for now.
  if (dom_bb && !cfun->can_throw_non_call_exceptions && r.varying_p ()
      && m_cache.m_non_null.non_null_deref_p (expr, dom_bb))
    r = range_nonzero (TREE_TYPE (expr));

  return true;
}

// Return the range of NAME on entry to block BB in R.

void
gimple_ranger::range_on_entry (irange &r, basic_block bb, tree name)
{
  int_range_max entry_range;
  gcc_checking_assert (gimple_range_ssa_p (name));

  // Start with any known range
  range_of_stmt (r, SSA_NAME_DEF_STMT (name), name);

  // Now see if there is any on_entry value which may refine it.
  if (m_cache.block_range (entry_range, bb, name))
    r.intersect (entry_range);
}

// Calculate the range for NAME at the end of block BB and return it in R.
// Return false if no range can be calculated.

void
gimple_ranger::range_on_exit (irange &r, basic_block bb, tree name)
{
  // on-exit from the exit block?
  gcc_checking_assert (bb != EXIT_BLOCK_PTR_FOR_FN (cfun));
  gcc_checking_assert (gimple_range_ssa_p (name));

  gimple *s = last_stmt (bb);
  // If there is no statement in the block and this isn't the entry
  // block, go get the range_on_entry for this block.  For the entry
  // block, a NULL stmt will return the global value for NAME.
  if (!s && bb != ENTRY_BLOCK_PTR_FOR_FN (cfun))
    range_on_entry (r, bb, name);
  else
    range_of_expr (r, name, s);
  gcc_checking_assert (r.undefined_p ()
		       || range_compatible_p (r.type (), TREE_TYPE (name)));
}

// Calculate a range for NAME on edge E and return it in R.

bool
gimple_ranger::range_on_edge (irange &r, edge e, tree name)
{
  int_range_max edge_range;
  gcc_checking_assert (irange::supports_type_p (TREE_TYPE (name)));

  // PHI arguments can be constants, catch these here.
  if (!gimple_range_ssa_p (name))
    return range_of_expr (r, name);

  range_on_exit (r, e->src, name);
  gcc_checking_assert  (r.undefined_p ()
			|| range_compatible_p (r.type(), TREE_TYPE (name)));

  // Check to see if NAME is defined on edge e.
  if (m_cache.outgoing_edge_range_p (edge_range, e, name))
    r.intersect (edge_range);

  return true;
}

// Calculate a range for statement S and return it in R.  If NAME is
// provided it represents the SSA_NAME on the LHS of the statement.
// It is only required if there is more than one lhs/output.  Check
// the global cache for NAME first to see if the evaluation can be
// avoided.  If a range cannot be calculated, return false and UNDEFINED.

bool
gimple_ranger::range_of_stmt (irange &r, gimple *s, tree name)
{
  r.set_undefined ();

  if (!name)
    name = gimple_get_lhs (s);

  // If no name, simply call the base routine.
  if (!name)
    return calc_stmt (r, s, NULL_TREE);

  if (!gimple_range_ssa_p (name))
    return false;

  // Check if the stmt has already been processed, and is not stale.
  if (m_cache.get_non_stale_global_range (r, name))
    return true;

  // Avoid deep recursive call chains.
  prefill_stmt_dependencies (name);

  // Otherwise calculate a new value.
  int_range_max tmp;
  calc_stmt (tmp, s, name);

  // Combine the new value with the old value.  This is required because
  // the way value propagation works, when the IL changes on the fly we
  // can sometimes get different results.  See PR 97741.
  r.intersect (tmp);
  m_cache.set_global_range (name, r);

  // Pointers which resolve to non-zero at the defintion point do not need
  // tracking in the cache as they will never change.  See PR 98866.
  if (POINTER_TYPE_P (TREE_TYPE (name)) && r.nonzero_p ())
    m_cache.set_range_invariant (name);

  return true;
}

// Check if NAME is a dependency that needs resolving, and push it on the
// stack if so.  R is a scratch range.

inline void
gimple_ranger::prefill_name (irange &r, tree name)
{
  if (!gimple_range_ssa_p (name))
    return;
  gimple *stmt = SSA_NAME_DEF_STMT (name);
  if (!range_op_handler (stmt) && !is_a<gphi *> (stmt))
    return;

  // If this op has not been processed yet, then push it on the stack
  if (!m_cache.get_global_range (r, name))
    {
      // Set as current.
      m_cache.get_non_stale_global_range (r, name);
      m_stmt_list.safe_push (name);
    }
}

// This routine will seed the global cache with most of the depnedencies of
// NAME.  This prevents excessive call depth through the normal API.

void
gimple_ranger::prefill_stmt_dependencies (tree ssa)
{
  if (SSA_NAME_IS_DEFAULT_DEF (ssa))
    return;

  int_range_max r;
  gimple *stmt = SSA_NAME_DEF_STMT (ssa);
  gcc_checking_assert (stmt && gimple_bb (stmt));

  // Only pre-process range-ops and phis.
  if (!range_op_handler (stmt) && !is_a<gphi *> (stmt))
    return;

  // Mark where on the stack we are starting.
  unsigned start = m_stmt_list.length ();
  m_stmt_list.safe_push (ssa);

  if (dump_file && (param_evrp_mode & EVRP_MODE_TRACE))
    {
      fprintf (dump_file, "Range_of_stmt dependence fill starting at");
      print_gimple_stmt (dump_file, stmt, 0, TDF_SLIM);
    }

  // Loop until back at the start point.
  while (m_stmt_list.length () > start)
    {
      tree name = m_stmt_list.last ();
      // NULL is a marker which indicates the next name in the stack has now
      // been fully resolved, so we can fold it.
      if (!name)
	{
	  // Pop the NULL, then pop the name.
	  m_stmt_list.pop ();
	  name = m_stmt_list.pop ();
	  // Don't fold initial request, it will be calculated upon return.
	  if (m_stmt_list.length () > start)
	    {
	      // Fold and save the value for NAME.
	      stmt = SSA_NAME_DEF_STMT (name);
	      calc_stmt (r, stmt, name);
	      m_cache.set_global_range (name, r);
	    }
	  continue;
	}

      // Add marker indicating previous NAME in list should be folded
      // when we get to this NULL.
      m_stmt_list.safe_push (NULL_TREE);
      stmt = SSA_NAME_DEF_STMT (name);

      if (dump_file && (param_evrp_mode & EVRP_MODE_TRACE))
	{
	  fprintf(dump_file, "   ROS dep fill (");
	  print_generic_expr (dump_file, name, TDF_SLIM);
	  fputs (") at stmt ", dump_file);
	  print_gimple_stmt (dump_file, stmt, 0, TDF_SLIM);
	}

      gphi *phi = dyn_cast <gphi *> (stmt);
      if (phi)
	{
	  for (unsigned x = 0; x < gimple_phi_num_args (phi); x++)
	    prefill_name (r, gimple_phi_arg_def (phi, x));
	}
      else
	{
	  gcc_checking_assert (range_op_handler (stmt));
	  tree op = gimple_range_operand2 (stmt);
	  if (op)
	    prefill_name (r, op);
	  op = gimple_range_operand1 (stmt);
	  if (op)
	    prefill_name (r, op);
	}
    }
  if (dump_file && (param_evrp_mode & EVRP_MODE_TRACE))
    fprintf (dump_file, "END range_of_stmt dependence fill\n");
}

// This routine will export whatever global ranges are known to GCC
// SSA_RANGE_NAME_INFO fields.

void
gimple_ranger::export_global_ranges ()
{
  unsigned x;
  int_range_max r;
  if (dump_file)
    {
      fprintf (dump_file, "Exported global range table\n");
      fprintf (dump_file, "===========================\n");
    }

  for ( x = 1; x < num_ssa_names; x++)
    {
      tree name = ssa_name (x);
      if (name && !SSA_NAME_IN_FREE_LIST (name)
	  && gimple_range_ssa_p (name)
	  && m_cache.get_global_range (r, name)
	  && !r.varying_p())
	{
	  // Make sure the new range is a subset of the old range.
	  int_range_max old_range;
	  old_range = gimple_range_global (name);
	  old_range.intersect (r);
	  /* Disable this while we fix tree-ssa/pr61743-2.c.  */
	  //gcc_checking_assert (old_range == r);

	  // WTF? Can't write non-null pointer ranges?? stupid set_range_info!
	  if (!POINTER_TYPE_P (TREE_TYPE (name)) && !r.undefined_p ())
	    {
	      value_range vr = r;
	      set_range_info (name, vr);
	      if (dump_file)
		{
		  print_generic_expr (dump_file, name , TDF_SLIM);
		  fprintf (dump_file, " --> ");
		  vr.dump (dump_file);
		  fprintf (dump_file, "\n");
		  fprintf (dump_file, "         irange : ");
		  r.dump (dump_file);
		  fprintf (dump_file, "\n");
		}
	    }
	}
    }
}

// Print the known table values to file F.

void
gimple_ranger::dump (FILE *f)
{
  basic_block bb;

  FOR_EACH_BB_FN (bb, cfun)
    {
      unsigned x;
      edge_iterator ei;
      edge e;
      int_range_max range;
      fprintf (f, "\n=========== BB %d ============\n", bb->index);
      m_cache.dump (f, bb);

      dump_bb (f, bb, 4, TDF_NONE);

      // Now find any globals defined in this block.
      for (x = 1; x < num_ssa_names; x++)
	{
	  tree name = ssa_name (x);
	  if (gimple_range_ssa_p (name) && SSA_NAME_DEF_STMT (name) &&
	      gimple_bb (SSA_NAME_DEF_STMT (name)) == bb &&
	      m_cache.get_global_range (range, name))
	    {
	      if (!range.varying_p ())
	       {
		 print_generic_expr (f, name, TDF_SLIM);
		 fprintf (f, " : ");
		 range.dump (f);
		 fprintf (f, "\n");
	       }

	    }
	}

      // And now outgoing edges, if they define anything.
      FOR_EACH_EDGE (e, ei, bb->succs)
	{
	  for (x = 1; x < num_ssa_names; x++)
	    {
	      tree name = gimple_range_ssa_p (ssa_name (x));
	      if (name && m_cache.outgoing_edge_range_p (range, e, name))
		{
		  gimple *s = SSA_NAME_DEF_STMT (name);
		  // Only print the range if this is the def block, or
		  // the on entry cache for either end of the edge is
		  // set.
		  if ((s && bb == gimple_bb (s)) ||
		      m_cache.block_range (range, bb, name, false) ||
		      m_cache.block_range (range, e->dest, name, false))
		    {
		      range_on_edge (range, e, name);
		      if (!range.varying_p ())
			{
			  fprintf (f, "%d->%d ", e->src->index,
				   e->dest->index);
			  char c = ' ';
			  if (e->flags & EDGE_TRUE_VALUE)
			    fprintf (f, " (T)%c", c);
			  else if (e->flags & EDGE_FALSE_VALUE)
			    fprintf (f, " (F)%c", c);
			  else
			    fprintf (f, "     ");
			  print_generic_expr (f, name, TDF_SLIM);
			  fprintf(f, " : \t");
			  range.dump(f);
			  fprintf (f, "\n");
			}
		    }
		}
	    }
	}
    }

  m_cache.dump (dump_file, (dump_flags & TDF_DETAILS) != 0);
}

// trace_ranger implementation.


trace_ranger::trace_ranger ()
{
  indent = 0;
  trace_count = 0;
}

// If dumping, return true and print the prefix for the next output line.

bool
trace_ranger::dumping (unsigned counter, bool trailing)
{
  if (dump_file && (dump_flags & TDF_DETAILS))
    {
      // Print counter index as well as INDENT spaces.
      if (!trailing)
	fprintf (dump_file, " %-7u ", counter);
      else
	fprintf (dump_file, "         ");
      unsigned x;
      for (x = 0; x< indent; x++)
	fputc (' ', dump_file);
      return true;
    }
  return false;
}

// After calling a routine, if dumping, print the CALLER, NAME, and RESULT,
// returning RESULT.

bool
trace_ranger::trailer (unsigned counter, const char *caller, bool result,
		       tree name, const irange &r)
{
  if (dumping (counter, true))
    {
      indent -= bump;
      fputs(result ? "TRUE : " : "FALSE : ", dump_file);
      fprintf (dump_file, "(%u) ", counter);
      fputs (caller, dump_file);
      fputs (" (",dump_file);
      if (name)
	print_generic_expr (dump_file, name, TDF_SLIM);
      fputs (") ",dump_file);
      if (result)
	{
	  r.dump (dump_file);
	  fputc('\n', dump_file);
	}
      else
	fputc('\n', dump_file);
      // Marks the end of a request.
      if (indent == 0)
	fputc('\n', dump_file);
    }
  return result;
}

// Tracing version of range_on_edge.  Call it with printing wrappers.

bool
trace_ranger::range_on_edge (irange &r, edge e, tree name)
{
  unsigned idx = ++trace_count;
  if (dumping (idx))
    {
      fprintf (dump_file, "range_on_edge (");
      print_generic_expr (dump_file, name, TDF_SLIM);
      fprintf (dump_file, ") on edge %d->%d\n", e->src->index, e->dest->index);
      indent += bump;
    }

  bool res = gimple_ranger::range_on_edge (r, e, name);
  trailer (idx, "range_on_edge", true, name, r);
  return res;
}

// Tracing version of range_on_entry.  Call it with printing wrappers.

void
trace_ranger::range_on_entry (irange &r, basic_block bb, tree name)
{
  unsigned idx = ++trace_count;
  if (dumping (idx))
    {
      fprintf (dump_file, "range_on_entry (");
      print_generic_expr (dump_file, name, TDF_SLIM);
      fprintf (dump_file, ") to BB %d\n", bb->index);
      indent += bump;
    }

  gimple_ranger::range_on_entry (r, bb, name);

  trailer (idx, "range_on_entry", true, name, r);
}

// Tracing version of range_on_exit.  Call it with printing wrappers.

void
trace_ranger::range_on_exit (irange &r, basic_block bb, tree name)
{
  unsigned idx = ++trace_count;
  if (dumping (idx))
    {
      fprintf (dump_file, "range_on_exit (");
      print_generic_expr (dump_file, name, TDF_SLIM);
      fprintf (dump_file, ") from BB %d\n", bb->index);
      indent += bump;
    }

  gimple_ranger::range_on_exit (r, bb, name);

  trailer (idx, "range_on_exit", true, name, r);
}

// Tracing version of range_of_stmt.  Call it with printing wrappers.

bool
trace_ranger::range_of_stmt (irange &r, gimple *s, tree name)
{
  bool res;
  unsigned idx = ++trace_count;
  if (dumping (idx))
    {
      fprintf (dump_file, "range_of_stmt (");
      if (name)
	print_generic_expr (dump_file, name, TDF_SLIM);
      fputs (") at stmt ", dump_file);
      print_gimple_stmt (dump_file, s, 0, TDF_SLIM);
      indent += bump;
    }

  res = gimple_ranger::range_of_stmt (r, s, name);

  return trailer (idx, "range_of_stmt", res, name, r);
}

// Tracing version of range_of_expr.  Call it with printing wrappers.

bool
trace_ranger::range_of_expr (irange &r, tree name, gimple *s)
{
  bool res;
  unsigned idx = ++trace_count;
  if (dumping (idx))
    {
      fprintf (dump_file, "range_of_expr(");
      print_generic_expr (dump_file, name, TDF_SLIM);
      fputs (")", dump_file);
      if (s)
	{
	  fputs (" at stmt ", dump_file);
	  print_gimple_stmt (dump_file, s, 0, TDF_SLIM);
	}
      else
	fputs ("\n", dump_file);
      indent += bump;
    }

  res = gimple_ranger::range_of_expr (r, name, s);

  return trailer (idx, "range_of_expr", res, name, r);
}
