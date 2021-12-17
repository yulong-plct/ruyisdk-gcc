/* Statement Analysis and Transformation for Vectorization
   Copyright (C) 2003-2023 Free Software Foundation, Inc.
   Contributed by Dorit Naishlos <dorit@il.ibm.com>
   and Ira Rosen <irar@il.ibm.com>

This file is part of GCC.

GCC is free software; you can redistribute it and/or modify it under
the terms of the GNU General Public License as published by the Free
Software Foundation; either version 3, or (at your option) any later
version.

GCC is distributed in the hope that it will be useful, but WITHOUT ANY
WARRANTY; without even the implied warranty of MERCHANTABILITY or
FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
for more details.

You should have received a copy of the GNU General Public License
along with GCC; see the file COPYING3.  If not see
<http://www.gnu.org/licenses/>.  */

#include "config.h"
#include "system.h"
#include "coretypes.h"
#include "backend.h"
#include "target.h"
#include "rtl.h"
#include "tree.h"
#include "gimple.h"
#include "ssa.h"
#include "optabs-tree.h"
#include "insn-config.h"
#include "recog.h"		/* FIXME: for insn_data */
#include "cgraph.h"
#include "dumpfile.h"
#include "alias.h"
#include "fold-const.h"
#include "stor-layout.h"
#include "tree-eh.h"
#include "gimplify.h"
#include "gimple-iterator.h"
#include "gimplify-me.h"
#include "tree-cfg.h"
#include "tree-ssa-loop-manip.h"
#include "cfgloop.h"
#include "explow.h"
#include "tree-ssa-loop.h"
#include "tree-scalar-evolution.h"
#include "tree-vectorizer.h"
#include "builtins.h"
#include "internal-fn.h"
#include "tree-vector-builder.h"
#include "vec-perm-indices.h"
#include "tree-ssa-loop-niter.h"
#include "gimple-fold.h"
#include "regs.h"
#include "attribs.h"

/* For lang_hooks.types.type_for_mode.  */
#include "langhooks.h"

/* Return the vectorized type for the given statement.  */

tree
stmt_vectype (class _stmt_vec_info *stmt_info)
{
  return STMT_VINFO_VECTYPE (stmt_info);
}

/* Return TRUE iff the given statement is in an inner loop relative to
   the loop being vectorized.  */
bool
stmt_in_inner_loop_p (vec_info *vinfo, class _stmt_vec_info *stmt_info)
{
  gimple *stmt = STMT_VINFO_STMT (stmt_info);
  basic_block bb = gimple_bb (stmt);
  loop_vec_info loop_vinfo = dyn_cast <loop_vec_info> (vinfo);
  class loop* loop;

  if (!loop_vinfo)
    return false;

  loop = LOOP_VINFO_LOOP (loop_vinfo);

  return (bb->loop_father == loop->inner);
}

/* Record the cost of a statement, either by directly informing the 
   target model or by saving it in a vector for later processing.
   Return a preliminary estimate of the statement's cost.  */

unsigned
record_stmt_cost (stmt_vector_for_cost *body_cost_vec, int count,
		  enum vect_cost_for_stmt kind, stmt_vec_info stmt_info,
		  tree vectype, int misalign,
		  enum vect_cost_model_location where)
{
  if ((kind == vector_load || kind == unaligned_load)
      && (stmt_info && STMT_VINFO_GATHER_SCATTER_P (stmt_info)))
    kind = vector_gather_load;
  if ((kind == vector_store || kind == unaligned_store)
      && (stmt_info && STMT_VINFO_GATHER_SCATTER_P (stmt_info)))
    kind = vector_scatter_store;

  stmt_info_for_cost si = { count, kind, where, stmt_info, vectype, misalign };
  body_cost_vec->safe_push (si);

  return (unsigned)
      (builtin_vectorization_cost (kind, vectype, misalign) * count);
}

/* Return a variable of type ELEM_TYPE[NELEMS].  */

static tree
create_vector_array (tree elem_type, unsigned HOST_WIDE_INT nelems)
{
  return create_tmp_var (build_array_type_nelts (elem_type, nelems),
			 "vect_array");
}

/* ARRAY is an array of vectors created by create_vector_array.
   Return an SSA_NAME for the vector in index N.  The reference
   is part of the vectorization of STMT_INFO and the vector is associated
   with scalar destination SCALAR_DEST.  */

static tree
read_vector_array (vec_info *vinfo,
		   stmt_vec_info stmt_info, gimple_stmt_iterator *gsi,
		   tree scalar_dest, tree array, unsigned HOST_WIDE_INT n)
{
  tree vect_type, vect, vect_name, array_ref;
  gimple *new_stmt;

  gcc_assert (TREE_CODE (TREE_TYPE (array)) == ARRAY_TYPE);
  vect_type = TREE_TYPE (TREE_TYPE (array));
  vect = vect_create_destination_var (scalar_dest, vect_type);
  array_ref = build4 (ARRAY_REF, vect_type, array,
		      build_int_cst (size_type_node, n),
		      NULL_TREE, NULL_TREE);

  new_stmt = gimple_build_assign (vect, array_ref);
  vect_name = make_ssa_name (vect, new_stmt);
  gimple_assign_set_lhs (new_stmt, vect_name);
  vect_finish_stmt_generation (vinfo, stmt_info, new_stmt, gsi);

  return vect_name;
}

/* ARRAY is an array of vectors created by create_vector_array.
   Emit code to store SSA_NAME VECT in index N of the array.
   The store is part of the vectorization of STMT_INFO.  */

static void
write_vector_array (vec_info *vinfo,
		    stmt_vec_info stmt_info, gimple_stmt_iterator *gsi,
		    tree vect, tree array, unsigned HOST_WIDE_INT n)
{
  tree array_ref;
  gimple *new_stmt;

  array_ref = build4 (ARRAY_REF, TREE_TYPE (vect), array,
		      build_int_cst (size_type_node, n),
		      NULL_TREE, NULL_TREE);

  new_stmt = gimple_build_assign (array_ref, vect);
  vect_finish_stmt_generation (vinfo, stmt_info, new_stmt, gsi);
}

/* PTR is a pointer to an array of type TYPE.  Return a representation
   of *PTR.  The memory reference replaces those in FIRST_DR
   (and its group).  */

static tree
create_array_ref (tree type, tree ptr, tree alias_ptr_type)
{
  tree mem_ref;

  mem_ref = build2 (MEM_REF, type, ptr, build_int_cst (alias_ptr_type, 0));
  /* Arrays have the same alignment as their type.  */
  set_ptr_info_alignment (get_ptr_info (ptr), TYPE_ALIGN_UNIT (type), 0);
  return mem_ref;
}

/* Add a clobber of variable VAR to the vectorization of STMT_INFO.
   Emit the clobber before *GSI.  */

static void
vect_clobber_variable (vec_info *vinfo, stmt_vec_info stmt_info,
		       gimple_stmt_iterator *gsi, tree var)
{
  tree clobber = build_clobber (TREE_TYPE (var));
  gimple *new_stmt = gimple_build_assign (var, clobber);
  vect_finish_stmt_generation (vinfo, stmt_info, new_stmt, gsi);
}

/* Utility functions used by vect_mark_stmts_to_be_vectorized.  */

/* Function vect_mark_relevant.

   Mark STMT_INFO as "relevant for vectorization" and add it to WORKLIST.  */

static void
vect_mark_relevant (vec<stmt_vec_info> *worklist, stmt_vec_info stmt_info,
		    enum vect_relevant relevant, bool live_p)
{
  enum vect_relevant save_relevant = STMT_VINFO_RELEVANT (stmt_info);
  bool save_live_p = STMT_VINFO_LIVE_P (stmt_info);

  if (dump_enabled_p ())
    dump_printf_loc (MSG_NOTE, vect_location,
		     "mark relevant %d, live %d: %G", relevant, live_p,
		     stmt_info->stmt);

  /* If this stmt is an original stmt in a pattern, we might need to mark its
     related pattern stmt instead of the original stmt.  However, such stmts
     may have their own uses that are not in any pattern, in such cases the
     stmt itself should be marked.  */
  if (STMT_VINFO_IN_PATTERN_P (stmt_info))
    {
      /* This is the last stmt in a sequence that was detected as a
	 pattern that can potentially be vectorized.  Don't mark the stmt
	 as relevant/live because it's not going to be vectorized.
	 Instead mark the pattern-stmt that replaces it.  */

      if (dump_enabled_p ())
	dump_printf_loc (MSG_NOTE, vect_location,
			 "last stmt in pattern. don't mark"
			 " relevant/live.\n");
      stmt_vec_info old_stmt_info = stmt_info;
      stmt_info = STMT_VINFO_RELATED_STMT (stmt_info);
      gcc_assert (STMT_VINFO_RELATED_STMT (stmt_info) == old_stmt_info);
      save_relevant = STMT_VINFO_RELEVANT (stmt_info);
      save_live_p = STMT_VINFO_LIVE_P (stmt_info);
    }

  STMT_VINFO_LIVE_P (stmt_info) |= live_p;
  if (relevant > STMT_VINFO_RELEVANT (stmt_info))
    STMT_VINFO_RELEVANT (stmt_info) = relevant;

  if (STMT_VINFO_RELEVANT (stmt_info) == save_relevant
      && STMT_VINFO_LIVE_P (stmt_info) == save_live_p)
    {
      if (dump_enabled_p ())
        dump_printf_loc (MSG_NOTE, vect_location,
                         "already marked relevant/live.\n");
      return;
    }

  worklist->safe_push (stmt_info);
}


/* Function is_simple_and_all_uses_invariant

   Return true if STMT_INFO is simple and all uses of it are invariant.  */

bool
is_simple_and_all_uses_invariant (stmt_vec_info stmt_info,
				  loop_vec_info loop_vinfo)
{
  tree op;
  ssa_op_iter iter;

  gassign *stmt = dyn_cast <gassign *> (stmt_info->stmt);
  if (!stmt)
    return false;

  FOR_EACH_SSA_TREE_OPERAND (op, stmt, iter, SSA_OP_USE)
    {
      enum vect_def_type dt = vect_uninitialized_def;

      if (!vect_is_simple_use (op, loop_vinfo, &dt))
	{
	  if (dump_enabled_p ())
	    dump_printf_loc (MSG_MISSED_OPTIMIZATION, vect_location,
			     "use not simple.\n");
	  return false;
	}

      if (dt != vect_external_def && dt != vect_constant_def)
	return false;
    }
  return true;
}

/* Function vect_stmt_relevant_p.

   Return true if STMT_INFO, in the loop that is represented by LOOP_VINFO,
   is "relevant for vectorization".

   A stmt is considered "relevant for vectorization" if:
   - it has uses outside the loop.
   - it has vdefs (it alters memory).
   - control stmts in the loop (except for the exit condition).

   CHECKME: what other side effects would the vectorizer allow?  */

static bool
vect_stmt_relevant_p (stmt_vec_info stmt_info, loop_vec_info loop_vinfo,
		      enum vect_relevant *relevant, bool *live_p)
{
  class loop *loop = LOOP_VINFO_LOOP (loop_vinfo);
  ssa_op_iter op_iter;
  imm_use_iterator imm_iter;
  use_operand_p use_p;
  def_operand_p def_p;

  *relevant = vect_unused_in_scope;
  *live_p = false;

  /* cond stmt other than loop exit cond.  */
  if (is_ctrl_stmt (stmt_info->stmt)
      && STMT_VINFO_TYPE (stmt_info) != loop_exit_ctrl_vec_info_type)
    *relevant = vect_used_in_scope;

  /* changing memory.  */
  if (gimple_code (stmt_info->stmt) != GIMPLE_PHI)
    if (gimple_vdef (stmt_info->stmt)
	&& !gimple_clobber_p (stmt_info->stmt))
      {
	if (dump_enabled_p ())
	  dump_printf_loc (MSG_NOTE, vect_location,
                           "vec_stmt_relevant_p: stmt has vdefs.\n");
	*relevant = vect_used_in_scope;
      }

  /* uses outside the loop.  */
  FOR_EACH_PHI_OR_STMT_DEF (def_p, stmt_info->stmt, op_iter, SSA_OP_DEF)
    {
      FOR_EACH_IMM_USE_FAST (use_p, imm_iter, DEF_FROM_PTR (def_p))
	{
	  basic_block bb = gimple_bb (USE_STMT (use_p));
	  if (!flow_bb_inside_loop_p (loop, bb))
	    {
	      if (is_gimple_debug (USE_STMT (use_p)))
		continue;

	      if (dump_enabled_p ())
		dump_printf_loc (MSG_NOTE, vect_location,
                                 "vec_stmt_relevant_p: used out of loop.\n");

	      /* We expect all such uses to be in the loop exit phis
		 (because of loop closed form)   */
	      gcc_assert (gimple_code (USE_STMT (use_p)) == GIMPLE_PHI);
	      gcc_assert (bb == single_exit (loop)->dest);

              *live_p = true;
	    }
	}
    }

  if (*live_p && *relevant == vect_unused_in_scope
      && !is_simple_and_all_uses_invariant (stmt_info, loop_vinfo))
    {
      if (dump_enabled_p ())
	dump_printf_loc (MSG_NOTE, vect_location,
			 "vec_stmt_relevant_p: stmt live but not relevant.\n");
      *relevant = vect_used_only_live;
    }

  return (*live_p || *relevant);
}


/* Function exist_non_indexing_operands_for_use_p

   USE is one of the uses attached to STMT_INFO.  Check if USE is
   used in STMT_INFO for anything other than indexing an array.  */

static bool
exist_non_indexing_operands_for_use_p (tree use, stmt_vec_info stmt_info)
{
  tree operand;

  /* USE corresponds to some operand in STMT.  If there is no data
     reference in STMT, then any operand that corresponds to USE
     is not indexing an array.  */
  if (!STMT_VINFO_DATA_REF (stmt_info))
    return true;

  /* STMT has a data_ref. FORNOW this means that its of one of
     the following forms:
     -1- ARRAY_REF = var
     -2- var = ARRAY_REF
     (This should have been verified in analyze_data_refs).

     'var' in the second case corresponds to a def, not a use,
     so USE cannot correspond to any operands that are not used
     for array indexing.

     Therefore, all we need to check is if STMT falls into the
     first case, and whether var corresponds to USE.  */

  gassign *assign = dyn_cast <gassign *> (stmt_info->stmt);
  if (!assign || !gimple_assign_copy_p (assign))
    {
      gcall *call = dyn_cast <gcall *> (stmt_info->stmt);
      if (call && gimple_call_internal_p (call))
	{
	  internal_fn ifn = gimple_call_internal_fn (call);
	  int mask_index = internal_fn_mask_index (ifn);
	  if (mask_index >= 0
	      && use == gimple_call_arg (call, mask_index))
	    return true;
	  int stored_value_index = internal_fn_stored_value_index (ifn);
	  if (stored_value_index >= 0
	      && use == gimple_call_arg (call, stored_value_index))
	    return true;
	  if (internal_gather_scatter_fn_p (ifn)
	      && use == gimple_call_arg (call, 1))
	    return true;
	}
      return false;
    }

  if (TREE_CODE (gimple_assign_lhs (assign)) == SSA_NAME)
    return false;
  operand = gimple_assign_rhs1 (assign);
  if (TREE_CODE (operand) != SSA_NAME)
    return false;

  if (operand == use)
    return true;

  return false;
}


/*
   Function process_use.

   Inputs:
   - a USE in STMT_VINFO in a loop represented by LOOP_VINFO
   - RELEVANT - enum value to be set in the STMT_VINFO of the stmt
     that defined USE.  This is done by calling mark_relevant and passing it
     the WORKLIST (to add DEF_STMT to the WORKLIST in case it is relevant).
   - FORCE is true if exist_non_indexing_operands_for_use_p check shouldn't
     be performed.

   Outputs:
   Generally, LIVE_P and RELEVANT are used to define the liveness and
   relevance info of the DEF_STMT of this USE:
       STMT_VINFO_LIVE_P (DEF_stmt_vinfo) <-- live_p
       STMT_VINFO_RELEVANT (DEF_stmt_vinfo) <-- relevant
   Exceptions:
   - case 1: If USE is used only for address computations (e.g. array indexing),
   which does not need to be directly vectorized, then the liveness/relevance
   of the respective DEF_STMT is left unchanged.
   - case 2: If STMT_VINFO is a reduction phi and DEF_STMT is a reduction stmt,
   we skip DEF_STMT cause it had already been processed.
   - case 3: If DEF_STMT and STMT_VINFO are in different nests, then
   "relevant" will be modified accordingly.

   Return true if everything is as expected. Return false otherwise.  */

static opt_result
process_use (stmt_vec_info stmt_vinfo, tree use, loop_vec_info loop_vinfo,
	     enum vect_relevant relevant, vec<stmt_vec_info> *worklist,
	     bool force)
{
  stmt_vec_info dstmt_vinfo;
  enum vect_def_type dt;

  /* case 1: we are only interested in uses that need to be vectorized.  Uses
     that are used for address computation are not considered relevant.  */
  if (!force && !exist_non_indexing_operands_for_use_p (use, stmt_vinfo))
    return opt_result::success ();

  if (!vect_is_simple_use (use, loop_vinfo, &dt, &dstmt_vinfo))
    return opt_result::failure_at (stmt_vinfo->stmt,
				   "not vectorized:"
				   " unsupported use in stmt.\n");

  if (!dstmt_vinfo)
    return opt_result::success ();

  basic_block def_bb = gimple_bb (dstmt_vinfo->stmt);
  basic_block bb = gimple_bb (stmt_vinfo->stmt);

  /* case 2: A reduction phi (STMT) defined by a reduction stmt (DSTMT_VINFO).
     We have to force the stmt live since the epilogue loop needs it to
     continue computing the reduction.  */
  if (gimple_code (stmt_vinfo->stmt) == GIMPLE_PHI
      && STMT_VINFO_DEF_TYPE (stmt_vinfo) == vect_reduction_def
      && gimple_code (dstmt_vinfo->stmt) != GIMPLE_PHI
      && STMT_VINFO_DEF_TYPE (dstmt_vinfo) == vect_reduction_def
      && bb->loop_father == def_bb->loop_father)
    {
      if (dump_enabled_p ())
	dump_printf_loc (MSG_NOTE, vect_location,
			 "reduc-stmt defining reduc-phi in the same nest.\n");
      vect_mark_relevant (worklist, dstmt_vinfo, relevant, true);
      return opt_result::success ();
    }

  /* case 3a: outer-loop stmt defining an inner-loop stmt:
	outer-loop-header-bb:
		d = dstmt_vinfo
	inner-loop:
		stmt # use (d)
	outer-loop-tail-bb:
		...		  */
  if (flow_loop_nested_p (def_bb->loop_father, bb->loop_father))
    {
      if (dump_enabled_p ())
	dump_printf_loc (MSG_NOTE, vect_location,
                         "outer-loop def-stmt defining inner-loop stmt.\n");

      switch (relevant)
	{
	case vect_unused_in_scope:
	  relevant = (STMT_VINFO_DEF_TYPE (stmt_vinfo) == vect_nested_cycle) ?
		      vect_used_in_scope : vect_unused_in_scope;
	  break;

	case vect_used_in_outer_by_reduction:
          gcc_assert (STMT_VINFO_DEF_TYPE (stmt_vinfo) != vect_reduction_def);
	  relevant = vect_used_by_reduction;
	  break;

	case vect_used_in_outer:
          gcc_assert (STMT_VINFO_DEF_TYPE (stmt_vinfo) != vect_reduction_def);
	  relevant = vect_used_in_scope;
	  break;

	case vect_used_in_scope:
	  break;

	default:
	  gcc_unreachable ();
	}
    }

  /* case 3b: inner-loop stmt defining an outer-loop stmt:
	outer-loop-header-bb:
		...
	inner-loop:
		d = dstmt_vinfo
	outer-loop-tail-bb (or outer-loop-exit-bb in double reduction):
		stmt # use (d)		*/
  else if (flow_loop_nested_p (bb->loop_father, def_bb->loop_father))
    {
      if (dump_enabled_p ())
	dump_printf_loc (MSG_NOTE, vect_location,
                         "inner-loop def-stmt defining outer-loop stmt.\n");

      switch (relevant)
        {
        case vect_unused_in_scope:
          relevant = (STMT_VINFO_DEF_TYPE (stmt_vinfo) == vect_reduction_def
            || STMT_VINFO_DEF_TYPE (stmt_vinfo) == vect_double_reduction_def) ?
                      vect_used_in_outer_by_reduction : vect_unused_in_scope;
          break;

        case vect_used_by_reduction:
	case vect_used_only_live:
          relevant = vect_used_in_outer_by_reduction;
          break;

        case vect_used_in_scope:
          relevant = vect_used_in_outer;
          break;

        default:
          gcc_unreachable ();
        }
    }
  /* We are also not interested in uses on loop PHI backedges that are
     inductions.  Otherwise we'll needlessly vectorize the IV increment
     and cause hybrid SLP for SLP inductions.  Unless the PHI is live
     of course.  */
  else if (gimple_code (stmt_vinfo->stmt) == GIMPLE_PHI
	   && STMT_VINFO_DEF_TYPE (stmt_vinfo) == vect_induction_def
	   && ! STMT_VINFO_LIVE_P (stmt_vinfo)
	   && (PHI_ARG_DEF_FROM_EDGE (stmt_vinfo->stmt,
				      loop_latch_edge (bb->loop_father))
	       == use))
    {
      if (dump_enabled_p ())
	dump_printf_loc (MSG_NOTE, vect_location,
                         "induction value on backedge.\n");
      return opt_result::success ();
    }


  vect_mark_relevant (worklist, dstmt_vinfo, relevant, false);
  return opt_result::success ();
}


/* Function vect_mark_stmts_to_be_vectorized.

   Not all stmts in the loop need to be vectorized. For example:

     for i...
       for j...
   1.    T0 = i + j
   2.	 T1 = a[T0]

   3.    j = j + 1

   Stmt 1 and 3 do not need to be vectorized, because loop control and
   addressing of vectorized data-refs are handled differently.

   This pass detects such stmts.  */

opt_result
vect_mark_stmts_to_be_vectorized (loop_vec_info loop_vinfo, bool *fatal)
{
  class loop *loop = LOOP_VINFO_LOOP (loop_vinfo);
  basic_block *bbs = LOOP_VINFO_BBS (loop_vinfo);
  unsigned int nbbs = loop->num_nodes;
  gimple_stmt_iterator si;
  unsigned int i;
  basic_block bb;
  bool live_p;
  enum vect_relevant relevant;

  DUMP_VECT_SCOPE ("vect_mark_stmts_to_be_vectorized");

  auto_vec<stmt_vec_info, 64> worklist;

  /* 1. Init worklist.  */
  for (i = 0; i < nbbs; i++)
    {
      bb = bbs[i];
      for (si = gsi_start_phis (bb); !gsi_end_p (si); gsi_next (&si))
	{
	  stmt_vec_info phi_info = loop_vinfo->lookup_stmt (gsi_stmt (si));
	  if (dump_enabled_p ())
	    dump_printf_loc (MSG_NOTE, vect_location, "init: phi relevant? %G",
			     phi_info->stmt);

	  if (vect_stmt_relevant_p (phi_info, loop_vinfo, &relevant, &live_p))
	    vect_mark_relevant (&worklist, phi_info, relevant, live_p);
	}
      for (si = gsi_start_bb (bb); !gsi_end_p (si); gsi_next (&si))
	{
	  if (is_gimple_debug (gsi_stmt (si)))
	    continue;
	  stmt_vec_info stmt_info = loop_vinfo->lookup_stmt (gsi_stmt (si));
	  if (dump_enabled_p ())
	      dump_printf_loc (MSG_NOTE, vect_location,
			       "init: stmt relevant? %G", stmt_info->stmt);

	  if (vect_stmt_relevant_p (stmt_info, loop_vinfo, &relevant, &live_p))
	    vect_mark_relevant (&worklist, stmt_info, relevant, live_p);
	}
    }

  /* 2. Process_worklist */
  while (worklist.length () > 0)
    {
      use_operand_p use_p;
      ssa_op_iter iter;

      stmt_vec_info stmt_vinfo = worklist.pop ();
      if (dump_enabled_p ())
	dump_printf_loc (MSG_NOTE, vect_location,
			 "worklist: examine stmt: %G", stmt_vinfo->stmt);

      /* Examine the USEs of STMT. For each USE, mark the stmt that defines it
	 (DEF_STMT) as relevant/irrelevant according to the relevance property
	 of STMT.  */
      relevant = STMT_VINFO_RELEVANT (stmt_vinfo);

      /* Generally, the relevance property of STMT (in STMT_VINFO_RELEVANT) is
	 propagated as is to the DEF_STMTs of its USEs.

	 One exception is when STMT has been identified as defining a reduction
	 variable; in this case we set the relevance to vect_used_by_reduction.
	 This is because we distinguish between two kinds of relevant stmts -
	 those that are used by a reduction computation, and those that are
	 (also) used by a regular computation.  This allows us later on to
	 identify stmts that are used solely by a reduction, and therefore the
	 order of the results that they produce does not have to be kept.  */

      switch (STMT_VINFO_DEF_TYPE (stmt_vinfo))
        {
          case vect_reduction_def:
	    gcc_assert (relevant != vect_unused_in_scope);
	    if (relevant != vect_unused_in_scope
		&& relevant != vect_used_in_scope
		&& relevant != vect_used_by_reduction
		&& relevant != vect_used_only_live)
	      return opt_result::failure_at
		(stmt_vinfo->stmt, "unsupported use of reduction.\n");
	    break;

          case vect_nested_cycle:
	    if (relevant != vect_unused_in_scope
		&& relevant != vect_used_in_outer_by_reduction
		&& relevant != vect_used_in_outer)
	      return opt_result::failure_at
		(stmt_vinfo->stmt, "unsupported use of nested cycle.\n");
            break;

          case vect_double_reduction_def:
	    if (relevant != vect_unused_in_scope
		&& relevant != vect_used_by_reduction
		&& relevant != vect_used_only_live)
	      return opt_result::failure_at
		(stmt_vinfo->stmt, "unsupported use of double reduction.\n");
            break;

          default:
            break;
        }

      if (is_pattern_stmt_p (stmt_vinfo))
        {
          /* Pattern statements are not inserted into the code, so
             FOR_EACH_PHI_OR_STMT_USE optimizes their operands out, and we
             have to scan the RHS or function arguments instead.  */
	  if (gassign *assign = dyn_cast <gassign *> (stmt_vinfo->stmt))
	    {
	      enum tree_code rhs_code = gimple_assign_rhs_code (assign);
	      tree op = gimple_assign_rhs1 (assign);

	      i = 1;
	      if (rhs_code == COND_EXPR && COMPARISON_CLASS_P (op))
		{
		  opt_result res
		    = process_use (stmt_vinfo, TREE_OPERAND (op, 0),
				   loop_vinfo, relevant, &worklist, false);
		  if (!res)
		    return res;
		  res = process_use (stmt_vinfo, TREE_OPERAND (op, 1),
				     loop_vinfo, relevant, &worklist, false);
		  if (!res)
		    return res;
		  i = 2;
		}
	      for (; i < gimple_num_ops (assign); i++)
		{
		  op = gimple_op (assign, i);
                  if (TREE_CODE (op) == SSA_NAME)
		    {
		      opt_result res
			= process_use (stmt_vinfo, op, loop_vinfo, relevant,
				       &worklist, false);
		      if (!res)
			return res;
		    }
                 }
            }
	  else if (gcall *call = dyn_cast <gcall *> (stmt_vinfo->stmt))
	    {
	      for (i = 0; i < gimple_call_num_args (call); i++)
		{
		  tree arg = gimple_call_arg (call, i);
		  opt_result res
		    = process_use (stmt_vinfo, arg, loop_vinfo, relevant,
				   &worklist, false);
		  if (!res)
		    return res;
		}
	    }
        }
      else
	FOR_EACH_PHI_OR_STMT_USE (use_p, stmt_vinfo->stmt, iter, SSA_OP_USE)
          {
            tree op = USE_FROM_PTR (use_p);
	    opt_result res
	      = process_use (stmt_vinfo, op, loop_vinfo, relevant,
			     &worklist, false);
	    if (!res)
	      return res;
          }

      if (STMT_VINFO_GATHER_SCATTER_P (stmt_vinfo))
	{
	  gather_scatter_info gs_info;
	  if (!vect_check_gather_scatter (stmt_vinfo, loop_vinfo, &gs_info))
	    gcc_unreachable ();
	  opt_result res
	    = process_use (stmt_vinfo, gs_info.offset, loop_vinfo, relevant,
			   &worklist, true);
	  if (!res)
	    {
	      if (fatal)
		*fatal = false;
	      return res;
	    }
	}
    } /* while worklist */

  return opt_result::success ();
}

/* Function vect_model_simple_cost.

   Models cost for simple operations, i.e. those that only emit ncopies of a
   single op.  Right now, this does not account for multiple insns that could
   be generated for the single vector op.  We will handle that shortly.  */

static void
vect_model_simple_cost (vec_info *,
			stmt_vec_info stmt_info, int ncopies,
			enum vect_def_type *dt,
			int ndts,
			slp_tree node,
			stmt_vector_for_cost *cost_vec,
			vect_cost_for_stmt kind = vector_stmt)
{
  int inside_cost = 0, prologue_cost = 0;

  gcc_assert (cost_vec != NULL);

  /* ???  Somehow we need to fix this at the callers.  */
  if (node)
    ncopies = SLP_TREE_NUMBER_OF_VEC_STMTS (node);

  if (!node)
    /* Cost the "broadcast" of a scalar operand in to a vector operand.
       Use scalar_to_vec to cost the broadcast, as elsewhere in the vector
       cost model.  */
    for (int i = 0; i < ndts; i++)
      if (dt[i] == vect_constant_def || dt[i] == vect_external_def)
	prologue_cost += record_stmt_cost (cost_vec, 1, scalar_to_vec,
					   stmt_info, 0, vect_prologue);

  /* Pass the inside-of-loop statements to the target-specific cost model.  */
  inside_cost += record_stmt_cost (cost_vec, ncopies, kind,
				   stmt_info, 0, vect_body);

  if (dump_enabled_p ())
    dump_printf_loc (MSG_NOTE, vect_location,
                     "vect_model_simple_cost: inside_cost = %d, "
                     "prologue_cost = %d .\n", inside_cost, prologue_cost);
}


/* Model cost for type demotion and promotion operations.  PWR is
   normally zero for single-step promotions and demotions.  It will be
   one if two-step promotion/demotion is required, and so on.  NCOPIES
   is the number of vector results (and thus number of instructions)
   for the narrowest end of the operation chain.  Each additional
   step doubles the number of instructions required.  */

static void
vect_model_promotion_demotion_cost (stmt_vec_info stmt_info,
				    enum vect_def_type *dt,
				    unsigned int ncopies, int pwr,
				    stmt_vector_for_cost *cost_vec)
{
  int i;
  int inside_cost = 0, prologue_cost = 0;

  for (i = 0; i < pwr + 1; i++)
    {
      inside_cost += record_stmt_cost (cost_vec, ncopies, vec_promote_demote,
				       stmt_info, 0, vect_body);
      ncopies *= 2;
    }

  /* FORNOW: Assuming maximum 2 args per stmts.  */
  for (i = 0; i < 2; i++)
    if (dt[i] == vect_constant_def || dt[i] == vect_external_def)
      prologue_cost += record_stmt_cost (cost_vec, 1, vector_stmt,
					 stmt_info, 0, vect_prologue);

  if (dump_enabled_p ())
    dump_printf_loc (MSG_NOTE, vect_location,
                     "vect_model_promotion_demotion_cost: inside_cost = %d, "
                     "prologue_cost = %d .\n", inside_cost, prologue_cost);
}

/* Returns true if the current function returns DECL.  */

static bool
cfun_returns (tree decl)
{
  edge_iterator ei;
  edge e;
  FOR_EACH_EDGE (e, ei, EXIT_BLOCK_PTR_FOR_FN (cfun)->preds)
    {
      greturn *ret = safe_dyn_cast <greturn *> (last_stmt (e->src));
      if (!ret)
	continue;
      if (gimple_return_retval (ret) == decl)
	return true;
      /* We often end up with an aggregate copy to the result decl,
         handle that case as well.  First skip intermediate clobbers
	 though.  */
      gimple *def = ret;
      do
	{
	  def = SSA_NAME_DEF_STMT (gimple_vuse (def));
	}
      while (gimple_clobber_p (def));
      if (is_a <gassign *> (def)
	  && gimple_assign_lhs (def) == gimple_return_retval (ret)
	  && gimple_assign_rhs1 (def) == decl)
	return true;
    }
  return false;
}

/* Function vect_model_store_cost

   Models cost for stores.  In the case of grouped accesses, one access
   has the overhead of the grouped access attributed to it.  */

static void
vect_model_store_cost (vec_info *vinfo, stmt_vec_info stmt_info, int ncopies,
		       vect_memory_access_type memory_access_type,
		       vec_load_store_type vls_type, slp_tree slp_node,
		       stmt_vector_for_cost *cost_vec)
{
  unsigned int inside_cost = 0, prologue_cost = 0;
  stmt_vec_info first_stmt_info = stmt_info;
  bool grouped_access_p = STMT_VINFO_GROUPED_ACCESS (stmt_info);

  /* ???  Somehow we need to fix this at the callers.  */
  if (slp_node)
    ncopies = SLP_TREE_NUMBER_OF_VEC_STMTS (slp_node);

  if (vls_type == VLS_STORE_INVARIANT)
    {
      if (!slp_node)
	prologue_cost += record_stmt_cost (cost_vec, 1, scalar_to_vec,
					   stmt_info, 0, vect_prologue);
    }

  /* Grouped stores update all elements in the group at once,
     so we want the DR for the first statement.  */
  if (!slp_node && grouped_access_p)
    first_stmt_info = DR_GROUP_FIRST_ELEMENT (stmt_info);

  /* True if we should include any once-per-group costs as well as
     the cost of the statement itself.  For SLP we only get called
     once per group anyhow.  */
  bool first_stmt_p = (first_stmt_info == stmt_info);

  /* We assume that the cost of a single store-lanes instruction is
     equivalent to the cost of DR_GROUP_SIZE separate stores.  If a grouped
     access is instead being provided by a permute-and-store operation,
     include the cost of the permutes.  */
  if (first_stmt_p
      && memory_access_type == VMAT_CONTIGUOUS_PERMUTE)
    {
      /* Uses a high and low interleave or shuffle operations for each
	 needed permute.  */
      int group_size = DR_GROUP_SIZE (first_stmt_info);
      int nstmts = ncopies * ceil_log2 (group_size) * group_size;
      inside_cost = record_stmt_cost (cost_vec, nstmts, vec_perm,
				      stmt_info, 0, vect_body);

      if (dump_enabled_p ())
        dump_printf_loc (MSG_NOTE, vect_location,
                         "vect_model_store_cost: strided group_size = %d .\n",
                         group_size);
    }

  tree vectype = STMT_VINFO_VECTYPE (stmt_info);
  /* Costs of the stores.  */
  if (memory_access_type == VMAT_ELEMENTWISE
      || memory_access_type == VMAT_GATHER_SCATTER)
    {
      /* N scalar stores plus extracting the elements.  */
      unsigned int assumed_nunits = vect_nunits_for_cost (vectype);
      inside_cost += record_stmt_cost (cost_vec,
				       ncopies * assumed_nunits,
				       scalar_store, stmt_info, 0, vect_body);
    }
  else
    vect_get_store_cost (vinfo, stmt_info, ncopies, &inside_cost, cost_vec);

  if (memory_access_type == VMAT_ELEMENTWISE
      || memory_access_type == VMAT_STRIDED_SLP)
    {
      /* N scalar stores plus extracting the elements.  */
      unsigned int assumed_nunits = vect_nunits_for_cost (vectype);
      inside_cost += record_stmt_cost (cost_vec,
				       ncopies * assumed_nunits,
				       vec_to_scalar, stmt_info, 0, vect_body);
    }

  /* When vectorizing a store into the function result assign
     a penalty if the function returns in a multi-register location.
     In this case we assume we'll end up with having to spill the
     vector result and do piecewise loads as a conservative estimate.  */
  tree base = get_base_address (STMT_VINFO_DATA_REF (stmt_info)->ref);
  if (base
      && (TREE_CODE (base) == RESULT_DECL
	  || (DECL_P (base) && cfun_returns (base)))
      && !aggregate_value_p (base, cfun->decl))
    {
      rtx reg = hard_function_value (TREE_TYPE (base), cfun->decl, 0, 1);
      /* ???  Handle PARALLEL in some way.  */
      if (REG_P (reg))
	{
	  int nregs = hard_regno_nregs (REGNO (reg), GET_MODE (reg));
	  /* Assume that a single reg-reg move is possible and cheap,
	     do not account for vector to gp register move cost.  */
	  if (nregs > 1)
	    {
	      /* Spill.  */
	      prologue_cost += record_stmt_cost (cost_vec, ncopies,
						 vector_store,
						 stmt_info, 0, vect_epilogue);
	      /* Loads.  */
	      prologue_cost += record_stmt_cost (cost_vec, ncopies * nregs,
						 scalar_load,
						 stmt_info, 0, vect_epilogue);
	    }
	}
    }

  if (dump_enabled_p ())
    dump_printf_loc (MSG_NOTE, vect_location,
                     "vect_model_store_cost: inside_cost = %d, "
                     "prologue_cost = %d .\n", inside_cost, prologue_cost);
}


/* Calculate cost of DR's memory access.  */
void
vect_get_store_cost (vec_info *vinfo, stmt_vec_info stmt_info, int ncopies,
		     unsigned int *inside_cost,
		     stmt_vector_for_cost *body_cost_vec)
{
  dr_vec_info *dr_info = STMT_VINFO_DR_INFO (stmt_info);
  int alignment_support_scheme
    = vect_supportable_dr_alignment (vinfo, dr_info, false);

  switch (alignment_support_scheme)
    {
    case dr_aligned:
      {
	*inside_cost += record_stmt_cost (body_cost_vec, ncopies,
					  vector_store, stmt_info, 0,
					  vect_body);

        if (dump_enabled_p ())
          dump_printf_loc (MSG_NOTE, vect_location,
                           "vect_model_store_cost: aligned.\n");
        break;
      }

    case dr_unaligned_supported:
      {
        /* Here, we assign an additional cost for the unaligned store.  */
	*inside_cost += record_stmt_cost (body_cost_vec, ncopies,
					  unaligned_store, stmt_info,
					  DR_MISALIGNMENT (dr_info),
					  vect_body);
        if (dump_enabled_p ())
          dump_printf_loc (MSG_NOTE, vect_location,
                           "vect_model_store_cost: unaligned supported by "
                           "hardware.\n");
        break;
      }

    case dr_unaligned_unsupported:
      {
        *inside_cost = VECT_MAX_COST;

        if (dump_enabled_p ())
          dump_printf_loc (MSG_MISSED_OPTIMIZATION, vect_location,
                           "vect_model_store_cost: unsupported access.\n");
        break;
      }

    default:
      gcc_unreachable ();
    }
}


/* Function vect_model_load_cost

   Models cost for loads.  In the case of grouped accesses, one access has
   the overhead of the grouped access attributed to it.  Since unaligned
   accesses are supported for loads, we also account for the costs of the
   access scheme chosen.  */

static void
vect_model_load_cost (vec_info *vinfo,
		      stmt_vec_info stmt_info, unsigned ncopies, poly_uint64 vf,
		      vect_memory_access_type memory_access_type,
		      slp_tree slp_node,
		      stmt_vector_for_cost *cost_vec)
{
  unsigned int inside_cost = 0, prologue_cost = 0;
  bool grouped_access_p = STMT_VINFO_GROUPED_ACCESS (stmt_info);

  gcc_assert (cost_vec);

  /* ???  Somehow we need to fix this at the callers.  */
  if (slp_node)
    ncopies = SLP_TREE_NUMBER_OF_VEC_STMTS (slp_node);

  if (slp_node && SLP_TREE_LOAD_PERMUTATION (slp_node).exists ())
    {
      /* If the load is permuted then the alignment is determined by
	 the first group element not by the first scalar stmt DR.  */
      stmt_vec_info first_stmt_info = DR_GROUP_FIRST_ELEMENT (stmt_info);
      /* Record the cost for the permutation.  */
      unsigned n_perms, n_loads;
      vect_transform_slp_perm_load (vinfo, slp_node, vNULL, NULL,
				    vf, true, &n_perms, &n_loads);
      inside_cost += record_stmt_cost (cost_vec, n_perms, vec_perm,
				       first_stmt_info, 0, vect_body);

      /* And adjust the number of loads performed.  This handles
	 redundancies as well as loads that are later dead.  */
      ncopies = n_loads;
    }

  /* Grouped loads read all elements in the group at once,
     so we want the DR for the first statement.  */
  stmt_vec_info first_stmt_info = stmt_info;
  if (!slp_node && grouped_access_p)
    first_stmt_info = DR_GROUP_FIRST_ELEMENT (stmt_info);

  /* True if we should include any once-per-group costs as well as
     the cost of the statement itself.  For SLP we only get called
     once per group anyhow.  */
  bool first_stmt_p = (first_stmt_info == stmt_info);

  /* An IFN_LOAD_LANES will load all its vector results, regardless of which
     ones we actually need.  Account for the cost of unused results.  */
  if (first_stmt_p && !slp_node && memory_access_type == VMAT_LOAD_STORE_LANES)
    {
      unsigned int gaps = DR_GROUP_SIZE (first_stmt_info);
      stmt_vec_info next_stmt_info = first_stmt_info;
      do
	{
	  gaps -= 1;
	  next_stmt_info = DR_GROUP_NEXT_ELEMENT (next_stmt_info);
	}
      while (next_stmt_info);
      if (gaps)
	{
	  if (dump_enabled_p ())
	    dump_printf_loc (MSG_NOTE, vect_location,
			     "vect_model_load_cost: %d unused vectors.\n",
			     gaps);
	  vect_get_load_cost (vinfo, stmt_info, ncopies * gaps, false,
			      &inside_cost, &prologue_cost,
			      cost_vec, cost_vec, true);
	}
    }

  /* We assume that the cost of a single load-lanes instruction is
     equivalent to the cost of DR_GROUP_SIZE separate loads.  If a grouped
     access is instead being provided by a load-and-permute operation,
     include the cost of the permutes.  */
  if (first_stmt_p
      && memory_access_type == VMAT_CONTIGUOUS_PERMUTE)
    {
      /* Uses an even and odd extract operations or shuffle operations
	 for each needed permute.  */
      int group_size = DR_GROUP_SIZE (first_stmt_info);
      int nstmts = ncopies * ceil_log2 (group_size) * group_size;
      inside_cost += record_stmt_cost (cost_vec, nstmts, vec_perm,
				       stmt_info, 0, vect_body);

      if (dump_enabled_p ())
        dump_printf_loc (MSG_NOTE, vect_location,
                         "vect_model_load_cost: strided group_size = %d .\n",
                         group_size);
    }

  /* The loads themselves.  */
  if (memory_access_type == VMAT_ELEMENTWISE
      || memory_access_type == VMAT_GATHER_SCATTER)
    {
      /* N scalar loads plus gathering them into a vector.  */
      tree vectype = STMT_VINFO_VECTYPE (stmt_info);
      unsigned int assumed_nunits = vect_nunits_for_cost (vectype);
      inside_cost += record_stmt_cost (cost_vec,
				       ncopies * assumed_nunits,
				       scalar_load, stmt_info, 0, vect_body);
    }
  else
    vect_get_load_cost (vinfo, stmt_info, ncopies, first_stmt_p,
			&inside_cost, &prologue_cost, 
			cost_vec, cost_vec, true);
  if (memory_access_type == VMAT_ELEMENTWISE
      || memory_access_type == VMAT_STRIDED_SLP)
    inside_cost += record_stmt_cost (cost_vec, ncopies, vec_construct,
				     stmt_info, 0, vect_body);

  if (dump_enabled_p ())
    dump_printf_loc (MSG_NOTE, vect_location,
                     "vect_model_load_cost: inside_cost = %d, "
                     "prologue_cost = %d .\n", inside_cost, prologue_cost);
}


/* Calculate cost of DR's memory access.  */
void
vect_get_load_cost (vec_info *vinfo, stmt_vec_info stmt_info, int ncopies,
		    bool add_realign_cost, unsigned int *inside_cost,
		    unsigned int *prologue_cost,
		    stmt_vector_for_cost *prologue_cost_vec,
		    stmt_vector_for_cost *body_cost_vec,
		    bool record_prologue_costs)
{
  dr_vec_info *dr_info = STMT_VINFO_DR_INFO (stmt_info);
  int alignment_support_scheme
    = vect_supportable_dr_alignment (vinfo, dr_info, false);

  switch (alignment_support_scheme)
    {
    case dr_aligned:
      {
	*inside_cost += record_stmt_cost (body_cost_vec, ncopies, vector_load,
					  stmt_info, 0, vect_body);

        if (dump_enabled_p ())
          dump_printf_loc (MSG_NOTE, vect_location,
                           "vect_model_load_cost: aligned.\n");

        break;
      }
    case dr_unaligned_supported:
      {
        /* Here, we assign an additional cost for the unaligned load.  */
	*inside_cost += record_stmt_cost (body_cost_vec, ncopies,
					  unaligned_load, stmt_info,
					  DR_MISALIGNMENT (dr_info),
					  vect_body);

        if (dump_enabled_p ())
          dump_printf_loc (MSG_NOTE, vect_location,
                           "vect_model_load_cost: unaligned supported by "
                           "hardware.\n");

        break;
      }
    case dr_explicit_realign:
      {
	*inside_cost += record_stmt_cost (body_cost_vec, ncopies * 2,
					  vector_load, stmt_info, 0, vect_body);
	*inside_cost += record_stmt_cost (body_cost_vec, ncopies,
					  vec_perm, stmt_info, 0, vect_body);

        /* FIXME: If the misalignment remains fixed across the iterations of
           the containing loop, the following cost should be added to the
           prologue costs.  */
        if (targetm.vectorize.builtin_mask_for_load)
	  *inside_cost += record_stmt_cost (body_cost_vec, 1, vector_stmt,
					    stmt_info, 0, vect_body);

        if (dump_enabled_p ())
          dump_printf_loc (MSG_NOTE, vect_location,
                           "vect_model_load_cost: explicit realign\n");

        break;
      }
    case dr_explicit_realign_optimized:
      {
        if (dump_enabled_p ())
          dump_printf_loc (MSG_NOTE, vect_location,
                           "vect_model_load_cost: unaligned software "
                           "pipelined.\n");

        /* Unaligned software pipeline has a load of an address, an initial
           load, and possibly a mask operation to "prime" the loop.  However,
           if this is an access in a group of loads, which provide grouped
           access, then the above cost should only be considered for one
           access in the group.  Inside the loop, there is a load op
           and a realignment op.  */

        if (add_realign_cost && record_prologue_costs)
          {
	    *prologue_cost += record_stmt_cost (prologue_cost_vec, 2,
						vector_stmt, stmt_info,
						0, vect_prologue);
            if (targetm.vectorize.builtin_mask_for_load)
	      *prologue_cost += record_stmt_cost (prologue_cost_vec, 1,
						  vector_stmt, stmt_info,
						  0, vect_prologue);
          }

	*inside_cost += record_stmt_cost (body_cost_vec, ncopies, vector_load,
					  stmt_info, 0, vect_body);
	*inside_cost += record_stmt_cost (body_cost_vec, ncopies, vec_perm,
					  stmt_info, 0, vect_body);

        if (dump_enabled_p ())
          dump_printf_loc (MSG_NOTE, vect_location,
                           "vect_model_load_cost: explicit realign optimized"
                           "\n");

        break;
      }

    case dr_unaligned_unsupported:
      {
        *inside_cost = VECT_MAX_COST;

        if (dump_enabled_p ())
          dump_printf_loc (MSG_MISSED_OPTIMIZATION, vect_location,
                           "vect_model_load_cost: unsupported access.\n");
        break;
      }

    default:
      gcc_unreachable ();
    }
}

/* Insert the new stmt NEW_STMT at *GSI or at the appropriate place in
   the loop preheader for the vectorized stmt STMT_VINFO.  */

static void
vect_init_vector_1 (vec_info *vinfo, stmt_vec_info stmt_vinfo, gimple *new_stmt,
		    gimple_stmt_iterator *gsi)
{
  if (gsi)
    vect_finish_stmt_generation (vinfo, stmt_vinfo, new_stmt, gsi);
  else
    vinfo->insert_on_entry (stmt_vinfo, new_stmt);

  if (dump_enabled_p ())
    dump_printf_loc (MSG_NOTE, vect_location,
		     "created new init_stmt: %G", new_stmt);
}

/* Function vect_init_vector.

   Insert a new stmt (INIT_STMT) that initializes a new variable of type
   TYPE with the value VAL.  If TYPE is a vector type and VAL does not have
   vector type a vector with all elements equal to VAL is created first.
   Place the initialization at GSI if it is not NULL.  Otherwise, place the
   initialization at the loop preheader.
   Return the DEF of INIT_STMT.
   It will be used in the vectorization of STMT_INFO.  */

tree
vect_init_vector (vec_info *vinfo, stmt_vec_info stmt_info, tree val, tree type,
		  gimple_stmt_iterator *gsi)
{
  gimple *init_stmt;
  tree new_temp;

  /* We abuse this function to push sth to a SSA name with initial 'val'.  */
  if (! useless_type_conversion_p (type, TREE_TYPE (val)))
    {
      gcc_assert (TREE_CODE (type) == VECTOR_TYPE);
      if (! types_compatible_p (TREE_TYPE (type), TREE_TYPE (val)))
	{
	  /* Scalar boolean value should be transformed into
	     all zeros or all ones value before building a vector.  */
	  if (VECTOR_BOOLEAN_TYPE_P (type))
	    {
	      tree true_val = build_all_ones_cst (TREE_TYPE (type));
	      tree false_val = build_zero_cst (TREE_TYPE (type));

	      if (CONSTANT_CLASS_P (val))
		val = integer_zerop (val) ? false_val : true_val;
	      else
		{
		  new_temp = make_ssa_name (TREE_TYPE (type));
		  init_stmt = gimple_build_assign (new_temp, COND_EXPR,
						   val, true_val, false_val);
		  vect_init_vector_1 (vinfo, stmt_info, init_stmt, gsi);
		  val = new_temp;
		}
	    }
	  else
	    {
	      gimple_seq stmts = NULL;
	      if (! INTEGRAL_TYPE_P (TREE_TYPE (val)))
		val = gimple_build (&stmts, VIEW_CONVERT_EXPR,
				    TREE_TYPE (type), val);
	      else
		/* ???  Condition vectorization expects us to do
		   promotion of invariant/external defs.  */
		val = gimple_convert (&stmts, TREE_TYPE (type), val);
	      for (gimple_stmt_iterator gsi2 = gsi_start (stmts);
		   !gsi_end_p (gsi2); )
		{
		  init_stmt = gsi_stmt (gsi2);
		  gsi_remove (&gsi2, false);
		  vect_init_vector_1 (vinfo, stmt_info, init_stmt, gsi);
		}
	    }
	}
      val = build_vector_from_val (type, val);
    }

  new_temp = vect_get_new_ssa_name (type, vect_simple_var, "cst_");
  init_stmt = gimple_build_assign (new_temp, val);
  vect_init_vector_1 (vinfo, stmt_info, init_stmt, gsi);
  return new_temp;
}


/* Function vect_get_vec_defs_for_operand.

   OP is an operand in STMT_VINFO.  This function returns a vector of
   NCOPIES defs that will be used in the vectorized stmts for STMT_VINFO.

   In the case that OP is an SSA_NAME which is defined in the loop, then
   STMT_VINFO_VEC_STMTS of the defining stmt holds the relevant defs.

   In case OP is an invariant or constant, a new stmt that creates a vector def
   needs to be introduced.  VECTYPE may be used to specify a required type for
   vector invariant.  */

void
vect_get_vec_defs_for_operand (vec_info *vinfo, stmt_vec_info stmt_vinfo,
			       unsigned ncopies,
			       tree op, vec<tree> *vec_oprnds, tree vectype)
{
  gimple *def_stmt;
  enum vect_def_type dt;
  bool is_simple_use;
  loop_vec_info loop_vinfo = dyn_cast <loop_vec_info> (vinfo);

  if (dump_enabled_p ())
    dump_printf_loc (MSG_NOTE, vect_location,
		     "vect_get_vec_defs_for_operand: %T\n", op);

  stmt_vec_info def_stmt_info;
  is_simple_use = vect_is_simple_use (op, loop_vinfo, &dt,
				      &def_stmt_info, &def_stmt);
  gcc_assert (is_simple_use);
  if (def_stmt && dump_enabled_p ())
    dump_printf_loc (MSG_NOTE, vect_location, "  def_stmt =  %G", def_stmt);

  vec_oprnds->create (ncopies);
  if (dt == vect_constant_def || dt == vect_external_def)
    {
      tree stmt_vectype = STMT_VINFO_VECTYPE (stmt_vinfo);
      tree vector_type;

      if (vectype)
	vector_type = vectype;
      else if (VECT_SCALAR_BOOLEAN_TYPE_P (TREE_TYPE (op))
	       && VECTOR_BOOLEAN_TYPE_P (stmt_vectype))
	vector_type = truth_type_for (stmt_vectype);
      else
	vector_type = get_vectype_for_scalar_type (loop_vinfo, TREE_TYPE (op));

      gcc_assert (vector_type);
      tree vop = vect_init_vector (vinfo, stmt_vinfo, op, vector_type, NULL);
      while (ncopies--)
	vec_oprnds->quick_push (vop);
    }
  else
    {
      def_stmt_info = vect_stmt_to_vectorize (def_stmt_info);
      gcc_assert (STMT_VINFO_VEC_STMTS (def_stmt_info).length () == ncopies);
      for (unsigned i = 0; i < ncopies; ++i)
	vec_oprnds->quick_push (gimple_get_lhs
				  (STMT_VINFO_VEC_STMTS (def_stmt_info)[i]));
    }
}


/* Get vectorized definitions for OP0 and OP1.  */

void
vect_get_vec_defs (vec_info *vinfo, stmt_vec_info stmt_info, slp_tree slp_node,
		   unsigned ncopies,
		   tree op0, vec<tree> *vec_oprnds0, tree vectype0,
		   tree op1, vec<tree> *vec_oprnds1, tree vectype1,
		   tree op2, vec<tree> *vec_oprnds2, tree vectype2,
		   tree op3, vec<tree> *vec_oprnds3, tree vectype3)
{
  if (slp_node)
    {
      if (op0)
	vect_get_slp_defs (SLP_TREE_CHILDREN (slp_node)[0], vec_oprnds0);
      if (op1)
	vect_get_slp_defs (SLP_TREE_CHILDREN (slp_node)[1], vec_oprnds1);
      if (op2)
	vect_get_slp_defs (SLP_TREE_CHILDREN (slp_node)[2], vec_oprnds2);
      if (op3)
	vect_get_slp_defs (SLP_TREE_CHILDREN (slp_node)[3], vec_oprnds3);
    }
  else
    {
      if (op0)
	vect_get_vec_defs_for_operand (vinfo, stmt_info, ncopies,
				       op0, vec_oprnds0, vectype0);
      if (op1)
	vect_get_vec_defs_for_operand (vinfo, stmt_info, ncopies,
				       op1, vec_oprnds1, vectype1);
      if (op2)
	vect_get_vec_defs_for_operand (vinfo, stmt_info, ncopies,
				       op2, vec_oprnds2, vectype2);
      if (op3)
	vect_get_vec_defs_for_operand (vinfo, stmt_info, ncopies,
				       op3, vec_oprnds3, vectype3);
    }
}

void
vect_get_vec_defs (vec_info *vinfo, stmt_vec_info stmt_info, slp_tree slp_node,
		   unsigned ncopies,
		   tree op0, vec<tree> *vec_oprnds0,
		   tree op1, vec<tree> *vec_oprnds1,
		   tree op2, vec<tree> *vec_oprnds2,
		   tree op3, vec<tree> *vec_oprnds3)
{
  vect_get_vec_defs (vinfo, stmt_info, slp_node, ncopies,
		     op0, vec_oprnds0, NULL_TREE,
		     op1, vec_oprnds1, NULL_TREE,
		     op2, vec_oprnds2, NULL_TREE,
		     op3, vec_oprnds3, NULL_TREE);
}

/* Helper function called by vect_finish_replace_stmt and
   vect_finish_stmt_generation.  Set the location of the new
   statement and create and return a stmt_vec_info for it.  */

static void
vect_finish_stmt_generation_1 (vec_info *,
			       stmt_vec_info stmt_info, gimple *vec_stmt)
{
  if (dump_enabled_p ())
    dump_printf_loc (MSG_NOTE, vect_location, "add new stmt: %G", vec_stmt);

  if (stmt_info)
    {
      gimple_set_location (vec_stmt, gimple_location (stmt_info->stmt));

      /* While EH edges will generally prevent vectorization, stmt might
	 e.g. be in a must-not-throw region.  Ensure newly created stmts
	 that could throw are part of the same region.  */
      int lp_nr = lookup_stmt_eh_lp (stmt_info->stmt);
      if (lp_nr != 0 && stmt_could_throw_p (cfun, vec_stmt))
	add_stmt_to_eh_lp (vec_stmt, lp_nr);
    }
  else
    gcc_assert (!stmt_could_throw_p (cfun, vec_stmt));
}

/* Replace the scalar statement STMT_INFO with a new vector statement VEC_STMT,
   which sets the same scalar result as STMT_INFO did.  Create and return a
   stmt_vec_info for VEC_STMT.  */

void
vect_finish_replace_stmt (vec_info *vinfo,
			  stmt_vec_info stmt_info, gimple *vec_stmt)
{
  gimple *scalar_stmt = vect_orig_stmt (stmt_info)->stmt;
  gcc_assert (gimple_get_lhs (scalar_stmt) == gimple_get_lhs (vec_stmt));

  gimple_stmt_iterator gsi = gsi_for_stmt (scalar_stmt);
  gsi_replace (&gsi, vec_stmt, true);

  vect_finish_stmt_generation_1 (vinfo, stmt_info, vec_stmt);
}

/* Add VEC_STMT to the vectorized implementation of STMT_INFO and insert it
   before *GSI.  Create and return a stmt_vec_info for VEC_STMT.  */

void
vect_finish_stmt_generation (vec_info *vinfo,
			     stmt_vec_info stmt_info, gimple *vec_stmt,
			     gimple_stmt_iterator *gsi)
{
  gcc_assert (!stmt_info || gimple_code (stmt_info->stmt) != GIMPLE_LABEL);

  if (!gsi_end_p (*gsi)
      && gimple_has_mem_ops (vec_stmt))
    {
      gimple *at_stmt = gsi_stmt (*gsi);
      tree vuse = gimple_vuse (at_stmt);
      if (vuse && TREE_CODE (vuse) == SSA_NAME)
	{
	  tree vdef = gimple_vdef (at_stmt);
	  gimple_set_vuse (vec_stmt, gimple_vuse (at_stmt));
	  gimple_set_modified (vec_stmt, true);
	  /* If we have an SSA vuse and insert a store, update virtual
	     SSA form to avoid triggering the renamer.  Do so only
	     if we can easily see all uses - which is what almost always
	     happens with the way vectorized stmts are inserted.  */
	  if ((vdef && TREE_CODE (vdef) == SSA_NAME)
	      && ((is_gimple_assign (vec_stmt)
		   && !is_gimple_reg (gimple_assign_lhs (vec_stmt)))
		  || (is_gimple_call (vec_stmt)
		      && !(gimple_call_flags (vec_stmt)
			   & (ECF_CONST|ECF_PURE|ECF_NOVOPS)))))
	    {
	      tree new_vdef = copy_ssa_name (vuse, vec_stmt);
	      gimple_set_vdef (vec_stmt, new_vdef);
	      SET_USE (gimple_vuse_op (at_stmt), new_vdef);
	    }
	}
    }
  gsi_insert_before (gsi, vec_stmt, GSI_SAME_STMT);
  vect_finish_stmt_generation_1 (vinfo, stmt_info, vec_stmt);
}

/* We want to vectorize a call to combined function CFN with function
   decl FNDECL, using VECTYPE_OUT as the type of the output and VECTYPE_IN
   as the types of all inputs.  Check whether this is possible using
   an internal function, returning its code if so or IFN_LAST if not.  */

static internal_fn
vectorizable_internal_function (combined_fn cfn, tree fndecl,
				tree vectype_out, tree vectype_in)
{
  internal_fn ifn;
  if (internal_fn_p (cfn))
    ifn = as_internal_fn (cfn);
  else
    ifn = associated_internal_fn (fndecl);
  if (ifn != IFN_LAST && direct_internal_fn_p (ifn))
    {
      const direct_internal_fn_info &info = direct_internal_fn (ifn);
      if (info.vectorizable)
	{
	  tree type0 = (info.type0 < 0 ? vectype_out : vectype_in);
	  tree type1 = (info.type1 < 0 ? vectype_out : vectype_in);
	  if (direct_internal_fn_supported_p (ifn, tree_pair (type0, type1),
					      OPTIMIZE_FOR_SPEED))
	    return ifn;
	}
    }
  return IFN_LAST;
}


static tree permute_vec_elements (vec_info *, tree, tree, tree, stmt_vec_info,
				  gimple_stmt_iterator *);

/* Check whether a load or store statement in the loop described by
   LOOP_VINFO is possible in a loop using partial vectors.  This is
   testing whether the vectorizer pass has the appropriate support,
   as well as whether the target does.

   VLS_TYPE says whether the statement is a load or store and VECTYPE
   is the type of the vector being loaded or stored.  MEMORY_ACCESS_TYPE
   says how the load or store is going to be implemented and GROUP_SIZE
   is the number of load or store statements in the containing group.
   If the access is a gather load or scatter store, GS_INFO describes
   its arguments.  If the load or store is conditional, SCALAR_MASK is the
   condition under which it occurs.

   Clear LOOP_VINFO_CAN_USE_PARTIAL_VECTORS_P if a loop using partial
   vectors is not supported, otherwise record the required rgroup control
   types.  */

static void
check_load_store_for_partial_vectors (loop_vec_info loop_vinfo, tree vectype,
				      vec_load_store_type vls_type,
				      int group_size,
				      vect_memory_access_type
				      memory_access_type,
				      unsigned int ncopies,
				      gather_scatter_info *gs_info,
				      tree scalar_mask)
{
  /* Invariant loads need no special support.  */
  if (memory_access_type == VMAT_INVARIANT)
    return;

  vec_loop_masks *masks = &LOOP_VINFO_MASKS (loop_vinfo);
  machine_mode vecmode = TYPE_MODE (vectype);
  bool is_load = (vls_type == VLS_LOAD);
  if (memory_access_type == VMAT_LOAD_STORE_LANES)
    {
      if (is_load
	  ? !vect_load_lanes_supported (vectype, group_size, true)
	  : !vect_store_lanes_supported (vectype, group_size, true))
	{
	  if (dump_enabled_p ())
	    dump_printf_loc (MSG_MISSED_OPTIMIZATION, vect_location,
			     "can't operate on partial vectors because"
			     " the target doesn't have an appropriate"
			     " load/store-lanes instruction.\n");
	  LOOP_VINFO_CAN_USE_PARTIAL_VECTORS_P (loop_vinfo) = false;
	  return;
	}
      vect_record_loop_mask (loop_vinfo, masks, ncopies, vectype, scalar_mask);
      return;
    }

  if (memory_access_type == VMAT_GATHER_SCATTER)
    {
      internal_fn ifn = (is_load
			 ? IFN_MASK_GATHER_LOAD
			 : IFN_MASK_SCATTER_STORE);
      if (!internal_gather_scatter_fn_supported_p (ifn, vectype,
						   gs_info->memory_type,
						   gs_info->offset_vectype,
						   gs_info->scale))
	{
	  if (dump_enabled_p ())
	    dump_printf_loc (MSG_MISSED_OPTIMIZATION, vect_location,
			     "can't operate on partial vectors because"
			     " the target doesn't have an appropriate"
			     " gather load or scatter store instruction.\n");
	  LOOP_VINFO_CAN_USE_PARTIAL_VECTORS_P (loop_vinfo) = false;
	  return;
	}
      vect_record_loop_mask (loop_vinfo, masks, ncopies, vectype, scalar_mask);
      return;
    }

  if (memory_access_type != VMAT_CONTIGUOUS
      && memory_access_type != VMAT_CONTIGUOUS_PERMUTE)
    {
      /* Element X of the data must come from iteration i * VF + X of the
	 scalar loop.  We need more work to support other mappings.  */
      if (dump_enabled_p ())
	dump_printf_loc (MSG_MISSED_OPTIMIZATION, vect_location,
			 "can't operate on partial vectors because an"
			 " access isn't contiguous.\n");
      LOOP_VINFO_CAN_USE_PARTIAL_VECTORS_P (loop_vinfo) = false;
      return;
    }

  if (!VECTOR_MODE_P (vecmode))
    {
      if (dump_enabled_p ())
	dump_printf_loc (MSG_MISSED_OPTIMIZATION, vect_location,
			 "can't operate on partial vectors when emulating"
			 " vector operations.\n");
      LOOP_VINFO_CAN_USE_PARTIAL_VECTORS_P (loop_vinfo) = false;
      return;
    }

  /* We might load more scalars than we need for permuting SLP loads.
     We checked in get_group_load_store_type that the extra elements
     don't leak into a new vector.  */
  auto get_valid_nvectors = [] (poly_uint64 size, poly_uint64 nunits)
  {
    unsigned int nvectors;
    if (can_div_away_from_zero_p (size, nunits, &nvectors))
      return nvectors;
    gcc_unreachable ();
  };

  poly_uint64 nunits = TYPE_VECTOR_SUBPARTS (vectype);
  poly_uint64 vf = LOOP_VINFO_VECT_FACTOR (loop_vinfo);
  machine_mode mask_mode;
  bool using_partial_vectors_p = false;
  if (targetm.vectorize.get_mask_mode (vecmode).exists (&mask_mode)
      && can_vec_mask_load_store_p (vecmode, mask_mode, is_load))
    {
      unsigned int nvectors = get_valid_nvectors (group_size * vf, nunits);
      vect_record_loop_mask (loop_vinfo, masks, nvectors, vectype, scalar_mask);
      using_partial_vectors_p = true;
    }

  machine_mode vmode;
  if (get_len_load_store_mode (vecmode, is_load).exists (&vmode))
    {
      unsigned int nvectors = get_valid_nvectors (group_size * vf, nunits);
      vec_loop_lens *lens = &LOOP_VINFO_LENS (loop_vinfo);
      unsigned factor = (vecmode == vmode) ? 1 : GET_MODE_UNIT_SIZE (vecmode);
      vect_record_loop_len (loop_vinfo, lens, nvectors, vectype, factor);
      using_partial_vectors_p = true;
    }

  if (!using_partial_vectors_p)
    {
      if (dump_enabled_p ())
	dump_printf_loc (MSG_MISSED_OPTIMIZATION, vect_location,
			 "can't operate on partial vectors because the"
			 " target doesn't have the appropriate partial"
			 " vectorization load or store.\n");
      LOOP_VINFO_CAN_USE_PARTIAL_VECTORS_P (loop_vinfo) = false;
    }
}

/* Return the mask input to a masked load or store.  VEC_MASK is the vectorized
   form of the scalar mask condition and LOOP_MASK, if nonnull, is the mask
   that needs to be applied to all loads and stores in a vectorized loop.
   Return VEC_MASK if LOOP_MASK is null, otherwise return VEC_MASK & LOOP_MASK.

   MASK_TYPE is the type of both masks.  If new statements are needed,
   insert them before GSI.  */

static tree
prepare_load_store_mask (tree mask_type, tree loop_mask, tree vec_mask,
			 gimple_stmt_iterator *gsi)
{
  gcc_assert (useless_type_conversion_p (mask_type, TREE_TYPE (vec_mask)));
  if (!loop_mask)
    return vec_mask;

  gcc_assert (TREE_TYPE (loop_mask) == mask_type);
  tree and_res = make_temp_ssa_name (mask_type, NULL, "vec_mask_and");
  gimple *and_stmt = gimple_build_assign (and_res, BIT_AND_EXPR,
					  vec_mask, loop_mask);
  gsi_insert_before (gsi, and_stmt, GSI_SAME_STMT);
  return and_res;
}

/* Determine whether we can use a gather load or scatter store to vectorize
   strided load or store STMT_INFO by truncating the current offset to a
   smaller width.  We need to be able to construct an offset vector:

     { 0, X, X*2, X*3, ... }

   without loss of precision, where X is STMT_INFO's DR_STEP.

   Return true if this is possible, describing the gather load or scatter
   store in GS_INFO.  MASKED_P is true if the load or store is conditional.  */

static bool
vect_truncate_gather_scatter_offset (stmt_vec_info stmt_info,
				     loop_vec_info loop_vinfo, bool masked_p,
				     gather_scatter_info *gs_info)
{
  dr_vec_info *dr_info = STMT_VINFO_DR_INFO (stmt_info);
  data_reference *dr = dr_info->dr;
  tree step = DR_STEP (dr);
  if (TREE_CODE (step) != INTEGER_CST)
    {
      /* ??? Perhaps we could use range information here?  */
      if (dump_enabled_p ())
	dump_printf_loc (MSG_NOTE, vect_location,
			 "cannot truncate variable step.\n");
      return false;
    }

  /* Get the number of bits in an element.  */
  tree vectype = STMT_VINFO_VECTYPE (stmt_info);
  scalar_mode element_mode = SCALAR_TYPE_MODE (TREE_TYPE (vectype));
  unsigned int element_bits = GET_MODE_BITSIZE (element_mode);

  /* Set COUNT to the upper limit on the number of elements - 1.
     Start with the maximum vectorization factor.  */
  unsigned HOST_WIDE_INT count = vect_max_vf (loop_vinfo) - 1;

  /* Try lowering COUNT to the number of scalar latch iterations.  */
  class loop *loop = LOOP_VINFO_LOOP (loop_vinfo);
  widest_int max_iters;
  if (max_loop_iterations (loop, &max_iters)
      && max_iters < count)
    count = max_iters.to_shwi ();

  /* Try scales of 1 and the element size.  */
  int scales[] = { 1, vect_get_scalar_dr_size (dr_info) };
  wi::overflow_type overflow = wi::OVF_NONE;
  for (int i = 0; i < 2; ++i)
    {
      int scale = scales[i];
      widest_int factor;
      if (!wi::multiple_of_p (wi::to_widest (step), scale, SIGNED, &factor))
	continue;

      /* Determine the minimum precision of (COUNT - 1) * STEP / SCALE.  */
      widest_int range = wi::mul (count, factor, SIGNED, &overflow);
      if (overflow)
	continue;
      signop sign = range >= 0 ? UNSIGNED : SIGNED;
      unsigned int min_offset_bits = wi::min_precision (range, sign);

      /* Find the narrowest viable offset type.  */
      unsigned int offset_bits = 1U << ceil_log2 (min_offset_bits);
      tree offset_type = build_nonstandard_integer_type (offset_bits,
							 sign == UNSIGNED);

      /* See whether the target supports the operation with an offset
	 no narrower than OFFSET_TYPE.  */
      tree memory_type = TREE_TYPE (DR_REF (dr));
      if (!vect_gather_scatter_fn_p (loop_vinfo, DR_IS_READ (dr), masked_p,
				     vectype, memory_type, offset_type, scale,
				     &gs_info->ifn, &gs_info->offset_vectype))
	continue;

      gs_info->decl = NULL_TREE;
      /* Logically the sum of DR_BASE_ADDRESS, DR_INIT and DR_OFFSET,
	 but we don't need to store that here.  */
      gs_info->base = NULL_TREE;
      gs_info->element_type = TREE_TYPE (vectype);
      gs_info->offset = fold_convert (offset_type, step);
      gs_info->offset_dt = vect_constant_def;
      gs_info->scale = scale;
      gs_info->memory_type = memory_type;
      return true;
    }

  if (overflow && dump_enabled_p ())
    dump_printf_loc (MSG_NOTE, vect_location,
		     "truncating gather/scatter offset to %d bits"
		     " might change its value.\n", element_bits);

  return false;
}

/* Return true if we can use gather/scatter internal functions to
   vectorize STMT_INFO, which is a grouped or strided load or store.
   MASKED_P is true if load or store is conditional.  When returning
   true, fill in GS_INFO with the information required to perform the
   operation.  */

static bool
vect_use_strided_gather_scatters_p (stmt_vec_info stmt_info,
				    loop_vec_info loop_vinfo, bool masked_p,
				    gather_scatter_info *gs_info)
{
  if (!vect_check_gather_scatter (stmt_info, loop_vinfo, gs_info)
      || gs_info->decl)
    return vect_truncate_gather_scatter_offset (stmt_info, loop_vinfo,
						masked_p, gs_info);

  tree old_offset_type = TREE_TYPE (gs_info->offset);
  tree new_offset_type = TREE_TYPE (gs_info->offset_vectype);

  gcc_assert (TYPE_PRECISION (new_offset_type)
	      >= TYPE_PRECISION (old_offset_type));
  gs_info->offset = fold_convert (new_offset_type, gs_info->offset);

  if (dump_enabled_p ())
    dump_printf_loc (MSG_NOTE, vect_location,
		     "using gather/scatter for strided/grouped access,"
		     " scale = %d\n", gs_info->scale);

  return true;
}

/* STMT_INFO is a non-strided load or store, meaning that it accesses
   elements with a known constant step.  Return -1 if that step
   is negative, 0 if it is zero, and 1 if it is greater than zero.  */

static int
compare_step_with_zero (vec_info *vinfo, stmt_vec_info stmt_info)
{
  dr_vec_info *dr_info = STMT_VINFO_DR_INFO (stmt_info);
  return tree_int_cst_compare (vect_dr_behavior (vinfo, dr_info)->step,
			       size_zero_node);
}

/* If the target supports a permute mask that reverses the elements in
   a vector of type VECTYPE, return that mask, otherwise return null.  */

static tree
perm_mask_for_reverse (tree vectype)
{
  poly_uint64 nunits = TYPE_VECTOR_SUBPARTS (vectype);

  /* The encoding has a single stepped pattern.  */
  vec_perm_builder sel (nunits, 1, 3);
  for (int i = 0; i < 3; ++i)
    sel.quick_push (nunits - 1 - i);

  vec_perm_indices indices (sel, 1, nunits);
  if (!can_vec_perm_const_p (TYPE_MODE (vectype), TYPE_MODE (vectype),
                            indices))
    return NULL_TREE;
  return vect_gen_perm_mask_checked (vectype, indices);
}

/* A subroutine of get_load_store_type, with a subset of the same
   arguments.  Handle the case where STMT_INFO is a load or store that
   accesses consecutive elements with a negative step.  */

static vect_memory_access_type
get_negative_load_store_type (vec_info *vinfo,
			      stmt_vec_info stmt_info, tree vectype,
			      vec_load_store_type vls_type,
			      unsigned int ncopies)
{
  dr_vec_info *dr_info = STMT_VINFO_DR_INFO (stmt_info);
  dr_alignment_support alignment_support_scheme;

  if (ncopies > 1)
    {
      if (dump_enabled_p ())
	dump_printf_loc (MSG_MISSED_OPTIMIZATION, vect_location,
			 "multiple types with negative step.\n");
      return VMAT_ELEMENTWISE;
    }

  alignment_support_scheme = vect_supportable_dr_alignment (vinfo,
							    dr_info, false);
  if (alignment_support_scheme != dr_aligned
      && alignment_support_scheme != dr_unaligned_supported)
    {
      if (dump_enabled_p ())
	dump_printf_loc (MSG_MISSED_OPTIMIZATION, vect_location,
			 "negative step but alignment required.\n");
      return VMAT_ELEMENTWISE;
    }

  if (vls_type == VLS_STORE_INVARIANT)
    {
      if (dump_enabled_p ())
	dump_printf_loc (MSG_NOTE, vect_location,
			 "negative step with invariant source;"
			 " no permute needed.\n");
      return VMAT_CONTIGUOUS_DOWN;
    }

  if (!perm_mask_for_reverse (vectype))
    {
      if (dump_enabled_p ())
	dump_printf_loc (MSG_MISSED_OPTIMIZATION, vect_location,
			 "negative step and reversing not supported.\n");
      return VMAT_ELEMENTWISE;
    }

  return VMAT_CONTIGUOUS_REVERSE;
}

/* STMT_INFO is either a masked or unconditional store.  Return the value
   being stored.  */

tree
vect_get_store_rhs (stmt_vec_info stmt_info)
{
  if (gassign *assign = dyn_cast <gassign *> (stmt_info->stmt))
    {
      gcc_assert (gimple_assign_single_p (assign));
      return gimple_assign_rhs1 (assign);
    }
  if (gcall *call = dyn_cast <gcall *> (stmt_info->stmt))
    {
      internal_fn ifn = gimple_call_internal_fn (call);
      int index = internal_fn_stored_value_index (ifn);
      gcc_assert (index >= 0);
      return gimple_call_arg (call, index);
    }
  gcc_unreachable ();
}

/* Function VECTOR_VECTOR_COMPOSITION_TYPE

   This function returns a vector type which can be composed with NETLS pieces,
   whose type is recorded in PTYPE.  VTYPE should be a vector type, and has the
   same vector size as the return vector.  It checks target whether supports
   pieces-size vector mode for construction firstly, if target fails to, check
   pieces-size scalar mode for construction further.  It returns NULL_TREE if
   fails to find the available composition.

   For example, for (vtype=V16QI, nelts=4), we can probably get:
     - V16QI with PTYPE V4QI.
     - V4SI with PTYPE SI.
     - NULL_TREE.  */

static tree
vector_vector_composition_type (tree vtype, poly_uint64 nelts, tree *ptype)
{
  gcc_assert (VECTOR_TYPE_P (vtype));
  gcc_assert (known_gt (nelts, 0U));

  machine_mode vmode = TYPE_MODE (vtype);
  if (!VECTOR_MODE_P (vmode))
    return NULL_TREE;

  poly_uint64 vbsize = GET_MODE_BITSIZE (vmode);
  unsigned int pbsize;
  if (constant_multiple_p (vbsize, nelts, &pbsize))
    {
      /* First check if vec_init optab supports construction from
	 vector pieces directly.  */
      scalar_mode elmode = SCALAR_TYPE_MODE (TREE_TYPE (vtype));
      poly_uint64 inelts = pbsize / GET_MODE_BITSIZE (elmode);
      machine_mode rmode;
      if (related_vector_mode (vmode, elmode, inelts).exists (&rmode)
	  && (convert_optab_handler (vec_init_optab, vmode, rmode)
	      != CODE_FOR_nothing))
	{
	  *ptype = build_vector_type (TREE_TYPE (vtype), inelts);
	  return vtype;
	}

      /* Otherwise check if exists an integer type of the same piece size and
	 if vec_init optab supports construction from it directly.  */
      if (int_mode_for_size (pbsize, 0).exists (&elmode)
	  && related_vector_mode (vmode, elmode, nelts).exists (&rmode)
	  && (convert_optab_handler (vec_init_optab, rmode, elmode)
	      != CODE_FOR_nothing))
	{
	  *ptype = build_nonstandard_integer_type (pbsize, 1);
	  return build_vector_type (*ptype, nelts);
	}
    }

  return NULL_TREE;
}

/* A subroutine of get_load_store_type, with a subset of the same
   arguments.  Handle the case where STMT_INFO is part of a grouped load
   or store.

   For stores, the statements in the group are all consecutive
   and there is no gap at the end.  For loads, the statements in the
   group might not be consecutive; there can be gaps between statements
   as well as at the end.  */

static bool
get_group_load_store_type (vec_info *vinfo, stmt_vec_info stmt_info,
			   tree vectype, slp_tree slp_node,
			   bool masked_p, vec_load_store_type vls_type,
			   vect_memory_access_type *memory_access_type,
			   dr_alignment_support *alignment_support_scheme,
			   gather_scatter_info *gs_info)
{
  loop_vec_info loop_vinfo = dyn_cast <loop_vec_info> (vinfo);
  class loop *loop = loop_vinfo ? LOOP_VINFO_LOOP (loop_vinfo) : NULL;
  stmt_vec_info first_stmt_info = DR_GROUP_FIRST_ELEMENT (stmt_info);
  dr_vec_info *first_dr_info = STMT_VINFO_DR_INFO (first_stmt_info);
  unsigned int group_size = DR_GROUP_SIZE (first_stmt_info);
  bool single_element_p = (stmt_info == first_stmt_info
			   && !DR_GROUP_NEXT_ELEMENT (stmt_info));
  unsigned HOST_WIDE_INT gap = DR_GROUP_GAP (first_stmt_info);
  poly_uint64 nunits = TYPE_VECTOR_SUBPARTS (vectype);

  /* True if the vectorized statements would access beyond the last
     statement in the group.  */
  bool overrun_p = false;

  /* True if we can cope with such overrun by peeling for gaps, so that
     there is at least one final scalar iteration after the vector loop.  */
  bool can_overrun_p = (!masked_p
			&& vls_type == VLS_LOAD
			&& loop_vinfo
			&& !loop->inner);

  /* There can only be a gap at the end of the group if the stride is
     known at compile time.  */
  gcc_assert (!STMT_VINFO_STRIDED_P (first_stmt_info) || gap == 0);

  /* Stores can't yet have gaps.  */
  gcc_assert (slp_node || vls_type == VLS_LOAD || gap == 0);

  if (slp_node)
    {
      /* For SLP vectorization we directly vectorize a subchain
	 without permutation.  */
      if (! SLP_TREE_LOAD_PERMUTATION (slp_node).exists ())
	first_dr_info
	  = STMT_VINFO_DR_INFO (SLP_TREE_SCALAR_STMTS (slp_node)[0]);
      if (STMT_VINFO_STRIDED_P (first_stmt_info))
	{
	  /* Try to use consecutive accesses of DR_GROUP_SIZE elements,
	     separated by the stride, until we have a complete vector.
	     Fall back to scalar accesses if that isn't possible.  */
	  if (multiple_p (nunits, group_size))
	    *memory_access_type = VMAT_STRIDED_SLP;
	  else
	    *memory_access_type = VMAT_ELEMENTWISE;
	}
      else
	{
	  overrun_p = loop_vinfo && gap != 0;
	  if (overrun_p && vls_type != VLS_LOAD)
	    {
	      dump_printf_loc (MSG_MISSED_OPTIMIZATION, vect_location,
			       "Grouped store with gaps requires"
			       " non-consecutive accesses\n");
	      return false;
	    }
	  /* An overrun is fine if the trailing elements are smaller
	     than the alignment boundary B.  Every vector access will
	     be a multiple of B and so we are guaranteed to access a
	     non-gap element in the same B-sized block.  */
	  if (overrun_p
	      && gap < (vect_known_alignment_in_bytes (first_dr_info)
			/ vect_get_scalar_dr_size (first_dr_info)))
	    overrun_p = false;

	  /* If the gap splits the vector in half and the target
	     can do half-vector operations avoid the epilogue peeling
	     by simply loading half of the vector only.  Usually
	     the construction with an upper zero half will be elided.  */
	  dr_alignment_support alignment_support_scheme;
	  tree half_vtype;
	  if (overrun_p
	      && !masked_p
	      && (((alignment_support_scheme
		      = vect_supportable_dr_alignment (vinfo,
						       first_dr_info, false)))
		   == dr_aligned
		  || alignment_support_scheme == dr_unaligned_supported)
	      && known_eq (nunits, (group_size - gap) * 2)
	      && known_eq (nunits, group_size)
	      && (vector_vector_composition_type (vectype, 2, &half_vtype)
		  != NULL_TREE))
	    overrun_p = false;

	  if (overrun_p && !can_overrun_p)
	    {
	      if (dump_enabled_p ())
		dump_printf_loc (MSG_MISSED_OPTIMIZATION, vect_location,
				 "Peeling for outer loop is not supported\n");
	      return false;
	    }
	  int cmp = compare_step_with_zero (vinfo, stmt_info);
	  if (cmp < 0)
	    {
	      if (single_element_p)
		/* ???  The VMAT_CONTIGUOUS_REVERSE code generation is
		   only correct for single element "interleaving" SLP.  */
		*memory_access_type = get_negative_load_store_type
				       (vinfo, stmt_info, vectype, vls_type, 1);
	      else
		{
		  /* Try to use consecutive accesses of DR_GROUP_SIZE elements,
		     separated by the stride, until we have a complete vector.
		     Fall back to scalar accesses if that isn't possible.  */
		  if (multiple_p (nunits, group_size))
		    *memory_access_type = VMAT_STRIDED_SLP;
		  else
		    *memory_access_type = VMAT_ELEMENTWISE;
		}
	    }
	  else
	    {
	      gcc_assert (!loop_vinfo || cmp > 0);
	      *memory_access_type = VMAT_CONTIGUOUS;
	    }

	  /* When we have a contiguous access across loop iterations
	     but the access in the loop doesn't cover the full vector
	     we can end up with no gap recorded but still excess
	     elements accessed, see PR103116.  Make sure we peel for
	     gaps if necessary and sufficient and give up if not.  */
	  if (loop_vinfo
	      && *memory_access_type == VMAT_CONTIGUOUS
	      && SLP_TREE_LOAD_PERMUTATION (slp_node).exists ()
	      && !multiple_p (group_size * LOOP_VINFO_VECT_FACTOR (loop_vinfo),
			      nunits))
	    {
	      unsigned HOST_WIDE_INT cnunits, cvf;
	      if (!can_overrun_p
		  || !nunits.is_constant (&cnunits)
		  || !LOOP_VINFO_VECT_FACTOR (loop_vinfo).is_constant (&cvf)
		  /* Peeling for gaps assumes that a single scalar iteration
		     is enough to make sure the last vector iteration doesn't
		     access excess elements.
		     ???  Enhancements include peeling multiple iterations
		     or using masked loads with a static mask.  */
		  || (group_size * cvf) % cnunits + group_size < cnunits)
		{
		  if (dump_enabled_p ())
		    dump_printf_loc (MSG_MISSED_OPTIMIZATION, vect_location,
				     "peeling for gaps insufficient for "
				     "access\n");
		  return false;
		}
	      overrun_p = true;
	    }
	}
    }
  else
    {
      /* We can always handle this case using elementwise accesses,
	 but see if something more efficient is available.  */
      *memory_access_type = VMAT_ELEMENTWISE;

      /* If there is a gap at the end of the group then these optimizations
	 would access excess elements in the last iteration.  */
      bool would_overrun_p = (gap != 0);
      /* An overrun is fine if the trailing elements are smaller than the
	 alignment boundary B.  Every vector access will be a multiple of B
	 and so we are guaranteed to access a non-gap element in the
	 same B-sized block.  */
      if (would_overrun_p
	  && !masked_p
	  && gap < (vect_known_alignment_in_bytes (first_dr_info)
		    / vect_get_scalar_dr_size (first_dr_info)))
	would_overrun_p = false;

      if (!STMT_VINFO_STRIDED_P (first_stmt_info)
	  && (can_overrun_p || !would_overrun_p)
	  && compare_step_with_zero (vinfo, stmt_info) > 0)
	{
	  /* First cope with the degenerate case of a single-element
	     vector.  */
	  if (known_eq (TYPE_VECTOR_SUBPARTS (vectype), 1U))
	    ;

	  /* Otherwise try using LOAD/STORE_LANES.  */
	  else if (vls_type == VLS_LOAD
		   ? vect_load_lanes_supported (vectype, group_size, masked_p)
		   : vect_store_lanes_supported (vectype, group_size,
						 masked_p))
	    {
	      *memory_access_type = VMAT_LOAD_STORE_LANES;
	      overrun_p = would_overrun_p;
	    }

	  /* If that fails, try using permuting loads.  */
	  else if (vls_type == VLS_LOAD
		   ? vect_grouped_load_supported (vectype, single_element_p,
						  group_size)
		   : vect_grouped_store_supported (vectype, group_size))
	    {
	      *memory_access_type = VMAT_CONTIGUOUS_PERMUTE;
	      overrun_p = would_overrun_p;
	    }
	}

      /* As a last resort, trying using a gather load or scatter store.

	 ??? Although the code can handle all group sizes correctly,
	 it probably isn't a win to use separate strided accesses based
	 on nearby locations.  Or, even if it's a win over scalar code,
	 it might not be a win over vectorizing at a lower VF, if that
	 allows us to use contiguous accesses.  */
      if (*memory_access_type == VMAT_ELEMENTWISE
	  && single_element_p
	  && loop_vinfo
	  && vect_use_strided_gather_scatters_p (stmt_info, loop_vinfo,
						 masked_p, gs_info))
	*memory_access_type = VMAT_GATHER_SCATTER;
    }

  if (*memory_access_type == VMAT_GATHER_SCATTER
      || *memory_access_type == VMAT_ELEMENTWISE)
    *alignment_support_scheme = dr_unaligned_supported;
  else
    *alignment_support_scheme
      = vect_supportable_dr_alignment (vinfo, first_dr_info, false);

  if (vls_type != VLS_LOAD && first_stmt_info == stmt_info)
    {
      /* STMT is the leader of the group. Check the operands of all the
	 stmts of the group.  */
      stmt_vec_info next_stmt_info = DR_GROUP_NEXT_ELEMENT (stmt_info);
      while (next_stmt_info)
	{
	  tree op = vect_get_store_rhs (next_stmt_info);
	  enum vect_def_type dt;
	  if (!vect_is_simple_use (op, vinfo, &dt))
	    {
	      if (dump_enabled_p ())
		dump_printf_loc (MSG_MISSED_OPTIMIZATION, vect_location,
				 "use not simple.\n");
	      return false;
	    }
	  next_stmt_info = DR_GROUP_NEXT_ELEMENT (next_stmt_info);
	}
    }

  if (overrun_p)
    {
      gcc_assert (can_overrun_p);
      if (dump_enabled_p ())
	dump_printf_loc (MSG_MISSED_OPTIMIZATION, vect_location,
			 "Data access with gaps requires scalar "
			 "epilogue loop\n");
      LOOP_VINFO_PEELING_FOR_GAPS (loop_vinfo) = true;
    }

  return true;
}

/* Analyze load or store statement STMT_INFO of type VLS_TYPE.  Return true
   if there is a memory access type that the vectorized form can use,
   storing it in *MEMORY_ACCESS_TYPE if so.  If we decide to use gathers
   or scatters, fill in GS_INFO accordingly.  In addition
   *ALIGNMENT_SUPPORT_SCHEME is filled out and false is returned if
   the target does not support the alignment scheme.

   SLP says whether we're performing SLP rather than loop vectorization.
   MASKED_P is true if the statement is conditional on a vectorized mask.
   VECTYPE is the vector type that the vectorized statements will use.
   NCOPIES is the number of vector statements that will be needed.  */

static bool
get_load_store_type (vec_info  *vinfo, stmt_vec_info stmt_info,
		     tree vectype, slp_tree slp_node,
		     bool masked_p, vec_load_store_type vls_type,
		     unsigned int ncopies,
		     vect_memory_access_type *memory_access_type,
		     dr_alignment_support *alignment_support_scheme,
		     gather_scatter_info *gs_info)
{
  loop_vec_info loop_vinfo = dyn_cast <loop_vec_info> (vinfo);
  poly_uint64 nunits = TYPE_VECTOR_SUBPARTS (vectype);
  if (STMT_VINFO_GATHER_SCATTER_P (stmt_info))
    {
      *memory_access_type = VMAT_GATHER_SCATTER;
      if (!vect_check_gather_scatter (stmt_info, loop_vinfo, gs_info))
	gcc_unreachable ();
      else if (!vect_is_simple_use (gs_info->offset, vinfo,
				    &gs_info->offset_dt,
				    &gs_info->offset_vectype))
	{
	  if (dump_enabled_p ())
	    dump_printf_loc (MSG_MISSED_OPTIMIZATION, vect_location,
			     "%s index use not simple.\n",
			     vls_type == VLS_LOAD ? "gather" : "scatter");
	  return false;
	}
      /* Gather-scatter accesses perform only component accesses, alignment
	 is irrelevant for them.  */
      *alignment_support_scheme = dr_unaligned_supported;
    }
  else if (STMT_VINFO_GROUPED_ACCESS (stmt_info))
    {
      if (!get_group_load_store_type (vinfo, stmt_info, vectype, slp_node,
				      masked_p,
				      vls_type, memory_access_type,
				      alignment_support_scheme, gs_info))
	return false;
    }
  else if (STMT_VINFO_STRIDED_P (stmt_info))
    {
      gcc_assert (!slp_node);
      if (loop_vinfo
	  && vect_use_strided_gather_scatters_p (stmt_info, loop_vinfo,
						 masked_p, gs_info))
	*memory_access_type = VMAT_GATHER_SCATTER;
      else
	*memory_access_type = VMAT_ELEMENTWISE;
      /* Alignment is irrelevant here.  */
      *alignment_support_scheme = dr_unaligned_supported;
    }
  else
    {
      int cmp = compare_step_with_zero (vinfo, stmt_info);
      if (cmp == 0)
	{
	  gcc_assert (vls_type == VLS_LOAD);
	  *memory_access_type = VMAT_INVARIANT;
	  /* Invariant accesses perform only component accesses, alignment
	     is irrelevant for them.  */
	  *alignment_support_scheme = dr_unaligned_supported;
	}
      else
	{
	  if (cmp < 0)
	    *memory_access_type = get_negative_load_store_type
	       (vinfo, stmt_info, vectype, vls_type, ncopies);
	  else
	    *memory_access_type = VMAT_CONTIGUOUS;
	  *alignment_support_scheme
	    = vect_supportable_dr_alignment (vinfo,
					     STMT_VINFO_DR_INFO (stmt_info),
					     false);
	}
    }

  if ((*memory_access_type == VMAT_ELEMENTWISE
       || *memory_access_type == VMAT_STRIDED_SLP)
      && !nunits.is_constant ())
    {
      if (dump_enabled_p ())
	dump_printf_loc (MSG_MISSED_OPTIMIZATION, vect_location,
			 "Not using elementwise accesses due to variable "
			 "vectorization factor.\n");
      return false;
    }

  if (*alignment_support_scheme == dr_unaligned_unsupported)
    {
      if (dump_enabled_p ())
	dump_printf_loc (MSG_MISSED_OPTIMIZATION, vect_location,
			 "unsupported unaligned access\n");
      return false;
    }

  /* FIXME: At the moment the cost model seems to underestimate the
     cost of using elementwise accesses.  This check preserves the
     traditional behavior until that can be fixed.  */
  stmt_vec_info first_stmt_info = DR_GROUP_FIRST_ELEMENT (stmt_info);
  if (!first_stmt_info)
    first_stmt_info = stmt_info;
  if (*memory_access_type == VMAT_ELEMENTWISE
      && !STMT_VINFO_STRIDED_P (first_stmt_info)
      && !(stmt_info == DR_GROUP_FIRST_ELEMENT (stmt_info)
	   && !DR_GROUP_NEXT_ELEMENT (stmt_info)
	   && !pow2p_hwi (DR_GROUP_SIZE (stmt_info))))
    {
      if (dump_enabled_p ())
	dump_printf_loc (MSG_MISSED_OPTIMIZATION, vect_location,
			 "not falling back to elementwise accesses\n");
      return false;
    }
  return true;
}

/* Return true if boolean argument MASK is suitable for vectorizing
   conditional operation STMT_INFO.  When returning true, store the type
   of the definition in *MASK_DT_OUT and the type of the vectorized mask
   in *MASK_VECTYPE_OUT.  */

static bool
vect_check_scalar_mask (vec_info *vinfo, stmt_vec_info stmt_info, tree mask,
			vect_def_type *mask_dt_out,
			tree *mask_vectype_out)
{
  if (!VECT_SCALAR_BOOLEAN_TYPE_P (TREE_TYPE (mask)))
    {
      if (dump_enabled_p ())
	dump_printf_loc (MSG_MISSED_OPTIMIZATION, vect_location,
			 "mask argument is not a boolean.\n");
      return false;
    }

  if (TREE_CODE (mask) != SSA_NAME)
    {
      if (dump_enabled_p ())
	dump_printf_loc (MSG_MISSED_OPTIMIZATION, vect_location,
			 "mask argument is not an SSA name.\n");
      return false;
    }

  enum vect_def_type mask_dt;
  tree mask_vectype;
  if (!vect_is_simple_use (mask, vinfo, &mask_dt, &mask_vectype))
    {
      if (dump_enabled_p ())
	dump_printf_loc (MSG_MISSED_OPTIMIZATION, vect_location,
			 "mask use not simple.\n");
      return false;
    }

  tree vectype = STMT_VINFO_VECTYPE (stmt_info);
  if (!mask_vectype)
    mask_vectype = get_mask_type_for_scalar_type (vinfo, TREE_TYPE (vectype));

  if (!mask_vectype || !VECTOR_BOOLEAN_TYPE_P (mask_vectype))
    {
      if (dump_enabled_p ())
	dump_printf_loc (MSG_MISSED_OPTIMIZATION, vect_location,
			 "could not find an appropriate vector mask type.\n");
      return false;
    }

  if (maybe_ne (TYPE_VECTOR_SUBPARTS (mask_vectype),
		TYPE_VECTOR_SUBPARTS (vectype)))
    {
      if (dump_enabled_p ())
	dump_printf_loc (MSG_MISSED_OPTIMIZATION, vect_location,
			 "vector mask type %T"
			 " does not match vector data type %T.\n",
			 mask_vectype, vectype);

      return false;
    }

  *mask_dt_out = mask_dt;
  *mask_vectype_out = mask_vectype;
  return true;
}

/* Return true if stored value RHS is suitable for vectorizing store
   statement STMT_INFO.  When returning true, store the type of the
   definition in *RHS_DT_OUT, the type of the vectorized store value in
   *RHS_VECTYPE_OUT and the type of the store in *VLS_TYPE_OUT.  */

static bool
vect_check_store_rhs (vec_info *vinfo, stmt_vec_info stmt_info,
		      slp_tree slp_node, tree rhs,
		      vect_def_type *rhs_dt_out, tree *rhs_vectype_out,
		      vec_load_store_type *vls_type_out)
{
  /* In the case this is a store from a constant make sure
     native_encode_expr can handle it.  */
  if (CONSTANT_CLASS_P (rhs) && native_encode_expr (rhs, NULL, 64) == 0)
    {
      if (dump_enabled_p ())
	dump_printf_loc (MSG_MISSED_OPTIMIZATION, vect_location,
			 "cannot encode constant as a byte sequence.\n");
      return false;
    }

  enum vect_def_type rhs_dt;
  tree rhs_vectype;
  slp_tree slp_op;
  if (!vect_is_simple_use (vinfo, stmt_info, slp_node, 0,
			   &rhs, &slp_op, &rhs_dt, &rhs_vectype))
    {
      if (dump_enabled_p ())
	dump_printf_loc (MSG_MISSED_OPTIMIZATION, vect_location,
			 "use not simple.\n");
      return false;
    }

  tree vectype = STMT_VINFO_VECTYPE (stmt_info);
  if (rhs_vectype && !useless_type_conversion_p (vectype, rhs_vectype))
    {
      if (dump_enabled_p ())
	dump_printf_loc (MSG_MISSED_OPTIMIZATION, vect_location,
			 "incompatible vector types.\n");
      return false;
    }

  *rhs_dt_out = rhs_dt;
  *rhs_vectype_out = rhs_vectype;
  if (rhs_dt == vect_constant_def || rhs_dt == vect_external_def)
    *vls_type_out = VLS_STORE_INVARIANT;
  else
    *vls_type_out = VLS_STORE;
  return true;
}

/* Build an all-ones vector mask of type MASKTYPE while vectorizing STMT_INFO.
   Note that we support masks with floating-point type, in which case the
   floats are interpreted as a bitmask.  */

static tree
vect_build_all_ones_mask (vec_info *vinfo,
			  stmt_vec_info stmt_info, tree masktype)
{
  if (TREE_CODE (masktype) == INTEGER_TYPE)
    return build_int_cst (masktype, -1);
  else if (TREE_CODE (TREE_TYPE (masktype)) == INTEGER_TYPE)
    {
      tree mask = build_int_cst (TREE_TYPE (masktype), -1);
      mask = build_vector_from_val (masktype, mask);
      return vect_init_vector (vinfo, stmt_info, mask, masktype, NULL);
    }
  else if (SCALAR_FLOAT_TYPE_P (TREE_TYPE (masktype)))
    {
      REAL_VALUE_TYPE r;
      long tmp[6];
      for (int j = 0; j < 6; ++j)
	tmp[j] = -1;
      real_from_target (&r, tmp, TYPE_MODE (TREE_TYPE (masktype)));
      tree mask = build_real (TREE_TYPE (masktype), r);
      mask = build_vector_from_val (masktype, mask);
      return vect_init_vector (vinfo, stmt_info, mask, masktype, NULL);
    }
  gcc_unreachable ();
}

/* Build an all-zero merge value of type VECTYPE while vectorizing
   STMT_INFO as a gather load.  */

static tree
vect_build_zero_merge_argument (vec_info *vinfo,
				stmt_vec_info stmt_info, tree vectype)
{
  tree merge;
  if (TREE_CODE (TREE_TYPE (vectype)) == INTEGER_TYPE)
    merge = build_int_cst (TREE_TYPE (vectype), 0);
  else if (SCALAR_FLOAT_TYPE_P (TREE_TYPE (vectype)))
    {
      REAL_VALUE_TYPE r;
      long tmp[6];
      for (int j = 0; j < 6; ++j)
	tmp[j] = 0;
      real_from_target (&r, tmp, TYPE_MODE (TREE_TYPE (vectype)));
      merge = build_real (TREE_TYPE (vectype), r);
    }
  else
    gcc_unreachable ();
  merge = build_vector_from_val (vectype, merge);
  return vect_init_vector (vinfo, stmt_info, merge, vectype, NULL);
}

/* Build a gather load call while vectorizing STMT_INFO.  Insert new
   instructions before GSI and add them to VEC_STMT.  GS_INFO describes
   the gather load operation.  If the load is conditional, MASK is the
   unvectorized condition and MASK_DT is its definition type, otherwise
   MASK is null.  */

static void
vect_build_gather_load_calls (vec_info *vinfo, stmt_vec_info stmt_info,
			      gimple_stmt_iterator *gsi,
			      gimple **vec_stmt,
			      gather_scatter_info *gs_info,
			      tree mask)
{
  loop_vec_info loop_vinfo = dyn_cast <loop_vec_info> (vinfo);
  class loop *loop = LOOP_VINFO_LOOP (loop_vinfo);
  tree vectype = STMT_VINFO_VECTYPE (stmt_info);
  poly_uint64 nunits = TYPE_VECTOR_SUBPARTS (vectype);
  int ncopies = vect_get_num_copies (loop_vinfo, vectype);
  edge pe = loop_preheader_edge (loop);
  enum { NARROW, NONE, WIDEN } modifier;
  poly_uint64 gather_off_nunits
    = TYPE_VECTOR_SUBPARTS (gs_info->offset_vectype);

  tree arglist = TYPE_ARG_TYPES (TREE_TYPE (gs_info->decl));
  tree rettype = TREE_TYPE (TREE_TYPE (gs_info->decl));
  tree srctype = TREE_VALUE (arglist); arglist = TREE_CHAIN (arglist);
  tree ptrtype = TREE_VALUE (arglist); arglist = TREE_CHAIN (arglist);
  tree idxtype = TREE_VALUE (arglist); arglist = TREE_CHAIN (arglist);
  tree masktype = TREE_VALUE (arglist); arglist = TREE_CHAIN (arglist);
  tree scaletype = TREE_VALUE (arglist);
  tree real_masktype = masktype;
  gcc_checking_assert (types_compatible_p (srctype, rettype)
		       && (!mask
			   || TREE_CODE (masktype) == INTEGER_TYPE
			   || types_compatible_p (srctype, masktype)));
  if (mask && TREE_CODE (masktype) == INTEGER_TYPE)
    masktype = truth_type_for (srctype);

  tree mask_halftype = masktype;
  tree perm_mask = NULL_TREE;
  tree mask_perm_mask = NULL_TREE;
  if (known_eq (nunits, gather_off_nunits))
    modifier = NONE;
  else if (known_eq (nunits * 2, gather_off_nunits))
    {
      modifier = WIDEN;

      /* Currently widening gathers and scatters are only supported for
	 fixed-length vectors.  */
      int count = gather_off_nunits.to_constant ();
      vec_perm_builder sel (count, count, 1);
      for (int i = 0; i < count; ++i)
	sel.quick_push (i | (count / 2));

      vec_perm_indices indices (sel, 1, count);
      perm_mask = vect_gen_perm_mask_checked (gs_info->offset_vectype,
					      indices);
    }
  else if (known_eq (nunits, gather_off_nunits * 2))
    {
      modifier = NARROW;

      /* Currently narrowing gathers and scatters are only supported for
	 fixed-length vectors.  */
      int count = nunits.to_constant ();
      vec_perm_builder sel (count, count, 1);
      sel.quick_grow (count);
      for (int i = 0; i < count; ++i)
	sel[i] = i < count / 2 ? i : i + count / 2;
      vec_perm_indices indices (sel, 2, count);
      perm_mask = vect_gen_perm_mask_checked (vectype, indices);

      ncopies *= 2;

      if (mask && masktype == real_masktype)
	{
	  for (int i = 0; i < count; ++i)
	    sel[i] = i | (count / 2);
	  indices.new_vector (sel, 2, count);
	  mask_perm_mask = vect_gen_perm_mask_checked (masktype, indices);
	}
      else if (mask)
	mask_halftype = truth_type_for (gs_info->offset_vectype);
    }
  else
    gcc_unreachable ();

  tree scalar_dest = gimple_get_lhs (stmt_info->stmt);
  tree vec_dest = vect_create_destination_var (scalar_dest, vectype);

  tree ptr = fold_convert (ptrtype, gs_info->base);
  if (!is_gimple_min_invariant (ptr))
    {
      gimple_seq seq;
      ptr = force_gimple_operand (ptr, &seq, true, NULL_TREE);
      basic_block new_bb = gsi_insert_seq_on_edge_immediate (pe, seq);
      gcc_assert (!new_bb);
    }

  tree scale = build_int_cst (scaletype, gs_info->scale);

  tree vec_oprnd0 = NULL_TREE;
  tree vec_mask = NULL_TREE;
  tree src_op = NULL_TREE;
  tree mask_op = NULL_TREE;
  tree prev_res = NULL_TREE;

  if (!mask)
    {
      src_op = vect_build_zero_merge_argument (vinfo, stmt_info, rettype);
      mask_op = vect_build_all_ones_mask (vinfo, stmt_info, masktype);
    }

  auto_vec<tree> vec_oprnds0;
  auto_vec<tree> vec_masks;
  vect_get_vec_defs_for_operand (vinfo, stmt_info,
				 modifier == WIDEN ? ncopies / 2 : ncopies,
				 gs_info->offset, &vec_oprnds0);
  if (mask)
    vect_get_vec_defs_for_operand (vinfo, stmt_info,
				   modifier == NARROW ? ncopies / 2 : ncopies,
				   mask, &vec_masks, masktype);
  for (int j = 0; j < ncopies; ++j)
    {
      tree op, var;
      if (modifier == WIDEN && (j & 1))
	op = permute_vec_elements (vinfo, vec_oprnd0, vec_oprnd0,
				   perm_mask, stmt_info, gsi);
      else
	op = vec_oprnd0 = vec_oprnds0[modifier == WIDEN ? j / 2 : j];

      if (!useless_type_conversion_p (idxtype, TREE_TYPE (op)))
	{
	  gcc_assert (known_eq (TYPE_VECTOR_SUBPARTS (TREE_TYPE (op)),
				TYPE_VECTOR_SUBPARTS (idxtype)));
	  var = vect_get_new_ssa_name (idxtype, vect_simple_var);
	  op = build1 (VIEW_CONVERT_EXPR, idxtype, op);
	  gassign *new_stmt = gimple_build_assign (var, VIEW_CONVERT_EXPR, op);
	  vect_finish_stmt_generation (vinfo, stmt_info, new_stmt, gsi);
	  op = var;
	}

      if (mask)
	{
	  if (mask_perm_mask && (j & 1))
	    mask_op = permute_vec_elements (vinfo, mask_op, mask_op,
					    mask_perm_mask, stmt_info, gsi);
	  else
	    {
	      if (modifier == NARROW)
		{
		  if ((j & 1) == 0)
		    vec_mask = vec_masks[j / 2];
		}
	      else
		vec_mask = vec_masks[j];

	      mask_op = vec_mask;
	      if (!useless_type_conversion_p (masktype, TREE_TYPE (vec_mask)))
		{
		  poly_uint64 sub1 = TYPE_VECTOR_SUBPARTS (TREE_TYPE (mask_op));
		  poly_uint64 sub2 = TYPE_VECTOR_SUBPARTS (masktype);
		  gcc_assert (known_eq (sub1, sub2));
		  var = vect_get_new_ssa_name (masktype, vect_simple_var);
		  mask_op = build1 (VIEW_CONVERT_EXPR, masktype, mask_op);
		  gassign *new_stmt
		    = gimple_build_assign (var, VIEW_CONVERT_EXPR, mask_op);
		  vect_finish_stmt_generation (vinfo, stmt_info, new_stmt, gsi);
		  mask_op = var;
		}
	    }
	  if (modifier == NARROW && masktype != real_masktype)
	    {
	      var = vect_get_new_ssa_name (mask_halftype, vect_simple_var);
	      gassign *new_stmt
		= gimple_build_assign (var, (j & 1) ? VEC_UNPACK_HI_EXPR
						    : VEC_UNPACK_LO_EXPR,
				       mask_op);
	      vect_finish_stmt_generation (vinfo, stmt_info, new_stmt, gsi);
	      mask_op = var;
	    }
	  src_op = mask_op;
	}

      tree mask_arg = mask_op;
      if (masktype != real_masktype)
	{
	  tree utype, optype = TREE_TYPE (mask_op);
	  if (TYPE_MODE (real_masktype) == TYPE_MODE (optype))
	    utype = real_masktype;
	  else
	    utype = lang_hooks.types.type_for_mode (TYPE_MODE (optype), 1);
	  var = vect_get_new_ssa_name (utype, vect_scalar_var);
	  mask_arg = build1 (VIEW_CONVERT_EXPR, utype, mask_op);
	  gassign *new_stmt
	    = gimple_build_assign (var, VIEW_CONVERT_EXPR, mask_arg);
	  vect_finish_stmt_generation (vinfo, stmt_info, new_stmt, gsi);
	  mask_arg = var;
	  if (!useless_type_conversion_p (real_masktype, utype))
	    {
	      gcc_assert (TYPE_PRECISION (utype)
			  <= TYPE_PRECISION (real_masktype));
	      var = vect_get_new_ssa_name (real_masktype, vect_scalar_var);
	      new_stmt = gimple_build_assign (var, NOP_EXPR, mask_arg);
	      vect_finish_stmt_generation (vinfo, stmt_info, new_stmt, gsi);
	      mask_arg = var;
	    }
	  src_op = build_zero_cst (srctype);
	}
      gimple *new_stmt = gimple_build_call (gs_info->decl, 5, src_op, ptr, op,
					    mask_arg, scale);

      if (!useless_type_conversion_p (vectype, rettype))
	{
	  gcc_assert (known_eq (TYPE_VECTOR_SUBPARTS (vectype),
				TYPE_VECTOR_SUBPARTS (rettype)));
	  op = vect_get_new_ssa_name (rettype, vect_simple_var);
	  gimple_call_set_lhs (new_stmt, op);
	  vect_finish_stmt_generation (vinfo, stmt_info, new_stmt, gsi);
	  var = make_ssa_name (vec_dest);
	  op = build1 (VIEW_CONVERT_EXPR, vectype, op);
	  new_stmt = gimple_build_assign (var, VIEW_CONVERT_EXPR, op);
	  vect_finish_stmt_generation (vinfo, stmt_info, new_stmt, gsi);
	}
      else
	{
	  var = make_ssa_name (vec_dest, new_stmt);
	  gimple_call_set_lhs (new_stmt, var);
	  vect_finish_stmt_generation (vinfo, stmt_info, new_stmt, gsi);
	}

      if (modifier == NARROW)
	{
	  if ((j & 1) == 0)
	    {
	      prev_res = var;
	      continue;
	    }
	  var = permute_vec_elements (vinfo, prev_res, var, perm_mask,
				      stmt_info, gsi);
	  new_stmt = SSA_NAME_DEF_STMT (var);
	}

      STMT_VINFO_VEC_STMTS (stmt_info).safe_push (new_stmt);
    }
  *vec_stmt = STMT_VINFO_VEC_STMTS (stmt_info)[0];
}

/* Prepare the base and offset in GS_INFO for vectorization.
   Set *DATAREF_PTR to the loop-invariant base address and *VEC_OFFSET
   to the vectorized offset argument for the first copy of STMT_INFO.
   STMT_INFO is the statement described by GS_INFO and LOOP is the
   containing loop.  */

static void
vect_get_gather_scatter_ops (vec_info *vinfo,
			     class loop *loop, stmt_vec_info stmt_info,
