/* An experimental state machine, for tracking "taint": unsanitized uses
   of data potentially under an attacker's control.

   Copyright (C) 2019-2021 Free Software Foundation, Inc.
   Contributed by David Malcolm <dmalcolm@redhat.com>.

This file is part of GCC.

GCC is free software; you can redistribute it and/or modify it
under the terms of the GNU General Public License as published by
the Free Software Foundation; either version 3, or (at your option)
any later version.

GCC is distributed in the hope that it will be useful, but
WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
General Public License for more details.

You should have received a copy of the GNU General Public License
along with GCC; see the file COPYING3.  If not see
<http://www.gnu.org/licenses/>.  */

#include "config.h"
#include "system.h"
#include "coretypes.h"
#include "tree.h"
#include "function.h"
#include "basic-block.h"
#include "gimple.h"
#include "options.h"
#include "diagnostic-path.h"
#include "diagnostic-metadata.h"
#include "function.h"
#include "json.h"
#include "analyzer/analyzer.h"
#include "diagnostic-event-id.h"
#include "analyzer/analyzer-logging.h"
#include "analyzer/sm.h"
#include "analyzer/pending-diagnostic.h"

#if ENABLE_ANALYZER

namespace ana {

namespace {

/* An experimental state machine, for tracking "taint": unsanitized uses
   of data potentially under an attacker's control.  */

class taint_state_machine : public state_machine
{
public:
  taint_state_machine (logger *logger);

  bool inherited_state_p () const FINAL OVERRIDE { return true; }

  bool on_stmt (sm_context *sm_ctxt,
		const supernode *node,
		const gimple *stmt) const FINAL OVERRIDE;

  void on_condition (sm_context *sm_ctxt,
		     const supernode *node,
		     const gimple *stmt,
		     tree lhs,
		     enum tree_code op,
		     tree rhs) const FINAL OVERRIDE;

  bool can_purge_p (state_t s) const FINAL OVERRIDE;

  /* State for a "tainted" value: unsanitized data potentially under an
     attacker's control.  */
  state_t m_tainted;

  /* State for a "tainted" value that has a lower bound.  */
  state_t m_has_lb;

  /* State for a "tainted" value that has an upper bound.  */
  state_t m_has_ub;

  /* Stop state, for a value we don't want to track any more.  */
  state_t m_stop;
};

enum bounds
{
  BOUNDS_NONE,
  BOUNDS_UPPER,
  BOUNDS_LOWER
};

class tainted_array_index
  : public pending_diagnostic_subclass<tainted_array_index>
{
public:
  tainted_array_index (const taint_state_machine &sm, tree arg,
		       enum bounds has_bounds)
  : m_sm (sm), m_arg (arg), m_has_bounds (has_bounds) {}

  const char *get_kind () const FINAL OVERRIDE { return "tainted_array_index"; }

  bool operator== (const tainted_array_index &other) const
  {
    return same_tree_p (m_arg, other.m_arg);
  }

  bool emit (rich_location *rich_loc) FINAL OVERRIDE
  {
    diagnostic_metadata m;
    m.add_cwe (129);
    switch (m_has_bounds)
      {
      default:
	gcc_unreachable ();
      case BOUNDS_NONE:
	return warning_meta (rich_loc, m, OPT_Wanalyzer_tainted_array_index,
			     "use of tainted value %qE in array lookup"
			     " without bounds checking",
			     m_arg);
	break;
      case BOUNDS_UPPER:
	return warning_meta (rich_loc, m, OPT_Wanalyzer_tainted_array_index,
			     "use of tainted value %qE in array lookup"
			     " without lower-bounds checking",
			     m_arg);
	break;
      case BOUNDS_LOWER:
	return warning_meta (rich_loc, m, OPT_Wanalyzer_tainted_array_index,
			     "use of tainted value %qE in array lookup"
			     " without upper-bounds checking",
			     m_arg);
	break;
      }
  }

  label_text describe_state_change (const evdesc::state_change &change)
    FINAL OVERRIDE
  {
    if (change.m_new_state == m_sm.m_tainted)
      {
	if (change.m_origin)
	  return change.formatted_print ("%qE has an unchecked value here"
					 " (from %qE)",
					 change.m_expr, change.m_origin);
	else
	  return change.formatted_print ("%qE gets an unchecked value here",
					 change.m_expr);
      }
    else if (change.m_new_state == m_sm.m_has_lb)
      return change.formatted_print ("%qE has its lower bound checked here",
				     change.m_expr);
    else if (change.m_new_state == m_sm.m_has_ub)
      return change.formatted_print ("%qE has its upper bound checked here",
				     change.m_expr);
    return label_text ();
  }

  label_text describe_final_event (const evdesc::final_event &ev) FINAL OVERRIDE
  {
    switch (m_has_bounds)
      {
      default:
	gcc_unreachable ();
      case BOUNDS_NONE:
	return ev.formatted_print ("use of tainted value %qE in array lookup"
				   " without bounds checking",
				   m_arg);
      case BOUNDS_UPPER:
	return ev.formatted_print ("use of tainted value %qE in array lookup"
				   " without lower-bounds checking",
				   m_arg);
      case BOUNDS_LOWER:
	return ev.formatted_print ("use of tainted value %qE in array lookup"
				   " without upper-bounds checking",
				   m_arg);
      }
  }

private:
  const taint_state_machine &m_sm;
  tree m_arg;
  enum bounds m_has_bounds;
};

/* taint_state_machine's ctor.  */

taint_state_machine::taint_state_machine (logger *logger)
: state_machine ("taint", logger)
{
  m_tainted = add_state ("tainted");
  m_has_lb = add_state ("has_lb");
  m_has_ub = add_state ("has_ub");
  m_stop = add_state ("stop");
}

/* Implementation of state_machine::on_stmt vfunc for taint_state_machine.  */

bool
taint_state_machine::on_stmt (sm_context *sm_ctxt,
			       const supernode *node,
			       const gimple *stmt) const
{
  if (const gcall *call = dyn_cast <const gcall *> (stmt))
    if (tree callee_fndecl = sm_ctxt->get_fndecl_for_call (call))
      {
	if (is_named_call_p (callee_fndecl, "fread", call, 4))
	  {
	    tree arg = gimple_call_arg (call, 0);

	    sm_ctxt->on_transition (node, stmt, arg, m_start, m_tainted);

	    /* Dereference an ADDR_EXPR.  */
	    // TODO: should the engine do this?
	    if (TREE_CODE (arg) == ADDR_EXPR)
	      sm_ctxt->on_transition (node, stmt, TREE_OPERAND (arg, 0),
				      m_start, m_tainted);
	    return true;
	  }
      }
  // TODO: ...etc; many other sources of untrusted data

  if (const gassign *assign = dyn_cast <const gassign *> (stmt))
    {
      tree rhs1 = gimple_assign_rhs1 (assign);
      enum tree_code op = gimple_assign_rhs_code (assign);

      /* Check array accesses.  */
      if (op == ARRAY_REF)
	{
	  tree arg = TREE_OPERAND (rhs1, 1);

	  /* Unsigned types have an implicit lower bound.  */
	  bool is_unsigned = false;
	  if (INTEGRAL_TYPE_P (TREE_TYPE (arg)))
	    is_unsigned = TYPE_UNSIGNED (TREE_TYPE (arg));

	  state_t state = sm_ctxt->get_state (stmt, arg);
	  /* Can't use a switch as the states are non-const.  */
	  if (state == m_tainted)
	    {
	      /* Complain about missing bounds.  */
	      tree diag_arg = sm_ctxt->get_diagnostic_tree (arg);
	      pending_diagnostic *d
		= new tainted_array_index (*this, diag_arg,
					   is_unsigned
					   ? BOUNDS_LOWER : BOUNDS_NONE);
	      sm_ctxt->warn (node, stmt, arg, d);
	      sm_ctxt->set_next_state (stmt, arg, m_stop);
	    }
	  else if (state == m_has_lb)
	    {
	      /* Complain about missing upper bound.  */
	      tree diag_arg = sm_ctxt->get_diagnostic_tree (arg);
	      sm_ctxt->warn (node, stmt, arg,
			      new tainted_array_index (*this, diag_arg,
						       BOUNDS_LOWER));
	      sm_ctxt->set_next_state (stmt, arg, m_stop);
	    }
	  else if (state == m_has_ub)
	    {
	      /* Complain about missing lower bound.  */
	      if (!is_unsigned)
		{
		  tree diag_arg = sm_ctxt->get_diagnostic_tree (arg);
		  sm_ctxt->warn  (node, stmt, arg,
				  new tainted_array_index (*this, diag_arg,
							   BOUNDS_UPPER));
		  sm_ctxt->set_next_state (stmt, arg, m_stop);
		}
	    }
	}
    }

  return false;
}

/* Implementation of state_machine::on_condition vfunc for taint_state_machine.
   Potentially transition state 'tainted' to 'has_ub' or 'has_lb',
   and states 'has_ub' and 'has_lb' to 'stop'.  */

void
taint_state_machine::on_condition (sm_context *sm_ctxt,
				   const supernode *node,
				   const gimple *stmt,
				   tree lhs,
				   enum tree_code op,
				   tree rhs ATTRIBUTE_UNUSED) const
{
  if (stmt == NULL)
    return;

  // TODO: this doesn't use the RHS; should we make it symmetric?

  // TODO
  switch (op)
    {
      //case NE_EXPR:
      //case EQ_EXPR:
    case GE_EXPR:
    case GT_EXPR:
      {
	sm_ctxt->on_transition (node, stmt, lhs, m_tainted,
				m_has_lb);
	sm_ctxt->on_transition (node, stmt, lhs, m_has_ub,
				m_stop);
      }
      break;
    case LE_EXPR:
    case LT_EXPR:
      {
	sm_ctxt->on_transition (node, stmt, lhs, m_tainted,
				m_has_ub);
	sm_ctxt->on_transition (node, stmt, lhs, m_has_lb,
				m_stop);
      }
      break;
    default:
      break;
    }
}

bool
taint_state_machine::can_purge_p (state_t s ATTRIBUTE_UNUSED) const
{
  return true;
}

/* If STATE is a tainted state, write the bounds to *OUT and return true.
   Otherwise return false.
   Use the signedness of TYPE to determine if "has_ub" is tainted.  */

bool
taint_state_machine::get_taint (state_t state, tree type,
				enum bounds *out) const
{
  /* Unsigned types have an implicit lower bound.  */
  bool is_unsigned = false;
  if (type)
    if (INTEGRAL_TYPE_P (type))
      is_unsigned = TYPE_UNSIGNED (type);

  /* Can't use a switch as the states are non-const.  */
  if (state == m_tainted)
    {
      *out = is_unsigned ? BOUNDS_LOWER : BOUNDS_NONE;
      return true;
    }
  else if (state == m_has_lb)
    {
      *out = BOUNDS_LOWER;
      return true;
    }
  else if (state == m_has_ub && !is_unsigned)
    {
      /* Missing lower bound.  */
      *out = BOUNDS_UPPER;
      return true;
    }
  return false;
}

/* Find the most tainted state of S0 and S1.  */

state_machine::state_t
taint_state_machine::combine_states (state_t s0, state_t s1) const
{
  gcc_assert (s0);
  gcc_assert (s1);
  if (s0 == s1)
    return s0;
  if (s0 == m_tainted || s1 == m_tainted)
    return m_tainted;
  if (s0 == m_start)
    return s1;
  if (s1 == m_start)
    return s0;
  if (s0 == m_stop)
    return s1;
  if (s1 == m_stop)
    return s0;
  /* The only remaining combinations are one of has_ub and has_lb
     (in either order).  */
  gcc_assert ((s0 == m_has_lb && s1 == m_has_ub)
	      || (s0 == m_has_ub && s1 == m_has_lb));
  return m_tainted;
}

/* Check for calls to external functions marked with
   __attribute__((access)) with a size-index: complain about
   tainted values passed as a size to such a function.  */

void
taint_state_machine::check_for_tainted_size_arg (sm_context *sm_ctxt,
						 const supernode *node,
						 const gcall *call,
						 tree callee_fndecl) const
{
  tree fntype = TREE_TYPE (callee_fndecl);
  if (!fntype)
    return;

  if (!TYPE_ATTRIBUTES (fntype))
    return;

  /* Initialize a map of attribute access specifications for arguments
     to the function call.  */
  rdwr_map rdwr_idx;
  init_attr_rdwr_indices (&rdwr_idx, TYPE_ATTRIBUTES (fntype));

  unsigned argno = 0;

  for (tree iter = TYPE_ARG_TYPES (fntype); iter;
       iter = TREE_CHAIN (iter), ++argno)
    {
      const attr_access* access = rdwr_idx.get (argno);
      if (!access)
	continue;

      if (access->sizarg == UINT_MAX)
	continue;

      tree size_arg = gimple_call_arg (call, access->sizarg);

      state_t state = sm_ctxt->get_state (call, size_arg);
      enum bounds b;
      if (get_taint (state, TREE_TYPE (size_arg), &b))
	{
	  const char* const access_str =
	    TREE_STRING_POINTER (access->to_external_string ());
	  tree diag_size = sm_ctxt->get_diagnostic_tree (size_arg);
	  sm_ctxt->warn (node, call, size_arg,
			 new tainted_access_attrib_size (*this, diag_size, b,
							 callee_fndecl,
							 access->sizarg,
							 access_str));
	}
    }
}

} // anonymous namespace

/* Internal interface to this file. */

state_machine *
make_taint_state_machine (logger *logger)
{
  return new taint_state_machine (logger);
}

} // namespace ana

#endif /* #if ENABLE_ANALYZER */
