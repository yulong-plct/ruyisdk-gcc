;; Machine description for optimization of RVV auto-vectorization.
;; Copyright (C) 2023 Free Software Foundation, Inc.
;; Contributed by Juzhe Zhong (juzhe.zhong@rivai.ai), RiVAI Technologies Ltd.

;; This file is part of GCC.

;; GCC is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 3, or (at your option)
;; any later version.

;; GCC is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GCC; see the file COPYING3.  If not see
;; <http://www.gnu.org/licenses/>.

;; We don't have vwmul.wv instruction like vwadd.wv in RVV.
;; This pattern is an intermediate RTL IR as a pseudo vwmul.wv to enhance
;; optimization of instructions combine.
(define_insn_and_split "@pred_single_widen_mul<any_extend:su><mode>"
  [(set (match_operand:VWEXTI 0 "register_operand"                  "=&vr,&vr")
	(if_then_else:VWEXTI
	  (unspec:<VM>
	    [(match_operand:<VM> 1 "vector_mask_operand"           "vmWc1,vmWc1")
	     (match_operand 5 "vector_length_operand"              "   rK,   rK")
	     (match_operand 6 "const_int_operand"                  "    i,    i")
	     (match_operand 7 "const_int_operand"                  "    i,    i")
	     (match_operand 8 "const_int_operand"                  "    i,    i")
	     (reg:SI VL_REGNUM)
	     (reg:SI VTYPE_REGNUM)] UNSPEC_VPREDICATE)
	  (mult:VWEXTI
	    (any_extend:VWEXTI
	      (match_operand:<V_DOUBLE_TRUNC> 4 "register_operand" "   vr,   vr"))
	    (match_operand:VWEXTI 3 "register_operand"             "   vr,   vr"))
	  (match_operand:VWEXTI 2 "vector_merge_operand"           "   vu,    0")))]
  "TARGET_VECTOR"
  "#"
  "&& can_create_pseudo_p ()"
  [(const_int 0)]
  {
    insn_code icode = code_for_pred_vf2 (<CODE>, <MODE>mode);
    rtx tmp = gen_reg_rtx (<MODE>mode);
    rtx ops[] = {tmp, operands[4]};
    riscv_vector::emit_vlmax_insn (icode, riscv_vector::RVV_UNOP, ops);

    emit_insn (gen_pred (MULT, <MODE>mode, operands[0], operands[1], operands[2],
			 operands[3], tmp, operands[5], operands[6],
			 operands[7], operands[8]));
    DONE;
  }
  [(set_attr "type" "viwmul")
   (set_attr "mode" "<MODE>")])

;; This pattern it to enchance the instruction combine optimizations for complicate
;; sign and unsigned widening multiplication operations.
(define_insn "*pred_widen_mulsu<mode>"
  [(set (match_operand:VWEXTI 0 "register_operand"                  "=&vr,&vr")
	(if_then_else:VWEXTI
	  (unspec:<VM>
	    [(match_operand:<VM> 1 "vector_mask_operand"           "vmWc1,vmWc1")
	     (match_operand 5 "vector_length_operand"              "   rK,   rK")
	     (match_operand 6 "const_int_operand"                  "    i,    i")
	     (match_operand 7 "const_int_operand"                  "    i,    i")
	     (match_operand 8 "const_int_operand"                  "    i,    i")
	     (reg:SI VL_REGNUM)
	     (reg:SI VTYPE_REGNUM)] UNSPEC_VPREDICATE)
	  (mult:VWEXTI
	    (zero_extend:VWEXTI
	      (match_operand:<V_DOUBLE_TRUNC> 4 "register_operand" "   vr,   vr"))
	    (sign_extend:VWEXTI
	      (match_operand:<V_DOUBLE_TRUNC> 3 "register_operand" "   vr,   vr")))
	  (match_operand:VWEXTI 2 "vector_merge_operand"           "   vu,    0")))]
  "TARGET_VECTOR"
  "vwmulsu.vv\t%0,%3,%4%p1"
  [(set_attr "type" "viwmul")
   (set_attr "mode" "<V_DOUBLE_TRUNC>")])

;; -----------------------------------------------------------------------------
;; ---- Integer Compare Instructions Simplification
;; -----------------------------------------------------------------------------
;; Simplify OP(V, V) Instructions to VMCLR.m Includes:
;; - 1.  VMSNE
;; - 2.  VMSLT
;; - 3.  VMSLTU
;; - 4.  VMSGT
;; - 5.  VMSGTU
;; -----------------------------------------------------------------------------
;; Simplify OP(V, V) Instructions to VMSET.m Includes:
;; - 1.  VMSEQ
;; - 2.  VMSLE
;; - 3.  VMSLEU
;; - 4.  VMSGE
;; - 5.  VMSGEU
;; -----------------------------------------------------------------------------

(define_split
  [(set (match_operand:VB      0 "register_operand")
	(if_then_else:VB
	  (unspec:VB
	    [(match_operand:VB 1 "vector_all_trues_mask_operand")
	     (match_operand    4 "vector_length_operand")
	     (match_operand    5 "const_int_operand")
	     (match_operand    6 "const_int_operand")
	     (reg:SI VL_REGNUM)
	     (reg:SI VTYPE_REGNUM)] UNSPEC_VPREDICATE)
	  (match_operand:VB    3 "vector_move_operand")
	  (match_operand:VB    2 "vector_undef_operand")))]
  "TARGET_VECTOR"
  [(const_int 0)]
  {
    emit_insn (gen_pred_mov (<MODE>mode, operands[0], CONST1_RTX (<MODE>mode),
			     RVV_VUNDEF (<MODE>mode), operands[3],
			     operands[4], operands[5]));
    DONE;
  }
)

;; -------------------------------------------------------------------------
;; ---- [BOOL] Binary logical operations (inverted second input)
;; -------------------------------------------------------------------------
;; Includes:
;; - vmandnot.mm
;; - vmornot.mm
;; -------------------------------------------------------------------------

(define_insn_and_split "*<optab>not<mode>"
  [(set (match_operand:VB 0 "register_operand"           "=vr")
	(bitmanip_bitwise:VB
	  (not:VB (match_operand:VB 2 "register_operand" " vr"))
	  (match_operand:VB 1 "register_operand"         " vr")))]
  "TARGET_VECTOR"
  "#"
  "&& can_create_pseudo_p ()"
  [(const_int 0)]
  {
    insn_code icode = code_for_pred_not (<CODE>, <MODE>mode);
    riscv_vector::emit_vlmax_insn (icode, riscv_vector::RVV_BINOP, operands);
    DONE;
  }
  [(set_attr "type" "vmalu")
   (set_attr "mode" "<MODE>")])

;; -------------------------------------------------------------------------
;; ---- [BOOL] Binary logical operations (inverted result)
;; -------------------------------------------------------------------------
;; Includes:
;; - vmnand.mm
;; - vmnor.mm
;; - vmxnor.mm
;; -------------------------------------------------------------------------

(define_insn_and_split "*n<optab><mode>"
  [(set (match_operand:VB 0 "register_operand"     "=vr")
	(not:VB
	  (any_bitwise:VB
	    (match_operand:VB 1 "register_operand" " vr")
	    (match_operand:VB 2 "register_operand" " vr"))))]
  "TARGET_VECTOR"
  "#"
  "&& can_create_pseudo_p ()"
  [(const_int 0)]
  {
    insn_code icode = code_for_pred_n (<CODE>, <MODE>mode);
    riscv_vector::emit_vlmax_insn (icode, riscv_vector::RVV_BINOP, operands);
    DONE;
  }
  [(set_attr "type" "vmalu")
   (set_attr "mode" "<MODE>")])
