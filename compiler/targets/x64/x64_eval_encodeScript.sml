(* --------------------------------------------------------------------------
   Pre-evaluate encoder (to help speed up EVAL)
   -------------------------------------------------------------------------- *)

open HolKernel Parse boolLib bossLib
open x64Theory x64_targetTheory

val () = new_theory "x64_eval_encode"

val () = Feedback.set_trace "TheoryPP.include_docs" 0

local
  val l = Drule.CONJUNCTS x64_enc0_def
  val thm =  Q.SPEC `f` boolTheory.LET_THM
in
  val enc_rwts = [encode_def, e_rm_reg_def, e_gen_rm_reg_def, e_ModRM_def]
  fun enc_thm i rwts = SIMP_RULE (srw_ss()) (enc_rwts @ rwts) (List.nth (l, i))
  fun mk_let_thm q = Q.ISPEC q thm
end

local
  val merge_thm = Q.prove (
    `(a ==> (f = x)) /\ ((a = F) ==> (f = y)) ==>
     (f = if a then x else y)`, rw [])
  fun rule1 tm = Conv.CONV_RULE (Conv.RHS_CONV (REWRITE_CONV [ASSUME tm]))
  fun rule2 thms = Drule.DISCH_ALL o SIMP_RULE (srw_ss()) thms
in
  fun simp_cases_rule tm l1 l2 th =
    let
      val th1 = rule2 l1 (rule1 tm th)
      val th2 = rule2 l2 (rule1 ``^tm = F`` th)
    in
      Drule.MATCH_MP merge_thm (Thm.CONJ th1 th2)
    end
end

val skip_rwt = enc_thm 0 []
val const_rwt = enc_thm 1 [boolTheory.LET_DEF]

local
   val th = Q.prove(`!bop. x64_bop bop <> Ztest`, Cases \\ simp [x64_bop_def])
in
  val binop_rwt =
     simp_cases_rule ``(bop = Or) /\ (r2 = r3 : num)``
        ([boolTheory.LET_THM, e_opsize_def] @ enc_rwts)
        ([mk_let_thm `(Z64,Zrm_r (Zr (num2Zreg r1),num2Zreg r3))`,
          mk_let_thm `(rex_prefix (v || 8w),1w: word8)`,
          mk_let_thm `n2w (Zreg2num (num2Zreg r1)) : word4`,
          e_opsize_def, th] @ enc_rwts)
        (List.nth (Drule.CONJUNCTS x64_enc0_def, 2))
end

val binop_imm_rwt = enc_thm 3 [not_byte_def, e_opsize_def]

val shift_rwt =
  enc_thm 4
   [e_rax_imm_def, e_opsize_imm_def, e_opsize_def, rex_prefix_def,
    mk_let_thm `([72w: word8], (1w: word8))`]

val add_carry_rwt =
  enc_thm 5
   [mk_let_thm `2w : word4`,
    mk_let_thm `7w : word4`,
    mk_let_thm `(rex_prefix (v || 8w),1w: word8)`,
    not_byte_def, e_opsize_def, e_imm8_def, e_rm_imm8_def, e_opsize_imm_def]

local
  val thms =
    [e_rm_reg_def, e_gen_rm_reg_def, e_ModRM_def, e_opsize_def,
     mk_let_thm `(rex_prefix (v || 8w),1w: word8)`,
     mk_let_thm `(rex_prefix (7w && v),1w: word8)`]
in
  val load_rwt = enc_thm 6 thms
  val load32_rwt = enc_thm 7 thms
  val load8_rwt = enc_thm 8 thms
  val store_rwt = enc_thm 9 thms
  val store32_rwt = enc_thm 10 thms
  val store8_rwt = enc_thm 11 thms
end

val jump_rwt = enc_thm 12 [x64_encode_jcc_def]

local
  val jump_cmp_case_rule =
    simp_cases_rule ``is_test cmp``
      [e_opsize_def, boolTheory.LET_DEF]
      [e_opsize_def, boolTheory.LET_DEF, Zbinop_name2num_thm, not_byte_def]
  val th = Q.prove(`!cmp. x64_cmp cmp <> Z_ALWAYS`, Cases \\ simp [x64_cmp_def])
  fun rwts i = jump_cmp_case_rule (enc_thm i [x64_encode_jcc_def, th])
in
  val jump_cmp_rwt = rwts 13
  val jump_cmp_imm_rwt = rwts 14
end

val call_rwt = enc_thm 15 []

val jump_reg_rwt = enc_thm 16 [e_opc_def, boolTheory.LET_DEF]

val loc_rwt = enc_thm 17 [e_opsize_def, boolTheory.LET_DEF]

val x64_encode_rwts = Theory.save_thm("x64_encode_rwts",
  Drule.LIST_CONJ
    [skip_rwt, const_rwt, binop_rwt, binop_imm_rwt, shift_rwt, add_carry_rwt,
     load_rwt, load32_rwt, load8_rwt, store_rwt, store32_rwt, store8_rwt,
     jump_rwt, jump_cmp_rwt, jump_cmp_imm_rwt, call_rwt, jump_reg_rwt, loc_rwt,
     x64_enc_def])

val () = export_theory ()
