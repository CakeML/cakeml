(* --------------------------------------------------------------------------
   Pre-evaluate encoder (to help speed up EVAL)
   -------------------------------------------------------------------------- *)

open HolKernel Parse boolLib bossLib
open x64Theory x64_targetTheory

val () = new_theory "x64_eval_encode"

val () = Feedback.set_trace "TheoryPP.include_docs" 0

local
  val n = ["skip", "const", "binop reg", "binop imm", "shift", "div",
           "long mul", "long div", "add carry", "add overflow", "sub overflow",
           "load", (* "load32", *) "load8", "store", (* "store32", *)
           "store8", "jump", "cjump reg", "cjump imm", "call",
           "jump reg", "loc"]
  val l = ListPair.zip (n, Drule.CONJUNCTS x64_enc0_def)
  val thm =  Q.SPEC `f` boolTheory.LET_THM
  val rex_prefix_conv =
     Conv.REWR_CONV rex_prefix_def
     THENC Conv.PATH_CONV "llr"
             (blastLib.BBLAST_CONV
              THENC (fn t => if t = boolSyntax.T orelse t = boolSyntax.F then
                                ALL_CONV t
                             else
                                NO_CONV t))
  val rex_prefix_ss =
    simpLib.std_conv_ss
       {name = "rex_prefix", conv = rex_prefix_conv, pats = [``rex_prefix _``]}
in
  val rex_prefix_rule =
    RIGHT_CONV_RULE
      (Conv.DEPTH_CONV rex_prefix_conv THENC SIMP_CONV (srw_ss()) [])
  val enc_rwts = [encode_def, e_rm_reg_def, e_gen_rm_reg_def, e_ModRM_def]
  fun enc_thm s rwts =
    SIMP_RULE (srw_ss()++rex_prefix_ss) (enc_rwts @ rwts) (Lib.assoc s l)
  fun mk_let_thm q = Q.ISPEC q thm
end

local
  val merge_thm = Q.prove (
    `(a ==> (f:'a = x)) /\ ((a = F) ==> (f = y)) ==>
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

val skip_rwt = enc_thm "skip" []
val div_rwt = enc_thm "div" []
val const_rwt = enc_thm "const" [boolTheory.LET_DEF]

local
   val th = Q.prove(`!bop. x64_bop bop <> Ztest`, Cases \\ simp [x64_bop_def])
in
  val binop_rwt =
     simp_cases_rule ``(bop = Or) /\ (r2 = r3 : num)``
        ([boolTheory.LET_THM, e_opsize_def] @ enc_rwts)
        ([mk_let_thm `(Z64,Zrm_r (Zr (total_num2Zreg r1),total_num2Zreg r3))`,
          mk_let_thm `(rex_prefix (v || 8w),1w: word8)`,
          mk_let_thm `n2w (Zreg2num (total_num2Zreg r1)) : word4`,
          e_opsize_def, th] @ enc_rwts)
        (List.nth (Drule.CONJUNCTS x64_enc0_def, 2))
     |> rex_prefix_rule
  val binop_imm_rwt =
    enc_thm "binop imm"
      [mk_let_thm `(_, 1w : word8)`, th, not_byte_def, e_opsize_def]
end

val shift_rwt =
  enc_thm "shift"
   [e_rax_imm_def, e_opsize_imm_def, e_opsize_def, not_byte_def,
    mk_let_thm `(_, 1w: word8)`,
    mk_let_thm `n2w (Zreg2num (total_num2Zreg r1))`]

val long_div_rwt =
  enc_thm "long div" [boolTheory.LET_THM, e_opsize_def]

val long_mul_rwt =
  enc_thm "long mul" [boolTheory.LET_THM, e_opsize_def]

val add_carry_rwt =
  enc_thm "add carry"
   [boolTheory.LET_THM, not_byte_def, e_opsize_def, e_imm8_def, e_rm_imm8_def,
    e_opsize_imm_def, e_imm32_def]

val add_overflow_rwt =
  enc_thm "add overflow"
   [boolTheory.LET_DEF, not_byte_def, e_opsize_def, e_imm8_def, e_rm_imm8_def,
    e_opsize_imm_def, e_imm32_def]

val sub_overflow_rwt =
  enc_thm "sub overflow"
   [boolTheory.LET_DEF, not_byte_def, e_opsize_def, e_imm8_def, e_rm_imm8_def,
    e_opsize_imm_def, e_imm32_def]

local
  val thms =
    [e_rm_reg_def, e_gen_rm_reg_def, e_ModRM_def, e_opsize_def,
     mk_let_thm `(rex_prefix (v || 8w),1w: word8)`,
     mk_let_thm `(rex_prefix (7w && v),1w: word8)`]
in
  val load_rwt = enc_thm "load" thms
(*val load32_rwt = enc_thm "load32" thms *)
  val load8_rwt = enc_thm "load8" thms
  val store_rwt = enc_thm "store" thms
(*val store32_rwt = enc_thm "store32" thms *)
  val store8_rwt = enc_thm "store8" thms
end

val jump_rwt = enc_thm "jump" [x64_encode_jcc_def]

local
  val jump_cmp_case_rule =
    simp_cases_rule ``is_test cmp``
      [e_opsize_def, boolTheory.LET_DEF]
      [e_opsize_def, boolTheory.LET_DEF, Zbinop_name2num_thm, not_byte_def]
  val th = Q.prove(`!cmp. x64_cmp cmp <> Z_ALWAYS`, Cases \\ simp [x64_cmp_def])
  fun rwts i = jump_cmp_case_rule (enc_thm i [x64_encode_jcc_def, th])
in
  val jump_cmp_rwt = rwts "cjump reg"
  val jump_cmp_imm_rwt = rwts "cjump imm"
end

val call_rwt = enc_thm "call" []

val jump_reg_rwt = enc_thm "jump reg" [e_opc_def, boolTheory.LET_DEF]

val loc_rwt = enc_thm "loc" [e_opsize_def, boolTheory.LET_DEF]

val x64_encode_rwts = Theory.save_thm("x64_encode_rwts",
  Drule.LIST_CONJ
    [skip_rwt, div_rwt, const_rwt, binop_rwt, binop_imm_rwt, shift_rwt,
     long_div_rwt, long_mul_rwt, add_carry_rwt, add_overflow_rwt,
     sub_overflow_rwt, load_rwt, (* load32_rwt, *) load8_rwt, store_rwt,
     (* store32_rwt, *) store8_rwt, jump_rwt, jump_cmp_rwt,
     jump_cmp_imm_rwt, call_rwt, jump_reg_rwt, loc_rwt, x64_enc_def])

val () = export_theory ()
