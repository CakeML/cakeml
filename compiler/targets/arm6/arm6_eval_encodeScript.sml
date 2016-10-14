(* --------------------------------------------------------------------------
   Pre-evaluate encoder (to help speed up EVAL)
   -------------------------------------------------------------------------- *)

open HolKernel Parse boolLib bossLib
open armTheory arm6_targetTheory alignmentTheory

val () = new_theory "arm6_eval_encode"

val () = Feedback.set_trace "TheoryPP.include_docs" 0

local
  val n = ["skip", "const", "binop reg", "binop imm", "shift", "long mul",
           "long div", "add carry", "load", (* "load32", *) "load8", "store",
           (* "store32", *) "store8", "jump", "cjump reg", "cjump imm", "call",
           "jump reg", "loc"]
  val l = ListPair.zip (n, Drule.CONJUNCTS arm6_enc_def)
  val thm =  Q.SPEC `f` boolTheory.LET_THM
  val lem = Q.prove(
    `(!n. (3 >< 0) (n2w n : word4) = w2w (n2w n : word4) : word8) /\
     (!n. (3 >< 0) (n2w n : word4) = w2w (n2w n : word4) : word32)`,
    SIMP_TAC (srw_ss()++wordsLib.WORD_EXTRACT_ss) [])
in
  val enc_rwts =
    [encode_def, arm6_encode_def, arm_stepTheory.Aligned,
     alignmentTheory.aligned_numeric, alignmentTheory.aligned_0]
  fun enc_thm s rwts =
   (REWRITE_RULE [lem] o
    SIMP_RULE
      (srw_ss()++bitstringLib.BITSTRING_GROUND_ss++bitstringLib.v2w_n2w_ss++
       wordsLib.WORD_EXTRACT_ss)
      (enc_rwts @ rwts)) (Lib.assoc s l)
  fun mk_let_thm q = Q.ISPEC q thm
end

val skip_rwt = enc_thm "skip"
  [e_data_def, EncodeImmShift_def, boolTheory.LET_DEF]
val const_rwt = enc_thm "const" [e_load_def, e_branch_def, e_data_def]
val binop_rwt = enc_thm "binop reg"
  [e_data_def, EncodeImmShift_def, boolTheory.LET_DEF]
val binop_imm_rwt = enc_thm "binop imm" [e_data_def]
val shift_rwt = enc_thm "shift" [e_data_def]
val add_carry_rwt = enc_thm "add carry"
  [e_data_def, EncodeImmShift_def, boolTheory.LET_DEF]

val load_rwt = enc_thm "load" [e_load_def]
(* val load32_rwt = enc_thm "load32" [e_load_def] *)
val load8_rwt = enc_thm "load8"
  [e_load_def, mk_let_thm `1w: word1`, mk_let_thm `0w : word1`,
   mk_let_thm `v2w [x]: word1`]

val store_rwt = enc_thm "store" [e_store_def]
(* val store32_rwt = enc_thm "store32" [e_store_def] *)
val store8_rwt = enc_thm "store8" [e_store_def]

val jump_rwt = enc_thm "jump" [e_branch_def]
val jump_cmp_rwt = enc_thm "cjump reg"
  [e_branch_def, e_data_def, EncodeImmShift_def,
   mk_let_thm `(0w: word2, 0w: word5)`]
val jump_cmp_imm_rwt = enc_thm "cjump imm" [e_branch_def, e_data_def]

val call_rwt = enc_thm "call" [e_branch_def]

val jump_reg_rwt = enc_thm "jump reg" [e_branch_def]

val loc_rwt = enc_thm "loc"
  [e_data_def,
   mk_let_thm `(15 >< 8) (imm32 : word32) || 3072w : word12`,
   mk_let_thm `(7 >< 0) (imm32 : word32) : word12`]

val arm6_encode_rwts = Theory.save_thm("arm6_encode_rwts",
  Drule.LIST_CONJ
    [skip_rwt, const_rwt, binop_rwt, binop_imm_rwt, shift_rwt, add_carry_rwt,
     load_rwt, (* load32_rwt, *) load8_rwt, store_rwt, (* store32_rwt, *)
     store8_rwt, jump_rwt, jump_cmp_rwt, jump_cmp_imm_rwt, call_rwt,
     jump_reg_rwt, loc_rwt])

val () = export_theory ()
