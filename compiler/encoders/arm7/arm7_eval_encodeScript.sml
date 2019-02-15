(* --------------------------------------------------------------------------
   Pre-evaluate encoder (to help speed up EVAL)
   -------------------------------------------------------------------------- *)

open HolKernel Parse boolLib bossLib
open armTheory arm7_targetTheory alignmentTheory

val () = new_theory "arm7_eval_encode"

val () = Feedback.set_trace "TheoryPP.include_docs" 0

local
  val n = ["skip", "const", "binop reg", "binop imm", "shift", "div",
           "long mul", "long div", "add carry", "add overflow", "sub overflow",
           "load", (* "load32", *) "load8", "store", (* "store32", *) "store8",
           "fp less", "fp less eq", "fp eq", "fp mov", "fp abs", "fp neg",
           "fp sqrt", "fp add", "fp sub", "fp mul", "fp div", "fp fma",
           "fp to reg", "fp from reg", "fp to int", "fp from int", "jump",
           "cjump reg", "cjump imm", "call", "jump reg", "loc"]
  val l = Lib.zip n (Drule.CONJUNCTS arm7_enc_def)
  val thm =  Q.SPEC `f` boolTheory.LET_THM
  val bits30 =
    SIMP_CONV std_ss [bitTheory.BITS_ZERO3, GSYM bitTheory.MOD_2EXP_def]
      ``BITS 3 0 n``
in
  val enc_rwts =
    [encode_def, arm7_encode_def, arm7_encode1_def, arm_stepTheory.Aligned,
     alignmentTheory.aligned_numeric, alignmentTheory.aligned_0]
  fun enc_thm s rwts =
   (SIMP_RULE (srw_ss())
      [wordsTheory.word_extract_n2w, addressTheory.word_LSL_n2w, bits30] o
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
val binop_imm_rwt = enc_thm "binop imm"
  [e_data_def, EncodeImmShift_def, boolTheory.LET_DEF]
val shift_rwt = enc_thm "shift" [e_data_def]
val long_mul_rwt = enc_thm "long mul" [e_multiply_def]
val add_carry_rwt = enc_thm "add carry"
  [e_data_def, EncodeImmShift_def, boolTheory.LET_DEF]
val add_overflow_rwt = enc_thm "add overflow"
  [e_data_def, EncodeImmShift_def, boolTheory.LET_DEF]
val sub_overflow_rwt = enc_thm "sub overflow"
  [e_data_def, EncodeImmShift_def, boolTheory.LET_DEF]

val load_rwt = enc_thm "load" [e_load_def]
(* val load32_rwt = enc_thm "load32" [e_load_def] *)
val load8_rwt = enc_thm "load8"
  [e_load_def, mk_let_thm `1w: word1`, mk_let_thm `0w : word1`,
   mk_let_thm `v2w [x]: word1`]

val store_rwt = enc_thm "store" [e_store_def]
(* val store32_rwt = enc_thm "store32" [e_store_def] *)
val store8_rwt = enc_thm "store8" [e_store_def]

val fp_rwts =
  [arm7_vfp_cmp_def, e_vfp_def, e_data_def, EncodeVFPReg_def,
   boolTheory.LET_DEF]

val fp_less_rwt = enc_thm "fp less" fp_rwts
val fp_less_eq_rwt = enc_thm "fp less eq" fp_rwts
val fp_eq_rwt = enc_thm "fp eq" fp_rwts
val fp_mov_rwt = enc_thm "fp mov" fp_rwts
val fp_abs_rwt = enc_thm "fp abs" fp_rwts
val fp_neg_rwt = enc_thm "fp neg" fp_rwts
val fp_sqrt_rwt = enc_thm "fp sqrt" fp_rwts
val fp_add_rwt = enc_thm "fp add" fp_rwts
val fp_sub_rwt = enc_thm "fp sub" fp_rwts
val fp_mul_rwt = enc_thm "fp mul" fp_rwts
val fp_div_rwt = enc_thm "fp div" fp_rwts
val fp_fma_rwt = enc_thm "fp fma" fp_rwts
val fp_to_reg_rwt = enc_thm "fp to reg" fp_rwts
val fp_from_reg_rwt = enc_thm "fp from reg" fp_rwts
val fp_to_int_rwt = enc_thm "fp to int" fp_rwts
val fp_from_int_rwt = enc_thm "fp from int" fp_rwts

val jump_rwt = enc_thm "jump" [e_branch_def]
val jump_cmp_rwt = enc_thm "cjump reg"
  [e_branch_def, e_data_def, EncodeImmShift_def,
   mk_let_thm `(0w: word2, 0w: word5)`]
val jump_cmp_imm_rwt = enc_thm "cjump imm" [e_branch_def, e_data_def]

val call_rwt = enc_thm "call" [e_branch_def]

val jump_reg_rwt = enc_thm "jump reg" [e_branch_def]

val loc_rwt = enc_thm "loc"
  [e_data_def, listTheory.LIST_BIND_def,
   Q.ISPEC `MAP f` boolTheory.COND_RAND,
   Q.ISPEC `FLAT` boolTheory.COND_RAND,
   mk_let_thm `(h >< l) (imm32 : word32) : word8`]

val arm7_encode_rwts = Theory.save_thm("arm7_encode_rwts",
  Drule.LIST_CONJ
    [skip_rwt, const_rwt, binop_rwt, binop_imm_rwt, shift_rwt, long_mul_rwt,
     add_carry_rwt, add_overflow_rwt, sub_overflow_rwt, load_rwt,
     (* load32_rwt, *) load8_rwt, store_rwt, (* store32_rwt, *) store8_rwt,
     jump_rwt, jump_cmp_rwt, jump_cmp_imm_rwt, call_rwt, jump_reg_rwt, loc_rwt,
     fp_less_rwt, fp_less_eq_rwt, fp_eq_rwt, fp_mov_rwt, fp_abs_rwt,
     fp_neg_rwt, fp_sqrt_rwt, fp_add_rwt, fp_sub_rwt, fp_mul_rwt, fp_div_rwt,
     fp_fma_rwt, fp_to_reg_rwt, fp_from_reg_rwt, fp_to_int_rwt,
     fp_from_int_rwt])

val () = export_theory ()
