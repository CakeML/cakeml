(*
  Translate the ag32 instruction encoder and ag32-specific config.
*)
open preamble;
open terminationTheory
open ml_translatorLib ml_translatorTheory;
open ag32_targetTheory ag32Theory;
open inliningLib;
local open arm7ProgTheory in end;

val _ = new_theory "ag32Prog"

val _ = translation_extends "arm7Prog";

val ri2bits_eq = prove(
  ``ri2bits ri = case ri of Imm v => (64w:word7 || w2w v) | Reg i => w2w i``,
  Cases_on `ri` \\ fs [ri2bits_def] \\ blastLib.BBLAST_TAC);

val r = translate ri2bits_eq;
val r = translate ag32Theory.funcT2num_thm;
val r = translate ag32Theory.shiftT2num_thm;

val enc_eq = prove(
  ``enc (func,w,a,b,opc) =
        (w2w (ri2bits w) << 25 ||
         w2w (ri2bits a) << 17 ||
         w2w (ri2bits b) << 10 ||
         w2w ((n2w (funcT2num func)):word4) << 6 ||
         w2w opc)``,
  fs [enc_def] \\ blastLib.BBLAST_TAC);

val r = translate enc_eq;

val encShift_eq = prove(
  ``encShift (sh,w,a,b,opc) =
        (w2w (ri2bits w) << 25 ||
         w2w (ri2bits a) << 17 ||
         w2w (ri2bits b) << 10 ||
         w2w ((n2w (shiftT2num sh)):word4) << 6 ||
         w2w opc)``,
  fs [encShift_def] \\ blastLib.BBLAST_TAC);

val r = translate encShift_eq;

val v2w_sing = prove(
  ``v2w [b] = if b then 1w else 0w:word1``,
  Cases_on `b` \\ EVAL_TAC);

val Encode_eq = Encode_def
  |> SIMP_RULE (srw_ss()) [wordsTheory.word_concat_def,v2w_sing,
                           wordsTheory.word_join_def,LET_THM];

val r = translate Encode_eq;

val def = ag32_encode1_def
  |> SIMP_RULE (srw_ss()) [wordsTheory.word_extract_def,
                           wordsTheory.word_bits_mask];

val r = translate def;

val ag32_encode_eq = prove(
  ``ag32_encode [] = [] /\
    ag32_encode (x::xs) = ag32_encode1 x ++ ag32_encode xs``,
  fs [ag32_encode_def]);

val r = translate ag32_encode_eq;

val word_msb_word_bit = prove(
  ``word_msb w = word_bit (dimindex (:'a) - 1) (w:'a word)``,
  fs [wordsTheory.word_msb_def,wordsTheory.word_bit_def]);

val word_neg = prove(``-w = 0w - w``,rw []);

val r = translate ag32_bop_def;
val r = translate ag32_sh_def;
val r = translate ag32_cmp_def;

fun format_def def = def
  |> SIMP_RULE std_ss [pred_setTheory.IN_INSERT,pred_setTheory.NOT_IN_EMPTY,
                       wordsTheory.WORD_LO,wordsTheory.word_abs_def,
                       wordsTheory.WORD_LE,wordsTheory.word_extract_def,
                       wordsTheory.word_bits_mask,wordsTheory.WORD_MUL_LSL,
                       wordsTheory.word_mul_n2w,addressTheory.word_arith_lemma2,
                       wordsTheory.WORD_LT,word_msb_word_bit,ag32_constant_def,
                       EVAL ``dimindex (:32)``,wordsTheory.word_bit_test]
  |> REWRITE_RULE [word_neg];

val r = translate (format_def ag32_jump_constant_def);

val r = translate (format_def ag32_enc_def);

val r = translate (format_def ag32_config_def);

val () = Feedback.set_trace "TheoryPP.include_docs" 0;

val _ = (ml_translatorLib.clean_on_exit := true);

val _ = export_theory();
