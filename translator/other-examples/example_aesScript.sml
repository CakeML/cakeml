open HolKernel bossLib Theory Parse Tactic boolLib Lib;

val _ = new_theory "example_aes";

open wordsTheory wordsLib arithmeticTheory listTheory aesTheory;
open ml_translatorTheory ml_translatorLib word_preludeTheory;

val _ = translation_extends "word_prelude";

(* translations *)

fun find_def tm = let
  val thy = #Thy (dest_thy_const tm)
  val name = #Name (dest_thy_const tm)
  in fetch thy (name ^ "_def") handle HOL_ERR _ =>
     fetch thy (name ^ "_DEF") handle HOL_ERR _ =>
     fetch thy (name)
  end

(* AES *)

val AES_def = save_thm("AES_def", AES_def);
val AES_CORRECT = save_thm("AES_CORRECT",AES_CORRECT);

val res = translate (find_def ``Sbox``);
val res = translate (find_def ``InvSbox``);

val Sbox_side = prove(
  ``!x. sbox_side x = T``,
  EVAL_TAC THEN MP_TAC (INST_TYPE [alpha|->``:8``] w2n_lt) THEN SRW_TAC [] [])
  |> update_precondition;

val InvSbox_side = prove(
  ``!x. invsbox_side x = T``,
  EVAL_TAC THEN MP_TAC (INST_TYPE [alpha|->``:8``] w2n_lt) THEN SRW_TAC [] [])
  |> update_precondition;

val res = translate (find_def ``genSubBytes``)
val res = translate (find_def ``SubBytes``)
val res = translate (find_def ``ShiftRows``)
val res = translate (find_def ``XOR_BLOCK``)
val res = translate (find_def ``AddRoundKey``)
val res = translate (find_def ``genMixColumns``)
val res = translate MultTheory.xtime_def
val res = translate MultTheory.ConstMult_def
val res = translate (find_def ``MultCol``)
val res = translate (find_def ``MixColumns``)
val res = translate aesTheory.ROTKEYS_def
val res = translate aesTheory.RoundTuple_def
val res = translate aesTheory.Round_def
val res = translate (find_def ``from_state``)
val res = translate (find_def ``to_state``)
val res = translate (find_def ``InvMultCol``)
val res = translate (find_def ``InvMixColumns``)
val res = translate (find_def ``InvShiftRows``)
val res = translate (find_def ``InvSubBytes``)
val res = translate aesTheory.InvRoundTuple_def
val res = translate aesTheory.InvRound_def
val res = translate (find_def ``AES_FWD``)
val res = translate (find_def ``AES_BWD``)

val _ = export_theory ();
