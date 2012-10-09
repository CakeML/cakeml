open HolKernel bossLib Theory Parse Tactic boolLib Lib

val _ = new_theory "example_tea";

open wordsTheory wordsLib arithmeticTheory listTheory teaTheory;
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

(* tea *)

val teaEncrypt_def = save_thm("teaEncrypt_def", teaEncrypt_def);
val teaDecrypt_def = save_thm("teaDecrypt_def", teaDecrypt_def);
val tea_correct = save_thm("tea_correct",tea_correct);

val res = translate ShiftXor_def
val res = translate (SIMP_RULE std_ss [DELTA_def] Round_def)
val res = translate (SIMP_RULE std_ss [DELTA_def] InvRound_def)
val res = translate Rounds_def
val res = translate InvRounds_def
val res = translate teaEncrypt_def
val res = translate (SIMP_RULE std_ss [DELTA_def] teaDecrypt_def)

val _ = export_theory ();
