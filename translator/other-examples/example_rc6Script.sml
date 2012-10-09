open HolKernel bossLib Theory Parse Tactic boolLib Lib

val _ = new_theory "example_rc6";

open wordsTheory wordsLib arithmeticTheory listTheory RC6Theory;
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

(* RC6 *)

val RC6_def = save_thm("RC6_def", RC6_def);
val RC6_CORRECT = save_thm("RC6_CORRECT",RC6_CORRECT);

val res = translate GETKEYS_def
val res = translate PreWhitening_def
(* ROTKEYS switches around a 44-tuple, so the next line takes a bit *)
val res = translate ROTKEYS_def
val res = translate InvPostWhitening_def
val res = translate InvPreWhitening_def
val res = translate RightShift_def
val res = translate LeftShift_def
val res = translate CompUT_def
val res = translate FwdRound_def
val res = translate BwdRound_def
val res = translate PostWhitening_def
val res = translate Round_def
val res = translate InvRound_def
val res = translate r_def
val res = translate RC6_FWD_def
val res = translate RC6_BWD_def

val _ = export_theory ();
