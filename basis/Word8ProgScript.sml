open preamble ml_translatorLib ml_progLib basisFunctionsLib
     Word64ProgTheory

val _ = new_theory "Word8Prog";

val _ = translation_extends "Word64Prog";

(* Word8 module -- translated *)

val _ = ml_prog_update (open_module "Word8");

val _ = append_dec ``Dtabbrev unknown_loc [] "word" (Tapp [] TC_word8)``;
val _ = trans "fromInt" `n2w:num->word8`
val _ = trans "toInt" `w2n:word8->num`
val _ = trans "andb" `word_and:word8->word8->word8`;

val _ = ml_prog_update (close_module NONE);

val _ = export_theory()
