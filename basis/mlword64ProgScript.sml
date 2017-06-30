open preamble ml_translatorLib ml_progLib basisFunctionsLib
     mlcharProgTheory

val _ = new_theory "mlword64Prog";

val _ = translation_extends "mlcharProg";

(* Word64 module -- translated *)

val _ = ml_prog_update (open_module "Word64");

val _ = append_dec ``Dtabbrev unknown_loc [] "word" (Tapp [] TC_word64)``;
val _ = trans "fromInt" `n2w:num->word64`
val _ = trans "toInt" `w2n:word64->num`
val _ = trans "andb" `word_and:word64->word64->word64`;

val _ = ml_prog_update (close_module NONE);

val _ = export_theory();
