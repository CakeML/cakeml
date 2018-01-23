open preamble ml_translatorLib ml_progLib basisFunctionsLib
     CharProgTheory

val _ = new_theory "Word64Prog";

val _ = translation_extends "CharProg";

(* Word64 module -- translated *)

val _ = ml_prog_update (open_module "Word64");

val () = generate_sigs := true;

val _ = append_dec ``Dtabbrev unknown_loc [] "word" (Tapp [] TC_word64)``;
val _ = trans "fromInt" `n2w:num->word64`
val _ = trans "toInt" `w2n:word64->num`
val _ = trans "andb" `word_and:word64->word64->word64`;

val sigs = module_signatures ["fromInt", "toInt", "andb"];

val _ = ml_prog_update (close_module (SOME sigs));

val _ = export_theory();
