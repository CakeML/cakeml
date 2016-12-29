open preamble ml_translatorLib ml_progLib basisFunctionsLib
     mlcharProgTheory

val _ = new_theory "mlword8Prog";

val _ = translation_extends "mlcharProg";

(* Word8 module -- translated *)

val _ = ml_prog_update (open_module "Word8");

val _ = append_dec ``Dtabbrev [] "word" (Tapp [] TC_word8)``;
val _ = trans "fromInt" `n2w:num->word8`
val _ = trans "toInt" `w2n:word8->num`

val _ = ml_prog_update (close_module NONE);

val _ = export_theory()
