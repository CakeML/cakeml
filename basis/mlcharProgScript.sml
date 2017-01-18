open preamble ml_translatorLib ml_progLib basisFunctionsLib
     mlbasicsProgTheory

val _ = new_theory "mlcharProg";

val _ = translation_extends "mlbasicsProg";

(* Char module -- translated *)

val _ = ml_prog_update (open_module "Char");

val _ = append_dec ``Dtabbrev [] "char" (Tapp [] TC_char)``;
val _ = trans "ord" `ORD`
val _ = trans "chr" `CHR`

val _ = ml_prog_update (close_module NONE);

val _ = export_theory()
