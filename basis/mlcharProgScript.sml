open preamble ml_translatorLib ml_progLib basisFunctionsLib
     mlratProgTheory

val _ = new_theory "mlcharProg";

val _ = translation_extends "mlratProg";

(* Char module -- translated *)

val _ = ml_prog_update (open_module "Char");

val _ = append_dec ``Dtabbrev unknown_loc [] "char" (Tapp [] TC_char)``;
val _ = trans "ord" `ORD`
val _ = trans "chr" `CHR`
val _ = trans "<" `string$char_lt`
val _ = trans ">" `string$char_gt`
val _ = trans "<=" `string$char_le`
val _ = trans ">=" `string$char_ge`

val _ = next_ml_names := ["isSpace"];
val res = translate stringTheory.isSpace_def;

val _ = ml_prog_update (close_module NONE);

val _ = export_theory()
