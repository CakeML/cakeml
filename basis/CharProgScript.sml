open preamble ml_translatorLib ml_progLib basisFunctionsLib
     RatProgTheory

val _ = new_theory "CharProg";

val _ = translation_extends "RatProg";

(* Char module -- translated *)

val _ = ml_prog_update (open_module "Char");

val () = generate_sigs := true;

val _ = append_dec ``Dtabbrev unknown_loc [] "char" (Tapp [] TC_char)``;
val _ = trans "ord" `ORD`
val _ = trans "chr" `CHR`
val _ = trans "<" `string$char_lt`
val _ = trans ">" `string$char_gt`
val _ = trans "<=" `string$char_le`
val _ = trans ">=" `string$char_ge`

val _ = next_ml_names := ["isSpace"];
val res = translate stringTheory.isSpace_def;

val sigs = module_signatures [
  "ord",
  "chr",
  "<",
  ">",
  "<=",
  ">=",
  "isSpace"
];

val _ = ml_prog_update (close_module (SOME sigs));

val _ = export_theory()
