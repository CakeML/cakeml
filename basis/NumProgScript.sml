open preamble ml_translatorLib ml_progLib
     IntProgTheory mlnumTheory basisFunctionsLib

val _ = new_theory"NumProg"

val _ = translation_extends "IntProg";

val _ = ml_prog_update (open_module "Num");

val _ = trans "+" `(+):num->num->num`
val _ = trans "-" `(-):num->num->num`
val _ = trans "*" `($*):num->num->num `
val _ = trans "div" `(DIV):num->num->num`
val _ = trans "mod" `(MOD):num->num->num`
val _ = trans "<" `(<):num->num->bool`
val _ = trans ">" `(>):num->num->bool`
val _ = trans "<=" `(<=):num->num->bool`
val _ = trans ">=" `(>=):num->num->bool`

val _ = next_ml_names := ["toString"];
val result = translate
               (toString_def |> REWRITE_RULE [num_toString_def
                                             , mlintTheory.maxSmall_DEC_def]);

val _ = next_ml_names := ["fromString_unsafe"];
val result = translate fromString_unsafe_def;

val fromstring_unsafe_1_side_def = definition"fromstring_unsafe_1_side_def";

val fromString_unsafe_1_side = Q.prove(
  `∀x. fromstring_unsafe_1_side x = T`,
  Cases \\ rw[fromstring_unsafe_1_side_def
             ,fromchars_unsafe_side_thm]) |> update_precondition;

val _ = next_ml_names := ["fromString"];
val result = translate fromString_def;

val fromstring_side_def = definition"fromstring_side_def";

val fromString_side = Q.prove(
  `∀x. fromstring_side x = T`,
  Cases \\ rw[fromstring_side_def
             ,fromchars_side_thm]) |> update_precondition;

val _ = ml_prog_update (close_module NONE);

val _ = export_theory();
