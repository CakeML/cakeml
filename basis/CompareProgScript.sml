(*
  Module with various comparison functions.
*)
open preamble
  ml_translatorLib ml_translatorTheory ml_progLib
  ArrayProgTheory basisFunctionsLib comparisonTheory;

val _ = new_theory "CompareProg"

val _ = translation_extends "ArrayProg";

val _ = ml_prog_update (open_module "Compare");

val result = translate bool_cmp_def;
val result = translate num_cmp_def;
val result = translate char_cmp_def;
val result = translate ternaryComparisonsTheory.list_compare_def;
val result = translate option_cmp_def;
val result = translate option_cmp2_def;
val result = translate pair_cmp_def;
val result = translate string_cmp_def;

val _ = ml_prog_update (close_module NONE);

val _ = export_theory ();
