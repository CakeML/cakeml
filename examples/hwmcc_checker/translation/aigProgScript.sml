(*
  Translates aig and xaig.
*)
Theory aigProg
Ancestors
  aig xaig basisProg
Libs
  preamble ml_translatorLib

val _ = translation_extends "basisProg";

val r = register_type “:('i, 'l) bvar”;
val r = register_type “:('a, 'i, 'l) var”;
val r = register_type “:('a, 'i, 'l) gty”;

val r = translate aigTheory.not_def;

val r = translate aigTheory.bvar_map_def;
val r = translate aigTheory.var_map_def;
val r = translate aigTheory.lit_map_def;

val r = translate xaigTheory.get_lits_def;
val r = translate xaigTheory.gty_map_def;
val r = translate xaigTheory.gate_map_def;
val r = translate xaigTheory.aig_to_xaig_def;
