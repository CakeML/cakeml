(*
  Translates aig.
*)
Theory aigProg
Ancestors
  aig basisProg
Libs
  preamble ml_translatorLib

val _ = translation_extends "basisProg";

val r = register_type “:('i, 'l) bvar”;
val r = register_type “:('a, 'i, 'l) var”;

val r = translate aigTheory.not_def;

val r = translate aigTheory.bvar_latches_def;
val r = translate aigTheory.var_latches_def;
val r = translate aigTheory.lit_latches_def;
val r = translate aigTheory.and_latches_def;
val r = translate aigTheory.circuit_latches_def;
