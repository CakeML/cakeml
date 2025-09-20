(*
  Translate the basis library term.
*)
Theory basis_defProg[no_sig_docs]
Ancestors
  ml_translator sexp_parserProg
Libs
  preamble ml_translatorLib basis

open preamble ml_translatorLib ml_translatorTheory;
open sexp_parserProgTheory basis;

val _ = translation_extends "sexp_parserProg";
val _ = ml_translatorLib.use_string_type true;
val _ = ml_translatorLib.use_sub_check true;

val _ = ml_translatorLib.ml_prog_update (ml_progLib.open_module "basis_defProg");

val _ = print "About to translate basis (this takes some time) ";
val res = translate basisProgTheory.basis_def;

val _ = ml_translatorLib.ml_prog_update (ml_progLib.close_module NONE);

