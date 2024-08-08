(*
  Translate the basis library term.
*)

open preamble ml_translatorLib ml_translatorTheory;
open sexp_parserProgTheory basis;

val _ = new_theory "basis_defProg";

val _ = translation_extends "sexp_parserProg";
val _ = ml_translatorLib.use_string_type true;

val _ = ml_translatorLib.ml_prog_update (ml_progLib.open_module "basis_defProg");

val _ = print "About to translate basis (this takes some time) ";
val res = translate basisProgTheory.basis_def;

val _ = ml_translatorLib.ml_prog_update (ml_progLib.close_module NONE);

val () = Feedback.set_trace "TheoryPP.include_docs" 0;
val _ = export_theory ();
