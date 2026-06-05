(*
  Translates aig_cert_full.
*)
Theory aig_cert_fullProg
Ancestors
  errorMonad  (* for defining demonadify *)
  aig_cert_encodeProg aig_cert_full
Libs
  preamble ml_translatorLib

val _ = translation_extends "aig_cert_encodeProg";

fun demonadify thm = SRULE [oneline bind_def, guard_def, UNCURRY] thm;

(*

val r = translate (aig_cert_fullTheory.make_cert_cnf_def |> demonadify);

val r = translate aig_cert_fullTheory.lit_to_string_def;
val r = translate aig_cert_fullTheory.clause_to_string_def;
val r = translate aig_cert_fullTheory.cnf_to_string_def;
val r = translate aig_cert_fullTheory.make_cert_strings_def;
*)
