(*
  Translates aig_cert_full.
*)
Theory aig_cert_fullProg
Ancestors
  errorMonad  (* for defining demonadify *)
  aig_to_cnfProg aig_cert_full
Libs
  preamble ml_translatorLib

val _ = translation_extends "aig_to_cnfProg";

fun demonadify thm = SRULE [oneline bind_def, guard_def, UNCURRY] thm;

val r = translate aig_cert_fullTheory.space_def;
val r = translate aig_cert_fullTheory.clause_end_def;
val r = translate aig_cert_fullTheory.lit_to_string_def;
val r = translate aig_cert_fullTheory.clause_to_string_def;
val r = translate aig_cert_fullTheory.cnf_to_string_def;

val r = translate (aig_cert_fullTheory.parse_and_process_def |> demonadify);

val r = translate aig_cert_fullTheory.make_reset_string_def;
val r = translate aig_cert_fullTheory.make_transition_string_def;
val r = translate aig_cert_fullTheory.make_property_string_def;
val r = translate aig_cert_fullTheory.make_base_string_def;
val r = translate aig_cert_fullTheory.make_step_string_def;
val r = translate aig_cert_fullTheory.make_liveness_string_def;
val r = translate aig_cert_fullTheory.make_decrease_string_def;
val r = translate aig_cert_fullTheory.make_closure_string_def;
val r = translate aig_cert_fullTheory.make_consistent_string_def;
