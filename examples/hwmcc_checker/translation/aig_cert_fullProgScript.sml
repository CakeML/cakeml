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

val _ = use_sub_check true;
val r = translate listRangeTheory.listRangeINC_def;  (* [x .. y] *)
val _ = use_sub_check false;

val r = translate aig_cert_fullTheory.range_inter_def;
val r = translate aig_cert_fullTheory.range_is_subset_def;

val r = translate syntax_helperTheory.print_lit_def;
val r = translate syntax_helperTheory.print_lits_def;
val r = translate syntax_helperTheory.print_header_line_def;
val r = translate aig_cert_fullTheory.cnf_to_string_def;

val r = translate (aig_cert_fullTheory.parse_def |> demonadify);
val r = translate aig_cert_fullTheory.preprocess_def;
val r = translate (aig_cert_fullTheory.process_mlatches_range_def |> demonadify);

val r = translate listTheory.LIST_REL_def;

val r = translate (aig_cert_fullTheory.process_and_check_def |> demonadify);

val r = translate aig_cert_fullTheory.make_reset_string_def;
val r = translate aig_cert_fullTheory.make_transition_string_def;
val r = translate aig_cert_fullTheory.make_property_string_def;
val r = translate aig_cert_fullTheory.make_base_string_def;
val r = translate aig_cert_fullTheory.make_step_string_def;
val r = translate aig_cert_fullTheory.make_liveness_string_def;
val r = translate aig_cert_fullTheory.make_decrease_string_def;
val r = translate aig_cert_fullTheory.make_closure_string_def;
val r = translate aig_cert_fullTheory.make_consistent_string_def;
