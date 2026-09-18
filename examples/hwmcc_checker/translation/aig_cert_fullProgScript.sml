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

val r = translate (aig_cert_fullTheory.parse_model_def |> demonadify);
val r = translate aig_cert_fullTheory.preprocess_model_def;

val r = translate (aig_cert_fullTheory.parse_witness_def |> demonadify);
val r = translate aig_cert_fullTheory.preprocess_witness_def;

val r = translate listTheory.mapPartial_def;
val r = translate (aig_cert_fullTheory.check_model_def |> demonadify);

val r = translate listTheory.LIST_REL_def;

val r = translate (aig_cert_fullTheory.process_and_check_def |> demonadify);

(* The mapped circuit is the one lowered to CNF, so its gate, input and latch
   names are num whatever the encoded condition was named by. *)
Theorem xaig_map_then_cnf_num[local] =
  aig_cert_fullTheory.xaig_map_then_cnf_def
  |> INST_TYPE [beta |-> “:num”, delta |-> “:num”, mk_vartype "'f" |-> “:num”];
val r = translate xaig_map_then_cnf_num;

val r = translate aig_cert_fullTheory.make_reset_string_def;
val r = translate aig_cert_fullTheory.make_transition_string_def;
val r = translate aig_cert_fullTheory.make_safety_string_def;
val r = translate aig_cert_fullTheory.make_base_string_def;
val r = translate aig_cert_fullTheory.make_induction_string_def;
val r = translate aig_cert_fullTheory.make_liveness_string_def;
val r = translate aig_cert_fullTheory.make_decrease_string_def;
val r = translate aig_cert_fullTheory.make_closure_string_def;
val r = translate aig_cert_fullTheory.make_stable_string_def;
