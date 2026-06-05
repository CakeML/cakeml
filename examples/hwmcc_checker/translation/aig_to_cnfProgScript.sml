(*
  Translates aig_to_cnf (and its dependencies on cnf).
*)
Theory aig_to_cnfProg
Ancestors
  aig_cert_encodeProg aig_to_cnf
Libs
  preamble ml_translatorLib

val _ = translation_extends "aig_cert_encodeProg";


(*
val r = translate aig_to_cnfTheory.new_live_def;
val r = translate aig_to_cnfTheory.prune_def;
val r = translate aig_to_cnfTheory.prune_rev_def;
val r = translate aig_to_cnfTheory.prune_for_def;
val r = translate aig_to_cnfTheory.eval_circuit;
val r = translate aig_to_cnfTheory.aig_rename_aux_def;
val r = translate aig_to_cnfTheory.aig_rename_def;
val r = translate aig_to_cnfTheory.aig_rename_rev_def;
val r = translate aig_to_cnfTheory.DISJOINT3_def;
val r = translate aig_to_cnfTheory.aig_read_def;
val r = translate aig_to_cnfTheory.has_var_def;
val r = translate aig_to_cnfTheory.closed_def;
val r = translate aig_to_cnfTheory.negate_def;
val r = translate aig_to_cnfTheory.imp_to_cnf_def;
val r = translate aig_to_cnfTheory.eq_every_to_cnf_def;
val r = translate aig_to_cnfTheory.not_TT_def;
val r = translate aig_to_cnfTheory.var_to_name_def;
val r = translate aig_to_cnfTheory.var_to_lit_def;
val r = translate aig_to_cnfTheory.and_to_cnf_def;
val r = translate aig_to_cnfTheory.to_cnf_def;
val r = translate aig_to_cnfTheory.direct_circuit_to_cnf_def;
val r = translate aig_to_cnfTheory.eval_circuits_def;
val r = translate aig_to_cnfTheory.find_suffix_def;
val r = translate aig_to_cnfTheory.cnf_witness_def;
val r = translate aig_to_cnfTheory.lits_within_def;
val r = translate aig_to_cnfTheory.aig_to_cnf_def;
*)
