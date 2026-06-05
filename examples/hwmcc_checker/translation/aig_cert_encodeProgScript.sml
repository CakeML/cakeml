(*
  Translates aig_cert_encode.
*)
Theory aig_cert_encodeProg
Ancestors
  ml_translator (* for MEMBER_INTRO *)
  aig_cert_encode aig_parseProg
Libs
  preamble ml_translatorLib

val _ = translation_extends "aig_parseProg";

val r = register_type “:'a ext”;
val r = register_type “:'a iext”;

val r = translate aig_cert_encodeTheory.left_name_var_def;
val r = translate aig_cert_encodeTheory.left_name_lit_def;
val r = translate aig_cert_encodeTheory.left_name_and_def;
val r = translate aig_cert_encodeTheory.right_name_var_def;
val r = translate aig_cert_encodeTheory.right_name_lit_def;
val r = translate aig_cert_encodeTheory.right_name_and_def;
val r = translate aig_cert_encodeTheory.merge_circuits_def;

val r = translate aig_cert_encodeTheory.left_bvar_def;
val r = translate aig_cert_encodeTheory.left_var_def;
val r = translate aig_cert_encodeTheory.left_lit_def;
val r = translate aig_cert_encodeTheory.left_and_def;
val r = translate aig_cert_encodeTheory.right_bvar_def;
val r = translate aig_cert_encodeTheory.right_var_def;
val r = translate aig_cert_encodeTheory.right_lit_def;
val r = translate aig_cert_encodeTheory.right_and_def;
val r = translate aig_cert_encodeTheory.pair_circuits_def;

val r = translate aig_cert_encodeTheory.iext_var_def;
val r = translate aig_cert_encodeTheory.iext_lit_def;
val r = translate aig_cert_encodeTheory.iext_and_def;
val r = translate aig_cert_encodeTheory.iext_circuit_def;

val r = translate aig_cert_encodeTheory.iname_def;

val r = translate rich_listTheory.MAX_LIST_def;
val r = translate aig_cert_encodeTheory.maxn_def;

val r = translate aig_cert_encodeTheory.encode_imply_def;
val r = translate aig_cert_encodeTheory.encode_equiv_aux_def;
val r = translate aig_cert_encodeTheory.encode_equiv_def;
val r = translate aig_cert_encodeTheory.latch_reset_pairs_def;
val r = translate aig_cert_encodeTheory.encode_is_reset_def;
val r = translate aig_cert_encodeTheory.encode_preds_hold_def;

val r = translate aig_cert_encodeTheory.left_reset_def;
val r = translate aig_cert_encodeTheory.right_reset_def;
val r = translate aig_cert_encodeTheory.iext_reset_def;
val r = translate aig_cert_encodeTheory.ileft_reset_def;
val r = translate aig_cert_encodeTheory.iright_reset_def;
val r = translate aig_cert_encodeTheory.ileft_name_lits_def;
val r = translate aig_cert_encodeTheory.iright_name_lits_def;
val r = translate aig_cert_encodeTheory.imerge_circuits_def;

val r = translate aig_cert_encodeTheory.encode_is_next_def;

val r = translate (miscTheory.list_inter_def |> SRULE [MEMBER_INTRO]);

val r = translate aig_cert_encodeTheory.encode_is_witness_reset_def;
val r = translate aig_cert_encodeTheory.encode_is_witness_transition_def;
val r = translate aig_cert_encodeTheory.encode_is_witness_property_def;
val r = translate aig_cert_encodeTheory.encode_is_witness_base_def;
val r = translate aig_cert_encodeTheory.encode_is_witness_step_def;
