(*
  Translates xaig_cert_encode.
*)
Theory aig_cert_encodeProg
Ancestors
  ml_translator (* for MEMBER_INTRO *)
  xaig_cert xaig_cert_encode aig_parseProg
Libs
  preamble ml_translatorLib

val _ = translation_extends "aig_parseProg";

val r = register_type “:'a ext”;

val r = translate xaig_certTheory.bvar_latches_def;
val r = translate xaig_certTheory.var_latches_def;
val r = translate xaig_certTheory.lit_latches_def;
val r = translate xaig_certTheory.gty_latches_def;
val r = translate xaig_certTheory.gate_latches_def;
val r = translate xaig_certTheory.xaig_latches_def;

val r = translate xaig_cert_encodeTheory.left_name_var_def;
val r = translate xaig_cert_encodeTheory.left_name_lit_def;
val r = translate xaig_cert_encodeTheory.left_name_gty_def;
val r = translate xaig_cert_encodeTheory.left_name_gate_def;
val r = translate xaig_cert_encodeTheory.right_name_var_def;
val r = translate xaig_cert_encodeTheory.right_name_lit_def;
val r = translate xaig_cert_encodeTheory.right_name_gty_def;
val r = translate xaig_cert_encodeTheory.right_name_gate_def;
val r = translate xaig_cert_encodeTheory.merge_xaigs_def;

val r = translate xaig_cert_encodeTheory.left_bvar_def;
val r = translate xaig_cert_encodeTheory.left_var_def;
val r = translate xaig_cert_encodeTheory.left_lit_def;
val r = translate xaig_cert_encodeTheory.left_gty_def;
val r = translate xaig_cert_encodeTheory.left_gate_def;
val r = translate xaig_cert_encodeTheory.right_bvar_def;
val r = translate xaig_cert_encodeTheory.right_var_def;
val r = translate xaig_cert_encodeTheory.right_lit_def;
val r = translate xaig_cert_encodeTheory.right_gty_def;
val r = translate xaig_cert_encodeTheory.right_gate_def;
val r = translate xaig_cert_encodeTheory.pair_xaigs_def;

val r = translate xaig_cert_encodeTheory.qinterv_lit_def;
val r = translate xaig_cert_encodeTheory.qinterv_gty_def;
val r = translate xaig_cert_encodeTheory.qinterv_gate_def;
val r = translate xaig_cert_encodeTheory.qinterv_live_def;
val r = translate xaig_cert_encodeTheory.qinterv_def;

val r = translate xaig_cert_encodeTheory.qinterv_l_r_def;
val r = translate xaig_cert_encodeTheory.qinterv_live_l_r_def;
val r = translate xaig_cert_encodeTheory.qinterv_live_r_l_def;
val r = translate xaig_cert_encodeTheory.qinterv_live_ll_r_def;
val r = translate xaig_cert_encodeTheory.qinterv_live_ll_lr_def;
val r = translate xaig_cert_encodeTheory.qinterv_live_lr_r_def;
val r = translate xaig_cert_encodeTheory.qinterv_r_l_def;
val r = translate xaig_cert_encodeTheory.qinterv_ll_r_def;
val r = translate xaig_cert_encodeTheory.qinterv_ll_lr_def;
val r = translate xaig_cert_encodeTheory.qinterv_lr_r_def;

val r = translate xaig_cert_encodeTheory.ext_var_def;
val r = translate xaig_cert_encodeTheory.ext_lit_def;
val r = translate xaig_cert_encodeTheory.ext_gty_def;
val r = translate xaig_cert_encodeTheory.ext_gate_def;
val r = translate xaig_cert_encodeTheory.ext_xaig_def;

val r = translate xaig_cert_encodeTheory.iname_def;
val r = translate rich_listTheory.MAX_LIST_def;
val r = translate xaig_cert_encodeTheory.maxn_def;

val r = translate xaig_cert_encodeTheory.encode_imply_def;

val r = translate xaig_cert_encodeTheory.xori_def;
val r = translate xaig_cert_encodeTheory.encode_pointwise_equal_def;
val r = translate xaig_cert_encodeTheory.impi_def;
val r = translate xaig_cert_encodeTheory.encode_pointwise_imply_def;

val r = translate xaig_cert_encodeTheory.latch_reset_pairs_def;
val r = translate xaig_cert_encodeTheory.encode_xis_reset_def;
val r = translate xaig_cert_encodeTheory.encode_xlits_hold_def;

val r = translate xaig_cert_encodeTheory.ext_reset_def;
val r = translate xaig_cert_encodeTheory.left_reset_def;
val r = translate xaig_cert_encodeTheory.right_reset_def;

val r = translate xaig_cert_encodeTheory.encode_xis_next_def;

val r = translate xaig_cert_encodeTheory.encode_signal_imply_def;
val r = translate xaig_cert_encodeTheory.ori_def;
val r = translate xaig_cert_encodeTheory.encode_lives_hold_def;

val r = translate xaig_cert_encodeTheory.encode_reset_cond_def;
val r = translate xaig_cert_encodeTheory.encode_transition_cond_def;
val r = translate xaig_cert_encodeTheory.encode_safety_cond_def;
val r = translate xaig_cert_encodeTheory.encode_base_cond_def;
val r = translate xaig_cert_encodeTheory.encode_induction_cond_def;

val r = translate xaig_cert_encodeTheory.encode_liveness_cond_def;
val r = translate xaig_cert_encodeTheory.encode_decrease_cond_def;
val r = translate xaig_cert_encodeTheory.encode_closure_cond_def;
val r = translate xaig_cert_encodeTheory.encode_stable_cond_def;

val r = translate xaig_cert_encodeTheory.xaig_lookup_def;
val r = translate xaig_cert_encodeTheory.latch_deps_def;
val r = translate xaig_cert_encodeTheory.reset_edges_def;
val r = translate xaig_cert_encodeTheory.reset_graph_def;

val r = translate sptreeTheory.mk_BN_def;
val r = translate sptreeTheory.mk_BS_def;
val r = translate sptreeTheory.inter_def;
val r = translate sptreeTheory.union_def;
val r = translate sptreeTheory.map_def;
val r = translate sptreeTheory.spt_fold_def;
val r = translate sptreeTheory.spt_left_def;
val r = translate sptreeTheory.spt_center_def;
val r = translate sptreeTheory.spt_right_def;
val r = translate sptreeTheory.subspt_eq;

val r = translate spt_closureTheory.closure_spt_def;

val r = translate topological_sortTheory.trans_clos_def;
val r = translate topological_sortTheory.needs_def;
val r = translate topological_sortTheory.partition_def;
val r = translate topological_sortTheory.top_sort_aux_def;
val r = translate topological_sortTheory.top_sort_def;

val r = translate topological_sortTheory.to_nums_def;
val r = translate topological_sortTheory.top_sort_any_def;

Theorem top_sort_any_side[local]:
  ∀x. top_sort_any_side x ⇔ T
Proof
  rw [definition "top_sort_any_side_def", NULL_EQ_NIL]
QED
val _ = top_sort_any_side |> update_precondition;

val r = translate
          (topological_sortTheory.has_cycle_def |> REWRITE_RULE [MEMBER_INTRO]);

val r = translate xaig_cert_encodeTheory.stratified_cond_def;
