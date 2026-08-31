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
val r = translate aig_cert_encodeTheory.merge_aigs_def;

val r = translate aig_cert_encodeTheory.left_bvar_def;
val r = translate aig_cert_encodeTheory.left_var_def;
val r = translate aig_cert_encodeTheory.left_lit_def;
val r = translate aig_cert_encodeTheory.left_and_def;
val r = translate aig_cert_encodeTheory.right_bvar_def;
val r = translate aig_cert_encodeTheory.right_var_def;
val r = translate aig_cert_encodeTheory.right_lit_def;
val r = translate aig_cert_encodeTheory.right_and_def;
val r = translate aig_cert_encodeTheory.pair_aigs_def;

val r = translate aig_cert_encodeTheory.iext_var_def;
val r = translate aig_cert_encodeTheory.iext_lit_def;
val r = translate aig_cert_encodeTheory.iext_and_def;
val r = translate aig_cert_encodeTheory.iext_aig_def;

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
val r = translate aig_cert_encodeTheory.imerge_aigs_def;

val r = translate aig_cert_encodeTheory.encode_is_next_with_def;
val r = translate aig_cert_encodeTheory.encode_is_next_def;

val r = translate (miscTheory.list_inter_def |> SRULE [MEMBER_INTRO]);

val r = translate aig_cert_encodeTheory.bvar_map_def;
val r = translate aig_cert_encodeTheory.var_map_base_def;
val r = translate aig_cert_encodeTheory.lit_map_base_def;
val r = translate aig_cert_encodeTheory.live_map_base_def;
val r = translate aig_cert_encodeTheory.and_map_base_def;
val r = translate aig_cert_encodeTheory.aig_map_base_def;

val r = translate aig_cert_encodeTheory.qleft_def;
val r = translate aig_cert_encodeTheory.qleft_live_def;

val r = translate aig_cert_encodeTheory.qinterv_lit_def;
val r = translate aig_cert_encodeTheory.qinterv_and_def;
val r = translate aig_cert_encodeTheory.qinterv_def;
val r = translate aig_cert_encodeTheory.qinterv_l_r_def;
val r = translate aig_cert_encodeTheory.qinterv_r_l_def;
val r = translate aig_cert_encodeTheory.qinterv_lr_r_def;
val r = translate aig_cert_encodeTheory.qinterv_ll_r_def;
val r = translate aig_cert_encodeTheory.qinterv_ll_lr_def;

val r = translate aig_cert_encodeTheory.qinterv_live_def;
val r = translate aig_cert_encodeTheory.qinterv_live_l_r_def;
val r = translate aig_cert_encodeTheory.qinterv_live_r_l_def;
val r = translate aig_cert_encodeTheory.qinterv_live_lr_r_def;
val r = translate aig_cert_encodeTheory.qinterv_live_ll_r_def;
val r = translate aig_cert_encodeTheory.qinterv_live_ll_lr_def;

val r = translate aig_cert_encodeTheory.encode_signal_imply_aux_def;
val r = translate aig_cert_encodeTheory.encode_signal_imply_def;

val r = translate aig_cert_encodeTheory.encode_lives_hold_aux_def;
val r = translate aig_cert_encodeTheory.encode_lives_hold_def;

val r = translate aig_cert_encodeTheory.encode_is_witness_reset_def;
val r = translate aig_cert_encodeTheory.encode_is_witness_transition_def;
val r = translate aig_cert_encodeTheory.encode_is_witness_property_def;
val r = translate aig_cert_encodeTheory.encode_is_witness_base_def;
val r = translate aig_cert_encodeTheory.encode_is_witness_step_def;

val r = translate aig_cert_encodeTheory.encode_is_witness_liveness_def;
val r = translate aig_cert_encodeTheory.encode_is_witness_decrease_def;
val r = translate aig_cert_encodeTheory.encode_is_witness_closure_def;
val r = translate aig_cert_encodeTheory.encode_is_witness_consistent_def;

val r = translate aig_cert_encodeTheory.aig_lookup_def;
val r = translate aig_cert_encodeTheory.latch_deps_def;
val r = translate aig_cert_encodeTheory.reset_edges_def;
val r = translate aig_cert_encodeTheory.reset_graph_def;

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

(* TODO potential inefficiency: unnecessary conversion to num.
     It might be more efficient for latch_deps to be directly over sptree/num_set *)
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

val r = translate aig_cert_encodeTheory.stratified_cond_def;
