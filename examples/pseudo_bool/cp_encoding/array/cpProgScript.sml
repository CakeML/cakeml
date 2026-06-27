(*
  CakeML frontend to the CP encoder: parse a CP s-expression input file
  and run full_encode to produce a PB formula.
*)
Theory cpProg
Ancestors
  basis_ffi pbc pbc_encode pbc_normalise npbc_parseProg
  int_bitwise int_bitwiseExtra ilp ilp_to_pb cp cp_parse cp_enc cp_to_ilp
  cp_to_ilp_prim cp_to_ilp_counting cp_to_ilp_linear cp_to_ilp_array
  cp_to_ilp_extensional cp_to_ilp_logical cp_to_ilp_lexicographical
  cp_to_ilp_channeling cp_to_ilp_misc cp_to_ilp_scheduling cp_to_ilp_all
Libs
  preamble basis

val _ = translation_extends"npbc_parseProg";

(* HOL *)

val res = translate result_monadTheory.bind_def;
val res = translate integerTheory.INT_MAX;

val res = translate int_not_def;
val res = translate bits_of_num_def;
val res = translate bits_of_int_def;

Theorem bits_of_int_side:
  bits_of_int_side i ⇔ T
Proof
  EVAL_TAC >>
  intLib.ARITH_TAC
QED

val _ = update_precondition bits_of_int_side;

val res = translate COUNT_LIST_AUX_def;
val res = translate COUNT_LIST_compute;

val res = translate (nub_def |> REWRITE_RULE [MEMBER_INTRO]);

val res = translate ISL;
val res = translate ISR;
val res = translate OUTL;
val res = translate OUTR;

val res = translate MIN_DEF;
val res = translate TAKE_def;
val res = translate indexedListsTheory.MAPi_ACC_def;
val res = translate indexedListsTheory.MAPi_compute;

(* pbc *)

val res = translate b2i_def;
val res = translate negate_def;
val res = translate iSUM_def;

(* pbc_encode*)

(* TODO: DEDUPLICATE, also defined in pbc_normalise *)
val res = translate pbc_encodeTheory.flip_coeffs_def;
val res = translate min_lin_term_def;
val res = translate max_lin_term_def;

(* cp *)
val res = translate bnd_lookup_def;

val _ = register_type``:'a constraint``;

(* cp_parse *)

(* shared list-parsing combinators *)
val res = translate result_monadTheory.result_mmap_def;
val res = translate sexp_list_of_def;

(* generic helpers *)
val res = translate sexp_bnd_def;
val res = translate sexp_bnds_def;

val res = translate sexp_varc_def;
val res = translate sexp_varc_list_def;

val res = translate sexp_int_def;
val res = translate sexp_int_list_def;

val res = translate sexp_cmpop_kw_def;
val res = translate sexp_cmpop_sym_def;
val res = translate sexp_reify_cmp_def;

val res = translate strip_reif_suffix_def;

Theorem strip_reif_suffix_side:
  strip_reif_suffix_side ms ⇔ T
Proof
  EVAL_TAC>>rw[]
QED

val _ = update_precondition strip_reif_suffix_side;

val res = translate peel_reif_def;

(* primitive *)
val res = translate sexp_prim_unop_def;
val res = translate sexp_prim_binop_def;
val res = translate sexp_unop_body_def;
val res = translate sexp_binop_body_def;
val res = translate sexp_cmpop_body_def;
val res = translate sexp_prim_dispatch_def;

(* linear *)
val res = translate sexp_iclin_pairs_def;
val res = translate sexp_iclin_term_def;
val res = translate sexp_linear_dispatch_def;

(* lex *)
val res = translate sexp_lex_dispatch_def;

(* extensional (table, regular) *)
val res = translate sexp_table_entry_def;
val res = translate sexp_table_row_def;
val res = translate sexp_table_rows_def;
val res = translate sexp_table_body_def;
val res = translate sexp_num_def;
val res = translate sexp_num_list_def;
val res = translate sexp_reg_edge_def;
val res = translate sexp_reg_edges_def;
val res = translate sexp_reg_trans_def;
val res = translate sexp_regular_body_def;
val res = translate sexp_extensional_dispatch_def;

(* array *)
val res = translate sexp_array_ind_def;
val res = translate sexp_varc_rows_def;
val res = translate sexp_array_aggr_def;
val res = translate sexp_element_body_def;
val res = translate sexp_element_2d_body_def;
val res = translate sexp_array_aggr_body_def;
val res = translate sexp_array_dispatch_def;

(* counting *)
val res = translate sexp_all_different_body_def;
val res = translate sexp_nvalue_body_def;
val res = translate sexp_count_body_def;
val res = translate sexp_among_body_def;
val res = translate sexp_in_body_def;
val res = translate sexp_at_most_one_body_def;
val res = translate sexp_all_equal_body_def;
val res = translate sexp_all_different_except_body_def;
val res = translate sexp_symmetric_all_different_body_def;
val res = translate sexp_global_cardinality_body_def;
val res = translate sexp_counting_dispatch_def;

(* logical *)
val res = translate sexp_logical_cons_def;
val res = translate sexp_logical_body_def;
val res = translate sexp_logical_dispatch_def;

(* channeling *)
val res = translate sexp_off_list_def;
val res = translate sexp_inverse_body_def;
val res = translate sexp_channeling_dispatch_def;

(* misc *)
val res = translate sexp_circuit_body_def;
val res = translate sexp_int_rows_def;
val res = translate sexp_knapsack_body_def;
val res = translate sexp_misc_dispatch_def;

(* scheduling *)
val res = translate sexp_disjunctive_body_def;
val res = translate sexp_disjunctive2d_body_def;
val res = translate sexp_cumulative_body_def;
val res = translate sexp_scheduling_dispatch_def;

val res = translate strip_prefix_def;

Theorem strip_prefix_side:
  strip_prefix_side pre s ⇔ T
Proof
  EVAL_TAC>>rw[]
QED

val _ = update_precondition strip_prefix_side;

val res = translate sexp_constraint_dispatch_def;
val res = translate sexp_constraint_def;
val res = translate sexp_constraints_def;
val res = translate sexp_prob_type_def;
val res = translate sexp_cp_inst_def;
val res = translate parse_cp_inst_def;

(* int_bitwiseExtra *)

val res = translate bit_width_def;

(* ilp *)

(* TODO: remove? *)
Theorem int_2_pow_eq:
  (2:int) ** n = &((2:num) ** n)
Proof
  rw[]
QED

val res = translate (min_iterm_def |> PURE_REWRITE_RULE[int_2_pow_eq]);
val res = translate min_ilin_term_def;
val res = translate bits_imply_def;
val res = translate (max_iterm_def |> PURE_REWRITE_RULE[int_2_pow_eq]);
val res = translate max_ilin_term_def;
val res = translate imply_bit_aux_def;
val res = translate imply_bit_def;
val res = translate imply_bits_def;
val res = translate bimply_bits_def;

(* ilp_to_pb *)

val res = translate encode_ivar_def;
val res = translate mul_lin_term_def;
val res = translate encode_iconstraint_one_def;

(* cp_to_ilp *)

(* has_char_to_escape_thm rewrites the strsub-based recursion to a safe
   EXISTS over (explode s), avoiding a non-trivial strsub side condition *)
val res = translate escape_chars_def;

val res = translate needs_escaping_def;

val needs_escaping_side_def = theorem "needs_escaping_side_def";

Theorem needs_escaping_side:
  ∀depth s n l. l ≤ strlen s ⇒ needs_escaping_side depth s n l
Proof
  ho_match_mp_tac needs_escaping_ind >> rw[]>>
  simp[Once needs_escaping_side_def]
QED

val res = needs_escaping_side |> update_precondition;

val res = translate escape_bad_brackets_def;

Theorem escape_bad_brackets_side:
  escape_bad_brackets_side s
Proof
  EVAL_TAC>>
  irule needs_escaping_side>>
  gvs[]
QED

val res = escape_bad_brackets_side |> update_precondition;

val res = translate format_varc_def;
val res = translate format_reif_def;
val res = translate format_annot_def;
val res = translate format_num_list_def;
val res = translate format_int_list_def;
val res = translate format_flag_def;
val res = translate format_var_def;

val res = translate encode_ge_aux_def;
val res = translate encode_eq_aux_def;

val res = translate mk_constraint_ge_def;
val res = translate mk_ge_def;
val res = translate mk_le_def;
val res = translate mk_gt_def;
val res = translate mk_lt_def;

val res = translate split_iclin_term_def;
val res = translate cbimply_var_def;
val res = translate cvar_imply_def;

val res = translate mk_name_def;
val res = translate at_least_one_def;
val res = translate cat_least_one_def;
val res = translate at_most_one_def;
val res = translate cat_most_one_def;

val res = translate intnum_def;

Theorem intnum_side:
  intnum_side i ⇔ T
Proof
  EVAL_TAC>>rw[]>>
  intLib.ARITH_TAC
QED

val _ = update_precondition intnum_side;

val res = translate numint_def;
val res = translate numset_to_intlist_def;
val res = translate union_def;
val res = translate domlist_def;

Theorem domlist_side:
  domlist_side x y ⇔ T
Proof
  EVAL_TAC>>rw[]>>
  intLib.ARITH_TAC
QED

val _ = update_precondition domlist_side;

val res = translate union_dom_def;

val res = translate lookup_int_def;
val res = translate insert_int_def;
val res = translate hash_varc_def;

(* Rewrite lookup_ht so the translator sees a direct case split. *)
Theorem lookup_ht_eq:
  lookup_ht k n ht ⇔
  case lookup (hash_varc k) ht of
    NONE => F
  | SOME t => (case lookup_int n t of NONE => F | SOME ls => MEMBER k ls)
Proof
  rw[lookup_ht_def,MEMBER_INTRO]>>
  every_case_tac>>rw[]
QED

val res = translate lookup_ht_eq;

val res = translate insert_ht_def;

val res = translate has_ge_def;
val res = translate has_eq_def;

val res = translate fold_cenc_def;

val res = translate add_ge_def;
val res = translate add_eq_def;

val res = translate mk_annotate_def;
val res = translate cencode_ge_def;
val res = translate cencode_eq_def;

val res = translate cencode_full_eq_def;
val res = translate cencode_eq_grid_def;
val res = translate cencode_reif_gen_def;

val res = translate reif_gen_def;
val res = translate gtv_def;
val res = translate ltv_def;
val res = translate nev_def;

val res = translate false_constr_def;
val res = translate cfalse_constr_def;

val res = translate flat_app_def;

val res = translate encode_bitsum_def;
val res = translate cencode_bitsum_def;

val res = translate mk_lin_constraint_ge_aux_def;
val res = translate mk_lin_constraint_ge_def;

val res = translate mk_constraint_one_ge_def;

val res = translate init_ec_def;

val res = translate encode_bvar_eq_def;

val res = translate neiv_def;

val res = translate mk_bounds_def;

val res = translate cp_to_ilpTheory.mk_constraint_ge_bin_def;
val res = translate cp_to_ilpTheory.mk_lbnd_bin_def;
val res = translate cp_to_ilpTheory.mk_ubnd_bin_def;
val res = translate cp_to_ilpTheory.mk_bounds_bin_def;
val res = translate cp_to_ilpTheory.ub_num_def;

(* cp_to_ilp_primScript *)

val res = translate cp_to_ilp_primTheory.mk_nge_def;
val res = translate cp_to_ilp_primTheory.mk_nle_def;

val res = translate cp_to_ilp_primTheory.encode_negative_def;
val res = translate cp_to_ilp_primTheory.encode_abs_body_def;

val res = translate cp_to_ilp_primTheory.encode_plus_def;
val res = translate cp_to_ilp_primTheory.cencode_plus_def;

val res = translate cp_to_ilp_primTheory.encode_minus_def;
val res = translate cp_to_ilp_primTheory.cencode_minus_def;

val res = translate cp_to_ilp_primTheory.cencode_negative_def;
val res = translate cp_to_ilp_primTheory.cencode_abs_def;

val res = translate cp_to_ilp_primTheory.cencode_min_def;
val res = translate cp_to_ilp_primTheory.cencode_max_def;

val res = translate cp_to_ilp_primTheory.cmk_eq_def;
val res = translate cp_to_ilp_primTheory.cencode_equal_1_def;
val res = translate cp_to_ilp_primTheory.cencode_equal_2_def;
val res = translate cp_to_ilp_primTheory.cencode_equal_def;

val res = translate cp_to_ilp_primTheory.cencode_not_equal_1_def;
val res = translate cp_to_ilp_primTheory.cencode_not_equal_2_def;
val res = translate cp_to_ilp_primTheory.cencode_not_equal_3_def;
val res = translate cp_to_ilp_primTheory.cencode_not_equal_def;

val res = translate cp_to_ilp_primTheory.encode_cmp_aux_def;
val res = translate cp_to_ilp_primTheory.cencode_order_cmpops_def;

val res = translate cp_to_ilp_primTheory.cencode_prim_constr_def;

(* cp_to_ilp_counting *)

val res = translate cp_to_ilp_countingTheory.equal_chain_def;
val res = translate cp_to_ilp_countingTheory.cencode_all_equal_def;

val res = translate cp_to_ilp_countingTheory.check_neqs_def;
val res = translate cp_to_ilp_countingTheory.cencode_all_different_except_aux_def;
val res = translate cp_to_ilp_countingTheory.cencode_all_different_except_def;
val res = translate cp_to_ilp_countingTheory.cencode_all_different_def;

val res = translate cp_to_ilp_countingTheory.cmk_bounds_def;
val res = translate cp_to_ilp_countingTheory.cmk_bounds_all_def;
val res = translate cp_to_ilp_countingTheory.cencode_symmetric_all_different_aux_def;
val res = translate cp_to_ilp_countingTheory.cencode_symmetric_all_different_def;

val res = translate cp_to_ilp_countingTheory.elm_def;
val res = translate cp_to_ilp_countingTheory.cencode_some_eq_def;

val res = translate cp_to_ilp_countingTheory.cencode_n_value_def;

val res = translate cp_to_ilp_countingTheory.eqi_def;
val res = translate cp_to_ilp_countingTheory.cencode_count_aux_def;
val res = translate cp_to_ilp_countingTheory.cencode_count_def;

val res = translate cp_to_ilp_countingTheory.cencode_among_aux_def;
val res = translate cp_to_ilp_countingTheory.cencode_among_def;

val res = translate cp_to_ilp_countingTheory.cencode_gcc_counts_def;
val res = translate cp_to_ilp_countingTheory.cencode_global_cardinality_aux_def;
val res = translate cp_to_ilp_countingTheory.cencode_global_cardinality_def;

Definition mk_outr_def:
  (mk_outr [] = []) ∧
  (mk_outr (x::xs) =
    (case x of INR y => y::mk_outr xs | _ => mk_outr xs))
End

Theorem EVERY_ISR_mk_outr:
  ∀ls. EVERY ISR ls ⇒
  MAP OUTR ls = mk_outr ls
Proof
  Induct>>rw[mk_outr_def]>>
  TOP_CASE_TAC>>gvs[]
QED

Theorem split_varc_in_list_eq:
  split_varc_in_list Xs =
   let (Xsc,Xsv) = PARTITION ISR Xs in (REVERSE Xsv,mk_outr Xsc)
Proof
  rw[split_varc_in_list_def]>>pairarg_tac>>rw[]>>
  irule EVERY_ISR_mk_outr>>
  drule PARTITION_FILTER >>
  rw[EVERY_FILTER]
QED

val res = translate mk_outr_def;
val res = translate split_varc_in_list_eq;

val res = translate cp_to_ilp_countingTheory.cencode_in_def;
val res = translate cp_to_ilp_countingTheory.cencode_at_most_one_def;

val res = translate cp_to_ilp_countingTheory.cencode_counting_constr_def;

(* cp_to_ilp_linear *)

val res = translate cp_to_ilp_linearTheory.mk_lin_ge_def;
val res = translate cp_to_ilp_linearTheory.mk_lin_le_def;
val res = translate cp_to_ilp_linearTheory.mk_lin_gt_def;
val res = translate cp_to_ilp_linearTheory.mk_lin_lt_def;

val res = translate cp_to_ilp_linearTheory.cmk_lin_eq_def;

val res = translate cp_to_ilp_linearTheory.cencode_lin_equal_1_def;
val res = translate cp_to_ilp_linearTheory.cencode_lin_equal_2_def;

val res = translate cp_to_ilp_linearTheory.cencode_lin_not_equal_1_def;
val res = translate cp_to_ilp_linearTheory.cencode_lin_not_equal_2_def;
val res = translate cp_to_ilp_linearTheory.cencode_lin_not_equal_3_def;

val res = translate cp_to_ilp_linearTheory.encode_lin_cmp_aux_def;

val res = translate cp_to_ilp_linearTheory.cencode_lin_equal_def;
val res = translate cp_to_ilp_linearTheory.cencode_lin_not_equal_def;
val res = translate cp_to_ilp_linearTheory.cencode_lin_order_cmpops_def;

val res = translate cp_to_ilp_linearTheory.cencode_linear_constr_def;

(* cp_to_ilp_array *)

val res = translate cp_to_ilp_arrayTheory.encode_proper_index_def;
val res = translate cp_to_ilp_arrayTheory.cencode_proper_index_def;

val res = translate cp_to_ilp_arrayTheory.encode_element_aux_def;
val res = translate cp_to_ilp_arrayTheory.cencode_element_aux_def;
val res = translate cp_to_ilp_arrayTheory.cencode_element_def;

val res = translate cp_to_ilp_arrayTheory.encode_element2d_aux_def;
val res = translate cp_to_ilp_arrayTheory.cencode_element2d_aux_def;

val res = translate cp_to_ilp_arrayTheory.cencode_element2d_def;

Theorem cencode_element2d_side:
  cencode_element2d_side a b c d e f g ⇔ T
Proof
  EVAL_TAC>>rw[]>>
  Cases_on`b`>>fs[]
QED

val _ = update_precondition cencode_element2d_side;

val res = translate cp_to_ilpTheory.arri_def;
val res = translate cp_to_ilp_arrayTheory.cencode_array_max_def;
val res = translate cp_to_ilp_arrayTheory.cencode_array_min_def;

val res = translate cp_to_ilp_arrayTheory.cencode_array_constr_def;

(* cp_to_ilp_extensional *)

val res = translate cp_to_ilp_extensionalTheory.filter_match_def;
val res = translate cp_to_ilp_extensionalTheory.cencode_tuple_eq_def;
val res = translate cp_to_ilp_extensionalTheory.ctable_al1_def;
val res = translate cp_to_ilp_extensionalTheory.cencode_full_eqs_def;
val res = translate cp_to_ilp_extensionalTheory.creify_tuple_eq_def;
val res = translate cp_to_ilp_extensionalTheory.creify_tuple_eqs_def;
val res = translate cp_to_ilp_extensionalTheory.cencode_table_def;

(* regular *)

(* the translated EL precondition holds for any in-bounds index *)
Theorem el_side_imp[local]:
  ∀xs n. n < LENGTH xs ⇒ el_side n xs
Proof
  Induct>>rw[Once npbc_arrayProgTheory.el_side_def]
QED

val res = translate cpTheory.nfa_edges_def;

Theorem nfa_edges_side:
  nfa_edges_side trans q ⇔ T
Proof
  rw[fetch "-" "nfa_edges_side_def"]>>metis_tac[el_side_imp]
QED

val _ = update_precondition nfa_edges_side;

val res = translate cp_to_ilp_extensionalTheory.reg_state_def;
val res = translate cp_to_ilp_extensionalTheory.state_idx_row;
val res = translate cp_to_ilp_extensionalTheory.state_idx_def;
val res = translate cp_to_ilp_extensionalTheory.start_state_def;
val res = translate cp_to_ilp_extensionalTheory.accept_state_def;
val res = translate cp_to_ilp_extensionalTheory.reg_targets_def;
val res = translate cp_to_ilp_extensionalTheory.reg_frame_def;
val res = translate cp_to_ilp_extensionalTheory.reg_trans_def;
val res = translate cp_to_ilp_extensionalTheory.reg_eq_pairs_def;
val res = translate cp_to_ilp_extensionalTheory.cencode_regular_def;
val res = translate cp_to_ilp_extensionalTheory.cencode_extensional_constr_def;

(* cp_to_ilp_logical *)

val res = translate cp_to_ilp_logicalTheory.encode_and_aux_def;
val res = translate cp_to_ilp_logicalTheory.cencode_and_aux_def;
val res = translate cp_to_ilp_logicalTheory.cencode_and_def;

val res = translate cp_to_ilp_logicalTheory.encode_or_aux_def;
val res = translate cp_to_ilp_logicalTheory.cencode_or_aux_def;
val res = translate cp_to_ilp_logicalTheory.cencode_or_def;

val res = translate cp_to_ilp_logicalTheory.encode_xor_def;
val res = translate cp_to_ilp_logicalTheory.cencode_parity_aux_def;
val res = translate cp_to_ilp_logicalTheory.cencode_parity_def;

val res = translate cp_to_ilp_logicalTheory.cencode_logical_constr_def;

(* cp_to_ilp_lexicographical *)

val res = translate cp_to_ilp_lexicographicalTheory.pref_eq_def;
val res = translate cp_to_ilp_lexicographicalTheory.dec_at_def;
val res = translate cp_to_ilp_lexicographicalTheory.inc_at_def;

val _ = ml_translatorLib.use_sub_check true;

val res = translate cp_to_ilp_lexicographicalTheory.pref_imp_pref_def;
val res = translate cp_to_ilp_lexicographicalTheory.pref_imp_eq_def;
val res = translate cp_to_ilp_lexicographicalTheory.dec_imp_pref_def;
val res = translate cp_to_ilp_lexicographicalTheory.inc_imp_pref_def;
val res = translate cp_to_ilp_lexicographicalTheory.dec_imp_gt_def;
val res = translate cp_to_ilp_lexicographicalTheory.inc_imp_lt_def;
val res = translate cp_to_ilp_lexicographicalTheory.mk_lex_gte_al1_def;
val res = translate cp_to_ilp_lexicographicalTheory.lex_gte_def;
val res = translate cp_to_ilp_lexicographicalTheory.mk_lex_lte_al1_def;
val res = translate cp_to_ilp_lexicographicalTheory.lex_lte_def;
val res = translate cp_to_ilp_lexicographicalTheory.cencode_lex_gte_def;
val res = translate cp_to_ilp_lexicographicalTheory.cencode_lex_lte_def;
val res = translate cp_to_ilp_lexicographicalTheory.cencode_lex_def;
val res = translate cp_to_ilp_lexicographicalTheory.cencode_lexicographical_constr_def;

val _ = ml_translatorLib.use_sub_check false;

(* cp_to_ilp_channeling *)

val res = translate cp_to_ilp_channelingTheory.encode_inverse_aux_def;
val res = translate cp_to_ilp_channelingTheory.cencode_inverse_def;

val res = translate cp_to_ilp_channelingTheory.cencode_channeling_constr_def;

(* cp_to_ilp_misc *)

val res = translate cp_to_ilp_miscTheory.cencode_circuit_pos_def;

Theorem cencode_circuit_pos_side[local]:
  cencode_circuit_pos_side bnd Xs nm ⇔ 1 ≤ LENGTH Xs
Proof
  rw[fetch "-" "cencode_circuit_pos_side_def"]>>gvs[]
QED

val _ = update_precondition cencode_circuit_pos_side;

val res = translate cp_to_ilp_miscTheory.cencode_circuit_aux_def;

Theorem cencode_circuit_aux_side[local]:
  cencode_circuit_aux_side bnd Xs nm ⇔ 1 ≤ LENGTH Xs
Proof
  rw[fetch "-" "cencode_circuit_aux_side_def"]>>gvs[]
QED

val _ = update_precondition cencode_circuit_aux_side;

val res = translate cp_to_ilp_miscTheory.cencode_circuit_def;

Theorem cencode_circuit_side:
  cencode_circuit_side bnd Xs nm ec ⇔ T
Proof
  rw[fetch "-" "cencode_circuit_side_def"]>>gvs[]>>Cases_on ‘Xs’>>gvs[]
QED

val _ = update_precondition cencode_circuit_side;

val res = translate cp_to_ilp_miscTheory.cencode_knapsack1_def;
val res = translate cp_to_ilp_miscTheory.cencode_knapsack_def;

val res = translate cp_to_ilp_miscTheory.cencode_misc_constr_def;

(* cp_to_ilp_scheduling *)
val res = translate cp_to_ilp_schedulingTheory.disj_before_def;
val res = translate cp_to_ilp_schedulingTheory.disj_zero_def;
val res = translate cp_to_ilp_schedulingTheory.zsize_inactive_def;
val res = translate cp_to_ilp_schedulingTheory.zsize_lit_def;
val res = translate cp_to_ilp_schedulingTheory.mk_before_links_def;
val res = translate cp_to_ilp_schedulingTheory.mk_zero_links_def;
val res = translate cp_to_ilp_schedulingTheory.mk_sep_clauses_def;
val res = translate cp_to_ilp_schedulingTheory.cencode_disjunctive_def;
val res = translate cp_to_ilp_schedulingTheory.cencode_disjunctive2d_def;

(* cumulative *)
val res = translate cp_to_ilp_schedulingTheory.varc_bnd_def;
val res = translate cp_to_ilp_schedulingTheory.cumul_before_def;
val res = translate cp_to_ilp_schedulingTheory.cumul_after_def;
val res = translate cp_to_ilp_schedulingTheory.cumul_active_def;
val res = translate cp_to_ilp_schedulingTheory.cumul_cbit_def;
val res = translate cp_to_ilp_schedulingTheory.cumul_ub_num_def;

Theorem cumul_ub_num_side[local]:
  cumul_ub_num_side a b c d ⇔ T
Proof
  rw[fetch "-" "cumul_ub_num_side_def"]>>rw[]>>intLib.ARITH_TAC
QED
val _ = update_precondition cumul_ub_num_side;

val res = translate cp_to_ilp_schedulingTheory.cumul_contrib_ge_def;
val res = translate cp_to_ilp_schedulingTheory.cumul_contrib_le_def;
val res = translate cp_to_ilp_schedulingTheory.cumul_contrib_le0_def;
val res = translate cp_to_ilp_schedulingTheory.mk_cumul_active_def;
val res = translate cp_to_ilp_schedulingTheory.cumul_tlo_def;
val res = translate cp_to_ilp_schedulingTheory.cumul_thi_def;
val res = translate cp_to_ilp_schedulingTheory.mk_cumul_contrib_def;
val res = translate cp_to_ilp_schedulingTheory.cumul_nonneg_def;
val res = translate cp_to_ilp_schedulingTheory.cumul_cap_line_def;
val res = translate cp_to_ilp_schedulingTheory.cencode_cumulative_def;

Theorem cencode_cumulative_side[local]:
  cencode_cumulative_side a b c d e f ⇔ T
Proof
  rw[fetch "-" "cencode_cumulative_side_def"]>>
  `cumul_tlo a (ZIP (b,ZIP (c,d))) ≤ 0` by
    simp[cp_to_ilp_schedulingTheory.cumul_tlo_LE_0]>>
  `0 ≤ cumul_thi a (ZIP (b,ZIP (c,d)))` by
    simp[cp_to_ilp_schedulingTheory.cumul_thi_0_LE]>>
  rpt(qpat_x_assum`LENGTH _ = LENGTH _`kall_tac)>>
  intLib.ARITH_TAC
QED
val _ = update_precondition cencode_cumulative_side;

val res = translate cp_to_ilp_schedulingTheory.cencode_scheduling_constr_def;

(* cp_to_ilp_all *)

val res = translate cencode_constraint_def;
val res = translate cencode_constraints_def;

(* cp_encScript *)

val res = translate cencode_bound_var_def;
val res = translate cencode_bound_all_def;

val res = translate cp_encTheory.encode_def;
val res = translate encode_nivar_def;
val res = translate proj_ivar_def;
val res = translate encode_prob_type_def;
val res = translate format_string_def;
val res = translate full_encode_def;
val res = translate conv_concl_def;

(* CF CakeML setup *)
Overload "cp_inst_TYPE" = ``
  PAIR_TYPE (LIST_TYPE (PAIR_TYPE vomap_TYPE (PAIR_TYPE INT INT)))
     (PAIR_TYPE
        (LIST_TYPE (PAIR_TYPE vomap_TYPE (CP_CONSTRAINT_TYPE vomap_TYPE)))
        (CP_PROB_TYPE_TYPE vomap_TYPE)) ``

Definition get_cp_inst_def:
  get_cp_inst fs f =
  if inFS_fname fs f then
    case parse_cp_inst (concat (all_lines_file fs f)) of
      INL _ => NONE
    | INR inst => SOME inst
  else NONE
End

(* Read an input file and parse into a cp_inst. *)
Quote add_cakeml:
  fun parse_cp_file f =
    let
      val fd = TextIO.openIn f
      val l = TextIO.inputAll fd
      val u = TextIO.closeIn fd
    in
      parse_cp_inst l
    end
    handle TextIO.BadFileName => Inl (notfound_string f)
End

Theorem parse_cp_file_spec:
  STRING_TYPE f fv ∧
  validArg f ∧
  hasFreeFD fs
  ⇒
  app (p:'ffi ffi_proj) ^(fetch_v"parse_cp_file"(get_ml_prog_state()))
    [fv]
    (STDIO fs)
    (POSTv v.
    STDIO fs *
    & ∃res.
       SUM_TYPE STRING_TYPE cp_inst_TYPE res v ∧
       case res of
        INL err =>
          get_cp_inst fs f = NONE
      | INR inst =>
          get_cp_inst fs f = SOME inst)
Proof
  cheat
QED

Quote add_cakeml:
  fun parse_and_enc f =
  case parse_cp_file f of
    Inl err => Inl err
  | Inr inst => Inr (snd (snd inst), full_encode inst)
End

Theorem parse_and_enc_spec:
  STRING_TYPE f fv ∧
  validArg f ∧
  hasFreeFD fs
  ⇒
  app (p:'ffi ffi_proj) ^(fetch_v"parse_and_enc"(get_ml_prog_state()))
    [fv]
    (STDIO fs)
    (POSTv v.
    STDIO fs *
    & ∃res.
       SUM_TYPE STRING_TYPE
         (PAIR_TYPE (CP_PROB_TYPE_TYPE STRING_TYPE)
         annot_prob_TYPE) res v ∧
       case res of
        INL err =>
          get_cp_inst fs f = NONE
      | INR (cpobj,prob) =>
          ∃inst.
          get_cp_inst fs f = SOME inst ∧
          SND (SND inst) = cpobj ∧
          full_encode inst = prob)
Proof
  rw[]>>
  xcf"parse_and_enc"(get_ml_prog_state())>>
  xlet_autop>>
  Cases_on`res`>>gvs[SUM_TYPE_def]>>
  xmatch
  >- (
    xcon>>xsimpl>>
    simp[AllCasePreds(),PULL_EXISTS,SUM_TYPE_def]>>
    metis_tac[])>>
  rpt xlet_autop>>
  xcon>>xsimpl>>
  simp[AllCasePreds(),PULL_EXISTS,SUM_TYPE_def,PAIR_TYPE_def]
QED

Definition cp_no_concl_str_def:
  cp_no_concl_str = «s NO CONCLUSION\n»
End

Definition cp_sat_str_def:
  cp_sat_str = «s VERIFIED SATISFIABLE\n»
End

Definition cp_unsat_str_def:
  cp_unsat_str = «s VERIFIED UNSATISFIABLE\n»
End

Definition cp_bound_str_def:
  cp_bound_str lbi ubi =
  concat [
    «s VERIFIED BOUNDS »;
    (case lbi of NONE => «-INF» | SOME l => mlint$toString (l:int));
    « <= OBJ <= »;
    (case ubi of NONE => «+INF» | SOME u => mlint$toString (u:int));
    «\n»]
End

Definition cp_enum_str_def:
  cp_enum_str (n:num) b =
    if b
    then
      «s VERIFIED COMPLETE ENUMERATION OF » ^ toString n ^ « SOLUTIONS\n»
    else
      «s VERIFIED PARTIAL ENUMERATION OF » ^ toString n ^ « SOLUTIONS\n»
End

Definition print_cp_concl_str_def:
  (print_cp_concl_str NoConcl = cp_no_concl_str) ∧
  (print_cp_concl_str DSat = cp_sat_str) ∧
  (print_cp_concl_str DUnsat = cp_unsat_str) ∧
  (print_cp_concl_str (OBounds lbi ubi) = cp_bound_str lbi ubi) ∧
  (print_cp_concl_str (EEnum n complete) = cp_enum_str n complete)
End

val res = translate cp_sat_str_def;
val res = translate cp_unsat_str_def;
val res = translate cp_bound_str_def;
val res = translate cp_no_concl_str_def;
val res = translate cp_enum_str_def;
val res = translate print_cp_concl_str_def;

Definition map_concl_to_string_def:
  (map_concl_to_string cpobj (INL s) = (INL s)) ∧
  (map_concl_to_string cpobj (INR (out,bnd,c)) =
    case conv_concl cpobj c of
      NONE => INL («invalid conclusion type for CP problem\n»)
    | SOME concl => INR (print_cp_concl_str concl))
End

val res = translate map_concl_to_string_def;

Definition check_unsat_2_sem_def:
  check_unsat_2_sem fs f out ⇔
  (out ≠ «» ⇒
  ∃inst c.
    get_cp_inst fs f = SOME inst ∧
    out = print_cp_concl_str c ∧
    cp_inst_sem_concl inst c)
End

Quote add_cakeml:
  fun check_unsat_2 f1 f2 =
  case parse_and_enc f1 of
    Inl err => TextIO.output TextIO.stdErr err
  | Inr (inst,prob) =>
    let
      val prob = strip_annot_prob prob
      val probt = default_prob in
      (case
        map_concl_to_string inst
          (check_unsat_top_norm False prob probt f2) of
        Inl err => TextIO.output TextIO.stdErr err
      | Inr s => TextIO.print s)
    end
End

Theorem check_unsat_2_spec:
  STRING_TYPE f1 f1v ∧ validArg f1 ∧
  STRING_TYPE f2 f2v ∧ validArg f2 ∧
  hasFreeFD fs
  ⇒
  app (p:'ffi ffi_proj) ^(fetch_v"check_unsat_2"(get_ml_prog_state()))
    [f1v; f2v]
    (STDIO fs)
    (POSTv uv. &UNIT_TYPE () uv *
    SEP_EXISTS out err.
      STDIO (add_stdout (add_stderr fs err) out) *
      &(check_unsat_2_sem fs f1 out))
Proof
  rw[check_unsat_2_sem_def]>>
  xcf "check_unsat_2" (get_ml_prog_state ())>>
  reverse (Cases_on `STD_streams fs`) >- (fs [TextIOProofTheory.STDIO_def] \\ xpull) >>
  xlet_autop>>
  Cases_on`res`>>fs[SUM_TYPE_def]
  >- (
    xmatch>>
    xapp_spec output_stderr_spec \\ xsimpl>>
    asm_exists_tac>>xsimpl>>
    qexists_tac`emp`>>xsimpl>>
    qexists_tac`fs`>>xsimpl>>
    rw[]>>
    qexists_tac`x`>>xsimpl>>rw[]>>
    fs[STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil]>>
    xsimpl)>>
  Cases_on`y`>>fs[PAIR_TYPE_def]>>
  xmatch>>
  xlet_autop>>
  assume_tac npbc_parseProgTheory.default_prob_v_thm>>
  xlet`POSTv v.
    STDIO fs *
    &prob_TYPE default_prob v`
  >-
    (xvar>>xsimpl)>>
  xlet`POSTv v. STDIO fs * &BOOL F v`
  >-
    (xcon>>xsimpl)>>
  drule npbc_parseProgTheory.check_unsat_top_norm_spec>>
  qpat_x_assum`prob_TYPE (strip_annot_prob _) _`assume_tac>>
  disch_then drule>>
  qpat_x_assum`prob_TYPE default_prob _`assume_tac>>
  disch_then drule>>
  strip_tac>>
  xlet_auto
  >- (
    xsimpl>>
    fs[validArg_def]>>
    metis_tac[])>>
  xlet_autop>>
  every_case_tac>>gvs[SUM_TYPE_def]
  >- (
    fs[map_concl_to_string_def,SUM_TYPE_def]>>
    xmatch>>
    xapp_spec output_stderr_spec \\ xsimpl>>
    asm_exists_tac>>xsimpl>>
    qexists_tac`emp`>>xsimpl>>
    qexists_tac`fs`>>xsimpl>>
    rw[]>>
    qexists_tac`«»`>>
    rename1`add_stderr _ err`>>
    qexists_tac`err`>>xsimpl>>rw[]>>
    fs[STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil]>>
    xsimpl)>>
  fs[map_concl_to_string_def]>>
  every_case_tac>>fs[SUM_TYPE_def]>>xmatch
  >- (
    xapp>>xsimpl>>
    cheat)
  >- (
    xapp>>xsimpl>>
    cheat)
QED

(* Emit just the PB encoding on stdout. *)
Definition check_unsat_1_sem_def:
  check_unsat_1_sem fs f1 out ⇔
  case get_cp_inst fs f1 of
    NONE => out = «»
  | SOME inst =>
    out = concat (print_annot_prob (full_encode inst))
End

Quote add_cakeml:
  fun check_unsat_1 f1 =
  case parse_and_enc f1 of
    Inl err => TextIO.output TextIO.stdErr err
  | Inr (cpobj,prob) =>
    TextIO.print_list (print_annot_prob prob)
End

Theorem check_unsat_1_spec:
  STRING_TYPE f1 f1v ∧ validArg f1 ∧
  hasFreeFD fs
  ⇒
  app (p:'ffi ffi_proj) ^(fetch_v"check_unsat_1"(get_ml_prog_state()))
    [f1v]
    (STDIO fs)
    (POSTv uv. &UNIT_TYPE () uv *
    SEP_EXISTS out err.
      STDIO (add_stdout (add_stderr fs err) out) *
      &(check_unsat_1_sem fs f1 out))
Proof
  rw[check_unsat_1_sem_def]>>
  xcf "check_unsat_1" (get_ml_prog_state ())>>
  reverse (Cases_on `STD_streams fs`) >- (fs [TextIOProofTheory.STDIO_def] \\ xpull) >>
  xlet_autop>>
  Cases_on`res`>>fs[SUM_TYPE_def]
  >- (
    xmatch>>
    xapp_spec output_stderr_spec \\ xsimpl>>
    asm_exists_tac>>xsimpl>>
    qexists_tac`emp`>>qexists_tac`fs`>>xsimpl>>
    fs[STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil]>>
    rw[]>>
    qexists_tac`x`>>xsimpl)>>
  Cases_on`y`>>gvs[PAIR_TYPE_def]>>
  xmatch>>
  xlet_autop>>
  xapp_spec print_list_spec>>xsimpl>>
  asm_exists_tac>>xsimpl>>
  qexists_tac`emp`>>qexists_tac`fs`>>xsimpl>>
  rw[]>>
  qexists_tac`«»`>>
  simp[STD_streams_stderr,add_stdo_nil]>>
  xsimpl
QED

Definition usage_string_def:
  usage_string = «Usage: cake_pb_cp <CP file> <optional: PB proof file>\n»
End

val r = translate usage_string_def;

Quote add_cakeml:
  fun main u =
  case CommandLine.arguments () of
    [f1] => check_unsat_1 f1
  | [f1,f2] => check_unsat_2 f1 f2
  | _ => TextIO.output TextIO.stdErr (mk_usage_string usage_string)
End

Definition main_sem_def:
  main_sem fs cl out =
  if LENGTH cl = 2 then
    check_unsat_1_sem fs (EL 1 cl) out
  else if LENGTH cl = 3 then
    check_unsat_2_sem fs (EL 1 cl) out
  else out = «»
End

Theorem STDIO_refl:
  STDIO A ==>>
  STDIO A * GC
Proof
  xsimpl
QED

Theorem main_spec:
  hasFreeFD fs
  ⇒
  app (p:'ffi ffi_proj) ^(fetch_v"main"(get_ml_prog_state()))
    [Conv NONE []]
    (COMMANDLINE cl * STDIO fs)
    (POSTv uv. &UNIT_TYPE () uv *
    COMMANDLINE cl *
    SEP_EXISTS out err.
      STDIO (add_stdout (add_stderr fs err) out) *
      &(main_sem fs cl out))
Proof
  rw[main_sem_def]>>
  xcf"main"(get_ml_prog_state())>>
  reverse (Cases_on `STD_streams fs`) >- (fs [TextIOProofTheory.STDIO_def] \\ xpull) >>
  reverse(Cases_on`wfcl cl`) >- (fs[COMMANDLINE_def] \\ xpull)>>
  rpt xlet_autop >>
  Cases_on `cl` >- fs[wfcl_def] >>
  Cases_on`t`>>fs[LIST_TYPE_def]
  >- (
    xmatch>>
    assume_tac (theorem "usage_string_v_thm")>>
    xlet_autop>>
    xapp_spec output_stderr_spec \\ xsimpl>>
    rename1`COMMANDLINE cl`>>
    qexists_tac`COMMANDLINE cl`>>xsimpl>>
    qexists_tac `mk_usage_string usage_string` >>
    simp [] >>
    qexists_tac`fs`>>xsimpl>>
    rw[]>>
    fs[STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil]>>
    metis_tac[STDIO_refl])>>
  Cases_on`t'`>>fs[LIST_TYPE_def]
  >- (
    xmatch>>
    xapp>>rw[]>>
    rpt(first_x_assum (irule_at Any)>>xsimpl)>>
    fs[wfcl_def]>>
    rw[]>>metis_tac[STDIO_refl])>>
  Cases_on`t`>>fs[LIST_TYPE_def]
  >- (
    xmatch>>
    xapp>>rw[]>>
    rpt(first_x_assum (irule_at Any)>>xsimpl)>>
    fs[wfcl_def]>>
    rw[]>>metis_tac[STDIO_refl])>>
  (*
  Cases_on`t'`>>fs[LIST_TYPE_def]
  >- (
    xmatch>>
    xapp>>rw[]>>
    rpt(first_x_assum (irule_at Any)>>xsimpl)>>
    fs[wfcl_def]>>
    rw[]>>metis_tac[STDIO_refl])>> *)
  xmatch>>
  assume_tac (theorem "usage_string_v_thm")>>
  xlet_autop>>
  xapp_spec output_stderr_spec \\ xsimpl>>
  rename1`COMMANDLINE cl`>>
  qexists_tac`COMMANDLINE cl`>>xsimpl>>
  qexists_tac `mk_usage_string usage_string` >>
  simp [] >>
  qexists_tac`fs`>>xsimpl>>
  rw[]>>
  fs[STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil]>>
  metis_tac[STDIO_refl]
QED

Theorem main_whole_prog_spec2:
   hasFreeFD fs ⇒
   whole_prog_spec2 main_v cl fs NONE
     (λfs'. ∃out err.
        fs' = add_stdout (add_stderr fs err) out ∧
        main_sem fs cl out)
Proof
  rw[basis_ffiTheory.whole_prog_spec2_def]
  \\ match_mp_tac (MP_CANON (DISCH_ALL (MATCH_MP app_wgframe (UNDISCH main_spec))))
  \\ xsimpl
  \\ rw[PULL_EXISTS]
  \\ qexists_tac`add_stdout (add_stderr fs x') x`
  \\ xsimpl
  \\ qexists_tac`x`
  \\ qexists_tac`x'`
  \\ xsimpl
  \\ simp[GSYM add_stdo_with_numchars,with_same_numchars]
QED

local

val name = "main"
val (sem_thm,prog_tm) =
  whole_prog_thm (get_ml_prog_state()) name (UNDISCH main_whole_prog_spec2)
Definition main_prog_def:
  main_prog = ^prog_tm
End

in

Theorem main_semantics =
  sem_thm
  |> REWRITE_RULE[GSYM main_prog_def]
  |> DISCH_ALL
  |> SIMP_RULE(srw_ss())[GSYM CONJ_ASSOC,AND_IMP_INTRO];

end
