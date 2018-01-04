open preamble reg_allocMonadTheory
open ml_translatorTheory ml_translatorLib
open ml_monadStoreLib ml_monad_translatorTheory
open ml_monad_translatorLib

val _ = new_theory "reg_allocMonadProg"

val _ = hide "state";

(* ------------------------------------------------------------------------- *)
(* Translation                                                               *)
(* ------------------------------------------------------------------------- *)

(* Those calls to register_type should be removed once the monadic
   register allocater is integrated in the compiler *)
val _ = register_type ``:'a # 'b``;
val _ = register_type ``:'a list``;
val _ = register_type ``:'a option``;
val _ = register_type ``:unit``;
val _ = register_type ``:tag``;
val _ = register_type ``:clash_tree``;

(* Accessor functions are defined (and used) previously together
   with exceptions, etc. *)

val state_type = ``:ra_state``;
val exn_type   = ``:state_exn``;
val _          = register_exn_type exn_type;

val STATE_EXN_TYPE_def =  theorem "REG_ALLOCMONAD_STATE_EXN_TYPE_def"
val exn_ri_def         = STATE_EXN_TYPE_def;
val store_hprop_name   = "RA_STATE";

val exn_functions = [
    (raise_Fail_def, handle_Fail_def),
    (raise_ReadError_def, handle_ReadError_def),
    (raise_WriteError_def, handle_WriteError_def)
];

val refs_manip_list = [
    ("dim", get_dim_def, set_dim_def),
    ("simp_wl", get_simp_wl_def, set_simp_wl_def),
    ("spill_wl", get_spill_wl_def, set_spill_wl_def),
    ("stack", get_stack_def, set_stack_def)
];

val arrays_manip_list = [
    ("adj_ls", get_adj_ls_def, set_adj_ls_def, adj_ls_length_def, adj_ls_sub_def, update_adj_ls_def, alloc_adj_ls_def),
    ("node_tag", get_node_tag_def, set_node_tag_def, node_tag_length_def, node_tag_sub_def, update_node_tag_def, alloc_node_tag_def),
    ("degrees", get_degrees_def, set_degrees_def, degrees_length_def, degrees_sub_def, update_degrees_def, alloc_degrees_def)
];

val add_type_theories  = ([] : string list);
val store_pinv_def_opt = NONE : thm option;

(* Initialize the translation *)

val (trans_params, exn_specs) =
  start_dynamic_init_fixed_store_translation
    refs_manip_list
    arrays_manip_list
    store_hprop_name
    state_type
    exn_ri_def
    exn_functions
    add_type_theories
    store_pinv_def_opt;

(* Rest of the translation *)

val _ = m_translate st_ex_FOREACH_def;
val _ = m_translate st_ex_MAP_def;
val _ = m_translate st_ex_PARTITION_def;
val _ = m_translate st_ex_FILTER_def;

val _ = translate FST
val _ = translate EVEN
val _ = translate lookup_def
val _ = translate insert_def
val _ = translate list_remap_def
val _ = translate lrnext_def
val _ = translate foldi_def
val _ = translate toAList_def
val _ = translate MAP
val _ = translate mk_bij_aux_def
val _ = translate mk_bij_def
val _ = translate MEMBER_def
val _ = translate FILTER
val _ = translate SNOC
val _ = translate NULL
val _ = translate GENLIST
val _ = translate APPEND
val _ = translate PART_DEF
val _ = translate PARTITION_DEF
val _ = translate QSORT_DEF
val _ = translate lookup_any_def
val _ = translate sp_default_def
val _ = translate LENGTH
val _ = translate extract_tag_def
val _ = translate fromAList_def

val _ = m_translate dec_deg_def;
val _ = m_translate dec_degree_def;
val _ = m_translate add_simp_wl_def;
val _ = m_translate add_stack_def;
val _ = m_translate split_degree_def;
val _ = m_translate unspill_def;
val _ = m_translate do_simplify_def;
val _ = m_translate st_ex_list_MAX_deg_def;
val _ = m_translate do_spill_def;
val _ = m_translate do_step_def;
val _ = m_translate rpt_do_step_def;
val _ = m_translate remove_colours_def;
val _ = m_translate assign_Atemp_tag_def;
val _ = m_translate assign_Atemps_def;
val _ = translate tag_col_def
val _ = translate unbound_colour_def
val _ = m_translate assign_Stemp_tag_def;
val _ = m_translate assign_Stemps_def;
val _ = m_translate (first_match_col_def |> REWRITE_RULE [MEMBER_INTRO]);
val _ = m_translate biased_pref_def;
val _ = m_translate (insert_edge_def |> REWRITE_RULE [MEMBER_INTRO]);
val _ = m_translate list_insert_edge_def;
val _ = m_translate clique_insert_edge_def;
val _ = m_translate (extend_clique_def |> REWRITE_RULE [MEMBER_INTRO]);
val _ = m_translate (mk_graph_def |> REWRITE_RULE [MEMBER_INTRO]);
val _ = m_translate extend_graph_def;
val _ = m_translate mk_tags_def;
val _ = m_translate init_ra_state_def;
val _ = m_translate is_Atemp_def;
val _ = m_translate init_alloc1_heu_def
val _ = m_translate do_alloc1_def
val _ = m_translate extract_color_def;
val _ = m_translate do_reg_alloc_def;

(* m_translate_run *)

val r = translate empty_ra_state_def;
val r = m_translate_run reg_alloc_def;

val reg_alloc_side = Q.prove (
  `reg_alloc_side k mtable ct forced <=> T`,
  rw [fetch"-""reg_alloc_side_def", empty_ra_state_def])
  |> update_precondition;

val _ = export_theory();
