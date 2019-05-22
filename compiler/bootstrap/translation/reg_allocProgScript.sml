(*
  Translate the compiler's register allocator.
*)
open preamble
open reg_allocTheory reg_allocProofTheory state_transformerTheory
open ml_monad_translatorLib ml_translatorTheory;
open parserProgTheory;

(*
open basisProgTheory
*)

val _ = new_theory "reg_allocProg";

val _ = translation_extends "parserProg";
(*
val _ = translation_extends "basisProg";
*)

val _ = monadsyntax.temp_add_monadsyntax()

val _ = temp_overload_on ("monad_bind", ``st_ex_bind``);
val _ = temp_overload_on ("monad_unitbind", ``\x y. st_ex_bind x (\z. y)``);
val _ = temp_overload_on ("monad_ignore_bind", ``\x y. st_ex_bind x (\z. y)``);
val _ = temp_overload_on ("return", ``st_ex_return``);

val _ = hide "state";

val _ = register_type ``:tag``;
val _ = register_type ``:clash_tree``;
val _ = register_type ``:algorithm``;

val res = translate sortingTheory.PART_DEF;
val res = translate sortingTheory.PARTITION_DEF;

(*
 *  Set up the monadic translator
 *)

(* The record types used for the monadic state and exceptions *)
val state_type = ``:ra_state``;
val exn_type   = ``:state_exn``;
val _          = register_exn_type exn_type;

val STATE_EXN_TYPE_def =  theorem "REG_ALLOC_STATE_EXN_TYPE_def"
val exn_ri_def         = STATE_EXN_TYPE_def;
val store_hprop_name   = "RA_STATE";

(* Accessor functions are defined (and used) previously together
   with exceptions, etc. *)

val exn_functions = [
    (raise_Fail_def, handle_Fail_def),
    (raise_Subscript_def, handle_Subscript_def)
];

val refs_manip_list = [
    ("dim", get_dim_def, set_dim_def),
    ("simp_wl", get_simp_wl_def, set_simp_wl_def),
    ("spill_wl", get_spill_wl_def, set_spill_wl_def),
    ("freeze_wl", get_freeze_wl_def, set_freeze_wl_def),
    ("avail_moves_wl", get_avail_moves_wl_def, set_avail_moves_wl_def),
    ("unavail_moves_wl", get_unavail_moves_wl_def, set_unavail_moves_wl_def),
    ("stack", get_stack_def, set_stack_def)
];

val rarrays_manip_list = [] : (string * thm * thm * thm * thm * thm * thm) list;
val farrays_manip_list = [
    ("adj_ls", get_adj_ls_def, set_adj_ls_def, adj_ls_length_def, adj_ls_sub_def, update_adj_ls_def),
    ("node_tag", get_node_tag_def, set_node_tag_def, node_tag_length_def, node_tag_sub_def, update_node_tag_def),
    ("degrees", get_degrees_def, set_degrees_def, degrees_length_def, degrees_sub_def, update_degrees_def),
    ("coalesced", get_coalesced_def, set_coalesced_def, coalesced_length_def, coalesced_sub_def, update_coalesced_def),
    ("move_related", get_move_related_def, set_move_related_def, move_related_length_def, move_related_sub_def, update_move_related_def)
];

val add_type_theories  = ([] : string list);
val store_pinv_def_opt = NONE : thm option;

(* Initialization *)

val _ = start_dynamic_init_fixed_store_translation
            refs_manip_list
            rarrays_manip_list
            farrays_manip_list
            store_hprop_name
            state_type
            exn_ri_def
            exn_functions
            add_type_theories
            store_pinv_def_opt

(*
 * Translate the register allocator
 *)
val _ = m_translate st_ex_FOREACH_def;
val _ = m_translate st_ex_MAP_def;
val _ = m_translate st_ex_PARTITION_def;
val _ = m_translate st_ex_FILTER_def;

(* MISC stuff, for standalone translation only

val _ = translate lookup_def;
val _ = translate insert_def;
val _ = translate lrnext_def;
val _ = translate foldi_def;
val _ = translate toAList_def;
val _ = translate map_def;
val _ = translate COUNT_LIST_AUX_def
val _ = translate COUNT_LIST_compute

*)

val _ = translate list_remap_def;
val _ = translate mk_bij_aux_def;

val _ = translate mk_bij_def;
val _ = translate is_phy_var_def;
val _ = translate sp_default_def;
val _ = translate extract_tag_def;
val _ = translate fromAList_def;

val _ = m_translate dec_deg_def;
val _ = m_translate dec_degree_def;
val _ = m_translate add_simp_wl_def;
val _ = m_translate add_spill_wl_def;
val _ = m_translate add_freeze_wl_def;
val _ = m_translate push_stack_def;
val _ = m_translate add_unavail_moves_wl_def;

val _ = m_translate is_not_coalesced_def;
val _ = m_translate split_degree_def;
val _ = translate sort_moves_def;
val _ = translate smerge_def;

val rewrite_subs = Q.prove(`
  (st_ex_MAP adj_ls_sub = st_ex_MAP (\v. adj_ls_sub v)) ∧
  (st_ex_MAP node_tag_sub = st_ex_MAP (\v. node_tag_sub v)) ∧
  (st_ex_PARTITION move_related_sub = st_ex_PARTITION (\v. move_related_sub v)) ∧
  (st_ex_MAP degrees_sub = st_ex_MAP (\v. degrees_sub v)) ∧
  (st_ex_FILTER (considered_var k) xs ys = st_ex_FILTER (\v. considered_var k v) xs ys) ∧
  (st_ex_MAP (deg_or_inf kk) xs = st_ex_MAP (\x. deg_or_inf kk x) xs)`,
  metis_tac[ETA_AX]);

val _ = translate sorted_mem_def;

val _ = m_translate (revive_moves_def |> REWRITE_RULE[rewrite_subs]);

val _ = m_translate (unspill_def |> REWRITE_RULE [rewrite_subs]);

val _ = m_translate do_simplify_def;
val _ = m_translate inc_deg_def;

val _ = translate sorted_insert_def;
val _ = m_translate (insert_edge_def)
val _ = m_translate list_insert_edge_def

val _ = m_translate is_Fixed_def;

val _ = m_translate (do_coalesce_real_def |> REWRITE_RULE [MEMBER_INTRO]);

val _ = m_translate is_Atemp_def;
val _ = m_translate is_Fixed_k_def;
val _ = m_translate deg_or_inf_def;
val _ = m_translate considered_var_def;

val _ = m_translate  (bg_ok_def |> REWRITE_RULE [MEMBER_INTRO,rewrite_subs])

(* TODO: something in the monadic translator automatically rewrites
  the ¬ (a ∧ b) check
  and then fails on the original def*)

val _ = m_translate (consistency_ok_def |> REWRITE_RULE [MEMBER_INTRO,
                           METIS_PROVE [] ``~(b1 /\ b2) <=> ~b1 \/ ~b2``]);

val _ = m_translate coalesce_parent_def;
val _ = m_translate canonize_move_def;
val _ = m_translate st_ex_FIRST_def;
val _ = m_translate (respill_def |> REWRITE_RULE [MEMBER_INTRO]);
val _ = m_translate do_coalesce_def;

val _ = m_translate reset_move_related_def;
val _ = m_translate (do_prefreeze_def |> REWRITE_RULE [rewrite_subs]);
val _ = m_translate do_freeze_def;

val _ = translate safe_div_def;
val _ = translate lookup_any_def;
val _ = m_translate st_ex_list_MIN_cost_def;
val _ = m_translate st_ex_list_MAX_deg_def;
val _ = m_translate do_spill_def;

val _ = m_translate (do_step_def |> SIMP_RULE std_ss []);

val _ = m_translate rpt_do_step_def;
val _ = m_translate remove_colours_def;
val _ = m_translate assign_Atemp_tag_def;
val _ = m_translate assign_Atemps_def;

val _ = translate tag_col_def;
val _ = translate unbound_colour_def;

val _ = m_translate (assign_Stemp_tag_def |> REWRITE_RULE [rewrite_subs]);
val _ = m_translate assign_Stemps_def;
val _ = m_translate (first_match_col_def |> REWRITE_RULE [MEMBER_INTRO]);
val _ = m_translate biased_pref_def;
val _ = m_translate clique_insert_edge_def;
val _ = m_translate (extend_clique_def |> REWRITE_RULE [MEMBER_INTRO]);
val _ = m_translate (mk_graph_def |> REWRITE_RULE [MEMBER_INTRO]);
val _ = m_translate extend_graph_def;
val _ = m_translate mk_tags_def;
val _ = m_translate init_ra_state_def;
val _ = m_translate do_upd_coalesce_def;
val _ = m_translate (init_alloc1_heu_def |> REWRITE_RULE [rewrite_subs]);
val _ = m_translate do_alloc1_def;
val _ = m_translate extract_color_def;

val _ = translate pri_move_insert_def;
val _ = translate undir_move_insert_def;
val _ = translate moves_to_sp_def;
val _ = translate resort_moves_def;

val _ = m_translate (full_consistency_ok_def |> REWRITE_RULE [MEMBER_INTRO,
                           METIS_PROVE [] ``~(b1 /\ b2) <=> ~b1 \/ ~b2``]);
val _ = translate update_move_def;
val _ = m_translate do_reg_alloc_def;

(* Finish the monadic translation *)
(* Rewrite reg_alloc_aux before giving it to the monadic translator *)
val reg_alloc_aux_trans_def = Q.prove(
 `∀k mtable ct forced x.
     reg_alloc_aux alg sc k mtable ct forced x =
     run_ira_state (do_reg_alloc alg sc k mtable ct forced x)
       <|adj_ls := (SND(SND x),[]);
         node_tag := (SND(SND x),Atemp);
         degrees := (SND(SND x),0);
         dim := SND(SND x);
         simp_wl := [];
         spill_wl := [];
         freeze_wl := [];
         avail_moves_wl := [];
         unavail_moves_wl := [];
         coalesced := (SND(SND x),0);
         move_related := (SND(SND x),F);
         stack := []|>`,
 Cases_on `x` >> Cases_on `r` >> fs[reg_alloc_aux_def]);

val def = reg_alloc_aux_trans_def
val _ = m_translate_run reg_alloc_aux_trans_def;

(* The final function used by the compiler *)
val _ = translate reg_alloc_def;


(* === Translation of linear scan register allocator === *)

open linear_scanTheory libTheory;

(*
 *  Set up the monadic translator
 *)


(* The record types used for the monadic state and exceptions *)
val state_type = ``:linear_scan_hidden_state``
val exn_type   = ``:state_exn``;
(* val _       = register_exn_type exn_type;  -- already registered above *)

val STATE_EXN_TYPE_def = theorem "REG_ALLOC_STATE_EXN_TYPE_def"
val exn_ri_def         = STATE_EXN_TYPE_def;
val store_hprop_name   = "LINEAR_SCAN_HIDDEN_STATE";

(* Accessor functions are defined (and used) previously together
   with exceptions, etc. *)

val exn_functions = [
    (raise_Fail_def, handle_Fail_def),
    (raise_Subscript_def, handle_Subscript_def)
];

val refs_manip_list = [] : (string * thm * thm) list;
val rarrays_manip_list = [] : (string * thm * thm * thm * thm * thm * thm) list;
val farrays_manip_list = [
    ("colors", get_colors_def, set_colors_def, colors_length_def, colors_sub_def, update_colors_def),
    ("int_beg", get_int_beg_def, set_int_beg_def, int_beg_length_def, int_beg_sub_def, update_int_beg_def),
    ("int_end", get_int_end_def, set_int_end_def, int_end_length_def, int_end_sub_def, update_int_end_def),
    ("sorted_regs", get_sorted_regs_def, set_sorted_regs_def, sorted_regs_length_def, sorted_regs_sub_def, update_sorted_regs_def),
    ("sorted_moves", get_sorted_moves_def, set_sorted_moves_def, sorted_moves_length_def, sorted_moves_sub_def, update_sorted_moves_def)
];

val add_type_theories  = ([] : string list);
val store_pinv_def_opt = NONE : thm option;

(* Initialization *)

val _ = start_dynamic_init_fixed_store_translation
            refs_manip_list
            rarrays_manip_list
            farrays_manip_list
            store_hprop_name
            state_type
            exn_ri_def
            [] (* exn_functions *)
            add_type_theories
            store_pinv_def_opt

(* Translate basics *)

val res = translate the_def;
val res = translate numset_list_delete_def;
val res = translate numset_list_insert_def;
val res = translate is_stack_var_def;
val res = translate is_phy_var_def;
val res = translate pairTheory.LEX_DEF;

(* Translate linear scan register allocator *)

val map_colors_sub_def = Define `
  (map_colors_sub [] = st_ex_return []) ∧
  (map_colors_sub (x::xs) =
     st_ex_bind (colors_sub x)
       (\fx. st_ex_bind (map_colors_sub xs)
               (\fxs. st_ex_return (fx::fxs))))`

Theorem map_colors_sub_eq:
   map_colors_sub = st_ex_MAP colors_sub
Proof
  once_rewrite_tac [FUN_EQ_THM]
  \\ Induct \\ fs [map_colors_sub_def,st_ex_MAP_def]
QED

val res = m_translate spill_register_def;
val res = m_translate MAP_colors_def;
val res = m_translate st_ex_FOLDL_def;
val res = m_translate map_colors_sub_def;
val res = m_translate remove_inactive_intervals_def;

val res = translate linear_reg_alloc_pass1_initial_state_def;
val res = translate linear_reg_alloc_pass2_initial_state_def;
val res = translate add_active_interval_def;
val res = translate find_color_in_list_def;
val res = translate find_color_in_colornum_def;
val res = translate find_color_def;
val res = m_translate color_register_def;
val res = m_translate find_last_stealable_def;
val res = m_translate find_spill_def;
val res = m_translate (linear_reg_alloc_step_aux_def
                       |> REWRITE_RULE [MEMBER_INTRO]);
val res = m_translate (linear_reg_alloc_step_pass1_def
                       |> REWRITE_RULE [GSYM map_colors_sub_eq]);
val res = m_translate (linear_reg_alloc_step_pass2_def
                       |> REWRITE_RULE [GSYM map_colors_sub_eq]);

val res = m_translate find_reg_exchange_def;
val res = m_translate apply_reg_exchange_def;

val res = m_translate list_to_sorted_regs_def;

val res = m_translate swap_regs_def;
val res = m_translate partition_regs_def;

val res = m_translate qsort_regs_def;
val res = m_translate sorted_regs_to_list_def;
val res = m_translate list_to_sorted_moves_def;

val res = m_translate swap_moves_def;
val res = m_translate partition_moves_def;
val res = m_translate qsort_moves_def;
val res = m_translate sorted_moves_to_list_def;

val res = m_translate edges_to_adjlist_def;
val res = m_translate st_ex_FILTER_good_def;

val res = m_translate (linear_reg_alloc_intervals_def)

val res = m_translate extract_coloration_def;
val res = translate find_bijection_init_def;
val res = translate find_bijection_step_def;
val res = translate apply_bijection_def;

val res = m_translate numset_list_add_if_lt_monad_def;
val res = m_translate numset_list_add_if_gt_monad_def;
val res = m_translate get_intervals_ct_monad_aux_def;
val res = m_translate get_intervals_ct_monad_def;
val res = m_translate linear_reg_alloc_and_extract_coloration_def;
val res = m_translate_run run_linear_reg_alloc_intervals_def;

val res = translate get_live_tree_def;
val res = translate get_live_backward_def;
val res = translate fix_domination_def;
val res = translate numset_list_add_if_def;
val res = translate numset_list_add_if_lt_def;
val res = translate numset_list_add_if_gt_def;
val res = translate get_intervals_def;
val res = translate find_bijection_clash_tree_def;
val res = translate apply_bij_on_clash_tree_def;
val res = translate size_of_clash_tree_def;
val res = translate linear_scan_reg_alloc_def;

val () = Feedback.set_trace "TheoryPP.include_docs" 0;

(*
TODO: update the following code (comes from the non-monadic register allocator

misc code to generate the unverified register allocator in SML

(* Not sure where this gets overwritten *)
val implode = String.implode;
val explode = String.explode;

open ml_progLib cfLib basis
open astPP

val main = process_topdecs`
  fun main u = ()`

val res = append_prog main;

val st =  get_ml_prog_state ();

Theorem main_whole_prog_spec:
   F ==> whole_prog_spec ^(fetch_v "main" st) cl fs NONE (\x. T)
Proof
  simp []
QED

val (_,prog_tm) = whole_prog_thm st "main" (UNDISCH main_whole_prog_spec);

val _ = enable_astPP()
val _ = Globals.max_print_depth:= ~1
val _ = trace("pp_avoids_symbol_merges",0)
val t = TextIO.openOut("reg_alloc.sml")
val _ = TextIO.output(t,term_to_string prog_tm)
val _ = TextIO.closeOut(t)
val _ = Globals.max_print_depth:= 20
val _ = disable_astPP()

*)

val _ = (ml_translatorLib.clean_on_exit := true);

val _ = export_theory();
