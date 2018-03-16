open preamble
open reg_allocTheory reg_allocProofTheory state_transformerTheory
open ml_monad_translatorLib ml_translatorTheory;
open inferProgTheory;

val _ = new_theory "reg_allocProg";

val _ = translation_extends "inferProg";

val _ = hide "state";

val _ = register_type ``:tag``;
val _ = register_type ``:clash_tree``;

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
    ("stack", get_stack_def, set_stack_def)
];

val rarrays_manip_list = [] : (string * thm * thm * thm * thm * thm * thm) list;
val farrays_manip_list = [
    ("adj_ls", get_adj_ls_def, set_adj_ls_def, adj_ls_length_def, adj_ls_sub_def, update_adj_ls_def),
    ("node_tag", get_node_tag_def, set_node_tag_def, node_tag_length_def, node_tag_sub_def, update_node_tag_def),
    ("degrees", get_degrees_def, set_degrees_def, degrees_length_def, degrees_sub_def, update_degrees_def)
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
val _ = m_translate st_ex_FOREACH_def
val _ = m_translate st_ex_MAP_def
val _ = m_translate st_ex_PARTITION_def
val _ = m_translate st_ex_FILTER_def

val _ = translate list_remap_def
val _ = translate mk_bij_aux_def

val _ = translate mk_bij_def
val _ = translate is_phy_var_def
val _ = translate sp_default_def
val _ = translate extract_tag_def
val _ = translate fromAList_def

val _ = m_translate dec_deg_def
val _ = m_translate dec_degree_def
val _ = m_translate add_simp_wl_def
val _ = m_translate add_stack_def
val _ = m_translate split_degree_def
val _ = m_translate unspill_def
val _ = m_translate do_simplify_def
val _ = m_translate st_ex_list_MAX_deg_def
val _ = m_translate do_spill_def
val _ = m_translate do_step_def
val _ = m_translate rpt_do_step_def
val _ = m_translate remove_colours_def
val _ = m_translate assign_Atemp_tag_def
val _ = m_translate assign_Atemps_def

val _ = translate tag_col_def
val _ = translate unbound_colour_def

val _ = m_translate assign_Stemp_tag_def
val _ = m_translate assign_Stemps_def
val _ = m_translate (first_match_col_def |> REWRITE_RULE [MEMBER_INTRO])
val _ = m_translate biased_pref_def
val _ = m_translate (insert_edge_def |> REWRITE_RULE [MEMBER_INTRO])
val _ = m_translate list_insert_edge_def
val _ = m_translate clique_insert_edge_def
val _ = m_translate (extend_clique_def |> REWRITE_RULE [MEMBER_INTRO])
val _ = m_translate (mk_graph_def |> REWRITE_RULE [MEMBER_INTRO])
val _ = m_translate extend_graph_def
val _ = m_translate mk_tags_def
val _ = m_translate init_ra_state_def
val _ = m_translate is_Atemp_def
val _ = m_translate init_alloc1_heu_def
val _ = m_translate do_alloc1_def
val _ = m_translate extract_color_def

val _ = translate pri_move_insert_def
val _ = translate undir_move_insert_def
val _ = translate moves_to_sp_def
val _ = translate resort_moves_def
val _ = m_translate do_reg_alloc_def

(* Finish the monadic translation *)
(* Rewrite reg_alloc_aux before giving it to the monadic translator *)
val reg_alloc_aux_trans_def = Q.prove(
 `∀k mtable ct forced x.
     reg_alloc_aux k mtable ct forced x =
     run_ira_state (do_reg_alloc k mtable ct forced x)
       <|adj_ls := (SND(SND x),[]); node_tag := (SND(SND x),Atemp); degrees := (SND(SND x),0);
         dim := SND(SND x); simp_wl := []; spill_wl := []; stack := []|>`,
 Cases_on `x` >> Cases_on `r` >> fs[reg_alloc_aux_def]);

val _ = m_translate_run reg_alloc_aux_trans_def

(* The final function used by the compiler *)
val _ = translate reg_alloc_def

val () = Feedback.set_trace "TheoryPP.include_docs" 0;

val _ = export_theory();

(*
TODO: update the following code (comes from the non-monadic register allocator

misc code to generate the unverified register allocator in SML

(* This normally gets generated inside word_alloc's translation *)
val _ = translate (clash_tree_to_spg_def |> REWRITE_RULE [MEMBER_INTRO])

open ml_progLib astPP

val ML_code_prog =
  get_ml_prog_state ()
  |> clean_state |> remove_snocs
  |> get_thm

val prog = ML_code_prog |> concl |> strip_comb |> #2 |> el 3

val _ = enable_astPP()

val _ = trace("pp_avoids_symbol_merges",0)
val t = TextIO.openOut("reg_alloc.sml")
val _ = TextIO.output(t,term_to_string prog)
val _ = TextIO.closeOut(t)

*)

val _ = (ml_translatorLib.clean_on_exit := true);

val _ = export_theory();
