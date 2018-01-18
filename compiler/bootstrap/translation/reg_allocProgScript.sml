open preamble
open reg_allocMonadTheory reg_allocMonadProofTheory state_transformerTheory
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

val STATE_EXN_TYPE_def =  theorem "REG_ALLOCMONAD_STATE_EXN_TYPE_def"
val exn_ri_def         = STATE_EXN_TYPE_def;
val store_hprop_name   = "RA_STATE";

(* Accessor functions are defined (and used) previously together
   with exceptions, etc. *)

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

val _ = export_theory();


(* val _ = new_theory "reg_allocProg";

val _ = translation_extends "inferProg";

val _ = add_preferred_thy "-";
val _ = add_preferred_thy "termination";

val NOT_NIL_AND_LEMMA = Q.prove(
  `(b <> [] /\ x) = if b = [] then F else x`,
  Cases_on `b` THEN FULL_SIMP_TAC std_ss []);

val extra_preprocessing = ref [MEMBER_INTRO,MAP];

fun def_of_const tm = let
  val res = dest_thy_const tm handle HOL_ERR _ =>
              failwith ("Unable to is_translated: " ^ term_to_string tm)
  val name = (#Name res)
  fun def_from_thy thy name =
    DB.fetch thy (name ^ "_pmatch") handle HOL_ERR _ =>
    DB.fetch thy (name ^ "_def") handle HOL_ERR _ =>
    DB.fetch thy (name ^ "_DEF") handle HOL_ERR _ =>
    DB.fetch thy name
  val def = def_from_thy "reg_alloc" name handle HOL_ERR _ =>
            def_from_thy (#Thy res) name handle HOL_ERR _ =>
            failwith ("Unable to find definition of " ^ name)
  val def = def |> REWRITE_RULE(!extra_preprocessing)
                |> CONV_RULE (DEPTH_CONV BETA_CONV)
                |> SIMP_RULE bool_ss [IN_INSERT,NOT_IN_EMPTY]
                |> REWRITE_RULE [NOT_NIL_AND_LEMMA]
  in def end

val _ = (find_def_for_const := def_of_const);

(* Translation of the register allocator requires some termination proofs *)
fun fsm ls = fs (ls@[BIND_DEF,UNIT_DEF,IGNORE_BIND_DEF,FOREACH_def]);

(*Use WHILE which is already is_translatedd in the prelude*)
val rpt_do_step_alt = Q.prove(`
  rpt_do_step = \s. ((),WHILE (FST o has_work) (SND o do_step) s)`,
  fs[FUN_EQ_THM,rpt_do_step_def]>>
  completeInduct_on`s.clock`>>
  rw[]>>
  fs[Once whileTheory.WHILE]>>
  Q.ISPECL_THEN [`has_work`,`do_step`] assume_tac MWHILE_DEF>>
  pop_assum (SUBST1_TAC)>>
  fsm[has_work_def,get_clock_def]>>
  IF_CASES_TAC>>fsm[]>>
  Cases_on`do_step s`>>
  first_x_assum(qspec_then`r.clock` mp_tac)>>
  Q.ISPECL_THEN [`s`,`s.graph`,`r`] mp_tac do_step_clock_lemma>>
  (*Need to use a different lemma without undir_graph assumption*)
  impl_tac>-
    (rfs[]>>DECIDE_TAC)>>
  (*Prove that the clock decreases*)
  fsm[]>>ntac 2 strip_tac>>
  simp[Once whileTheory.WHILE,SimpRHS])

val _ = is_translated rpt_do_step_alt

val rpt_do_step2_alt = Q.prove(`
  rpt_do_step2 = \s. ((),WHILE (FST o has_work) (SND o do_step2) s)`,
  fs[FUN_EQ_THM,rpt_do_step2_def]>>
  completeInduct_on`s.clock`>>
  rw[]>>
  fs[Once whileTheory.WHILE]>>
  Q.ISPECL_THEN [`has_work`,`do_step2`] assume_tac MWHILE_DEF>>
  pop_assum (SUBST1_TAC)>>
  fsm[has_work_def,get_clock_def]>>
  IF_CASES_TAC>>fsm[]>>
  Cases_on`do_step2 s`>>
  first_x_assum(qspec_then`r.clock` mp_tac)>>
  Q.ISPECL_THEN [`s`,`s.graph`,`r`] mp_tac do_step2_clock_lemma>>
  impl_tac>-
    (rfs[]>>DECIDE_TAC)>>
  (*Prove that the clock decreases*)
  fsm[]>>ntac 2 strip_tac>>
  simp[Once whileTheory.WHILE,SimpRHS])

val _ = is_translated rpt_do_step2_alt

val briggs_coalesce_alt_lem = Q.prove(
`∀s.
  MWHILE briggs_has_work do_briggs_step s =
  ((),WHILE (FST o briggs_has_work) (SND o do_briggs_step) s)`,
  completeInduct_on`s.clock`>>rw[]>>
  fs[Once whileTheory.WHILE]>>
  Q.ISPECL_THEN [`briggs_has_work`,`do_briggs_step`] assume_tac MWHILE_DEF>>
  pop_assum (SUBST1_TAC)>>
  fsm[briggs_has_work_def,get_clock_def,get_avail_moves_def,get_avail_moves_pri_def]>>
  IF_CASES_TAC>>fsm[PULL_FORALL]>>
  Cases_on`do_briggs_step s`>>
  first_x_assum(qspec_then`r` mp_tac)>>
  fsm[do_briggs_step_clock_lemma]>>
  strip_tac>>
  simp[Once whileTheory.WHILE,SimpRHS])

val briggs_coalesce_alt = Q.prove(`
  briggs_coalesce = \s. ((),SND (set_unavail_moves [] (SND (set_move_rel LN (WHILE (FST o briggs_has_work) (SND o do_briggs_step) s)))))`,
  fs[FUN_EQ_THM,briggs_coalesce_def,IGNORE_BIND_DEF,BIND_DEF,UNCURRY,set_unavail_moves_def,set_move_rel_def]>>
  fs[briggs_coalesce_alt_lem])

val _ = is_translated briggs_coalesce_alt

(*Use the clock trick*)
val rpt_do_step_side = Q.prove(`
  ∀s. rpt_do_step_side s ⇔ T`,
  fsm[fetch "-" "rpt_do_step_side_def"]>>
  completeInduct_on`s.clock`>>
  rw[]>>
  fsm[whileTheory.OWHILE_def]>>
  Cases_on`s.clock = 0`>>
  fsm[has_work_def,get_clock_def]>-
    (IF_CASES_TAC>>fsm[]>>pop_assum (qspec_then `0` assume_tac)>>
    fsm[FUNPOW]>>DECIDE_TAC)>>
  Cases_on`do_step s`>>
  first_x_assum(qspec_then`r.clock` mp_tac)>>
  Q.ISPECL_THEN [`s`,`s.graph`,`r`] mp_tac do_step_clock_lemma>>
  (*Need to use a different lemma without undir_graph assumption*)
  impl_tac>-
    (rfs[]>>DECIDE_TAC)>>
  (*Prove that the clock decreases*)
  fsm[]>>ntac 2 strip_tac>>
  pop_assum(qspec_then`r` mp_tac)>>rfs[]>>
  IF_CASES_TAC>>fs[]>>
  `¬((FUNPOW (SND o do_step) (SUC n) s).clock > 0)` by
    fs[FUNPOW]>>
  IF_CASES_TAC>>fs[]>>metis_tac[])|>update_precondition

(*Use the clock trick*)
val rpt_do_step2_side = Q.prove(`
  ∀s. rpt_do_step2_side s ⇔ T`,
  fsm[fetch "-" "rpt_do_step2_side_def"]>>
  completeInduct_on`s.clock`>>
  rw[]>>
  fsm[whileTheory.OWHILE_def]>>
  Cases_on`s.clock = 0`>>
  fsm[has_work_def,get_clock_def]>-
    (IF_CASES_TAC>>fsm[]>>pop_assum (qspec_then `0` assume_tac)>>
    fsm[FUNPOW]>>DECIDE_TAC)>>
  Cases_on`do_step2 s`>>
  first_x_assum(qspec_then`r.clock` mp_tac)>>
  Q.ISPECL_THEN [`s`,`s.graph`,`r`] mp_tac do_step2_clock_lemma>>
  (*Need to use a different lemma without undir_graph assumption*)
  impl_tac>-
    (rfs[]>>DECIDE_TAC)>>
  (*Prove that the clock decreases*)
  fsm[]>>ntac 2 strip_tac>>
  pop_assum(qspec_then`r` mp_tac)>>rfs[]>>
  IF_CASES_TAC>>fs[]>>
  `¬((FUNPOW (SND o do_step2) (SUC n) s).clock > 0)` by
    fs[FUNPOW]>>
  IF_CASES_TAC>>fs[]>>metis_tac[])|>update_precondition

val briggs_coalesce_side = Q.prove(`
  ∀s. briggs_coalesce_side s ⇔ T`,
  fsm[fetch "-" "briggs_coalesce_side_def"]>>
  completeInduct_on`s.clock`>>
  rw[]>>
  fsm[whileTheory.OWHILE_def]>>
  reverse (Cases_on`FST(briggs_has_work s)`)>>
  fsm[briggs_has_work_def,get_clock_def,get_avail_moves_def,get_avail_moves_pri_def]>>
  TRY
    (IF_CASES_TAC>>fsm[]>>pop_assum (qspec_then `0` assume_tac)>>
    fsm[FUNPOW]>>rfs[]>>DECIDE_TAC)>>
  Cases_on`do_briggs_step s`>>
  first_x_assum(qspec_then`r.clock` mp_tac)>>
  Q.ISPECL_THEN [`s`,`s.graph`,`r`] mp_tac do_briggs_step_clock_lemma>>
  (impl_tac>-
    (rfs[]>>DECIDE_TAC))>>
  fsm[]>>ntac 2 strip_tac>>
  pop_assum(qspec_then`r` mp_tac)>>rfs[]>>
  IF_CASES_TAC>>fs[]>>
  `¬((FUNPOW (SND o do_briggs_step) (SUC n) s).clock > 0) ∨
  (FUNPOW (SND o do_briggs_step) (SUC n) s).avail_moves = [] ∧
  (FUNPOW (SND o do_briggs_step) (SUC n) s).avail_moves_pri = []` by
    fs[FUNPOW]>>
  IF_CASES_TAC>>fs[]>>metis_tac[])|>update_precondition

val _ = is_translated init_ra_state_def

val init_ra_state_side_def = Q.prove(`
  ∀a b c. init_ra_state_side a b c ⇔ T`,
  fs[fetch "-" "init_ra_state_side_def"]>>rw[]>>
  fs[MEM_FILTER,MEM_MAP]>>Cases_on`y`>>
  fs[MEM_toAList]) |> update_precondition

val _ = is_translated (sec_ra_state_def |> REWRITE_RULE[MEMBER_INTRO])

val sec_ra_state_side_def = Q.prove(`
  ∀a b c d. sec_ra_state_side a b c d ⇔ T`,
  fs[fetch "-" "sec_ra_state_side_def"]>>rw[]>>
  fs[MEM_FILTER,MEM_MAP,quantHeuristicsTheory.IS_SOME_EQ_NOT_NONE])
  |>update_precondition

val _ = is_translated reg_alloc_def;

val () = Feedback.set_trace "TheoryPP.include_docs" 0;

(*
misc code to generate the unverified register allocator in SML

(* This normally gets generated inside word_alloc's translation *)
val _ = is_translated (clash_tree_to_spg_def |> REWRITE_RULE [MEMBER_INTRO])

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
*)
