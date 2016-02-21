open preamble
open ml_translatorLib mini_preludeTheory listLib;
open reg_allocTheory reg_allocProofTheory state_transformerTheory
open astPP ml_translatorTheory
open lcsymtacs

val _ = new_theory "reg_alloc_translate";

val _ = std_preludeLib.std_prelude ();

val _ = add_preferred_thy "reg_alloc";

val _ = set_trace "Goalstack.print_goal_at_top" 0; (*/"*)

val NOT_NIL_AND_LEMMA = prove(
  ``(b <> [] /\ x) = if b = [] then F else x``,
  Cases_on `b` THEN FULL_SIMP_TAC std_ss []);

val extra_preprocessing = ref [MEMBER_INTRO,MAP];

fun def_of_const tm = let
  val res = dest_thy_const tm handle HOL_ERR _ =>
              failwith ("Unable to translate: " ^ term_to_string tm)
  val name = (#Name res)
  fun def_from_thy thy name =
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

(*Use WHILE which is already translated in the prelude*)
val rpt_do_step_alt = prove(``
  rpt_do_step = \s. ((),WHILE (FST o has_work) (SND o do_step) s)``,
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
  discharge_hyps>- 
    (rfs[]>>DECIDE_TAC)>>
  (*Prove that the clock decreases*)
  fsm[]>>ntac 2 strip_tac>>
  simp[Once whileTheory.WHILE,SimpRHS])

val _ = translate rpt_do_step_alt

val rpt_do_step2_alt = prove(``
  rpt_do_step2 = \s. ((),WHILE (FST o has_work) (SND o do_step2) s)``,
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
  discharge_hyps>- 
    (rfs[]>>DECIDE_TAC)>>
  (*Prove that the clock decreases*)
  fsm[]>>ntac 2 strip_tac>>
  simp[Once whileTheory.WHILE,SimpRHS])

val _ = translate rpt_do_step2_alt

(*Use the clock trick*)
val rpt_do_step_side_def = prove(``
  ∀s. rpt_do_step_side s ⇔ T``,
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
  discharge_hyps>- 
    (rfs[]>>DECIDE_TAC)>>
  (*Prove that the clock decreases*)
  fsm[]>>ntac 2 strip_tac>>
  pop_assum(qspec_then`r` mp_tac)>>rfs[]>>
  IF_CASES_TAC>>fs[]>>
  `¬((FUNPOW (SND o do_step) (SUC n) s).clock > 0)` by
    fs[FUNPOW]>>
  IF_CASES_TAC>>fs[]>>metis_tac[])|>update_precondition

(*Use the clock trick*)
val rpt_do_step2_side_def = prove(``
  ∀s. rpt_do_step2_side s ⇔ T``,
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
  discharge_hyps>- 
    (rfs[]>>DECIDE_TAC)>>
  (*Prove that the clock decreases*)
  fsm[]>>ntac 2 strip_tac>>
  pop_assum(qspec_then`r` mp_tac)>>rfs[]>>
  IF_CASES_TAC>>fs[]>>
  `¬((FUNPOW (SND o do_step2) (SUC n) s).clock > 0)` by
    fs[FUNPOW]>>
  IF_CASES_TAC>>fs[]>>metis_tac[])|>update_precondition

val _ = translate init_ra_state_def

val init_ra_state_side_def = prove(``
  ∀a b c. init_ra_state_side a b c ⇔ T``,
  fs[fetch "-" "init_ra_state_side_def"]>>rw[]>>
  fs[MEM_FILTER,MEM_MAP]>>Cases_on`y`>>
  fs[MEM_toAList]) |> update_precondition

val _ = translate (sec_ra_state_def |> REWRITE_RULE[MEMBER_INTRO])

val sec_ra_state_side_def = prove(``
  ∀a b c d. sec_ra_state_side a b c d ⇔ T``,
  fs[fetch "-" "sec_ra_state_side_def"]>>rw[]>>
  fs[MEM_FILTER,MEM_MAP,quantHeuristicsTheory.IS_SOME_EQ_NOT_NONE])
  |>update_precondition

(*Specialized interface to allocator for unverified translation*)
val irc_alloc_def = Define`
  irc_alloc clash_sets k moves =
  let G = clash_sets_to_sp_g clash_sets in
  let moves = MAP maybe_flip moves in
  let s = init_ra_state G k moves in
  let ((),s) = rpt_do_step s in
  let pref = aux_move_pref s.coalesced (resort_moves(moves_to_sp moves LN)) in
  let (col,ls) = alloc_colouring s.graph k pref s.stack in
  let (G,spills,coalesce_map) = full_coalesce s.graph k moves ls in
  let s = sec_ra_state G k spills coalesce_map in
  let ((),s) = rpt_do_step2 s in
  let col = spill_colouring G k coalesce_map s.stack col in
  let col = spill_colouring G k LN ls col in
    col`

(*Prove that irc alloc is an instance of the actual algorithm*)
val irc_alloc_reg_alloc_3 = prove(``
  ∀G k moves.
  irc_alloc ls k moves = reg_alloc 3 (clash_sets_to_sp_g ls) k moves``,
  fs[irc_alloc_def,reg_alloc_def])

val _ = translate irc_alloc_def

(*Dump to file*)
(*
val _ = enable_astPP();
val _ = set_trace "pp_avoids_symbol_merges" 0;

val _ = let
val file = TextIO.openOut "reg_alloc_poly.sml"
fun print s = TextIO.output(file,s)
val _ = finalise_translation()
val decls = get_decls()
in
  print (term_to_string decls)
end

val _ = disable_astPP();
*)

(*val _ = Feedback.set_trace "TheoryPP.include_docs" 0;*)
val _ = ml_translatorLib.print_asts:=true;

val _ = export_theory();
