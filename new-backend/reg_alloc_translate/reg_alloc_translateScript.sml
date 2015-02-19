open HolKernel Parse boolLib bossLib;
open listTheory arithmeticTheory ml_translatorLib mini_preludeTheory listLib;
open reg_allocTheory word_procTheory sortingTheory ml_translatorTheory
open sptreeTheory state_transformerTheory
open astPP
open lcsymtacs numeralTheory pred_setTheory
open miscLib BasicProvers

val _ = new_theory "reg_alloc_translate";

val _ = std_preludeLib.std_prelude ();

val _ = add_preferred_thy "reg_alloc";
val _ = add_preferred_thy "word_proc";

val _ = enable_astPP();

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
            def_from_thy "word_proc" name handle HOL_ERR _ =>
            def_from_thy (#Thy res) name handle HOL_ERR _ =>
            failwith ("Unable to find definition of " ^ name)
  val def = def |> RW (!extra_preprocessing)
                |> CONV_RULE (DEPTH_CONV BETA_CONV)
                |> SIMP_RULE bool_ss [IN_INSERT,NOT_IN_EMPTY]
                |> RW [NOT_NIL_AND_LEMMA]
  in def end

val _ = (find_def_for_const := def_of_const);

(* translation *)
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
  Q.ISPECL_THEN [`s`,`s.graph`,`r`] mp_tac do_step_graph_lemma>>
  (*Need to use a different lemma without undir_graph assumption*)
  discharge_hyps>- cheat>>
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
  discharge_hyps>- cheat>>
  (*Prove that the clock decreases*)
  fsm[]>>strip_tac>>
  simp[Once whileTheory.WHILE,SimpRHS])

val _ = translate rpt_do_step2_alt

(*Use the clock trick*)
val rpt_do_step_side_def = prove(``
  ∀s. rpt_do_step_side s ⇔ T``,cheat)|>update_precondition

(*Use the clock trick*)
val rpt_do_step2_side_def = prove(``
  ∀s. rpt_do_step2_side s ⇔ T``,cheat) |> update_precondition

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
  
val irc_alloc_def =  Define`
  irc_alloc G k moves =
  let s = init_ra_state G k moves in
  let s = SND (rpt_do_step s) in
  let coalesced = s.coalesced in
  let pref x y z = aux_move_pref coalesced (resort_moves(moves_to_sp moves LN)) x y z in
  let (col,ls) = alloc_coloring s.graph k pref s.stack in
  let (G,spills,coalesce_map) = full_coalesce s.graph moves ls in
  let s = sec_ra_state G k spills coalesce_map in
  let s = SND (rpt_do_step2 s) in
  let col = spill_coloring G k coalesce_map s.stack col in
  let col = spill_coloring G k LN ls col in
    col`

(*Prove that irc alloc is an instance of the actual algorithm*)
val irc_alloc_reg_alloc_3 = prove(``
  ∀G k moves.
  irc_alloc G k moves = reg_alloc 3 G k moves``,
  fs[irc_alloc_def,reg_alloc_def]>>
  rw[]>>
  `pref = pref'` by 
    (fs[FUN_EQ_THM]>>
    unabbrev_all_tac>>fs[])>>
  unabbrev_all_tac>>
  fs[]>>rfs[]>>
  rpt VAR_EQ_TAC>>
  fs[])

val _ = translate irc_alloc_def

val _ = set_trace "pp_avoids_symbol_merges" 0;

val _ = export_theory();
