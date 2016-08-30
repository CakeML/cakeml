open preamble
open reg_allocTheory reg_allocProofTheory state_transformerTheory
open ml_translatorLib ml_translatorTheory;
open inferProgTheory;

val _ = new_theory "reg_allocProg";

val _ = translation_extends "inferProg";

val _ = add_preferred_thy "-";
val _ = add_preferred_thy "termination";

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
  impl_tac>-
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
  impl_tac>-
    (rfs[]>>DECIDE_TAC)>>
  (*Prove that the clock decreases*)
  fsm[]>>ntac 2 strip_tac>>
  simp[Once whileTheory.WHILE,SimpRHS])

val _ = translate rpt_do_step2_alt

val briggs_coalesce_alt_lem = prove(
``∀s.
  MWHILE briggs_has_work do_briggs_step s =
  ((),WHILE (FST o briggs_has_work) (SND o do_briggs_step) s)``,
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

val briggs_coalesce_alt = prove(``
  briggs_coalesce = \s. ((),SND (set_unavail_moves [] (SND (set_move_rel LN (WHILE (FST o briggs_has_work) (SND o do_briggs_step) s)))))``,
  fs[FUN_EQ_THM,briggs_coalesce_def,IGNORE_BIND_DEF,BIND_DEF,UNCURRY,set_unavail_moves_def,set_move_rel_def]>>
  fs[briggs_coalesce_alt_lem])

val _ = translate briggs_coalesce_alt

(*Use the clock trick*)
val rpt_do_step_side = prove(``
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
val rpt_do_step2_side = prove(``
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
  impl_tac>-
    (rfs[]>>DECIDE_TAC)>>
  (*Prove that the clock decreases*)
  fsm[]>>ntac 2 strip_tac>>
  pop_assum(qspec_then`r` mp_tac)>>rfs[]>>
  IF_CASES_TAC>>fs[]>>
  `¬((FUNPOW (SND o do_step2) (SUC n) s).clock > 0)` by
    fs[FUNPOW]>>
  IF_CASES_TAC>>fs[]>>metis_tac[])|>update_precondition

val briggs_coalesce_side = prove(``
  ∀s. briggs_coalesce_side s ⇔ T``,
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

val _ = translate reg_alloc_def;

val () = Feedback.set_trace "TheoryPP.include_docs" 0;

val _ = export_theory();
