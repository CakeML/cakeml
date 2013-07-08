open HolKernel boolLib bossLib relationTheory lcsymtacs
open BytecodeTheory bytecodeTerminationTheory bytecodeEvalTheory bytecodeExtraTheory

val _ = new_theory"bytecodeClock"

val bc_fetch_with_clock = store_thm("bc_fetch_with_clock",
  ``bc_fetch (s with clock := ck) = bc_fetch s``,
  rw[bc_fetch_def])

val bc_find_loc_with_clock = store_thm("bc_find_loc_with_clock",
  ``bc_find_loc (s with clock := ck) = bc_find_loc s``,
  rw[FUN_EQ_THM]>>Cases_on`x`>>rw[bc_find_loc_def])

val bool_to_tag_equals = store_thm("bool_to_tag_equals",
  ``((1 = bool_to_tag b) ⇔ (b = T)) ∧
    ((0 = bool_to_tag b) ⇔ (b = F))``,
  Cases_on`b`>>rw[])

val bc_next_can_be_clocked = store_thm("bc_next_can_be_clocked",
  ``∀s1 s2. bc_next s1 s2 ⇒ ∃ck. bc_next (s1 with clock := SOME ck) (s2 with clock := SOME 0)``,
  ho_match_mp_tac bc_next_ind >> rw[] >>
  TRY(
    qexists_tac`0`>>
    simp[Once bc_next_cases,bc_fetch_with_clock,bc_fetch_with_stack,bump_pc_def,bc_find_loc_with_clock,bool_to_tag_equals] >>
    simp[bc_state_component_equality] >>
    NO_TAC) >>
  rw[Once bc_next_cases,bc_fetch_with_clock,bump_pc_def,bc_state_component_equality] >>
  qexists_tac`1`>>simp[])

val bc_next_add_clock = store_thm("bc_next_add_clock",
  ``∀s1 s2. bc_next s1 s2 ⇒ ∀n. bc_next (s1 with clock := OPTION_MAP ($+ n) s1.clock) (s2 with clock := OPTION_MAP ($+ n) s2.clock)``,
  ho_match_mp_tac bc_next_ind >> rw[] >>
  simp[Once bc_next_cases,bc_fetch_with_clock,bc_fetch_with_stack,bump_pc_def,bc_find_loc_with_clock,bool_to_tag_equals] >>
  simp[bc_state_component_equality] >>
  simp[optionTheory.OPTION_MAP_COMPOSE,combinTheory.o_DEF,arithmeticTheory.PRE_SUB1] >>
  Cases_on`s1.clock`>>fs[]>>simp[])

val RTC_bc_next_add_clock = store_thm("RTC_bc_next_add_clock",
  ``∀s1 s2. bc_next^* s1 s2 ⇒ ∀n. bc_next^* (s1 with clock := OPTION_MAP ($+ n) s1.clock) (s2 with clock := OPTION_MAP ($+ n) s2.clock)``,
  rw[] >> pop_assum mp_tac >>
  qho_match_abbrev_tac`R^* s1 s2 ⇒ R^* (f s1) (f s2)` >>
  map_every qid_spec_tac [`s2`,`s1`] >>
  match_mp_tac RTC_lifts_monotonicities >>
  simp[bc_next_add_clock,Abbr`R`,Abbr`f`])

val RTC_bc_next_can_be_clocked = store_thm("RTC_bc_next_can_be_clocked",
  ``∀s1 s2. RTC bc_next s1 s2 ⇒ ∃ck. RTC bc_next (s1 with clock := SOME ck) (s2 with clock := SOME 0)``,
  qho_match_abbrev_tac`∀s1 s2. RTC bc_next s1 s2 ⇒ Q s1 s2` >>
  mp_tac(Q.ISPECL[`bc_next`,`I:bc_state->bc_state`,`Q:bc_state->bc_state->bool`]
    (Q.GENL[`Q`,`f`,`R`]RTC_lifts_reflexive_transitive_relations)) >>
  simp[] >> disch_then match_mp_tac >>
  simp[Abbr`Q`] >>
  conj_tac >- metis_tac[bc_next_can_be_clocked,RTC_SUBSET]>>
  conj_tac >- (simp[reflexive_def]>>gen_tac>>qexists_tac`0`>>simp[])>>
  rw[transitive_def] >>
  imp_res_tac RTC_bc_next_add_clock >> fs[] >>
  metis_tac[RTC_TRANSITIVE,transitive_def])

val bc_next_can_be_unclocked = store_thm("bc_next_can_be_unclocked",
  ``∀s1 s2. bc_next s1 s2 ⇒ bc_next (s1 with clock := NONE) (s2 with clock := NONE)``,
  ho_match_mp_tac bc_next_ind >> rw[] >>
  simp[Once bc_next_cases,bc_fetch_with_clock,bc_fetch_with_stack,bump_pc_def,bc_find_loc_with_clock,bool_to_tag_equals] >>
  simp[bc_state_component_equality])

val RTC_bc_next_can_be_unclocked = store_thm("RTC_bc_next_can_be_unclocked",
  ``∀s1 s2. bc_next^* s1 s2 ⇒ bc_next^* (s1 with clock := NONE) (s2 with clock := NONE)``,
  rw[] >> pop_assum mp_tac >>
  qho_match_abbrev_tac`R^* s1 s2 ⇒ R^* (f s1) (f s2)` >>
  map_every qid_spec_tac [`s2`,`s1`] >>
  match_mp_tac RTC_lifts_monotonicities >>
  simp[bc_next_can_be_unclocked,Abbr`R`,Abbr`f`])

val RTC_bc_next_determ = store_thm("RTC_bc_next_determ",
  ``∀s1 s2. bc_next^* s1 s2 ⇒ (∀s4. ¬bc_next s2 s4) ⇒ ∀s3. bc_next^* s1 s3 ∧ (∀s4. ¬bc_next s3 s4) ⇒ s2 = s3``,
  ho_match_mp_tac RTC_INDUCT >>
  reverse conj_tac >- (
    rw[] >> fs[] >>
    qpat_assum`bc_next^* s1 s3`mp_tac >>
    simp[Once RTC_CASES1] >>
    Cases_on`s1 = s3`>>fs[] >>
    fs[bc_eval1_thm] ) >>
  rw[Once RTC_CASES1])

val bc_next_not_Tick_same_clock = store_thm("bc_next_not_Tick_same_clock",
  ``∀s1 s2. bc_next s1 s2 ⇒ ∀ck. s1.clock = SOME ck ∧ bc_fetch s1 ≠ SOME Tick ⇒ s2.clock = SOME ck``,
  ho_match_mp_tac bc_next_ind >> simp[bump_pc_def] >>
  rw[] >> simp[bc_fetch_with_stack])

val bc_next_not_Tick_any_clock = store_thm("bc_next_not_Tick_any_clock",
  ``∀s1 s2. bc_next s1 s2 ⇒ bc_fetch s1 ≠ SOME Tick ⇒ ∀ck'. bc_next (s1 with clock := ck') (s2 with clock := ck')``,
  ho_match_mp_tac bc_next_ind >> rw[] >>
  rw[bc_eval1_thm,bc_eval1_def,bc_fetch_with_clock,LET_THM] >>
  rw[bump_pc_def,bc_fetch_with_clock,bc_state_component_equality,bc_find_loc_with_clock,bc_fetch_with_stack] >>
  fs[bc_eval_stack_thm,bc_find_loc_with_clock] >> simp[] >>
  simp[EL_REVERSE,PRE_SUB1,EL_APPEND1,EL_LENGTH_APPEND_rwt,bc_state_component_equality] >>
  simp[REVERSE_APPEND,TAKE_APPEND1,TAKE_REVERSE] >>
  metis_tac[LASTN_LENGTH_ID])

val RTC_bc_next_less_timeout = store_thm("RTC_bc_next_less_timeout",
  ``∀s1 s2. bc_next^* s1 s2 ⇒
      ∀ck. s1.clock = SOME ck ∧ bc_fetch s2 = SOME Tick ∧ s2.clock = SOME 0 ⇒
         ∀ck'. ck' ≤ ck ⇒
           ∃s2'. bc_next^* (s1 with clock := SOME ck') s2' ∧
                 bc_fetch s2' = SOME Tick ∧ s2'.clock = SOME 0``,
  ho_match_mp_tac RTC_INDUCT >>
  conj_tac >- (
    rw[] >> fs[] >> rw[] >> fs[] >>
    qexists_tac`s1 with clock := SOME 0` >>
    simp[bc_fetch_with_clock] ) >>
  map_every qx_gen_tac[`s1`,`s2`,`s3`] >>
  rw[] >> fs[] >>
  qpat_assum`s3.clock = x`kall_tac >>
  qpat_assum`bc_fetch s3 = x`kall_tac >>
  Cases_on`bc_fetch s1 = SOME Tick` >- (
    Cases_on`ck' = 0` >- (
      qexists_tac`s1 with clock := SOME 0` >>
      simp[bc_fetch_with_clock] ) >>
    fs[bc_eval1_thm] >>
    fs[bc_eval1_def] >>
    rw[] >> fs[bump_pc_def] >>
    first_x_assum(qspec_then`ck'-1`mp_tac) >>
    simp[] >>
    disch_then(Q.X_CHOOSE_THEN`s3`strip_assume_tac) >>
    qexists_tac`s3` >> simp[] >>
    simp[Once RTC_CASES1] >> disj2_tac >>
    HINT_EXISTS_TAC >> simp[] >>
    simp[bc_eval1_thm] >>
    simp[bc_eval1_def,bc_fetch_with_clock,bump_pc_def] ) >>
  imp_res_tac bc_next_not_Tick_same_clock >> fs[] >>
  first_x_assum(qspec_then`ck'`mp_tac) >>
  simp[] >> strip_tac >>
  simp[Once RTC_CASES1] >>
  imp_res_tac bc_next_not_Tick_any_clock >>
  metis_tac[])

val _ = export_theory()
