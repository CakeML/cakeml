(*
  Determinism for the small-step and relational big-step semantics
*)
Theory determ
Ancestors
  semanticPrimitives bigStep smallStep
Libs
  preamble


val s = ``s:'ffi state``;

(******************** Big step ********************)

Theorem big_exp_determ:
  (∀ck env ^s e r1.
     evaluate ck env s e r1 ⇒
     ∀r2. evaluate ck env s e r2 ⇒
          (r1 = r2)) ∧
  (∀ck env ^s es r1.
     evaluate_list ck env s es r1 ⇒
     ∀r2. evaluate_list ck env s es r2 ⇒
          (r1 = r2)) ∧
  (∀ck env ^s v pes err_v r1.
     evaluate_match ck env s v pes err_v r1 ⇒
     ∀r2. evaluate_match ck env s v pes err_v r2 ⇒
          (r1 = r2))
Proof
  HO_MATCH_MP_TAC evaluate_ind >>
  rw [] >>
  pop_assum (ASSUME_TAC o SIMP_RULE (srw_ss ()) [Once evaluate_cases, opClass_cases]) >>
  fs [] >>
  rw [] >>
  fs [opClass_cases] >>
  res_tac >>
  fs [] >>
  rw [] >>
  res_tac >>
  fs [] >>
  rw [] >>
  ‘s with fp_state := s.fp_state = s’ by gs[state_component_equality] >>
  gs[] >> res_tac >> gs[] >>
  metis_tac []
QED

Theorem decs_determ:
  (!ck env (s:'a state) d r1.
     evaluate_dec ck env s d r1 ⇒
     !r2.
       evaluate_dec ck env s d r2
       ⇒
       (r1 = r2)) ∧
  (!ck env (s:'a state) ds r1.
     evaluate_decs ck env s ds r1 ⇒
     !r2.
       evaluate_decs ck env s ds r2
       ⇒
       (r1 = r2))
Proof
  HO_MATCH_MP_TAC evaluate_dec_ind >>
  rw [] >>
  pop_assum mp_tac >>
  simp [Once evaluate_dec_cases] >>
  fs [] >>
  rw [] >>
  metis_tac [big_exp_determ, result_11, result_distinct,PAIR_EQ,NOT_EXISTS,
             NOT_EVERY, match_result_11, match_result_distinct, optionTheory.SOME_11,PAIR]
QED


(******************** Small step ********************)

Theorem TC_functional_confluence:
  ∀R. (∀a b1 b2. R a b1 ∧ R a b2 ⇒ b1 = b2) ⇒
    ∀a b1 b2.
      R⁺ a b1 ∧ R⁺ a b2
    ⇒ (b1 = b2) ∨
      (R⁺ a b1 ∧ R⁺ b1 b2) ∨
      (R⁺ a b2 ∧ R⁺ b2 b1)
Proof
  ntac 2 strip_tac >> Induct_on `TC R` >> rw[]
  >- (
    qpat_x_assum `TC _ _ _` mp_tac >>
    simp[Once TC_CASES1] >> strip_tac >> gvs[] >- metis_tac[] >>
    `y = b1` by metis_tac[] >> gvs[] >>
    disj2_tac >> simp[Once TC_CASES1]
    ) >>
  rename1 `R⁺ mid b1` >>
  last_x_assum assume_tac >>
  last_x_assum $ qspec_then `b2` assume_tac >> gvs[]
  >- (
    last_x_assum drule >> strip_tac >> gvs[] >>
    disj2_tac >> disj1_tac >>
    irule $ cj 2 TC_RULES >> qexists_tac `mid` >> simp[]
    )
  >- (
    ntac 2 disj2_tac >>
    irule $ cj 2 TC_RULES >> goal_assum drule >> simp[]
    )
QED

Theorem TC_functional_deterministic:
  ∀R. (∀a b1 b2. R a b1 ∧ R a b2 ⇒ b1 = b2) ⇒
  ∀a b1 b2.
    R⁺ a b1 ∧ R⁺ a b2 ∧
    (∀c. ¬R b1 c) ∧ (∀c. ¬R b2 c)
  ⇒ b1 = b2
Proof
  rw[] >> drule TC_functional_confluence >> disch_then drule >>
  disch_then $ qspec_then `b1` assume_tac >> gvs[] >> metis_tac[TC_CASES1]
QED

Theorem RTC_functional_confluence:
  ∀R. (∀a b1 b2. R a b1 ∧ R a b2 ⇒ b1 = b2) ⇒
    ∀a b1 b2.
      R꙳ a b1 ∧ R꙳ a b2
    ⇒ (R꙳ a b1 ∧ R꙳ b1 b2) ∨
      (R꙳ a b2 ∧ R꙳ b2 b1)
Proof
  ntac 2 strip_tac >> Induct_on `RTC R` >>
  once_rewrite_tac[RTC_CASES1] >> rw[] >> gvs[] >>
  metis_tac[RTC_CASES1]
QED

Theorem RTC_functional_deterministic:
  ∀R. (∀a b1 b2. R a b1 ∧ R a b2 ⇒ b1 = b2) ⇒
  ∀a b1 b2.
    R꙳ a b1 ∧ R꙳ a b2 ∧
    (∀c. ¬R b1 c) ∧ (∀c. ¬R b2 c)
  ⇒ b1 = b2
Proof
  once_rewrite_tac[RTC_CASES_TC] >> rw[] >> gvs[]
  >- gvs[Once TC_CASES1] >- gvs[Once TC_CASES1] >>
  metis_tac[TC_functional_deterministic]
QED

Triviality decl_step_reln_functional:
  ∀env a b1 b2. decl_step_reln env a b1 ∧ decl_step_reln env a b2 ⇒ b1 = b2
Proof
  rw[decl_step_reln_def] >> gvs[]
QED

Theorem RTC_decl_step_confl = RTC_functional_confluence |>
  Q.ISPEC `decl_step_reln env` |>
  Lib.C MATCH_MP (Q.SPEC `env` decl_step_reln_functional) |> GEN_ALL

Theorem RTC_decl_step_determ = RTC_functional_deterministic |>
  Q.ISPEC `decl_step_reln env` |>
  Lib.C MATCH_MP (Q.SPEC `env` decl_step_reln_functional) |> GEN_ALL

Definition Rerr_to_decl_step_result_def[simp]:
  Rerr_to_decl_step_result fps (Rraise v) = Draise (fps, v) ∧
  Rerr_to_decl_step_result fps (Rabort v) = Dabort (fps, v)
End

Theorem small_eval_dec_def:
  (∀benv dst st e. small_eval_dec benv dst (st, Rval e) =
    (decl_step_reln benv)꙳ dst (st, Env e, [])) ∧
  (∀benv dst st err. small_eval_dec benv dst (st, Rerr err) =
    ∃fp dst'.
      (decl_step_reln benv)꙳ dst (st with fp_state := fp, dst') ∧
      decl_step benv (st with fp_state := fp, dst') = Rerr_to_decl_step_result (st.fp_state) err)
Proof
  rw[small_eval_dec_def] >>
  Cases_on `err` >> rw[small_eval_dec_def, EXISTS_PROD] >>
  metis_tac[]
QED

Theorem small_eval_dec_cases:
  ∀env dev st res.
    small_eval_dec env dev res ⇔
      ∃dev'.
        (decl_step_reln env)꙳ dev dev' ∧
        ((∃env'. SND res = Rval env' ∧ dev' = (FST res, Env env', [])) ∨
         (∃err fp. SND res = Rerr err ∧ FST dev' = FST res with fp_state := fp ∧
            decl_step env dev' = Rerr_to_decl_step_result (FST res).fp_state err))
Proof
  rw[] >> reverse eq_tac >> rw[] >> gvs[small_eval_dec_def] >>
  PairCases_on `res` >> gvs[small_eval_dec_def]
  >- (PairCases_on `dev'` >> gs[] >> goal_assum drule >> simp[]) >>
  Cases_on `res1` >> gvs[small_eval_dec_def] >>
  goal_assum drule >> simp[] >> metis_tac[]
QED

Theorem small_eval_dec_determ:
    small_eval_dec env dev r1 ∧ small_eval_dec env dev r2
  ⇒ r1 = r2
Proof
  rw[small_eval_dec_cases] >> gvs[]
  >- (
    qmatch_asmsub_abbrev_tac `RTC _ _ a` >>
    last_x_assum assume_tac >> qmatch_asmsub_abbrev_tac `RTC _ _ b` >>
    qspecl_then [`env`,`dev`,`a`,`b`] assume_tac RTC_decl_step_determ >> gvs[] >>
    unabbrev_all_tac >> gvs[decl_step_reln_def, decl_step_def, decl_continue_def] >>
    metis_tac[PAIR]
    )
  >- (
    qmatch_asmsub_abbrev_tac `RTC _ _ a` >>
    last_x_assum assume_tac >> qmatch_asmsub_abbrev_tac `RTC _ _ b` >>
    qspecl_then [`env`,`dev`,`a`,`b`] assume_tac RTC_decl_step_determ >> gvs[] >>
    unabbrev_all_tac >> Cases_on `err` >>
    gvs[decl_step_reln_def, decl_step_def, decl_continue_def]
    )
  >- (
    qmatch_asmsub_abbrev_tac `RTC _ _ a` >>
    last_x_assum assume_tac >> qmatch_asmsub_abbrev_tac `RTC _ _ b` >>
    qspecl_then [`env`,`dev`,`a`,`b`] assume_tac RTC_decl_step_determ >> gvs[] >>
    unabbrev_all_tac >> Cases_on `err` >>
    gvs[decl_step_reln_def, decl_step_def, decl_continue_def]
    )
  >- (
    qmatch_asmsub_abbrev_tac `RTC _ _ a` >>
    last_x_assum assume_tac >> qmatch_asmsub_abbrev_tac `RTC _ _ b` >>
    qspecl_then [`env`,`dev`,`a`,`b`] assume_tac RTC_decl_step_determ >> gvs[] >>
    unabbrev_all_tac >> Cases_on `err` >> Cases_on `err'` >>
    gvs[decl_step_reln_def, decl_step_def, decl_continue_def] >>
    Cases_on ‘r1’ >> Cases_on ‘r2’ >> gs[state_component_equality]
    )
QED

