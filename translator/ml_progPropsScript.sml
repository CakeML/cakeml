(*
  Clock-erased successful execution interfaces for program composition.
*)
Theory ml_progProps
Ancestors
  ml_prog evaluateProps
Libs
  preamble

Theorem Prog_deterministic:
  Prog env (st:'ffi semanticPrimitives$state) ds envA stA /\
  Prog env st ds envB stB ==>
  envA = envB /\ stA = stB
Proof
  strip_tac >>
  pop_assum (mp_tac o REWRITE_RULE [Prog_def]) >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (qx_choosel_then [`clockB`,`remainingB`] assume_tac)) >>
  qpat_x_assum `Prog _ _ _ _ _` (mp_tac o REWRITE_RULE [Prog_def]) >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (qx_choosel_then [`clockA`,`remainingA`] assume_tac)) >>
  drule evaluate_decs_add_to_clock >> simp [] >>
  disch_then (qspec_then `clockB` assume_tac) >>
  qpat_x_assum `evaluate_decs (st with clock := clockB) env ds = _`
    (mp_then (Pos hd) mp_tac evaluate_decs_add_to_clock) >>
  simp [] >> disch_then (qspec_then `clockA` mp_tac) >>
  simp [semanticPrimitivesTheory.state_component_equality]
QED

Theorem Prog_append_split:
  Prog env (st:'ffi semanticPrimitives$state) (ds1 ++ ds2) result_env result_st ==>
  ?envA envB mid_st.
    Prog env st ds1 envA mid_st /\
    Prog (extend_dec_env envA env) mid_st ds2 envB result_st /\
    result_env = extend_dec_env envB envA
Proof
  strip_tac >>
  pop_assum (mp_tac o REWRITE_RULE [Prog_def]) >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (qx_choosel_then [`start_clock`,`end_clock`] assume_tac)) >>
  qpat_x_assum `evaluate_decs _ _ (_ ++ _) = _`
    (mp_tac o ONCE_REWRITE_RULE [evaluate_decs_append]) >>
  namedCases_on `evaluate_decs (st with clock := start_clock) env ds1`
    ["first_st first_result"] >>
  namedCases_on `first_result` ["first_env","first_error"] >> simp [] >>
  namedCases_on `evaluate_decs first_st (extend_dec_env first_env env) ds2`
    ["tail_st tail_result"] >>
  namedCases_on `tail_result` ["tail_env","tail_error"] >>
  simp [semanticPrimitivesTheory.combine_dec_result_def] >> strip_tac >>
  qexistsl_tac [`first_env`,`tail_env`,`first_st with clock := st.clock`] >>
  simp [Prog_def, semanticPrimitivesTheory.extend_dec_env_def] >>
  conj_tac >- (
    qexistsl_tac [`start_clock`,`first_st.clock`] >>
    simp [semanticPrimitivesTheory.state_component_equality]) >>
  qexistsl_tac [`first_st.clock`,`end_clock`] >>
  fs [semanticPrimitivesTheory.state_component_equality,
    semanticPrimitivesTheory.extend_dec_env_def]
QED

Theorem Prog_module_split:
  Prog env (st:'ffi semanticPrimitives$state) [Dmod mn ds] result_env result_st ==>
  ?body_env.
    Prog env st ds body_env result_st /\
    result_env = write_mod mn body_env empty_env
Proof
  strip_tac >>
  pop_assum (mp_tac o REWRITE_RULE [Prog_def]) >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (qx_choosel_then [`start_clock`,`end_clock`] assume_tac)) >>
  qpat_x_assum `evaluate_decs _ _ [Dmod _ _] = _`
    (mp_tac o ONCE_REWRITE_RULE [evaluateTheory.evaluate_decs_def]) >>
  namedCases_on `evaluate_decs (st with clock := start_clock) env ds`
    ["body_st body_result"] >>
  namedCases_on `body_result` ["body_env","body_error"] >> simp [] >>
  strip_tac >>
  qexists_tac `body_env` >> simp [Prog_def, write_mod_def, empty_env_def] >>
  qexistsl_tac [`start_clock`,`end_clock`] >> simp []
QED
