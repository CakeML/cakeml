(*
  In evalSem's EvalDecs mode, the declarations given to Eval are decoded
  by the EvalDecs state and checked against its compiler. This theory
  shows that a source-to-source compiler can be moved from the compiler
  of the EvalDecs state into its decoding of declarations: the program
  behaves the same if the decoded declarations are compiled before they
  are evaluated, as long as the compiler checks the same thing. The
  compiled declarations may need extra clock to run. This does not
  apply in the EvalOracle, EvalRun and EvalPending modes.
*)
Theory source_adjust_decsProof
Ancestors
  evaluateProps[qualified] semanticPrimitives evalSem evalSemProps
Libs
  preamble

(* decode the declarations and compile them with g; the compiler of
   the state is C, which together with g must agree with the original *)
Definition adjust_decs_def:
  adjust_decs g C (eds:eval_decs_state) =
    eds with <| compiler := C; decode_decs := OPTION_MAP g o eds.decode_decs |>
End

Definition decs_factor_def:
  decs_factor g C (eds:eval_decs_state) ⇔
    ∀a b ds. eds.compiler (a,b,ds) = C (a,b,g ds)
End

Definition adjust_es_def:
  adjust_es g C (EvalDecs eds) = EvalDecs (adjust_decs g C eds) ∧
  adjust_es g C (EvalOracle x) = EvalOracle x ∧
  adjust_es g C (EvalRun eds) = EvalRun eds ∧
  adjust_es g C (EvalPending eds) = EvalPending eds
End

(* the eval state is in none of the EvalOracle, EvalRun and EvalPending
   modes, and factors in EvalDecs mode *)
Definition decs_factor_es_def:
  decs_factor_es g C NONE = T ∧
  decs_factor_es g C (SOME (EvalDecs eds)) = decs_factor g C eds ∧
  decs_factor_es g C (SOME (EvalOracle x)) = F ∧
  decs_factor_es g C (SOME (EvalRun eds)) = F ∧
  decs_factor_es g C (SOME (EvalPending eds)) = F
End

Definition decs_factor_st_def:
  decs_factor_st g C (s:'ffi state) ⇔ decs_factor_es g C s.eval_state
End

Overload s_adjust[local] =
  “λg C (s:'ffi state). s with eval_state updated_by OPTION_MAP (adjust_es g C)”

Theorem decs_factor_es_not_EvalRun:
  decs_factor_es g C es ⇒
  (∀r. es ≠ SOME (EvalRun r)) ∧
  (∀r. OPTION_MAP (adjust_es g C) es ≠ SOME (EvalRun r)) ∧
  (∀r. es ≠ SOME (EvalPending r)) ∧
  (∀r. OPTION_MAP (adjust_es g C) es ≠ SOME (EvalPending r))
Proof
  Cases_on ‘es’ \\ simp []
  \\ rename1 ‘SOME e’
  \\ Cases_on ‘e’
  \\ simp [decs_factor_es_def, adjust_es_def]
QED

Theorem decs_factor_es_do_eval_init:
  decs_factor_es g C es ⇒
  do_eval_init vs es (:'a) = NONE ∧
  do_eval_init vs (OPTION_MAP (adjust_es g C) es) (:'a) = NONE ∧
  do_eval_fail vs es = NONE ∧
  do_eval_fail vs (OPTION_MAP (adjust_es g C) es) = NONE ∧
  eval_result es x = x ∧
  eval_result (OPTION_MAP (adjust_es g C) es) x = x
Proof
  Cases_on ‘es’ \\ simp [eval_result_def]
  \\ rename1 ‘SOME e’
  \\ Cases_on ‘e’
  \\ simp [decs_factor_es_def, adjust_es_def, do_eval_init_def,
           do_eval_fail_def, eval_result_def]
  \\ every_case_tac
QED

Theorem compiler_agrees_factor:
  ∀f C g.
    (∀a b ds. f (a,b,ds) = C (a,b,g ds)) ⇒
    ∀id st decs x.
      compiler_agrees C (id,st,g decs) x = compiler_agrees f (id,st,decs) x
Proof
  rpt strip_tac
  \\ PairCases_on ‘x’
  \\ simp [compiler_agrees_def]
QED

Theorem do_eval_adjust_decs:
  decs_factor_es g C es ⇒
  do_eval vs (OPTION_MAP (adjust_es g C) es) =
  OPTION_MAP (λ(env,decs,es). (env, g decs, OPTION_MAP (adjust_es g C) es))
    (do_eval vs es)
Proof
  Cases_on ‘es’ >- simp [do_eval_def]
  \\ rename1 ‘SOME e’
  \\ Cases_on ‘e’
  \\ simp [decs_factor_es_def, adjust_es_def]
  \\ rename1 ‘decs_factor g C eds’
  \\ rw [decs_factor_def]
  \\ drule_then assume_tac compiler_agrees_factor
  \\ simp [do_eval_def]
  \\ every_case_tac
  \\ gvs [adjust_decs_def, add_decs_generation_def, adjust_es_def]
  \\ Cases_on ‘eds.env_id_counter’
  \\ rename1 ‘_ = (gen,rest)’
  \\ PairCases_on ‘rest’
  \\ simp [adjust_decs_def, eval_decs_state_component_equality]
QED

Theorem do_eval_decs_factor:
  do_eval vs es = SOME (env,decs,es') ∧ decs_factor_es g C es ⇒
  decs_factor_es g C es'
Proof
  Cases_on ‘es’ >- simp [do_eval_def]
  \\ rename1 ‘SOME e’
  \\ Cases_on ‘e’
  \\ simp [decs_factor_es_def]
  \\ rename1 ‘decs_factor g C eds’
  \\ rw [do_eval_def, AllCaseEqs()]
  \\ gvs [decs_factor_es_def, decs_factor_def, add_decs_generation_def]
  \\ Cases_on ‘eds.env_id_counter’
  \\ rename1 ‘_ = (gen,rest)’
  \\ PairCases_on ‘rest’
  \\ simp []
QED

Theorem declare_env_adjust_decs:
  declare_env (OPTION_MAP (adjust_es g C) es) env =
  OPTION_MAP (λ(x,es'). (x, OPTION_MAP (adjust_es g C) es')) (declare_env es env)
Proof
  Cases_on ‘es’ >- simp [declare_env_def]
  \\ rename1 ‘SOME e’
  \\ Cases_on ‘e’
  >~ [‘EvalOracle’] >- (
    simp [declare_env_def, adjust_es_def]
    \\ every_case_tac
    \\ simp [adjust_es_def])
  >~ [‘EvalRun’] >- (
    simp [declare_env_def, adjust_es_def]
    \\ every_case_tac
    \\ simp [adjust_es_def])
  >~ [‘EvalPending’] >- (
    simp [declare_env_def, adjust_es_def]
    \\ every_case_tac
    \\ simp [adjust_es_def])
  \\ simp [declare_env_def, adjust_es_def]
  \\ rename1 ‘adjust_decs g C eds’
  \\ simp [adjust_decs_def]
  \\ Cases_on ‘eds.env_id_counter’
  \\ rename1 ‘_ = (gen,rest)’
  \\ PairCases_on ‘rest’
  \\ simp [adjust_decs_def, adjust_es_def, eval_decs_state_component_equality]
QED

Theorem reset_env_generation_adjust_decs:
  reset_env_generation (OPTION_MAP (adjust_es g C) p)
    (OPTION_MAP (adjust_es g C) c) =
  OPTION_MAP (adjust_es g C) (reset_env_generation p c)
Proof
  namedCases_on ‘p’ ["","p1"]
  \\ namedCases_on ‘c’ ["","c1"]
  \\ simp [reset_env_generation_def]
  \\ namedCases_on ‘p1’ ["prior","prior_o","prior_r","prior_p"]
  \\ namedCases_on ‘c1’ ["current","current_o","current_r","current_p"]
  \\ simp [reset_env_generation_def, adjust_es_def]
  >~ [‘EvalRun’] >- (
    every_case_tac
    \\ simp [adjust_es_def])
  \\ simp [adjust_decs_def]
  \\ Cases_on ‘prior.env_id_counter’
  \\ rename1 ‘_ = (gen1,rest1)’
  \\ PairCases_on ‘rest1’
  \\ Cases_on ‘current.env_id_counter’
  \\ rename1 ‘_ = (gen2,rest2)’
  \\ PairCases_on ‘rest2’
  \\ simp [adjust_decs_def, adjust_es_def, eval_decs_state_component_equality]
QED

Theorem decs_factor_reset_env_generation:
  decs_factor_es g C c ⇒
  decs_factor_es g C (reset_env_generation p c)
Proof
  rw [reset_env_generation_def]
  \\ every_case_tac
  \\ gvs [decs_factor_es_def, decs_factor_def]
QED

Theorem decs_factor_declare_env:
  declare_env es env = SOME (x,es2) ∧
  decs_factor_es g C es ⇒
  decs_factor_es g C es2
Proof
  rw [declare_env_def]
  \\ every_case_tac
  \\ gvs [decs_factor_es_def, decs_factor_def]
QED

Theorem with_clock_same[local,simp]:
  (s:'ffi state) with clock := s.clock = s
Proof
  simp [state_component_equality]
QED

Theorem lift_clock[local]:
  (evaluate (s:'ffi state) env es = (s1,r) ⇒
   ∀extra. r ≠ Rerr (Rabort Rtimeout_error) ⇒
     evaluate (s with clock := s.clock + extra) env es =
       (s1 with clock := s1.clock + extra,r)) ∧
  (evaluate_match (s:'ffi state) env v pes err_v = (s1,r) ⇒
   ∀extra. r ≠ Rerr (Rabort Rtimeout_error) ⇒
     evaluate_match (s with clock := s.clock + extra) env v pes err_v =
       (s1 with clock := s1.clock + extra,r)) ∧
  (evaluate_decs (s:'ffi state) env ds = (s1,res) ⇒
   ∀extra. res ≠ Rerr (Rabort Rtimeout_error) ⇒
     evaluate_decs (s with clock := s.clock + extra) env ds =
       (s1 with clock := s1.clock + extra,res))
Proof
  metis_tac [evaluate_add_to_clock_all]
QED

(* g may need extra clock to evaluate like the declarations it is given;
   the adjusted program then needs extra clock too *)
Theorem adjust_decs_evaluate:
  (∀(s:'ffi state) env ds s' res.
    evaluate_decs s env ds = (s', res) ∧
    res ≠ Rerr (Rabort Rtype_error) ⇒
      ∃ck. evaluate_decs (s with clock := s.clock + ck) env (g ds) = (s', res)) ⇒
  (∀(s:'ffi state) env exps s' res.
    evaluate s env exps = (s', res) ∧
    decs_factor_st g C s ∧
    res ≠ Rerr (Rabort Rtype_error) ⇒
      decs_factor_st g C s' ∧
      ∃ck. evaluate (s_adjust g C (s with clock := s.clock + ck)) env exps =
           (s_adjust g C s', res)) ∧
  (∀(s:'ffi state) env x pes err_x s' res.
    evaluate_match s env x pes err_x = (s', res) ∧
    decs_factor_st g C s ∧
    res ≠ Rerr (Rabort Rtype_error) ⇒
      decs_factor_st g C s' ∧
      ∃ck. evaluate_match (s_adjust g C (s with clock := s.clock + ck)) env x pes err_x =
           (s_adjust g C s', res)) ∧
  (∀(s:'ffi state) env ds s' res.
    evaluate_decs s env ds = (s', res) ∧
    decs_factor_st g C s ∧
    res ≠ Rerr (Rabort Rtype_error) ⇒
      decs_factor_st g C s' ∧
      ∃ck. evaluate_decs (s_adjust g C (s with clock := s.clock + ck)) env ds =
           (s_adjust g C s', res))
Proof
  disch_tac
  \\ ho_match_mp_tac (name_ind_cases [] full_evaluate_ind)
  \\ rpt conj_tac
  \\ rpt (rpt gen_tac \\ disch_tac)
  \\ pop_assum strip_assume_tac
  >~ [‘evalSem$evaluate _ _ [] = _’] >- suspend "nil"
  >~ [‘evalSem$evaluate _ _ (_::_::_) = _’] >- suspend "cons"
  >~ [‘evalSem$evaluate _ _ [Lit _] = _’] >- suspend "Lit"
  >~ [‘evalSem$evaluate _ _ [Raise _] = _’] >- suspend "Raise"
  >~ [‘evalSem$evaluate _ _ [Handle _ _] = _’] >- suspend "Handle"
  >~ [‘evalSem$evaluate _ _ [Con _ _] = _’] >- suspend "Con"
  >~ [‘evalSem$evaluate _ _ [Var _] = _’] >- suspend "Var"
  >~ [‘evalSem$evaluate _ _ [Fun _ _] = _’] >- suspend "Fun"
  >~ [‘evalSem$evaluate _ _ [App _ _] = _’] >- suspend "App"
  >~ [‘evalSem$evaluate _ _ [Log _ _ _] = _’] >- suspend "Log"
  >~ [‘evalSem$evaluate _ _ [If _ _ _] = _’] >- suspend "If"
  >~ [‘evalSem$evaluate _ _ [Mat _ _] = _’] >- suspend "Mat"
  >~ [‘evalSem$evaluate _ _ [Let _ _ _] = _’] >- suspend "Let"
  >~ [‘evalSem$evaluate _ _ [Letrec _ _] = _’] >- suspend "Letrec"
  >~ [‘evalSem$evaluate _ _ [Tannot _ _] = _’] >- suspend "Tannot"
  >~ [‘evalSem$evaluate _ _ [Lannot _ _] = _’] >- suspend "Lannot"
  >~ [‘evalSem$evaluate _ _ [Open _ _] = _’] >- suspend "Open"
  >~ [‘evalSem$evaluate_match _ _ _ [] _ = _’] >- suspend "match_nil"
  >~ [‘evalSem$evaluate_match _ _ _ ((_,_)::_) _ = _’] >- suspend "match_cons"
  >~ [‘evalSem$evaluate_decs _ _ [] = _’] >- suspend "decs_nil"
  >~ [‘evalSem$evaluate_decs _ _ (_::_::_) = _’] >- suspend "decs_cons"
  >~ [‘evalSem$evaluate_decs _ _ [Dlet _ _ _] = _’] >- suspend "Dlet"
  >~ [‘evalSem$evaluate_decs _ _ [Dletrec _ _] = _’] >- suspend "Dletrec"
  >~ [‘evalSem$evaluate_decs _ _ [Dtype _ _] = _’] >- suspend "Dtype"
  >~ [‘evalSem$evaluate_decs _ _ [Dtabbrev _ _ _ _] = _’] >- suspend "Dtabbrev"
  >~ [‘evalSem$evaluate_decs _ _ [Denv _] = _’] >- suspend "Denv"
  >~ [‘evalSem$evaluate_decs _ _ [Dexn _ _ _] = _’] >- suspend "Dexn"
  >~ [‘evalSem$evaluate_decs _ _ [Dopen _ _] = _’] >- suspend "Dopen"
  >~ [‘evalSem$evaluate_decs _ _ [Dmod _ _] = _’] >- suspend "Dmod"
  >- suspend "Dlocal"
QED

Resume adjust_decs_evaluate[nil]:
  gvs [full_evaluate_def, AllCaseEqs()]
  \\ qexists_tac ‘0’
  \\ gvs [full_evaluate_def, decs_factor_st_def, state_component_equality]
QED

Resume adjust_decs_evaluate[cons]:
  gvs [full_evaluate_def, AllCaseEqs()]
  >- (
    qpat_x_assum ‘evaluate _ env [e1] = (s_adjust g C st', _)’
      (mp_tac o MATCH_MP (cj 1 lift_clock))
    \\ disch_then (qspec_then ‘ck’ mp_tac)
    \\ simp []
    \\ strip_tac
    \\ qexists_tac ‘ck' + ck’
    \\ gvs [])
  >- (
    qpat_x_assum ‘evaluate _ env [e1] = (s_adjust g C st', _)’
      (mp_tac o MATCH_MP (cj 1 lift_clock))
    \\ disch_then (qspec_then ‘ck’ mp_tac)
    \\ simp []
    \\ strip_tac
    \\ qexists_tac ‘ck' + ck’
    \\ gvs [])
  \\ qexists_tac ‘ck’
  \\ gvs []
QED

Resume adjust_decs_evaluate[Lit]:
  gvs [full_evaluate_def, AllCaseEqs()]
  \\ qexists_tac ‘0’
  \\ gvs [full_evaluate_def, decs_factor_st_def, state_component_equality]
QED

Resume adjust_decs_evaluate[Raise]:
  gvs [full_evaluate_def, AllCaseEqs()]
  \\ qexists_tac ‘ck’
  \\ gvs []
QED

Resume adjust_decs_evaluate[Handle]:
  gvs [full_evaluate_def, AllCaseEqs()]
  >- (
    qexists_tac ‘ck’
    \\ gvs [])
  >- (
    qpat_x_assum ‘evaluate _ env [e] = (s_adjust g C st', _)’
      (mp_tac o MATCH_MP (cj 1 lift_clock))
    \\ disch_then (qspec_then ‘ck’ mp_tac)
    \\ simp []
    \\ strip_tac
    \\ qexists_tac ‘ck' + ck’
    \\ gvs [])
  \\ qexists_tac ‘ck’
  \\ gvs []
QED

Resume adjust_decs_evaluate[Con]:
  gvs [full_evaluate_def, AllCaseEqs()]
  \\ qexists_tac ‘ck’
  \\ gvs []
QED

Resume adjust_decs_evaluate[Var]:
  gvs [full_evaluate_def, AllCaseEqs()]
  \\ qexists_tac ‘0’
  \\ gvs [full_evaluate_def, decs_factor_st_def, state_component_equality]
QED

Resume adjust_decs_evaluate[Fun]:
  gvs [full_evaluate_def, AllCaseEqs()]
  \\ qexists_tac ‘0’
  \\ gvs [full_evaluate_def, decs_factor_st_def, state_component_equality]
QED

Resume adjust_decs_evaluate[App]:
  qpat_x_assum ‘(∀a b c d e f. _) ∧ _’ strip_assume_tac
  \\ qpat_x_assum ‘evalSem$evaluate s env [App op es] = _’ mp_tac
  \\ simp [Once full_evaluate_def]
  \\ Cases_on ‘evalSem$evaluate s env (REVERSE es)’
  \\ rename1 ‘evalSem$evaluate s env (REVERSE es) = (st1,r1)’
  \\ Cases_on ‘r1 = Rerr (Rabort Rtype_error)’
  >- simp []
  \\ qpat_x_assum ‘∀x y. (st1,r1) = (x,y) ∧ _ ⇒ _’
       (qspecl_then [‘st1’,‘r1’] mp_tac)
  \\ impl_tac >- fs []
  \\ strip_tac
  \\ reverse (Cases_on ‘r1’)
  >- (
    strip_tac
    \\ gvs []
    \\ qexists_tac ‘ck’
    \\ simp [Once full_evaluate_def]
    \\ gvs [])
  \\ rename1 ‘Rval vs’
  \\ simp []
  \\ Cases_on ‘op = Opapp’
  >- (
    gvs []
    \\ strip_tac
    \\ gvs [AllCaseEqs()]
    >- (
      qexists_tac ‘ck’
      \\ simp [Once full_evaluate_def]
      \\ gvs [])
    \\ qpat_x_assum ‘decs_factor_st _ _ (dec_clock _) ⇒ _’ mp_tac
    \\ impl_tac >- gvs [decs_factor_st_def, evalSemTheory.dec_clock_def]
    \\ strip_tac
    \\ gvs []
    \\ qpat_x_assum ‘evalSem$evaluate _ env (REVERSE es) = (s_adjust g C st1, _)’
         (mp_tac o MATCH_MP (cj 1 lift_clock))
    \\ disch_then (qspec_then ‘ck'’ mp_tac)
    \\ simp []
    \\ strip_tac
    \\ qexists_tac ‘ck + ck'’
    \\ simp [Once full_evaluate_def]
    \\ gvs [evalSemTheory.dec_clock_def]
    \\ ‘ck' + st1.clock - 1 = ck' + (st1.clock - 1)’ by decide_tac
    \\ gvs [])
  \\ Cases_on ‘op = ThunkOp ForceThunk’
  >- (
    gvs []
    \\ strip_tac
    \\ gvs [AllCaseEqs()]
    >- (
      qexists_tac ‘ck’
      \\ simp [Once full_evaluate_def]
      \\ gvs [])
    >- (
      qexists_tac ‘ck’
      \\ simp [Once full_evaluate_def]
      \\ gvs [])
    >- (
      qpat_x_assum ‘decs_factor_st _ _ (dec_clock _) ⇒ _’ mp_tac
      \\ impl_tac >- gvs [decs_factor_st_def, evalSemTheory.dec_clock_def]
      \\ strip_tac
      \\ gvs [decs_factor_st_def]
      \\ qpat_x_assum ‘evalSem$evaluate _ env (REVERSE es) = (s_adjust g C st1, _)’
           (mp_tac o MATCH_MP (cj 1 lift_clock))
      \\ disch_then (qspec_then ‘ck'’ mp_tac)
      \\ simp []
      \\ strip_tac
      \\ qexists_tac ‘ck + ck'’
      \\ simp [Once full_evaluate_def]
      \\ gvs [evalSemTheory.dec_clock_def]
      \\ ‘ck' + st1.clock - 1 = ck' + (st1.clock - 1)’ by decide_tac
      \\ gvs [])
    \\ qpat_x_assum ‘decs_factor_st _ _ (dec_clock _) ⇒ _’ mp_tac
    \\ impl_tac >- gvs [decs_factor_st_def, evalSemTheory.dec_clock_def]
    \\ strip_tac
    \\ gvs [decs_factor_st_def]
    \\ qpat_x_assum ‘evalSem$evaluate _ env (REVERSE es) = (s_adjust g C st1, _)’
         (mp_tac o MATCH_MP (cj 1 lift_clock))
    \\ disch_then (qspec_then ‘ck'’ mp_tac)
    \\ simp []
    \\ strip_tac
    \\ qexists_tac ‘ck + ck'’
    \\ simp [Once full_evaluate_def]
    \\ gvs [evalSemTheory.dec_clock_def]
    \\ ‘ck' + st1.clock - 1 = ck' + (st1.clock - 1)’ by decide_tac
    \\ gvs [])
  \\ Cases_on ‘op = Eval’
  >- (
    gvs []
    \\ ‘decs_factor_es g C st1.eval_state’ by gvs [decs_factor_st_def]
    \\ drule (INST_TYPE [alpha |-> “:'ffi”] decs_factor_es_do_eval_init)
    \\ strip_tac
    \\ strip_tac
    \\ gvs [AllCaseEqs(), do_eval_res_def]
    >>~- ([‘EvalRun’], gvs [decs_factor_st_def, decs_factor_es_def])
    >>~- ([‘EvalPending’], gvs [decs_factor_st_def, decs_factor_es_def])
    \\ ‘decs_factor_es g C es1’ by metis_tac [do_eval_decs_factor]
    \\ ‘do_eval (REVERSE vs) (OPTION_MAP (adjust_es g C) st1.eval_state) =
        SOME (env1, g decs, OPTION_MAP (adjust_es g C) es1)’
      by gvs [do_eval_adjust_decs]
    >- (
      conj_tac >- gvs [decs_factor_st_def]
      \\ qexists_tac ‘ck’
      \\ simp [Once full_evaluate_def]
      \\ gvs [do_eval_res_def])
    >- (
      qpat_x_assum ‘decs_factor_st _ _ (dec_clock _) ⇒ _’ mp_tac
      \\ impl_tac >- gvs [decs_factor_st_def, evalSemTheory.dec_clock_def]
      \\ disch_then (CONJUNCTS_THEN2 assume_tac (qx_choose_then ‘ck2’ assume_tac))
      \\ qpat_assum ‘∀s env ds s' res. _’
           (fn gp => qpat_assum ‘evalSem$evaluate_decs (_ with <|clock := _; eval_state updated_by _|>) env1 decs = _’
              (fn th => mp_tac (MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO] gp) th)))
      \\ impl_tac >- simp []
      \\ disch_then (qx_choose_then ‘ck3’ assume_tac)
      \\ qpat_x_assum ‘evalSem$evaluate _ env (REVERSE es) = (s_adjust g C st1, _)’
           (mp_tac o MATCH_MP (cj 1 lift_clock))
      \\ disch_then (qspec_then ‘ck2 + ck3’ mp_tac)
      \\ simp []
      \\ strip_tac
      \\ conj_tac
      >- (
        gvs [decs_factor_st_def]
        \\ irule decs_factor_reset_env_generation
        \\ drule_then irule decs_factor_declare_env
        \\ gvs [])
      \\ qexists_tac ‘ck + (ck2 + ck3)’
      \\ simp [Once full_evaluate_def]
      \\ qpat_x_assum ‘evalSem$evaluate_decs _ env1 (g decs) = _’
           (assume_tac o SIMP_RULE (srw_ss()) [evalSemTheory.dec_clock_def])
      \\ once_rewrite_tac [do_eval_res_def]
      \\ simp []
      \\ rewrite_tac [evalSemTheory.dec_clock_def]
      \\ Cases_on ‘st1.clock’ >- gvs []
      \\ fs [ADD1, declare_env_adjust_decs, reset_env_generation_adjust_decs])
    >- (
      qpat_x_assum ‘decs_factor_st _ _ (dec_clock _) ⇒ _’ mp_tac
      \\ impl_tac >- gvs [decs_factor_st_def, evalSemTheory.dec_clock_def]
      \\ disch_then (CONJUNCTS_THEN2 assume_tac (qx_choose_then ‘ck2’ assume_tac))
      \\ qpat_assum ‘∀s env ds s' res. _’
           (fn gp => qpat_assum ‘evalSem$evaluate_decs (_ with <|clock := _; eval_state updated_by _|>) env1 decs = _’
              (fn th => mp_tac (MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO] gp) th)))
      \\ impl_tac >- simp []
      \\ disch_then (qx_choose_then ‘ck3’ assume_tac)
      \\ qpat_x_assum ‘evalSem$evaluate _ env (REVERSE es) = (s_adjust g C st1, _)’
           (mp_tac o MATCH_MP (cj 1 lift_clock))
      \\ disch_then (qspec_then ‘ck2 + ck3’ mp_tac)
      \\ simp []
      \\ strip_tac
      \\ conj_tac
      >- (
        gvs [decs_factor_st_def]
        \\ irule decs_factor_reset_env_generation
        \\ gvs [])
      \\ qexists_tac ‘ck + (ck2 + ck3)’
      \\ simp [Once full_evaluate_def]
      \\ qpat_x_assum ‘evalSem$evaluate_decs _ env1 (g decs) = _’
           (assume_tac o SIMP_RULE (srw_ss()) [evalSemTheory.dec_clock_def])
      \\ once_rewrite_tac [do_eval_res_def]
      \\ simp []
      \\ rewrite_tac [evalSemTheory.dec_clock_def]
      \\ Cases_on ‘st1.clock’ >- gvs []
      \\ fs [ADD1, reset_env_generation_adjust_decs])
    \\ qpat_x_assum ‘decs_factor_st _ _ (dec_clock _) ⇒ _’ mp_tac
    \\ impl_tac >- gvs [decs_factor_st_def, evalSemTheory.dec_clock_def]
    \\ disch_then (CONJUNCTS_THEN2 assume_tac (qx_choose_then ‘ck2’ assume_tac))
    \\ qpat_assum ‘∀s env ds s' res. _’
         (fn gp => qpat_assum ‘evalSem$evaluate_decs (_ with <|clock := _; eval_state updated_by _|>) env1 decs = _’
            (fn th => mp_tac (MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO] gp) th)))
    \\ impl_tac >- simp []
    \\ disch_then (qx_choose_then ‘ck3’ assume_tac)
    \\ qpat_x_assum ‘evalSem$evaluate _ env (REVERSE es) = (s_adjust g C st1, _)’
         (mp_tac o MATCH_MP (cj 1 lift_clock))
    \\ disch_then (qspec_then ‘ck2 + ck3’ mp_tac)
    \\ simp []
    \\ strip_tac
    \\ qexists_tac ‘ck + (ck2 + ck3)’
    \\ simp [Once full_evaluate_def]
    \\ qpat_x_assum ‘evalSem$evaluate_decs _ env1 (g decs) = _’
         (assume_tac o SIMP_RULE (srw_ss()) [evalSemTheory.dec_clock_def])
    \\ once_rewrite_tac [do_eval_res_def]
    \\ simp []
    \\ rewrite_tac [evalSemTheory.dec_clock_def]
    \\ Cases_on ‘st1.clock’ >- gvs []
    \\ fs [ADD1])
  \\ gvs []
  \\ strip_tac
  \\ gvs [AllCaseEqs(), decs_factor_st_def]
  \\ qexists_tac ‘ck’
  \\ simp [Once full_evaluate_def]
  \\ gvs []
QED

Resume adjust_decs_evaluate[Log]:
  gvs [full_evaluate_def, AllCaseEqs()]
  >- (
    qpat_x_assum ‘evaluate _ env [e1] = (s_adjust g C st', _)’
      (mp_tac o MATCH_MP (cj 1 lift_clock))
    \\ disch_then (qspec_then ‘ck’ mp_tac)
    \\ simp []
    \\ strip_tac
    \\ qexists_tac ‘ck' + ck’
    \\ gvs [])
  >- (
    qexists_tac ‘ck’
    \\ gvs [])
  \\ qexists_tac ‘ck’
  \\ gvs []
QED

Resume adjust_decs_evaluate[If]:
  gvs [full_evaluate_def, AllCaseEqs()]
  >- (
    qpat_x_assum ‘evaluate _ env [e1] = (s_adjust g C st', _)’
      (mp_tac o MATCH_MP (cj 1 lift_clock))
    \\ disch_then (qspec_then ‘ck’ mp_tac)
    \\ simp []
    \\ strip_tac
    \\ qexists_tac ‘ck' + ck’
    \\ gvs [])
  \\ qexists_tac ‘ck’
  \\ gvs []
QED

Resume adjust_decs_evaluate[Mat]:
  gvs [full_evaluate_def, AllCaseEqs()]
  >- (
    qpat_x_assum ‘evaluate _ env [e] = (s_adjust g C st', _)’
      (mp_tac o MATCH_MP (cj 1 lift_clock))
    \\ disch_then (qspec_then ‘ck’ mp_tac)
    \\ simp []
    \\ strip_tac
    \\ qexists_tac ‘ck' + ck’
    \\ gvs [])
  \\ qexists_tac ‘ck’
  \\ gvs []
QED

Resume adjust_decs_evaluate[Let]:
  gvs [full_evaluate_def, AllCaseEqs()]
  >- (
    qpat_x_assum ‘evaluate _ env [e1] = (s_adjust g C st', _)’
      (mp_tac o MATCH_MP (cj 1 lift_clock))
    \\ disch_then (qspec_then ‘ck’ mp_tac)
    \\ simp []
    \\ strip_tac
    \\ qexists_tac ‘ck' + ck’
    \\ gvs [])
  \\ qexists_tac ‘ck’
  \\ gvs []
QED

Resume adjust_decs_evaluate[Letrec]:
  gvs [full_evaluate_def, AllCaseEqs()]
  \\ qexists_tac ‘ck’
  \\ gvs []
QED

Resume adjust_decs_evaluate[Tannot]:
  gvs [full_evaluate_def, AllCaseEqs()]
  \\ qexists_tac ‘ck’
  \\ gvs []
QED

Resume adjust_decs_evaluate[Lannot]:
  gvs [full_evaluate_def, AllCaseEqs()]
  \\ qexists_tac ‘ck’
  \\ gvs []
QED

Resume adjust_decs_evaluate[Open]:
  gvs [full_evaluate_def, AllCaseEqs()]
  \\ qexists_tac ‘ck’
  \\ gvs []
QED

Resume adjust_decs_evaluate[match_nil]:
  gvs [full_evaluate_def, AllCaseEqs()]
  \\ qexists_tac ‘0’
  \\ gvs [full_evaluate_def, decs_factor_st_def, state_component_equality]
QED

Resume adjust_decs_evaluate[match_cons]:
  gvs [full_evaluate_def, AllCaseEqs()]
  \\ qexists_tac ‘ck’
  \\ gvs []
QED

Resume adjust_decs_evaluate[decs_nil]:
  gvs [full_evaluate_def, AllCaseEqs()]
  \\ qexists_tac ‘0’
  \\ gvs [full_evaluate_def, decs_factor_st_def, state_component_equality]
QED

Resume adjust_decs_evaluate[decs_cons]:
  gvs [full_evaluate_def, AllCaseEqs(),
       evaluatePropsTheory.combine_dec_result_eq_Rerr]
  >- (
    qpat_x_assum ‘evaluate_decs _ env [d1] = (s_adjust g C st1, _)’
      (mp_tac o MATCH_MP (cj 3 lift_clock))
    \\ disch_then (qspec_then ‘ck'’ mp_tac)
    \\ simp []
    \\ strip_tac
    \\ qexists_tac ‘ck + ck'’
    \\ gvs [])
  \\ qexists_tac ‘ck’
  \\ gvs []
QED

Resume adjust_decs_evaluate[Dlet]:
  gvs [full_evaluate_def, AllCaseEqs()]
  \\ qexists_tac ‘ck’
  \\ gvs []
QED

Resume adjust_decs_evaluate[Dletrec]:
  gvs [full_evaluate_def, AllCaseEqs()]
  \\ qexists_tac ‘0’
  \\ gvs [full_evaluate_def, decs_factor_st_def, state_component_equality]
QED

Resume adjust_decs_evaluate[Dtype]:
  gvs [full_evaluate_def, AllCaseEqs(), decs_factor_st_def]
  \\ qexists_tac ‘0’
  \\ gvs [full_evaluate_def, state_component_equality]
QED

Resume adjust_decs_evaluate[Dtabbrev]:
  gvs [full_evaluate_def, AllCaseEqs()]
  \\ qexists_tac ‘0’
  \\ gvs [full_evaluate_def, decs_factor_st_def, state_component_equality]
QED

Resume adjust_decs_evaluate[Denv]:
  gvs [full_evaluate_def, AllCaseEqs()]
  \\ conj_tac
  >- (
    gvs [decs_factor_st_def]
    \\ drule_then irule decs_factor_declare_env
    \\ simp [])
  \\ qexists_tac ‘0’
  \\ gvs [full_evaluate_def, declare_env_adjust_decs, state_component_equality]
QED

Resume adjust_decs_evaluate[Dexn]:
  gvs [full_evaluate_def, AllCaseEqs(), decs_factor_st_def]
  \\ qexists_tac ‘0’
  \\ gvs [full_evaluate_def, state_component_equality]
QED

Resume adjust_decs_evaluate[Dopen]:
  gvs [full_evaluate_def, AllCaseEqs()]
  \\ qexists_tac ‘0’
  \\ gvs [full_evaluate_def, decs_factor_st_def, state_component_equality]
QED

Resume adjust_decs_evaluate[Dmod]:
  gvs [full_evaluate_def, AllCaseEqs()]
  \\ qexists_tac ‘ck’
  \\ gvs []
QED

Resume adjust_decs_evaluate[Dlocal]:
  gvs [full_evaluate_def, AllCaseEqs()]
  >- (
    qpat_x_assum ‘evaluate_decs _ env ds = (s_adjust g C st1, _)’
      (mp_tac o MATCH_MP (cj 3 lift_clock))
    \\ disch_then (qspec_then ‘ck’ mp_tac)
    \\ simp []
    \\ strip_tac
    \\ qexists_tac ‘ck' + ck’
    \\ gvs [])
  \\ qexists_tac ‘ck’
  \\ gvs []
QED

Finalise adjust_decs_evaluate;

Theorem adjust_decs_semantics_prog:
  (∀(s:'ffi state) env ds s' res.
    evaluate_decs s env ds = (s', res) ∧
    res ≠ Rerr (Rabort Rtype_error) ⇒
      ∃ck. evaluate_decs (s with clock := s.clock + ck) env (g ds) = (s', res)) ∧
  decs_factor_st g C (s:'ffi state) ∧
  ¬ semantics_determ s env prog Fail ∧
  semantics_determ s env prog outcome ⇒
  semantics_determ (s_adjust g C s) env prog outcome
Proof
  strip_tac
  \\ drule_then (qspec_then ‘C’ strip_assume_tac) adjust_decs_evaluate
  \\ ‘semantics_determ (s_adjust g C s) env prog = semantics_determ s env prog’
    suffices_by simp []
  \\ irule semantics_determ_clock_extra
  \\ rw [evaluate_prog_with_clock_def]
  \\ pairarg_tac
  \\ gvs []
  \\ ‘decs_factor_st g C (s with clock := k)’ by gvs [decs_factor_st_def]
  \\ qpat_x_assum ‘∀s env ds s' res. evalSem$evaluate_decs s env ds = _ ∧
                              decs_factor_st _ _ _ ∧ _ ⇒ _’
       (qspecl_then [‘s with clock := k’,‘env’,‘prog’,‘st'’,‘r’] mp_tac)
  \\ simp []
  \\ strip_tac
  \\ qexists_tac ‘ck’
  \\ gvs []
QED

(* a g that needs no extra clock *)
Theorem decs_exact_clock:
  (∀(s:'ffi state) env ds s' res.
     evaluate_decs s env ds = (s', res) ∧ res ≠ Rerr (Rabort Rtype_error) ⇒
     evaluate_decs s env (g ds) = (s', res)) ⇒
  ∀(s:'ffi state) env ds s' res.
    evaluate_decs s env ds = (s', res) ∧ res ≠ Rerr (Rabort Rtype_error) ⇒
    ∃ck. evaluate_decs (s with clock := s.clock + ck) env (g ds) = (s', res)
Proof
  rpt strip_tac
  \\ qexists_tac ‘0’
  \\ simp []
QED
