open preamble;
open flatLangTheory flatSemTheory flatPropsTheory flat_uncheck_ctorsTheory;

val _ = new_theory "flat_uncheck_ctorsProof";

val compile_append = Q.prove (
  `!es es2. compile (es ++ es2) = compile es ++ compile es2`,
  Induct >>
  rw [compile_def] >>
  Cases_on `es` >>
  rw [compile_def] >>
  fs [compile_def] >>
  Cases_on `es2` >>
  rw [] >>
  Cases_on `h` >>
  rw [compile_def]);

val compile_reverse = Q.prove (
  `!es. compile (REVERSE es) = REVERSE (compile es)`,
  ho_match_mp_tac compile_ind >>
  rw [compile_def, compile_append]);

val (v_rel_rules, v_rel_ind, v_rel_cases) = Hol_reln `
  (!lit.
    v_rel (flatSem$Litv lit) (flatSem$Litv lit)) ∧
  (!cn vs vs' t.
    LIST_REL v_rel vs vs'
    ⇒
    v_rel (flatSem$Conv cn vs) (flatSem$Conv (SOME (the (0,t) cn)) vs')) ∧
  (!env x e env'.
    LIST_REL (\(x,v1) (y,v2). x = y ∧ v_rel v1 v2) env env'
    ⇒
    v_rel (flatSem$Closure env x e) (flatSem$Closure env' x (HD (compile [e])))) ∧
  (!env funs x env'.
    LIST_REL (\(x,v1) (y,v2). x = y ∧ v_rel v1 v2) env env'
    ⇒
    v_rel (Recclosure env funs x)
      (Recclosure env' (MAP (\(f,x,e). (f, x, HD (compile [e]))) funs) x)) ∧
  (!loc.
    v_rel (Loc loc) (Loc loc)) ∧
  (!vs vs'.
    LIST_REL v_rel vs vs'
    ⇒
    v_rel (Vectorv vs) (Vectorv vs'))`;

val (sv_rel_rules, sv_rel_ind, sv_rel_cases) = Hol_reln `
  (!v v'.
    v_rel v v'
    ⇒
    sv_rel (Refv v) (Refv v')) ∧
  (!w.
    sv_rel (W8array w) (W8array w)) ∧
  (!vs vs'.
    LIST_REL v_rel vs vs'
    ⇒
    sv_rel (Varray vs) (Varray vs'))`;

val (s_rel_rules, s_rel_ind, s_rel_cases) = Hol_reln `
  (!s s'.
    s.clock = s'.clock ∧
    LIST_REL sv_rel s.refs s'.refs ∧
    s.ffi = s'.ffi ∧
    LIST_REL (OPTION_REL v_rel) s.globals s'.globals
    ⇒
    s_rel s s')`;

val (env_rel_rules, env_rel_ind, env_rel_cases) = Hol_reln `
  (!env env'.
    LIST_REL (\(x,v1) (y,v2). x = y ∧ v_rel v1 v2) env.v env'.v ∧
    env.exh_pat = env'.exh_pat ∧
    env.check_ctor ∧
    ~env'.check_ctor
    ⇒
    env_rel env env')`;

val (result_rel_rules, result_rel_ind, result_rel_cases) = Hol_reln `
  (∀v v'.
    f v v'
    ⇒
    result_rel f (Rval v) (Rval v')) ∧
  (∀v v'.
    v_rel v v'
    ⇒
    result_rel f (Rerr (Rraise v)) (Rerr (Rraise v'))) ∧
  (!a.
    result_rel f (Rerr (Rabort a)) (Rerr (Rabort a)))`;

val alookup_env_rel = Q.prove (
  `!env env' n x.
    env_rel env env' ∧
    ALOOKUP env.v n = SOME x
    ⇒
    ∃x'. v_rel x x' ∧ ALOOKUP env'.v n = SOME x'`,
  strip_tac >>
  Induct_on `env.v` >>
  rw [env_rel_cases]
  >- metis_tac [ALOOKUP_def, NOT_SOME_NONE] >>
  qpat_x_assum `_::_ = _.v` (assume_tac o GSYM) >>
  fs [LIST_REL_CONS1, ALOOKUP_def] >>
  rename1 `ALOOKUP (p::_) _ = SOME _` >>
  Cases_on `p` >>
  fs [ALOOKUP_def] >>
  rename1 `ALOOKUP (p::_) _ = SOME _` >>
  Cases_on `p` >>
  fs [ALOOKUP_def] >>
  rw [] >>
  rw [] >>
  fs [] >>
  first_x_assum (qspec_then `env with v := v` mp_tac) >>
  rw [] >>
  first_x_assum (qspec_then `env' with v := t'` mp_tac) >>
  rw [env_rel_cases]);

val v_rel_bool = Q.prove (
  `!v b. v_rel (Boolv b) v ⇔ v = Boolv b`,
  rw [Once v_rel_cases, Boolv_def, libTheory.the_def]);

val lemma = Q.prove (
  `(\(x,y,z). x) = FST`,
  rw [FUN_EQ_THM] >>
  pairarg_tac >>
  fs []);

val do_opapp_correct = Q.prove (
  `∀vs vs'.
     LIST_REL v_rel vs vs'
     ⇒
     (flatSem$do_opapp vs = NONE ⇒ do_opapp vs' = NONE) ∧
     (!env e.
       do_opapp vs = SOME (env,e) ⇒
       ∃env'. LIST_REL (\(x,v1) (y,v2). x = y ∧ v_rel v1 v2) env env' ∧
              do_opapp vs' = SOME (env', HD (compile [e])))`,
  rw [do_opapp_def] >>
  every_case_tac >>
  fs [] >>
  rw [] >>
  TRY (fs [Once v_rel_cases] >> NO_TAC) >>
  qpat_x_assum `v_rel (Recclosure _ _ _) _` mp_tac >>
  simp [Once v_rel_cases] >>
  CCONTR_TAC >>
  fs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
  rw [] >>
  fs [semanticPrimitivesPropsTheory.find_recfun_ALOOKUP, ALOOKUP_NONE] >>
  imp_res_tac ALOOKUP_MEM >>
  fs [MEM_MAP, lemma, FORALL_PROD] >>
  TRY (pairarg_tac >> fs []) >>
  rw [] >>
  imp_res_tac ALOOKUP_ALL_DISTINCT_MEM >>
  fs [] >>
  rw []
  >- metis_tac [FST]
  >- metis_tac [FST] >>
  fs [build_rec_env_merge, LIST_REL_APPEND_EQ] >>
  fs [EVERY2_MAP, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
  cheat);

val compile_exp_correct = Q.prove (
  `(∀env (s : 'a flatSem$state) es s' r s1 env'.
    evaluate env s es = (s',r) ∧
    r ≠ Rerr (Rabort Rtype_error) ∧
    env_rel env env' ∧
    s_rel s s1
    ⇒
    ?s1' r1.
      result_rel (LIST_REL v_rel) r r1 ∧
      s_rel s' s1' ∧
      evaluate env' s1 (compile es) = (s1', r1)) ∧
   (∀env (s : 'a flatSem$state) v pes err_v s' r s1 env' err_v1 v1.
    evaluate_match env s v pes err_v = (s',r) ∧
    r ≠ Rerr (Rabort Rtype_error) ∧
    env_rel env env' ∧
    s_rel s s1 ∧
    v_rel v v1 ∧
    v_rel err_v err_v1
    ⇒
    ?s1' r1.
      result_rel (LIST_REL v_rel) r r1 ∧
      s_rel s' s1' ∧
      evaluate_match env' s1 v1 (MAP (λ(p,e'). (p,HD (compile [e']))) pes) err_v1 = (s1', r1))`,

  ho_match_mp_tac evaluate_ind >>
  rw [evaluate_def, result_rel_cases, compile_def] >>
  rw [] >>
  TRY (fs [env_rel_cases] >> NO_TAC) >>
  TRY (split_pair_case_tac >> rw []) >>
  TRY (split_pair_case_tac >> rw [])
  >- (
    every_case_tac >>
    fs [] >>
    rw [PULL_EXISTS] >>
    rfs [] >>
    rw [evaluate_append] >>
    res_tac >>
    rw [] >>
    imp_res_tac evaluate_sing >>
    rw [] >>
    res_tac >>
    fs [])
  >- rw [Once v_rel_cases]
  >- (
    every_case_tac >>
    fs [] >>
    imp_res_tac evaluate_sing >>
    rw [] >>
    `?e'. compile [e] = [e']` by metis_tac [compile_sing] >>
    res_tac >>
    fs [] >>
    rw [] >>
    rfs [])
  >- (
    fs [] >>
    `?e'. compile [e] = [e']` by metis_tac [compile_sing] >>
    fs [] >>
    rename [`evaluate env s [e] = (s1, r)`] >>
    Cases_on `r` >>
    fs [] >>
    rw []
    >- (
      res_tac >>
      rw [] >>
      fs [] >>
      rw []) >>
    Cases_on `e''` >>
    rw [] >>
    fs [] >>
    rfs [] >>
    rw [] >>
    fs [] >>
    rfs []
    >- (
      first_x_assum drule >>
      disch_then drule >>
      rw [] >>
      first_x_assum drule >>
      disch_then drule >>
      disch_then drule >>
      disch_then drule >>
      rw [])
    >- (
      first_x_assum drule >>
      disch_then drule >>
      rw []))
  >- (
    rename1 `evaluate _ _ _ = (s1', r')` >>
    Cases_on `r'` >>
    fs [] >>
    rw [] >>
    res_tac >>
    fs [] >>
    rw [] >>
    fs [compile_reverse] >>
    rw [] >>
    simp [Once v_rel_cases, libTheory.the_def])
  >- (
    rename1 `evaluate _ _ _ = (s1', r')` >>
    Cases_on `r'` >>
    fs [] >>
    rw [] >>
    res_tac >>
    fs [] >>
    rw [] >>
    fs [compile_reverse] >>
    rw [] >>
    simp [Once v_rel_cases, libTheory.the_def])
 >- (
    every_case_tac >>
    fs [LIST_REL_def] >>
    metis_tac [alookup_env_rel, NOT_SOME_NONE, SOME_11])
  >- (
    simp [Once v_rel_cases] >>
    fs [env_rel_cases])

  >- (
    fs [] >>
    rename [`evaluate _ _ _ = (s', r')`,
            `evaluate env1 _ (REVERSE (compile _)) = (s1', r1')`] >>
    Cases_on `r'` >>
    fs [] >>
    rw [] >>
    fs []
    >- (
      Cases_on `op = Opapp` >>
      fs []
      >- (
        rename1 `do_opapp (REVERSE vs)` >>
        Cases_on `do_opapp (REVERSE vs)` >>
        fs [] >>
        rw [] >>
        split_pair_case_tac >>
        fs [] >>
        res_tac >>
        fs [] >>
        rw [] >>
        Cases_on `s'.clock = 0` >>
        fs [compile_reverse] >>
        rw [] >>
        `LIST_REL v_rel (REVERSE vs) (REVERSE v')` by metis_tac [EVERY2_REVERSE] >>
        imp_res_tac do_opapp_correct >>
        rw []
        >- fs [s_rel_cases]
        >- fs [s_rel_cases]
        >- fs [s_rel_cases] >>
        `env_rel (env with v := env') (env1 with v := env'')` by fs [env_rel_cases] >>
        `s_rel (dec_clock s') (dec_clock s1')` by fs [dec_clock_def,s_rel_cases] >>
        res_tac >>
        rw [] >>
        metis_tac [HD, compile_sing])
      >- cheat)
    >- (
      res_tac >>
      fs [compile_reverse] >>
      rw []))

  >- (
    rename1 `evaluate _ _ _ = (s1', r')` >>
    Cases_on `r'` >>
    fs [] >>
    rw []
    >- (
      imp_res_tac evaluate_sing >>
      rw [] >>
      fs [] >>
      rename1 `do_if v e2 e3` >>
      Cases_on `do_if v e2 e3` >>
      fs [] >>
      first_x_assum drule >>
      disch_then drule >>
      rw [] >>
      fs [] >>
      `?e'. compile [e1] = [e']` by metis_tac [compile_sing] >>
      fs [] >>
      rw [] >>
      fs [do_if_def] >>
      Cases_on `v = Boolv T` >>
      fs [v_rel_bool]
      >- metis_tac [compile_sing, HD] >>
      rfs [v_rel_bool] >>
      metis_tac [compile_sing, HD])
    >- (
      `?e'. compile [e1] = [e']` by metis_tac [compile_sing] >>
      res_tac >>
      fs [] >>
      rw [] >>
      rfs []))

  >- cheat
  >- cheat
  >- cheat
  >- cheat
  >- cheat);

val _ = export_theory ();

