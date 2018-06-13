open preamble;
open flatLangTheory flatSemTheory flatPropsTheory flat_uncheck_ctorsTheory;

val _ = new_theory "flat_uncheck_ctorsProof";

(* TODO: move? *)

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

val compile_HD_sing = Q.store_thm("compile_HD_sing",
  `[HD (compile [e])] = compile [e]`,
  qspec_then`e`strip_assume_tac compile_sing
  \\ fs[]);

(* -- *)

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

val (s_rel_rules, s_rel_ind, s_rel_cases) = Hol_reln `
  (!s s'.
    s.clock = s'.clock ∧
    LIST_REL (sv_rel v_rel) s.refs s'.refs ∧
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

val v_rel_bool = Q.store_thm("v_rel_bool[simp]",
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
  qpat_x_assum`¬_`mp_tac
  \\ simp[Once v_rel_cases]
  \\ simp[LIST_REL_EL_EQN,UNCURRY]);

val s_rel_store_assign = Q.prove (
  `s_rel s1 s1' ∧
   v_rel v v' ∧
   store_assign l (Refv v) s1.refs = SOME v1 ⇒
   ∃v1'. store_assign l (Refv v') s1'.refs = SOME v1' ∧
         s_rel (s1 with refs := v1) (s1' with refs := v1')`,
  rw [semanticPrimitivesTheory.store_assign_def, s_rel_cases]
  >- metis_tac [LIST_REL_LENGTH] >>
  fs [semanticPrimitivesTheory.store_v_same_type_def, LIST_REL_EL_EQN, EL_LUPDATE] >>
  rw[] \\ every_case_tac >> fs [] >> rw [] >>
  res_tac >>
  fs[semanticPrimitivesPropsTheory.sv_rel_cases] >>
  rw [] >>
  fs []);

val s_rel_store_alloc = Q.prove (
  `s_rel s1 s1' ∧
   v_rel v v' ∧
   store_alloc (Refv v) s1.refs = (s,n) ⇒
   ∃s'. store_alloc (Refv v') s1'.refs = (s',n) ∧
           s_rel (s1 with refs := s) (s1' with refs := s')`,
  rw [semanticPrimitivesTheory.store_alloc_def, s_rel_cases]
  \\ fs[LIST_REL_EL_EQN]);

val sv_rel_store_alloc = Q.prove (
  `s_rel s1 s1' ∧
   sv_rel v_rel sv sv' ∧
   store_alloc sv s1.refs = (s,n) ⇒
   ∃s' n'. store_alloc sv' s1'.refs = (s',n')`,
  rw [semanticPrimitivesPropsTheory.sv_rel_cases, semanticPrimitivesTheory.store_alloc_def, s_rel_cases]);

val s_rel_store_lookup = Q.prove (
  `s_rel s1 s1' ∧
   store_lookup n s1.refs = SOME sv ⇒
   ∃sv'. store_lookup n s1'.refs = SOME sv' ∧ sv_rel v_rel sv sv'`,
  rw [semanticPrimitivesTheory.store_lookup_def, s_rel_cases] >>
  fs [LIST_REL_EL_EQN] >>
  res_tac >>
  fs [semanticPrimitivesPropsTheory.sv_rel_cases] >>
  fs []);

val v_rel_eqn = Q.store_thm("v_rel_eqn[simp]",
 `(!lit v. v_rel (flatSem$Litv lit) v ⇔ v = Litv lit) ∧
  (!lit v. v_rel v (flatSem$Litv lit) ⇔ v = Litv lit) ∧
  (v_rel (Conv NONE []) (Conv (SOME (0,NONE)) [])) ∧
  (v_rel subscript_exn_v subscript_exn_v) ∧
  (v_rel bind_exn_v bind_exn_v) ∧
  (!loc l. v_rel (Loc loc) l ⇔ l = Loc loc) ∧
  (!loc l. v_rel l (Loc loc) ⇔ l = Loc loc) ∧
  (!vs v. v_rel (Vectorv vs) v ⇔ ∃vs'. v = Vectorv vs' ∧ LIST_REL v_rel vs vs') ∧
  (!vs v. v_rel v (Vectorv vs) ⇔ ∃vs'. v = Vectorv vs' ∧ LIST_REL v_rel vs' vs)`,
  rw [flatSemTheory.subscript_exn_v_def, flatSemTheory.bind_exn_v_def] >>
  ONCE_REWRITE_TAC [v_rel_cases] >>
  rw [libTheory.the_def]);

val do_app_correct = Q.prove (
  `∀s1 s1' s2 op vs vs' r.
     LIST_REL v_rel vs vs' ∧
     s_rel s1 s1' ∧
     do_app T s1 op vs = SOME (s2,r) ⇒
     ∃r' s2'. do_app F s1' op vs' = SOME (s2', r') ∧
              s_rel s2 s2' ∧
              result_rel v_rel v_rel r r'`,
  rw [do_app_cases] >>
  fs [] >>
  rw [] >>
  TRY (
    qmatch_rename_tac`v_rel _ _`
    \\ EVAL_TAC
    \\ rw[Once v_rel_cases]
    \\ EVAL_TAC
    \\ rw[] \\ NO_TAC )
  \\ fs [PULL_EXISTS] >>
  TRY (
    imp_res_tac s_rel_store_lookup >>
    fs [semanticPrimitivesPropsTheory.sv_rel_cases] >>
    NO_TAC)
  >> TRY ( fsrw_tac[DNF_ss][] >> fs[LIST_REL_EL_EQN] >> NO_TAC)
  >- cheat (* do_eq *)
  >- metis_tac [s_rel_store_assign]
  >- metis_tac [semanticPrimitivesPropsTheory.sv_rel_cases, s_rel_store_alloc]
  >- (
    fs[semanticPrimitivesTheory.store_alloc_def, s_rel_cases]
    \\ rw[] \\ fs[LIST_REL_EL_EQN] )
  >- (
    fsrw_tac[DNF_ss][] >>
    imp_res_tac s_rel_store_lookup >>
    fs [semanticPrimitivesPropsTheory.sv_rel_cases] )
  >- (
    fsrw_tac[DNF_ss][] >>
    imp_res_tac s_rel_store_lookup >>
    fs[semanticPrimitivesTheory.store_assign_def] >> rw[] >>
    fs [semanticPrimitivesPropsTheory.sv_rel_cases] >>
    fs [s_rel_cases] >>
    fs[EVERY2_LUPDATE_same] >>
    fs[LIST_REL_EL_EQN, semanticPrimitivesTheory.store_lookup_def] >>
    EVAL_TAC)
  >- (
    imp_res_tac s_rel_store_lookup >>
    fs [semanticPrimitivesPropsTheory.sv_rel_cases] >>
    fsrw_tac[DNF_ss][] )
  >- cheat (* copy_array *)
  >- cheat (* copy_array *)
  >- cheat (* v_to_char_list *)
  >- cheat (* v_to_list, vs_to_string *)
  >- cheat (* v_to_list *)
  >- (
    fs[semanticPrimitivesTheory.store_alloc_def]
    \\ fs[s_rel_cases]
    \\ rw[LIST_REL_REPLICATE_same]
    \\ fs[LIST_REL_EL_EQN] )
  >- (
    fsrw_tac[DNF_ss][]
    \\ imp_res_tac s_rel_store_lookup
    \\ fs[semanticPrimitivesPropsTheory.sv_rel_cases]
    \\ fs[LIST_REL_EL_EQN] )
  >- (
    fsrw_tac[DNF_ss][]
    \\ imp_res_tac s_rel_store_lookup
    \\ fs[semanticPrimitivesPropsTheory.sv_rel_cases]
    \\ fs[LIST_REL_EL_EQN] )
  >- (
    fsrw_tac[DNF_ss][]
    \\ imp_res_tac s_rel_store_lookup
    \\ fs[semanticPrimitivesPropsTheory.sv_rel_cases]
    \\ fs[LIST_REL_EL_EQN] )
  >- (
    imp_res_tac s_rel_store_lookup >>
    fs [semanticPrimitivesPropsTheory.sv_rel_cases]
    \\ fs[LIST_REL_EL_EQN] )
  >- (
    fsrw_tac[DNF_ss][]
    \\ imp_res_tac s_rel_store_lookup
    \\ fs[semanticPrimitivesPropsTheory.sv_rel_cases]
    \\ fs[semanticPrimitivesTheory.store_assign_def]
    \\ fs[s_rel_cases]
    \\ rw[EVERY2_LUPDATE_same]
    \\ fs[LIST_REL_EL_EQN]
    \\ fs[semanticPrimitivesTheory.store_lookup_def]
    \\ rfs[semanticPrimitivesTheory.store_v_same_type_def] )
  >- (
    fsrw_tac[DNF_ss][]
    \\ imp_res_tac s_rel_store_lookup
    \\ fs[semanticPrimitivesPropsTheory.sv_rel_cases]
    \\ fs[semanticPrimitivesTheory.store_lookup_def]
    \\ rw[] \\ fs[LIST_REL_EL_EQN] )
  >- (
    fsrw_tac[DNF_ss][]
    \\ imp_res_tac s_rel_store_lookup
    \\ fs[semanticPrimitivesPropsTheory.sv_rel_cases]
    \\ fs[semanticPrimitivesTheory.store_lookup_def]
    \\ rw[] \\ fs[LIST_REL_EL_EQN] )
  >- cheat (* v_to_list *)
  >- cheat (* call_FFI *)
  >- (
    fs[s_rel_cases]
    \\ match_mp_tac EVERY2_APPEND_suff
    \\ fs[LIST_REL_REPLICATE_same, OPTREL_def] )
  >- (
    fsrw_tac[DNF_ss][]
    \\ fs[s_rel_cases]
    \\ fs[LIST_REL_EL_EQN, EL_LUPDATE]
    \\ res_tac \\ fs[OPTREL_def] \\ rfs[]
    \\ rw[] )
  >- (
    fsrw_tac[DNF_ss][]
    \\ fs[s_rel_cases]
    \\ fs[LIST_REL_EL_EQN, EL_LUPDATE]
    \\ res_tac \\ fs[OPTREL_def] \\ rfs[]
    \\ rw[] )
  >- (
    fsrw_tac[DNF_ss][]
    \\ fs[s_rel_cases]
    \\ fs[LIST_REL_EL_EQN, EL_LUPDATE]
    \\ res_tac \\ fs[OPTREL_def] \\ rfs[]
    \\ rw[] \\ fs[]));

val compile_exp_correct = Q.prove (
  `(∀env (s : 'a flatSem$state) es s' r s1 env'.
    evaluate env s es = (s',r) ∧
    r ≠ Rerr (Rabort Rtype_error) ∧
    env_rel env env' ∧
    s_rel s s1
    ⇒
    ?s1' r1.
      result_rel (LIST_REL v_rel) v_rel r r1 ∧
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
      result_rel (LIST_REL v_rel) v_rel r r1 ∧
      s_rel s' s1' ∧
      evaluate_match env' s1 v1 (MAP (λ(p,e'). (p,HD (compile [e']))) pes) err_v1 = (s1', r1))`,
  ho_match_mp_tac evaluate_ind >>
  rw [evaluate_def, compile_def] >>
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
      >- (
        first_x_assum drule
        \\ disch_then drule
        \\ strip_tac
        \\ rveq \\ fs[]
        \\ qpat_x_assum`_ = (_, r)`mp_tac
        \\ TOP_CASE_TAC \\ strip_tac \\ fs[pair_case_eq]
        \\ imp_res_tac EVERY2_REVERSE
        \\ drule do_app_correct
        \\ disch_then drule
        \\ rveq
        \\ fs[env_rel_cases] \\ rfs[]
        \\ disch_then drule
        \\ strip_tac
        \\ goal_assum (first_assum o mp_then Any mp_tac)
        \\ fs[compile_reverse]
        \\ rveq \\ fs[]))
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
  >- (
    every_case_tac >>
    fs [] >>
    imp_res_tac evaluate_sing >>
    rw [] >>
    `?e'. compile [e] = [e']` by metis_tac [compile_sing] >>
    res_tac >>
    fs [] >>
    rw [] >>
    rfs [] >>
    metis_tac[v_rel_eqn] )
  >- (
    reverse(fsrw_tac[DNF_ss][case_eq_thms, compile_HD_sing] \\ rveq \\ fs[])
    \\ first_x_assum drule \\ disch_then drule
    \\ strip_tac \\ fs[] \\ rveq
    >- metis_tac[]
    \\ fs[]
    \\ first_x_assum match_mp_tac
    \\ fs[env_rel_cases, libTheory.opt_bind_def]
    \\ CASE_TAC \\ fs[]
    \\ imp_res_tac evaluate_sing \\ fs[] )
  >- (
    fs[compile_HD_sing]
    \\ first_x_assum match_mp_tac
    \\ fs[env_rel_cases]
    \\ fs[build_rec_env_merge]
    \\ match_mp_tac EVERY2_APPEND_suff
    \\ fs[MAP_MAP_o, o_DEF, UNCURRY, EVERY2_MAP]
    \\ simp[Once v_rel_cases]
    \\ fs[EVERY2_refl] )
  >- fs[MAP_MAP_o,o_DEF,UNCURRY,ETA_AX]
  >- (
    cheat (* pmatch *)
  ));

(* TODO: compile_decs_correct *)

val _ = export_theory ();
