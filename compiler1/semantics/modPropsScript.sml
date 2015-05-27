open preamble alistTheory modSemTheory
local open astTheory evalPropsTheory terminationTheory in end

val _ = new_theory"modProps"

val pat_bindings_def = astTheory.pat_bindings_def
val pat_bindings_accum = evalPropsTheory.pat_bindings_accum

val pmatch_extend = Q.store_thm("pmatch_extend",
  `(!cenv s p v env env' env''.
    pmatch cenv s p v env = Match env'
    ⇒
    ?env''. env' = env'' ++ env ∧ MAP FST env'' = pat_bindings p []) ∧
   (!cenv s ps vs env env' env''.
    pmatch_list cenv s ps vs env = Match env'
    ⇒
    ?env''. env' = env'' ++ env ∧ MAP FST env'' = pats_bindings ps [])`,
  ho_match_mp_tac pmatch_ind >>
  rw [pat_bindings_def, pmatch_def] >>
  every_case_tac >>
  fs [] >>
  rw [] >>
  res_tac >>
  qexists_tac `env'''++env''` >>
  rw [] >>
  metis_tac [pat_bindings_accum]);

val build_rec_env_help_lem = Q.prove (
  `∀funs env funs'.
  FOLDR (λ(f,x,e) env'. (f, Recclosure env funs' f)::env') env' funs =
  MAP (λ(fn,n,e). (fn, Recclosure env funs' fn)) funs ++ env'`,
  Induct >>
  rw [] >>
  PairCases_on `h` >>
  rw []);

(* Alternate definition for build_rec_env *)
val build_rec_env_merge = Q.store_thm ("build_rec_env_merge",
  `∀funs funs' env env'.
    build_rec_env funs env env' =
    MAP (λ(fn,n,e). (fn, Recclosure env funs fn)) funs ++ env'`,
  rw [build_rec_env_def, build_rec_env_help_lem]);

val Boolv_11 = store_thm("Boolv_11[simp]",``Boolv b1 = Boolv b2 ⇔ (b1 = b2)``,rw[Boolv_def]);

val evaluate_con = Q.store_thm("evaluate_con",
  `evaluate a0 a1 a2 (Con cn es) a4 ⇔
        (∃vs s' v.
           a4 = (s',Rval v) ∧
           do_con_check (all_env_to_cenv a1) cn (LENGTH es) ∧
           build_conv (all_env_to_cenv a1) cn (REVERSE vs) = SOME v ∧
           evaluate_list a0 a1 a2 (REVERSE es) (s',Rval vs)) ∨
        (∃err s'.
           a4 = (s',Rerr err) ∧
           do_con_check (all_env_to_cenv a1) cn (LENGTH es) ∧
           evaluate_list a0 a1 a2 (REVERSE es) (s',Rerr err))`,
  rw [Once modSemTheory.evaluate_cases] >>
  eq_tac >>
  rw []);

val evaluate_list_vars = Q.store_thm("evaluate_list_vars",
  `!b genv cenv env c s env'.
    ALL_DISTINCT (MAP FST env) ∧
    DISJOINT (set (MAP FST env)) (set (MAP FST env'))
    ⇒
    evaluate_list b (genv,cenv,env'++env) (c,s)
      (MAP Var_local (MAP FST env)) ((c,s),Rval (MAP SND env))`,
  induct_on `env` >>
  rw [Once evaluate_cases] >>
  rw [Once evaluate_cases, modSemTheory.all_env_to_env_def]
  >- (PairCases_on `h` >>
      fs [ALOOKUP_APPEND] >>
      full_case_tac >>
      imp_res_tac ALOOKUP_MEM >>
      metis_tac [MEM_MAP, FST])
  >- (FIRST_X_ASSUM (qspecl_then [`b`, `genv`, `cenv`, `c`, `s`, `env'++[h]`] mp_tac) >>
      rw [] >>
      metis_tac [DISJOINT_SYM, APPEND, APPEND_ASSOC]));

val pmatch_evaluate_list = Q.store_thm("pmatch_evaluate_list",
  `(!cenv s p v env env'.
    pmatch cenv s p v env = Match env' ∧
    ALL_DISTINCT (pat_bindings p (MAP FST env))
    ⇒
    evaluate_list b (genv,cenv,env') (c,s,t) (MAP Var_local (pat_bindings p (MAP FST env))) ((c,s,t),Rval (MAP SND env'))) ∧
   (!cenv s ps vs env env'.
    pmatch_list cenv s ps vs env = Match env' ∧
    ALL_DISTINCT (pats_bindings ps (MAP FST env))
    ⇒
    evaluate_list b (genv,cenv,env') (c,s,t) (MAP Var_local (pats_bindings ps (MAP FST env))) ((c,s,t),Rval (MAP SND env')))`,
  ho_match_mp_tac pmatch_ind >>
  rw [pat_bindings_def, pmatch_def]
  >- (rw [Once evaluate_cases] >>
      rw [Once evaluate_cases, modSemTheory.all_env_to_env_def] >>
      `DISJOINT (set (MAP FST env)) (set (MAP FST [(x,v)]))`
                   by rw [DISJOINT_DEF, EXTENSION] >>
      metis_tac [evaluate_list_vars, APPEND, APPEND_ASSOC])
  >- (`DISJOINT (set (MAP FST env)) (set (MAP FST ([]:(varN,modSem$v) alist)))`
                   by rw [DISJOINT_DEF, EXTENSION] >>
      metis_tac [evaluate_list_vars, APPEND, APPEND_ASSOC])
  >- (every_case_tac >>
      fs [])
  >- (every_case_tac >>
      fs [])
  >- (`DISJOINT (set (MAP FST env)) (set (MAP FST ([]:(varN,modSem$v) alist)))`
                   by rw [DISJOINT_DEF, EXTENSION] >>
      metis_tac [evaluate_list_vars, APPEND, APPEND_ASSOC])
  >- (every_case_tac >>
      fs [] >>
      `ALL_DISTINCT (pat_bindings p (MAP FST env))`
              by fs [Once pat_bindings_accum, ALL_DISTINCT_APPEND] >>
      `MAP FST a = pat_bindings p (MAP FST env)`
                   by (imp_res_tac pmatch_extend >>
                       rw [] >>
                       metis_tac [pat_bindings_accum]) >>
      metis_tac []));

val evaluate_list_reverse = Q.store_thm("evaluate_list_reverse",
  `!b env s es s' vs.
    evaluate_list b env s (MAP Var_local es) (s, Rval vs)
    ⇒
    evaluate_list b env s (MAP Var_local (REVERSE es)) (s, Rval (REVERSE vs))`,
  induct_on `es` >>
  rw []
  >- fs [Once evaluate_cases] >>
  pop_assum (mp_tac o SIMP_RULE (srw_ss()) [Once evaluate_cases]) >>
  rw [] >>
  fs [Once (hd (CONJUNCTS evaluate_cases))] >>
  rw [] >>
  res_tac >>
  pop_assum mp_tac >>
  pop_assum (fn _ => all_tac) >>
  pop_assum mp_tac >>
  pop_assum (fn _ => all_tac) >>
  Q.SPEC_TAC (`REVERSE vs'`, `vs`) >>
  Q.SPEC_TAC (`REVERSE es`, `es`) >>
  induct_on `es` >>
  rw []
  >- (ntac 3 (rw [Once evaluate_cases]) >>
      fs [Once evaluate_cases]) >>
  rw [] >>
  pop_assum (mp_tac o SIMP_RULE (srw_ss()) [Once evaluate_cases]) >>
  rw [] >>
  fs [Once (hd (CONJUNCTS evaluate_cases))] >>
  rw [] >>
  res_tac >>
  rw [Once evaluate_cases] >>
  qexists_tac `s` >>
  rw [] >>
  rw [Once evaluate_cases]);

val _ = export_theory()
