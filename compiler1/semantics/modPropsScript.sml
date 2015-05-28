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

val no_dup_types_cons_imp = Q.store_thm("no_dup_types_cons_imp",
  `no_dup_types (d::ds) ⇒ no_dup_types ds`,
  rw[decs_to_types_def,no_dup_types_def,ALL_DISTINCT_APPEND]);

val no_dup_mods_eqn = Q.store_thm ("no_dup_mods_eqn",
  `!p ps.
    (no_dup_mods [] (x,y,mods) ⇔ T) ∧
    (no_dup_mods (p::ps) (x,y,mods) ⇔
       (case p of
         | Prompt (SOME mn) ds =>
             ~MEM mn (prog_to_mods ps) ∧ mn ∉ mods
         | Prompt NONE _ => T) ∧
      no_dup_mods ps (x,y,mods))`,
  rw [modSemTheory.no_dup_mods_def, modSemTheory.prog_to_mods_def] >>
  every_case_tac >>
  rw [] >>
  metis_tac []);

val no_dup_top_types_eqn = Q.store_thm ("no_dup_top_types_eqn",
  `!p ps.
    (no_dup_top_types [] (x,tids,y) ⇔ T) ∧
    (no_dup_top_types (p::ps) (x,tids,y) ⇔
       (case p of
         | Prompt NONE ds =>
             ALL_DISTINCT (decs_to_types ds) ∧
             DISJOINT (set (decs_to_types ds)) (set (prog_to_top_types ps)) ∧
             DISJOINT (IMAGE (\tn. TypeId (Short tn)) (set (decs_to_types ds))) tids
         | Prompt (SOME mn) _ => T) ∧
      no_dup_top_types ps (x,tids,y))`,
  rw [no_dup_top_types_def, prog_to_top_types_def] >>
  every_case_tac >>
  rw [ALL_DISTINCT_APPEND, DISJOINT_DEF, EXTENSION] >>
  fs [MEM_MAP] >>
  metis_tac []);

val tids_of_decs_def = Define`
  tids_of_decs ds = set (FLAT (MAP (λd. case d of Dtype mn tds => MAP (mk_id mn o FST o SND) tds | _ => []) ds))`;

val tids_of_decs_thm = Q.store_thm("tids_of_decs_thm",
  `(tids_of_decs [] = {}) ∧
   (tids_of_decs (d::ds) = tids_of_decs ds ∪
     case d of Dtype mn tds => set (MAP (mk_id mn o FST o SND) tds) | _ => {})`,
  simp[tids_of_decs_def] >>
  every_case_tac >> simp[] >>
  metis_tac[UNION_COMM]);

val evaluate_dec_tids_acc = store_thm("evaluate_dec_tids_acc",
  ``∀ck genv envC st d res. evaluate_dec ck genv envC st d res ⇒
      SND st ⊆ SND (FST res)``,
  ho_match_mp_tac modSemTheory.evaluate_dec_ind >> simp[]);

val evaluate_decs_tids_acc = store_thm("evaluate_decs_tids_acc",
  ``∀ck genv envC st ds res. evaluate_decs ck genv envC st ds res ⇒
      SND st ⊆ SND(FST res)``,
  ho_match_mp_tac evaluate_decs_ind >> simp[] >> rw[] >>
  first_x_assum(mp_tac o MATCH_MP evaluate_dec_tids_acc) >>
  fs[] >> metis_tac[SUBSET_TRANS]);

val evaluate_decs_tids = Q.store_thm("evaluate_decs_tids",
  `∀ck genv envC st ds res. evaluate_decs ck genv envC st ds res ⇒
     SND(SND(SND res)) = NONE ⇒
     {id | TypeId id ∈ SND(FST res)} = (tids_of_decs ds) ∪ {id | TypeId id ∈ SND st}`,
  ho_match_mp_tac evaluate_decs_ind >> simp[] >>
  conj_tac >- simp[tids_of_decs_thm] >>
  rw[modSemTheory.evaluate_dec_cases,tids_of_decs_thm] >> fs[] >>
  simp[EXTENSION,semanticPrimitivesTheory.type_defs_to_new_tdecs_def,MEM_MAP,PULL_EXISTS,UNCURRY] >>
  metis_tac[])

val evaluate_decs_tids_disjoint = Q.store_thm("evaluate_decs_tids_disjoint",
  `∀ck genv envC st ds res. evaluate_decs ck genv envC st ds res ⇒
     SND(SND(SND res)) = NONE ⇒
     DISJOINT (IMAGE TypeId (tids_of_decs ds)) (SND st)`,
  ho_match_mp_tac evaluate_decs_ind >> simp[] >>
  conj_tac >- simp[tids_of_decs_thm] >>
  rw[modSemTheory.evaluate_dec_cases,tids_of_decs_thm] >> fs[DISJOINT_SYM] >>
  fs[semanticPrimitivesTheory.type_defs_to_new_tdecs_def,IN_DISJOINT,MEM_MAP,UNCURRY] >>
  metis_tac[]);

val tids_of_prompt_def = Define`
  tids_of_prompt (Prompt _ ds) = tids_of_decs ds`;

val evaluate_prompt_tids_disjoint = prove(
  ``∀ck genv envC stm p res. evaluate_prompt ck genv envC stm p res ⇒
      SND(SND(SND res)) = NONE ⇒
      DISJOINT (IMAGE TypeId (tids_of_prompt p)) (FST(SND stm))``,
  ho_match_mp_tac modSemTheory.evaluate_prompt_ind >> simp[] >> rw[] >>
  imp_res_tac evaluate_decs_tids_disjoint >> fs[tids_of_prompt_def]);

val evaluate_prompt_tids_acc = prove(
  ``∀ck genv envC stm p res. evaluate_prompt ck genv envC stm p res ⇒
      FST(SND stm) ⊆ FST(SND(FST res))``,
  ho_match_mp_tac modSemTheory.evaluate_prompt_ind >> simp[] >> rw[] >>
  imp_res_tac evaluate_decs_tids_acc >> fs[]);

val evaluate_prompt_tids = Q.store_thm("evaluate_prompt_tids",
  `∀ck genv envC stm p res. evaluate_prompt ck genv envC stm p res ⇒
     SND(SND(SND res)) = NONE ⇒
     {id | TypeId id ∈ FST(SND(FST res))} = (tids_of_prompt p) ∪ {id | TypeId id ∈ FST(SND stm)}`,
  ho_match_mp_tac modSemTheory.evaluate_prompt_ind >> simp[] >> rw[] >>
  imp_res_tac evaluate_decs_tids >> fs[tids_of_prompt_def]);

val evaluate_prompt_mods_disjoint = Q.store_thm("evaluate_prompt_mods_disjoint",
  `∀ck genv envC stm p res. evaluate_prompt ck genv envC stm p res ⇒
     SND(SND(SND res)) = NONE ⇒
     ∀mn ds. p = Prompt (SOME mn) ds ⇒ mn ∉ (SND(SND stm))`,
  ho_match_mp_tac modSemTheory.evaluate_prompt_ind >> simp[]);

val _ = export_theory()
