open preamble modSemTheory
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

val evaluate_length = Q.store_thm("evaluate_length",
  `(∀env (s:'ffi modSem$state) ls s' vs.
      evaluate env s ls = (s',Rval vs) ⇒ LENGTH vs = LENGTH ls) ∧
   (∀env (s:'ffi modSem$state) v pes ev s' vs.
      evaluate_match env s v pes ev = (s', Rval vs) ⇒ LENGTH vs = 1)`,
  ho_match_mp_tac evaluate_ind >>
  rw[evaluate_def] >> rw[] >>
  every_case_tac >> fs[] >> rw[]);

val evaluate_cons = Q.store_thm("evaluate_cons",
  `evaluate env s (e::es) =
   (case evaluate env s [e] of
    | (s,Rval v) =>
      (case evaluate env s es of
       | (s,Rval vs) => (s,Rval (v++vs))
       | r => r)
    | r => r)`,
  Cases_on`es`>>rw[evaluate_def] >>
  every_case_tac >> fs[evaluate_def] >>
  imp_res_tac evaluate_length >> fs[SING_HD]);

val evaluate_sing = Q.store_thm("evaluate_sing",
  `(evaluate env s [e] = (s',Rval vs) ⇒ ∃y. vs = [y]) ∧
   (evaluate_match env s v pes ev = (s',Rval vs) ⇒ ∃y. vs = [y])`,
  rw[] >> imp_res_tac evaluate_length >> fs[] >> metis_tac[SING_HD])

val evaluate_add_to_clock = Q.store_thm("evaluate_add_to_clock",
  `(∀env (s:'ffi modSem$state) es s' r.
       evaluate env s es = (s',r) ∧
       r ≠ Rerr (Rabort Rtimeout_error) ⇒
       evaluate env (s with clock := s.clock + extra) es =
         (s' with clock := s'.clock + extra,r)) ∧
   (∀env (s:'ffi modSem$state) pes v err_v s' r.
       evaluate_match env s pes v err_v = (s',r) ∧
       r ≠ Rerr (Rabort Rtimeout_error) ⇒
       evaluate_match env (s with clock := s.clock + extra) pes v err_v =
         (s' with clock := s'.clock + extra,r))`,
  ho_match_mp_tac evaluate_ind >>
  rw[evaluate_def] >>
  every_case_tac >> fs[] >> rw[] >> rfs[] >>
  rev_full_simp_tac(srw_ss()++ARITH_ss)[dec_clock_def]);

val evaluate_vars = Q.store_thm("evaluate_vars",
  `!env s kvs env' ks vs.
    ALL_DISTINCT (MAP FST kvs) ∧
    DISJOINT (set (MAP FST kvs)) (set (MAP FST env')) ∧
    env.v = env' ++ kvs ∧ ks = MAP FST kvs ∧ vs = MAP SND kvs
    ⇒
    evaluate env s (MAP Var_local ks) = (s,Rval vs)`,
  induct_on `kvs` >> rw[evaluate_def] >>
  rw[Once evaluate_cons,evaluate_def] >>
  PairCases_on`h`>>rw[]>> fs[] >>
  rw[ALOOKUP_APPEND] >>
  reverse BasicProvers.CASE_TAC >>
  imp_res_tac ALOOKUP_MEM >- metis_tac[MEM_MAP,FST] >>
  first_x_assum(qspecl_then[`env`,`s`]mp_tac) >>
  fs[DISJOINT_SYM]);

val with_same_v = Q.store_thm("with_same_v[simp]",
  `env with v := env.v = env`,
  rw[environment_component_equality])

val pmatch_evaluate_vars = Q.store_thm("pmatch_evaluate_vars",
  `(!cenv refs p v evs env env'.
    (cenv,refs,evs) = (env.c,s.refs,env.v) ∧
    pmatch env.c s.refs p v env.v = Match env' ∧
    ALL_DISTINCT (pat_bindings p (MAP FST env.v))
    ⇒
    evaluate (env with v := env') s (MAP Var_local (pat_bindings p (MAP FST evs))) = (s,Rval (MAP SND env'))) ∧
   (!cenv refs ps vs evs env env'.
    (cenv,refs,evs) = (env.c,s.refs,env.v) ∧
    pmatch_list env.c s.refs ps vs env.v = Match env' ∧
    ALL_DISTINCT (pats_bindings ps (MAP FST env.v))
    ⇒
    evaluate (env with v := env') s (MAP Var_local (pats_bindings ps (MAP FST evs))) = (s,Rval (MAP SND env')))`,
  ho_match_mp_tac pmatch_ind >>
  rw [pat_bindings_def, pmatch_def]
  >- (
    ONCE_REWRITE_TAC[GSYM MAP] >>
    match_mp_tac evaluate_vars >> rw[] >>
    qexists_tac`(x,v)::env.v` >> rw[] )
  >- (
    match_mp_tac evaluate_vars >> rw[] >>
    first_assum(match_exists_tac o concl) >> simp[] )
  >- (
    first_x_assum (match_mp_tac o MP_CANON) >>
    every_case_tac >> fs[] )
  >- (
    first_x_assum (match_mp_tac o MP_CANON) >>
    every_case_tac >> fs[] )
  >- (
    first_x_assum (match_mp_tac o MP_CANON) >>
    every_case_tac >> fs[] )
  >- (
    match_mp_tac evaluate_vars >> rw[] >>
    first_assum(match_exists_tac o concl) >> simp[] )
  >- (
    every_case_tac >> fs[] >>
    `ALL_DISTINCT (pat_bindings p (MAP FST env.v))`
            by fs [Once pat_bindings_accum, ALL_DISTINCT_APPEND] >>
    `pat_bindings p (MAP FST env.v) = MAP FST a`
                 by (imp_res_tac pmatch_extend >>
                     rw [] >>
                     metis_tac [pat_bindings_accum]) >>
    fsrw_tac[QUANT_INST_ss[record_default_qp]][] >> rfs[] >>
    `env with v := env' = <| globals := env.globals; c := env.c; v := env' |>` by (
      rw[environment_component_equality]) >> metis_tac[]));

val evaluate_append = Q.store_thm("evaluate_append",
  `∀env s s1 s2 e1 e2 v1 v2.
   evaluate env s e1 = (s1, Rval v1) ∧
   evaluate env s1 e2 = (s2, Rval v2) ⇒
   evaluate env s (e1++e2) = (s2, Rval (v1++v2))`,
  Induct_on`e1`>>rw[evaluate_def] >>
  fs[Once evaluate_cons] >>
  every_case_tac >> fs[] >> rw[] >>
  res_tac >> fs[]);

val evaluate_vars_reverse = Q.store_thm("evaluate_vars_reverse",
  `!env s es s' vs.
    evaluate env s (MAP Var_local es) = (s, Rval vs)
    ⇒
    evaluate env s (MAP Var_local (REVERSE es)) = (s, Rval (REVERSE vs))`,
  induct_on `es` >> rw [evaluate_def] >> rw[] >>
  pop_assum mp_tac >>
  rw[Once evaluate_cons] >>
  every_case_tac >> fs[] >> rw[] >>
  fs[evaluate_def] >>
  every_case_tac >> fs[] >> rw[] >>
  match_mp_tac evaluate_append >>
  rw[evaluate_def]);

val no_dup_types_cons_imp = Q.store_thm("no_dup_types_cons_imp",
  `no_dup_types (d::ds) ⇒ no_dup_types ds`,
  rw[decs_to_types_def,no_dup_types_def,ALL_DISTINCT_APPEND]);

val no_dup_mods_eqn = Q.store_thm ("no_dup_mods_eqn",
  `!p ps.
    (no_dup_mods [] mods ⇔ T) ∧
    (no_dup_mods (p::ps) mods ⇔
       (case p of
         | Prompt (SOME mn) ds =>
             ~MEM mn (prog_to_mods ps) ∧ mn ∉ mods
         | Prompt NONE _ => T) ∧
      no_dup_mods ps mods)`,
  rw [modSemTheory.no_dup_mods_def, modSemTheory.prog_to_mods_def] >>
  every_case_tac >>
  rw [] >>
  metis_tac []);

val no_dup_top_types_eqn = Q.store_thm ("no_dup_top_types_eqn",
  `!p ps.
    (no_dup_top_types [] tids ⇔ T) ∧
    (no_dup_top_types (p::ps) tids ⇔
       (case p of
         | Prompt NONE ds =>
             ALL_DISTINCT (decs_to_types ds) ∧
             DISJOINT (set (decs_to_types ds)) (set (prog_to_top_types ps)) ∧
             DISJOINT (IMAGE (\tn. TypeId (Short tn)) (set (decs_to_types ds))) tids
         | Prompt (SOME mn) _ => T) ∧
      no_dup_top_types ps tids)`,
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

val dec_clock_const = Q.store_thm("dec_clock_const[simp]",
  `(dec_clock s).defined_types = s.defined_types ∧
   (dec_clock s).defined_mods = s.defined_mods`,
   EVAL_TAC)

val evaluate_state_const = Q.store_thm("evaluate_state_const",
  `(∀env (s:'ffi modSem$state) ls s' vs.
      evaluate env s ls = (s',vs) ⇒
      s'.defined_types = s.defined_types ∧
      s'.defined_mods = s.defined_mods) ∧
   (∀env (s:'ffi modSem$state) v pes ev s' vs.
      evaluate_match env s v pes ev = (s', vs) ⇒
      s'.defined_types = s.defined_types ∧
      s'.defined_mods = s.defined_mods)`,
  ho_match_mp_tac evaluate_ind >>
  rw[evaluate_def] >> rw[] >>
  every_case_tac >> fs[] >> rw[]);

val evaluate_dec_tids_acc = store_thm("evaluate_dec_tids_acc",
  ``∀env st d res. evaluate_dec env st d = res ⇒
      st.defined_types ⊆ (FST res).defined_types``,
  Cases_on`d`>>rw[evaluate_dec_def] >> rw[] >>
  BasicProvers.CASE_TAC >>
  imp_res_tac evaluate_state_const >>
  every_case_tac >> rw[]);

val evaluate_decs_tids_acc = store_thm("evaluate_decs_tids_acc",
  ``∀env st ds res. evaluate_decs env st ds = res ⇒
      st.defined_types ⊆ (FST res).defined_types``,
  Induct_on`ds`>>rw[evaluate_decs_def]>>rw[]>>
  every_case_tac >> fs[]>>
  imp_res_tac evaluate_dec_tids_acc >> fs[] >>
  metis_tac[FST,SUBSET_TRANS]);

val evaluate_decs_tids = Q.store_thm("evaluate_decs_tids",
  `∀env st ds res. evaluate_decs env st ds = res ⇒
     SND(SND(SND res)) = NONE ⇒
     {id | TypeId id ∈ (FST res).defined_types} = (tids_of_decs ds) ∪ {id | TypeId id ∈ st.defined_types}`,
  Induct_on`ds`>>rw[evaluate_decs_def]>>fs[tids_of_decs_thm]>>
  every_case_tac>>fs[evaluate_dec_def,LET_THM]>>rw[]>>
  every_case_tac>>fs[]>>rw[]>>
  fs[EXTENSION,semanticPrimitivesTheory.type_defs_to_new_tdecs_def,MEM_MAP,PULL_EXISTS,UNCURRY] >>
  qmatch_assum_abbrev_tac`evaluate_decs env' st' _ = _` >>
  last_x_assum(qspecl_then[`env'`,`st'`]mp_tac)>>rw[]>>
  unabbrev_all_tac >> fs[]>>
  fs[EXTENSION,semanticPrimitivesTheory.type_defs_to_new_tdecs_def,MEM_MAP,PULL_EXISTS,UNCURRY] >>
  metis_tac[evaluate_state_const]);

val evaluate_decs_tids_disjoint = Q.store_thm("evaluate_decs_tids_disjoint",
  `∀env st ds res. evaluate_decs env st ds = res ⇒
     SND(SND(SND res)) = NONE ⇒
     DISJOINT (IMAGE TypeId (tids_of_decs ds)) st.defined_types`,
  Induct_on`ds`>>rw[evaluate_decs_def]>>fs[tids_of_decs_thm]>>
  every_case_tac >> fs[evaluate_dec_def,LET_THM] >> rw[] >>
  every_case_tac>>fs[]>>rw[]>>
  qmatch_assum_abbrev_tac`evaluate_decs env' st' _ = _` >>
  last_x_assum(qspecl_then[`env'`,`st'`]mp_tac)>>rw[]>>
  unabbrev_all_tac >> fs[]>>
  fs[semanticPrimitivesTheory.type_defs_to_new_tdecs_def,IN_DISJOINT,MEM_MAP,UNCURRY] >>
  metis_tac[evaluate_state_const]);

val tids_of_prompt_def = Define`
  tids_of_prompt (Prompt _ ds) = tids_of_decs ds`;

val evaluate_prompt_tids_disjoint = prove(
  ``∀env s p res. evaluate_prompt env s p = res ⇒
      SND(SND(SND res)) = NONE ⇒
      DISJOINT (IMAGE TypeId (tids_of_prompt p)) s.defined_types``,
  Cases_on`p`>>rw[evaluate_prompt_def]>>fs[tids_of_prompt_def]>>
  fs[LET_THM,UNCURRY] >> metis_tac[evaluate_decs_tids_disjoint]);

val evaluate_prompt_tids_acc = prove(
  ``∀env s p res. evaluate_prompt env s p = res ⇒
      s.defined_types ⊆ (FST res).defined_types``,
  Cases_on`p`>>rw[evaluate_prompt_def]>>fs[]>>
  metis_tac[evaluate_decs_tids_acc,FST]);

val evaluate_prompt_tids = Q.store_thm("evaluate_prompt_tids",
  `∀env s p res. evaluate_prompt env s p = res ⇒
     SND(SND(SND res)) = NONE ⇒
     {id | TypeId id ∈ (FST res).defined_types} = (tids_of_prompt p) ∪ {id | TypeId id ∈ s.defined_types}`,
  Cases_on`p`>>rw[evaluate_prompt_def]>>fs[tids_of_prompt_def]>> fs[LET_THM,UNCURRY] >>
  metis_tac[evaluate_decs_tids]);

val evaluate_prompt_mods_disjoint = Q.store_thm("evaluate_prompt_mods_disjoint",
  `∀env s p res. evaluate_prompt env s p = res ⇒
     SND(SND(SND res)) = NONE ⇒
     ∀mn ds. p = Prompt (SOME mn) ds ⇒ mn ∉ s.defined_mods`,
  Cases_on`p`>>rw[evaluate_prompt_def]>>fs[]);

val _ = export_theory()
