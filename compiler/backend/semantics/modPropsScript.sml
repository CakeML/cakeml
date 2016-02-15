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
  srw_tac[][pat_bindings_def, pmatch_def] >>
  every_case_tac >>
  full_simp_tac(srw_ss())[] >>
  srw_tac[][] >>
  res_tac >>
  qexists_tac `env'''++env''` >>
  srw_tac[][] >>
  metis_tac [pat_bindings_accum]);

val build_rec_env_help_lem = Q.prove (
  `∀funs env funs'.
  FOLDR (λ(f,x,e) env'. (f, Recclosure env funs' f)::env') env' funs =
  MAP (λ(fn,n,e). (fn, Recclosure env funs' fn)) funs ++ env'`,
  Induct >>
  srw_tac[][] >>
  PairCases_on `h` >>
  srw_tac[][]);

(* Alternate definition for build_rec_env *)
val build_rec_env_merge = Q.store_thm ("build_rec_env_merge",
  `∀funs funs' env env'.
    build_rec_env funs env env' =
    MAP (λ(fn,n,e). (fn, Recclosure env funs fn)) funs ++ env'`,
  srw_tac[][build_rec_env_def, build_rec_env_help_lem]);

val Boolv_11 = store_thm("Boolv_11[simp]",``Boolv b1 = Boolv b2 ⇔ (b1 = b2)``,srw_tac[][Boolv_def]);

val evaluate_length = Q.store_thm("evaluate_length",
  `(∀env (s:'ffi modSem$state) ls s' vs.
      evaluate env s ls = (s',Rval vs) ⇒ LENGTH vs = LENGTH ls) ∧
   (∀env (s:'ffi modSem$state) v pes ev s' vs.
      evaluate_match env s v pes ev = (s', Rval vs) ⇒ LENGTH vs = 1)`,
  ho_match_mp_tac evaluate_ind >>
  srw_tac[][evaluate_def] >> srw_tac[][] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][]);

val evaluate_cons = Q.store_thm("evaluate_cons",
  `evaluate env s (e::es) =
   (case evaluate env s [e] of
    | (s,Rval v) =>
      (case evaluate env s es of
       | (s,Rval vs) => (s,Rval (v++vs))
       | r => r)
    | r => r)`,
  Cases_on`es`>>srw_tac[][evaluate_def] >>
  every_case_tac >> full_simp_tac(srw_ss())[evaluate_def] >>
  imp_res_tac evaluate_length >> full_simp_tac(srw_ss())[SING_HD]);

val evaluate_sing = Q.store_thm("evaluate_sing",
  `(evaluate env s [e] = (s',Rval vs) ⇒ ∃y. vs = [y]) ∧
   (evaluate_match env s v pes ev = (s',Rval vs) ⇒ ∃y. vs = [y])`,
  srw_tac[][] >> imp_res_tac evaluate_length >> full_simp_tac(srw_ss())[] >> metis_tac[SING_HD])

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
  srw_tac[][evaluate_def] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >> rev_full_simp_tac(srw_ss())[] >>
  rev_full_simp_tac(srw_ss()++ARITH_ss)[dec_clock_def]);

val evaluate_dec_add_to_clock = Q.prove(
  `∀env s d s' r.
    r ≠ Rerr (Rabort Rtimeout_error) ∧
    evaluate_dec env s d = (s',r) ⇒
    evaluate_dec env (s with clock := s.clock + extra) d =
      (s' with clock := s'.clock + extra,r)`,
  Cases_on`d`>>simp[evaluate_dec_def] >>
  srw_tac[][]>>full_simp_tac(srw_ss())[state_component_equality]>>
  pop_assum mp_tac >>
  BasicProvers.TOP_CASE_TAC >>
  imp_res_tac evaluate_add_to_clock >>
  BasicProvers.TOP_CASE_TAC >> full_simp_tac(srw_ss())[] >>
  TRY (strip_tac >> var_eq_tac) >> full_simp_tac(srw_ss())[] >> rev_full_simp_tac(srw_ss())[] >>
  first_x_assum(qspec_then`extra`mp_tac)>>simp[] >>
  BasicProvers.TOP_CASE_TAC >> simp[] >>
  BasicProvers.TOP_CASE_TAC >> simp[] >>
  BasicProvers.TOP_CASE_TAC >> simp[] >>
  BasicProvers.TOP_CASE_TAC >> simp[]);

val evaluate_decs_add_to_clock = Q.prove(
  `∀decs env s s' r.
   SND (SND r) ≠ SOME (Rabort Rtimeout_error) ∧
   evaluate_decs env s decs = (s',r) ⇒
   evaluate_decs env (s with clock := s.clock + extra) decs =
   (s' with clock := s'.clock + extra,r)`,
  Induct >> srw_tac[][evaluate_decs_def] >>
  pop_assum mp_tac >>
  BasicProvers.TOP_CASE_TAC >>
  imp_res_tac evaluate_dec_add_to_clock >>
  BasicProvers.TOP_CASE_TAC >> rev_full_simp_tac(srw_ss())[] >>
  TRY(strip_tac >> var_eq_tac) >> full_simp_tac(srw_ss())[] >> rev_full_simp_tac(srw_ss())[] >>
  BasicProvers.TOP_CASE_TAC >> full_simp_tac(srw_ss())[] >>
  BasicProvers.TOP_CASE_TAC >> full_simp_tac(srw_ss())[] >>
  BasicProvers.TOP_CASE_TAC >> full_simp_tac(srw_ss())[] >>
  BasicProvers.TOP_CASE_TAC >> full_simp_tac(srw_ss())[] >>
  strip_tac >> rveq >> full_simp_tac(srw_ss())[] >>
  BasicProvers.TOP_CASE_TAC >> full_simp_tac(srw_ss())[] >>
  BasicProvers.TOP_CASE_TAC >> full_simp_tac(srw_ss())[] >>
  BasicProvers.TOP_CASE_TAC >> full_simp_tac(srw_ss())[] >>
  rator_x_assum`evaluate_decs`mp_tac >>
  qmatch_assum_abbrev_tac`evaluate_decs envv ss decs = (sr,rr)` >>
  first_x_assum(qspecl_then[`envv`,`ss`,`sr`,`rr`]mp_tac) >>
  unabbrev_all_tac >> simp[]);

val evaluate_prompt_add_to_clock = Q.prove(
  `∀env s p s' r.
     SND(SND r) ≠ SOME (Rabort Rtimeout_error) ∧
     evaluate_prompt env s p = (s',r) ⇒
     evaluate_prompt env (s with clock := s.clock + extra) p =
       (s' with clock := s'.clock + extra,r)`,
  Cases_on`p` >>
  srw_tac[][evaluate_prompt_def] >>
  full_simp_tac(srw_ss())[LET_THM] >>
  split_pair_tac >> full_simp_tac(srw_ss())[] >> rveq >>
  simp[] >> full_simp_tac(srw_ss())[] >>
  imp_res_tac evaluate_decs_add_to_clock >> rev_full_simp_tac(srw_ss())[] >>
  rpt(first_x_assum(qspec_then`extra`mp_tac))>>simp[]);

val evaluate_prompts_add_to_clock = Q.prove(
  `∀prog env s s' r.
     SND(SND r) ≠ SOME (Rabort Rtimeout_error) ∧
     evaluate_prompts env s prog = (s',r) ⇒
     evaluate_prompts env (s with clock := s.clock + extra) prog =
     (s' with clock := s'.clock + extra,r)`,
  Induct >> srw_tac[][evaluate_prompts_def] >>
  pop_assum mp_tac >>
  ntac 3 BasicProvers.TOP_CASE_TAC >>
  imp_res_tac evaluate_prompt_add_to_clock >> rev_full_simp_tac(srw_ss())[] >>
  res_tac >>
  BasicProvers.TOP_CASE_TAC >> full_simp_tac(srw_ss())[] >>
  TRY(strip_tac >> var_eq_tac) >> full_simp_tac(srw_ss())[] >> rev_full_simp_tac(srw_ss())[] >>
  BasicProvers.TOP_CASE_TAC >> full_simp_tac(srw_ss())[] >>
  BasicProvers.TOP_CASE_TAC >> full_simp_tac(srw_ss())[] >>
  BasicProvers.TOP_CASE_TAC >> full_simp_tac(srw_ss())[] >>
  strip_tac >> rveq >> full_simp_tac(srw_ss())[] >>
  first_x_assum(drule o ONCE_REWRITE_RULE[CONJ_COMM]) >>
  simp[]);

val evaluate_prog_add_to_clock = Q.store_thm("evaluate_prog_add_to_clock",
  `∀prog env s s' r.
   evaluate_prog env s prog = (s',r) ∧
   r ≠ SOME (Rabort Rtimeout_error) ⇒
   evaluate_prog env (s with clock := s.clock + extra) prog =
     (s' with clock := s'.clock + extra,r)`,
  srw_tac[][evaluate_prog_def] >> full_simp_tac(srw_ss())[LET_THM] >>
  split_pair_tac >> full_simp_tac(srw_ss())[] >> rveq >>
  imp_res_tac evaluate_prompts_add_to_clock >>
  rev_full_simp_tac(srw_ss())[] >>
  rpt(first_x_assum(qspec_then`extra`mp_tac))>>simp[]);

val do_app_io_events_mono = Q.store_thm("do_app_io_events_mono",
  `do_app (f,s) op vs = SOME((f',s'),r) ⇒
   s.io_events ≼ s'.io_events ∧
   (IS_SOME s.final_event ⇒ s' = s)`,
  srw_tac[][] >> full_simp_tac(srw_ss())[do_app_def] >>
  every_case_tac >>
  full_simp_tac(srw_ss())[LET_THM,
     semanticPrimitivesTheory.store_alloc_def,
     semanticPrimitivesTheory.store_lookup_def,
     semanticPrimitivesTheory.store_assign_def] >> srw_tac[][] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
  full_simp_tac(srw_ss())[ffiTheory.call_FFI_def] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][]);

val evaluate_io_events_mono = Q.store_thm("evaluate_io_events_mono",
  `(∀env (s:'ffi modSem$state) es.
      s.ffi.io_events ≼ (FST (evaluate env s es)).ffi.io_events ∧
      (IS_SOME s.ffi.final_event ⇒ (FST (evaluate env s es)).ffi = s.ffi)) ∧
   (∀env (s:'ffi modSem$state) pes v err_v.
      s.ffi.io_events ≼ (FST (evaluate_match env s pes v err_v)).ffi.io_events ∧
      (IS_SOME s.ffi.final_event ⇒ (FST (evaluate_match env s pes v err_v)).ffi = s.ffi))`,
  ho_match_mp_tac evaluate_ind >>
  srw_tac[][evaluate_def] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >> rev_full_simp_tac(srw_ss())[] >>
  full_simp_tac(srw_ss())[dec_clock_def] >>
  imp_res_tac do_app_io_events_mono >>
  metis_tac[IS_PREFIX_TRANS]);

val with_clock_ffi = Q.store_thm("with_clock_ffi",
  `(s with clock := k).ffi = s.ffi`,
  EVAL_TAC)

val evaluate_add_to_clock_io_events_mono = Q.store_thm("evaluate_add_to_clock_io_events_mono",
  `(∀env (s:'ffi modSem$state) es extra.
       (FST (evaluate env s es)).ffi.io_events ≼
       (FST (evaluate env (s with clock := s.clock + extra) es)).ffi.io_events ∧
       (IS_SOME ((FST (evaluate env s es)).ffi.final_event) ⇒
         (FST (evaluate env (s with clock := s.clock + extra) es)).ffi =
         (FST (evaluate env s es)).ffi)) ∧
   (∀env (s:'ffi modSem$state) pes v err_v extra.
       (FST (evaluate_match env s pes v err_v)).ffi.io_events ≼
       (FST (evaluate_match env (s with clock := s.clock + extra) pes v err_v)).ffi.io_events ∧
       (IS_SOME ((FST (evaluate_match env s pes v err_v)).ffi.final_event) ⇒
         (FST (evaluate_match env (s with clock := s.clock + extra) pes v err_v)).ffi =
         (FST (evaluate_match env s pes v err_v)).ffi))`,
  ho_match_mp_tac evaluate_ind >>
  srw_tac[][evaluate_def] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >>
  imp_res_tac evaluate_add_to_clock >> rev_full_simp_tac(srw_ss())[] >> full_simp_tac(srw_ss())[] >> srw_tac[][] >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
  imp_res_tac evaluate_io_events_mono >> full_simp_tac(srw_ss())[] >> rev_full_simp_tac(srw_ss())[dec_clock_def] >>
  fsrw_tac[ARITH_ss][] >>
  rev_full_simp_tac(srw_ss()++ARITH_ss)[] >>
  metis_tac[IS_PREFIX_TRANS,FST,PAIR,evaluate_io_events_mono,with_clock_ffi,do_app_io_events_mono]);

val evaluate_dec_io_events_mono = Q.store_thm("evaluate_dec_io_events_mono",
  `∀x y z.
     y.ffi.io_events ≼ (FST (evaluate_dec x y z)).ffi.io_events ∧
     (IS_SOME y.ffi.final_event ⇒ (FST (evaluate_dec x y z)).ffi = y.ffi)`,
   Cases_on`z`>>srw_tac[][evaluate_dec_def] >>
   every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
   metis_tac[evaluate_io_events_mono,FST]);

val evaluate_dec_add_to_clock_io_events_mono = Q.store_thm("evaluate_dec_add_to_clock_io_events_mono",
  `∀env s prog extra.
   (FST (evaluate_dec env s prog)).ffi.io_events ≼
   (FST (evaluate_dec env (s with clock := s.clock + extra) prog)).ffi.io_events ∧
   (IS_SOME ((FST (evaluate_dec env s prog)).ffi.final_event) ⇒
     (FST (evaluate_dec env (s with clock := s.clock + extra) prog)).ffi =
     (FST (evaluate_dec env s prog)).ffi)`,
  Cases_on`prog`>>srw_tac[][evaluate_dec_def]>> srw_tac[][] >> full_simp_tac(srw_ss())[] >>
  (fn g => subterm split_pair_case_tac (#2 g) g) >> full_simp_tac(srw_ss())[] >>
  (fn g => subterm split_pair_case_tac (#2 g) g) >> full_simp_tac(srw_ss())[] >>
  qmatch_assum_abbrev_tac`evaluate ee (s with clock := _) pp = _` >>
  qispl_then[`ee`,`s`,`pp`,`extra`]mp_tac(CONJUNCT1 evaluate_add_to_clock_io_events_mono) >>
  simp[] >> strip_tac >>
  every_case_tac >> full_simp_tac(srw_ss())[]);

val evaluate_decs_io_events_mono = Q.store_thm("evaluate_decs_io_events_mono",
  `∀prog env s s' x y. evaluate_decs env s prog = (s',x,y) ⇒
   s.ffi.io_events ≼ s'.ffi.io_events ∧
   (IS_SOME s.ffi.final_event ⇒ s'.ffi = s.ffi)`,
  Induct >> srw_tac[][evaluate_decs_def] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
  res_tac >> full_simp_tac(srw_ss())[] >>
  metis_tac[IS_PREFIX_TRANS,FST,evaluate_dec_io_events_mono]);

val evaluate_decs_add_to_clock_io_events_mono = Q.store_thm("evaluate_decs_add_to_clock_io_events_mono",
  `∀env s prog extra.
   (FST (evaluate_decs env s prog)).ffi.io_events ≼
   (FST (evaluate_decs env (s with clock := s.clock + extra) prog)).ffi.io_events ∧
   (IS_SOME ((FST (evaluate_decs env s prog)).ffi.final_event) ⇒
     (FST (evaluate_decs env (s with clock := s.clock + extra) prog)).ffi =
     (FST (evaluate_decs env s prog)).ffi)`,
  Induct_on`prog`>>srw_tac[][evaluate_decs_def] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >>
  qmatch_assum_abbrev_tac`evaluate_dec ee (ss with clock := _ + extra) pp = _` >>
  qispl_then[`ee`,`ss`,`pp`,`extra`]mp_tac evaluate_dec_add_to_clock_io_events_mono >>
  simp[] >> strip_tac >>
  imp_res_tac evaluate_dec_add_to_clock >> full_simp_tac(srw_ss())[] >>
  imp_res_tac evaluate_decs_io_events_mono >> full_simp_tac(srw_ss())[] >>
  rveq >|[rator_x_assum`evaluate_decs`mp_tac,ALL_TAC,ALL_TAC]>>
  qmatch_assum_abbrev_tac`evaluate_decs eee sss prog = _` >>
  last_x_assum(qspecl_then[`eee`,`sss`,`extra`]mp_tac)>>simp[Abbr`sss`]>>
  fsrw_tac[ARITH_ss][] >> srw_tac[][] >> full_simp_tac(srw_ss())[] >>
  metis_tac[IS_PREFIX_TRANS,FST]);

val evaluate_prompt_io_events_mono = Q.store_thm("evaluate_prompt_io_events_mono",
  `∀x y z. evaluate_prompt x y z = (a,b) ⇒
     y.ffi.io_events ≼ a.ffi.io_events ∧
     (IS_SOME y.ffi.final_event ⇒ a.ffi = y.ffi)`,
   Cases_on`z`>>srw_tac[][evaluate_prompt_def] >>
   every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
   full_simp_tac(srw_ss())[LET_THM] >> split_pair_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
   imp_res_tac evaluate_decs_io_events_mono);

val evaluate_prompt_add_to_clock_io_events_mono = Q.store_thm("evaluate_prompt_add_to_clock_io_events_mono",
  `∀env s prog extra.
   (FST (evaluate_prompt env s prog)).ffi.io_events ≼
   (FST (evaluate_prompt env (s with clock := s.clock + extra) prog)).ffi.io_events ∧
   (IS_SOME ((FST (evaluate_prompt env s prog)).ffi.final_event) ⇒
     (FST (evaluate_prompt env (s with clock := s.clock + extra) prog)).ffi =
     (FST (evaluate_prompt env s prog)).ffi)`,
  Cases_on`prog`>>srw_tac[][evaluate_prompt_def]>>
  every_case_tac >> full_simp_tac(srw_ss())[LET_THM] >>
  TRY split_pair_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
  qmatch_assum_abbrev_tac`evaluate_decs ee (ss with clock := _ + extra) pp = _` >>
  qispl_then[`ee`,`ss`,`pp`,`extra`]mp_tac evaluate_decs_add_to_clock_io_events_mono >>
  simp[]);

val evaluate_prompts_io_events_mono = Q.store_thm("evaluate_prompts_io_events_mono",
  `∀prog env s s' x y. evaluate_prompts env s prog = (s',x,y) ⇒
   s.ffi.io_events ≼ s'.ffi.io_events ∧
   (IS_SOME s.ffi.final_event ⇒ s'.ffi = s.ffi)`,
  Induct >> srw_tac[][evaluate_prompts_def] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
  imp_res_tac evaluate_prompt_io_events_mono >>
  res_tac >> full_simp_tac(srw_ss())[] >>
  metis_tac[IS_PREFIX_TRANS]);

val evaluate_prompts_add_to_clock_io_events_mono = Q.store_thm("evaluate_prompts_add_to_clock_io_events_mono",
  `∀env s prog extra.
   (FST (evaluate_prompts env s prog)).ffi.io_events ≼
   (FST (evaluate_prompts env (s with clock := s.clock + extra) prog)).ffi.io_events ∧
   (IS_SOME ((FST (evaluate_prompts env s prog)).ffi.final_event) ⇒
     (FST (evaluate_prompts env (s with clock := s.clock + extra) prog)).ffi =
     (FST (evaluate_prompts env s prog)).ffi)`,
  Induct_on`prog` >> srw_tac[][evaluate_prompts_def] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >>
  qmatch_assum_abbrev_tac`evaluate_prompt ee (ss with clock := _ + extra) pp = _` >>
  qispl_then[`ee`,`ss`,`pp`,`extra`]mp_tac evaluate_prompt_add_to_clock_io_events_mono >>
  simp[] >> srw_tac[][] >>
  imp_res_tac evaluate_prompt_add_to_clock >> full_simp_tac(srw_ss())[] >>
  imp_res_tac evaluate_prompts_io_events_mono >> full_simp_tac(srw_ss())[] >>
  rveq >|[rator_x_assum`evaluate_prompts`mp_tac,ALL_TAC,ALL_TAC]>>
  qmatch_assum_abbrev_tac`evaluate_prompts eee sss prog = _` >>
  last_x_assum(qspecl_then[`eee`,`sss`,`extra`]mp_tac)>>simp[Abbr`sss`]>>
  fsrw_tac[ARITH_ss][] >> srw_tac[][] >> full_simp_tac(srw_ss())[] >>
  metis_tac[IS_PREFIX_TRANS,FST]);

val evaluate_prog_add_to_clock_io_events_mono = Q.store_thm("evaluate_prog_add_to_clock_io_events_mono",
  `∀env s prog extra.
   (FST (evaluate_prog env s prog)).ffi.io_events ≼
   (FST (evaluate_prog env (s with clock := s.clock + extra) prog)).ffi.io_events ∧
   (IS_SOME ((FST (evaluate_prog env s prog)).ffi.final_event) ⇒
     (FST (evaluate_prog env (s with clock := s.clock + extra) prog)).ffi =
     (FST (evaluate_prog env s prog)).ffi)`,
  srw_tac[][evaluate_prog_def] >> full_simp_tac(srw_ss())[LET_THM] >>
  metis_tac[evaluate_prompts_add_to_clock_io_events_mono,FST]);

val evaluate_vars = Q.store_thm("evaluate_vars",
  `!env s kvs env' ks vs.
    ALL_DISTINCT (MAP FST kvs) ∧
    DISJOINT (set (MAP FST kvs)) (set (MAP FST env')) ∧
    env.v = env' ++ kvs ∧ ks = MAP FST kvs ∧ vs = MAP SND kvs
    ⇒
    evaluate env s (MAP Var_local ks) = (s,Rval vs)`,
  induct_on `kvs` >> srw_tac[][evaluate_def] >>
  srw_tac[][Once evaluate_cons,evaluate_def] >>
  PairCases_on`h`>>srw_tac[][]>> full_simp_tac(srw_ss())[] >>
  srw_tac[][ALOOKUP_APPEND] >>
  reverse BasicProvers.CASE_TAC >>
  imp_res_tac ALOOKUP_MEM >- metis_tac[MEM_MAP,FST] >>
  first_x_assum(qspecl_then[`env`,`s`]mp_tac) >>
  full_simp_tac(srw_ss())[DISJOINT_SYM]);

val with_same_v = Q.store_thm("with_same_v[simp]",
  `env with v := env.v = env`,
  srw_tac[][environment_component_equality])

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
  srw_tac[][pat_bindings_def, pmatch_def]
  >- (
    ONCE_REWRITE_TAC[GSYM MAP] >>
    match_mp_tac evaluate_vars >> srw_tac[][] >>
    qexists_tac`(x,v)::env.v` >> srw_tac[][] )
  >- (
    match_mp_tac evaluate_vars >> srw_tac[][] >>
    first_assum(match_exists_tac o concl) >> simp[] )
  >- (
    first_x_assum (match_mp_tac o MP_CANON) >>
    every_case_tac >> full_simp_tac(srw_ss())[] )
  >- (
    first_x_assum (match_mp_tac o MP_CANON) >>
    every_case_tac >> full_simp_tac(srw_ss())[] )
  >- (
    first_x_assum (match_mp_tac o MP_CANON) >>
    every_case_tac >> full_simp_tac(srw_ss())[] )
  >- (
    match_mp_tac evaluate_vars >> srw_tac[][] >>
    first_assum(match_exists_tac o concl) >> simp[] )
  >- (
    every_case_tac >> full_simp_tac(srw_ss())[] >>
    `ALL_DISTINCT (pat_bindings p (MAP FST env.v))`
            by full_simp_tac(srw_ss())[Once pat_bindings_accum, ALL_DISTINCT_APPEND] >>
    `pat_bindings p (MAP FST env.v) = MAP FST a`
                 by (imp_res_tac pmatch_extend >>
                     srw_tac[][] >>
                     metis_tac [pat_bindings_accum]) >>
    fsrw_tac[QUANT_INST_ss[record_default_qp]][] >> rev_full_simp_tac(srw_ss())[] >>
    `env with v := env' = <| c := env.c; v := env' |>` by (
      srw_tac[][environment_component_equality]) >> metis_tac[]));

val evaluate_append = Q.store_thm("evaluate_append",
  `∀env s s1 s2 e1 e2 v1 v2.
   evaluate env s e1 = (s1, Rval v1) ∧
   evaluate env s1 e2 = (s2, Rval v2) ⇒
   evaluate env s (e1++e2) = (s2, Rval (v1++v2))`,
  Induct_on`e1`>>srw_tac[][evaluate_def] >>
  full_simp_tac(srw_ss())[Once evaluate_cons] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
  res_tac >> full_simp_tac(srw_ss())[]);

val evaluate_vars_reverse = Q.store_thm("evaluate_vars_reverse",
  `!env s es s' vs.
    evaluate env s (MAP Var_local es) = (s, Rval vs)
    ⇒
    evaluate env s (MAP Var_local (REVERSE es)) = (s, Rval (REVERSE vs))`,
  induct_on `es` >> srw_tac[][evaluate_def] >> srw_tac[][] >>
  pop_assum mp_tac >>
  srw_tac[][Once evaluate_cons] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
  full_simp_tac(srw_ss())[evaluate_def] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
  match_mp_tac evaluate_append >>
  srw_tac[][evaluate_def]);

val no_dup_types_cons_imp = Q.store_thm("no_dup_types_cons_imp",
  `no_dup_types (d::ds) ⇒ no_dup_types ds`,
  srw_tac[][decs_to_types_def,no_dup_types_def,ALL_DISTINCT_APPEND]);

val no_dup_mods_eqn = Q.store_thm ("no_dup_mods_eqn",
  `!p ps.
    (no_dup_mods [] mods ⇔ T) ∧
    (no_dup_mods (p::ps) mods ⇔
       (case p of
         | Prompt (SOME mn) ds =>
             ~MEM mn (prog_to_mods ps) ∧ mn ∉ mods
         | Prompt NONE _ => T) ∧
      no_dup_mods ps mods)`,
  srw_tac[][modSemTheory.no_dup_mods_def, modSemTheory.prog_to_mods_def] >>
  every_case_tac >>
  srw_tac[][] >>
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
  srw_tac[][no_dup_top_types_def, prog_to_top_types_def] >>
  every_case_tac >>
  srw_tac[][ALL_DISTINCT_APPEND, DISJOINT_DEF, EXTENSION] >>
  full_simp_tac(srw_ss())[MEM_MAP] >>
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
  srw_tac[][evaluate_def] >> srw_tac[][] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][]);

val evaluate_dec_state_const = Q.store_thm("evaluate_dec_state_const",
  `∀env st d res. evaluate_dec env st d = res ⇒
   (FST res).defined_mods = st.defined_mods`,
  Cases_on`d`>>srw_tac[][evaluate_dec_def] >> srw_tac[][] >>
  BasicProvers.CASE_TAC >> full_simp_tac(srw_ss())[] >>
  imp_res_tac evaluate_state_const >>
  every_case_tac >> full_simp_tac(srw_ss())[]);

val evaluate_decs_state_const = Q.store_thm("evaluate_decs_state_const",
  `∀env st ds res. evaluate_decs env st ds = res ⇒
    (FST res).defined_mods = st.defined_mods`,
  Induct_on`ds`>>srw_tac[][evaluate_decs_def] >> srw_tac[][] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >>
  imp_res_tac evaluate_dec_state_const >> full_simp_tac(srw_ss())[] >>
  `∀x f.(x with globals updated_by f).defined_mods = x.defined_mods` by simp[] >>
  metis_tac[FST]);

val evaluate_dec_tids_acc = store_thm("evaluate_dec_tids_acc",
  ``∀env st d res. evaluate_dec env st d = res ⇒
      st.defined_types ⊆ (FST res).defined_types``,
  Cases_on`d`>>srw_tac[][evaluate_dec_def] >> srw_tac[][] >>
  BasicProvers.CASE_TAC >>
  imp_res_tac evaluate_state_const >>
  every_case_tac >> srw_tac[][]);

val evaluate_decs_tids_acc = store_thm("evaluate_decs_tids_acc",
  ``∀env st ds res. evaluate_decs env st ds = res ⇒
      st.defined_types ⊆ (FST res).defined_types``,
  Induct_on`ds`>>srw_tac[][evaluate_decs_def]>>srw_tac[][]>>
  every_case_tac >> full_simp_tac(srw_ss())[]>>
  imp_res_tac evaluate_dec_tids_acc >> full_simp_tac(srw_ss())[] >>
  `∀x f.(x with globals updated_by f).defined_types = x.defined_types` by simp[] >>
  metis_tac[FST,SUBSET_TRANS]);

val evaluate_decs_tids = Q.store_thm("evaluate_decs_tids",
  `∀env st ds res. evaluate_decs env st ds = res ⇒
     SND(SND(SND res)) = NONE ⇒
     {id | TypeId id ∈ (FST res).defined_types} = (tids_of_decs ds) ∪ {id | TypeId id ∈ st.defined_types}`,
  Induct_on`ds`>>srw_tac[][evaluate_decs_def]>>full_simp_tac(srw_ss())[tids_of_decs_thm]>>
  every_case_tac>>full_simp_tac(srw_ss())[evaluate_dec_def,LET_THM]>>srw_tac[][]>>
  every_case_tac>>full_simp_tac(srw_ss())[]>>srw_tac[][]>>
  full_simp_tac(srw_ss())[EXTENSION,semanticPrimitivesTheory.type_defs_to_new_tdecs_def,MEM_MAP,PULL_EXISTS,UNCURRY] >>
  qmatch_assum_abbrev_tac`evaluate_decs env' st' _ = _` >>
  last_x_assum(qspecl_then[`env'`,`st'`]mp_tac)>>srw_tac[][]>>
  unabbrev_all_tac >> full_simp_tac(srw_ss())[]>>
  full_simp_tac(srw_ss())[EXTENSION,semanticPrimitivesTheory.type_defs_to_new_tdecs_def,MEM_MAP,PULL_EXISTS,UNCURRY] >>
  metis_tac[evaluate_state_const]);

val evaluate_decs_tids_disjoint = Q.store_thm("evaluate_decs_tids_disjoint",
  `∀env st ds res. evaluate_decs env st ds = res ⇒
     SND(SND(SND res)) = NONE ⇒
     DISJOINT (IMAGE TypeId (tids_of_decs ds)) st.defined_types`,
  Induct_on`ds`>>srw_tac[][evaluate_decs_def]>>full_simp_tac(srw_ss())[tids_of_decs_thm]>>
  every_case_tac >> full_simp_tac(srw_ss())[evaluate_dec_def,LET_THM] >> srw_tac[][] >>
  every_case_tac>>full_simp_tac(srw_ss())[]>>srw_tac[][]>>
  qmatch_assum_abbrev_tac`evaluate_decs env' st' _ = _` >>
  last_x_assum(qspecl_then[`env'`,`st'`]mp_tac)>>srw_tac[][]>>
  unabbrev_all_tac >> full_simp_tac(srw_ss())[]>>
  full_simp_tac(srw_ss())[semanticPrimitivesTheory.type_defs_to_new_tdecs_def,IN_DISJOINT,MEM_MAP,UNCURRY] >>
  metis_tac[evaluate_state_const]);

val tids_of_prompt_def = Define`
  tids_of_prompt (Prompt _ ds) = tids_of_decs ds`;

val evaluate_prompt_tids_disjoint = prove(
  ``∀env s p res. evaluate_prompt env s p = res ⇒
      SND(SND(SND res)) = NONE ⇒
      DISJOINT (IMAGE TypeId (tids_of_prompt p)) s.defined_types``,
  Cases_on`p`>>srw_tac[][evaluate_prompt_def]>>full_simp_tac(srw_ss())[tids_of_prompt_def]>>
  full_simp_tac(srw_ss())[LET_THM,UNCURRY] >> metis_tac[evaluate_decs_tids_disjoint]);

val evaluate_prompt_tids_acc = prove(
  ``∀env s p res. evaluate_prompt env s p = res ⇒
      s.defined_types ⊆ (FST res).defined_types``,
  Cases_on`p`>>srw_tac[][evaluate_prompt_def]>>full_simp_tac(srw_ss())[]>>
  metis_tac[evaluate_decs_tids_acc,FST]);

val evaluate_prompt_tids = Q.store_thm("evaluate_prompt_tids",
  `∀env s p res. evaluate_prompt env s p = res ⇒
     SND(SND(SND res)) = NONE ⇒
     {id | TypeId id ∈ (FST res).defined_types} = (tids_of_prompt p) ∪ {id | TypeId id ∈ s.defined_types}`,
  Cases_on`p`>>srw_tac[][evaluate_prompt_def]>>full_simp_tac(srw_ss())[tids_of_prompt_def]>> full_simp_tac(srw_ss())[LET_THM,UNCURRY] >>
  metis_tac[evaluate_decs_tids]);

val evaluate_prompt_mods_disjoint = Q.store_thm("evaluate_prompt_mods_disjoint",
  `∀env s p res. evaluate_prompt env s p = res ⇒
     SND(SND(SND res)) = NONE ⇒
     ∀mn ds. p = Prompt (SOME mn) ds ⇒ mn ∉ s.defined_mods`,
  Cases_on`p`>>srw_tac[][evaluate_prompt_def]>>full_simp_tac(srw_ss())[]);

val s = ``s:'ffi modSem$state``;

val evaluate_globals = Q.store_thm("evaluate_globals",
  `(∀env ^s es s' r. evaluate env s es = (s',r) ⇒ s'.globals = s.globals) ∧
   (∀env ^s pes v err_v s' r. evaluate_match env s pes v err_v = (s',r) ⇒
      s'.globals = s.globals)`,
  ho_match_mp_tac evaluate_ind >>
  srw_tac[][evaluate_def] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >> full_simp_tac(srw_ss())[] >> rev_full_simp_tac(srw_ss())[] >> full_simp_tac(srw_ss())[dec_clock_def]);

val _ = export_theory()
