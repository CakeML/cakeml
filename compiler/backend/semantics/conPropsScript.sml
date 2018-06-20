open preamble conSemTheory
open evaluatePropsTheory semanticsPropsTheory

val _ = new_theory"conProps"

val with_same_v = Q.store_thm("with_same_v[simp]",
  `((env:conSem$environment) with v := env.v) = env`,
  srw_tac[][conSemTheory.environment_component_equality])

val op_thms = { nchotomy = conLangTheory.op_nchotomy, case_def = conLangTheory.op_case_def}
val astop_thms = {nchotomy = astTheory.op_nchotomy, case_def = astTheory.op_case_def}
val modop_thms = {nchotomy = modLangTheory.op_nchotomy, case_def = modLangTheory.op_case_def}
val list_thms = { nchotomy = list_nchotomy, case_def = list_case_def}
val option_thms = { nchotomy = option_nchotomy, case_def = option_case_def}
val v_thms = { nchotomy = v_nchotomy, case_def = v_case_def}
val sv_thms = { nchotomy = semanticPrimitivesTheory.store_v_nchotomy, case_def = semanticPrimitivesTheory.store_v_case_def }
val lit_thms = { nchotomy = astTheory.lit_nchotomy, case_def = astTheory.lit_case_def}
val ffi_result_thms = { nchotomy = ffiTheory.ffi_result_nchotomy, case_def = ffiTheory.ffi_result_case_def };
val eqs = LIST_CONJ (map prove_case_eq_thm
  [op_thms, modop_thms, astop_thms, list_thms, option_thms, v_thms, sv_thms, lit_thms, ffi_result_thms])

val do_app_cases = save_thm("do_app_cases",
  ``conSem$do_app (s,t) op vs = SOME x`` |>
  SIMP_CONV(srw_ss()++COND_elim_ss++LET_ss)[PULL_EXISTS, do_app_def, eqs, pair_case_eq]);

val eq_result_CASE_tm = prim_mk_const{Name="eq_result_CASE",Thy="semanticPrimitives"};
val check =
  do_app_cases |> concl |> find_terms TypeBase.is_case
  |> List.map (#1 o strip_comb)
  |> List.all (fn tm => List.exists (same_const tm) [optionSyntax.option_case_tm, eq_result_CASE_tm])
val () = if check then () else raise(ERR"conProps""do_app_cases failed")

val do_app_io_events_mono = Q.store_thm("do_app_io_events_mono",
  `do_app (f,s) op vs = SOME((f',s'),r) ⇒
   s.io_events ≼ s'.io_events`,
  simp[do_app_cases] >> strip_tac \\ fs[] \\
  every_case_tac >>
  full_simp_tac(srw_ss())[LET_THM,
     semanticPrimitivesTheory.store_alloc_def,
     semanticPrimitivesTheory.store_lookup_def,
     semanticPrimitivesTheory.store_assign_def] >> srw_tac[][] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
  full_simp_tac(srw_ss())[ffiTheory.call_FFI_def] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][]);

val s = ``s:'ffi conSem$state``;

val evaluate_io_events_mono = Q.store_thm("evaluate_io_events_mono",
  `(∀env ^s es s' r. evaluate env s es = (s',r) ⇒
      s.ffi.io_events ≼ s'.ffi.io_events) ∧
   (∀env ^s pes v err_v s' r. evaluate_match env s pes v err_v = (s',r) ⇒
      s.ffi.io_events ≼ s'.ffi.io_events)`,
  ho_match_mp_tac evaluate_ind >>
  srw_tac[][evaluate_def] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >> full_simp_tac(srw_ss())[] >> rev_full_simp_tac(srw_ss())[] >> full_simp_tac(srw_ss())[dec_clock_def] >>
  imp_res_tac do_app_io_events_mono >>
  metis_tac[IS_PREFIX_TRANS]);

val build_rec_env_help_lem = Q.prove (
  `∀funs env funs'.
    FOLDR (λ(f,x,e) env'. ((f, Recclosure env funs' f) :: env')) env' funs =
    MAP (λ(fn,n,e). (fn, Recclosure env funs' fn)) funs ++ env'`,
  Induct >>
  srw_tac[][] >>
  PairCases_on `h` >>
  srw_tac[][]);

val build_rec_env_merge = Q.store_thm ("build_rec_env_merge",
  `∀funs funs' env env'.
    build_rec_env funs env env' =
    MAP (λ(fn,n,e). (fn, Recclosure env funs fn)) funs ++ env'`,
  srw_tac[][build_rec_env_def, build_rec_env_help_lem]);

val pat_bindings_accum = Q.store_thm ("pat_bindings_accum",
  `(!p acc. pat_bindings p acc = pat_bindings p [] ++ acc) ∧
   (!ps acc. pats_bindings ps acc = pats_bindings ps [] ++ acc)`,
  Induct >>
  srw_tac[][]
  >- srw_tac[][pat_bindings_def]
  >- srw_tac[][pat_bindings_def]
  >- srw_tac[][pat_bindings_def]
  >- metis_tac [APPEND_ASSOC, pat_bindings_def]
  >- metis_tac [APPEND_ASSOC, pat_bindings_def]
  >- srw_tac[][pat_bindings_def]
  >- metis_tac [APPEND_ASSOC, pat_bindings_def]);

val Boolv_11 = Q.store_thm("Boolv_11[simp]",
  `Boolv b1 = Boolv b2 ⇔ (b1 = b2)`, EVAL_TAC >> srw_tac[][])

val evaluate_length = Q.store_thm("evaluate_length",
  `(∀env (s:'ffi conSem$state) ls s' vs.
      evaluate env s ls = (s',Rval vs) ⇒ LENGTH vs = LENGTH ls) ∧
   (∀env (s:'ffi conSem$state) v pes ev s' vs.
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
  `(∀env ^s es s' r.
       evaluate env s es = (s',r) ∧
       r ≠ Rerr (Rabort Rtimeout_error) ⇒
       evaluate env (s with clock := s.clock + extra) es =
         (s' with clock := s'.clock + extra,r)) ∧
   (∀env ^s pes v err_v s' r.
       evaluate_match env s pes v err_v = (s',r) ∧
       r ≠ Rerr (Rabort Rtimeout_error) ⇒
       evaluate_match env (s with clock := s.clock + extra) pes v err_v =
         (s' with clock := s'.clock + extra,r))`,
  ho_match_mp_tac evaluate_ind >>
  srw_tac[][evaluate_def] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >> rev_full_simp_tac(srw_ss())[] >>
  rev_full_simp_tac(srw_ss()++ARITH_ss)[dec_clock_def]);

val evaluate_dec_add_to_clock = Q.store_thm("evaluate_dec_add_to_clock",
  `evaluate_dec env s d = (s',r) ∧
   r ≠ Rerr (Rabort Rtimeout_error) ⇒
   evaluate_dec env (s with clock := s.clock + extra) d =
     (s' with clock := s'.clock + extra,r)`,
  Cases_on`d`>>srw_tac[][evaluate_dec_def]>>
  first_assum(split_pair_case0_tac o lhs o concl) >> full_simp_tac(srw_ss())[] >>
  imp_res_tac evaluate_add_to_clock >>
  first_x_assum(fn th => mp_tac th >> impl_tac >- (strip_tac >> full_simp_tac(srw_ss())[])) >>
  disch_then(qspec_then`extra`strip_assume_tac) >> simp[] >>
  BasicProvers.CASE_TAC >> full_simp_tac(srw_ss())[] >>
  every_case_tac >> full_simp_tac(srw_ss())[]);

val evaluate_decs_add_to_clock = Q.store_thm("evaluate_decs_add_to_clock",
  `∀decs env s s' x r.
   evaluate_decs env s decs = (s',x,r) ∧
   r ≠ SOME (Rabort Rtimeout_error) ⇒
   evaluate_decs env (s with clock := s.clock + extra) decs =
     (s' with clock := s'.clock + extra, x,r)`,
  Induct >> srw_tac[][evaluate_decs_def] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
  imp_res_tac evaluate_dec_add_to_clock >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
  res_tac >> full_simp_tac(srw_ss())[]);

val evaluate_prompt_add_to_clock = Q.store_thm("evaluate_prompt_add_to_clock",
  `evaluate_prompt env s p = (s',g,r) ∧
   r ≠ SOME (Rabort Rtimeout_error) ⇒
   evaluate_prompt env (s with clock := s.clock + extra) p =
     (s' with clock := s'.clock + extra,g,r)`,
  Cases_on`p` >> srw_tac[][evaluate_prompt_def] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
  imp_res_tac evaluate_decs_add_to_clock >> full_simp_tac(srw_ss())[]);

val evaluate_prog_add_to_clock = Q.store_thm("evaluate_prog_add_to_clock",
  `∀prog env s s' g r.
   evaluate_prog env s prog = (s',g,r) ∧
   r ≠ SOME (Rabort Rtimeout_error) ⇒
   evaluate_prog env (s with clock := s.clock + extra) prog =
     (s' with clock := s'.clock + extra,g,r)`,
  Induct >> srw_tac[][evaluate_prog_def] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
  imp_res_tac evaluate_prompt_add_to_clock >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
  res_tac >> full_simp_tac(srw_ss())[]);

val with_clock_ffi = Q.store_thm("with_clock_ffi",
  `(s with clock := k).ffi = s.ffi`,
  EVAL_TAC);

val evaluate_add_to_clock_io_events_mono = Q.store_thm("evaluate_add_to_clock_io_events_mono",
  `(∀env ^s prog extra.
    (FST (evaluate env s prog)).ffi.io_events ≼
    (FST (evaluate env (s with clock := s.clock + extra) prog)).ffi.io_events) ∧
   (∀env ^s pes v err_v extra.
    (FST (evaluate_match env s pes v err_v)).ffi.io_events ≼
    (FST (evaluate_match env (s with clock := s.clock + extra) pes v err_v)).ffi.io_events)`,
  ho_match_mp_tac evaluate_ind >>
  srw_tac[][evaluate_def] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >>
  imp_res_tac evaluate_add_to_clock >> rev_full_simp_tac(srw_ss())[] >> full_simp_tac(srw_ss())[] >> srw_tac[][] >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
  imp_res_tac evaluate_io_events_mono >> full_simp_tac(srw_ss())[] >> rev_full_simp_tac(srw_ss())[dec_clock_def] >>
  fsrw_tac[ARITH_ss][] >>
  rev_full_simp_tac(srw_ss()++ARITH_ss)[] >>
  metis_tac[IS_PREFIX_TRANS,FST,PAIR,evaluate_io_events_mono,with_clock_ffi,do_app_io_events_mono]);

val evaluate_dec_io_events_mono = Q.store_thm("evaluate_dec_io_events_mono",
  `∀x y z. evaluate_dec x y z = (a,b) ⇒
     y.ffi.io_events ≼ a.ffi.io_events`,
   Cases_on`z`>>srw_tac[][evaluate_dec_def] >>
   every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
   imp_res_tac evaluate_io_events_mono);

val evaluate_dec_add_to_clock_io_events_mono = Q.store_thm("evaluate_dec_add_to_clock_io_events_mono",
  `∀env s prog extra.
   (FST (evaluate_dec env s prog)).ffi.io_events ≼
   (FST (evaluate_dec env (s with clock := s.clock + extra) prog)).ffi.io_events`,
  Cases_on`prog`>>srw_tac[][evaluate_dec_def]>>
  split_pair_case_tac >> full_simp_tac(srw_ss())[] >>
  split_pair_case_tac >> full_simp_tac(srw_ss())[] >>
  qmatch_assum_abbrev_tac`evaluate ee (s with clock := _) pp = _` >>
  qispl_then[`ee`,`s`,`pp`,`extra`]mp_tac(CONJUNCT1 evaluate_add_to_clock_io_events_mono) >>
  simp[] >> strip_tac >>
  every_case_tac >> full_simp_tac(srw_ss())[]);

val evaluate_decs_io_events_mono = Q.store_thm("evaluate_decs_io_events_mono",
  `∀prog env s s' x y. evaluate_decs env s prog = (s',x,y) ⇒
   s.ffi.io_events ≼ s'.ffi.io_events`,
  Induct >> srw_tac[][evaluate_decs_def] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
  imp_res_tac evaluate_dec_io_events_mono >>
  res_tac >> full_simp_tac(srw_ss())[] >>
  metis_tac[IS_PREFIX_TRANS]);

val evaluate_decs_add_to_clock_io_events_mono = Q.store_thm("evaluate_decs_add_to_clock_io_events_mono",
  `∀env s prog extra.
   (FST (evaluate_decs env s prog)).ffi.io_events ≼
   (FST (evaluate_decs env (s with clock := s.clock + extra) prog)).ffi.io_events`,
  Induct_on`prog`>>srw_tac[][evaluate_decs_def] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >>
  qmatch_assum_abbrev_tac`evaluate_dec ee (ss with clock := _ + extra) pp = _` >>
  qispl_then[`ee`,`ss`,`pp`,`extra`]mp_tac evaluate_dec_add_to_clock_io_events_mono >>
  simp[] >> strip_tac >>
  imp_res_tac evaluate_dec_add_to_clock >> full_simp_tac(srw_ss())[] >>
  imp_res_tac evaluate_decs_io_events_mono >> full_simp_tac(srw_ss())[] >>
  rveq >|[qhdtm_x_assum`evaluate_decs`mp_tac,ALL_TAC]>>
  qmatch_assum_abbrev_tac`evaluate_decs ee sss prog = _` >>
  last_x_assum(qspecl_then[`ee`,`sss`,`extra`]mp_tac)>>simp[Abbr`sss`]>>
  fsrw_tac[ARITH_ss][] >> srw_tac[][] >> full_simp_tac(srw_ss())[] >>
  metis_tac[IS_PREFIX_TRANS,FST]);

val evaluate_prompt_io_events_mono = Q.store_thm("evaluate_prompt_io_events_mono",
  `∀x y z. evaluate_prompt x y z = (a,b) ⇒
     y.ffi.io_events ≼ a.ffi.io_events`,
   Cases_on`z`>>srw_tac[][evaluate_prompt_def] >>
   every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
   imp_res_tac evaluate_decs_io_events_mono);

val evaluate_prompt_add_to_clock_io_events_mono = Q.store_thm("evaluate_prompt_add_to_clock_io_events_mono",
  `∀env s prog extra.
   (FST (evaluate_prompt env s prog)).ffi.io_events ≼
   (FST (evaluate_prompt env (s with clock := s.clock + extra) prog)).ffi.io_events`,
  Cases_on`prog`>>srw_tac[][evaluate_prompt_def]>>
  every_case_tac >> full_simp_tac(srw_ss())[] >>
  qmatch_assum_abbrev_tac`evaluate_decs ee (ss with clock := _ + extra) pp = _` >>
  qispl_then[`ee`,`ss`,`pp`,`extra`]mp_tac evaluate_decs_add_to_clock_io_events_mono >>
  simp[]);

val evaluate_prog_io_events_mono = Q.store_thm("evaluate_prog_io_events_mono",
  `∀prog env s s' x y. evaluate_prog env s prog = (s',x,y) ⇒
   s.ffi.io_events ≼ s'.ffi.io_events`,
  Induct >> srw_tac[][evaluate_prog_def] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
  imp_res_tac evaluate_prompt_io_events_mono >>
  res_tac >> full_simp_tac(srw_ss())[] >>
  metis_tac[IS_PREFIX_TRANS]);

val evaluate_prog_add_to_clock_io_events_mono = Q.store_thm("evaluate_prog_add_to_clock_io_events_mono",
  `∀env s prog extra.
   (FST (evaluate_prog env s prog)).ffi.io_events ≼
   (FST (evaluate_prog env (s with clock := s.clock + extra) prog)).ffi.io_events`,
  Induct_on`prog` >> srw_tac[][evaluate_prog_def] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >>
  qmatch_assum_abbrev_tac`evaluate_prompt ee (ss with clock := _ + extra) pp = _` >>
  qispl_then[`ee`,`ss`,`pp`,`extra`]mp_tac evaluate_prompt_add_to_clock_io_events_mono >>
  simp[] >> srw_tac[][] >>
  imp_res_tac evaluate_prompt_add_to_clock >> full_simp_tac(srw_ss())[] >>
  imp_res_tac evaluate_prog_io_events_mono >> full_simp_tac(srw_ss())[] >>
  rveq >|[qhdtm_x_assum`evaluate_prog`mp_tac,ALL_TAC]>>
  qmatch_assum_abbrev_tac`evaluate_prog ee sss prog = _` >>
  last_x_assum(qspecl_then[`ee`,`sss`,`extra`]mp_tac)>>simp[Abbr`sss`]>>
  fsrw_tac[ARITH_ss][] >> srw_tac[][] >> full_simp_tac(srw_ss())[] >>
  metis_tac[IS_PREFIX_TRANS,FST]);

val pmatch_list_Pvar = Q.store_thm("pmatch_list_Pvar",
  `∀xs exh vs s env.
     LENGTH xs = LENGTH vs ⇒
     pmatch_list exh s (MAP Pvar xs) vs env = Match (REVERSE(ZIP(xs,vs))++env)`,
  Induct >> simp[LENGTH_NIL_SYM,pmatch_def] >>
  Cases_on`vs`>>simp[pmatch_def]);

val pats_bindings_MAP_Pvar = Q.store_thm("pats_bindings_MAP_Pvar",
  `∀ws ls. pats_bindings (MAP Pvar ws) ls = (REVERSE ws) ++ ls`,
  Induct >> simp[pat_bindings_def]);

val pmatch_any_match = Q.store_thm("pmatch_any_match",
  `(∀(exh:exh_ctors_env) s p v env env'. pmatch exh s p v env = Match env' ⇒
       ∀env. ∃env'. pmatch exh s p v env = Match env') ∧
    (∀(exh:exh_ctors_env) s ps vs env env'. pmatch_list exh s ps vs env = Match env' ⇒
       ∀env. ∃env'. pmatch_list exh s ps vs env = Match env')`,
  ho_match_mp_tac pmatch_ind >>
  srw_tac[][pmatch_def] >>
  pop_assum mp_tac >>
  BasicProvers.CASE_TAC >>
  full_simp_tac(srw_ss())[] >> strip_tac >> full_simp_tac(srw_ss())[LET_THM] >>
  BasicProvers.CASE_TAC >> full_simp_tac(srw_ss())[] >>
  every_case_tac >> fs [] >>
  metis_tac[semanticPrimitivesTheory.match_result_distinct])

val pmatch_any_no_match = Q.store_thm("pmatch_any_no_match",
  `(∀(exh:exh_ctors_env) s p v env. pmatch exh s p v env = No_match ⇒
       ∀env. pmatch exh s p v env = No_match) ∧
    (∀(exh:exh_ctors_env) s ps vs env. pmatch_list exh s ps vs env = No_match ⇒
       ∀env. pmatch_list exh s ps vs env = No_match)`,
  ho_match_mp_tac pmatch_ind >>
  srw_tac[][pmatch_def] >>
  pop_assum mp_tac >>
  BasicProvers.CASE_TAC >>
  full_simp_tac(srw_ss())[] >> strip_tac >> full_simp_tac(srw_ss())[LET_THM] >>
  BasicProvers.CASE_TAC >> full_simp_tac(srw_ss())[] >>
  imp_res_tac pmatch_any_match >>
  every_case_tac >> fs [] >>
  metis_tac[semanticPrimitivesTheory.match_result_distinct]);

val eval_decs_num_defs = Q.store_thm("eval_decs_num_defs",
  `!env s ds s' env'.
    evaluate_decs env s ds = (s',env',NONE) ⇒ num_defs ds = LENGTH env'`,
  induct_on `ds` >>
  srw_tac[][conLangTheory.num_defs_def,evaluate_decs_def] >> srw_tac[][LENGTH_NIL] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
  cases_on `h` >>
  srw_tac[][conLangTheory.num_defs_def] >>
  res_tac >>
  srw_tac[][] >> full_simp_tac(srw_ss())[evaluate_dec_def] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][]);

val eval_decs_num_defs_err = Q.store_thm("eval_decs_num_defs_err",
  `!env s ds s' env'. evaluate_decs env s ds = (s',env',SOME err) ⇒ LENGTH env' <= num_defs ds`,
  induct_on `ds` >>
  srw_tac[][conLangTheory.num_defs_def,evaluate_decs_def] >> srw_tac[][LENGTH_NIL] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
  cases_on `h` >>
  srw_tac[][conLangTheory.num_defs_def] >>
  res_tac >>
  srw_tac[][] >> full_simp_tac(srw_ss())[evaluate_dec_def] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][]);

val evaluate_globals = Q.store_thm("evaluate_globals",
  `(∀env ^s es s' r. evaluate env s es = (s',r) ⇒ s'.globals = s.globals) ∧
   (∀env ^s pes v err_v s' r. evaluate_match env s pes v err_v = (s',r) ⇒
      s'.globals = s.globals)`,
  ho_match_mp_tac evaluate_ind >>
  srw_tac[][evaluate_def] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >> full_simp_tac(srw_ss())[] >> rev_full_simp_tac(srw_ss())[] >> full_simp_tac(srw_ss())[dec_clock_def]);

val evaluate_decs_globals = Q.store_thm("evaluate_decs_globals",
  `∀env s ds s' g r.
    conSem$evaluate_decs env s ds = (s',g,r) ⇒
    s'.globals = s.globals ++ MAP SOME g`,
  Induct_on`ds`>>srw_tac[][evaluate_decs_def,conLangTheory.num_defs_def,LENGTH_NIL]>>
  every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >> res_tac >> full_simp_tac(srw_ss())[] >>
  Cases_on`h`>>full_simp_tac(srw_ss())[evaluate_dec_def,conLangTheory.num_defs_def] >>
  rpt (pop_assum mp_tac) >> TRY BasicProvers.TOP_CASE_TAC >> full_simp_tac(srw_ss())[] >>
  srw_tac[][] >> full_simp_tac(srw_ss())[]  >> srw_tac[][] >>
  imp_res_tac evaluate_globals >> simp[] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >> simp[]);

val evaluate_prog_globals = Q.store_thm("evaluate_prog_globals",
  `∀env s p s' g r. evaluate_prog env s p = (s',g,NONE) ⇒
    s'.globals = s.globals ++ g`,
  Induct_on`p`>>srw_tac[][evaluate_prog_def] >> srw_tac[][LENGTH_NIL] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >> res_tac >> full_simp_tac(srw_ss())[]);

(* finding the InitGlobal operations *)
val op_gbag_def = Define`
  op_gbag (Init_global_var n) = BAG_INSERT n {||} ∧
  op_gbag _ = {||}
`;

val set_globals_def = tDefine "set_globals"`
  (set_globals ((Raise _ e):conLang$exp) = set_globals e) ∧
  (set_globals (Handle _ e pes) = set_globals e ⊎ elist_globals (MAP SND pes)) ∧
  (set_globals (Con _ _ es) = elist_globals es) ∧
  (set_globals (Fun _ _ e) = set_globals e) ∧
  (set_globals (App _ op es) = op_gbag op ⊎ elist_globals es) ∧
  (set_globals (Mat _ e pes) = set_globals e ⊎ elist_globals (MAP SND pes)) ∧
  (set_globals (Let _ _ e1 e2) = set_globals e1 ⊎ set_globals e2) ∧
  (set_globals (Letrec _ es e) =
    set_globals e ⊎ (elist_globals (MAP (SND o SND) es))) ∧
  (set_globals _ = {||}) ∧
  (elist_globals [] = {||}) ∧
  (elist_globals (e::es) = set_globals e ⊎ elist_globals es)`
 (WF_REL_TAC `
      measure (λa. case a of INL e => conLang$exp_size e | INR el => conLang$exp6_size el)` >>
  rw[]
  >-
    (Induct_on`es`>>fs[conLangTheory.exp_size_def]>>
    Cases>>Cases_on`r`>>fs[conLangTheory.exp_size_def])
  >>
    Induct_on`pes`>>fs[conLangTheory.exp_size_def]>>
    Cases>>fs[conLangTheory.exp_size_def])
val _ = export_rewrites ["set_globals_def"]

val elist_globals_append = Q.store_thm("elist_globals_append",
  `∀a b. elist_globals (a++b) =
  elist_globals a ⊎ elist_globals b`,
  Induct>>fs[set_globals_def,ASSOC_BAG_UNION])

val elist_globals_reverse = Q.store_thm("elist_globals_reverse",
  `∀ls. elist_globals (REVERSE ls) = elist_globals ls`,
  Induct>>fs[set_globals_def,elist_globals_append,COMM_BAG_UNION])

val esgc_free_def = tDefine "esgc_free" `
  (esgc_free ((Raise _ e):conLang$exp) ⇔ esgc_free e) ∧
  (esgc_free (Handle _ e pes) ⇔ esgc_free e ∧ EVERY esgc_free (MAP SND pes)) ∧
  (esgc_free (Con _ _ es) ⇔ EVERY esgc_free es) ∧
  (esgc_free (Fun _ _ e) ⇔ set_globals e = {||}) ∧
  (esgc_free (App _ op es) ⇔ EVERY esgc_free es) ∧
  (esgc_free (Mat _ e pes) ⇔ esgc_free e ∧ EVERY esgc_free (MAP SND pes)) ∧
  (esgc_free (Let _ _ e1 e2) ⇔ esgc_free e1 ∧ esgc_free e2) ∧
  (esgc_free (Letrec _ es e) ⇔
    esgc_free e ∧ (elist_globals (MAP (SND o SND) es)) = {||}) ∧
  (esgc_free _ = T)`
  (WF_REL_TAC `measure exp_size` >> simp[] >> rpt strip_tac >>
  TRY
   (Induct_on`pes`>>fs[]>>
   Cases>>rw[]>>
   fs[conLangTheory.exp_size_def]>>NO_TAC)>>
  Induct_on`es`>>fs[]>>rw[]>>fs[conLangTheory.exp_size_def])

val esgc_free_def = save_thm("esgc_free_def[simp]",
  SIMP_RULE (bool_ss ++ ETA_ss) [] esgc_free_def)

val dec_set_globals_def = Define`
  (dec_set_globals (Dlet n e) = set_globals e) ∧
  (dec_set_globals (Dletrec es) = elist_globals (MAP (SND o SND) es)) ∧
  (decs_set_globals (Prompt []) = {||}) ∧
  (decs_set_globals (Prompt (d::ds)) = dec_set_globals d ⊎ decs_set_globals (Prompt ds))`

val _ = export_theory()
