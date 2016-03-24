open preamble conSemTheory

val _ = new_theory"conProps"

val with_same_v = Q.store_thm("with_same_v[simp]",
  `((env:conSem$environment) with v := env.v) = env`,
  srw_tac[][conSemTheory.environment_component_equality])

val do_app_cases = Q.store_thm("do_app_cases",
  `conSem$do_app s op vs = SOME x ⇒
    (∃z n1 n2. op = (Op (Opn z)) ∧ vs = [Litv (IntLit n1); Litv (IntLit n2)]) ∨
    (∃z n1 n2. op = (Op (Opb z)) ∧ vs = [Litv (IntLit n1); Litv (IntLit n2)]) ∨
    (∃v1 v2. op = (Op Equality) ∧ vs = [v1; v2]) ∨
    (∃lnum v. op = (Op Opassign) ∧ vs = [Loc lnum; v]) ∨
    (∃n. op = (Op Opderef) ∧ vs = [Loc n]) ∨
    (∃v. op = (Op Opref) ∧ vs = [v]) ∨
    (∃n w. op = (Op Aw8alloc) ∧ vs = [Litv (IntLit n); Litv (Word8 w)]) ∨
    (∃lnum i. op = (Op Aw8sub) ∧ vs = [Loc lnum; Litv (IntLit i)]) ∨
    (∃n. op = (Op Aw8length) ∧ vs = [Loc n]) ∨
    (∃lnum i w. op = (Op Aw8update) ∧ vs = [Loc lnum; Litv (IntLit i); Litv (Word8 w)]) ∨
    (∃w. op = (Op W8toInt) ∧ vs = [Litv (Word8 w)]) ∨
    (∃n. op = (Op W8fromInt) ∧ vs = [Litv (IntLit n)]) ∨
    (∃c. op = (Op Ord) ∧ vs = [Litv (Char c)]) ∨
    (∃n. op = (Op Chr) ∧ vs = [Litv (IntLit n)]) ∨
    (∃z c1 c2. op = (Op (Chopb z)) ∧ vs = [Litv (Char c1); Litv (Char c2)]) ∨
    (∃s. op = (Op Explode) ∧ vs = [Litv (StrLit s)]) ∨
    (∃v ls. op = (Op Implode) ∧ vs = [v] ∧ (v_to_char_list v = SOME ls)) ∨
    (∃s. op = (Op Strlen) ∧ vs = [Litv (StrLit s)]) ∨
    (∃v vs'. op = (Op VfromList) ∧ vs = [v] ∧ (v_to_list v = SOME vs')) ∨
    (∃vs' i. op = (Op Vsub) ∧ vs = [Vectorv vs'; Litv (IntLit i)]) ∨
    (∃vs'. op = (Op Vlength) ∧ vs = [Vectorv vs']) ∨
    (∃v n. op = (Op Aalloc) ∧ vs = [Litv (IntLit n); v]) ∨
    (∃lnum i. op = (Op Asub) ∧ vs = [Loc lnum; Litv (IntLit i)]) ∨
    (∃n. op = (Op Alength) ∧ vs = [Loc n]) ∨
    (∃lnum i v. op = (Op Aupdate) ∧ vs = [Loc lnum; Litv (IntLit i); v]) ∨
    (∃lnum n. op = (Op (FFI n)) ∧ vs = [Loc lnum])`,
  Cases_on`s`>>srw_tac[][conSemTheory.do_app_def] >>
  pop_assum mp_tac >>
  Cases_on`op` >- (
    simp[] >>
    every_case_tac >> full_simp_tac(srw_ss())[] ) >>
  BasicProvers.CASE_TAC);

val do_app_io_events_mono = Q.store_thm("do_app_io_events_mono",
  `do_app (f,s) op vs = SOME((f',s'),r) ⇒
   s.io_events ≼ s'.io_events ∧
   (IS_SOME s.final_event ⇒ s' = s)`,
  srw_tac[][] >> imp_res_tac do_app_cases >> full_simp_tac(srw_ss())[do_app_def] >>
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
      s.ffi.io_events ≼ s'.ffi.io_events ∧
      (IS_SOME s.ffi.final_event ⇒ s'.ffi = s.ffi)) ∧
   (∀env ^s pes v err_v s' r. evaluate_match env s pes v err_v = (s',r) ⇒
      s.ffi.io_events ≼ s'.ffi.io_events ∧
      (IS_SOME s.ffi.final_event ⇒ s'.ffi = s.ffi))`,
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
  >- metis_tac [APPEND_ASSOC, pat_bindings_def]
  >- metis_tac [APPEND_ASSOC, pat_bindings_def]
  >- srw_tac[][pat_bindings_def]
  >- metis_tac [APPEND_ASSOC, pat_bindings_def]);

val Boolv_11 = store_thm("Boolv_11[simp]",
  ``Boolv b1 = Boolv b2 ⇔ (b1 = b2)``, EVAL_TAC >> srw_tac[][])

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
  EVAL_TAC)

val evaluate_add_to_clock_io_events_mono = Q.store_thm("evaluate_add_to_clock_io_events_mono",
  `(∀env ^s prog extra.
    (FST (evaluate env s prog)).ffi.io_events ≼
    (FST (evaluate env (s with clock := s.clock + extra) prog)).ffi.io_events ∧
    (IS_SOME ((FST (evaluate env s prog)).ffi.final_event) ⇒
      (FST (evaluate env (s with clock := s.clock + extra) prog)).ffi =
      (FST (evaluate env s prog)).ffi)) ∧
   (∀env ^s pes v err_v extra.
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
  `∀x y z. evaluate_dec x y z = (a,b) ⇒
     y.ffi.io_events ≼ a.ffi.io_events ∧
     (IS_SOME y.ffi.final_event ⇒ a.ffi = y.ffi)`,
   Cases_on`z`>>srw_tac[][evaluate_dec_def] >>
   every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
   imp_res_tac evaluate_io_events_mono);

val evaluate_dec_add_to_clock_io_events_mono = Q.store_thm("evaluate_dec_add_to_clock_io_events_mono",
  `∀env s prog extra.
   (FST (evaluate_dec env s prog)).ffi.io_events ≼
   (FST (evaluate_dec env (s with clock := s.clock + extra) prog)).ffi.io_events ∧
   (IS_SOME ((FST (evaluate_dec env s prog)).ffi.final_event) ⇒
     (FST (evaluate_dec env (s with clock := s.clock + extra) prog)).ffi =
     (FST (evaluate_dec env s prog)).ffi)`,
  Cases_on`prog`>>srw_tac[][evaluate_dec_def]>>
  split_pair_case_tac >> full_simp_tac(srw_ss())[] >>
  split_pair_case_tac >> full_simp_tac(srw_ss())[] >>
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
  imp_res_tac evaluate_dec_io_events_mono >>
  res_tac >> full_simp_tac(srw_ss())[] >>
  metis_tac[IS_PREFIX_TRANS]);

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
  qmatch_assum_abbrev_tac`evaluate_decs ee sss prog = _` >>
  last_x_assum(qspecl_then[`ee`,`sss`,`extra`]mp_tac)>>simp[Abbr`sss`]>>
  fsrw_tac[ARITH_ss][] >> srw_tac[][] >> full_simp_tac(srw_ss())[] >>
  metis_tac[IS_PREFIX_TRANS,FST]);

val evaluate_prompt_io_events_mono = Q.store_thm("evaluate_prompt_io_events_mono",
  `∀x y z. evaluate_prompt x y z = (a,b) ⇒
     y.ffi.io_events ≼ a.ffi.io_events ∧
     (IS_SOME y.ffi.final_event ⇒ a.ffi = y.ffi)`,
   Cases_on`z`>>srw_tac[][evaluate_prompt_def] >>
   every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
   imp_res_tac evaluate_decs_io_events_mono);

val evaluate_prompt_add_to_clock_io_events_mono = Q.store_thm("evaluate_prompt_add_to_clock_io_events_mono",
  `∀env s prog extra.
   (FST (evaluate_prompt env s prog)).ffi.io_events ≼
   (FST (evaluate_prompt env (s with clock := s.clock + extra) prog)).ffi.io_events ∧
   (IS_SOME ((FST (evaluate_prompt env s prog)).ffi.final_event) ⇒
     (FST (evaluate_prompt env (s with clock := s.clock + extra) prog)).ffi =
     (FST (evaluate_prompt env s prog)).ffi)`,
  Cases_on`prog`>>srw_tac[][evaluate_prompt_def]>>
  every_case_tac >> full_simp_tac(srw_ss())[] >>
  qmatch_assum_abbrev_tac`evaluate_decs ee (ss with clock := _ + extra) pp = _` >>
  qispl_then[`ee`,`ss`,`pp`,`extra`]mp_tac evaluate_decs_add_to_clock_io_events_mono >>
  simp[]);

val evaluate_prog_io_events_mono = Q.store_thm("evaluate_prog_io_events_mono",
  `∀prog env s s' x y. evaluate_prog env s prog = (s',x,y) ⇒
   s.ffi.io_events ≼ s'.ffi.io_events ∧
   (IS_SOME s.ffi.final_event ⇒ s'.ffi = s.ffi)`,
  Induct >> srw_tac[][evaluate_prog_def] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
  imp_res_tac evaluate_prompt_io_events_mono >>
  res_tac >> full_simp_tac(srw_ss())[] >>
  metis_tac[IS_PREFIX_TRANS]);

val evaluate_prog_add_to_clock_io_events_mono = Q.store_thm("evaluate_prog_add_to_clock_io_events_mono",
  `∀env s prog extra.
   (FST (evaluate_prog env s prog)).ffi.io_events ≼
   (FST (evaluate_prog env (s with clock := s.clock + extra) prog)).ffi.io_events ∧
   (IS_SOME ((FST (evaluate_prog env s prog)).ffi.final_event) ⇒
     (FST (evaluate_prog env (s with clock := s.clock + extra) prog)).ffi =
     (FST (evaluate_prog env s prog)).ffi)`,
  Induct_on`prog` >> srw_tac[][evaluate_prog_def] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >>
  qmatch_assum_abbrev_tac`evaluate_prompt ee (ss with clock := _ + extra) pp = _` >>
  qispl_then[`ee`,`ss`,`pp`,`extra`]mp_tac evaluate_prompt_add_to_clock_io_events_mono >>
  simp[] >> srw_tac[][] >>
  imp_res_tac evaluate_prompt_add_to_clock >> full_simp_tac(srw_ss())[] >>
  imp_res_tac evaluate_prog_io_events_mono >> full_simp_tac(srw_ss())[] >>
  rveq >|[rator_x_assum`evaluate_prog`mp_tac,ALL_TAC,ALL_TAC]>>
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

val pmatch_any_match = store_thm("pmatch_any_match",
  ``(∀(exh:exh_ctors_env) s p v env env'. pmatch exh s p v env = Match env' ⇒
       ∀env. ∃env'. pmatch exh s p v env = Match env') ∧
    (∀(exh:exh_ctors_env) s ps vs env env'. pmatch_list exh s ps vs env = Match env' ⇒
       ∀env. ∃env'. pmatch_list exh s ps vs env = Match env')``,
  ho_match_mp_tac pmatch_ind >>
  srw_tac[][pmatch_def] >>
  pop_assum mp_tac >>
  BasicProvers.CASE_TAC >>
  full_simp_tac(srw_ss())[] >> strip_tac >> full_simp_tac(srw_ss())[LET_THM] >>
  BasicProvers.CASE_TAC >> full_simp_tac(srw_ss())[] >>
  TRY BasicProvers.CASE_TAC >> full_simp_tac(srw_ss())[] >> srw_tac[][] >> rev_full_simp_tac(srw_ss())[] >> full_simp_tac(srw_ss())[] >>
  metis_tac[semanticPrimitivesTheory.match_result_distinct])

val pmatch_any_no_match = store_thm("pmatch_any_no_match",
  ``(∀(exh:exh_ctors_env) s p v env. pmatch exh s p v env = No_match ⇒
       ∀env. pmatch exh s p v env = No_match) ∧
    (∀(exh:exh_ctors_env) s ps vs env. pmatch_list exh s ps vs env = No_match ⇒
       ∀env. pmatch_list exh s ps vs env = No_match)``,
  ho_match_mp_tac pmatch_ind >>
  srw_tac[][pmatch_def] >>
  pop_assum mp_tac >>
  BasicProvers.CASE_TAC >>
  full_simp_tac(srw_ss())[] >> strip_tac >> full_simp_tac(srw_ss())[LET_THM] >>
  BasicProvers.CASE_TAC >> full_simp_tac(srw_ss())[] >>
  imp_res_tac pmatch_any_match >>
  TRY BasicProvers.CASE_TAC >> full_simp_tac(srw_ss())[] >> srw_tac[][] >> rev_full_simp_tac(srw_ss())[] >> full_simp_tac(srw_ss())[] >>
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

val _ = export_theory()
