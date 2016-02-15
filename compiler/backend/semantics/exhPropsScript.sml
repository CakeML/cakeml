open preamble exhSemTheory;

val _ = new_theory"exhProps";

val build_rec_env_merge = store_thm("build_rec_env_merge",
  ``build_rec_env funs cle env = MAP (λ(f,cdr). (f, (Recclosure cle funs f))) funs ++ env``,
  srw_tac[][build_rec_env_def] >>
  qho_match_abbrev_tac `FOLDR (f funs) env funs = MAP (g funs) funs ++ env` >>
  qsuff_tac `∀funs env funs0. FOLDR (f funs0) env funs = MAP (g funs0) funs ++ env` >- srw_tac[][]  >>
  unabbrev_all_tac >> simp[] >>
  Induct >> srw_tac[][] >>
  PairCases_on`h` >> srw_tac[][])

val Boolv_disjoint = save_thm("Boolv_disjoint",EVAL``exhSem$Boolv T = Boolv F``);

val pmatch_any_match = store_thm("pmatch_any_match",
  ``(∀s p v env env'. pmatch s p v env = Match env' ⇒
       ∀env. ∃env'. pmatch s p v env = Match env') ∧
    (∀s ps vs env env'. pmatch_list s ps vs env = Match env' ⇒
       ∀env. ∃env'. pmatch_list s ps vs env = Match env')``,
  ho_match_mp_tac pmatch_ind >>
  srw_tac[][pmatch_def] >>
  pop_assum mp_tac >>
  BasicProvers.CASE_TAC >>
  full_simp_tac(srw_ss())[] >> strip_tac >> full_simp_tac(srw_ss())[] >>
  BasicProvers.CASE_TAC >> full_simp_tac(srw_ss())[] >>
  metis_tac[semanticPrimitivesTheory.match_result_distinct])

val pmatch_any_no_match = store_thm("pmatch_any_no_match",
  ``(∀s p v env. pmatch s p v env = No_match ⇒
       ∀env. pmatch s p v env = No_match) ∧
    (∀s ps vs env. pmatch_list s ps vs env = No_match ⇒
       ∀env. pmatch_list s ps vs env = No_match)``,
  ho_match_mp_tac pmatch_ind >>
  srw_tac[][pmatch_def] >>
  pop_assum mp_tac >>
  BasicProvers.CASE_TAC >>
  full_simp_tac(srw_ss())[] >> strip_tac >> full_simp_tac(srw_ss())[] >>
  BasicProvers.CASE_TAC >> full_simp_tac(srw_ss())[] >>
  imp_res_tac pmatch_any_match >>
  metis_tac[semanticPrimitivesTheory.match_result_distinct])

val pmatch_any_match_error = store_thm("pmatch_any_match_error",
  ``(∀s p v env. pmatch s p v env = Match_type_error ⇒
       ∀env. pmatch s p v env = Match_type_error) ∧
    (∀s ps vs env. pmatch_list s ps vs env = Match_type_error ⇒
       ∀env. pmatch_list s ps vs env = Match_type_error)``,
  srw_tac[][] >> qmatch_abbrev_tac`X = Y` >> Cases_on`X` >> full_simp_tac(srw_ss())[markerTheory.Abbrev_def] >>
  metis_tac[semanticPrimitivesTheory.match_result_distinct
           ,pmatch_any_no_match,pmatch_any_match]);

val pmatch_list_pairwise = store_thm("pmatch_list_pairwise",
  ``∀ps vs s env env'. pmatch_list s ps vs env = Match env' ⇒
      EVERY2 (λp v. ∀env. ∃env'. pmatch s p v env = Match env') ps vs``,
  Induct >> Cases_on`vs` >> simp[pmatch_def] >>
  rpt gen_tac >> BasicProvers.CASE_TAC >> strip_tac >>
  res_tac >> simp[] >> metis_tac[pmatch_any_match])

val _ = store_thm("pmatch_list_snoc_nil[simp]",
  ``∀p ps v vs s env.
      (pmatch_list s [] (SNOC v vs) env = Match_type_error) ∧
      (pmatch_list s (SNOC p ps) [] env = Match_type_error)``,
  Cases_on`ps`>>Cases_on`vs`>>simp[pmatch_def]);

val pmatch_list_snoc = store_thm("pmatch_list_snoc",
  ``∀ps vs p v s env. LENGTH ps = LENGTH vs ⇒
      pmatch_list s (SNOC p ps) (SNOC v vs) env =
      case pmatch_list s ps vs env of
      | Match env' => pmatch s p v env'
      | res => res``,
  Induct >> Cases_on`vs` >> simp[pmatch_def] >> srw_tac[][] >>
  BasicProvers.CASE_TAC)

val pmatch_append = store_thm("pmatch_append",
  ``(∀s p v env n.
      (pmatch s p v env =
       map_match (combin$C APPEND (DROP n env)) (pmatch s p v (TAKE n env)))) ∧
    (∀s ps vs env n.
      (pmatch_list s ps vs env =
       map_match (combin$C APPEND (DROP n env)) (pmatch_list s ps vs (TAKE n env))))``,
  ho_match_mp_tac pmatch_ind >>
  srw_tac[][pmatch_def]
  >- ( BasicProvers.CASE_TAC >> full_simp_tac(srw_ss())[] >>
       BasicProvers.CASE_TAC >> full_simp_tac(srw_ss())[]) >>
  pop_assum (qspec_then`n`mp_tac) >>
  Cases_on `pmatch s p v (TAKE n env)`>>full_simp_tac(srw_ss())[] >>
  strip_tac >> res_tac >>
  qmatch_assum_rename_tac`pmatch s p v (TAKE n env) = Match env1` >>
  pop_assum(qspec_then`LENGTH env1`mp_tac) >>
  simp_tac(srw_ss())[rich_listTheory.TAKE_LENGTH_APPEND,rich_listTheory.DROP_LENGTH_APPEND] )

val pmatch_nil = save_thm("pmatch_nil",
  LIST_CONJ [
    pmatch_append
    |> CONJUNCT1
    |> Q.SPECL[`s`,`p`,`v`,`env`,`0`]
    |> SIMP_RULE(srw_ss())[]
  ,
    pmatch_append
    |> CONJUNCT2
    |> Q.SPECL[`s`,`ps`,`vs`,`env`,`0`]
    |> SIMP_RULE(srw_ss())[]
  ])

val evaluate_length = Q.store_thm("evaluate_length",
  `(∀env (s:'ffi exhSem$state) ls s' vs.
      evaluate env s ls = (s',Rval vs) ⇒ LENGTH vs = LENGTH ls) ∧
   (∀env (s:'ffi exhSem$state) v pes s' vs.
      evaluate_match env s v pes = (s', Rval vs) ⇒ LENGTH vs = 1)`,
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
   (evaluate_match env s v pes = (s',Rval vs) ⇒ ∃y. vs = [y])`,
  srw_tac[][] >> imp_res_tac evaluate_length >> full_simp_tac(srw_ss())[] >> metis_tac[SING_HD])

val do_app_add_to_clock = Q.store_thm("do_app_add_to_clock",
  `(do_app (s with clock := s.clock + extra) op vs =
    OPTION_MAP (λ(s',r). (s' with clock := s'.clock + extra,r)) (do_app s op vs))`,
  full_simp_tac(srw_ss())[do_app_def] >>
  BasicProvers.CASE_TAC >> full_simp_tac(srw_ss())[]>-( every_case_tac >> full_simp_tac(srw_ss())[] ) >>
  reverse(Cases_on`op`>>full_simp_tac(srw_ss())[]) >- ( every_case_tac >> full_simp_tac(srw_ss())[] ) >>
  qmatch_goalsub_rename_tac`op:ast$op` >>
  Cases_on`op`>>full_simp_tac(srw_ss())[] >>
  every_case_tac >>
  full_simp_tac(srw_ss())[LET_THM,
     semanticPrimitivesTheory.store_alloc_def,
     semanticPrimitivesTheory.store_lookup_def,
     semanticPrimitivesTheory.store_assign_def] >>
  srw_tac[][]);

val evaluate_add_to_clock = Q.store_thm("evaluate_add_to_clock",
  `(∀env (s:'ffi exhSem$state) es s' r.
       evaluate env s es = (s',r) ∧
       r ≠ Rerr (Rabort Rtimeout_error) ⇒
       evaluate env (s with clock := s.clock + extra) es =
         (s' with clock := s'.clock + extra,r)) ∧
   (∀env (s:'ffi exhSem$state) pes v s' r.
       evaluate_match env s pes v = (s',r) ∧
       r ≠ Rerr (Rabort Rtimeout_error) ⇒
       evaluate_match env (s with clock := s.clock + extra) pes v =
         (s' with clock := s'.clock + extra,r))`,
  ho_match_mp_tac evaluate_ind >>
  srw_tac[][evaluate_def] >>
  every_case_tac >> full_simp_tac(srw_ss())[do_app_add_to_clock] >> srw_tac[][] >> rev_full_simp_tac(srw_ss())[] >>
  rev_full_simp_tac(srw_ss()++ARITH_ss)[dec_clock_def]);

val do_app_io_events_mono = Q.prove(
  `do_app s op vs = SOME(s',r) ⇒
   s.ffi.io_events ≼ s'.ffi.io_events ∧
   (IS_SOME s.ffi.final_event ⇒ s'.ffi = s.ffi)`,
  srw_tac[][] >> imp_res_tac do_app_cases >> full_simp_tac(srw_ss())[do_app_def] >>
  every_case_tac >>
  full_simp_tac(srw_ss())[LET_THM,
     semanticPrimitivesTheory.store_alloc_def,
     semanticPrimitivesTheory.store_lookup_def,
     semanticPrimitivesTheory.store_assign_def] >> srw_tac[][] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
  full_simp_tac(srw_ss())[ffiTheory.call_FFI_def] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][]);

val evaluate_io_events_mono = Q.store_thm("evaluate_io_events_mono",
  `(∀env (s:'ffi exhSem$state) es s' r.
      evaluate env s es = (s',r) ⇒
      s.ffi.io_events ≼ s'.ffi.io_events ∧
      (IS_SOME s.ffi.final_event ⇒ s'.ffi = s.ffi)) ∧
   (∀env (s:'ffi exhSem$state) pes v s' r.
      evaluate_match env s pes v = (s',r) ⇒
      s.ffi.io_events ≼ s'.ffi.io_events ∧
      (IS_SOME s.ffi.final_event ⇒ s'.ffi = s.ffi))`,
  ho_match_mp_tac evaluate_ind >> srw_tac[][evaluate_def] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >> rev_full_simp_tac(srw_ss())[] >> full_simp_tac(srw_ss())[dec_clock_def] >>
  imp_res_tac do_app_io_events_mono >> full_simp_tac(srw_ss())[] >>
  metis_tac[IS_PREFIX_TRANS]);

val with_clock_ffi = Q.prove(
  `(s with clock := k).ffi = s.ffi`,EVAL_TAC)

val evaluate_add_to_clock_io_events_mono = Q.store_thm("evaluate_add_to_clock_io_events_mono",
  `(∀env (s:'ffi exhSem$state) es extra.
       (FST(evaluate env s es)).ffi.io_events ≼
       (FST(evaluate env (s with clock := s.clock + extra) es)).ffi.io_events ∧
       (IS_SOME((FST(evaluate env s es)).ffi.final_event) ⇒
        (FST(evaluate env (s with clock := s.clock + extra) es)).ffi =
        (FST(evaluate env s es)).ffi)) ∧
   (∀env (s:'ffi exhSem$state) pes v extra.
       (FST(evaluate_match env s pes v)).ffi.io_events ≼
       (FST(evaluate_match env (s with clock := s.clock + extra) pes v)).ffi.io_events ∧
       (IS_SOME((FST(evaluate_match env s pes v)).ffi.final_event) ⇒
        (FST(evaluate_match env (s with clock := s.clock + extra) pes v)).ffi =
        (FST(evaluate_match env s pes v)).ffi))`,
  ho_match_mp_tac evaluate_ind >> srw_tac[][evaluate_def] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >>
  imp_res_tac evaluate_add_to_clock >> rev_full_simp_tac(srw_ss())[] >> full_simp_tac(srw_ss())[] >> srw_tac[][] >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
  imp_res_tac evaluate_io_events_mono >> full_simp_tac(srw_ss())[] >> full_simp_tac(srw_ss())[dec_clock_def] >>
  full_simp_tac(srw_ss())[do_app_add_to_clock,UNCURRY] >> srw_tac[][] >> full_simp_tac(srw_ss())[] >>
  TRY(last_x_assum(qspec_then`extra`mp_tac)>>simp[]>>NO_TAC) >>
  metis_tac[FST,IS_PREFIX_TRANS,evaluate_io_events_mono,PAIR,with_clock_ffi,do_app_io_events_mono]);

val _ = export_theory()
