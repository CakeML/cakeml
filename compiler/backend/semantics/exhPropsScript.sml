open preamble 

val _ = new_theory"exhProps";

(*
val build_rec_env_merge = Q.store_thm("build_rec_env_merge",
  `build_rec_env funs cle env = MAP (λ(f,cdr). (f, (Recclosure cle funs f))) funs ++ env`,
  srw_tac[][build_rec_env_def] >>
  qho_match_abbrev_tac `FOLDR (f funs) env funs = MAP (g funs) funs ++ env` >>
  qsuff_tac `∀funs env funs0. FOLDR (f funs0) env funs = MAP (g funs0) funs ++ env` >- srw_tac[][]  >>
  unabbrev_all_tac >> simp[] >>
  Induct >> srw_tac[][] >>
  PairCases_on`h` >> srw_tac[][])

val Boolv_disjoint = save_thm("Boolv_disjoint",EVAL``exhSem$Boolv T = Boolv F``);

val pmatch_any_match = Q.store_thm("pmatch_any_match",
  `(∀s p v env env'. pmatch s p v env = Match env' ⇒
       ∀env. ∃env'. pmatch s p v env = Match env') ∧
    (∀s ps vs env env'. pmatch_list s ps vs env = Match env' ⇒
       ∀env. ∃env'. pmatch_list s ps vs env = Match env')`,
  ho_match_mp_tac pmatch_ind >>
  srw_tac[][pmatch_def] >>
  pop_assum mp_tac >>
  BasicProvers.CASE_TAC >>
  full_simp_tac(srw_ss())[] >> strip_tac >> full_simp_tac(srw_ss())[] >>
  BasicProvers.CASE_TAC >> full_simp_tac(srw_ss())[] >>
  metis_tac[semanticPrimitivesTheory.match_result_distinct])

val pmatch_any_no_match = Q.store_thm("pmatch_any_no_match",
  `(∀s p v env. pmatch s p v env = No_match ⇒
       ∀env. pmatch s p v env = No_match) ∧
    (∀s ps vs env. pmatch_list s ps vs env = No_match ⇒
       ∀env. pmatch_list s ps vs env = No_match)`,
  ho_match_mp_tac pmatch_ind >>
  srw_tac[][pmatch_def] >>
  pop_assum mp_tac >>
  BasicProvers.CASE_TAC >>
  full_simp_tac(srw_ss())[] >> strip_tac >> full_simp_tac(srw_ss())[] >>
  BasicProvers.CASE_TAC >> full_simp_tac(srw_ss())[] >>
  imp_res_tac pmatch_any_match >>
  metis_tac[semanticPrimitivesTheory.match_result_distinct])

val pmatch_any_match_error = Q.store_thm("pmatch_any_match_error",
  `(∀s p v env. pmatch s p v env = Match_type_error ⇒
       ∀env. pmatch s p v env = Match_type_error) ∧
    (∀s ps vs env. pmatch_list s ps vs env = Match_type_error ⇒
       ∀env. pmatch_list s ps vs env = Match_type_error)`,
  srw_tac[][] >> qmatch_abbrev_tac`X = Y` >> Cases_on`X` >> full_simp_tac(srw_ss())[markerTheory.Abbrev_def] >>
  metis_tac[semanticPrimitivesTheory.match_result_distinct
           ,pmatch_any_no_match,pmatch_any_match]);

val pmatch_list_pairwise = Q.store_thm("pmatch_list_pairwise",
  `∀ps vs s env env'. pmatch_list s ps vs env = Match env' ⇒
      EVERY2 (λp v. ∀env. ∃env'. pmatch s p v env = Match env') ps vs`,
  Induct >> Cases_on`vs` >> simp[pmatch_def] >>
  rpt gen_tac >> BasicProvers.CASE_TAC >> strip_tac >>
  res_tac >> simp[] >> metis_tac[pmatch_any_match])

val _ = Q.store_thm("pmatch_list_snoc_nil[simp]",
  `∀p ps v vs s env.
      (pmatch_list s [] (SNOC v vs) env = Match_type_error) ∧
      (pmatch_list s (SNOC p ps) [] env = Match_type_error)`,
  Cases_on`ps`>>Cases_on`vs`>>simp[pmatch_def]);

val pmatch_list_snoc = Q.store_thm("pmatch_list_snoc",
  `∀ps vs p v s env. LENGTH ps = LENGTH vs ⇒
      pmatch_list s (SNOC p ps) (SNOC v vs) env =
      case pmatch_list s ps vs env of
      | Match env' => pmatch s p v env'
      | res => res`,
  Induct >> Cases_on`vs` >> simp[pmatch_def] >> srw_tac[][] >>
  BasicProvers.CASE_TAC);

val pmatch_append = Q.store_thm("pmatch_append",
  `(∀s p v env n.
      (pmatch s p v env =
       map_match (combin$C APPEND (DROP n env)) (pmatch s p v (TAKE n env)))) ∧
    (∀s ps vs env n.
      (pmatch_list s ps vs env =
       map_match (combin$C APPEND (DROP n env)) (pmatch_list s ps vs (TAKE n env))))`,
  ho_match_mp_tac pmatch_ind >>
  srw_tac[][pmatch_def]
  >- ( BasicProvers.CASE_TAC >> full_simp_tac(srw_ss())[] >>
       BasicProvers.CASE_TAC >> full_simp_tac(srw_ss())[]) >>
  pop_assum (qspec_then`n`mp_tac) >>
  Cases_on `pmatch s p v (TAKE n env)`>>full_simp_tac(srw_ss())[] >>
  strip_tac >> res_tac >>
  qmatch_assum_rename_tac`pmatch s p v (TAKE n env) = Match env1` >>
  pop_assum(qspec_then`LENGTH env1`mp_tac) >>
  simp_tac(srw_ss())[rich_listTheory.TAKE_LENGTH_APPEND,rich_listTheory.DROP_LENGTH_APPEND]);

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
  ]);

val evaluate_length = Q.store_thm("evaluate_length",
  `(∀env (s:'ffi exhSem$state) ls s' vs.
      evaluate env s ls = (s',Rval vs) ⇒ LENGTH vs = LENGTH ls) ∧
   (∀env (s:'ffi exhSem$state) v pes s' vs.
      evaluate_match env s v pes = (s', Rval vs) ⇒ LENGTH vs = 1)`,
  ho_match_mp_tac evaluate_ind >>
  srw_tac[][evaluate_def] >> srw_tac[][] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
  Cases_on `r` >>
  fs [evaluateTheory.list_result_def] >>
  var_eq_tac >>
  rw []);

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
  qmatch_goalsub_rename_tac`op:modLang$op` >>
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
  srw_tac[][] >> full_simp_tac(srw_ss())[do_app_cases] >>
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

open bagTheory conPropsTheory

(* Same naming scheme as clos *)
val set_globals_def = tDefine "set_globals"`
  (set_globals (Raise _ e) = set_globals e) ∧
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
      measure (λa. case a of INL e => exp_size e | INR el => exp6_size el)` >>
  rw[]
  >-
    (Induct_on`es`>>fs[exhLangTheory.exp_size_def]>>
    Cases>>Cases_on`r`>>fs[exhLangTheory.exp_size_def])
  >>
    Induct_on`pes`>>fs[exhLangTheory.exp_size_def]>>
    Cases>>fs[exhLangTheory.exp_size_def])
val _ = export_rewrites ["set_globals_def"]

val elist_globals_append = Q.store_thm("elist_globals_append",
  `∀a b. elist_globals (a++b) =
  elist_globals a ⊎ elist_globals b`,
  Induct>>fs[set_globals_def,ASSOC_BAG_UNION])

val elist_globals_reverse = Q.store_thm("elist_globals_reverse",
  `∀ls. elist_globals (REVERSE ls) = elist_globals ls`,
  Induct>>fs[set_globals_def,elist_globals_append,COMM_BAG_UNION])

val esgc_free_def = tDefine "esgc_free" `
  (esgc_free (Raise _ e) ⇔ esgc_free e) ∧
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
   fs[exhLangTheory.exp_size_def]>>NO_TAC)>>
  Induct_on`es`>>fs[]>>rw[]>>fs[exhLangTheory.exp_size_def])

val esgc_free_def = save_thm("esgc_free_def[simp]",
  SIMP_RULE (bool_ss ++ ETA_ss) [] esgc_free_def)
  *)

val _ = export_theory()
