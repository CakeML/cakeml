(*
  Properties about flatLang and its semantics
*)
open preamble flatSemTheory
local
  open astTheory semanticPrimitivesPropsTheory terminationTheory
       evaluatePropsTheory
in end

val _ = new_theory"flatProps"

Theorem ctor_same_type_OPTREL:
   ∀c1 c2. ctor_same_type c1 c2 ⇔ OPTREL (inv_image $= SND) c1 c2
Proof
  Cases \\ Cases \\ simp[OPTREL_def,ctor_same_type_def]
  \\ rename1`_ (SOME p1) (SOME p2)`
  \\ Cases_on`p1` \\ Cases_on`p2`
  \\ EVAL_TAC
QED

Theorem pat_bindings_accum:
   (∀p acc. flatSem$pat_bindings p acc = pat_bindings p [] ⧺ acc) ∧
    ∀ps acc. pats_bindings ps acc = pats_bindings ps [] ⧺ acc
Proof
  ho_match_mp_tac flatLangTheory.pat_induction >>
  rw [] >>
  REWRITE_TAC [flatSemTheory.pat_bindings_def] >>
  metis_tac [APPEND, APPEND_ASSOC]
QED

Theorem pmatch_extend:
   (!cenv s p v env env' env''.
    pmatch cenv s p v env = Match env'
    ⇒
    ?env''. env' = env'' ++ env ∧ MAP FST env'' = pat_bindings p []) ∧
   (!cenv s ps vs env env' env''.
    pmatch_list cenv s ps vs env = Match env'
    ⇒
    ?env''. env' = env'' ++ env ∧ MAP FST env'' = pats_bindings ps [])
Proof
  ho_match_mp_tac pmatch_ind >>
  srw_tac[][pat_bindings_def, pmatch_def] >>
  every_case_tac >>
  full_simp_tac(srw_ss())[] >>
  srw_tac[][] >>
  res_tac >>
  qexists_tac `env'''++env''` >>
  srw_tac[][] >>
  metis_tac [pat_bindings_accum]
QED

Theorem pmatch_bindings:
   (∀cenv s p v env r.
      flatSem$pmatch cenv s p v env = Match r
      ⇒
      MAP FST r = pat_bindings p [] ++ MAP FST env) ∧
   ∀cenv s ps vs env r.
     flatSem$pmatch_list cenv s ps vs env = Match r
     ⇒
     MAP FST r = pats_bindings ps [] ++ MAP FST env
Proof
  ho_match_mp_tac flatSemTheory.pmatch_ind >>
  rw [pmatch_def, pat_bindings_def] >>
  rw [] >>
  every_case_tac >>
  fs [] >>
  prove_tac [pat_bindings_accum]
QED

Theorem pmatch_length:
   ∀cenv s p v env r.
      flatSem$pmatch cenv s p v env = Match r
      ⇒
      LENGTH r = LENGTH (pat_bindings p []) + LENGTH env
Proof
  rw [] >>
  imp_res_tac pmatch_bindings >>
  metis_tac [LENGTH_APPEND, LENGTH_MAP]
QED

Theorem pmatch_any_match:
   (∀cenv s p v env env'. pmatch cenv s p v env = Match env' ⇒
       ∀env. ∃env'. pmatch cenv s p v env = Match env') ∧
    (∀cenv s ps vs env env'. pmatch_list cenv s ps vs env = Match env' ⇒
       ∀env. ∃env'. pmatch_list cenv s ps vs env = Match env')
Proof
  ho_match_mp_tac pmatch_ind >>
  srw_tac[][pmatch_def] >> fs[] >>
  pop_assum mp_tac >>
  BasicProvers.CASE_TAC >>
  full_simp_tac(srw_ss())[] >> strip_tac >> full_simp_tac(srw_ss())[] >>
  BasicProvers.CASE_TAC >> full_simp_tac(srw_ss())[] >>
  metis_tac[semanticPrimitivesTheory.match_result_distinct]
QED

Theorem pmatch_any_no_match:
   (∀cenv s p v env. pmatch cenv s p v env = No_match ⇒
       ∀env. pmatch cenv s p v env = No_match) ∧
    (∀cenv s ps vs env. pmatch_list cenv s ps vs env = No_match ⇒
       ∀env. pmatch_list cenv s ps vs env = No_match)
Proof
  ho_match_mp_tac pmatch_ind >>
  srw_tac[][pmatch_def] >> fs[] >>
  pop_assum mp_tac >>
  BasicProvers.CASE_TAC >>
  full_simp_tac(srw_ss())[] >> strip_tac >> full_simp_tac(srw_ss())[] >>
  BasicProvers.CASE_TAC >> full_simp_tac(srw_ss())[] >>
  imp_res_tac pmatch_any_match >>
  metis_tac[semanticPrimitivesTheory.match_result_distinct]
QED

Theorem pmatch_any_match_error:
   (∀cenv s p v env. pmatch cenv s p v env = Match_type_error ⇒
       ∀env. pmatch cenv s p v env = Match_type_error) ∧
    (∀cenv s ps vs env. pmatch_list cenv s ps vs env = Match_type_error ⇒
       ∀env. pmatch_list cenv s ps vs env = Match_type_error)
Proof
  srw_tac[][] >> qmatch_abbrev_tac`X = Y` >> Cases_on`X` >> full_simp_tac(srw_ss())[markerTheory.Abbrev_def] >>
  metis_tac[semanticPrimitivesTheory.match_result_distinct
           ,pmatch_any_no_match,pmatch_any_match]
QED

Theorem pmatch_list_pairwise:
   ∀ps vs cenv s env env'. pmatch_list cenv s ps vs env = Match env' ⇒
      EVERY2 (λp v. ∀env. ∃env'. pmatch cenv s p v env = Match env') ps vs
Proof
  Induct >> Cases_on`vs` >> simp[pmatch_def] >>
  rpt gen_tac >> BasicProvers.CASE_TAC >> strip_tac >>
  res_tac >> simp[] >> metis_tac[pmatch_any_match]
QED

Theorem pmatch_list_snoc_nil[simp]:
   ∀p ps v vs cenv s env.
      (pmatch_list cenv s [] (SNOC v vs) env = Match_type_error) ∧
      (pmatch_list cenv s (SNOC p ps) [] env = Match_type_error)
Proof
  Cases_on`ps`>>Cases_on`vs`>>simp[pmatch_def]
QED

Theorem pmatch_list_snoc:
   ∀ps vs p v cenv s env. LENGTH ps = LENGTH vs ⇒
      pmatch_list cenv s (SNOC p ps) (SNOC v vs) env =
      case pmatch_list cenv s ps vs env of
      | Match env' => pmatch cenv s p v env'
      | res => res
Proof
  Induct >> Cases_on`vs` >> simp[pmatch_def] >> srw_tac[][] >>
  BasicProvers.CASE_TAC
QED

Theorem pmatch_append:
   (∀cenv s p v env n.
      (pmatch cenv s p v env =
       map_match (combin$C APPEND (DROP n env)) (pmatch cenv s p v (TAKE n env)))) ∧
    (∀cenv s ps vs env n.
      (pmatch_list cenv s ps vs env =
       map_match (combin$C APPEND (DROP n env)) (pmatch_list cenv s ps vs (TAKE n env))))
Proof
  ho_match_mp_tac pmatch_ind >>
  srw_tac[][pmatch_def] \\ fs[]
  >- ( BasicProvers.CASE_TAC >> full_simp_tac(srw_ss())[] >>
       BasicProvers.CASE_TAC >> full_simp_tac(srw_ss())[]) >>
  pop_assum (qspec_then`n`mp_tac) >>
  Cases_on `pmatch cenv s p v (TAKE n env)`>>full_simp_tac(srw_ss())[] >>
  strip_tac >> res_tac >>
  qmatch_assum_rename_tac`pmatch cenv s p v (TAKE n env) = Match env1` >>
  pop_assum(qspec_then`LENGTH env1`mp_tac) >>
  simp_tac(srw_ss())[rich_listTheory.TAKE_LENGTH_APPEND,rich_listTheory.DROP_LENGTH_APPEND]
QED

val pmatch_nil = save_thm("pmatch_nil",
  LIST_CONJ [
    pmatch_append
    |> CONJUNCT1
    |> Q.SPECL[`cenv`,`s`,`p`,`v`,`env`,`0`]
    |> SIMP_RULE(srw_ss())[]
  ,
    pmatch_append
    |> CONJUNCT2
    |> Q.SPECL[`cenv`,`s`,`ps`,`vs`,`env`,`0`]
    |> SIMP_RULE(srw_ss())[]
  ]);

val build_rec_env_help_lem = Q.prove (
  `∀funs env funs'.
  FOLDR (λ(f,x,e) env'. (f, flatSem$Recclosure env funs' f)::env') env' funs =
  MAP (λ(fn,n,e). (fn, Recclosure env funs' fn)) funs ++ env'`,
  Induct >>
  srw_tac[][] >>
  PairCases_on `h` >>
  srw_tac[][]);

(* Alternate definition for build_rec_env *)
Theorem build_rec_env_merge:
   ∀funs funs' env env'.
    build_rec_env funs env env' =
    MAP (λ(fn,n,e). (fn, Recclosure env funs fn)) funs ++ env'
Proof
  srw_tac[][build_rec_env_def, build_rec_env_help_lem]
QED

  (*
Theorem Boolv_11[simp]:
  Boolv b1 = Boolv b2 ⇔ (b1 = b2)
Proof
srw_tac[][Boolv_def]
QED
*)

val Unitv_simp = save_thm("Unitv_simp[simp]",
  CONJ (EVAL``Unitv T``) (EVAL ``Unitv F``));

Theorem evaluate_length:
   (∀env (s:'ffi flatSem$state) ls s' vs.
      evaluate env s ls = (s',Rval vs) ⇒ LENGTH vs = LENGTH ls) ∧
   (∀env (s:'ffi flatSem$state) v pes ev s' vs.
      evaluate_match env s v pes ev = (s', Rval vs) ⇒ LENGTH vs = 1)
Proof
  ho_match_mp_tac evaluate_ind >>
  srw_tac[][evaluate_def] >> srw_tac[][] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][]
QED

Theorem evaluate_cons:
   flatSem$evaluate env s (e::es) =
   (case evaluate env s [e] of
    | (s,Rval v) =>
      (case evaluate env s es of
       | (s,Rval vs) => (s,Rval (v++vs))
       | r => r)
    | r => r)
Proof
  Cases_on`es`>>srw_tac[][evaluate_def] >>
  every_case_tac >> full_simp_tac(srw_ss())[evaluate_def] >>
  imp_res_tac evaluate_length >>
  full_simp_tac(srw_ss())[SING_HD]
QED

Theorem evaluate_sing:
   (evaluate env s [e] = (s',Rval vs) ⇒ ∃y. vs = [y]) ∧
   (evaluate_match env s v pes ev = (s',Rval vs) ⇒ ∃y. vs = [y])
Proof
  srw_tac[][] >> imp_res_tac evaluate_length >> full_simp_tac(srw_ss())[] >> metis_tac[SING_HD]
QED

Theorem evaluate_append:
   evaluate env s (l1 ++ l2) =
   case evaluate env s l1 of
   | (s,Rval v1) =>
     (case evaluate env s l2 of
      | (s,Rval v2) => (s,Rval(v1++v2))
      | r => r)
   | r => r
Proof
  map_every qid_spec_tac[`l2`,`s`] >> Induct_on`l1` >>
  srw_tac[][evaluate_def] >- (
    every_case_tac >> full_simp_tac(srw_ss())[] ) >>
  srw_tac[][Once evaluate_cons] >>
  match_mp_tac EQ_SYM >>
  srw_tac[][Once evaluate_cons] >>
  BasicProvers.CASE_TAC >> full_simp_tac(srw_ss())[] >>
  Cases_on`r`>>full_simp_tac(srw_ss())[] >>
  every_case_tac  >> full_simp_tac(srw_ss())[]
QED

val c_updated_by = Q.prove (
  `((env:flatSem$environment) with c updated_by f) = (env with c := f env.c)`,
  rw [environment_component_equality]);

val env_lemma = Q.prove (
  `((env:flatSem$environment) with c := env.c) = env`,
  rw [environment_component_equality]);

Theorem evaluate_decs_append:
   !env s ds1 s1 cenv1 s2 cenv2 r ds2.
    evaluate_decs env s ds1 = (s1,cenv1,NONE) ∧
    evaluate_decs (env with c updated_by $UNION cenv1) s1 ds2 =
      (s2,cenv2,r)
    ⇒
    evaluate_decs env s (ds1++ds2) = (s2,cenv2 ∪ cenv1,r)
Proof
  induct_on `ds1` >>
  rw [evaluate_decs_def] >>
  fs [Once c_updated_by, env_lemma] >>
  every_case_tac >>
  fs [] >>
  rpt var_eq_tac >>
  first_x_assum drule >>
  simp [] >>
  fs [UNION_ASSOC] >>
  disch_then drule >>
  fs [Once c_updated_by]
QED

Theorem evaluate_decs_append_err:
   !env s d s' cenv' err_i1 ds.
    evaluate_decs env s d = (s',cenv',SOME err_i1)
    ⇒
    evaluate_decs env s (d++ds) = (s',cenv',SOME err_i1)
Proof
  induct_on `d` >>
  rw [evaluate_decs_def] >>
  every_case_tac >>
  fs [] >>
  rw [] >>
  metis_tac [PAIR_EQ]
QED

val do_app_add_to_clock = Q.prove (
  `do_app cc s op es = SOME (t, r)
   ==>
   do_app cc (s with clock := s.clock + k) op es =
     SOME (t with clock := t.clock + k, r)`,
  rw [do_app_cases]);

val do_app_add_to_clock_NONE = Q.prove (
  `do_app cc s op es = NONE
   ==>
   do_app cc (s with clock := s.clock + k) op es = NONE`,
  Cases_on `op` \\ rw [do_app_def]
  \\ fs [case_eq_thms, pair_case_eq] \\ rw [] \\ fs []
  \\ rpt (pairarg_tac \\ fs [])
  \\ fs [bool_case_eq, case_eq_thms]);

Theorem evaluate_add_to_clock:
   (∀env (s:'ffi flatSem$state) es s' r.
       evaluate env s es = (s',r) ∧
       r ≠ Rerr (Rabort Rtimeout_error) ⇒
       evaluate env (s with clock := s.clock + extra) es =
         (s' with clock := s'.clock + extra,r)) ∧
   (∀env (s:'ffi flatSem$state) pes v err_v s' r.
       evaluate_match env s pes v err_v = (s',r) ∧
       r ≠ Rerr (Rabort Rtimeout_error) ⇒
       evaluate_match env (s with clock := s.clock + extra) pes v err_v =
         (s' with clock := s'.clock + extra,r))
Proof
  ho_match_mp_tac evaluate_ind \\ rw [evaluate_def]
  \\ fs [case_eq_thms, pair_case_eq] \\ rw [] \\ fs [PULL_EXISTS]
  \\ rw [] \\ fs []
  \\ fs [case_eq_thms, pair_case_eq, bool_case_eq] \\ rw []
  \\ fs [dec_clock_def]
  \\ rw [METIS_PROVE [] ``a \/ b <=> ~a ==> b``]
  \\ map_every imp_res_tac
      [do_app_add_to_clock_NONE,
       do_app_add_to_clock] \\ fs []
  \\ every_case_tac \\ fs []
QED

val evaluate_dec_add_to_clock = Q.prove(
  `∀d env s s' r.
    r ≠ SOME (Rabort Rtimeout_error) ∧
    evaluate_dec env s d = (s',c,r) ⇒
    evaluate_dec env (s with clock := s.clock + extra) d =
      (s' with clock := s'.clock + extra,c,r)`,
  Cases \\ rw [evaluate_dec_def]
  \\ fs [case_eq_thms, pair_case_eq]
  \\ imp_res_tac evaluate_add_to_clock \\ fs []
  \\ rw [] \\ rfs [] >>
  fs []);

Theorem evaluate_decs_add_to_clock:
   ∀decs env s s' c r.
   r ≠ SOME (Rabort Rtimeout_error) ∧
   evaluate_decs env s decs = (s',c,r) ⇒
   evaluate_decs env (s with clock := s.clock + extra) decs =
   (s' with clock := s'.clock + extra,c,r)
Proof
  Induct \\ rw [evaluate_decs_def]
  \\ fs [case_eq_thms, pair_case_eq] \\ rw [] \\ fs [PULL_EXISTS]
  \\ imp_res_tac evaluate_dec_add_to_clock \\ fs []
  \\ metis_tac []
QED

(*
val evaluate_prompt_add_to_clock = Q.prove(
  `∀env s p s' r.
     SND(SND r) ≠ SOME (Rabort Rtimeout_error) ∧
     evaluate_prompt env s p = (s',r) ⇒
     evaluate_prompt env (s with clock := s.clock + extra) p =
       (s' with clock := s'.clock + extra,r)`,
  Cases_on`p` >>
  srw_tac[][evaluate_prompt_def] >>
  full_simp_tac(srw_ss())[LET_THM] >>
  pairarg_tac >> full_simp_tac(srw_ss())[] >> rveq >>
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

Theorem evaluate_prog_add_to_clock:
   ∀prog env s s' r.
   evaluate_prog env s prog = (s',r) ∧
   r ≠ SOME (Rabort Rtimeout_error) ⇒
   evaluate_prog env (s with clock := s.clock + extra) prog =
     (s' with clock := s'.clock + extra,r)
Proof
  srw_tac[][evaluate_prog_def] >> full_simp_tac(srw_ss())[LET_THM] >>
  pairarg_tac >> full_simp_tac(srw_ss())[] >> rveq >>
  imp_res_tac evaluate_prompts_add_to_clock >>
  rev_full_simp_tac(srw_ss())[] >>
  rpt(first_x_assum(qspec_then`extra`mp_tac))>>simp[]
QED
*)

Theorem do_app_io_events_mono:
   do_app cc (s:'ffi flatSem$state) op vs = SOME (t, r) ⇒
   s.ffi.io_events ≼ t.ffi.io_events
Proof
  rw [do_app_def] \\ fs [case_eq_thms, pair_case_eq, bool_case_eq]
  \\ rw [] \\ fs []
  \\ rpt (pairarg_tac \\ fs []) \\ rw []
  \\ fs [semanticPrimitivesTheory.store_assign_def,
         semanticPrimitivesTheory.store_lookup_def,
         ffiTheory.call_FFI_def]
  \\ rw [] \\ every_case_tac \\ fs [] \\ rw []
QED

Theorem evaluate_io_events_mono:
   (∀env (s:'ffi flatSem$state) es.
      s.ffi.io_events ≼ (FST (evaluate env s es)).ffi.io_events) ∧
   (∀env (s:'ffi flatSem$state) pes v err_v.
      s.ffi.io_events ≼ (FST (evaluate_match env s pes v err_v)).ffi.io_events)
Proof
  ho_match_mp_tac evaluate_ind \\ rw [evaluate_def]
  \\ every_case_tac \\ fs [] \\ rfs []
  \\ fs [dec_clock_def]
  \\ imp_res_tac do_app_io_events_mono \\ fs []
  \\ metis_tac [IS_PREFIX_TRANS]
QED

Theorem with_clock_ffi:
   (s with clock := k).ffi = s.ffi
Proof
  EVAL_TAC
QED

Theorem evaluate_add_to_clock_io_events_mono:
   (∀env (s:'ffi flatSem$state) es extra.
       (FST (evaluate env s es)).ffi.io_events ≼
       (FST (evaluate env (s with clock := s.clock + extra) es)).ffi.io_events) ∧
   (∀env (s:'ffi flatSem$state) pes v err_v extra.
       (FST (evaluate_match env s pes v err_v)).ffi.io_events ≼
       (FST (evaluate_match env (s with clock := s.clock + extra) pes v err_v)).ffi.io_events)
Proof
  ho_match_mp_tac evaluate_ind \\ rw [evaluate_def] \\ fs []
  \\ rpt (PURE_FULL_CASE_TAC \\ fs []) \\ rfs []
  \\ map_every imp_res_tac [evaluate_add_to_clock,
                            evaluate_io_events_mono,
                            do_app_add_to_clock_NONE,
                            do_app_add_to_clock]
  \\ fs [dec_clock_def]
  \\ rw [] \\ fs [] \\ rw [] \\ fs []
  \\ metis_tac [IS_PREFIX_TRANS, FST, PAIR,
                evaluate_io_events_mono,
                with_clock_ffi,
                do_app_io_events_mono]
QED

Theorem evaluate_dec_io_events_mono:
   ∀z x y.
     y.ffi.io_events ≼ (FST (evaluate_dec x y z)).ffi.io_events
Proof
  Cases \\ rw [evaluate_dec_def] \\ every_case_tac \\ fs [] \\ rw []
  \\ metis_tac [evaluate_io_events_mono, FST]
QED

Theorem evaluate_dec_add_to_clock_io_events_mono:
   ∀prog env (s:'ffi flatSem$state) extra.
   (FST (evaluate_dec env s prog)).ffi.io_events ≼
   (FST (evaluate_dec env (s with clock := s.clock + extra) prog)).ffi.io_events
Proof
  Cases \\ rw [evaluate_dec_def] \\ fs []
  \\ split_pair_case_tac \\ fs []
  \\ split_pair_case_tac \\ fs []
  \\ qmatch_assum_abbrev_tac `evaluate ee (s with clock := _) pp = _`
  \\ qispl_then
         [`ee`,`s`,`pp`,`extra`] mp_tac
         (CONJUNCT1 evaluate_add_to_clock_io_events_mono)
  \\ rw [] \\ fs []
  \\ every_case_tac \\ fs []
QED

Theorem evaluate_decs_io_events_mono:
   ∀prog env s s' x y. evaluate_decs env s prog = (s',x,y) ⇒
   s.ffi.io_events ≼ s'.ffi.io_events
Proof
  Induct \\ rw [evaluate_decs_def]
  \\ every_case_tac \\ fs [] \\ rw []
  \\ res_tac \\ fs []
  \\ metis_tac [IS_PREFIX_TRANS, FST, evaluate_dec_io_events_mono]
QED

Theorem evaluate_decs_add_to_clock_io_events_mono:
   ∀prog env s extra.
   (FST (evaluate_decs env s prog)).ffi.io_events ≼
   (FST (evaluate_decs env (s with clock := s.clock + extra) prog)).ffi.io_events
Proof
  Induct \\ rw [evaluate_decs_def] \\ every_case_tac \\ fs []
  \\ qmatch_assum_abbrev_tac
         `evaluate_dec ee (ss with clock := extra + _) pp = _`
  \\ qispl_then
         [`pp`,`ee`,`ss`,`extra`] mp_tac
         evaluate_dec_add_to_clock_io_events_mono
  \\ rw [] \\ fs []
  \\ imp_res_tac evaluate_dec_add_to_clock \\ fs []
  \\ imp_res_tac evaluate_decs_io_events_mono \\ fs []
  \\ metis_tac [IS_PREFIX_TRANS, FST]
QED

(*
Theorem evaluate_prompt_io_events_mono:
   ∀x y z. evaluate_prompt x y z = (a,b) ⇒
     y.ffi.io_events ≼ a.ffi.io_events ∧
     (IS_SOME y.ffi.final_event ⇒ a.ffi = y.ffi)
Proof
   Cases_on`z`>>srw_tac[][evaluate_prompt_def] >>
   every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
   full_simp_tac(srw_ss())[LET_THM] >> pairarg_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
   imp_res_tac evaluate_decs_io_events_mono
QED

Theorem evaluate_prompt_add_to_clock_io_events_mono:
   ∀env s prog extra.
   (FST (evaluate_prompt env s prog)).ffi.io_events ≼
   (FST (evaluate_prompt env (s with clock := s.clock + extra) prog)).ffi.io_events ∧
   (IS_SOME ((FST (evaluate_prompt env s prog)).ffi.final_event) ⇒
     (FST (evaluate_prompt env (s with clock := s.clock + extra) prog)).ffi =
     (FST (evaluate_prompt env s prog)).ffi)
Proof
  Cases_on`prog`>>srw_tac[][evaluate_prompt_def]>>
  every_case_tac >> full_simp_tac(srw_ss())[LET_THM] >>
  TRY pairarg_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
  qmatch_assum_abbrev_tac`evaluate_decs ee (ss with clock := _ + extra) pp = _` >>
  qispl_then[`ee`,`ss`,`pp`,`extra`]mp_tac evaluate_decs_add_to_clock_io_events_mono >>
  simp[]
QED

Theorem evaluate_prompts_io_events_mono:
   ∀prog env s s' x y. evaluate_prompts env s prog = (s',x,y) ⇒
   s.ffi.io_events ≼ s'.ffi.io_events ∧
   (IS_SOME s.ffi.final_event ⇒ s'.ffi = s.ffi)
Proof
  Induct >> srw_tac[][evaluate_prompts_def] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
  imp_res_tac evaluate_prompt_io_events_mono >>
  res_tac >> full_simp_tac(srw_ss())[] >>
  metis_tac[IS_PREFIX_TRANS]
QED

Theorem evaluate_prompts_add_to_clock_io_events_mono:
   ∀env s prog extra.
   (FST (evaluate_prompts env s prog)).ffi.io_events ≼
   (FST (evaluate_prompts env (s with clock := s.clock + extra) prog)).ffi.io_events ∧
   (IS_SOME ((FST (evaluate_prompts env s prog)).ffi.final_event) ⇒
     (FST (evaluate_prompts env (s with clock := s.clock + extra) prog)).ffi =
     (FST (evaluate_prompts env s prog)).ffi)
Proof
  Induct_on`prog` >> srw_tac[][evaluate_prompts_def] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >>
  qmatch_assum_abbrev_tac`evaluate_prompt ee (ss with clock := _ + extra) pp = _` >>
  qispl_then[`ee`,`ss`,`pp`,`extra`]mp_tac evaluate_prompt_add_to_clock_io_events_mono >>
  simp[] >> srw_tac[][] >>
  imp_res_tac evaluate_prompt_add_to_clock >> full_simp_tac(srw_ss())[] >>
  imp_res_tac evaluate_prompts_io_events_mono >> full_simp_tac(srw_ss())[] >>
  rveq >|[qhdtm_x_assum`evaluate_prompts`mp_tac,ALL_TAC,ALL_TAC]>>
  qmatch_assum_abbrev_tac`evaluate_prompts eee sss prog = _` >>
  last_x_assum(qspecl_then[`eee`,`sss`,`extra`]mp_tac)>>simp[Abbr`sss`]>>
  fsrw_tac[ARITH_ss][] >> srw_tac[][] >> full_simp_tac(srw_ss())[] >>
  metis_tac[IS_PREFIX_TRANS,FST]
QED

Theorem evaluate_prog_add_to_clock_io_events_mono:
   ∀env s prog extra.
   (FST (evaluate_prog env s prog)).ffi.io_events ≼
   (FST (evaluate_prog env (s with clock := s.clock + extra) prog)).ffi.io_events ∧
   (IS_SOME ((FST (evaluate_prog env s prog)).ffi.final_event) ⇒
     (FST (evaluate_prog env (s with clock := s.clock + extra) prog)).ffi =
     (FST (evaluate_prog env s prog)).ffi)
Proof
  srw_tac[][evaluate_prog_def] >> full_simp_tac(srw_ss())[LET_THM] >>
  metis_tac[evaluate_prompts_add_to_clock_io_events_mono,FST]
QED
  *)

val bind_locals_list_def = Define`
  bind_locals_list ts ks = list$MAP2 (λt x. (flatLang$Var_local t x)) ts ks`;


Theorem evaluate_vars:
   !env s kvs env' ks vs ts.
    ALL_DISTINCT (MAP FST kvs) ∧
    DISJOINT (set (MAP FST kvs)) (set (MAP FST env')) ∧
    env.v = env' ++ kvs ∧ ks = MAP FST kvs ∧ vs = MAP SND kvs ∧
    LENGTH ts = LENGTH ks
    ⇒
    evaluate env s (bind_locals_list ts ks) = (s,Rval vs)
Proof
  induct_on `kvs` >> fs[bind_locals_list_def]>>
  srw_tac[][evaluate_def] >>
  Cases_on`ts`>>fs[]>>
  srw_tac[][Once evaluate_cons,evaluate_def] >>
  PairCases_on`h`>>srw_tac[][]>> full_simp_tac(srw_ss())[] >>
  srw_tac[][ALOOKUP_APPEND] >>
  reverse BasicProvers.CASE_TAC >>
  imp_res_tac ALOOKUP_MEM >- metis_tac[MEM_MAP,FST] >>
  first_x_assum(qspecl_then[`env`,`s`]mp_tac) >>
  full_simp_tac(srw_ss())[DISJOINT_SYM]
QED

  (*
Theorem with_same_v[simp]:
   env with v := env.v = env
Proof
  srw_tac[][environment_component_equality]
QED
  *)

Theorem pmatch_evaluate_vars:
   (!env refs p v evs env' ts.
    refs = s.refs ∧
    flatSem$pmatch env s.refs p v evs = Match env' ∧
    ALL_DISTINCT (pat_bindings p (MAP FST evs)) ∧
    LENGTH ts = LENGTH (pat_bindings p (MAP FST evs))
    ⇒
    flatSem$evaluate (env with v := env') s (bind_locals_list ts (pat_bindings p (MAP FST evs))) = (s,Rval (MAP SND env'))) ∧
   (!env refs ps vs evs env' ts.
    refs = s.refs ∧
    flatSem$pmatch_list env s.refs ps vs evs = Match env' ∧
    ALL_DISTINCT (pats_bindings ps (MAP FST evs)) ∧
    LENGTH ts = LENGTH (pats_bindings ps (MAP FST evs))
    ⇒
    flatSem$evaluate (env with v := env') s (bind_locals_list ts (pats_bindings ps (MAP FST evs))) = (s,Rval (MAP SND env')))
Proof
  ho_match_mp_tac pmatch_ind >>
  srw_tac[][pat_bindings_def, pmatch_def]
  >- (
    match_mp_tac evaluate_vars >> srw_tac[][] >>
    qexists_tac`(x,v)::evs` >> srw_tac[][] )
  >- (
    match_mp_tac evaluate_vars >> srw_tac[][] >>
    first_assum(match_exists_tac o concl) >> simp[] )
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
    match_mp_tac evaluate_vars >> srw_tac[][] >>
    first_assum(match_exists_tac o concl) >> simp[] )
  >- (
    every_case_tac >> full_simp_tac(srw_ss())[] >>
    `ALL_DISTINCT (pat_bindings p (MAP FST evs))`
            by metis_tac[pat_bindings_accum, ALL_DISTINCT_APPEND] >>
    `pat_bindings p (MAP FST evs) = MAP FST a`
                 by (imp_res_tac pmatch_extend >>
                     srw_tac[][] >>
                     metis_tac [pat_bindings_accum]) >>
    fsrw_tac[QUANT_INST_ss[record_default_qp]][] >>
    rev_full_simp_tac(srw_ss())[])
QED

Theorem pmatch_evaluate_vars_lem:
   ∀p v bindings env s ts.
    pmatch env s.refs p v [] = Match bindings ∧
    ALL_DISTINCT (pat_bindings p []) ∧
    LENGTH ts = LENGTH (pat_bindings p [])
    ⇒
    evaluate (env with v := bindings) s (bind_locals_list ts (pat_bindings p [])) = (s,Rval (MAP SND bindings))
Proof
  rw [] >>
  imp_res_tac pmatch_evaluate_vars >>
  fs []
QED



      (*
Theorem evaluate_append:
   ∀env s s1 s2 e1 e2 v1 v2.
   evaluate env s e1 = (s1, Rval v1) ∧
   evaluate env s1 e2 = (s2, Rval v2) ⇒
   evaluate env s (e1++e2) = (s2, Rval (v1++v2))
Proof
  Induct_on`e1`>>srw_tac[][evaluate_def] >>
  full_simp_tac(srw_ss())[Once evaluate_cons] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
  res_tac >> full_simp_tac(srw_ss())[]
QED

Theorem evaluate_vars_reverse:
   !env s es s' vs.
    evaluate env s (MAP (Var_local tra) es) = (s, Rval vs)
    ⇒
    evaluate env s (MAP (Var_local tra) (REVERSE es)) = (s, Rval (REVERSE vs))
Proof
  induct_on `es` >> srw_tac[][evaluate_def] >> srw_tac[][] >>
  pop_assum mp_tac >>
  srw_tac[][Once evaluate_cons] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
  full_simp_tac(srw_ss())[evaluate_def] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
  match_mp_tac evaluate_append >>
  srw_tac[][evaluate_def]
QED

val tids_of_decs_def = Define`
  tids_of_decs ds = set (FLAT (MAP (λd. case d of Dtype mn tds => MAP (mk_id mn o FST o SND) tds | _ => []) ds))`;

Theorem tids_of_decs_thm:
   (tids_of_decs [] = {}) ∧
   (tids_of_decs (d::ds) = tids_of_decs ds ∪
     case d of Dtype mn tds => set (MAP (mk_id mn o FST o SND) tds) | _ => {})
Proof
  simp[tids_of_decs_def] >>
  every_case_tac >> simp[] >>
  metis_tac[UNION_COMM]
QED

Theorem dec_clock_const[simp]:
   (dec_clock s).defined_types = s.defined_types ∧
   (dec_clock s).defined_mods = s.defined_mods
Proof
   EVAL_TAC
QED
   *)

   (*
Theorem evaluate_state_const:
   (∀env (s:'ffi flatSem$state) ls s' vs.
      flatSem$evaluate env s ls = (s',vs) ⇒
      s'.next_type_id = s.next_type_id ∧
      s'.next_exn_id = s.next_exn_id) ∧
   (∀env (s:'ffi flatSem$state) v pes ev s' vs.
      evaluate_match env s v pes ev = (s', vs) ⇒
      s'.next_type_id = s.next_type_id ∧
      s'.next_exn_id = s.next_exn_id)
Proof
  ho_match_mp_tac evaluate_ind >>
  srw_tac[][evaluate_def] >> srw_tac[][] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >> imp_res_tac do_app_const >>
  srw_tac[][dec_clock_def] >> metis_tac []
QED
  *)

  (*
Theorem evaluate_dec_state_const:
   ∀env st d res. evaluate_dec env st d = res ⇒
   (FST res).defined_mods = st.defined_mods
Proof
  Cases_on`d`>>srw_tac[][evaluate_dec_def] >> srw_tac[][] >>
  BasicProvers.CASE_TAC >> full_simp_tac(srw_ss())[] >>
  imp_res_tac evaluate_state_const >>
  every_case_tac >> full_simp_tac(srw_ss())[]
QED

Theorem evaluate_decs_state_const:
   ∀env st ds res. evaluate_decs env st ds = res ⇒
    (FST res).defined_mods = st.defined_mods
Proof
  Induct_on`ds`>>srw_tac[][evaluate_decs_def] >> srw_tac[][] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >>
  imp_res_tac evaluate_dec_state_const >> full_simp_tac(srw_ss())[] >>
  `∀x f.(x with globals updated_by f).defined_mods = x.defined_mods` by simp[] >>
  metis_tac[FST]
QED

Theorem evaluate_dec_tids_acc:
   ∀env st d res. evaluate_dec env st d = res ⇒
      st.defined_types ⊆ (FST res).defined_types
Proof
  Cases_on`d`>>srw_tac[][evaluate_dec_def] >> srw_tac[][] >>
  BasicProvers.CASE_TAC >>
  imp_res_tac evaluate_state_const >>
  every_case_tac >> srw_tac[][]
QED

Theorem evaluate_decs_tids_acc:
   ∀env st ds res. evaluate_decs env st ds = res ⇒
      st.defined_types ⊆ (FST res).defined_types
Proof
  Induct_on`ds`>>srw_tac[][evaluate_decs_def]>>srw_tac[][]>>
  every_case_tac >> full_simp_tac(srw_ss())[]>>
  imp_res_tac evaluate_dec_tids_acc >> full_simp_tac(srw_ss())[] >>
  `∀x f.(x with globals updated_by f).defined_types = x.defined_types` by simp[] >>
  metis_tac[FST,SUBSET_TRANS]
QED

Theorem evaluate_decs_tids:
   ∀env st ds res. evaluate_decs env st ds = res ⇒
     SND(SND(SND res)) = NONE ⇒
     {id | TypeId id ∈ (FST res).defined_types} = (tids_of_decs ds) ∪ {id | TypeId id ∈ st.defined_types}
Proof
  Induct_on`ds`>>srw_tac[][evaluate_decs_def]>>full_simp_tac(srw_ss())[tids_of_decs_thm]>>
  every_case_tac>>full_simp_tac(srw_ss())[evaluate_dec_def,LET_THM]>>srw_tac[][]>>
  every_case_tac>>full_simp_tac(srw_ss())[]>>srw_tac[][]>>
  full_simp_tac(srw_ss())[EXTENSION,semanticPrimitivesTheory.type_defs_to_new_tdecs_def,MEM_MAP,PULL_EXISTS,UNCURRY] >>
  qmatch_assum_abbrev_tac`evaluate_decs env' st' _ = _` >>
  last_x_assum(qspecl_then[`env'`,`st'`]mp_tac)>>srw_tac[][]>>
  unabbrev_all_tac >> full_simp_tac(srw_ss())[]>>
  full_simp_tac(srw_ss())[EXTENSION,semanticPrimitivesTheory.type_defs_to_new_tdecs_def,MEM_MAP,PULL_EXISTS,UNCURRY] >>
  metis_tac[evaluate_state_const]
QED

Theorem evaluate_decs_tids_disjoint:
   ∀env st ds res. evaluate_decs env st ds = res ⇒
     SND(SND(SND res)) = NONE ⇒
     DISJOINT (IMAGE TypeId (tids_of_decs ds)) st.defined_types
Proof
  Induct_on`ds`>>srw_tac[][evaluate_decs_def]>>full_simp_tac(srw_ss())[tids_of_decs_thm]>>
  every_case_tac >> full_simp_tac(srw_ss())[evaluate_dec_def,LET_THM] >> srw_tac[][] >>
  every_case_tac>>full_simp_tac(srw_ss())[]>>srw_tac[][]>>
  qmatch_assum_abbrev_tac`evaluate_decs env' st' _ = _` >>
  last_x_assum(qspecl_then[`env'`,`st'`]mp_tac)>>srw_tac[][]>>
  unabbrev_all_tac >> full_simp_tac(srw_ss())[]>>
  full_simp_tac(srw_ss())[semanticPrimitivesTheory.type_defs_to_new_tdecs_def,IN_DISJOINT,MEM_MAP,UNCURRY] >>
  metis_tac[evaluate_state_const]
QED

val tids_of_prompt_def = Define`
  tids_of_prompt (Prompt _ ds) = tids_of_decs ds`;

val evaluate_prompt_tids_disjoint = Q.prove(
  `∀env s p res. evaluate_prompt env s p = res ⇒
      SND(SND(SND res)) = NONE ⇒
      DISJOINT (IMAGE TypeId (tids_of_prompt p)) s.defined_types`,
  Cases_on`p`>>srw_tac[][evaluate_prompt_def]>>full_simp_tac(srw_ss())[tids_of_prompt_def]>>
  full_simp_tac(srw_ss())[LET_THM,UNCURRY] >> metis_tac[evaluate_decs_tids_disjoint]);

val evaluate_prompt_tids_acc = Q.prove(
  `∀env s p res. evaluate_prompt env s p = res ⇒
      s.defined_types ⊆ (FST res).defined_types`,
  Cases_on`p`>>srw_tac[][evaluate_prompt_def]>>full_simp_tac(srw_ss())[]>>
  metis_tac[evaluate_decs_tids_acc,FST]);

Theorem evaluate_prompt_tids:
   ∀env s p res. evaluate_prompt env s p = res ⇒
     SND(SND(SND res)) = NONE ⇒
     {id | TypeId id ∈ (FST res).defined_types} = (tids_of_prompt p) ∪ {id | TypeId id ∈ s.defined_types}
Proof
  Cases_on`p`>>srw_tac[][evaluate_prompt_def]>>full_simp_tac(srw_ss())[tids_of_prompt_def]>> full_simp_tac(srw_ss())[LET_THM,UNCURRY] >>
  metis_tac[evaluate_decs_tids]
QED

  (*
Theorem evaluate_prompt_mods_disjoint:
   ∀env s p res. evaluate_prompt env s p = res ⇒
     SND(SND(SND res)) = NONE ⇒
     ∀mn ds. p = Prompt (SOME mn) ds ⇒ mn ∉ s.defined_mods
Proof
  Cases_on`p`>>srw_tac[][evaluate_prompt_def]>>full_simp_tac(srw_ss())[]
QED
  *)
  *)

  (*
val s = ``s:'ffi flatSem$state``;

Theorem evaluate_globals:
   (∀env ^s es s' r. evaluate env s es = (s',r) ⇒ s'.globals = s.globals) ∧
   (∀env ^s pes v err_v s' r. evaluate_match env s pes v err_v = (s',r) ⇒
      s'.globals = s.globals)
Proof
  ho_match_mp_tac evaluate_ind >>
  srw_tac[][evaluate_def] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >> full_simp_tac(srw_ss())[] >> rev_full_simp_tac(srw_ss())[] >> full_simp_tac(srw_ss())[dec_clock_def]
QED


Theorem evaluate_dec_globals:
   ∀env st d res. evaluate_dec env st d = res ⇒
   (FST res).globals = st.globals
Proof
  Cases_on`d`>>srw_tac[][evaluate_dec_def] >> srw_tac[][] >>
  BasicProvers.CASE_TAC >> full_simp_tac(srw_ss())[] >>
  imp_res_tac evaluate_globals >>
  every_case_tac >> full_simp_tac(srw_ss())[]
QED

Theorem evaluate_decs_globals:
   ∀decs env st res. evaluate_decs env st decs = res ⇒
      (FST res).globals = st.globals ++ MAP SOME (FST(SND(SND res)))
Proof
  Induct \\ rw[evaluate_decs_def] \\ rw[]
  \\ BasicProvers.TOP_CASE_TAC
  \\ imp_res_tac evaluate_dec_globals
  \\ reverse BasicProvers.TOP_CASE_TAC >- fs[]
  \\ BasicProvers.TOP_CASE_TAC
  \\ BasicProvers.TOP_CASE_TAC
  \\ res_tac
  \\ BasicProvers.TOP_CASE_TAC \\ fs[]
  \\ BasicProvers.TOP_CASE_TAC \\ fs[]
QED
  *)

val evaluate_decs_add_to_clock_initial_state = Q.prove(
  `r ≠ SOME (Rabort Rtimeout_error) ∧
   evaluate_decs env (initial_state ffi k) decs = (s',c,r) ⇒
   evaluate_decs env (initial_state ffi (ck + k)) decs =
   (s' with clock := s'.clock + ck,c,r)`,
  rw [initial_state_def]
  \\ imp_res_tac evaluate_decs_add_to_clock \\ fs []);

val evaluate_decs_add_to_clock_initial_state_io_events_mono = Q.prove (
  `evaluate_decs env (initial_state ffi k) prog = (s',c,r) ==>
   s'.ffi.io_events ≼
   (FST (evaluate_decs env (initial_state ffi (k+ck)) prog)).ffi.io_events`,
  rw [initial_state_def]
  \\ qmatch_assum_abbrev_tac `evaluate_decs _ s1 _ = _`
  \\ qispl_then
         [`prog`,`env`,`s1`,`ck`] mp_tac
         (GEN_ALL evaluate_decs_add_to_clock_io_events_mono)
  \\ fs [Abbr`s1`]);

val initial_state_with_clock = Q.prove (
  `(initial_state ffi k with clock := (initial_state ffi k).clock + ck) =
   initial_state ffi (k + ck)`,
  rw [initial_state_def]);

val SND_SND_lemma = prove(
  ``SND (SND x) = y <=> ?y1 y2. x = (y1, y2, y)``,
  PairCases_on `x` \\ fs []);

val eval_sim_def = Define `
  eval_sim ffi exh1 ctor1 ds1 exh2 ctor2 ds2 rel allow_fail =
    !k res1 s2 c1.
      evaluate_decs (initial_env exh1 ctor1) (initial_state ffi k) ds1 =
        (s2, c1, res1) /\
      (allow_fail \/ res1 <> SOME (Rabort Rtype_error)) /\
      rel ds1 ds2
      ==>
      ?ck res2 t2 c2.
        evaluate_decs (initial_env exh2 ctor2) (initial_state ffi (k + ck)) ds2 =
          (t2, c2, res2) /\
        s2.ffi = t2.ffi /\
        (res1 = NONE ==> res2 = NONE) /\
        (!v. res1 = SOME (Rraise v) ==> ?v1. res2 = SOME (Rraise v1)) /\
        (!a. res1 = SOME (Rabort a) ==> res2 = SOME (Rabort a))`;

Theorem IMP_semantics_eq:
   eval_sim ffi exh1 ctor1 ds1 exh2 ctor2 ds2 rel F /\
   semantics exh1 ctor1 (ffi:'ffi ffi_state) ds1 <> Fail ==>
   rel ds1 ds2 ==>
   semantics exh1 ctor1 ffi ds1 =
   semantics exh2 ctor2 ffi ds2
Proof
  rewrite_tac [GSYM AND_IMP_INTRO]
  \\ strip_tac
  \\ simp [Once semantics_def]
  \\ IF_CASES_TAC \\ fs [SND_SND_lemma] \\ disch_then kall_tac
  \\ strip_tac
  \\ simp [Once semantics_def]
  \\ IF_CASES_TAC \\ fs [SND_SND_lemma]
  >-
   (simp [semantics_def]
    \\ IF_CASES_TAC \\ fs [SND_SND_lemma]
    \\ DEEP_INTRO_TAC some_intro \\ fs [] \\ rw []
    \\ fs [eval_sim_def]
    \\ Cases_on
         `evaluate_decs (initial_env exh1 ctor1) (initial_state ffi k') ds1`
    \\ rename1 `(q,rr)` \\ PairCases_on `rr`
    \\ `rr1 <> SOME (Rabort Rtype_error)` by metis_tac []
    \\ last_x_assum drule \\ strip_tac \\ rfs [])
  \\ DEEP_INTRO_TAC some_intro \\ fs [] \\ rw []
  >- (
    simp[semantics_def, SND_SND_lemma]
    \\ IF_CASES_TAC \\ fs[]
    >- (
      fs[eval_sim_def]
      \\ first_x_assum drule
      \\ impl_tac >- (strip_tac \\ fs[])
      \\ strip_tac
      \\ imp_res_tac evaluate_decs_add_to_clock_initial_state
      \\ fs[]
      \\ first_x_assum(qspec_then`ck+k`mp_tac)
      \\ simp[]
      \\ Cases_on`res2` \\ Cases_on`r` \\ fs[]
      \\ TRY(rpt(first_x_assum(qspec_then`k'`mp_tac)) \\ simp[] \\ NO_TAC)
      \\ every_case_tac \\ fs[] \\ rveq \\ fs[]
      \\ TRY(rpt(first_x_assum(qspec_then`k'`mp_tac)) \\ simp[] \\ NO_TAC))
    \\ DEEP_INTRO_TAC some_intro \\ fs []
    \\ conj_tac
    >- (
      rw[]
      \\ fs[eval_sim_def]
      \\ first_x_assum drule
      \\ impl_tac >- (strip_tac \\ fs[])
      \\ strip_tac
      \\ imp_res_tac evaluate_decs_add_to_clock_initial_state
      \\ fs[]
      \\ first_x_assum(fn th => mp_tac th \\ impl_tac >- (strip_tac \\ fs[]) \\ strip_tac)
      \\ first_x_assum(fn th => mp_tac th \\ impl_tac >- (strip_tac \\ fs[]) \\ strip_tac)
      \\ first_x_assum(fn th => mp_tac th \\ impl_tac >- (every_case_tac \\ fs[]) \\ strip_tac)
      \\ first_x_assum(qspec_then`k'`mp_tac) \\ fs[]
      \\ first_x_assum(qspec_then`ck+k`mp_tac) \\ fs[]
      \\ ntac 2 strip_tac
      \\ rveq \\ fs[state_component_equality]
      \\ every_case_tac \\ fs[])
    \\ fs[eval_sim_def]
    \\ first_x_assum drule
    \\ impl_tac >- (strip_tac \\ fs[])
    \\ strip_tac
    \\ asm_exists_tac \\ fs[]
    \\ every_case_tac \\ fs[] )
  \\ simp [Once semantics_def]
  \\ IF_CASES_TAC \\ fs [SND_SND_lemma]
  >-
   (Cases_on `evaluate_decs (initial_env exh1 ctor1) (initial_state ffi k) ds1`
    \\ rename1 `(q,rr)` \\ PairCases_on `rr`
    \\ first_x_assum (qspec_then `k` mp_tac)
    \\ disch_then (qspecl_then [`q`,`rr1`] mp_tac)
    \\ disch_then (qspec_then `rr0` mp_tac o CONV_RULE SWAP_FORALL_CONV)
    \\ strip_tac \\ rfs []
    \\ fs [eval_sim_def]
    \\ last_x_assum drule
    \\ impl_keep_tac >- metis_tac []
    \\ strip_tac \\ fs []
    \\ imp_res_tac evaluate_decs_add_to_clock_initial_state \\ fs []
    \\ rveq \\ fs []
    \\ Cases_on `rr1` \\ fs [] \\ rveq
    \\ Cases_on `x` \\ fs [])
  \\ DEEP_INTRO_TAC some_intro
  \\ fs [] \\ rw []
  >-
   (Cases_on `evaluate_decs (initial_env exh1 ctor1) (initial_state ffi k) ds1`
    \\ rename1 `(q, rr)` \\ PairCases_on `rr`
    \\ last_x_assum (qspecl_then [`k`, `q`, `rr1`] mp_tac)
    \\ disch_then (qspec_then `rr0` mp_tac o CONV_RULE SWAP_FORALL_CONV)
    \\ strip_tac \\ rfs []
    \\ fs [eval_sim_def]
    \\ last_x_assum drule
    \\ impl_keep_tac >- metis_tac []
    \\ strip_tac \\ fs []
    \\ imp_res_tac evaluate_decs_add_to_clock_initial_state \\ fs []
    \\ imp_res_tac evaluate_decs_add_to_clock_initial_state_io_events_mono
    \\ fs [] \\ rveq
    \\ every_case_tac \\ fs [] \\ rw []  \\ fs []
    \\ first_x_assum (qspec_then `ck` mp_tac)
    \\ strip_tac \\ fs [] \\ rfs [])
  \\ qmatch_abbrev_tac `build_lprefix_lub l1 = build_lprefix_lub l2`
  \\ `(lprefix_chain l1 /\ lprefix_chain l2) /\ equiv_lprefix_chain l1 l2`
     suffices_by metis_tac [build_lprefix_lub_thm,
                            lprefix_lub_new_chain,
                            unique_lprefix_lub]
  \\ conj_asm1_tac
  >-
   (unabbrev_all_tac
    \\ conj_tac
    \\ Ho_Rewrite.ONCE_REWRITE_TAC [GSYM o_DEF]
    \\ rewrite_tac [IMAGE_COMPOSE]
    \\ match_mp_tac prefix_chain_lprefix_chain
    \\ simp [prefix_chain_def, PULL_EXISTS]
    \\ qx_genl_tac [`k1`,`k2`]
    \\ qspecl_then [`k1`,`k2`] mp_tac LESS_EQ_CASES
    \\ strip_tac \\ fs [LESS_EQ_EXISTS] \\ rveq
    \\ metis_tac [evaluate_decs_add_to_clock_io_events_mono,
                  initial_state_with_clock])
  \\ simp [equiv_lprefix_chain_thm]
  \\ unabbrev_all_tac \\ simp [PULL_EXISTS]
  \\ simp [LNTH_fromList, PULL_EXISTS, GSYM FORALL_AND_THM]
  \\ rpt gen_tac
  \\ Cases_on `evaluate_decs (initial_env exh1 ctor1) (initial_state ffi k) ds1`
  \\ rename1 `(q,rr)` \\ PairCases_on `rr`
  \\ fs [eval_sim_def]
  \\ first_x_assum drule
  \\ impl_keep_tac >- metis_tac []
  \\ strip_tac \\ fs []
  \\ conj_tac \\ rw []
  >- (qexists_tac `ck+k` \\ fs [])
  \\ qexists_tac `k` \\ fs []
  \\ qmatch_assum_abbrev_tac `_ < LENGTH (_ ffi1)`
  \\ `ffi1.io_events ≼ t2.ffi.io_events`
     suffices_by (rw [] \\ fs [IS_PREFIX_APPEND] \\ simp [EL_APPEND1])
  \\ qunabbrev_tac `ffi1`
  \\ metis_tac
        [evaluate_decs_add_to_clock_io_events_mono,
         initial_state_with_clock, FST, ADD_SYM]
QED

val op_gbag_def = Define `
  op_gbag (GlobalVarInit n) = BAG_INSERT n {||} /\
  op_gbag _ = {||}`;

val set_globals_def = tDefine "set_globals" `
  (set_globals (Raise t e) = set_globals e) /\
  (set_globals (Handle t e pes) = set_globals e ⊎ elist_globals (MAP SND pes)) /\
  (set_globals (Con t id es) = elist_globals es) /\
  (set_globals (Fun t v e) = set_globals e) /\
  (set_globals (App t op es) = elist_globals es ⊎ op_gbag op) /\
  (set_globals (If t e1 e2 e3) =
    set_globals e1 ⊎ set_globals e2 ⊎ set_globals e3) /\
  (set_globals (Mat t e pes) = set_globals e ⊎ elist_globals (MAP SND pes)) /\
  (set_globals (Let t v e1 e2) = set_globals e1 ⊎ set_globals e2) /\
  (set_globals (Letrec t fs e) =
    set_globals e ⊎ elist_globals (MAP (SND o SND) fs)) /\
  (set_globals _ = {||}) /\
  (elist_globals [] = {||}) /\
  (elist_globals (e::es) = set_globals e ⊎ elist_globals es)`
 (WF_REL_TAC
     `measure (\a. case a of INL e => exp_size e | INR es => exp6_size es)`
   \\ rw [flatLangTheory.exp_size_def]
   \\ fs [GSYM o_DEF]
   >-
    (`exp6_size (MAP (SND o SND) fs) < exp1_size fs + 1` suffices_by rw []
     \\ fs [flatLangTheory.exp_size_MAP])
   \\ `exp6_size (MAP SND pes) < exp3_size pes + 1` suffices_by rw []
   \\ fs [flatLangTheory.exp_size_MAP]);

val _ = export_rewrites ["set_globals_def"];

val esgc_free_def = tDefine "esgc_free" `
  (esgc_free (Raise t e) <=> esgc_free e) /\
  (esgc_free (Handle t e pes) <=>
    esgc_free e /\ EVERY esgc_free (MAP SND pes)) /\
  (esgc_free (Con t id es) <=> EVERY esgc_free es) /\
  (esgc_free (Fun t v e) <=> set_globals e = {||}) /\
  (esgc_free (App t op es) <=> EVERY esgc_free es) /\
  (esgc_free (If t e1 e2 e3) <=>
    esgc_free e1 /\ esgc_free e2 /\ esgc_free e3) /\
  (esgc_free (Mat t e pes) <=> esgc_free e /\ EVERY esgc_free (MAP SND pes)) /\
  (esgc_free (Let t v e1 e2) <=> esgc_free e1 /\ esgc_free e2) /\
  (esgc_free (Letrec t fs e) <=>
    esgc_free e /\ elist_globals (MAP (SND o SND) fs) = {||}) /\
  (esgc_free _ <=> T)`
 (WF_REL_TAC `measure exp_size`
  \\ rw []
  \\ fs [MEM_MAP] \\ rw []
  \\ imp_res_tac flatLangTheory.exp_size_MEM \\ fs [])

val esgc_free_def = save_thm("esgc_free_def[simp,compute]",
  SIMP_RULE (bool_ss ++ ETA_ss) [] esgc_free_def)

Theorem elist_globals_eq_empty:
   elist_globals l = {||} ⇔ ∀e. MEM e l ⇒ set_globals e = {||}
Proof
  Induct_on`l` \\ rw[set_globals_def] \\ rw[EQ_IMP_THM] \\ rw[]
QED

Theorem elist_globals_append:
   elist_globals (xs ++ ys) = elist_globals xs ⊎ elist_globals ys
Proof
 Induct_on `xs` \\ rw [BAG_UNION, FUN_EQ_THM, EMPTY_BAG]
QED

Theorem elist_globals_FOLDR:
   elist_globals es = FOLDR BAG_UNION {||} (MAP set_globals es)
Proof
  Induct_on `es` >> simp[]
QED

val is_Dlet_def = Define `
  (is_Dlet (Dlet _) <=> T) /\
  (is_Dlet _ <=> F)`;

val dest_Dlet_def = Define `dest_Dlet (Dlet e) = e`;

val _ = export_rewrites ["is_Dlet_def", "dest_Dlet_def"];

val _ = export_theory()
