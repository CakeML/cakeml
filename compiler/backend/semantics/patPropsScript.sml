(*
  Properties about patLang and its semantics
*)
open preamble patSemTheory

val _ = new_theory"patProps"

val evaluate_lit = save_thm("evaluate_lit[simp]",
      EVAL``patSem$evaluate env s [Lit tra l]``)

Theorem Boolv_11[simp]:
  patSem$Boolv b1 = Boolv b2 ⇔ b1 = b2
Proof
EVAL_TAC>>srw_tac[][]
QED

val Boolv_disjoint = save_thm("Boolv_disjoint",EVAL``patSem$Boolv T = Boolv F``);

val evaluate_Con_nil =
  ``evaluate env s [Con tra x []]``
  |> EVAL
  |> curry save_thm"evaluate_Con_nil";

val no_closures_def = tDefine"no_closures"`
  (no_closures (Litv _) ⇔ T) ∧
  (no_closures (Conv _ vs) ⇔ EVERY no_closures vs) ∧
  (no_closures (Closure _ _) = F) ∧
  (no_closures (Recclosure _ _ _) = F) ∧
  (no_closures (Loc _) = T) ∧
  (no_closures (Vectorv vs) ⇔ EVERY no_closures vs)`
(WF_REL_TAC`measure v_size`>>CONJ_TAC >|[all_tac,gen_tac]>>Induct>>
 simp[v_size_def]>>srw_tac[][]>>res_tac>>simp[])
val _ = export_rewrites["no_closures_def"];

Theorem no_closures_Boolv[simp]:
   no_closures (Boolv b)
Proof
  EVAL_TAC
QED

Theorem evaluate_raise_rval:
   ∀env s e s' v. patSem$evaluate env s [Raise tra e] ≠ (s', Rval v)
Proof
  EVAL_TAC >> srw_tac[][] >> every_case_tac >> simp[]
QED
val _ = export_rewrites["evaluate_raise_rval"]

Theorem evaluate_length:
   ∀env s ls s' vs.
      evaluate env s ls = (s',Rval vs) ⇒ LENGTH vs = LENGTH ls
Proof
  ho_match_mp_tac evaluate_ind >> rw[evaluate_def]
  \\ fs[case_eq_thms,pair_case_eq,bool_case_eq] \\ rw[] \\ fs[]
  \\ TRY(qpat_x_assum`(_,_) = _`(assume_tac o SYM)) \\ fs[]
  \\ rename1`list_result lr`
  \\ Cases_on`lr` \\ fs[] \\ rw[]
QED

Theorem evaluate_cons:
   evaluate env s (e::es) =
   (case evaluate env s [e] of
    | (s,Rval v) =>
      (case evaluate env s es of
       | (s,Rval vs) => (s,Rval (v++vs))
       | r => r)
    | r => r)
Proof
  Cases_on`es`>>srw_tac[][evaluate_def] >>
  every_case_tac >> full_simp_tac(srw_ss())[evaluate_def] >>
  imp_res_tac evaluate_length >> full_simp_tac(srw_ss())[SING_HD]
QED

Theorem evaluate_sing:
   evaluate env s [e] = (s',Rval vs) ⇒ ∃y. vs = [y]
Proof
  srw_tac[][] >> imp_res_tac evaluate_length >> full_simp_tac(srw_ss())[] >> metis_tac[SING_HD]
QED

Theorem evaluate_append_Rval:
   ∀l1 env s l2 s' vs.
    evaluate env s (l1 ++ l2) = (s',Rval vs) ⇒
    ∃s1 v1 v2. evaluate env s l1 = (s1,Rval v1) ∧
               evaluate env s1 l2 = (s',Rval v2) ∧
               vs = v1++v2
Proof
  Induct >> simp[evaluate_def,Once evaluate_cons] >>
  srw_tac[][] >> simp[Once evaluate_cons] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >> res_tac >>
  srw_tac[][] >> full_simp_tac(srw_ss())[] >> srw_tac[][]
QED

Theorem evaluate_append_Rval_iff:
   ∀l1 env s l2 s' vs.
    evaluate env s (l1 ++ l2) = (s',Rval vs) ⇔
    ∃s1 v1 v2. evaluate env s l1 = (s1,Rval v1) ∧
               evaluate env s1 l2 = (s',Rval v2) ∧
               vs = v1++v2
Proof
  srw_tac[][] >> EQ_TAC >- MATCH_ACCEPT_TAC evaluate_append_Rval >>
  map_every qid_spec_tac[`vs`,`s`] >>
  Induct_on`l1`>>srw_tac[][evaluate_def,Once evaluate_cons] >> srw_tac[][] >>
  srw_tac[][Once evaluate_cons] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
  full_simp_tac(srw_ss())[PULL_EXISTS] >>
  res_tac >> full_simp_tac(srw_ss())[]
QED

Theorem evaluate_append_Rerr:
   ∀l1 env s l2 s' e.
    evaluate env s (l1 ++ l2) = (s',Rerr e) ⇔
    (evaluate env s l1 = (s', Rerr e) ∨
       ∃s1 v1.
         evaluate env s l1 = (s1, Rval v1) ∧
         evaluate env s1 l2 = (s', Rerr e))
Proof
  Induct >> srw_tac[][evaluate_def] >>
  srw_tac[][Once evaluate_cons] >> MATCH_MP_TAC EQ_SYM >>
  srw_tac[][Once evaluate_cons] >> MATCH_MP_TAC EQ_SYM >>
  every_case_tac >> simp[] >>
  srw_tac[][Once evaluate_cons] >>
  TRY EQ_TAC >>
  spose_not_then strip_assume_tac >> srw_tac[][] >> full_simp_tac(srw_ss())[] >>
  full_simp_tac(srw_ss())[evaluate_append_Rval_iff] >>
  first_x_assum(qspecl_then[`env`,`q`,`l2`]mp_tac) >>
  simp[] >> metis_tac[]
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

Theorem dec_clock_with_clock[simp]:
   dec_clock s with clock := y = s with clock := y
Proof
  EVAL_TAC
QED

Theorem do_app_add_to_clock:
   (do_app (s with clock := s.clock + extra) op vs =
    OPTION_MAP (λ(s',r). (s' with clock := s'.clock + extra,r)) (do_app s op vs))
Proof
  Cases_on`do_app s op vs`
  \\ ((pop_assum(strip_assume_tac o CONV_RULE(REWR_CONV do_app_cases_none)))
     ORELSE(pop_assum(strip_assume_tac o CONV_RULE(REWR_CONV do_app_cases))))
  \\ rw[do_app_def] >>
  fs[semanticPrimitivesTheory.store_alloc_def,
     semanticPrimitivesTheory.store_lookup_def,
     semanticPrimitivesTheory.store_assign_def]
  >> srw_tac[][]
  >> every_case_tac \\ fs[] \\ rw[] \\ rfs[]
QED

Theorem do_app_const:
   do_app s op vs = SOME (s',r) ⇒ s'.compile = s.compile
Proof
  rw[do_app_def,case_eq_thms,bool_case_eq,UNCURRY,pair_case_eq] \\ rw[]
QED

Theorem do_install_with_clock:
   do_install vs (s with clock := k) =
   OPTION_MAP (λ(e,s'). (e, s' with clock := k)) (do_install vs s)
Proof
  rw[do_install_def] \\ rpt(PURE_TOP_CASE_TAC \\ fs[UNCURRY])
QED

Theorem do_install_const:
   do_install vs s = SOME (e,s') ⇒ s'.ffi = s.ffi ∧ s'.clock = s.clock ∧ s'.compile = s.compile
Proof
  rw[do_install_def,case_eq_thms,UNCURRY,pair_case_eq] \\ rw[]
QED

Theorem evaluate_add_to_clock:
   ∀env s es s' r.
      evaluate env s es = (s',r) ∧
      r ≠ Rerr (Rabort Rtimeout_error) ⇒
      evaluate env (s with clock := s.clock + extra) es =
        (s' with clock := s'.clock + extra,r)
Proof
  ho_match_mp_tac evaluate_ind >>
  srw_tac[][evaluate_def,case_eq_thms,pair_case_eq] >>
  full_simp_tac(srw_ss())[do_app_add_to_clock,do_install_with_clock,case_eq_thms,pair_case_eq,bool_case_eq] >>
  srw_tac[][] >> rev_full_simp_tac(srw_ss())[] >>
  rev_full_simp_tac(srw_ss()++ARITH_ss)[dec_clock_def] >>
  imp_res_tac do_install_const >> fs [] \\ rfs[]
QED

val do_app_io_events_mono = Q.prove(
  `do_app s op vs = SOME(s',r) ⇒
   s.ffi.io_events ≼ s'.ffi.io_events`,
  srw_tac[][] >> full_simp_tac(srw_ss())[do_app_cases] >>
  every_case_tac >>
  full_simp_tac(srw_ss())[LET_THM,
     semanticPrimitivesTheory.store_alloc_def,
     semanticPrimitivesTheory.store_lookup_def,
     semanticPrimitivesTheory.store_assign_def] >> srw_tac[][] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
  full_simp_tac(srw_ss())[ffiTheory.call_FFI_def,IS_SOME_EXISTS] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][]);

Theorem evaluate_io_events_mono:
   ∀env s es. s.ffi.io_events ≼ (FST (evaluate env s es)).ffi.io_events
Proof
  ho_match_mp_tac evaluate_ind >> srw_tac[][evaluate_def] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >> rev_full_simp_tac(srw_ss())[] >> full_simp_tac(srw_ss())[dec_clock_def] >>
  metis_tac[IS_PREFIX_TRANS,do_app_io_events_mono,do_install_const]
QED

val evaluate_io_events_mono_imp = Q.prove(
  `evaluate env s es = (s',r) ⇒
    s.ffi.io_events ≼ s'.ffi.io_events`,
  metis_tac[evaluate_io_events_mono,FST])

val with_clock_ffi = Q.prove(
  `(s with clock := k).ffi = s.ffi`,EVAL_TAC)
val lemma = DECIDE``x ≠ 0n ⇒ x - 1 + y = x + y - 1``

Theorem evaluate_add_to_clock_io_events_mono:
   ∀env s es.
    (FST(evaluate env s es)).ffi.io_events ≼
    (FST(evaluate env (s with clock := s.clock + extra) es)).ffi.io_events
Proof
  ho_match_mp_tac evaluate_ind >> srw_tac[][evaluate_def] >>
  every_case_tac >> fsrw_tac[][] >>
  imp_res_tac evaluate_add_to_clock >> rev_full_simp_tac(srw_ss())[] >> fsrw_tac[][] >> srw_tac[][] >>
  imp_res_tac evaluate_io_events_mono_imp >> fsrw_tac[][] >> srw_tac[][] >>
  fsrw_tac[][dec_clock_def] >> fsrw_tac[][do_app_add_to_clock,do_install_with_clock] >>
  TRY(first_assum(split_uncurry_arg_tac o rhs o concl) >> fsrw_tac[][]) >>
  imp_res_tac do_app_io_events_mono >>
  imp_res_tac do_install_const >> fsrw_tac[][] >>
  rveq >> fsrw_tac[][do_install_with_clock] >>
  rpt(first_x_assum(qspec_then`extra`mp_tac) \\ srw_tac[][]) >> rev_full_simp_tac(srw_ss())[] >>
  TRY(rfs[] \\ fs[] \\ NO_TAC) \\
  metis_tac[evaluate_io_events_mono,with_clock_ffi,FST,IS_PREFIX_TRANS,lemma]
QED

Theorem evaluate_const:
   ∀env s xs res s'.
    evaluate env s xs = (s',res) ⇒ s'.compile = s.compile
Proof
  ho_match_mp_tac evaluate_ind
  \\ rw[evaluate_def,case_eq_thms,pair_case_eq,bool_case_eq]
  \\ fs[] \\ rfs[patSemTheory.dec_clock_def]
  \\ imp_res_tac do_install_const \\ fs[]
  \\ imp_res_tac do_app_const \\ fs[]
  \\ metis_tac[]
QED

(*
Theorem not_evaluate_list_append:
   ∀l1 ck env s l2 res.
    (∀res. ¬evaluate_list ck env s (l1 ++ l2) res) ⇔
    ((∀res. ¬evaluate_list ck env s l1 res) ∨
       ∃s1 v1.
         evaluate_list ck env s l1 (s1, Rval v1) ∧
         (∀res. ¬evaluate_list ck env s1 l2 res))
Proof
  Induct >- (
    srw_tac[][EQ_IMP_THM] >- (
      full_simp_tac(srw_ss())[Once(CONJUNCT2(evaluate_cases))] >>
      simp[Once(CONJUNCT2(evaluate_cases))] >>
      simp[Once(CONJUNCT2(evaluate_cases))] >>
      srw_tac[][] >> metis_tac[] )
    >- (
      full_simp_tac(srw_ss())[Once(CONJUNCT2(evaluate_cases))] ) >>
    full_simp_tac(srw_ss())[Once(Q.SPECL[`ck`,`env`,`s`,`[]`](CONJUNCT2(evaluate_cases)))] >>
    srw_tac[][] ) >>
  full_simp_tac(srw_ss())[Q.SPECL[`ck`,`env`,`s`,`X::Y`](CONJUNCT2(evaluate_cases))] >>
  srw_tac[][PULL_EXISTS] >>
  reverse(Cases_on`∃res. evaluate ck env s h res`) >- (
    metis_tac[] ) >>
  full_simp_tac(srw_ss())[] >>
  `∃s1 r1. res = (s1,r1)` by metis_tac[PAIR] >>
  reverse (Cases_on`r1`) >- (
    srw_tac[boolSimps.DNF_ss][] >>
    EQ_TAC >> strip_tac >>
    metis_tac[evaluate_determ,semanticPrimitivesTheory.result_distinct,PAIR_EQ]) >>
  srw_tac[boolSimps.DNF_ss][] >>
  first_x_assum(qspecl_then[`ck`,`env`,`s1`,`l2`]strip_assume_tac) >>
  Cases_on`∀res. ¬evaluate_list ck env s1 (l1++l2) res` >- (
    full_simp_tac(srw_ss())[] >>
    metis_tac[evaluate_determ,PAIR_EQ,
              semanticPrimitivesTheory.result_11,
              semanticPrimitivesTheory.result_distinct] ) >>
  FULL_SIMP_TAC pure_ss [] >> full_simp_tac(srw_ss())[] >>
  `∃s2 r2. res = (s2,r2)` by metis_tac[PAIR] >>
  Cases_on`r2` >>
  metis_tac[evaluate_determ,PAIR_EQ,pair_CASES,
            semanticPrimitivesTheory.result_11,
            semanticPrimitivesTheory.result_nchotomy,
            semanticPrimitivesTheory.result_distinct]
QED
*)

open bagTheory

(* finding the InitGlobal operations *)
val op_gbag_def = Define`
  op_gbag (Op (GlobalVarInit n)) = BAG_INSERT n {||} ∧
  op_gbag _ = {||}
`;

(* Same naming scheme as clos *)
val set_globals_def = tDefine "set_globals"`
  (set_globals (Raise _ e) = set_globals e) ∧
  (set_globals (Handle _ e1 e2) = set_globals e1 ⊎ set_globals e2) ∧
  (set_globals (Con _ _ es) = elist_globals es) ∧
  (set_globals (Fun _ e) = set_globals e) ∧
  (set_globals (App _ op es) = op_gbag op ⊎ elist_globals es) ∧
  (set_globals (If _ e1 e2 e3) = set_globals e1 ⊎ set_globals e2 ⊎ set_globals e3) ∧
  (set_globals (Let _ e1 e2) = set_globals e1 ⊎ set_globals e2) ∧
  (set_globals (Seq _ e1 e2) = set_globals e1 ⊎ set_globals e2) ∧
  (set_globals (Letrec _ es e) =
    set_globals e ⊎ elist_globals es) ∧
  (set_globals _ = {||}) ∧
  (elist_globals [] = {||}) ∧
  (elist_globals (e::es) = set_globals e ⊎ elist_globals es)`
 (WF_REL_TAC `
      measure (λa. case a of INL e => exp_size e | INR y => exp1_size y)` >>
  rw[]);
val _ = export_rewrites ["set_globals_def"]

Theorem elist_globals_append:
   ∀a b. elist_globals (a++b) =
  elist_globals a ⊎ elist_globals b
Proof
  Induct>>fs[set_globals_def,ASSOC_BAG_UNION]
QED

Theorem elist_globals_reverse:
   ∀ls. elist_globals (REVERSE ls) = elist_globals ls
Proof
  Induct>>fs[set_globals_def,elist_globals_append,COMM_BAG_UNION]
QED

Theorem elist_globals_FOLDR:
   elist_globals es = FOLDR BAG_UNION {||} (MAP set_globals es)
Proof
  Induct_on `es` >> simp[]
QED

Theorem exp_size_MEM:
   (∀elist e. MEM e elist ⇒ exp_size e < patLang$exp1_size elist)
Proof
  Induct>>rw[]>>fs[patLangTheory.exp_size_def]>>rw[]>>
  res_tac>>fs[]
QED

val esgc_free_def = tDefine "esgc_free" `
  (esgc_free (Raise _ e) ⇔ esgc_free e) ∧
  (esgc_free (Handle _ e1 e2) ⇔ esgc_free e1 ∧ esgc_free e2) ∧
  (esgc_free (Con _ _ es) ⇔ EVERY esgc_free es) ∧
  (esgc_free (Fun _ e) ⇔ set_globals e = {||}) ∧
  (esgc_free (App _ op es) ⇔ EVERY esgc_free es) ∧
  (esgc_free (If _ e1 e2 e3) ⇔ esgc_free e1 ∧ esgc_free e2 ∧ esgc_free e3) ∧
  (esgc_free (Let _ e1 e2) ⇔ esgc_free e1 ∧ esgc_free e2) ∧
  (esgc_free (Seq _ e1 e2) ⇔ esgc_free e1 ∧ esgc_free e2) ∧
  (esgc_free (Letrec _ es e) ⇔
    elist_globals es = {||} ∧ esgc_free e) ∧
  (esgc_free _ = T)`
  (WF_REL_TAC `measure exp_size` >> simp[] >> rpt strip_tac >>
   imp_res_tac exp_size_MEM >> simp[])

val esgc_free_def = save_thm("esgc_free_def[simp,compute]",
  SIMP_RULE (bool_ss ++ ETA_ss) [] esgc_free_def)

val _ = export_theory()
