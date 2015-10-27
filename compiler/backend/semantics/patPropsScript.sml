open preamble patSemTheory

val _ = new_theory"patProps"

val evaluate_lit = save_thm("evaluate_lit[simp]",
      EVAL``patSem$evaluate env s [Lit l]``)

val Boolv_11 = store_thm("Boolv_11[simp]",``patSem$Boolv b1 = Boolv b2 ⇔ b1 = b2``,EVAL_TAC>>rw[]);

val Boolv_disjoint = save_thm("Boolv_disjoint",EVAL``patSem$Boolv T = Boolv F``);

val evaluate_Con_nil =
  ``evaluate env s [Con x []]``
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
 simp[v_size_def]>>rw[]>>res_tac>>simp[])
val _ = export_rewrites["no_closures_def"];

val no_closures_Boolv = store_thm("no_closures_Boolv[simp]",
  ``no_closures (Boolv b)``,
  EVAL_TAC);

val evaluate_raise_rval = store_thm("evaluate_raise_rval",
  ``∀env s e s' v. patSem$evaluate env s [Raise e] ≠ (s', Rval v)``,
  EVAL_TAC >> rw[] >> every_case_tac >> simp[])
val _ = export_rewrites["evaluate_raise_rval"]

val evaluate_length = store_thm("evaluate_length",
  ``∀env s ls s' vs.
      evaluate env s ls = (s',Rval vs) ⇒ LENGTH vs = LENGTH ls``,
  ho_match_mp_tac evaluate_ind >>
  rw[evaluate_def] >> rw[] >>
  every_case_tac >> fs[] >> rw[] >>
  imp_res_tac do_app_cases >> fs[do_app_def] >> rw[] >>
  every_case_tac >> fs[] >> rw[] >>
  fs[LET_THM,
     semanticPrimitivesTheory.store_alloc_def,
     semanticPrimitivesTheory.store_lookup_def,
     semanticPrimitivesTheory.store_assign_def] >> rw[] >>
  fs[] >> rw[] >>
  every_case_tac >> fs[] >> rw[] >>
  fs[] >> rw[]);

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
  `evaluate env s [e] = (s',Rval vs) ⇒ vs = [HD vs]`,
  rw[] >> imp_res_tac evaluate_length >> rw[SING_HD])

val evaluate_append_Rval = store_thm("evaluate_append_Rval",
  ``∀l1 env s l2 s' vs.
    evaluate env s (l1 ++ l2) = (s',Rval vs) ⇒
    ∃s1 v1 v2. evaluate env s l1 = (s1,Rval v1) ∧
               evaluate env s1 l2 = (s',Rval v2) ∧
               vs = v1++v2``,
  Induct >> simp[evaluate_def,Once evaluate_cons] >>
  rw[] >> simp[Once evaluate_cons] >>
  every_case_tac >> fs[] >> rw[] >> res_tac >>
  rw[] >> fs[] >> rw[]);

val evaluate_append_Rval_iff = store_thm("evaluate_append_Rval_iff",
  ``∀l1 env s l2 s' vs.
    evaluate env s (l1 ++ l2) = (s',Rval vs) ⇔
    ∃s1 v1 v2. evaluate env s l1 = (s1,Rval v1) ∧
               evaluate env s1 l2 = (s',Rval v2) ∧
               vs = v1++v2``,
  rw[] >> EQ_TAC >- MATCH_ACCEPT_TAC evaluate_append_Rval >>
  map_every qid_spec_tac[`vs`,`s`] >>
  Induct_on`l1`>>rw[evaluate_def,Once evaluate_cons] >> rw[] >>
  rw[Once evaluate_cons] >>
  every_case_tac >> fs[] >> rw[] >>
  fs[PULL_EXISTS] >>
  res_tac >> fs[]);

val evaluate_append_Rerr = store_thm("evaluate_append_Rerr",
  ``∀l1 env s l2 s' e.
    evaluate env s (l1 ++ l2) = (s',Rerr e) ⇔
    (evaluate env s l1 = (s', Rerr e) ∨
       ∃s1 v1.
         evaluate env s l1 = (s1, Rval v1) ∧
         evaluate env s1 l2 = (s', Rerr e))``,
  Induct >> rw[evaluate_def] >>
  rw[Once evaluate_cons] >> MATCH_MP_TAC EQ_SYM >>
  rw[Once evaluate_cons] >> MATCH_MP_TAC EQ_SYM >>
  every_case_tac >> simp[] >>
  rw[Once evaluate_cons] >>
  TRY EQ_TAC >>
  spose_not_then strip_assume_tac >> rw[] >> fs[] >>
  fs[evaluate_append_Rval_iff] >>
  first_x_assum(qspecl_then[`env`,`q`,`l2`]mp_tac) >>
  simp[] >> metis_tac[]);

val evaluate_append = Q.store_thm("evaluate_append",
  `evaluate env s (l1 ++ l2) =
   case evaluate env s l1 of
   | (s,Rval v1) =>
     (case evaluate env s l2 of
      | (s,Rval v2) => (s,Rval(v1++v2))
      | r => r)
   | r => r`,
  map_every qid_spec_tac[`l2`,`s`] >> Induct_on`l1` >>
  rw[evaluate_def] >- (
    every_case_tac >> fs[] ) >>
  rw[Once evaluate_cons] >>
  match_mp_tac EQ_SYM >>
  rw[Once evaluate_cons] >>
  BasicProvers.CASE_TAC >> fs[] >>
  Cases_on`r`>>fs[] >>
  every_case_tac  >> fs[]);

(*
val not_evaluate_list_append = store_thm("not_evaluate_list_append",
  ``∀l1 ck env s l2 res.
    (∀res. ¬evaluate_list ck env s (l1 ++ l2) res) ⇔
    ((∀res. ¬evaluate_list ck env s l1 res) ∨
       ∃s1 v1.
         evaluate_list ck env s l1 (s1, Rval v1) ∧
         (∀res. ¬evaluate_list ck env s1 l2 res))``,
  Induct >- (
    rw[EQ_IMP_THM] >- (
      fs[Once(CONJUNCT2(evaluate_cases))] >>
      simp[Once(CONJUNCT2(evaluate_cases))] >>
      simp[Once(CONJUNCT2(evaluate_cases))] >>
      rw[] >> metis_tac[] )
    >- (
      fs[Once(CONJUNCT2(evaluate_cases))] ) >>
    fs[Once(Q.SPECL[`ck`,`env`,`s`,`[]`](CONJUNCT2(evaluate_cases)))] >>
    rw[] ) >>
  fs[Q.SPECL[`ck`,`env`,`s`,`X::Y`](CONJUNCT2(evaluate_cases))] >>
  rw[PULL_EXISTS] >>
  reverse(Cases_on`∃res. evaluate ck env s h res`) >- (
    metis_tac[] ) >>
  fs[] >>
  `∃s1 r1. res = (s1,r1)` by metis_tac[PAIR] >>
  reverse (Cases_on`r1`) >- (
    srw_tac[boolSimps.DNF_ss][] >>
    EQ_TAC >> strip_tac >>
    metis_tac[evaluate_determ,semanticPrimitivesTheory.result_distinct,PAIR_EQ]) >>
  srw_tac[boolSimps.DNF_ss][] >>
  first_x_assum(qspecl_then[`ck`,`env`,`s1`,`l2`]strip_assume_tac) >>
  Cases_on`∀res. ¬evaluate_list ck env s1 (l1++l2) res` >- (
    fs[] >>
    metis_tac[evaluate_determ,PAIR_EQ,
              semanticPrimitivesTheory.result_11,
              semanticPrimitivesTheory.result_distinct] ) >>
  FULL_SIMP_TAC pure_ss [] >> fs[] >>
  `∃s2 r2. res = (s2,r2)` by metis_tac[PAIR] >>
  Cases_on`r2` >>
  metis_tac[evaluate_determ,PAIR_EQ,pair_CASES,
            semanticPrimitivesTheory.result_11,
            semanticPrimitivesTheory.result_nchotomy,
            semanticPrimitivesTheory.result_distinct] )
*)

val _ = export_theory()
