open preamble patSemTheory

val _ = new_theory"patProps"

val do_app_cases = Q.store_thm("do_app_cases",
  `patSem$do_app s op vs = SOME x ⇒
    (∃z n1 n2. op = (Op (Op (Opn z))) ∧ vs = [Litv (IntLit n1); Litv (IntLit n2)]) ∨
    (∃z n1 n2. op = (Op (Op (Opb z))) ∧ vs = [Litv (IntLit n1); Litv (IntLit n2)]) ∨
    (∃v1 v2. op = (Op (Op Equality)) ∧ vs = [v1; v2]) ∨
    (∃lnum v. op = (Op (Op Opassign)) ∧ vs = [Loc lnum; v]) ∨
    (∃n. op = (Op (Op Opderef)) ∧ vs = [Loc n]) ∨
    (∃v. op = (Op (Op Opref)) ∧ vs = [v]) ∨
    (∃idx v. op = (Op (Init_global_var idx)) ∧ vs = [v]) ∨
    (∃n l tag v. op = Tag_eq n l ∧ vs = [Conv tag v]) ∨
    (∃n tag v. op = El n ∧ vs = [Conv tag v]) ∨
    (∃n w. op = (Op (Op Aw8alloc)) ∧ vs = [Litv (IntLit n); Litv (Word8 w)]) ∨
    (∃lnum i. op = (Op (Op Aw8sub)) ∧ vs = [Loc lnum; Litv (IntLit i)]) ∨
    (∃n. op = (Op (Op Aw8length)) ∧ vs = [Loc n]) ∨
    (∃lnum i w. op = (Op (Op Aw8update)) ∧ vs = [Loc lnum; Litv (IntLit i); Litv (Word8 w)]) ∨
    (∃c. op = (Op (Op Ord)) ∧ vs = [Litv (Char c)]) ∨
    (∃n. op = (Op (Op Chr)) ∧ vs = [Litv (IntLit n)]) ∨
    (∃z c1 c2. op = (Op (Op (Chopb z))) ∧ vs = [Litv (Char c1); Litv (Char c2)]) ∨
    (∃s. op = (Op (Op Explode)) ∧ vs = [Litv (StrLit s)]) ∨
    (∃v ls. op = (Op (Op Implode)) ∧ vs = [v] ∧ (v_to_char_list v = SOME ls)) ∨
    (∃s. op = (Op (Op Strlen)) ∧ vs = [Litv (StrLit s)]) ∨
    (∃v vs'. op = (Op (Op VfromList)) ∧ vs = [v] ∧ (v_to_list v = SOME vs')) ∨
    (∃vs' i. op = (Op (Op Vsub)) ∧ vs = [Vectorv vs'; Litv (IntLit i)]) ∨
    (∃vs'. op = (Op (Op Vlength)) ∧ vs = [Vectorv vs']) ∨
    (∃v n. op = (Op (Op Aalloc)) ∧ vs = [Litv (IntLit n); v]) ∨
    (∃lnum i. op = (Op (Op Asub)) ∧ vs = [Loc lnum; Litv (IntLit i)]) ∨
    (∃n. op = (Op (Op Alength)) ∧ vs = [Loc n]) ∨
    (∃lnum i v. op = (Op (Op Aupdate)) ∧ vs = [Loc lnum; Litv (IntLit i); v]) ∨
    (∃lnum n. op = (Op (Op (FFI n))) ∧ vs = [Loc lnum])`,
  PairCases_on`s`>>rw[patSemTheory.do_app_def] >>
  pop_assum mp_tac >>
  Cases_on`op` >- (
    simp[] >>
    every_case_tac >> fs[] ) >>
  BasicProvers.CASE_TAC >>
  every_case_tac);

val evaluate_lit = store_thm("evaluate_lit[simp]",
  ``∀ck env s l res.
      patSem$evaluate ck env s (Lit l) res ⇔ (res = (s,Rval(Litv l)))``,
  rw[Once evaluate_cases]);

val Boolv_11 = store_thm("Boolv_11[simp]",``patSem$Boolv b1 = Boolv b2 ⇔ b1 = b2``,EVAL_TAC>>rw[]);

val Boolv_disjoint = save_thm("Boolv_disjoint",EVAL``patSem$Boolv T = Boolv F``);

val evaluate_Con_nil =
  ``evaluate ck env s (Con x []) y``
  |> (SIMP_CONV(srw_ss())[Once evaluate_cases]
      THENC SIMP_CONV(srw_ss())[Once evaluate_cases]
      THENC SIMP_CONV(srw_ss())[Once evaluate_cases])
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
  ``∀ck env s e s' v. ¬patSem$evaluate ck env s (Raise e) (s', Rval v)``,
  rw[Once evaluate_cases])
val _ = export_rewrites["evaluate_raise_rval"]

val evaluate_list_length = store_thm("evaluate_list_length",
  ``∀ls ck env s s' vs.
      evaluate_list ck env s ls (s',Rval vs) ⇒ LENGTH vs = LENGTH ls``,
  Induct >> simp[Once evaluate_cases,PULL_EXISTS] >>
  rw[] >> res_tac)

val evaluate_list_append_Rval = store_thm("evaluate_list_append_Rval",
  ``∀l1 ck env s l2 s' vs.
    evaluate_list ck env s (l1 ++ l2) (s',Rval vs) ⇒
    ∃s1 v1 v2. evaluate_list ck env s l1 (s1,Rval v1) ∧
               evaluate_list ck env s1 l2 (s',Rval v2) ∧
               vs = v1++v2``,
  Induct >> simp[Once evaluate_cases,PULL_EXISTS] >> rw[]
  >- (
    rw[Once evaluate_cases] >>
    rw[Once evaluate_cases] )
  >- (
    rw[Once evaluate_cases] >>
    rw[Once evaluate_cases] >>
    metis_tac[] )
  >- (
    rw[Once evaluate_cases,PULL_EXISTS] >>
    first_assum(match_exists_tac o concl) >> rw[] >> res_tac >>
    first_assum(match_exists_tac o concl) >> rw[]))

val evaluate_list_append_Rval_iff = store_thm("evaluate_list_append_Rval_iff",
  ``∀l1 ck env s l2 s' vs.
    evaluate_list ck env s (l1 ++ l2) (s',Rval vs) ⇔
    ∃s1 v1 v2. evaluate_list ck env s l1 (s1,Rval v1) ∧
               evaluate_list ck env s1 l2 (s',Rval v2) ∧
               vs = v1++v2``,
  rw[] >> EQ_TAC >- MATCH_ACCEPT_TAC evaluate_list_append_Rval >>
  map_every qid_spec_tac[`vs`,`s`] >>
  Induct_on`l1`>>rw[Once evaluate_cases] >> rw[] >>
  fs[PULL_EXISTS] >>
  rw[Once evaluate_cases] >>
  first_assum(match_exists_tac o concl) >> rw[] >>
  first_x_assum(match_mp_tac) >> metis_tac[])

val evaluate_list_append_Rerr = store_thm("evaluate_list_append_Rerr",
  ``∀l1 ck env s l2 s' e.
    evaluate_list ck env s (l1 ++ l2) (s',Rerr e) ⇔
    (evaluate_list ck env s l1 (s', Rerr e) ∨
       ∃s1 v1.
         evaluate_list ck env s l1 (s1, Rval v1) ∧
         evaluate_list ck env s1 l2 (s', Rerr e))``,
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
  rw[EQ_IMP_THM] >>
  fs[Once(Q.SPECL[`ck`,`env`,`s`,`X::Y`](CONJUNCT2(evaluate_cases)))] >>
  simp[Once(Q.SPECL[`ck`,`env`,`s`,`X::Y`](CONJUNCT2(evaluate_cases)))] >>
  metis_tac[])

val evaluate_determ = store_thm("evaluate_determ",
  ``(∀ck env s e res1. evaluate ck env s e res1 ⇒
       ∀res2. patSem$evaluate ck env s e res2 ⇒ (res2 = res1)) ∧
    (∀ck env s e res1. evaluate_list ck env s e res1 ⇒
       ∀res2. patSem$evaluate_list ck env s e res2 ⇒ (res2 = res1))``,
  ho_match_mp_tac evaluate_ind >>
  rpt conj_tac >>
  rpt gen_tac >> strip_tac >>
  simp_tac(srw_ss())[Once evaluate_cases] >> fs[] >>
  TRY (
    gen_tac >> strip_tac >>
    rpt (res_tac >> fs[] >> rpt BasicProvers.VAR_EQ_TAC)) >>
  pop_assum mp_tac >> simp[Once evaluate_cases]);

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

val _ = export_theory()
