open preamble
     ml_translatorTheory
     patternMatchesTheory patternMatchesLib;
open astTheory libTheory semanticPrimitivesTheory;
open mlstringTheory;
open integerTheory terminationTheory;

val _ = new_theory "ml_pmatch";

val write_def = ml_progTheory.write_def;

val EvalPatRel_def = Define`
  EvalPatRel env a p pat ⇔
    ∀k x av. a x av ⇒
      evaluate_match (empty_state k) env av
        [(p,Con NONE [])] ARB =
        (empty_state k,
         if ∃vars. pat vars = x
         then Rval[Conv NONE []] else Rerr(Rraise ARB))`;

val Pmatch_def = tDefine"Pmatch"`
  (Pmatch env [] [] = SOME env) ∧
  (Pmatch env (p1::p2::ps) (v1::v2::vs) =
     case Pmatch env [p1] [v1] of | NONE => NONE
     | SOME env' => Pmatch env' (p2::ps) (v2::vs)) ∧
  (Pmatch env [Pvar x] [v] = SOME (write x v env)) ∧
  (Pmatch env [Plit l] [Litv l'] =
     if l = l' then SOME env else NONE) ∧
  (Pmatch env [Pcon (SOME n) ps] [Conv (SOME (n',t')) vs] =
     case lookup_alist_mod_env n env.c of
      | NONE => NONE
     | SOME (l,t) =>
       if same_tid t t' ∧ LENGTH ps = l ∧
          same_ctor (id_to_n n, t) (n',t')
       then Pmatch env ps vs
       else NONE) ∧
  (Pmatch env [Pcon NONE ps] [Conv NONE vs] =
     if LENGTH ps = LENGTH vs then
       Pmatch env ps vs
     else NONE) ∧
  (Pmatch env [Ptannot p t] [v] = Pmatch env [p] [v]) ∧
  (Pmatch env _ _ = NONE)`
  (WF_REL_TAC`measure (pat1_size o FST o SND)`)

val Pmatch_ind = theorem"Pmatch_ind"

val EvalPatBind_def = Define`
  EvalPatBind env a p pat vars env2 ⇔
    ∃x av.
      a x av ∧
      (Pmatch env [p] [av] = SOME env2) ∧
      (pat vars = x)`;

val Pmatch_cons = store_thm("Pmatch_cons",
  ``∀ps vs.
      Pmatch env (p::ps) (v::vs) =
      case Pmatch env [p] [v] of | NONE => NONE
      | SOME env' => Pmatch env' ps vs``,
  Induct >> Cases_on`vs` >> simp[Pmatch_def] >>
  BasicProvers.CASE_TAC >>
  Cases_on`ps`>>simp[Pmatch_def])

val Pmatch_SOME_const = store_thm("Pmatch_SOME_const",
  ``∀env ps vs env'.
      Pmatch env ps vs = SOME env' ⇒
      env'.m = env.m ∧
      env'.c = env.c``,
  ho_match_mp_tac Pmatch_ind >> simp[Pmatch_def] >>
  rw[] >> BasicProvers.EVERY_CASE_TAC >> fs[] >>
  fs[write_def]);

val pmatch_imp_Pmatch = prove(
  ``(∀envC s p v env aenv.
      s = empty_store ⇒
      envC = aenv.c ∧ env = aenv.v ⇒
      case pmatch envC s p v aenv.v of
      | Match env' =>
        Pmatch aenv [p] [v] = SOME (aenv with v := env')
      | _ => Pmatch aenv [p] [v] = NONE) ∧
    (∀envC s ps vs env aenv.
      s = empty_store ⇒
      envC = aenv.c ∧ env = aenv.v ⇒
      case pmatch_list envC s ps vs aenv.v of
      | Match env' =>
        Pmatch aenv ps vs = SOME (aenv with v := env')
      | _ => Pmatch aenv ps vs = NONE)``,
  ho_match_mp_tac pmatch_ind >>
  rw[pmatch_def,Pmatch_def,write_def]
  >> TRY (rw[environment_component_equality]>>NO_TAC)
  >- (
    BasicProvers.CASE_TAC >>
    BasicProvers.CASE_TAC >>
    BasicProvers.CASE_TAC >> fs[] >>
    BasicProvers.CASE_TAC >> fs[] )
  >- (
    BasicProvers.CASE_TAC >>
    BasicProvers.CASE_TAC >>
    BasicProvers.CASE_TAC >>
    fs[store_lookup_def] >>
    fs[empty_store_def])
  >- (
    first_x_assum(qspec_then`aenv`mp_tac)>>simp[]>>
    BasicProvers.CASE_TAC >> fs[] >>
    simp[Once Pmatch_cons] >>
    BasicProvers.CASE_TAC >> fs[] >>
    simp[Once Pmatch_cons] >> rw[Pmatch_def] >>
    first_x_assum(qspec_then`aenv with v := a`mp_tac)>>simp[]>>
    BasicProvers.CASE_TAC >> simp[Once Pmatch_cons])
  >- (
    rename1 `Pmatch _ (h::t) _ = _` >>
    Cases_on`t`>>simp[Pmatch_def]))
  |> SIMP_RULE std_ss []
  |> curry save_thm "pmatch_imp_Pmatch";

val Pmatch_imp_pmatch = store_thm("Pmatch_imp_pmatch",
  ``∀env ps vs env'.
      (Pmatch env ps vs = SOME env' ⇒
       pmatch_list env.c empty_store ps vs env.v =
         Match env'.v) ∧
      (Pmatch env ps vs = NONE ⇒
       ∀env2.
       pmatch_list env.c empty_store ps vs env.v ≠
         Match env2)``,
  ho_match_mp_tac Pmatch_ind >>
  simp[Pmatch_def,pmatch_def] >> rw[] >>
  fs[write_def] >>
  BasicProvers.CASE_TAC >> fs[] >>
  BasicProvers.EVERY_CASE_TAC >> rfs[] >> rw[] >>
  imp_res_tac Pmatch_SOME_const >>
  fs[write_def] >>
  rfs[] >>
  Cases_on`v20`>>fs[pmatch_def] >>
  BasicProvers.EVERY_CASE_TAC >> fs[store_lookup_def,empty_store_def]);

val pmatch_PMATCH_ROW_COND_No_match = store_thm("pmatch_PMATCH_ROW_COND_No_match",
  ``EvalPatRel env a p pat ∧
    (∀vars. ¬PMATCH_ROW_COND pat (K T) xv vars) ∧
    a xv res ⇒
    Pmatch env [p] [res] = NONE``,
  rw[EvalPatRel_def,PMATCH_ROW_COND_def] >>
  first_x_assum drule >>
  disch_then (qspec_then `ARB` mp_tac) >>
  rw [evaluate_def] >>
  every_case_tac >>
  fs [] >>
  rw [] >>
  CCONTR_TAC >>
  fs [] >>
  `?env2. Pmatch env [p] [res] = SOME env2` by metis_tac [option_nchotomy] >>
  imp_res_tac Pmatch_imp_pmatch >>
  fs [empty_state_def,pmatch_def] >>
  every_case_tac >>
  fs [build_conv_def, do_con_check_def] >>
  rw [] >>
  metis_tac []);

val pmatch_PMATCH_ROW_COND_Match = store_thm("pmatch_PMATCH_ROW_COND_Match",
  ``EvalPatRel env a p pat ∧
    PMATCH_ROW_COND pat (K T) xv vars ∧
    a xv res
    ⇒ ∃env2. Pmatch env [p] [res] = SOME env2``,
  rw[EvalPatRel_def,PMATCH_ROW_COND_def] >>
  first_x_assum drule >>
  disch_then (qspec_then `ARB` mp_tac) >>
  rw [evaluate_def] >>
  every_case_tac >>
  fs [] >>
  rw [] >>
  CCONTR_TAC >>
  fs [] >>
  `Pmatch env [p] [res] = NONE` by metis_tac [option_nchotomy] >>
  imp_res_tac Pmatch_imp_pmatch >>
  fs [empty_state_def,pmatch_def] >>
  every_case_tac >>
  fs [build_conv_def, do_con_check_def] >>
  rw [] >>
  metis_tac []);

val Eval_PMATCH_NIL = store_thm("Eval_PMATCH_NIL",
  ``!b x xv a.
      Eval env x (a xv) ==>
      CONTAINER F ==>
      Eval env (Mat x []) (b (PMATCH xv []))``,
  rw[CONTAINER_def]);

val empty_state_refs = EVAL``(empty_state k).refs = empty_store`` |> EQT_ELIM

val clock_different_lemma3 = Q.store_thm ("clock_different_lemma3",
 `!k1 k2 env e res1 res2.
   evaluate (empty_state k1) env [e] = (empty_state k1', Rval [res1]) ∧
   evaluate (empty_state k2) env [e] = (st1, Rval r)
   ⇒
   ?k3. st1 = empty_state k3 ∧ [res1] = r`,
 rpt gen_tac
 >> strip_tac
 >> `?extra. k1 = k2 + extra ∨ k2 = k1 + extra` by intLib.ARITH_TAC
 >> fs []
 >- (
   drule (CONJUNCT1 evaluatePropsTheory.evaluate_add_to_clock)
   >> disch_then (qspec_then `extra` assume_tac)
   >> fs [empty_state_def, state_component_equality])
 >- (
   qpat_assum `evaluate _ _ _ = _` mp_tac
   >> drule clock_add_lemma
   >> disch_then (qspec_then `extra` assume_tac)
   >> fs [empty_state_def, state_component_equality]));

val Eval_PMATCH = store_thm("Eval_PMATCH",
  ``!b a x xv.
      ALL_DISTINCT (pat_bindings p []) ⇒
      (∀v1 v2. pat v1 = pat v2 ⇒ v1 = v2) ⇒
      Eval env x (a xv) ⇒
      (p1 xv ⇒ Eval env (Mat x ys) (b (PMATCH xv yrs))) ⇒
      EvalPatRel env a p pat ⇒
      (∀env2 vars.
        EvalPatBind env a p pat vars env2 ∧ p2 vars ⇒
        Eval env2 e (b (res vars))) ⇒
      (∀vars. PMATCH_ROW_COND pat (K T) xv vars ⇒ p2 vars) ∧
      ((∀vars. ¬PMATCH_ROW_COND pat (K T) xv vars) ⇒ p1 xv) ⇒
      Eval env (Mat x ((p,e)::ys)) (b (PMATCH xv ((PMATCH_ROW pat (K T) res)::yrs)))``,
  rw[Eval_def, evaluate_def] >>
  rfs [] >>
  Cases_on`∃vars. PMATCH_ROW_COND pat (K T) xv vars` >> fs[] >- (
    imp_res_tac pmatch_PMATCH_ROW_COND_Match >>
    ntac 3 (pop_assum kall_tac) >>
    fs[EvalPatRel_def] >>
    first_x_assum(qspec_then`vars`mp_tac)>>simp[] >>
    qpat_assum`p1 xv ⇒ X`kall_tac >>
    fs[EvalPatBind_def,PMATCH_ROW_COND_def,PULL_EXISTS] >>
    first_x_assum(qspec_then`vars`mp_tac)>>simp[] >> strip_tac >>
    first_x_assum(fn th => first_assum(strip_assume_tac o MATCH_MP th)) >>
    fs [evaluate_def] >>
    rfs [] >>
    strip_tac >>
    first_x_assum (qspecl_then [`env2`, `vars`, `res'`] mp_tac) >>
    simp [] >>
    rw [] >>
    first_x_assum (qspec_then `ARB` mp_tac) >>
    simp [empty_state_refs] >>
    Cases_on `pmatch env.c empty_store p res' env.v` >>
    simp [] >>
    rw []
    >- metis_tac []
    >- (
      CONV_TAC SWAP_EXISTS_CONV >>
      qexists_tac `k + k'` >>
      mp_tac (Q.SPECL [`x`, `k`] clock_add_lemma) >>
      disch_then drule >>
      disch_then (qspec_then `k'` mp_tac) >>
      simp [empty_state_refs] >>
      rw [] >>
      qexists_tac `res''` >>
      simp [] >>
      imp_res_tac Pmatch_imp_pmatch >>
      imp_res_tac Pmatch_SOME_const >>
      rfs[pmatch_def] >>
      var_eq_tac >>
      `env with v := env2.v = env2` by rw [environment_component_equality] >>
      fs [] >>
      simp[PMATCH_def,PMATCH_ROW_def,PMATCH_ROW_COND_def] >>
      `(∃vars'. pat vars' = pat vars) = T` by metis_tac[] >>
      `(some x. pat x = pat vars) = SOME vars` by ( simp[optionTheory.some_def] >> METIS_TAC[] ) >>
      simp [])
   >- metis_tac []) >>
  split_pair_case_tac >>
  fs [] >>
  rename1 `evaluate _ _ _ = (st1, r1)` >>
  Cases_on `r1` >>
  fs [] >>
  imp_res_tac clock_different_lemma3 >>
  fs [] >>
  rpt var_eq_tac >>
  CONV_TAC SWAP_EXISTS_CONV >>
  qexists_tac `k'` >>
  simp [empty_state_refs] >>
  simp[PMATCH_def,PMATCH_ROW_def] >>
  imp_res_tac pmatch_PMATCH_ROW_COND_No_match >>
  imp_res_tac Pmatch_imp_pmatch >>
  fs[pmatch_def] >>
  fs[EvalPatRel_def] >>
  CASE_TAC >>
  fs [empty_state_refs] >>
  fs [] >>
  first_x_assum(fn th => first_x_assum(mp_tac o MATCH_MP th)) >>
  simp [evaluate_def, empty_state_refs] >> rw []);

val PMATCH_option_case_rwt = store_thm("PMATCH_option_case_rwt",
  ``((case x of NONE => NONE
      | SOME (y1,y2) => P y1 y2) = SOME env2) <=>
    ?y1 y2. (x = SOME (y1,y2)) /\ (P y1 y2 = SOME env2)``,
  Cases_on `x` \\ fs [] \\ Cases_on `x'` \\ fs []);

val _ = export_theory()
