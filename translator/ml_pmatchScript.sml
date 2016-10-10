open preamble
     determTheory ml_translatorTheory
     patternMatchesTheory patternMatchesLib;
open astTheory libTheory semanticPrimitivesTheory bigStepTheory;
open determTheory evalPropsTheory bigClockTheory mlstringTheory;
open integerTheory terminationTheory;

val _ = new_theory "ml_pmatch";

val write_def = ml_progTheory.write_def;

val EvalPatRel_def = Define`
  EvalPatRel env a p pat ⇔
    ∀x av. a x av ⇒ ∀refs.
      evaluate_match F env (empty_state with refs := refs) av
        [(p,Con NONE [])] ARB
        (empty_state with refs := refs,
         if ∃vars. pat vars = x
         then Rval(Conv NONE []) else Rerr(Rraise ARB))`

val EvalPatBind_def = Define`
  EvalPatBind env a p pat vars env2 ⇔
    ∃x av refs env'.
      a x av ∧
      (pmatch env.c refs p av env.v = Match env') ∧
      (env2 = env with v := env') ∧
      (pat vars = x)`

val pmatch_PMATCH_ROW_COND_No_match = store_thm("pmatch_PMATCH_ROW_COND_No_match",
  ``EvalPatRel env a p pat ∧
    (∀vars. ¬PMATCH_ROW_COND pat (K T) xv vars) ∧
    a xv res ⇒
    pmatch env.c refs p res env.v = No_match``,
  fs [PMATCH_ROW_COND_def] >>
  rw[EvalPatRel_def] >>
  first_x_assum(fn th => first_x_assum(strip_assume_tac o MATCH_MP th)) >>
  first_x_assum(qspec_then`refs`mp_tac) >>
  ntac 4 (simp[Once evaluate_cases]) >>
  rw[pmatch_def]);

val pmatch_PMATCH_ROW_COND_Match = store_thm("pmatch_PMATCH_ROW_COND_Match",
  ``EvalPatRel env a p pat ∧
    PMATCH_ROW_COND pat (K T) xv vars ∧
    a xv res
    ⇒ ∃env2. pmatch env.c refs p res env.v = Match env2``,
  rw[EvalPatRel_def,PMATCH_ROW_COND_def] >>
  first_x_assum(fn th => first_x_assum(strip_assume_tac o MATCH_MP th)) >>
  first_x_assum(qspec_then`refs`mp_tac) >>
  ntac 4 (fs[Once evaluate_cases]) >>
  strip_tac \\ every_case_tac \\ fs[] \\
  fs[pmatch_def] \\ fs[Once evaluate_cases] \\
  metis_tac[]);

val Eval_PMATCH_NIL = store_thm("Eval_PMATCH_NIL",
  ``!b x xv a.
      Eval env x (a xv) ==>
      CONTAINER F ==>
      Eval env (Mat x []) (b (PMATCH xv []))``,
  rw[CONTAINER_def]);

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
  rw[Eval_def] >>
  rw[Once evaluate_cases,PULL_EXISTS] >> fs[] >>
  first_x_assum(qspec_then`refs`strip_assume_tac) >>
  asm_exists_tac \\ fs[] \\
  rw[Once evaluate_cases,PULL_EXISTS] >>
  Cases_on`∃vars. PMATCH_ROW_COND pat (K T) xv vars` >> fs[] >- (
    imp_res_tac pmatch_PMATCH_ROW_COND_Match >>
    pop_assum kall_tac >>
    first_x_assum(qspec_then`refs++refs'`strip_assume_tac) \\ fs[] \\
    qpat_x_assum`p1 xv ⇒ $! _`kall_tac >>
    fs[EvalPatRel_def] >>
    first_x_assum(qspec_then`vars`mp_tac)>>simp[] >> strip_tac >>
    first_x_assum(fn th => first_assum(strip_assume_tac o MATCH_MP th)) >>
    first_x_assum(qspec_then`refs++refs'`mp_tac) >>
    ntac 4 (simp[Once evaluate_cases]) \\ rw[] \\
    fs[PMATCH_ROW_COND_def] \\
    `EvalPatBind env a p pat vars (env with v := env2)`
    by (
      simp[EvalPatBind_def,environment_component_equality] \\
      metis_tac[] ) \\
    first_x_assum drule \\ simp[]
    \\ disch_then(qspec_then`refs++refs'`strip_assume_tac)
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ asm_exists_tac \\ fs[]
    \\ simp[PMATCH_def,PMATCH_ROW_def,PMATCH_ROW_COND_def] >>
    `(some x. pat x = pat vars') = SOME vars` by (
      simp[optionTheory.some_def] >>
      METIS_TAC[] ) >>
    simp[]) >>
  first_x_assum(qspec_then`refs`strip_assume_tac) \\
  qpat_x_assum`evaluate F _ _ (Mat _ _) _`mp_tac >>
  simp[Once evaluate_cases] >> strip_tac >>
  imp_res_tac (CONJUNCT1 big_exp_determ) >> fs[] >> rw[] >>
  srw_tac[DNF_ss][] >> disj2_tac >>
  simp[PMATCH_def,PMATCH_ROW_def] >>
  imp_res_tac pmatch_PMATCH_ROW_COND_No_match >>
  first_x_assum(qspec_then`refs++refs'`strip_assume_tac) >> fs[] >>
  asm_exists_tac \\ fs[]);

val PMATCH_option_case_rwt = store_thm("PMATCH_option_case_rwt",
  ``((case x of NONE => NONE
      | SOME (y1,y2) => P y1 y2) = SOME env2) <=>
    ?y1 y2. (x = SOME (y1,y2)) /\ (P y1 y2 = SOME env2)``,
  Cases_on `x` \\ fs [] \\ Cases_on `x'` \\ fs []);

val _ = export_theory()
