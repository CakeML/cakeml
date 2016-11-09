open preamble
     determTheory ml_translatorTheory
     patternMatchesTheory patternMatchesLib;
open astTheory libTheory semanticPrimitivesTheory bigStepTheory;
open determTheory bigStepPropsTheory bigClockTheory mlstringTheory;
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

(*
  This is very similar to pmatch_list (see theorems proving connection below).
  It omits some checks, which are unnecessary for the translator but needed in
  the semantics; it thereby makes the translator's automation easier.
*)
val Pmatch_def = tDefine"Pmatch"`
  (Pmatch env refs [] [] = SOME env) ∧
  (Pmatch env refs (p1::p2::ps) (v1::v2::vs) =
     case Pmatch env refs [p1] [v1] of | NONE => NONE
     | SOME env' => Pmatch env' refs (p2::ps) (v2::vs)) ∧
  (Pmatch env refs [Pvar x] [v] = SOME (write x v env)) ∧
  (Pmatch env refs [Plit l] [Litv l'] =
     if l = l' then SOME env else NONE) ∧
  (Pmatch env refs [Pcon (SOME n) ps] [Conv (SOME (n',t')) vs] =
     case lookup_alist_mod_env n env.c of
      | NONE => NONE
     | SOME (l,t) =>
       if same_tid t t' ∧ LENGTH ps = l ∧
          same_ctor (id_to_n n, t) (n',t')
       then Pmatch env refs ps vs
       else NONE) ∧
  (Pmatch env refs [Pcon NONE ps] [Conv NONE vs] =
     if LENGTH ps = LENGTH vs then
       Pmatch env refs ps vs
     else NONE) ∧
  (Pmatch env refs [Pref p] [Loc lnum] =
   case store_lookup lnum refs of
   | SOME (Refv v) => Pmatch env refs [p] [v]
   | _ => NONE) ∧
  (Pmatch env refs [Ptannot p t] [v] = Pmatch env refs [p] [v]) ∧
  (Pmatch env refs _ _ = NONE)`
  (WF_REL_TAC`measure (pat1_size o FST o SND o SND)`)

val Pmatch_ind = theorem"Pmatch_ind"

val EvalPatBind_def = Define`
  EvalPatBind env a p pat vars env2 ⇔
    ∃x av refs.
      a x av ∧
      (Pmatch env refs [p] [av] = SOME env2) ∧
      (pat vars = x)`

val Pmatch_cons = Q.store_thm("Pmatch_cons",
  `∀ps vs.
      Pmatch env refs (p::ps) (v::vs) =
      case Pmatch env refs [p] [v] of | NONE => NONE
      | SOME env' => Pmatch env' refs ps vs`,
  Induct >> Cases_on`vs` >> simp[Pmatch_def] >>
  BasicProvers.CASE_TAC >>
  Cases_on`ps`>>simp[Pmatch_def])

val Pmatch_SOME_const = Q.store_thm("Pmatch_SOME_const",
  `∀env refs ps vs env'.
      Pmatch env refs ps vs = SOME env' ⇒
      env'.m = env.m ∧
      env'.c = env.c`,
  ho_match_mp_tac Pmatch_ind >> simp[Pmatch_def] >>
  rw[] >> BasicProvers.EVERY_CASE_TAC >> fs[] >>
  fs[write_def])

val pmatch_imp_Pmatch = Q.prove(
  `(∀envC s p v env aenv.
      envC = aenv.c ∧ env = aenv.v ⇒
      case pmatch envC s p v aenv.v of
      | Match env' =>
        Pmatch aenv s [p] [v] = SOME (aenv with v := env')
      | _ => Pmatch aenv s [p] [v] = NONE) ∧
    (∀envC s ps vs env aenv.
      envC = aenv.c ∧ env = aenv.v ⇒
      case pmatch_list envC s ps vs aenv.v of
      | Match env' =>
        Pmatch aenv s ps vs = SOME (aenv with v := env')
      | _ => Pmatch aenv s ps vs = NONE)`,
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
    first_x_assum(qspec_then`aenv`mp_tac) \\
    simp[])
  >- (
    first_x_assum(qspec_then`aenv`mp_tac)>>simp[]>>
    BasicProvers.CASE_TAC >> fs[] >>
    simp[Once Pmatch_cons] >>
    BasicProvers.CASE_TAC >> fs[] >>
    simp[Once Pmatch_cons] >> rw[Pmatch_def] >>
    first_x_assum(qspec_then`aenv with v := a`mp_tac)>>simp[]>>
    BasicProvers.CASE_TAC >> simp[Once Pmatch_cons])
  >- (
    qmatch_goalsub_rename_tac`h::t` >>
    Cases_on`t`>>simp[Pmatch_def]))
  |> SIMP_RULE std_ss []
  |> curry save_thm "pmatch_imp_Pmatch"

val Pmatch_imp_pmatch = Q.store_thm("Pmatch_imp_pmatch",
  `∀env s ps vs env'.
    (Pmatch env s ps vs = SOME env' ⇒
       pmatch_list env.c s ps vs env.v =
         Match env'.v) ∧
      (Pmatch env s ps vs = NONE ⇒
       ∀env2.
       pmatch_list env.c s ps vs env.v ≠
         Match env2)`,
  ho_match_mp_tac Pmatch_ind >>
  simp[Pmatch_def,pmatch_def] >> rw[] >>
  fs[write_def] >>
  BasicProvers.CASE_TAC >> fs[] >>
  BasicProvers.EVERY_CASE_TAC >> rfs[] >> rw[] >>
  imp_res_tac Pmatch_SOME_const >>
  fs[write_def] >>
  rfs[] >>
  Cases_on`v20`>>fs[pmatch_def] >>
  BasicProvers.EVERY_CASE_TAC >> fs[store_lookup_def,empty_store_def])

val pmatch_PMATCH_ROW_COND_No_match = Q.store_thm("pmatch_PMATCH_ROW_COND_No_match",
  `EvalPatRel env a p pat ∧
    (∀vars. ¬PMATCH_ROW_COND pat (K T) xv vars) ∧
    a xv res ⇒
    pmatch env.c refs p res env.v = No_match`,
  fs [PMATCH_ROW_COND_def] >>
  rw[EvalPatRel_def] >>
  first_x_assum(fn th => first_x_assum(strip_assume_tac o MATCH_MP th)) >>
  first_x_assum(qspec_then`refs`mp_tac) >>
  ntac 4 (simp[Once evaluate_cases]) >>
  rw[pmatch_def]);

val pmatch_PMATCH_ROW_COND_Match = Q.store_thm("pmatch_PMATCH_ROW_COND_Match",
  `EvalPatRel env a p pat ∧
    PMATCH_ROW_COND pat (K T) xv vars ∧
    a xv res
    ⇒ ∃env2. pmatch env.c refs p res env.v = Match env2`,
  rw[EvalPatRel_def,PMATCH_ROW_COND_def] >>
  first_x_assum(fn th => first_x_assum(strip_assume_tac o MATCH_MP th)) >>
  first_x_assum(qspec_then`refs`mp_tac) >>
  ntac 4 (fs[Once evaluate_cases]) >>
  strip_tac \\ every_case_tac \\ fs[] \\
  fs[pmatch_def] \\ fs[Once evaluate_cases] \\
  metis_tac[]);

val Eval_PMATCH_NIL = Q.store_thm("Eval_PMATCH_NIL",
  `!b x xv a.
      Eval env x (a xv) ==>
      CONTAINER F ==>
      Eval env (Mat x []) (b (PMATCH xv []))`,
  rw[CONTAINER_def]);

val Eval_PMATCH = Q.store_thm("Eval_PMATCH",
  `!b a x xv.
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
      Eval env (Mat x ((p,e)::ys)) (b (PMATCH xv ((PMATCH_ROW pat (K T) res)::yrs)))`,
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
      qspecl_then[`refs++refs'`,`p`,`res'`,`env`]mp_tac(CONJUNCT1 pmatch_imp_Pmatch) \\
      simp[] \\
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

val PMATCH_option_case_rwt = Q.store_thm("PMATCH_option_case_rwt",
  `((case x of NONE => NONE
      | SOME (y1,y2) => P y1 y2) = SOME env2) <=>
    ?y1 y2. (x = SOME (y1,y2)) /\ (P y1 y2 = SOME env2)`,
  Cases_on `x` \\ fs [] \\ Cases_on `x'` \\ fs []);

val _ = export_theory()
