(*
  Theory support for translation of deeply-embedded (PMATCH-based)
  pattern-matches occurring in HOL functions.
*)
open preamble
     astTheory semanticPrimitivesTheory
     patternMatchesTheory patternMatchesLib
     ml_progTheory ml_translatorTheory evaluateTheory
     semanticPrimitivesPropsTheory evaluatePropsTheory;
open ml_translatorTheory integerTheory;

val _ = new_theory "ml_pmatch";

val write_def = ml_progTheory.write_def;

Definition EvalPatRel_def:
  EvalPatRel env a p pat ⇔
    ∀x av. a x av ⇒ ∀refs.
      evaluate_match (empty_state with refs := refs) env av
        [(p,Con NONE [])] ARB =
        (empty_state with refs := refs,
         if ∃vars. pat vars = x
         then Rval([Conv NONE []]) else Rerr(Rraise ARB))
End

(*
  This is very similar to pmatch_list (see theorems proving connection below).
  It omits some checks, which are unnecessary for the translator but needed in
  the semantics; it thereby makes the translator's automation easier.
*)
Definition Pmatch_def:
  (Pmatch env refs [] [] = SOME env) ∧
  (Pmatch env refs (p1::p2::ps) (v1::v2::vs) =
     case Pmatch env refs [p1] [v1] of | NONE => NONE
     | SOME env' => Pmatch env' refs (p2::ps) (v2::vs)) ∧
  (Pmatch env refs [Pany] [v] = SOME env) ∧
  (Pmatch env refs [Pvar x] [v] = SOME (write x v env)) ∧
  (Pmatch env refs [Pas p x] [v] =
     Pmatch (write x v env) refs [p] [v]) ∧
  (Pmatch env refs [Plit l] [Litv l'] =
     if l = l' then SOME env else NONE) ∧
  (Pmatch env refs [Pcon (SOME n) ps] [Conv (SOME (t')) vs] =
     case nsLookup env.c n of
     | NONE => NONE
     | SOME (l,t) =>
       if LENGTH ps = l ∧ LENGTH vs = l ∧
          same_ctor t t' ∧
          same_type t t'
       then Pmatch env refs ps vs
       else NONE) ∧
  (Pmatch env refs [Pcon NONE ps] [Conv NONE vs] =
     if LENGTH ps = LENGTH vs then
       Pmatch env refs ps vs
     else NONE) ∧
  (Pmatch env refs [Pref p] [Loc b lnum] =
   case store_lookup lnum refs of
   | SOME (Refv v) => Pmatch env refs [p] [v]
   | _ => NONE) ∧
  (Pmatch env refs [Ptannot p t] [v] = Pmatch env refs [p] [v]) ∧
  (Pmatch env refs _ _ = NONE)
End

val Pmatch_ind = theorem"Pmatch_ind"

Definition EvalPatBind_def:
  EvalPatBind env a p pat vars env2 ⇔
    ∃x av refs.
      a x av ∧
      (Pmatch env refs [p] [av] = SOME env2) ∧
      (pat vars = x)
End

Theorem Pmatch_cons:
   ∀ps vs.
      Pmatch env refs (p::ps) (v::vs) =
      case Pmatch env refs [p] [v] of | NONE => NONE
      | SOME env' => Pmatch env' refs ps vs
Proof
  Induct >> Cases_on`vs` >> simp[Pmatch_def] >>
  BasicProvers.CASE_TAC >>
  Cases_on`ps`>>simp[Pmatch_def]
QED

Theorem pmatch_imp_Pmatch = Q.prove(
  `(∀envC s p v env aenv.
      envC = aenv.c ⇒
      case pmatch envC s p v env of
      | Match env' =>
        ∃ext. env' = ext ++ env ∧
        Pmatch aenv s [p] [v] = SOME (aenv with v := nsAppend (alist_to_ns ext) aenv.v)
      | No_match => Pmatch aenv s [p] [v] = NONE
      | _ => T) ∧
    (∀envC s ps vs env aenv.
      envC = aenv.c ⇒
      case pmatch_list envC s ps vs env of
      | Match env' =>
        ∃ext. env' = ext ++ env ∧
        Pmatch aenv s ps vs = SOME (aenv with v := nsAppend (alist_to_ns ext) aenv.v)
      | No_match => Pmatch aenv s ps vs = NONE
      | _ => T)`,
  ho_match_mp_tac pmatch_ind >>
  rw[pmatch_def,Pmatch_def,write_def]
  >> TRY (rw[]>>NO_TAC)
  >- (
    BasicProvers.CASE_TAC >>
    BasicProvers.CASE_TAC >>
    BasicProvers.CASE_TAC >> fs[] >>
    BasicProvers.CASE_TAC >> fs[] >>
    TRY BasicProvers.CASE_TAC >> fs[] >>
    first_x_assum(qspec_then`aenv`mp_tac) >>
    simp[] >>
    BasicProvers.CASE_TAC >> fs[] >>
    rw [] \\ fs [])
  >- (
    BasicProvers.CASE_TAC >>
    BasicProvers.CASE_TAC >>
    BasicProvers.CASE_TAC >>
    fs[store_lookup_def] >>
    first_x_assum(qspec_then`aenv`mp_tac) \\
    simp[])
  >- (
    fs [AllCaseEqs()]
    \\ last_x_assum (qspec_then ‘(aenv with v := nsBind i v aenv.v)’ mp_tac) \\ fs []
    \\ CASE_TAC \\ fs []
    \\ strip_tac \\ fs []
    \\ Cases_on ‘aenv.v’
    \\ EVAL_TAC \\ rewrite_tac [APPEND,GSYM APPEND_ASSOC])
  >- (
    first_x_assum(qspec_then`aenv`mp_tac)>>simp[]>>
    BasicProvers.CASE_TAC >> fs[] >>
    simp[Once Pmatch_cons] >>
    BasicProvers.CASE_TAC >> fs[] >>
    simp[Once Pmatch_cons] >> rw[Pmatch_def] >>
    first_x_assum(qspec_then`aenv with v := nsAppend (alist_to_ns ext) aenv.v`mp_tac)>>simp[]>>
    BasicProvers.CASE_TAC >> simp[Once Pmatch_cons] >>
    rw[] \\ rw[]))
  |> SIMP_RULE std_ss []

Theorem Pmatch_SOME_const:
   ∀env refs ps vs env'.
      Pmatch env refs ps vs = SOME env' ⇒
      env'.c = env.c
Proof
  ho_match_mp_tac Pmatch_ind >> simp[Pmatch_def] >>
  rw[] >> BasicProvers.EVERY_CASE_TAC >> fs[] >>
  fs[write_def]
QED

Theorem pmatch_PMATCH_ROW_COND_No_match:
   EvalPatRel env a p pat ∧
    (∀vars. ¬PMATCH_ROW_COND pat (K T) xv vars) ∧
    a xv res ⇒
    pmatch env.c refs p res [] = No_match
Proof
  fs [PMATCH_ROW_COND_def] >>
  rw[EvalPatRel_def] >>
  first_x_assum(fn th => first_x_assum(strip_assume_tac o MATCH_MP th)) >>
  first_x_assum(qspec_then`refs`mp_tac) >>
  simp [evaluate_def] >>
  every_case_tac >> fs []
QED

Theorem pmatch_PMATCH_ROW_COND_Match:
   EvalPatRel env a p pat ∧
    PMATCH_ROW_COND pat (K T) xv vars ∧
    a xv res
    ⇒ ∃env2. pmatch env.c refs p res [] = Match env2
Proof
  rw[EvalPatRel_def,PMATCH_ROW_COND_def] >>
  first_x_assum(fn th => first_x_assum(strip_assume_tac o MATCH_MP th)) >>
  first_x_assum(qspec_then`refs`mp_tac) >>
  simp [evaluate_def] >>
  every_case_tac >>
  fs [pmatch_def,build_conv_def,do_con_check_def] >>
  metis_tac []
QED

Definition pmatch_no_type_error_def:
  pmatch_no_type_error envC a p <=>
    ALL_DISTINCT (pat_bindings p []) /\
    !x v refs.
       a x v ==> pmatch envC refs p v [] <> Match_type_error
End

Definition pmatch_all_no_type_error_def:
  pmatch_all_no_type_error envC a [] = T /\
  pmatch_all_no_type_error envC a ((p,e)::rows) =
    (pmatch_no_type_error envC a p /\
     pmatch_all_no_type_error envC a rows)
End

Theorem Eval_PMATCH_NIL:
   !b x xv a.
      Eval env x (a xv) ==>
      pmatch_all_no_type_error env.c a ([]:(pat # exp) list) /\
      (CONTAINER F ==>
       Eval env (Mat x []) (b (PMATCH xv [])))
Proof
  rw[CONTAINER_def,pmatch_all_no_type_error_def]
QED

Theorem pmatch_all_no_type_error_IMP_can_pmatch_all:
  pmatch_all_no_type_error env.c a ys /\ a x v ==>
  can_pmatch_all env.c refs (MAP FST ys) v
Proof
  Induct_on `ys`
  \\ fs [pmatch_all_no_type_error_def,can_pmatch_all_def,FORALL_PROD]
  \\ fs [pmatch_no_type_error_def]
  \\ metis_tac []
QED

Theorem Eval_PMATCH:
   !b a x xv.
      ALL_DISTINCT (pat_bindings p []) ⇒
      (∀v1 v2. pat v1 = pat v2 ⇒ v1 = v2) ⇒
      Eval env x (a xv) ⇒
      (p1 xv ⇒ Eval env (Mat x ys) (b (PMATCH xv yrs))) ⇒
      EvalPatRel env a p pat ⇒
      (∀env2 vars.
        EvalPatBind env a p pat vars env2 ∧ p2 vars ⇒
        Eval env2 e (b (res vars))) ⇒
      pmatch_all_no_type_error env.c a ys ⇒
      pmatch_all_no_type_error env.c a ((p,e)::ys) /\
      ((∀vars. CONTAINER (PMATCH_ROW_COND pat (K T) xv vars) ⇒ p2 vars) ∧
       ((∀vars. ¬CONTAINER (PMATCH_ROW_COND pat (K T) xv vars)) ⇒ p1 xv) ⇒
       Eval env (Mat x ((p,e)::ys)) (b (PMATCH xv ((PMATCH_ROW pat (K T) res)::yrs))))
Proof
  rpt gen_tac \\ rewrite_tac [AND_IMP_INTRO] \\ strip_tac
  \\ conj_asm1_tac
  THEN1
   (fs [pmatch_all_no_type_error_def,pmatch_no_type_error_def]
    \\ fs[EvalPatRel_def] \\ rw [] \\ res_tac
    \\ rename [`pmatch env.c refs2`]
    \\ pop_assum (qspec_then `refs2` strip_assume_tac)
    \\ fs [CaseEq"bool",evaluate_def,CaseEq"match_result"])
  \\ rpt (pop_assum mp_tac)
  \\ rw[Eval_def,CONTAINER_def]
  \\ rw[evaluate_def,PULL_EXISTS] \\ fs[]
  \\ first_x_assum(qspec_then`refs`strip_assume_tac)
  \\ reverse (Cases_on`∃vars. PMATCH_ROW_COND pat (K T) xv vars` >> fs[])
  THEN1
   (first_x_assum(qspec_then`refs`strip_assume_tac)
    \\ drule (GEN_ALL pmatch_PMATCH_ROW_COND_No_match)
    \\ rpt (disch_then drule) \\ rw []
    \\ simp [eval_rel_def,PULL_EXISTS]
    \\ fs [evaluate_def,pair_case_eq,result_case_eq,PULL_EXISTS]
    \\ fs [eval_rel_def,PULL_EXISTS]
    \\ qpat_x_assum `_ env [x] = _` assume_tac
    \\ fs [evaluate_def,pair_case_eq,result_case_eq] \\ rveq \\ fs []
    \\ drule evaluate_add_to_clock \\ fs []
    \\ disch_then (qspec_then `ck1'` assume_tac)
    \\ asm_exists_tac \\ fs []
    \\ qpat_x_assum `_ = (_,Rval v)` assume_tac
    \\ drule evaluate_add_to_clock \\ fs []
    \\ disch_then (qspec_then `ck1` assume_tac)
    \\ rfs [] \\ rveq \\ fs [] \\ rfs [CaseEq"bool"]
    \\ drule evaluate_match_add_to_clock \\ fs []
    \\ fs [state_component_equality]
    \\ simp[PMATCH_def,PMATCH_ROW_def]
    \\ drule pmatch_all_no_type_error_IMP_can_pmatch_all
    \\ disch_then drule \\ fs [])
  \\ drule (GEN_ALL pmatch_PMATCH_ROW_COND_Match)
  \\ rpt (disch_then drule) \\ strip_tac
  \\ first_x_assum(qspec_then`refs++refs'`strip_assume_tac) \\ fs[]
  \\ qpat_x_assum`p1 xv ⇒ $! _`kall_tac
  \\ fs[EvalPatRel_def]
  \\ first_x_assum(qspec_then`vars`mp_tac) \\ simp[] \\ strip_tac
  \\ first_x_assum(fn th => first_assum(strip_assume_tac o MATCH_MP th))
  \\ first_x_assum(qspec_then`refs++refs'`mp_tac)
  \\ fs[PMATCH_ROW_COND_def] \\ rveq
  \\ `EvalPatBind env a p pat vars (env with v := nsAppend (alist_to_ns env2) env.v)`
    by (
      simp[EvalPatBind_def]
      \\ qspecl_then[`refs++refs'`,`p`,`res'`,`[]`,`env`]
            mp_tac(CONJUNCT1 pmatch_imp_Pmatch)
      \\ simp[] \\ metis_tac[])
  \\ first_x_assum drule \\ simp[]
  \\ disch_then(qspec_then`refs++refs'`strip_assume_tac)
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ rpt strip_tac \\ fs [eval_rel_def,PULL_EXISTS,evaluate_def]
  \\ rfs [pair_case_eq,result_case_eq,PULL_EXISTS]
  \\ fs [EVAL ``do_con_check env.c NONE 0``]
  \\ fs [EVAL ``build_conv env.c NONE []``,bool_case_eq]
  \\ `vars' = vars` by (res_tac \\ fs []) \\ rveq \\ fs []
  \\ qpat_x_assum `_ env [x] = _` assume_tac
  \\ drule evaluate_add_to_clock \\ fs []
  \\ disch_then (qspec_then `ck1'` assume_tac)
  \\ asm_exists_tac \\ fs []
  \\ drule pmatch_all_no_type_error_IMP_can_pmatch_all
  \\ disch_then drule \\ fs []
  \\ qpat_x_assum `_ [e] = _` assume_tac
  \\ drule evaluate_add_to_clock \\ fs []
  \\ fs [state_component_equality]
  \\ simp[PMATCH_def,PMATCH_ROW_def,PMATCH_ROW_COND_def]
  \\ qsuff_tac `(some x. pat x = pat vars) = SOME vars` \\ simp []
  \\ simp[optionTheory.some_def] \\ metis_tac []
QED

Theorem PMATCH_option_case_rwt:
   ((case x of NONE => NONE
      | SOME (y1,y2) => P y1 y2) = SOME env2) <=>
    ?y1 y2. (x = SOME (y1,y2)) /\ (P y1 y2 = SOME env2)
Proof
  Cases_on `x` \\ fs [] \\ Cases_on `x'` \\ fs []
QED

Theorem PMATCH_SIMP:
   ((∀vars. ¬CONTAINER (vars = x)) = F) /\
    ((∀vars. ¬CONTAINER (x = vars)) = F) /\
    ((∀vars. ¬(vars = x)) = F) /\
    ((∀vars. ¬(x = vars)) = F)
Proof
  fs [CONTAINER_def]
QED

val _ = export_theory()
