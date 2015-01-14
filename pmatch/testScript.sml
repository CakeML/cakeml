open HolKernel boolLib bossLib lcsymtacs boolSimps
open determTheory ml_translatorTheory ml_translatorLib miscLib
open deepMatchesTheory deepMatchesLib

val _ = new_theory"test"

(* might need EvalMat (using evaluate_match) instead to only evaluate x once *)

(*
Eval_def
val EvalMat_def = Define`
  EvalMat xv env xs P ⇔
    ∃res. evaluate_match F env (0,empty_store) 
    type_of``evaluate_match``
*)

val EvalPatRel_def = Define`
  EvalPatRel env a p pat ⇔
    ∀x av. a x av ⇒
      evaluate_match F env (0,empty_store) av
        [(p,(Lit(Bool T)))] (Litv(Bool F))
        ((0,empty_store),Rval(Litv(Bool(∃vars. pat vars = x))))`

(* want version of pmatch that doesn't break apart an all_env, but does bindings with write *)
val EvalPatBind_def = Define`
  EvalPatBind env a p pat vars env2 ⇔
    ∃x av enve.
      a x av ∧
      pmatch (all_env_to_cenv env) empty_store p av (all_env_to_env env) = Match enve ∧
      (env2 = (all_env_to_menv env,all_env_to_cenv env,enve)) ∧
      (pat vars = x)`

val pmatch_PMATCH_ROW_COND_No_match = store_thm("pmatch_PMATCH_ROW_COND_No_match",
  ``EvalPatRel env a p pat ∧
    (∀vars. ¬PMATCH_ROW_COND pat (K T) xv vars) ∧
    a xv res ⇒
    pmatch (all_env_to_cenv env) empty_store p res (all_env_to_env env) = No_match``,
  rw[EvalPatRel_def] >>
  first_x_assum(fn th => first_x_assum(strip_assume_tac o MATCH_MP th)) >>
  fs[Eval_def,Once evaluate_cases] >>
  `∃menv cenv eenv. env = (menv,cenv,eenv)` by METIS_TAC[PAIR] >> fs[] >>
  simp[all_env_to_cenv_def,all_env_to_env_def] >> fs[write_def] >>
  fs[Once evaluate_cases,lookup_var_id_def] >>
  rfs[PMATCH_ROW_COND_def])

val pmatch_PMATCH_ROW_COND_Match = store_thm("pmatch_PMATCH_ROW_COND_Match",
  ``EvalPatRel env a p pat ∧
    PMATCH_ROW_COND pat (K T) xv vars ∧
    a xv res
    ⇒ ∃env2. pmatch (all_env_to_cenv env) empty_store p res (all_env_to_env env) = Match env2``,
  rw[EvalPatRel_def,PMATCH_ROW_COND_def] >>
  first_x_assum(fn th => first_x_assum(strip_assume_tac o MATCH_MP th)) >>
  fs[Once evaluate_cases,all_env_to_cenv_def,all_env_to_env_def] >>
  fs[Once evaluate_cases])

val Eval_PMATCH_NIL = store_thm("Eval_PMATCH_NIL",
  ``CONTAINER F ⇒
    Eval env (Mat x []) (b (PMATCH xv []))``,
  rw[CONTAINER_def])

val Eval_PMATCH = store_thm("Eval_PMATCH",
  ``ALL_DISTINCT (pat_bindings p []) ⇒
    (∀v1 v2. pat v1 = pat v2 ⇒ v1 = v2) ⇒
    (p0 ⇒ Eval env x (a xv)) ⇒
    (p1 xv ⇒ Eval env (Mat x ys) (b (PMATCH xv yrs))) ⇒
    EvalPatRel env a p pat ⇒
    (∀vars env2.
      EvalPatBind env a p pat vars env2 ∧ p2 vars ⇒
      Eval env2 e (b (res vars))) ⇒
    p0 ∧
    (∀vars. PMATCH_ROW_COND pat (K T) xv vars ⇒ p2 vars) ∧
    (∀vars. ¬PMATCH_ROW_COND pat (K T) xv vars ⇒ p1 xv) ⇒
    Eval env (Mat x ((p,e)::ys)) (b (PMATCH xv ((PMATCH_ROW pat (K T) res)::yrs)))``,
  rw[Eval_def] >>
  rw[Once evaluate_cases,PULL_EXISTS] >> fs[] >>
  first_assum(match_exists_tac o concl) >> simp[] >>
  rw[Once evaluate_cases,PULL_EXISTS] >>
  `∃menv cenv eenv. env = (menv,cenv,eenv)` by METIS_TAC[PAIR] >> fs[] >>
  Cases_on`∃vars. PMATCH_ROW_COND pat (K T) xv vars` >> fs[] >- (
    imp_res_tac pmatch_PMATCH_ROW_COND_Match >>
    ntac 3 (pop_assum kall_tac) >>
    fs[EvalPatRel_def] >>
    first_x_assum(qspec_then`vars`mp_tac)>>simp[] >>
    qpat_assum`p1 xv ⇒ X`kall_tac >>
    fs[EvalPatBind_def,PMATCH_ROW_COND_def,PULL_EXISTS] >>
    first_x_assum(qspec_then`vars`mp_tac)>>simp[] >> strip_tac >>
    first_x_assum(fn th => first_assum(strip_assume_tac o MATCH_MP th)) >>
    srw_tac[DNF_ss][] >> disj1_tac >>
    fs[all_env_to_cenv_def,all_env_to_env_def] >>
    fs[GSYM AND_IMP_INTRO] >>
    first_x_assum(fn th => first_assum(strip_assume_tac o MATCH_MP th)) >>
    rfs[] >>
    `(∃vars'. pat vars' = pat vars) = T` by metis_tac[] >> fs[] >> rfs[] >>
    simp[PMATCH_def,PMATCH_ROW_def,PMATCH_ROW_COND_def] >>
    `(some x. pat x = pat vars) = SOME vars` by (
      simp[optionTheory.some_def] >>
      METIS_TAC[] ) >>
    simp[] >> fs[all_env_to_menv_def] >>
    METIS_TAC[]) >>
  qpat_assum`evaluate F X Y (Mat A B) R`mp_tac >>
  simp[Once evaluate_cases] >> strip_tac >>
  imp_res_tac (CONJUNCT1 big_exp_determ) >> fs[] >> rw[] >>
  srw_tac[DNF_ss][] >> disj2_tac >>
  simp[PMATCH_def,PMATCH_ROW_def] >>
  imp_res_tac pmatch_PMATCH_ROW_COND_No_match >>
  fs[all_env_to_cenv_def,all_env_to_env_def] >>
  METIS_TAC[])

(* TODO: now, use the above two theorems to do the tm example below manually *)

(*

val () = set_trace"use pmatch_pp"0
val () = register_type``:'a list``
val () = show_assums := true

val tm = ``case x of (y::ys) => y + (3:num)``

val pth = (PMATCH_INTRO_CONV THENC PMATCH_SIMP_CONV) tm
val ptm = rhs(concl pth)

fun to_pattern tm =
  if can(match_term``Var(Short x)``)tm then
    ``Pvar^(rand(rand tm))``
  else if can(match_term``Con name args``) tm then
    let
      val (_,[name,args]) = strip_comb tm
      val (args,_) = listSyntax.dest_list args
      val args = listSyntax.mk_list(map to_pattern args,``:pat``)
    in
      ``Pcon ^name ^args``
    end
  else tm

val xth = hol2deep (rand(rator(ptm)))
val x = xth |> concl |> rator |> rand
val pat = hol2deep (ptm |> rand |> rator |> rand |> strip_comb |> snd |> el 1 |> dest_pabs |> snd)
          |> concl |> rator |> rand |> to_pattern
val eth = hol2deep (ptm |> rand |> rator |> rand |> strip_comb |> snd |> el 3 |> dest_pabs |> snd)
val exp = eth |> concl |> rator |> rand
val Eval_Mat =
  ``Eval env (Mat e pats) P``
  |> (REWR_CONV Eval_def THENC
      ONCE_REWRITE_CONV [evaluate_cases] THENC
      SIMP_CONV (srw_ss())[PULL_EXISTS])

val evaluate_match_Conv =
  ``evaluate_match c x env args
       ((Pcon xx pats,exp2)::pats2) errv (yyy,Rval y)``
  |> (ONCE_REWRITE_CONV [evaluate_cases] THENC
      SIMP_CONV (srw_ss()) [pmatch_def])
val evaluate_match_rw = prove(
  ``evaluate_match c (menv,cenv,env) (e1,e2) args
      ((Pcon xx pats,exp2)::pats2) errv (yyy,Rval y) <=>
    ALL_DISTINCT (pat_bindings (Pcon xx pats) []) /\
    case pmatch cenv e2 (Pcon xx pats) args env of
    | No_match =>
        evaluate_match c (menv,cenv,env) (e1,e2) args pats2 errv (yyy,Rval y)
    | Match env7 =>
        evaluate c (menv,cenv,env7) (e1,e2) exp2 (yyy,Rval y)
    | _ => F``,
  SIMP_TAC std_ss [evaluate_match_Conv
    |> Q.INST [`x`|->`(menv,cenv,e)`,`env`|->`(e1,e2)`]
    |> Q.INST [`e`|->`env`]
    |> SIMP_RULE std_ss []]
  \\ Cases_on `pmatch cenv e2 (Pcon xx pats) args env`
  \\ FULL_SIMP_TAC (srw_ss()) []);

val thm = prove(
  ``^(concl xth) ⇒
    Eval env (Mat ^x [(^pat,^exp)]) (NUM ^ptm)``,
  strip_tac >>
  REWRITE_TAC[Eval_Mat] >>
  FULL_SIMP_TAC pure_ss [Eval_def] >>
  first_assum(match_exists_tac o concl) >>
  ASM_SIMP_TAC bool_ss [] >>
  `∃menv cenv env1. env = (menv,cenv,env1)` by METIS_TAC[pair_CASES] >>
  BasicProvers.VAR_EQ_TAC >>
  REWRITE_TAC[evaluate_match_rw] >>
  simp[pat_bindings_def] >>
  REWRITE_TAC[PMATCH_def,PMATCH_ROW_def] >>
  simp[Once evaluate_cases]
  optionTheory.some_intro
  f"some"

val Eval_PMATCH = store_thm("Eval_PMATCH",
  ``Eval env x (P v) ⇒
    LIST_REL (λ((p,e),r).???) pes rows
    Eval env (Mat x pes) (Q (PMATCH x rows)``
type_of``evaluate_match``
evaluate_rules

type_of ``PMATCH x``
PMATCH_def
PMATCH_ROW_def
type_of``PMATCH_ROW``
*)

val _ = export_theory()
