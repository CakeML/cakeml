open HolKernel boolLib bossLib lcsymtacs boolSimps
open determTheory ml_translatorTheory ml_translatorLib miscLib
open deepMatchesTheory deepMatchesLib

val _ = new_theory"test"

(* might need EvalMat (using evaluate_match) instead to only evaluate x once *)

val EvalPatRel_def = Define`
  EvalPatRel env a p pat ⇔
    ∀x av. a x av ⇒
      evaluate_match F env (0,empty_store) av
        [(p,(Lit(Unit)))] ARB
        ((0,empty_store),if ∃vars. pat vars = x then Rval(Litv(Unit)) else Rerr(Rraise ARB))`
val Pmatch_def = tDefine"Pmatch"`

  (Pmatch env [] [] = SOME env) ∧
  (Pmatch env (p1::p2::ps) (v1::v2::vs) =
     case Pmatch env [p1] [v1] of | NONE => NONE
     | SOME env' => Pmatch env' (p2::ps) (v2::vs)) ∧
  (Pmatch env [Pvar x] [v] = SOME (write x v env)) ∧
  (Pmatch env [Plit l] [Litv l'] =
     if l = l' then SOME env else NONE) ∧
  (Pmatch env [Pcon (SOME n) ps] [Conv (SOME (n',t')) vs] =
     case lookup_alist_mod_env n (all_env_to_cenv env) of | NONE => NONE
     | SOME (l,t) =>
       if same_tid t t' ∧ LENGTH ps = l ∧ same_ctor (id_to_n n, t) (n',t') then
           Pmatch env ps vs
       else NONE) ∧
  (Pmatch env [Pcon NONE ps] [Conv NONE vs] =
     if LENGTH ps = LENGTH vs then
       Pmatch env ps vs
     else NONE) ∧
  (Pmatch env _ _ = NONE)`
(WF_REL_TAC`measure (pat1_size o FST o SND)`)

val Pmatch_ind = theorem"Pmatch_ind"

val EvalPatBind_def = Define`
  EvalPatBind env a p pat vars env2 ⇔
    ∃x av.
      a x av ∧
      (Pmatch env [p] [av] = SOME env2) ∧
      (pat vars = x)`

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
      all_env_to_menv env' = all_env_to_menv env ∧
      all_env_to_cenv env' = all_env_to_cenv env``,
  ho_match_mp_tac Pmatch_ind >> simp[Pmatch_def] >>
  rw[] >> BasicProvers.EVERY_CASE_TAC >> fs[] >>
  PairCases_on`env`>>
  fs[write_def,all_env_to_cenv_def,all_env_to_menv_def])

val pmatch_imp_Pmatch = prove(
  ``(∀envC s p v env.
      s = empty_store ⇒
      case pmatch envC s p v env of
      | Match env' =>
        Pmatch (envM,envC,env) [p] [v] = SOME (envM,envC,env')
      | _ => Pmatch (envM,envC,env) [p] [v] = NONE) ∧
    (∀envC s ps vs env.
      s = empty_store ⇒
      case pmatch_list envC s ps vs env of
      | Match env' =>
        Pmatch (envM,envC,env) ps vs = SOME (envM,envC,env')
      | _ => Pmatch (envM,envC,env) ps vs = NONE)``,
  ho_match_mp_tac pmatch_ind >>
  rw[pmatch_def,Pmatch_def,write_def,all_env_to_cenv_def]
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
    BasicProvers.CASE_TAC >> fs[] >>
    simp[Once Pmatch_cons] >>
    BasicProvers.CASE_TAC >> fs[] >>
    simp[Once Pmatch_cons] )
  >- (
    Cases_on`v110`>>simp[Pmatch_def]))
  |> SIMP_RULE std_ss []
  |> curry save_thm "pmatch_imp_Pmatch"

val Pmatch_imp_pmatch = store_thm("Pmatch_imp_pmatch",
  ``∀env ps vs env'.
      (Pmatch env ps vs = SOME env' ⇒
       pmatch_list (all_env_to_cenv env) empty_store ps vs (all_env_to_env env) =
         Match (all_env_to_env env')) ∧
      (Pmatch env ps vs = NONE ⇒
       ∀env2.
       pmatch_list (all_env_to_cenv env) empty_store ps vs (all_env_to_env env) ≠
         Match env2)``,
  ho_match_mp_tac Pmatch_ind >>
  simp[Pmatch_def,pmatch_def] >> rw[] >>
  `∃envM envC envE. env = (envM,envC,envE)` by METIS_TAC[PAIR] >>
  fs[all_env_to_cenv_def,all_env_to_menv_def,all_env_to_env_def,write_def] >>
  BasicProvers.CASE_TAC >> fs[] >>
  BasicProvers.EVERY_CASE_TAC >> rfs[] >> rw[] >>
  imp_res_tac Pmatch_SOME_const >>
  fs[all_env_to_cenv_def,all_env_to_menv_def,all_env_to_env_def,write_def] >>
  rfs[] >>
  Cases_on`v20`>>fs[pmatch_def] >>
  BasicProvers.EVERY_CASE_TAC >> fs[store_lookup_def,empty_store_def])

val pmatch_PMATCH_ROW_COND_No_match = store_thm("pmatch_PMATCH_ROW_COND_No_match",
  ``EvalPatRel env a p pat ∧
    (∀vars. ¬PMATCH_ROW_COND pat (K T) xv vars) ∧
    a xv res ⇒
    Pmatch env [p] [res] = NONE``,
  rw[EvalPatRel_def] >>
  first_x_assum(fn th => first_x_assum(strip_assume_tac o MATCH_MP th)) >>
  `∃envM envC envE. env = (envM,envC,envE)` by METIS_TAC[PAIR] >> fs[] >>
  qspecl_then[`envC`,`p`,`res`,`envE`]strip_assume_tac(CONJUNCT1 pmatch_imp_Pmatch) >>
  fs[Eval_def,Once evaluate_cases] >> rfs[] >>
  rpt(pop_assum mp_tac) >>
  rw[Once evaluate_cases,PMATCH_ROW_COND_def])

val pmatch_PMATCH_ROW_COND_Match = store_thm("pmatch_PMATCH_ROW_COND_Match",
  ``EvalPatRel env a p pat ∧
    PMATCH_ROW_COND pat (K T) xv vars ∧
    a xv res
    ⇒ ∃env2. Pmatch env [p] [res] = SOME env2``,
  rw[EvalPatRel_def,PMATCH_ROW_COND_def] >>
  first_x_assum(fn th => first_x_assum(strip_assume_tac o MATCH_MP th)) >>
  `∃envM envC envE. env = (envM,envC,envE)` by METIS_TAC[PAIR] >> fs[] >>
  qspecl_then[`envC`,`p`,`res`,`envE`]strip_assume_tac(CONJUNCT1 pmatch_imp_Pmatch) >>
  fs[Once evaluate_cases] >> rfs[] >>
  BasicProvers.EVERY_CASE_TAC >> fs[] >>
  fs[Once evaluate_cases] >>
  PROVE_TAC[])

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
    ((∀vars. ¬PMATCH_ROW_COND pat (K T) xv vars) ⇒ p1 xv) ⇒
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
    imp_res_tac Pmatch_imp_pmatch >>
    imp_res_tac Pmatch_SOME_const >>
    fs[all_env_to_cenv_def,all_env_to_env_def,pmatch_def,all_env_to_menv_def] >>
    qpat_assum`X = Match Y` mp_tac >> BasicProvers.CASE_TAC >>
    fs[GSYM AND_IMP_INTRO] >>
    first_x_assum(fn th => first_assum(strip_assume_tac o MATCH_MP th)) >>
    rfs[] >>
    `(∃vars'. pat vars' = pat vars) = T` by metis_tac[] >> fs[] >> rfs[] >>
    simp[PMATCH_def,PMATCH_ROW_def,PMATCH_ROW_COND_def] >>
    `(some x. pat x = pat vars) = SOME vars` by (
      simp[optionTheory.some_def] >>
      METIS_TAC[] ) >>
    simp[] >> fs[all_env_to_menv_def] >> rw[] >>
    PairCases_on`env2`>> fs[all_env_to_cenv_def,all_env_to_env_def,pmatch_def,all_env_to_menv_def] >>
    METIS_TAC[]) >>
  qpat_assum`evaluate F X Y (Mat A B) R`mp_tac >>
  simp[Once evaluate_cases] >> strip_tac >>
  imp_res_tac (CONJUNCT1 big_exp_determ) >> fs[] >> rw[] >>
  srw_tac[DNF_ss][] >> disj2_tac >>
  simp[PMATCH_def,PMATCH_ROW_def] >>
  imp_res_tac pmatch_PMATCH_ROW_COND_No_match >>
  imp_res_tac Pmatch_imp_pmatch >>
  fs[all_env_to_cenv_def,all_env_to_env_def,pmatch_def] >>
  pop_assum mp_tac >> BasicProvers.CASE_TAC >- METIS_TAC[] >>
  fs[EvalPatRel_def] >>
  first_x_assum(fn th => first_x_assum(mp_tac o MATCH_MP th)) >>
  simp[Once evaluate_cases] >> rw[])

val () = set_trace"use pmatch_pp"0
val () = register_type``:'a list``
val () = show_assums := true
val () = computeLib.add_funs [pat_bindings_def]

val tm = ``case x of (y::ys) => y + (3:num)``

val pth = (PMATCH_INTRO_CONV THENC PMATCH_SIMP_CONV) tm
val ptm = rhs(concl pth)
val rows = rand ptm |> listSyntax.dest_list |> fst
val row1 = el 1 rows

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
val xv = xth |> concl |> rand |> rand

val base_case =
  Eval_PMATCH_NIL |> Q.GENL[`x`,`xv`] |> ISPECL [xv,x]

val pat = row1 |> strip_comb |> snd |> el 1
val p = hol2deep (pat |> dest_pabs |> snd)
          |> concl |> rator |> rand |> to_pattern
val ALL_DISTINCT_th =
  ``ALL_DISTINCT (pat_bindings ^p [])``
  |> EVAL |> EQT_ELIM
val pat_11 =
  ``∀v1 v2. ^pat v1 = ^pat v2 ⇒ v1 = v2``
  |> SIMP_CONV (std_ss++listSimps.LIST_ss) [FORALL_PROD]
  |> EQT_ELIM
val th1 = MATCH_MP Eval_PMATCH ALL_DISTINCT_th
val th2 = MATCH_MP th1 pat_11
val th3 = MATCH_MP th2 (DISCH_ALL xth)
val th4 = HO_MATCH_MP th3 base_case

val res = row1 |> strip_comb |> snd |> el 3
val eth = hol2deep (res |> dest_pabs |> snd)
val e = eth |> concl |> rator |> rand
val b = eth |> concl |> rand |> rator

val th5 = Q.GENL[`res`,`e`,`b`]th4 |> ISPECL [b,e,res]

val asms =
  hol2deep (pat |> dest_pabs |> snd)
  |> hyp
  |> filter(can (assert (same_const``lookup_cons``) o fst o strip_comb o lhs))
val gtm = th5 |> concl |> dest_imp |> fst
(*
  set_goal(asms,gtm)
*)
val gth = TAC_PROOF((asms,gtm),
  `∃x y z. env = (x,y,z)` by METIS_TAC[PAIR] >>
  simp[EvalPatRel_def,Once evaluate_cases,ALL_DISTINCT_th] >>
  fs[lookup_cons_def] >>
  Cases >> simp[LIST_TYPE_def,pmatch_def,same_tid_def,same_ctor_def,id_to_n_def,EXISTS_PROD] >- (
    simp[Once evaluate_cases]) >>
  simp[PULL_EXISTS,pmatch_def,same_tid_def,same_ctor_def,id_to_n_def,EXISTS_PROD] >>
  simp[Once evaluate_cases])

val th6 = MATCH_MP th5 gth

(*
val p2 =
  hyp eth |> list_mk_conj |> curry mk_pabs(res |> dest_pabs |> fst)
*)
val p2 = mk_pabs(res |> dest_pabs |> fst, T) (* don't know what this should be *)

val th7 = Q.GEN`p2` th6 |> SPEC p2

val gtm2 = th7 |> concl |> dest_imp |> fst
(*
  set_goal(asms,gtm2)
*)
val gth2 = TAC_PROOF((asms,gtm2),
  `∃x y z. env = (x,y,z)` by METIS_TAC[PAIR] >>
  simp[EvalPatBind_def,all_env_to_cenv_def,all_env_to_env_def,PULL_EXISTS,all_env_to_menv_def] >>
  simp[UNCURRY,LIST_TYPE_def,PULL_EXISTS] >>
  fs[lookup_cons_def] >>
  simp[Pmatch_def,all_env_to_cenv_def,same_tid_def,same_ctor_def,id_to_n_def] >>
  simp[Eval_def] >>
  simp[Once evaluate_cases,PULL_EXISTS] >>
  simp[Once evaluate_cases,PULL_EXISTS] >>
  simp[Once evaluate_cases,PULL_EXISTS,lookup_var_id_def,write_def] >>
  simp[Once evaluate_cases,PULL_EXISTS] >>
  simp[Once evaluate_cases,PULL_EXISTS] >>
  simp[Once evaluate_cases,PULL_EXISTS] >>
  simp[do_app_def,NUM_def,INT_def,opn_lookup_def] >>
  rw[INT_ADD])

val th8 = MATCH_MP th7 gth2

val th9 = th8
  |> SIMP_RULE std_ss [PMATCH_ROW_COND_def,FORALL_PROD,CONTAINER_def]
  |> ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]
  |> C MATCH_MP xth
  |> CONV_RULE(LAND_CONV(STRIP_QUANT_CONV SYM_CONV THENC REWR_CONV(GSYM CONTAINER_def)))
  |> UNDISCH

val intro_K_T =
  ``^(mk_pabs(res |> dest_pabs |> fst,T)) = K T``
  |> SIMP_CONV std_ss [FUN_EQ_THM,FORALL_PROD]
  |> EQT_ELIM

val th10 =
  th9 |> ONCE_REWRITE_RULE[pth |> REWRITE_RULE[intro_K_T] |> SYM]

val _ = save_thm("example",th10)

val _ = export_theory()
