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
        ((0,empty_store),
         if ∃vars. pat vars = x
         then Rval(Litv(Unit)) else Rerr(Rraise ARB))`

val Pmatch_def = tDefine"Pmatch"`
  (Pmatch env [] [] = SOME env) ∧
  (Pmatch env (p1::p2::ps) (v1::v2::vs) =
     case Pmatch env [p1] [v1] of | NONE => NONE
     | SOME env' => Pmatch env' (p2::ps) (v2::vs)) ∧
  (Pmatch env [Pvar x] [v] = SOME (write x v env)) ∧
  (Pmatch env [Plit l] [Litv l'] =
     if l = l' then SOME env else NONE) ∧
  (Pmatch env [Pcon (SOME n) ps] [Conv (SOME (n',t')) vs] =
     case lookup_alist_mod_env n (all_env_to_cenv env) of
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
    (∀env2 vars.
      EvalPatBind env a p pat vars env2 ∧ p2 vars ⇒
      Eval env2 e (b (res vars))) ⇒
    p0 ==>
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
    `(∃vars'. pat vars' = pat vars) = T` by metis_tac[] >>
    fs[] >> rfs[] >>
    simp[PMATCH_def,PMATCH_ROW_def,PMATCH_ROW_COND_def] >>
    `(some x. pat x = pat vars) = SOME vars` by (
      simp[optionTheory.some_def] >>
      METIS_TAC[] ) >>
    simp[] >> fs[all_env_to_menv_def] >> rw[] >>
    PairCases_on`env2`>>
    fs[all_env_to_cenv_def,all_env_to_env_def,
       pmatch_def,all_env_to_menv_def] >>
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

val PMATCH_option_case_rwt = store_thm("PMATCH_option_case_rwt",
  ``((case x of NONE => NONE
      | SOME (y1,y2) => P y1 y2) = SOME env2) <=>
    ?y1 y2. (x = SOME (y1,y2)) /\ (P y1 y2 = SOME env2)``,
  Cases_on `x` \\ fs [] \\ Cases_on `x'` \\ fs []);

val () = set_trace "use pmatch_pp" 0
val () = register_type``:'a list``
val () = show_assums := true
val () = computeLib.add_funs [pat_bindings_def]

local
  val pat = ``(PMATCH_ROW f1 f2):('a -> 'c) -> 'b -> 'c option``
  fun K_T_CONV tm =
    if not (can (match_term pat) tm) then NO_CONV tm else
    if aconv (snd (dest_pabs (rand tm))) T then let
      val t = combinSyntax.mk_K(T,fst (dest_pabs (rand tm))) |> rator
      val goal = mk_eq(rand tm,t)
      val lemma = TAC_PROOF(([],goal),fs [FUN_EQ_THM,FORALL_PROD])
      in (RAND_CONV (fn tm => lemma)) tm end
    else NO_CONV tm
in
  val PMATCH_ROW_K_T_INTRO_CONV = DEPTH_CONV K_T_CONV
end;

local
  val pmatch_pat = ``PMATCH x (l :('a -> 'b option) list)``
  val pmatch_row_pat =
    ``(PMATCH_ROW (f1:'a->'b) (K T) f3):'b -> 'c option``
in
  fun dest_pmatch_row_K_T tm =
    if can (match_term pmatch_row_pat) tm then let
      val (ixy,z) = dest_comb tm
      val (ix,y) = dest_comb ixy
      val (i,x) = dest_comb ix
      in (x,z) end
    else failwith "not a PMATCH_ROW with K T"
  fun dest_pmatch_K_T tm =
    if can (match_term pmatch_pat) tm then let
      val (xy,z) = dest_comb tm
      val (x,y) = dest_comb xy
      in (y,map dest_pmatch_row_K_T (fst (listSyntax.dest_list z))) end
    else failwith "not a PMATCH"
end

val lookup_cons_pat = ``lookup_cons n env = x``
val prove_EvalPatRel_fail = ref T;
val goal = !prove_EvalPatRel_fail;

fun prove_EvalPatRel goal = let
  val asms =
    goal |> rand |> dest_pabs |> snd |> hol2deep |> hyp
         |> filter (can (match_term lookup_cons_pat))
  val pat = ``~(x = y:'a)``
  fun tac (hs,gg) = let
    val find_neg = find_term (can (match_term pat))
    val tm = find_neg (first (can find_neg) hs)
    in (Cases_on `^(tm |> rand |> rand)` \\ fs []) (hs,gg) end
  (*
    set_goal(asms,goal)
  *)
  val th = TAC_PROOF((asms,goal),
    PairCases_on `env` >>
    simp[EvalPatRel_def,EXISTS_PROD] >>
    SRW_TAC [] [] \\ fs [] >>
    POP_ASSUM MP_TAC >>
    REPEAT tac
    \\ CONV_TAC ((RATOR_CONV o RAND_CONV) EVAL)
    \\ REPEAT STRIP_TAC \\ fs [] >>
    fs[Once evaluate_cases] >>
    fs[lookup_cons_def] >>
    simp[LIST_TYPE_def,pmatch_def,same_tid_def,
         same_ctor_def,id_to_n_def,EXISTS_PROD,
         pat_bindings_def] >>
    fs[Once evaluate_cases])
  in th end handle HOL_ERR e =>
  (prove_EvalPatRel_fail := goal;
   failwith "prove_EvalPatRel failed");

val prove_EvalPatBind_fail = ref T;
val goal = !prove_EvalPatBind_fail;

fun prove_EvalPatBind goal = let
  val (vars,rhs_tm) = repeat (snd o dest_forall) goal
                      |> rand |> rand |> rand |> rator
                      |> dest_pabs
  val res = hol2deep rhs_tm
  val exp = res |> concl |> rator |> rand
  val th = D res
  val th = CONV_RULE ((RATOR_CONV o RAND_CONV)
              (PairRules.UNPBETA_CONV vars)) th
  val p = th |> concl |> dest_imp |> fst |> rator
  val p2 = goal |> dest_forall |> snd |> dest_forall |> snd
                |> dest_imp |> fst |> rand |> rator
  val new_goal = goal |> subst [``e:exp``|->exp,p2 |-> p]
  (*
    set_goal([],new_goal)
  *)
  val th = TAC_PROOF (([],new_goal),
    STRIP_TAC
    \\ fs [FORALL_PROD] \\ REPEAT STRIP_TAC
    \\ MATCH_MP_TAC (D res)
    \\ fs [EvalPatBind_def,Pmatch_def]
    \\ REPEAT (POP_ASSUM MP_TAC)
    \\ CONV_TAC ((RATOR_CONV o RAND_CONV) EVAL)
    \\ STRIP_TAC \\ fs [] \\ rfs []
    \\ fs [Pmatch_def,PMATCH_option_case_rwt]
    \\ SRW_TAC [] [Eval_Var_SIMP]
    \\ SRW_TAC [] [Eval_Var_SIMP]
    \\ EVAL_TAC)
  in th end handle HOL_ERR e =>
  (prove_EvalPatBind_fail := goal;
   failwith "prove_EvalPatBind failed");

fun to_pattern tm =
  if can(match_term``Var(Short x)``)tm then
    ``Pvar ^(rand (rand tm))``
  else if can(match_term``Con name args``) tm then
    let
      val (_,xs) = strip_comb tm
      val name = el 1 xs
      val args = el 2 xs
      val (args,_) = listSyntax.dest_list args
      val args = listSyntax.mk_list(map to_pattern args,``:pat``)
    in
      ``Pcon ^name ^args``
    end
  else tm

fun pmatch2deep tm = let
  val (x,ts) = dest_pmatch_K_T tm
  val x_res = hol2deep x |> D
  val x_type = type_of x
  val x_inv = get_type_inv x_type
  val pmatch_type = type_of tm
  val pmatch_inv = get_type_inv pmatch_type
  val x_exp = x_res |> UNDISCH |> concl |> rator |> rand
  val nil_lemma = Eval_PMATCH_NIL
                  |> Q.GEN `b` |> ISPEC pmatch_inv
                  |> Q.GEN `x` |> ISPEC x_exp
                  |> Q.GEN `xv` |> ISPEC x
                  |> D
  val cons_lemma = Eval_PMATCH
                   |> Q.GEN `b` |> ISPEC pmatch_inv
                   |> Q.GEN `a` |> ISPEC x_inv
  fun prove_hyp conv th =
    MP (CONV_RULE ((RATOR_CONV o RAND_CONV) conv) th) TRUTH
  fun trans [] = nil_lemma
    | trans ((pat,rhs_tm)::xs) = let
    (*
    val ((pat,rhs_tm)::xs) = ts
    *)
    val th = trans xs
    val p = pat |> dest_pabs |> snd |> hol2deep
                |> concl |> rator |> rand |> to_pattern
    val lemma = cons_lemma |> Q.GEN `p` |> ISPEC p
    val lemma = prove_hyp EVAL lemma
    val lemma = lemma |> Q.GEN `pat` |> ISPEC pat
    val lemma = prove_hyp (SIMP_CONV (srw_ss()) [FORALL_PROD]) lemma
    val lemma = MATCH_MP lemma x_res
    val th = D th |> CONV_RULE ((RATOR_CONV o RAND_CONV) (UNBETA_CONV x))
    val th = MATCH_MP lemma th
    val goal = fst (dest_imp (concl th))
    val th = MP th (prove_EvalPatRel goal)
    val th = th |> Q.GEN `res` |> ISPEC rhs_tm
    val goal = fst (dest_imp (concl th))
    val th = MATCH_MP th (prove_EvalPatBind goal)
    val th = UNDISCH th
    val th = CONV_RULE ((RATOR_CONV o RAND_CONV)
          (SIMP_CONV std_ss [FORALL_PROD,PMATCH_ROW_COND_def])) th
    val th = UNDISCH_ALL th
    in th end
  in trans ts end

val tm = ``case f x of (t::y::ys) => t + y + (3:num) | _ => 5``
val pth = (PMATCH_INTRO_CONV THENC PMATCH_SIMP_CONV
           THENC PMATCH_ROW_K_T_INTRO_CONV) tm
val tm = rhs(concl pth)

val example = save_thm("example", pmatch2deep tm)

val _ = export_theory()
