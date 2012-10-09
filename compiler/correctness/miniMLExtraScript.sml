open HolKernel bossLib boolLib boolSimps alistTheory listTheory rich_listTheory pred_setTheory lcsymtacs SatisfySimps
open MiniMLTheory MiniMLTerminationTheory miscTheory compileTerminationTheory
val _ = new_theory "miniMLExtra"

val lookup_ALOOKUP = store_thm(
"lookup_ALOOKUP",
``lookup = combin$C ALOOKUP``,
fs[FUN_EQ_THM] >> gen_tac >> Induct >- rw[] >> Cases >> rw[])
val _ = export_rewrites["lookup_ALOOKUP"];

val find_recfun_ALOOKUP = store_thm(
"find_recfun_ALOOKUP",
``find_recfun = combin$C ALOOKUP``,
rw[FUN_EQ_THM] >>
qmatch_rename_tac `find_recfun n funs = ALOOKUP funs n`[] >>
qid_spec_tac `n` >>
Induct_on `funs` >- rw[find_recfun_def] >>
qx_gen_tac `d` >>
PairCases_on `d` >>
rw[find_recfun_def])
val _ = export_rewrites["find_recfun_ALOOKUP"]

val pat_vars_def = tDefine "pat_vars"`
(pat_vars (Pvar v) = {v}) ∧
(pat_vars (Plit l) = {}) ∧
(pat_vars (Pcon c ps) = BIGUNION (IMAGE pat_vars (set ps)))`(
WF_REL_TAC `measure pat_size` >>
srw_tac[ARITH_ss][pat1_size_thm] >>
Q.ISPEC_THEN `pat_size` imp_res_tac SUM_MAP_MEM_bound >>
srw_tac[ARITH_ss][])
val _ = export_rewrites["pat_vars_def"]

val FINITE_pat_vars = store_thm("FINITE_pat_vars",
  ``∀p. FINITE (pat_vars p)``,
  ho_match_mp_tac (theorem"pat_vars_ind") >>
  rw[] >> res_tac)
val _ = export_rewrites["FINITE_pat_vars"]

val FV_def = tDefine "FV"`
(FV (Raise _) = {}) ∧
(FV (Lit _) = {}) ∧
(FV (Con _ ls) = BIGUNION (IMAGE FV (set ls))) ∧
(FV (Var x) = {x}) ∧
(FV (Fun x e) = FV e DIFF {x}) ∧
(FV (App _ e1 e2) = FV e1 ∪ FV e2) ∧
(FV (Log _ e1 e2) = FV e1 ∪ FV e2) ∧
(FV (If e1 e2 e3) = FV e1 ∪ FV e2 ∪ FV e3) ∧
(FV (Mat e pes) = FV e ∪ BIGUNION (IMAGE (λ(p,e). FV e DIFF pat_vars p) (set pes))) ∧
(FV (Let x e b) = FV e ∪ (FV b DIFF {x})) ∧
(FV (Letrec defs b) = BIGUNION (IMAGE (λ(y,x,e). FV e DIFF ({x} ∪ (IMAGE FST (set defs)))) (set defs)) ∪ (FV b DIFF (IMAGE FST (set defs))))`
(WF_REL_TAC `measure exp_size` >>
srw_tac[ARITH_ss][exp1_size_thm,exp6_size_thm,exp4_size_thm] >>
map_every (fn q => Q.ISPEC_THEN q imp_res_tac SUM_MAP_MEM_bound)
  [`exp2_size`,`exp5_size`,`exp_size`] >>
fsrw_tac[ARITH_ss][exp_size_def])
val _ = export_rewrites["FV_def"]

val FINITE_FV = store_thm(
"FINITE_FV",
``∀exp. FINITE (FV exp)``,
ho_match_mp_tac (theorem"FV_ind") >>
rw[pairTheory.EXISTS_PROD] >>
fsrw_tac[SATISFY_ss][])
val _ = export_rewrites["FINITE_FV"]

val (evaluate_list_with_rules,evaluate_list_with_ind,evaluate_list_with_cases) = Hol_reln [ANTIQUOTE(
evaluate_rules |> SIMP_RULE (srw_ss()) [] |> concl |>
strip_conj |>
Lib.filter (fn tm => tm |> strip_forall |> snd |> strip_imp |> snd |> strip_comb |> fst |> same_const ``evaluate_list``) |>
let val t1 = ``evaluate cenv env``
    val t2 = ``evaluate_list cenv env``
    val tP = type_of t1
    val P = mk_var ("P",tP)
    val ew = mk_comb(mk_var("evaluate_list_with",tP --> type_of t2),P)
in List.map (fn tm => tm |> strip_forall |> snd |>
                   subst [t1|->P, t2|->ew])
end |> list_mk_conj)]

val evaluate_list_with_evaluate = store_thm(
"evaluate_list_with_evaluate",
``∀cenv env. evaluate_list cenv env = evaluate_list_with (evaluate cenv env)``,
ntac 2 gen_tac >>
simp_tac std_ss [Once FUN_EQ_THM] >>
Induct >>
rw[FUN_EQ_THM] >-
  rw[Once evaluate_cases,Once evaluate_list_with_cases] >>
rw[Once evaluate_cases] >>
rw[Once evaluate_list_with_cases,SimpRHS] >>
PROVE_TAC[])

val (evaluate_match_with_rules,evaluate_match_with_ind,evaluate_match_with_cases) = Hol_reln
  (* evaluate_rules |> SIMP_RULE (srw_ss()) [] |> concl |> strip_conj |>
     Lib.filter (fn tm => tm |> strip_forall |> snd |> strip_imp |> snd |>
     strip_comb |> fst |> same_const ``evaluate_match``) *)
   `(evaluate_match_with P cenv env v [] (Rerr (Rraise Bind_error))) ∧
    (ALL_DISTINCT (pat_bindings p []) ∧
     (pmatch cenv p v env = Match env') ∧ P cenv env' e bv ⇒
     evaluate_match_with P cenv env v ((p,e)::pes) bv) ∧
    (ALL_DISTINCT (pat_bindings p []) ∧
     (pmatch cenv p v env = No_match) ∧
     evaluate_match_with P cenv env v pes bv ⇒
     evaluate_match_with P cenv env v ((p,e)::pes) bv) ∧
    ((pmatch cenv p v env = Match_type_error) ⇒
     evaluate_match_with P cenv env v ((p,e)::pes) (Rerr Rtype_error)) ∧
    (¬ALL_DISTINCT (pat_bindings p []) ⇒
     evaluate_match_with P cenv env v ((p,e)::pes) (Rerr Rtype_error))`

val evaluate_match_with_evaluate = store_thm(
"evaluate_match_with_evaluate",
``evaluate_match = evaluate_match_with evaluate``,
simp_tac std_ss [FUN_EQ_THM] >>
ntac 3 gen_tac >>
Induct >-
  rw[Once evaluate_cases,Once evaluate_match_with_cases] >>
rw[Once evaluate_cases] >>
rw[Once evaluate_match_with_cases,SimpRHS] >>
PROVE_TAC[])

val evaluate_nice_ind = save_thm(
"evaluate_nice_ind",
evaluate_ind
|> Q.SPECL [`P`,`λcenv env. evaluate_list_with (P cenv env)`,`evaluate_match_with P`] |> SIMP_RULE (srw_ss()) []
|> UNDISCH_ALL
|> CONJUNCTS
|> List.hd
|> DISCH_ALL
|> Q.GEN `P`
|> SIMP_RULE (srw_ss()) [])

val evaluate_nice_strongind = save_thm(
"evaluate_nice_strongind",
evaluate_strongind
|> Q.SPECL [`P`,`λcenv env. evaluate_list_with (P cenv env)`,`evaluate_match_with P`] |> SIMP_RULE (srw_ss()) []
|> UNDISCH_ALL
|> CONJUNCTS
|> List.hd
|> DISCH_ALL
|> Q.GEN `P`
|> SIMP_RULE (srw_ss()) [evaluate_list_with_evaluate])

val evaluate_list_with_nil = store_thm(
"evaluate_list_with_nil",
``∀f res. evaluate_list_with f [] res = (res = Rval [])``,
rw[Once evaluate_list_with_cases])
val _ = export_rewrites["evaluate_list_with_nil"];

val evaluate_list_with_cons = store_thm(
"evaluate_list_with_cons",
``∀f e es res. evaluate_list_with f (e::es) res =
  (∃v vs. f e (Rval v) ∧ evaluate_list_with f es (Rval vs) ∧ (res = Rval (v::vs))) ∨
  (∃v err. f e (Rval v) ∧ evaluate_list_with f es (Rerr err) ∧ (res = Rerr err)) ∨
  (∃err. f e (Rerr err) ∧ (res = Rerr err))``,
rw[Once evaluate_list_with_cases] >> PROVE_TAC[])

val evaluate_list_with_error = store_thm(
"evaluate_list_with_error",
``!P ls err. evaluate_list_with P ls (Rerr err) =
             (∃n. n < LENGTH ls ∧ P (EL n ls) (Rerr err) ∧
               !m. m < n ⇒ ∃v. P (EL m ls) (Rval v))``,
gen_tac >> Induct >- rw[evaluate_list_with_nil] >>
rw[EQ_IMP_THM,evaluate_list_with_cons] >- (
  qexists_tac `SUC n` >>
  rw[] >>
  Cases_on `m` >> rw[] >- (
    qexists_tac `v` >> rw[] ) >>
  fs[] )
>- (
  qexists_tac `0` >>
  rw[] ) >>
Cases_on `n` >> fs[] >>
disj1_tac >>
first_assum (qspec_then `0` mp_tac) >>
simp_tac(srw_ss())[] >>
rw[] >> qexists_tac `v` >> rw[] >>
qmatch_assum_rename_tac `n < LENGTH ls` [] >>
qexists_tac `n` >> rw[] >>
first_x_assum (qspec_then `SUC m` mp_tac) >>
rw[])

val evaluate_list_with_value = store_thm(
"evaluate_list_with_value",
``!P ls vs. evaluate_list_with P ls (Rval vs) = (LENGTH ls = LENGTH vs) ∧ ∀n. n < LENGTH ls ⇒ P (EL n ls) (Rval (EL n vs))``,
gen_tac >> Induct >- rw[evaluate_list_with_nil,LENGTH_NIL_SYM] >>
gen_tac >> Cases >> rw[evaluate_list_with_cons,EQ_IMP_THM] >- (
  Cases_on `n` >> fs[] )
>- (
  first_x_assum (qspec_then `0` mp_tac) >>
  rw[] ) >>
first_x_assum (qspec_then `SUC n` mp_tac) >>
rw[])

val evaluate_list_with_EVERY = store_thm(
"evaluate_list_with_EVERY",
``∀P es vs. evaluate_list_with P es (Rval vs) = (LENGTH es = LENGTH vs) ∧ EVERY (UNCURRY P) (ZIP (es,MAP Rval vs))``,
gen_tac >> Induct >- (
  rw[evaluate_list_with_nil,LENGTH_NIL_SYM,EQ_IMP_THM] ) >>
rw[evaluate_list_with_cons,EQ_IMP_THM] >> rw[] >>
Cases_on `vs` >> fs[])

val do_prim_app_FV = store_thm(
"do_prim_app_FV",
``∀env op v1 v2 env' exp.
  (op ≠ Opapp) ∧
  (do_app env op v1 v2 = SOME (env',exp)) ⇒
  (FV exp = {})``,
gen_tac >> Cases >>
Cases >> TRY (Cases_on `l`) >>
Cases >> TRY (Cases_on `l`) >>
rw[do_app_def] >> rw[])

val do_log_FV = store_thm(
"do_log_FV",
``(do_log op v e2 = SOME exp) ⇒
  (FV exp ⊆ FV e2)``,
fs[do_log_def] >>
BasicProvers.EVERY_CASE_TAC >>
rw[] >>rw[])

val do_if_FV = store_thm(
"do_if_FV",
``(do_if v e2 e3 = SOME e) ⇒
  (FV e ⊆ FV e2 ∪ FV e3)``,
fs[do_if_def] >>
BasicProvers.EVERY_CASE_TAC >>
rw[] >>rw[])

val build_rec_env_dom = store_thm(
"build_rec_env_dom",
``MAP FST (build_rec_env defs env) = MAP FST defs ++ MAP FST env``,
rw[build_rec_env_def,bind_def,FOLDR_CONS_triple] >>
rw[MAP_MAP_o,combinTheory.o_DEF,pairTheory.LAMBDA_PROD] >>
rw[FST_triple])
val _ = export_rewrites["build_rec_env_dom"]

(* TODO: move *)
val pmatch_def = save_thm("pmatch_def",pmatch_def)
val pmatch_ind = save_thm("pmatch_ind",pmatch_ind)
val lit_same_type_def = save_thm("lit_same_type_def",lit_same_type_def)

val map_match_def = Define`
  (map_match f (Match env) = Match (f env)) ∧
  (map_match f x = x)`
val _ = export_rewrites["map_match_def"]

val pmatch_APPEND = store_thm(
"pmatch_APPEND",
``(∀cenv p v env n.
    (pmatch cenv p v env =
     map_match (combin$C APPEND (DROP n env)) (pmatch cenv p v (TAKE n env)))) ∧
  (∀cenv ps vs env n.
    (pmatch_list cenv ps vs env =
     map_match (combin$C APPEND (DROP n env)) (pmatch_list cenv ps vs (TAKE n env))))``,
ho_match_mp_tac pmatch_ind >>
strip_tac >- rw[pmatch_def,bind_def] >>
strip_tac >- rw[pmatch_def] >>
strip_tac >- (
  rw[pmatch_def] >>
  Cases_on `ALOOKUP cenv n` >> fs[] >>
  PairCases_on `x` >> fs[] >>
  rw[] >> fs[] >>
  Cases_on `ALOOKUP cenv n'` >> fs[] >>
  PairCases_on `x` >> fs[] >>
  rw[] >> fs[] ) >>
strip_tac >- rw[pmatch_def] >>
strip_tac >- rw[pmatch_def] >>
strip_tac >- rw[pmatch_def] >>
strip_tac >- rw[pmatch_def] >>
strip_tac >- rw[pmatch_def] >>
strip_tac >- rw[pmatch_def] >>
strip_tac >- rw[pmatch_def] >>
strip_tac >- (
  rw[pmatch_def] >>
  Cases_on `pmatch cenv p v (TAKE n env)` >> fs[] >>
  Cases_on `pmatch cenv p v env` >> fs[] >>
  TRY (first_x_assum (qspec_then `n` mp_tac) >> rw[] >> NO_TAC) >>
  first_x_assum (qspec_then `n` mp_tac) >> rw[] >>
  first_x_assum (qspec_then `LENGTH l` mp_tac) >> rw[] >>
  rw[TAKE_APPEND1,DROP_APPEND1,DROP_LENGTH_NIL] ) >>
strip_tac >- rw[pmatch_def] >>
strip_tac >- rw[pmatch_def])

val pmatch_plit = store_thm(
"pmatch_plit",
``(pmatch cenv (Plit l) v env = r) =
  (((v = Litv l) ∧ (r = Match env)) ∨
   ((∃l'. (v = Litv l') ∧ lit_same_type l l' ∧ l ≠ l') ∧
    (r = No_match)) ∨
   ((∀l'. (v = Litv l') ⇒ ¬lit_same_type l l') ∧ (r = Match_type_error)))``,
Cases_on `v` >> rw[pmatch_def,EQ_IMP_THM] >>
Cases_on `l` >> fs[lit_same_type_def])

val pmatch_nil = save_thm("pmatch_nil",
  LIST_CONJ [
    pmatch_APPEND
    |> CONJUNCT1
    |> Q.SPECL[`cenv`,`p`,`v`,`env`,`0`]
    |> SIMP_RULE(srw_ss())[]
  ,
    pmatch_APPEND
    |> CONJUNCT2
    |> Q.SPECL[`cenv`,`ps`,`vs`,`env`,`0`]
    |> SIMP_RULE(srw_ss())[]
  ])

val (closed_rules,closed_ind,closed_cases) = Hol_reln`
(closed (Litv l)) ∧
(EVERY closed vs ⇒ closed (Conv n vs)) ∧
(EVERY closed (MAP SND env) ∧
 FV b ⊆ set (MAP FST env) ∪ {x}
⇒ closed (Closure env x b)) ∧
(EVERY closed (MAP SND env) ∧
 ALL_DISTINCT (MAP FST defs) ∧
 MEM d (MAP FST defs) ∧
 (∀i d x b. i < LENGTH defs ∧ (EL i defs = (d,x,b)) ⇒
            FV b ⊆ set (MAP FST env) ∪ set (MAP FST defs) ∪ {x})
⇒ closed (Recclosure env defs d))`

val closed_lit = save_thm(
"closed_lit",
SIMP_RULE(srw_ss())[]
(Q.SPEC`Litv l`closed_cases))
val _ = export_rewrites["closed_lit"]

val closed_conv = save_thm(
"closed_conv",
SIMP_RULE(srw_ss())[]
(Q.SPEC`Conv cn vs`closed_cases))
val _ = export_rewrites["closed_conv"]

val build_rec_env_closed = store_thm(
"build_rec_env_closed",
``∀defs l.
  EVERY closed (MAP SND l) ∧
  ALL_DISTINCT (MAP FST defs) ∧
  (∀i d x b. i < LENGTH defs ∧ (EL i defs = (d,x,b)) ⇒
   FV b ⊆ set (MAP FST l) ∪ set (MAP FST defs) ∪ {x})
  ⇒ EVERY closed (MAP SND (build_rec_env defs l))``,
rw[build_rec_env_def,bind_def,FOLDR_CONS_triple] >>
rw[MAP_MAP_o,combinTheory.o_DEF,pairTheory.LAMBDA_PROD] >>
asm_simp_tac(srw_ss())[EVERY_MEM,MEM_MAP,pairTheory.EXISTS_PROD] >>
rw[MEM_EL] >>
rw[Once closed_cases] >- (
  rw[MEM_MAP,pairTheory.EXISTS_PROD,MEM_EL] >>
  PROVE_TAC[]) >>
first_x_assum match_mp_tac >>
PROVE_TAC[])

val do_app_closed = store_thm(
"do_app_closed",
``∀env op v1 v2 env' exp.
  EVERY closed (MAP SND env) ∧
  closed v1 ∧ closed v2 ∧
  (do_app env op v1 v2 = SOME (env',exp))
  ⇒ EVERY closed (MAP SND env') ∧
    FV exp ⊆ set (MAP FST env')``,
gen_tac >> Cases
>- (
  Cases >> TRY (Cases_on `l`) >>
  Cases >> TRY (Cases_on `l`) >>
  rw[do_app_def] >>
  fs[closed_cases])
>- (
  Cases >> TRY (Cases_on `l`) >>
  Cases >> TRY (Cases_on `l`) >>
  rw[do_app_def] >>
  fs[closed_cases])
>- (
  Cases >> TRY (Cases_on `l`) >>
  Cases >> TRY (Cases_on `l`) >>
  rw[do_app_def] >> fs[]) >>
Cases >> Cases >> rw[do_app_def,bind_def] >> fs[closed_cases] >>
fs[] >> rw[] >>
rw[Once INSERT_SING_UNION,Once UNION_COMM] >>
qmatch_assum_rename_tac `MEM s (MAP FST defs)`[] >>
Cases_on `ALOOKUP defs s` >> fs[] >>
qmatch_assum_rename_tac `ALOOKUP defs d = SOME p`[] >>
Cases_on `p` >> fs[] >> rw[] >> rw[Once closed_cases] >>
TRY (qmatch_abbrev_tac `EVERY closed X` >>
     PROVE_TAC[build_rec_env_closed]) >>
imp_res_tac ALOOKUP_MEM >>
fsrw_tac[DNF_ss][MEM_EL] >>
fsrw_tac[DNF_ss][SUBSET_DEF] >>
PROVE_TAC[])

val pmatch_closed = store_thm("pmatch_closed",
  ``(∀cenv p v env env'.
      EVERY closed (MAP SND env) ∧ closed v ∧
      (pmatch cenv p v env = Match env') ⇒
      EVERY closed (MAP SND env') ∧
      (set (MAP FST env') = pat_vars p ∪ set (MAP FST env))) ∧
    (∀cenv ps vs env env'.
      EVERY closed (MAP SND env) ∧ EVERY closed vs ∧
      (pmatch_list cenv ps vs env = Match env') ⇒
      EVERY closed (MAP SND env') ∧
      (set (MAP FST env') = BIGUNION (IMAGE pat_vars (set ps)) ∪ set (MAP FST env)))``,
  ho_match_mp_tac pmatch_ind >>
  strip_tac >- (
    rw[pmatch_def,bind_def] >>
    rw[] >> rw[EXTENSION] ) >>
  strip_tac >- (
    rw[pmatch_def] >> rw[] ) >>
  strip_tac >- (
    rpt gen_tac >> fs[] >>
    Cases_on `ALOOKUP cenv n` >> fs[] >- (
      rw[pmatch_def] ) >>
    qmatch_assum_rename_tac `ALOOKUP cenv n = SOME p`[] >>
    PairCases_on `p` >> fs[] >>
    Cases_on `ALOOKUP cenv n'` >> fs[] >- (
      rw[pmatch_def] ) >>
    qmatch_assum_rename_tac `ALOOKUP cenv n' = SOME p`[] >>
    PairCases_on `p` >> fs[] >>
    rw[pmatch_def] >>
    srw_tac[ETA_ss][] ) >>
  strip_tac >- rw[pmatch_def] >>
  strip_tac >- rw[pmatch_def] >>
  strip_tac >- rw[pmatch_def] >>
  strip_tac >- rw[pmatch_def] >>
  strip_tac >- rw[pmatch_def] >>
  strip_tac >- rw[pmatch_def] >>
  strip_tac >- ( rw[pmatch_def] >> rw[] ) >>
  strip_tac >- (
    rpt gen_tac >>
    strip_tac >>
    simp_tac(srw_ss())[pmatch_def] >>
    Cases_on `pmatch cenv p v env` >> fs[] >>
    qmatch_assum_rename_tac `pmatch cenv p v env = Match env0`[] >>
    Cases_on `pmatch_list cenv ps vs env0` >> fs[] >>
    strip_tac >> fs[] >>
    PROVE_TAC[UNION_COMM,UNION_ASSOC]) >>
  rw[pmatch_def])

val evaluate_closed = store_thm(
"evaluate_closed",
``∀cenv env exp res.
  evaluate cenv env exp res ⇒
  FV exp ⊆ set (MAP FST env) ∧
  EVERY closed (MAP SND env) ⇒
  every_result closed res``,
ho_match_mp_tac evaluate_nice_ind >>
strip_tac >- rw[] >>
strip_tac >- rw[] >>
strip_tac >- (
  rw[] >>
  fs[evaluate_list_with_EVERY] >>
  qpat_assum `LENGTH X = Y` assume_tac >>
  fsrw_tac[DNF_ss][EVERY_MEM,MEM_ZIP,EL_MAP] >>
  rw[MEM_EL] >>
  fsrw_tac[DNF_ss][SUBSET_DEF,MEM_EL] >>
  PROVE_TAC[]) >>
strip_tac >- rw[] >>
strip_tac >- rw[] >>
strip_tac >- (
  rw[] >>
  imp_res_tac ALOOKUP_MEM >>
  fs[EVERY_MEM,MEM_MAP,pairTheory.EXISTS_PROD] >>
  PROVE_TAC[]) >>
strip_tac >- rw[] >>
strip_tac >- (
  rw[] >>
  rw[Once closed_cases] >>
  fsrw_tac[DNF_ss][SUBSET_DEF] >>
  PROVE_TAC[]) >>
strip_tac >- (
  rw[] >> fs[] >>
  PROVE_TAC[do_app_closed]) >>
strip_tac >- rw[] >>
strip_tac >- rw[] >>
strip_tac >- rw[] >>
strip_tac >- (
  rw[] >> fs[] >>
  PROVE_TAC[do_log_FV,SUBSET_TRANS]) >>
strip_tac >- rw[] >>
strip_tac >- rw[] >>
strip_tac >- (
  rw[] >> fs[] >>
  PROVE_TAC[do_if_FV,SUBSET_DEF,IN_UNION]) >>
strip_tac >- rw[] >>
strip_tac >- rw[] >>
strip_tac >- (
  gen_tac >>
  CONV_TAC (RESORT_FORALL_CONV
    (uncurry cons o pluck (equal "pes" o fst o dest_var))) >>
  Induct >- rw[Once evaluate_match_with_cases] >>
  rpt gen_tac >>
  strip_tac >>
  pop_assum mp_tac >>
  rw[Once evaluate_match_with_cases] >> rw[] >- (
    fs[] >>
    first_x_assum match_mp_tac >>
    imp_res_tac (CONJUNCT1 pmatch_closed) >>
    fs[] >>
    fsrw_tac[DNF_ss][SUBSET_DEF] >>
    PROVE_TAC[] ) >>
  first_x_assum (match_mp_tac o MP_CANON) >>
  rw[] >>
  map_every qexists_tac[`env`,`exp`,`v`] >>
  fs[] ) >>
strip_tac >- rw[] >>
strip_tac >- (
  rw[bind_def] >>
  fs[] >>
  fsrw_tac[DNF_ss][SUBSET_DEF] >>
  PROVE_TAC[]) >>
strip_tac >- rw[] >>
strip_tac >- (
  rw[] >>
  fs[LIST_TO_SET_MAP] >>
  fsrw_tac[DNF_ss][SUBSET_DEF,pairTheory.EXISTS_PROD] >>
  first_x_assum match_mp_tac >>
  conj_tac >- PROVE_TAC[] >>
  match_mp_tac build_rec_env_closed >>
  fs[LIST_TO_SET_MAP] >>
  fsrw_tac[DNF_ss][MEM_EL,SUBSET_DEF,FST_triple] >>
  metis_tac[pairTheory.FST,pairTheory.PAIR_EQ,pairTheory.pair_CASES]) >>
strip_tac >- rw[] >>
strip_tac >- rw[] >>
strip_tac >- rw[evaluate_list_with_cons] >>
strip_tac >- rw[evaluate_list_with_cons] >>
strip_tac >- rw[evaluate_list_with_cons] >>
strip_tac >- rw[Once evaluate_match_with_cases] >>
strip_tac >- rw[Once evaluate_match_with_cases] >>
strip_tac >- (
  rw[] >> rw[Once evaluate_match_with_cases] ) >>
strip_tac >- (
  rw[] >> rw[Once evaluate_match_with_cases] ) >>
strip_tac >- (
  rw[] >> rw[Once evaluate_match_with_cases] ))

(* TODO: move? *)
val result_rel_def = Define`
(result_rel R (Rval v1) (Rval v2) = R v1 v2) ∧
(result_rel R (Rerr e1) (Rerr e2) = (e1 = e2)) ∧
(result_rel R _ _ = F)`
val _ = export_rewrites["result_rel_def"]

val result_rel_Rval = store_thm(
"result_rel_Rval",
``result_rel R (Rval v) r = ∃v'. (r = Rval v') ∧ R v v'``,
Cases_on `r` >> rw[])
val result_rel_Rerr = store_thm(
"result_rel_Rerr",
``result_rel R (Rerr e) r = (r = Rerr e)``,
Cases_on `r` >> rw[EQ_IMP_THM])
val _ = export_rewrites["result_rel_Rval","result_rel_Rerr"]

val result_rel_err = store_thm("result_rel_err",
  ``result_rel R r (Rerr err) = (r = Rerr err)``,
  Cases_on `r` >> rw[result_rel_def])
val _ = export_rewrites["result_rel_err"]

val result_rel_refl = store_thm(
"result_rel_refl",
``(∀x. R x x) ⇒ ∀x. result_rel R x x``,
strip_tac >> Cases >> rw[])
val _ = export_rewrites["result_rel_refl"]

val result_rel_trans = store_thm(
"result_rel_trans",
``(∀x y z. R x y ∧ R y z ⇒ R x z) ⇒ (∀x y z. result_rel R x y ∧ result_rel R y z ⇒ result_rel R x z)``,
rw[] >>
Cases_on `x` >> fs[] >> rw[] >> fs[] >> PROVE_TAC[])

val result_rel_sym = store_thm(
"result_rel_sym",
``(∀x y. R x y ⇒ R y x) ⇒ (∀x y. result_rel R x y ⇒ result_rel R y x)``,
rw[] >> Cases_on `x` >> fs[])

val good_cenv_def = Define`
  good_cenv cenv =
  ∀c n s. (MEM (c,(n,s)) cenv) ⇒
    c ∈ s ∧
    ∀c' n' s'. MEM (c',(n',s')) cenv ∧ c' ∈ s' ⇒ (s = s')`

val _ = export_theory()
