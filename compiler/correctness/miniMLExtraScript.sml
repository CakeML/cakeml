open HolKernel bossLib boolLib boolSimps pairTheory alistTheory listTheory rich_listTheory pred_setTheory finite_mapTheory lcsymtacs SatisfySimps quantHeuristicsLib
open MiniMLTheory MiniMLTerminationTheory miscTheory compileTerminationTheory
val _ = new_theory "miniMLExtra"

val lookup_ALOOKUP = store_thm(
"lookup_ALOOKUP",
``lookup = combin$C ALOOKUP``,
fs[FUN_EQ_THM] >> gen_tac >> Induct >- rw[] >> Cases >> rw[])
val _ = export_rewrites["lookup_ALOOKUP"];

val find_recfun_ALOOKUP = store_thm(
"find_recfun_ALOOKUP",
``∀funs n. find_recfun n funs = OPTION_MAP SND (ALOOKUP funs n)``,
Induct >- rw[find_recfun_def] >>
qx_gen_tac `d` >>
PairCases_on `d` >>
rw[find_recfun_def])
val _ = export_rewrites["find_recfun_ALOOKUP"]

val pat_vars_def = tDefine "pat_vars"`
(pat_vars (Pvar v _) = {v}) ∧
(pat_vars (Plit l) = {}) ∧
(pat_vars (Pcon c ps) = BIGUNION (IMAGE pat_vars (set ps))) ∧
(pat_vars (Pref p) = pat_vars p)`(
WF_REL_TAC `measure (pat_size ARB)` >>
srw_tac[ARITH_ss][pat1_size_thm] >>
Q.ISPEC_THEN `pat_size ARB` imp_res_tac SUM_MAP_MEM_bound >>
srw_tac[ARITH_ss][])
val _ = export_rewrites["pat_vars_def"]

val FINITE_pat_vars = store_thm("FINITE_pat_vars",
  ``∀p. FINITE (pat_vars p)``,
  ho_match_mp_tac (theorem"pat_vars_ind") >>
  rw[] >> res_tac)
val _ = export_rewrites["FINITE_pat_vars"]

val pat_bindings_acc = store_thm("pat_bindings_acc",
  ``(∀(p:α pat) l. pat_bindings p l = pat_bindings p [] ++ l) ∧
    (∀(ps:α pat list) l. pats_bindings ps l = pats_bindings ps [] ++ l)``,
  ho_match_mp_tac (TypeBase.induction_of``:α pat``) >> rw[] >>
  simp_tac std_ss [pat_bindings_def] >>
  metis_tac[APPEND,APPEND_ASSOC])

val pats_bindings_MAP = store_thm("pats_bindings_MAP",
  ``∀ps ls. pats_bindings ps ls = FLAT (MAP (combin$C pat_bindings []) (REVERSE ps)) ++ ls``,
  Induct >>
  rw[pat_bindings_def] >>
  rw[Once pat_bindings_acc])

val pat_vars_pat_bindings = store_thm("pat_vars_pat_bindings",
  ``(∀(p:α pat). pat_vars p = set (pat_bindings p [])) ∧
    (∀(ps:α pat list). BIGUNION (IMAGE pat_vars (set ps)) = set (pats_bindings ps []))``,
  ho_match_mp_tac(TypeBase.induction_of``:α pat``) >>
  srw_tac[ETA_ss][pat_bindings_def] >>
  rw[Once pat_bindings_acc,SimpRHS] >>
  rw[UNION_COMM])

val FV_def = tDefine "FV"`
(FV (Raise _) = {}) ∧
(FV (Handle e1 x e2) = FV e1 ∪ (FV e2 DIFF {x})) ∧
(FV (Lit _) = {}) ∧
(FV (Con _ ls) = BIGUNION (IMAGE FV (set ls))) ∧
(FV (Var x _) = {x}) ∧
(FV (Fun x _ e) = FV e DIFF {x}) ∧
(FV (Uapp _ e) = FV e) ∧
(FV (App _ e1 e2) = FV e1 ∪ FV e2) ∧
(FV (Log _ e1 e2) = FV e1 ∪ FV e2) ∧
(FV (If e1 e2 e3) = FV e1 ∪ FV e2 ∪ FV e3) ∧
(FV (Mat e pes) = FV e ∪ BIGUNION (IMAGE (λ(p,e). FV e DIFF pat_vars p) (set pes))) ∧
(FV (Let _ x _ e b) = FV e ∪ (FV b DIFF {x})) ∧
(FV (Letrec _ defs b) = BIGUNION (IMAGE (λ(y,_0,x,_1,e). FV e DIFF ({x} ∪ (IMAGE FST (set defs)))) (set defs)) ∪ (FV b DIFF (IMAGE FST (set defs))))`
(WF_REL_TAC `measure (exp_size ARB)` >>
srw_tac[ARITH_ss][exp1_size_thm,exp5_size_thm,exp8_size_thm,
                  SUM_MAP_exp7_size_thm,SUM_MAP_exp2_size_thm,
                  SUM_MAP_exp3_size_thm,SUM_MAP_exp4_size_thm,SUM_MAP_exp6_size_thm] >>
TRY (
  qmatch_assum_rename_tac`MEM (a,z,c,d,e) defs`[]>>
  `MEM e (MAP SND (MAP SND (MAP SND (MAP SND defs))))`by
  srw_tac[SATISFY_ss][MEM_MAP,EXISTS_PROD] ) >>
TRY (
  qmatch_assum_rename_tac`MEM (p,z) pes`[]>>
  `MEM z (MAP SND pes)`by srw_tac[SATISFY_ss][MEM_MAP,EXISTS_PROD] ) >>
map_every (fn q => Q.ISPEC_THEN q imp_res_tac SUM_MAP_MEM_bound)
  [`exp2_size ARB`,`exp5_size ARB`,`exp_size ARB`] >>
fsrw_tac[ARITH_ss][exp_size_def])
val _ = export_rewrites["FV_def"]

val FINITE_FV = store_thm(
"FINITE_FV",
``∀exp. FINITE (FV exp)``,
ho_match_mp_tac (theorem"FV_ind") >>
rw[pairTheory.EXISTS_PROD] >>
fsrw_tac[SATISFY_ss][])
val _ = export_rewrites["FINITE_FV"]

(*
val (evaluate_list_with_rules,evaluate_list_with_ind,evaluate_list_with_cases) = Hol_reln [ANTIQUOTE(
evaluate_rules |> SIMP_RULE (srw_ss()) [] |> concl |>
strip_conj |>
Lib.filter (fn tm => tm |> strip_forall |> snd |> strip_imp |> snd |> strip_comb |> fst |> same_const ``evaluate_list``) |>
let val t1 = ``combin$C (evaluate cenv) env``
    val t2 = ``combin$C (evaluate_list cenv) env``
    val tP = type_of t1
    val s = ``s:store`` val s1 = ``s1:store``
    val s' = ``s':store`` val s2 = ``s2:store``
    val P = mk_var ("P",tP)
    val ew = mk_comb(mk_var("evaluate_list_with",tP --> type_of t2),P)
    val t1s1 = ``evaluate cenv s1 env``
    val t2s1 = ``evaluate_list cenv s1 env``
    val t2s2 = ``evaluate_list cenv s2 env``
    val Ps1 = mk_comb(P,s1)
    val ews1 = mk_comb(ew,s1)
    val ews2 = mk_comb(ew,s2)
in List.map (fn tm => tm |> strip_forall |> snd |>
                   subst [s|->s1] |>
                   subst [s'|->s2] |>
                   subst [t1s1|->Ps1, t2s1|->ews1, t2s2|->ews2])
end |> list_mk_conj)]

val evaluate_list_with_evaluate = store_thm(
"evaluate_list_with_evaluate",
``∀cenv s env. evaluate_list cenv s env = evaluate_list_with (combin$C (evaluate cenv) env) s``,
gen_tac >> CONV_TAC SWAP_FORALL_CONV >> gen_tac >>
simp_tac std_ss [Once FUN_EQ_THM] >>
CONV_TAC SWAP_FORALL_CONV >>
Induct >>
rw[FUN_EQ_THM] >-
  rw[Once evaluate_cases,Once evaluate_list_with_cases] >>
rw[Once evaluate_cases] >>
rw[Once evaluate_list_with_cases,SimpRHS] >>
PROVE_TAC[])
*)

val (evaluate_match_with_rules,evaluate_match_with_ind,evaluate_match_with_cases) = Hol_reln
  (* evaluate_rules |> SIMP_RULE (srw_ss()) [] |> concl |> strip_conj |>
     Lib.filter (fn tm => tm |> strip_forall |> snd |> strip_imp |> snd |>
     strip_comb |> fst |> same_const ``evaluate_match``) *)
   `(evaluate_match_with P cenv s env v [] (s,Rerr (Rraise Bind_error))) ∧
    (ALL_DISTINCT (pat_bindings p []) ∧
     (pmatch (SOME 0) cenv s p v env = Match env') ∧ P cenv s env' (p,e) bv ⇒
     evaluate_match_with P cenv s env v ((p,e)::pes) bv) ∧
    (ALL_DISTINCT (pat_bindings p []) ∧
     (pmatch (SOME 0) cenv s p v env = No_match) ∧
     evaluate_match_with P cenv s env v pes bv ⇒
     evaluate_match_with P cenv s env v ((p,e)::pes) bv) ∧
    ((pmatch (SOME 0) cenv s p v env = Match_type_error) ⇒
     evaluate_match_with P cenv s env v ((p,e)::pes) (s,Rerr Rtype_error)) ∧
    (¬ALL_DISTINCT (pat_bindings p []) ⇒
     evaluate_match_with P cenv s env v ((p,e)::pes) (s,Rerr Rtype_error))`

val evaluate_match_with_evaluate = store_thm(
"evaluate_match_with_evaluate",
``evaluate_match = evaluate_match_with (λcenv s env pe bv. evaluate cenv s env (SND pe) bv)``,
simp_tac std_ss [FUN_EQ_THM] >>
ntac 4 gen_tac >>
Induct >-
  rw[Once evaluate_cases,Once evaluate_match_with_cases] >>
rw[Once evaluate_cases] >>
rw[Once evaluate_match_with_cases,SimpRHS] >>
PROVE_TAC[])

(*
val evaluate_list_with_nil = store_thm(
"evaluate_list_with_nil",
``∀f res. evaluate_list_with f s [] res = (res = (s,Rval []))``,
rw[Once evaluate_list_with_cases])
val _ = export_rewrites["evaluate_list_with_nil"];

val evaluate_list_with_cons = store_thm(
"evaluate_list_with_cons",
``∀f s e es res. evaluate_list_with f s (e::es) res =
  (∃s' s'' v vs. f s e (s',Rval v) ∧ evaluate_list_with f s' es (s'',Rval vs) ∧ (res = (s'',Rval (v::vs)))) ∨
  (∃s' s'' v err. f s e (s',Rval v) ∧ evaluate_list_with f s' es (s'',Rerr err) ∧ (res = (s'',Rerr err))) ∨
  (∃s' err. f s e (s',Rerr err) ∧ (res = (s',Rerr err)))``,
rw[Once evaluate_list_with_cases] >> PROVE_TAC[])

val evaluate_nice_ind = save_thm(
"evaluate_nice_ind",
evaluate_ind
|> Q.SPECL [`P`,`λcenv s env. evaluate_list_with (combin$C (P cenv) env) s`,`evaluate_match_with P`] |> SIMP_RULE (srw_ss()) []
|> UNDISCH_ALL
|> CONJUNCTS
|> List.hd
|> DISCH_ALL
|> Q.GEN `P`
|> SIMP_RULE (srw_ss()) [evaluate_match_with_rules])

val evaluate_nice_strongind = save_thm(
"evaluate_nice_strongind",
evaluate_strongind
|> Q.SPECL [`P`,`λcenv s env. evaluate_list_with (combin$C (P cenv) env) s`,`evaluate_match_with P`] |> SIMP_RULE (srw_ss()) []
|> UNDISCH_ALL
|> CONJUNCTS
|> List.hd
|> DISCH_ALL
|> Q.GEN `P`
|> SIMP_RULE (srw_ss()) [evaluate_list_with_evaluate,evaluate_match_with_rules])
*)

val evaluate_nicematch_strongind = save_thm(
"evaluate_nicematch_strongind",
evaluate_strongind
|> Q.SPECL [`P0`,`P1`,`evaluate_match_with (λcenv s env pe bv. P0 cenv s env (SND pe) bv)`] |> SIMP_RULE (srw_ss()) []
|> UNDISCH_ALL
|> CONJUNCTS
|> C (curry List.take) 2
|> LIST_CONJ
|> DISCH_ALL
|> Q.GENL [`P1`,`P0`]
|> SIMP_RULE (srw_ss()) [evaluate_match_with_rules])

(*
val evaluate_list_with_error = store_thm(
"evaluate_list_with_error",
``!P ls s s' err. evaluate_list_with P s ls (s',Rerr err) =
      ∃l. LENGTH l < LENGTH ls ∧
          (∀m. m < LENGTH l ⇒ ∃v. P (EL m (s::l)) (EL m ls) (EL m l, Rval v)) ∧
          P (LAST (s::l)) (EL (LENGTH l) ls) (s',Rerr err)``,
gen_tac >> Induct >- (
  rw[evaluate_list_with_nil] >>
  Cases_on `l` >> rw[] ) >>
rw[EQ_IMP_THM,evaluate_list_with_cons] >- (
  qmatch_assum_rename_tac `P s h (s0,Rval v)`[] >>
  qexists_tac `s0::l` >> simp[] >>
  rw[] >>
  Cases_on `m` >> rw[] >>
  fsrw_tac[ARITH_ss][] >>
  qexists_tac `v` >> rw[] )
>- (
  qexists_tac `[]` >>
  srw_tac[ARITH_ss][] ) >>
Cases_on `l` >> fs[] >>
disj1_tac >>
first_assum (qspec_then `0` mp_tac) >>
simp_tac(srw_ss())[] >>
rw[] >>
qmatch_assum_rename_tac`P s h (h',Rval v)`[] >>
qexists_tac`h'` >>
qexists_tac `v` >> rw[] >>
qmatch_assum_rename_tac `LENGTH t < LENGTH ls` [] >>
qexists_tac `t` >> rw[] >>
first_x_assum (qspec_then `SUC m` mp_tac) >>
rw[])

val evaluate_list_with_value = store_thm(
"evaluate_list_with_value",
``!P ls s s' vs. evaluate_list_with P s ls (s',Rval vs) =
  (LENGTH vs = LENGTH ls) ∧
  ∃l. (LENGTH l = LENGTH ls) ∧ (LAST (s::l) = s') ∧
  ∀n. n < LENGTH ls ⇒ P (EL n (s::l)) (EL n ls) (EL n l, Rval (EL n vs))``,
gen_tac >> Induct >- (
  rw[evaluate_list_with_nil,LENGTH_NIL] >>
  PROVE_TAC[] ) >>
ntac 3 gen_tac >>
Cases >> rw[evaluate_list_with_cons,EQ_IMP_THM] >- fs[]
>- (
  qmatch_assum_rename_tac`P s h (s0,Rval v)`[] >>
  qexists_tac`s0::l`>>rw[] >>
  Cases_on`n`>>rw[] >>
  first_x_assum match_mp_tac >>
  fs[]) >>
qexists_tac`HD l` >>
first_assum (qspec_then `0` mp_tac) >> simp_tac(srw_ss())[] >> rw[] >>
qexists_tac `TL l` >>
Cases_on`l`>>fs[] >> rw[] >>
first_x_assum(qspec_then`SUC n`mp_tac) >>
rw[])

val evaluate_list_with_EVERY = store_thm(
"evaluate_list_with_EVERY",
``∀P es s s' vs. evaluate_list_with P s es (s',Rval vs) =
  (LENGTH vs = LENGTH es) ∧
  ∃l. (LENGTH l = SUC (LENGTH es)) ∧ (HD l = s) ∧ (LAST l = s') ∧
  EVERY (UNCURRY (UNCURRY P)) (ZIP (ZIP (FRONT l,es), ZIP (TL l,MAP Rval vs)))``,
gen_tac >> Induct >- (
  rw[evaluate_list_with_nil,EQ_IMP_THM,LENGTH_NIL] >-
    (qexists_tac`[s]` >> rw[]) >>
  Cases_on`l`>>fs[]>>
  Cases_on`t`>>fs[]) >>
rw[evaluate_list_with_cons,EQ_IMP_THM] >> rw[] >- (
  qexists_tac`s::l` >>
  Cases_on`l`>>fs[] ) >>
Cases_on `vs` >> fs[] >>
Cases_on`l`>>fs[] >>
Cases_on`t'`>>fs[] >>
qexists_tac`h'''` >> rw[] >>
qexists_tac`h'''::t''`>>fs[])
*)

val do_prim_app_FV = store_thm(
"do_prim_app_FV",
``∀s env op v1 v2 s' env' exp.
  (op ≠ Opapp) ∧
  (do_app s env op v1 v2 = SOME (s',env',exp)) ⇒
  (FV exp = {})``,
ntac 2 gen_tac >> Cases >>
Cases >> TRY (Cases_on `l`) >>
Cases >> TRY (Cases_on `l`) >>
rw[do_app_def] >> rw[] >>
fs[store_assign_def] >>
pop_assum mp_tac >> rw[] >> fs[])

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
``MAP FST (build_rec_env nopt defs env) = MAP FST defs ++ MAP FST env``,
rw[build_rec_env_def,bind_def,FOLDR_CONS_5tup] >>
rw[MAP_MAP_o,combinTheory.o_DEF,pairTheory.LAMBDA_PROD] >>
rw[FST_5tup])
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
``(∀tvs cenv s p v env n.
    (pmatch tvs cenv (s:α store) p v env =
     map_match (combin$C APPEND (DROP n env)) (pmatch tvs cenv s p v (TAKE n env)))) ∧
  (∀tvs cenv (s:α store) ps vs env n.
    (pmatch_list tvs cenv s ps vs env =
     map_match (combin$C APPEND (DROP n env)) (pmatch_list tvs cenv s ps vs (TAKE n env))))``,
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
strip_tac >- (
  rw[pmatch_def] >>
  BasicProvers.CASE_TAC >>
  fs[] ) >>
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
strip_tac >- rw[pmatch_def] >>
strip_tac >- rw[pmatch_def] >>
strip_tac >- rw[pmatch_def] >>
strip_tac >- rw[pmatch_def] >>
strip_tac >- (
  rw[pmatch_def] >>
  pop_assum (qspec_then`n`mp_tac) >>
  Cases_on `pmatch tvs cenv s p v (TAKE n env)`>>fs[] >>
  strip_tac >> res_tac >>
  pop_assum(qspec_then`LENGTH l`mp_tac) >>
  simp_tac(srw_ss())[TAKE_LENGTH_APPEND,DROP_LENGTH_APPEND] ) >>
strip_tac >- rw[pmatch_def] >>
strip_tac >- rw[pmatch_def])

val pmatch_plit = store_thm(
"pmatch_plit",
``(pmatch tvs cenv s (Plit l) v env = r) =
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
    |> Q.SPECL[`tvs`,`cenv`,`s`,`p`,`v`,`env`,`0`]
    |> SIMP_RULE(srw_ss())[]
  ,
    pmatch_APPEND
    |> CONJUNCT2
    |> Q.SPECL[`tvs`,`cenv`,`s`,`ps`,`vs`,`env`,`0`]
    |> SIMP_RULE(srw_ss())[]
  ])

(* TODO: move *)
val OPTION_EVERY_def = Define`
  (OPTION_EVERY P NONE = T) /\
  (OPTION_EVERY P (SOME v) = P v)`
val _ = export_rewrites["OPTION_EVERY_def"]
val OPTION_EVERY_cong = store_thm("OPTION_EVERY_cong",
  ``!o1 o2 P1 P2. (o1 = o2) /\ (!x. (o2 = SOME x) ==> (P1 x = P2 x)) ==>
                  (OPTION_EVERY P1 o1 = OPTION_EVERY P2 o2)``,
  Cases THEN SRW_TAC[][] THEN SRW_TAC[][])
val _ = DefnBase.export_cong"OPTION_EVERY_cong"
val OPTION_EVERY_mono = store_thm("OPTION_EVERY_mono",
  ``(!x. P x ==> Q x) ==> OPTION_EVERY P op ==> OPTION_EVERY Q op``,
  Cases_on `op` THEN SRW_TAC[][])
val _ = IndDefLib.export_mono"OPTION_EVERY_mono"

val store_to_fmap_def = Define`
  store_to_fmap s = FUN_FMAP (combin$C EL s) (count (LENGTH s))`

val (closed_rules,closed_ind,closed_cases) = Hol_reln`
(closed (Litv l)) ∧
(EVERY closed vs ⇒ closed (Conv cn vs)) ∧
(EVERY closed (MAP (FST o SND) env) ∧
 FV b ⊆ set (MAP FST env) ∪ {x}
⇒ closed (Closure env x topt b)) ∧
(EVERY closed (MAP (FST o SND) env) ∧
 ALL_DISTINCT (MAP FST defs) ∧
 MEM d (MAP FST defs) ∧
 (∀i d t1 x t2 b. i < LENGTH defs ∧ (EL i defs = (d,t1,x,t2,b)) ⇒
            FV b ⊆ set (MAP FST env) ∪ set (MAP FST defs) ∪ {x})
⇒ closed (Recclosure env defs d)) ∧
(closed (Loc n))`

val closed_lit = save_thm(
"closed_lit",
SIMP_RULE(srw_ss())[]
(Q.SPECL[`Litv l`]closed_cases))
val _ = export_rewrites["closed_lit"]

val closed_conv = save_thm(
"closed_conv",
SIMP_RULE(srw_ss())[]
(Q.SPECL[`Conv cn vs`]closed_cases))
val _ = export_rewrites["closed_conv"]

val closed_loc = save_thm("closed_loc",
SIMP_RULE(srw_ss())[]
(Q.SPECL[`Loc n`]closed_cases))
val _ = export_rewrites["closed_loc"]

val build_rec_env_closed = store_thm(
"build_rec_env_closed",
``∀tvs defs l.
  EVERY closed (MAP (FST o SND) l) ∧
  ALL_DISTINCT (MAP FST defs) ∧
  (∀i d t1 x t2 b. i < LENGTH defs ∧ (EL i defs = (d,t1,x,t2,b)) ⇒
   FV b ⊆ set (MAP FST l) ∪ set (MAP FST defs) ∪ {x})
  ⇒ EVERY closed (MAP (FST o SND) (build_rec_env tvs defs l))``,
rw[build_rec_env_def,bind_def,FOLDR_CONS_5tup] >>
rw[MAP_MAP_o,combinTheory.o_DEF,pairTheory.LAMBDA_PROD] >>
asm_simp_tac(srw_ss())[EVERY_MEM,MEM_MAP,pairTheory.EXISTS_PROD] >>
rw[MEM_EL] >>
rw[Once closed_cases] >- (
  rw[MEM_MAP,pairTheory.EXISTS_PROD,MEM_EL] >>
  PROVE_TAC[]) >>
first_x_assum match_mp_tac >>
PROVE_TAC[])

val closed_strongind=theorem"closed_strongind"

(*
val closed_store_FUPDATE = store_thm("closed_store_FUPDATE",
  ``∀n x s v. closed s v ∧ closed s (SND x) ⇒ closed (s |+ x) v``,
  not true?

  simp[GSYM AND_IMP_INTRO] >>
  gen_tac >>
  ho_match_mp_tac closed_strongind >>
  rw[] >> fsrw_tac[DNF_ss][EVERY_MEM] >>
  TRY (
    rw[Once closed_cases,EVERY_MEM] >>
    res_tac >> NO_TAC) >>
  Cases_on`x` >>
  fs[FLOOKUP_UPDATE,DOMSUB_FUPDATE_THM] >>
  fs[FLOOKUP_DEF] >> rw[] >> fs[]
  fsrw_tac[ETA_ss][]
  rw[]
  fs[DOMSUB_FUPDATE_THM]
  DB.find"FLOOKUP_UPDATE"
  fs[store_lookup_def,store_assign_def,store_remove_def] >>
  rw[] >> fs[] >>
  rw[EL_LUPDATE] )
*)

(* TODO move *)
val MEM_LUPDATE = store_thm("MEM_LUPDATE",
  ``!l x y i. MEM x (LUPDATE y i l) ==> (x = y) \/ MEM x l``,
  Induct THEN SRW_TAC[][LUPDATE_def] THEN
  Cases_on`i`THEN FULL_SIMP_TAC(srw_ss())[LUPDATE_def] THEN
  PROVE_TAC[])

val do_app_closed = store_thm(
"do_app_closed",
``∀s s' env op v1 v2 env' exp.
  EVERY closed (MAP (FST o SND) env) ∧
  closed v1 ∧ closed v2 ∧
  EVERY closed s ∧
  (do_app s env op v1 v2 = SOME (s',env',exp))
  ⇒ EVERY closed (MAP (FST o SND) env') ∧
    FV exp ⊆ set (MAP FST env') ∧
    EVERY closed s'``,
ntac 3 gen_tac >> Cases
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
  rw[do_app_def] >> fs[])
>- (
  Cases >> Cases >> rw[do_app_def,bind_def] >> fs[closed_cases] >>
  fs[] >> rw[] >>
  rw[Once INSERT_SING_UNION,Once UNION_COMM] >>
  pop_assum mp_tac >>
  BasicProvers.CASE_TAC >>
  strip_tac >> fs[] >>
  qmatch_assum_rename_tac `ALOOKUP defs dd = SOME pp`[] >>
  PairCases_on `pp` >> fs[] >> rw[] >> rw[Once closed_cases] >>
  fs[] >> rw[] >> rw[Once closed_cases] >>
  TRY (qmatch_abbrev_tac `EVERY closed X` >>
       PROVE_TAC[build_rec_env_closed]) >>
  imp_res_tac ALOOKUP_MEM >>
  fsrw_tac[DNF_ss][MEM_EL] >>
  fsrw_tac[DNF_ss][SUBSET_DEF] >>
  PROVE_TAC[])
>- (
  Cases >> Cases >> rw[do_app_def] >>
  pop_assum mp_tac >> BasicProvers.CASE_TAC >>
  rw[] >> fs[] >>
  fsrw_tac[DNF_ss][EVERY_MEM,MEM_MAP,FORALL_PROD] >>
  rw[] >>
  fs[store_assign_def] >> rw[] >>
  PROVE_TAC[MEM_LUPDATE,closed_lit,closed_conv,EVERY_MEM,closed_loc]))

val pmatch_closed = store_thm("pmatch_closed",
  ``(∀no cenv (s:α store) p v env env'.
      EVERY closed (MAP (FST o SND) env) ∧ closed v ∧
      EVERY closed s ∧
      (pmatch no cenv s p v env = Match env') ⇒
      EVERY closed (MAP (FST o SND) env') ∧
      (MAP FST env' = pat_bindings p [] ++ (MAP FST env))) ∧
    (∀no cenv (s:α store) ps vs env env'.
      EVERY closed (MAP (FST o SND) env) ∧ EVERY closed vs ∧
      EVERY closed s ∧
      (pmatch_list no cenv s ps vs env = Match env') ⇒
      EVERY closed (MAP (FST o SND) env') ∧
      (MAP FST env' = pats_bindings ps [] ++ MAP FST env))``,
  ho_match_mp_tac pmatch_ind >>
  strip_tac >- (
    rw[pmatch_def,bind_def,pat_bindings_def] >>
    rw[] >> rw[EXTENSION] ) >>
  strip_tac >- (
    rw[pmatch_def,pat_bindings_def] >> rw[] ) >>
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
    rw[pmatch_def,pat_bindings_def] >>
    srw_tac[ETA_ss][] ) >>
  strip_tac >- (
    rw[pmatch_def,pat_bindings_def] >>
    Cases_on `store_lookup lnum s`>>
    fsrw_tac[DNF_ss][store_lookup_def,EVERY_MEM,MEM_EL] >>
    PROVE_TAC[] ) >>
  strip_tac >- rw[pmatch_def] >>
  strip_tac >- rw[pmatch_def] >>
  strip_tac >- rw[pmatch_def] >>
  strip_tac >- rw[pmatch_def] >>
  strip_tac >- rw[pmatch_def] >>
  strip_tac >- rw[pmatch_def] >>
  strip_tac >- ( rw[pmatch_def] >> rw[] ) >>
  strip_tac >- rw[pmatch_def] >>
  strip_tac >- rw[pmatch_def] >>
  strip_tac >- rw[pmatch_def] >>
  strip_tac >- rw[pmatch_def] >>
  strip_tac >- rw[pmatch_def] >>
  strip_tac >- (rw[pmatch_def,pat_bindings_def] >> rw[]) >>
  strip_tac >- (
    rpt gen_tac >>
    strip_tac >>
    simp_tac(srw_ss())[pmatch_def,pat_bindings_def] >>
    Cases_on `pmatch no cenv s p v env` >> fs[] >>
    qmatch_assum_rename_tac `pmatch no cenv s p v env = Match env0`[] >>
    Cases_on `pmatch_list no cenv s ps vs env0` >> fs[] >>
    strip_tac >> fs[] >>
    simp[Once pat_bindings_acc,SimpRHS]) >>
  rw[pmatch_def])

val do_uapp_closed = store_thm("do_uapp_closed",
  ``∀s uop v s' v'.
    EVERY closed s ∧ closed v ∧
    (do_uapp s uop v = SOME (s',v')) ⇒
    EVERY closed s' ∧ closed v'``,
  gen_tac >> Cases >>
  rw[do_uapp_def,LET_THM,store_alloc_def] >>
  rw[EVERY_APPEND] >>
  Cases_on`v`>>fs[store_lookup_def]>>
  pop_assum mp_tac >> rw[] >> rw[]>>
  fsrw_tac[DNF_ss][EVERY_MEM,MEM_EL])

val every_result_rwt = store_thm("every_result_rwt",
  ``every_result P res = (∀v. (res = Rval v) ⇒ P v)``,
  Cases_on`res`>>rw[])

val pat_vars_deBruijn_subst_p = store_thm("pat_vars_deBruijn_subst_p",
  ``∀n x p. pat_vars (deBruijn_subst_p n x p) = pat_vars p``,
  ho_match_mp_tac deBruijn_subst_p_ind >>
  srw_tac[ETA_ss][deBruijn_subst_p_def] >>
  AP_TERM_TAC >>
  rw[GSYM LIST_TO_SET_MAP] >>
  AP_TERM_TAC >>
  rw[MAP_MAP_o,MAP_EQ_f] )
val _ = export_rewrites["pat_vars_deBruijn_subst_p"]

val FV_deBruijn_subst_e = store_thm("FV_deBruijn_subst_e",
  ``∀n x e. FV (deBruijn_subst_e n x e) = FV e``,
  ho_match_mp_tac deBruijn_subst_e_ind >>
  srw_tac[ETA_ss][deBruijn_subst_e_def,LET_THM]
  >- (
    AP_TERM_TAC >>
    rw[GSYM LIST_TO_SET_MAP] >>
    AP_TERM_TAC >>
    rw[MAP_MAP_o,MAP_EQ_f] )
  >- (
    AP_TERM_TAC >> AP_TERM_TAC >>
    rw[GSYM LIST_TO_SET_MAP] >>
    AP_TERM_TAC >>
    rw[MAP_MAP_o,MAP_EQ_f,UNCURRY] >>
    qmatch_assum_rename_tac`MEM Z pes`[] >>
    PairCases_on`Z`>>fs[] >>
    res_tac >> rw[] )
  >- (
    qmatch_abbrev_tac`A ∪ B = C ∪ D` >>
    `A = C` by (
      unabbrev_all_tac >>
      AP_TERM_TAC >>
      rw[GSYM LIST_TO_SET_MAP] >>
      AP_TERM_TAC >>
      rw[MAP_MAP_o,MAP_EQ_f] >>
      qmatch_assum_rename_tac`MEM f funs`[] >>
      PairCases_on`f`>>fs[] >>
      res_tac >>
      srw_tac[ETA_ss][combinTheory.o_DEF,UNCURRY] ) >>
    `B = D` by (
      unabbrev_all_tac >>
      AP_TERM_TAC >>
      rw[GSYM LIST_TO_SET_MAP] >>
      AP_TERM_TAC >>
      rw[MAP_MAP_o,MAP_EQ_f] >>
      qmatch_assum_rename_tac`MEM f funs`[] >>
      PairCases_on`f`>>fs[] ) >>
    rw[] ) )
val _ = export_rewrites["FV_deBruijn_subst_e"]

val closed_deBruijn_subst_v = store_thm("closed_deBruijn_subst_v",
  ``∀x v. closed (deBruijn_subst_v x v) = closed v``,
  ho_match_mp_tac deBruijn_subst_v_ind >>
  srw_tac[ETA_ss][deBruijn_subst_v_def]
  >- srw_tac[DNF_ss][EVERY_MEM,MEM_MAP]
  >- (ntac 2 (rw[Once closed_cases]))
  >- (
    ntac 2 (rw[Once closed_cases]) >>
    srw_tac[ETA_ss][MAP_MAP_o,combinTheory.o_DEF,UNCURRY] >>
    EQ_TAC >> rw[] >> rfs[EL_MAP,UNCURRY] >- (
      res_tac >> rfs[EL_MAP] ) >>
    qabbrev_tac`p=EL i funs` >>
    PairCases_on`p`>>fs[]>>rw[]>>
    res_tac>>fs[]))
val _ = export_rewrites["closed_deBruijn_subst_v"]

val closed_do_tapp = store_thm("closed_do_tapp",
  ``∀ts ta v. closed (do_tapp ts ta v) = closed v``,
  Cases >> rw[do_tapp_def] >>
  Cases_on`x`>>rw[] >>
  BasicProvers.CASE_TAC >>
  rw[])
val _ = export_rewrites["closed_do_tapp"]

val evaluate_closed = store_thm(
"evaluate_closed",
``(∀cenv s env exp res.
   evaluate cenv s env exp res ⇒
   FV exp ⊆ set (MAP FST env) ∧
   EVERY closed (MAP (FST o SND) env) ∧
   EVERY closed s
   ⇒
   EVERY closed (FST res) ∧
   every_result closed (SND res)) ∧
  (∀cenv s env exps ress.
   evaluate_list cenv s env exps ress ⇒
   BIGUNION (IMAGE FV (set exps)) ⊆ set (MAP FST env) ∧
   EVERY closed (MAP (FST o SND) env) ∧
   EVERY closed s
   ⇒
   EVERY closed (FST ress) ∧
   every_result (EVERY closed) (SND ress)) ∧
  (∀cenv s env v pes res.
   evaluate_match cenv s env v pes res ⇒
   BIGUNION (IMAGE (λ(p,e). FV e DIFF pat_vars p) (set pes)) ⊆ set (MAP FST env) ∧
   EVERY closed (MAP (FST o SND) env) ∧
   EVERY closed s ∧ closed v
   ⇒
   EVERY closed (FST res) ∧
   every_result closed (SND res))``,
ho_match_mp_tac evaluate_ind >>
strip_tac (* Lit *) >- rw[] >>
strip_tac (* Raise *) >- rw[] >>
strip_tac (* Handle *) >- rw[] >>
strip_tac (* Handle *) >- (
  rw[] >> fs[] >> rfs[] >>
  fsrw_tac[DNF_ss][SUBSET_DEF,bind_def,MEM_MAP,EXISTS_PROD] >>
  PROVE_TAC[] ) >>
strip_tac (* Handle *) >- rw[] >>
strip_tac (* Con *) >- ( rw[] >> fsrw_tac[ETA_ss][] ) >>
strip_tac (* Con *) >- rw[] >>
strip_tac (* Con *) >- ( rw[] >> fsrw_tac[ETA_ss][] ) >>
strip_tac (* Var *) >- (
  rw[] >>
  imp_res_tac ALOOKUP_MEM >>
  fs[EVERY_MEM,MEM_MAP,EXISTS_PROD] >>
  PROVE_TAC[]) >>
strip_tac (* Var *) >- rw[] >>
strip_tac (* Fun *) >- (
  rw[] >>
  rw[Once closed_cases] >>
  fsrw_tac[DNF_ss][SUBSET_DEF] >>
  PROVE_TAC[]) >>
strip_tac (* Uapp *) >- (
  rpt gen_tac >> strip_tac >> strip_tac >> fs[] >>
  PROVE_TAC[do_uapp_closed] ) >>
strip_tac (* Uapp *) >- rw[] >>
strip_tac (* Uapp *) >- rw[] >>
strip_tac (* App *) >- (
  rpt gen_tac >> ntac 2 strip_tac >> fs[] >> rfs[] >>
  PROVE_TAC[do_app_closed]) >>
strip_tac (* App *) >- rw[] >>
strip_tac (* App *) >- rw[] >>
strip_tac (* App *) >- rw[] >>
strip_tac (* Log *) >- (
  rw[] >> fs[] >>
  PROVE_TAC[do_log_FV,SUBSET_TRANS]) >>
strip_tac (* Log *) >- rw[] >>
strip_tac (* Log *) >- rw[] >>
strip_tac (* If *) >- (
  rw[] >> fs[] >>
  PROVE_TAC[do_if_FV,SUBSET_DEF,IN_UNION]) >>
strip_tac (* If *) >- rw[] >>
strip_tac (* If *) >- rw[] >>
strip_tac (* Mat *) >- rw[] >>
strip_tac (* Mat *) >- rw[] >>
strip_tac (* Let *) >- (
  rpt gen_tac >> ntac 2 strip_tac >>
  fs[] >> rfs[bind_def] >>
  fsrw_tac[DNF_ss][SUBSET_DEF,FORALL_PROD] >>
  PROVE_TAC[] ) >>
strip_tac (* Let *) >- rw[] >>
strip_tac (* Letrec *) >- (
  rpt gen_tac >> ntac 2 strip_tac >>
  first_x_assum match_mp_tac >>
  fs[FST_5tup] >> rfs[] >>
  conj_tac >- (
    fsrw_tac[DNF_ss][SUBSET_DEF,MEM_MAP,FORALL_PROD,EXISTS_PROD] >>
    PROVE_TAC[] ) >>
  match_mp_tac build_rec_env_closed >> fs[] >>
  fsrw_tac[DNF_ss][SUBSET_DEF,MEM_MAP,FORALL_PROD,EXISTS_PROD,MEM_EL] >>
  metis_tac[]) >>
strip_tac (* Letrec *) >- rw[] >>
strip_tac (* [] *) >- rw[] >>
strip_tac (* :: *) >- rw[] >>
strip_tac (* :: *) >- rw[] >>
strip_tac (* :: *) >- rw[] >>
strip_tac (* [] *) >- rw[] >>
strip_tac (* Match *) >- (
  rpt gen_tac >> ntac 2 strip_tac >>
  fs[] >> rfs[] >>
  first_x_assum match_mp_tac >>
  MP_TAC(SPEC_ALL(Q.SPEC`SOME 0`(INST_TYPE[alpha|->``:t``](CONJUNCT1 pmatch_closed)))) >>
  fs[pat_vars_pat_bindings] >>
  fsrw_tac[DNF_ss][SUBSET_DEF,FORALL_PROD,EXTENSION] >>
  metis_tac[]) >>
strip_tac (* Match *) >- rw[] >>
strip_tac (* Match *) >- rw[] >>
rw[])

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

(* TODO: categorise *)

val build_rec_env_MAP = store_thm("build_rec_env_MAP",
  ``build_rec_env tvs funs env = MAP (λ(f,cdr). (f, (Recclosure env funs f,add_tvs tvs (FST cdr)))) funs ++ env``,
  rw[build_rec_env_def] >>
  qho_match_abbrev_tac `FOLDR (f env funs) env funs = MAP (g env funs) funs ++ env` >>
  qsuff_tac `∀funs env env0 funs0. FOLDR (f env0 funs0) env funs = MAP (g env0 funs0) funs ++ env` >- rw[]  >>
  unabbrev_all_tac >> simp[] >>
  Induct >> rw[bind_def] >>
  PairCases_on`h` >> rw[])

val _ = Parse.overload_on("env_range",``λenv:α envE. IMAGE (FST o SND) (set env)``)

val all_cns_def = tDefine "all_cns"`
  (all_cns (Litv _) = {}) ∧
  (all_cns (Conv cn vs) = cn INSERT BIGUNION (IMAGE all_cns (set vs))) ∧
  (all_cns (Closure env _ _ _) = BIGUNION (IMAGE all_cns (env_range env))) ∧
  (all_cns (Recclosure env _ _) = BIGUNION (IMAGE all_cns (env_range env))) ∧
  (all_cns (Loc _) = {})`
  (WF_REL_TAC `measure (v_size ARB)` >>
   srw_tac[ARITH_ss][v1_size_thm,v4_size_thm,SUM_MAP_v2_size_thm,SUM_MAP_v3_size_thm] >>
   TRY (
     Q.ISPEC_THEN`v_size ARB`imp_res_tac SUM_MAP_MEM_bound >>
     fsrw_tac[ARITH_ss][] >> NO_TAC ) >>
   `MEM (FST (SND x)) (MAP FST (MAP SND env))` by ( rw[MEM_MAP] >> PROVE_TAC[] ) >>
   Q.ISPEC_THEN`v_size ARB`imp_res_tac SUM_MAP_MEM_bound >>
   fsrw_tac[ARITH_ss][])
val all_cns_def = save_thm("all_cns_def",SIMP_RULE(srw_ss()++ETA_ss)[]all_cns_def)
val _ = export_rewrites["all_cns_def"]

(* TODO: move *)
val IN_FRANGE_o_f_suff = store_thm("IN_FRANGE_o_f_suff",
  ``(∀v. v ∈ FRANGE fm ⇒ P (f v)) ⇒ ∀v. v ∈ FRANGE (f o_f fm) ⇒ P v``,
  rw[IN_FRANGE] >> rw[] >> first_x_assum match_mp_tac >> PROVE_TAC[])

val do_app_all_cns = store_thm("do_app_all_cns",
  ``∀cns s env op v1 v2 s' env' exp.
      all_cns v1 ⊆ cns ∧ all_cns v2 ⊆ cns ∧
      BIGUNION (IMAGE all_cns (env_range env)) ⊆ cns ∧
      BIGUNION (IMAGE all_cns (set s)) ⊆ cns ∧
      (do_app s env op v1 v2 = SOME (s',env',exp))
      ⇒
      BIGUNION (IMAGE all_cns (set s')) ⊆ cns ∧
      BIGUNION (IMAGE all_cns (env_range env')) ⊆ cns``,
  ntac 3 gen_tac >> Cases >>
  Cases >> TRY (Cases_on`l`) >>
  Cases >> TRY (Cases_on`l`) >>
  rw[do_app_def] >> rw[] >> fs[bind_def] >>
  TRY (
    pop_assum mp_tac >>
    BasicProvers.CASE_TAC >>
    PairCases_on`x`>>rw[]>>
    rw[] >>
    TRY(PairCases_on`h`) >>
    rw[build_rec_env_MAP,LIST_TO_SET_MAP,GSYM IMAGE_COMPOSE,combinTheory.o_DEF,LAMBDA_PROD] >>
    fsrw_tac[DNF_ss][SUBSET_DEF,FORALL_PROD] >>
    metis_tac[]) >>
  TRY (
    pop_assum mp_tac >>
    BasicProvers.CASE_TAC >>
    rw[] >> fs[store_assign_def] >> rw[] >>
    fsrw_tac[DNF_ss][SUBSET_DEF,FORALL_PROD] >> rw[] >>
    imp_res_tac MEM_LUPDATE >> fs[] >> rw[] >>
    TRY (qmatch_assum_rename_tac`MEM z t`[]>>PairCases_on`z`>>fs[]) >>
    metis_tac[]))

val pmatch_all_cns = store_thm("pmatch_all_cns",
  ``(∀tvs cenv (s:α store) p v env env'. (pmatch tvs cenv s p v env = Match env') ⇒
    BIGUNION (IMAGE all_cns (env_range env')) ⊆
    all_cns v ∪
    BIGUNION (IMAGE all_cns (env_range env)) ∪
    BIGUNION (IMAGE all_cns (set s))) ∧
    (∀tvs cenv (s:α store) ps vs env env'. (pmatch_list tvs cenv s ps vs env = Match env') ⇒
    BIGUNION (IMAGE all_cns (env_range env')) ⊆
    BIGUNION (IMAGE all_cns (set vs)) ∪
    BIGUNION (IMAGE all_cns (env_range env)) ∪
    BIGUNION (IMAGE all_cns (set s)))``,
  ho_match_mp_tac pmatch_ind >>
  rw[pmatch_def,bind_def] >>
  BasicProvers.EVERY_CASE_TAC >> fs[] >>
  rfs[] >>
  fsrw_tac[DNF_ss][SUBSET_DEF,store_lookup_def,FORALL_PROD,EXISTS_PROD] >>
  rw[] >> metis_tac[MEM_EL])

val do_uapp_all_cns = store_thm("do_uapp_all_cns",
  ``∀cns s uop v s' v'.
      all_cns v ⊆ cns ∧
      BIGUNION (IMAGE all_cns (set s)) ⊆ cns ∧
      (do_uapp s uop v = SOME (s',v')) ⇒
      all_cns v' ⊆ cns ∧ BIGUNION (IMAGE all_cns (set s')) ⊆ cns``,
  ntac 2 gen_tac >> Cases >>
  Cases >> TRY (Cases_on`l`) >>
  rw[do_uapp_def,LET_THM,store_alloc_def] >>
  fsrw_tac[DNF_ss][SUBSET_DEF,store_lookup_def] >>
  TRY (pop_assum mp_tac >> rw[]) >>
  metis_tac[MEM_EL])

val BIGUNION_IMAGE_set_SUBSET = store_thm("BIGUNION_IMAGE_set_SUBSET",
  ``(BIGUNION (IMAGE f (set ls)) ⊆ s) =
    (∀x. MEM x ls ⇒ f x ⊆ s)``,
  srw_tac[DNF_ss][SUBSET_DEF] >> metis_tac[])

val all_cns_deBruijn_subst_v = store_thm("all_cns_deBruijn_subst_v",
  ``∀x v. all_cns (deBruijn_subst_v x v) = all_cns v``,
  ho_match_mp_tac deBruijn_subst_v_ind >>
  srw_tac[ETA_ss][deBruijn_subst_v_def] >>
  AP_TERM_TAC >> AP_TERM_TAC >>
  simp[GSYM LIST_TO_SET_MAP] >>
  AP_TERM_TAC >>
  rw[MAP_MAP_o,MAP_EQ_f])
val _ = export_rewrites["all_cns_deBruijn_subst_v"]

val all_cns_do_tapp = store_thm("all_cns_do_tapp",
  ``∀ts ta v. all_cns (do_tapp ts ta v) = all_cns v``,
  rw[do_tapp_def] >>
  BasicProvers.EVERY_CASE_TAC >>
  rw[])
val _ = export_rewrites["all_cns_do_tapp"]

val evaluate_all_cns = store_thm("evaluate_all_cns",
  ``(∀cenv s env exp res. evaluate cenv s env exp res ⇒
       (∀v. v ∈ env_range env ∨ MEM v s ⇒ all_cns v ⊆ set (MAP FST cenv)) ⇒
       every_result (λv. all_cns v ⊆ set (MAP FST cenv)) (SND res) ∧
       (∀v. MEM v (FST res) ⇒ all_cns v ⊆ set (MAP FST cenv))) ∧
    (∀cenv s env exps ress. evaluate_list cenv s env exps ress ⇒
       (∀v. v ∈ env_range env ∨ MEM v s ⇒ all_cns v ⊆ set (MAP FST cenv)) ⇒
       every_result (EVERY (λv. all_cns v ⊆ set (MAP FST cenv))) (SND ress) ∧
       (∀v. MEM v (FST ress) ⇒ all_cns v ⊆ set (MAP FST cenv))) ∧
    (∀cenv s env v pes res. evaluate_match cenv s env v pes res ⇒
      (∀v. v ∈ env_range env ∨ MEM v s ⇒ all_cns v ⊆ set (MAP FST cenv)) ∧
      all_cns v ⊆ set (MAP FST cenv) ⇒
      every_result (λw. all_cns w ⊆ set (MAP FST cenv)) (SND res) ∧
      (∀v. MEM v (FST res) ⇒ all_cns v ⊆ set (MAP FST cenv)))``,
  ho_match_mp_tac evaluate_ind >>
  strip_tac (* Lit *) >- rw[] >>
  strip_tac (* Raise *) >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac (* Handle *) >- (
    rpt gen_tac >> ntac 2 strip_tac >>
    first_x_assum match_mp_tac >>
    fsrw_tac[DNF_ss][bind_def] >>
    ho_match_mp_tac IN_FRANGE_DOMSUB_suff >> rw[]) >>
  strip_tac >- rw[] >>
  strip_tac (* Con *) >- (
    srw_tac[DNF_ss][MEM_MAP] >>
    fs[do_con_check_def] >>
    Cases_on `ALOOKUP cenv cn` >> fs[] >>
    qexists_tac `(cn,x)` >>
    imp_res_tac ALOOKUP_MEM >>
    fs[] >>
    fsrw_tac[DNF_ss][SUBSET_DEF,MEM_MAP,EVERY_MEM] >>
    fsrw_tac[DNF_ss][MEM_EL,SUBSET_DEF] >>
    metis_tac[EL_MAP] ) >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rw[] >>
    imp_res_tac ALOOKUP_MEM >>
    fs[FORALL_PROD,EXISTS_PROD] >>
    first_x_assum match_mp_tac >>
    metis_tac[] ) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rw[] >>
    fsrw_tac[DNF_ss][SUBSET_DEF,MEM_MAP,EXISTS_PROD,FORALL_PROD] >>
    metis_tac[] ) >>
  strip_tac (* Uapp *) >- (
    rpt gen_tac >> ntac 2 strip_tac >> fs[] >>
    qmatch_assum_rename_tac`do_uapp s0 uop v = SOME (s',v')`[] >>
    Q.ISPECL_THEN[`set (MAP FST cenv)`,`s0`,`uop`,`v`,`s'`,`v'`]mp_tac(do_uapp_all_cns) >>
    simp[BIGUNION_IMAGE_set_SUBSET] >> metis_tac[]) >>
  strip_tac >- ( rpt gen_tac >> ntac 2 strip_tac >> fs[] >> PROVE_TAC[] ) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rpt gen_tac >> ntac 2 strip_tac >>
    first_x_assum match_mp_tac >> fs[] >>
    fsrw_tac[DNF_ss][] >>
    fsrw_tac[DNF_ss][SUBSET_DEF] >>
    Q.ISPECL_THEN[`set (MAP FST cenv)`,`s3`,`env`,`op`,`v1`,`v2`,`s''`,`env'`,`exp''`]
      (mp_tac o SIMP_RULE(srw_ss()++DNF_ss)[SUBSET_DEF]) do_app_all_cns >>
    metis_tac[]) >>
  strip_tac >- ( rw[] >> metis_tac[] ) >>
  strip_tac >- ( rw[] >> metis_tac[] ) >>
  strip_tac >- rw[] >>
  strip_tac (* Log *) >- ( rpt gen_tac >> ntac 2 strip_tac >> fs[] >> PROVE_TAC[] ) >>
  strip_tac >- ( rw[] >> metis_tac[] ) >>
  strip_tac >- rw[] >>
  strip_tac (* If *) >- ( rw[] >> metis_tac[] ) >>
  strip_tac >- ( rw[] >> metis_tac[] ) >>
  strip_tac >- rw[] >>
  strip_tac >- ( rw[] >> metis_tac[] ) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rpt gen_tac >> ntac 2 strip_tac >> fs[] >>
    first_x_assum match_mp_tac >>
    fsrw_tac[DNF_ss][bind_def] >>
    ho_match_mp_tac IN_FRANGE_DOMSUB_suff >>
    PROVE_TAC[]) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rpt gen_tac >> ntac 2 strip_tac >> fs[] >>
    first_x_assum match_mp_tac >>
    fsrw_tac[DNF_ss][] >>
    simp[build_rec_env_MAP,MEM_MAP,EXISTS_PROD] >>
    rw[] >> rw[] >>
    fsrw_tac[DNF_ss][MEM_MAP,FORALL_PROD,SUBSET_DEF,EXISTS_PROD] >>
    metis_tac[]) >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- ( rw[] >> PROVE_TAC[] ) >>
  strip_tac >- rw[] >>
  strip_tac >- ( rw[] >> PROVE_TAC[] ) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rpt gen_tac >> ntac 2 strip_tac >> fs[] >>
    first_x_assum match_mp_tac >>
    imp_res_tac pmatch_all_cns >>
    fsrw_tac[DNF_ss][SUBSET_DEF] >>
    metis_tac[]) >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- rw[])

val all_locs_def = tDefine "all_locs"`
  (all_locs (Litv _) = {}) ∧
  (all_locs (Conv _ vs) = BIGUNION (IMAGE all_locs (set vs))) ∧
  (all_locs (Closure env _ _ _) = BIGUNION (IMAGE all_locs (env_range env))) ∧
  (all_locs (Recclosure env _ _) = BIGUNION (IMAGE all_locs (env_range env))) ∧
  (all_locs (Loc n) = {n})`
(WF_REL_TAC `measure (v_size ARB)` >>
 srw_tac[ARITH_ss][v1_size_thm,v4_size_thm,SUM_MAP_v2_size_thm,SUM_MAP_v3_size_thm] >>
 TRY (
   Q.ISPEC_THEN`v_size ARB`imp_res_tac SUM_MAP_MEM_bound >>
   fsrw_tac[ARITH_ss][] >> NO_TAC ) >>
 `MEM (FST (SND x)) (MAP FST (MAP SND env))` by ( rw[MEM_MAP] >> PROVE_TAC[] ) >>
 Q.ISPEC_THEN`v_size ARB`imp_res_tac SUM_MAP_MEM_bound >>
 fsrw_tac[ARITH_ss][])
val _ = export_rewrites["all_locs_def"]

val reachable_def = tDefine "reachable"`
  reachable s n = n INSERT case FLOOKUP s n of NONE => {}
  | SOME v => BIGUNION (IMAGE (reachable (s \\ n)) (all_locs v))`
(WF_REL_TAC`measure (CARD o FDOM o FST)` >>
 srw_tac[ARITH_ss][FLOOKUP_DEF] >>
 Cases_on`CARD (FDOM s)`>>fs[])

val _ = export_theory()
