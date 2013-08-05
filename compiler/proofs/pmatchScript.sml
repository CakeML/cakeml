open HolKernel bossLib boolLib boolSimps pairTheory listTheory pred_setTheory finite_mapTheory alistTheory relationTheory SatisfySimps arithmeticTheory rich_listTheory lcsymtacs
open LibTheory SemanticPrimitivesTheory terminationTheory miscTheory semanticsExtraTheory CompilerLibTheory IntLangTheory ToIntLangTheory compilerTerminationTheory intLangExtraTheory
val _ = new_theory "pmatch"
val fsd = full_simp_tac std_ss

(* Characterise MAP-like constants *)

val exps_to_Cexps_MAP = store_thm(
"exps_to_Cexps_MAP",
``∀s es. exps_to_Cexps s es = MAP (exp_to_Cexp s) es``,
gen_tac >> Induct >> rw[exp_to_Cexp_def])

val pes_to_Cpes_MAP = store_thm(
"pes_to_Cpes_MAP",
``∀s pes. pes_to_Cpes s pes = MAP (λ(p,e). let (s',Cp) = pat_to_Cpat s p in (Cp, exp_to_Cexp s' e)) pes``,
gen_tac >> Induct >- rw[exp_to_Cexp_def] >>
Cases >> rw[exp_to_Cexp_def])

val defs_to_Cdefs_MAP = store_thm(
"defs_to_Cdefs_MAP",
``∀s defs. defs_to_Cdefs s defs = MAP (λ(d,vn,e). (NONE, (1,exp_to_Cexp (s with <|bvars := vn::s.bvars|>) e))) defs``,
gen_tac >> Induct >- rw[exp_to_Cexp_def] >>
qx_gen_tac `d` >> PairCases_on `d` >> rw[exp_to_Cexp_def])

val vs_to_Cvs_MAP = store_thm(
"vs_to_Cvs_MAP",
``∀m s vs. vs_to_Cvs m s vs = MAP (v_to_Cv m s) vs``,
ntac 2 gen_tac >> Induct >> rw[v_to_Cv_def])

val env_to_Cenv_MAP = store_thm(
"env_to_Cenv_MAP",
``∀m s env. env_to_Cenv m s env = MAP (v_to_Cv m s o SND) env``,
ntac 2 gen_tac >> Induct >- rw[exp_to_Cexp_def,v_to_Cv_def] >>
qx_gen_tac`h` >> PairCases_on`h` >>
rw[exp_to_Cexp_def,v_to_Cv_def])

val Cpat_vars_list_SUM_MAP = store_thm("Cpat_vars_list_SUM_MAP",
  ``∀ps. Cpat_vars_list ps = SUM (MAP Cpat_vars ps)``,
  Induct >> rw[])

val pats_to_Cpats_LENGTH = store_thm("pats_to_Cpats_LENGTH",
  ``∀ps m. LENGTH (SND (pats_to_Cpats m ps)) = LENGTH ps``,
  Induct >> rw[pat_to_Cpat_def] >> fs[] >> metis_tac[SND])

(* free vars lemmas *)

val free_vars_remove_mat_vp_SUBSET = store_thm(
"free_vars_remove_mat_vp_SUBSET",
``(∀p fk sk v. set (free_vars (remove_mat_vp fk sk v p)) ⊆
  {v;fk} ∪ set (lshift (Cpat_vars p) (free_vars sk))) ∧
(∀ps fk sk v n. set (free_vars (remove_mat_con fk sk v n ps)) ⊆
  {v;fk} ∪ set (lshift (Cpat_vars_list ps) (free_vars sk)))``,
ho_match_mp_tac (TypeBase.induction_of(``:Cpat``)) >>
strip_tac >- (
  rw[SUBSET_DEF,MEM_MAP,MEM_FILTER] >> PROVE_TAC[]) >>
strip_tac >- (rw[SUBSET_DEF,MEM_FILTER] >> PROVE_TAC[]) >>
strip_tac >- (
  rw[SUBSET_DEF,MEM_MAP,MEM_FILTER] >>
  pop_assum mp_tac >> rw[] >>
  PROVE_TAC[] ) >>
strip_tac >- (
  rw[SUBSET_DEF,MEM_MAP,MEM_FILTER] >>
  qmatch_assum_abbrev_tac`MEM z (free_vars (remove_mat_vp X Y Z p))` >>
  first_assum(qspecl_then[`X`,`Y`,`Z`,`z`]mp_tac) >>
  simp[] >>
  spose_not_then strip_assume_tac >>
  unabbrev_all_tac >>
  fsrw_tac[ARITH_ss][] >> rw[] >>
  rev_full_simp_tac(srw_ss()++ARITH_ss)[] >>
  res_tac >> fsrw_tac[ARITH_ss][] >>
  rw[] >> fsrw_tac[DNF_ss,ARITH_ss][] >>
  pop_assum mp_tac >> srw_tac[ARITH_ss][] >>
  first_x_assum(qspec_then`v'`strip_assume_tac) >> rfs[] >>
  fsrw_tac[ARITH_ss][]) >>
strip_tac >- rw[] >>
srw_tac[DNF_ss][LET_THM,SUBSET_DEF] >>
first_x_assum(qspecl_then[`fk+1+Cpat_vars p`,`shift 1 (Cpat_vars_list ps + Cpat_vars p) sk`,`v+1+Cpat_vars p`,`n+1`]mp_tac) >>
qmatch_assum_abbrev_tac`MEM z (free_vars (remove_mat_vp fk0 sk0 v0 p))` >>
first_x_assum(qspecl_then[`fk0`,`sk0`,`v0`,`z`]mp_tac) >>
unabbrev_all_tac >> srw_tac[ARITH_ss][PRE_SUB1] >- (
  disj1_tac >> disj2_tac >> simp[] ) >>
first_x_assum(qspec_then`m'`mp_tac) >>
simp[] >> strip_tac >> simp[] >> rw[] >>
pop_assum mp_tac >> rw[] >> fsrw_tac[ARITH_ss][] >>
metis_tac[NOT_LESS])

val free_vars_remove_mat_var_SUBSET = store_thm(
"free_vars_remove_mat_var_SUBSET",
``∀b v pes. set (free_vars (remove_mat_var b v pes)) ⊆ {v} ∪ BIGUNION (IMAGE (λ(p,e). set (lshift (Cpat_vars p) (free_vars e))) (set pes))``,
ho_match_mp_tac remove_mat_var_ind >>
strip_tac >- rw[remove_mat_var_def] >>
srw_tac[DNF_ss][remove_mat_var_def,SUBSET_DEF,LET_THM] >-
  metis_tac[] >>
qspecl_then[`p`,`0`,`shift 1 (Cpat_vars p) sk`,`v + 1`]mp_tac(CONJUNCT1 free_vars_remove_mat_vp_SUBSET) >>
rw[SUBSET_DEF] >>
pop_assum(qspec_then`m`mp_tac) >>
srw_tac[ARITH_ss][] >> fsrw_tac[ARITH_ss][] >>
pop_assum mp_tac >> srw_tac[ARITH_ss][] >>
metis_tac[NOT_LESS])

(* Misc. lemmas *)

val no_labs_remove_mat_vp = store_thm("no_labs_remove_mat_vp",
  ``(∀p fk e x. no_labs (remove_mat_vp fk e x p) = no_labs e) ∧
    (∀ps fk e x n. no_labs (remove_mat_con fk e x n ps) = no_labs e)``,
  ho_match_mp_tac(TypeBase.induction_of(``:Cpat``)) >> simp[])
val _ = export_rewrites["no_labs_remove_mat_vp"]

val no_labs_remove_mat_var = store_thm("no_labs_remove_mat_var",
  ``∀b x pes. no_labs (remove_mat_var b x pes) ⇔ no_labs_list (MAP SND pes)``,
  ho_match_mp_tac remove_mat_var_ind >> rw[remove_mat_var_def] >> simp[] >> metis_tac[])
val _ = export_rewrites["no_labs_remove_mat_var"]

val pat_to_Cpat_cnmap = store_thm("pat_to_Cpat_cnmap",
  ``(∀p m. (FST (pat_to_Cpat m p)).cnmap = m.cnmap) ∧
    (∀ps m. (FST (pats_to_Cpats m ps)).cnmap = m.cnmap)``,
  ho_match_mp_tac (TypeBase.induction_of``:pat``) >>
  rw[pat_to_Cpat_def] >> metis_tac[FST])

val SND_pat_to_Cpat_cnmap = store_thm(
"SND_pat_to_Cpat_cnmap",
``(∀p m m'. (m.cnmap = m'.cnmap) ⇒ (SND (pat_to_Cpat m p) = SND (pat_to_Cpat m' p))) ∧
  (∀ps m m'. (m.cnmap = m'.cnmap) ⇒ (SND (pats_to_Cpats m ps) = SND (pats_to_Cpats m' ps)))``,
ho_match_mp_tac (TypeBase.induction_of``:pat``) >>
strip_tac >- rw[pat_to_Cpat_def] >>
strip_tac >- rw[pat_to_Cpat_def] >>
strip_tac >- (
  rw[pat_to_Cpat_def] >>
  qspecl_then[`ps`,`m`]strip_assume_tac(CONJUNCT2 pat_to_Cpat_cnmap)>>
  qspecl_then[`ps`,`m'`]strip_assume_tac(CONJUNCT2 pat_to_Cpat_cnmap)>>
  rfs[] >> first_x_assum(qspecl_then[`m`,`m'`]mp_tac) >>rw[] ) >>
strip_tac >- (
  rw[pat_to_Cpat_def] >>
  qspecl_then[`p`,`m`]strip_assume_tac(CONJUNCT1 pat_to_Cpat_cnmap)>>
  qspecl_then[`p`,`m'`]strip_assume_tac(CONJUNCT1 pat_to_Cpat_cnmap)>>
  rfs[] >> first_x_assum(qspecl_then[`m`,`m'`]mp_tac) >>rw[] ) >>
strip_tac >- rw[pat_to_Cpat_def] >>
rw[pat_to_Cpat_def] >>
qspecl_then[`p`,`m`]strip_assume_tac(CONJUNCT1 pat_to_Cpat_cnmap)>>
qspecl_then[`p`,`m'`]strip_assume_tac(CONJUNCT1 pat_to_Cpat_cnmap)>>
qmatch_assum_rename_tac`pats_to_Cpats m2 ps = (m3,Cps')`[] >>
qmatch_assum_rename_tac`pats_to_Cpats m0 ps = (m1,Cps)`[] >>
qspecl_then[`ps`,`m0`]strip_assume_tac(CONJUNCT2 pat_to_Cpat_cnmap)>>
qspecl_then[`ps`,`m2`]strip_assume_tac(CONJUNCT2 pat_to_Cpat_cnmap)>>
rfs[] >>
first_x_assum(qspecl_then[`m0`,`m2`]mp_tac)>>
first_x_assum(qspecl_then[`m`,`m'`]mp_tac)>>
rw[] )

(* intermediate language pattern-matching *)

val (Cpmatch_rules,Cpmatch_ind,Cpmatch_cases) = Hol_reln`
  (Cpmatch s CPvar v [v]) ∧
  (Cpmatch s (CPlit l) (CLitv l) []) ∧
  (Cpmatch s p v env ∧ (el_check n s = SOME v)
   ⇒ Cpmatch s (CPref p) (CLoc n) env) ∧
  (Cpmatch_list s ps vs env
   ⇒ Cpmatch s (CPcon n ps) (CConv n vs) env) ∧
  (Cpmatch_list s [] [] []) ∧
  (Cpmatch s p v env ∧ Cpmatch_list s ps vs envs
    ⇒ Cpmatch_list s (p::ps) (v::vs) (envs ++ env))`

val (Cpnomatch_rules,Cpnomatch_ind,Cpnomatch_cases) = Hol_reln`
  (l ≠ l' ⇒ Cpnomatch s (CPlit l) (CLitv l')) ∧
  (c ≠ c' ⇒ Cpnomatch s (CPcon c ps) (CConv c' vs)) ∧
  (Cpnomatch s p v ∧ (el_check n s = SOME v) ⇒
   Cpnomatch s (CPref p) (CLoc n)) ∧
  (Cpnomatch_list s ps vs ⇒
   Cpnomatch s (CPcon c ps) (CConv c vs)) ∧
  (Cpnomatch s p v ∧ (LENGTH ps = LENGTH vs) ⇒ Cpnomatch_list s (p::ps) (v::vs)) ∧
  (Cpmatch s p v env ∧ Cpnomatch_list s ps vs ⇒ Cpnomatch_list s (p::ps) (v::vs))`

val (Cpmatch_error_rules,Cpmatch_error_ind,Cpmatch_error_cases) = Hol_reln`
  (Cpmatch_error s (CPlit l) (CConv c vs)) ∧
  (Cpmatch_error s (CPlit l) (CRecClos env defs n)) ∧
  (Cpmatch_error s (CPlit l ) (CLoc m)) ∧
  (Cpmatch_error s (CPcon c ps) (CLitv l)) ∧
  (Cpmatch_error s (CPcon c ps) (CRecClos env defs n)) ∧
  (Cpmatch_error s (CPcon c ps) (CLoc m)) ∧
  (Cpmatch_error s (CPref p) (CLitv l)) ∧
  (Cpmatch_error s (CPref p) (CConv c vs)) ∧
  (Cpmatch_error s (CPref p) (CRecClos env defs n)) ∧
  ((el_check m s = NONE) ⇒ Cpmatch_error s (CPref p) (CLoc m)) ∧
  (Cpmatch_error s p v ∧ (el_check m s = SOME v) ⇒ Cpmatch_error s (CPref p) (CLoc m)) ∧
  (Cpmatch_list_error s ps vs ⇒ Cpmatch_error s (CPcon c ps) (CConv c' vs)) ∧
  (Cpmatch_list_error s (p::ps) []) ∧
  (Cpmatch_list_error s [] (v::vs)) ∧
  (Cpmatch_error s p v ⇒ Cpmatch_list_error s (p::ps) (v::vs)) ∧
  (Cpmatch_list_error s ps vs ⇒ Cpmatch_list_error s (p::ps) (v::vs))`

val Cpmatch_NOT_Cpnomatch = store_thm("Cpmatch_NOT_Cpnomatch",
  ``(∀p v env. Cpmatch s p v env ⇒ ¬Cpnomatch s p v) ∧
    (∀ps vs env. Cpmatch_list s ps vs env ⇒ ¬Cpnomatch_list s ps vs)``,
  ho_match_mp_tac Cpmatch_ind >>
  strip_tac >- rw[Once Cpnomatch_cases] >>
  strip_tac >- rw[Once Cpnomatch_cases] >>
  strip_tac >- ( rw[] >> rw[Once Cpnomatch_cases] ) >>
  strip_tac >- ( rw[] >> rw[Once Cpnomatch_cases] ) >>
  strip_tac >- rw[Once Cpnomatch_cases] >>
  rw[] >> rw[Once Cpnomatch_cases])

val Cpmatch_list_error_LENGTH = store_thm("Cpmatch_list_error_LENGTH",
 ``∀s ps vs. LENGTH ps ≠ LENGTH vs ⇒ Cpmatch_list_error s ps vs``,
 gen_tac >> Induct >> rw[Once Cpmatch_error_cases] >>
 Cases_on `vs` >> fs[])

val Cpmatch_trichotomy = store_thm("Cpmatch_trichotomy",
  ``(∀p s v. (∃env. Cpmatch s p v env) ∨ Cpnomatch s p v ∨ Cpmatch_error s p v) ∧
    (∀ps s vs.  (∃env. Cpmatch_list s ps vs env) ∨ Cpnomatch_list s ps vs ∨ Cpmatch_list_error s ps vs)``,
  ho_match_mp_tac(TypeBase.induction_of``:Cpat``) >>
  strip_tac >- rw[Once Cpmatch_cases] >>
  strip_tac >- (
    rw[Once Cpmatch_cases] >>
    rw[Once Cpmatch_error_cases] >>
    rw[Once Cpnomatch_cases] >>
    Cases_on `v` >> rw[] >> PROVE_TAC[] ) >>
  strip_tac >- (
    rw[] >>
    rw[Once Cpmatch_cases] >>
    rw[Once Cpnomatch_cases] >>
    rw[Once Cpmatch_error_cases] >>
    Cases_on `v` >> rw[] >>
    spose_not_then strip_assume_tac >>
    rfs[] >> fs[] >> PROVE_TAC[]) >>
  strip_tac >- (
    rw[] >>
    rw[Once Cpmatch_cases] >>
    rw[Once Cpnomatch_cases] >>
    rw[Once Cpmatch_error_cases] >>
    Cases_on `v` >> rw[] >>
    Cases_on `el_check n s` >> rw[]) >>
  strip_tac >- (
    rw[Once Cpmatch_cases] >>
    rw[Once Cpnomatch_cases] >>
    rw[Once Cpmatch_error_cases] >>
    Cases_on `vs` >> rw[] >> PROVE_TAC[] ) >>
  rw[] >>
  rw[Once Cpmatch_cases] >>
  rw[Once Cpnomatch_cases] >>
  rw[Once Cpmatch_error_cases] >>
  Cases_on `vs` >> rw[] >>
  PROVE_TAC[Cpmatch_list_error_LENGTH] )

val Cpmatch_determ = store_thm("Cpmatch_determ",
  ``(∀p v env. Cpmatch s p v env ⇒ ∀env'. Cpmatch s p v env' ⇒ (env' = env)) ∧
    (∀ps vs env. Cpmatch_list s ps vs env ⇒ ∀env'. Cpmatch_list s ps vs env' ⇒ (env' = env))``,
  ho_match_mp_tac Cpmatch_ind >>
  strip_tac >- rw[Once Cpmatch_cases] >>
  strip_tac >- rw[Once Cpmatch_cases] >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    rw[Once Cpmatch_cases] ) >>
  strip_tac >- (
    rw[] >>
    first_x_assum match_mp_tac >>
    fs[Once Cpmatch_cases] ) >>
  strip_tac >- rw[Once Cpmatch_cases] >>
  rw[] >>
  pop_assum mp_tac >>
  rw[Once Cpmatch_cases] >>
  PROVE_TAC[])

val (Cevaluate_match_rules,Cevaluate_match_ind,Cevaluate_match_cases) = Hol_reln`
  (Cevaluate_match s v [] [] NONE) ∧
  (Cpmatch s p v env
    ⇒ Cevaluate_match s v ((p,e)::pes) env (SOME e)) ∧
  (Cpnomatch s p v ∧ Cevaluate_match s v pes env r
    ⇒ Cevaluate_match s v ((p,e)::pes) env r)`

(* correctness *)

val Cpmatch_list_LENGTH = store_thm("Cpmatch_list_LENGTH",
  ``∀s ps vs menv. Cpmatch_list s ps vs menv ⇒ (LENGTH ps = LENGTH vs)``,
  gen_tac >> Induct >> rw[Once Cpmatch_cases] >> rw[] >> PROVE_TAC[])

val Cpmatch_list_nil = store_thm("Cpmatch_list_nil",
  ``(Cpmatch_list s [] vs e = ((vs = []) ∧ (e = []))) ∧
    (Cpmatch_list s ps [] e = ((ps = []) ∧ (e = [])))``,
  rw[Once Cpmatch_cases] >>
  rw[Once Cpmatch_cases] )
val _ = export_rewrites["Cpmatch_list_nil"]

val Cpmatch_list_APPEND = store_thm("Cpmatch_list_APPEND",
  ``∀s p0 p1 vs e. Cpmatch_list s (p0 ++ p1) vs e =
            ∃e0 e1. Cpmatch_list s p0 (TAKE (LENGTH p0) vs) e0 ∧
                    Cpmatch_list s p1 (DROP (LENGTH p0) vs) e1 ∧
                    (e = e1 ++ e0)``,
  gen_tac >> Induct >- (
    rw[Once Cpmatch_cases] >>
    Cases_on `p1` >> fs[] >>
    rw[Once Cpmatch_cases,SimpRHS] ) >>
  rw[Once Cpmatch_cases] >>
  Cases_on `vs` >> fs[] >>
  rw[Once Cpmatch_cases,SimpRHS] >>
  srw_tac[DNF_ss][] >>
  PROVE_TAC[])

val cenv = rand ``pmatch cenv``

val pmatch_Cpmatch = store_thm("pmatch_Cpmatch",
  ``(∀^cenv s p v env env'. (pmatch cenv s p v env = Match (env' ++ env))
      ⇒ ∀m. Cpmatch (MAP (v_to_Cv m.mvars m.cnmap) s) (SND (pat_to_Cpat m p)) (v_to_Cv m.mvars m.cnmap v) (env_to_Cenv m.mvars m.cnmap env')) ∧
    (∀^cenv s ps vs env env'. (pmatch_list cenv s ps vs env = Match (env' ++ env))
      ⇒ ∀m. Cpmatch_list (MAP (v_to_Cv m.mvars m.cnmap) s) (SND (pats_to_Cpats m ps)) (vs_to_Cvs m.mvars m.cnmap vs) (env_to_Cenv m.mvars m.cnmap env'))``,
  ho_match_mp_tac pmatch_ind >>
  strip_tac >- (
    rw[pmatch_def,bind_def,env_to_Cenv_MAP,pat_to_Cpat_def] >>
    rw[Once Cpmatch_cases] ) >>
  strip_tac >- (
    rw[pat_to_Cpat_def,Once Cpmatch_cases,v_to_Cv_def
      ,env_to_Cenv_MAP,pmatch_def]) >>
  strip_tac >- (
    fs[pmatch_def] >>
    rpt gen_tac >> strip_tac >>
    Cases_on `ALOOKUP cenv n` >> fs[] >>
    qmatch_assum_rename_tac `ALOOKUP cenv n = SOME p`[] >>
    PairCases_on `p` >> fs[] >>
    Cases_on `ALOOKUP cenv n'` >> fs[] >>
    qmatch_assum_rename_tac `ALOOKUP cenv n' = SOME p`[] >>
    PairCases_on `p` >> fs[] >>
    rw[] >> rfs[] >>
    fs[pat_to_Cpat_def,LET_THM,UNCURRY] >>
    simp[pat_to_Cpat_cnmap] >>
    imp_res_tac ALOOKUP_MEM >>
    simp[v_to_Cv_def] >>
    rw[Once Cpmatch_cases] >>
    rw[pat_to_Cpat_cnmap]) >>
  strip_tac >- (
    rw [pmatch_def, pat_to_Cpat_def] >>
    rw [v_to_Cv_def] >>
    rw [Once Cpmatch_cases] >>
    metis_tac [SND, pat_to_Cpat_cnmap, FST]) >>
  strip_tac >- (
    fs[pmatch_def] >>
    rpt gen_tac >> strip_tac >>
    Cases_on `store_lookup lnum s` >> fs[] >>
    gen_tac >> strip_tac >>
    fs[pat_to_Cpat_def,LET_THM,UNCURRY,v_to_Cv_def] >>
    rw[Once Cpmatch_cases] >>
    qexists_tac`v_to_Cv m.mvars m.cnmap x` >> rw[] >>
    fs[el_check_def,store_lookup_def,EL_MAP]) >>
  strip_tac >- rw[pmatch_def] >>
  strip_tac >- rw[pmatch_def] >>
  strip_tac >- rw[pmatch_def] >>
  strip_tac >- rw[pmatch_def] >>
  strip_tac >- rw[pmatch_def] >>
  strip_tac >- rw[pmatch_def] >>
  strip_tac >- rw[pmatch_def] >>
  strip_tac >- rw[pmatch_def] >>
  strip_tac >- rw[pmatch_def] >>
  strip_tac >- rw[pmatch_def] >>
  strip_tac >- rw[pmatch_def] >>
  strip_tac >- rw[pmatch_def] >>
  strip_tac >- (
    rw[pmatch_def,env_to_Cenv_MAP,pat_to_Cpat_def,vs_to_Cvs_MAP] >>
    rw[Once Cpmatch_cases] ) >>
  strip_tac >- (
    rw[pmatch_def] >>
    pop_assum mp_tac >>
    fs[Once pmatch_nil] >>
    rw[Once (CONJUNCT1 pmatch_nil)] >>
    Cases_on `pmatch cenv s p v []` >> fs[] >> rw[] >>
    qmatch_assum_rename_tac `pmatch cenv s p v [] = Match env0`[] >>
    qpat_assum`pmatch_list cenv s ps vs X = Y` mp_tac >>
    simp[Once pmatch_nil] >> strip_tac >>
    Cases_on `pmatch_list cenv s ps vs []` >> fs[] >> rw[] >>
    qmatch_assum_rename_tac `pmatch_list cenv s ps vs [] = Match env1`[] >>
    fs[Once (Q.INST[`env`|->`env0++env`]pmatch_nil)] >>
    fs[pat_to_Cpat_def,vs_to_Cvs_MAP,UNCURRY,env_to_Cenv_MAP,LET_THM] >>
    REWRITE_TAC[Once(rich_listTheory.CONS_APPEND)] >>
    REWRITE_TAC[Cpmatch_list_APPEND] >>
    simp[Once Cpmatch_cases] >>
    qexists_tac`MAP (v_to_Cv m.mvars m.cnmap o SND) env0` >>
    simp[] >>
    metis_tac[SND_pat_to_Cpat_cnmap,pat_to_Cpat_cnmap]) >>
  strip_tac >- (
    rw[pmatch_def,env_to_Cenv_MAP,pat_to_Cpat_def,vs_to_Cvs_MAP] >>
    rw[Once Cpmatch_cases] ) >>
  strip_tac >- (
    rw[pmatch_def] >>
    pop_assum mp_tac >>
    fs[Once pmatch_nil] >>
    rw[Once (CONJUNCT1 pmatch_nil)] >>
    Cases_on `pmatch cenv s p v []` >> fs[] >> rw[] >>
    qmatch_assum_rename_tac `pmatch cenv s p v [] = Match env0`[] >>
    qpat_assum`pmatch_list cenv s ps vs X = Y` mp_tac >>
    simp[Once pmatch_nil] >> strip_tac >>
    Cases_on `pmatch_list cenv s ps vs []` >> fs[] >> rw[] >>
    qmatch_assum_rename_tac `pmatch_list cenv s ps vs [] = Match env1`[] >>
    fs[Once (Q.INST[`env`|->`env0++env`]pmatch_nil)] >>
    fs[pat_to_Cpat_def,vs_to_Cvs_MAP,UNCURRY,env_to_Cenv_MAP,LET_THM] >>
    REWRITE_TAC[Once(rich_listTheory.CONS_APPEND)] >>
    REWRITE_TAC[Cpmatch_list_APPEND] >>
    simp[Once Cpmatch_cases] >>
    qexists_tac`MAP (v_to_Cv m.mvars m.cnmap o SND) env0` >>
    simp[] >>
    metis_tac[SND_pat_to_Cpat_cnmap,pat_to_Cpat_cnmap]) >>
  strip_tac >- rw[pmatch_def] >>
  strip_tac >- rw[pmatch_def] >>
  rw[pmatch_def])

val pmatch_Cpnomatch = store_thm("pmatch_Cpnomatch",
  ``(∀^cenv s p v env. (pmatch cenv s p v env = No_match)
      ⇒ ∀m. good_cmap cenv m.cnmap ⇒
            Cpnomatch (MAP (v_to_Cv m.mvars m.cnmap) s) (SND (pat_to_Cpat m p)) (v_to_Cv m.mvars m.cnmap v)) ∧
    (∀^cenv s ps vs env env'. (pmatch_list cenv s ps vs env = No_match) ∧ (LENGTH ps = LENGTH vs)
      ⇒ ∀m. good_cmap cenv m.cnmap ⇒
            Cpnomatch_list (MAP (v_to_Cv m.mvars m.cnmap) s) (SND (pats_to_Cpats m ps)) (vs_to_Cvs m.mvars m.cnmap vs))``,
  ho_match_mp_tac pmatch_ind >>
  strip_tac >- rw[pmatch_def] >>
  strip_tac >- (
    rw[pmatch_def,lit_same_type_def] >>
    rpt (pop_assum mp_tac) >>
    BasicProvers.CASE_TAC >>
    BasicProvers.CASE_TAC >>
    rw[pat_to_Cpat_def,Once Cpnomatch_cases,v_to_Cv_def] ) >>
  strip_tac >- (
    fs[pmatch_def] >>
    rpt gen_tac >> strip_tac >>
    Cases_on `ALOOKUP cenv n` >> fs[] >>
    qmatch_assum_rename_tac `ALOOKUP cenv n = SOME p`[] >>
    PairCases_on `p` >> fs[] >>
    Cases_on `ALOOKUP cenv n'` >> fs[] >>
    qmatch_assum_rename_tac `ALOOKUP cenv n' = SOME p`[] >>
    PairCases_on `p` >> fs[] >>
    rw[] >> pop_assum mp_tac >> rw[] >>
    simp[pat_to_Cpat_def] >> simp[v_to_Cv_def,FLOOKUP_DEF] >>
    `SOME n ∈ FDOM m.cnmap` by (
      imp_res_tac ALOOKUP_MEM >>
      fs[good_cmap_def,FORALL_PROD] >>
      metis_tac[] ) >>
    TRY (
      `SOME n' ∈ FDOM m.cnmap` by (
        imp_res_tac ALOOKUP_MEM >>
        fs[good_cmap_def,FORALL_PROD] >>
        metis_tac[] )) >>
    rw[Once Cpnomatch_cases] >- (
      simp[UNCURRY,pat_to_Cpat_cnmap] >>
      PROVE_TAC[SND,optionTheory.SOME_11,PAIR_EQ] ) >>
    simp[UNCURRY,pat_to_Cpat_cnmap] >>
    fs[good_cmap_def,FORALL_PROD] >>
    imp_res_tac ALOOKUP_MEM >>
    metis_tac[]) >>
  strip_tac >- (
    rw [pmatch_def, pat_to_Cpat_def] >>
    rw [v_to_Cv_def] >>
    rw [Once Cpnomatch_cases] >>
    metis_tac [SND, pat_to_Cpat_cnmap, FST]) >>
  strip_tac >- (
    rw[pmatch_def] >>
    Cases_on `store_lookup lnum s` >> fs[] >>
    rw[pat_to_Cpat_def,v_to_Cv_def] >>
    rw[Once Cpnomatch_cases] >>
    qexists_tac `v_to_Cv m.mvars m.cnmap x` >>
    first_x_assum (qspec_then`m`mp_tac) >> rw[] >>
    fs[store_to_fmap_def,store_lookup_def,el_check_def,EL_MAP] ) >>
  strip_tac >- rw[pmatch_def] >>
  strip_tac >- rw[pmatch_def] >>
  strip_tac >- rw[pmatch_def] >>
  strip_tac >- rw[pmatch_def] >>
  strip_tac >- rw[pmatch_def] >>
  strip_tac >- rw[pmatch_def] >>
  strip_tac >- rw[pmatch_def] >>
  strip_tac >- rw[pmatch_def] >>
  strip_tac >- rw[pmatch_def] >>
  strip_tac >- rw[pmatch_def] >>
  strip_tac >- rw[pmatch_def] >>
  strip_tac >- rw[pmatch_def] >>
  strip_tac >- rw[pmatch_def] >>
  strip_tac >- rw[pmatch_def] >>
  strip_tac >- rw[pmatch_def] >>
  strip_tac >- (
    rw[pmatch_def] >>
    qpat_assum`X = No_match`mp_tac>>
    fs[Once pmatch_nil] >>
    rw[Once (CONJUNCT1 pmatch_nil)] >>
    Cases_on `pmatch cenv s p v []` >> fs[] >> rw[] >- (
      rw[pat_to_Cpat_def,vs_to_Cvs_MAP] >>
      rw[Once Cpnomatch_cases] >>
      metis_tac[SND_pat_to_Cpat_cnmap,SND,pat_to_Cpat_cnmap,pats_to_Cpats_LENGTH]) >>
    rw[pat_to_Cpat_def,vs_to_Cvs_MAP] >>
    rw[Once Cpnomatch_cases] >>
    fs[vs_to_Cvs_MAP] >> rw[] >>
    `l = l ++ []` by rw[] >>
    qpat_assum `x = Match l` mp_tac >>
    pop_assum SUBST1_TAC >> strip_tac >>
    imp_res_tac pmatch_Cpmatch >>
    disj2_tac >>
    simp[LEFT_EXISTS_AND_THM] >>
    conj_tac >- metis_tac[SND] >>
    metis_tac[SND,pat_to_Cpat_cnmap,SND_pat_to_Cpat_cnmap,FST]) >>
  strip_tac >- rw[pmatch_def] >>
  rw[pmatch_def])

val matchres_def = Define`
  matchres (env:envE) cenv s env' e r = ∃env''. (env' = env'' ++ env) ∧ (r = (s, Rval (env'',e)))`

val evaluate_match_with_Cevaluate_match = store_thm("evaluate_match_with_Cevaluate_match",
  ``∀pes errv r. evaluate_match_with (matchres env) cenv s env v pes errv r ⇒
      ∀m. good_cmap cenv m.cnmap ⇒
        ((r = (s, Rerr (Rraise errv)))
            ⇒ Cevaluate_match (MAP (v_to_Cv m.mvars m.cnmap) (SND s)) (v_to_Cv m.mvars m.cnmap v)
                (MAP (λ(p,e). (SND (pat_to_Cpat m p),(p,e))) pes)
                [] NONE) ∧
        ∀env' (pe:pat#exp). (r = (s, Rval (env',pe)))
          ⇒ Cevaluate_match (MAP (v_to_Cv m.mvars m.cnmap) (SND s)) (v_to_Cv m.mvars m.cnmap v)
              (MAP (λ(p,e). (SND (pat_to_Cpat m p),(p,e))) pes)
              (env_to_Cenv m.mvars m.cnmap env') (SOME pe)``,
  ho_match_mp_tac evaluate_match_with_ind >>
  strip_tac >- ( rw[] >> rw[Once Cevaluate_match_cases] ) >>
  strip_tac >- (
    rw[] >> rw[Once Cevaluate_match_cases] >>
    fs[matchres_def] >>
    PROVE_TAC[pmatch_Cpmatch] ) >>
  strip_tac >- (
    rw[] >>
    rw[Once Cevaluate_match_cases] >>
    PROVE_TAC[pmatch_Cpnomatch] ) >>
  strip_tac >- rw[] >> rw[] )

val evaluate_match_with_matchres = store_thm("evaluate_match_with_matchres",
  ``∀(pes:(pat#exp)list) errv r. evaluate_match_with P cenv s env v pes errv r ⇒
            (SND r ≠ Rerr Rtype_error) ⇒
            ((SND r = Rerr (Rraise errv)) ∧
             evaluate_match_with (matchres env) cenv s env v pes errv (s, Rerr (Rraise errv)) ∧
             (FST r = s)) ∨
            ∃menv mr. evaluate_match_with (matchres env) cenv s env v pes errv (s, Rval (menv,mr)) ∧
                      P cenv s (menv++env) mr r``,
  ho_match_mp_tac evaluate_match_with_ind >>
  strip_tac >- rw[Once evaluate_match_with_cases] >>
  strip_tac >- (
    rw[] >>
    disj2_tac >>
    rw[Once evaluate_match_with_cases] >>
    rw[matchres_def] >>
    fs[Once pmatch_nil] >>
    Cases_on `pmatch cenv (SND s) p v []` >>fs[] >>
    PROVE_TAC[] ) >>
  strip_tac >- (
    rw[] >> fs[] >>
    rw[Once evaluate_match_with_cases] >>
    disj2_tac >>
    rw[Once evaluate_match_with_cases] >>
    PROVE_TAC[] ) >>
  strip_tac >- rw[] >>
  rw[])

val evaluate_match_with_matchres_closed = store_thm("evaluate_match_with_matchres_closed",
  ``∀(pes:(pat#exp)list) errv r. evaluate_match_with (matchres env) cenv s env v pes errv r ⇒
            EVERY (closed envM) (SND s) ∧ EVERY (closed envM) (MAP SND env) ∧ closed envM v ⇒
            every_result (λ(menv,mr). EVERY (closed envM) (MAP SND menv) ∧
                                      MEM mr pes ∧
                                      ((MAP FST menv) = pat_bindings (FST mr) []))
                         (λv. v = errv) (SND r) ``,
  ho_match_mp_tac evaluate_match_with_ind >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rw[matchres_def] >>
    fs[] >>
    fs[Once pmatch_nil] >>
    Cases_on `pmatch cenv (SND s) p v []` >> fs[] >>
    qspecl_then [`cenv`,`(SND s)`,`p`,`v`,`[]`] mp_tac (CONJUNCT1 pmatch_closed) >>
    fs[] >> fsrw_tac[DNF_ss][] >> metis_tac[] ) >>
  strip_tac >- (
    rw[] >> fs[] >>
    Cases_on `SND r` >> fs[] >>
    fs[UNCURRY] >>
    fsrw_tac[DNF_ss][] >>
    Cases_on`e'`>>fs[]) >>
  strip_tac >- rw[] >>
  rw[])

val evaluate_match_with_matchres_all_cns = store_thm("evaluate_match_with_matchres_all_cns",
  ``∀pes errv r. evaluate_match_with (matchres env) ^cenv s env v pes errv r ⇒
            (∀w. MEM w (SND s) ∨ MEM w (MAP SND env) ∨ (w = v) ⇒ all_cns w ⊆ cenv_dom cenv) ⇒
            (∀v. MEM v (SND (FST r)) ⇒ all_cns v ⊆ cenv_dom cenv) ∧
            every_result (λ(menv,mr). ∀v. MEM v (MAP SND menv) ⇒ all_cns v ⊆ cenv_dom cenv) (λv. v = errv) (SND r) ``,
  ho_match_mp_tac evaluate_match_with_ind >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rw[matchres_def] >>
    fs[] >>
    fs[Once pmatch_nil] >>
    Cases_on `pmatch cenv (SND s) p v []` >> fs[] >>
    qspecl_then[`cenv`,`(SND s)`,`p`,`v`,`[]`] mp_tac (CONJUNCT1 pmatch_all_cns) >>
    fs[] >>
    fsrw_tac[DNF_ss][SUBSET_DEF,MEM_MAP] >>
    metis_tac[]) >>
  strip_tac >- (
    rw[] >> fs[] >>
    Cases_on `SND r` >> fs[] >>
    fs[UNCURRY] >>
    fsrw_tac[DNF_ss][] >> PROVE_TAC[]) >>
  strip_tac >- rw[] >>
  rw[])

val Cevaluate_match_MAP_exp = store_thm("Cevaluate_match_MAP_exp",
  ``∀pes env r. Cevaluate_match s v pes env r ⇒
      ∀f. Cevaluate_match s v (MAP (λ(p,e). (p, f e)) pes) env (OPTION_MAP f r)``,
  ho_match_mp_tac Cevaluate_match_ind >>
  strip_tac >- rw[Once Cevaluate_match_rules] >>
  strip_tac >- rw[Once Cevaluate_match_cases] >>
  rw[] >>
  rw[Once Cevaluate_match_cases])

val Cpmatch_FDOM = store_thm("Cpmatch_FDOM",
  ``(∀p v env. Cpmatch s p v env ⇒ (LENGTH env = Cpat_vars p)) ∧
    (∀ps vs env. Cpmatch_list s ps vs env ⇒ (LENGTH env = SUM (MAP Cpat_vars ps)))``,
  ho_match_mp_tac Cpmatch_ind >> rw[] >> fsrw_tac[ARITH_ss][] >>
  pop_assum kall_tac >>
  Induct_on`ps` >> rw[])

val Cpmatch_closed = store_thm("Cpmatch_closed",
  ``(∀p v e. Cpmatch s p v e ⇒ Cclosed v ∧ (EVERY (Cclosed) s) ⇒ EVERY (Cclosed) e) ∧
    (∀ps vs e. Cpmatch_list s ps vs e ⇒ EVERY (Cclosed) vs ∧ (EVERY (Cclosed) s) ⇒ EVERY (Cclosed) e)``,
  ho_match_mp_tac Cpmatch_ind >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- (rw[] >> fs[el_check_def,EVERY_MEM,MEM_EL] >> PROVE_TAC[]) >>
  strip_tac >- (rw[] >> fs[Once Cclosed_cases]) >>
  rw[])

val Cpmatch_strongind = theorem"Cpmatch_strongind"

val Cpmatch_remove_mat = store_thm("Cpmatch_remove_mat",
  ``(∀p v menv. Cpmatch (SND s) p v menv ⇒
       ∀mod env x fk e r0.
         (el_check x env = SOME v) ∧
         set (free_vars e) ⊆ count (Cpat_vars p + LENGTH env) ∧
         fk < LENGTH env ∧
         no_labs e ∧
         Cevaluate mod s (menv ++ env) e r0
       ⇒ ∃r. Cevaluate mod s env (remove_mat_vp fk e x p) r ∧
             FST (FST r0) = FST (FST r) ∧
             EVERY2 (syneq) (SND (FST r0)) (SND (FST r)) ∧
             Cresult_rel syneq syneq (SND r0) (SND r)) ∧
    (∀ps vs menv. Cpmatch_list (SND s) ps vs menv ⇒
       ∀mod env x c vs0 menv0 fk e r0.
         (el_check x (menv0 ++ env) = SOME (CConv c (vs0++vs))) ∧
         set (free_vars e) ⊆ count (LENGTH (menv ++ menv0 ++ env)) ∧
         fk < LENGTH (menv0 ++ env) ∧
         no_labs e ∧
         Cevaluate mod s (menv ++ menv0 ++ env) e r0
       ⇒ ∃r. Cevaluate mod s (menv0 ++ env) (remove_mat_con fk e x (LENGTH vs0) ps) r ∧
             FST (FST r0) = FST (FST r) ∧
             EVERY2 (syneq) (SND (FST r0)) (SND (FST r)) ∧
             Cresult_rel syneq syneq (SND r0) (SND r))``,
  ho_match_mp_tac Cpmatch_strongind >>
  strip_tac >- (
    rw[remove_mat_var_def] >>
    rw[Once Cevaluate_cases] >>
    fs[el_check_def] >>
    metis_tac[Cresult_rel_syneq_refl,EVERY2_syneq_refl]) >>
  strip_tac >- (
    rw[remove_mat_vp_def] >>
    fs[el_check_def] >>
    rw[Once Cevaluate_cases] >>
    srw_tac[DNF_ss][] >>
    disj1_tac >>
    CONV_TAC (RESORT_EXISTS_CONV List.rev) >> qexists_tac `T` >>
    fs[] >>
    rw[Once Cevaluate_cases] >>
    rw[Once Cevaluate_cases] >>
    rw[Once Cevaluate_cases] >>
    rw[Once Cevaluate_cases] >>
    metis_tac[Cresult_rel_syneq_refl,EVERY2_syneq_refl]) >>
  strip_tac >- (
    rw[remove_mat_vp_def,LET_THM] >>
    rw[Once Cevaluate_cases] >>
    srw_tac[DNF_ss][] >>
    disj1_tac >>
    rw[Once Cevaluate_cases,LET_THM] >>
    fs[el_check_def] >> rw[] >>
    imp_res_tac Cpmatch_FDOM >>
    qspecl_then[`mod`,`s`,`menv++env`,`e`,`r0`]mp_tac(CONJUNCT1 Cevaluate_syneq) >>
    simp[] >>
    disch_then(qspecl_then[`λv1 v2. if v1 < LENGTH menv then (v2 = v1) else (v2 = v1+1)`
                          ,`mod`,`s`,`menv++(EL n (SND s)::env)`,`shift 1 (Cpat_vars p) e`]mp_tac) >>
    qmatch_abbrev_tac`(P ⇒ Q) ⇒ R` >>
    `P` by (
      unabbrev_all_tac >> simp[] >>
      conj_tac >- (
        simp[shift_def] >>
        match_mp_tac mkshift_thm >>
        simp[] ) >>
      lrw[EL_APPEND1,EL_APPEND2,EL_CONS,PRE_SUB1] ) >>
    simp[] >>
    map_every qunabbrev_tac[`P`,`Q`,`R`] >> fs[] >>
    disch_then(Q.X_CHOOSE_THEN`r1`strip_assume_tac) >>
    first_x_assum(qspecl_then[`mod`,`EL n (SND s)::env`,`0`,`fk+1`,`shift 1 (Cpat_vars p) e`,`r1`]mp_tac) >>
    simp[] >>
    qmatch_abbrev_tac`(P ⇒ Q) ⇒ R` >>
    `P` by (
      unabbrev_all_tac >>
      fsrw_tac[DNF_ss][EVERY_MEM,MEM_EL,SUBSET_DEF,ADD1] >>
      rw[] >> fsrw_tac[ARITH_ss][] >>
      res_tac >>
      fsrw_tac[ARITH_ss][] ) >>
    map_every qunabbrev_tac[`P`,`Q`,`R`] >> fs[] >>
    Cases_on`s`>>asm_simp_tac(srw_ss()++DNF_ss)[FORALL_PROD] >> fs[] >>
    metis_tac[Cresult_rel_syneq_trans,EVERY2_syneq_trans,FST,SND] ) >>
  strip_tac >- (
    rw[] >>
    rw[Once Cevaluate_cases] >>
    srw_tac[DNF_ss][] >>
    disj1_tac >>
    CONV_TAC (RESORT_EXISTS_CONV List.rev) >> qexists_tac `T` >>
    fs[] >>
    qexists_tac`s` >>
    fs[RIGHT_EXISTS_AND_THM,GSYM CONJ_ASSOC] >>
    conj_tac >- (
      rw[Once Cevaluate_cases] >>
      fs[el_check_def] ) >>
    `0 = LENGTH ([]:Cv list)` by rw[] >> pop_assum SUBST1_TAC >>
    `env = [] ++ env` by rw[] >> pop_assum SUBST1_TAC >>
    first_x_assum (match_mp_tac o MP_CANON) >>
    fs[FOLDL_UNION_BIGUNION] >>
    imp_res_tac Cpmatch_FDOM >>
    fsrw_tac[DNF_ss][SUBSET_DEF,Cpat_vars_list_SUM_MAP]) >>
  strip_tac >- (
    rw[FUNION_FEMPTY_1] >>
    PROVE_TAC[Cresult_rel_syneq_refl,EVERY2_syneq_refl] ) >>
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  rw[LET_THM] >>
  rw[Once Cevaluate_cases] >>
  srw_tac[DNF_ss][] >>
  disj1_tac >>
  rw[Once Cevaluate_cases] >>
  srw_tac[DNF_ss][] >>
  map_every (fn q => CONV_TAC SWAP_EXISTS_CONV >> qexists_tac q) [`c`,`vs0++v::vs`] >>
  fs[el_check_def] >>
  fs[rich_listTheory.EL_LENGTH_APPEND] >>
  qspecl_then[`mod`,`s`,`menv' ++ menv ++ menv0 ++ env`,`e`,`r0`]mp_tac(CONJUNCT1 Cevaluate_syneq) >>
  simp[] >>
  disch_then(qspecl_then[`λv1 v2. if v1 < LENGTH menv' + LENGTH menv then (v2 = v1) else (v2 = v1+1)`
                        ,`mod`,`s`,`menv'++menv++[v]++menv0++env`
                        ,`shift 1 (Cpat_vars_list ps + Cpat_vars p) e`]mp_tac) >>
  qmatch_abbrev_tac`(P ⇒ Q) ⇒ R` >>
  `P` by (
    map_every qunabbrev_tac[`P`,`Q`,`R`] >>
    simp[] >>
    conj_tac >- (
      simp[shift_def] >>
      match_mp_tac mkshift_thm >>
      imp_res_tac Cpmatch_FDOM >>
      simp[Cpat_vars_list_SUM_MAP] >>
      fsrw_tac[DNF_ss][SUBSET_DEF] >>
      qx_gen_tac`z` >> strip_tac >>
      first_x_assum(qspec_then`z`mp_tac) >>
      simp[SUM_APPEND] ) >>
    lrw[ADD1,EL_APPEND1,EL_APPEND2,EL_CONS,PRE_SUB1] >>
    qabbrev_tac`l1 = menv' ++ menv` >>
    REWRITE_TAC[GSYM APPEND_ASSOC] >>
    `LENGTH l1 ≤ v1` by simp[Abbr`l1`] >>
    simp[EL_APPEND2]) >>
  simp[] >>
  map_every qunabbrev_tac[`P`,`Q`,`R`] >>
  pop_assum kall_tac >>
  disch_then(Q.X_CHOOSE_THEN`r1`strip_assume_tac) >>
  first_x_assum (qspecl_then [`mod`,`env`,`x+(Cpat_vars p+1)`,`c`,`vs0 ++ [v]`,`menv ++ [v] ++ menv0`,`fk+(Cpat_vars p+1)`
                             ,`shift 1 (Cpat_vars_list ps + Cpat_vars p) e`,`r1`] mp_tac) >>
  qmatch_abbrev_tac`(P ⇒ Q) ⇒ R` >>
  `P` by (
    map_every qunabbrev_tac[`P`,`Q`,`R`] >>
    imp_res_tac Cpmatch_FDOM >>
    simp[ADD1] >>
    conj_tac >- (
      qabbrev_tac`l1 = menv ++ [v]` >>
      `LENGTH l1 = Cpat_vars p + 1` by simp[Abbr`l1`] >>
      REWRITE_TAC[Once (GSYM APPEND_ASSOC)] >>
      qabbrev_tac`l2 = menv0 ++ env` >>
      REWRITE_TAC[Once (GSYM APPEND_ASSOC)] >>
      lrw[EL_APPEND2]) >>
    fsrw_tac[ARITH_ss,DNF_ss][SUBSET_DEF,Cpat_vars_list_SUM_MAP,SUM_APPEND] >>
    qx_gen_tac`z` >> strip_tac >>
    first_x_assum(qspec_then`z`mp_tac) >>
    simp[] ) >>
  simp[] >>
  map_every qunabbrev_tac[`P`,`Q`,`R`] >>
  pop_assum kall_tac >>
  disch_then(Q.X_CHOOSE_THEN`r2`strip_assume_tac) >>
  fsrw_tac[ARITH_ss][] >>
  Q.PAT_ABBREV_TAC`e' = remove_mat_con X Y Z A B` >>
  first_x_assum(qspecl_then[`mod`,`[v]++menv0++env`,`0`,`fk+1`,`e'`,`r2`]mp_tac) >>
  qmatch_abbrev_tac`(P ⇒ Q) ⇒ R` >>
  `P` by (
    map_every qunabbrev_tac[`P`,`Q`,`R`] >>
    simp[Abbr`e'`] >>
    qmatch_abbrev_tac`set (free_vars (remove_mat_con fk0 sk0 v0 n0 ps)) ⊆ s0` >>
    match_mp_tac SUBSET_TRANS >>
    qspecl_then[`ps`,`fk0`,`sk0`,`v0`,`n0`]strip_assume_tac(CONJUNCT2 free_vars_remove_mat_vp_SUBSET) >>
    HINT_EXISTS_TAC >> simp[] >>
    fsrw_tac[DNF_ss][SUBSET_DEF,Abbr`v0`,Abbr`fk0`,Abbr`s0`,Abbr`sk0`] >>
    simp[] >>
    imp_res_tac Cpmatch_FDOM >>
    srw_tac[ARITH_ss][Cpat_vars_list_SUM_MAP] >>
    fsrw_tac[ARITH_ss][] >>
    res_tac >> DECIDE_TAC ) >>
  fs[] >> pop_assum kall_tac >>
  map_every qunabbrev_tac[`Q`,`R`] >>
  metis_tac[Cresult_rel_syneq_trans,EVERY2_syneq_trans])

val Cpnomatch_strongind = theorem"Cpnomatch_strongind"

val Cpnomatch_remove_mat = store_thm("Cpnomatch_remove_mat",
  ``(∀p v. Cpnomatch (SND s) p v ⇒
       ∀env x fk e r0.
         (el_check x env = SOME v) ∧ fk < LENGTH env ∧
         set (free_vars e) ⊆ count (Cpat_vars p + LENGTH env) ∧
         no_labs e ∧
         Cevaluate mod s env (CCall F (CVar (Short fk)) []) r0
         ⇒ ∃r. Cevaluate mod s env (remove_mat_vp fk e x p) r ∧
               FST (FST r0) = FST (FST r) ∧
               EVERY2 (syneq) (SND (FST r0)) (SND (FST r)) ∧
               Cresult_rel syneq syneq (SND r0) (SND r)) ∧
    (∀ps vs. Cpnomatch_list (SND s) ps vs ⇒
       ∀env x c vs0 fk e r0.
         (el_check x env = SOME (CConv c (vs0 ++ vs))) ∧ fk < LENGTH env ∧
         set (free_vars e) ⊆ count (Cpat_vars_list ps + LENGTH env) ∧
         no_labs e ∧
         Cevaluate mod s env (CCall F (CVar (Short fk)) []) r0
         ⇒ ∃r. Cevaluate mod s env (remove_mat_con fk e x (LENGTH vs0) ps) r ∧
               FST (FST r0) = FST (FST r) ∧
               EVERY2 (syneq) (SND (FST r0)) (SND (FST r)) ∧
               Cresult_rel syneq syneq (SND r0) (SND r))``,
  ho_match_mp_tac Cpnomatch_ind >>
  strip_tac >- (
    rw[] >>
    rw[Once Cevaluate_cases] >>
    srw_tac[DNF_ss][] >>
    disj1_tac >>
    CONV_TAC (RESORT_EXISTS_CONV List.rev) >>qexists_tac `F` >> fs[] >>
    rw[Once Cevaluate_cases] >>
    rw[Once Cevaluate_cases] >>
    simp[Once Cevaluate_cases] >>
    fs[el_check_def] >>
    rw[] >>
    rw[Once Cevaluate_cases] >>
    PROVE_TAC[Cresult_rel_syneq_refl,EVERY2_syneq_refl]) >>
  strip_tac >- (
    rw[] >>
    rw[Once Cevaluate_cases] >>
    rw[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][] >>
    fs[el_check_def] >>
    PROVE_TAC[Cresult_rel_syneq_refl,EVERY2_syneq_refl]) >>
  strip_tac >- (
    rw[LET_THM] >>
    rw[Once Cevaluate_cases] >>
    srw_tac[DNF_ss][] >>
    disj1_tac >>
    rw[Once Cevaluate_cases,LET_THM] >>
    fs[el_check_def] >> rw[] >>
    qspecl_then[`mod`,`s`,`env`,`CCall F (CVar (Short fk)) []`,`r0`]mp_tac(CONJUNCT1 Cevaluate_syneq)>>
    simp[] >>
    disch_then(qspecl_then[`λv1 v2. v2 = v1 + 1`,`mod`,`s`,`EL n (SND s)::env`,`CCall F (CVar (Short (fk+1))) []`]mp_tac) >>
    qmatch_abbrev_tac`(P ⇒ Q) ⇒ R` >>
    `P` by (
      map_every qunabbrev_tac[`P`,`Q`,`R`] >>
      simp[] >>
      conj_tac >- (
        simp[Once syneq_exp_cases] >>
        simp[Once syneq_exp_cases]  ) >>
      simp[ADD1,EL_CONS,PRE_SUB1] ) >>
    simp[] >>
    map_every qunabbrev_tac[`P`,`Q`,`R`] >>
    pop_assum kall_tac >>
    disch_then(Q.X_CHOOSE_THEN`r1`strip_assume_tac) >>
    first_x_assum(qspecl_then[`EL n (SND s)::env`,`0`,`fk+1`,`shift 1 (Cpat_vars p) e`,`r1`]mp_tac) >>
    simp[] >>
    fsrw_tac[DNF_ss,ARITH_ss][SUBSET_DEF,ADD1] >>
    qmatch_abbrev_tac`(P ⇒ Q) ⇒ R` >>
    `P` by (
      simp[Abbr`P`] >>
      srw_tac[ARITH_ss][] >>
      res_tac >> simp[] ) >>
    simp[] >>
    map_every qunabbrev_tac[`P`,`Q`,`R`] >>
    pop_assum kall_tac >>
    Cases_on`s`>>asm_simp_tac(srw_ss()++DNF_ss)[FORALL_PROD] >> fs[] >>
    metis_tac[Cresult_rel_syneq_trans,EVERY2_syneq_trans,FST,SND] ) >>
  strip_tac >- (
    rw[el_check_def] >>
    rw[Once Cevaluate_cases] >>
    rw[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][] >>
    disj1_tac >>
    first_x_assum (qspecl_then [`env`,`x`,`c`,`[]`,`fk`,`e`,`r0`] mp_tac) >>
    simp[]) >>
  strip_tac >- (
    rw[el_check_def,LET_THM] >>
    rw[Once Cevaluate_cases] >>
    rw[Once Cevaluate_cases] >>
    rw[Cevaluate_proj] >>
    imp_res_tac Cpmatch_FDOM >>
    fsrw_tac[DNF_ss,ARITH_ss][] >>
    REWRITE_TAC[GSYM APPEND_ASSOC] >>
    lrw[EL_APPEND2] >>
    Q.PAT_ABBREV_TAC`e' = remove_mat_con X Y Z A B` >>
    qspecl_then[`mod`,`s`,`env`,`CCall F (CVar (Short fk)) []`,`r0`]mp_tac(CONJUNCT1 Cevaluate_syneq)>>
    simp[] >>
    disch_then(qspecl_then[`λv1 v2. v2 = v1 + 1`,`mod`,`s`,`[v]++env`,`CCall F (CVar (Short (fk+1))) []`]mp_tac) >>
    qmatch_abbrev_tac`(P ⇒ Q) ⇒ R` >>
    `P` by (
      map_every qunabbrev_tac[`P`,`Q`,`R`] >>
      simp[] >>
      conj_tac >- (
        simp[Once syneq_exp_cases] >>
        simp[Once syneq_exp_cases]  ) >>
      simp[ADD1,EL_CONS,PRE_SUB1] ) >>
    simp[] >>
    map_every qunabbrev_tac[`P`,`Q`,`R`] >>
    pop_assum kall_tac >>
    disch_then(Q.X_CHOOSE_THEN`r1`strip_assume_tac) >>
    first_x_assum(qspecl_then[`[v]++env`,`0`,`fk+1`,`e'`,`r1`]mp_tac) >>
    simp[] >>
    simp[Abbr`e'`] >>
    qmatch_abbrev_tac`(P ⇒ Q) ⇒ R` >>
    `P` by (
      simp[Abbr`P`] >>
      qmatch_abbrev_tac`set (free_vars (remove_mat_con fk0 e0 x0 n0 ps0)) ⊆ ss` >>
      qspecl_then[`ps0`,`fk0`,`e0`,`x0`,`n0`]strip_assume_tac(CONJUNCT2 free_vars_remove_mat_vp_SUBSET) >>
      match_mp_tac SUBSET_TRANS >>
      HINT_EXISTS_TAC >> simp[] >>
      unabbrev_all_tac >>
      fsrw_tac[DNF_ss,ARITH_ss][SUBSET_DEF] >>
      srw_tac[ARITH_ss][] >>
      res_tac >> simp[] ) >>
    PROVE_TAC[Cresult_rel_syneq_trans,EVERY2_syneq_trans]) >>
  rw[el_check_def,LET_THM] >>
  rw[Once Cevaluate_cases] >>
  rw[Once Cevaluate_cases] >>
  rw[Cevaluate_proj] >>
  fsrw_tac[DNF_ss,ARITH_ss][] >>
  REWRITE_TAC[GSYM APPEND_ASSOC] >>
  lrw[EL_APPEND2] >>
  qspecl_then[`mod`,`s`,`env'`,`CCall F (CVar (Short fk)) []`,`r0`]mp_tac(CONJUNCT1 Cevaluate_syneq)>>
  simp[] >>
  disch_then(qspecl_then[`λv1 v2. v2 = v1+(Cpat_vars p+1)`,`mod`,`s`,`env++[v]++env'`,`CCall F (CVar (Short (fk+(Cpat_vars p+1)))) []`]mp_tac) >>
  qmatch_abbrev_tac`(P ⇒ Q) ⇒ R` >>
  `P` by (
    map_every qunabbrev_tac[`P`,`Q`,`R`] >>
    simp[] >>
    imp_res_tac Cpmatch_FDOM >>
    conj_tac >- (
      simp[Once syneq_exp_cases] >>
      simp[Once syneq_exp_cases] >>
      srw_tac[ARITH_ss][]) >>
    srw_tac[ARITH_ss][ADD1,PRE_SUB1,EL_APPEND2] >>
    REWRITE_TAC[GSYM (APPEND_ASSOC)] >>
    lrw[EL_APPEND2] ) >>
  simp[] >>
  map_every qunabbrev_tac[`P`,`Q`,`R`] >>
  pop_assum kall_tac >>
  disch_then(Q.X_CHOOSE_THEN`r1`strip_assume_tac) >>
  Q.PAT_ABBREV_TAC`e' = remove_mat_con X Y Z A B` >>
  first_x_assum(qspecl_then[`env++[v]++env'`,`x+(Cpat_vars p+1)`,`c`,`vs0++[v]`,`fk+(Cpat_vars p+1)`
                           ,`shift 1 (Cpat_vars p + Cpat_vars_list ps) e`,`r1`]mp_tac) >>
  qmatch_abbrev_tac`(P ⇒ Q) ⇒ R` >>
  `P` by (
    map_every qunabbrev_tac[`P`,`Q`,`R`] >>
    imp_res_tac Cpmatch_FDOM >>
    simp[] >>
    lrw[EL_APPEND2] >>
    fsrw_tac[ARITH_ss,DNF_ss][SUBSET_DEF] >>
    srw_tac[ARITH_ss][] >>
    res_tac >> simp[] ) >>
  simp[] >>
  map_every qunabbrev_tac[`P`,`Q`,`R`] >>
  pop_assum kall_tac >>
  disch_then(Q.X_CHOOSE_THEN`r2`strip_assume_tac) >>
  qspecl_then[`p`,`v`,`env`]mp_tac(CONJUNCT1 Cpmatch_remove_mat) >>
  simp[] >>
  disch_then(qspecl_then[`mod`,`[v]++env'`,`0`,`fk+1`,`e'`,`r2`]mp_tac) >>
  simp[el_check_def] >>
  qmatch_abbrev_tac`(P ⇒ Q) ⇒ R` >>
  `P` by (
    map_every qunabbrev_tac[`P`,`Q`,`R`] >>
    imp_res_tac Cpmatch_FDOM >>
    simp[Abbr`e'`] >>
    fsrw_tac[ARITH_ss][] >>
    qmatch_abbrev_tac`set (free_vars (remove_mat_con fk0 e0 x0 n0 ps0)) ⊆ ss` >>
    qspecl_then[`ps0`,`fk0`,`e0`,`x0`,`n0`]strip_assume_tac(CONJUNCT2 free_vars_remove_mat_vp_SUBSET) >>
    match_mp_tac SUBSET_TRANS >>
    HINT_EXISTS_TAC >> simp[] >>
    unabbrev_all_tac >>
    fsrw_tac[DNF_ss,ARITH_ss][SUBSET_DEF] >>
    srw_tac[ARITH_ss][] >>
    res_tac >> simp[] ) >>
  simp[] >>
  map_every qunabbrev_tac[`P`,`Q`,`R`] >>
  pop_assum kall_tac >>
  metis_tac[Cresult_rel_syneq_trans,EVERY2_syneq_trans] )

val Cevaluate_match_strongind = theorem"Cevaluate_match_strongind"

val Cevaluate_match_least_el = store_thm("Cevaluate_match_least_el",
  ``∀pes env r. Cevaluate_match s v pes env r ⇒ ∀e. (r = SOME e) ⇒
      ∃i p. i < LENGTH pes ∧ (EL i pes = (p,e)) ∧ Cpmatch s p v env ∧
      ∀j. j < i ⇒ Cpnomatch s (FST (EL j pes)) v``,
  ho_match_mp_tac Cevaluate_match_ind >>
  rw[] >- ( qexists_tac `0` >> rw[] ) >>
  qexists_tac `SUC i` >> rw[] >>
  Cases_on `j` >> rw[] >>
  fs[])

val Cevaluate_match_NONE_NIL = store_thm("Cevaluate_match_NONE_NIL",
  ``Cevaluate_match s v pes env NONE ⇒ (env = [])``,
  qsuff_tac `∀pes env r. Cevaluate_match s v pes env r ⇒ (r = NONE) ⇒ (env = [])` >- PROVE_TAC[] >>
  ho_match_mp_tac Cevaluate_match_ind >> rw[])

val Cevaluate_match_remove_mat_var = store_thm("Cevaluate_match_remove_mat_var",
  ``∀pes menv mr. Cevaluate_match (SND s) v pes menv mr ⇒
      ∀env b x. (el_check x env = SOME v) ∧
              EVERY (λ(p,e). set (free_vars e) ⊆ count (Cpat_vars p + LENGTH env) ∧ no_labs e) pes
      ⇒
       case mr of
       | NONE =>
           ∃r. Cevaluate mod s env (remove_mat_var b x pes) r ∧
               FST s = FST (FST r) ∧
               EVERY2 (syneq) (SND s) (SND (FST r)) ∧
               ∃e. (SND r = Cexc (Craise e)) ∧
                   (syneq (if b then v else CBind_excv) e)
       | SOME e => ∀r0. Cevaluate mod s (menv ++ env) e r0 ⇒
           ∃r. Cevaluate mod s env (remove_mat_var b x pes) r ∧
               FST (FST r0) = FST (FST r) ∧
               EVERY2 (syneq) (SND (FST r0)) (SND (FST r)) ∧
               Cresult_rel syneq syneq (SND r0) (SND r)``,
  ho_match_mp_tac Cevaluate_match_strongind >>
  strip_tac >- (
    rw[remove_mat_var_def] >>
    rw[Once Cevaluate_cases] >>
    fs[el_check_def] >>
    rw[Once Cevaluate_cases] >>
    rw[Once Cevaluate_cases] >>
    rw[Once Cevaluate_cases] >>
    rw[Once Cevaluate_cases] ) >>
  strip_tac >- (
    rw[remove_mat_var_def,LET_THM] >>
    rw[Once Cevaluate_cases] >>
    Q.PAT_ABBREV_TAC`f = CRecClos env A B` >>
    Q.PAT_ABBREV_TAC`e' = shift 1 X e` >>
    qspecl_then[`mod`,`s`,`menv++env`,`e`,`r0`]mp_tac(CONJUNCT1 Cevaluate_syneq) >>
    simp[] >>
    disch_then(qspecl_then[`λv1 v2. if v1 < LENGTH menv then v2 = v1 else v2 = v1 + 1`,`mod`,`s`,`menv++[f]++env`,`e'`]mp_tac) >>
    qmatch_abbrev_tac`(P ⇒ Q) ⇒ R` >>
    `P` by (
      map_every qunabbrev_tac[`P`,`Q`,`R`] >>
      simp[] >>
      imp_res_tac Cpmatch_FDOM >>
      conj_tac >- (
        simp[Abbr`e'`,shift_def] >>
        match_mp_tac mkshift_thm >>
        simp[] ) >>
      lrw[EL_APPEND2,EL_APPEND1] ) >>
    simp[] >>
    map_every qunabbrev_tac[`P`,`Q`,`R`] >>
    pop_assum kall_tac >>
    disch_then(Q.X_CHOOSE_THEN`r1`strip_assume_tac) >>
    qspecl_then [`p`,`v`,`menv`] mp_tac (CONJUNCT1 Cpmatch_remove_mat) >>
    simp[] >>
    disch_then(qspecl_then[`mod`,`[f]++env`,`x+1`,`0`,`e'`,`r1`]mp_tac) >>
    simp[] >> fs[el_check_def] >>
    simp[EL_CONS,PRE_SUB1] >>
    qmatch_abbrev_tac`(P ⇒ Q) ⇒ R` >>
    `P` by (
      map_every qunabbrev_tac[`P`,`Q`,`R`] >>
      imp_res_tac Cpmatch_FDOM >>
      simp[Abbr`e'`,ADD1] >>
      fsrw_tac[DNF_ss][SUBSET_DEF] >>
      srw_tac[ARITH_ss][] >>
      res_tac >> simp[] ) >>
    metis_tac[Cresult_rel_syneq_trans,EVERY2_syneq_trans ] ) >>
  rw[] >>
  Q.PAT_ABBREV_TAC`errv = if b then v else X` >>
  rw[remove_mat_var_def,LET_THM] >>
  qspecl_then [`p`,`v`] mp_tac (CONJUNCT1 Cpnomatch_remove_mat) >>
  rw[] >>
  Q.PAT_ABBREV_TAC`ex = CLetrec X Y` >>
  qsuff_tac `∀r0. (case mr of NONE => ∃err0. (r0 = (s,Cexc (Craise err0))) ∧ syneq err0 errv
                   | SOME e => Cevaluate mod s (menv ++ env) e r0)
                   ⇒ ∃r. Cevaluate mod s env ex r ∧
                         FST (FST r0) = FST (FST r) ∧
                         EVERY2 syneq (SND (FST r0)) (SND (FST r)) ∧
                         Cresult_rel syneq syneq (SND r0) (SND r)` >- (
    Cases_on `mr` >> fs[EXISTS_PROD,FORALL_PROD] >>
    Cases_on`s`>>srw_tac[DNF_ss][]) >>
  qx_gen_tac `r0` >>
  strip_tac >>
  qunabbrev_tac`ex` >>
  rw[Once Cevaluate_cases] >>
  Q.PAT_ABBREV_TAC`env1 = f::env` >>
  Q.PAT_ABBREV_TAC`e' = shift 1 X e` >>
  first_x_assum (qspecl_then [`env1`,`x+1`,`0`,`e'`] mp_tac) >>
  fs[el_check_def] >>
  simp[Abbr`env1`,EL_CONS,PRE_SUB1] >>
  simp[Once Cevaluate_cases] >>
  simp[Once Cevaluate_cases] >>
  simp[Once(CONJUNCT2 Cevaluate_cases)] >>
  qho_match_abbrev_tac`(∀r. P r ⇒ Q r) ⇒ R` >>
  qsuff_tac`∃r. P r ∧ FST (FST r0) = FST (FST r) ∧ EVERY2 syneq (SND (FST r0)) (SND (FST r))
                    ∧ Cresult_rel syneq syneq (SND r0) (SND r)` >- (
    rw[Abbr`R`,Abbr`Q`] >>
    metis_tac[EVERY2_syneq_trans,Cresult_rel_syneq_trans] ) >>
  simp[Abbr`P`,Abbr`Q`,Abbr`R`] >>
  simp[Abbr`e'`] >>
  simp[GSYM CONJ_ASSOC] >>
  simp[RIGHT_EXISTS_AND_THM] >>
  conj_tac >- (
    fsrw_tac[DNF_ss][SUBSET_DEF] >>
    srw_tac[ARITH_ss][ADD1] >>
    res_tac >> simp[] ) >>
  qsuff_tac`
      ∃r. Cevaluate mod s env (remove_mat_var b x pes) r ∧
          FST (FST r0) = FST (FST r) ∧
          EVERY2 (syneq) (SND (FST r0)) (SND (FST r)) ∧
          Cresult_rel syneq syneq (SND r0) (SND r)` >- (
    disch_then(Q.X_CHOOSE_THEN`r1`strip_assume_tac) >>
    qspecl_then[`mod`,`s`,`env`,`remove_mat_var b x pes`,`r1`]mp_tac(CONJUNCT1 Cevaluate_syneq) >>
    simp[] >>
    Q.PAT_ABBREV_TAC`f = CRecClos env A B` >>
    disch_then(qspecl_then[`λv1 v2. v2 = v1 + 1`,`mod`,`s`,`f::env`,`shift 1 0 (remove_mat_var b x pes)`]mp_tac) >>
    qmatch_abbrev_tac`(P ⇒ Q) ⇒ R` >>
    qsuff_tac`P` >- (
      unabbrev_all_tac >>
      Cases_on`s`>>fs[] >>
      metis_tac[Cresult_rel_syneq_trans,EVERY2_syneq_trans] ) >>
    map_every qunabbrev_tac[`P`,`Q`,`R`] >>
    simp[shift_def,ADD1,EL_CONS,PRE_SUB1] >>
    match_mp_tac mkshift_thm >>
    simp[] >> conj_tac >- (
      qspecl_then[`b`,`x`,`pes`]strip_assume_tac free_vars_remove_mat_var_SUBSET >>
      match_mp_tac SUBSET_TRANS >> HINT_EXISTS_TAC >>
      fsrw_tac[DNF_ss][SUBSET_DEF] >>
      qx_gen_tac`y` >>
      simp[FORALL_PROD] >>
      Cases_on`y=x`>>rw[] >>
      fsrw_tac[DNF_ss][EVERY_MEM,FORALL_PROD] >>
      srw_tac[ARITH_ss][] >>
      metis_tac[] ) >>
    fsrw_tac[DNF_ss][EVERY_MEM,FORALL_PROD] >>
    simp[free_labs_list_MAP,FLAT_EQ_NIL,EVERY_MAP,EVERY_MEM,FORALL_PROD,MEM_MAP,EXISTS_PROD] >>
    metis_tac[]) >>
  first_x_assum(qspecl_then[`env`,`b`,`x`]mp_tac) >>
  simp[] >>
  Cases_on`mr`>>fs[] >>
  srw_tac[DNF_ss][] >>
  metis_tac[syneq_trans,EVERY2_syneq_trans])

val Cpmatch_syneq = store_thm("Cpmatch_syneq",
  ``(∀p v env. Cpmatch s p v env ⇒
      ∀s' w. syneq v w ∧ EVERY2 (syneq) s s' ⇒
      ∃env'. Cpmatch s' p w env' ∧ EVERY2 (syneq) env env') ∧
    (∀ps vs env. Cpmatch_list s ps vs env ⇒
      ∀s' ws. EVERY2 (syneq) vs ws ∧ EVERY2 (syneq) s s' ⇒
      ∃env'. Cpmatch_list s' ps ws env' ∧ EVERY2 (syneq) env env')``,
  ho_match_mp_tac Cpmatch_ind >>
  strip_tac >- rw[Once Cpmatch_cases,fmap_rel_def] >>
  strip_tac >- rw[Once Cpmatch_cases,Once syneq_cases] >>
  strip_tac >- (
    rw[] >>
    rw[Once Cpmatch_cases] >>
    fsrw_tac[DNF_ss][] >> rw[] >>
    `∃w. (el_check n s' = SOME w) ∧ syneq v w` by (
      fs[EVERY2_EVERY,el_check_def,EVERY_MEM,FORALL_PROD] >>
      rfs[MEM_ZIP] >> metis_tac[]) >>
    fs[]) >>
  strip_tac >- (
    rw[Once syneq_cases] >>
    res_tac >>
    rw[Once Cpmatch_cases] ) >>
  strip_tac >- rw[Once Cpmatch_cases] >>
  rw[] >>
  rw[Once Cpmatch_cases] >>
  res_tac >>
  srw_tac[DNF_ss][] >>
  metis_tac[EVERY2_APPEND])

val Cpnomatch_syneq = store_thm("Cpnomatch_syneq",
  ``(∀p v. Cpnomatch s p v ⇒
      ∀s' w. syneq v w ∧ EVERY2 (syneq) s s' ⇒
        Cpnomatch s' p w) ∧
    (∀ps vs. Cpnomatch_list s ps vs ⇒
      ∀s' ws. EVERY2 (syneq) vs ws ∧ EVERY2 (syneq) s s' ⇒
        Cpnomatch_list s' ps ws)``,
  ho_match_mp_tac Cpnomatch_ind >> rw[] >>
  TRY (
    rw[Once Cpnomatch_cases] >>
    fs[Once syneq_cases] >>
    res_tac >> NO_TAC) >>
  TRY (
    rw[Once Cpnomatch_cases] >>
    `∃w. (el_check n s' = SOME w) ∧ syneq v w` by (
      fs[el_check_def,EVERY2_EVERY,EVERY_MEM] >>
      rfs[MEM_ZIP,FORALL_PROD] >>
      metis_tac[]) >>
    fs[] >> first_x_assum match_mp_tac >>
    metis_tac[]) >>
  rw[Once Cpnomatch_cases] >>
  fs[EVERY2_EVERY] >>
  metis_tac[Cpmatch_syneq,EVERY2_EVERY])

val Cevaluate_match_syneq = store_thm("Cevaluate_match_syneq",
  ``∀pes env r. Cevaluate_match s v pes env r ⇒
      ∀s' w. syneq v w ∧ EVERY2 (syneq) s s' ⇒
        ∃env'. Cevaluate_match s' w pes env' r ∧ EVERY2 (syneq) env env'``,
  ho_match_mp_tac Cevaluate_match_ind >>
  strip_tac >- rw[Once Cevaluate_match_cases] >>
  strip_tac >- (
    rw[Once Cevaluate_match_cases] >>
    imp_res_tac Cpmatch_syneq >>
    rw[Once Cevaluate_match_cases] >>
    metis_tac[] ) >>
  rw[] >>
  rw[Once Cevaluate_match_cases] >>
  metis_tac[Cpnomatch_syneq])

val Cevaluate_match_closed = store_thm("Cevaluate_match_closed",
  ``∀pes env r. Cevaluate_match s v pes env r ⇒
      EVERY (Cclosed) s ∧ Cclosed v ⇒
      EVERY (Cclosed) env``,
  ho_match_mp_tac Cevaluate_match_ind >>
  rw[Cpmatch_closed] >>
  imp_res_tac Cpmatch_closed)

val _ = export_theory()
