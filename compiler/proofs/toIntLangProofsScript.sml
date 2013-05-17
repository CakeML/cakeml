open HolKernel bossLib boolLib miscLib boolSimps intLib pairTheory sumTheory listTheory pred_setTheory finite_mapTheory arithmeticTheory alistTheory rich_listTheory lcsymtacs
open LibTheory SemanticPrimitivesTheory AstTheory terminationTheory semanticsExtraTheory evaluateEquationsTheory miscTheory CompilerLibTheory IntLangTheory ToIntLangTheory compilerTerminationTheory intLangExtraTheory pmatchTheory
val _ = new_theory "toIntLangProofs"
val fsd = full_simp_tac std_ss

(* TODO: move? *)
val find_index_ALL_DISTINCT_REVERSE = store_thm("find_index_ALL_DISTINCT_REVERSE",
  ``∀ls x m j. ALL_DISTINCT ls ∧ (find_index x ls m = SOME j) ⇒ (find_index x (REVERSE ls) m = SOME (m + LENGTH ls + m - j - 1))``,
  rw[] >> imp_res_tac find_index_ALL_DISTINCT_EL_eq >>
  `ALL_DISTINCT (REVERSE ls)` by rw[ALL_DISTINCT_REVERSE] >>
  simp[find_index_ALL_DISTINCT_EL_eq] >>
  rw[] >> fsrw_tac[ARITH_ss][] >> rw[] >>
  qmatch_assum_rename_tac`z < LENGTH ls`[] >>
  qexists_tac`LENGTH ls - z - 1` >>
  lrw[EL_REVERSE,PRE_SUB1])

(* Nicer induction *)

val exp_to_Cexp_nice_ind = save_thm(
"exp_to_Cexp_nice_ind",
exp_to_Cexp_ind
|> Q.SPECL [`P`
   ,`λs defs. EVERY (λ(d,vn,e). P (s with bvars := vn::s.bvars) e) defs`
   ,`λs pes. EVERY (λ(p,e). P (FST (pat_to_Cpat s p)) e) pes`
   ,`λs. EVERY (P s)`]
|> SIMP_RULE (srw_ss()) []
|> UNDISCH_ALL
|> CONJUNCTS
|> el 1
|> DISCH_ALL
|> Q.GEN `P`
|> SIMP_RULE (srw_ss()) [optionTheory.option_case_compute,cond_sum_expand])

(* Misc. lemmas *)

val do_Opapp_SOME_CRecClos = store_thm(
"do_Opapp_SOME_CRecClos",
``(do_app s env Opapp v1 v2 = SOME (s',env',exp'')) ∧
  syneq (v_to_Cv m v1) w1 ⇒
  ∃env'' defs n.
    (w1 = CRecClos env'' defs n)``,
Cases_on `v1` >> rw[do_app_def,v_to_Cv_def,LET_THM] >>
fs[defs_to_Cdefs_MAP, Once syneq_cases])

val env_to_Cenv_APPEND = store_thm("env_to_Cenv_APPEND",
  ``env_to_Cenv m (l1 ++ l2) = env_to_Cenv m l1 ++ env_to_Cenv m l2``,
  rw[env_to_Cenv_MAP])
val _ = export_rewrites["env_to_Cenv_APPEND"]

val all_Clocs_v_to_Cv = store_thm("all_Clocs_v_to_Cv",
  ``(∀m v. all_Clocs (v_to_Cv m v) = all_locs v) ∧
    (∀m vs. MAP all_Clocs (vs_to_Cvs m vs) = MAP all_locs vs) ∧
    (∀m env. MAP all_Clocs (env_to_Cenv m env) = MAP (all_locs o SND) env)``,
  ho_match_mp_tac v_to_Cv_ind >>
  srw_tac[ETA_ss][v_to_Cv_def,LET_THM,defs_to_Cdefs_MAP] >>
  fs[GSYM LIST_TO_SET_MAP,MAP_MAP_o])

val no_labs_exp_to_Cexp = store_thm("no_labs_exp_to_Cexp",
  ``∀s e. no_labs (exp_to_Cexp s e)``,
  ho_match_mp_tac exp_to_Cexp_nice_ind >>
  rw[exp_to_Cexp_def,exps_to_Cexps_MAP,defs_to_Cdefs_MAP,pes_to_Cpes_MAP] >>
  rw[EVERY_MAP,EVERY_REVERSE] >>
  TRY (unabbrev_all_tac >>
       fsrw_tac[DNF_ss][EVERY_MEM,MEM_MAP,FORALL_PROD] >>
       simp[UNCURRY] >> NO_TAC) >>
  TRY (BasicProvers.CASE_TAC >> rw[] >> NO_TAC)
  >- (
    simp[EVERY_MEM,EXISTS_MEM,MEM_MAP,EXISTS_PROD] >>
    unabbrev_all_tac >>
    fsrw_tac[DNF_ss][EVERY_MEM,FORALL_PROD] >>
    metis_tac[] )
  >- ( Cases_on`pat_to_Cpat m p`>>fs[] ))
val _ = export_rewrites["no_labs_exp_to_Cexp"]

val no_vlabs_v_to_Cv = store_thm("no_vlabs_v_to_Cv",
  ``(∀m v. no_vlabs (v_to_Cv m v)) ∧
    (∀m vs. no_vlabs_list (vs_to_Cvs m vs)) ∧
    (∀m env. no_vlabs_list (env_to_Cenv m env))``,
  ho_match_mp_tac v_to_Cv_ind >>
  rw[v_to_Cv_def] >>
  TRY(qunabbrev_tac`Ce`)>>
  TRY(qunabbrev_tac`Cdefs`)>>
  simp[FLAT_EQ_NIL,EVERY_MAP,defs_to_Cdefs_MAP] >>
  simp[EVERY_MEM,UNCURRY])
val _ = export_rewrites["no_vlabs_v_to_Cv"]

val cmap_linv_def = Define`
  cmap_linv m w ⇔ ∀x. x ∈ FDOM m ⇒ (ALOOKUP w (FAPPLY m x) = SOME (id_to_string x))`

val cmap_linv_FAPPLY = store_thm("cmap_linv_FAPPLY",
  ``cmap_linv f g ∧ x ∈ FDOM f ⇒ (the d (ALOOKUP g (FAPPLY f x)) = (id_to_string x))``,
  rw[cmap_linv_def,IN_FRANGE])

val v_to_Cv_ov = store_thm("v_to_Cv_ov",
  ``(∀m v w s. (all_cns v ⊆ FDOM m) ∧ cmap_linv m w ==> (Cv_to_ov w s (v_to_Cv m v) = v_to_ov s v)) ∧
    (∀m vs w s. (BIGUNION (IMAGE all_cns (set vs)) ⊆ FDOM m) ∧ cmap_linv m w ==> (MAP (Cv_to_ov w s) (vs_to_Cvs m vs) = MAP (v_to_ov s) vs)) ∧
    (∀(m:(conN id)|->num) (env:envE). T)``,
  ho_match_mp_tac v_to_Cv_ind >>
  rw[v_to_Cv_def] >> rw[Cv_to_ov_def] >>
  srw_tac[ETA_ss][cmap_linv_FAPPLY])

(* free vars lemmas *)

val Cpat_vars_pat_to_Cpat = store_thm(
"Cpat_vars_pat_to_Cpat",
``(∀p s s' Cp. (pat_to_Cpat s p = (s',Cp))
  ⇒ (Cpat_vars Cp = (LENGTH (pat_bindings p [])))) ∧
  (∀ps s s' Cps. (pats_to_Cpats s ps = (s',Cps))
  ⇒ (MAP Cpat_vars Cps = MAP (λp. (LENGTH (pat_bindings p []))) ps))``,
ho_match_mp_tac (TypeBase.induction_of ``:pat``) >>
rw[pat_to_Cpat_def,LET_THM,pairTheory.UNCURRY,pat_bindings_def] >>
rw[FOLDL_UNION_BIGUNION,IMAGE_BIGUNION] >- (
  qabbrev_tac `q = pats_to_Cpats s ps` >>
  PairCases_on `q` >>
  fsrw_tac[ETA_ss][MAP_EQ_EVERY2,EVERY2_EVERY,EVERY_MEM,pairTheory.FORALL_PROD] >>
  first_x_assum (qspecl_then [`s`] mp_tac) >>
  rw[] >>
  rw[Cpat_vars_list_SUM_MAP] >>
  rw[pats_bindings_MAP,LENGTH_FLAT,MAP_REVERSE,SUM_REVERSE,MAP_MAP_o] >>
  AP_TERM_TAC >>
  rw[MAP_EQ_EVERY2,EVERY2_EVERY,EVERY_MEM,FORALL_PROD] )
>- (
  qabbrev_tac `q = pat_to_Cpat s p` >>
  PairCases_on `q` >>
  fs[] >>
  PROVE_TAC[] )
>- (
  POP_ASSUM_LIST (MAP_EVERY ASSUME_TAC) >>
  first_x_assum(qspec_then`s`mp_tac) >>
  qabbrev_tac `r = pat_to_Cpat s p` >>
  PairCases_on `r` >>
  first_x_assum(qspec_then`r0`mp_tac) >>
  qabbrev_tac `q = pats_to_Cpats r0 ps` >>
  PairCases_on `q` >> fs[] )
>- (
  POP_ASSUM_LIST (MAP_EVERY ASSUME_TAC) >>
  first_x_assum(qspec_then`s`mp_tac) >>
  qabbrev_tac `r = pat_to_Cpat s p` >>
  PairCases_on `r` >>
  qabbrev_tac `q = pats_to_Cpats r0 ps` >>
  PairCases_on `q` >> rw[] >>
  metis_tac[]))

val Cpat_vars_SND_pat_to_Cpat = store_thm("Cpat_vars_SND_pat_to_Cpat",
  ``Cpat_vars (SND (pat_to_Cpat s z)) = LENGTH (pat_bindings z [])``,
  Cases_on `pat_to_Cpat s z` >>
  imp_res_tac Cpat_vars_pat_to_Cpat >>
  rw[])
val _ = export_rewrites["Cpat_vars_SND_pat_to_Cpat"]

val set_FST_pat_to_Cpat_bvars = store_thm("set_FST_pat_to_Cpat_bvars",
  ``(∀p s. set (FST (pat_to_Cpat s p)).bvars = pat_vars p ∪ set s.bvars) ∧
    (∀ps s. set (FST (pats_to_Cpats s ps)).bvars = BIGUNION (IMAGE pat_vars (set ps)) ∪ set s.bvars)``,
  ho_match_mp_tac (TypeBase.induction_of``:pat``) >>
  rw[pat_to_Cpat_def,pat_bindings_def,pats_bindings_MAP] >> rw[]
  >- simp[Once EXTENSION]
  >- ( first_x_assum(qspec_then`s`mp_tac) >> rw[EXTENSION,MEM_FLAT,MEM_MAP] >> metis_tac[] )
  >- ( first_x_assum(qspec_then`s`mp_tac) >> rw[EXTENSION,MEM_FLAT,MEM_MAP] >> metis_tac[] ) >>
  first_x_assum(qspec_then`m`mp_tac) >>
  first_x_assum(qspec_then`s`mp_tac) >>
  rw[] >>
  metis_tac[UNION_ASSOC,UNION_COMM])

val FST_pat_to_Cpat_bvars = store_thm("FST_pat_to_Cpat_bvars",
  ``(∀p s. (FST (pat_to_Cpat s p)).bvars = pat_bindings p [] ++ s.bvars) ∧
    (∀ps s. (FST (pats_to_Cpats s ps)).bvars = pats_bindings ps [] ++ s.bvars)``,
  ho_match_mp_tac (TypeBase.induction_of``:pat``) >>
  rw[pat_to_Cpat_def,pat_bindings_def] >> rw[]
  >- ( first_x_assum(qspec_then`s`mp_tac) >> simp[] )
  >- ( first_x_assum(qspec_then`s`mp_tac) >> simp[] ) >>
  first_x_assum(qspec_then`m`mp_tac) >>
  first_x_assum(qspec_then`s`mp_tac) >>
  rw[] >>
  simp[Once pat_bindings_acc,SimpRHS])

val LENGTH_FST_pat_to_Cpat_bvars = store_thm("LENGTH_FST_pat_to_Cpat_bvars",
  ``(∀p s l. LENGTH (FST (pat_to_Cpat s p)).bvars = LENGTH (pat_bindings p l) - LENGTH l + LENGTH s.bvars) ∧
    (∀ps s l. LENGTH (FST (pats_to_Cpats s ps)).bvars = LENGTH (pats_bindings ps l) - LENGTH l + LENGTH s.bvars)``,
  ho_match_mp_tac (TypeBase.induction_of``:pat``) >>
  srw_tac[ARITH_ss,ETA_ss][pat_to_Cpat_def,ADD1,pat_bindings_def]
  >- ( first_x_assum(qspec_then`s`mp_tac) >> simp[] )
  >- ( first_x_assum(qspec_then`s`mp_tac) >> simp[] ) >>
  first_x_assum(qspec_then`m`mp_tac) >>
  first_x_assum(qspec_then`s`mp_tac) >>
  rw[] >>
  simp[Once pat_bindings_acc] >>
  first_x_assum(qspec_then`[]`mp_tac) >>
  first_x_assum(qspec_then`l`mp_tac) >>
  disch_then SUBST1_TAC >>
  disch_then SUBST1_TAC >>
  simp[] >>
  simp[Once (CONJUNCT1 pat_bindings_acc)] >>
  simp[Once (CONJUNCT1 pat_bindings_acc),SimpRHS])

val lem = PROVE[]``(a ==> (b \/ c)) = (a /\ ~b ==> c)``

val free_vars_exp_to_Cexp = store_thm(
"free_vars_exp_to_Cexp",
``∀s e. SFV e ⊆ set s.bvars ⇒
        set (free_vars (exp_to_Cexp s e)) ⊆ count (LENGTH s.bvars)``,
ho_match_mp_tac exp_to_Cexp_nice_ind >>
strip_tac >- (
  rw[exp_to_Cexp_def] >>
  fsrw_tac[DNF_ss,ARITH_ss][SUBSET_DEF,PRE_SUB1,ADD1] >>
  conj_tac >> Cases >> fsrw_tac[ARITH_ss,DNF_ss][ADD1,lem] >>
  strip_tac >> res_tac >> fsrw_tac[ARITH_ss][] ) >>
strip_tac >- rw[exp_to_Cexp_def] >>
strip_tac >- rw[exp_to_Cexp_def] >>
strip_tac >- (
  rw[exp_to_Cexp_def,free_vars_list_MAP,FV_list_MAP] >>
  fsrw_tac[DNF_ss][SUBSET_DEF,EVERY_MEM,exps_to_Cexps_MAP,MEM_MAP,MEM_FLAT] >>
  metis_tac[] ) >>
strip_tac >- (
  rw[exp_to_Cexp_def] >>
  imp_res_tac find_index_MEM >>
  pop_assum(qspec_then`0`mp_tac)>>rw[] >>
  rw[] ) >>
strip_tac >- rw[exp_to_Cexp_def] >>
strip_tac >- (
  rw[exp_to_Cexp_def] >>
  fsrw_tac[DNF_ss,ARITH_ss][SUBSET_DEF,PRE_SUB1,ADD1] >>
  rw[] >>
  fsrw_tac[ARITH_ss][lem] >>
  res_tac >> fsrw_tac[ARITH_ss][] ) >>
strip_tac >- (
  rw[exp_to_Cexp_def] >>
  BasicProvers.CASE_TAC >> rw[] >>
  fsrw_tac[DNF_ss,ARITH_ss][SUBSET_DEF,PRE_SUB1] >>
  conj_tac >> Cases >> fsrw_tac[ARITH_ss][ADD1] >>
  strip_tac >> res_tac >> fsrw_tac[ARITH_ss][] ) >>
strip_tac >- (
  rw[exp_to_Cexp_def] >>
  BasicProvers.CASE_TAC >> rw[] >>
  fsrw_tac[DNF_ss,ARITH_ss][SUBSET_DEF,PRE_SUB1] >>
  conj_tac >> Cases >> fsrw_tac[ARITH_ss][ADD1] >>
  strip_tac >> res_tac >> fsrw_tac[ARITH_ss][] ) >>
strip_tac >- (
  rw[exp_to_Cexp_def] >> rw[] >>
  fsrw_tac[DNF_ss,ARITH_ss][SUBSET_DEF,PRE_SUB1] ) >>
strip_tac >- (
  rw[exp_to_Cexp_def] >> rw[] >>
  fsrw_tac[DNF_ss,ARITH_ss][SUBSET_DEF,PRE_SUB1] ) >>
strip_tac >- (
  rw[exp_to_Cexp_def] >> rw[] >>
  fsrw_tac[DNF_ss,ARITH_ss][SUBSET_DEF,PRE_SUB1] ) >>
strip_tac >- ( rw[exp_to_Cexp_def] >> rw[] ) >>
strip_tac >- (
  rw[exp_to_Cexp_def] >>
  BasicProvers.CASE_TAC >> rw[] >>
  fsrw_tac[DNF_ss,ARITH_ss][SUBSET_DEF] ) >>
strip_tac >- (
  rw[exp_to_Cexp_def] >> rw[] >>
  fsrw_tac[DNF_ss,ARITH_ss][SUBSET_DEF] ) >>
strip_tac >- (
  rw[exp_to_Cexp_def] >>
  rw[] >- (
    first_x_assum match_mp_tac >>
    fsrw_tac[DNF_ss][SUBSET_DEF] ) >>
  qspecl_then[`0`,`Cpes'`]strip_assume_tac free_vars_remove_mat_var_SUBSET >>
  unabbrev_all_tac >>
  fsrw_tac[DNF_ss,ARITH_ss][EVERY_MEM,SUBSET_DEF,FORALL_PROD,PRE_SUB1,pes_to_Cpes_MAP,LET_THM,MEM_MAP,UNCURRY,FV_pes_MAP] >>
  simp[GSYM FORALL_AND_THM,GSYM IMP_CONJ_THM] >>
  qx_gen_tac`m` >> strip_tac >>
  Cases_on`m=0`>>fsrw_tac[ARITH_ss][] >>
  first_x_assum(qspec_then`m`mp_tac) >>
  simp[EXISTS_PROD] >>
  simp[GSYM LEFT_FORALL_IMP_THM] >>
  map_every qx_gen_tac[`pp`,`ee`,`v`] >>
  qmatch_abbrev_tac`P ⇒ Q` >>
  qunabbrev_tac`P` >>
  srw_tac[ARITH_ss][] >>
  first_x_assum(qspecl_then[`pp`,`ee`,`v`]mp_tac) >>
  simp[] >>
  qmatch_abbrev_tac`(P ⇒ R) ⇒ Q` >>
  qsuff_tac`P` >- (
    simp[Abbr`Q`,Abbr`R`] >>
    qspecl_then[`pp`,`s`,`[]`]mp_tac(CONJUNCT1 LENGTH_FST_pat_to_Cpat_bvars) >>
    simp[] ) >>
  simp[Abbr`P`] >>
  simp[set_FST_pat_to_Cpat_bvars] >>
  metis_tac[] ) >>
strip_tac >- (
  rw[exp_to_Cexp_def] >>
  fsrw_tac[DNF_ss,ARITH_ss][SUBSET_DEF,PRE_SUB1,ADD1] >>
  conj_tac >> Cases >> fsrw_tac[ARITH_ss,DNF_ss][ADD1,lem] >>
  strip_tac >> res_tac >> fsrw_tac[ARITH_ss][] ) >>
strip_tac >- (
  rw[exp_to_Cexp_def] >>
  fsrw_tac[DNF_ss,ARITH_ss][SUBSET_DEF,PRE_SUB1,ADD1,LET_THM,free_vars_defs_MAP,defs_to_Cdefs_MAP,MEM_FLAT,FV_defs_MAP] >>
  fsrw_tac[DNF_ss,ARITH_ss][EVERY_MEM,FORALL_PROD,MEM_MAP] >>
  conj_tac >- (
    simp[GSYM FORALL_AND_THM,GSYM IMP_CONJ_THM] >>
    map_every qx_gen_tac[`m`,`x`,`y`,`z`] >>
    strip_tac >>
    last_x_assum(qspecl_then[`m`,`x`,`y`,`z`]mp_tac) >>
    fs[EXISTS_PROD] >>
    discharge_hyps >- metis_tac[] >>
    discharge_hyps >- fs[Abbr`m'`] >>
    simp[] ) >>
  simp[GSYM FORALL_AND_THM] >>
  simp[GSYM IMP_CONJ_THM] >>
  qx_gen_tac`m` >> strip_tac >>
  last_x_assum(qspec_then`m`mp_tac) >>
  discharge_hyps >- (
    simp[MEM_MAP,EXISTS_PROD] >>
    metis_tac[] ) >>
  simp[] ) >>
rw[exp_to_Cexp_def] >>
qabbrev_tac `q = pat_to_Cpat m p` >>
PairCases_on`q`>>fs[] )

val free_vars_exp_to_Cexp_matchable = store_thm("free_vars_exp_to_Cexp_matchable",
  ``SFV e ⊆ set m.bvars ∧ count (LENGTH m.bvars) ⊆ s ⇒ set (free_vars (exp_to_Cexp m e)) ⊆ s``,
  metis_tac[free_vars_exp_to_Cexp,SUBSET_TRANS])

(* closed lemmas *)

val v_to_Cv_closed = store_thm(
"v_to_Cv_closed",
``(∀m v. closed [] v ⇒ Cclosed (v_to_Cv m v)) ∧
  (∀m vs. EVERY (closed []) vs ⇒ EVERY (Cclosed) (vs_to_Cvs m vs)) ∧
  (∀m env. EVERY (closed []) (MAP SND env) ⇒ EVERY (Cclosed) (env_to_Cenv m env))``,
ho_match_mp_tac v_to_Cv_ind >>
rw[v_to_Cv_def] >> rw[Cclosed_rules]
>- (
  fs[Once closed_cases] >>
  rw[Once Cclosed_cases] >- simp[Abbr`Ce`] >>
  simp[Abbr`Cenv`,env_to_Cenv_MAP,SUBSET_DEF,GSYM LEFT_FORALL_IMP_THM] >>
  Cases >> simp[Abbr`Ce`,ADD1] >>
  strip_tac >>
  qmatch_assum_abbrev_tac`MEM z (free_vars (exp_to_Cexp s e))` >>
  qspecl_then[`s`,`e`]mp_tac free_vars_exp_to_Cexp >>
  unabbrev_all_tac >>
  simp[SUBSET_DEF,ADD1] >> fs[SUBSET_DEF] >>
  discharge_hyps >- (rw[] >> res_tac >> fs[MEM_MAP] >> metis_tac[]) >>
  disch_then(qspec_then`n+1`mp_tac) >>
  simp[] ) >>
fs[Once closed_cases] >>
simp[Once Cclosed_cases] >>
simp[defs_to_Cdefs_MAP,Abbr`Cdefs`,MEM_MAP,FORALL_PROD,EXISTS_PROD] >>
Q.ISPECL_THEN[`fns`,`vn`,`0:num`]mp_tac find_index_MEM >>
`MEM vn (fns)` by (
  unabbrev_all_tac >>
  fs[MEM_MAP,EXISTS_PROD] >>
  PROVE_TAC[] ) >>
simp[] >> strip_tac >>
`LENGTH defs = LENGTH fns`by simp[Abbr`fns`] >>
simp[] >>
fsrw_tac[DNF_ss][] >>
fsrw_tac[DNF_ss][MEM_EL] >>
rpt gen_tac >> strip_tac >>
qmatch_assum_rename_tac`(a,b,c) = EL j defs`[] >>
first_x_assum(qspecl_then[`a`,`b`,`c`,`j`]mp_tac) >>
simp[] >>
strip_tac >>
match_mp_tac free_vars_exp_to_Cexp_matchable >>
simp[] >>
unabbrev_all_tac >> fs[] >>
conj_tac >- (
  fsrw_tac[DNF_ss][SUBSET_DEF,MEM_MAP,EXISTS_PROD] >>
  rw[] >> res_tac >> fs[MEM_MAP] >>
  metis_tac[]) >>
simp[env_to_Cenv_MAP,ADD1])

(* do_app SOME lemmas *)

val do_app_Opn_SOME = store_thm("do_app_Opn_SOME",
  ``(do_app s env (Opn opn) v1 v2 = SOME (s',env',exp')) =
    ((s' = s) ∧ (env' = env) ∧
     ∃n1 n2. (v1 = Litv (IntLit n1)) ∧ (v2 = Litv (IntLit n2)) ∧
      (exp' =
       if (n2 = 0) ∧ ((opn = Divide) ∨ (opn = Modulo)) then
         Raise Div_error
       else Lit (IntLit (opn_lookup opn n1 n2))))``,
  Cases_on`opn`>>
  Cases_on`v1`>>TRY(Cases_on`l`)>>
  Cases_on`v2`>>TRY(Cases_on`l`)>>
  rw[do_app_def,opn_lookup_def] >>
  rw[EQ_IMP_THM])

val do_app_Opb_SOME = store_thm("do_app_Opb_SOME",
  ``(do_app s env (Opb opb) v1 v2 = SOME (s',env',exp')) =
    ((s' = s) ∧ (env' = env) ∧
     ∃n1 n2. (v1 = Litv (IntLit n1)) ∧ (v2 = Litv (IntLit n2)) ∧
      (exp' = Lit (Bool (opb_lookup opb n1 n2))))``,
  Cases_on`opb`>>
  Cases_on`v1`>>TRY(Cases_on`l`)>>
  Cases_on`v2`>>TRY(Cases_on`l`)>>
  rw[do_app_def,opb_lookup_def] >>
  rw[EQ_IMP_THM])

val do_app_Opapp_SOME = store_thm("do_app_Opapp_SOME",
``(do_app s env_ Opapp v1 v2 = SOME (s',env',exp')) =
  ((s' = s) ∧
   ((∃env n to e. (v1 = Closure env n e) ∧
                  (env' = bind n v2 env) ∧
                  (exp' = e)) ∨
    (∃env funs n to m.
      (v1 = Recclosure env funs n) ∧
      (find_recfun n funs = SOME (m,exp')) ∧
      (env' = bind m v2 (build_rec_env funs env env)))))``,
  Cases_on`v1`>>rw[do_app_def] >- rw[EQ_IMP_THM] >>
  BasicProvers.EVERY_CASE_TAC >>
  fs[optionTheory.OPTION_MAP_EQ_NONE] >>
  rw[EQ_IMP_THM] >>
  pop_assum (assume_tac o SYM) >> fs[])

(* correctness *)

val v_to_Cv_inj = store_thm(
"v_to_Cv_inj",
``(∀s v1 v2.
    all_cns v1 ⊆ set (MAP FST (cenv:envC)) ∧
    all_cns v2 ⊆ set (MAP FST cenv) ∧
    good_cmap cenv s ∧
    ¬contains_closure v1 ∧ ¬contains_closure v2 ∧
    (v_to_Cv s v1 = v_to_Cv s v2) ⇒ (v1 = v2)) ∧
  (∀s vs1 vs2.
    BIGUNION (IMAGE all_cns (set vs1)) ⊆ set (MAP FST cenv) ∧
    BIGUNION (IMAGE all_cns (set vs2)) ⊆ set (MAP FST cenv) ∧
    good_cmap cenv s ∧
    ¬EXISTS contains_closure vs1 ∧ ¬EXISTS contains_closure vs2 ∧
    (vs_to_Cvs s vs1 = vs_to_Cvs s vs2) ⇒ (vs1 = vs2)) ∧
  (∀(s:string id|->num) (env1:envE).T)``,
ho_match_mp_tac v_to_Cv_ind >> rw[v_to_Cv_def,LET_THM,vs_to_Cvs_MAP,env_to_Cenv_MAP] >>
TRY (Cases_on`v2`>>fs[v_to_Cv_def,LET_THM]>>NO_TAC)
>- (
  Cases_on`v2`>>fs[v_to_Cv_def,vs_to_Cvs_MAP,MAP_EQ_EVERY2,EVERY2_EVERY,LET_THM] >>
  fsrw_tac[ETA_ss][good_cmap_def,MEM_MAP,EXISTS_PROD,contains_closure_def] >>
  fs[FORALL_PROD] >>
  metis_tac[] )
>- (
  fs[good_cmap_def,MEM_MAP] >>
  metis_tac[] )
>- fs[contains_closure_def]
>- fs[contains_closure_def]
>- (Cases_on`vs2`>>fs[]))

val pat_to_Cpat_acc = store_thm("pat_to_Cpat_acc",
  ``(∀p s s' Cp. (pat_to_Cpat s p = (s',Cp)) ⇒
      ∃ls. (s'.bvars = ls ++ s.bvars) ∧ (set ls = pat_vars p) ∧
           (pat_to_Cpat (s with bvars := []) p = (s' with bvars := ls, Cp))) ∧
    (∀ps s s' Cps. (pats_to_Cpats s ps = (s',Cps)) ⇒
      ∃ls. (s'.bvars = ls ++ s.bvars) ∧ (set ls = BIGUNION (IMAGE pat_vars (set ps))) ∧
           (pats_to_Cpats (s with bvars := []) ps = (s' with bvars := ls, Cps)))``,
  ho_match_mp_tac(TypeBase.induction_of``:pat``) >>
  rw[pat_to_Cpat_def,exp_to_Cexp_state_component_equality,pat_bindings_def,pats_bindings_MAP]
  >- (
    first_x_assum(qspec_then`s`mp_tac) >>
    qabbrev_tac`q = pats_to_Cpats s ps` >>
    PairCases_on`q`>>fs[LET_THM]>>rw[]>>fsrw_tac[ETA_ss][] >>
    srw_tac[DNF_ss][EXTENSION,MEM_FLAT,MEM_MAP] >>
    metis_tac[])
  >- (
    first_x_assum(qspec_then`s`mp_tac) >>
    qabbrev_tac`q = pat_to_Cpat s p` >>
    PairCases_on`q`>>fs[LET_THM]>>rw[]>>fs[]) >>
  last_x_assum(qspec_then`s`mp_tac)>>
  qabbrev_tac`q = pat_to_Cpat s p` >>
  PairCases_on`q`>>fs[LET_THM]>>rw[]>>fs[UNCURRY]>>rw[]>>
  qabbrev_tac`r = pats_to_Cpats q0 ps` >>
  PairCases_on`r`>>fs[]>>
  first_assum(qspec_then`q0`mp_tac) >>
  first_x_assum(qspec_then`q0 with bvars := ls`mp_tac) >>
  simp[] >>
  qabbrev_tac`q = pats_to_Cpats (q0 with bvars := ls) ps` >>
  qabbrev_tac`r = pats_to_Cpats (q0 with bvars := []) ps` >>
  PairCases_on`q`>>
  PairCases_on`r`>>
  simp[] >> rw[] >>
  fs[exp_to_Cexp_state_component_equality,UNION_COMM])

val exp_to_Cexp_append_bvars = store_thm("exp_to_Cexp_append_bvars",
  ``∀ls s e. SFV e ⊆ set s.bvars ⇒ (exp_to_Cexp (s with bvars := s.bvars ++ ls) e = exp_to_Cexp s e)``,
  gen_tac >> ho_match_mp_tac exp_to_Cexp_nice_ind >>
  rw[exp_to_Cexp_def,exps_to_Cexps_MAP,defs_to_Cdefs_MAP,pes_to_Cpes_MAP,FV_pes_MAP,FV_defs_MAP,FV_list_MAP] >>
  TRY (
    fsrw_tac[DNF_ss][SUBSET_DEF,lem,EVERY_MEM,MAP_EQ_f] >>
    rw[] >> first_x_assum (match_mp_tac o MP_CANON) >>
    rw[] >> res_tac >> NO_TAC)
  >- (
    metis_tac[find_index_MEM,find_index_APPEND_same] )
  >- (
    unabbrev_all_tac >>
    conj_tac >- (
      first_x_assum match_mp_tac >>
      fsrw_tac[DNF_ss][SUBSET_DEF] ) >>
    rpt AP_TERM_TAC >>
    rw[MAP_EQ_f,FORALL_PROD] >>
    qmatch_assum_rename_tac`pat_to_Cpat s p = (s',Cp)`[] >>
    qspecl_then[`p`,`s`,`s'`,`Cp`]mp_tac(CONJUNCT1 pat_to_Cpat_acc)>>
    simp[] >>
    qmatch_assum_rename_tac`pat_to_Cpat (s with bvars := s.bvars ++ ls) p = (s'',Cp')`[] >>
    qspecl_then[`p`,`s with bvars := s.bvars ++ ls`,`s''`,`Cp'`]mp_tac(CONJUNCT1 pat_to_Cpat_acc)>>
    simp[] >> rw[] >> fs[exp_to_Cexp_state_component_equality] >>
    fsrw_tac[DNF_ss][EVERY_MEM,FORALL_PROD,SUBSET_DEF,lem] >> rw[] >>
    qmatch_assum_rename_tac`MEM (p,z) pes`[] >>
    first_x_assum(qspecl_then[`p`,`z`]mp_tac) >> simp[lem] >>
    first_x_assum((qspecl_then[`z`,`p`]mp_tac) o CONV_RULE (RESORT_FORALL_CONV List.rev)) >>
    simp[] >> rw[] >>
    qmatch_assum_abbrev_tac`exp_to_Cexp a z = exp_to_Cexp b z` >>
    qsuff_tac`s'' = a`>-rw[] >>
    rw[Abbr`a`,exp_to_Cexp_state_component_equality] )
  >- (
    rw[MAP_EQ_f,FORALL_PROD] >>
    unabbrev_all_tac >>
    fsrw_tac[DNF_ss][EVERY_MEM,FORALL_PROD] >>
    first_x_assum (ho_match_mp_tac o MP_CANON) >>
    fsrw_tac[DNF_ss][SUBSET_DEF,FORALL_PROD,MEM_MAP,EXISTS_PROD,LET_THM] >>
    metis_tac[] ) >>
  qabbrev_tac`q = pat_to_Cpat m p` >>
  PairCases_on`q`>>fs[])

val exp_to_Cexp_append_bvars_matchable = store_thm(
  "exp_to_Cexp_append_bvars_matchable",
  ``∀ls s s' e. SFV e ⊆ set s.bvars ∧ (s'.cnmap = s.cnmap) ∧ (s'.bvars = s.bvars ++ ls) ⇒
             (exp_to_Cexp s' e = exp_to_Cexp s e)``,
  rw[] >> imp_res_tac exp_to_Cexp_append_bvars >>
  pop_assum(qspec_then`ls`strip_assume_tac) >>
  qmatch_assum_abbrev_tac`exp_to_Cexp z e = exp_to_Cexp s e` >>
  qsuff_tac`z = s'`>-PROVE_TAC[]>>
  simp[exp_to_Cexp_state_component_equality,Abbr`z`])

val closed_under_cenv_def = Define`
  closed_under_cenv (cenv:envC) (menv:envM) env s =
  (∀v. v ∈ menv_range menv ∨ v ∈ env_range env ∨ MEM v s ⇒ all_cns v ⊆ set (MAP FST cenv))`

val evaluate_closed_under_cenv = store_thm("evaluate_closed_under_cenv",
  ``∀menv cenv s env exp res. closed_under_cenv cenv menv env s ∧ evaluate menv cenv s env exp res ⇒
    closed_under_cenv cenv menv env (FST res)``,
  rw[] >>
  qspecl_then[`menv`,`cenv`,`s`,`env`,`exp`,`res`]mp_tac (CONJUNCT1 evaluate_all_cns) >>
  fsrw_tac[DNF_ss][closed_under_cenv_def])

val is_null_def = Define`is_null menv ⇔ menv = []`

val no_closures_contains_closure = store_thm("no_closures_contains_closure",
  ``(∀v m. no_closures (v_to_Cv m v) = ¬contains_closure v)``,
  ho_match_mp_tac contains_closure_ind >>
  simp[contains_closure_def,v_to_Cv_def,no_closures_def] >>
  simp_tac(srw_ss()++DNF_ss)[EVERY_MEM,vs_to_Cvs_MAP,MEM_MAP])

val exp_to_Cexp_thm1 = store_thm("exp_to_Cexp_thm1",
  ``(∀menv cenv s env exp res. evaluate menv cenv s env exp res ⇒
     (is_null menv) ∧
     FV exp ⊆ set (MAP (Short o FST) env) ∪ menv_dom menv ∧
     (EVERY (closed menv) s) ∧ (EVERY (closed menv) (MAP SND env)) ∧
     EVERY (EVERY (closed menv) o MAP SND) (MAP SND menv) ∧
     closed_under_cenv cenv menv env s ∧
     (SND res ≠ Rerr Rtype_error) ⇒
     ∀cm. good_cmap cenv cm ⇒
       ∃Cres.
       Cevaluate
         (MAP (v_to_Cv cm) s)
         (env_to_Cenv cm env)
         (exp_to_Cexp (<| bvars := MAP FST env; cnmap := cm|>) exp)
         Cres ∧
         EVERY2 (syneq) (MAP (v_to_Cv cm) (FST res)) (FST Cres) ∧
         result_rel (syneq) (map_result (v_to_Cv cm) (SND res)) (SND Cres))∧
    (∀menv cenv s env exps res. evaluate_list menv cenv s env exps res ⇒
     (is_null menv) ∧
     FV_list exps ⊆ set (MAP (Short o FST) env) ∪ menv_dom menv ∧
     (EVERY (closed menv) s) ∧ (EVERY (closed menv) (MAP SND env)) ∧
     EVERY (EVERY (closed menv) o MAP SND) (MAP SND menv) ∧
     closed_under_cenv cenv menv env s ∧
     (SND res ≠ Rerr Rtype_error) ⇒
     ∀cm. good_cmap cenv cm ⇒
       ∃Cres.
       Cevaluate_list
         (MAP (v_to_Cv cm) s)
         (env_to_Cenv cm env)
         (MAP (exp_to_Cexp (<| bvars := MAP FST env; cnmap := cm|>)) exps)
         Cres ∧
         EVERY2 (syneq) (MAP (v_to_Cv cm) (FST res)) (FST Cres) ∧
         result_rel (EVERY2 (syneq)) (map_result (MAP (v_to_Cv cm)) (SND res)) (SND Cres))``,
  ho_match_mp_tac evaluate_nicematch_strongind >>
  strip_tac >- rw[exp_to_Cexp_def,v_to_Cv_def] >>
  strip_tac >- rw[exp_to_Cexp_def] >>
  strip_tac >- (
    rw[exp_to_Cexp_def] >> fs[] >>
    first_x_assum(qspec_then`cm`mp_tac) >> rw[] >>
    Cases_on`Cres`>>fs[] >>
    rw[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][] >>
    PROVE_TAC[]) >>
  strip_tac >- (
    rw[exp_to_Cexp_def] >> fs[bind_def] >>
    rw[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][EXISTS_PROD] >>
    disj2_tac >> disj1_tac >>
    last_x_assum(qspec_then`cm`mp_tac) >> simp[] >>
    disch_then(Q.X_CHOOSE_THEN`s2`strip_assume_tac) >>
    qspecl_then[`menv`,`cenv`,`s`,`env`,`exp`,`(s',Rerr (Rraise (Int_error n)))`]mp_tac(CONJUNCT1 evaluate_closed) >>
    qspecl_then[`menv`,`cenv`,`s`,`env`,`exp`,`(s',Rerr (Rraise (Int_error n)))`]mp_tac(evaluate_closed_under_cenv) >>
    fsrw_tac[DNF_ss][env_to_Cenv_MAP,SUBSET_DEF,lem] >> strip_tac >> strip_tac >>
    first_x_assum(qspec_then`cm`mp_tac) >>
    fsrw_tac[DNF_ss][closed_under_cenv_def,EXISTS_PROD] >>
    map_every qx_gen_tac [`s3`,`v`] >> strip_tac >>
    CONV_TAC(RESORT_EXISTS_CONV List.rev) >>
    map_every qexists_tac[`n`,`s2`] >> simp[] >> fs[v_to_Cv_def] >>
    qmatch_assum_abbrev_tac`Cevaluate s1 env1 exp1 (s3,v)` >>
    qspecl_then[`s1`,`env1`,`exp1`,`(s3,v)`]mp_tac(CONJUNCT1 Cevaluate_syneq) >>
    simp[] >>
    disch_then(qspecl_then[`$=`,`s2`,`env1`,`exp1`]mp_tac) >>
    simp[syneq_exp_refl,EXISTS_PROD] >>
    metis_tac[result_rel_syneq_trans,EVERY2_syneq_trans]) >>
  strip_tac >- (
    rw[exp_to_Cexp_def] >>
    rw[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][EXISTS_PROD]) >>
  strip_tac >- (
    rw[exp_to_Cexp_def,v_to_Cv_def,
       exps_to_Cexps_MAP,vs_to_Cvs_MAP,
       Cevaluate_con] >>
    fsrw_tac[DNF_ss,ETA_ss][EXISTS_PROD] >>
    simp[Once syneq_cases]) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rw[exp_to_Cexp_def,v_to_Cv_def,
       exps_to_Cexps_MAP,Cevaluate_con] >>
    fsrw_tac[DNF_ss,ETA_ss][EXISTS_PROD]) >>
  strip_tac >- (
    fs[exp_to_Cexp_def,MEM_MAP,pairTheory.EXISTS_PROD,env_to_Cenv_MAP,lookup_var_id_def] >>
    rpt gen_tac >>
    reverse BasicProvers.CASE_TAC >- (
      simp[MEM_FLAT,is_null_def,MEM_MAP] >>
      rw[] >> fs[] ) >>
    simp_tac(srw_ss()++DNF_ss)[MEM_FLAT,MEM_MAP] >>
    qx_gen_tac `m` >> simp[exp_to_Cexp_def] >>
    gen_tac >> ntac 3 strip_tac >>
    fs[ALOOKUP_LEAST_EL] >>
    simp[find_index_LEAST_EL] >>
    conj_asm1_tac >- (
      numLib.LEAST_ELIM_TAC >>
      fs[MEM_EL] >>
      conj_tac >- PROVE_TAC[] >>
      rw[] >>
      qpat_assum`x < LENGTH env`kall_tac >>
      qmatch_assum_rename_tac`a < LENGTH env`[] >>
      qmatch_rename_tac`b < LENGTH env`[] >>
      `~(a<b)`by metis_tac[] >>
      DECIDE_TAC ) >>
    `(LEAST m. EL m (MAP FST env) = a) = (LEAST m. a = EL m (MAP FST env))` by (
      rw[] >> AP_TERM_TAC >> rw[FUN_EQ_THM] >> PROVE_TAC[] ) >>
    fs[EL_MAP]) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rw[exp_to_Cexp_def,v_to_Cv_def,env_to_Cenv_MAP,LET_THM] >>
    rw[Once syneq_cases] >>
    qexists_tac`λv1 v2. v1 < LENGTH env ∧ (v2 = v1)` >>
    qexists_tac`λv1 v2. v1 < 1 ∧ (v2 = v1)` >>
    simp[] >>
    simp[Once syneq_exp_cases] >>
    disj2_tac >>
    AP_TERM_TAC >>
    qmatch_abbrev_tac`exp_to_Cexp z' e = exp_to_Cexp z e` >>
    Q.ISPECL_THEN[`m.bvars`,`z`,`e`]mp_tac exp_to_Cexp_append_bvars >>
    fsrw_tac[DNF_ss][SUBSET_DEF,lem,Abbr`z`] ) >>
  strip_tac >- (
    rw[exp_to_Cexp_def,LET_THM] >> fs[] >>
    rw[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][EXISTS_PROD] >>
    first_x_assum(qspec_then`cm`mp_tac)>>simp[]>>
    disch_then(qx_choosel_then[`s0`,`v0`]strip_assume_tac)>>
    CONV_TAC SWAP_EXISTS_CONV >>qexists_tac`s0`>>
    CONV_TAC SWAP_EXISTS_CONV >>qexists_tac`v0`>>
    simp[] >>
    fs[do_uapp_def,LET_THM,store_alloc_def] >>
    BasicProvers.EVERY_CASE_TAC >>
    fs[v_to_Cv_def,LET_THM] >- (
      rpt BasicProvers.VAR_EQ_TAC >>
      fs[v_to_Cv_def] >>
      reverse conj_asm2_tac >- fs[EVERY2_EVERY] >>
      match_mp_tac EVERY2_APPEND_suff >>
      simp[] ) >>
    fs[store_lookup_def,el_check_def,EVERY2_EVERY] >>
    rw[] >> rfs[] >>
    fsrw_tac[DNF_ss][EVERY_MEM,FORALL_PROD] >>
    first_x_assum match_mp_tac >>
    simp[MEM_ZIP] >>
    qexists_tac`n` >>
    simp[EL_MAP] ) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rw[exp_to_Cexp_def,LET_THM,EXISTS_PROD] >>
    rw[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][] ) >>
  strip_tac >- (
    ntac 3 gen_tac >>
    Cases >> fs[exp_to_Cexp_def] >>
    qx_gen_tac `e1` >>
    qx_gen_tac `e2` >>
    rw[LET_THM] >- (
      rw[Once Cevaluate_cases] >>
      fsrw_tac[DNF_ss][] >>
      disj1_tac >>
      rw[Once(CONJUNCT2 Cevaluate_cases)] >> fsrw_tac[DNF_ss][] >>
      rw[Once(CONJUNCT2 Cevaluate_cases)] >> fsrw_tac[DNF_ss][] >>
      rw[Once(CONJUNCT2 Cevaluate_cases)] >> fsrw_tac[DNF_ss][] >>
      rpt (first_x_assum (qspec_then `cm` mp_tac)) >>
      `closed_under_cenv cenv menv env' s'' ∧ closed_under_cenv cenv menv env s'` by (
        `(s'' = s3) ∧ (env' = env)` by fs[do_app_Opn_SOME] >>
        imp_res_tac evaluate_closed_under_cenv >> fs[] ) >>
      rw[] >>
      qmatch_assum_rename_tac `syneq (v_to_Cv cm v1) w1`[] >>
      qspecl_then[`menv`,`cenv`,`s`,`env`,`e1`,`(s',Rval v1)`]mp_tac(CONJUNCT1 evaluate_closed) >>
      simp[] >> strip_tac >> fs[] >>
      qmatch_assum_rename_tac `syneq (v_to_Cv m v2) w2`[] >>
      qmatch_assum_rename_tac`SND r1 = Rval w1`[] >>
      qmatch_assum_rename_tac`SND r2 = Rval w2`[] >>
      qmatch_assum_abbrev_tac`Cevaluate sa enva e1a r1` >>
      qmatch_assum_abbrev_tac`Cevaluate sb enva e2a r2` >>
      CONV_TAC SWAP_EXISTS_CONV >> qexists_tac`w1` >>
      CONV_TAC (RESORT_EXISTS_CONV List.rev) >> qexists_tac`FST r1` >>
      PairCases_on`r1`>>fs[] >>
      qspecl_then[`sb`,`enva`,`e2a`,`r2`]mp_tac (CONJUNCT1 Cevaluate_syneq) >> simp[] >>
      disch_then(qspecl_then[`$=`,`r10`,`enva`,`e2a`]mp_tac) >> simp[syneq_exp_refl] >>
      fsrw_tac[DNF_ss][FORALL_PROD] >>
      map_every qx_gen_tac[`s2`,`u2`] >> strip_tac >>
      PairCases_on`res`>>fsrw_tac[DNF_ss][EXISTS_PROD] >> rw[] >>
      qspecl_then[`menv`,`cenv`,`s'`,`env`,`e2`,`(s3,Rval v2)`]mp_tac(CONJUNCT1 evaluate_closed) >>
      simp[] >> strip_tac >>
      qmatch_assum_rename_tac `do_app s3 env (Opn opn) v1 v2 = SOME (s4,env',exp'')` [] >>
      Q.ISPECL_THEN[`menv`,`s3`,`s4`,`env`,`Opn opn`,`v1`,`v2`,`env'`,`exp''`]mp_tac do_app_closed >>
      simp[] >> strip_tac >> fs[] >>
      fs[do_app_Opn_SOME] >> rw[] >>
      fs[v_to_Cv_def] >> rw[] >>
      fs[Once syneq_cases] >> rw[] >>
      map_every qexists_tac[`CLitv (IntLit n2)`,`s2`] >>
      simp[] >>
      qpat_assum`Cevaluate X enva (exp_to_Cexp Y Z) R`mp_tac >>
      BasicProvers.CASE_TAC >- (
        simp[exp_to_Cexp_def] >>
        fs[i0_def] >>
        metis_tac[EVERY2_syneq_trans] ) >>
      simp[exp_to_Cexp_def] >> strip_tac >>
      conj_tac >- metis_tac[EVERY2_syneq_trans] >>
      fs[v_to_Cv_def] >> rw[] >>
      Cases_on`opn`>>fs[]>>
      fs[v_to_Cv_def,opn_lookup_def,i0_def] >>
      Cases_on`n2=0`>>fs[v_to_Cv_def] )
    >- (
      qmatch_assum_rename_tac `do_app s3 env (Opb opb) v1 v2 = SOME (s4,env',exp'')` [] >>
      fs[] >>
      qmatch_assum_rename_tac`evaluate menv cenv s env e1 (s1,Rval v1)`[] >>
      qmatch_assum_rename_tac`evaluate menv cenv s1 env e2 (s2,Rval v2)`[] >>
      qspecl_then[`menv`,`cenv`,`s`,`env`,`e1`,`(s1,Rval v1)`]mp_tac(CONJUNCT1 evaluate_closed) >>
      simp[] >> strip_tac >>
      qspecl_then[`menv`,`cenv`,`s1`,`env`,`e2`,`(s2,Rval v2)`]mp_tac(CONJUNCT1 evaluate_closed) >>
      simp[] >> strip_tac >>
      fs[] >>
      Q.ISPECL_THEN[`menv`,`s2`,`s4`,`env`,`Opb opb`,`v1`,`v2`,`env'`,`exp''`]mp_tac do_app_closed >>
      simp[] >> strip_tac >> fs[] >>
      `closed_under_cenv cenv menv env s1 ∧ closed_under_cenv cenv menv env' s4` by (
        fs[do_app_Opb_SOME] >>
        imp_res_tac evaluate_closed_under_cenv >> rfs[] ) >>
      fs[] >>
      rpt (first_x_assum (qspec_then `cm` mp_tac)) >> rw[] >>
      qmatch_assum_rename_tac `syneq (v_to_Cv m v1) w1`[] >>
      qmatch_assum_rename_tac `syneq (v_to_Cv m v2) w2`[] >>
      Cases_on`Cres`>> Cases_on`Cres'`>> Cases_on`Cres''`>>fs[]>>rw[]>>
      fs[do_app_Opb_SOME]>>rw[]>>fs[v_to_Cv_def]>>rw[]>>fs[]>>rw[]>>
      fs[v_to_Cv_def]>>fs[]>>rw[]>>
      fs[exp_to_Cexp_def]>>rw[]>>
      qabbrev_tac`sa = MAP (v_to_Cv m) s` >>
      qabbrev_tac`sb = MAP (v_to_Cv m) s1` >>
      qabbrev_tac`sc = MAP (v_to_Cv m) s2` >> fs[]>>rw[]>>
      qmatch_assum_rename_tac`EVERY2 (syneq) sb sd`[]>>
      qmatch_assum_rename_tac`EVERY2 (syneq) sc se`[]>>
      qabbrev_tac`enva = env_to_Cenv m env`>>
      Q.PAT_ABBREV_TAC`e1a = exp_to_Cexp X e1`>>
      Q.PAT_ABBREV_TAC`e2a = exp_to_Cexp X e2`>>
      qabbrev_tac`w1 = CLitv (IntLit n1)`>>
      qabbrev_tac`w2 = CLitv (IntLit n2)`>>
      Cases_on `opb` >> fsrw_tac[DNF_ss][EXISTS_PROD,opb_lookup_def]
      >- (
        rw[Once Cevaluate_cases] >>
        rw[Once (CONJUNCT2 Cevaluate_cases)] >>
        rw[Once (CONJUNCT2 Cevaluate_cases)] >>
        rw[Once (CONJUNCT2 Cevaluate_cases)] >>
        srw_tac[DNF_ss][] >>
        CONV_TAC (RESORT_EXISTS_CONV List.rev) >> qexists_tac`sd` >>
        CONV_TAC SWAP_EXISTS_CONV >> qexists_tac`w1` >>
        qspecl_then[`sb`,`enva`,`e2a`,`(se,Rval w2)`]mp_tac(CONJUNCT1 Cevaluate_syneq) >> simp[] >>
        disch_then(qspecl_then[`$=`,`sd`,`enva`,`e2a`]mp_tac) >>
        simp[EXISTS_PROD,syneq_exp_refl] >>
        fsrw_tac[DNF_ss][] >>
        map_every qx_gen_tac[`sf`,`w3`] >>
        strip_tac >>
        map_every qexists_tac[`w3`,`sf`] >>
        reverse conj_tac >- metis_tac[EVERY2_syneq_trans] >>
        map_every qunabbrev_tac[`w1`,`w2`] >> fs[])
      >- (
        rw[Once Cevaluate_cases] >>
        srw_tac[DNF_ss][] >>
        CONV_TAC (RESORT_EXISTS_CONV List.rev) >>
        map_every qexists_tac [`w1`,`sd`] >> fs[] >>
        rw[Once Cevaluate_cases] >>
        srw_tac[DNF_ss][] >>
        qspecl_then[`sb`,`enva`,`e2a`,`(se,Rval w2)`]mp_tac(CONJUNCT1 Cevaluate_syneq) >> simp[] >>
        disch_then(qspecl_then[`λv1 v2. v2 = v1 + 1`,`sd`,`w1::enva`,`shift 1 0 e2a`]mp_tac) >>
        qmatch_abbrev_tac`(P⇒Q)⇒R` >>
        `P` by (
          map_every qunabbrev_tac[`P`,`Q`,`R`] >>
          conj_tac >- (
            simp[shift_def] >>
            match_mp_tac mkshift_thm >>
            simp[ADD1,Abbr`enva`,Abbr`e2a`,env_to_Cenv_MAP] >>
            match_mp_tac free_vars_exp_to_Cexp_matchable >>
            simp[] >>
            fsrw_tac[DNF_ss][SUBSET_DEF,MEM_MAP,is_null_def,MEM_FLAT] >> rfs[] >>
            fsrw_tac[DNF_ss][EXISTS_PROD] >> rw[] >> res_tac >> fs[] >> metis_tac[]) >>
          lrw[EL_CONS,PRE_SUB1] ) >>
        simp[] >> map_every qunabbrev_tac[`P`,`Q`,`R`] >> pop_assum kall_tac >>
        fsrw_tac[DNF_ss][FORALL_PROD] >>
        map_every qx_gen_tac[`sf`,`w3`] >> strip_tac >>
        CONV_TAC (RESORT_EXISTS_CONV List.rev) >>
        map_every qexists_tac [`w3`,`sf`] >> fs[] >>
        rw[Once Cevaluate_cases] >>
        srw_tac[DNF_ss][] >>
        rw[Once (CONJUNCT2 Cevaluate_cases)] >>
        rw[Once (CONJUNCT2 Cevaluate_cases)] >>
        lrw[Once (CONJUNCT2 Cevaluate_cases),ADD1,Abbr`w1`,Abbr`w2`] >>
        fs[] >> rw[integerTheory.int_gt] >>
        metis_tac[EVERY2_syneq_trans])
      >- (
        rw[Once Cevaluate_cases] >>
        srw_tac[DNF_ss][] >>
        rw[Once (CONJUNCT2 Cevaluate_cases)] >>
        rw[Once (CONJUNCT2 Cevaluate_cases)] >>
        rw[Once (CONJUNCT2 Cevaluate_cases)] >>
        rw[Once Cevaluate_cases] >>
        srw_tac[DNF_ss][] >>
        rw[Once (CONJUNCT2 Cevaluate_cases)] >>
        rw[Once (CONJUNCT2 Cevaluate_cases)] >>
        rw[Once (CONJUNCT2 Cevaluate_cases)] >>
        srw_tac[DNF_ss][] >>
        CONV_TAC (RESORT_EXISTS_CONV List.rev) >>
        map_every qexists_tac[`sd`,`w2`,`w1`] >>
        qspecl_then[`sb`,`enva`,`e2a`,`(se,Rval w2)`]mp_tac(CONJUNCT1 Cevaluate_syneq) >> simp[] >>
        disch_then(qspecl_then[`$=`,`sd`,`enva`,`e2a`]mp_tac) >> simp[syneq_exp_refl] >>
        fsrw_tac[DNF_ss][FORALL_PROD,Abbr`w2`,Abbr`w1`] >>
        qx_gen_tac`sf` >> strip_tac >>
        qexists_tac`sf`>>
        reverse conj_tac >- metis_tac[EVERY2_syneq_trans] >>
        rw[CompilerLibTheory.i1_def] >> ARITH_TAC )
      >- (
        rw[Once Cevaluate_cases] >>
        srw_tac[DNF_ss][] >>
        CONV_TAC (RESORT_EXISTS_CONV List.rev) >>
        map_every qexists_tac [`w1`,`sd`] >> fs[] >>
        rw[Once Cevaluate_cases] >>
        srw_tac[DNF_ss][] >>
        qspecl_then[`sb`,`enva`,`e2a`,`(se,Rval w2)`]mp_tac(CONJUNCT1 Cevaluate_syneq) >> simp[] >>
        disch_then(qspecl_then[`λv1 v2. v2 = v1 + 1`,`sd`,`w1::enva`,`shift 1 0 e2a`]mp_tac) >>
        qmatch_abbrev_tac`(P⇒Q)⇒R` >>
        `P` by (
          map_every qunabbrev_tac[`P`,`Q`,`R`] >>
          conj_tac >- (
            simp[shift_def] >>
            match_mp_tac mkshift_thm >>
            simp[ADD1,Abbr`enva`,Abbr`e2a`,env_to_Cenv_MAP] >>
            match_mp_tac free_vars_exp_to_Cexp_matchable >>
            simp[] >>
            fsrw_tac[DNF_ss][SUBSET_DEF,MEM_MAP,is_null_def,MEM_FLAT] >> rfs[] >>
            fsrw_tac[DNF_ss][EXISTS_PROD] >> rw[] >> res_tac >> fs[] >> metis_tac[]) >>
          lrw[EL_CONS,PRE_SUB1] ) >>
        simp[] >> map_every qunabbrev_tac[`P`,`Q`,`R`] >> pop_assum kall_tac >>
        fsrw_tac[DNF_ss][FORALL_PROD] >>
        map_every qx_gen_tac[`sf`,`w3`] >> strip_tac >>
        CONV_TAC (RESORT_EXISTS_CONV List.rev) >>
        map_every qexists_tac [`w3`,`sf`] >> fs[] >>
        rw[Once Cevaluate_cases] >>
        srw_tac[DNF_ss][] >>
        rw[Once (CONJUNCT2 Cevaluate_cases)] >>
        rw[Once (CONJUNCT2 Cevaluate_cases)] >>
        lrw[Once (CONJUNCT2 Cevaluate_cases),ADD1,Abbr`w1`,Abbr`w2`] >>
        rw[Once Cevaluate_cases] >>
        rw[Once (CONJUNCT2 Cevaluate_cases)] >>
        rw[Once (CONJUNCT2 Cevaluate_cases)] >>
        rw[Once (CONJUNCT2 Cevaluate_cases)] >>
        fs[] >>
        lrw[ADD1,CompilerLibTheory.i1_def] >- ARITH_TAC >>
        metis_tac[EVERY2_syneq_trans]) )
    >- (
      rw[Once Cevaluate_cases] >>
      srw_tac[DNF_ss][] >>
      disj1_tac >>
      rw[Once(CONJUNCT2 Cevaluate_cases)] >>
      rw[Once(CONJUNCT2 Cevaluate_cases)] >>
      rw[Once(CONJUNCT2 Cevaluate_cases)] >>
      srw_tac[DNF_ss][] >> fs[] >>
      qspecl_then[`menv`,`cenv`,`s`,`env`,`e1`,`(s',Rval v1)`]mp_tac(CONJUNCT1 evaluate_closed) >>
      simp[]>>strip_tac >>
      qspecl_then[`menv`,`cenv`,`s'`,`env`,`e2`,`(s3,Rval v2)`]mp_tac(CONJUNCT1 evaluate_closed) >>
      simp[]>>strip_tac >>
      Q.ISPECL_THEN[`menv`,`s3`,`s''`,`env`,`Equality`,`v1`,`v2`,`env'`,`exp''`]mp_tac do_app_closed >>
      simp[]>>strip_tac>> fs[] >>
      `closed_under_cenv cenv menv env' s'' ∧ closed_under_cenv cenv menv env s'` by (
        fs[do_app_def] >> imp_res_tac evaluate_closed_under_cenv >> rfs[] ) >> fs[] >>
      rpt (first_x_assum (qspec_then `cm` mp_tac)) >>
      rw[EXISTS_PROD] >>
      qmatch_assum_rename_tac `syneq(v_to_Cv cm v1) w1`[] >>
      qmatch_assum_rename_tac `syneq(v_to_Cv m v2) w2`[] >>
      qabbrev_tac`sa = MAP (v_to_Cv m) s` >>
      qabbrev_tac`sb = MAP (v_to_Cv m) s'` >>
      qabbrev_tac`sc = MAP (v_to_Cv m) s3` >>
      qmatch_assum_abbrev_tac`Cevaluate sa enva e1a X` >>
      qmatch_assum_rename_tac`Abbrev(X=(sd,Rval w1))`[]>> qunabbrev_tac`X` >>
      qmatch_assum_abbrev_tac`Cevaluate sb enva e2a X` >>
      qmatch_assum_rename_tac`Abbrev(X=(se,Rval w2))`[]>>
      qspecl_then[`sb`,`enva`,`e2a`,`X`]mp_tac(CONJUNCT1 Cevaluate_syneq) >> simp[] >>
      disch_then(qspecl_then[`$=`,`sd`,`enva`,`e2a`]mp_tac) >> simp[syneq_exp_refl] >>
      fsrw_tac[DNF_ss][EXISTS_PROD,FORALL_PROD,Abbr`X`] >>
      map_every qx_gen_tac[`sf`,`w3`] >> strip_tac >>
      map_every qexists_tac[`sf`,`w1`,`w3`,`sd`] >>
      simp[] >>
      fs[do_app_def] >>
      rpt BasicProvers.VAR_EQ_TAC >>
      fs[] >>
      rpt BasicProvers.VAR_EQ_TAC >>
      fs[v_to_Cv_def] >> fs[exp_to_Cexp_def] >>
      conj_tac >- metis_tac[EVERY2_syneq_trans] >>
      BasicProvers.CASE_TAC >- (
        fs[] >>
        `no_closures w2` by metis_tac[syneq_no_closures] >>
        `w3 = w2` by metis_tac[no_closures_syneq_equal] >>
        `w2 = v_to_Cv m v2` by metis_tac[no_closures_syneq_equal,syneq_no_closures] >>
        `w1 = v_to_Cv m v1` by metis_tac[no_closures_syneq_equal,syneq_no_closures] >>
        rw[] >>
        reverse EQ_TAC >- rw[] >>
        strip_tac >>
        match_mp_tac (MP_CANON(CONJUNCT1 v_to_Cv_inj)) >>
        qexists_tac`m` >>
        qspecl_then[`menv`,`cenv`,`s`,`env`,`e1`,`(s',Rval v1)`]mp_tac(CONJUNCT1 evaluate_all_cns) >>
        qspecl_then[`menv`,`cenv`,`s'`,`env`,`e2`,`(s'',Rval v2)`]mp_tac(CONJUNCT1 evaluate_all_cns) >>
        fsrw_tac[DNF_ss][closed_under_cenv_def] ) >>
      metis_tac[no_closures_contains_closure,syneq_no_closures])
    >- (
      rw[Once Cevaluate_cases] >>
      srw_tac[DNF_ss][] >>
      disj1_tac >>
      rw[Once(CONJUNCT2 Cevaluate_cases)]>>
      rw[Once(CONJUNCT2 Cevaluate_cases)]>>
      fsrw_tac[DNF_ss][] >>
      qspecl_then[`menv`,`cenv`,`s`,`env`,`e1`,`(s',Rval v1)`]mp_tac(CONJUNCT1 evaluate_closed) >>
      simp[] >> strip_tac >>
      qspecl_then[`menv`,`cenv`,`s'`,`env`,`e2`,`(s3,Rval v2)`]mp_tac(CONJUNCT1 evaluate_closed) >>
      simp[] >> strip_tac >>
      Q.ISPECL_THEN[`menv`,`s3`,`s''`,`env`,`Opapp`,`v1`,`v2`,`env'`,`exp''`]mp_tac do_app_closed >>
      simp[] >> strip_tac >>
      fs[] >>
      `closed_under_cenv cenv menv env s' ∧ closed_under_cenv cenv menv env' s''` by (
        qspecl_then[`menv`,`cenv`,`s`,`env`,`e1`,`(s',Rval v1)`]mp_tac(CONJUNCT1 evaluate_all_cns) >>
        qspecl_then[`menv`,`cenv`,`s`,`env`,`e1`,`(s',Rval v1)`]mp_tac(evaluate_closed_under_cenv) >>
        qspecl_then[`menv`,`cenv`,`s'`,`env`,`e2`,`(s3,Rval v2)`]mp_tac(CONJUNCT1 evaluate_all_cns) >>
        qspecl_then[`menv`,`cenv`,`s'`,`env`,`e2`,`(s3,Rval v2)`]mp_tac(evaluate_closed_under_cenv) >>
        rpt(first_x_assum(qspec_then`cm`kall_tac)) >>
        simp[] >>
        fs[do_app_Opapp_SOME] >> rw[] >>fs[] >- (
          fsrw_tac[DNF_ss][closed_under_cenv_def,bind_def] >> rw[] >>
          rfs[] >> fsrw_tac[DNF_ss][SUBSET_DEF] >> metis_tac[] ) >>
        fsrw_tac[DNF_ss][closed_under_cenv_def,bind_def] >>
        simp[build_rec_env_MAP,MEM_MAP] >>
        fsrw_tac[DNF_ss][UNCURRY,is_null_def] >>
        rfs[] >> fsrw_tac[DNF_ss][SUBSET_DEF,MEM_FLAT,MEM_MAP] >>
        metis_tac[] ) >> fs[] >>
      rpt (first_x_assum (qspec_then `cm` mp_tac)) >>
      srw_tac[DNF_ss][EXISTS_PROD] >>
      qmatch_assum_rename_tac `syneq(v_to_Cv cm v1) w1`[] >>
      qmatch_assum_rename_tac `syneq(v_to_Cv cm v2) w2`[] >>
      qmatch_assum_abbrev_tac`Cevaluate sa enva e1a (sd,Rval w1)`>>
      pop_assum kall_tac >>
      qmatch_assum_abbrev_tac`Cevaluate sb enva e2a (se,Rval w2)`>>
      pop_assum kall_tac >>
      qmatch_assum_abbrev_tac`EVERY2 (syneq) sc se` >>
      qspecl_then[`sb`,`enva`,`e2a`,`(se,Rval w2)`]mp_tac(CONJUNCT1 Cevaluate_syneq) >> simp[] >>
      disch_then(qspecl_then[`$=`,`sd`,`enva`,`e2a`]mp_tac) >>
      simp[syneq_exp_refl,EXISTS_PROD] >>
      fsrw_tac[DNF_ss][] >>
      map_every qx_gen_tac[`sf`,`w3`] >> strip_tac >>
      CONV_TAC (RESORT_EXISTS_CONV List.rev) >>
      map_every qexists_tac[`w3`,`sf`] >>
      `∃env1 defs n. w1 = CRecClos env1 defs n` by (
        imp_res_tac do_Opapp_SOME_CRecClos >> rw[] ) >>
      CONV_TAC (RESORT_EXISTS_CONV (fn ls => List.drop(ls,2)@List.take(ls,2))) >>
      map_every qexists_tac[`n`,`defs`,`env1`,`sd`] >>
      rw[] >>
      `set (free_vars e1a) ⊆ count (LENGTH enva)` by (
        qmatch_assum_abbrev_tac`Abbrev(e1a = exp_to_Cexp m' e1)` >>
        Q.ISPECL_THEN[`m'`,`e1`]mp_tac free_vars_exp_to_Cexp >>
        simp[Abbr`m'`,Abbr`enva`,env_to_Cenv_MAP] >>
        fsrw_tac[DNF_ss][SUBSET_DEF,MEM_FLAT,is_null_def,MEM_MAP] >> rfs[] >>
        rw[] >> first_x_assum (match_mp_tac o MP_CANON) >> rw[] >>
        res_tac >> fs[] >> metis_tac[]) >>
      `EVERY (Cclosed) sa` by (
        simp[Abbr`sa`,EVERY_MAP] >>
        fs[is_null_def,EVERY_MEM] >> PROVE_TAC[v_to_Cv_closed]) >>
      `EVERY (Cclosed) enva` by (
        simp[Abbr`enva`,env_to_Cenv_MAP,EVERY_MAP] >>
        fs[EVERY_MEM,MEM_MAP,FORALL_PROD,EXISTS_PROD] >>
        metis_tac[v_to_Cv_closed,is_null_def] ) >>
      qspecl_then[`sa`,`enva`,`e1a`,`sd,Rval (CRecClos env1 defs n)`]mp_tac(CONJUNCT1 Cevaluate_closed)>>
      simp[] >>
      simp[Q.SPECL[`CRecClos env1 defs n`]Cclosed_cases] >>
      `no_labs e1a` by rw[Abbr`e1a`] >> simp[] >>
      strip_tac >>
      `∃b. EL n defs = (NONE,1,b)` by (
        qspecl_then[`sa`,`enva`,`e1a`,`(sd,Rval (CRecClos env1 defs n))`]mp_tac(CONJUNCT1 Cevaluate_no_vlabs) >>
        simp[] >>
        simp_tac(srw_ss()++DNF_ss)[EVERY_MAP,Abbr`enva`,env_to_Cenv_MAP,Abbr`sa`] >>
        strip_tac >>
        qabbrev_tac`p = EL n defs` >> PairCases_on`p` >>
        `MEM (p0,p1,p2) defs` by metis_tac[MEM_EL] >> res_tac >> fs[] >>
        fs[do_app_Opapp_SOME] >> rw[] >- (
          fs[v_to_Cv_def,LET_THM] >>
          fs[Q.SPECL[`CRecClos env1 defs zz`]syneq_cases] >>
          rator_x_assum`syneq_defs`mp_tac >>
          simp[Once syneq_exp_cases,env_to_Cenv_MAP] >>
          disch_then(qspecl_then[`0`,`n`]mp_tac) >>
          simp[] >>
          simp[syneq_cb_aux_def]  ) >>
        fs[v_to_Cv_def,LET_THM] >>
        fs[Q.SPECL[`CRecClos env1 defs zz`]syneq_cases] >>
        rator_x_assum`syneq_defs`mp_tac >>
        simp[Once syneq_exp_cases,env_to_Cenv_MAP,defs_to_Cdefs_MAP] >>
        qmatch_assum_abbrev_tac`V' a n` >>
        disch_then(qspecl_then[`a`,`n`]mp_tac) >>
        `(λx. x < LENGTH funs) a` by (
          qunabbrev_tac`a` >>
          match_mp_tac the_find_index_suff >>
          simp[MEM_MAP,EXISTS_PROD] >>
          imp_res_tac ALOOKUP_MEM >>
          PROVE_TAC[] ) >>
        fs[] >>
        simp[EL_MAP,syneq_cb_aux_def,UNCURRY] ) >>
      simp[] >>
      fs[do_app_Opapp_SOME] >- (
        rw[] >> fs[v_to_Cv_def,LET_THM] >>
        fs[Q.SPECL[`c`,`CRecClos env1 defs zz`]syneq_cases] >>
        rator_x_assum`syneq_defs`mp_tac >>
        Q.PAT_ABBREV_TAC`env0 = env_to_Cenv cm Z` >>
        Q.PAT_ABBREV_TAC`defs0 = [X]:def list` >>
        qabbrev_tac`cl = CRecClos env0 defs0 0` >>
        simp[Once syneq_exp_cases]>>
        simp[] >> strip_tac >>
        first_assum(qspecl_then[`0`,`n`]mp_tac) >>
        simp_tac(srw_ss())[Abbr`defs0`] >>
        simp[syneq_cb_aux_def] >>
        strip_tac >>
        fs[bind_def] >>
        qmatch_assum_abbrev_tac`Cevaluate sc envc expc resc` >>
        qspecl_then[`sc`,`envc`,`expc`,`resc`]mp_tac(CONJUNCT1 Cevaluate_syneq) >>
        simp[] >>
        Q.PAT_ABBREV_TAC`envf = w3::ls` >>
        qmatch_assum_abbrev_tac`syneq_exp z1 z2 U (shift 1 1 expc) x1`>>
        fs[env_to_Cenv_MAP] >>
        qunabbrev_tac`envc` >>
        Q.PAT_ABBREV_TAC`envc:Cv list = MAP f env''` >>
        disch_then(qspecl_then[`λv1 v2. if v1 < 1 then (v2 = v1) else v2 = v1 + 1`,`sf`,`w2::cl::envc`,`shift 1 1 expc`]mp_tac) >>
        qmatch_abbrev_tac`(P ⇒ Q) ⇒ R` >>
        `P` by (
          map_every qunabbrev_tac[`P`,`Q`,`R`] >>
          simp[] >>
          conj_tac >- (
            simp[shift_def] >>
            match_mp_tac mkshift_thm >>
            simp[Abbr`envc`,Abbr`expc`,env_to_Cenv_MAP,ADD1,Abbr`z1`,Abbr`env0`] >>
            match_mp_tac free_vars_exp_to_Cexp_matchable >>
            simp[ADD1] >>
            fsrw_tac[DNF_ss][SUBSET_DEF,MEM_MAP,MEM_FLAT] >>
            rw[] >> res_tac >> fs[] >> metis_tac[]) >>
          conj_tac >- (
            lrw[ADD1,Abbr`envc`,env_to_Cenv_MAP,EL_CONS,PRE_SUB1] ) >>
          metis_tac[EVERY2_syneq_trans] ) >>
        simp[] >>
        map_every qunabbrev_tac[`P`,`Q`,`R`] >>
        pop_assum kall_tac >>
        disch_then(Q.X_CHOOSE_THEN`resd`strip_assume_tac) >>
        qspecl_then[`sf`,`w2::cl::envc`,`shift 1 1 expc`,`resd`]mp_tac(CONJUNCT1 Cevaluate_syneq) >>
        simp[] >>
        disch_then(qspecl_then[`U`,`sf`,`envf`,`x1`]mp_tac) >>
        qmatch_abbrev_tac`(P ⇒ Q) ⇒ R` >>
        `P` by (
          map_every qunabbrev_tac[`P`,`Q`,`R`] >>
          simp[] >>
          unabbrev_all_tac >>
          fsrw_tac[ARITH_ss][ADD1,env_to_Cenv_MAP] >>
          simp[syneq_cb_V_def] >>
          lrw[EL_CONS] >> lrw[EL_CONS,PRE_SUB1] >- (
            `v1 = 1` by DECIDE_TAC >>
            lrw[EL_APPEND1,EL_REVERSE,PRE_SUB1] >>
            simp[Once syneq_cases] >>
            map_every qexists_tac[`V`,`V'`] >>
            simp[] >> conj_tac >- metis_tac[] >>
            qmatch_assum_rename_tac`nd < LENGTH defs + 1`[] >>
            `nd - 1 + 1 = nd` by fsrw_tac[ARITH_ss][] >> fs[] >>
            pop_assum kall_tac >>
            simp[Once syneq_exp_cases] >>
            metis_tac[] ) >>
          lrw[EL_APPEND2] ) >>
        simp[] >>
        map_every qunabbrev_tac[`P`,`Q`,`R`] >>
        pop_assum kall_tac >>
        simp[EXISTS_PROD] >>
        qunabbrev_tac`resc`>>fs[]>>
        metis_tac[EVERY2_syneq_trans,result_rel_syneq_trans] ) >>
      rw[] >> fs[v_to_Cv_def,LET_THM,defs_to_Cdefs_MAP] >> rw[] >>
      reverse(fs[Q.SPECL[`c`,`CRecClos env1 defs zz`]syneq_cases]) >- (
        qpat_assum`LENGTH funs ≤ X`mp_tac >>
        imp_res_tac ALOOKUP_MEM >>
        qmatch_assum_rename_tac`MEM (a,z) funs`[] >>
        Q.PAT_ABBREV_TAC`ffuns:string list = MAP x funs` >>
        `MEM a ffuns` by (
          rw[Abbr`ffuns`,MEM_MAP,EXISTS_PROD] >>
          PairCases_on`z` >> metis_tac[] ) >>
        Q.ISPECL_THEN[`ffuns`,`a`,`0:num`]mp_tac find_index_MEM >>
        asm_simp_tac std_ss [] >>
        BasicProvers.VAR_EQ_TAC >>
        disch_then(Q.X_CHOOSE_THEN`i`strip_assume_tac) >>
        asm_simp_tac std_ss [] >>
        `LENGTH funs = LENGTH ffuns` by rw[Abbr`ffuns`] >>
        fs[] >> strip_tac >>
        qsuff_tac`F`>-rw[] >> pop_assum mp_tac >>
        simp[] ) >>
      qmatch_assum_abbrev_tac`V' m0 n` >>
      qmatch_assum_rename_tac`ALOOKUP funs fn = SOME (m,expc)`[] >>
      `ALL_DISTINCT (MAP FST funs)` by (
        fs[Once closed_cases] ) >>
      `EL m0 funs = (fn,m,expc)` by (
        Q.ISPEC_THEN`(MAP FST funs)`mp_tac find_index_ALL_DISTINCT_EL_eq >>
        simp[ALL_DISTINCT_REVERSE] >>
        disch_then(qspecl_then[`fn`,`0`]mp_tac) >>
        simp[] >> strip_tac >>
        qunabbrev_tac`m0` >>
        Q.PAT_ABBREV_TAC`ffuns:string list = MAP x funs` >>
        `ffuns = MAP FST funs` by (
          lrw[Abbr`ffuns`,LIST_EQ_REWRITE,EL_MAP] >>
          Cases_on`EL x funs`>>rw[] ) >>
        simp[] >>
        imp_res_tac ALOOKUP_MEM >>
        pop_assum mp_tac >>
        simp[MEM_EL] >>
        disch_then(Q.X_CHOOSE_THEN`i`strip_assume_tac) >>
        pop_assum (assume_tac o SYM) >>
        first_x_assum(qspec_then`i`mp_tac) >>
        simp[EL_MAP]) >>
      fs[]>>rw[] >>
      rator_assum`syneq_defs`mp_tac >>
      Q.PAT_ABBREV_TAC`env0 = env_to_Cenv cm Z` >>
      Q.PAT_ABBREV_TAC`defs0:def list = MAP f funs` >>
      simp_tac (srw_ss()) [Once syneq_exp_cases] >>
      simp[] >>
      simp[Abbr`defs0`,EVERY_MAP,EVERY_REVERSE,UNCURRY] >>
      strip_tac >>
      first_assum(qspecl_then[`m0`,`n`]mp_tac) >>
      qpat_assum`m0 < LENGTH funs`mp_tac >>
      qpat_assum`V' m0 n`mp_tac >>
      simp_tac(srw_ss())[] >>
      ntac 3 strip_tac >>
      rfs[EL_MAP,GSYM MAP_REVERSE] >>
      fs[syneq_cb_aux_def,bind_def] >>
      rpt BasicProvers.VAR_EQ_TAC >>
      rfs[] >>
      rator_x_assum`syneq_exp`mp_tac >>
      Q.PAT_ABBREV_TAC`ffuns:string list = MAP X funs` >>
      `ffuns = MAP FST funs` by (
        lrw[Abbr`ffuns`,LIST_EQ_REWRITE,EL_MAP] >>
        Cases_on`EL x funs`>>rw[] ) >>
      fs[] >> ntac 2 (pop_assum kall_tac) >>
      qmatch_assum_abbrev_tac`Cevaluate sc envc Cexp resc` >>
      strip_tac >>
      qspecl_then[`sc`,`envc`,`Cexp`,`resc`]mp_tac(CONJUNCT1 Cevaluate_syneq) >>
      simp[] >>
      Q.PAT_ABBREV_TAC`envf = w3::ls` >>
      qmatch_assum_abbrev_tac`syneq_exp z1 z2 U Cexp ef`>>
      fs[env_to_Cenv_MAP] >>
      qunabbrev_tac`envc` >>
      fs[build_rec_env_MAP,MAP_MAP_o,combinTheory.o_DEF,UNCURRY] >>
      disch_then(qspecl_then[`U`,`sf`,`envf`,`ef`]mp_tac) >>
      qmatch_abbrev_tac`(P ⇒ Q) ⇒ R` >>
      `P` by (
        map_every qunabbrev_tac[`P`,`Q`,`R`] >>
        simp[] >>
        conj_tac >- (
          qmatch_abbrev_tac`syneq_exp z3 z4 U Cexp ef` >>
          qsuff_tac`(z3 = z1) ∧ (z4 = z2)`>-rw[] >>
          map_every qunabbrev_tac[`z1`,`z2`,`z3`,`z4`] >>
          simp[ADD1,Abbr`envf`,Abbr`env0`] ) >>
        conj_tac >- (
          lrw[ADD1,Abbr`envf`,Abbr`U`,syneq_cb_V_def] >- (
            rw[] >> metis_tac[syneq_trans] )
          >- (
            fs[Abbr`env0`] >>
            lrw[EL_CONS,PRE_SUB1,EL_APPEND1,EL_REVERSE,EL_MAP,v_to_Cv_def,env_to_Cenv_MAP] >>
            rw[Once syneq_cases] >>
            map_every qexists_tac[`V`,`V'`] >>
            conj_tac >- metis_tac[] >>
            Q.PAT_ABBREV_TAC`ffuns:string list = MAP X funs` >>
            `ffuns = MAP FST funs` by (
              lrw[Abbr`ffuns`,LIST_EQ_REWRITE,EL_MAP] >>
              Cases_on`EL x funs`>>rw[] ) >>
            fs[] >> ntac 2 (pop_assum kall_tac) >>
            simp[defs_to_Cdefs_MAP] >>
            fs[MAP_REVERSE] >>
            pop_assum mp_tac >> simp[] >> strip_tac >>
            qmatch_abbrev_tac`a < LENGTH funs ∧ X` >>
            qsuff_tac`a = v1-1`>-simp[] >>
            qunabbrev_tac`a` >>
            Q.ISPEC_THEN`(MAP FST funs)`mp_tac find_index_ALL_DISTINCT_EL_eq >>
            simp[ALL_DISTINCT_REVERSE] >>
            disch_then(qspecl_then[`FST (EL (v1-1) funs)`,`0`]mp_tac) >> simp[] >>
            disch_then(qspec_then`v1-1`mp_tac) >>
            simp[EL_REVERSE,PRE_SUB1,EL_MAP] )
          >- (
            res_tac >>
            pop_assum mp_tac >>
            qpat_assum`∀v1 v2. V v1 v2 ⇒ P`kall_tac >>
            simp[Abbr`env0`] >>
            simp[EL_CONS,PRE_SUB1,EL_MAP,EL_REVERSE,LENGTH_GENLIST,EL_APPEND2] )
          >- (
            fsrw_tac[ARITH_ss][Abbr`z1`,Abbr`z2`] )) >>
        metis_tac[EVERY2_syneq_trans] ) >>
      simp[] >>
      map_every qunabbrev_tac[`P`,`Q`,`R`] >>
      pop_assum kall_tac >>
      simp[EXISTS_PROD] >>
      qunabbrev_tac`resc`>>fs[]>>
      metis_tac[EVERY2_syneq_trans,result_rel_syneq_trans] )
    >- (
      rw[Once Cevaluate_cases] >>
      fsrw_tac[DNF_ss][] >>
      disj1_tac >>
      rw[Once(CONJUNCT2 Cevaluate_cases)] >>
      rw[Once(CONJUNCT2 Cevaluate_cases)] >>
      rw[Once(CONJUNCT2 Cevaluate_cases)] >>
      fsrw_tac[DNF_ss][] >>
      fs[do_app_def] >>
      Cases_on`v1`>>fs[] >>
      Cases_on`store_assign n v2 s3`>>fs[] >>
      rw[] >>
      qspecl_then[`menv`,`cenv`,`s`,`env`,`e1`,`(s',Rval (Loc n))`]mp_tac(CONJUNCT1 evaluate_closed) >>
      simp[]>>strip_tac >> fs[] >>
      fs[store_assign_def] >> rw[] >> fs[] >> rw[] >>
      qspecl_then[`menv`,`cenv`,`s'`,`env`,`e2`,`(s3,Rval v2)`]mp_tac(CONJUNCT1 evaluate_closed) >>
      simp[]>>strip_tac >>
      `EVERY (closed menv) (LUPDATE v2 n s3)` by (
        fs[EVERY_MEM] >>
        metis_tac[MEM_LUPDATE] ) >>
      fs[] >>
      `closed_under_cenv cenv menv env s' ∧ closed_under_cenv cenv menv env (LUPDATE v2 n s3)` by (
        qspecl_then[`menv`,`cenv`,`s`,`env`,`e1`,`(s',Rval (Loc n))`]mp_tac(evaluate_closed_under_cenv) >>
        qspecl_then[`menv`,`cenv`,`s'`,`env`,`e2`,`(s3,Rval v2)`]mp_tac(evaluate_closed_under_cenv) >>
        simp[] >> rw[] >>
        fsrw_tac[DNF_ss][closed_under_cenv_def] >>
        rw[] >>
        imp_res_tac MEM_LUPDATE >> fs[] >>
        qspecl_then[`menv`,`cenv`,`s'`,`env`,`e2`,`(s3,Rval v2)`]mp_tac(CONJUNCT1 evaluate_all_cns) >>
        simp[] >> disch_then match_mp_tac >>
        fsrw_tac[DNF_ss][] ) >> fs[] >>
      rpt (first_x_assum (qspec_then`cm`mp_tac)) >>
      fsrw_tac[DNF_ss][EXISTS_PROD] >> rw[] >>
      fs[v_to_Cv_def,exp_to_Cexp_def] >>
      rw[] >> fs[] >> rw[] >>
      CONV_TAC SWAP_EXISTS_CONV >> qexists_tac`CLoc n` >> rw[] >>
      qmatch_assum_abbrev_tac`Cevaluate sa enva e1a (sd,Rval (CLoc n))` >>
      pop_assum kall_tac >>
      qmatch_assum_abbrev_tac`Cevaluate sb enva e2a (se,w1)` >>
      qpat_assum`Abbrev (se  = X)`kall_tac >>
      qspecl_then[`sb`,`enva`,`e2a`,`(se,w1)`]mp_tac(CONJUNCT1 Cevaluate_syneq) >> simp[] >>
      disch_then(qspecl_then[`$=`,`sd`,`enva`,`e2a`]mp_tac) >> simp[syneq_exp_refl] >>
      fsrw_tac[DNF_ss][FORALL_PROD] >>
      map_every qx_gen_tac[`sf`,`w2`] >>
      strip_tac >>
      fs[Abbr`w1`] >> rw[] >>
      qmatch_assum_rename_tac`syneq w1 w2`[] >>
      map_every qexists_tac[`sf`,`w2`,`sd`] >>
      simp[] >>
      fs[EVERY2_EVERY] >>
      fs[EVERY_MEM,FORALL_PROD] >>
      rpt(qpat_assum`LENGTH X = Y`mp_tac) >> ntac 3 strip_tac >>
      fs[MEM_ZIP] >> fsrw_tac[DNF_ss][] >>
      gen_tac >> strip_tac >>
      simp[EL_LUPDATE,EL_MAP] >>
      rw[] >>
      metis_tac[syneq_trans,EL_MAP])) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    ntac 3 gen_tac >>
    Cases >> fs[exp_to_Cexp_def] >>
    qx_gen_tac `e1` >>
    qx_gen_tac `e2` >>
    rw[LET_THM] >- (
      rw[Once Cevaluate_cases] >>
      fsrw_tac[DNF_ss][EXISTS_PROD] >>
      disj2_tac >>
      rw[Once(CONJUNCT2 Cevaluate_cases)] >>
      rw[Once(CONJUNCT2 Cevaluate_cases)] >>
      rw[Once(CONJUNCT2 Cevaluate_cases)] >>
      fsrw_tac[DNF_ss][] >>
      qspecl_then[`menv`,`cenv`,`s`,`env`,`e1`,`(s',Rval v1)`]mp_tac(CONJUNCT1 evaluate_closed) >>
      qspecl_then[`menv`,`cenv`,`s`,`env`,`e1`,`(s',Rval v1)`]mp_tac(evaluate_closed_under_cenv) >>
      simp[] >> strip_tac >> fs[] >> strip_tac >> fs[] >>
      rpt (first_x_assum (qspec_then `cm` mp_tac)) >>
      rw[] >>
      disj2_tac >>
      qmatch_assum_rename_tac `syneq (v_to_Cv m v1) w1`[] >>
      qmatch_assum_abbrev_tac `Cevaluate sb enva e2a (sc,Rerr err)`>>
      pop_assum kall_tac >>
      qmatch_assum_rename_tac `EVERY2 (syneq) sb sd`[] >>
      qspecl_then[`sb`,`sd`,`enva`,`e2a`,`(sc,Rerr err)`]mp_tac Cevaluate_any_syneq_store >>
      simp[] >>
      fsrw_tac[DNF_ss][FORALL_PROD] >>
      qx_gen_tac`se` >> strip_tac >>
      map_every qexists_tac [`se`,`sd`,`w1`] >> fs[] >>
      PROVE_TAC[EVERY2_syneq_trans])
    >- (
      fs[] >>
      qspecl_then[`menv`,`cenv`,`s`,`env`,`e1`,`(s',Rval v1)`]mp_tac(CONJUNCT1 evaluate_closed) >>
      qspecl_then[`menv`,`cenv`,`s`,`env`,`e1`,`(s',Rval v1)`]mp_tac(evaluate_closed_under_cenv) >>
      simp[]>> rpt strip_tac >> fs[] >>
      fsrw_tac[DNF_ss][EXISTS_PROD]>>
      rpt (first_x_assum (qspec_then `cm` mp_tac)) >>
      rw[] >>
      qmatch_assum_rename_tac `syneq (v_to_Cv m v1) w1`[] >>
      qmatch_assum_abbrev_tac `Cevaluate sa enva e1a (sd,Rval w1)` >>
      pop_assum kall_tac >>
      qmatch_assum_abbrev_tac `Cevaluate sb enva e2a (sc,Rerr err)` >>
      pop_assum kall_tac >>
      qspecl_then[`sb`,`sd`,`enva`,`e2a`,`(sc,Rerr err)`]mp_tac Cevaluate_any_syneq_store >>
      fsrw_tac[DNF_ss][EXISTS_PROD] >>
      qx_gen_tac`se`>>strip_tac >>
      `EVERY2 (syneq) (MAP (v_to_Cv m) s3) se` by PROVE_TAC[EVERY2_syneq_trans] >>
      BasicProvers.EVERY_CASE_TAC >>
      rw[Once Cevaluate_cases] >>
      fsrw_tac[DNF_ss][]
      >- (
        disj2_tac >>
        rw[Once(CONJUNCT2(Cevaluate_cases))] >>
        rw[Once(CONJUNCT2(Cevaluate_cases))] >>
        rw[Once(CONJUNCT2(Cevaluate_cases))] >>
        srw_tac[DNF_ss][] >>
        disj2_tac >>
        metis_tac[])
      >- (
        disj1_tac >>
        CONV_TAC (RESORT_EXISTS_CONV List.rev) >>
        map_every qexists_tac[`w1`,`sd`] >> fs[] >>
        rw[Once Cevaluate_cases] >>
        srw_tac[DNF_ss][] >>
        disj2_tac >>
        qspecl_then[`sb`,`enva`,`e2a`,`sc,Rerr err`]mp_tac(CONJUNCT1 Cevaluate_syneq) >> simp[] >>
        disch_then(qspecl_then[`λv1 v2. v2 = v1 + 1`,`sd`,`w1::enva`,`shift 1 0 e2a`]mp_tac) >>
        simp[EXISTS_PROD] >>
        discharge_hyps >- (
          conj_tac >- (
            simp[shift_def] >>
            match_mp_tac mkshift_thm >>
            simp[ADD1,Abbr`e2a`,Abbr`enva`,env_to_Cenv_MAP] >>
            match_mp_tac free_vars_exp_to_Cexp_matchable >>
            simp[] >>
            fsrw_tac[DNF_ss][SUBSET_DEF,MEM_MAP,MEM_FLAT,is_null_def] >>
            rw[] >> rfs[] >> res_tac >> fs[] >> metis_tac[]) >>
          simp[ADD1,Abbr`enva`,env_to_Cenv_MAP,EL_CONS,PRE_SUB1] ) >>
        PROVE_TAC[EVERY2_syneq_trans])
      >- (
        disj2_tac >>
        rw[Once(CONJUNCT2(Cevaluate_cases))] >>
        rw[Once(CONJUNCT2(Cevaluate_cases))] >>
        rw[Once(CONJUNCT2(Cevaluate_cases))] >>
        rw[Once Cevaluate_cases] >>
        srw_tac[DNF_ss][] >>
        disj2_tac >>
        rw[Once(CONJUNCT2(Cevaluate_cases))] >>
        rw[Once(CONJUNCT2(Cevaluate_cases))] >>
        rw[Once(CONJUNCT2(Cevaluate_cases))] >>
        srw_tac[DNF_ss][] >>
        disj2_tac >>
        PROVE_TAC[] )
      >- (
        disj1_tac >>
        CONV_TAC (RESORT_EXISTS_CONV List.rev) >>
        map_every qexists_tac[`w1`,`sd`] >> fs[] >>
        rw[Once Cevaluate_cases] >>
        srw_tac[DNF_ss][] >>
        disj2_tac >>
        qspecl_then[`sb`,`enva`,`e2a`,`sc,Rerr err`]mp_tac(CONJUNCT1 Cevaluate_syneq) >> simp[] >>
        disch_then(qspecl_then[`λv1 v2. v2 = v1 + 1`,`sd`,`w1::enva`,`shift 1 0 e2a`]mp_tac) >>
        simp[EXISTS_PROD] >>
        discharge_hyps >- (
          conj_tac >- (
            simp[shift_def] >>
            match_mp_tac mkshift_thm >>
            simp[ADD1,Abbr`e2a`,Abbr`enva`,env_to_Cenv_MAP] >>
            match_mp_tac free_vars_exp_to_Cexp_matchable >>
            simp[]>>
            fsrw_tac[DNF_ss][SUBSET_DEF,MEM_MAP,MEM_FLAT,is_null_def] >>
            rw[] >> rfs[] >> res_tac >> fs[] >> metis_tac[]) >>
          simp[ADD1,Abbr`enva`,env_to_Cenv_MAP,EL_CONS,PRE_SUB1] ) >>
        PROVE_TAC[EVERY2_syneq_trans]))
    >- (
      rw[Once Cevaluate_cases] >>
      fsrw_tac[DNF_ss][EXISTS_PROD] >>
      disj2_tac >>
      rw[Once(CONJUNCT2 Cevaluate_cases)] >>
      rw[Once(CONJUNCT2 Cevaluate_cases)] >>
      rw[Once(CONJUNCT2 Cevaluate_cases)] >>
      srw_tac[DNF_ss][]>>
      disj2_tac >>
      qspecl_then[`menv`,`cenv`,`s`,`env`,`e1`,`(s',Rval v1)`]mp_tac(CONJUNCT1 evaluate_closed) >>
      qspecl_then[`menv`,`cenv`,`s`,`env`,`e1`,`(s',Rval v1)`]mp_tac(evaluate_closed_under_cenv) >>
      simp[]>>rpt strip_tac>>fs[]>>
      rpt (first_x_assum (qspec_then `cm` mp_tac)) >> rw[] >>
      qmatch_assum_rename_tac `syneq (v_to_Cv m v1) w1`[] >>
      qmatch_assum_abbrev_tac `Cevaluate sa enva e1a (sd,Rval w1)` >>
      pop_assum kall_tac >>
      qmatch_assum_abbrev_tac `Cevaluate sb enva e2a (sc,Rerr err)` >>
      pop_assum kall_tac >>
      qspecl_then[`sb`,`sd`,`enva`,`e2a`,`(sc,Rerr err)`]mp_tac Cevaluate_any_syneq_store >>
      fsrw_tac[DNF_ss][EXISTS_PROD] >>
      PROVE_TAC[EVERY2_syneq_trans] )
    >- (
      rw[Once Cevaluate_cases] >>
      fsrw_tac[DNF_ss][] >>
      disj2_tac >> disj1_tac >>
      fsrw_tac[DNF_ss][EXISTS_PROD] >>
      rw[Once(CONJUNCT2 Cevaluate_cases)] >>
      rw[Once(CONJUNCT2 Cevaluate_cases)] >>
      qspecl_then[`menv`,`cenv`,`s`,`env`,`e1`,`(s',Rval v1)`]mp_tac(CONJUNCT1 evaluate_closed) >>
      qspecl_then[`menv`,`cenv`,`s`,`env`,`e1`,`(s',Rval v1)`]mp_tac(evaluate_closed_under_cenv) >>
      simp[]>>rpt strip_tac>>fs[]>>
      rpt (first_x_assum (qspec_then `cm` mp_tac)) >> rw[] >>
      qmatch_assum_rename_tac `syneq (v_to_Cv m v1) w1`[] >>
      qmatch_assum_abbrev_tac `Cevaluate sa enva e1a (sd,Rval w1)` >>
      pop_assum kall_tac >>
      qmatch_assum_abbrev_tac `Cevaluate sb enva e2a (sc,Rerr err)` >>
      pop_assum kall_tac >>
      qspecl_then[`sb`,`sd`,`enva`,`e2a`,`(sc,Rerr err)`]mp_tac Cevaluate_any_syneq_store >>
      fsrw_tac[DNF_ss][EXISTS_PROD] >>
      PROVE_TAC[EVERY2_syneq_trans])
    >- (
      rw[Once Cevaluate_cases] >>
      fsrw_tac[DNF_ss][EXISTS_PROD] >>
      disj2_tac >>
      rw[Once(CONJUNCT2 Cevaluate_cases)] >>
      rw[Once(CONJUNCT2 Cevaluate_cases)] >>
      rw[Once(CONJUNCT2 Cevaluate_cases)] >>
      srw_tac[DNF_ss][] >>
      disj2_tac >>
      qspecl_then[`menv`,`cenv`,`s`,`env`,`e1`,`(s',Rval v1)`]mp_tac(CONJUNCT1 evaluate_closed) >>
      qspecl_then[`menv`,`cenv`,`s`,`env`,`e1`,`(s',Rval v1)`]mp_tac(evaluate_closed_under_cenv) >>
      simp[]>>rpt strip_tac>>fs[]>>
      rpt (first_x_assum (qspec_then `cm` mp_tac)) >> rw[] >>
      qmatch_assum_rename_tac `syneq (v_to_Cv m v1) w1`[] >>
      qmatch_assum_abbrev_tac `Cevaluate sa enva e1a (sd,Rval w1)` >>
      pop_assum kall_tac >>
      qmatch_assum_abbrev_tac `Cevaluate sb enva e2a (sc,Rerr err)` >>
      pop_assum kall_tac >>
      qspecl_then[`sb`,`sd`,`enva`,`e2a`,`(sc,Rerr err)`]mp_tac Cevaluate_any_syneq_store >>
      fsrw_tac[DNF_ss][EXISTS_PROD] >>
      PROVE_TAC[EVERY2_syneq_trans])) >>
  strip_tac >- (
    ntac 3 gen_tac >>
    Cases >> fs[exp_to_Cexp_def] >>
    qx_gen_tac `e1` >>
    qx_gen_tac `e2` >>
    rw[LET_THM] >- (
      rw[Once Cevaluate_cases] >>
      fsrw_tac[DNF_ss][EXISTS_PROD] >>
      disj2_tac >>
      rw[Once(CONJUNCT2 Cevaluate_cases)] >>
      rw[Once(CONJUNCT2 Cevaluate_cases)] >>
      rw[Once(CONJUNCT2 Cevaluate_cases)] >>
      fsrw_tac[DNF_ss][])
    >- (
      BasicProvers.EVERY_CASE_TAC >>
      rw[Once Cevaluate_cases] >>
      fsrw_tac[DNF_ss][EXISTS_PROD] >>
      rw[Once(CONJUNCT2 Cevaluate_cases)] >>
      rw[Once(CONJUNCT2 Cevaluate_cases)] >>
      rw[Once(CONJUNCT2 Cevaluate_cases)] >>
      fsrw_tac[DNF_ss][] >>
      disj2_tac >- (
        rw[Once(CONJUNCT2 Cevaluate_cases)] >>
        fsrw_tac[DNF_ss][] ) >>
      rw[Once Cevaluate_cases] >>
      fsrw_tac[DNF_ss][] >>
      disj1_tac >>
      rw[Once Cevaluate_cases] >>
      fsrw_tac[DNF_ss][] >>
      disj2_tac >>
      rw[Once(CONJUNCT2 Cevaluate_cases)] >>
      rw[Once(CONJUNCT2 Cevaluate_cases)] >>
      rw[Once(CONJUNCT2 Cevaluate_cases)] >>
      fsrw_tac[DNF_ss][])
    >- (
      rw[Once Cevaluate_cases] >>
      fsrw_tac[DNF_ss][EXISTS_PROD] >>
      disj2_tac >>
      rw[Once(CONJUNCT2 Cevaluate_cases)] >>
      rw[Once(CONJUNCT2 Cevaluate_cases)] >>
      rw[Once(CONJUNCT2 Cevaluate_cases)] >>
      fsrw_tac[DNF_ss][])
    >- (
      rw[Once Cevaluate_cases] >>
      fsrw_tac[DNF_ss][EXISTS_PROD])
    >- (
      rw[Once Cevaluate_cases] >>
      fsrw_tac[DNF_ss][EXISTS_PROD] >>
      disj2_tac >>
      rw[Once(CONJUNCT2 Cevaluate_cases)] >>
      rw[Once(CONJUNCT2 Cevaluate_cases)] >>
      rw[Once(CONJUNCT2 Cevaluate_cases)] >>
      fsrw_tac[DNF_ss][]) ) >>
  strip_tac >- (
    rw[exp_to_Cexp_def,LET_THM] >>
    fsrw_tac[DNF_ss][EXISTS_PROD] >>
    imp_res_tac do_log_FV >>
    `FV exp' ⊆ set (MAP (Short o FST) env) ∪ menv_dom menv` by PROVE_TAC[SUBSET_TRANS] >>
    qspecl_then[`menv`,`cenv`,`s`,`env`,`exp`,`(s',Rval v)`]mp_tac(CONJUNCT1 evaluate_closed) >>
    qspecl_then[`menv`,`cenv`,`s`,`env`,`exp`,`(s',Rval v)`]mp_tac(evaluate_closed_under_cenv) >>
    simp[]>>rpt strip_tac>>fs[]>>
    rpt (first_x_assum (qspec_then`cm` mp_tac)) >> rw[] >>
    qmatch_assum_rename_tac`syneq (v_to_Cv m v) w`[] >>
    qmatch_assum_abbrev_tac `Cevaluate sa enva e1a (sd,Rval w)` >>
    pop_assum kall_tac >>
    qmatch_assum_abbrev_tac `Cevaluate sb enva e2a (sc,w2)` >>
    ntac 2 (pop_assum kall_tac) >>
    qspecl_then[`sb`,`sd`,`enva`,`e2a`,`(sc,w2)`]mp_tac Cevaluate_any_syneq_store >>
    fsrw_tac[DNF_ss][EXISTS_PROD] >>
    map_every qx_gen_tac[`se`,`w3`] >>strip_tac >>
    Cases_on `op` >> Cases_on `v` >> fs[do_log_def] >>
    Cases_on `l` >> fs[v_to_Cv_def] >>
    rw[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][] >> disj1_tac >>
    CONV_TAC (RESORT_EXISTS_CONV List.rev) >>
    map_every qexists_tac [`b`,`sd`] >> fs[] >>
    rw[] >> fs[] >> rw[] >>
    fs[evaluate_lit] >> rw[v_to_Cv_def] >>
    PROVE_TAC[result_rel_syneq_trans,EVERY2_syneq_trans] ) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rw[exp_to_Cexp_def,LET_THM] >>
    Cases_on `op` >> fsrw_tac[DNF_ss][] >>
    rw[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][EXISTS_PROD]) >>
  strip_tac >- (
    rw[exp_to_Cexp_def,LET_THM] >>
    fsrw_tac[DNF_ss][EXISTS_PROD] >>
    imp_res_tac do_if_FV >>
    `FV exp' ⊆ set (MAP (Short o FST) env) ∪ menv_dom menv` by (
      fsrw_tac[DNF_ss][SUBSET_DEF] >>
      PROVE_TAC[]) >> fs[] >>
    qspecl_then[`menv`,`cenv`,`s`,`env`,`exp`,`(s',Rval v)`]mp_tac(CONJUNCT1 evaluate_closed) >>
    qspecl_then[`menv`,`cenv`,`s`,`env`,`exp`,`(s',Rval v)`]mp_tac(evaluate_closed_under_cenv) >>
    simp[]>>rpt strip_tac>>fs[]>>
    rw[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][] >>
    disj1_tac >>
    rpt (first_x_assum (qspec_then`cm` mp_tac)) >> rw[] >>
    qmatch_assum_rename_tac`syneq (v_to_Cv m v) w`[] >>
    qmatch_assum_abbrev_tac `Cevaluate sa enva e1a (sd,Rval w)` >>
    pop_assum kall_tac >>
    qmatch_assum_abbrev_tac `Cevaluate sb enva e2a (sc,w2)` >>
    ntac 2 (pop_assum kall_tac) >>
    qspecl_then[`sb`,`sd`,`enva`,`e2a`,`(sc,w2)`]mp_tac Cevaluate_any_syneq_store >>
    fsrw_tac[DNF_ss][EXISTS_PROD] >>
    map_every qx_gen_tac[`se`,`w3`] >>strip_tac >>
    CONV_TAC (RESORT_EXISTS_CONV List.rev) >>
    CONV_TAC SWAP_EXISTS_CONV >> qexists_tac`sd` >>
    CONV_TAC SWAP_EXISTS_CONV >> qexists_tac`w3` >>
    CONV_TAC SWAP_EXISTS_CONV >> qexists_tac`se` >>
    qpat_assum `do_if v e2 e3 = X` mp_tac >>
    fs[do_if_def] >> rw[] >|[
      qexists_tac`T`,
      qexists_tac`F`] >>
    fsrw_tac[DNF_ss][v_to_Cv_def] >>
    PROVE_TAC[EVERY2_syneq_trans,result_rel_syneq_trans]) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rw[exp_to_Cexp_def,LET_THM] >> fs[] >>
    rw[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][EXISTS_PROD]) >>
  strip_tac >- (
    rpt strip_tac >> fs[] >>
    fsrw_tac[DNF_ss][EXISTS_PROD] >>
    first_x_assum (qspec_then `cm` mp_tac) >> rw[] >>
    qmatch_assum_rename_tac `syneq (v_to_Cv m v) w`[] >>
    rw[exp_to_Cexp_def,LET_THM] >>
    rw[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][] >>
    disj1_tac >>
    qmatch_assum_abbrev_tac`Cevaluate sa enva ea (sd,Rval w)` >>
    pop_assum kall_tac >>
    CONV_TAC (RESORT_EXISTS_CONV List.rev) >>
    map_every qexists_tac [`w`,`sd`] >> fs[] >>
    qmatch_assum_abbrev_tac `evaluate_match_with P cenv s2 env v pes res` >>
    Q.ISPECL_THEN [`s2`,`pes`,`res`] mp_tac (Q.GEN`s`evaluate_match_with_matchres) >> fs[] >>
    qmatch_assum_abbrev_tac`Abbrev(ea = exp_to_Cexp mm exp)` >>
    `mm.cnmap = m` by rw[Abbr`mm`] >>
    PairCases_on`res`>>fs[]>>strip_tac>>
    qmatch_assum_abbrev_tac`evaluate_match_with (matchres env) cenv s2 env v pes r` >>
    Q.ISPECL_THEN [`s2`,`pes`,`r`] mp_tac (Q.GEN`s`evaluate_match_with_Cevaluate_match) >>
    fs[Abbr`r`] >>
    disch_then (qspec_then `mm` mp_tac) >>
    rw[] >- (
      qmatch_assum_abbrev_tac `Cevaluate_match sb vv ppes [] NONE` >>
      `Cevaluate_match sb vv (MAP (λ(Cp,pe). (Cp, shift 1 (Cpat_vars (SND (pat_to_Cpat mm (FST pe))))
          (exp_to_Cexp (FST (pat_to_Cpat mm (FST pe))) (SND pe)))) ppes) [] NONE` by (
        metis_tac [Cevaluate_match_MAP_exp, optionTheory.OPTION_MAP_DEF] ) >>
      qmatch_assum_abbrev_tac `Cevaluate_match sb vv (MAP ff ppes) [] NONE` >>
      Q.PAT_ABBREV_TAC`Cpes:((Cpat#Cexp) list) = MAP X (pes_to_Cpes mm pes)` >>
      `MAP ff ppes = Cpes` by (
        unabbrev_all_tac >>
        rw[pes_to_Cpes_MAP,LET_THM] >>
        rw[MAP_MAP_o,combinTheory.o_DEF,pairTheory.LAMBDA_PROD] >>
        rw[pairTheory.UNCURRY] ) >>
      fs[] >>
      map_every qunabbrev_tac[`ppes`,`ff`,`vv`] >>
      pop_assum kall_tac >>
      ntac 3 (pop_assum mp_tac) >> pop_assum kall_tac >> ntac 3 strip_tac >>
      Q.SPECL_THEN [`sb`,`v_to_Cv mm.cnmap v`,`Cpes`,`[]`,`NONE`]
        mp_tac (INST_TYPE[alpha|->``:Cexp``](Q.GENL[`v`,`s`] Cevaluate_match_syneq)) >>
      fs[] >>
      disch_then (qspecl_then [`sd`,`w`] mp_tac) >> fs[] >>
      strip_tac >>
      qspecl_then[`sd`,`w`,`Cpes`,`[]`,`NONE`]mp_tac(Q.GENL[`v`,`s`]Cevaluate_match_remove_mat_var)>>
      fs[] >>
      fsrw_tac[DNF_ss][EXISTS_PROD] >>
      disch_then (qspecl_then[`w::enva`,`0`]mp_tac)>>
      discharge_hyps >- (
        simp[el_check_def,Abbr`Cpes`,pes_to_Cpes_MAP,EVERY_MAP,UNCURRY] >>
        simp[EVERY_MEM,FORALL_PROD] >>
        rpt strip_tac >>
        match_mp_tac IMAGE_SUBSET_gen >>
        Q.PAT_ABBREV_TAC`a = LENGTH ls` >>
        qexists_tac`count (a + LENGTH enva)` >>
        conj_tac >- (
          match_mp_tac free_vars_exp_to_Cexp_matchable >>
          simp[FST_pat_to_Cpat_bvars,Abbr`mm`,Abbr`a`] >>
          conj_tac >- (
            fsrw_tac[DNF_ss][SUBSET_DEF,FORALL_PROD,MEM_FLAT,MEM_MAP,is_null_def,FV_pes_MAP] >>
            rw[] >> rfs[] >> res_tac >> fs[] >> metis_tac[] ) >>
          simp[SUBSET_DEF,ADD1,Abbr`enva`,env_to_Cenv_MAP] ) >>
        simp[SUBSET_DEF] ) >>
      metis_tac[EVERY2_syneq_trans] ) >>
    qmatch_assum_abbrev_tac `Cevaluate_match sb vv ppes eenv (SOME mr)` >>
    Q.ISPECL_THEN[`sb`,`vv`,`ppes`,`eenv`,`SOME mr`]mp_tac
      (INST_TYPE[beta|->``:Cexp``](Q.GENL[`v`,`s`]Cevaluate_match_MAP_exp)) >> simp[] >>
    disch_then(qspec_then`λ(p,e). shift 1 (Cpat_vars (SND (pat_to_Cpat mm p))) (exp_to_Cexp (FST(pat_to_Cpat mm p)) e)`mp_tac) >>
    map_every qunabbrev_tac[`ppes`,`eenv`,`vv`] >>
    pop_assum mp_tac >>
    pop_assum kall_tac >>
    ntac 2 strip_tac >>
    qmatch_assum_abbrev_tac `Cevaluate_match sb vv (MAP ff ppes) eenv mmr` >>
    Q.PAT_ABBREV_TAC`ps:((Cpat#Cexp)list) = MAP X Y` >>
    `MAP ff ppes = ps` by (
      unabbrev_all_tac >>
      rw[pes_to_Cpes_MAP,LET_THM] >>
      rw[MAP_MAP_o,combinTheory.o_DEF,pairTheory.LAMBDA_PROD] >>
      rw[pairTheory.UNCURRY] ) >>
    fs[] >>
    pop_assum kall_tac >>
    qunabbrev_tac `ppes` >>
    Q.ISPECL_THEN[`sb`,`vv`,`ps`,`eenv`,`mmr`]mp_tac(Q.GENL[`v`,`s`]Cevaluate_match_syneq) >>
    simp[] >>
    disch_then(qspecl_then[`sd`,`w`]mp_tac) >>
    simp[] >>
    disch_then(Q.X_CHOOSE_THEN`wenv`strip_assume_tac) >>
    qspecl_then[`sd`,`w`,`ps`,`wenv`,`mmr`]mp_tac(Q.GENL[`v`,`s`]Cevaluate_match_remove_mat_var) >>
    simp[Abbr`mmr`] >>
    disch_then(qspecl_then[`w::enva`,`0`]mp_tac) >>
    discharge_hyps >- (
      simp[el_check_def,Abbr`ps`,pes_to_Cpes_MAP,EVERY_MAP,UNCURRY] >>
      simp[EVERY_MEM,FORALL_PROD] >>
      rpt strip_tac >>
      match_mp_tac IMAGE_SUBSET_gen >>
      Q.PAT_ABBREV_TAC`a = LENGTH ls` >>
      qexists_tac`count (a + LENGTH enva)` >>
      conj_tac >- (
        match_mp_tac free_vars_exp_to_Cexp_matchable >>
        simp[FST_pat_to_Cpat_bvars,Abbr`mm`,Abbr`a`] >>
        conj_tac >- (
          fsrw_tac[DNF_ss][SUBSET_DEF,FORALL_PROD,MEM_MAP,MEM_FLAT,is_null_def,FV_pes_MAP] >>
          rw[] >> rfs[] >> res_tac >> fs[] >>
          metis_tac[] ) >>
        simp[SUBSET_DEF,ADD1,Abbr`enva`,env_to_Cenv_MAP] ) >>
      simp[SUBSET_DEF] ) >>
    qspecl_then[`menv`,`cenv`,`s`,`env`,`exp`,`(s2,Rval v)`]mp_tac(CONJUNCT1 evaluate_closed) >>
    simp[] >> strip_tac >>
    Q.ISPECL_THEN[`s2`,`menv`,`pes`,`(s2,Rval(menv',mr))`]mp_tac(Q.GENL[`envM`,`s`]evaluate_match_with_matchres_closed)>>
    simp[] >> strip_tac >>
    `FV (SND mr) ⊆ set (MAP (Short o FST) (menv' ++ env)) ∪ menv_dom menv` by (
      fsrw_tac[DNF_ss][SUBSET_DEF,FORALL_PROD,MEM_MAP,EXISTS_PROD,is_null_def,MEM_FLAT,FV_pes_MAP] >>
      PairCases_on`mr`>>fs[] >>
      qx_gen_tac`x` >> strip_tac >>
      first_x_assum(qspecl_then[`x`,`mr0`,`mr1`]mp_tac) >>
      simp[] >>
      qpat_assum`X = Y`(mp_tac o SYM) >>
      simp[MEM_MAP,EXISTS_PROD] >>
      METIS_TAC[] ) >>
    `closed_under_cenv cenv menv (menv' ++ env) s2` by (
      Q.ISPECL_THEN[`s2`,`pes`,`(s2,Rval(menv',mr))`]mp_tac(Q.GEN`s`evaluate_match_with_matchres_all_cns)>>
      qspecl_then[`menv`,`cenv`,`s`,`env`,`exp`,`(s2,Rval v)`]mp_tac(CONJUNCT1 evaluate_all_cns) >>
      simp[] >>
      fs[closed_under_cenv_def] >>
      fs[MEM_MAP] >>
      METIS_TAC[] ) >>
    fs[Abbr`P`] >> rfs[] >> fs[] >>
    first_x_assum(qspec_then`mm.cnmap`mp_tac)>>
    fsrw_tac[DNF_ss][] >>
    qpat_assum`evaluate_match_with P cenv s2 env v pes (res0,res1)`kall_tac >>
    map_every qx_gen_tac [`se`,`re`] >> strip_tac >>
    qmatch_assum_abbrev_tac`Cevaluate sb eee xe er` >>
    qspecl_then[`sb`,`eee`,`xe`,`er`]mp_tac(CONJUNCT1 Cevaluate_syneq) >>
    simp[] >>
    Q.PAT_ABBREV_TAC`we:Cexp = f mr` >>
    `we = shift 1 (LENGTH (pat_bindings (FST mr) [])) xe` by (
      unabbrev_all_tac >>
      PairCases_on`mr`>>simp[] >>
      rpt AP_TERM_TAC >> AP_THM_TAC >> AP_TERM_TAC >>
      simp[exp_to_Cexp_state_component_equality,pat_to_Cpat_cnmap,FST_pat_to_Cpat_bvars] ) >>
    disch_then(qspecl_then[`λv1 v2. if v1 < LENGTH wenv then v2 = v1 else v2 = v1 + 1`,`sd`,`wenv++w::enva`,`we`]mp_tac) >>
    discharge_hyps >- (
      conj_tac >- (
        rw[shift_def] >>
        match_mp_tac mkshift_thm >>
        simp[Abbr`xe`,Abbr`eee`] >>
        qpat_assum`MAP FST menv' = X`(assume_tac o SYM) >>
        `LENGTH wenv = LENGTH eenv` by fs[EVERY2_EVERY] >>
        `LENGTH eenv = LENGTH menv'` by fs[Abbr`eenv`,env_to_Cenv_MAP] >>
        simp[] >>
        match_mp_tac free_vars_exp_to_Cexp_matchable >>
        fs[] >>
        simp[Abbr`enva`,env_to_Cenv_MAP] >>
        fsrw_tac[DNF_ss][SUBSET_DEF,MEM_MAP,MEM_FLAT,is_null_def] >>
        rfs[] >> rw[] >> res_tac >> fs[] >> METIS_TAC[]) >>
      fs[EVERY2_EVERY,EVERY_MEM,FORALL_PROD,Abbr`eee`,ADD1] >>
      lrw[EL_APPEND1,EL_APPEND2] >- (
        first_x_assum(qspec_then`EL v1 eenv`kall_tac) >>
        first_x_assum match_mp_tac >>
        simp[MEM_ZIP] >>
        METIS_TAC[] ) >>
      lrw[EL_CONS,PRE_SUB1] ) >>
    disch_then(Q.X_CHOOSE_THEN`rg`strip_assume_tac) >>
    disch_then(qspec_then`rg`mp_tac) >>
    simp[EXISTS_PROD] >>
    fs[Abbr`er`] >>
    metis_tac[result_rel_syneq_trans,EVERY2_syneq_trans]) >>
  strip_tac >- (
    rw[exp_to_Cexp_def,LET_THM] >>
    rw[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][EXISTS_PROD]) >>
  strip_tac >- (
    rw[exp_to_Cexp_def,LET_THM] >> fs[bind_def] >>
    rw[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][EXISTS_PROD] >>
    disj1_tac >>
    last_x_assum(qspec_then`cm`mp_tac) >> simp[] >>
    disch_then(qx_choosel_then[`s2`,`vv`]strip_assume_tac) >>
    qspecl_then[`menv`,`cenv`,`s`,`env`,`exp`,`(s',Rval v)`]mp_tac(CONJUNCT1 evaluate_closed) >>
    qspecl_then[`menv`,`cenv`,`s`,`env`,`exp`,`(s',Rval v)`]mp_tac(evaluate_closed_under_cenv) >>
    fsrw_tac[DNF_ss][env_to_Cenv_MAP,SUBSET_DEF,lem] >> strip_tac >> strip_tac >>
    first_x_assum(qspec_then`cm`mp_tac) >>
    `all_cns v ⊆ set (MAP FST cenv)` by (
      qspecl_then[`menv`,`cenv`,`s`,`env`,`exp`,`(s',Rval v)`]mp_tac(CONJUNCT1 evaluate_all_cns) >>
      fs[closed_under_cenv_def] >> metis_tac[] ) >>
    fsrw_tac[DNF_ss][closed_under_cenv_def,EXISTS_PROD] >>
    map_every qx_gen_tac [`s3`,`v3`] >> strip_tac >>
    CONV_TAC(RESORT_EXISTS_CONV List.rev) >>
    map_every qexists_tac[`vv`,`s2`] >> simp[] >> fs[v_to_Cv_def] >>
    qmatch_assum_abbrev_tac`Cevaluate s1 env1 exp1 (s3,v3)` >>
    qspecl_then[`s1`,`env1`,`exp1`,`(s3,v3)`]mp_tac(CONJUNCT1 Cevaluate_syneq) >>
    simp[] >>
    disch_then(qspecl_then[`$=`,`s2`,`vv::(TL env1)`,`exp1`]mp_tac) >>
    simp[syneq_exp_refl,EXISTS_PROD,Abbr`env1`,ADD1] >>
    discharge_hyps >- (
      Cases >> lrw[EL_CONS] ) >>
    metis_tac[result_rel_syneq_trans,EVERY2_syneq_trans]) >>
  strip_tac >- (
    rw[exp_to_Cexp_def,LET_THM] >>
    rw[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][EXISTS_PROD]) >>
  strip_tac >- (
    rw[exp_to_Cexp_def,LET_THM,FST_triple] >>
    fs[] >>
    rw[defs_to_Cdefs_MAP] >>
    rw[Once Cevaluate_cases,FOLDL_FUPDATE_LIST] >>
    `FV exp ⊆ set (MAP (Short o FST) (build_rec_env funs env env)) ∪ menv_dom menv` by (
      fsrw_tac[DNF_ss][SUBSET_DEF,pairTheory.FORALL_PROD,MEM_MAP,pairTheory.EXISTS_PROD,MEM_FLAT,is_null_def,build_rec_env_MAP] >>
      rw[] >> res_tac >> fs[] >>
      METIS_TAC[] ) >>
    fs[] >>
    `EVERY (closed menv) (MAP SND (build_rec_env funs env env))` by (
      match_mp_tac build_rec_env_closed >>
      fs[] >>
      fsrw_tac[DNF_ss][SUBSET_DEF,pairTheory.FORALL_PROD,MEM_MAP,pairTheory.EXISTS_PROD,MEM_EL,FST_triple,is_null_def,FV_defs_MAP] >>
      rw[] >> res_tac >> fs[] >>
      METIS_TAC[] ) >>
    fs[] >>
    `closed_under_cenv cenv menv (build_rec_env funs env env) s` by (
      simp[build_rec_env_MAP] >>
      fsrw_tac[DNF_ss][closed_under_cenv_def,MEM_MAP,EXISTS_PROD,SUBSET_DEF] >>
      METIS_TAC[] ) >>
    fs[] >>
    first_x_assum (qspec_then `cm` mp_tac) >>
    fs[] >>
    simp[build_rec_env_def,bind_def,FOLDR_CONS_triple] >>
    fsrw_tac[DNF_ss][EXISTS_PROD,FORALL_PROD] >>
    simp[v_to_Cv_def,LET_THM,pairTheory.UNCURRY,defs_to_Cdefs_MAP
        ,env_to_Cenv_MAP,MAP_MAP_o,combinTheory.o_DEF,pairTheory.LAMBDA_PROD] >>
    simp[REVERSE_GENLIST,PRE_SUB1,FST_triple] >>
    Q.PAT_ABBREV_TAC`defs:def list = (MAP f funs)` >>
    map_every qx_gen_tac[`p1`,`p2`] >> strip_tac >>
    map_every qexists_tac[`p1`,`p2`] >>
    reverse conj_tac >- METIS_TAC[] >>
    qmatch_abbrev_tac`Cevaluate ss l1 ee rr` >>
    qmatch_assum_abbrev_tac`Cevaluate ss l2 ee rr` >>
    qsuff_tac`l1 = l2`>-rw[] >>
    lrw[Abbr`l1`,Abbr`l2`,LIST_EQ_REWRITE,EL_MAP,UNCURRY] >>
    Q.ISPEC_THEN`(MAP FST funs)`mp_tac find_index_ALL_DISTINCT_EL_eq >>
    simp[ALL_DISTINCT_REVERSE] >>
    disch_then(qspecl_then[`FST (EL x funs)`,`0`]mp_tac) >>
    simp[] >>
    disch_then(qspec_then`x`mp_tac) >>
    simp[EL_REVERSE,PRE_SUB1,EL_MAP]) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rw[] >>
    fsrw_tac[DNF_ss][EXISTS_PROD] >>
    rw[Once Cevaluate_cases] ) >>
  strip_tac >- (
    rw[] >>
    rw[Once (CONJUNCT2 Cevaluate_cases)] >>
    fsrw_tac[DNF_ss][EXISTS_PROD] >>
    qspecl_then[`menv`,`cenv`,`s`,`env`,`exp`,`(s',Rval v)`]mp_tac(CONJUNCT1 evaluate_closed) >>
    qspecl_then[`menv`,`cenv`,`s`,`env`,`exp`,`(s',Rval v)`]mp_tac(evaluate_closed_under_cenv) >>
    simp[] >> rpt strip_tac >> fs[] >>
    rpt (first_x_assum (qspec_then`cm` mp_tac)) >>
    rw[] >>
    qmatch_assum_rename_tac`syneq (v_to_Cv m v) w`[] >>
    qmatch_assum_abbrev_tac`Cevaluate sa enva ea (sd,Rval w)` >>
    pop_assum kall_tac >>
    CONV_TAC SWAP_EXISTS_CONV >> qexists_tac`sd` >>
    CONV_TAC SWAP_EXISTS_CONV >> qexists_tac`w` >> rw[] >>
    qmatch_assum_abbrev_tac`Cevaluate_list sb enva eb (se,Rval ws)` >>
    ntac 2 (pop_assum kall_tac) >>
    qspecl_then[`sb`,`sd`,`enva`,`enva`,`eb`,`(se,Rval ws)`]mp_tac Cevaluate_list_any_syneq_any >>
    fsrw_tac[DNF_ss][FORALL_PROD] >>
    map_every qx_gen_tac[`sf`,`rf`] >>
    strip_tac >>
    map_every qexists_tac[`sf`,`rf`] >>
    simp[] >>
    METIS_TAC[EVERY2_syneq_trans]) >>
  strip_tac >- (
    rw[] >>
    rw[Once (CONJUNCT2 Cevaluate_cases)] >>
    fsrw_tac[DNF_ss][EXISTS_PROD] ) >>
  rw[] >>
  rw[Once (CONJUNCT2 Cevaluate_cases)] >>
  fsrw_tac[DNF_ss][EXISTS_PROD] >>
  disj2_tac >>
  qspecl_then[`menv`,`cenv`,`s`,`env`,`exp`,`(s',Rval v)`]mp_tac(CONJUNCT1 evaluate_closed) >>
  qspecl_then[`menv`,`cenv`,`s`,`env`,`exp`,`(s',Rval v)`]mp_tac(evaluate_closed_under_cenv) >>
  simp[] >> rpt strip_tac >> fs[] >>
  rpt (first_x_assum (qspec_then`cm` mp_tac)) >>
  rw[] >>
  qmatch_assum_rename_tac`syneq (v_to_Cv m v) w`[] >>
  qmatch_assum_abbrev_tac`Cevaluate sa enva ea (sd,Rval w)` >>
  pop_assum kall_tac >>
  CONV_TAC SWAP_EXISTS_CONV >> qexists_tac`sd` >>
  CONV_TAC SWAP_EXISTS_CONV >> qexists_tac`w` >> rw[] >>
  qmatch_assum_abbrev_tac`Cevaluate_list sb enva eb (se,Rerr err)` >>
  pop_assum kall_tac >>
  qspecl_then[`sb`,`sd`,`enva`,`enva`,`eb`,`(se,Rerr err)`]mp_tac Cevaluate_list_any_syneq_any >>
  fsrw_tac[DNF_ss][FORALL_PROD] >>
  METIS_TAC[EVERY2_syneq_trans])

val exp_to_Cexp_syneq = store_thm("exp_to_Cexp_syneq",
  ``(∀m exp bvs1 bvs2. (set bvs1 = set bvs2) ⇒
      syneq_exp (LENGTH bvs1) (LENGTH bvs2)
        (λv1 v2. v1 < LENGTH bvs1 ∧ v2 < LENGTH bvs2 ∧ (EL v1 bvs1 = EL v2 bvs2) ∨
                 LENGTH bvs1 ≤ v1 ∧ LENGTH bvs2 ≤ v2 ∧ (v2 = v1))
        (exp_to_Cexp (m with bvars := bvs1) exp)
        (exp_to_Cexp (m with bvars := bvs2) exp)) ∧
    (∀m defs bvs1 bvs2. (set bvs1 = set bvs2) ⇒
      syneq_defs (LENGTH bvs1) (LENGTH bvs2)
        (λv1 v2. v1 < LENGTH bvs1 ∧ v2 < LENGTH bvs2 ∧ (EL v1 bvs1 = EL v2 bvs2) ∨
                 LENGTH bvs1 ≤ v1 ∧ LENGTH bvs2 ≤ v2 ∧ (v2 = v1))
        (defs_to_Cdefs (m with bvars := (MAP FST defs) ++ bvs1) defs)
        (defs_to_Cdefs (m with bvars := (MAP FST defs) ++ bvs2) defs)
        (λv1 v2. v1 < LENGTH defs ∧ (v2 = v1))) ∧
    (∀m pes bvs1 bvs2. (set bvs1 = set bvs2) ⇒
      EVERY2 (λ(p1,e1) (p2,e2).
        syneq_exp (Cpat_vars p1 + LENGTH bvs1) (Cpat_vars p2 + LENGTH bvs2)
          (λv1 v2. v1 < Cpat_vars p1 ∧ v2 < Cpat_vars p2 ∧ (v2 = v1) ∨
                   Cpat_vars p1 ≤ v1 ∧ Cpat_vars p2 ≤ v2 ∧
                   v1 < Cpat_vars p1 + LENGTH bvs1 ∧ v2 < Cpat_vars p2 + LENGTH bvs2 ∧ (EL v1 bvs1 = EL v2 bvs2) ∨
                   Cpat_vars p1 + LENGTH bvs1 ≤ v1 ∧ Cpat_vars p2 + LENGTH bvs2 ≤ v2 ∧ (v2 = v1))
          e1 e2)
                        (pes_to_Cpes (m with bvars := bvs1) pes)
                        (pes_to_Cpes (m with bvars := bvs2) pes)) ∧
    (∀m es bvs1 bvs2. (set bvs1 = set bvs2) ⇒
      EVERY2 (syneq_exp (LENGTH bvs1) (LENGTH bvs2)
               (λv1 v2. v1 < LENGTH bvs1 ∧ v2 < LENGTH bvs2 ∧ (EL v1 bvs1 = EL v2 bvs2) ∨
                        LENGTH bvs1 ≤ v1 ∧ LENGTH bvs2 ≤ v2 ∧ (v2 = v1)))
         (exps_to_Cexps (m with bvars := bvs1) es)
         (exps_to_Cexps (m with bvars := bvs2) es))``
  ho_match_mp_tac exp_to_Cexp_ind >>
  strip_tac >- (
    rw[exp_to_Cexp_def] >>
    rw[Once syneq_exp_cases] >>
    first_x_assum(qspecl_then[`x::bvs1`,`x::bvs2`]mp_tac) >>
    simp[ADD1,EL_CONS]

val enveq_v_to_Cv = store_thm("enveq_v_to_Cv",
  ``∀v1 v2. enveq v1 v2 ⇒ ∀m. syneq (v_to_Cv m v1) (v_to_Cv m v2)``,
  ho_match_mp_tac enveq_ind >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rw[] >>
    rw[v_to_Cv_def] >>
    rw[Once syneq_cases,vs_to_Cvs_MAP] >>
    simp[EVERY2_MAP] >>
    match_mp_tac (GEN_ALL (MP_CANON EVERY2_mono)) >>
    HINT_EXISTS_TAC >> simp[] ) >>
  strip_tac >- (
    rw[] >>
    rw[v_to_Cv_def] >>
    rw[Once syneq_cases] >>
    rw[Once syneq_exp_cases]
  strip_tac >- (
    rw[] >>
    rw[v_to_Cv_def] >>
    rw[Once syneq_cases] >>
    rw[Once syneq_exp_cases]

  v_to_Cv_ind
  type_of ``env_to_Cenv``
  exp_to_Cexp_nice_ind
  exp_to_Cexp_ind

val _ = export_theory()
