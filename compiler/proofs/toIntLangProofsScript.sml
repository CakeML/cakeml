open HolKernel bossLib boolLib miscLib boolSimps intLib pairTheory sumTheory listTheory pred_setTheory finite_mapTheory arithmeticTheory alistTheory rich_listTheory lcsymtacs
open LibTheory SemanticPrimitivesTheory AstTheory terminationTheory semanticsExtraTheory miscTheory CompilerLibTheory IntLangTheory ToIntLangTheory compilerTerminationTheory intLangExtraTheory pmatchTheory
val _ = numLib.prefer_num()
val _ = new_theory "toIntLangProofs"
val fsd = full_simp_tac std_ss

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
  syneq (v_to_Cv d m v1) w1 ⇒
  ∃env'' defs n.
    (w1 = CRecClos env'' defs n)``,
Cases_on `v1` >> rw[do_app_def,v_to_Cv_def,LET_THM] >>
fs[defs_to_Cdefs_MAP, Once syneq_cases])

val env_to_Cenv_APPEND = store_thm("env_to_Cenv_APPEND",
  ``env_to_Cenv mv m (l1 ++ l2) = env_to_Cenv mv m l1 ++ env_to_Cenv mv m l2``,
  rw[env_to_Cenv_MAP])
val _ = export_rewrites["env_to_Cenv_APPEND"]

val all_Clocs_v_to_Cv = store_thm("all_Clocs_v_to_Cv",
  ``(∀mv m v. all_Clocs (v_to_Cv mv m v) = all_locs v) ∧
    (∀mv m vs. MAP all_Clocs (vs_to_Cvs mv m vs) = MAP all_locs vs) ∧
    (∀mv m env. MAP all_Clocs (env_to_Cenv mv m env) = MAP (all_locs o SND) env)``,
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
  ``(∀mv m v. no_vlabs (v_to_Cv mv m v)) ∧
    (∀mv m vs. no_vlabs_list (vs_to_Cvs mv m vs)) ∧
    (∀mv m env. no_vlabs_list (env_to_Cenv mv m env))``,
  ho_match_mp_tac v_to_Cv_ind >>
  rw[v_to_Cv_def] >>
  TRY(qunabbrev_tac`Ce`)>>
  TRY(qunabbrev_tac`Cdefs`)>>
  simp[FLAT_EQ_NIL,EVERY_MAP,defs_to_Cdefs_MAP] >>
  simp[EVERY_MEM,UNCURRY])
val _ = export_rewrites["no_vlabs_v_to_Cv"]

val cmap_linv_def = Define`
  cmap_linv m w ⇔ ∀x. x ∈ FDOM m ⇒ (ALOOKUP w (FAPPLY m x) = SOME x)`

val cmap_linv_FAPPLY = store_thm("cmap_linv_FAPPLY",
  ``cmap_linv f g ∧ x ∈ FDOM f ⇒ (the d (ALOOKUP g (FAPPLY f x)) = x)``,
  rw[cmap_linv_def,IN_FRANGE])

val v_to_Cv_ov = store_thm("v_to_Cv_ov",
  ``(∀mv m v w s. (all_cns v ⊆ FDOM m) ∧ cmap_linv m w ==> (Cv_to_ov w s (v_to_Cv mv m v) = v_to_ov s v)) ∧
    (∀mv m vs w s. (BIGUNION (IMAGE all_cns (set vs)) ⊆ FDOM m) ∧ cmap_linv m w ==> (MAP (Cv_to_ov w s) (vs_to_Cvs mv m vs) = MAP (v_to_ov s) vs)) ∧
    (∀(mv:modN |-> varN list) (m:(conN id option)|->num) (env:envE). T)``,
  ho_match_mp_tac v_to_Cv_ind >>
  rw[v_to_Cv_def,FLOOKUP_DEF] >> rw[Cv_to_ov_def] >>
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

val mvars_def = tDefine"mvars"`
  (mvars (CRaise e) = mvars e) ∧
  (mvars (CHandle e1 e2) = mvars e1 ∪ mvars e2) ∧
  (mvars (CVar (Short _)) = {}) ∧
  (mvars (CVar (Long mn x)) = {(mn,x)}) ∧
  (mvars (CLit _) = {}) ∧
  (mvars (CCon _ es) = mvars_list es) ∧
  (mvars (CTagEq e _) = mvars e) ∧
  (mvars (CProj e _) = mvars e) ∧
  (mvars (CLet e eb) = mvars e ∪ mvars eb) ∧
  (mvars (CLetrec defs e) = mvars_defs defs ∪ mvars e) ∧
  (mvars (CCall _ e es) = mvars e ∪ mvars_list es) ∧
  (mvars (CPrim1 _ e) = mvars e) ∧
  (mvars (CPrim2 _ e1 e2) = mvars e1 ∪ mvars e2) ∧
  (mvars (CUpd e1 e2) = mvars e1 ∪ mvars e2) ∧
  (mvars (CIf e1 e2 e3) = mvars e1 ∪ mvars e2 ∪ mvars e3) ∧
  (mvars_list [] = {}) ∧
  (mvars_list (e::es) = mvars e ∪ mvars_list es) ∧
  (mvars_defs [] = {}) ∧
  (mvars_defs (d::ds) = mvars_def d ∪ mvars_defs ds) ∧
  (mvars_def (_,_,e) = mvars e)`
  (WF_REL_TAC `inv_image $< (λx. case x of
    | INL e => Cexp_size e
    | INR (INL es) => Cexp4_size es
    | INR (INR (INL (defs))) => Cexp1_size defs
    | INR (INR (INR (def))) => Cexp2_size def)`)
val _ = export_rewrites["mvars_def"]

val FST_pat_to_Cpat_mvars = store_thm("FST_pat_to_Cpat_mvars",
  ``(∀p s. (FST (pat_to_Cpat s p)).mvars = s.mvars) ∧
    (∀ps s. (FST (pats_to_Cpats s ps)).mvars = s.mvars)``,
  ho_match_mp_tac (TypeBase.induction_of``:pat``) >>
  rw[pat_to_Cpat_def,pat_bindings_def] >> rw[]
  >- ( first_x_assum(qspec_then`s`mp_tac) >> simp[] )
  >- ( first_x_assum(qspec_then`s`mp_tac) >> simp[] ) >>
  first_x_assum(qspec_then`m`mp_tac) >>
  first_x_assum(qspec_then`s`mp_tac) >>
  rw[] >>
  simp[Once pat_bindings_acc,SimpRHS])
val _ = export_rewrites["FST_pat_to_Cpat_mvars"]

val SND_pat_to_Cpat_ignore_mvars = store_thm("SND_pat_to_Cpat_ignore_mvars",
  ``(∀p m m'. m'.bvars = m.bvars ∧ m'.cnmap = m.cnmap ⇒ SND(pat_to_Cpat m' p) = SND(pat_to_Cpat m p)) ∧
    (∀ps m m'. m'.bvars = m.bvars ∧ m'.cnmap = m.cnmap ⇒ SND(pats_to_Cpats m' ps) = SND(pats_to_Cpats m ps))``,
  ho_match_mp_tac(TypeBase.induction_of``:pat``) >>
  simp[ToIntLangTheory.pat_to_Cpat_def] >>
  simp[UNCURRY] >>
  rw[] >- metis_tac[pmatchTheory.pat_to_Cpat_cnmap,FST] >>
  first_x_assum match_mp_tac >>
  conj_tac >- metis_tac[FST_pat_to_Cpat_bvars,FST] >>
  metis_tac[pmatchTheory.pat_to_Cpat_cnmap,FST])

val FST_pat_to_Cpat_ignore_mvars = store_thm("FST_pat_to_Cpat_ignore_mvars",
  ``(∀p m m'. m'.bvars = m.bvars ∧ m'.cnmap = m.cnmap ⇒ FST(pat_to_Cpat m' p) = FST(pat_to_Cpat m p) with mvars := m'.mvars) ∧
    (∀ps m m'. m'.bvars = m.bvars ∧ m'.cnmap = m.cnmap ⇒ FST(pats_to_Cpats m' ps) = FST(pats_to_Cpats m ps) with mvars := m'.mvars)``,
  ho_match_mp_tac(TypeBase.induction_of``:pat``) >>
  simp[ToIntLangTheory.pat_to_Cpat_def] >>
  simp[UNCURRY] >>
  rw[ToIntLangTheory.exp_to_Cexp_state_component_equality])

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
strip_tac >- rw[exp_to_Cexp_def] >>
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
  fsrw_tac[DNF_ss,ARITH_ss][SUBSET_DEF,PRE_SUB1,ADD1,Abbr`n`] >>
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
``(∀mv m v. closed menv v ⇒ Cclosed (v_to_Cv mv m v)) ∧
  (∀mv m vs. EVERY (closed menv) vs ⇒ EVERY (Cclosed) (vs_to_Cvs mv m vs)) ∧
  (∀mv m env. EVERY (closed menv) (MAP SND env) ⇒ EVERY (Cclosed) (env_to_Cenv mv m env))``,
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
  discharge_hyps >- (
    rw[] >> res_tac >> fs[MEM_MAP,MEM_FLAT] >>
    rw[] >> fs[MEM_MAP] >>
    metis_tac[]) >>
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
  rw[] >> res_tac >> fs[MEM_MAP,MEM_FLAT] >> rw[] >> fs[MEM_MAP] >>
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
  pop_assum (assume_tac o SYM) >> fs[]);

(* correctness *)

val v_to_Cv_inj = store_thm(
"v_to_Cv_inj",
``(∀mv s v1 v2.
    all_cns v1 ⊆ cenv_dom cenv ∧
    all_cns v2 ⊆ cenv_dom cenv ∧
    good_cmap cenv s ∧
    ¬contains_closure v1 ∧ ¬contains_closure v2 ∧
    (v_to_Cv mv s v1 = v_to_Cv mv s v2) ⇒ (v1 = v2)) ∧
  (∀mv s vs1 vs2.
    BIGUNION (IMAGE all_cns (set vs1)) ⊆ cenv_dom cenv ∧
    BIGUNION (IMAGE all_cns (set vs2)) ⊆ cenv_dom cenv ∧
    good_cmap cenv s ∧
    ¬EXISTS contains_closure vs1 ∧ ¬EXISTS contains_closure vs2 ∧
    (vs_to_Cvs mv s vs1 = vs_to_Cvs mv s vs2) ⇒ (vs1 = vs2)) ∧
  (∀(mv:string |-> string list) (s:string id option|->num) (env1:envE).T)``,
ho_match_mp_tac v_to_Cv_ind >> rw[FLOOKUP_DEF,v_to_Cv_def,LET_THM,vs_to_Cvs_MAP,env_to_Cenv_MAP] >>
TRY (Cases_on`v2`>>fs[FLOOKUP_DEF,v_to_Cv_def,LET_THM]>>NO_TAC)
>- (
  Cases_on`v2`>>fs[cenv_dom_def,FLOOKUP_DEF,v_to_Cv_def,vs_to_Cvs_MAP,MAP_EQ_EVERY2,EVERY2_EVERY,LET_THM] >>
  fsrw_tac[ETA_ss][good_cmap_def,MEM_MAP,EXISTS_PROD,contains_closure_def] >>
  fs[FORALL_PROD] >>
  BasicProvers.EVERY_CASE_TAC>>fs[]>>
  metis_tac[])
>- (
  Cases_on`v2`>>fs[cenv_dom_def,FLOOKUP_DEF,v_to_Cv_def,vs_to_Cvs_MAP,MAP_EQ_EVERY2,EVERY2_EVERY,LET_THM] >>
  fsrw_tac[ETA_ss][good_cmap_def,MEM_MAP,EXISTS_PROD,contains_closure_def] >>
  fs[FORALL_PROD] >>
  BasicProvers.EVERY_CASE_TAC>>fs[]>>
  metis_tac[])
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
  fs[exp_to_Cexp_state_component_equality,UNION_COMM] >>
  metis_tac[FST_pat_to_Cpat_mvars,FST,FST])

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
  ``∀ls s s' e. SFV e ⊆ set s.bvars ∧ (s'.cnmap = s.cnmap) ∧ (s'.mvars = s.mvars) ∧ (s'.bvars = s.bvars ++ ls) ⇒
             (exp_to_Cexp s' e = exp_to_Cexp s e)``,
  rw[] >> imp_res_tac exp_to_Cexp_append_bvars >>
  pop_assum(qspec_then`ls`strip_assume_tac) >>
  qmatch_assum_abbrev_tac`exp_to_Cexp z e = exp_to_Cexp s e` >>
  qsuff_tac`z = s'`>-PROVE_TAC[]>>
  simp[exp_to_Cexp_state_component_equality,Abbr`z`])

val no_closures_contains_closure = store_thm("no_closures_contains_closure",
  ``(∀v mv m. no_closures (v_to_Cv m mv v) = ¬contains_closure v)``,
  ho_match_mp_tac contains_closure_ind >>
  simp[contains_closure_def,v_to_Cv_def,no_closures_def] >>
  simp_tac(srw_ss()++DNF_ss)[EVERY_MEM,vs_to_Cvs_MAP,MEM_MAP])

val do_eq_to_do_Ceq = Q.prove (
`good_cmap cenv m ⇒
 (!v1 v2.
    all_cns v1 ⊆ cenv_dom cenv ∧ all_cns v2 ⊆ cenv_dom cenv ⇒
    (!b. (do_eq v1 v2 = Eq_val b) ⇒ (do_Ceq (v_to_Cv mv m v1) (v_to_Cv mv m v2) = Eq_val b)) ∧
    ((do_eq v1 v2 = Eq_closure) ⇒ (do_Ceq (v_to_Cv mv m v1) (v_to_Cv mv m v2) = Eq_closure))) ∧
 (!vs1 vs2.
    BIGUNION (IMAGE all_cns (set vs1)) ⊆ cenv_dom cenv ∧ BIGUNION (IMAGE all_cns (set vs2)) ⊆ cenv_dom cenv ⇒
    (!b. (do_eq_list vs1 vs2 = Eq_val b) ⇒ (do_Ceq_list (vs_to_Cvs mv m vs1) (vs_to_Cvs mv m vs2) = Eq_val b)) ∧
    ((do_eq_list vs1 vs2 = Eq_closure) ⇒ (do_Ceq_list (vs_to_Cvs mv m vs1) (vs_to_Cvs mv m vs2) = Eq_closure)))`,
 strip_tac >>
 ho_match_mp_tac do_eq_ind >>
 rw [do_eq_def, v_to_Cv_def] >>
 rw [] >>
 TRY(fs[vs_to_Cvs_MAP]>>NO_TAC)>- (
   Cases_on `FLOOKUP m cn1` >>
   Cases_on `FLOOKUP m cn2` >>
   fs [] >>
   rw [] >>
   fs [FLOOKUP_DEF, MEM_MAP, SUBSET_DEF, good_cmap_def, cenv_dom_def] >>
   TRY(fs[vs_to_Cvs_MAP]>>NO_TAC) >>
   metis_tac []) >>
 Cases_on `do_eq v1 v2` >>
 fs [] >>
 metis_tac []);

fun tac w1 =
 ho_match_mp_tac syneq_ind >>
 rw [] >>
 Cases_on w1 >>
 fs [] >>
 Cases_on `n = cn` >>
 fs [] >>
 rpt (pop_assum mp_tac) >>
 Q.SPEC_TAC (`vs1`, `vs1`) >>
 Q.SPEC_TAC (`vs2`, `vs2`) >>
 Induct_on `l` >>
 rw [] >>
 Cases_on `vs2` >>
 fs [] >>
 rw [] >>
 fs [] >>
 TRY(fs[EVERY2_EVERY]>>NO_TAC)>>
 BasicProvers.CASE_TAC >>
 fs [] >>
 Cases_on `b` >>
 fs [] >>
 metis_tac[]

val do_Ceq_syneq1 = Q.prove (
`!w1 w2. syneq w1 w2  ⇒ ∀w3. do_Ceq w1 w3 = do_Ceq w2 w3`,
tac `w3`)

val do_Ceq_syneq2 = Q.prove (
`!w2 w3. syneq w2 w3  ⇒ ∀w1. do_Ceq w1 w2 = do_Ceq w1 w3`,
tac `w1`)

val exp_to_Cexp_thm1 = store_thm("exp_to_Cexp_thm1",
  ``(∀ck menv (cenv:envC) cs env exp res. evaluate ck menv cenv cs env exp res ⇒
     ck ∧ FV exp ⊆ set (MAP (Short o FST) env) ∪ menv_dom menv ∧
     (EVERY (closed menv) (SND cs)) ∧ (EVERY (closed menv) (MAP SND env)) ∧
     EVERY (EVERY (closed menv) o MAP SND) (MAP SND menv) ∧
     closed_under_cenv cenv menv env (SND cs) ∧
     all_cns_exp exp ⊆ cenv_dom cenv ∧
     (SND res ≠ Rerr Rtype_error) ⇒
     ∀cm. good_cmap cenv cm ⇒
       let fmv = alist_to_fmap menv in
       let mv = MAP FST o_f fmv in
       ∃Cres.
       Cevaluate
         (env_to_Cenv mv cm o_f fmv)
         (FST cs, (MAP (v_to_Cv mv cm) (SND cs)))
         (env_to_Cenv mv cm env)
         (exp_to_Cexp (<| bvars := MAP FST env; mvars := mv; cnmap := cm|>) exp)
         Cres ∧
         FST (FST res) = FST (FST Cres) ∧
         EVERY2 (syneq) (MAP (v_to_Cv mv cm) (SND (FST res))) (SND (FST Cres)) ∧
         Cresult_rel syneq syneq (Cmap_result (v_to_Cv mv cm) (SND res)) (SND Cres))∧
    (∀ck menv (cenv:envC) cs env exps res. evaluate_list ck menv cenv cs env exps res ⇒
     ck ∧ FV_list exps ⊆ set (MAP (Short o FST) env) ∪ menv_dom menv ∧
     (EVERY (closed menv) (SND cs)) ∧ (EVERY (closed menv) (MAP SND env)) ∧
     EVERY (EVERY (closed menv) o MAP SND) (MAP SND menv) ∧
     closed_under_cenv cenv menv env (SND cs) ∧
     all_cns_list exps ⊆ cenv_dom cenv ∧
     (SND res ≠ Rerr Rtype_error) ⇒
     ∀cm. good_cmap cenv cm ⇒
       let fmv = alist_to_fmap menv in
       let mv = MAP FST o_f fmv in
       ∃Cres.
       Cevaluate_list
         (env_to_Cenv mv cm o_f fmv)
         (FST cs, MAP (v_to_Cv mv cm) (SND cs))
         (env_to_Cenv mv cm env)
         (MAP (exp_to_Cexp (<| bvars := MAP FST env; mvars := mv; cnmap := cm|>)) exps)
         Cres ∧
         FST (FST res) = FST (FST Cres) ∧
         EVERY2 (syneq) (MAP (v_to_Cv mv cm) (SND (FST res))) (SND (FST Cres)) ∧
         Cresult_rel (EVERY2 (syneq)) syneq (Cmap_result (MAP (v_to_Cv mv cm)) (SND res)) (SND Cres))``,
  ho_match_mp_tac evaluate_nicematch_strongind >>
  strip_tac >- (rw[exp_to_Cexp_def,v_to_Cv_def] >> rw[]) >>
  strip_tac >- (
    rw[exp_to_Cexp_def] >>
    Cases_on`err`>>simp[] >>
    simp[exp_to_Cexp_def] >>
    simp[Once Cevaluate_cases] >>
    srw_tac[DNF_ss][] >>
    ntac 2 (simp[Once syneq_cases]) >>
    simp[Once Cevaluate_cases] >>
    simp[Once Cevaluate_cases] ) >>
  strip_tac >- (
    rw[exp_to_Cexp_def] >> fs[LET_THM] >>
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
    disch_then(qx_choosel_then[`s2`]strip_assume_tac) >>
    qspecl_then[`T`,`menv`,`cenv`,`cs`,`env`,`exp`,`(cs',Rerr (Rraise (Int_error n)))`]mp_tac(CONJUNCT1 evaluate_closed) >>
    qspecl_then[`T`,`menv`,`cenv`,`cs`,`env`,`exp`,`(cs',Rerr (Rraise (Int_error n)))`]mp_tac(evaluate_closed_under_cenv) >>
    fsrw_tac[DNF_ss][env_to_Cenv_MAP,SUBSET_DEF,lem] >> strip_tac >> strip_tac >>
    first_x_assum(qspec_then`cm`mp_tac) >>
    fsrw_tac[DNF_ss][closed_under_cenv_def,EXISTS_PROD,LET_THM] >>
    map_every qx_gen_tac [`s3`,`v`] >> strip_tac >>
    CONV_TAC(RESORT_EXISTS_CONV List.rev) >>
    map_every qexists_tac[`CLitv (IntLit n)`,`s2`,`FST cs'`] >> simp[] >> fs[v_to_Cv_def] >>
    qmatch_assum_abbrev_tac`Cevaluate Cmenv s1 env1 exp1 ((clk3,s3),v)` >>
    qspecl_then[`Cmenv`,`s1`,`env1`,`exp1`,`((clk3,s3),v)`]mp_tac(CONJUNCT1 Cevaluate_syneq) >>
    simp[] >>
    disch_then(qspecl_then[`$=`,`Cmenv`,`FST cs',s2`,`env1`,`exp1`]mp_tac) >>
    simp[syneq_exp_refl,EXISTS_PROD,Abbr`s1`] >>
    strip_tac >>
    srw_tac[DNF_ss][Once Cevaluate_cases] >> disj1_tac >>
    ntac 4 (srw_tac[DNF_ss][Once Cevaluate_cases]) >>
    srw_tac[DNF_ss][Once Cevaluate_cases,Abbr`env1`] >>
    srw_tac[DNF_ss][Once Cevaluate_cases] >>
    srw_tac[DNF_ss][Once Cevaluate_cases] >> disj1_tac >>
    ntac 6 (srw_tac[DNF_ss][Once Cevaluate_cases]) >>
    srw_tac[DNF_ss][Once Cevaluate_cases] >> disj1_tac >>
    ntac 6 (srw_tac[DNF_ss][Once Cevaluate_cases]) >>
    metis_tac[Cresult_rel_syneq_trans,EVERY2_syneq_trans]) >>
  strip_tac >- (
    rpt gen_tac >> simp[] >>
    rw[exp_to_Cexp_def] >>
    rw[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][EXISTS_PROD] >>
    fs[Once syneq_cases] >>
    CONV_TAC (RESORT_EXISTS_CONV List.rev) >|
      [qexists_tac`CBind_excv`,qexists_tac`CDiv_excv`,qexists_tac`CEq_excv`] >>
    first_x_assum(qspec_then`cm`mp_tac) >> simp[] >>
    disch_then(Q.X_CHOOSE_THEN`s3`strip_assume_tac) >>
    map_every qexists_tac[`s3`,`FST s2`] >> simp[] >>
    srw_tac[DNF_ss][Once Cevaluate_cases] >> disj1_tac >>
    ntac 6 (srw_tac[DNF_ss][Once Cevaluate_cases]) >>
    srw_tac[DNF_ss][Once Cevaluate_cases] >> disj1_tac >>
    rpt (srw_tac[DNF_ss][Once Cevaluate_cases])) >>
  strip_tac >- (
    rw[exp_to_Cexp_def,v_to_Cv_def,
       exps_to_Cexps_MAP,vs_to_Cvs_MAP,
       Cevaluate_con] >>
    fsrw_tac[DNF_ss,ETA_ss][EXISTS_PROD,LET_THM] >>
    simp[Once syneq_cases]) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rw[exp_to_Cexp_def,v_to_Cv_def,
       exps_to_Cexps_MAP,Cevaluate_con] >>
    fsrw_tac[DNF_ss,ETA_ss][EXISTS_PROD,LET_THM] >>
    Cases_on`err`>>simp[]>>fs[]>>
    Cases_on`e`>>simp[]>>fs[] >>
    metis_tac[]) >>
  strip_tac >- (
    fs[exp_to_Cexp_def,MEM_MAP,pairTheory.EXISTS_PROD,env_to_Cenv_MAP,lookup_var_id_def] >>
    rpt gen_tac >>
    reverse BasicProvers.CASE_TAC >- (
      simp[MEM_FLAT,MEM_MAP] >>
      BasicProvers.CASE_TAC >>
      rw[] >>
      simp[exp_to_Cexp_def] >>
      simp[Once Cevaluate_cases] >>
      simp_tac(srw_ss()++DNF_ss)[] >>
      simp[FLOOKUP_DEF,env_to_Cenv_MAP] >>
      fs[MEM_MAP] >>
      conj_asm1_tac >- metis_tac[] >>
      simp[] >>
      rpt BasicProvers.VAR_EQ_TAC >>
      imp_res_tac ALOOKUP_SOME_FAPPLY_alist_to_fmap >>
      simp[] >> ntac 3 (pop_assum kall_tac) >>
      conj_tac >- (
        qmatch_abbrev_tac`X < Y` >>
        qsuff_tac`(λx. x < Y) X`>-rw[] >>
        unabbrev_all_tac >>
        match_mp_tac the_find_index_suff >>
        imp_res_tac ALOOKUP_MEM >>
        simp[MEM_MAP] >> PROVE_TAC[FST] ) >>
      qpat_assum`ALOOKUP X Y = SOME v`mp_tac >>
      simp[ALOOKUP_LEAST_EL,find_index_LEAST_EL] >>
      strip_tac >>
      BasicProvers.VAR_EQ_TAC >>
      `(LEAST n. EL n (MAP FST x) = FST y) = (LEAST n. FST y = EL n (MAP FST x))` by (
        rw[] >> AP_TERM_TAC >> rw[FUN_EQ_THM] >> PROVE_TAC[] ) >>
      qmatch_assum_abbrev_tac`X = Y` >>
      qpat_assum`X = Y`SUBST1_TAC >>
      `Y < LENGTH x` by (
        qunabbrev_tac`Y` >>
        numLib.LEAST_ELIM_TAC >>
        fs[MEM_EL] >>
        conj_tac >- metis_tac[] >>
        rw[] >>
        qmatch_assum_rename_tac`a < LENGTH b`[] >>
        qmatch_rename_tac`c < LENGTH b`[] >>
        `~(a<c)`by metis_tac[] >>
        DECIDE_TAC ) >>
      simp[EL_MAP]) >>
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
    simp[Once Cevaluate_cases]) >>
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
    fsrw_tac[DNF_ss][] >>
    Cases_on`err`>>simp[]>>fs[]>>
    Cases_on`e`>>simp[]>>fs[]>>
    metis_tac[]) >>
  strip_tac >- (
    ntac 4 gen_tac >>
    Cases >> fs[exp_to_Cexp_def] >>
    qx_gen_tac `e1` >>
    qx_gen_tac `e2` >>
    rpt gen_tac >>
    Q.PAT_ABBREV_TAC`cnt' = if ck then X else Y:num` >>
    rw[LET_THM] >- (
      qmatch_assum_rename_tac `do_app s3 env (Opn opn) v1 v2 = SOME (s4,env',exp'')` [] >>
      Cases_on `opn_to_prim2 opn` >> simp[] >- (
        rw[Once Cevaluate_cases] >>
        fsrw_tac[DNF_ss][] >>
        disj1_tac >>
        rw[Once(CONJUNCT2 Cevaluate_cases)] >> fsrw_tac[DNF_ss][] >>
        rw[Once(CONJUNCT2 Cevaluate_cases)] >> fsrw_tac[DNF_ss][] >>
        rw[Once(CONJUNCT2 Cevaluate_cases)] >> fsrw_tac[DNF_ss][] >>
        rpt (first_x_assum (qspec_then `cm` mp_tac)) >>
        `closed_under_cenv cenv menv env' s4 ∧ closed_under_cenv cenv menv env (SND cs')` by (
          `(s4 = s3) ∧ (env' = env)` by fs[do_app_Opn_SOME] >>
          imp_res_tac evaluate_closed_under_cenv >> fs[] ) >>
        rw[] >>
        qmatch_assum_abbrev_tac `syneq (v_to_Cv mv cm v1) w1` >>
        pop_assum kall_tac >>
        qspecl_then[`T`,`menv`,`cenv`,`cs`,`env`,`e1`,`(cs',Rval v1)`]mp_tac(CONJUNCT1 evaluate_closed) >>
        simp[] >> strip_tac >> fs[] >>
        qmatch_assum_rename_tac `syneq (v_to_Cv mv m v2) w2`[] >>
        qmatch_assum_rename_tac`SND r1 = Cval w1`[] >>
        qmatch_assum_rename_tac`SND r2 = Cval w2`[] >>
        qmatch_assum_abbrev_tac`Cevaluate Cmenv sa enva e1a r1` >>
        qmatch_assum_abbrev_tac`Cevaluate Cmenv sb enva e2a r2` >>
        CONV_TAC SWAP_EXISTS_CONV >> qexists_tac`w1` >>
        CONV_TAC (RESORT_EXISTS_CONV List.rev) >> qexists_tac`FST r1` >>
        PairCases_on`r1`>>fs[] >>
        qspecl_then[`Cmenv`,`sb`,`enva`,`e2a`,`r2`]mp_tac (CONJUNCT1 Cevaluate_syneq) >> simp[] >>
        disch_then(qspecl_then[`$=`,`Cmenv`,`r10,r11`,`enva`,`e2a`]mp_tac) >> simp[syneq_exp_refl] >>
        fsrw_tac[DNF_ss][FORALL_PROD,Abbr`sb`] >>
        map_every qx_gen_tac[`s2`,`u2`] >> strip_tac >>
        PairCases_on`res`>>fsrw_tac[DNF_ss][EXISTS_PROD] >> rw[] >>
        qspecl_then[`T`,`menv`,`cenv`,`cs'`,`env`,`e2`,`((FST(FST r2),s3),Rval v2)`]mp_tac(CONJUNCT1 evaluate_closed) >>
        simp[] >> strip_tac >>
        Q.ISPECL_THEN[`menv`,`s3`,`s4`,`env`,`Opn opn`,`v1`,`v2`,`env'`,`exp''`]mp_tac do_app_closed >>
        simp[] >> strip_tac >> fs[] >>
        fs[do_app_Opn_SOME] >> rw[] >>
        fs[v_to_Cv_def] >> rw[] >>
        fs[Once syneq_cases] >> rw[] >>
        map_every qexists_tac[`CLitv (IntLit n2)`,`s2`] >>
        simp[] >>
        qpat_assum`P ⇒ Q`mp_tac >>
        discharge_hyps >- rw[] >> strip_tac >>
        qpat_assum`Cevaluate Cmenv X enva (exp_to_Cexp Y Z) R`mp_tac >>
        BasicProvers.CASE_TAC >- (
          simp[exp_to_Cexp_def] >>
          fs[] >> fs[]) >>
        simp[exp_to_Cexp_def] >> strip_tac >>
        simp[] >>
        simp[Abbr`cnt'`,BigStepTheory.dec_count_def] >>
        fs[v_to_Cv_def] >> rw[] >>
        Cases_on`opn`>>fs[]>>
        fs[v_to_Cv_def,opn_lookup_def] >>
        rw[]>>fs[v_to_Cv_def] >>
        metis_tac[EVERY2_syneq_trans]) >>
      srw_tac[DNF_ss][Once Cevaluate_cases] >> disj1_tac >> fs[] >>
      qspecl_then[`T`,`menv`,`cenv`,`cs`,`env`,`e1`,`(cs',Rval v1)`]mp_tac(CONJUNCT1 evaluate_closed) >>
      simp[] >> strip_tac >> fs[] >>
      `closed_under_cenv cenv menv env' s4 ∧ closed_under_cenv cenv menv env (SND cs')` by (
        `(s4 = s3) ∧ (env' = env)` by fs[do_app_Opn_SOME] >>
        imp_res_tac evaluate_closed_under_cenv >> fs[] ) >> fs[] >>
      rpt (first_x_assum (qspec_then `cm` mp_tac)) >>
      rw[] >>
      qmatch_assum_abbrev_tac `syneq (v_to_Cv mv cm v1) w1` >> pop_assum kall_tac >>
      qmatch_assum_rename_tac `syneq (v_to_Cv mv m v2) w2`[] >>
      qmatch_assum_rename_tac`SND r1 = Cval w1`[] >>
      qmatch_assum_rename_tac`SND r2 = Cval w2`[] >>
      qmatch_assum_abbrev_tac`Cevaluate Cmenv sa enva e1a r1` >>
      qmatch_assum_abbrev_tac`Cevaluate Cmenv sb enva e2a r2` >>
      CONV_TAC (RESORT_EXISTS_CONV List.rev) >> qexists_tac`w1` >>
      qexists_tac`FST r1` >>
      PairCases_on`r1`>>fs[] >>
      srw_tac[DNF_ss][Once Cevaluate_cases] >> disj1_tac >> fs[] >>
      qspecl_then[`Cmenv`,`sb`,`enva`,`e2a`,`r2`]mp_tac (CONJUNCT1 Cevaluate_syneq) >> simp[] >>
      disch_then(qspecl_then[`λx y. y = x + 1`,`Cmenv`,`FST cs',r11`,`w1::enva`,`shift 1 0 e2a`]mp_tac) >>
      discharge_hyps >- (
        simp[shift_def,ADD1,EL_CONS,PRE_SUB1,Abbr`sb`] >>
        match_mp_tac mkshift_thm >>
        simp[Abbr`e2a`] >>
        match_mp_tac free_vars_exp_to_Cexp_matchable >>
        simp[Abbr`enva`,env_to_Cenv_MAP] >>
        fsrw_tac[DNF_ss][SUBSET_DEF,MEM_MAP,EXISTS_PROD,MEM_FLAT] >>
        rw[] >> res_tac >> fs[] >> metis_tac[] ) >>
      fsrw_tac[DNF_ss][FORALL_PROD] >>
      map_every qx_gen_tac[`s2`,`u2`] >> strip_tac >>
      PairCases_on`res`>>fsrw_tac[DNF_ss][EXISTS_PROD] >> rw[] >>
      CONV_TAC (RESORT_EXISTS_CONV List.rev) >>
      map_every qexists_tac[`u2`,`s2`,`FST(FST r2)`] >> simp[] >>
      srw_tac[DNF_ss][Once Cevaluate_cases] >> disj1_tac >>
      srw_tac[DNF_ss][Once Cevaluate_cases] >>
      srw_tac[DNF_ss][Once Cevaluate_cases] >>
      srw_tac[DNF_ss][Once Cevaluate_cases] >>
      srw_tac[DNF_ss][Once Cevaluate_cases] >>
      fs [do_app_Opn_SOME] >>
      rw [] >>
      fs [v_to_Cv_def] >>
      rw [] >>
      `u2 = CLitv (IntLit n2)` by fs [syneq_cases] >>
      rw [] >- (
        srw_tac[DNF_ss][Once Cevaluate_cases] >> disj1_tac >>
        srw_tac[DNF_ss][Once Cevaluate_cases] >> 
        srw_tac[DNF_ss][Once Cevaluate_cases] >> 
        Cases_on`opn`>>fs[Abbr`cnt'`,BigStepTheory.dec_count_def]>>
        metis_tac[EVERY2_syneq_trans] ) >>
      srw_tac[DNF_ss][Once Cevaluate_cases] >> disj1_tac >>
      srw_tac[DNF_ss][Once Cevaluate_cases] >> 
      srw_tac[DNF_ss][Once Cevaluate_cases] >> 
      srw_tac[DNF_ss][Once Cevaluate_cases] >-
      decide_tac >>
      rw[] >> fs[v_to_Cv_def,Abbr`cnt'`,BigStepTheory.dec_count_def] >>
      Cases_on`opn`>>Cases_on`n2=0`>>fs[] >>rw[]>>fs[]>>rw[v_to_Cv_def,opn_lookup_def]>>
      metis_tac[EVERY2_syneq_trans] )
    >- (
      qmatch_assum_rename_tac `do_app s3 env (Opb opb) v1 v2 = SOME (s4,env',exp'')` [] >>
      fs[] >>
      Q.PAT_ABBREV_TAC`e1a = exp_to_Cexp X e1`>>
      Q.PAT_ABBREV_TAC`e2a = exp_to_Cexp X e2`>>
      qmatch_assum_rename_tac`evaluate T menv cenv cs env e1 (cs',Rval v1)`[] >>
      qmatch_assum_rename_tac`evaluate T menv cenv cs' env e2 ((count',s2),Rval v2)`[] >>
      qspecl_then[`T`,`menv`,`cenv`,`cs`,`env`,`e1`,`(cs',Rval v1)`]mp_tac(CONJUNCT1 evaluate_closed) >>
      simp[] >> strip_tac >>
      qspecl_then[`T`,`menv`,`cenv`,`cs'`,`env`,`e2`,`((count',s2),Rval v2)`]mp_tac(CONJUNCT1 evaluate_closed) >>
      simp[] >> strip_tac >>
      fs[] >>
      Q.ISPECL_THEN[`menv`,`s2`,`s4`,`env`,`Opb opb`,`v1`,`v2`,`env'`,`exp''`]mp_tac do_app_closed >>
      simp[] >> strip_tac >> fs[] >>
      `closed_under_cenv cenv menv env (SND cs') ∧ closed_under_cenv cenv menv env' s4` by (
        fs[do_app_Opb_SOME] >>
        imp_res_tac evaluate_closed_under_cenv >> rfs[] ) >>
      `all_cns_exp exp'' ⊆ cenv_dom cenv` by (
        qspecl_then[`cenv_dom cenv`,`s2`,`env`,`Opb opb`,`v1`,`v2`]mp_tac(do_app_all_cns) >>
        simp[] >>
        discharge_hyps >- (
          qspecl_then[`T`,`menv`,`cenv`,`cs'`,`env`,`e2`,`(count',s2),Rval v2`]mp_tac(evaluate_closed_under_cenv) >>
          qspecl_then[`T`,`menv`,`cenv`,`cs`,`env`,`e1`,`cs',Rval v1`]mp_tac(evaluate_closed_under_cenv) >>
          simp[] >> strip_tac >> strip_tac >>
          fsrw_tac[DNF_ss][SUBSET_DEF,closed_under_cenv_def] >>
          metis_tac[] ) >>
        simp[] ) >>
      fs[] >>
      rpt (first_x_assum (qspec_then `cm` mp_tac)) >> rw[] >>
      qmatch_assum_abbrev_tac `syneq (v_to_Cv mv cm v1) w1` >> pop_assum kall_tac >>
      qmatch_assum_rename_tac `syneq (v_to_Cv mv m v2) w2`[] >>
      Cases_on`Cres`>> Cases_on`Cres'`>> Cases_on`Cres''`>>fs[]>>rw[]>>
      qunabbrev_tac`cnt'` >>
      fs[do_app_Opb_SOME]>>rw[]>>fs[v_to_Cv_def]>>rw[]>>fs[]>>rw[]>>
      fs[v_to_Cv_def]>>fs[]>>rw[]>>
      fs[exp_to_Cexp_def,BigStepTheory.dec_count_def]>>rw[]>>
      qmatch_assum_rename_tac`FST x = FST y`[] >>
      PairCases_on`y`>>fs[] >> rw[] >>
      qabbrev_tac`sa = MAP (v_to_Cv mv m) (SND cs)` >>
      qabbrev_tac`sb = MAP (v_to_Cv mv m) (SND cs')` >>
      qabbrev_tac`sc = MAP (v_to_Cv mv m) s2` >> fs[]>>rw[]>>
      qabbrev_tac`enva = env_to_Cenv mv m env`>>
      qabbrev_tac`w1 = CLitv (IntLit n1)`>>
      qabbrev_tac`w2 = CLitv (IntLit n2)`>>
      qmatch_assum_rename_tac`FST cs' = FST y`[] >>
      PairCases_on`y`>>fs[]>>rw[]>>
      qmatch_assum_rename_tac`EVERY2 (syneq) sb sd`[]>>
      PairCases_on`x`>>fs[]>>rw[]>>
      qmatch_assum_rename_tac`EVERY2 (syneq) sc se`[]>>
      Q.PAT_ABBREV_TAC`Cmenv:string |-> Cv list = X o_f Y` >>
      Cases_on `opb` >> fsrw_tac[DNF_ss][EXISTS_PROD,opb_lookup_def]
      >- (
        rw[Once Cevaluate_cases] >>
        rw[Once (CONJUNCT2 Cevaluate_cases)] >>
        rw[Once (CONJUNCT2 Cevaluate_cases)] >>
        rw[Once (CONJUNCT2 Cevaluate_cases)] >>
        srw_tac[DNF_ss][] >>
        CONV_TAC (RESORT_EXISTS_CONV List.rev) >> qexists_tac`FST cs',sd` >>
        CONV_TAC SWAP_EXISTS_CONV >> qexists_tac`w1` >>
        qspecl_then[`Cmenv`,`FST cs',sb`,`enva`,`e2a`,`((x0,se),Cval w2)`]mp_tac(CONJUNCT1 Cevaluate_syneq) >> simp[] >>
        disch_then(qspecl_then[`$=`,`Cmenv`,`FST cs',sd`,`enva`,`e2a`]mp_tac) >>
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
        map_every qexists_tac [`w1`,`FST cs',sd`] >> fs[] >>
        rw[Once Cevaluate_cases] >>
        srw_tac[DNF_ss][] >>
        qspecl_then[`Cmenv`,`FST cs',sb`,`enva`,`e2a`,`((x0,se),Cval w2)`]mp_tac(CONJUNCT1 Cevaluate_syneq) >> simp[] >>
        disch_then(qspecl_then[`λv1 v2. v2 = v1 + 1`,`Cmenv`,`FST cs',sd`,`w1::enva`,`shift 1 0 e2a`]mp_tac) >>
        discharge_hyps >- (
          conj_tac >- (
            simp[shift_def] >>
            match_mp_tac mkshift_thm >>
            simp[ADD1,Abbr`enva`,Abbr`e2a`,env_to_Cenv_MAP] >>
            match_mp_tac free_vars_exp_to_Cexp_matchable >>
            simp[] >>
            fsrw_tac[DNF_ss][SUBSET_DEF,MEM_MAP,MEM_FLAT] >> rfs[] >>
            fsrw_tac[DNF_ss][EXISTS_PROD] >> rw[] >> res_tac >> fs[] >> metis_tac[]) >>
          lrw[EL_CONS,PRE_SUB1] ) >>
        fsrw_tac[DNF_ss][FORALL_PROD] >>
        map_every qx_gen_tac[`sf`,`w3`] >> strip_tac >>
        CONV_TAC (RESORT_EXISTS_CONV List.rev) >>
        map_every qexists_tac [`w3`,`x0,sf`,`sf`] >> fs[] >>
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
        map_every qexists_tac[`FST cs',sd`,`w2`,`w1`] >>
        qspecl_then[`Cmenv`,`FST cs',sb`,`enva`,`e2a`,`((x0,se),Cval w2)`]mp_tac(CONJUNCT1 Cevaluate_syneq) >> simp[] >>
        disch_then(qspecl_then[`$=`,`Cmenv`,`FST cs',sd`,`enva`,`e2a`]mp_tac) >> simp[syneq_exp_refl] >>
        fsrw_tac[DNF_ss][FORALL_PROD,Abbr`w2`,Abbr`w1`] >>
        qx_gen_tac`sf` >> strip_tac >>
        qexists_tac`sf`>>
        reverse conj_tac >- metis_tac[EVERY2_syneq_trans] >>
        rw[] >> ARITH_TAC )
      >- (
        rw[Once Cevaluate_cases] >>
        srw_tac[DNF_ss][] >>
        CONV_TAC (RESORT_EXISTS_CONV List.rev) >>
        map_every qexists_tac [`w1`,`FST cs',sd`] >> fs[] >>
        rw[Once Cevaluate_cases] >>
        srw_tac[DNF_ss][] >>
        qspecl_then[`Cmenv`,`FST cs',sb`,`enva`,`e2a`,`((x0,se),Cval w2)`]mp_tac(CONJUNCT1 Cevaluate_syneq) >> simp[] >>
        disch_then(qspecl_then[`λv1 v2. v2 = v1 + 1`,`Cmenv`,`FST cs',sd`,`w1::enva`,`shift 1 0 e2a`]mp_tac) >>
        discharge_hyps >- (
          conj_tac >- (
            simp[shift_def] >>
            match_mp_tac mkshift_thm >>
            simp[ADD1,Abbr`enva`,Abbr`e2a`,env_to_Cenv_MAP] >>
            match_mp_tac free_vars_exp_to_Cexp_matchable >>
            simp[] >>
            fsrw_tac[DNF_ss][SUBSET_DEF,MEM_MAP,MEM_FLAT] >> rfs[] >>
            fsrw_tac[DNF_ss][EXISTS_PROD] >> rw[] >> res_tac >> fs[] >> metis_tac[]) >>
          lrw[EL_CONS,PRE_SUB1] ) >>
        fsrw_tac[DNF_ss][FORALL_PROD] >>
        map_every qx_gen_tac[`sf`,`w3`] >> strip_tac >>
        CONV_TAC (RESORT_EXISTS_CONV List.rev) >>
        map_every qexists_tac [`w3`,`x0,sf`,`sf`] >> fs[] >>
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
        lrw[ADD1] >- ARITH_TAC >>
        metis_tac[EVERY2_syneq_trans]) )
    >- (
      rw[Once Cevaluate_cases] >>
      rw[Once Cevaluate_cases] >>
      srw_tac[DNF_ss][] >>
      disj1_tac >>
      rw[Once(CONJUNCT2 Cevaluate_cases)] >>
      rw[Once(CONJUNCT2 Cevaluate_cases)] >>
      rw[Once(CONJUNCT2 Cevaluate_cases)] >>
      srw_tac[DNF_ss][] >> fs[] >>
      qspecl_then[`T`,`menv`,`cenv`,`cs`,`env`,`e1`,`(cs',Rval v1)`]mp_tac(CONJUNCT1 evaluate_closed) >>
      simp[]>>strip_tac >>
      qspecl_then[`T`,`menv`,`cenv`,`cs'`,`env`,`e2`,`((count',s3),Rval v2)`]mp_tac(CONJUNCT1 evaluate_closed) >>
      simp[]>>strip_tac >>
      Q.ISPECL_THEN[`menv`,`s3`,`s4`,`env`,`Equality`,`v1`,`v2`,`env'`,`exp''`]mp_tac do_app_closed >>
      simp[]>>strip_tac>> fs[] >>
      `closed_under_cenv cenv menv env' s4 ∧ closed_under_cenv cenv menv env (SND cs')` by (
        fs[bigClockTheory.do_app_cases] >> imp_res_tac evaluate_closed_under_cenv >> rfs[] >>
        rw[] >> rfs[] >> rw[] >> fs[] >> metis_tac[FST, optionTheory.SOME_11, PAIR_EQ]) >> fs[] >>
      `all_cns_exp exp'' ⊆ cenv_dom cenv` by (
        qspecl_then[`cenv_dom cenv`,`s3`,`env`,`Equality`,`v1`,`v2`]mp_tac do_app_all_cns >>
        simp[] >> discharge_hyps >- (
          qspecl_then[`T`,`menv`,`cenv`,`cs`,`env`,`e1`,`cs',Rval v1`]mp_tac(CONJUNCT1 evaluate_all_cns) >>
          qspecl_then[`T`,`menv`,`cenv`,`cs'`,`env`,`e2`,`(count',s3),Rval v2`]mp_tac(CONJUNCT1 evaluate_all_cns) >>
          fs[closed_under_cenv_def] >>
          discharge_hyps >- metis_tac[] >> strip_tac >>
          discharge_hyps >- metis_tac[] >> strip_tac >>
          simp[] >> fsrw_tac[DNF_ss][SUBSET_DEF] >> metis_tac[] ) >>
        simp[]) >>
      rpt (first_x_assum (qspec_then `cm` mp_tac)) >>
      rw[EXISTS_PROD] >>
      qmatch_assum_abbrev_tac `syneq(v_to_Cv mv cm v1) w1` >> pop_assum kall_tac >>
      qmatch_assum_rename_tac `syneq(v_to_Cv mv m v2) w2`[] >>
      qabbrev_tac`sa = MAP (v_to_Cv mv m) (SND cs)` >>
      qabbrev_tac`sb = MAP (v_to_Cv mv m) (SND cs')` >>
      qabbrev_tac`sc = MAP (v_to_Cv mv m) s3` >>
      qmatch_assum_abbrev_tac`Cevaluate Cmenv (FST cs,sa) enva e1a X` >>
      qmatch_assum_rename_tac`Abbrev(X=((FST cs',sd),Cval w1))`[]>> qunabbrev_tac`X` >>
      qmatch_assum_abbrev_tac`Cevaluate Cmenv (FST cs',sb) enva e2a X` >>
      qmatch_assum_rename_tac`Abbrev(X=((cnte,se),Cval w2))`[]>>
      qspecl_then[`Cmenv`,`FST cs',sb`,`enva`,`e2a`,`X`]mp_tac(CONJUNCT1 Cevaluate_syneq) >> simp[] >>
      disch_then(qspecl_then[`$=`,`Cmenv`,`FST cs',sd`,`enva`,`e2a`]mp_tac) >> simp[syneq_exp_refl] >>
      fsrw_tac[DNF_ss][EXISTS_PROD,FORALL_PROD,Abbr`X`] >>
      map_every qx_gen_tac[`sf`,`w3`] >> strip_tac >>
      fs[do_app_def] >>
      `(s3 = s4) ∧ (env = env')` 
                 by (Cases_on `do_eq v1 v2` >>
                     fs []) >>
      `(FST res = (cnt',s4))` 
                by (Cases_on `do_eq v1 v2` >>
                    fs [] >>
                    rw [] >>
                    fs [Once BigStepTheory.evaluate_cases]) >>
      rpt BasicProvers.VAR_EQ_TAC >>
      fs[] >>
      rpt BasicProvers.VAR_EQ_TAC >>
      Cases_on `do_eq v1 v2` >>
      fs [] >>
      rpt BasicProvers.VAR_EQ_TAC >>
      `all_cns v2 ⊆ cenv_dom cenv ∧ all_cns v1 ⊆ cenv_dom cenv` 
                 by (imp_res_tac evaluate_closed_under_cenv >>
                     fs []  >>
                     rw [every_result_rwt]) >- (
        map_every qexists_tac [`sf`, `Cval (CLitv (Bool b))`, `cnte`, `sf`, `CLitv (Bool b)`, `w1`, `w3`, `FST cs'`, `sd`] >>
        fs [] >>
        `do_Ceq w1 w3 = Eq_val b` by metis_tac [do_eq_to_do_Ceq, do_Ceq_syneq1, do_Ceq_syneq2] >>
        fs [] >>
        simp [Once Cevaluate_cases, v_to_Cv_def] >>
        simp [Once Cevaluate_cases] >>
        fs[exp_to_Cexp_def,Abbr`cnt'`,BigStepTheory.dec_count_def]  >>
        metis_tac[EVERY2_syneq_trans]) >>
      map_every qexists_tac [`sf`, `Cexc (Craise CEq_excv)`, `cnte`, `sf`, `CLitv (IntLit 0)`, `w1`, `w3`, `FST cs'`, `sd`] >>
      fs [] >>
      `do_Ceq w1 w3 = Eq_closure` by metis_tac [do_eq_to_do_Ceq, do_Ceq_syneq1, do_Ceq_syneq2] >>
      fs [] >>
      simp [Once Cevaluate_cases] >>
      `LIST_REL syneq sc sf` by metis_tac [EVERY2_syneq_trans] >>
      simp [] >> disj1_tac >>
      simp [Once Cevaluate_cases] >>
      simp [Once Cevaluate_cases] >> disj1_tac >>
      simp [Once Cevaluate_cases] >>
      simp [Once Cevaluate_cases] >>
      fs[exp_to_Cexp_def,Abbr`cnt'`,BigStepTheory.dec_count_def])
  >- (
      rw[Once Cevaluate_cases] >>
      srw_tac[DNF_ss][] >>
      disj1_tac >>
      rw[Once(CONJUNCT2 Cevaluate_cases)]>>
      rw[Once(CONJUNCT2 Cevaluate_cases)]>>
      fsrw_tac[DNF_ss][] >>
      qspecl_then[`T`,`menv`,`cenv`,`cs`,`env`,`e1`,`(cs',Rval v1)`]mp_tac(CONJUNCT1 evaluate_closed) >>
      simp[] >> strip_tac >>
      qspecl_then[`T`,`menv`,`cenv`,`cs'`,`env`,`e2`,`((count',s3),Rval v2)`]mp_tac(CONJUNCT1 evaluate_closed) >>
      simp[] >> strip_tac >>
      Q.ISPECL_THEN[`menv`,`s3`,`s4`,`env`,`Opapp`,`v1`,`v2`,`env'`,`exp''`]mp_tac do_app_closed >>
      simp[] >> strip_tac >>
      fs[] >>
      `closed_under_cenv cenv menv env (SND cs') ∧ closed_under_cenv cenv menv env' s4` by (
        qspecl_then[`T`,`menv`,`cenv`,`cs`,`env`,`e1`,`(cs',Rval v1)`]mp_tac(CONJUNCT1 evaluate_all_cns) >>
        qspecl_then[`T`,`menv`,`cenv`,`cs`,`env`,`e1`,`(cs',Rval v1)`]mp_tac(evaluate_closed_under_cenv) >>
        qspecl_then[`T`,`menv`,`cenv`,`cs'`,`env`,`e2`,`((count',s3),Rval v2)`]mp_tac(CONJUNCT1 evaluate_all_cns) >>
        qspecl_then[`T`,`menv`,`cenv`,`cs'`,`env`,`e2`,`((count',s3),Rval v2)`]mp_tac(evaluate_closed_under_cenv) >>
        rpt(first_x_assum(qspec_then`cm`kall_tac)) >>
        simp[] >>
        fs[do_app_Opapp_SOME] >> rw[] >>fs[] >- (
          fsrw_tac[DNF_ss][closed_under_cenv_def,bind_def] >> rw[] >>
          rfs[] >> fsrw_tac[DNF_ss][SUBSET_DEF] >> metis_tac[] ) >>
        fsrw_tac[DNF_ss][closed_under_cenv_def,bind_def] >>
        simp[build_rec_env_MAP,MEM_MAP] >>
        fsrw_tac[DNF_ss][UNCURRY] >>
        rfs[] >> fsrw_tac[DNF_ss][SUBSET_DEF,MEM_FLAT,MEM_MAP] >>
        metis_tac[] ) >> fs[] >>
      `all_cns_exp exp'' ⊆ cenv_dom cenv` by (
        qspecl_then[`cenv_dom cenv`,`s3`,`env`,`Opapp`,`v1`,`v2`]mp_tac do_app_all_cns >> simp[] >>
        discharge_hyps >- (
          qspecl_then[`T`,`menv`,`cenv`,`cs`,`env`,`e1`,`cs',Rval v1`]mp_tac(CONJUNCT1 evaluate_all_cns)>>
          simp[] >> fs[closed_under_cenv_def] >>
          discharge_hyps >- metis_tac[] >> simp[] >> strip_tac >>
          qspecl_then[`T`,`menv`,`cenv`,`cs'`,`env`,`e2`,`(count',s3),Rval v2`]mp_tac(CONJUNCT1 evaluate_all_cns)>> simp[]>>
          discharge_hyps >- metis_tac[] >> simp[] >> strip_tac >>
          simp[] >> fsrw_tac[DNF_ss][SUBSET_DEF] >> metis_tac[] ) >>
        simp[]) >>
      rpt (first_x_assum (qspec_then `cm` mp_tac)) >>
      srw_tac[DNF_ss][EXISTS_PROD] >>
      qmatch_assum_abbrev_tac `syneq(v_to_Cv mv cm v1) w1` >> pop_assum kall_tac >>
      qmatch_assum_rename_tac `syneq(v_to_Cv mv cm v2) w2`[] >>
      qmatch_assum_abbrev_tac`Cevaluate Cmenv (FST cs,sa) enva e1a ((FST cs',sd),Cval w1)`>>
      pop_assum kall_tac >>
      qmatch_assum_abbrev_tac`Cevaluate Cmenv (FST cs',sb) enva e2a ((cnte,se),Cval w2)`>>
      ntac 2 (pop_assum kall_tac) >>
      qmatch_assum_abbrev_tac`EVERY2 (syneq) sc se` >>
      qspecl_then[`Cmenv`,`(FST cs',sb)`,`enva`,`e2a`,`((cnte,se),Cval w2)`]mp_tac(CONJUNCT1 Cevaluate_syneq) >> simp[] >>
      disch_then(qspecl_then[`$=`,`Cmenv`,`(FST cs',sd)`,`enva`,`e2a`]mp_tac) >>
      simp[syneq_exp_refl,EXISTS_PROD] >>
      fsrw_tac[DNF_ss][] >>
      map_every qx_gen_tac[`sf`,`w3`] >> strip_tac >>
      CONV_TAC (RESORT_EXISTS_CONV List.rev) >>
      map_every qexists_tac[`w3`,`sf`,`cnte`] >>
      `∃env1 defs n. w1 = CRecClos env1 defs n` by (
        imp_res_tac do_Opapp_SOME_CRecClos >> rw[] ) >>
      CONV_TAC (RESORT_EXISTS_CONV (fn ls => List.drop(ls,2)@List.take(ls,2))) >>
      map_every qexists_tac[`n`,`defs`,`env1`,`sd`,`FST cs'`] >>
      rw[] >>
      `set (free_vars e1a) ⊆ count (LENGTH enva)` by (
        qmatch_assum_abbrev_tac`Abbrev(e1a = exp_to_Cexp m' e1)` >>
        Q.ISPECL_THEN[`m'`,`e1`]mp_tac free_vars_exp_to_Cexp >>
        simp[Abbr`m'`,Abbr`enva`,env_to_Cenv_MAP] >>
        fsrw_tac[DNF_ss][SUBSET_DEF,MEM_FLAT,MEM_MAP] >> rfs[] >>
        rw[] >> first_x_assum (match_mp_tac o MP_CANON) >> rw[] >>
        res_tac >> fs[] >> metis_tac[]) >>
      `EVERY (Cclosed) sa` by (
        simp[Abbr`sa`,EVERY_MAP] >>
        fs[EVERY_MEM] >> PROVE_TAC[v_to_Cv_closed]) >>
      `EVERY (Cclosed) enva` by (
        simp[Abbr`enva`,env_to_Cenv_MAP,EVERY_MAP] >>
        fs[EVERY_MEM,MEM_MAP,FORALL_PROD,EXISTS_PROD] >>
        metis_tac[v_to_Cv_closed] ) >>
      qspecl_then[`Cmenv`,`FST cs,sa`,`enva`,`e1a`,`(FST cs',sd),Cval (CRecClos env1 defs n)`]mp_tac(CONJUNCT1 Cevaluate_closed)>>
      simp[] >>
      simp[Q.SPECL[`CRecClos env1 defs n`]Cclosed_cases] >>
      discharge_hyps >- (
        rw[Abbr`e1a`,Abbr`Cmenv`,IN_FRANGE] >>
        simp[o_f_FAPPLY,env_to_Cenv_MAP] >>
        fsrw_tac[DNF_ss][EVERY_MEM,MEM_MAP,FORALL_PROD,EXISTS_PROD] >>
        rw[] >>
        match_mp_tac (CONJUNCT1 v_to_Cv_closed) >>
        `k ∈ FDOM (alist_to_fmap menv)` by (rw[MEM_MAP,EXISTS_PROD] >> PROVE_TAC[]) >>
        imp_res_tac alist_to_fmap_FAPPLY_MEM >>
        metis_tac[] ) >>
      strip_tac >>
      `∃b. EL n defs = (NONE,1,b)` by (
        qspecl_then[`Cmenv`,`FST cs,sa`,`enva`,`e1a`,`((FST cs',sd),Cval (CRecClos env1 defs n))`]mp_tac(CONJUNCT1 Cevaluate_no_vlabs) >>
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
          metis_tac[] ) >>
        fs[] >>
        simp[EL_MAP,syneq_cb_aux_def,UNCURRY] ) >>
      simp[] >>
      fs[do_app_Opapp_SOME] >- (
        rw[] >> fs[v_to_Cv_def,LET_THM] >>
        fs[Q.SPECL[`c`,`CRecClos env1 defs zz`]syneq_cases] >>
        rator_x_assum`syneq_defs`mp_tac >>
        Q.PAT_ABBREV_TAC`env0 = env_to_Cenv mv cm Z` >>
        Q.PAT_ABBREV_TAC`defs0 = [X]:def list` >>
        qabbrev_tac`cl = CRecClos env0 defs0 0` >>
        simp[Once syneq_exp_cases]>>
        simp[] >> strip_tac >>
        first_assum(qspecl_then[`0`,`n`]mp_tac) >>
        simp_tac(srw_ss())[Abbr`defs0`] >>
        simp[syneq_cb_aux_def] >>
        strip_tac >>
        fs[bind_def] >>
        qmatch_assum_abbrev_tac`Cevaluate Cmenv (kc,sc) envc expc resc` >>
        qspecl_then[`Cmenv`,`kc,sc`,`envc`,`expc`,`resc`]mp_tac(CONJUNCT1 Cevaluate_syneq) >>
        simp[] >>
        Q.PAT_ABBREV_TAC`envf = w3::ls` >>
        qmatch_assum_abbrev_tac`syneq_exp z1 z2 U (shift 1 1 expc) x1`>>
        fs[env_to_Cenv_MAP] >>
        qunabbrev_tac`envc` >>
        Q.PAT_ABBREV_TAC`envc:Cv list = MAP f env''` >>
        disch_then(qspecl_then[`λv1 v2. if v1 < 1 then (v2 = v1) else v2 = v1 + 1`,`Cmenv`,`kc,sf`,`w2::cl::envc`,`shift 1 1 expc`]mp_tac) >>
        discharge_hyps >- (
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
          simp[] >>
          metis_tac[EVERY2_syneq_trans] ) >>
        disch_then(Q.X_CHOOSE_THEN`resd`strip_assume_tac) >>
        qspecl_then[`Cmenv`,`kc,sf`,`w2::cl::envc`,`shift 1 1 expc`,`resd`]mp_tac(CONJUNCT1 Cevaluate_syneq) >>
        simp[] >>
        disch_then(qspecl_then[`U`,`Cmenv`,`kc,sf`,`envf`,`x1`]mp_tac) >>
        discharge_hyps >- (
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
        simp[EXISTS_PROD] >>
        qunabbrev_tac`resc`>>fs[]>>
        simp[Abbr`kc`,Abbr`cnt'`,BigStepTheory.dec_count_def] >>
        metis_tac[EVERY2_syneq_trans,Cresult_rel_syneq_trans] ) >>
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
      Q.PAT_ABBREV_TAC`env0 = env_to_Cenv mv cm Z` >>
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
      qmatch_assum_abbrev_tac`Cevaluate Cmenv (kc,sc) envc Cexp resc` >>
      strip_tac >>
      qspecl_then[`Cmenv`,`kc,sc`,`envc`,`Cexp`,`resc`]mp_tac(CONJUNCT1 Cevaluate_syneq) >>
      simp[] >>
      Q.PAT_ABBREV_TAC`envf = w3::ls` >>
      qmatch_assum_abbrev_tac`syneq_exp z1 z2 U Cexp ef`>>
      fs[env_to_Cenv_MAP] >>
      qunabbrev_tac`envc` >>
      fs[build_rec_env_MAP,MAP_MAP_o,combinTheory.o_DEF,UNCURRY] >>
      disch_then(qspecl_then[`U`,`Cmenv`,`kc,sf`,`envf`,`ef`]mp_tac) >>
      discharge_hyps >- (
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
        simp[] >>
        metis_tac[EVERY2_syneq_trans] ) >>
      simp[EXISTS_PROD] >>
      qunabbrev_tac`resc`>>fs[]>>
      simp[Abbr`kc`,Abbr`cnt'`,BigStepTheory.dec_count_def] >>
      metis_tac[EVERY2_syneq_trans,Cresult_rel_syneq_trans] )
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
      qspecl_then[`T`,`menv`,`cenv`,`cs`,`env`,`e1`,`(cs',Rval (Loc n))`]mp_tac(CONJUNCT1 evaluate_closed) >>
      simp[]>>strip_tac >> fs[] >>
      fs[store_assign_def] >> rw[] >> fs[] >> rw[] >>
      qspecl_then[`T`,`menv`,`cenv`,`cs'`,`env`,`e2`,`((count',s3),Rval v2)`]mp_tac(CONJUNCT1 evaluate_closed) >>
      simp[]>>strip_tac >>
      `EVERY (closed menv) (LUPDATE v2 n s3)` by (
        fs[EVERY_MEM] >>
        metis_tac[MEM_LUPDATE] ) >>
      fs[] >>
      `closed_under_cenv cenv menv env (SND cs') ∧ closed_under_cenv cenv menv env (LUPDATE v2 n s3)` by (
        qspecl_then[`T`,`menv`,`cenv`,`cs`,`env`,`e1`,`(cs',Rval (Loc n))`]mp_tac(evaluate_closed_under_cenv) >>
        qspecl_then[`T`,`menv`,`cenv`,`cs'`,`env`,`e2`,`((count',s3),Rval v2)`]mp_tac(evaluate_closed_under_cenv) >>
        simp[] >> rw[] >>
        fsrw_tac[DNF_ss][closed_under_cenv_def] >>
        rw[] >>
        imp_res_tac MEM_LUPDATE >> fs[] >>
        qspecl_then[`T`,`menv`,`cenv`,`cs'`,`env`,`e2`,`((count',s3),Rval v2)`]mp_tac(CONJUNCT1 evaluate_all_cns) >>
        simp[] >> disch_then match_mp_tac >>
        fsrw_tac[DNF_ss][] ) >> fs[] >>
      rpt (first_x_assum (qspec_then`cm`mp_tac)) >>
      fsrw_tac[DNF_ss][EXISTS_PROD] >> rw[] >>
      fs[v_to_Cv_def,exp_to_Cexp_def] >>
      rw[] >> fs[] >> rw[] >>
      CONV_TAC SWAP_EXISTS_CONV >> qexists_tac`CLoc n` >> rw[] >>
      qmatch_assum_abbrev_tac`Cevaluate Cmenv sa enva e1a ((FST cs',sd),Cval (CLoc n))` >>
      pop_assum kall_tac >>
      qmatch_assum_abbrev_tac`Cevaluate Cmenv sb enva e2a ((ke,se),w1)` >>
      qpat_assum`Abbrev (se  = X)`kall_tac >>
      qpat_assum`Abbrev (ke  = X)`kall_tac >>
      qspecl_then[`Cmenv`,`sb`,`enva`,`e2a`,`((ke,se),w1)`]mp_tac(CONJUNCT1 Cevaluate_syneq) >> simp[] >>
      disch_then(qspecl_then[`$=`,`Cmenv`,`FST sb,sd`,`enva`,`e2a`]mp_tac) >> simp[syneq_exp_refl] >>
      fsrw_tac[DNF_ss][FORALL_PROD,Abbr`sb`] >>
      map_every qx_gen_tac[`sf`,`w2`] >>
      strip_tac >>
      fs[Abbr`w1`] >> rw[] >>
      qmatch_assum_rename_tac`syneq w1 w2`[] >>
      simp[Abbr`cnt'`,BigStepTheory.dec_count_def]>>
      map_every qexists_tac[`sf`,`w2`,`LUPDATE w2 n sf`,`FST cs'`,`sd`] >>
      simp[] >>
      fs[EVERY2_EVERY] >>
      fs[EVERY_MEM,FORALL_PROD] >>
      rpt(qpat_assum`LENGTH X = Y`mp_tac) >> ntac 3 strip_tac >>
      fs[MEM_ZIP] >> fsrw_tac[DNF_ss][] >>
      gen_tac >> strip_tac >>
      simp[EL_LUPDATE,EL_MAP] >>
      rw[] >>
      metis_tac[syneq_trans,EL_MAP])) >>
  strip_tac >- (
    rw[] >> fs[] >>
    qspecl_then[`T`,`menv`,`cenv`,`cs`,`env`,`exp`,`(cs',Rval v1)`]mp_tac(CONJUNCT1 evaluate_closed) >>
    simp[] >> strip_tac >>
    qspecl_then[`T`,`menv`,`cenv`,`cs'`,`env`,`exp'`,`((0,s3),Rval v2)`]mp_tac(CONJUNCT1 evaluate_closed) >>
    simp[] >> strip_tac >>
    Q.ISPECL_THEN[`menv`,`s3`,`s4`,`env`,`Opapp`,`v1`,`v2`,`env'`,`e3`]mp_tac do_app_closed >>
    simp[] >> strip_tac >> fs[] >>
    `closed_under_cenv cenv menv env (SND cs')` by (
      qspecl_then[`T`,`menv`,`cenv`,`cs`,`env`,`exp`,`(cs',Rval v1)`]mp_tac(evaluate_closed_under_cenv) >>
      qspecl_then[`T`,`menv`,`cenv`,`cs'`,`env`,`exp'`,`((0,s3),Rval v2)`]mp_tac(evaluate_closed_under_cenv) >>
      rpt(first_x_assum(qspec_then`cm`kall_tac)) >>
      simp[]) >> fs[] >>
    rpt (first_x_assum (qspec_then `cm` mp_tac)) >>
    simp[EXISTS_PROD] >>
    simp_tac(srw_ss()++DNF_ss)[] >>
    map_every qx_gen_tac [`sa`,`w1`,`sb`,`w2`] >>
    strip_tac >> strip_tac >>
    simp[exp_to_Cexp_def] >>
    srw_tac[DNF_ss][Once Cevaluate_cases] >>
    disj2_tac >> disj1_tac >>
    `s4 = s3` by fs[do_app_Opapp_SOME] >> rw[] >>
    `∃cenv defs n. w1 = CRecClos cenv defs n ∧ n < LENGTH defs` by (
      fs[do_app_Opapp_SOME] >> rw[] >> fs[v_to_Cv_def,LET_THM] >>
      qpat_assum`syneq X w1`mp_tac >> simp[Once syneq_cases] >> rw[] >>
      qsuff_tac`F`>-rw[] >>
      qpat_assum`LENGTH (defs_to_Cdefs X Y) ≤ Z`mp_tac >>
      simp[NOT_LESS_EQUAL] >>
      qmatch_abbrev_tac `X < Y` >>
      qsuff_tac`(λx. x < Y) X` >- rw[] >>
      unabbrev_all_tac >>
      match_mp_tac the_find_index_suff >>
      simp[] >>
      imp_res_tac ALOOKUP_MEM >>
      simp[MEM_MAP,EXISTS_PROD,defs_to_Cdefs_MAP] >>
      PROVE_TAC[] ) >>
    simp[Once(CONJUNCT2 Cevaluate_cases)] >>
    simp[Once(CONJUNCT2 Cevaluate_cases)] >>
    simp_tac(srw_ss()++DNF_ss)[] >>
    qmatch_assum_abbrev_tac`Cevaluate menvc sc envc expc (sc',Cval w2)` >>
    qspecl_then[`menvc`,`sc`,`FST cs',sa`,`envc`,`expc`,`(sc',Cval w2)`]mp_tac Cevaluate_any_syneq_store >>
    simp[Abbr`sc`,EXISTS_PROD,Abbr`sc'`] >>
    srw_tac[DNF_ss][] >>
    metis_tac[EVERY2_syneq_trans] ) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    ntac 4 gen_tac >>
    Cases >> fs[exp_to_Cexp_def] >>
    qx_gen_tac `e1` >>
    qx_gen_tac `e2` >>
    rpt gen_tac >>
    rw[LET_THM] >- (
      Q.PAT_ABBREV_TAC`sum = opn_to_prim2 X` >>
      Cases_on`sum`>>simp[] >- (
        rw[Once Cevaluate_cases] >>
        fsrw_tac[DNF_ss][EXISTS_PROD] >>
        disj2_tac >>
        rw[Once(CONJUNCT2 Cevaluate_cases)] >>
        rw[Once(CONJUNCT2 Cevaluate_cases)] >>
        rw[Once(CONJUNCT2 Cevaluate_cases)] >>
        fsrw_tac[DNF_ss][] >>
        qspecl_then[`T`,`menv`,`cenv`,`cs`,`env`,`e1`,`(cs',Rval v1)`]mp_tac(CONJUNCT1 evaluate_closed) >>
        qspecl_then[`T`,`menv`,`cenv`,`cs`,`env`,`e1`,`(cs',Rval v1)`]mp_tac(evaluate_closed_under_cenv) >>
        simp[] >> strip_tac >> fs[] >> strip_tac >> fs[] >>
        rpt (first_x_assum (qspec_then `cm` mp_tac)) >>
        rw[] >>
        disj2_tac >>
        qmatch_assum_abbrev_tac `syneq (v_to_Cv mv cm v1) w1` >> pop_assum kall_tac >>
        qmatch_assum_abbrev_tac `Cevaluate Cmenv (FST cs',sb) enva e2a ((FST s3,sc),er)`>>
        pop_assum kall_tac >> pop_assum kall_tac >>
        qmatch_assum_rename_tac `EVERY2 (syneq) sb sd`[] >>
        qspecl_then[`Cmenv`,`FST cs',sb`,`FST cs',sd`,`enva`,`e2a`,`((FST s3,sc),er)`]mp_tac Cevaluate_any_syneq_store >>
        simp[] >>
        fsrw_tac[DNF_ss][FORALL_PROD] >>
        qx_gen_tac`se` >> strip_tac >> strip_tac >>
        CONV_TAC (RESORT_EXISTS_CONV List.rev) >>
        map_every qexists_tac[`w1`,`FST cs',sd`] >> simp[] >>
        Cases_on`err`>>fs[]>-(
          Cases_on`e`>>fs[] >>
          fs[Q.SPEC`CConv X []`syneq_cases] >>
          rw[] >> fs[] >> fs[Q.SPEC`CConv X []`syneq_cases] >>
          metis_tac[EVERY2_syneq_trans]) >>
        rw[] >> fs[] >> rw[] >>
        metis_tac[EVERY2_syneq_trans] ) >>
      srw_tac[DNF_ss][Once Cevaluate_cases] >> disj1_tac >> fs[] >>
      qspecl_then[`T`,`menv`,`cenv`,`cs`,`env`,`e1`,`(cs',Rval v1)`]mp_tac(CONJUNCT1 evaluate_closed) >>
      simp[] >> strip_tac >> fs[] >>
      `closed_under_cenv cenv menv env (SND cs')` by (
        imp_res_tac evaluate_closed_under_cenv >> fs[] ) >> fs[] >>
      rpt (first_x_assum (qspec_then `cm` mp_tac)) >>
      rw[] >>
      qmatch_assum_abbrev_tac `syneq (v_to_Cv mv cm v1) w1` >> pop_assum kall_tac >>
      qmatch_assum_rename_tac`SND r1 = Cval w1`[] >>
      qmatch_assum_abbrev_tac`Cevaluate Cmenv (FST cs,sa) enva e1a r1` >>
      qmatch_assum_abbrev_tac`Cevaluate Cmenv (FST cs',sb) enva e2a r2` >>
      pop_assum kall_tac >>
      PairCases_on`r1`>>fs[] >>
      qmatch_assum_rename_tac `EVERY2 syneq sb sd`[] >>
      CONV_TAC (RESORT_EXISTS_CONV List.rev) >>
      map_every qexists_tac[`w1`,`FST cs',sd`] >>
      srw_tac[DNF_ss][Once Cevaluate_cases] >> disj2_tac >>
      qspecl_then[`Cmenv`,`FST cs',sb`,`enva`,`e2a`,`r2`]mp_tac (CONJUNCT1 Cevaluate_syneq) >> simp[] >>
      disch_then(qspecl_then[`λx y. y = x + 1`,`Cmenv`,`FST cs',sd`,`w1::enva`,`shift 1 0 e2a`]mp_tac) >>
      discharge_hyps >- (
        simp[shift_def,ADD1,EL_CONS,PRE_SUB1] >>
        match_mp_tac mkshift_thm >>
        simp[Abbr`e2a`] >>
        match_mp_tac free_vars_exp_to_Cexp_matchable >>
        simp[Abbr`enva`,env_to_Cenv_MAP] >>
        rfs[] >>
        fsrw_tac[DNF_ss][SUBSET_DEF,MEM_MAP,EXISTS_PROD,MEM_FLAT] >>
        rw[] >> res_tac >> fs[] >> metis_tac[] ) >>
      fsrw_tac[DNF_ss][FORALL_PROD] >>
      map_every qx_gen_tac[`s2`,`u2`] >> strip_tac >>
      Cases_on`err`>>fs[]>>
      TRY(Cases_on`e`>>fs[])>>
      fs[Q.SPEC`CConv X []`syneq_cases] >>
      rw[] >> fs[] >> rfs[] >> fs[Q.SPEC`CConv X []`syneq_cases] >>
      rw[EXISTS_PROD] >>
      metis_tac[EVERY2_syneq_trans])
    >- (
      fs[] >>
      qspecl_then[`T`,`menv`,`cenv`,`cs`,`env`,`e1`,`(cs',Rval v1)`]mp_tac(CONJUNCT1 evaluate_closed) >>
      qspecl_then[`T`,`menv`,`cenv`,`cs`,`env`,`e1`,`(cs',Rval v1)`]mp_tac(evaluate_closed_under_cenv) >>
      simp[]>> rpt strip_tac >> fs[] >>
      fsrw_tac[DNF_ss][EXISTS_PROD]>>
      rpt (first_x_assum (qspec_then `cm` mp_tac)) >>
      rw[] >>
      qmatch_assum_rename_tac `syneq (v_to_Cv mv m v1) w1`[] >>
      qmatch_assum_abbrev_tac `Cevaluate Cmenv (FST cs,sa) enva e1a ((FST cs',sd),Cval w1)` >>
      pop_assum kall_tac >>
      qmatch_assum_abbrev_tac `Cevaluate Cmenv (FST cs',sb) enva e2a ((FST s3,sc),er)` >>
      pop_assum kall_tac >> pop_assum kall_tac >>
      qspecl_then[`Cmenv`,`FST cs',sb`,`FST cs',sd`,`enva`,`e2a`,`((FST s3,sc),er)`]mp_tac Cevaluate_any_syneq_store >>
      fsrw_tac[DNF_ss][EXISTS_PROD] >>
      map_every qx_gen_tac[`se`,`er2`]>>strip_tac >>
      `EVERY2 (syneq) (MAP (v_to_Cv mv m) (SND s3)) se` by PROVE_TAC[EVERY2_syneq_trans] >>
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
        Cases_on`err`>>fs[]>>
        TRY(Cases_on`e`)>>fs[] >>
        fs[Q.SPEC`CConv X []`syneq_cases] >>
        rw[] >> fs[] >> rfs[] >> fs[Q.SPEC`CConv X []`syneq_cases] >>
        metis_tac[EVERY2_syneq_trans])
      >- (
        disj1_tac >>
        CONV_TAC (RESORT_EXISTS_CONV List.rev) >>
        map_every qexists_tac[`w1`,`FST cs',sd`] >> fs[] >>
        rw[Once Cevaluate_cases] >>
        srw_tac[DNF_ss][] >>
        disj2_tac >>
        qspecl_then[`Cmenv`,`FST cs',sb`,`enva`,`e2a`,`(FST s3,sc),er`]mp_tac(CONJUNCT1 Cevaluate_syneq) >> simp[] >>
        disch_then(qspecl_then[`λv1 v2. v2 = v1 + 1`,`Cmenv`,`FST cs',sd`,`w1::enva`,`shift 1 0 e2a`]mp_tac) >>
        simp[EXISTS_PROD] >>
        discharge_hyps >- (
          conj_tac >- (
            simp[shift_def] >>
            match_mp_tac mkshift_thm >>
            simp[ADD1,Abbr`e2a`,Abbr`enva`,env_to_Cenv_MAP] >>
            match_mp_tac free_vars_exp_to_Cexp_matchable >>
            simp[] >>
            fsrw_tac[DNF_ss][SUBSET_DEF,MEM_MAP,MEM_FLAT] >>
            rw[] >> rfs[] >> res_tac >> fs[] >> metis_tac[]) >>
          simp[ADD1,Abbr`enva`,env_to_Cenv_MAP,EL_CONS,PRE_SUB1] ) >>
        Cases_on`err`>>fs[]>>
        TRY(Cases_on`e`>>fs[])>>
        fs[Q.SPEC`CConv X []`syneq_cases] >>
        rw[] >> fs[] >> rfs[] >> fs[Q.SPEC`CConv X []`syneq_cases] >>
        metis_tac[EVERY2_syneq_trans])
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
        Cases_on`err`>>fs[]>>
        TRY(Cases_on`e`>>fs[])>>
        fs[Q.SPEC`CConv X []`syneq_cases] >>
        rw[] >> fs[] >> rfs[] >> fs[Q.SPEC`CConv X []`syneq_cases] >>
        metis_tac[EVERY2_syneq_trans])
      >- (
        disj1_tac >>
        CONV_TAC (RESORT_EXISTS_CONV List.rev) >>
        map_every qexists_tac[`w1`,`FST cs',sd`] >> fs[] >>
        rw[Once Cevaluate_cases] >>
        srw_tac[DNF_ss][] >>
        disj2_tac >>
        qspecl_then[`Cmenv`,`FST cs',sb`,`enva`,`e2a`,`(FST s3,sc),er`]mp_tac(CONJUNCT1 Cevaluate_syneq) >> simp[] >>
        disch_then(qspecl_then[`λv1 v2. v2 = v1 + 1`,`Cmenv`,`FST cs',sd`,`w1::enva`,`shift 1 0 e2a`]mp_tac) >>
        simp[EXISTS_PROD] >>
        discharge_hyps >- (
          conj_tac >- (
            simp[shift_def] >>
            match_mp_tac mkshift_thm >>
            simp[ADD1,Abbr`e2a`,Abbr`enva`,env_to_Cenv_MAP] >>
            match_mp_tac free_vars_exp_to_Cexp_matchable >>
            simp[]>>
            fsrw_tac[DNF_ss][SUBSET_DEF,MEM_MAP,MEM_FLAT] >>
            rw[] >> rfs[] >> res_tac >> fs[] >> metis_tac[]) >>
          simp[ADD1,Abbr`enva`,env_to_Cenv_MAP,EL_CONS,PRE_SUB1] ) >>
        Cases_on`err`>>fs[]>>
        TRY(Cases_on`e`>>fs[])>>
        fs[Q.SPEC`CConv X []`syneq_cases] >>
        rw[] >> fs[] >> rfs[] >> fs[Q.SPEC`CConv X []`syneq_cases] >>
        PROVE_TAC[EVERY2_syneq_trans]))
    >- (
      rw[Once Cevaluate_cases] >>
      fsrw_tac[DNF_ss][EXISTS_PROD] >>
      disj2_tac >>
      rw[Once Cevaluate_cases] >>
      fsrw_tac[DNF_ss][EXISTS_PROD] >>
      disj2_tac >>
      rw[Once(CONJUNCT2 Cevaluate_cases)] >>
      rw[Once(CONJUNCT2 Cevaluate_cases)] >>
      rw[Once(CONJUNCT2 Cevaluate_cases)] >>
      srw_tac[DNF_ss][]>>
      disj2_tac >>
      qspecl_then[`T`,`menv`,`cenv`,`cs`,`env`,`e1`,`(cs',Rval v1)`]mp_tac(CONJUNCT1 evaluate_closed) >>
      qspecl_then[`T`,`menv`,`cenv`,`cs`,`env`,`e1`,`(cs',Rval v1)`]mp_tac(evaluate_closed_under_cenv) >>
      simp[]>>rpt strip_tac>>fs[]>>
      rpt (first_x_assum (qspec_then `cm` mp_tac)) >> rw[] >>
      qmatch_assum_rename_tac `syneq (v_to_Cv mv m v1) w1`[] >>
      qmatch_assum_abbrev_tac `Cevaluate Cmenv (FST cs,sa) enva e1a ((FST cs',sd),Cval w1)` >>
      pop_assum kall_tac >>
      qmatch_assum_abbrev_tac `Cevaluate Cmenv (FST cs',sb) enva e2a ((FST s3,sc),er)` >>
      pop_assum kall_tac >> pop_assum kall_tac >>
      qspecl_then[`Cmenv`,`FST cs',sb`,`FST cs',sd`,`enva`,`e2a`,`((FST s3,sc),er)`]mp_tac Cevaluate_any_syneq_store >>
      fsrw_tac[DNF_ss][EXISTS_PROD] >>
      Cases_on`err`>>fs[]>>
      TRY(Cases_on`e`>>fs[])>>
      fs[Q.SPEC`CConv X []`syneq_cases] >>
      rw[] >> fs[] >> rfs[] >> fs[Q.SPEC`CConv X []`syneq_cases] >>
      metis_tac[EVERY2_syneq_trans])
    >- (
      rw[Once Cevaluate_cases] >>
      fsrw_tac[DNF_ss][] >>
      disj2_tac >> disj2_tac >> disj1_tac >>
      fsrw_tac[DNF_ss][EXISTS_PROD] >>
      rw[Once(CONJUNCT2 Cevaluate_cases)] >>
      rw[Once(CONJUNCT2 Cevaluate_cases)] >>
      qspecl_then[`T`,`menv`,`cenv`,`cs`,`env`,`e1`,`(cs',Rval v1)`]mp_tac(CONJUNCT1 evaluate_closed) >>
      qspecl_then[`T`,`menv`,`cenv`,`cs`,`env`,`e1`,`(cs',Rval v1)`]mp_tac(evaluate_closed_under_cenv) >>
      simp[]>>rpt strip_tac>>fs[]>>
      rpt (first_x_assum (qspec_then `cm` mp_tac)) >> rw[] >>
      qmatch_assum_rename_tac `syneq (v_to_Cv mv m v1) w1`[] >>
      qmatch_assum_abbrev_tac `Cevaluate Cmenv (FST cs,sa) enva e1a ((FST cs',sd),Cval w1)` >>
      pop_assum kall_tac >>
      qmatch_assum_abbrev_tac `Cevaluate Cmenv (FST cs',sb) enva e2a ((FST s3,sc),er)` >>
      pop_assum kall_tac >> pop_assum kall_tac >>
      qspecl_then[`Cmenv`,`FST cs',sb`,`FST cs',sd`,`enva`,`e2a`,`((FST s3,sc),er)`]mp_tac Cevaluate_any_syneq_store >>
      fsrw_tac[DNF_ss][EXISTS_PROD] >>
      Cases_on`err`>>fs[]>>
      TRY(Cases_on`e`>>fs[])>>
      fs[Q.SPEC`CConv X []`syneq_cases] >>
      rw[] >> fs[] >> rfs[] >> fs[Q.SPEC`CConv X []`syneq_cases] >>
      metis_tac[EVERY2_syneq_trans])
    >- (
      rw[Once Cevaluate_cases] >>
      fsrw_tac[DNF_ss][EXISTS_PROD] >>
      disj2_tac >>
      rw[Once(CONJUNCT2 Cevaluate_cases)] >>
      rw[Once(CONJUNCT2 Cevaluate_cases)] >>
      rw[Once(CONJUNCT2 Cevaluate_cases)] >>
      srw_tac[DNF_ss][] >>
      disj2_tac >>
      qspecl_then[`T`,`menv`,`cenv`,`cs`,`env`,`e1`,`(cs',Rval v1)`]mp_tac(CONJUNCT1 evaluate_closed) >>
      qspecl_then[`T`,`menv`,`cenv`,`cs`,`env`,`e1`,`(cs',Rval v1)`]mp_tac(evaluate_closed_under_cenv) >>
      simp[]>>rpt strip_tac>>fs[]>>
      rpt (first_x_assum (qspec_then `cm` mp_tac)) >> rw[] >>
      qmatch_assum_rename_tac `syneq (v_to_Cv mv m v1) w1`[] >>
      qmatch_assum_abbrev_tac `Cevaluate Cmenv (FST cs,sa) enva e1a ((FST cs',sd),Cval w1)` >>
      pop_assum kall_tac >>
      qmatch_assum_abbrev_tac `Cevaluate Cmenv (FST cs',sb) enva e2a ((FST s3,sc),er)` >>
      pop_assum kall_tac >> pop_assum kall_tac >>
      qspecl_then[`Cmenv`,`FST cs',sb`,`FST cs',sd`,`enva`,`e2a`,`((FST s3,sc),er)`]mp_tac Cevaluate_any_syneq_store >>
      fsrw_tac[DNF_ss][EXISTS_PROD] >>
      Cases_on`err`>>fs[]>>
      TRY(Cases_on`e`>>fs[])>>
      fs[Q.SPEC`CConv X []`syneq_cases] >>
      rw[] >> fs[] >> rfs[] >> fs[Q.SPEC`CConv X []`syneq_cases] >>
      PROVE_TAC[EVERY2_syneq_trans])) >>
  strip_tac >- (
    ntac 4 gen_tac >>
    Cases >> fs[exp_to_Cexp_def] >>
    qx_gen_tac `e1` >>
    qx_gen_tac `e2` >>
    rw[LET_THM] >- (
      Q.PAT_ABBREV_TAC`sum = opn_to_prim2 X` >>
      Cases_on`sum`>>simp[]>-(
        rw[Once Cevaluate_cases] >>
        fsrw_tac[DNF_ss][EXISTS_PROD] >>
        disj2_tac >>
        rw[Once(CONJUNCT2 Cevaluate_cases)] >>
        rw[Once(CONJUNCT2 Cevaluate_cases)] >>
        rw[Once(CONJUNCT2 Cevaluate_cases)] >>
        fsrw_tac[DNF_ss][] >>
        Cases_on`err`>>fs[]>>
        Cases_on`e`>>fs[] >>
        fs[Q.SPEC`CConv X []`syneq_cases] >>
        rw[] >> fs[] >> rfs[] >> fs[Q.SPEC`CConv X []`syneq_cases]) >>
      srw_tac[DNF_ss][Once Cevaluate_cases] >> disj2_tac >> fs[] >>
      first_x_assum(qspec_then`cm`mp_tac) >> simp[EXISTS_PROD] >> rw[] >>
      HINT_EXISTS_TAC >>
      Cases_on`err`>>fs[]>>
      Cases_on`e`>>fs[] >>
      fs[Q.SPEC`CConv X []`syneq_cases])
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
        fsrw_tac[DNF_ss][] >>
        Cases_on`err`>>fs[]>>
        Cases_on`e`>>
        fs[Q.SPEC`CConv X []`syneq_cases])
      >- (
        Cases_on`err`>>fs[]>>
        Cases_on`e`>>
        fs[Q.SPEC`CConv X []`syneq_cases] )
      >- (
        rw[Once Cevaluate_cases] >>
        fsrw_tac[DNF_ss][] >>
        disj1_tac >>
        rw[Once Cevaluate_cases] >>
        fsrw_tac[DNF_ss][] >>
        disj2_tac >>
        rw[Once(CONJUNCT2 Cevaluate_cases)] >>
        rw[Once(CONJUNCT2 Cevaluate_cases)] >>
        rw[Once(CONJUNCT2 Cevaluate_cases)] >>
        fsrw_tac[DNF_ss][] >>
        Cases_on`err`>>fs[]>>
        Cases_on`e`>>
        fs[Q.SPEC`CConv X []`syneq_cases] ) >>
      Cases_on`err`>>fs[]>>
      Cases_on`e`>>
      fs[Q.SPEC`CConv X []`syneq_cases] )
    >- (
      rw[Once Cevaluate_cases] >>
      fsrw_tac[DNF_ss][EXISTS_PROD] >>
      disj2_tac >>
      rw[Once Cevaluate_cases] >>
      fsrw_tac[DNF_ss][EXISTS_PROD] >>
      disj2_tac >>
      rw[Once(CONJUNCT2 Cevaluate_cases)] >>
      rw[Once(CONJUNCT2 Cevaluate_cases)] >>
      rw[Once(CONJUNCT2 Cevaluate_cases)] >>
      fsrw_tac[DNF_ss][] >>
      Cases_on`err`>>fs[]>>
      Cases_on`e`>>
      fs[Q.SPEC`CConv X []`syneq_cases] )
    >- (
      rw[Once Cevaluate_cases] >>
      fsrw_tac[DNF_ss][EXISTS_PROD] >>
      disj2_tac >>
      rw[Once(CONJUNCT2 Cevaluate_cases)] >>
      rw[Once(CONJUNCT2 Cevaluate_cases)] >>
      rw[Once(CONJUNCT2 Cevaluate_cases)] >>
      fsrw_tac[DNF_ss][] >>
      Cases_on`err`>>fs[]>>
      Cases_on`e`>>
      fs[Q.SPEC`CConv X []`syneq_cases] )
    >- (
      rw[Once Cevaluate_cases] >>
      fsrw_tac[DNF_ss][EXISTS_PROD] >>
      disj2_tac >>
      rw[Once(CONJUNCT2 Cevaluate_cases)] >>
      rw[Once(CONJUNCT2 Cevaluate_cases)] >>
      rw[Once(CONJUNCT2 Cevaluate_cases)] >>
      fsrw_tac[DNF_ss][] >>
      Cases_on`err`>>fs[]>>
      Cases_on`e`>>
      fs[Q.SPEC`CConv X []`syneq_cases]) ) >>
  strip_tac >- (
    rw[exp_to_Cexp_def,LET_THM] >>
    fsrw_tac[DNF_ss][EXISTS_PROD] >>
    imp_res_tac do_log_FV >>
    `FV exp' ⊆ set (MAP (Short o FST) env) ∪ menv_dom menv` by PROVE_TAC[SUBSET_TRANS] >>
    qspecl_then[`T`,`menv`,`cenv`,`cs`,`env`,`exp`,`(cs',Rval v)`]mp_tac(CONJUNCT1 evaluate_closed) >>
    qspecl_then[`T`,`menv`,`cenv`,`cs`,`env`,`exp`,`(cs',Rval v)`]mp_tac(evaluate_closed_under_cenv) >>
    simp[]>>rpt strip_tac>>fs[]>>
    `all_cns_exp exp' ⊆ cenv_dom cenv` by (
      match_mp_tac do_log_all_cns >> metis_tac[] ) >> fs[] >>
    rpt (first_x_assum (qspec_then`cm` mp_tac)) >> rw[] >>
    qmatch_assum_rename_tac`syneq (v_to_Cv mv m v) w`[] >>
    qmatch_assum_abbrev_tac `Cevaluate Cmenv (FST cs,sa) enva e1a ((FST cs',sd),Cval w)` >>
    pop_assum kall_tac >>
    qmatch_assum_abbrev_tac `Cevaluate Cmenv (FST cs',sb) enva e2a ((FST (FST res),sc),w2)` >>
    ntac 2 (pop_assum kall_tac) >>
    qspecl_then[`Cmenv`,`FST cs',sb`,`FST cs',sd`,`enva`,`e2a`,`((FST (FST res),sc),w2)`]mp_tac Cevaluate_any_syneq_store >>
    fsrw_tac[DNF_ss][EXISTS_PROD] >>
    map_every qx_gen_tac[`se`,`w3`] >>strip_tac >>
    Cases_on `op` >> Cases_on `v` >> fs[do_log_def] >>
    Cases_on `l` >> fs[v_to_Cv_def] >>
    rw[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][] >> disj1_tac >>
    CONV_TAC (RESORT_EXISTS_CONV List.rev) >>
    map_every qexists_tac [`b`,`FST cs',sd`] >> fs[] >>
    rw[] >> fs[] >> rw[] >>
    fs[evaluate_lit] >> rw[v_to_Cv_def] >>
    PROVE_TAC[Cresult_rel_syneq_trans,EVERY2_syneq_trans] ) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rw[exp_to_Cexp_def,LET_THM] >>
    Cases_on `op` >> fsrw_tac[DNF_ss][] >>
    rw[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][EXISTS_PROD] >>
    Cases_on`err`>>fs[]>>
    Cases_on`e`>>fs[] >>
    fs[Q.SPEC`CConv X []`syneq_cases]) >>
  strip_tac >- (
    rw[exp_to_Cexp_def,LET_THM] >>
    fsrw_tac[DNF_ss][EXISTS_PROD] >>
    imp_res_tac do_if_FV >>
    `FV exp' ⊆ set (MAP (Short o FST) env) ∪ menv_dom menv` by (
      fsrw_tac[DNF_ss][SUBSET_DEF] >>
      PROVE_TAC[]) >> fs[] >>
    qspecl_then[`T`,`menv`,`cenv`,`cs`,`env`,`exp`,`(cs',Rval v)`]mp_tac(CONJUNCT1 evaluate_closed) >>
    qspecl_then[`T`,`menv`,`cenv`,`cs`,`env`,`exp`,`(cs',Rval v)`]mp_tac(evaluate_closed_under_cenv) >>
    simp[]>>rpt strip_tac>>fs[]>>
    rw[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][] >>
    disj1_tac >>
    `all_cns_exp exp' ⊆ cenv_dom cenv` by (
      match_mp_tac do_if_all_cns >> metis_tac[] ) >>
    rpt (first_x_assum (qspec_then`cm` mp_tac)) >> rw[] >>
    qmatch_assum_rename_tac`syneq (v_to_Cv mv m v) w`[] >>
    qmatch_assum_abbrev_tac `Cevaluate Cmenv (FST cs,sa) enva e1a ((FST cs',sd),Cval w)` >>
    pop_assum kall_tac >>
    qmatch_assum_abbrev_tac `Cevaluate Cmenv (FST cs',sb) enva e2a ((FST (FST res),sc),w2)` >>
    ntac 2 (pop_assum kall_tac) >>
    qspecl_then[`Cmenv`,`FST cs',sb`,`FST cs',sd`,`enva`,`e2a`,`((FST (FST res),sc),w2)`]mp_tac Cevaluate_any_syneq_store >>
    fsrw_tac[DNF_ss][EXISTS_PROD] >>
    map_every qx_gen_tac[`se`,`w3`] >>strip_tac >>
    CONV_TAC (RESORT_EXISTS_CONV List.rev) >>
    CONV_TAC SWAP_EXISTS_CONV >> qexists_tac`sd` >>
    CONV_TAC SWAP_EXISTS_CONV >> qexists_tac`FST cs'` >>
    CONV_TAC SWAP_EXISTS_CONV >> qexists_tac`w3` >>
    CONV_TAC SWAP_EXISTS_CONV >> qexists_tac`se` >>
    qpat_assum `do_if v e2 e3 = X` mp_tac >>
    fs[do_if_def] >> rw[] >|[
      qexists_tac`T`,
      qexists_tac`F`] >>
    fsrw_tac[DNF_ss][v_to_Cv_def] >>
    PROVE_TAC[EVERY2_syneq_trans,Cresult_rel_syneq_trans]) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rw[exp_to_Cexp_def,LET_THM] >> fs[] >>
    rw[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][EXISTS_PROD] >>
    Cases_on`err`>>fs[]>>
    Cases_on`e`>>fs[] >>
    fs[Q.SPEC`CConv X []`syneq_cases]) >>
  strip_tac >- (
    rpt strip_tac >> fs[] >>
    fsrw_tac[DNF_ss][EXISTS_PROD,LET_THM] >>
    first_x_assum (qspec_then `cm` mp_tac) >> rw[] >>
    qmatch_assum_abbrev_tac `syneq (v_to_Cv mv cm v) w` >> pop_assum kall_tac >>
    qmatch_assum_rename_tac `syneq (v_to_Cv mv m v) w`[]>>
    rw[exp_to_Cexp_def,LET_THM] >>
    rw[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][] >>
    disj1_tac >>
    qmatch_assum_abbrev_tac`Cevaluate Cmenv (FST cs,sa) enva ea ((FST s2,sd),Cval w)` >>
    pop_assum kall_tac >>
    CONV_TAC (RESORT_EXISTS_CONV List.rev) >>
    map_every qexists_tac [`w`,`FST s2,sd`] >> fs[] >>
    qmatch_assum_abbrev_tac `evaluate_match_with P cenv s2 env v pes res` >>
    Q.ISPECL_THEN [`s2`,`pes`,`res`] mp_tac (Q.GEN`s`evaluate_match_with_matchres) >> fs[] >>
    qmatch_assum_abbrev_tac`Abbrev(ea = exp_to_Cexp mm exp)` >>
    `mm.cnmap = m` by rw[Abbr`mm`] >>
    `mm.mvars = mv` by rw[Abbr`mm`] >>
    qunabbrev_tac`mv` >>
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
      Q.SPECL_THEN [`sb`,`v_to_Cv mm.mvars mm.cnmap v`,`Cpes`,`[]`,`NONE`]
        mp_tac (INST_TYPE[alpha|->``:Cexp``](Q.GENL[`v`,`s`] Cevaluate_match_syneq)) >>
      fs[] >>
      disch_then (qspecl_then [`sd`,`w`] mp_tac) >> fs[] >>
      strip_tac >>
      qspecl_then[`Cmenv`,`res0,sd`,`w`,`Cpes`,`[]`,`NONE`]mp_tac(Q.GENL[`v`,`s`,`mod`]Cevaluate_match_remove_mat_var)>>
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
            fsrw_tac[DNF_ss][SUBSET_DEF,FORALL_PROD,MEM_FLAT,MEM_MAP,FV_pes_MAP] >>
            rw[] >> rfs[] >> res_tac >> fs[] >> metis_tac[] ) >>
          simp[SUBSET_DEF,ADD1,Abbr`enva`,env_to_Cenv_MAP] ) >>
        simp[SUBSET_DEF] ) >>
      simp[Once syneq_cases] >>
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
    qspecl_then[`Cmenv`,`FST s2,sd`,`w`,`ps`,`wenv`,`mmr`]mp_tac(Q.GENL[`v`,`s`,`mod`]Cevaluate_match_remove_mat_var) >>
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
          fsrw_tac[DNF_ss][SUBSET_DEF,FORALL_PROD,MEM_MAP,MEM_FLAT,FV_pes_MAP] >>
          rw[] >> rfs[] >> res_tac >> fs[] >>
          metis_tac[] ) >>
        simp[SUBSET_DEF,ADD1,Abbr`enva`,env_to_Cenv_MAP] ) >>
      simp[SUBSET_DEF] ) >>
    qspecl_then[`T`,`menv`,`cenv`,`cs`,`env`,`exp`,`(s2,Rval v)`]mp_tac(CONJUNCT1 evaluate_closed) >>
    simp[] >> strip_tac >>
    Q.ISPECL_THEN[`s2`,`menv`,`pes`,`(s2,Rval(menv',mr))`]mp_tac(Q.GENL[`envM`,`s`]evaluate_match_with_matchres_closed)>>
    simp[] >> strip_tac >>
    `FV (SND mr) ⊆ set (MAP (Short o FST) (menv' ++ env)) ∪ menv_dom menv` by (
      fsrw_tac[DNF_ss][SUBSET_DEF,FORALL_PROD,MEM_MAP,EXISTS_PROD,MEM_FLAT,FV_pes_MAP] >>
      PairCases_on`mr`>>fs[] >>
      qx_gen_tac`x` >> strip_tac >>
      first_x_assum(qspecl_then[`x`,`mr0`,`mr1`]mp_tac) >>
      simp[] >>
      qpat_assum`X = Y`(mp_tac o SYM) >>
      simp[MEM_MAP,EXISTS_PROD] >>
      METIS_TAC[] ) >>
    `closed_under_cenv cenv menv (menv' ++ env) (SND s2)` by (
      Q.ISPECL_THEN[`s2`,`pes`,`(s2,Rval(menv',mr))`]mp_tac(Q.GEN`s`evaluate_match_with_matchres_all_cns)>>
      qspecl_then[`T`,`menv`,`cenv`,`cs`,`env`,`exp`,`(s2,Rval v)`]mp_tac(CONJUNCT1 evaluate_all_cns) >>
      simp[] >>
      fs[closed_under_cenv_def] >>
      fs[MEM_MAP] >>
      METIS_TAC[] ) >>
    fs[Abbr`P`] >> rfs[] >> fs[] >>
    first_x_assum(qspec_then`mm.cnmap`mp_tac)>>
    fsrw_tac[DNF_ss][] >>
    discharge_hyps >- (
      qpat_assum`all_cns_pes X ⊆ Y`mp_tac >>
      simp_tac(srw_ss()++DNF_ss)[all_cns_pes_MAP,SUBSET_DEF,MEM_MAP,FORALL_PROD,EXISTS_PROD] >>
      PairCases_on`mr`>>fs[] >> METIS_TAC[]) >>
    fsrw_tac[DNF_ss][] >>
    qpat_assum`evaluate_match_with P cenv s2 env v pes (R,res2)`kall_tac >>
    map_every qx_gen_tac [`se`,`re`] >> strip_tac >>
    qmatch_assum_abbrev_tac`Cevaluate Cmenv (FST s2,sb) eee xe er` >>
    qspecl_then[`Cmenv`,`FST s2,sb`,`eee`,`xe`,`er`]mp_tac(CONJUNCT1 Cevaluate_syneq) >>
    simp[] >>
    Q.PAT_ABBREV_TAC`we:Cexp = f mr` >>
    `we = shift 1 (LENGTH (pat_bindings (FST mr) [])) xe` by (
      unabbrev_all_tac >>
      PairCases_on`mr`>>simp[] >>
      rpt AP_TERM_TAC >> AP_THM_TAC >> AP_TERM_TAC >>
      simp[exp_to_Cexp_state_component_equality,pat_to_Cpat_cnmap,FST_pat_to_Cpat_bvars] ) >>
    disch_then(qspecl_then[`λv1 v2. if v1 < LENGTH wenv then v2 = v1 else v2 = v1 + 1`,`Cmenv`,`FST s2,sd`,`wenv++w::enva`,`we`]mp_tac) >>
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
        fsrw_tac[DNF_ss][SUBSET_DEF,MEM_MAP,MEM_FLAT] >>
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
    metis_tac[Cresult_rel_syneq_trans,EVERY2_syneq_trans]) >>
  strip_tac >- (
    rw[exp_to_Cexp_def,LET_THM] >>
    rw[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][EXISTS_PROD] >>
    Cases_on`err`>>fs[]>>
    Cases_on`e`>>fs[Q.SPEC`CConv X []`syneq_cases]) >>
  strip_tac >- (
    rw[exp_to_Cexp_def,LET_THM] >> fs[bind_def] >>
    rw[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][EXISTS_PROD] >>
    disj1_tac >>
    last_x_assum(qspec_then`cm`mp_tac) >> simp[] >>
    disch_then(qx_choosel_then[`s2`,`vv`]strip_assume_tac) >>
    qspecl_then[`T`,`menv`,`cenv`,`cs`,`env`,`exp`,`(cs',Rval v)`]mp_tac(CONJUNCT1 evaluate_closed) >>
    qspecl_then[`T`,`menv`,`cenv`,`cs`,`env`,`exp`,`(cs',Rval v)`]mp_tac(evaluate_closed_under_cenv) >>
    fsrw_tac[DNF_ss][env_to_Cenv_MAP,SUBSET_DEF,lem] >> strip_tac >> strip_tac >>
    first_x_assum(qspec_then`cm`mp_tac) >>
    simp[] >>
    `all_cns v ⊆ cenv_dom cenv` by (
      qspecl_then[`ck`,`menv`,`cenv`,`cs`,`env`,`exp`,`(cs',Rval v)`]mp_tac(CONJUNCT1 evaluate_all_cns) >>
      fs[closed_under_cenv_def] >>
      metis_tac[SUBSET_DEF] ) >>
    fsrw_tac[DNF_ss][closed_under_cenv_def,EXISTS_PROD] >>
    map_every qx_gen_tac [`s3`,`v3`] >> strip_tac >>
    CONV_TAC(RESORT_EXISTS_CONV List.rev) >>
    map_every qexists_tac[`vv`,`s2`] >> simp[] >> fs[v_to_Cv_def] >>
    qmatch_assum_abbrev_tac`Cevaluate Cmenv (c1,s1) env1 exp1 ((c3,s3),v3)` >>
    qspecl_then[`Cmenv`,`c1,s1`,`env1`,`exp1`,`((c3,s3),v3)`]mp_tac(CONJUNCT1 Cevaluate_syneq) >>
    simp[] >>
    disch_then(qspecl_then[`$=`,`Cmenv`,`c1,s2`,`vv::(TL env1)`,`exp1`]mp_tac) >>
    simp[syneq_exp_refl,EXISTS_PROD,Abbr`env1`,ADD1] >>
    discharge_hyps >- (
      Cases >> lrw[EL_CONS] ) >>
    metis_tac[Cresult_rel_syneq_trans,EVERY2_syneq_trans]) >>
  strip_tac >- (
    rw[exp_to_Cexp_def,LET_THM] >>
    rw[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][EXISTS_PROD] >>
    Cases_on`err`>>fs[]>>
    Cases_on`e`>>fs[Q.SPEC`CConv X []`syneq_cases]) >>
  strip_tac >- (
    rw[exp_to_Cexp_def,LET_THM,FST_triple] >>
    fs[] >>
    rw[defs_to_Cdefs_MAP] >>
    rw[Once Cevaluate_cases,FOLDL_FUPDATE_LIST] >>
    `FV exp ⊆ set (MAP (Short o FST) (build_rec_env funs env env)) ∪ menv_dom menv` by (
      fsrw_tac[DNF_ss][SUBSET_DEF,pairTheory.FORALL_PROD,MEM_MAP,pairTheory.EXISTS_PROD,MEM_FLAT,build_rec_env_MAP] >>
      rw[] >> res_tac >> fs[] >>
      METIS_TAC[] ) >>
    fs[] >>
    `EVERY (closed menv) (MAP SND (build_rec_env funs env env))` by (
      match_mp_tac build_rec_env_closed >>
      fs[] >>
      fsrw_tac[DNF_ss][SUBSET_DEF,pairTheory.FORALL_PROD,MEM_MAP,pairTheory.EXISTS_PROD,MEM_EL,FST_triple,FV_defs_MAP] >>
      rw[] >> res_tac >> fs[] >>
      METIS_TAC[] ) >>
    fs[] >>
    `closed_under_cenv cenv menv (build_rec_env funs env env) (SND cs)` by (
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
    qmatch_abbrev_tac`Cevaluate Cm ss l1 ee rr` >>
    qmatch_assum_abbrev_tac`Cevaluate Cm ss l2 ee rr` >>
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
    rw[LET_THM] >>
    rw[Once (CONJUNCT2 Cevaluate_cases)] >>
    fsrw_tac[DNF_ss][EXISTS_PROD] >>
    qspecl_then[`T`,`menv`,`cenv`,`cs`,`env`,`exp`,`(cs',Rval v)`]mp_tac(CONJUNCT1 evaluate_closed) >>
    qspecl_then[`T`,`menv`,`cenv`,`cs`,`env`,`exp`,`(cs',Rval v)`]mp_tac(evaluate_closed_under_cenv) >>
    simp[] >> rpt strip_tac >> fs[] >>
    rpt (first_x_assum (qspec_then`cm` mp_tac)) >>
    rw[] >>
    qmatch_assum_rename_tac`syneq (v_to_Cv mv m v) w`[] >>
    qmatch_assum_abbrev_tac`Cevaluate Cmenv (ca,sa) enva ea ((cd,sd),Cval w)` >>
    pop_assum kall_tac >>
    CONV_TAC SWAP_EXISTS_CONV >> qexists_tac`cd` >>
    CONV_TAC SWAP_EXISTS_CONV >> qexists_tac`sd` >>
    CONV_TAC SWAP_EXISTS_CONV >> qexists_tac`w` >> rw[] >>
    qmatch_assum_abbrev_tac`Cevaluate_list Cmenv (cb,sb) enva eb ((ce,se),Cval ws)` >>
    ntac 2 (pop_assum kall_tac) >>
    qspecl_then[`Cmenv`,`Cmenv`,`cb,sb`,`cd,sd`,`enva`,`enva`,`eb`,`((ce,se),Cval ws)`]mp_tac Cevaluate_list_any_syneq_any >>
    fsrw_tac[DNF_ss][FORALL_PROD] >>
    map_every qx_gen_tac[`sf`,`rf`] >>
    strip_tac >>
    map_every qexists_tac[`sf`,`rf`] >>
    simp[] >>
    METIS_TAC[EVERY2_syneq_trans]) >>
  strip_tac >- (
    rw[LET_THM] >>
    rw[Once (CONJUNCT2 Cevaluate_cases)] >>
    fsrw_tac[DNF_ss][EXISTS_PROD] >>
    Cases_on`err`>>fs[]>>
    Cases_on`e`>>fs[Q.SPEC`CConv X []`syneq_cases]) >>
  rw[LET_THM] >>
  rw[Once (CONJUNCT2 Cevaluate_cases)] >>
  fsrw_tac[DNF_ss][EXISTS_PROD] >>
  disj2_tac >>
  qspecl_then[`T`,`menv`,`cenv`,`cs`,`env`,`exp`,`(cs',Rval v)`]mp_tac(CONJUNCT1 evaluate_closed) >>
  qspecl_then[`T`,`menv`,`cenv`,`cs`,`env`,`exp`,`(cs',Rval v)`]mp_tac(evaluate_closed_under_cenv) >>
  simp[] >> rpt strip_tac >> fs[] >>
  rpt (first_x_assum (qspec_then`cm` mp_tac)) >>
  rw[] >>
  qmatch_assum_rename_tac`syneq (v_to_Cv mv m v) w`[] >>
  qmatch_assum_abbrev_tac`Cevaluate Cm (ca,sa) enva ea ((cd,sd),Cval w)` >>
  pop_assum kall_tac >>
  qmatch_assum_abbrev_tac`Cevaluate_list Cm (cd,sb) enva eb ((ce,se),er)` >>
  pop_assum kall_tac >> pop_assum kall_tac >>
  disj2_tac >>
  CONV_TAC SWAP_EXISTS_CONV >> qexists_tac`cd` >>
  CONV_TAC SWAP_EXISTS_CONV >> qexists_tac`sd` >>
  CONV_TAC SWAP_EXISTS_CONV >> qexists_tac`w` >> rw[] >>
  qspecl_then[`Cm`,`Cm`,`cd,sb`,`cd,sd`,`enva`,`enva`,`eb`,`((ce,se),er)`]mp_tac Cevaluate_list_any_syneq_any >>
  fsrw_tac[DNF_ss][FORALL_PROD] >>
  Cases_on`err`>>fs[] >>
  TRY(Cases_on`e`)>>fs[Q.SPEC`CConv X []`syneq_cases] >>
  rw[] >> fs[] >>
  METIS_TAC[EVERY2_syneq_trans])

(* TODO: move/categorise *)

val pat_to_Cpat_SUBMAP = store_thm("pat_to_Cpat_SUBMAP",
  ``(∀p m m'. all_cns_pat p ⊆ FDOM m.cnmap ∧ m.cnmap ⊑ m'.cnmap ∧ (m'.bvars = m.bvars) ⇒ (SND (pat_to_Cpat m' p) = SND (pat_to_Cpat m p))) ∧
    (∀ps m m'. all_cns_pats ps ⊆ FDOM m.cnmap ∧ m.cnmap ⊑ m'.cnmap ∧ (m'.bvars = m.bvars) ⇒ (SND (pats_to_Cpats m' ps) = SND (pats_to_Cpats m ps)))``,
  ho_match_mp_tac(TypeBase.induction_of``:pat``)>>
  simp[ToIntLangTheory.pat_to_Cpat_def,UNCURRY,FLOOKUP_DEF] >>
  simp[pat_to_Cpat_cnmap] >>
  conj_tac >- rw[SUBMAP_DEF] >>
  rw[] >>
  first_x_assum match_mp_tac >>
  simp[pat_to_Cpat_cnmap] >>
  simp[FST_pat_to_Cpat_bvars])

val exp_to_Cexp_SUBMAP = store_thm("exp_to_Cexp_SUBMAP",
  ``(∀m exp m'. all_cns_exp exp ⊆ FDOM m.cnmap ∧ m.cnmap ⊑ m'.cnmap ∧ (m'.bvars = m.bvars) ∧ (m'.mvars = m.mvars) ⇒ (exp_to_Cexp m' exp = exp_to_Cexp m exp)) ∧
    (∀m ds m'. all_cns_defs ds ⊆ FDOM m.cnmap ∧ m.cnmap ⊑ m'.cnmap ∧ (m'.bvars = m.bvars) ∧ (m'.mvars = m.mvars) ⇒ (defs_to_Cdefs m' ds = defs_to_Cdefs m ds)) ∧
    (∀m pes m'. all_cns_pes pes ⊆ FDOM m.cnmap ∧ m.cnmap ⊑ m'.cnmap ∧ (m'.bvars = m.bvars) ∧ (m'.mvars = m.mvars) ⇒ (pes_to_Cpes m' pes = pes_to_Cpes m pes)) ∧
    (∀m es m'. all_cns_list es ⊆ FDOM m.cnmap ∧ m.cnmap ⊑ m'.cnmap ∧ (m'.bvars = m.bvars) ∧ (m'.mvars = m.mvars) ⇒ (exps_to_Cexps m' es = exps_to_Cexps m es))``,
  ho_match_mp_tac exp_to_Cexp_ind >>
  simp[exp_to_Cexp_def] >>
  conj_tac >- rw[SUBMAP_DEF,FLOOKUP_DEF] >>
  simp[UNCURRY] >>
  simp[pat_to_Cpat_SUBMAP] >>
  rw[] >>
  first_x_assum (match_mp_tac o MP_CANON) >>
  simp[pat_to_Cpat_cnmap,FST_pat_to_Cpat_bvars] >>
  Cases_on`pat_to_Cpat m p`>>simp[])

val v_to_Cv_SUBMAP = store_thm("v_to_Cv_SUBMAP",
  ``(∀mv m v m'. all_cns v ⊆ (FDOM m) ∧ m ⊑ m' ⇒ v_to_Cv mv m' v = v_to_Cv mv m v) ∧
    (∀mv m vs m'. BIGUNION (IMAGE all_cns (set vs)) ⊆ FDOM m ∧ m ⊑ m' ⇒ vs_to_Cvs mv m' vs = vs_to_Cvs mv m vs) ∧
    (∀mv m env m'. BIGUNION (IMAGE all_cns (env_range env)) ⊆ FDOM m ∧ m ⊑ m' ⇒ env_to_Cenv mv m' env = env_to_Cenv mv m env)``,
  ho_match_mp_tac v_to_Cv_ind >> simp[v_to_Cv_def] >>
  conj_tac >- rw[SUBMAP_DEF,FLOOKUP_DEF] >>
  simp[exp_to_Cexp_SUBMAP] >>
  rw[] >> AP_TERM_TAC >>
  simp[exp_to_Cexp_SUBMAP])

val exp_to_Cexp_mvars_SUBMAP = store_thm("exp_to_Cexp_mvars_SUBMAP",
  ``(∀m exp m'.
      (∀mn x. Long mn x ∈ FV exp ⇒ ∃menv. FLOOKUP m.mvars mn = SOME menv ∧ MEM x menv) ∧
      m'.bvars = m.bvars ∧ m'.cnmap = m.cnmap ∧ m.mvars ⊑  m'.mvars ⇒
            exp_to_Cexp m' exp = exp_to_Cexp m exp) ∧
    (∀m ds m'.
      (∀mn x. Long mn x ∈ FV_defs (set (MAP (Short o FST) ds)) ds ⇒ ∃menv. FLOOKUP m.mvars mn = SOME menv ∧ MEM x menv) ∧
      m'.bvars = m.bvars ∧ m'.cnmap = m.cnmap ∧ m.mvars ⊑ m'.mvars ⇒
      defs_to_Cdefs m' ds = defs_to_Cdefs m ds) ∧
  (∀m pes m'.
    (∀mn x. Long mn x ∈ FV_pes pes ⇒ ∃menv. FLOOKUP m.mvars mn = SOME menv ∧ MEM x menv) ∧
     m'.bvars = m.bvars ∧
     m'.cnmap = m.cnmap ∧
     m.mvars ⊑ m'.mvars ⇒
    pes_to_Cpes m' pes = pes_to_Cpes m pes) ∧
   (∀m es m'.
    (∀mn x. Long mn x ∈ FV_list es ⇒ ∃menv. FLOOKUP m.mvars mn = SOME menv ∧ MEM x menv) ∧
     m'.bvars = m.bvars ∧
     m'.cnmap = m.cnmap ∧
     m.mvars ⊑ m'.mvars ⇒
     exps_to_Cexps m' es = exps_to_Cexps m es)``,
  ho_match_mp_tac exp_to_Cexp_ind >>
  simp[exp_to_Cexp_def] >>
  conj_tac >- (
    rw[] >>
    BasicProvers.CASE_TAC >>
    imp_res_tac FLOOKUP_SUBMAP >> fs[] ) >>
  conj_tac >- (
    rw[] >>
    first_x_assum match_mp_tac >>
    simp[] >>
    rw[] >>
    first_x_assum match_mp_tac >>
    simp[] >>
    fsrw_tac[DNF_ss][FV_defs_MAP,EXISTS_PROD] >>
    fsrw_tac[DNF_ss][MEM_MAP] ) >>
  conj_tac >- (
    rw[] >>
    first_x_assum match_mp_tac >>
    simp[] >>
    fsrw_tac[DNF_ss][FV_defs_MAP,EXISTS_PROD,MEM_MAP] >>
    metis_tac[] ) >>
  rw[] >>
  simp[UNCURRY] >>
  conj_tac >- metis_tac[SND_pat_to_Cpat_cnmap] >>
  first_x_assum (match_mp_tac o MP_CANON) >>
  simp[] >>
  qabbrev_tac`x = pat_to_Cpat m p` >>
  PairCases_on`x`>>fs[]>>
  conj_tac >- (
    metis_tac[FST_pat_to_Cpat_bvars,FST] ) >>
  metis_tac[pmatchTheory.pat_to_Cpat_cnmap,FST] )

val v_to_Cv_mvars_SUBMAP = store_thm("v_to_Cv_mvars_SUBMAP",
  ``(∀mv m v menv mv'. ALL_DISTINCT (MAP FST menv) ∧ closed menv v ∧ mv = (MAP FST o_f alist_to_fmap menv) ∧ mv ⊑ mv' ⇒ v_to_Cv mv' m v = v_to_Cv mv m v) ∧
    (∀mv m v menv mv'. ALL_DISTINCT (MAP FST menv) ∧ EVERY (closed menv) v ∧ mv = (MAP FST o_f alist_to_fmap menv)∧ mv ⊑ mv' ⇒ vs_to_Cvs mv' m v = vs_to_Cvs mv m v) ∧
    (∀mv m v menv mv'. ALL_DISTINCT (MAP FST menv) ∧ EVERY (closed menv) (MAP SND v) ∧ mv = (MAP FST o_f alist_to_fmap menv)∧ mv ⊑ mv' ⇒ env_to_Cenv mv' m v = env_to_Cenv mv m v)``,
  ho_match_mp_tac v_to_Cv_ind >>
  simp[v_to_Cv_def] >>
  conj_tac >- (
    rw[] >> fs[] >- (
      first_x_assum match_mp_tac >>
      fs[Once closed_cases] ) >>
    AP_TERM_TAC >>
    match_mp_tac (CONJUNCT1 exp_to_Cexp_mvars_SUBMAP) >>
    simp[] >>
    fs[Once closed_cases] >>
    fsrw_tac[DNF_ss][SUBSET_DEF,MEM_MAP,MEM_FLAT,FLOOKUP_DEF] >>
    rw[] >>
    first_x_assum(qspec_then`Long mn x`mp_tac) >>
    simp[] >>
    strip_tac >>
    HINT_EXISTS_TAC >> simp[] >>
    qexists_tac`y`>>simp[] >>
    imp_res_tac ALOOKUP_ALL_DISTINCT_MEM >>
    qmatch_assum_rename_tac`mn = FST z`[] >>
    PairCases_on`z` >>
    pop_assum(qspecl_then[`z1`,`z0`]mp_tac) >>
    simp[] >> strip_tac >>
    imp_res_tac ALOOKUP_SOME_FAPPLY_alist_to_fmap >>
    fs[] ) >>
  rw[] >- (
    first_x_assum match_mp_tac >>
    fs[Once closed_cases] ) >>
  match_mp_tac (CONJUNCT1 (CONJUNCT2 exp_to_Cexp_mvars_SUBMAP)) >>
  simp[] >>
  fs[Once closed_cases] >>
  fsrw_tac[DNF_ss][SUBSET_DEF,MEM_MAP,MEM_FLAT,FLOOKUP_DEF] >>
  rw[] >>
  fsrw_tac[DNF_ss][FV_defs_MAP,UNCURRY] >>
  qmatch_assum_rename_tac`MEM d defs`[] >>
  PairCases_on`d`>>fs[] >>
  first_x_assum(qspecl_then[`d0`,`d1`,`d2`]mp_tac) >>
  simp[] >>
  disch_then(qspec_then`Long mn x`mp_tac) >>
  simp[] >>
  strip_tac >>
  HINT_EXISTS_TAC >> simp[] >>
  qmatch_assum_rename_tac`x = FST z`[] >>
  qexists_tac`z`>>simp[] >>
  imp_res_tac ALOOKUP_ALL_DISTINCT_MEM >>
  qmatch_assum_rename_tac`mn = FST w`[] >>
  PairCases_on`w` >>
  pop_assum(qspecl_then[`w1`,`w0`]mp_tac) >>
  simp[] >> strip_tac >>
  imp_res_tac ALOOKUP_SOME_FAPPLY_alist_to_fmap >>
  fs[] )

val err_to_Cerr_def = Define`
  (err_to_Cerr (Rraise Bind_error) = Craise CBind_excv) ∧
  (err_to_Cerr (Rraise Div_error) = Craise CDiv_excv) ∧
  (err_to_Cerr (Rraise Eq_error) = Craise CEq_excv) ∧
  (err_to_Cerr (Rraise (Int_error n)) = Craise (CLitv (IntLit n))) ∧
  (err_to_Cerr (Rtype_error) = Ctype_error) ∧
  (err_to_Cerr (Rtimeout_error) = Ctimeout_error)`
val _ = export_rewrites["err_to_Cerr_def"]

val Cmap_result_Rerr = store_thm("Cmap_result_Rerr",
 ``Cmap_result f (Rerr err) = Cexc (err_to_Cerr err)``,
 Cases_on`err`>>simp[]>>Cases_on`e`>>simp[IntLangTheory.eq_exc_cn_def])

val good_cd_def = Define`
  good_cd ((ez,nz,ix),(l,cc,recs,envs),az,b) ⇔
    EVERY (λv. v < ez) envs ∧
    set (free_vars b) ⊆ count (LENGTH cc) ∧
    ∃e e'. (cc,(recs,envs),e') = (bind_fv (az,e) nz ix)`

val code_env_cd_def = Define`
  code_env_cd menv code (x,(l,ccenv,ce),(az,b)) ⇔
    (∀mn x. (mn,x) ∈ mvars b ⇒ ∃env. FLOOKUP menv mn = SOME env ∧ x < LENGTH env) ∧
    good_cd (x,(l,ccenv,ce),(az,b)) ∧
    ∃cs bc0 cc bc1.
      ((compile menv (MAP CTEnv ccenv) (TCTail az 0) 0 cs b).out = cc ++ cs.out) ∧
      EVERY (combin$C $< cs.next_label o dest_Label) (FILTER is_Label bc0) ∧ l < cs.next_label ∧
      (code = bc0 ++ Label l :: (REVERSE cc) ++ bc1)`

val closed_vlabs_def = Define`
  closed_vlabs Cmenv Cenv Cs cmnv code ⇔
    EVERY all_vlabs Cs ∧ EVERY all_vlabs Cenv ∧ all_vlabs_menv Cmenv ∧
    (∀cd. cd ∈ vlabs_list Cs ⇒ code_env_cd cmnv code cd) ∧
    (∀cd. cd ∈ vlabs_list Cenv ⇒ code_env_cd cmnv code cd) ∧
    (∀cd. cd ∈ vlabs_menv Cmenv ⇒ code_env_cd cmnv code cd)`

val Cevaluate_closed_vlabs = store_thm("Cevaluate_closed_vlabs",
  ``∀menv s env exp res cmnv code.
    closed_vlabs menv env (SND s) cmnv code ∧
    Cevaluate menv s env exp res ∧ all_labs exp ∧
    (∀cd. MEM cd (free_labs (LENGTH env) exp) ⇒ code_env_cd cmnv code cd)
    ⇒
    closed_vlabs menv env (SND(FST res)) cmnv code ∧
    (∀v. SND res = Cval v ∨ SND res = Cexc (Craise v) ⇒
      all_vlabs v ∧
      vlabs v ⊆ vlabs_menv menv ∪ vlabs_list (SND s) ∪ vlabs_list env ∪ set (free_labs (LENGTH env) exp))``,
  rpt gen_tac >>
  simp[closed_vlabs_def] >>
  strip_tac >>
  qspecl_then[`menv`,`s`,`env`,`exp`,`res`]mp_tac(CONJUNCT1 Cevaluate_vlabs)>>
  qspecl_then[`menv`,`s`,`env`,`exp`,`res`]mp_tac(CONJUNCT1 Cevaluate_all_vlabs)>>
  simp[] >>
  rw[] >> fs[SUBSET_DEF] >>
  metis_tac[])

val closed_Clocs_def = Define`
  closed_Clocs Cmenv Cenv Cs ⇔
    (BIGUNION (IMAGE (BIGUNION o IMAGE all_Clocs o set) (FRANGE Cmenv)) ⊆ count (LENGTH Cs)) ∧
    (BIGUNION (IMAGE all_Clocs (set Cs)) ⊆ count (LENGTH Cs)) ∧
    (BIGUNION (IMAGE all_Clocs (set Cenv)) ⊆ count (LENGTH Cs))`

val Cevaluate_closed_Clocs = store_thm("Cevaluate_closed_Clocs",
  ``∀menv s env exp res.
    closed_Clocs menv env (SND s) ∧
    Cevaluate menv s env exp res
    ⇒
    closed_Clocs menv env (SND(FST res)) ∧
    (∀v. SND res = Cval v ∨ SND res = Cexc (Craise v) ⇒ all_Clocs v ⊆ count (LENGTH (SND (FST res))))``,
  rw[closed_Clocs_def] >>
  TRY (
    match_mp_tac SUBSET_TRANS >>
    HINT_EXISTS_TAC >> simp[] >>
    qspecl_then[`menv`,`s`,`env`,`exp`,`res`]mp_tac(CONJUNCT1 Cevaluate_store_SUBSET) >>
    simp[SUBSET_DEF] ) >>
  qspecl_then[`menv`,`s`,`env`,`exp`,`res`]mp_tac(CONJUNCT1 Cevaluate_Clocs) >>
  simp[])

(*
(* TODO: move *)
val find_index_APPEND1 = store_thm("find_index_APPEND1",
  ``∀l1 n l2 m i. (find_index n (l1 ++ l2) m = SOME i) ∧ (i < m+LENGTH l1) ⇒ (find_index n l1 m = SOME i)``,
  Induct >> simp[find_index_def] >- (
    spose_not_then strip_assume_tac >>
    imp_res_tac find_index_LESS_LENGTH >>
    DECIDE_TAC ) >>
  rw[] >> res_tac >>
  first_x_assum match_mp_tac >>
  simp[])

val find_index_APPEND2 = store_thm("find_index_APPEND2",
  ``∀l1 n l2 m i. (find_index n (l1 ++ l2) m = SOME i) ∧ (m + LENGTH l1 ≤ i) ⇒ (find_index n l2 (m+LENGTH l1) = SOME i)``,
  Induct >> simp[find_index_def] >>
  rw[] >> fsrw_tac[ARITH_ss][] >>
  res_tac >> fsrw_tac[ARITH_ss][ADD1])

val syneq_exp_trans_matchable = store_thm("syneq_exp_trans_matchable",
  ``∀ez1 ez2 ez3 e1 e2 e3 V V' U.
    syneq_exp ez1 ez2 V e1 e2 ∧ syneq_exp ez2 ez3 V' e2 e3 ∧
    (∀x y. (V' O V) x y ∧ x < ez1 ∧ y < ez3 ⇒ U x y)
    ⇒
    syneq_exp ez1 ez3 U e1 e3``,
  rw[] >>
  imp_res_tac (CONJUNCT1 syneq_exp_trans) >>
  match_mp_tac (MP_CANON (CONJUNCT1 syneq_exp_mono_V)) >>
  HINT_EXISTS_TAC >> simp[])

val syneq_exp_mkshift_both = store_thm("syneq_exp_mkshift_both",
  ``∀y1 y2 z1 z2 V f k e1 e2 U.
    syneq_exp y1 y2 U e1 e2 ∧
    set(free_vars e1) ⊆ count y1 ∧
    set(free_vars e2) ⊆ count y2 ∧
    k ≤ y1 ∧ k ≤ y2 ∧ k ≤ z1 ∧ k ≤ z2 ∧
    no_labs e1 ∧ no_labs e2 ∧
    (let R = λx y. if x < k then y = x else y = f (x-k) + k in
       (∀x y. (R O U O inv R) x y ⇒ V x y)) ∧
    (∀x. MEM x (free_vars e1) ∧ k ≤ x ⇒ f (x-k)+k < z1) ∧
    (∀x. MEM x (free_vars e2) ∧ k ≤ x ⇒ f (x-k)+k < z2)
    ⇒ syneq_exp z1 z2 V (mkshift f k e1) (mkshift f k e2)``,
  rw[] >>
  match_mp_tac (MP_CANON (CONJUNCT1 syneq_exp_mono_V)) >>
  qabbrev_tac`R = λx y. if x < k then y = x else y = f (x-k) + k` >>
  qexists_tac`R O U O (inv R)` >>
  conj_tac >- (
    match_mp_tac syneq_exp_trans_matchable >>
    map_every qexists_tac[`y1`,`e1`,`inv R`] >>
    simp[RIGHT_EXISTS_AND_THM] >>
    conj_tac >- (
      match_mp_tac (MP_CANON (CONJUNCT1 syneq_exp_sym_no_labs)) >>
      simp[] >>
      match_mp_tac mkshift_thm >>
      simp[]>> simp[Abbr`R`]) >>
    qexists_tac `R O U` >>
    conj_tac >- (
      match_mp_tac syneq_exp_trans_matchable >>
      map_every qexists_tac[`y2`,`e2`,`U`] >>
      simp[] >>
      qexists_tac`R` >>
      conj_tac >- (
        match_mp_tac mkshift_thm >>
        simp[] >> simp[Abbr`R`]) >>
      simp[] ) >>
    simp[relationTheory.O_ASSOC] ) >>
  fs[LET_THM])

val free_vars_remove_mat_con = store_thm("free_vars_remove_mat_con",
  ``∀fk sk v n ps s. {v; fk} ∪ set (lshift (Cpat_vars_list ps) (free_vars sk)) ⊆ s
    ⇒ set (free_vars (remove_mat_con fk sk v n ps)) ⊆ s``,
  rpt strip_tac >> match_mp_tac SUBSET_TRANS >>
  HINT_EXISTS_TAC >>
  asm_simp_tac std_ss [free_vars_remove_mat_vp_SUBSET])

val remove_mat_vp_syneq = store_thm("remove_mat_vp_syneq",
  ``(∀p fk v sk1 sk2 z1 z2 V.
      syneq_exp (z1 + Cpat_vars p) (z2 + Cpat_vars p)
        (λx y. x < Cpat_vars p ∧ y = x ∨ Cpat_vars p ≤ x ∧ Cpat_vars p ≤ y ∧ V (x-Cpat_vars p) (y-Cpat_vars p))
        sk1 sk2 ∧
      V v v ∧ v < z1 ∧ v < z2 ∧
      V fk fk ∧ fk < z1 ∧ fk < z2 ∧
      no_labs sk1 ∧ no_labs sk2 ∧
      set (free_vars sk1) ⊆ count (z1 + Cpat_vars p) ∧
      set (free_vars sk2) ⊆ count (z2 + Cpat_vars p)
      ⇒
      syneq_exp z1 z2 V (remove_mat_vp fk sk1 v p) (remove_mat_vp fk sk2 v p)) ∧
    (∀ps fk n v sk1 sk2 z1 z2 V.
      syneq_exp (z1 + Cpat_vars_list ps) (z2 + Cpat_vars_list ps)
        (λx y. x < Cpat_vars_list ps ∧ y = x ∨ Cpat_vars_list ps ≤ x ∧ Cpat_vars_list ps ≤ y ∧ V (x-Cpat_vars_list ps) (y-Cpat_vars_list ps))
        sk1 sk2 ∧
      V v v ∧ v < z1 ∧ v < z2 ∧
      V fk fk ∧ fk < z1 ∧ fk < z2 ∧
      no_labs sk1 ∧ no_labs sk2 ∧
      set (free_vars sk1) ⊆ count (z1 + Cpat_vars_list ps) ∧
      set (free_vars sk2) ⊆ count (z2 + Cpat_vars_list ps)
      ⇒
      syneq_exp z1 z2 V (remove_mat_con fk sk1 v n ps) (remove_mat_con fk sk2 v n ps))``,
  ho_match_mp_tac(TypeBase.induction_of``:Cpat``) >>
  strip_tac >- (
    simp[] >> rw[] >>
    simp[Once syneq_exp_cases] >>
    conj_tac >- (
      simp[Once syneq_exp_cases] ) >>
    match_mp_tac (MP_CANON (CONJUNCT1 syneq_exp_mono_V)) >>
    HINT_EXISTS_TAC >>
    simp[] >> Cases >> simp[] ) >>
  strip_tac >- (
    simp[] >> rw[] >>
    simp[Once syneq_exp_cases] >>
    simp[Once syneq_exp_cases] >>
    simp[Once syneq_exp_cases] >>
    simp[Once syneq_exp_cases] >>
    fsrw_tac[ETA_ss][] >>
    simp[Once syneq_exp_cases] >>
    simp[Once syneq_exp_cases] ) >>
  strip_tac >- (
    simp[] >> rw[] >>
    simp[Once syneq_exp_cases] >>
    simp[Once syneq_exp_cases] >>
    simp[Once syneq_exp_cases] >>
    simp[Once syneq_exp_cases] >>
    simp[Once syneq_exp_cases] ) >>
  strip_tac >- (
    simp[] >> rw[] >>
    simp[Once syneq_exp_cases] >>
    simp[Once syneq_exp_cases] >>
    simp[Once syneq_exp_cases] >>
    first_x_assum match_mp_tac >>
    simp[] >>
    reverse conj_tac >- (
      fsrw_tac[DNF_ss][SUBSET_DEF] >>
      rw[] >> simp[] >>
      res_tac >> simp[] ) >>
    simp[shift_def] >>
    match_mp_tac syneq_exp_mkshift_both >>
    qmatch_assum_abbrev_tac`syneq_exp zp1 zp2 U sk1 sk2` >>
    map_every qexists_tac[`zp1`,`zp2`,`U`] >>
    simp[] >>
    simp[Abbr`zp1`,Abbr`zp2`] >>
    reverse conj_tac >- (
      fsrw_tac[DNF_ss][SUBSET_DEF] >>
      rw[] >> res_tac >> simp[] ) >>
    simp[relationTheory.inv_DEF,relationTheory.O_DEF,Abbr`U`] >>
    map_every qx_gen_tac[`x`,`y`] >>
    Cases_on `x < Cpat_vars p`>>simp[]>>
    Cases_on `y < Cpat_vars p`>>simp[]>>
    simp_tac(srw_ss()++DNF_ss++ARITH_ss)[]) >>
  strip_tac >- (
    rw[] >> fsrw_tac[ETA_ss][] ) >>
  rw[] >>
  simp[Once syneq_exp_cases] >>
  conj_tac >- (
    simp[Once syneq_exp_cases] >>
    simp[Once syneq_exp_cases] ) >>
  first_x_assum match_mp_tac >>
  simp[] >>
  reverse conj_tac >- (
    conj_tac >>
    match_mp_tac free_vars_remove_mat_con >>
    fsrw_tac[DNF_ss,ARITH_ss][SUBSET_DEF] >>
    rw[] >> simp[] >>
    qmatch_assum_rename_tac`MEM z (free_vars sk)`[] >>
    qpat_assum`∀x. MEM x (free_vars sk) ⇒ P`(qspec_then`z` mp_tac) >>
    simp[] ) >>
  first_x_assum match_mp_tac >>
  simp[] >>
  reverse conj_tac >- (
    fsrw_tac[DNF_ss][SUBSET_DEF] >>
    rw[] >> res_tac >> simp[] ) >>
  simp[shift_def] >>
  match_mp_tac syneq_exp_mkshift_both >>
  qmatch_assum_abbrev_tac`syneq_exp zp1 zp2 U sk1 sk2` >>
  map_every qexists_tac[`zp1`,`zp2`,`U`] >>
  simp[] >>
  simp[Abbr`zp1`,Abbr`zp2`] >>
  reverse conj_tac >- (
    fsrw_tac[DNF_ss][SUBSET_DEF] >>
    rw[] >> res_tac >> simp[] ) >>
  simp[relationTheory.inv_DEF,relationTheory.O_DEF,Abbr`U`] >>
  map_every qx_gen_tac[`x`,`y`] >>
  Cases_on `x < p1`>>simp[]>>
  Cases_on `y < p1`>>simp[]>>
  Cases_on `x < p2`>>simp[]>>
  Cases_on `y < p2`>>simp[]>>
  Cases_on `x < p1 + p2`>>simp[]>>
  Cases_on `y < p1 + p2`>>simp[]>>
  simp_tac(srw_ss()++DNF_ss++ARITH_ss)[])

val free_vars_remove_mat_var_matchable = store_thm("free_vars_remove_mat_var_matchable",
  ``∀v pes s. {v} ∪ BIGUNION (IMAGE (λ(p,e). set (lshift (Cpat_vars p) (free_vars e))) (set pes)) ⊆ s
    ⇒ set (free_vars (remove_mat_var v pes)) ⊆ s``,
    rpt strip_tac >> match_mp_tac SUBSET_TRANS >>
    HINT_EXISTS_TAC >>
    asm_simp_tac std_ss [free_vars_remove_mat_var_SUBSET])

val remove_mat_var_syneq = store_thm("remove_mat_var_syneq",
  ``∀v pes1 pes2 z1 z2 V.
      EVERY no_labs (MAP SND pes1) ∧
      EVERY no_labs (MAP SND pes2) ∧
      {v} ∪ BIGUNION (IMAGE (λ(p,e). set (lshift (Cpat_vars p) (free_vars e))) (set pes1)) ⊆ count z1 ∧
      {v} ∪ BIGUNION (IMAGE (λ(p,e). set (lshift (Cpat_vars p) (free_vars e))) (set pes2)) ⊆ count z2 ∧
      V v v ∧
      EVERY2 (λ(p,e1) (p',e2).
                (p' = p) ∧
                syneq_exp (z1 + Cpat_vars p) (z2 + Cpat_vars p)
                (λx y. x < Cpat_vars p ∧ (y = x) ∨
                       Cpat_vars p ≤ x ∧ Cpat_vars p ≤ y ∧ V (x-Cpat_vars p) (y-Cpat_vars p))
                e1 e2)
        pes1 pes2 ⇒
      syneq_exp z1 z2 V (remove_mat_var v pes1) (remove_mat_var v pes2)``,
  ho_match_mp_tac remove_mat_var_ind >>
  strip_tac >- (
    simp[remove_mat_var_def] >>
    simp[Once syneq_exp_cases] >>
    simp[Once syneq_exp_cases] ) >>
  rpt gen_tac >> strip_tac >>
  Cases >- simp[] >>
  PairCases_on`h` >>
  simp[remove_mat_var_def] >>
  rpt gen_tac >> strip_tac >>
  simp[Once syneq_exp_cases] >>
  qexists_tac`λx y. x = 0 ∧ y = 0` >>
  conj_tac >- (
    simp[Once syneq_exp_cases] >>
    simp[syneq_cb_aux_def] >>
    simp[shift_def] >>
    match_mp_tac syneq_exp_mkshift_both >>
    simp[] >>
    first_x_assum(qspecl_then[`t`,`z1`,`z2`,`V`]mp_tac) >>
    simp[] >> strip_tac >>
    map_every qexists_tac[`z1`,`z2`,`λx y. x < z1 ∧ y < z2 ∧ V x y`] >>
    simp[relationTheory.O_DEF,relationTheory.inv_DEF,syneq_cb_V_def] >>
    conj_tac >- (
      match_mp_tac (MP_CANON (CONJUNCT1 syneq_exp_mono_V)) >>
      qexists_tac`V` >> simp[]) >>
    conj_asm1_tac >- (
      match_mp_tac free_vars_remove_mat_var_matchable >> simp[] ) >>
    conj_asm1_tac >- (
      match_mp_tac free_vars_remove_mat_var_matchable >> simp[] ) >>
    reverse conj_tac >- fsrw_tac[DNF_ss][SUBSET_DEF] >>
    Cases >> simp[] >>
    Cases >> simp[ADD1] ) >>
  `syneq_exp (z1 + Cpat_vars p + 1) (z2 + Cpat_vars p + 1)
     (λx y. (x < Cpat_vars p + 1 ∧ y = x) ∨ Cpat_vars p + 1 ≤ x ∧ Cpat_vars p + 1 ≤ y ∧ V (x-Cpat_vars p-1) (y-Cpat_vars p-1))
     (shift 1 (Cpat_vars p) sk) (shift 1 (Cpat_vars p) h1)` by (
    simp[shift_def] >>
    match_mp_tac syneq_exp_mkshift_both >>
    qmatch_assum_abbrev_tac`syneq_exp zp1 zp2 U sk h1` >>
    map_every qexists_tac[`zp1`,`zp2`,`U`] >>
    simp[] >>
    simp[Abbr`zp1`,Abbr`zp2`] >>
    conj_asm1_tac >- (
      fsrw_tac[DNF_ss][SUBSET_DEF] >>
      rw[] >>
      Cases_on`x < Cpat_vars h0` >> simp[] >>
      metis_tac[NOT_LESS,ADD_SYM] ) >>
    conj_asm1_tac >- (
      fsrw_tac[DNF_ss][SUBSET_DEF] >>
      rw[] >>
      Cases_on`x < Cpat_vars h0` >> simp[] >>
      metis_tac[NOT_LESS,ADD_SYM] ) >>
    reverse conj_tac >- (
      fsrw_tac[DNF_ss,ARITH_ss][SUBSET_DEF] >>
      rw[] >> simp[] >> res_tac >> simp[] ) >>
    simp[Abbr`U`,relationTheory.O_DEF,relationTheory.inv_DEF] >>
    map_every qx_gen_tac[`x`,`y`] >>
    Cases_on `x < Cpat_vars p`>>simp[]>>
    Cases_on `y < Cpat_vars p`>>simp[]>>
    Cases_on `x < Cpat_vars p+1`>>simp[]>>
    Cases_on `y < Cpat_vars p+1`>>simp[]>>
    rw[] >> simp[]) >>
  match_mp_tac (CONJUNCT1 remove_mat_vp_syneq) >>
  simp[] >>
  reverse conj_tac >- (
    fsrw_tac[DNF_ss][SUBSET_DEF] >>
    rw[] >> res_tac >> simp[] ) >>
  fsrw_tac[ARITH_ss][] >>
  match_mp_tac (MP_CANON (CONJUNCT1 syneq_exp_mono_V)) >>
  HINT_EXISTS_TAC >>
  simp[] >>
  map_every qx_gen_tac[`x`,`y`] >>
  Cases_on`x < Cpat_vars p`>>simp[] >>
  Cases_on`y < Cpat_vars p`>>simp[] >>
  Cases_on`x < Cpat_vars p + 1`>>simp[])

val SND_pat_to_Cpat_with_bvars = store_thm("SND_pat_to_Cpat_with_bvars",
  ``SND (pat_to_Cpat (m with bvars := x) p) = SND (pat_to_Cpat m p)``,
  match_mp_tac (CONJUNCT1 SND_pat_to_Cpat_cnmap) >> simp[])

val FST_pat_to_Cpat_with_bvars = store_thm("FST_pat_to_Cpat_with_bvars",
  ``FST (pat_to_Cpat (m with bvars := x) p) = FST (pat_to_Cpat m p) with bvars := pat_bindings p [] ++ x``,
  simp[exp_to_Cexp_state_component_equality,pat_to_Cpat_cnmap] >>
  simp[FST_pat_to_Cpat_bvars])

val EVERY2_same = store_thm("EVERY2_same",
  ``EVERY (W P) ls ⇒ EVERY2 P ls ls``,
  simp[EVERY2_EVERY,EVERY_MEM,FORALL_PROD,MEM_ZIP,GSYM LEFT_FORALL_IMP_THM] >>
  simp[MEM_EL,GSYM LEFT_FORALL_IMP_THM])

val exp_to_Cexp_syneq = store_thm("exp_to_Cexp_syneq",
  ``∀m exp bvs bvs1 bvs2. {x | Short x ∈ FV exp} ⊆ set (bvs ++ bvs1) ∧ (set bvs1 = set bvs2) ⇒
      syneq_exp (LENGTH bvs + LENGTH bvs1) (LENGTH bvs + LENGTH bvs2)
        (λv1 v2. (v1 < LENGTH bvs ∧ (v2 = v1)) ∨
                 (LENGTH bvs ≤ v1 ∧ LENGTH bvs ≤ v2 ∧ v1 < LENGTH bvs + LENGTH bvs1 ∧ v2 < LENGTH bvs + LENGTH bvs2 ∧
                  (EL (v1 - LENGTH bvs) bvs1 = EL (v2 - LENGTH bvs) bvs2) ∧
                  (∀n. n < LENGTH bvs1 ∧ EL n bvs1 = EL (v1 - LENGTH bvs) bvs1 ⇒ v1 - LENGTH bvs ≤ n) ∧
                  (∀n. n < LENGTH bvs2 ∧ EL n bvs2 = EL (v2 - LENGTH bvs) bvs2 ⇒ v2 - LENGTH bvs ≤ n)))
        (exp_to_Cexp (m with bvars := bvs++bvs1) exp)
        (exp_to_Cexp (m with bvars := bvs++bvs2) exp)``,
  ho_match_mp_tac exp_to_Cexp_nice_ind >>
  strip_tac >- (
    rw[exp_to_Cexp_def] >>
    rw[Once syneq_exp_cases] >- (
      first_x_assum match_mp_tac >>
      fsrw_tac[DNF_ss][SUBSET_DEF] ) >>
    simp[Once syneq_exp_cases] >>
    conj_tac >- (
      rw[Once syneq_exp_cases] >>
      simp[Once syneq_exp_cases] ) >>
    conj_tac >- (
      rw[Once syneq_exp_cases] >>
      simp[Once syneq_exp_cases] ) >>
    simp[Once syneq_exp_cases] >>
    conj_tac >- (
      rw[Once syneq_exp_cases] >>
      simp[Once syneq_exp_cases] ) >>
    conj_tac >- (
      rw[Once syneq_exp_cases] >>
      simp[Once syneq_exp_cases] ) >>
    first_x_assum(qspecl_then[`x::bvs`,`bvs1`,`bvs2`]mp_tac) >>
    discharge_hyps >- (fsrw_tac[DNF_ss][SUBSET_DEF] >> metis_tac[]) >>
    simp[ADD1,EL_CONS] >> strip_tac >>
    match_mp_tac (MP_CANON (CONJUNCT1 syneq_exp_mono_V)) >>
    HINT_EXISTS_TAC >> simp[] >>
    Cases >> simp[ADD1] >>
    rw[] >> simp[] ) >>
  strip_tac >- (
    rw[exp_to_Cexp_def] >>
    rw[Once syneq_exp_cases] >>
    rw[Once syneq_exp_cases] ) >>
  strip_tac >- (
    rw[exp_to_Cexp_def] >>
    rw[Once syneq_exp_cases] >>
    rw[Once syneq_exp_cases] ) >>
  strip_tac >- (
    rw[exp_to_Cexp_def] >>
    rw[Once syneq_exp_cases] >>
    rw[Once syneq_exp_cases] ) >>
  strip_tac >- (
    rw[exp_to_Cexp_def] >>
    rw[Once syneq_exp_cases] >>
    rw[Once syneq_exp_cases] ) >>
  strip_tac >- (
    simp[exp_to_Cexp_def,FLOOKUP_DEF] >>
    rpt gen_tac >> strip_tac >>
    rw[Once syneq_exp_cases] >>
    simp[exps_to_Cexps_MAP] >>
    simp[EVERY2_MAP] >>
    fs[EVERY2_EVERY,EVERY_MEM,FORALL_PROD,MEM_ZIP,GSYM LEFT_FORALL_IMP_THM] >>
    fs[MEM_EL,GSYM LEFT_FORALL_IMP_THM] >>
    gen_tac >> strip_tac >> first_x_assum(qspec_then`n`mp_tac) >> simp[] >>
    disch_then match_mp_tac >>
    fsrw_tac[DNF_ss][SUBSET_DEF,FV_list_MAP,MEM_EL,EXTENSION] >>
    metis_tac[]) >>
  strip_tac >- (
    simp[exp_to_Cexp_def] >>
    rpt gen_tac >>
    Q.PAT_ABBREV_TAC`M ⇔ P ∨ Q` >>
    rw[Once syneq_exp_cases] >>
    Cases_on`find_index vn (bvs ++ bvs1) 0` >> simp[] >- (
      fs[GSYM find_index_NOT_MEM,markerTheory.Abbrev_def] ) >>
    Cases_on`find_index vn (bvs ++ bvs2) 0` >> simp[] >- (
      fs[GSYM find_index_NOT_MEM,markerTheory.Abbrev_def] ) >>
    imp_res_tac find_index_LESS_LENGTH >>
    fsrw_tac[ARITH_ss][] >>
    Cases_on `x < LENGTH bvs` >- (
      Q.ISPECL_THEN[`bvs`,`vn`,`bvs1`,`0`]mp_tac find_index_APPEND1 >>
      simp[] >> strip_tac >>
      imp_res_tac find_index_APPEND_same >>
      metis_tac[optionTheory.SOME_11] ) >>
    simp[] >>
    imp_res_tac find_index_APPEND2 >>
    imp_res_tac find_index_APPEND1 >>
    ntac 2 (pop_assum kall_tac) >> rfs[] >>
    Cases_on`x' < LENGTH bvs` >> fs[] >- (
      `MEM vn bvs` by metis_tac[find_index_NOT_MEM,optionTheory.NOT_SOME_NONE] >>
      Q.ISPECL_THEN[`bvs`,`vn`,`0`]mp_tac find_index_MEM >>
      discharge_hyps >- rw[] >>
      strip_tac >> fs[] >>
      `SOME x = SOME i` by metis_tac[find_index_APPEND_same] >>
      fs[] ) >>
    rev_full_simp_tac(srw_ss()++ARITH_ss)[] >>
    `MEM vn bvs1` by metis_tac[find_index_NOT_MEM,optionTheory.NOT_SOME_NONE] >>
    Q.ISPECL_THEN[`bvs1`,`vn`,`LENGTH bvs`]mp_tac find_index_MEM >>
    simp[] >> fsrw_tac[ARITH_ss][] >>
    Q.ISPECL_THEN[`bvs2`,`vn`,`LENGTH bvs`]mp_tac find_index_MEM >>
    fs[EXTENSION] >>
    discharge_hyps >- PROVE_TAC[] >>
    rw[] >> simp[] >> fsrw_tac[ARITH_ss][] >>
    fs[find_index_LEAST_EL] >>
    fsrw_tac[ARITH_ss][] >>
    qmatch_rename_tac`z ≤ n`[] >>
    TRY(qpat_assum`EL z bvs2 = X`(assume_tac o SYM)>>fs[]) >>
    qpat_assum`X = z`(SUBST1_TAC o SYM) >>
    numLib.LEAST_ELIM_TAC >>
    metis_tac[NOT_LESS]) >>
  strip_tac >- (
    rw[exp_to_Cexp_def] >>
    rw[Once syneq_exp_cases] >>
    rw[Once syneq_exp_cases] ) >>
  strip_tac >- (
    rw[exp_to_Cexp_def] >>
    rw[Once syneq_exp_cases] >>
    qexists_tac`λv1 v2. (v1 = 0) ∧ (v2 = v1)` >>
    simp[] >>
    simp[Once syneq_exp_cases] >>
    simp[syneq_cb_aux_def] >>
    simp[shift_def] >>
    reverse conj_tac >- simp[Once syneq_exp_cases] >>
    match_mp_tac syneq_exp_trans_matchable >>
    Q.PAT_ABBREV_TAC`e1 = exp_to_Cexp X exp` >>
    map_every qexists_tac[`LENGTH bvs + LENGTH bvs1 + 1`,`e1`,`inv (λx y. ((x = 0) ∧ (y = 0)) ∨ (x ≠ 0) ∧ (y = x + 1))`] >>
    simp[RIGHT_EXISTS_AND_THM] >>
    conj_tac >- (
      match_mp_tac (MP_CANON (CONJUNCT1 syneq_exp_sym_no_labs)) >>
      reverse conj_tac >- simp[Abbr`e1`] >>
      match_mp_tac mkshift_thm >>
      simp[Abbr`e1`] >>
      match_mp_tac free_vars_exp_to_Cexp_matchable >>
      fsrw_tac[DNF_ss,ARITH_ss][SUBSET_DEF,lem,ADD1] ) >>
    qexists_tac`λx y. if x = 0 then y = 0 else
                      if x-1 < LENGTH bvs then y = x + 1 else
                      2+LENGTH bvs ≤ y ∧ (EL (x-LENGTH bvs-1) bvs1 = EL (y-LENGTH bvs-2) bvs2) ∧
                      (∀n. n < LENGTH bvs1 ∧ EL n bvs1 = EL (x-LENGTH bvs-1) bvs1 ⇒ x-LENGTH bvs-1 ≤ n) ∧
                      (∀n. n < LENGTH bvs2 ∧ EL n bvs2 = EL (y-LENGTH bvs-2) bvs2 ⇒ y-LENGTH bvs-2 ≤ n)` >>
    conj_tac >- (
      match_mp_tac syneq_exp_trans_matchable >>
      first_x_assum(qspecl_then[`vn::bvs`,`bvs1`,`bvs2`]mp_tac) >>
      discharge_hyps >- ( fsrw_tac[DNF_ss][SUBSET_DEF,lem] ) >>
      simp[ADD1] >>
      Q.PAT_ABBREV_TAC`e2 = exp_to_Cexp X exp` >>
      strip_tac >>
      map_every qexists_tac[`LENGTH bvs + LENGTH bvs2 + 1`,`e2`] >>
      simp[] >> HINT_EXISTS_TAC >>
      simp[] >>
      qexists_tac`λx y. ((x = 0) ∧ (y = 0)) ∨ (x ≠ 0) ∧ (y = x + 1)` >>
      conj_tac >- (
        match_mp_tac mkshift_thm >>
        simp[Abbr`e2`] >>
        match_mp_tac free_vars_exp_to_Cexp_matchable >>
        fsrw_tac[DNF_ss,ARITH_ss][SUBSET_DEF,lem] ) >>
      simp[relationTheory.O_DEF] >>
      Cases >> simp[ADD1] >>
      Cases >> simp[ADD1] >>
      rw[] >> simp[] >>
      fsrw_tac[ARITH_ss][] >>
      qmatch_rename_tac`a + 1 ≤ b + (LENGTH bvs + 2)`[] >>
      qsuff_tac`a ≤ b + (LENGTH bvs + 1)` >- DECIDE_TAC >>
      first_x_assum match_mp_tac >>
      simp[]) >>
    simp[relationTheory.O_DEF,relationTheory.inv_DEF] >>
    simp[syneq_cb_V_def] >>
    Cases >> simp[] >>
    Cases >> simp[ADD1] >>
    rw[] >> simp[] >>
    qmatch_rename_tac`a ≤ b + (LENGTH bvs + 1)`[] >>
    qsuff_tac`a + 1 ≤ b + (LENGTH bvs + 2)` >- DECIDE_TAC >>
    first_x_assum match_mp_tac >>
    simp[]) >>
  strip_tac >- (
    simp[exp_to_Cexp_def] >>
    rw[] >>
    Cases_on`opn_to_prim2 opn`>>simp[]>-(
      rw[Once syneq_exp_cases] >>
      first_x_assum match_mp_tac >>
      fsrw_tac[DNF_ss][SUBSET_DEF] ) >>
    simp[Once syneq_exp_cases] >>
    conj_tac >- (
      first_x_assum match_mp_tac >>
      fsrw_tac[DNF_ss][SUBSET_DEF] ) >>
    simp[Once syneq_exp_cases] >>
    conj_tac >- (
      simp[shift_def] >>
      match_mp_tac syneq_exp_mkshift_both >>
      simp[] >>
      last_x_assum(qspecl_then[`bvs`,`bvs1`,`bvs2`]mp_tac) >>
      discharge_hyps >- fsrw_tac[DNF_ss][SUBSET_DEF] >>
      strip_tac >>
      qmatch_assum_abbrev_tac`syneq_exp y1 y2 U X Y` >>
      map_every qexists_tac[`y1`,`y2`,`U`] >>
      unabbrev_all_tac >> simp[] >>
      conj_asm1_tac >- (
        match_mp_tac free_vars_exp_to_Cexp_matchable >>
        fsrw_tac[DNF_ss][SUBSET_DEF] ) >>
      conj_asm1_tac >- (
        match_mp_tac free_vars_exp_to_Cexp_matchable >>
        fsrw_tac[DNF_ss][SUBSET_DEF] ) >>
      reverse conj_tac >- (
        fsrw_tac[DNF_ss,ARITH_ss][SUBSET_DEF] >>
        rw[] >> res_tac >> simp[] ) >>
      simp[relationTheory.O_DEF,relationTheory.inv_DEF] >>
      Cases >> simp[] >>
      Cases >> simp[ADD1] >>
      rw[] >> simp[] >>
      rw[] >>
      qmatch_rename_tac`a + 1 ≤ b + (LENGTH bvs + 1)`[] >>
      (qsuff_tac`a ≤ b + LENGTH bvs` >- DECIDE_TAC) >>
      first_x_assum match_mp_tac >> simp[]) >>
    simp[Once syneq_exp_cases] >>
    conj_tac >- (
      simp[Once syneq_exp_cases] >>
      conj_tac >> simp[Once syneq_exp_cases] ) >>
    conj_tac >- (
      simp[Once syneq_exp_cases] >>
      simp[Once syneq_exp_cases] ) >>
    simp[Once syneq_exp_cases] >>
    conj_tac >> simp[Once syneq_exp_cases] ) >>
  strip_tac >- (
    gen_tac >> Cases >>
    simp[exp_to_Cexp_def] >>
    rw[] >>
    rw[Once syneq_exp_cases] >>
    TRY (
      first_x_assum match_mp_tac >>
      fsrw_tac[DNF_ss][SUBSET_DEF] >>
      NO_TAC) >>
    rw[Once syneq_exp_cases,shift_def] >>
    TRY (
      first_x_assum match_mp_tac >>
      fsrw_tac[DNF_ss][SUBSET_DEF] >>
      NO_TAC) >>
    TRY (
      match_mp_tac syneq_exp_mkshift_both >>
      last_x_assum(qspecl_then[`bvs`,`bvs1`,`bvs2`]mp_tac) >>
      discharge_hyps >- fsrw_tac[DNF_ss][SUBSET_DEF] >> strip_tac >>
      qmatch_assum_abbrev_tac`syneq_exp y1 y2 U e1 e2` >>
      map_every qexists_tac[`y1`,`y2`,`U`] >>
      simp[] >>
      conj_tac >- simp[Abbr`U`] >>
      conj_asm1_tac >- (
        simp[Abbr`e1`,Abbr`y1`] >>
        match_mp_tac free_vars_exp_to_Cexp_matchable >>
        fsrw_tac[DNF_ss][SUBSET_DEF] ) >>
      conj_asm1_tac >- (
        simp[Abbr`e2`,Abbr`y2`] >>
        match_mp_tac free_vars_exp_to_Cexp_matchable >>
        fsrw_tac[DNF_ss][SUBSET_DEF] ) >>
      conj_tac >- simp[Abbr`e1`] >>
      conj_tac >- simp[Abbr`e2`] >>
      conj_tac >- (
        simp[relationTheory.O_DEF,relationTheory.inv_DEF,Abbr`U`] >>
        Cases >> simp[] >>
        Cases >> simp[ADD1] >>
        rw[] >> simp[] >>
        rw[] >>
        qmatch_rename_tac`a + 1 ≤ b + (LENGTH bvs + 1)`[] >>
        (qsuff_tac`a ≤ b + LENGTH bvs` >- DECIDE_TAC) >>
        first_x_assum match_mp_tac >> simp[]) >>
      fsrw_tac[DNF_ss][SUBSET_DEF] >> NO_TAC) >>
    TRY (
      rw[Once syneq_exp_cases] >>
      rw[Once syneq_exp_cases] >>
      rw[Once syneq_exp_cases] >>
      simp[] >> NO_TAC)) >>
  strip_tac >- (
    simp[exp_to_Cexp_def] >>
    rw[] >>
    rw[Once syneq_exp_cases] >>
    first_x_assum match_mp_tac >>
    fsrw_tac[DNF_ss][SUBSET_DEF] ) >>
  strip_tac >- (
    simp[exp_to_Cexp_def] >>
    rw[] >>
    rw[Once syneq_exp_cases] >>
    first_x_assum match_mp_tac >>
    fsrw_tac[DNF_ss][SUBSET_DEF] ) >>
  strip_tac >- (
    simp[exp_to_Cexp_def] >>
    rw[] >>
    rw[Once syneq_exp_cases] >>
    first_x_assum match_mp_tac >>
    fsrw_tac[DNF_ss][SUBSET_DEF] ) >>
  strip_tac >- (
    simp[exp_to_Cexp_def] >>
    rw[] >>
    rw[Once syneq_exp_cases] >>
    first_x_assum match_mp_tac >>
    fsrw_tac[DNF_ss][SUBSET_DEF] ) >>
  strip_tac >- (
    gen_tac >> Cases >>
    simp[exp_to_Cexp_def] >>
    rw[] >>
    rw[Once syneq_exp_cases] >>
    TRY (
      first_x_assum match_mp_tac >>
      fsrw_tac[DNF_ss][SUBSET_DEF] >> NO_TAC) >>
    rw[Once syneq_exp_cases] ) >>
  strip_tac >- (
    simp[exp_to_Cexp_def] >>
    rw[] >>
    rw[Once syneq_exp_cases] >>
    first_x_assum match_mp_tac >>
    fsrw_tac[DNF_ss][SUBSET_DEF] ) >>
  strip_tac >- (
    simp[exp_to_Cexp_def] >>
    rw[] >>
    rw[Once syneq_exp_cases] >- (
      first_x_assum match_mp_tac >>
      fsrw_tac[DNF_ss][SUBSET_DEF] ) >>
    simp[pes_to_Cpes_MAP,MAP_MAP_o,LAMBDA_PROD,combinTheory.o_DEF] >>
    simp[UNCURRY] >>
    simp[SND_pat_to_Cpat_with_bvars] >>
    simp[FST_pat_to_Cpat_with_bvars] >>
    match_mp_tac remove_mat_var_syneq >>
    simp[EVERY_MAP,UNCURRY] >>
    simp[EVERY2_MAP,UNCURRY] >>
    conj_tac >- (
      fsrw_tac[DNF_ss,ARITH_ss][FV_pes_MAP,SUBSET_DEF,FORALL_PROD,MEM_MAP] >>
      rw[] >> simp[] >>
      qmatch_assum_abbrev_tac`MEM v (free_vars (exp_to_Cexp s e))` >>
      qspecl_then[`s`,`e`]mp_tac free_vars_exp_to_Cexp >>
      discharge_hyps >- (
        fsrw_tac[DNF_ss][Abbr`s`,SUBSET_DEF] >>
        metis_tac[] ) >>
      fsrw_tac[DNF_ss][SUBSET_DEF,Abbr`s`] >>
      disch_then(qspec_then`v`mp_tac) >>
      simp[] ) >>
    conj_tac >- (
      fsrw_tac[DNF_ss,ARITH_ss][FV_pes_MAP,SUBSET_DEF,FORALL_PROD,MEM_MAP] >>
      rw[] >> simp[] >>
      qmatch_assum_abbrev_tac`MEM v (free_vars (exp_to_Cexp s e))` >>
      qspecl_then[`s`,`e`]mp_tac free_vars_exp_to_Cexp >>
      discharge_hyps >- (
        fsrw_tac[DNF_ss][Abbr`s`,SUBSET_DEF] >>
        metis_tac[] ) >>
      fsrw_tac[DNF_ss][SUBSET_DEF,Abbr`s`] >>
      disch_then(qspec_then`v`mp_tac) >>
      simp[] ) >>
    match_mp_tac EVERY2_same >>
    match_mp_tac EVERY_MEM_MONO >>
    HINT_EXISTS_TAC >> simp[] >>
    simp[FORALL_PROD] >>
    map_every qx_gen_tac[`p`,`e`] >> strip_tac >>
    simp[shift_def] >>
    match_mp_tac syneq_exp_mkshift_both >>
    simp[] >>
    first_x_assum(qspecl_then[`pat_bindings p [] ++ bvs`,`bvs1`,`bvs2`]mp_tac) >>
    discharge_hyps >- (
      fsrw_tac[DNF_ss][SUBSET_DEF,FV_pes_MAP,FORALL_PROD] >>
      metis_tac[] ) >>
    simp[] >> strip_tac >>
    qmatch_assum_abbrev_tac`syneq_exp z1 z2 U e1 e2` >>
    map_every qexists_tac[`z1`,`z2`,`U`] >>
    conj_tac >- simp[Abbr`U`] >>
    conj_asm1_tac >- (
      simp[Abbr`z1`,Abbr`e1`] >>
      match_mp_tac free_vars_exp_to_Cexp_matchable >>
      simp[] >>
      fsrw_tac[DNF_ss][SUBSET_DEF,FV_pes_MAP,FORALL_PROD] >>
      metis_tac[] ) >>
    conj_asm1_tac >- (
      simp[Abbr`z2`,Abbr`e2`] >>
      match_mp_tac free_vars_exp_to_Cexp_matchable >>
      simp[] >>
      fsrw_tac[DNF_ss][SUBSET_DEF,FV_pes_MAP,FORALL_PROD] >>
      metis_tac[] ) >>
    simp[Abbr`z1`,Abbr`z2`] >>
    reverse conj_tac >- (
      fsrw_tac[DNF_ss][SUBSET_DEF] >>
      rw[] >> res_tac >> simp[] ) >>
    simp[relationTheory.O_DEF,relationTheory.inv_DEF] >>
    simp[Abbr`U`] >>
    map_every qx_gen_tac[`x`,`y`] >>
    Cases_on `x < LENGTH (pat_bindings p [])` >> simp[] >>
    Cases_on `y < LENGTH (pat_bindings p [])` >> simp[] >>
    Cases_on`x`>>simp[]>>
    Cases_on`y`>>simp[ADD1]>>
    Cases_on`n < LENGTH bvs`>>simp[]>>
    Cases_on`n' < LENGTH bvs`>>simp[]>>
    Cases_on`n < LENGTH (pat_bindings p [])`>>simp[]>>
    Cases_on`n' < LENGTH (pat_bindings p [])`>>simp[]>>
    rw[] >> simp[] >>
    rw[] >> simp[] >>
    qmatch_rename_tac`a + 1 ≤ b + (c + (d + 1))`[] >>
    (qsuff_tac`a ≤ b + (c + d)` >- DECIDE_TAC) >>
    first_x_assum match_mp_tac >>
    simp[]) >>
  strip_tac >- (
    simp[exp_to_Cexp_def] >> rw[] >>
    rw[Once syneq_exp_cases] >- (
      first_x_assum match_mp_tac >>
      fsrw_tac[DNF_ss][SUBSET_DEF] ) >>
    first_x_assum(qspecl_then[`vn::bvs`,`bvs1`,`bvs2`]mp_tac) >>
    discharge_hyps >- (fsrw_tac[DNF_ss][SUBSET_DEF] >> metis_tac[]) >>
    simp[ADD1,EL_CONS] >> strip_tac >>
    match_mp_tac (MP_CANON (CONJUNCT1 syneq_exp_mono_V)) >>
    first_x_assum(qspecl_then[`vn::bvs`,`bvs1`,`bvs2`]mp_tac) >>
    discharge_hyps >- (fsrw_tac[DNF_ss][SUBSET_DEF] >> metis_tac[]) >>
    simp[ADD1] >> strip_tac >>
    HINT_EXISTS_TAC >> simp[] >>
    Cases >> simp[ADD1] >>
    rw[] >> simp[] ) >>
  strip_tac >- (
    simp[exp_to_Cexp_def] >> rw[] >>
    Q.PAT_ABBREV_TAC`MFd:string list = MAP X defs` >>
    `MFd = MAP FST defs` by (
      simp[Abbr`MFd`,MAP_EQ_f,FORALL_PROD] ) >>
    pop_assum SUBST1_TAC >> qunabbrev_tac`MFd` >>
    rw[Once syneq_exp_cases] >>
    qexists_tac`λv1 v2. v1 < LENGTH defs ∧ v2 = v1` >>
    conj_tac >- (
      simp[defs_to_Cdefs_MAP] >>
      simp[Once syneq_exp_cases] >>
      qx_gen_tac`n` >> strip_tac >>
      simp[EL_MAP,UNCURRY] >>
      simp[syneq_cb_aux_def] >>
      fs[EVERY_MEM,UNCURRY] >>
      first_x_assum(qspec_then`EL n defs`mp_tac) >>
      discharge_hyps >- metis_tac[MEM_EL] >>
      disch_then(qspecl_then[`FST(SND(EL n defs))::(MAP FST defs ++ bvs)`,`bvs1`,`bvs2`]mp_tac) >>
      discharge_hyps >- (
        qabbrev_tac`p = EL n defs` >> PairCases_on`p` >> simp[] >>
        fsrw_tac[DNF_ss][SUBSET_DEF,FV_defs_MAP,FORALL_PROD,MEM_MAP,EXISTS_PROD] >>
        metis_tac[AstTheory.id_11,MEM_EL] ) >>
      simp[ADD1] >> strip_tac >>
      match_mp_tac (MP_CANON (CONJUNCT1 syneq_exp_mono_V)) >>
      HINT_EXISTS_TAC >>
      simp[] >>
      simp[syneq_cb_V_def] >>
      Cases >> simp[] >>
      Cases >> simp[ADD1] >>
      rw[] >> simp[] >>
      rw[] >> simp[] >>
      qmatch_rename_tac`a ≤ b + (c + d)`[] >>
      (qsuff_tac`a + 1 ≤ b + (c + (d + 1))` >- DECIDE_TAC) >>
      first_x_assum match_mp_tac >>
      simp[]) >>
    Q.PAT_ABBREV_TAC`X = LENGTH (Q R defs)` >>
    `X = LENGTH defs` by simp[Abbr`X`,defs_to_Cdefs_MAP] >>
    pop_assum SUBST1_TAC >> qunabbrev_tac`X` >>
    Q.PAT_ABBREV_TAC`X = LENGTH (Q R defs)` >>
    `X = LENGTH defs` by simp[Abbr`X`,defs_to_Cdefs_MAP] >>
    pop_assum SUBST1_TAC >> qunabbrev_tac`X` >>
    last_x_assum(qspecl_then[`MAP FST defs ++ bvs`,`bvs1`,`bvs2`]mp_tac) >>
    discharge_hyps >- (
      fsrw_tac[DNF_ss][SUBSET_DEF,FV_defs_MAP,FORALL_PROD,MEM_MAP,EXISTS_PROD] >>
      metis_tac[] ) >>
    simp[] >> strip_tac >>
    match_mp_tac (MP_CANON (CONJUNCT1 syneq_exp_mono_V)) >>
    HINT_EXISTS_TAC >>
    simp[] >>
    rw[] >> simp[] >>
    Cases_on`x < LENGTH defs` >> simp[]) >>
  simp[] >>
  rw[] >>
  qabbrev_tac`q = pat_to_Cpat m p` >>
  PairCases_on`q` >> fs[] )

val enveq_v_to_Cv = store_thm("enveq_v_to_Cv",
  ``∀v1 v2. enveq v1 v2 ⇒ ∀menv m. closed menv v1 ∧ closed menv v2 ⇒ let mv = MAP FST o_f alist_to_fmap menv in syneq (v_to_Cv mv m v1) (v_to_Cv mv m v2)``,
  ho_match_mp_tac enveq_ind >>
  strip_tac >- rw[LET_THM] >>
  strip_tac >- (
    rw[LET_THM] >>
    rw[v_to_Cv_def] >>
    rw[Once syneq_cases,vs_to_Cvs_MAP] >>
    simp[EVERY2_MAP] >>
    match_mp_tac EVERY2_MEM_MONO >>
    HINT_EXISTS_TAC >> simp[FORALL_PROD] >>
    fs[EVERY2_EVERY] >>
    simp[MEM_ZIP] >>
    metis_tac[MEM_EL,EVERY_MEM]) >>
  strip_tac >- (
    rw[] >>
    simp[v_to_Cv_def] >>
    rw[Once syneq_cases] >>
    simp[env_to_Cenv_MAP] >>
    qexists_tac`λx y. x < LENGTH env1 ∧ y < LENGTH env2 ∧
      (∀n. n < LENGTH env1 ∧ FST (EL n env1) = FST (EL x env1) ⇒ x ≤ n) ∧
      (∀n. n < LENGTH env2 ∧ FST (EL n env2) = FST (EL y env2) ⇒ y ≤ n) ∧
      syneq (v_to_Cv mv m (SND (EL x env1))) (v_to_Cv mv m (SND (EL y env2)))` >>
    qexists_tac`λx y. x = 0 ∧ y = 0` >>
    simp[] >>
    conj_tac >- (rw[] >> simp[EL_MAP]) >>
    simp[Once syneq_exp_cases] >>
    simp[syneq_cb_aux_def] >>
    simp[shift_def] >>
    match_mp_tac syneq_exp_mkshift_both >>
    qspecl_then[`<| mvars := mv; cnmap := m |>`,`e`,`[vn]`,`MAP FST env1`,`MAP FST env2`]mp_tac exp_to_Cexp_syneq >>
    discharge_hyps >- (
      fs[Once closed_cases] >>
      conj_tac >- (
        fsrw_tac[DNF_ss][SUBSET_DEF,MEM_MAP,MEM_FLAT,EXISTS_PROD] >>
        rw[] >> res_tac >> fs[] >> metis_tac[] ) >>
      fs[ALIST_REL_fmap_rel,fmap_rel_def] ) >>
    simp[] >>
    strip_tac >>
    qmatch_assum_abbrev_tac`syneq_exp z1 z2 U e1 e2` >>
    map_every qexists_tac[`z1`,`z2`,`U`] >>
    simp[Abbr`z1`,Abbr`z2`,Abbr`U`] >>
    conj_asm1_tac >- (
      simp[Abbr`e1`] >>
      match_mp_tac free_vars_exp_to_Cexp_matchable >>
      fs[Once closed_cases] >>
      fsrw_tac[DNF_ss,ARITH_ss][SUBSET_DEF] >>
      fsrw_tac[DNF_ss][SUBSET_DEF,MEM_MAP,MEM_FLAT,EXISTS_PROD] >>
      rw[] >> res_tac >> fs[] >> metis_tac[] ) >>
    conj_asm1_tac >- (
      simp[Abbr`e2`] >>
      match_mp_tac free_vars_exp_to_Cexp_matchable >>
      fs[Once closed_cases] >>
      fsrw_tac[DNF_ss,ARITH_ss][SUBSET_DEF] >>
      fsrw_tac[DNF_ss][SUBSET_DEF,MEM_MAP,MEM_FLAT,EXISTS_PROD] >>
      rw[] >> res_tac >> fs[] >> metis_tac[] ) >>
    reverse conj_tac >- (
      fsrw_tac[DNF_ss,ARITH_ss][SUBSET_DEF] >>
      rw[] >> res_tac >> simp[] ) >>
    simp[relationTheory.O_DEF,relationTheory.inv_DEF,syneq_cb_V_def] >>
    Cases >> simp[] >>
    Cases >> simp[ADD1] >>
    Cases_on`n + 1 < LENGTH env1 + 2` >> simp[] >>
    Cases_on`n' + 1 < LENGTH env2 + 2` >> simp[] >>
    Cases_on`n`>>simp[ADD1] >>
    Cases_on`n'`>>simp[ADD1] >>
    simp[EL_MAP] >> strip_tac >>
    fs[ALIST_REL_def] >>
    qmatch_assum_rename_tac`FST (EL a env1) = FST (EL b env2)`[] >>
    `ALOOKUP env1 (FST (EL a env1)) = SOME (SND (EL a env1))` by (
      simp[ALOOKUP_LEAST_EL] >>
      simp[MEM_MAP] >>
      fsrw_tac[ARITH_ss][ADD1] >>
      conj_tac >- metis_tac[MEM_EL] >>
      numLib.LEAST_ELIM_TAC >>
      conj_tac >- (qexists_tac`a` >> simp[EL_MAP]) >>
      rw[] >>
      `¬(a < n)` by metis_tac[EL_MAP] >>
      `n < LENGTH env1` by DECIDE_TAC >>
      `a ≤ n` by metis_tac[] >>
      `a = n` by DECIDE_TAC >>
      simp[EL_MAP] ) >>
    `ALOOKUP env2 (FST (EL b env2)) = SOME (SND (EL b env2))` by (
      simp[ALOOKUP_LEAST_EL] >>
      simp[MEM_MAP] >>
      fsrw_tac[ARITH_ss][ADD1] >>
      conj_tac >- metis_tac[MEM_EL] >>
      numLib.LEAST_ELIM_TAC >>
      conj_tac >- (qexists_tac`b` >> simp[EL_MAP]) >>
      rw[] >>
      `¬(b < n)` by metis_tac[EL_MAP] >>
      `n < LENGTH env2` by DECIDE_TAC >>
      `b ≤ n` by metis_tac[] >>
      `b = n` by DECIDE_TAC >>
      simp[EL_MAP] ) >>
    last_x_assum(qspec_then`FST (EL a env1)`mp_tac) >>
    simp[optionTheory.OPTREL_def,Abbr`mv`] >>
    disch_then match_mp_tac >>
    fs[Q.SPECL[`menv`,`Closure env1 vn e`] closed_cases,EVERY_MAP] >>
    fs[EVERY_MEM] >>
    fsrw_tac[ARITH_ss][ADD1] >>
    metis_tac[MEM_EL] ) >>
  strip_tac >- (
    rw[] >>
    simp[v_to_Cv_def] >>
    rw[Once syneq_cases] >>
    Q.PAT_ABBREV_TAC`Mfd:string list = MAP X defs` >>
    `Mfd = MAP FST defs` by (
      simp[Abbr`Mfd`,MAP_EQ_f,FORALL_PROD] ) >>
    pop_assum SUBST1_TAC >> qunabbrev_tac`Mfd` >>
    qho_match_abbrev_tac `P (the 0 (find_index vn (MAP FST defs) 0))` >>
    match_mp_tac the_find_index_suff >>
    reverse conj_tac >- fs[Once closed_cases] >>
    simp[Abbr`P`] >>
    qx_gen_tac`n` >> strip_tac >>
    simp[defs_to_Cdefs_MAP] >>
    simp[env_to_Cenv_MAP] >>
    qexists_tac`λx y. x < LENGTH env1 ∧ y < LENGTH env2 ∧
      (∀n. n < LENGTH env1 ∧ FST (EL n env1) = FST (EL x env1) ⇒ x ≤ n) ∧
      (∀n. n < LENGTH env2 ∧ FST (EL n env2) = FST (EL y env2) ⇒ y ≤ n) ∧
      syneq (v_to_Cv mv m (SND (EL x env1))) (v_to_Cv mv m (SND (EL y env2)))` >>
    qexists_tac`λx y. x < LENGTH defs ∧ x = y` >>
    simp[] >>
    conj_tac >- (rw[] >> simp[EL_MAP]) >>
    simp[Once syneq_exp_cases] >>
    simp[EL_MAP] >>
    simp[UNCURRY] >>
    simp[syneq_cb_aux_def] >>
    qx_gen_tac`k` >> strip_tac >>
    qspecl_then[`<|mvars := mv; cnmap := m|>`,`SND(SND(EL k defs))`,`FST(SND(EL k defs))::MAP FST defs`,`MAP FST env1`,`MAP FST env2`]mp_tac exp_to_Cexp_syneq >>
    discharge_hyps >- (
      fs[Once closed_cases] >>
      conj_tac >- (
        fsrw_tac[DNF_ss][SUBSET_DEF,MEM_MAP,MEM_FLAT,EXISTS_PROD] >>
        qabbrev_tac`p = EL k defs` >> PairCases_on`p` >> fs[] >>
        `MEM (p0,p1,p2) defs` by metis_tac[MEM_EL] >>
        rw[] >> res_tac >> fs[] >> metis_tac[] ) >>
      fs[ALIST_REL_fmap_rel,fmap_rel_def] ) >>
    simp[ADD1] >>
    strip_tac >>
    qmatch_assum_abbrev_tac`syneq_exp z1 z2 U e1 e2` >>
    match_mp_tac (MP_CANON (CONJUNCT1 syneq_exp_mono_V)) >>
    qexists_tac`U` >>
    simp[Abbr`z1`,Abbr`z2`,Abbr`U`] >>
    simp[relationTheory.O_DEF,relationTheory.inv_DEF,syneq_cb_V_def] >>
    Cases >> simp[] >>
    Cases >> simp[ADD1] >>
    Cases_on`n' + 1 < LENGTH defs + (LENGTH env1 + 1)` >> simp[] >>
    Cases_on`n'' + 1 < LENGTH defs + (LENGTH env2 + 1)` >> simp[] >>
    Cases_on`n' < LENGTH defs` >> simp[] >>
    Cases_on`n'' < LENGTH defs` >> simp[] >>
    simp[EL_MAP,GSYM AND_IMP_INTRO] >> strip_tac >>
    ntac 2 strip_tac >>
    conj_asm1_tac >- (
      rw[] >> res_tac >>
      fsrw_tac[ARITH_ss][] ) >>
    conj_asm1_tac >- (
      rw[] >> res_tac >>
      fsrw_tac[ARITH_ss][] ) >>
    fs[ALIST_REL_def] >>
    qmatch_assum_rename_tac`FST (EL (a - LENGTH defs) env1) = FST (EL (b - LENGTH defs) env2)`[] >>
    `ALOOKUP env1 (FST (EL (a - LENGTH defs) env1)) = SOME (SND (EL (a - LENGTH defs) env1))` by (
      simp[ALOOKUP_LEAST_EL] >>
      simp[MEM_MAP] >>
      fsrw_tac[ARITH_ss][ADD1] >>
      `a - LENGTH defs < LENGTH env1` by simp[] >>
      conj_tac >- metis_tac[MEM_EL] >>
      numLib.LEAST_ELIM_TAC >>
      conj_tac >- (qexists_tac`a - LENGTH defs` >> simp[EL_MAP]) >>
      rw[] >>
      `¬(a - LENGTH defs < n')` by metis_tac[EL_MAP] >>
      `n' < LENGTH env1` by DECIDE_TAC >>
      `a ≤ n' + LENGTH defs` by metis_tac[EL_MAP] >>
      `a - LENGTH defs = n'` by DECIDE_TAC >>
      simp[EL_MAP] ) >>
    `ALOOKUP env2 (FST (EL (b - LENGTH defs) env2)) = SOME (SND (EL (b - LENGTH defs) env2))` by (
      simp[ALOOKUP_LEAST_EL] >>
      simp[MEM_MAP] >>
      fsrw_tac[ARITH_ss][ADD1] >>
      `b - LENGTH defs < LENGTH env2` by simp[] >>
      conj_tac >- metis_tac[MEM_EL] >>
      numLib.LEAST_ELIM_TAC >>
      conj_tac >- (qexists_tac`b - LENGTH defs` >> simp[EL_MAP]) >>
      rw[] >>
      `¬(b - LENGTH defs < n')` by metis_tac[EL_MAP] >>
      `n' < LENGTH env2` by DECIDE_TAC >>
      `b ≤ n' + LENGTH defs` by metis_tac[EL_MAP] >>
      `b - LENGTH defs = n'` by DECIDE_TAC >>
      simp[EL_MAP] ) >>
    last_x_assum(qspec_then`FST (EL (a - LENGTH defs) env1)`mp_tac) >>
    simp[optionTheory.OPTREL_def,Abbr`mv`] >>
    disch_then match_mp_tac >>
    fs[Q.SPECL[`menv`,`Recclosure env1 defs vn`] closed_cases,EVERY_MAP] >>
    fs[EVERY_MEM] >>
    fsrw_tac[ARITH_ss][ADD1] >>
    `a - LENGTH defs < LENGTH env1 ∧ b - LENGTH defs < LENGTH env2` by simp[] >>
    metis_tac[MEM_EL] ) >>
  simp[])
*)

val _ = export_theory()
