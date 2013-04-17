open HolKernel bossLib boolLib miscLib boolSimps intLib pairTheory sumTheory listTheory pred_setTheory finite_mapTheory arithmeticTheory alistTheory rich_listTheory lcsymtacs
open MiniMLTheory MiniMLTerminationTheory miniMLExtraTheory evaluateEquationsTheory miscTheory intLangTheory compileTerminationTheory pmatchTheory
val _ = new_theory "expToCexp"
val fsd = full_simp_tac std_ss

(* Nicer induction *)

val exp_to_Cexp_nice_ind = save_thm(
"exp_to_Cexp_nice_ind",
exp_to_Cexp_ind
|> Q.SPECL [`P`
   ,`λs defs. EVERY (λ(d,t1,vn,t2,e). P (s with bvars := vn::s.bvars) e) defs`
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
  syneq c1 c2 (v_to_Cv m v1) w1 ⇒
  ∃env'' defs n.
    (w1 = CRecClos env'' defs n)``,
Cases_on `v1` >> rw[do_app_def,v_to_Cv_def,LET_THM] >>
fs[defs_to_Cdefs_MAP, Once syneq_cases])

val env_to_Cenv_APPEND = store_thm("env_to_Cenv_APPEND",
  ``env_to_Cenv m (l1 ++ l2) = env_to_Cenv m l1 ++ env_to_Cenv m l2``,
  rw[env_to_Cenv_MAP])
val _ = export_rewrites["env_to_Cenv_APPEND"]

val all_Clocs_v_to_Cv = store_thm("all_Clocs_v_to_Cv",
  ``(∀m (v:α v). all_Clocs (v_to_Cv m v) = all_locs v) ∧
    (∀m (vs:α v list). MAP all_Clocs (vs_to_Cvs m vs) = MAP all_locs vs) ∧
    (∀m env: α envE. MAP all_Clocs (env_to_Cenv m env) = MAP (all_locs o FST o SND) env)``,
  ho_match_mp_tac v_to_Cv_ind >>
  srw_tac[ETA_ss][v_to_Cv_def,LET_THM,defs_to_Cdefs_MAP] >>
  fs[GSYM LIST_TO_SET_MAP,MAP_MAP_o])

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

(* free vars lemmas *)

val Cpat_vars_pat_to_Cpat = store_thm(
"Cpat_vars_pat_to_Cpat",
``(∀(p:α pat) s s' Cp. (pat_to_Cpat s p = (s',Cp))
  ⇒ (Cpat_vars Cp = (LENGTH (pat_bindings p [])))) ∧
  (∀(ps:α pat list) s s' Cps. (pats_to_Cpats s ps = (s',Cps))
  ⇒ (MAP Cpat_vars Cps = MAP (λp. (LENGTH (pat_bindings p []))) ps))``,
ho_match_mp_tac (TypeBase.induction_of ``:α pat``) >>
rw[pat_to_Cpat_def,LET_THM,pairTheory.UNCURRY,pat_bindings_def] >>
rw[FOLDL_UNION_BIGUNION,IMAGE_BIGUNION] >- (
  qabbrev_tac `q = pats_to_Cpats s' ps` >>
  PairCases_on `q` >>
  fsrw_tac[ETA_ss][MAP_EQ_EVERY2,EVERY2_EVERY,EVERY_MEM,pairTheory.FORALL_PROD] >>
  first_x_assum (qspecl_then [`s'`] mp_tac) >>
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
  ``(∀(p:α pat) s. set (FST (pat_to_Cpat s p)).bvars = pat_vars p ∪ set s.bvars) ∧
    (∀(ps:α pat list) s. set (FST (pats_to_Cpats s ps)).bvars = BIGUNION (IMAGE pat_vars (set ps)) ∪ set s.bvars)``,
  ho_match_mp_tac (TypeBase.induction_of``:α pat``) >>
  rw[pat_to_Cpat_def] >> rw[Once EXTENSION]
  >- ( first_x_assum(qspec_then`s'`mp_tac) >> simp[] )
  >- ( first_x_assum(qspec_then`s`mp_tac) >> simp[] ) >>
  first_x_assum(qspec_then`m`mp_tac) >>
  first_x_assum(qspec_then`s`mp_tac) >>
  rw[] >>
  metis_tac[])

(* TODO: move *)
val CARD_UNION_LE = store_thm("CARD_UNION_LE",
  ``FINITE s ∧ FINITE t ⇒ CARD (s ∪ t) ≤ CARD s + CARD t``,
  rw[] >> imp_res_tac CARD_UNION >> fsrw_tac[ARITH_ss][])

(*
val lem = prove(``combin$C (combin$C f) = f``,simp[FUN_EQ_THM])

val CARD_BIGUNION_LE = store_thm("CARD_BIGUNION_LE",
  ``∀P n. FINITE P ⇒ (∀s. s ∈ P ⇒ FINITE s) ⇒
    CARD (BIGUNION P) ≤ ITSET (λe a. a + CARD e) P n``,
    ho_match_mp_tac ITSET_ind >>
    rw[]

val CARD_BIGUNION_LE = store_thm("CARD_BIGUNION_LE",
  ``∀P. FINITE P ⇒ (∀s. s ∈ P ⇒ FINITE s) ⇒
    CARD (BIGUNION P) ≤ SUM (MAP CARD (SET_TO_LIST P))``,
  ho_match_mp_tac FINITE_INDUCT >> rw[] >>
  simp[SUM_MAP_FOLDL] >>
  Q.PAT_ABBREV_TAC`f = (λa e. a + CARD e)` >>
  Q.ISPEC_THEN`e INSERT P`mp_tac (INST_TYPE[beta|->``:num``]ITSET_eq_FOLDL_SET_TO_LIST) >>
  simp[] >>
  disch_then(Q.ISPECL_THEN[`combin$C f`,`0:num`](mp_tac o SYM)) >>
  simp[lem] >> strip_tac >>
  ITSET_ind

  PERM_SUM
  DB.find"PERM_SUM"
  ITSET_ind
  CHOICE_IND
  DB.find"SET_TO_LIST"
  DB.find"MAP_FOLDL"
  SET_TO_LIST
  CHOICE_INDUCT
  simp[Once SET_TO_LIST_THM]
  DB.match [] ``SET_TO_LIST (a INSERT b)``
  simp[SUM_SET_THM] >>
  simp[SUM_SET_DELETE] >>
  rw[] >> fs[] >>
  match_mp_tac LESS_EQ_TRANS >>
  qexists_tac`CARD e + CARD (BIGUNION P)` >>
  conj_tac >- (
    match_mp_tac CARD_UNION_LE >> simp[] ) >>
  simp[]
  DB.find"SUM_SET"
  SUM_SET_INSERT
  conj_tac >> simp[]
  DB.match [] ``X:(num -> bool)->num``
*)

val LENGTH_FST_pat_to_Cpat_bvars = store_thm("LENGTH_FST_pat_to_Cpat_bvars",
  ``(∀(p:α pat) s l. LENGTH (FST (pat_to_Cpat s p)).bvars = LENGTH (pat_bindings p l) - LENGTH l + LENGTH s.bvars) ∧
    (∀(ps:α pat list) s l. LENGTH (FST (pats_to_Cpats s ps)).bvars = LENGTH (pats_bindings ps l) - LENGTH l + LENGTH s.bvars)``,
  ho_match_mp_tac (TypeBase.induction_of``:α pat``) >>
  srw_tac[ARITH_ss,ETA_ss][pat_to_Cpat_def,ADD1,pat_bindings_def]
  >- ( first_x_assum(qspec_then`s'`mp_tac) >> simp[] )
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
``∀s e. FV e ⊆ set s.bvars ⇒
        free_vars (exp_to_Cexp s e) ⊆ count (LENGTH s.bvars)``,
ho_match_mp_tac exp_to_Cexp_nice_ind >>
strip_tac >- (
  rw[exp_to_Cexp_def] >>
  fsrw_tac[DNF_ss,ARITH_ss][SUBSET_DEF,PRE_SUB1,ADD1] >>
  conj_tac >> Cases >> fsrw_tac[ARITH_ss,DNF_ss][ADD1,lem] >>
  strip_tac >> res_tac >> fsrw_tac[ARITH_ss][] ) >>
strip_tac >- rw[exp_to_Cexp_def] >>
strip_tac >- rw[exp_to_Cexp_def] >>
strip_tac >- (
  rw[exp_to_Cexp_def,FOLDL_UNION_BIGUNION] >>
  fsrw_tac[DNF_ss][SUBSET_DEF,EVERY_MEM,exps_to_Cexps_MAP,MEM_MAP] >>
  metis_tac[] ) >>
strip_tac >- (
  rw[exp_to_Cexp_def] >>
  imp_res_tac find_index_MEM >>
  pop_assum(qspec_then`0`mp_tac)>>rw[] >>
  rw[] ) >>
strip_tac >- (
  rw[exp_to_Cexp_def] >>
  fsrw_tac[DNF_ss,ARITH_ss][SUBSET_DEF,PRE_SUB1,ADD1] >>
  rw[] >>
  fsrw_tac[ARITH_ss][lem] >>
  res_tac >> fsrw_tac[ARITH_ss][] ) >>
strip_tac >- ( rw[exp_to_Cexp_def] >> rw[] ) >>
strip_tac >- (
  rw[exp_to_Cexp_def] >>
  BasicProvers.CASE_TAC >> rw[] >>
  fsrw_tac[DNF_ss,ARITH_ss][SUBSET_DEF,PRE_SUB1] >>
  conj_tac >> Cases >> fsrw_tac[ARITH_ss][ADD1] >>
  strip_tac >> res_tac >> fsrw_tac[ARITH_ss][] ) >>
strip_tac >- ( rw[exp_to_Cexp_def] >> rw[] ) >>
strip_tac >- ( rw[exp_to_Cexp_def] >> rw[] ) >>
strip_tac >- ( rw[exp_to_Cexp_def] >> rw[] ) >>
strip_tac >- ( rw[exp_to_Cexp_def] >> rw[] ) >>
strip_tac >- (
  rw[exp_to_Cexp_def] >>
  BasicProvers.CASE_TAC >> rw[] ) >>
strip_tac >- ( rw[exp_to_Cexp_def] >> rw[] ) >>
strip_tac >- (
  rw[exp_to_Cexp_def] >>
  rw[] >>
  simp[free_vars_remove_mat_var] >>
  unabbrev_all_tac >>
  fsrw_tac[DNF_ss,ARITH_ss][EVERY_MEM,SUBSET_DEF,FORALL_PROD,PRE_SUB1,pes_to_Cpes_MAP,LET_THM,MEM_MAP,UNCURRY] >>
  simp[GSYM FORALL_AND_THM,GSYM IMP_CONJ_THM] >>
  map_every qx_gen_tac[`pp`,`ee`,`v`] >>
  qmatch_abbrev_tac`P ⇒ Q` >>
  qunabbrev_tac`P` >>
  srw_tac[ARITH_ss][] >>
  POP_ASSUM_LIST(MAP_EVERY ASSUME_TAC) >>
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
  fsrw_tac[DNF_ss,ARITH_ss][SUBSET_DEF,PRE_SUB1,ADD1,LET_THM,FOLDL_UNION_BIGUNION,defs_to_Cdefs_MAP] >>
  fsrw_tac[DNF_ss,ARITH_ss][EVERY_MEM,FORALL_PROD] >>
  conj_tac >- (
    simp[GSYM FORALL_AND_THM] >>
    qx_gen_tac`m` >>
    POP_ASSUM_LIST(MAP_EVERY ASSUME_TAC) >>
    simp[GSYM IMP_CONJ_THM] >>
    strip_tac >>
    first_x_assum(qspec_then`m`mp_tac) >>
    simp[] >>
    qmatch_abbrev_tac`(P⇒Q)⇒R` >>
    `P` by (
      simp[Abbr`P`] >>
      fs[lem] >> rw[] >>
      POP_ASSUM_LIST(MAP_EVERY ASSUME_TAC) >>
      first_x_assum match_mp_tac >>
      fs[MEM_MAP,FORALL_PROD] ) >>
    simp[Abbr`Q`,Abbr`R`] ) >>
  simp[GSYM FORALL_AND_THM] >>
  Cases >> fs[] >>
  simp[GSYM IMP_CONJ_THM] >>
  PairCases_on`x` >>
  simp[MEM_MAP,EXISTS_PROD] >>
  qx_gen_tac`m` >> strip_tac >>
  rpt BasicProvers.VAR_EQ_TAC >>
  qmatch_assum_rename_tac`MEM (a,b,c,d,f) defs`[] >>
  POP_ASSUM_LIST(MAP_EVERY ASSUME_TAC) >>
  first_x_assum(qspecl_then[`a`,`b`,`c`,`d`,`f`]mp_tac) >>
  qpat_assum`z ∈ y`mp_tac >>
  unabbrev_all_tac >> simp[] >> strip_tac >>
  qmatch_assum_rename_tac`z ∈ free_vars X`["X"] >>
  disch_then(qspec_then`z`mp_tac) >>
  qmatch_abbrev_tac`(P⇒Q)⇒R` >>
  `P` by (
    unabbrev_all_tac >>
    qx_gen_tac`y` >> strip_tac >>
    first_x_assum(qspecl_then[`y`,`a`,`b`,`c`,`d`,`f`]mp_tac) >>
    simp[MEM_MAP,EXISTS_PROD,lem] ) >>
  simp[Abbr`Q`,Abbr`R`] ) >>
rw[exp_to_Cexp_def] >>
qabbrev_tac `q = pat_to_Cpat m p` >>
PairCases_on`q`>>fs[] )

val free_vars_exp_to_Cexp_matchable = store_thm("free_vars_exp_to_Cexp_matchable",
  ``FV e ⊆ set m.bvars ∧ count (LENGTH m.bvars) ⊆ s ⇒ free_vars (exp_to_Cexp m e) ⊆ s``,
  metis_tac[free_vars_exp_to_Cexp,SUBSET_TRANS])

(* closed lemmas *)

val v_to_Cv_closed = store_thm(
"v_to_Cv_closed",
``(∀m (v:α v). closed v ⇒ Cclosed FEMPTY (v_to_Cv m v)) ∧
  (∀m (vs:α v list). EVERY closed vs ⇒ EVERY (Cclosed FEMPTY) (vs_to_Cvs m vs)) ∧
  (∀m (env:α envE). EVERY closed (MAP (FST o SND) env) ⇒ EVERY (Cclosed FEMPTY) (env_to_Cenv m env))``,
ho_match_mp_tac v_to_Cv_ind >>
rw[v_to_Cv_def] >> rw[Cclosed_rules]
>- (
  fs[Once closed_cases] >>
  rw[Once Cclosed_cases] >>
  unabbrev_all_tac >>
  srw_tac[ARITH_ss][env_to_Cenv_MAP] >>
  qmatch_assum_abbrev_tac`z ∈ free_vars (exp_to_Cexp s e)` >>
  qspecl_then[`s`,`e`]mp_tac free_vars_exp_to_Cexp >>
  fs[Once UNION_COMM] >>
  fsrw_tac[DNF_ss,ARITH_ss][SUBSET_DEF,Abbr`s`,lem,ADD1] >>
  rw[] >> res_tac >> simp[] ) >>
fs[Once closed_cases] >>
simp[Once Cclosed_cases] >>
simp[defs_to_Cdefs_MAP,Abbr`Cdefs`,MEM_MAP,FORALL_PROD,EXISTS_PROD] >>
Q.ISPECL_THEN[`REVERSE fns`,`vn`,`0:num`]mp_tac find_index_MEM >>
`MEM vn (REVERSE fns)` by (
  unabbrev_all_tac >>
  fs[MEM_MAP,EXISTS_PROD] >>
  PROVE_TAC[] ) >>
simp[] >> strip_tac >>
`LENGTH defs = LENGTH fns`by simp[Abbr`fns`] >>
simp[] >>
fsrw_tac[DNF_ss][] >>
fsrw_tac[DNF_ss][MEM_EL] >>
rpt gen_tac >> strip_tac >>
qmatch_assum_rename_tac`(a,b,c,d,e) = EL j defs`[] >>
first_x_assum(qspecl_then[`j`,`a`,`b`,`c`,`d`,`e`]mp_tac) >>
simp[] >> strip_tac >> strip_tac >>
qmatch_assum_abbrev_tac`v ∈ free_vars (exp_to_Cexp z e)` >>
qsuff_tac`FV e ⊆ set z.bvars` >- (
  strip_tac >>
  imp_res_tac free_vars_exp_to_Cexp >>
  fsrw_tac[DNF_ss][SUBSET_DEF] >>
  pop_assum (qspec_then`v`mp_tac) >>
  simp[] >>
  unabbrev_all_tac >>
  fs[] >>
  simp[env_to_Cenv_MAP,ADD1] ) >>
unabbrev_all_tac >> fs[] >>
fsrw_tac[DNF_ss][SUBSET_DEF,MEM_MAP,FORALL_PROD,EXISTS_PROD,EL_MAP] >>
metis_tac[])

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
   ((∃env n to e. (v1 = Closure env n to e) ∧
                  (env' = bind n (v2,add_tvs (SOME 0) to) env) ∧
                  (exp' = e)) ∨
    (∃env funs n to m.
      (v1 = Recclosure env funs n) ∧
      (find_recfun n funs = SOME (m,to,exp')) ∧
      (env' = bind m (v2,add_tvs(SOME 0) to) (build_rec_env (SOME 0) funs env)))))``,
  Cases_on`v1`>>rw[do_app_def] >- rw[EQ_IMP_THM] >>
  BasicProvers.EVERY_CASE_TAC >>
  fs[optionTheory.OPTION_MAP_EQ_NONE] >>
  rw[EQ_IMP_THM] >>
  pop_assum (assume_tac o SYM) >> fs[])

(* correctness *)

(*
val v_to_Cv_inj_rwt = store_thm(
"v_to_Cv_inj_rwt",
``∀s v1 v2. (v_to_Cv s v1 = v_to_Cv s v2) = (v1 = v2)``,
probably not true until equality is corrected in the source language *)

(* TODO: categorise *)

val pat_to_Cpat_deBruijn_subst_p = store_thm("pat_to_Cpat_deBruijn_subst_p",
  ``(∀p n x m. pat_to_Cpat m (deBruijn_subst_p n x p) = pat_to_Cpat m p) ∧
    (∀ps n x m. pats_to_Cpats m (MAP (deBruijn_subst_p n x) ps) = pats_to_Cpats m ps)``,
  ho_match_mp_tac (TypeBase.induction_of``:t pat``) >>
  srw_tac[ETA_ss][deBruijn_subst_p_def,pat_to_Cpat_def])
val _ = export_rewrites["pat_to_Cpat_deBruijn_subst_p"]

val exp_to_Cexp_deBruijn_subst_e = store_thm("exp_to_Cexp_deBruijn_subst_e",
  ``∀n x e m. exp_to_Cexp m (deBruijn_subst_e n x e) = exp_to_Cexp m e``,
  ho_match_mp_tac deBruijn_subst_e_ind >>
  srw_tac[ETA_ss][deBruijn_subst_e_def] >>
  rw[exp_to_Cexp_def,exps_to_Cexps_MAP,MAP_MAP_o,MAP_EQ_f,
     defs_to_Cdefs_MAP,pes_to_Cpes_MAP,LET_THM,FORALL_PROD]
  >- ( Cases_on`bop`>>rw[exp_to_Cexp_def] )
  >- ( rw[UNCURRY,combinTheory.o_DEF] >>
       AP_TERM_TAC >>
       rw[MAP_EQ_f,FORALL_PROD] >>
       AP_TERM_TAC >>
       res_tac >> rw[] ) >>
  rw[UNCURRY,combinTheory.o_DEF] >>
  rw[LAMBDA_PROD] >>
  metis_tac[])
val _ = export_rewrites["exp_to_Cexp_deBruijn_subst_e"]

val v_to_Cv_deBruijn_subst_v = store_thm("v_to_Cv_deBruijn_subst_v",
  ``∀x v m. v_to_Cv m (deBruijn_subst_v x v) = v_to_Cv m v``,
  ho_match_mp_tac deBruijn_subst_v_ind >>
  srw_tac[ETA_ss][deBruijn_subst_v_def,v_to_Cv_def,LET_THM,MAP_REVERSE,
                  defs_to_Cdefs_MAP,vs_to_Cvs_MAP,MAP_MAP_o,MAP_EQ_f,FORALL_PROD] >>
  rw[combinTheory.o_DEF,UNCURRY,LAMBDA_PROD])
val _ = export_rewrites["v_to_Cv_deBruijn_subst_v"]

val v_to_Cv_do_tapp = store_thm("v_to_Cv_do_tapp",
  ``∀ts to v m. v_to_Cv m (do_tapp ts to v) = v_to_Cv m v``,
  rw[do_tapp_def] >>
  BasicProvers.EVERY_CASE_TAC >>
  rw[])
val _ = export_rewrites["v_to_Cv_do_tapp"]

val free_labs_exp_to_Cexp = store_thm("free_labs_exp_to_Cexp",
  ``∀s e. free_labs (exp_to_Cexp s e) = {}``,
  ho_match_mp_tac exp_to_Cexp_nice_ind >>
  rw[exp_to_Cexp_def,exps_to_Cexps_MAP,defs_to_Cdefs_MAP,pes_to_Cpes_MAP] >>
  rw[FILTER_EQ_NIL,IMAGE_EQ_SING,MEM_FILTER] >>
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
val _ = export_rewrites["free_labs_exp_to_Cexp"]

(* TODO: move *)
val syneq_shift_same = store_thm("syneq_shift_same",
 ``∀c z1 z2 V k f1 e1 f2 e2 V'.
   syneq_exp c c z1 z2 V' e1 e2 ∧
   (free_labs e1 = {}) ∧ (free_labs e2 = {}) ∧
   free_vars e1 ⊆ count z1 ∧ free_vars e2 ⊆ count z2 ∧
   k ≤ z1 ∧ k ≤ z2 ∧
   (∀x1 x2. V' x1 x2 ⇒ V (if x1 < k then x1 else (f1(x1-k)+k)) (if x2 < k then x2 else (f2(x2-k)+k))) ∧
   (∀x. k ≤ x ∧ x < z1 ⇒ k+f1(x-k) < z1) ∧ (∀x. k ≤ x ∧ x < z2 ⇒ k+f2(x-k) < z2)
   ⇒
   syneq_exp c c z1 z2 V (mkshift f1 k e1) (mkshift f2 k e2)``,
  rw[] >>
  `syneq_exp c c z1 z1 (inv (λv1 v2. if v1 < k then v2 = v1 else v2 = f1(v1-k)+k)) (mkshift f1 k e1) e1` by (
    match_mp_tac (CONJUNCT1 syneq_exp_sym) >>
    match_mp_tac mkshift_thm >>
    simp[] ) >>
  qmatch_assum_abbrev_tac`syneq_exp c c z1 z1 U se1 e1` >>
  qspecl_then[`c`,`c`,`z1`,`z1`,`U`,`se1`,`e1`]mp_tac(CONJUNCT1 syneq_exp_trans) >> simp[] >>
  disch_then(qspecl_then[`c`,`z2`,`V'`,`e2`]mp_tac) >> rw[] >>
  `syneq_exp c c z2 z2 (λv1 v2. if v1 < k then v2 = v1 else v2 = f2 (v1-k)+k) e2 (mkshift f2 k e2)` by (
    match_mp_tac mkshift_thm >> simp[] ) >>
  qmatch_assum_abbrev_tac`syneq_exp c c z2 z2 Y e2 se2` >>
  `syneq_exp c c z1 z2 (Y O (V' O U)) se1 se2` by metis_tac[syneq_exp_trans] >>
  match_mp_tac (MP_CANON (CONJUNCT1 syneq_exp_mono_V)) >>
  HINT_EXISTS_TAC >>
  unabbrev_all_tac >>
  simp[FUN_EQ_THM,relationTheory.O_DEF,relationTheory.inv_DEF] >>
  rw[] >> fsrw_tac[ARITH_ss][] >>
  metis_tac[])

(* TODO: move *)
val find_index_ALL_DISTINCT_REVERSE = store_thm("find_index_ALL_DISTINCT_REVERSE",
  ``∀ls x m j. ALL_DISTINCT ls ∧ (find_index x ls m = SOME j) ⇒ (find_index x (REVERSE ls) m = SOME (m + LENGTH ls + m - j - 1))``,
  rw[] >> imp_res_tac find_index_ALL_DISTINCT_EL_eq >>
  `ALL_DISTINCT (REVERSE ls)` by rw[ALL_DISTINCT_REVERSE] >>
  simp[find_index_ALL_DISTINCT_EL_eq] >>
  rw[] >> fsrw_tac[ARITH_ss][] >> rw[] >>
  qmatch_assum_rename_tac`z < LENGTH ls`[] >>
  qexists_tac`LENGTH ls - z - 1` >>
  lrw[EL_REVERSE,PRE_SUB1])

val syneq_defs_elim_thm = let
  val th = (List.last (CONJUNCTS syneq_exp_cases))
  val (xs,t) = strip_forall(concl th)
  val (l,r) = dest_eq t
  val (d1,d2) = dest_disj r
  val th2 = prove (mk_imp(d2,d1),
    rw[] >>
    Q.PAT_ABBREV_TAC`p = syneq_cb_aux a b c d e` >>
    PairCases_on`p` >> simp[] >>
    match_mp_tac syneq_exp_refl >>
    simp[syneq_cb_V_def] >>
    srw_tac[ARITH_ss][] >>
    Cases_on`v<p1`>>srw_tac[ARITH_ss][]>>
    Cases_on`EL n1 a12`>>
    TRY(qmatch_assum_rename_tac`EL n1 a12 = INL x`[]>>PairCases_on`x`) >>
    fs[syneq_cb_aux_def,LET_THM,UNCURRY,markerTheory.Abbrev_def]>>
    srw_tac[ARITH_ss][]>>
    Cases_on`p4 (v-p1)`>>rw[]>>
    spose_not_then strip_assume_tac >>
    fsrw_tac[ARITH_ss][])
  val th3 = UNDISCH_ALL(PROVE[]``(c ==> b) ==> (a = b \/ c) ==> (b ==> P) ==> a ==> P``)
  val th4 = INST[``a:bool``|->l,``b:bool``|->d1,``c:bool``|->d2] th3
  val th5 = DISCH_ALL(DISCH l(PROVE_HYP (SPEC_ALL th) (PROVE_HYP th2 th4)))
in Q.GEN`P`(GENL xs th5) end

val EVERY2_APPEND_suff = store_thm("EVERY2_APPEND_suff",
  ``EVERY2 R l1 l2 ∧ EVERY2 R l3 l4 ⇒ EVERY2 R (l1 ++ l3) (l2 ++ l4)``,
  metis_tac[EVERY2_APPEND])

val exp_to_Cexp_state_component_equality = DB.fetch"Compile""exp_to_Cexp_state_component_equality"

val pat_to_Cpat_acc = store_thm("pat_to_Cpat_acc",
  ``(∀(p:α pat) s s' Cp. (pat_to_Cpat s p = (s',Cp)) ⇒
      ∃ls. (s'.bvars = ls ++ s.bvars) ∧ (set ls = pat_vars p) ∧
           (pat_to_Cpat (s with bvars := []) p = (s' with bvars := ls, Cp))) ∧
    (∀(ps:α pat list) s s' Cps. (pats_to_Cpats s ps = (s',Cps)) ⇒
      ∃ls. (s'.bvars = ls ++ s.bvars) ∧ (set ls = BIGUNION (IMAGE pat_vars (set ps))) ∧
           (pats_to_Cpats (s with bvars := []) ps = (s' with bvars := ls, Cps)))``,
  ho_match_mp_tac(TypeBase.induction_of``:α pat``) >>
  rw[pat_to_Cpat_def,exp_to_Cexp_state_component_equality]
  >- (
    first_x_assum(qspec_then`s'`mp_tac) >>
    qabbrev_tac`q = pats_to_Cpats s' ps` >>
    PairCases_on`q`>>fs[LET_THM]>>rw[]>>fsrw_tac[ETA_ss][])
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
  ``∀ls s e. FV e ⊆ set s.bvars ⇒ (exp_to_Cexp (s with bvars := s.bvars ++ ls) e = exp_to_Cexp s e)``,
  gen_tac >> ho_match_mp_tac exp_to_Cexp_nice_ind >>
  rw[exp_to_Cexp_def,exps_to_Cexps_MAP,defs_to_Cdefs_MAP,pes_to_Cpes_MAP] >>
  TRY (
    fsrw_tac[DNF_ss][SUBSET_DEF,lem,EVERY_MEM,MAP_EQ_f] >>
    rw[] >> first_x_assum (match_mp_tac o MP_CANON) >>
    rw[] >> res_tac >> NO_TAC)
  >- (
    metis_tac[find_index_MEM,find_index_APPEND_same] )
  >- (
    unabbrev_all_tac >>
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
    fsrw_tac[DNF_ss][SUBSET_DEF,FORALL_PROD,MEM_MAP,EXISTS_PROD] >>
    metis_tac[] ) >>
  qabbrev_tac`q = pat_to_Cpat m p` >>
  PairCases_on`q`>>fs[])

val exp_to_Cexp_append_bvars_matchable = store_thm(
  "exp_to_Cexp_append_bvars_matchable",
  ``∀ls s s' e. FV e ⊆ set s.bvars ∧ (s'.cnmap = s.cnmap) ∧ (s'.bvars = s.bvars ++ ls) ⇒
             (exp_to_Cexp s' e = exp_to_Cexp s e)``,
  rw[] >> imp_res_tac exp_to_Cexp_append_bvars >>
  pop_assum(qspec_then`ls`strip_assume_tac) >>
  qmatch_assum_abbrev_tac`exp_to_Cexp z e = exp_to_Cexp s e` >>
  qsuff_tac`z = s'`>-PROVE_TAC[]>>
  simp[exp_to_Cexp_state_component_equality,Abbr`z`])

val exp_to_Cexp_thm1 = store_thm("exp_to_Cexp_thm1",
  ``(∀cenv s env exp res. evaluate cenv s env exp res ⇒
     FV exp ⊆ set (MAP FST env) ∧
     (EVERY closed s) ∧ (EVERY closed (MAP (FST o SND) env)) ∧
     good_cenv cenv ∧ (SND res ≠ Rerr Rtype_error) ⇒
     ∀cm. good_cmap cenv cm ⇒
       ∃Cres.
       Cevaluate FEMPTY
         (MAP (v_to_Cv cm) s)
         (env_to_Cenv cm env)
         (exp_to_Cexp (<| bvars := MAP FST env; cnmap := cm|>) exp)
         Cres ∧
         EVERY2 (syneq FEMPTY FEMPTY) (MAP (v_to_Cv cm) (FST res)) (FST Cres) ∧
         result_rel (syneq FEMPTY FEMPTY) (map_result (v_to_Cv cm) (SND res)) (SND Cres))∧
    (∀cenv s env exps res. evaluate_list cenv s env exps res ⇒
     (BIGUNION (IMAGE FV (set exps)) ⊆ set (MAP FST env)) ∧
     (EVERY closed s) ∧ (EVERY closed (MAP (FST o SND) env)) ∧
     good_cenv cenv ∧ (SND res ≠ Rerr Rtype_error) ⇒
     ∀cm. good_cmap cenv cm ⇒
       ∃Cres.
       Cevaluate_list FEMPTY
         (MAP (v_to_Cv cm) s)
         (env_to_Cenv cm env)
         (MAP (exp_to_Cexp (<| bvars := MAP FST env; cnmap := cm|>)) exps)
         Cres ∧
         EVERY2 (syneq FEMPTY FEMPTY) (MAP (v_to_Cv cm) (FST res)) (FST Cres) ∧
         result_rel (EVERY2 (syneq FEMPTY FEMPTY)) (map_result (MAP (v_to_Cv cm)) (SND res)) (SND Cres))``,
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
    qspecl_then[`cenv`,`s`,`env`,`exp`,`(s',Rerr (Rraise (Int_error n)))`]mp_tac(CONJUNCT1 evaluate_closed) >>
    fsrw_tac[DNF_ss][env_to_Cenv_MAP,SUBSET_DEF,lem] >> strip_tac >>
    first_x_assum(qspec_then`cm`mp_tac) >> simp[] >>
    disch_then(qx_choosel_then[`s3`,`v`]strip_assume_tac) >>
    CONV_TAC(RESORT_EXISTS_CONV List.rev) >>
    map_every qexists_tac[`n`,`s2`] >> simp[] >> fs[v_to_Cv_def] >>
    qmatch_assum_abbrev_tac`Cevaluate c1 s1 env1 exp1 (s3,v)` >>
    qspecl_then[`c1`,`s1`,`env1`,`exp1`,`(s3,v)`]mp_tac(CONJUNCT1 Cevaluate_syneq) >>
    simp[] >>
    disch_then(qspecl_then[`c1`,`$=`,`s2`,`env1`,`exp1`]mp_tac) >>
    simp[syneq_exp_refl,EXISTS_PROD] >>
    metis_tac[result_rel_syneq_trans,EVERY2_syneq_trans,
              result_rel_syneq_sym,EVERY2_syneq_sym]) >>
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
    fs[exp_to_Cexp_def,MEM_MAP,pairTheory.EXISTS_PROD,env_to_Cenv_MAP] >>
    rpt gen_tac >> rpt (disch_then strip_assume_tac) >> qx_gen_tac `m` >>
    fs[ALOOKUP_LEAST_EL] >>
    simp[find_index_LEAST_EL] >>
    strip_tac >>
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
    `(LEAST m. EL m (MAP FST env) = n) = (LEAST m. n = EL m (MAP FST env))` by (
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
    ntac 2 gen_tac >>
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
      rpt (first_x_assum (qspec_then `m` mp_tac)) >>
      rw[] >>
      qmatch_assum_rename_tac `syneq FEMPTY FEMPTY (v_to_Cv m v1) w1`[] >>
      qspecl_then[`cenv`,`s`,`env`,`e1`,`(s',Rval v1)`]mp_tac(CONJUNCT1 evaluate_closed) >>
      simp[] >> strip_tac >> fs[] >>
      qmatch_assum_rename_tac `syneq FEMPTY (v_to_Cv m v2) w2`[] >>
      qmatch_assum_rename_tac`SND r1 = Rval w1`[] >>
      qmatch_assum_rename_tac`SND r2 = Rval w2`[] >>
      qmatch_assum_abbrev_tac`Cevaluate FEMPTY FEMPTY sa enva e1a r1` >>
      qmatch_assum_abbrev_tac`Cevaluate FEMPTY FEMPTY sb enva e2a r2` >>
      qspecl_then[`FEMPTY`,`FEMPTY`,`sb`,`FST r1`,`enva`,`e2a`,`r2`]mp_tac Cevaluate_any_syneq_store >>
      `∀v. v ∈ FRANGE enva ⇒ Cclosed FEMPTY v` by (
        unabbrev_all_tac >>
        match_mp_tac IN_FRANGE_alist_to_fmap_suff >>
        simp[env_to_Cenv_MAP,MAP_MAP_o,combinTheory.o_DEF,MEM_MAP,EXISTS_PROD] >>
        srw_tac[DNF_ss][] >>
        match_mp_tac (CONJUNCT1 v_to_Cv_closed) >>
        fs[EVERY_MEM,FORALL_PROD,MEM_MAP,EXISTS_PROD] >>
        metis_tac[] ) >>
      `free_vars FEMPTY e2a ⊆ FDOM enva` by (
        unabbrev_all_tac >>
        fsrw_tac[DNF_ss][SUBSET_DEF] >>
        simp[env_to_Cenv_MAP,MAP_MAP_o,combinTheory.o_DEF,FST_pair,LAMBDA_PROD,FST_triple]) >>
      qspecl_then[`FEMPTY`,`FEMPTY`,`sb`,`enva`,`e2a`,`r2`]mp_tac(CONJUNCT1 Cevaluate_closed) >>
      `∀v. v ∈ FRANGE sb ⇒ Cclosed FEMPTY v` by (
        unabbrev_all_tac >>
        simp[FRANGE_store_to_Cstore,MEM_MAP] >>
        fsrw_tac[DNF_ss][EVERY_MEM] >> rw[] >>
        match_mp_tac (CONJUNCT1 v_to_Cv_closed) >>
        rw[] ) >>
      qspecl_then[`FEMPTY`,`FEMPTY`,`sa`,`enva`,`e1a`,`r1`]mp_tac(CONJUNCT1 Cevaluate_closed) >>
      `free_vars FEMPTY e1a ⊆ FDOM enva` by (
        unabbrev_all_tac >>
        fsrw_tac[DNF_ss][SUBSET_DEF] >>
        simp[env_to_Cenv_MAP,MAP_MAP_o,combinTheory.o_DEF,FST_pair,LAMBDA_PROD,FST_triple])>>
      `∀v. v ∈ FRANGE sa ⇒ Cclosed FEMPTY v` by (
        unabbrev_all_tac >>
        simp[FRANGE_store_to_Cstore,MEM_MAP] >>
        fsrw_tac[DNF_ss][EVERY_MEM] >> rw[] >>
        match_mp_tac (CONJUNCT1 v_to_Cv_closed) >>
        rw[] ) >>
      simp[] >> strip_tac >> strip_tac >>
      disch_then(Q.X_CHOOSE_THEN`r3`strip_assume_tac) >>
      qmatch_assum_rename_tac`syneq FEMPTY w2 w3`[] >>
      qmatch_assum_rename_tac `do_app s3 env (Opn opn) v1 v2 = SOME (s4,env',exp'')` [] >>
      qspecl_then[`cenv`,`s'`,`env`,`e2`,`(s3,Rval v2)`]mp_tac(CONJUNCT1 evaluate_closed) >>
      simp[] >> strip_tac >>
      Q.ISPECL_THEN[`s3`,`s4`,`env`,`Opn opn`,`v1`,`v2`,`env'`,`exp''`]mp_tac do_app_closed >>
      simp[] >> strip_tac >> fs[] >>
      fs[do_app_Opn_SOME] >>
      rpt BasicProvers.VAR_EQ_TAC >>
      qexists_tac`FST r3` >>
      qexists_tac `w1` >>
      qexists_tac `w3` >>
      qexists_tac`FST r1` >>
      PairCases_on`r1`>>PairCases_on`r3`>>
      fs[] >> rpt BasicProvers.VAR_EQ_TAC >> fs[] >>
      PairCases_on`res`>>fs[] >>
      PairCases_on`Cres`>>fs[] >>
      PairCases_on`r2`>>fs[] >>
      fs[v_to_Cv_def,Q.SPECL[`FEMPTY`,`CLitv (IntLit x)`]syneq_cases,i0_def] >>
      rpt BasicProvers.VAR_EQ_TAC >>
      fs[v_to_Cv_def,Q.SPECL[`FEMPTY`,`CLitv (IntLit x)`]syneq_cases,i0_def] >>
      rpt BasicProvers.VAR_EQ_TAC >>
      rpt(qpat_assum`T`kall_tac) >>
      `res0 = s3` by (
        qpat_assum`evaluate cenv s3 env X Y`mp_tac >>
        BasicProvers.CASE_TAC >>
        simp[Once evaluate_cases] ) >>
      BasicProvers.VAR_EQ_TAC >>
      qabbrev_tac`sc = store_to_Cstore m res0` >>
      `fmap_rel (syneq FEMPTY) sc r30` by
        metis_tac[fmap_rel_syneq_trans] >>
      Cases_on`opn`>>fs[]>>
      fs[v_to_Cv_def,opn_lookup_def,i0_def] >>
      Cases_on`n2=0`>>fs[v_to_Cv_def] )
    >- (
      qmatch_assum_rename_tac `do_app s3 env (Opb opb) v1 v2 = SOME (s4,env',exp'')` [] >>
      fs[] >>
      qmatch_assum_rename_tac`evaluate cenv s env e1 (s1,Rval v1)`[] >>
      qmatch_assum_rename_tac`evaluate cenv s1 env e2 (s2,Rval v2)`[] >>
      qspecl_then[`cenv`,`s`,`env`,`e1`,`(s1,Rval v1)`]mp_tac(CONJUNCT1 evaluate_closed) >>
      simp[] >> strip_tac >>
      qspecl_then[`cenv`,`s1`,`env`,`e2`,`(s2,Rval v2)`]mp_tac(CONJUNCT1 evaluate_closed) >>
      simp[] >> strip_tac >>
      fs[] >>
      Q.ISPECL_THEN[`s2`,`s4`,`env`,`Opb opb`,`v1`,`v2`,`env'`,`exp''`]mp_tac do_app_closed >>
      simp[] >> strip_tac >>
      fs[] >>
      rpt (first_x_assum (qspec_then `m` mp_tac)) >> rw[] >>
      qmatch_assum_rename_tac `syneq FEMPTY (v_to_Cv m v1) w1`[] >>
      qmatch_assum_rename_tac `syneq FEMPTY (v_to_Cv m v2) w2`[] >>
      Cases_on`Cres`>> Cases_on`Cres'`>> Cases_on`Cres''`>>fs[]>>rw[]>>
      fs[do_app_Opb_SOME]>>rw[]>>fs[v_to_Cv_def]>>rw[]>>fs[]>>rw[]>>
      fs[v_to_Cv_def]>>fs[Q.SPECL[`FEMPTY`,`CLitv l`]syneq_cases]>>rw[]>>
      fs[exp_to_Cexp_def]>>rw[]>>
      qabbrev_tac`sa = store_to_Cstore m s` >>
      qabbrev_tac`sb = store_to_Cstore m s1` >>
      qabbrev_tac`sc = store_to_Cstore m s2` >>
      fs[]>>rw[]>>
      qmatch_assum_rename_tac`fmap_rel (syneq FEMPTY) sb sd`[]>>
      qmatch_assum_rename_tac`fmap_rel (syneq FEMPTY) sc se`[]>>
      qabbrev_tac`enva = alist_to_fmap(env_to_Cenv m env)`>>
      qabbrev_tac`e1a = exp_to_Cexp m e1`>>
      qabbrev_tac`e2a = exp_to_Cexp m e2`>>
      qabbrev_tac`w1 = CLitv (IntLit n1)`>>
      qabbrev_tac`w2 = CLitv (IntLit n2)`>>
      `∀v. v ∈ FRANGE enva ⇒ Cclosed FEMPTY v` by (
        unabbrev_all_tac >>
        match_mp_tac IN_FRANGE_alist_to_fmap_suff >>
        simp[env_to_Cenv_MAP,MAP_MAP_o,combinTheory.o_DEF,MEM_MAP,EXISTS_PROD] >>
        srw_tac[DNF_ss][] >>
        match_mp_tac (CONJUNCT1 v_to_Cv_closed) >>
        fs[EVERY_MEM,EXISTS_PROD,MEM_MAP] >>
        metis_tac[] ) >>
      `∀v. v ∈ FRANGE sa ⇒ Cclosed FEMPTY v` by (
        unabbrev_all_tac >>
        simp[FRANGE_store_to_Cstore,MEM_MAP] >>
        srw_tac[DNF_ss][] >>
        match_mp_tac (CONJUNCT1 v_to_Cv_closed) >>
        fs[EVERY_MEM] ) >>
      `∀v. v ∈ FRANGE sb ⇒ Cclosed FEMPTY v` by (
        unabbrev_all_tac >>
        simp[FRANGE_store_to_Cstore,MEM_MAP] >>
        srw_tac[DNF_ss][] >>
        match_mp_tac (CONJUNCT1 v_to_Cv_closed) >>
        fs[EVERY_MEM] ) >>
      `∀v. v ∈ FRANGE sc ⇒ Cclosed FEMPTY v` by (
        unabbrev_all_tac >>
        simp[FRANGE_store_to_Cstore,MEM_MAP] >>
        srw_tac[DNF_ss][] >>
        match_mp_tac (CONJUNCT1 v_to_Cv_closed) >>
        fs[EVERY_MEM] ) >>
      `free_vars FEMPTY e1a ⊆ FDOM enva` by (
        unabbrev_all_tac >>
        fsrw_tac[DNF_ss][SUBSET_DEF,env_to_Cenv_MAP,MEM_MAP,
                         EXISTS_PROD,FORALL_PROD] ) >>
      `free_vars FEMPTY e2a ⊆ FDOM enva` by (
        unabbrev_all_tac >>
        fsrw_tac[DNF_ss][SUBSET_DEF,env_to_Cenv_MAP,MEM_MAP,
                         EXISTS_PROD,FORALL_PROD] ) >>
      qspecl_then[`FEMPTY`,`FEMPTY`,`sa`,`enva`,`e1a`,`(sd,Rval w1)`]mp_tac(CONJUNCT1 Cevaluate_closed) >>
      simp[] >> strip_tac >>
      qspecl_then[`FEMPTY`,`FEMPTY`,`sb`,`enva`,`e2a`,`(se,Rval w2)`]mp_tac(CONJUNCT1 Cevaluate_closed) >>
      simp[] >> strip_tac >>
      Cases_on `opb` >> fsrw_tac[DNF_ss][EXISTS_PROD,opb_lookup_def]
      >- (
        rw[Once Cevaluate_cases] >>
        rw[Once (CONJUNCT2 Cevaluate_cases)] >>
        rw[Once (CONJUNCT2 Cevaluate_cases)] >>
        rw[Once (CONJUNCT2 Cevaluate_cases)] >>
        srw_tac[DNF_ss][] >>
        qspecl_then[`FEMPTY`,`FEMPTY`,`sb`,`sd`,`enva`,`e2a`,`(se,Rval w2)`]mp_tac(Cevaluate_any_syneq_store) >>
        fsrw_tac[DNF_ss][EXISTS_PROD] >>
        qx_gen_tac`sf` >>
        qx_gen_tac`w3` >>
        strip_tac >>
        qexists_tac`sf`>>
        qexists_tac `w1` >>
        qexists_tac `w3` >>
        qexists_tac`sd`>>
        simp[] >>
        reverse conj_tac >- metis_tac[fmap_rel_syneq_trans] >>
        map_every qunabbrev_tac[`w1`,`w2`] >>
        fs[Q.SPECL[`FEMPTY`,`CLitv l`]syneq_cases] )
      >- (
        rw[Once Cevaluate_cases] >>
        srw_tac[DNF_ss][] >>
        CONV_TAC (RESORT_EXISTS_CONV List.rev) >>
        map_every qexists_tac [`w1`,`sd`] >> fs[] >>
        rw[Once Cevaluate_cases] >>
        srw_tac[DNF_ss][] >>
        qspecl_then[`FEMPTY`,`FEMPTY`,`sb`,`sd`,`enva`,`e2a`,`(se,Rval w2)`]mp_tac Cevaluate_any_syneq_store >>
        fsrw_tac[DNF_ss][EXISTS_PROD] >>
        qx_gen_tac`sf` >> qx_gen_tac`w3` >>
        strip_tac >>
        Q.PAT_ABBREV_TAC`fv = fresh_var X` >>
        qspecl_then[`FEMPTY`,`FEMPTY`,`sd`,`enva`,`e2a`,`(sf,Rval w3)`,`fv`,`w1`]mp_tac Cevaluate_FUPDATE >>
        `fv ∉ free_vars FEMPTY e2a` by (
          unabbrev_all_tac >>
          match_mp_tac fresh_var_not_in_any >>
          rw[] ) >>
        fsrw_tac[DNF_ss][EXISTS_PROD] >>
        qx_gen_tac`sg`>>qx_gen_tac`w4`>>
        strip_tac >>
        CONV_TAC (RESORT_EXISTS_CONV List.rev) >>
        map_every qexists_tac [`w4`,`sg`] >> fs[] >>
        rw[Once Cevaluate_cases] >>
        srw_tac[DNF_ss][] >>
        rw[Once (CONJUNCT2 Cevaluate_cases)] >>
        rw[Once (CONJUNCT2 Cevaluate_cases)] >>
        rw[Once (CONJUNCT2 Cevaluate_cases)] >>
        rw[FAPPLY_FUPDATE_THM,NOT_fresh_var] >>
        map_every qunabbrev_tac[`w1`,`w2`] >> rw[] >>
        fs[Q.SPECL[`FEMPTY`,`CLitv l`]syneq_cases] >> rw[] >>
        fs[Q.SPECL[`FEMPTY`,`CLitv l`]syneq_cases] >> rw[] >>
        rw[integerTheory.int_gt] >>
        metis_tac[fmap_rel_syneq_trans])
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
        qexists_tac`sd`>>
        qexists_tac`w2`>>
        qexists_tac`w1`>>
        qspecl_then[`FEMPTY`,`FEMPTY`,`sb`,`sd`,`enva`,`e2a`,`(se,Rval w2)`]mp_tac(Cevaluate_any_syneq_store) >>
        fsrw_tac[DNF_ss][EXISTS_PROD,Abbr`w2`,Abbr`w1`] >>
        qx_gen_tac`sf` >>
        qx_gen_tac`w3` >>
        strip_tac >>
        fs[Q.SPECL[`FEMPTY`,`CLitv l`]syneq_cases] >>
        `fmap_rel (syneq FEMPTY) sc sf` by PROVE_TAC[fmap_rel_syneq_trans] >>
        qexists_tac`sf`>>
        rw[CompileTheory.i1_def] >>
        ARITH_TAC )
      >- (
        rw[Once Cevaluate_cases] >>
        srw_tac[DNF_ss][] >>
        CONV_TAC (RESORT_EXISTS_CONV List.rev) >>
        map_every qexists_tac [`w1`,`sd`] >> fs[] >>
        rw[Once Cevaluate_cases] >>
        srw_tac[DNF_ss][] >>
        qspecl_then[`FEMPTY`,`FEMPTY`,`sb`,`sd`,`enva`,`e2a`,`(se,Rval w2)`]mp_tac Cevaluate_any_syneq_store >>
        fsrw_tac[DNF_ss][EXISTS_PROD] >>
        qx_gen_tac`sf` >> qx_gen_tac`w3` >>
        strip_tac >>
        Q.PAT_ABBREV_TAC`fv = fresh_var X` >>
        qspecl_then[`FEMPTY`,`FEMPTY`,`sd`,`enva`,`e2a`,`(sf,Rval w3)`,`fv`,`w1`]mp_tac Cevaluate_FUPDATE >>
        `fv ∉ free_vars FEMPTY e2a` by (
          unabbrev_all_tac >>
          match_mp_tac fresh_var_not_in_any >>
          rw[] ) >>
        fsrw_tac[DNF_ss][EXISTS_PROD] >>
        qx_gen_tac`sg`>>qx_gen_tac`w4`>>
        strip_tac >>
        CONV_TAC (RESORT_EXISTS_CONV List.rev) >>
        map_every qexists_tac [`w4`,`sg`] >> fs[] >>
        rw[Once Cevaluate_cases] >>
        srw_tac[DNF_ss][] >>
        rw[Once (CONJUNCT2 Cevaluate_cases)] >>
        rw[Once (CONJUNCT2 Cevaluate_cases)] >>
        rw[Once (CONJUNCT2 Cevaluate_cases)] >>
        rw[FAPPLY_FUPDATE_THM,NOT_fresh_var] >>
        rw[Once Cevaluate_cases] >>
        rw[Once (CONJUNCT2 Cevaluate_cases)] >>
        rw[Once (CONJUNCT2 Cevaluate_cases)] >>
        rw[Once (CONJUNCT2 Cevaluate_cases)] >>
        srw_tac[DNF_ss][] >>
        rw[FAPPLY_FUPDATE_THM,NOT_fresh_var] >>
        map_every qunabbrev_tac[`w1`,`w2`] >> rw[] >>
        fs[Q.SPECL[`FEMPTY`,`CLitv l`]syneq_cases] >> rw[] >>
        `fmap_rel (syneq FEMPTY) sc sg` by PROVE_TAC[fmap_rel_syneq_trans] >>
        fs[Q.SPECL[`FEMPTY`,`CLitv l`]syneq_cases] >> rw[] >>
        rw[CompileTheory.i1_def] >>
        ARITH_TAC) )
    >- (
      rw[Once Cevaluate_cases] >>
      srw_tac[DNF_ss][] >>
      disj1_tac >>
      rw[Once(CONJUNCT2 Cevaluate_cases)] >>
      rw[Once(CONJUNCT2 Cevaluate_cases)] >>
      rw[Once(CONJUNCT2 Cevaluate_cases)] >>
      srw_tac[DNF_ss][] >>
      fs[] >>
      qspecl_then[`cenv`,`s`,`env`,`e1`,`(s',Rval v1)`]mp_tac(CONJUNCT1 evaluate_closed) >>
      simp[]>>strip_tac >>
      qspecl_then[`cenv`,`s'`,`env`,`e2`,`(s3,Rval v2)`]mp_tac(CONJUNCT1 evaluate_closed) >>
      simp[]>>strip_tac >>
      Q.ISPECL_THEN[`s3`,`s''`,`env`,`Equality`,`v1`,`v2`,`env'`,`exp''`]mp_tac do_app_closed >>
      simp[]>>strip_tac>>
      fs[] >>
      rpt (first_x_assum (qspec_then `cm` mp_tac)) >>
      rw[EXISTS_PROD] >>
      qmatch_assum_rename_tac `syneq FEMPTY(v_to_Cv cm v1) w1`[] >>
      qmatch_assum_rename_tac `syneq FEMPTY(v_to_Cv m v2) w2`[] >>
      qabbrev_tac`sa = store_to_Cstore m s` >>
      qabbrev_tac`sb = store_to_Cstore m s'` >>
      qabbrev_tac`sc = store_to_Cstore m s3` >>
      qmatch_assum_abbrev_tac`Cevaluate FEMPTY FEMPTY sa enva e1a X` >>
      qmatch_assum_rename_tac`Abbrev(X=(sd,Rval w1))`[]>>
      qunabbrev_tac`X` >>
      qmatch_assum_abbrev_tac`Cevaluate FEMPTY FEMPTY sb enva e2a X` >>
      qmatch_assum_rename_tac`Abbrev(X=(se,Rval w2))`[]>>
      qspecl_then[`FEMPTY`,`FEMPTY`,`sb`,`sd`,`enva`,`e2a`,`X`]mp_tac Cevaluate_any_syneq_store >>
      `∀v. v ∈ FRANGE enva ⇒ Cclosed FEMPTY v` by (
        unabbrev_all_tac >>
        match_mp_tac IN_FRANGE_alist_to_fmap_suff >>
        simp[env_to_Cenv_MAP,MAP_MAP_o,combinTheory.o_DEF,MEM_MAP,EXISTS_PROD] >>
        srw_tac[DNF_ss][] >>
        match_mp_tac (CONJUNCT1 v_to_Cv_closed) >>
        fs[EVERY_MEM,EXISTS_PROD,MEM_MAP] >>
        metis_tac[] ) >>
      `free_vars FEMPTY e1a ⊆ FDOM enva` by (
        unabbrev_all_tac >>
        fsrw_tac[DNF_ss][SUBSET_DEF,env_to_Cenv_MAP,MEM_MAP,
                         EXISTS_PROD,FORALL_PROD] ) >>
      `free_vars FEMPTY e2a ⊆ FDOM enva` by (
        unabbrev_all_tac >>
        fsrw_tac[DNF_ss][SUBSET_DEF,env_to_Cenv_MAP,MEM_MAP,
                         EXISTS_PROD,FORALL_PROD] ) >>
      `∀v. v ∈ FRANGE sa ⇒ Cclosed FEMPTY v` by (
        unabbrev_all_tac >>
        simp[FRANGE_store_to_Cstore,MEM_MAP] >>
        srw_tac[DNF_ss][] >>
        match_mp_tac (CONJUNCT1 v_to_Cv_closed) >>
        fs[EVERY_MEM] ) >>
      `∀v. v ∈ FRANGE sb ⇒ Cclosed FEMPTY v` by (
        unabbrev_all_tac >>
        simp[FRANGE_store_to_Cstore,MEM_MAP] >>
        srw_tac[DNF_ss][] >>
        match_mp_tac (CONJUNCT1 v_to_Cv_closed) >>
        fs[EVERY_MEM] ) >>
      qspecl_then[`FEMPTY`,`FEMPTY`,`sa`,`enva`,`e1a`,`(sd,Rval w1)`]mp_tac(CONJUNCT1 Cevaluate_closed) >>
      simp[] >> strip_tac >>
      qspecl_then[`FEMPTY`,`FEMPTY`,`sb`,`enva`,`e2a`,`X`]mp_tac(CONJUNCT1 Cevaluate_closed) >>
      simp[Abbr`X`] >> strip_tac >>
      fsrw_tac[DNF_ss][EXISTS_PROD,FORALL_PROD] >>
      map_every qx_gen_tac[`sf`,`w3`] >>
      strip_tac >>
      map_every qexists_tac[`sf`,`w1`,`w3`,`sd`] >>
      simp[] >>
      fs[do_app_def] >>
      rpt BasicProvers.VAR_EQ_TAC >>
      fs[] >>
      rpt BasicProvers.VAR_EQ_TAC >>
      fs[v_to_Cv_def,Q.SPECL[`c`,`CLitv l`]syneq_cases] >>
      fs[exp_to_Cexp_def] >>
      `fmap_rel (syneq FEMPTY) sc sf` by PROVE_TAC[fmap_rel_syneq_trans] >>
      cheat )
    >- (
      rw[Once Cevaluate_cases] >>
      srw_tac[DNF_ss][] >>
      disj1_tac >>
      rw[Once(CONJUNCT2 Cevaluate_cases)]>>
      rw[Once(CONJUNCT2 Cevaluate_cases)]>>
      fsrw_tac[DNF_ss][] >>
      qspecl_then[`cenv`,`s`,`env`,`e1`,`(s',Rval v1)`]mp_tac(CONJUNCT1 evaluate_closed) >>
      simp[] >> strip_tac >>
      qspecl_then[`cenv`,`s'`,`env`,`e2`,`(s3,Rval v2)`]mp_tac(CONJUNCT1 evaluate_closed) >>
      simp[] >> strip_tac >>
      Q.ISPECL_THEN[`s3`,`s''`,`env`,`Opapp`,`v1`,`v2`,`env'`,`exp''`]mp_tac do_app_closed >>
      simp[] >> strip_tac >>
      fs[] >>
      rpt (first_x_assum (qspec_then `cm` mp_tac)) >>
      srw_tac[DNF_ss][EXISTS_PROD] >>
      qmatch_assum_rename_tac `syneq FEMPTY FEMPTY(v_to_Cv cm v1) w1`[] >>
      qmatch_assum_rename_tac `syneq FEMPTY FEMPTY(v_to_Cv cm v2) w2`[] >>
      qmatch_assum_abbrev_tac`Cevaluate FEMPTY sa enva e1a (sd,Rval w1)`>>
      pop_assum kall_tac >>
      qmatch_assum_abbrev_tac`Cevaluate FEMPTY sb enva e2a (se,Rval w2)`>>
      pop_assum kall_tac >>
      qmatch_assum_abbrev_tac`EVERY2 (syneq FEMPTY FEMPTY) sc se` >>
      qspecl_then[`FEMPTY`,`sb`,`enva`,`e2a`,`(se,Rval w2)`]mp_tac(CONJUNCT1 Cevaluate_syneq) >> simp[] >>
      disch_then(qspecl_then[`FEMPTY`,`$=`,`sd`,`enva`,`e2a`]mp_tac) >>
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
      `free_vars e1a ⊆ count (LENGTH enva)` by (
        qmatch_assum_abbrev_tac`Abbrev(e1a = exp_to_Cexp m' e1)` >>
        Q.ISPECL_THEN[`m'`,`e1`]mp_tac free_vars_exp_to_Cexp >>
        simp[Abbr`m'`,Abbr`enva`,env_to_Cenv_MAP] ) >>
      `EVERY (Cclosed FEMPTY) sa` by (
        simp[Abbr`sa`,EVERY_MAP] >>
        fs[EVERY_MEM,v_to_Cv_closed] ) >>
      `EVERY (Cclosed FEMPTY) enva` by (
        simp[Abbr`enva`,env_to_Cenv_MAP,EVERY_MAP] >>
        fs[EVERY_MEM,MEM_MAP,FORALL_PROD,EXISTS_PROD] >>
        metis_tac[v_to_Cv_closed] ) >>
      qspecl_then[`FEMPTY`,`sa`,`enva`,`e1a`,`sd,Rval (CRecClos env1 defs n)`]mp_tac(CONJUNCT1 Cevaluate_closed)>>
      simp[FEVERY_DEF] >>
      simp[Q.SPECL[`FEMPTY`,`CRecClos env1 defs n`]Cclosed_cases] >>
      strip_tac >>
      fs[MEM_EL] >>
      reverse(Cases_on`EL n defs`)>>fs[]>-metis_tac[]>>
      PairCases_on`x`>>simp[] >>
      fs[do_app_Opapp_SOME] >- (
        rw[] >> fs[v_to_Cv_def,LET_THM] >>
        fs[Q.SPECL[`c`,`c`,`CRecClos env1 defs zz`]syneq_cases] >>
        rator_x_assum`syneq_defs`mp_tac >>
        Q.PAT_ABBREV_TAC`env0 = env_to_Cenv cm Z` >>
        Q.PAT_ABBREV_TAC`defs0 = [X]:def list` >>
        qabbrev_tac`cl = CRecClos env0 defs0 0` >>
        ho_match_mp_tac syneq_defs_elim_thm >>
        simp[] >> strip_tac >>
        first_assum(qspecl_then[`0`,`n`]mp_tac) >>
        simp_tac(srw_ss())[Abbr`defs0`] >>
        simp[syneq_cb_aux_def] >>
        strip_tac >>
        fs[bind_def] >>
        BasicProvers.VAR_EQ_TAC >>
        qmatch_assum_abbrev_tac`Cevaluate FEMPTY sc envc expc resc` >>
        qspecl_then[`FEMPTY`,`sc`,`envc`,`expc`,`resc`]mp_tac(CONJUNCT1 Cevaluate_syneq) >>
        simp[] >>
        Q.PAT_ABBREV_TAC`envf = w3::ls` >>
        qmatch_assum_abbrev_tac`syneq_exp FEMPTY FEMPTY z1 z2 U (shift 1 1 expc) x1`>>
        fs[env_to_Cenv_MAP] >>
        qunabbrev_tac`envc` >>
        Q.PAT_ABBREV_TAC`envc:Cv list = MAP f env''` >>
        disch_then(qspecl_then[`FEMPTY`,`λv1 v2. if v1 < 1 then (v2 = v1) else v2 = v1 + 1`,`sf`,`w2::cl::envc`,`shift 1 1 expc`]mp_tac) >>
        qmatch_abbrev_tac`(P ⇒ Q) ⇒ R` >>
        `P` by (
          map_every qunabbrev_tac[`P`,`Q`,`R`] >>
          simp[] >>
          conj_tac >- (
            simp[shift_def] >>
            match_mp_tac mkshift_thm >>
            simp[Abbr`envc`,Abbr`expc`,env_to_Cenv_MAP,ADD1,Abbr`z1`,Abbr`env0`] >>
            match_mp_tac free_vars_exp_to_Cexp_matchable >>
            simp[ADD1] ) >>
          conj_tac >- (
            lrw[ADD1,Abbr`envc`,env_to_Cenv_MAP,EL_CONS,PRE_SUB1] ) >>
          metis_tac[EVERY2_syneq_trans] ) >>
        simp[] >>
        map_every qunabbrev_tac[`P`,`Q`,`R`] >>
        pop_assum kall_tac >>
        disch_then(Q.X_CHOOSE_THEN`resd`strip_assume_tac) >>
        qspecl_then[`FEMPTY`,`sf`,`w2::cl::envc`,`shift 1 1 expc`,`resd`]mp_tac(CONJUNCT1 Cevaluate_syneq) >>
        simp[] >>
        disch_then(qspecl_then[`FEMPTY`,`U`,`sf`,`envf`,`x1`]mp_tac) >>
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
            disj1_tac >- metis_tac[] ) >>
          lrw[EL_APPEND2] ) >>
        simp[] >>
        map_every qunabbrev_tac[`P`,`Q`,`R`] >>
        pop_assum kall_tac >>
        simp[EXISTS_PROD] >>
        qunabbrev_tac`resc`>>fs[]>>
        metis_tac[EVERY2_syneq_trans,result_rel_syneq_trans,EVERY2_syneq_sym,result_rel_syneq_sym] ) >>
      rw[] >> fs[v_to_Cv_def,LET_THM,defs_to_Cdefs_MAP] >> rw[] >>
      reverse(fs[Q.SPECL[`c`,`c`,`CRecClos env1 defs zz`]syneq_cases]) >- (
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
      qmatch_assum_rename_tac`ALOOKUP funs fn = SOME z`[] >>
      (*
      `EL m0 funs = (fn,z)` by (
        fs[ALOOKUP_LEAST_EL] >>
        qunabbrev_tac`m0` >>
        simp[find_index_LEAST_EL] >>
        Q.PAT_ABBREV_TAC`ffuns:string list = MAP x funs` >>
        `ffuns = MAP FST funs` by (
          lrw[Abbr`ffuns`,LIST_EQ_REWRITE,EL_MAP] >>
          Cases_on`EL x funs`>>rw[] ) >>
        simp[] >>
        numLib.LEAST_ELIM_TAC >>
        conj_tac >- ( fs[MEM_EL] >> metis_tac[] ) >>
        qx_gen_tac`a` >>
        strip_tac >>
        `a < LENGTH funs` by (
          fs[MEM_MAP,MEM_EL] >>
          spose_not_then strip_assume_tac >>
          qmatch_assum_rename_tac`c = EL b funs`[] >>
          `b < a` by DECIDE_TAC >>
          res_tac >>
          rfs[EL_MAP] ) >>
        `EL a funs = (FST (EL a funs), SND (EL a funs))` by (
          Cases_on`EL a funs` >> rw[] ) >>
        pop_assum SUBST1_TAC >>
        simp[EL_MAP] >> rw[] >>
        numLib.LEAST_ELIM_TAC >>
        conj_tac >- metis_tac[] >>
        qx_gen_tac`c` >> rw[] >>
        qsuff_tac`c = a`>-rw[EL_MAP] >>
        Cases_on`a < c` >- metis_tac[] >>
        Cases_on`c < a` >- metis_tac[] >>
        DECIDE_TAC ) >>
      *)
      `ALL_DISTINCT (MAP FST funs)` by (
        fs[Once closed_cases] ) >>
      `EL m0 (REVERSE funs) = (fn,z)` by (
        Q.ISPEC_THEN`REVERSE (MAP FST funs)`mp_tac find_index_ALL_DISTINCT_EL_eq >>
        simp[ALL_DISTINCT_REVERSE >>
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
        simp[MEM_EL]
        disch_then(Q.X_CHOOSE_THEN`i`strip_assume_tac) >>
        pop_assum (assume_tac o SYM) >>
        `EL (LENGTH funs - i- 1) (REVERSE (MAP FST funs)) = fn` by (
          lrw[EL_REVERSE,EL_MAP,PRE_SUB1] ) >>
        first_x_assum(qspec_then`LENGTH funs - i -1`mp_tac) >>
        simp[] >>
        lrw[EL_REVERSE,PRE_SUB1] ) >>
      PairCases_on`z`>>fs[]>>rw[]>>
      rator_assum`syneq_defs`mp_tac >>
      Q.PAT_ABBREV_TAC`env0 = env_to_Cenv cm Z` >>
      Q.PAT_ABBREV_TAC`defs0:def list = MAP f funs` >>
      ho_match_mp_tac syneq_defs_elim_thm >>
      simp[] >>
      qabbrev_tac`cl = CRecClos env0 (REVERSE defs0) m0` >>
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
      rator_x_assum`syneq_exp`mp_tac >>
      Q.PAT_ABBREV_TAC`ffuns:string list = MAP X funs` >>
      `ffuns = MAP FST funs` by (
        lrw[Abbr`ffuns`,LIST_EQ_REWRITE,EL_MAP] >>
        Cases_on`EL x funs`>>rw[] ) >>
      fs[] >> ntac 2 (pop_assum kall_tac) >>
      qmatch_assum_abbrev_tac`Cevaluate FEMPTY sc envc expc resc` >>
      strip_tac >>
      qspecl_then[`FEMPTY`,`sc`,`envc`,`expc`,`resc`]mp_tac(CONJUNCT1 Cevaluate_syneq) >>
      simp[] >>
      Q.PAT_ABBREV_TAC`envf = w3::ls` >>
      qmatch_assum_abbrev_tac`syneq_exp FEMPTY FEMPTY z1 z2 U expc ef`>>
      fs[env_to_Cenv_MAP] >>
      qunabbrev_tac`envc` >>
      fs[build_rec_env_MAP,MAP_MAP_o,combinTheory.o_DEF,UNCURRY] >>
      disch_then(qspecl_then[`FEMPTY`,`U`,`sf`,`envf`,`ef`]mp_tac) >>
      qmatch_abbrev_tac`(P ⇒ Q) ⇒ R` >>
      `P` by (
        map_every qunabbrev_tac[`P`,`Q`,`R`] >>
        simp[] >>
        conj_tac >- (
          qmatch_abbrev_tac`syneq_exp c c z3 z4 U expc ef` >>
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
            qsuff_tac`a = LENGTH funs - v1`>-simp[] >>
            qunabbrev_tac`a` >>
            Q.ISPEC_THEN`REVERSE (MAP FST funs)`mp_tac find_index_ALL_DISTINCT_EL_eq >>
            simp[ALL_DISTINCT_REVERSE] >>
            disch_then(qspecl_then[`FST (EL (v1-1) funs)`,`0`]mp_tac) >> simp[] >>
            disch_then(qspec_then`LENGTH funs - v1`mp_tac) >>
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
      metis_tac[EVERY2_syneq_trans,result_rel_syneq_trans,EVERY2_syneq_sym,result_rel_syneq_sym] )
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
      qspecl_then[`cenv`,`s`,`env`,`e1`,`(s',Rval (Loc n))`]mp_tac(CONJUNCT1 evaluate_closed) >>
      simp[]>>strip_tac >> fs[] >>
      fs[store_assign_def] >> rw[] >> fs[] >> rw[] >>
      qspecl_then[`cenv`,`s'`,`env`,`e2`,`(s3,Rval v2)`]mp_tac(CONJUNCT1 evaluate_closed) >>
      simp[]>>strip_tac >>
      `EVERY closed (LUPDATE v2 n s3)` by (
        fs[EVERY_MEM] >>
        metis_tac[MEM_LUPDATE] ) >>
      fs[] >>
      rpt (first_x_assum (qspec_then`m`mp_tac)) >>
      fsrw_tac[DNF_ss][EXISTS_PROD] >> rw[] >>
      fs[v_to_Cv_def,exp_to_Cexp_def] >>
      rw[] >> fs[] >> rw[] >>
      fs[Q.SPECL[`FEMPTY`,`CLoc n`]syneq_cases] >> rw[] >>
      CONV_TAC SWAP_EXISTS_CONV >> qexists_tac`CLoc n` >> rw[] >>
      qmatch_assum_abbrev_tac`Cevaluate FEMPTY FEMPTY sa enva e1a (sd,Rval (CLoc n))` >>
      pop_assum kall_tac >>
      qmatch_assum_abbrev_tac`Cevaluate FEMPTY FEMPTY sb enva e2a (se,w1)` >>
      qpat_assum`Abbrev (se  = X)`kall_tac >>
      qspecl_then[`FEMPTY`,`FEMPTY`,`sb`,`sd`,`enva`,`e2a`,`(se,w1)`]mp_tac Cevaluate_any_syneq_store >>
      `∀v. v ∈ FRANGE enva ⇒ Cclosed FEMPTY v` by (
        unabbrev_all_tac >>
        match_mp_tac IN_FRANGE_alist_to_fmap_suff >>
        simp[env_to_Cenv_MAP,MAP_MAP_o,combinTheory.o_DEF,MEM_MAP,EXISTS_PROD] >>
        srw_tac[DNF_ss][] >>
        match_mp_tac (CONJUNCT1 v_to_Cv_closed) >>
        fs[EVERY_MEM,EXISTS_PROD,MEM_MAP] >>
        metis_tac[] ) >>
      `free_vars FEMPTY e1a ⊆ FDOM enva` by (
        unabbrev_all_tac >>
        fsrw_tac[DNF_ss][SUBSET_DEF,env_to_Cenv_MAP,MEM_MAP,
                         EXISTS_PROD,FORALL_PROD] ) >>
      `free_vars FEMPTY e2a ⊆ FDOM enva` by (
        unabbrev_all_tac >>
        fsrw_tac[DNF_ss][SUBSET_DEF,env_to_Cenv_MAP,MEM_MAP,
                         EXISTS_PROD,FORALL_PROD] ) >>
      `∀v. v ∈ FRANGE sa ⇒ Cclosed FEMPTY v` by (
        unabbrev_all_tac >>
        simp[FRANGE_store_to_Cstore,MEM_MAP] >>
        srw_tac[DNF_ss][] >>
        match_mp_tac (CONJUNCT1 v_to_Cv_closed) >>
        fs[EVERY_MEM] ) >>
      `∀v. v ∈ FRANGE sb ⇒ Cclosed FEMPTY v` by (
        unabbrev_all_tac >>
        simp[FRANGE_store_to_Cstore,MEM_MAP] >>
        srw_tac[DNF_ss][] >>
        match_mp_tac (CONJUNCT1 v_to_Cv_closed) >>
        fs[EVERY_MEM] ) >>
      qspecl_then[`FEMPTY`,`FEMPTY`,`sa`,`enva`,`e1a`,`(sd,Rval (CLoc n))`]mp_tac(CONJUNCT1 Cevaluate_closed) >>
      simp[] >> strip_tac >>
      fsrw_tac[DNF_ss][FORALL_PROD] >>
      map_every qx_gen_tac[`sf`,`w2`] >>
      strip_tac >>
      fs[Abbr`w1`] >> rw[] >>
      qmatch_assum_rename_tac`syneq FEMPTY w1 w2`[] >>
      map_every qexists_tac[`sf`,`w2`,`sd`] >>
      simp[] >>
      fs[fmap_rel_def] >>
      conj_tac >- (rw[EXTENSION] >> PROVE_TAC[]) >>
      rw[FAPPLY_FUPDATE_THM,FAPPLY_store_to_Cstore,EL_LUPDATE] >-
        PROVE_TAC[syneq_trans] >>
      fs[FAPPLY_store_to_Cstore,EXTENSION] >>
      PROVE_TAC[syneq_trans])) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    ntac 2 gen_tac >>
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
      qspecl_then[`cenv`,`s`,`env`,`e1`,`(s',Rval v1)`]mp_tac(CONJUNCT1 evaluate_closed) >>
      simp[] >> strip_tac >> fs[] >>
      rpt (first_x_assum (qspec_then `m` mp_tac)) >>
      rw[] >>
      disj2_tac >>
      qmatch_assum_rename_tac `syneq FEMPTY (v_to_Cv m v1) w1`[] >>
      qmatch_assum_abbrev_tac `Cevaluate FEMPTY FEMPTY sb enva e2a (sc,Rerr err)`>>
      pop_assum kall_tac >>
      qmatch_assum_rename_tac `fmap_rel (syneq FEMPTY) sb sd`[] >>
      qspecl_then[`FEMPTY`,`FEMPTY`,`sb`,`sd`,`enva`,`e2a`,`(sc,Rerr err)`]mp_tac Cevaluate_any_syneq_store >>
      qmatch_assum_abbrev_tac `Cevaluate FEMPTY FEMPTY sa enva e1a (sd,Rval w1)`>>
      `∀v. v ∈ FRANGE enva ⇒ Cclosed FEMPTY v` by (
        unabbrev_all_tac >>
        match_mp_tac IN_FRANGE_alist_to_fmap_suff >>
        fsrw_tac[DNF_ss][SUBSET_DEF,env_to_Cenv_MAP,MEM_MAP,
                         EVERY_MEM,EXISTS_PROD,FORALL_PROD] >>
        rw[] >>
        match_mp_tac (CONJUNCT1 v_to_Cv_closed) >>
        PROVE_TAC[]) >>
      `free_vars FEMPTY e1a ⊆ FDOM enva` by (
        unabbrev_all_tac >>
        fsrw_tac[DNF_ss][SUBSET_DEF,env_to_Cenv_MAP,MEM_MAP,
                         EXISTS_PROD,FORALL_PROD] ) >>
      `free_vars FEMPTY e2a ⊆ FDOM enva` by (
        unabbrev_all_tac >>
        fsrw_tac[DNF_ss][SUBSET_DEF,env_to_Cenv_MAP,MEM_MAP,
                         EXISTS_PROD,FORALL_PROD] ) >>
      `∀v. v ∈ FRANGE sa ⇒ Cclosed FEMPTY v` by (
        unabbrev_all_tac >>
        fsrw_tac[DNF_ss][FRANGE_store_to_Cstore,MEM_MAP,EVERY_MEM] >>
        rw[] >> match_mp_tac (CONJUNCT1 v_to_Cv_closed) >> PROVE_TAC[] ) >>
      `∀v. v ∈ FRANGE sb ⇒ Cclosed FEMPTY v` by (
        unabbrev_all_tac >>
        fsrw_tac[DNF_ss][FRANGE_store_to_Cstore,MEM_MAP,EVERY_MEM] >>
        rw[] >> match_mp_tac (CONJUNCT1 v_to_Cv_closed) >> PROVE_TAC[] ) >>
      qspecl_then[`FEMPTY`,`FEMPTY`,`sa`,`enva`,`e1a`,`(sd,Rval w1)`]mp_tac(CONJUNCT1 Cevaluate_closed) >>
      simp[] >> strip_tac >>
      fsrw_tac[DNF_ss][FORALL_PROD] >>
      qx_gen_tac`se` >> strip_tac >>
      map_every qexists_tac [`se`,`sd`,`w1`] >> fs[] >>
      PROVE_TAC[fmap_rel_syneq_trans])
    >- (
      fs[] >>
      qspecl_then[`cenv`,`s`,`env`,`e1`,`(s',Rval v1)`]mp_tac(CONJUNCT1 evaluate_closed) >>
      simp[]>>strip_tac>>fs[]>>
      fsrw_tac[DNF_ss][EXISTS_PROD]>>
      rpt (first_x_assum (qspec_then `m` mp_tac)) >>
      rw[] >>
      qmatch_assum_rename_tac `syneq FEMPTY (v_to_Cv m v1) w1`[] >>
      qmatch_assum_abbrev_tac `Cevaluate FEMPTY FEMPTY sa enva e1a (sd,Rval w1)` >>
      pop_assum kall_tac >>
      qmatch_assum_abbrev_tac `Cevaluate FEMPTY FEMPTY sb enva e2a (sc,Rerr err)` >>
      pop_assum kall_tac >>
      `∀v. v ∈ FRANGE enva ⇒ Cclosed FEMPTY v` by (
        imp_res_tac v_to_Cv_closed >>
        fs[FEVERY_DEF] >> PROVE_TAC[] ) >>
      `free_vars FEMPTY e1a ⊆ FDOM enva ∧
       free_vars FEMPTY e2a ⊆ FDOM enva` by (
        fs[Abbr`e1a`,Abbr`e2a`,Abbr`enva`,env_to_Cenv_MAP,MAP_MAP_o,
           pairTheory.LAMBDA_PROD,combinTheory.o_DEF,FST_pair,FST_triple] ) >>
      `(∀v. v ∈ FRANGE sa ⇒ Cclosed FEMPTY v) ∧
       (∀v. v ∈ FRANGE sb ⇒ Cclosed FEMPTY v)` by (
         unabbrev_all_tac >>
         fsrw_tac[DNF_ss][FRANGE_store_to_Cstore,MEM_MAP,EVERY_MEM] >>
         rw[] >> match_mp_tac (CONJUNCT1 v_to_Cv_closed) >> res_tac ) >>
      qspecl_then[`FEMPTY`,`FEMPTY`,`sa`,`enva`,`e1a`,`(sd,Rval w1)`]mp_tac(CONJUNCT1 Cevaluate_closed) >>
      simp[] >> strip_tac >> fs[] >>
      qspecl_then[`FEMPTY`,`FEMPTY`,`sb`,`sd`,`enva`,`e2a`,`(sc,Rerr err)`]mp_tac Cevaluate_any_syneq_store >>
      fsrw_tac[DNF_ss][EXISTS_PROD] >>
      qx_gen_tac`se`>>strip_tac >>
      `fmap_rel (syneq FEMPTY) (store_to_Cstore m s3) se` by PROVE_TAC[fmap_rel_syneq_trans] >>
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
        Q.PAT_ABBREV_TAC`fv = fresh_var X` >>
        qspecl_then[`FEMPTY`,`FEMPTY`,`sd`,`enva`,`e2a`,`se`,`err`,`fv`,`w1`]mp_tac Cevaluate_FUPDATE_Rerr >>
        `fv ∉ free_vars FEMPTY e2a` by (
          unabbrev_all_tac >>
          match_mp_tac fresh_var_not_in_any >>
          rw[] ) >>
        simp[] >>
        PROVE_TAC[fmap_rel_syneq_trans])
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
        Q.PAT_ABBREV_TAC`fv = fresh_var X` >>
        qspecl_then[`FEMPTY`,`FEMPTY`,`sd`,`enva`,`e2a`,`se`,`err`,`fv`,`w1`]mp_tac Cevaluate_FUPDATE_Rerr >>
        `fv ∉ free_vars FEMPTY e2a` by (
          unabbrev_all_tac >>
          match_mp_tac fresh_var_not_in_any >>
          rw[] ) >>
        simp[] >>
        PROVE_TAC[fmap_rel_syneq_trans]))
    >- (
      rw[Once Cevaluate_cases] >>
      fsrw_tac[DNF_ss][EXISTS_PROD] >>
      disj2_tac >>
      rw[Once(CONJUNCT2 Cevaluate_cases)] >>
      rw[Once(CONJUNCT2 Cevaluate_cases)] >>
      rw[Once(CONJUNCT2 Cevaluate_cases)] >>
      srw_tac[DNF_ss][]>>
      disj2_tac >>
      qspecl_then[`cenv`,`s`,`env`,`e1`,`(s',Rval v1)`]mp_tac(CONJUNCT1 evaluate_closed) >>
      simp[]>>strip_tac>>fs[]>>
      rpt (first_x_assum (qspec_then `m` mp_tac)) >> rw[] >>
      qmatch_assum_rename_tac `syneq FEMPTY (v_to_Cv m v1) w1`[] >>
      qmatch_assum_abbrev_tac `Cevaluate FEMPTY FEMPTY sa enva e1a (sd,Rval w1)` >>
      pop_assum kall_tac >>
      qmatch_assum_abbrev_tac `Cevaluate FEMPTY FEMPTY sb enva e2a (sc,Rerr err)` >>
      pop_assum kall_tac >>
      `∀v. v ∈ FRANGE enva ⇒ Cclosed FEMPTY v` by (
        imp_res_tac v_to_Cv_closed >>
        fs[FEVERY_DEF] >> PROVE_TAC[] ) >>
      `free_vars FEMPTY e1a ⊆ FDOM enva ∧
       free_vars FEMPTY e2a ⊆ FDOM enva` by (
        fs[Abbr`e1a`,Abbr`e2a`,Abbr`enva`,env_to_Cenv_MAP,MAP_MAP_o,
           pairTheory.LAMBDA_PROD,combinTheory.o_DEF,FST_pair,FST_triple] ) >>
      `(∀v. v ∈ FRANGE sa ⇒ Cclosed FEMPTY v) ∧
       (∀v. v ∈ FRANGE sb ⇒ Cclosed FEMPTY v)` by (
         unabbrev_all_tac >>
         fsrw_tac[DNF_ss][FRANGE_store_to_Cstore,MEM_MAP,EVERY_MEM] >>
         rw[] >> match_mp_tac (CONJUNCT1 v_to_Cv_closed) >> res_tac ) >>
      qspecl_then[`FEMPTY`,`FEMPTY`,`sa`,`enva`,`e1a`,`(sd,Rval w1)`]mp_tac(CONJUNCT1 Cevaluate_closed) >>
      simp[] >> strip_tac >> fs[] >>
      qspecl_then[`FEMPTY`,`FEMPTY`,`sb`,`sd`,`enva`,`e2a`,`(sc,Rerr err)`]mp_tac Cevaluate_any_syneq_store >>
      fsrw_tac[DNF_ss][EXISTS_PROD] >>
      qx_gen_tac`se`>>strip_tac >>
      PROVE_TAC[fmap_rel_syneq_trans] )
    >- (
      rw[Once Cevaluate_cases] >>
      fsrw_tac[DNF_ss][] >>
      disj2_tac >> disj1_tac >>
      fsrw_tac[DNF_ss][EXISTS_PROD] >>
      rw[Once(CONJUNCT2 Cevaluate_cases)] >>
      rw[Once(CONJUNCT2 Cevaluate_cases)] >>
      qspecl_then[`cenv`,`s`,`env`,`e1`,`(s',Rval v1)`]mp_tac(CONJUNCT1 evaluate_closed) >>
      simp[]>>strip_tac>>fs[]>>
      rpt (first_x_assum (qspec_then `m` mp_tac)) >> rw[] >>
      qmatch_assum_rename_tac `syneq FEMPTY (v_to_Cv m v1) w1`[] >>
      qmatch_assum_abbrev_tac `Cevaluate FEMPTY FEMPTY sa enva e1a (sd,Rval w1)` >>
      pop_assum kall_tac >>
      qmatch_assum_abbrev_tac `Cevaluate FEMPTY FEMPTY sb enva e2a (sc,Rerr err)` >>
      pop_assum kall_tac >>
      `∀v. v ∈ FRANGE enva ⇒ Cclosed FEMPTY v` by (
        imp_res_tac v_to_Cv_closed >>
        fs[FEVERY_DEF] >> PROVE_TAC[] ) >>
      `free_vars FEMPTY e1a ⊆ FDOM enva ∧
       free_vars FEMPTY e2a ⊆ FDOM enva` by (
        fs[Abbr`e1a`,Abbr`e2a`,Abbr`enva`,env_to_Cenv_MAP,MAP_MAP_o,
           pairTheory.LAMBDA_PROD,combinTheory.o_DEF,FST_pair,FST_triple] ) >>
      `(∀v. v ∈ FRANGE sa ⇒ Cclosed FEMPTY v) ∧
       (∀v. v ∈ FRANGE sb ⇒ Cclosed FEMPTY v)` by (
         unabbrev_all_tac >>
         fsrw_tac[DNF_ss][FRANGE_store_to_Cstore,MEM_MAP,EVERY_MEM] >>
         rw[] >> match_mp_tac (CONJUNCT1 v_to_Cv_closed) >> res_tac ) >>
      qspecl_then[`FEMPTY`,`FEMPTY`,`sa`,`enva`,`e1a`,`(sd,Rval w1)`]mp_tac(CONJUNCT1 Cevaluate_closed) >>
      simp[] >> strip_tac >> fs[] >>
      qspecl_then[`FEMPTY`,`FEMPTY`,`sb`,`sd`,`enva`,`e2a`,`(sc,Rerr err)`]mp_tac Cevaluate_any_syneq_store >>
      fsrw_tac[DNF_ss][EXISTS_PROD] >>
      PROVE_TAC[fmap_rel_syneq_trans])
    >- (
      rw[Once Cevaluate_cases] >>
      fsrw_tac[DNF_ss][EXISTS_PROD] >>
      disj2_tac >>
      rw[Once(CONJUNCT2 Cevaluate_cases)] >>
      rw[Once(CONJUNCT2 Cevaluate_cases)] >>
      rw[Once(CONJUNCT2 Cevaluate_cases)] >>
      srw_tac[DNF_ss][] >>
      disj2_tac >>
      qspecl_then[`cenv`,`s`,`env`,`e1`,`(s',Rval v1)`]mp_tac(CONJUNCT1 evaluate_closed) >>
      simp[]>>strip_tac>>fs[]>>
      rpt (first_x_assum (qspec_then `m` mp_tac)) >> rw[] >>
      qmatch_assum_rename_tac `syneq FEMPTY (v_to_Cv m v1) w1`[] >>
      qmatch_assum_abbrev_tac `Cevaluate FEMPTY FEMPTY sa enva e1a (sd,Rval w1)` >>
      pop_assum kall_tac >>
      qmatch_assum_abbrev_tac `Cevaluate FEMPTY FEMPTY sb enva e2a (sc,Rerr err)` >>
      pop_assum kall_tac >>
      `∀v. v ∈ FRANGE enva ⇒ Cclosed FEMPTY v` by (
        imp_res_tac v_to_Cv_closed >>
        fs[FEVERY_DEF] >> PROVE_TAC[] ) >>
      `free_vars FEMPTY e1a ⊆ FDOM enva ∧
       free_vars FEMPTY e2a ⊆ FDOM enva` by (
        fs[Abbr`e1a`,Abbr`e2a`,Abbr`enva`,env_to_Cenv_MAP,MAP_MAP_o,
           pairTheory.LAMBDA_PROD,combinTheory.o_DEF,FST_pair,FST_triple] ) >>
      `(∀v. v ∈ FRANGE sa ⇒ Cclosed FEMPTY v) ∧
       (∀v. v ∈ FRANGE sb ⇒ Cclosed FEMPTY v)` by (
         unabbrev_all_tac >>
         fsrw_tac[DNF_ss][FRANGE_store_to_Cstore,MEM_MAP,EVERY_MEM] >>
         rw[] >> match_mp_tac (CONJUNCT1 v_to_Cv_closed) >> res_tac ) >>
      qspecl_then[`FEMPTY`,`FEMPTY`,`sa`,`enva`,`e1a`,`(sd,Rval w1)`]mp_tac(CONJUNCT1 Cevaluate_closed) >>
      simp[] >> strip_tac >> fs[] >>
      qspecl_then[`FEMPTY`,`FEMPTY`,`sb`,`sd`,`enva`,`e2a`,`(sc,Rerr err)`]mp_tac Cevaluate_any_syneq_store >>
      fsrw_tac[DNF_ss][EXISTS_PROD] >>
      PROVE_TAC[fmap_rel_syneq_trans])) >>
  strip_tac >- (
    ntac 2 gen_tac >>
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
    `FV exp' ⊆ set (MAP FST env)` by PROVE_TAC[SUBSET_TRANS] >>
    qspecl_then[`cenv`,`s`,`env`,`exp`,`(s',Rval v)`]mp_tac(CONJUNCT1 evaluate_closed) >>
    simp[]>>strip_tac>>fs[]>>
    rpt (first_x_assum (qspec_then`m` mp_tac)) >> rw[] >>
    qmatch_assum_rename_tac`syneq FEMPTY (v_to_Cv m v) w`[] >>
    qmatch_assum_abbrev_tac `Cevaluate FEMPTY FEMPTY sa enva e1a (sd,Rval w)` >>
    pop_assum kall_tac >>
    qmatch_assum_abbrev_tac `Cevaluate FEMPTY FEMPTY sb enva e2a (sc,w2)` >>
    ntac 2 (pop_assum kall_tac) >>
    `∀v. v ∈ FRANGE enva ⇒ Cclosed FEMPTY v` by (
      imp_res_tac v_to_Cv_closed >>
      fs[FEVERY_DEF] >> PROVE_TAC[] ) >>
    `free_vars FEMPTY e1a ⊆ FDOM enva ∧
     free_vars FEMPTY e2a ⊆ FDOM enva` by (
      fs[Abbr`e1a`,Abbr`e2a`,Abbr`enva`,env_to_Cenv_MAP,MAP_MAP_o,
         pairTheory.LAMBDA_PROD,combinTheory.o_DEF,FST_pair,FST_triple] ) >>
    `(∀v. v ∈ FRANGE sa ⇒ Cclosed FEMPTY v) ∧
     (∀v. v ∈ FRANGE sb ⇒ Cclosed FEMPTY v)` by (
       unabbrev_all_tac >>
       fsrw_tac[DNF_ss][FRANGE_store_to_Cstore,MEM_MAP,EVERY_MEM] >>
       rw[] >> match_mp_tac (CONJUNCT1 v_to_Cv_closed) >> res_tac ) >>
    qspecl_then[`FEMPTY`,`FEMPTY`,`sa`,`enva`,`e1a`,`(sd,Rval w)`]mp_tac(CONJUNCT1 Cevaluate_closed) >>
    simp[] >> strip_tac >> fs[] >>
    qspecl_then[`FEMPTY`,`FEMPTY`,`sb`,`sd`,`enva`,`e2a`,`(sc,w2)`]mp_tac Cevaluate_any_syneq_store >>
    fsrw_tac[DNF_ss][EXISTS_PROD] >>
    map_every qx_gen_tac[`se`,`w3`] >>strip_tac >>
    Cases_on `op` >> Cases_on `v` >> fs[do_log_def] >>
    Cases_on `l` >> fs[v_to_Cv_def] >>
    fs[Q.SPECL[`c`,`CLitv l`]syneq_cases] >> rw[] >>
    rw[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][] >> disj1_tac >>
    CONV_TAC (RESORT_EXISTS_CONV List.rev) >>
    map_every qexists_tac [`b`,`sd`] >> fs[] >>
    rw[] >> fs[] >> rw[] >>
    fs[evaluate_lit] >> rw[v_to_Cv_def] >>
    PROVE_TAC[result_rel_syneq_trans,fmap_rel_syneq_trans] ) >>
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
    `FV exp' ⊆ set (MAP FST env)` by (
      fsrw_tac[DNF_ss][SUBSET_DEF] >>
      PROVE_TAC[]) >> fs[] >>
    qspecl_then[`cenv`,`s`,`env`,`exp`,`(s',Rval v)`]mp_tac(CONJUNCT1 evaluate_closed) >>
    simp[]>>strip_tac>>fs[]>>
    rw[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][] >>
    disj1_tac >>
    rpt (first_x_assum (qspec_then`m` mp_tac)) >> rw[] >>
    qmatch_assum_rename_tac`syneq FEMPTY (v_to_Cv m v) w`[] >>
    qmatch_assum_abbrev_tac `Cevaluate FEMPTY FEMPTY sa enva e1a (sd,Rval w)` >>
    pop_assum kall_tac >>
    qmatch_assum_abbrev_tac `Cevaluate FEMPTY FEMPTY sb enva e2a (sc,w2)` >>
    ntac 2 (pop_assum kall_tac) >>
    `∀v. v ∈ FRANGE enva ⇒ Cclosed FEMPTY v` by (
      imp_res_tac v_to_Cv_closed >>
      fs[FEVERY_DEF] >> PROVE_TAC[] ) >>
    `free_vars FEMPTY e1a ⊆ FDOM enva ∧
     free_vars FEMPTY e2a ⊆ FDOM enva` by (
      fs[Abbr`e1a`,Abbr`e2a`,Abbr`enva`,env_to_Cenv_MAP,MAP_MAP_o,
         pairTheory.LAMBDA_PROD,combinTheory.o_DEF,FST_pair,FST_triple] ) >>
    `(∀v. v ∈ FRANGE sa ⇒ Cclosed FEMPTY v) ∧
     (∀v. v ∈ FRANGE sb ⇒ Cclosed FEMPTY v)` by (
       unabbrev_all_tac >>
       fsrw_tac[DNF_ss][FRANGE_store_to_Cstore,MEM_MAP,EVERY_MEM] >>
       rw[] >> match_mp_tac (CONJUNCT1 v_to_Cv_closed) >> res_tac ) >>
    qspecl_then[`FEMPTY`,`FEMPTY`,`sa`,`enva`,`e1a`,`(sd,Rval w)`]mp_tac(CONJUNCT1 Cevaluate_closed) >>
    simp[] >> strip_tac >> fs[] >>
    qspecl_then[`FEMPTY`,`FEMPTY`,`sb`,`sd`,`enva`,`e2a`,`(sc,w2)`]mp_tac Cevaluate_any_syneq_store >>
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
    fsrw_tac[DNF_ss][v_to_Cv_def,Q.SPECL[`c`,`CLitv l`]syneq_cases] >>
    PROVE_TAC[fmap_rel_syneq_trans,result_rel_syneq_trans]) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rw[exp_to_Cexp_def,LET_THM] >> fs[] >>
    rw[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][EXISTS_PROD]) >>
  strip_tac >- (
    rpt strip_tac >> fs[] >>
    fsrw_tac[DNF_ss][EXISTS_PROD] >>
    first_x_assum (qspec_then `m` mp_tac) >> rw[] >>
    qmatch_assum_rename_tac `syneq FEMPTY (v_to_Cv m v) w`[] >>
    rw[exp_to_Cexp_def,LET_THM] >>
    rw[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][] >>
    disj1_tac >>
    qmatch_assum_abbrev_tac`Cevaluate FEMPTY FEMPTY sa enva ea (sd,Rval w)` >>
    pop_assum kall_tac >>
    CONV_TAC (RESORT_EXISTS_CONV List.rev) >>
    map_every qexists_tac [`w`,`sd`] >> fs[] >>
    qmatch_assum_abbrev_tac `evaluate_match_with P cenv s2 env v pes res` >>
    Q.ISPECL_THEN [`s2`,`pes`,`res`] mp_tac (Q.GEN`s`evaluate_match_with_matchres) >> fs[] >>
    PairCases_on`res`>>fs[]>>strip_tac>>
    qmatch_assum_abbrev_tac`evaluate_match_with (matchres env) cenv s2 env v pes r` >>
    Q.ISPECL_THEN [`s2`,`pes`,`r`] mp_tac (Q.GEN`s`evaluate_match_with_Cevaluate_match) >>
    fs[Abbr`r`] >>
    disch_then (qspec_then `m` mp_tac) >>
    rw[] >- (
      qmatch_assum_abbrev_tac `Cevaluate_match sb vv ppes FEMPTY NONE` >>
      `Cevaluate_match sb vv (MAP (λ(p,e). (p, exp_to_Cexp m e)) ppes) FEMPTY NONE` by (
        metis_tac [Cevaluate_match_MAP_exp, optionTheory.OPTION_MAP_DEF] ) >>
      qmatch_assum_abbrev_tac `Cevaluate_match sb vv (MAP ff ppes) FEMPTY NONE` >>
      `MAP ff ppes = pes_to_Cpes m pes` by (
        unabbrev_all_tac >>
        rw[pes_to_Cpes_MAP,LET_THM] >>
        rw[MAP_MAP_o,combinTheory.o_DEF,pairTheory.LAMBDA_PROD] >>
        rw[pairTheory.UNCURRY] ) >>
      fs[] >>
      map_every qunabbrev_tac[`ppes`,`ff`,`vv`] >>
      pop_assum kall_tac >>
      ntac 2 (pop_assum mp_tac) >>
      pop_assum kall_tac >>
      ntac 2 strip_tac >>
      Q.SPECL_THEN [`sb`,`v_to_Cv m v`,`pes_to_Cpes m pes`,`FEMPTY`,`NONE`]
        mp_tac (INST_TYPE[alpha|->``:Cexp``](Q.GENL[`v`,`s`] Cevaluate_match_syneq)) >>
      fs[] >>
      disch_then (qspecl_then [`FEMPTY`,`sd`,`w`] mp_tac) >> fs[] >>
      strip_tac >>
      qabbrev_tac`ps = pes_to_Cpes m pes` >>
      qspecl_then[`sd`,`w`,`ps`,`FEMPTY`,`NONE`]mp_tac(Q.GENL[`v`,`s`]Cevaluate_match_remove_mat_var)>>
      fs[] >>
      fsrw_tac[DNF_ss][EXISTS_PROD] >>
      Q.PAT_ABBREV_TAC`envu = enva |+ X` >>
      Q.PAT_ABBREV_TAC`fv = fresh_var X` >>
      disch_then (qspecl_then[`envu`,`fv`]mp_tac)>>
      qmatch_abbrev_tac`(P0 ⇒ Q) ⇒ R` >>
      `P0` by (
        map_every qunabbrev_tac[`P0`,`Q`,`R`] >>
        fs[FLOOKUP_UPDATE,Abbr`envu`] >>
        fsrw_tac[DNF_ss][pairTheory.FORALL_PROD] >>
        conj_tac >- (
          qx_gen_tac `z` >>
          Cases_on `fv ∈ z` >> fs[] >>
          qx_gen_tac `p` >>
          qx_gen_tac `e` >>
          Cases_on `z = Cpat_vars p` >> fs[] >>
          spose_not_then strip_assume_tac >>
          `fv ∉ Cpat_vars p` by (
            unabbrev_all_tac >>
            match_mp_tac fresh_var_not_in_any >>
            rw[Cpes_vars_thm] >> rw[] >>
            srw_tac[DNF_ss][SUBSET_DEF,pairTheory.EXISTS_PROD,MEM_MAP] >>
            metis_tac[] ) ) >>
        conj_tac >- (
          unabbrev_all_tac >>
          fsrw_tac[DNF_ss][env_to_Cenv_MAP,MAP_MAP_o,combinTheory.o_DEF,pairTheory.LAMBDA_PROD,FST_pair,FST_triple] >>
          fsrw_tac[DNF_ss][SUBSET_DEF,pairTheory.FORALL_PROD,pes_to_Cpes_MAP,MEM_MAP,LET_THM,pairTheory.EXISTS_PROD] >>
          fsrw_tac[DNF_ss][pairTheory.UNCURRY,Cpes_vars_thm] >>
          metis_tac[Cpat_vars_pat_to_Cpat,pairTheory.pair_CASES,pairTheory.SND] ) >>
        `∀v. v ∈ FRANGE sa ⇒ Cclosed FEMPTY v` by (
          unabbrev_all_tac >>
          fsrw_tac[DNF_ss][FRANGE_store_to_Cstore,MEM_MAP,EVERY_MEM] >>
          rw[] >> match_mp_tac (CONJUNCT1 v_to_Cv_closed) >> res_tac ) >>
        `free_vars FEMPTY ea ⊆ FDOM enva` by (
          unabbrev_all_tac >>
          fs[env_to_Cenv_MAP,MAP_MAP_o,combinTheory.o_DEF,LAMBDA_PROD,FST_pair,FST_triple]) >>
        `∀v. v ∈ FRANGE enva ⇒ Cclosed FEMPTY v` by (
          unabbrev_all_tac >>
          match_mp_tac IN_FRANGE_alist_to_fmap_suff >>
          fsrw_tac[DNF_ss][MEM_MAP,FORALL_PROD,env_to_Cenv_MAP,EVERY_MEM] >>
          rw[] >> match_mp_tac (CONJUNCT1 v_to_Cv_closed) >> res_tac ) >>
        qspecl_then[`FEMPTY`,`FEMPTY`,`sa`,`enva`,`ea`,`(sd,Rval w)`]mp_tac(CONJUNCT1 Cevaluate_closed) >>
        simp[] >> strip_tac >>
        match_mp_tac IN_FRANGE_DOMSUB_suff >>
        rw[] ) >>
      simp[] >>
      map_every qunabbrev_tac[`P0`,`Q`,`R`] >>
      metis_tac[fmap_rel_syneq_trans,fmap_rel_syneq_sym] ) >>
    qmatch_assum_abbrev_tac `Cevaluate_match sb vv ppes eenv (SOME mr)` >>
    `Cevaluate_match sb vv (MAP (λ(p,e). (p, exp_to_Cexp m e)) ppes) eenv (SOME (exp_to_Cexp m mr))` by (
      metis_tac [Cevaluate_match_MAP_exp, optionTheory.OPTION_MAP_DEF] ) >>
    pop_assum mp_tac >>
    map_every qunabbrev_tac[`ppes`,`eenv`,`vv`] >>
    pop_assum mp_tac >>
    pop_assum kall_tac >>
    ntac 2 strip_tac >>
    qmatch_assum_abbrev_tac `Cevaluate_match sb vv (MAP ff ppes) eenv mmr` >>
    `MAP ff ppes = pes_to_Cpes m pes` by (
      unabbrev_all_tac >>
      rw[pes_to_Cpes_MAP,LET_THM] >>
      rw[MAP_MAP_o,combinTheory.o_DEF,pairTheory.LAMBDA_PROD] >>
      rw[pairTheory.UNCURRY] ) >>
    fs[] >>
    pop_assum kall_tac >>
    qunabbrev_tac `ppes` >>
    qabbrev_tac`ps = pes_to_Cpes m pes` >>
    Q.ISPECL_THEN[`sb`,`vv`,`ps`,`eenv`,`mmr`]mp_tac(Q.GENL[`v`,`s`]Cevaluate_match_syneq) >>
    simp[] >>
    disch_then(qspecl_then[`FEMPTY`,`sd`,`w`]mp_tac) >>
    simp[] >>
    disch_then(Q.X_CHOOSE_THEN`wenv`strip_assume_tac) >>
    qspecl_then[`sd`,`w`,`ps`,`wenv`,`mmr`]mp_tac(Q.GENL[`v`,`s`]Cevaluate_match_remove_mat_var) >>
    simp[Abbr`mmr`] >>
    Q.PAT_ABBREV_TAC`fv = fresh_var X` >>
    fsrw_tac[DNF_ss][FORALL_PROD,EXISTS_PROD] >>
    disch_then(qspecl_then[`enva|+(fv,w)`,`fv`]mp_tac) >>
    qspecl_then[`cenv`,`s`,`env`,`exp`,`(s2,Rval v)`]mp_tac(CONJUNCT1 evaluate_closed) >>
    simp[] >> strip_tac >>
    Q.ISPECL_THEN[`s2`,`pes`,`(s2,Rval(menv,mr))`]mp_tac(Q.GEN`s`evaluate_match_with_matchres_closed)>>
    simp[] >> strip_tac >>
    `FV mr ⊆ set (MAP FST (menv ++ env))` by (
      fsrw_tac[DNF_ss][SUBSET_DEF,FORALL_PROD,MEM_MAP,EXISTS_PROD] >>
      pop_assum mp_tac >>
      simp[EXTENSION] >>
      fsrw_tac[DNF_ss][MEM_MAP,EXISTS_PROD] >>
      METIS_TAC[] ) >>
    fs[Abbr`P`] >> rfs[] >> fs[] >>
    first_x_assum(qspec_then`m`mp_tac)>>
    fsrw_tac[DNF_ss][] >>
    qpat_assum`evaluate_match_with P cenv s2 env v pes (res0,res1)`kall_tac >>
    map_every qx_gen_tac [`se`,`re`] >> strip_tac >>
    qabbrev_tac`emr = exp_to_Cexp m mr` >>
    qspecl_then[`FEMPTY`,`FEMPTY`,`sb`,`sd`,`eenv ⊌ enva`,`wenv ⊌ enva`,`emr`,`(se,re)`]mp_tac Cevaluate_any_syneq_any >>
    `∀v. v ∈ FRANGE sb ⇒ Cclosed FEMPTY v` by (
      unabbrev_all_tac >>
      fsrw_tac[DNF_ss][FRANGE_store_to_Cstore,MEM_MAP,EVERY_MEM] >>
      rw[] >> match_mp_tac (CONJUNCT1 v_to_Cv_closed) >> res_tac ) >>
    `∀v. v ∈ FRANGE enva ⇒ Cclosed FEMPTY v` by (
      unabbrev_all_tac >>
      match_mp_tac IN_FRANGE_alist_to_fmap_suff >>
      fsrw_tac[DNF_ss][env_to_Cenv_MAP,MEM_MAP,FORALL_PROD,EVERY_MEM] >>
      rw[] >> match_mp_tac (CONJUNCT1 v_to_Cv_closed) >> res_tac ) >>
    `free_vars FEMPTY ea ⊆ FDOM enva` by (
      unabbrev_all_tac >>
      fsrw_tac[DNF_ss][env_to_Cenv_MAP,SUBSET_DEF,MEM_MAP,FORALL_PROD,EXISTS_PROD]) >>
    `∀v. v ∈ FRANGE sa ⇒ Cclosed FEMPTY v` by (
      unabbrev_all_tac >>
      fsrw_tac[DNF_ss][FRANGE_store_to_Cstore,MEM_MAP,EVERY_MEM] >>
      rw[] >> match_mp_tac (CONJUNCT1 v_to_Cv_closed) >> res_tac ) >>
    qspecl_then[`FEMPTY`,`FEMPTY`,`sa`,`enva`,`ea`,`(sd,Rval w)`]mp_tac(CONJUNCT1 Cevaluate_closed) >>
    simp[] >> strip_tac >>
    qspecl_then[`FEMPTY`,`sd`,`w`,`ps`,`wenv`,`SOME emr`]mp_tac
      (INST_TYPE[alpha|->``:Cexp``](Q.GENL[`v`,`s`,`c`]Cevaluate_match_closed)) >>
    simp[] >> strip_tac >>
    `∀v. v ∈ FRANGE eenv ⇒ Cclosed FEMPTY v` by (
      unabbrev_all_tac >>
      match_mp_tac IN_FRANGE_alist_to_fmap_suff >>
      fsrw_tac[DNF_ss][env_to_Cenv_MAP,MEM_MAP,EVERY_MEM,FORALL_PROD,EXISTS_PROD] >>
      rw[] >> match_mp_tac (CONJUNCT1 v_to_Cv_closed) >> res_tac ) >>
    qmatch_abbrev_tac`(P ⇒ Q) ⇒ R` >>
    `P` by (
      map_every qunabbrev_tac[`P`,`Q`,`R`] >>
      conj_tac >- (
        match_mp_tac fmap_rel_FUNION_rels >> rw[] ) >>
      conj_tac >- (
        match_mp_tac IN_FRANGE_FUNION_suff >> rw[] ) >>
      conj_tac >- (
        unabbrev_all_tac >>
        rw[env_to_Cenv_MAP,MAP_MAP_o,combinTheory.o_DEF,UNCURRY] >>
        srw_tac[ETA_ss][] ) >>
      match_mp_tac IN_FRANGE_FUNION_suff >> rw[] ) >>
    simp[] >>
    map_every qunabbrev_tac[`P`,`Q`,`R`] >>
    fsrw_tac[DNF_ss][FORALL_PROD] >>
    map_every qx_gen_tac[`sf`,`rf`] >> strip_tac >>
    qspecl_then[`FEMPTY`,`FEMPTY`,`sd`,`wenv ⊌ enva`,`emr`,`(sf,rf)`,`fv`,`w`]mp_tac Cevaluate_FUPDATE >>
    `fv ∉ free_vars FEMPTY emr` by (
      unabbrev_all_tac >>
      match_mp_tac fresh_var_not_in_any >>
      fsrw_tac[DNF_ss][SUBSET_DEF,Cpes_vars_thm,pes_to_Cpes_MAP,LET_THM,MEM_MAP,
                       UNCURRY,EXISTS_PROD,FORALL_PROD] >>
      fsrw_tac[DNF_ss][env_to_Cenv_MAP,MEM_MAP,EXISTS_PROD] >>
      PROVE_TAC[] ) >>
    `FDOM wenv = FDOM eenv` by fs[fmap_rel_def] >>
    fsrw_tac[DNF_ss][FORALL_PROD] >>
    map_every qx_gen_tac[`sg`,`rg`] >> strip_tac >>
    `(wenv ⊌ enva) |+ (fv,w) = wenv ⊌ enva |+ (fv,w)` by (
      `fv ∉ FDOM eenv` by (
        unabbrev_all_tac >>
        match_mp_tac fresh_var_not_in_any >>
        fs[fmap_rel_def] >>
        fsrw_tac[DNF_ss][Cpes_vars_thm] >>
        `set (MAP FST (env_to_Cenv m menv)) = Cpat_vars (SND (pat_to_Cpat m [] p))` by (
          fsrw_tac[DNF_ss][env_to_Cenv_MAP,MAP_MAP_o,pairTheory.LAMBDA_PROD,combinTheory.o_DEF,FST_pair,FST_triple] >>
          METIS_TAC[Cpat_vars_pat_to_Cpat,pairTheory.SND,pairTheory.pair_CASES] ) >>
        fs[] >>
        fsrw_tac[DNF_ss][SUBSET_DEF,pes_to_Cpes_MAP,MEM_MAP,LET_THM] >>
        qpat_assum `MEM (p,x) pes` mp_tac >>
        rpt (pop_assum kall_tac) >>
        fsrw_tac[DNF_ss][pairTheory.EXISTS_PROD,pairTheory.UNCURRY] >>
        METIS_TAC[Cpat_vars_pat_to_Cpat,pairTheory.SND,pairTheory.pair_CASES] ) >>
      rw[FUNION_FUPDATE_2] ) >>
    disch_then(qspecl_then[`sg`,`rg`]mp_tac)>> fs[] >>
    qmatch_abbrev_tac`(P ⇒ Q) ⇒ R` >>
    `P` by (
      map_every qunabbrev_tac[`P`,`Q`,`R`] >>
      simp[FLOOKUP_UPDATE] >>
      conj_tac >- (
        spose_not_then strip_assume_tac >>
        unabbrev_all_tac >> rw[] >>
        qpat_assum`fresh_var X ∈ Y`mp_tac >>
        simp[] >>
        match_mp_tac fresh_var_not_in_any >>
        fsrw_tac[DNF_ss][SUBSET_DEF,Cpes_vars_thm,MEM_MAP,pes_to_Cpes_MAP,LET_THM,UNCURRY] >>
        PROVE_TAC[] ) >>
      conj_tac >- (
        unabbrev_all_tac >>
        fsrw_tac[DNF_ss][SUBSET_DEF,pes_to_Cpes_MAP,env_to_Cenv_MAP,MEM_MAP,LET_THM,UNCURRY] >>
        PROVE_TAC[] ) >>
      match_mp_tac IN_FRANGE_DOMSUB_suff >>
      rw[] ) >>
    simp[] >>
    map_every qunabbrev_tac[`P`,`Q`,`R`] >>
    metis_tac[result_rel_syneq_trans,result_rel_syneq_sym,
              fmap_rel_syneq_sym,fmap_rel_syneq_trans]) >>
  strip_tac >- (
    rw[exp_to_Cexp_def,LET_THM] >>
    rw[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][EXISTS_PROD]) >>
  strip_tac >- (
    rw[exp_to_Cexp_def,LET_THM] >>
    rw[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][bind_def,EXISTS_PROD] >>
    disj1_tac >>
    qspecl_then[`cenv`,`s`,`env`,`exp`,`(s',Rval v)`]mp_tac(CONJUNCT1 evaluate_closed) >>
    simp[] >> strip_tac >> fs[] >>
    rpt (first_x_assum (qspec_then `m` mp_tac)) >>
    rw[] >>
    qmatch_assum_rename_tac`syneq FEMPTY (v_to_Cv m v) w`[] >>
    pop_assum mp_tac >>
    Q.PAT_ABBREV_TAC`P = X ⊆ Y` >>
    `P` by (
      unabbrev_all_tac >>
      fsrw_tac[DNF_ss][SUBSET_DEF] >>
      METIS_TAC[] ) >>
    simp[] >> qunabbrev_tac`P` >>
    qmatch_assum_abbrev_tac`Cevaluate FEMPTY FEMPTY sa enva ea (sd,Rval w)` >>
    pop_assum kall_tac >>
    fsrw_tac[DNF_ss][] >>
    map_every qx_gen_tac[`se`,`re`] >>
    strip_tac >>
    qmatch_assum_abbrev_tac`Cevaluate FEMPTY FEMPTY sb envb eb (se,re)` >>
    CONV_TAC (RESORT_EXISTS_CONV List.rev) >>
    map_every qexists_tac[`w`,`sd`] >>
    rw[] >>
    qspecl_then[`FEMPTY`,`FEMPTY`,`sb`,`sd`,`envb`,`enva |+ (n,w)`,`eb`,`(se,re)`]mp_tac Cevaluate_any_syneq_any >>
    `(∀v. v ∈ FRANGE sa ⇒ Cclosed FEMPTY v) ∧
     (∀v. v ∈ FRANGE sb ⇒ Cclosed FEMPTY v)` by (
      unabbrev_all_tac >>
      fsrw_tac[DNF_ss][FRANGE_store_to_Cstore,MEM_MAP,EVERY_MEM] >>
      rw[] >> match_mp_tac(CONJUNCT1 v_to_Cv_closed) >> res_tac) >>
    `(free_vars FEMPTY ea ⊆ FDOM enva) ∧
     (free_vars FEMPTY eb ⊆ FDOM envb)` by (
      unabbrev_all_tac >>
      fsrw_tac[DNF_ss][env_to_Cenv_MAP,MAP_MAP_o,SUBSET_DEF,MEM_MAP,FORALL_PROD,EXISTS_PROD]) >>
    `(∀v. v ∈ FRANGE enva ⇒ Cclosed FEMPTY v) ∧
     (∀v. v ∈ FRANGE envb ⇒ Cclosed FEMPTY v)` by (
      unabbrev_all_tac >> conj_tac >>
      match_mp_tac IN_FRANGE_alist_to_fmap_suff >>
      fsrw_tac[DNF_ss][MEM_MAP,env_to_Cenv_MAP,FORALL_PROD,EVERY_MEM] >>
      rw[] >> match_mp_tac (CONJUNCT1 v_to_Cv_closed) >> res_tac >> fs[] ) >>
    qspecl_then[`FEMPTY`,`FEMPTY`,`sa`,`enva`,`ea`,`(sd,Rval w)`]mp_tac(CONJUNCT1 Cevaluate_closed) >>
    simp[] >> strip_tac >>
    qmatch_abbrev_tac`(P ⇒ Q) ⇒ R` >>
    `P` by (
      unabbrev_all_tac >>
      conj_tac >- (
        rw[fmap_rel_def,env_to_Cenv_MAP,FAPPLY_FUPDATE_THM] >>
        rw[] ) >>
      fsrw_tac[DNF_ss][] >>
      match_mp_tac IN_FRANGE_DOMSUB_suff >>
      simp[] ) >>
    simp[] >>
    unabbrev_all_tac >>
    fsrw_tac[DNF_ss][FORALL_PROD] >>
    metis_tac[result_rel_syneq_trans,fmap_rel_syneq_trans] ) >>
  strip_tac >- (
    rw[exp_to_Cexp_def,LET_THM] >>
    rw[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][EXISTS_PROD]) >>
  strip_tac >- (
    rw[exp_to_Cexp_def,LET_THM,FST_triple] >>
    fs[] >>
    rw[defs_to_Cdefs_MAP] >>
    rw[Once Cevaluate_cases,FOLDL_FUPDATE_LIST] >>
    `FV exp ⊆ set (MAP FST funs) ∪ set (MAP FST env)` by (
      fsrw_tac[DNF_ss][SUBSET_DEF,pairTheory.FORALL_PROD,MEM_MAP,pairTheory.EXISTS_PROD] >>
      METIS_TAC[] ) >>
    fs[] >>
    `EVERY closed (MAP (FST o SND) (build_rec_env tvs funs env))` by (
      match_mp_tac build_rec_env_closed >>
      fs[] >>
      fsrw_tac[DNF_ss][SUBSET_DEF,pairTheory.FORALL_PROD,MEM_MAP,pairTheory.EXISTS_PROD,MEM_EL,FST_5tup] >>
      METIS_TAC[] ) >>
    fs[] >>
    first_x_assum (qspec_then `m` mp_tac) >>
    fs[] >>
    simp_tac std_ss [build_rec_env_def,bind_def,FOLDR_CONS_5tup] >>
    fsrw_tac[DNF_ss][EXISTS_PROD,FORALL_PROD] >>
    simp_tac std_ss [FUNION_alist_to_fmap] >>
    Q.PAT_ABBREV_TAC`ee = alist_to_fmap (env_to_Cenv X Y)` >>
    simp_tac (srw_ss()) [env_to_Cenv_MAP,MAP_MAP_o,combinTheory.o_DEF,pairTheory.LAMBDA_PROD] >>
    simp_tac (srw_ss()) [v_to_Cv_def,LET_THM,pairTheory.UNCURRY,defs_to_Cdefs_MAP] >>
    Q.PAT_ABBREV_TAC`ls:(string#Cv) list = MAP f funs` >>
    `ALL_DISTINCT (MAP FST ls)` by (
      unabbrev_all_tac >>
      rw[MAP_MAP_o,combinTheory.o_DEF,pairTheory.LAMBDA_PROD,FST_triple] ) >>
    rw[FUPDATE_LIST_ALL_DISTINCT_REVERSE] >>
    rw[MEM_MAP,FORALL_PROD,EXISTS_PROD] >>
    fs[FST_5tup] >>
    qmatch_assum_rename_tac `Cevaluate FEMPTY FEMPTY X Y Z (p1,p2)`["X","Y","Z"] >>
    map_every qexists_tac[`p1`,`p2`] >>
    reverse conj_tac >- METIS_TAC[] >>
    reverse conj_tac >- METIS_TAC[] >>
    spose_not_then strip_assume_tac >>
    pop_assum mp_tac >> rw[EL_MAP,UNCURRY]) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rw[] >>
    fsrw_tac[DNF_ss][EXISTS_PROD] >>
    rw[Once Cevaluate_cases] ) >>
  strip_tac >- (
    rw[] >>
    rw[Once (CONJUNCT2 Cevaluate_cases)] >>
    fsrw_tac[DNF_ss][EXISTS_PROD] >>
    qspecl_then[`cenv`,`s`,`env`,`exp`,`(s',Rval v)`]mp_tac(CONJUNCT1 evaluate_closed) >>
    simp[] >> strip_tac >> fs[] >>
    rpt (first_x_assum (qspec_then`m` mp_tac)) >>
    rw[] >>
    qmatch_assum_rename_tac`syneq FEMPTY (v_to_Cv m v) w`[] >>
    qmatch_assum_abbrev_tac`Cevaluate FEMPTY FEMPTY sa enva ea (sd,Rval w)` >>
    pop_assum kall_tac >>
    CONV_TAC SWAP_EXISTS_CONV >> qexists_tac`sd` >>
    CONV_TAC SWAP_EXISTS_CONV >> qexists_tac`w` >> rw[] >>
    qmatch_assum_abbrev_tac`Cevaluate_list FEMPTY FEMPTY sb enva eb (se,Rval ws)` >>
    ntac 2 (pop_assum kall_tac) >>
    qspecl_then[`FEMPTY`,`FEMPTY`,`sb`,`sd`,`enva`,`enva`,`eb`,`(se,Rval ws)`]mp_tac Cevaluate_list_any_syneq_any >>
    `∀v. v ∈ FRANGE enva ⇒ Cclosed FEMPTY v` by (
      unabbrev_all_tac >>
      match_mp_tac IN_FRANGE_alist_to_fmap_suff >>
      fsrw_tac[DNF_ss][MEM_MAP,env_to_Cenv_MAP,EVERY_MEM,FORALL_PROD] >>
      rw[] >> match_mp_tac (CONJUNCT1 v_to_Cv_closed) >> res_tac ) >>
    `(∀v. v ∈ FRANGE sa ⇒ Cclosed FEMPTY v) ∧
     (∀v. v ∈ FRANGE sb ⇒ Cclosed FEMPTY v)` by (
      unabbrev_all_tac >>
      fsrw_tac[DNF_ss][FRANGE_store_to_Cstore,MEM_MAP,EVERY_MEM] >>
      rw[] >> match_mp_tac(CONJUNCT1 v_to_Cv_closed) >> res_tac) >>
    `(free_vars FEMPTY ea ⊆ FDOM enva) ∧
     (BIGUNION (IMAGE (free_vars FEMPTY) (set eb)) ⊆ FDOM enva)` by (
      unabbrev_all_tac >>
      fsrw_tac[DNF_ss][env_to_Cenv_MAP,MAP_MAP_o,SUBSET_DEF,MEM_MAP,FORALL_PROD,EXISTS_PROD]) >>
    qspecl_then[`FEMPTY`,`FEMPTY`,`sa`,`enva`,`ea`,`(sd,Rval w)`]mp_tac(CONJUNCT1 Cevaluate_closed) >>
    simp[] >> strip_tac >>
    fsrw_tac[DNF_ss][FORALL_PROD] >>
    map_every qx_gen_tac[`sf`,`rf`] >>
    strip_tac >>
    map_every qexists_tac[`sf`,`rf`] >>
    simp[] >>
    conj_tac >- METIS_TAC[fmap_rel_syneq_trans] >>
    fsrw_tac[DNF_ss][EVERY2_EVERY,EVERY_MEM,FORALL_PROD,MEM_ZIP] >>
    `LENGTH vs = LENGTH ws` by rw[] >>
    qpat_assum `LENGTH ws = LENGTH rf` assume_tac >>
    fsrw_tac[DNF_ss][MEM_ZIP] >>
    rw[EL_MAP] >>
    rpt (first_x_assum (qspec_then`n`mp_tac)) >>
    rw[EL_MAP] >>
    METIS_TAC[syneq_trans] ) >>
  strip_tac >- (
    rw[] >>
    rw[Once (CONJUNCT2 Cevaluate_cases)] >>
    fsrw_tac[DNF_ss][EXISTS_PROD] ) >>
  rw[] >>
  rw[Once (CONJUNCT2 Cevaluate_cases)] >>
  fsrw_tac[DNF_ss][EXISTS_PROD] >>
  disj2_tac >>
  qspecl_then[`cenv`,`s`,`env`,`exp`,`(s',Rval v)`]mp_tac(CONJUNCT1 evaluate_closed) >>
  simp[] >> strip_tac >> fs[] >>
  rpt (first_x_assum (qspec_then`m` mp_tac)) >>
  rw[] >>
  qmatch_assum_rename_tac`syneq FEMPTY (v_to_Cv m v) w`[] >>
  qmatch_assum_abbrev_tac`Cevaluate FEMPTY FEMPTY sa enva ea (sd,Rval w)` >>
  pop_assum kall_tac >>
  CONV_TAC SWAP_EXISTS_CONV >> qexists_tac`sd` >>
  CONV_TAC SWAP_EXISTS_CONV >> qexists_tac`w` >> rw[] >>
  qmatch_assum_abbrev_tac`Cevaluate_list FEMPTY FEMPTY sb enva eb (se,Rerr err)` >>
  pop_assum kall_tac >>
  qspecl_then[`FEMPTY`,`FEMPTY`,`sb`,`sd`,`enva`,`enva`,`eb`,`(se,Rerr err)`]mp_tac Cevaluate_list_any_syneq_any >>
  `∀v. v ∈ FRANGE enva ⇒ Cclosed FEMPTY v` by (
    unabbrev_all_tac >>
    match_mp_tac IN_FRANGE_alist_to_fmap_suff >>
    fsrw_tac[DNF_ss][MEM_MAP,env_to_Cenv_MAP,EVERY_MEM,FORALL_PROD] >>
    rw[] >> match_mp_tac (CONJUNCT1 v_to_Cv_closed) >> res_tac ) >>
  `(∀v. v ∈ FRANGE sa ⇒ Cclosed FEMPTY v) ∧
   (∀v. v ∈ FRANGE sb ⇒ Cclosed FEMPTY v)` by (
    unabbrev_all_tac >>
    fsrw_tac[DNF_ss][FRANGE_store_to_Cstore,MEM_MAP,EVERY_MEM] >>
    rw[] >> match_mp_tac(CONJUNCT1 v_to_Cv_closed) >> res_tac) >>
  `(free_vars FEMPTY ea ⊆ FDOM enva) ∧
   (BIGUNION (IMAGE (free_vars FEMPTY) (set eb)) ⊆ FDOM enva)` by (
    unabbrev_all_tac >>
    fsrw_tac[DNF_ss][env_to_Cenv_MAP,MAP_MAP_o,SUBSET_DEF,MEM_MAP,FORALL_PROD,EXISTS_PROD]) >>
  qspecl_then[`FEMPTY`,`FEMPTY`,`sa`,`enva`,`ea`,`(sd,Rval w)`]mp_tac(CONJUNCT1 Cevaluate_closed) >>
  simp[] >> strip_tac >>
  fsrw_tac[DNF_ss][FORALL_PROD] >>
  METIS_TAC[fmap_rel_syneq_trans])

set_trace"goalstack print goal at top"0

val exp_to_Cexp_thm1 = store_thm("exp_to_Cexp_thm1",
  ``(∀cenv s env exp res. evaluate cenv s env exp res ⇒
     (*
     (EVERY closed s) ∧
     (EVERY closed (MAP (FST o SND) env)) ∧
     *)
     (FV exp ⊆ set (MAP FST env)) ∧
     good_cenv cenv ∧ (SND res ≠ Rerr Rtype_error) ⇒
     ∀m. good_cmap cenv m.cnmap ⇒
       ∃Cres.
         Cevaluate FEMPTY
           (MAP (v_to_Cv m) s)
           (env_to_Cenv m env)
           (exp_to_Cexp m exp) Cres ∧
         EVERY2 (syneq FEMPTY FEMPTY) (MAP (v_to_Cv m) (FST res)) (FST Cres) ∧
         result_rel (syneq FEMPTY FEMPTY) (map_result (v_to_Cv m) (SND res)) (SND Cres)) ∧
    (∀cenv s env exps res. evaluate_list cenv s env exps res ⇒
     (*
     (EVERY closed s) ∧
     (EVERY closed (MAP (FST o SND) env)) ∧
     *)
     (BIGUNION (IMAGE FV (set exps)) ⊆ set (MAP FST env)) ∧
     good_cenv cenv ∧ (SND res ≠ Rerr Rtype_error) ⇒
     ∀m. good_cmap cenv m.cnmap ⇒
       ∃Cres.
         Cevaluate_list FEMPTY
           (MAP (v_to_Cv m) s)
           (env_to_Cenv m env)
           (MAP (exp_to_Cexp m) exps) Cres ∧
         EVERY2 (syneq FEMPTY FEMPTY) (MAP (v_to_Cv m) (FST res)) (FST Cres) ∧
         result_rel (EVERY2 (syneq FEMPTY FEMPTY)) (map_result (MAP (v_to_Cv m)) (SND res)) (SND Cres))``,
  ho_match_mp_tac evaluate_nicematch_strongind >>
  strip_tac >- rw[exp_to_Cexp_def,v_to_Cv_def] >>
  strip_tac >- rw[exp_to_Cexp_def] >>
  strip_tac >- (
    rw[exp_to_Cexp_def] >> fs[] >>
    first_x_assum(qspec_then`m`mp_tac) >> rw[] >>
    rw[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][] >>
    disj1_tac >>
    Cases_on`Cres`>>fs[] >>
    metis_tac[] ) >>
  strip_tac >- (
    rw[exp_to_Cexp_def] >> fs[] >>
    first_x_assum(qspec_then`m`mp_tac) >> rw[] >>
    Cases_on`Cres` >>
    rw[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][EXISTS_PROD] >>
    disj2_tac >> disj1_tac >>
    qmatch_assum_rename_tac`Cevaluate FEMPTY FEMPTY X Y Z
      (s0,Rerr (Rraise (Int_error n)))`["X","Y","Z"] >>
    CONV_TAC (RESORT_EXISTS_CONV List.rev) >>
    map_every qexists_tac[`n`,`s0`] >>
    simp[] >>
    qspecl_then[`cenv`,`s`,`env`,`exp`,`(s',Rerr(Rraise(Int_error n)))`]
      mp_tac(CONJUNCT1 evaluate_closed) >>
    simp[] >> strip_tac >> fs[] >>
    first_x_assum(qspec_then`m`mp_tac) >>
    simp[bind_def] >>
    qmatch_abbrev_tac`(P ⇒ Q) ⇒ R` >>
    `P` by (
      unabbrev_all_tac >>
      fsrw_tac[DNF_ss][SUBSET_DEF] >>
      metis_tac[] ) >>
    simp[] >>
    map_every qunabbrev_tac[`P`,`Q`,`R`] >>
    rw[] >>
    qmatch_assum_abbrev_tac`Cevaluate FEMPTY FEMPTY ss env0 exp0 res0` >>
    qspecl_then[`FEMPTY`,`FEMPTY`,`ss`,`s0`,`env0`,`exp0`,`res0`]mp_tac
      Cevaluate_any_syneq_store >>
    simp[] >>
    `∀v. v ∈ FRANGE env0 ⇒ Cclosed FEMPTY v` by (
      unabbrev_all_tac >>
      match_mp_tac IN_FRANGE_alist_to_fmap_suff >> simp[] >>
      fs[EVERY_MEM,env_to_Cenv_MAP,MAP_MAP_o,v_to_Cv_def] >>
      fs[combinTheory.o_DEF,FORALL_PROD,MEM_MAP,EXISTS_PROD] >>
      rw[]>>rw[]>>
      match_mp_tac (CONJUNCT1 v_to_Cv_closed) >>
      metis_tac[] ) >>
    `free_vars FEMPTY exp0 ⊆ FDOM env0` by (
      unabbrev_all_tac >>
      fs[env_to_Cenv_MAP,MAP_MAP_o,v_to_Cv_def] >>
      fs[combinTheory.o_DEF,LAMBDA_PROD,FST_pair,FST_triple] ) >>
    simp[] >>
    `∀v. v ∈ FRANGE ss ⇒ Cclosed FEMPTY v` by (
      unabbrev_all_tac >>
      rw[FRANGE_store_to_Cstore,MEM_MAP] >>
      match_mp_tac (CONJUNCT1 v_to_Cv_closed) >>
      fs[EVERY_MEM] ) >>
    `∀v. v ∈ FRANGE (store_to_Cstore m s) ⇒ Cclosed FEMPTY v` by (
      rw[FRANGE_store_to_Cstore,MEM_MAP] >>
      match_mp_tac (CONJUNCT1 v_to_Cv_closed) >>
      fs[EVERY_MEM] ) >>
    qmatch_assum_abbrev_tac`Cevaluate FEMPTY FEMPTY s1 env1 exp1 (s0,r1)` >>
    qspecl_then[`FEMPTY`,`FEMPTY`,`s1`,`env1`,`exp1`,`(s0,r1)`]mp_tac(CONJUNCT1 Cevaluate_closed) >>
    `free_vars FEMPTY exp1 ⊆ FDOM env1` by (
      unabbrev_all_tac >> simp[] >>
      simp[env_to_Cenv_MAP,MAP_MAP_o,combinTheory.o_DEF,FST_pair,LAMBDA_PROD,FST_triple] ) >>
    `∀v. v ∈ FRANGE env1 ⇒ Cclosed FEMPTY v` by (
      unabbrev_all_tac >>
      match_mp_tac IN_FRANGE_alist_to_fmap_suff >>
      simp[env_to_Cenv_MAP,MAP_MAP_o,combinTheory.o_DEF,EXISTS_PROD,MEM_MAP] >>
      rw[] >> match_mp_tac (CONJUNCT1 v_to_Cv_closed) >>
      fs[MEM_MAP,EVERY_MEM,EXISTS_PROD] >>
      PROVE_TAC[] ) >>
    simp[Abbr`r1`] >> strip_tac >>
    simp[Abbr`res0`,EXISTS_PROD] >>
    strip_tac >>
    Q.PAT_ABBREV_TAC`env2 = env1 |+ X` >>
    `env0 = env2` by (
      unabbrev_all_tac >>
      rw[env_to_Cenv_MAP,alist_to_fmap_MAP_values,v_to_Cv_def] ) >>
    metis_tac[fmap_rel_syneq_trans, result_rel_syneq_trans] ) >>
  strip_tac >- (
    rpt gen_tac >>
    simp[AND_IMP_INTRO] >>
    Q.PAT_ABBREV_TAC`D = (X ∨ Y ∨ Z)` >>
    strip_tac >>
    rw[exp_to_Cexp_def] >>
    rfs[] >> fs[] >>
    first_x_assum (qspec_then`m`mp_tac) >>rw[]>>
    rw[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][] >>
    disj2_tac >>
    qexists_tac`FST Cres` >>
    Cases_on`Cres`>>fs[] >>
    Cases_on`err`>>fs[]>>
    Cases_on`e`>>fs[markerTheory.Abbrev_def] ) >>
  strip_tac >- (
    rw[exp_to_Cexp_def,v_to_Cv_def,
       exps_to_Cexps_MAP,vs_to_Cvs_MAP,
       Cevaluate_con] >>
    rw[syneq_cases] >>
    fsrw_tac[DNF_ss][EVERY2_EVERY,EVERY_MEM,pairTheory.FORALL_PROD] >>
    fsrw_tac[ETA_ss][] >>
    first_x_assum (qspec_then `m` mp_tac) >>
    rw[EXISTS_PROD]) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rw[exp_to_Cexp_def,v_to_Cv_def,
       exps_to_Cexps_MAP,Cevaluate_con] >>
    fsrw_tac[ETA_ss][] >>
    first_x_assum (qspec_then `m` mp_tac) >>
    rw[EXISTS_PROD]) >>
  strip_tac >- (
    fs[exp_to_Cexp_def,MEM_MAP,pairTheory.EXISTS_PROD,env_to_Cenv_MAP] >>
    rpt gen_tac >> rpt (disch_then strip_assume_tac) >> qx_gen_tac `m` >>
    rw[SIMP_RULE(srw_ss())[LAMBDA_PROD,UNCURRY](Q.SPEC`UNCURRY f`(INST_TYPE[alpha|->``:'a#'d``]alist_to_fmap_MAP_values))] >>
    `n ∈ FDOM (alist_to_fmap env)` by (
      rw[MEM_MAP,pairTheory.EXISTS_PROD] >> PROVE_TAC[] ) >>
    rw[o_f_FAPPLY,UNCURRY] >>
    PROVE_TAC[ALOOKUP_SOME_FAPPLY_alist_to_fmap,syneq_refl,FST] ) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rw[exp_to_Cexp_def,v_to_Cv_def,env_to_Cenv_MAP,LET_THM] >>
    srw_tac[DNF_ss][Once syneq_cases] >>
    rw[FINITE_has_fresh_string,fresh_var_not_in]) >>
  strip_tac >- (
    rw[exp_to_Cexp_def,LET_THM] >> fs[] >>
    rw[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][EXISTS_PROD] >>
    first_x_assum(qspec_then`m`mp_tac)>>simp[]>>
    disch_then(Q.X_CHOOSE_THEN`s0`mp_tac)>>
    disch_then(Q.X_CHOOSE_THEN`v0`strip_assume_tac)>>
    CONV_TAC SWAP_EXISTS_CONV >>qexists_tac`s0`>>
    CONV_TAC SWAP_EXISTS_CONV >>qexists_tac`v0`>>
    simp[] >>
    fs[do_uapp_def,LET_THM,store_alloc_def] >>
    BasicProvers.EVERY_CASE_TAC >>
    fs[v_to_Cv_def,LET_THM] >- (
      BasicProvers.VAR_EQ_TAC >>
      BasicProvers.VAR_EQ_TAC >>
      fs[v_to_Cv_def] >>
      simp[Once syneq_cases] >>
      fs[fmap_rel_def] >>
      reverse conj_asm2_tac >- (
        numLib.LEAST_ELIM_TAC >>
        qabbrev_tac`n = LENGTH s2` >>
        conj_tac >- (
          qexists_tac`SUC n` >>
          srw_tac[ARITH_ss][] ) >>
        qx_gen_tac`a` >>
        srw_tac[ARITH_ss][] >>
        Cases_on`n < a` >- (res_tac >> fs[]) >>
        DECIDE_TAC ) >>
      fs[] >>
      conj_tac >- (
        srw_tac[ARITH_ss][EXTENSION] ) >>
      simp[FAPPLY_store_to_Cstore,FAPPLY_FUPDATE_THM] >>
      fs[FAPPLY_store_to_Cstore] >>
      qx_gen_tac`x` >>
      Cases_on`x < LENGTH s2` >- (
        srw_tac[ARITH_ss][] >>
        rw[rich_listTheory.EL_APPEND1] ) >>
      strip_tac >>
      `x = LENGTH s2` by DECIDE_TAC >>
      fs[] >>
      simp[rich_listTheory.EL_LENGTH_APPEND] ) >>
    fs[Q.SPECL[`FEMPTY`,`CLoc n`]syneq_cases] >>
    rpt BasicProvers.VAR_EQ_TAC >>
    fs[fmap_rel_def,store_lookup_def] >>
    simp[FLOOKUP_DEF] >>
    BasicProvers.VAR_EQ_TAC >>
    fs[FAPPLY_store_to_Cstore] ) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rw[exp_to_Cexp_def,LET_THM,EXISTS_PROD] >>
    rw[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][] ) >>
  strip_tac >- (
    ntac 2 gen_tac >>
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
      rpt (first_x_assum (qspec_then `m` mp_tac)) >>
      rw[] >>
      qmatch_assum_rename_tac `syneq FEMPTY (v_to_Cv m v1) w1`[] >>
      qspecl_then[`cenv`,`s`,`env`,`e1`,`(s',Rval v1)`]mp_tac(CONJUNCT1 evaluate_closed) >>
      simp[] >> strip_tac >> fs[] >>
      qmatch_assum_rename_tac `syneq FEMPTY (v_to_Cv m v2) w2`[] >>
      qmatch_assum_rename_tac`SND r1 = Rval w1`[] >>
      qmatch_assum_rename_tac`SND r2 = Rval w2`[] >>
      qmatch_assum_abbrev_tac`Cevaluate FEMPTY FEMPTY sa enva e1a r1` >>
      qmatch_assum_abbrev_tac`Cevaluate FEMPTY FEMPTY sb enva e2a r2` >>
      qspecl_then[`FEMPTY`,`FEMPTY`,`sb`,`FST r1`,`enva`,`e2a`,`r2`]mp_tac Cevaluate_any_syneq_store >>
      `∀v. v ∈ FRANGE enva ⇒ Cclosed FEMPTY v` by (
        unabbrev_all_tac >>
        match_mp_tac IN_FRANGE_alist_to_fmap_suff >>
        simp[env_to_Cenv_MAP,MAP_MAP_o,combinTheory.o_DEF,MEM_MAP,EXISTS_PROD] >>
        srw_tac[DNF_ss][] >>
        match_mp_tac (CONJUNCT1 v_to_Cv_closed) >>
        fs[EVERY_MEM,FORALL_PROD,MEM_MAP,EXISTS_PROD] >>
        metis_tac[] ) >>
      `free_vars FEMPTY e2a ⊆ FDOM enva` by (
        unabbrev_all_tac >>
        fsrw_tac[DNF_ss][SUBSET_DEF] >>
        simp[env_to_Cenv_MAP,MAP_MAP_o,combinTheory.o_DEF,FST_pair,LAMBDA_PROD,FST_triple]) >>
      qspecl_then[`FEMPTY`,`FEMPTY`,`sb`,`enva`,`e2a`,`r2`]mp_tac(CONJUNCT1 Cevaluate_closed) >>
      `∀v. v ∈ FRANGE sb ⇒ Cclosed FEMPTY v` by (
        unabbrev_all_tac >>
        simp[FRANGE_store_to_Cstore,MEM_MAP] >>
        fsrw_tac[DNF_ss][EVERY_MEM] >> rw[] >>
        match_mp_tac (CONJUNCT1 v_to_Cv_closed) >>
        rw[] ) >>
      qspecl_then[`FEMPTY`,`FEMPTY`,`sa`,`enva`,`e1a`,`r1`]mp_tac(CONJUNCT1 Cevaluate_closed) >>
      `free_vars FEMPTY e1a ⊆ FDOM enva` by (
        unabbrev_all_tac >>
        fsrw_tac[DNF_ss][SUBSET_DEF] >>
        simp[env_to_Cenv_MAP,MAP_MAP_o,combinTheory.o_DEF,FST_pair,LAMBDA_PROD,FST_triple])>>
      `∀v. v ∈ FRANGE sa ⇒ Cclosed FEMPTY v` by (
        unabbrev_all_tac >>
        simp[FRANGE_store_to_Cstore,MEM_MAP] >>
        fsrw_tac[DNF_ss][EVERY_MEM] >> rw[] >>
        match_mp_tac (CONJUNCT1 v_to_Cv_closed) >>
        rw[] ) >>
      simp[] >> strip_tac >> strip_tac >>
      disch_then(Q.X_CHOOSE_THEN`r3`strip_assume_tac) >>
      qmatch_assum_rename_tac`syneq FEMPTY w2 w3`[] >>
      qmatch_assum_rename_tac `do_app s3 env (Opn opn) v1 v2 = SOME (s4,env',exp'')` [] >>
      qspecl_then[`cenv`,`s'`,`env`,`e2`,`(s3,Rval v2)`]mp_tac(CONJUNCT1 evaluate_closed) >>
      simp[] >> strip_tac >>
      Q.ISPECL_THEN[`s3`,`s4`,`env`,`Opn opn`,`v1`,`v2`,`env'`,`exp''`]mp_tac do_app_closed >>
      simp[] >> strip_tac >> fs[] >>
      fs[do_app_Opn_SOME] >>
      rpt BasicProvers.VAR_EQ_TAC >>
      qexists_tac`FST r3` >>
      qexists_tac `w1` >>
      qexists_tac `w3` >>
      qexists_tac`FST r1` >>
      PairCases_on`r1`>>PairCases_on`r3`>>
      fs[] >> rpt BasicProvers.VAR_EQ_TAC >> fs[] >>
      PairCases_on`res`>>fs[] >>
      PairCases_on`Cres`>>fs[] >>
      PairCases_on`r2`>>fs[] >>
      fs[v_to_Cv_def,Q.SPECL[`FEMPTY`,`CLitv (IntLit x)`]syneq_cases,i0_def] >>
      rpt BasicProvers.VAR_EQ_TAC >>
      fs[v_to_Cv_def,Q.SPECL[`FEMPTY`,`CLitv (IntLit x)`]syneq_cases,i0_def] >>
      rpt BasicProvers.VAR_EQ_TAC >>
      rpt(qpat_assum`T`kall_tac) >>
      `res0 = s3` by (
        qpat_assum`evaluate cenv s3 env X Y`mp_tac >>
        BasicProvers.CASE_TAC >>
        simp[Once evaluate_cases] ) >>
      BasicProvers.VAR_EQ_TAC >>
      qabbrev_tac`sc = store_to_Cstore m res0` >>
      `fmap_rel (syneq FEMPTY) sc r30` by
        metis_tac[fmap_rel_syneq_trans] >>
      Cases_on`opn`>>fs[]>>
      fs[v_to_Cv_def,opn_lookup_def,i0_def] >>
      Cases_on`n2=0`>>fs[v_to_Cv_def] )
    >- (
      qmatch_assum_rename_tac `do_app s3 env (Opb opb) v1 v2 = SOME (s4,env',exp'')` [] >>
      fs[] >>
      qmatch_assum_rename_tac`evaluate cenv s env e1 (s1,Rval v1)`[] >>
      qmatch_assum_rename_tac`evaluate cenv s1 env e2 (s2,Rval v2)`[] >>
      qspecl_then[`cenv`,`s`,`env`,`e1`,`(s1,Rval v1)`]mp_tac(CONJUNCT1 evaluate_closed) >>
      simp[] >> strip_tac >>
      qspecl_then[`cenv`,`s1`,`env`,`e2`,`(s2,Rval v2)`]mp_tac(CONJUNCT1 evaluate_closed) >>
      simp[] >> strip_tac >>
      fs[] >>
      Q.ISPECL_THEN[`s2`,`s4`,`env`,`Opb opb`,`v1`,`v2`,`env'`,`exp''`]mp_tac do_app_closed >>
      simp[] >> strip_tac >>
      fs[] >>
      rpt (first_x_assum (qspec_then `m` mp_tac)) >> rw[] >>
      qmatch_assum_rename_tac `syneq FEMPTY (v_to_Cv m v1) w1`[] >>
      qmatch_assum_rename_tac `syneq FEMPTY (v_to_Cv m v2) w2`[] >>
      Cases_on`Cres`>> Cases_on`Cres'`>> Cases_on`Cres''`>>fs[]>>rw[]>>
      fs[do_app_Opb_SOME]>>rw[]>>fs[v_to_Cv_def]>>rw[]>>fs[]>>rw[]>>
      fs[v_to_Cv_def]>>fs[Q.SPECL[`FEMPTY`,`CLitv l`]syneq_cases]>>rw[]>>
      fs[exp_to_Cexp_def]>>rw[]>>
      qabbrev_tac`sa = store_to_Cstore m s` >>
      qabbrev_tac`sb = store_to_Cstore m s1` >>
      qabbrev_tac`sc = store_to_Cstore m s2` >>
      fs[]>>rw[]>>
      qmatch_assum_rename_tac`fmap_rel (syneq FEMPTY) sb sd`[]>>
      qmatch_assum_rename_tac`fmap_rel (syneq FEMPTY) sc se`[]>>
      qabbrev_tac`enva = alist_to_fmap(env_to_Cenv m env)`>>
      qabbrev_tac`e1a = exp_to_Cexp m e1`>>
      qabbrev_tac`e2a = exp_to_Cexp m e2`>>
      qabbrev_tac`w1 = CLitv (IntLit n1)`>>
      qabbrev_tac`w2 = CLitv (IntLit n2)`>>
      `∀v. v ∈ FRANGE enva ⇒ Cclosed FEMPTY v` by (
        unabbrev_all_tac >>
        match_mp_tac IN_FRANGE_alist_to_fmap_suff >>
        simp[env_to_Cenv_MAP,MAP_MAP_o,combinTheory.o_DEF,MEM_MAP,EXISTS_PROD] >>
        srw_tac[DNF_ss][] >>
        match_mp_tac (CONJUNCT1 v_to_Cv_closed) >>
        fs[EVERY_MEM,EXISTS_PROD,MEM_MAP] >>
        metis_tac[] ) >>
      `∀v. v ∈ FRANGE sa ⇒ Cclosed FEMPTY v` by (
        unabbrev_all_tac >>
        simp[FRANGE_store_to_Cstore,MEM_MAP] >>
        srw_tac[DNF_ss][] >>
        match_mp_tac (CONJUNCT1 v_to_Cv_closed) >>
        fs[EVERY_MEM] ) >>
      `∀v. v ∈ FRANGE sb ⇒ Cclosed FEMPTY v` by (
        unabbrev_all_tac >>
        simp[FRANGE_store_to_Cstore,MEM_MAP] >>
        srw_tac[DNF_ss][] >>
        match_mp_tac (CONJUNCT1 v_to_Cv_closed) >>
        fs[EVERY_MEM] ) >>
      `∀v. v ∈ FRANGE sc ⇒ Cclosed FEMPTY v` by (
        unabbrev_all_tac >>
        simp[FRANGE_store_to_Cstore,MEM_MAP] >>
        srw_tac[DNF_ss][] >>
        match_mp_tac (CONJUNCT1 v_to_Cv_closed) >>
        fs[EVERY_MEM] ) >>
      `free_vars FEMPTY e1a ⊆ FDOM enva` by (
        unabbrev_all_tac >>
        fsrw_tac[DNF_ss][SUBSET_DEF,env_to_Cenv_MAP,MEM_MAP,
                         EXISTS_PROD,FORALL_PROD] ) >>
      `free_vars FEMPTY e2a ⊆ FDOM enva` by (
        unabbrev_all_tac >>
        fsrw_tac[DNF_ss][SUBSET_DEF,env_to_Cenv_MAP,MEM_MAP,
                         EXISTS_PROD,FORALL_PROD] ) >>
      qspecl_then[`FEMPTY`,`FEMPTY`,`sa`,`enva`,`e1a`,`(sd,Rval w1)`]mp_tac(CONJUNCT1 Cevaluate_closed) >>
      simp[] >> strip_tac >>
      qspecl_then[`FEMPTY`,`FEMPTY`,`sb`,`enva`,`e2a`,`(se,Rval w2)`]mp_tac(CONJUNCT1 Cevaluate_closed) >>
      simp[] >> strip_tac >>
      Cases_on `opb` >> fsrw_tac[DNF_ss][EXISTS_PROD,opb_lookup_def]
      >- (
        rw[Once Cevaluate_cases] >>
        rw[Once (CONJUNCT2 Cevaluate_cases)] >>
        rw[Once (CONJUNCT2 Cevaluate_cases)] >>
        rw[Once (CONJUNCT2 Cevaluate_cases)] >>
        srw_tac[DNF_ss][] >>
        qspecl_then[`FEMPTY`,`FEMPTY`,`sb`,`sd`,`enva`,`e2a`,`(se,Rval w2)`]mp_tac(Cevaluate_any_syneq_store) >>
        fsrw_tac[DNF_ss][EXISTS_PROD] >>
        qx_gen_tac`sf` >>
        qx_gen_tac`w3` >>
        strip_tac >>
        qexists_tac`sf`>>
        qexists_tac `w1` >>
        qexists_tac `w3` >>
        qexists_tac`sd`>>
        simp[] >>
        reverse conj_tac >- metis_tac[fmap_rel_syneq_trans] >>
        map_every qunabbrev_tac[`w1`,`w2`] >>
        fs[Q.SPECL[`FEMPTY`,`CLitv l`]syneq_cases] )
      >- (
        rw[Once Cevaluate_cases] >>
        srw_tac[DNF_ss][] >>
        CONV_TAC (RESORT_EXISTS_CONV List.rev) >>
        map_every qexists_tac [`w1`,`sd`] >> fs[] >>
        rw[Once Cevaluate_cases] >>
        srw_tac[DNF_ss][] >>
        qspecl_then[`FEMPTY`,`FEMPTY`,`sb`,`sd`,`enva`,`e2a`,`(se,Rval w2)`]mp_tac Cevaluate_any_syneq_store >>
        fsrw_tac[DNF_ss][EXISTS_PROD] >>
        qx_gen_tac`sf` >> qx_gen_tac`w3` >>
        strip_tac >>
        Q.PAT_ABBREV_TAC`fv = fresh_var X` >>
        qspecl_then[`FEMPTY`,`FEMPTY`,`sd`,`enva`,`e2a`,`(sf,Rval w3)`,`fv`,`w1`]mp_tac Cevaluate_FUPDATE >>
        `fv ∉ free_vars FEMPTY e2a` by (
          unabbrev_all_tac >>
          match_mp_tac fresh_var_not_in_any >>
          rw[] ) >>
        fsrw_tac[DNF_ss][EXISTS_PROD] >>
        qx_gen_tac`sg`>>qx_gen_tac`w4`>>
        strip_tac >>
        CONV_TAC (RESORT_EXISTS_CONV List.rev) >>
        map_every qexists_tac [`w4`,`sg`] >> fs[] >>
        rw[Once Cevaluate_cases] >>
        srw_tac[DNF_ss][] >>
        rw[Once (CONJUNCT2 Cevaluate_cases)] >>
        rw[Once (CONJUNCT2 Cevaluate_cases)] >>
        rw[Once (CONJUNCT2 Cevaluate_cases)] >>
        rw[FAPPLY_FUPDATE_THM,NOT_fresh_var] >>
        map_every qunabbrev_tac[`w1`,`w2`] >> rw[] >>
        fs[Q.SPECL[`FEMPTY`,`CLitv l`]syneq_cases] >> rw[] >>
        fs[Q.SPECL[`FEMPTY`,`CLitv l`]syneq_cases] >> rw[] >>
        rw[integerTheory.int_gt] >>
        metis_tac[fmap_rel_syneq_trans])
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
        qexists_tac`sd`>>
        qexists_tac`w2`>>
        qexists_tac`w1`>>
        qspecl_then[`FEMPTY`,`FEMPTY`,`sb`,`sd`,`enva`,`e2a`,`(se,Rval w2)`]mp_tac(Cevaluate_any_syneq_store) >>
        fsrw_tac[DNF_ss][EXISTS_PROD,Abbr`w2`,Abbr`w1`] >>
        qx_gen_tac`sf` >>
        qx_gen_tac`w3` >>
        strip_tac >>
        fs[Q.SPECL[`FEMPTY`,`CLitv l`]syneq_cases] >>
        `fmap_rel (syneq FEMPTY) sc sf` by PROVE_TAC[fmap_rel_syneq_trans] >>
        qexists_tac`sf`>>
        rw[CompileTheory.i1_def] >>
        ARITH_TAC )
      >- (
        rw[Once Cevaluate_cases] >>
        srw_tac[DNF_ss][] >>
        CONV_TAC (RESORT_EXISTS_CONV List.rev) >>
        map_every qexists_tac [`w1`,`sd`] >> fs[] >>
        rw[Once Cevaluate_cases] >>
        srw_tac[DNF_ss][] >>
        qspecl_then[`FEMPTY`,`FEMPTY`,`sb`,`sd`,`enva`,`e2a`,`(se,Rval w2)`]mp_tac Cevaluate_any_syneq_store >>
        fsrw_tac[DNF_ss][EXISTS_PROD] >>
        qx_gen_tac`sf` >> qx_gen_tac`w3` >>
        strip_tac >>
        Q.PAT_ABBREV_TAC`fv = fresh_var X` >>
        qspecl_then[`FEMPTY`,`FEMPTY`,`sd`,`enva`,`e2a`,`(sf,Rval w3)`,`fv`,`w1`]mp_tac Cevaluate_FUPDATE >>
        `fv ∉ free_vars FEMPTY e2a` by (
          unabbrev_all_tac >>
          match_mp_tac fresh_var_not_in_any >>
          rw[] ) >>
        fsrw_tac[DNF_ss][EXISTS_PROD] >>
        qx_gen_tac`sg`>>qx_gen_tac`w4`>>
        strip_tac >>
        CONV_TAC (RESORT_EXISTS_CONV List.rev) >>
        map_every qexists_tac [`w4`,`sg`] >> fs[] >>
        rw[Once Cevaluate_cases] >>
        srw_tac[DNF_ss][] >>
        rw[Once (CONJUNCT2 Cevaluate_cases)] >>
        rw[Once (CONJUNCT2 Cevaluate_cases)] >>
        rw[Once (CONJUNCT2 Cevaluate_cases)] >>
        rw[FAPPLY_FUPDATE_THM,NOT_fresh_var] >>
        rw[Once Cevaluate_cases] >>
        rw[Once (CONJUNCT2 Cevaluate_cases)] >>
        rw[Once (CONJUNCT2 Cevaluate_cases)] >>
        rw[Once (CONJUNCT2 Cevaluate_cases)] >>
        srw_tac[DNF_ss][] >>
        rw[FAPPLY_FUPDATE_THM,NOT_fresh_var] >>
        map_every qunabbrev_tac[`w1`,`w2`] >> rw[] >>
        fs[Q.SPECL[`FEMPTY`,`CLitv l`]syneq_cases] >> rw[] >>
        `fmap_rel (syneq FEMPTY) sc sg` by PROVE_TAC[fmap_rel_syneq_trans] >>
        fs[Q.SPECL[`FEMPTY`,`CLitv l`]syneq_cases] >> rw[] >>
        rw[CompileTheory.i1_def] >>
        ARITH_TAC) )
    >- (
      rw[Once Cevaluate_cases] >>
      srw_tac[DNF_ss][] >>
      disj1_tac >>
      rw[Once(CONJUNCT2 Cevaluate_cases)] >>
      rw[Once(CONJUNCT2 Cevaluate_cases)] >>
      rw[Once(CONJUNCT2 Cevaluate_cases)] >>
      srw_tac[DNF_ss][] >>
      fs[] >>
      qspecl_then[`cenv`,`s`,`env`,`e1`,`(s',Rval v1)`]mp_tac(CONJUNCT1 evaluate_closed) >>
      simp[]>>strip_tac >>
      qspecl_then[`cenv`,`s'`,`env`,`e2`,`(s3,Rval v2)`]mp_tac(CONJUNCT1 evaluate_closed) >>
      simp[]>>strip_tac >>
      Q.ISPECL_THEN[`s3`,`s''`,`env`,`Equality`,`v1`,`v2`,`env'`,`exp''`]mp_tac do_app_closed >>
      simp[]>>strip_tac>>
      fs[] >>
      rpt (first_x_assum (qspec_then `m` mp_tac)) >>
      rw[EXISTS_PROD] >>
      qmatch_assum_rename_tac `syneq FEMPTY(v_to_Cv m v1) w1`[] >>
      qmatch_assum_rename_tac `syneq FEMPTY(v_to_Cv m v2) w2`[] >>
      qabbrev_tac`sa = store_to_Cstore m s` >>
      qabbrev_tac`sb = store_to_Cstore m s'` >>
      qabbrev_tac`sc = store_to_Cstore m s3` >>
      qmatch_assum_abbrev_tac`Cevaluate FEMPTY FEMPTY sa enva e1a X` >>
      qmatch_assum_rename_tac`Abbrev(X=(sd,Rval w1))`[]>>
      qunabbrev_tac`X` >>
      qmatch_assum_abbrev_tac`Cevaluate FEMPTY FEMPTY sb enva e2a X` >>
      qmatch_assum_rename_tac`Abbrev(X=(se,Rval w2))`[]>>
      qspecl_then[`FEMPTY`,`FEMPTY`,`sb`,`sd`,`enva`,`e2a`,`X`]mp_tac Cevaluate_any_syneq_store >>
      `∀v. v ∈ FRANGE enva ⇒ Cclosed FEMPTY v` by (
        unabbrev_all_tac >>
        match_mp_tac IN_FRANGE_alist_to_fmap_suff >>
        simp[env_to_Cenv_MAP,MAP_MAP_o,combinTheory.o_DEF,MEM_MAP,EXISTS_PROD] >>
        srw_tac[DNF_ss][] >>
        match_mp_tac (CONJUNCT1 v_to_Cv_closed) >>
        fs[EVERY_MEM,EXISTS_PROD,MEM_MAP] >>
        metis_tac[] ) >>
      `free_vars FEMPTY e1a ⊆ FDOM enva` by (
        unabbrev_all_tac >>
        fsrw_tac[DNF_ss][SUBSET_DEF,env_to_Cenv_MAP,MEM_MAP,
                         EXISTS_PROD,FORALL_PROD] ) >>
      `free_vars FEMPTY e2a ⊆ FDOM enva` by (
        unabbrev_all_tac >>
        fsrw_tac[DNF_ss][SUBSET_DEF,env_to_Cenv_MAP,MEM_MAP,
                         EXISTS_PROD,FORALL_PROD] ) >>
      `∀v. v ∈ FRANGE sa ⇒ Cclosed FEMPTY v` by (
        unabbrev_all_tac >>
        simp[FRANGE_store_to_Cstore,MEM_MAP] >>
        srw_tac[DNF_ss][] >>
        match_mp_tac (CONJUNCT1 v_to_Cv_closed) >>
        fs[EVERY_MEM] ) >>
      `∀v. v ∈ FRANGE sb ⇒ Cclosed FEMPTY v` by (
        unabbrev_all_tac >>
        simp[FRANGE_store_to_Cstore,MEM_MAP] >>
        srw_tac[DNF_ss][] >>
        match_mp_tac (CONJUNCT1 v_to_Cv_closed) >>
        fs[EVERY_MEM] ) >>
      qspecl_then[`FEMPTY`,`FEMPTY`,`sa`,`enva`,`e1a`,`(sd,Rval w1)`]mp_tac(CONJUNCT1 Cevaluate_closed) >>
      simp[] >> strip_tac >>
      qspecl_then[`FEMPTY`,`FEMPTY`,`sb`,`enva`,`e2a`,`X`]mp_tac(CONJUNCT1 Cevaluate_closed) >>
      simp[Abbr`X`] >> strip_tac >>
      fsrw_tac[DNF_ss][EXISTS_PROD,FORALL_PROD] >>
      map_every qx_gen_tac[`sf`,`w3`] >>
      strip_tac >>
      map_every qexists_tac[`sf`,`w1`,`w3`,`sd`] >>
      simp[] >>
      fs[do_app_def] >>
      rpt BasicProvers.VAR_EQ_TAC >>
      fs[] >>
      rpt BasicProvers.VAR_EQ_TAC >>
      fs[v_to_Cv_def,Q.SPECL[`c`,`CLitv l`]syneq_cases] >>
      fs[exp_to_Cexp_def] >>
      `fmap_rel (syneq FEMPTY) sc sf` by PROVE_TAC[fmap_rel_syneq_trans] >>
      cheat )
    >- (
      rw[Once Cevaluate_cases] >>
      srw_tac[DNF_ss][] >>
      disj1_tac >>
      rw[Once(CONJUNCT2 Cevaluate_cases)]>>
      rw[Once(CONJUNCT2 Cevaluate_cases)]>>
      fsrw_tac[DNF_ss][] >>
      qspecl_then[`cenv`,`s`,`env`,`e1`,`(s',Rval v1)`]mp_tac(CONJUNCT1 evaluate_closed) >>
      simp[] >> strip_tac >>
      qspecl_then[`cenv`,`s'`,`env`,`e2`,`(s3,Rval v2)`]mp_tac(CONJUNCT1 evaluate_closed) >>
      simp[] >> strip_tac >>
      Q.ISPECL_THEN[`s3`,`s''`,`env`,`Opapp`,`v1`,`v2`,`env'`,`exp''`]mp_tac do_app_closed >>
      simp[] >> strip_tac >>
      fs[] >>
      rpt (first_x_assum (qspec_then `m` mp_tac)) >>
      srw_tac[DNF_ss][EXISTS_PROD] >>
      qmatch_assum_rename_tac `syneq FEMPTY(v_to_Cv m v1) w1`[] >>
      qmatch_assum_rename_tac `syneq FEMPTY(v_to_Cv m v2) w2`[] >>
      qmatch_assum_abbrev_tac`Cevaluate FEMPTY FEMPTY sa enva e1a (sd,Rval w1)`>>
      pop_assum kall_tac >>
      qmatch_assum_abbrev_tac`Cevaluate FEMPTY FEMPTY sb enva e2a (se,Rval w2)`>>
      pop_assum kall_tac >>
      qmatch_assum_abbrev_tac`fmap_rel (syneq FEMPTY) sc se` >>
      qspecl_then[`FEMPTY`,`FEMPTY`,`sb`,`sd`,`enva`,`e2a`,`(se,Rval w2)`]mp_tac Cevaluate_any_syneq_store >>
      `∀v. v ∈ FRANGE enva ⇒ Cclosed FEMPTY v` by (
        unabbrev_all_tac >>
        match_mp_tac IN_FRANGE_alist_to_fmap_suff >>
        simp[env_to_Cenv_MAP,MAP_MAP_o,combinTheory.o_DEF,MEM_MAP,EXISTS_PROD] >>
        srw_tac[DNF_ss][] >>
        match_mp_tac (CONJUNCT1 v_to_Cv_closed) >>
        fs[EVERY_MEM,EXISTS_PROD,MEM_MAP] >>
        metis_tac[] ) >>
      `free_vars FEMPTY e1a ⊆ FDOM enva` by (
        unabbrev_all_tac >>
        fsrw_tac[DNF_ss][SUBSET_DEF,env_to_Cenv_MAP,MEM_MAP,
                         EXISTS_PROD,FORALL_PROD] ) >>
      `free_vars FEMPTY e2a ⊆ FDOM enva` by (
        unabbrev_all_tac >>
        fsrw_tac[DNF_ss][SUBSET_DEF,env_to_Cenv_MAP,MEM_MAP,
                         EXISTS_PROD,FORALL_PROD] ) >>
      `∀v. v ∈ FRANGE sa ⇒ Cclosed FEMPTY v` by (
        unabbrev_all_tac >>
        simp[FRANGE_store_to_Cstore,MEM_MAP] >>
        srw_tac[DNF_ss][] >>
        match_mp_tac (CONJUNCT1 v_to_Cv_closed) >>
        fs[EVERY_MEM] ) >>
      `∀v. v ∈ FRANGE sb ⇒ Cclosed FEMPTY v` by (
        unabbrev_all_tac >>
        simp[FRANGE_store_to_Cstore,MEM_MAP] >>
        srw_tac[DNF_ss][] >>
        match_mp_tac (CONJUNCT1 v_to_Cv_closed) >>
        fs[EVERY_MEM] ) >>
      qspecl_then[`FEMPTY`,`FEMPTY`,`sa`,`enva`,`e1a`,`(sd,Rval w1)`]mp_tac(CONJUNCT1 Cevaluate_closed) >>
      simp[] >> strip_tac >>
      fsrw_tac[DNF_ss][EXISTS_PROD,FORALL_PROD] >>
      map_every qx_gen_tac[`sf`,`w3`] >>
      strip_tac >>
      CONV_TAC (RESORT_EXISTS_CONV List.rev) >>
      qexists_tac`w3` >>
      qexists_tac`sf` >>
      `∃env1 ns' defs n. w1 = CRecClos env1 ns' defs n` by (
        imp_res_tac do_Opapp_SOME_CRecClos >> rw[] ) >>
      CONV_TAC (RESORT_EXISTS_CONV (fn ls => List.drop(ls,4)@List.take(ls,4))) >>
      map_every qexists_tac[`n`,`defs`,`ns'`,`env1`,`sd`] >>
      rw[] >>
      fs[Q.SPECL[`FEMPTY`,`CRecClos env1 ns' defs n`]Cclosed_cases] >>
      fs[MEM_EL] >> rw[] >>
      fs[do_app_Opapp_SOME] >- (
        rw[] >> fs[v_to_Cv_def,LET_THM] >>
        fs[Q.SPECL[`c`,`CRecClos env1 ns' defs zz`]syneq_cases] >>
        rw[] >> fs[] >>
        Q.PAT_ABBREV_TAC`env2 = X:string|->Cv` >>
        qmatch_assum_abbrev_tac`Cevaluate FEMPTY FEMPTY sc env3 e3a (sg,r)` >>
        ntac 2 (pop_assum kall_tac) >>
        `fmap_rel (syneq FEMPTY) sc sf` by PROVE_TAC[fmap_rel_syneq_trans] >>
        qspecl_then[`FEMPTY`,`FEMPTY`,`sc`,`sf`,`env3`,`e3a`,`(sg,r)`]mp_tac Cevaluate_any_syneq_store >>
        `free_vars FEMPTY e3a ⊆ FDOM env3` by(
          unabbrev_all_tac >> fs[] >>
          rw[env_to_Cenv_MAP,MAP_MAP_o] >>
          rw[combinTheory.o_DEF,pairTheory.LAMBDA_PROD,FST_pair,FST_triple] ) >>
        `∀v. v ∈ FRANGE env3 ⇒ Cclosed FEMPTY v` by(
          unabbrev_all_tac >>
          fs[env_to_Cenv_MAP] >>
          match_mp_tac IN_FRANGE_alist_to_fmap_suff >>
          fs[MAP_MAP_o,combinTheory.o_DEF,pairTheory.LAMBDA_PROD] >>
          rw[bind_def,MEM_MAP,pairTheory.EXISTS_PROD] >>
          match_mp_tac (CONJUNCT1 v_to_Cv_closed) >>
          fs[EVERY_MEM,bind_def,MEM_MAP,pairTheory.EXISTS_PROD] >>
          PROVE_TAC[]) >>
        qspecl_then[`FEMPTY`,`FEMPTY`,`sd`,`enva`,`e2a`,`(sf,Rval w3)`]mp_tac(CONJUNCT1 Cevaluate_closed) >>
        `∀v. v ∈ FRANGE sc ⇒ Cclosed FEMPTY v` by (
          unabbrev_all_tac >>
          simp[FRANGE_store_to_Cstore,MEM_MAP] >>
          fsrw_tac[DNF_ss][EVERY_MEM] >>
          PROVE_TAC[v_to_Cv_closed] ) >>
        simp[] >> strip_tac >>
        fsrw_tac[DNF_ss][EXISTS_PROD,FORALL_PROD] >>
        map_every qx_gen_tac[`sh`,`w4`]>>strip_tac>>
        qspecl_then[`FEMPTY`,`FEMPTY`,`sf`,`env3`,`e3a`,`(sh,w4)`]mp_tac Cevaluate_free_vars_env >>
        fsrw_tac[DNF_ss][FORALL_PROD] >>
        map_every qx_gen_tac[`si`,`w5`]>>strip_tac>>
        `free_vars FEMPTY e3a ⊆ FDOM env2` by (
          unabbrev_all_tac >> fs[] ) >>
        `fmap_rel (syneq FEMPTY)
           (DRESTRICT env3 (free_vars FEMPTY e3a))
           (DRESTRICT env2 (free_vars FEMPTY e3a))` by(
          rw[fmap_rel_def,FDOM_DRESTRICT] >-
            fs[SUBSET_INTER_ABSORPTION,INTER_COMM] >>
          `x ∈ FDOM env2` by fs[SUBSET_DEF] >>
          rw[DRESTRICT_DEF] >>
          qunabbrev_tac `env3` >>
          qmatch_abbrev_tac `syneq FEMPTY (alist_to_fmap al ' x) (env2 ' x)` >>
          `∃v. ALOOKUP al x = SOME v` by (
            Cases_on `ALOOKUP al x` >> fs[] >>
            imp_res_tac ALOOKUP_FAILS >>
            unabbrev_all_tac >>
            fs[MEM_MAP,pairTheory.EXISTS_PROD] ) >>
          imp_res_tac ALOOKUP_SOME_FAPPLY_alist_to_fmap >>
          pop_assum(SUBST1_TAC) >>
          fs[Abbr`al`,env_to_Cenv_MAP,ALOOKUP_MAP] >>
          fs[bind_def] >- (
            rw[Abbr`env2`] >>
            rw[extend_rec_env_def] >>
            PROVE_TAC[syneq_trans]) >>
          rw[Abbr`env2`,extend_rec_env_def] >>
          simp[FAPPLY_FUPDATE_THM] >>
          Cases_on`n'=x` >- (
            rw[] >> PROVE_TAC[syneq_trans] ) >>
          simp[] >>
          rw[] >- (
            fs[Abbr`e3a`,NOT_fresh_var] >>
            fs[FLOOKUP_DEF,optionTheory.OPTREL_def] >>
            fsrw_tac[DNF_ss][] >>
            metis_tac[NOT_fresh_var,FINITE_FV,optionTheory.SOME_11]) >>
          fs[Abbr`e3a`] >>
          fs[FLOOKUP_DEF,optionTheory.OPTREL_def] >>
          fsrw_tac[DNF_ss][] >>
          metis_tac[NOT_fresh_var,FINITE_FV,optionTheory.SOME_11]) >>
        qspecl_then[`FEMPTY`,`FEMPTY`,`sf`,
          `DRESTRICT env3 (free_vars FEMPTY e3a)`,
          `DRESTRICT env2 (free_vars FEMPTY e3a)`,
          `e3a`,`(si,w5)`]mp_tac Cevaluate_any_syneq_env >>
        simp[FDOM_DRESTRICT] >>
        `∀v. v ∈ FRANGE env2 ⇒ Cclosed FEMPTY v` by (
          unabbrev_all_tac >>
          simp[extend_rec_env_def] >>
          fsrw_tac[DNF_ss][] >>
          match_mp_tac IN_FRANGE_DOMSUB_suff >> simp[] >>
          match_mp_tac IN_FRANGE_FUPDATE_suff >> simp[] >>
          rw[Once Cclosed_cases] ) >>
        qmatch_abbrev_tac`(P ⇒ Q) ⇒ R` >>
        `P` by (
          map_every qunabbrev_tac[`P`,`Q`,`R`] >>
          conj_tac >> match_mp_tac IN_FRANGE_DRESTRICT_suff >>
          simp[] ) >>
        simp[] >>
        map_every qunabbrev_tac[`P`,`Q`,`R`] >>
        pop_assum kall_tac >>
        fsrw_tac[DNF_ss][FORALL_PROD] >>
        map_every qx_gen_tac [`sj`,`w6`] >>
        strip_tac >>
        qspecl_then[`FEMPTY`,`FEMPTY`,`sf`,`env2`,`e3a`,`(sj,w6)`]mp_tac Cevaluate_any_super_env >>
        fsrw_tac[DNF_ss][EXISTS_PROD] >>
        map_every qx_gen_tac [`sk`,`w7`] >>
        strip_tac >>
        map_every qexists_tac[`w7`,`sk`] >>
        simp[] >>
        PROVE_TAC[fmap_rel_syneq_trans,result_rel_syneq_trans] ) >>
      rw[] >>
      fs[v_to_Cv_def,LET_THM,defs_to_Cdefs_MAP] >>
      fs[Q.SPECL[`c`,`CRecClos env1 ns' defs X`]syneq_cases] >>
      rw[] >> fs[] >> rw[] >> rfs[] >> rw[] >>
      PairCases_on`z`>>fs[]>>rw[]>>
      qpat_assum `X < LENGTH Y` assume_tac >>
      fs[EL_MAP] >>
      qmatch_assum_rename_tac `ALL_DISTINCT (MAP FST ns)`[] >>
      qabbrev_tac`q = EL n' ns` >>
      PairCases_on `q` >>
      pop_assum (mp_tac o SYM o SIMP_RULE std_ss [markerTheory.Abbrev_def]) >> rw[] >>
      fs[] >> rw[] >>
      `ALOOKUP ns q0 = SOME (q1,q2,q3,q4)` by (
        match_mp_tac ALOOKUP_ALL_DISTINCT_MEM >>
        rw[MEM_EL] >> PROVE_TAC[] ) >>
      fs[] >> rw[] >>
      qmatch_assum_abbrev_tac`Cevaluate FEMPTY FEMPTY sc env3 ee r` >>
      qmatch_assum_rename_tac`Abbrev(r=(sg,w4))`[]>>
      qmatch_assum_rename_tac`EL n' ns = (q0,q1,q2,q3,q4)`[]>>
      Q.PAT_ABBREV_TAC`env2 = X:string|->Cv` >>
      qmatch_assum_abbrev_tac `result_rel (syneq FEMPTY) rr w4` >>
      fs[Q.SPEC`Recclosure l ns q0`closed_cases] >>
      `free_vars FEMPTY ee ⊆ FDOM env2` by (
        first_x_assum (qspecl_then [`n'`,`[q2]`,`INL ee`] mp_tac) >>
        unabbrev_all_tac >> fs[] >>
        rw[EL_MAP] ) >>
      qspecl_then[`FEMPTY`,`FEMPTY`,`sd`,`enva`,`e2a`,`(sf,Rval w3)`]mp_tac(CONJUNCT1 Cevaluate_closed) >>
      simp[] >> strip_tac >>
      `∀v. v ∈ FRANGE env2 ⇒ Cclosed FEMPTY v` by (
        unabbrev_all_tac >> fs[] >>
        fs[extend_rec_env_def] >>
        qx_gen_tac `v` >>
        Cases_on `v=w3` >> fs[] >>
        match_mp_tac IN_FRANGE_DOMSUB_suff >>
        fs[FOLDL_FUPDATE_LIST] >>
        match_mp_tac IN_FRANGE_FUPDATE_LIST_suff >> fs[] >>
        fs[MAP_MAP_o,MEM_MAP,pairTheory.EXISTS_PROD] >>
        fsrw_tac[DNF_ss][] >>
        rw[Once Cclosed_cases,MEM_MAP,pairTheory.EXISTS_PROD]
          >- PROVE_TAC[]
          >- ( first_x_assum match_mp_tac >>
               PROVE_TAC[] ) >>
        Cases_on `cb` >> fs[] >>
        pop_assum mp_tac >>
        fs[EL_MAP,pairTheory.UNCURRY]) >>
      `fmap_rel (syneq FEMPTY) sc sf` by metis_tac[fmap_rel_syneq_trans] >>
      `∀v. v ∈ FRANGE env3 ⇒ Cclosed FEMPTY v` by (
        unabbrev_all_tac >>
        match_mp_tac IN_FRANGE_alist_to_fmap_suff >>
        simp[env_to_Cenv_MAP,build_rec_env_MAP,MAP_MAP_o,bind_def,MEM_MAP,EXISTS_PROD] >>
        fsrw_tac[DNF_ss][] >>
        conj_tac >- (
          match_mp_tac (CONJUNCT1 v_to_Cv_closed) >> rw[] ) >>
        conj_tac >- (
          rpt gen_tac >> strip_tac >>
          match_mp_tac (CONJUNCT1 v_to_Cv_closed) >>
          rw[Once closed_cases,MEM_MAP,EXISTS_PROD] >>
          metis_tac[] ) >>
        rpt gen_tac >> strip_tac >>
        match_mp_tac (CONJUNCT1 v_to_Cv_closed) >>
        fs[EVERY_MEM,build_rec_env_MAP,MEM_MAP,EXISTS_PROD,bind_def] >>
        metis_tac[] ) >>
      `free_vars FEMPTY ee ⊆ FDOM env3` by (
        unabbrev_all_tac >> fs[] >>
        rw[env_to_Cenv_MAP,MAP_MAP_o] >>
        rw[combinTheory.o_DEF,pairTheory.LAMBDA_PROD,FST_pair,FST_triple] ) >>
      `∀v. v ∈ FRANGE sc ⇒ Cclosed FEMPTY v` by (
        unabbrev_all_tac >>
        simp[FRANGE_store_to_Cstore,MEM_MAP] >>
        fsrw_tac[DNF_ss][FORALL_PROD] >> rw[] >>
        fs[EVERY_MEM] >>
        match_mp_tac (CONJUNCT1 v_to_Cv_closed) >>
        PROVE_TAC[] ) >>
      qspecl_then[`FEMPTY`,`FEMPTY`,`sc`,`sf`,`env3`,`ee`,`r`]mp_tac Cevaluate_any_syneq_store >>
      fsrw_tac[DNF_ss][FORALL_PROD,Abbr`r`] >>
      `fmap_rel (syneq FEMPTY)
         (DRESTRICT env3 (free_vars FEMPTY ee))
         (DRESTRICT env2 (free_vars FEMPTY ee))` by (
        rw[fmap_rel_def,FDOM_DRESTRICT] >-
          fs[SUBSET_INTER_ABSORPTION,INTER_COMM] >>
        `x ∈ FDOM env2` by fs[SUBSET_DEF] >>
        rw[DRESTRICT_DEF] >>
        qunabbrev_tac `env3` >>
        qmatch_abbrev_tac `syneq FEMPTY (alist_to_fmap al ' x) (env2 ' x)` >>
        `∃v. ALOOKUP al x = SOME v` by (
          Cases_on `ALOOKUP al x` >> fs[] >>
          imp_res_tac ALOOKUP_FAILS >>
          unabbrev_all_tac >>
          fs[MEM_MAP,pairTheory.EXISTS_PROD] ) >>
        imp_res_tac ALOOKUP_SOME_FAPPLY_alist_to_fmap >>
        qpat_assum `alist_to_fmap al ' x = X`(SUBST1_TAC) >>
        fs[Abbr`al`,env_to_Cenv_MAP,ALOOKUP_MAP] >> rw[] >>
        fs[bind_def] >- (
          rw[Abbr`env2`] >>
          rw[extend_rec_env_def] >>
          PROVE_TAC[syneq_trans]) >>
        Cases_on `q2=x`>>fs[] >- (
          rw[] >>
          rw[Abbr`env2`,extend_rec_env_def] >>
          PROVE_TAC[syneq_trans]) >>
        qpat_assum `ALOOKUP X Y = SOME Z` mp_tac >>
        asm_simp_tac(srw_ss())[build_rec_env_def,bind_def,FOLDR_CONS_5tup] >>
        rw[ALOOKUP_APPEND] >>
        Cases_on `MEM x (MAP FST ns)` >>
        fs[MAP_MAP_o,combinTheory.o_DEF,pairTheory.LAMBDA_PROD,FST_pair,FST_triple] >- (
          qpat_assum `X = SOME v'` mp_tac >>
          qho_match_abbrev_tac `((case ALOOKUP (MAP ff ns) x of
            NONE => ALOOKUP (MAP fg env'') x | SOME v => SOME v) = SOME v') ⇒ P` >>
          `MAP FST (MAP ff ns) = MAP FST ns` by (
            asm_simp_tac(srw_ss())[LIST_EQ_REWRITE,Abbr`ff`] >>
            qx_gen_tac `y` >> strip_tac >>
            fs[MAP_MAP_o,combinTheory.o_DEF,EL_MAP] >>
            qabbrev_tac `yy = EL y ns` >>
            PairCases_on `yy` >> fs[] ) >>
          `ALL_DISTINCT (MAP FST (MAP ff ns))` by PROVE_TAC[] >>
          `MEM (x,v_to_Cv m (Recclosure env'' ns x)) (MAP ff ns)` by (
            rw[Abbr`ff`,MEM_MAP,pairTheory.EXISTS_PROD] >>
            fs[MEM_MAP,pairTheory.EXISTS_PROD,MAP_MAP_o,combinTheory.o_DEF,UNCURRY] >>
            PROVE_TAC[] ) >>
          imp_res_tac ALOOKUP_ALL_DISTINCT_MEM >>
          fs[] >> rw[Abbr`P`] >>
          rw[v_to_Cv_def] >>
          rw[Abbr`env2`,extend_rec_env_def,FOLDL_FUPDATE_LIST] >>
          rw[FAPPLY_FUPDATE_THM] >>
          ho_match_mp_tac FUPDATE_LIST_ALL_DISTINCT_APPLY_MEM >>
          fs[MAP_MAP_o,combinTheory.o_DEF] >>
          fsrw_tac[ETA_ss][] >>
          fs[pairTheory.LAMBDA_PROD] >>
          fsrw_tac[DNF_ss][MEM_MAP,pairTheory.EXISTS_PROD] >>
          rw[Once syneq_cases] >>
          fs[defs_to_Cdefs_MAP] >>
          qmatch_assum_rename_tac `MEM (x,z0,z1,z2,z3) ns`[] >>
          map_every qexists_tac [`z0`,`z1`,`z2`,`z3`] >> fs[] >>
          rw[] >>
          fs[EVERY_MEM,pairTheory.FORALL_PROD] >>
          fs[MEM_MAP,pairTheory.EXISTS_PROD] >>
          fsrw_tac[DNF_ss][] >>
          fs[env_to_Cenv_MAP,ALOOKUP_MAP] >>
          fsrw_tac[ETA_ss][] >>
          fs[Abbr`Cenv`] >>
          fs[ALOOKUP_MAP] >>
          fsrw_tac[ETA_ss][] >>
          metis_tac[]) >>
        qpat_assum `X = SOME v'` mp_tac >>
        qho_match_abbrev_tac `((case ALOOKUP (MAP ff ns) x of
          NONE => ALOOKUP (MAP fg env'') x | SOME v => SOME v) = SOME v') ⇒ P` >>
        `MAP FST (MAP ff ns) = MAP FST ns` by (
          asm_simp_tac(srw_ss())[LIST_EQ_REWRITE,Abbr`ff`] >>
          qx_gen_tac `y` >> strip_tac >>
          fs[MAP_MAP_o,combinTheory.o_DEF,EL_MAP] >>
          qabbrev_tac `yy = EL y ns` >>
          PairCases_on `yy` >> fs[] ) >>
        `ALOOKUP (MAP ff ns) x= NONE` by (
          rw[ALOOKUP_NONE]) >>
        rw[Abbr`P`] >>
        rw[Abbr`env2`] >>
        rw[extend_rec_env_def,FOLDL_FUPDATE_LIST] >>
        rw[FAPPLY_FUPDATE_THM] >>
        ho_match_mp_tac FUPDATE_LIST_APPLY_HO_THM >>
        disj2_tac >>
        fs[MAP_MAP_o,combinTheory.o_DEF] >>
        fsrw_tac[ETA_ss][] >>
        fsrw_tac[DNF_ss][EVERY_MEM,pairTheory.FORALL_PROD] >>
        fsrw_tac[DNF_ss][optionTheory.OPTREL_def,FLOOKUP_DEF] >>
        fsrw_tac[DNF_ss][MEM_MAP,pairTheory.EXISTS_PROD] >>
        fs[Abbr`ee`] >>
        imp_res_tac ALOOKUP_MEM >>
        metis_tac[NOT_fresh_var,FINITE_FV,optionTheory.SOME_11] ) >>
      map_every qx_gen_tac[`sh`,`w5`] >> strip_tac >>
      qspecl_then [`FEMPTY`,`FEMPTY`,`sf`,`env3`,`ee`,`(sh,w5)`] mp_tac Cevaluate_free_vars_env >>
      simp[] >>
      fsrw_tac[DNF_ss][FORALL_PROD] >>
      map_every qx_gen_tac[`si`,`w6`] >> strip_tac >>
      qspecl_then[`FEMPTY`,`FEMPTY`,`sf`,
        `DRESTRICT env3 (free_vars FEMPTY ee)`,
        `DRESTRICT env2 (free_vars FEMPTY ee)`,
        `ee`,`(si,w6)`]mp_tac Cevaluate_any_syneq_env >>
      simp[FDOM_DRESTRICT] >>
      qmatch_abbrev_tac`(P ⇒ Q) ⇒ R` >>
      `P` by (
        map_every qunabbrev_tac[`P`,`Q`,`R`] >>
        conj_tac >> match_mp_tac IN_FRANGE_DRESTRICT_suff >>
        simp[] ) >>
      simp[] >>
      map_every qunabbrev_tac[`P`,`Q`,`R`] >>
      pop_assum kall_tac >>
      fsrw_tac[DNF_ss][FORALL_PROD] >>
      map_every qx_gen_tac [`sj`,`w7`] >>
      strip_tac >>
      qspecl_then[`FEMPTY`,`FEMPTY`,`sf`,`env2`,`ee`,`(sj,w7)`]mp_tac Cevaluate_any_super_env >>
      fsrw_tac[DNF_ss][EXISTS_PROD] >>
      map_every qx_gen_tac [`sk`,`w8`] >>
      strip_tac >>
      map_every qexists_tac[`w8`,`sk`] >>
      simp[] >>
      PROVE_TAC[fmap_rel_syneq_trans,result_rel_syneq_trans] )
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
      qspecl_then[`cenv`,`s`,`env`,`e1`,`(s',Rval (Loc n))`]mp_tac(CONJUNCT1 evaluate_closed) >>
      simp[]>>strip_tac >> fs[] >>
      fs[store_assign_def] >> rw[] >> fs[] >> rw[] >>
      qspecl_then[`cenv`,`s'`,`env`,`e2`,`(s3,Rval v2)`]mp_tac(CONJUNCT1 evaluate_closed) >>
      simp[]>>strip_tac >>
      `EVERY closed (LUPDATE v2 n s3)` by (
        fs[EVERY_MEM] >>
        metis_tac[MEM_LUPDATE] ) >>
      fs[] >>
      rpt (first_x_assum (qspec_then`m`mp_tac)) >>
      fsrw_tac[DNF_ss][EXISTS_PROD] >> rw[] >>
      fs[v_to_Cv_def,exp_to_Cexp_def] >>
      rw[] >> fs[] >> rw[] >>
      fs[Q.SPECL[`FEMPTY`,`CLoc n`]syneq_cases] >> rw[] >>
      CONV_TAC SWAP_EXISTS_CONV >> qexists_tac`CLoc n` >> rw[] >>
      qmatch_assum_abbrev_tac`Cevaluate FEMPTY FEMPTY sa enva e1a (sd,Rval (CLoc n))` >>
      pop_assum kall_tac >>
      qmatch_assum_abbrev_tac`Cevaluate FEMPTY FEMPTY sb enva e2a (se,w1)` >>
      qpat_assum`Abbrev (se  = X)`kall_tac >>
      qspecl_then[`FEMPTY`,`FEMPTY`,`sb`,`sd`,`enva`,`e2a`,`(se,w1)`]mp_tac Cevaluate_any_syneq_store >>
      `∀v. v ∈ FRANGE enva ⇒ Cclosed FEMPTY v` by (
        unabbrev_all_tac >>
        match_mp_tac IN_FRANGE_alist_to_fmap_suff >>
        simp[env_to_Cenv_MAP,MAP_MAP_o,combinTheory.o_DEF,MEM_MAP,EXISTS_PROD] >>
        srw_tac[DNF_ss][] >>
        match_mp_tac (CONJUNCT1 v_to_Cv_closed) >>
        fs[EVERY_MEM,EXISTS_PROD,MEM_MAP] >>
        metis_tac[] ) >>
      `free_vars FEMPTY e1a ⊆ FDOM enva` by (
        unabbrev_all_tac >>
        fsrw_tac[DNF_ss][SUBSET_DEF,env_to_Cenv_MAP,MEM_MAP,
                         EXISTS_PROD,FORALL_PROD] ) >>
      `free_vars FEMPTY e2a ⊆ FDOM enva` by (
        unabbrev_all_tac >>
        fsrw_tac[DNF_ss][SUBSET_DEF,env_to_Cenv_MAP,MEM_MAP,
                         EXISTS_PROD,FORALL_PROD] ) >>
      `∀v. v ∈ FRANGE sa ⇒ Cclosed FEMPTY v` by (
        unabbrev_all_tac >>
        simp[FRANGE_store_to_Cstore,MEM_MAP] >>
        srw_tac[DNF_ss][] >>
        match_mp_tac (CONJUNCT1 v_to_Cv_closed) >>
        fs[EVERY_MEM] ) >>
      `∀v. v ∈ FRANGE sb ⇒ Cclosed FEMPTY v` by (
        unabbrev_all_tac >>
        simp[FRANGE_store_to_Cstore,MEM_MAP] >>
        srw_tac[DNF_ss][] >>
        match_mp_tac (CONJUNCT1 v_to_Cv_closed) >>
        fs[EVERY_MEM] ) >>
      qspecl_then[`FEMPTY`,`FEMPTY`,`sa`,`enva`,`e1a`,`(sd,Rval (CLoc n))`]mp_tac(CONJUNCT1 Cevaluate_closed) >>
      simp[] >> strip_tac >>
      fsrw_tac[DNF_ss][FORALL_PROD] >>
      map_every qx_gen_tac[`sf`,`w2`] >>
      strip_tac >>
      fs[Abbr`w1`] >> rw[] >>
      qmatch_assum_rename_tac`syneq FEMPTY w1 w2`[] >>
      map_every qexists_tac[`sf`,`w2`,`sd`] >>
      simp[] >>
      fs[fmap_rel_def] >>
      conj_tac >- (rw[EXTENSION] >> PROVE_TAC[]) >>
      rw[FAPPLY_FUPDATE_THM,FAPPLY_store_to_Cstore,EL_LUPDATE] >-
        PROVE_TAC[syneq_trans] >>
      fs[FAPPLY_store_to_Cstore,EXTENSION] >>
      PROVE_TAC[syneq_trans])) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    ntac 2 gen_tac >>
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
      qspecl_then[`cenv`,`s`,`env`,`e1`,`(s',Rval v1)`]mp_tac(CONJUNCT1 evaluate_closed) >>
      simp[] >> strip_tac >> fs[] >>
      rpt (first_x_assum (qspec_then `m` mp_tac)) >>
      rw[] >>
      disj2_tac >>
      qmatch_assum_rename_tac `syneq FEMPTY (v_to_Cv m v1) w1`[] >>
      qmatch_assum_abbrev_tac `Cevaluate FEMPTY FEMPTY sb enva e2a (sc,Rerr err)`>>
      pop_assum kall_tac >>
      qmatch_assum_rename_tac `fmap_rel (syneq FEMPTY) sb sd`[] >>
      qspecl_then[`FEMPTY`,`FEMPTY`,`sb`,`sd`,`enva`,`e2a`,`(sc,Rerr err)`]mp_tac Cevaluate_any_syneq_store >>
      qmatch_assum_abbrev_tac `Cevaluate FEMPTY FEMPTY sa enva e1a (sd,Rval w1)`>>
      `∀v. v ∈ FRANGE enva ⇒ Cclosed FEMPTY v` by (
        unabbrev_all_tac >>
        match_mp_tac IN_FRANGE_alist_to_fmap_suff >>
        fsrw_tac[DNF_ss][SUBSET_DEF,env_to_Cenv_MAP,MEM_MAP,
                         EVERY_MEM,EXISTS_PROD,FORALL_PROD] >>
        rw[] >>
        match_mp_tac (CONJUNCT1 v_to_Cv_closed) >>
        PROVE_TAC[]) >>
      `free_vars FEMPTY e1a ⊆ FDOM enva` by (
        unabbrev_all_tac >>
        fsrw_tac[DNF_ss][SUBSET_DEF,env_to_Cenv_MAP,MEM_MAP,
                         EXISTS_PROD,FORALL_PROD] ) >>
      `free_vars FEMPTY e2a ⊆ FDOM enva` by (
        unabbrev_all_tac >>
        fsrw_tac[DNF_ss][SUBSET_DEF,env_to_Cenv_MAP,MEM_MAP,
                         EXISTS_PROD,FORALL_PROD] ) >>
      `∀v. v ∈ FRANGE sa ⇒ Cclosed FEMPTY v` by (
        unabbrev_all_tac >>
        fsrw_tac[DNF_ss][FRANGE_store_to_Cstore,MEM_MAP,EVERY_MEM] >>
        rw[] >> match_mp_tac (CONJUNCT1 v_to_Cv_closed) >> PROVE_TAC[] ) >>
      `∀v. v ∈ FRANGE sb ⇒ Cclosed FEMPTY v` by (
        unabbrev_all_tac >>
        fsrw_tac[DNF_ss][FRANGE_store_to_Cstore,MEM_MAP,EVERY_MEM] >>
        rw[] >> match_mp_tac (CONJUNCT1 v_to_Cv_closed) >> PROVE_TAC[] ) >>
      qspecl_then[`FEMPTY`,`FEMPTY`,`sa`,`enva`,`e1a`,`(sd,Rval w1)`]mp_tac(CONJUNCT1 Cevaluate_closed) >>
      simp[] >> strip_tac >>
      fsrw_tac[DNF_ss][FORALL_PROD] >>
      qx_gen_tac`se` >> strip_tac >>
      map_every qexists_tac [`se`,`sd`,`w1`] >> fs[] >>
      PROVE_TAC[fmap_rel_syneq_trans])
    >- (
      fs[] >>
      qspecl_then[`cenv`,`s`,`env`,`e1`,`(s',Rval v1)`]mp_tac(CONJUNCT1 evaluate_closed) >>
      simp[]>>strip_tac>>fs[]>>
      fsrw_tac[DNF_ss][EXISTS_PROD]>>
      rpt (first_x_assum (qspec_then `m` mp_tac)) >>
      rw[] >>
      qmatch_assum_rename_tac `syneq FEMPTY (v_to_Cv m v1) w1`[] >>
      qmatch_assum_abbrev_tac `Cevaluate FEMPTY FEMPTY sa enva e1a (sd,Rval w1)` >>
      pop_assum kall_tac >>
      qmatch_assum_abbrev_tac `Cevaluate FEMPTY FEMPTY sb enva e2a (sc,Rerr err)` >>
      pop_assum kall_tac >>
      `∀v. v ∈ FRANGE enva ⇒ Cclosed FEMPTY v` by (
        imp_res_tac v_to_Cv_closed >>
        fs[FEVERY_DEF] >> PROVE_TAC[] ) >>
      `free_vars FEMPTY e1a ⊆ FDOM enva ∧
       free_vars FEMPTY e2a ⊆ FDOM enva` by (
        fs[Abbr`e1a`,Abbr`e2a`,Abbr`enva`,env_to_Cenv_MAP,MAP_MAP_o,
           pairTheory.LAMBDA_PROD,combinTheory.o_DEF,FST_pair,FST_triple] ) >>
      `(∀v. v ∈ FRANGE sa ⇒ Cclosed FEMPTY v) ∧
       (∀v. v ∈ FRANGE sb ⇒ Cclosed FEMPTY v)` by (
         unabbrev_all_tac >>
         fsrw_tac[DNF_ss][FRANGE_store_to_Cstore,MEM_MAP,EVERY_MEM] >>
         rw[] >> match_mp_tac (CONJUNCT1 v_to_Cv_closed) >> res_tac ) >>
      qspecl_then[`FEMPTY`,`FEMPTY`,`sa`,`enva`,`e1a`,`(sd,Rval w1)`]mp_tac(CONJUNCT1 Cevaluate_closed) >>
      simp[] >> strip_tac >> fs[] >>
      qspecl_then[`FEMPTY`,`FEMPTY`,`sb`,`sd`,`enva`,`e2a`,`(sc,Rerr err)`]mp_tac Cevaluate_any_syneq_store >>
      fsrw_tac[DNF_ss][EXISTS_PROD] >>
      qx_gen_tac`se`>>strip_tac >>
      `fmap_rel (syneq FEMPTY) (store_to_Cstore m s3) se` by PROVE_TAC[fmap_rel_syneq_trans] >>
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
        Q.PAT_ABBREV_TAC`fv = fresh_var X` >>
        qspecl_then[`FEMPTY`,`FEMPTY`,`sd`,`enva`,`e2a`,`se`,`err`,`fv`,`w1`]mp_tac Cevaluate_FUPDATE_Rerr >>
        `fv ∉ free_vars FEMPTY e2a` by (
          unabbrev_all_tac >>
          match_mp_tac fresh_var_not_in_any >>
          rw[] ) >>
        simp[] >>
        PROVE_TAC[fmap_rel_syneq_trans])
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
        Q.PAT_ABBREV_TAC`fv = fresh_var X` >>
        qspecl_then[`FEMPTY`,`FEMPTY`,`sd`,`enva`,`e2a`,`se`,`err`,`fv`,`w1`]mp_tac Cevaluate_FUPDATE_Rerr >>
        `fv ∉ free_vars FEMPTY e2a` by (
          unabbrev_all_tac >>
          match_mp_tac fresh_var_not_in_any >>
          rw[] ) >>
        simp[] >>
        PROVE_TAC[fmap_rel_syneq_trans]))
    >- (
      rw[Once Cevaluate_cases] >>
      fsrw_tac[DNF_ss][EXISTS_PROD] >>
      disj2_tac >>
      rw[Once(CONJUNCT2 Cevaluate_cases)] >>
      rw[Once(CONJUNCT2 Cevaluate_cases)] >>
      rw[Once(CONJUNCT2 Cevaluate_cases)] >>
      srw_tac[DNF_ss][]>>
      disj2_tac >>
      qspecl_then[`cenv`,`s`,`env`,`e1`,`(s',Rval v1)`]mp_tac(CONJUNCT1 evaluate_closed) >>
      simp[]>>strip_tac>>fs[]>>
      rpt (first_x_assum (qspec_then `m` mp_tac)) >> rw[] >>
      qmatch_assum_rename_tac `syneq FEMPTY (v_to_Cv m v1) w1`[] >>
      qmatch_assum_abbrev_tac `Cevaluate FEMPTY FEMPTY sa enva e1a (sd,Rval w1)` >>
      pop_assum kall_tac >>
      qmatch_assum_abbrev_tac `Cevaluate FEMPTY FEMPTY sb enva e2a (sc,Rerr err)` >>
      pop_assum kall_tac >>
      `∀v. v ∈ FRANGE enva ⇒ Cclosed FEMPTY v` by (
        imp_res_tac v_to_Cv_closed >>
        fs[FEVERY_DEF] >> PROVE_TAC[] ) >>
      `free_vars FEMPTY e1a ⊆ FDOM enva ∧
       free_vars FEMPTY e2a ⊆ FDOM enva` by (
        fs[Abbr`e1a`,Abbr`e2a`,Abbr`enva`,env_to_Cenv_MAP,MAP_MAP_o,
           pairTheory.LAMBDA_PROD,combinTheory.o_DEF,FST_pair,FST_triple] ) >>
      `(∀v. v ∈ FRANGE sa ⇒ Cclosed FEMPTY v) ∧
       (∀v. v ∈ FRANGE sb ⇒ Cclosed FEMPTY v)` by (
         unabbrev_all_tac >>
         fsrw_tac[DNF_ss][FRANGE_store_to_Cstore,MEM_MAP,EVERY_MEM] >>
         rw[] >> match_mp_tac (CONJUNCT1 v_to_Cv_closed) >> res_tac ) >>
      qspecl_then[`FEMPTY`,`FEMPTY`,`sa`,`enva`,`e1a`,`(sd,Rval w1)`]mp_tac(CONJUNCT1 Cevaluate_closed) >>
      simp[] >> strip_tac >> fs[] >>
      qspecl_then[`FEMPTY`,`FEMPTY`,`sb`,`sd`,`enva`,`e2a`,`(sc,Rerr err)`]mp_tac Cevaluate_any_syneq_store >>
      fsrw_tac[DNF_ss][EXISTS_PROD] >>
      qx_gen_tac`se`>>strip_tac >>
      PROVE_TAC[fmap_rel_syneq_trans] )
    >- (
      rw[Once Cevaluate_cases] >>
      fsrw_tac[DNF_ss][] >>
      disj2_tac >> disj1_tac >>
      fsrw_tac[DNF_ss][EXISTS_PROD] >>
      rw[Once(CONJUNCT2 Cevaluate_cases)] >>
      rw[Once(CONJUNCT2 Cevaluate_cases)] >>
      qspecl_then[`cenv`,`s`,`env`,`e1`,`(s',Rval v1)`]mp_tac(CONJUNCT1 evaluate_closed) >>
      simp[]>>strip_tac>>fs[]>>
      rpt (first_x_assum (qspec_then `m` mp_tac)) >> rw[] >>
      qmatch_assum_rename_tac `syneq FEMPTY (v_to_Cv m v1) w1`[] >>
      qmatch_assum_abbrev_tac `Cevaluate FEMPTY FEMPTY sa enva e1a (sd,Rval w1)` >>
      pop_assum kall_tac >>
      qmatch_assum_abbrev_tac `Cevaluate FEMPTY FEMPTY sb enva e2a (sc,Rerr err)` >>
      pop_assum kall_tac >>
      `∀v. v ∈ FRANGE enva ⇒ Cclosed FEMPTY v` by (
        imp_res_tac v_to_Cv_closed >>
        fs[FEVERY_DEF] >> PROVE_TAC[] ) >>
      `free_vars FEMPTY e1a ⊆ FDOM enva ∧
       free_vars FEMPTY e2a ⊆ FDOM enva` by (
        fs[Abbr`e1a`,Abbr`e2a`,Abbr`enva`,env_to_Cenv_MAP,MAP_MAP_o,
           pairTheory.LAMBDA_PROD,combinTheory.o_DEF,FST_pair,FST_triple] ) >>
      `(∀v. v ∈ FRANGE sa ⇒ Cclosed FEMPTY v) ∧
       (∀v. v ∈ FRANGE sb ⇒ Cclosed FEMPTY v)` by (
         unabbrev_all_tac >>
         fsrw_tac[DNF_ss][FRANGE_store_to_Cstore,MEM_MAP,EVERY_MEM] >>
         rw[] >> match_mp_tac (CONJUNCT1 v_to_Cv_closed) >> res_tac ) >>
      qspecl_then[`FEMPTY`,`FEMPTY`,`sa`,`enva`,`e1a`,`(sd,Rval w1)`]mp_tac(CONJUNCT1 Cevaluate_closed) >>
      simp[] >> strip_tac >> fs[] >>
      qspecl_then[`FEMPTY`,`FEMPTY`,`sb`,`sd`,`enva`,`e2a`,`(sc,Rerr err)`]mp_tac Cevaluate_any_syneq_store >>
      fsrw_tac[DNF_ss][EXISTS_PROD] >>
      PROVE_TAC[fmap_rel_syneq_trans])
    >- (
      rw[Once Cevaluate_cases] >>
      fsrw_tac[DNF_ss][EXISTS_PROD] >>
      disj2_tac >>
      rw[Once(CONJUNCT2 Cevaluate_cases)] >>
      rw[Once(CONJUNCT2 Cevaluate_cases)] >>
      rw[Once(CONJUNCT2 Cevaluate_cases)] >>
      srw_tac[DNF_ss][] >>
      disj2_tac >>
      qspecl_then[`cenv`,`s`,`env`,`e1`,`(s',Rval v1)`]mp_tac(CONJUNCT1 evaluate_closed) >>
      simp[]>>strip_tac>>fs[]>>
      rpt (first_x_assum (qspec_then `m` mp_tac)) >> rw[] >>
      qmatch_assum_rename_tac `syneq FEMPTY (v_to_Cv m v1) w1`[] >>
      qmatch_assum_abbrev_tac `Cevaluate FEMPTY FEMPTY sa enva e1a (sd,Rval w1)` >>
      pop_assum kall_tac >>
      qmatch_assum_abbrev_tac `Cevaluate FEMPTY FEMPTY sb enva e2a (sc,Rerr err)` >>
      pop_assum kall_tac >>
      `∀v. v ∈ FRANGE enva ⇒ Cclosed FEMPTY v` by (
        imp_res_tac v_to_Cv_closed >>
        fs[FEVERY_DEF] >> PROVE_TAC[] ) >>
      `free_vars FEMPTY e1a ⊆ FDOM enva ∧
       free_vars FEMPTY e2a ⊆ FDOM enva` by (
        fs[Abbr`e1a`,Abbr`e2a`,Abbr`enva`,env_to_Cenv_MAP,MAP_MAP_o,
           pairTheory.LAMBDA_PROD,combinTheory.o_DEF,FST_pair,FST_triple] ) >>
      `(∀v. v ∈ FRANGE sa ⇒ Cclosed FEMPTY v) ∧
       (∀v. v ∈ FRANGE sb ⇒ Cclosed FEMPTY v)` by (
         unabbrev_all_tac >>
         fsrw_tac[DNF_ss][FRANGE_store_to_Cstore,MEM_MAP,EVERY_MEM] >>
         rw[] >> match_mp_tac (CONJUNCT1 v_to_Cv_closed) >> res_tac ) >>
      qspecl_then[`FEMPTY`,`FEMPTY`,`sa`,`enva`,`e1a`,`(sd,Rval w1)`]mp_tac(CONJUNCT1 Cevaluate_closed) >>
      simp[] >> strip_tac >> fs[] >>
      qspecl_then[`FEMPTY`,`FEMPTY`,`sb`,`sd`,`enva`,`e2a`,`(sc,Rerr err)`]mp_tac Cevaluate_any_syneq_store >>
      fsrw_tac[DNF_ss][EXISTS_PROD] >>
      PROVE_TAC[fmap_rel_syneq_trans])) >>
  strip_tac >- (
    ntac 2 gen_tac >>
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
    `FV exp' ⊆ set (MAP FST env)` by PROVE_TAC[SUBSET_TRANS] >>
    qspecl_then[`cenv`,`s`,`env`,`exp`,`(s',Rval v)`]mp_tac(CONJUNCT1 evaluate_closed) >>
    simp[]>>strip_tac>>fs[]>>
    rpt (first_x_assum (qspec_then`m` mp_tac)) >> rw[] >>
    qmatch_assum_rename_tac`syneq FEMPTY (v_to_Cv m v) w`[] >>
    qmatch_assum_abbrev_tac `Cevaluate FEMPTY FEMPTY sa enva e1a (sd,Rval w)` >>
    pop_assum kall_tac >>
    qmatch_assum_abbrev_tac `Cevaluate FEMPTY FEMPTY sb enva e2a (sc,w2)` >>
    ntac 2 (pop_assum kall_tac) >>
    `∀v. v ∈ FRANGE enva ⇒ Cclosed FEMPTY v` by (
      imp_res_tac v_to_Cv_closed >>
      fs[FEVERY_DEF] >> PROVE_TAC[] ) >>
    `free_vars FEMPTY e1a ⊆ FDOM enva ∧
     free_vars FEMPTY e2a ⊆ FDOM enva` by (
      fs[Abbr`e1a`,Abbr`e2a`,Abbr`enva`,env_to_Cenv_MAP,MAP_MAP_o,
         pairTheory.LAMBDA_PROD,combinTheory.o_DEF,FST_pair,FST_triple] ) >>
    `(∀v. v ∈ FRANGE sa ⇒ Cclosed FEMPTY v) ∧
     (∀v. v ∈ FRANGE sb ⇒ Cclosed FEMPTY v)` by (
       unabbrev_all_tac >>
       fsrw_tac[DNF_ss][FRANGE_store_to_Cstore,MEM_MAP,EVERY_MEM] >>
       rw[] >> match_mp_tac (CONJUNCT1 v_to_Cv_closed) >> res_tac ) >>
    qspecl_then[`FEMPTY`,`FEMPTY`,`sa`,`enva`,`e1a`,`(sd,Rval w)`]mp_tac(CONJUNCT1 Cevaluate_closed) >>
    simp[] >> strip_tac >> fs[] >>
    qspecl_then[`FEMPTY`,`FEMPTY`,`sb`,`sd`,`enva`,`e2a`,`(sc,w2)`]mp_tac Cevaluate_any_syneq_store >>
    fsrw_tac[DNF_ss][EXISTS_PROD] >>
    map_every qx_gen_tac[`se`,`w3`] >>strip_tac >>
    Cases_on `op` >> Cases_on `v` >> fs[do_log_def] >>
    Cases_on `l` >> fs[v_to_Cv_def] >>
    fs[Q.SPECL[`c`,`CLitv l`]syneq_cases] >> rw[] >>
    rw[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][] >> disj1_tac >>
    CONV_TAC (RESORT_EXISTS_CONV List.rev) >>
    map_every qexists_tac [`b`,`sd`] >> fs[] >>
    rw[] >> fs[] >> rw[] >>
    fs[evaluate_lit] >> rw[v_to_Cv_def] >>
    PROVE_TAC[result_rel_syneq_trans,fmap_rel_syneq_trans] ) >>
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
    `FV exp' ⊆ set (MAP FST env)` by (
      fsrw_tac[DNF_ss][SUBSET_DEF] >>
      PROVE_TAC[]) >> fs[] >>
    qspecl_then[`cenv`,`s`,`env`,`exp`,`(s',Rval v)`]mp_tac(CONJUNCT1 evaluate_closed) >>
    simp[]>>strip_tac>>fs[]>>
    rw[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][] >>
    disj1_tac >>
    rpt (first_x_assum (qspec_then`m` mp_tac)) >> rw[] >>
    qmatch_assum_rename_tac`syneq FEMPTY (v_to_Cv m v) w`[] >>
    qmatch_assum_abbrev_tac `Cevaluate FEMPTY FEMPTY sa enva e1a (sd,Rval w)` >>
    pop_assum kall_tac >>
    qmatch_assum_abbrev_tac `Cevaluate FEMPTY FEMPTY sb enva e2a (sc,w2)` >>
    ntac 2 (pop_assum kall_tac) >>
    `∀v. v ∈ FRANGE enva ⇒ Cclosed FEMPTY v` by (
      imp_res_tac v_to_Cv_closed >>
      fs[FEVERY_DEF] >> PROVE_TAC[] ) >>
    `free_vars FEMPTY e1a ⊆ FDOM enva ∧
     free_vars FEMPTY e2a ⊆ FDOM enva` by (
      fs[Abbr`e1a`,Abbr`e2a`,Abbr`enva`,env_to_Cenv_MAP,MAP_MAP_o,
         pairTheory.LAMBDA_PROD,combinTheory.o_DEF,FST_pair,FST_triple] ) >>
    `(∀v. v ∈ FRANGE sa ⇒ Cclosed FEMPTY v) ∧
     (∀v. v ∈ FRANGE sb ⇒ Cclosed FEMPTY v)` by (
       unabbrev_all_tac >>
       fsrw_tac[DNF_ss][FRANGE_store_to_Cstore,MEM_MAP,EVERY_MEM] >>
       rw[] >> match_mp_tac (CONJUNCT1 v_to_Cv_closed) >> res_tac ) >>
    qspecl_then[`FEMPTY`,`FEMPTY`,`sa`,`enva`,`e1a`,`(sd,Rval w)`]mp_tac(CONJUNCT1 Cevaluate_closed) >>
    simp[] >> strip_tac >> fs[] >>
    qspecl_then[`FEMPTY`,`FEMPTY`,`sb`,`sd`,`enva`,`e2a`,`(sc,w2)`]mp_tac Cevaluate_any_syneq_store >>
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
    fsrw_tac[DNF_ss][v_to_Cv_def,Q.SPECL[`c`,`CLitv l`]syneq_cases] >>
    PROVE_TAC[fmap_rel_syneq_trans,result_rel_syneq_trans]) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rw[exp_to_Cexp_def,LET_THM] >> fs[] >>
    rw[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][EXISTS_PROD]) >>
  strip_tac >- (
    rpt strip_tac >> fs[] >>
    fsrw_tac[DNF_ss][EXISTS_PROD] >>
    first_x_assum (qspec_then `m` mp_tac) >> rw[] >>
    qmatch_assum_rename_tac `syneq FEMPTY (v_to_Cv m v) w`[] >>
    rw[exp_to_Cexp_def,LET_THM] >>
    rw[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][] >>
    disj1_tac >>
    qmatch_assum_abbrev_tac`Cevaluate FEMPTY FEMPTY sa enva ea (sd,Rval w)` >>
    pop_assum kall_tac >>
    CONV_TAC (RESORT_EXISTS_CONV List.rev) >>
    map_every qexists_tac [`w`,`sd`] >> fs[] >>
    qmatch_assum_abbrev_tac `evaluate_match_with P cenv s2 env v pes res` >>
    Q.ISPECL_THEN [`s2`,`pes`,`res`] mp_tac (Q.GEN`s`evaluate_match_with_matchres) >> fs[] >>
    PairCases_on`res`>>fs[]>>strip_tac>>
    qmatch_assum_abbrev_tac`evaluate_match_with (matchres env) cenv s2 env v pes r` >>
    Q.ISPECL_THEN [`s2`,`pes`,`r`] mp_tac (Q.GEN`s`evaluate_match_with_Cevaluate_match) >>
    fs[Abbr`r`] >>
    disch_then (qspec_then `m` mp_tac) >>
    rw[] >- (
      qmatch_assum_abbrev_tac `Cevaluate_match sb vv ppes FEMPTY NONE` >>
      `Cevaluate_match sb vv (MAP (λ(p,e). (p, exp_to_Cexp m e)) ppes) FEMPTY NONE` by (
        metis_tac [Cevaluate_match_MAP_exp, optionTheory.OPTION_MAP_DEF] ) >>
      qmatch_assum_abbrev_tac `Cevaluate_match sb vv (MAP ff ppes) FEMPTY NONE` >>
      `MAP ff ppes = pes_to_Cpes m pes` by (
        unabbrev_all_tac >>
        rw[pes_to_Cpes_MAP,LET_THM] >>
        rw[MAP_MAP_o,combinTheory.o_DEF,pairTheory.LAMBDA_PROD] >>
        rw[pairTheory.UNCURRY] ) >>
      fs[] >>
      map_every qunabbrev_tac[`ppes`,`ff`,`vv`] >>
      pop_assum kall_tac >>
      ntac 2 (pop_assum mp_tac) >>
      pop_assum kall_tac >>
      ntac 2 strip_tac >>
      Q.SPECL_THEN [`sb`,`v_to_Cv m v`,`pes_to_Cpes m pes`,`FEMPTY`,`NONE`]
        mp_tac (INST_TYPE[alpha|->``:Cexp``](Q.GENL[`v`,`s`] Cevaluate_match_syneq)) >>
      fs[] >>
      disch_then (qspecl_then [`FEMPTY`,`sd`,`w`] mp_tac) >> fs[] >>
      strip_tac >>
      qabbrev_tac`ps = pes_to_Cpes m pes` >>
      qspecl_then[`sd`,`w`,`ps`,`FEMPTY`,`NONE`]mp_tac(Q.GENL[`v`,`s`]Cevaluate_match_remove_mat_var)>>
      fs[] >>
      fsrw_tac[DNF_ss][EXISTS_PROD] >>
      Q.PAT_ABBREV_TAC`envu = enva |+ X` >>
      Q.PAT_ABBREV_TAC`fv = fresh_var X` >>
      disch_then (qspecl_then[`envu`,`fv`]mp_tac)>>
      qmatch_abbrev_tac`(P0 ⇒ Q) ⇒ R` >>
      `P0` by (
        map_every qunabbrev_tac[`P0`,`Q`,`R`] >>
        fs[FLOOKUP_UPDATE,Abbr`envu`] >>
        fsrw_tac[DNF_ss][pairTheory.FORALL_PROD] >>
        conj_tac >- (
          qx_gen_tac `z` >>
          Cases_on `fv ∈ z` >> fs[] >>
          qx_gen_tac `p` >>
          qx_gen_tac `e` >>
          Cases_on `z = Cpat_vars p` >> fs[] >>
          spose_not_then strip_assume_tac >>
          `fv ∉ Cpat_vars p` by (
            unabbrev_all_tac >>
            match_mp_tac fresh_var_not_in_any >>
            rw[Cpes_vars_thm] >> rw[] >>
            srw_tac[DNF_ss][SUBSET_DEF,pairTheory.EXISTS_PROD,MEM_MAP] >>
            metis_tac[] ) ) >>
        conj_tac >- (
          unabbrev_all_tac >>
          fsrw_tac[DNF_ss][env_to_Cenv_MAP,MAP_MAP_o,combinTheory.o_DEF,pairTheory.LAMBDA_PROD,FST_pair,FST_triple] >>
          fsrw_tac[DNF_ss][SUBSET_DEF,pairTheory.FORALL_PROD,pes_to_Cpes_MAP,MEM_MAP,LET_THM,pairTheory.EXISTS_PROD] >>
          fsrw_tac[DNF_ss][pairTheory.UNCURRY,Cpes_vars_thm] >>
          metis_tac[Cpat_vars_pat_to_Cpat,pairTheory.pair_CASES,pairTheory.SND] ) >>
        `∀v. v ∈ FRANGE sa ⇒ Cclosed FEMPTY v` by (
          unabbrev_all_tac >>
          fsrw_tac[DNF_ss][FRANGE_store_to_Cstore,MEM_MAP,EVERY_MEM] >>
          rw[] >> match_mp_tac (CONJUNCT1 v_to_Cv_closed) >> res_tac ) >>
        `free_vars FEMPTY ea ⊆ FDOM enva` by (
          unabbrev_all_tac >>
          fs[env_to_Cenv_MAP,MAP_MAP_o,combinTheory.o_DEF,LAMBDA_PROD,FST_pair,FST_triple]) >>
        `∀v. v ∈ FRANGE enva ⇒ Cclosed FEMPTY v` by (
          unabbrev_all_tac >>
          match_mp_tac IN_FRANGE_alist_to_fmap_suff >>
          fsrw_tac[DNF_ss][MEM_MAP,FORALL_PROD,env_to_Cenv_MAP,EVERY_MEM] >>
          rw[] >> match_mp_tac (CONJUNCT1 v_to_Cv_closed) >> res_tac ) >>
        qspecl_then[`FEMPTY`,`FEMPTY`,`sa`,`enva`,`ea`,`(sd,Rval w)`]mp_tac(CONJUNCT1 Cevaluate_closed) >>
        simp[] >> strip_tac >>
        match_mp_tac IN_FRANGE_DOMSUB_suff >>
        rw[] ) >>
      simp[] >>
      map_every qunabbrev_tac[`P0`,`Q`,`R`] >>
      metis_tac[fmap_rel_syneq_trans,fmap_rel_syneq_sym] ) >>
    qmatch_assum_abbrev_tac `Cevaluate_match sb vv ppes eenv (SOME mr)` >>
    `Cevaluate_match sb vv (MAP (λ(p,e). (p, exp_to_Cexp m e)) ppes) eenv (SOME (exp_to_Cexp m mr))` by (
      metis_tac [Cevaluate_match_MAP_exp, optionTheory.OPTION_MAP_DEF] ) >>
    pop_assum mp_tac >>
    map_every qunabbrev_tac[`ppes`,`eenv`,`vv`] >>
    pop_assum mp_tac >>
    pop_assum kall_tac >>
    ntac 2 strip_tac >>
    qmatch_assum_abbrev_tac `Cevaluate_match sb vv (MAP ff ppes) eenv mmr` >>
    `MAP ff ppes = pes_to_Cpes m pes` by (
      unabbrev_all_tac >>
      rw[pes_to_Cpes_MAP,LET_THM] >>
      rw[MAP_MAP_o,combinTheory.o_DEF,pairTheory.LAMBDA_PROD] >>
      rw[pairTheory.UNCURRY] ) >>
    fs[] >>
    pop_assum kall_tac >>
    qunabbrev_tac `ppes` >>
    qabbrev_tac`ps = pes_to_Cpes m pes` >>
    Q.ISPECL_THEN[`sb`,`vv`,`ps`,`eenv`,`mmr`]mp_tac(Q.GENL[`v`,`s`]Cevaluate_match_syneq) >>
    simp[] >>
    disch_then(qspecl_then[`FEMPTY`,`sd`,`w`]mp_tac) >>
    simp[] >>
    disch_then(Q.X_CHOOSE_THEN`wenv`strip_assume_tac) >>
    qspecl_then[`sd`,`w`,`ps`,`wenv`,`mmr`]mp_tac(Q.GENL[`v`,`s`]Cevaluate_match_remove_mat_var) >>
    simp[Abbr`mmr`] >>
    Q.PAT_ABBREV_TAC`fv = fresh_var X` >>
    fsrw_tac[DNF_ss][FORALL_PROD,EXISTS_PROD] >>
    disch_then(qspecl_then[`enva|+(fv,w)`,`fv`]mp_tac) >>
    qspecl_then[`cenv`,`s`,`env`,`exp`,`(s2,Rval v)`]mp_tac(CONJUNCT1 evaluate_closed) >>
    simp[] >> strip_tac >>
    Q.ISPECL_THEN[`s2`,`pes`,`(s2,Rval(menv,mr))`]mp_tac(Q.GEN`s`evaluate_match_with_matchres_closed)>>
    simp[] >> strip_tac >>
    `FV mr ⊆ set (MAP FST (menv ++ env))` by (
      fsrw_tac[DNF_ss][SUBSET_DEF,FORALL_PROD,MEM_MAP,EXISTS_PROD] >>
      pop_assum mp_tac >>
      simp[EXTENSION] >>
      fsrw_tac[DNF_ss][MEM_MAP,EXISTS_PROD] >>
      METIS_TAC[] ) >>
    fs[Abbr`P`] >> rfs[] >> fs[] >>
    first_x_assum(qspec_then`m`mp_tac)>>
    fsrw_tac[DNF_ss][] >>
    qpat_assum`evaluate_match_with P cenv s2 env v pes (res0,res1)`kall_tac >>
    map_every qx_gen_tac [`se`,`re`] >> strip_tac >>
    qabbrev_tac`emr = exp_to_Cexp m mr` >>
    qspecl_then[`FEMPTY`,`FEMPTY`,`sb`,`sd`,`eenv ⊌ enva`,`wenv ⊌ enva`,`emr`,`(se,re)`]mp_tac Cevaluate_any_syneq_any >>
    `∀v. v ∈ FRANGE sb ⇒ Cclosed FEMPTY v` by (
      unabbrev_all_tac >>
      fsrw_tac[DNF_ss][FRANGE_store_to_Cstore,MEM_MAP,EVERY_MEM] >>
      rw[] >> match_mp_tac (CONJUNCT1 v_to_Cv_closed) >> res_tac ) >>
    `∀v. v ∈ FRANGE enva ⇒ Cclosed FEMPTY v` by (
      unabbrev_all_tac >>
      match_mp_tac IN_FRANGE_alist_to_fmap_suff >>
      fsrw_tac[DNF_ss][env_to_Cenv_MAP,MEM_MAP,FORALL_PROD,EVERY_MEM] >>
      rw[] >> match_mp_tac (CONJUNCT1 v_to_Cv_closed) >> res_tac ) >>
    `free_vars FEMPTY ea ⊆ FDOM enva` by (
      unabbrev_all_tac >>
      fsrw_tac[DNF_ss][env_to_Cenv_MAP,SUBSET_DEF,MEM_MAP,FORALL_PROD,EXISTS_PROD]) >>
    `∀v. v ∈ FRANGE sa ⇒ Cclosed FEMPTY v` by (
      unabbrev_all_tac >>
      fsrw_tac[DNF_ss][FRANGE_store_to_Cstore,MEM_MAP,EVERY_MEM] >>
      rw[] >> match_mp_tac (CONJUNCT1 v_to_Cv_closed) >> res_tac ) >>
    qspecl_then[`FEMPTY`,`FEMPTY`,`sa`,`enva`,`ea`,`(sd,Rval w)`]mp_tac(CONJUNCT1 Cevaluate_closed) >>
    simp[] >> strip_tac >>
    qspecl_then[`FEMPTY`,`sd`,`w`,`ps`,`wenv`,`SOME emr`]mp_tac
      (INST_TYPE[alpha|->``:Cexp``](Q.GENL[`v`,`s`,`c`]Cevaluate_match_closed)) >>
    simp[] >> strip_tac >>
    `∀v. v ∈ FRANGE eenv ⇒ Cclosed FEMPTY v` by (
      unabbrev_all_tac >>
      match_mp_tac IN_FRANGE_alist_to_fmap_suff >>
      fsrw_tac[DNF_ss][env_to_Cenv_MAP,MEM_MAP,EVERY_MEM,FORALL_PROD,EXISTS_PROD] >>
      rw[] >> match_mp_tac (CONJUNCT1 v_to_Cv_closed) >> res_tac ) >>
    qmatch_abbrev_tac`(P ⇒ Q) ⇒ R` >>
    `P` by (
      map_every qunabbrev_tac[`P`,`Q`,`R`] >>
      conj_tac >- (
        match_mp_tac fmap_rel_FUNION_rels >> rw[] ) >>
      conj_tac >- (
        match_mp_tac IN_FRANGE_FUNION_suff >> rw[] ) >>
      conj_tac >- (
        unabbrev_all_tac >>
        rw[env_to_Cenv_MAP,MAP_MAP_o,combinTheory.o_DEF,UNCURRY] >>
        srw_tac[ETA_ss][] ) >>
      match_mp_tac IN_FRANGE_FUNION_suff >> rw[] ) >>
    simp[] >>
    map_every qunabbrev_tac[`P`,`Q`,`R`] >>
    fsrw_tac[DNF_ss][FORALL_PROD] >>
    map_every qx_gen_tac[`sf`,`rf`] >> strip_tac >>
    qspecl_then[`FEMPTY`,`FEMPTY`,`sd`,`wenv ⊌ enva`,`emr`,`(sf,rf)`,`fv`,`w`]mp_tac Cevaluate_FUPDATE >>
    `fv ∉ free_vars FEMPTY emr` by (
      unabbrev_all_tac >>
      match_mp_tac fresh_var_not_in_any >>
      fsrw_tac[DNF_ss][SUBSET_DEF,Cpes_vars_thm,pes_to_Cpes_MAP,LET_THM,MEM_MAP,
                       UNCURRY,EXISTS_PROD,FORALL_PROD] >>
      fsrw_tac[DNF_ss][env_to_Cenv_MAP,MEM_MAP,EXISTS_PROD] >>
      PROVE_TAC[] ) >>
    `FDOM wenv = FDOM eenv` by fs[fmap_rel_def] >>
    fsrw_tac[DNF_ss][FORALL_PROD] >>
    map_every qx_gen_tac[`sg`,`rg`] >> strip_tac >>
    `(wenv ⊌ enva) |+ (fv,w) = wenv ⊌ enva |+ (fv,w)` by (
      `fv ∉ FDOM eenv` by (
        unabbrev_all_tac >>
        match_mp_tac fresh_var_not_in_any >>
        fs[fmap_rel_def] >>
        fsrw_tac[DNF_ss][Cpes_vars_thm] >>
        `set (MAP FST (env_to_Cenv m menv)) = Cpat_vars (SND (pat_to_Cpat m [] p))` by (
          fsrw_tac[DNF_ss][env_to_Cenv_MAP,MAP_MAP_o,pairTheory.LAMBDA_PROD,combinTheory.o_DEF,FST_pair,FST_triple] >>
          METIS_TAC[Cpat_vars_pat_to_Cpat,pairTheory.SND,pairTheory.pair_CASES] ) >>
        fs[] >>
        fsrw_tac[DNF_ss][SUBSET_DEF,pes_to_Cpes_MAP,MEM_MAP,LET_THM] >>
        qpat_assum `MEM (p,x) pes` mp_tac >>
        rpt (pop_assum kall_tac) >>
        fsrw_tac[DNF_ss][pairTheory.EXISTS_PROD,pairTheory.UNCURRY] >>
        METIS_TAC[Cpat_vars_pat_to_Cpat,pairTheory.SND,pairTheory.pair_CASES] ) >>
      rw[FUNION_FUPDATE_2] ) >>
    disch_then(qspecl_then[`sg`,`rg`]mp_tac)>> fs[] >>
    qmatch_abbrev_tac`(P ⇒ Q) ⇒ R` >>
    `P` by (
      map_every qunabbrev_tac[`P`,`Q`,`R`] >>
      simp[FLOOKUP_UPDATE] >>
      conj_tac >- (
        spose_not_then strip_assume_tac >>
        unabbrev_all_tac >> rw[] >>
        qpat_assum`fresh_var X ∈ Y`mp_tac >>
        simp[] >>
        match_mp_tac fresh_var_not_in_any >>
        fsrw_tac[DNF_ss][SUBSET_DEF,Cpes_vars_thm,MEM_MAP,pes_to_Cpes_MAP,LET_THM,UNCURRY] >>
        PROVE_TAC[] ) >>
      conj_tac >- (
        unabbrev_all_tac >>
        fsrw_tac[DNF_ss][SUBSET_DEF,pes_to_Cpes_MAP,env_to_Cenv_MAP,MEM_MAP,LET_THM,UNCURRY] >>
        PROVE_TAC[] ) >>
      match_mp_tac IN_FRANGE_DOMSUB_suff >>
      rw[] ) >>
    simp[] >>
    map_every qunabbrev_tac[`P`,`Q`,`R`] >>
    metis_tac[result_rel_syneq_trans,result_rel_syneq_sym,
              fmap_rel_syneq_sym,fmap_rel_syneq_trans]) >>
  strip_tac >- (
    rw[exp_to_Cexp_def,LET_THM] >>
    rw[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][EXISTS_PROD]) >>
  strip_tac >- (
    rw[exp_to_Cexp_def,LET_THM] >>
    rw[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][bind_def,EXISTS_PROD] >>
    disj1_tac >>
    qspecl_then[`cenv`,`s`,`env`,`exp`,`(s',Rval v)`]mp_tac(CONJUNCT1 evaluate_closed) >>
    simp[] >> strip_tac >> fs[] >>
    rpt (first_x_assum (qspec_then `m` mp_tac)) >>
    rw[] >>
    qmatch_assum_rename_tac`syneq FEMPTY (v_to_Cv m v) w`[] >>
    pop_assum mp_tac >>
    Q.PAT_ABBREV_TAC`P = X ⊆ Y` >>
    `P` by (
      unabbrev_all_tac >>
      fsrw_tac[DNF_ss][SUBSET_DEF] >>
      METIS_TAC[] ) >>
    simp[] >> qunabbrev_tac`P` >>
    qmatch_assum_abbrev_tac`Cevaluate FEMPTY FEMPTY sa enva ea (sd,Rval w)` >>
    pop_assum kall_tac >>
    fsrw_tac[DNF_ss][] >>
    map_every qx_gen_tac[`se`,`re`] >>
    strip_tac >>
    qmatch_assum_abbrev_tac`Cevaluate FEMPTY FEMPTY sb envb eb (se,re)` >>
    CONV_TAC (RESORT_EXISTS_CONV List.rev) >>
    map_every qexists_tac[`w`,`sd`] >>
    rw[] >>
    qspecl_then[`FEMPTY`,`FEMPTY`,`sb`,`sd`,`envb`,`enva |+ (n,w)`,`eb`,`(se,re)`]mp_tac Cevaluate_any_syneq_any >>
    `(∀v. v ∈ FRANGE sa ⇒ Cclosed FEMPTY v) ∧
     (∀v. v ∈ FRANGE sb ⇒ Cclosed FEMPTY v)` by (
      unabbrev_all_tac >>
      fsrw_tac[DNF_ss][FRANGE_store_to_Cstore,MEM_MAP,EVERY_MEM] >>
      rw[] >> match_mp_tac(CONJUNCT1 v_to_Cv_closed) >> res_tac) >>
    `(free_vars FEMPTY ea ⊆ FDOM enva) ∧
     (free_vars FEMPTY eb ⊆ FDOM envb)` by (
      unabbrev_all_tac >>
      fsrw_tac[DNF_ss][env_to_Cenv_MAP,MAP_MAP_o,SUBSET_DEF,MEM_MAP,FORALL_PROD,EXISTS_PROD]) >>
    `(∀v. v ∈ FRANGE enva ⇒ Cclosed FEMPTY v) ∧
     (∀v. v ∈ FRANGE envb ⇒ Cclosed FEMPTY v)` by (
      unabbrev_all_tac >> conj_tac >>
      match_mp_tac IN_FRANGE_alist_to_fmap_suff >>
      fsrw_tac[DNF_ss][MEM_MAP,env_to_Cenv_MAP,FORALL_PROD,EVERY_MEM] >>
      rw[] >> match_mp_tac (CONJUNCT1 v_to_Cv_closed) >> res_tac >> fs[] ) >>
    qspecl_then[`FEMPTY`,`FEMPTY`,`sa`,`enva`,`ea`,`(sd,Rval w)`]mp_tac(CONJUNCT1 Cevaluate_closed) >>
    simp[] >> strip_tac >>
    qmatch_abbrev_tac`(P ⇒ Q) ⇒ R` >>
    `P` by (
      unabbrev_all_tac >>
      conj_tac >- (
        rw[fmap_rel_def,env_to_Cenv_MAP,FAPPLY_FUPDATE_THM] >>
        rw[] ) >>
      fsrw_tac[DNF_ss][] >>
      match_mp_tac IN_FRANGE_DOMSUB_suff >>
      simp[] ) >>
    simp[] >>
    unabbrev_all_tac >>
    fsrw_tac[DNF_ss][FORALL_PROD] >>
    metis_tac[result_rel_syneq_trans,fmap_rel_syneq_trans] ) >>
  strip_tac >- (
    rw[exp_to_Cexp_def,LET_THM] >>
    rw[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][EXISTS_PROD]) >>
  strip_tac >- (
    rw[exp_to_Cexp_def,LET_THM,FST_triple] >>
    fs[] >>
    rw[defs_to_Cdefs_MAP] >>
    rw[Once Cevaluate_cases,FOLDL_FUPDATE_LIST] >>
    `FV exp ⊆ set (MAP FST funs) ∪ set (MAP FST env)` by (
      fsrw_tac[DNF_ss][SUBSET_DEF,pairTheory.FORALL_PROD,MEM_MAP,pairTheory.EXISTS_PROD] >>
      METIS_TAC[] ) >>
    fs[] >>
    `EVERY closed (MAP (FST o SND) (build_rec_env tvs funs env))` by (
      match_mp_tac build_rec_env_closed >>
      fs[] >>
      fsrw_tac[DNF_ss][SUBSET_DEF,pairTheory.FORALL_PROD,MEM_MAP,pairTheory.EXISTS_PROD,MEM_EL,FST_5tup] >>
      METIS_TAC[] ) >>
    fs[] >>
    first_x_assum (qspec_then `m` mp_tac) >>
    fs[] >>
    simp_tac std_ss [build_rec_env_def,bind_def,FOLDR_CONS_5tup] >>
    fsrw_tac[DNF_ss][EXISTS_PROD,FORALL_PROD] >>
    simp_tac std_ss [FUNION_alist_to_fmap] >>
    Q.PAT_ABBREV_TAC`ee = alist_to_fmap (env_to_Cenv X Y)` >>
    simp_tac (srw_ss()) [env_to_Cenv_MAP,MAP_MAP_o,combinTheory.o_DEF,pairTheory.LAMBDA_PROD] >>
    simp_tac (srw_ss()) [v_to_Cv_def,LET_THM,pairTheory.UNCURRY,defs_to_Cdefs_MAP] >>
    Q.PAT_ABBREV_TAC`ls:(string#Cv) list = MAP f funs` >>
    `ALL_DISTINCT (MAP FST ls)` by (
      unabbrev_all_tac >>
      rw[MAP_MAP_o,combinTheory.o_DEF,pairTheory.LAMBDA_PROD,FST_triple] ) >>
    rw[FUPDATE_LIST_ALL_DISTINCT_REVERSE] >>
    rw[MEM_MAP,FORALL_PROD,EXISTS_PROD] >>
    fs[FST_5tup] >>
    qmatch_assum_rename_tac `Cevaluate FEMPTY FEMPTY X Y Z (p1,p2)`["X","Y","Z"] >>
    map_every qexists_tac[`p1`,`p2`] >>
    reverse conj_tac >- METIS_TAC[] >>
    reverse conj_tac >- METIS_TAC[] >>
    spose_not_then strip_assume_tac >>
    pop_assum mp_tac >> rw[EL_MAP,UNCURRY]) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rw[] >>
    fsrw_tac[DNF_ss][EXISTS_PROD] >>
    rw[Once Cevaluate_cases] ) >>
  strip_tac >- (
    rw[] >>
    rw[Once (CONJUNCT2 Cevaluate_cases)] >>
    fsrw_tac[DNF_ss][EXISTS_PROD] >>
    qspecl_then[`cenv`,`s`,`env`,`exp`,`(s',Rval v)`]mp_tac(CONJUNCT1 evaluate_closed) >>
    simp[] >> strip_tac >> fs[] >>
    rpt (first_x_assum (qspec_then`m` mp_tac)) >>
    rw[] >>
    qmatch_assum_rename_tac`syneq FEMPTY (v_to_Cv m v) w`[] >>
    qmatch_assum_abbrev_tac`Cevaluate FEMPTY FEMPTY sa enva ea (sd,Rval w)` >>
    pop_assum kall_tac >>
    CONV_TAC SWAP_EXISTS_CONV >> qexists_tac`sd` >>
    CONV_TAC SWAP_EXISTS_CONV >> qexists_tac`w` >> rw[] >>
    qmatch_assum_abbrev_tac`Cevaluate_list FEMPTY FEMPTY sb enva eb (se,Rval ws)` >>
    ntac 2 (pop_assum kall_tac) >>
    qspecl_then[`FEMPTY`,`FEMPTY`,`sb`,`sd`,`enva`,`enva`,`eb`,`(se,Rval ws)`]mp_tac Cevaluate_list_any_syneq_any >>
    `∀v. v ∈ FRANGE enva ⇒ Cclosed FEMPTY v` by (
      unabbrev_all_tac >>
      match_mp_tac IN_FRANGE_alist_to_fmap_suff >>
      fsrw_tac[DNF_ss][MEM_MAP,env_to_Cenv_MAP,EVERY_MEM,FORALL_PROD] >>
      rw[] >> match_mp_tac (CONJUNCT1 v_to_Cv_closed) >> res_tac ) >>
    `(∀v. v ∈ FRANGE sa ⇒ Cclosed FEMPTY v) ∧
     (∀v. v ∈ FRANGE sb ⇒ Cclosed FEMPTY v)` by (
      unabbrev_all_tac >>
      fsrw_tac[DNF_ss][FRANGE_store_to_Cstore,MEM_MAP,EVERY_MEM] >>
      rw[] >> match_mp_tac(CONJUNCT1 v_to_Cv_closed) >> res_tac) >>
    `(free_vars FEMPTY ea ⊆ FDOM enva) ∧
     (BIGUNION (IMAGE (free_vars FEMPTY) (set eb)) ⊆ FDOM enva)` by (
      unabbrev_all_tac >>
      fsrw_tac[DNF_ss][env_to_Cenv_MAP,MAP_MAP_o,SUBSET_DEF,MEM_MAP,FORALL_PROD,EXISTS_PROD]) >>
    qspecl_then[`FEMPTY`,`FEMPTY`,`sa`,`enva`,`ea`,`(sd,Rval w)`]mp_tac(CONJUNCT1 Cevaluate_closed) >>
    simp[] >> strip_tac >>
    fsrw_tac[DNF_ss][FORALL_PROD] >>
    map_every qx_gen_tac[`sf`,`rf`] >>
    strip_tac >>
    map_every qexists_tac[`sf`,`rf`] >>
    simp[] >>
    conj_tac >- METIS_TAC[fmap_rel_syneq_trans] >>
    fsrw_tac[DNF_ss][EVERY2_EVERY,EVERY_MEM,FORALL_PROD,MEM_ZIP] >>
    `LENGTH vs = LENGTH ws` by rw[] >>
    qpat_assum `LENGTH ws = LENGTH rf` assume_tac >>
    fsrw_tac[DNF_ss][MEM_ZIP] >>
    rw[EL_MAP] >>
    rpt (first_x_assum (qspec_then`n`mp_tac)) >>
    rw[EL_MAP] >>
    METIS_TAC[syneq_trans] ) >>
  strip_tac >- (
    rw[] >>
    rw[Once (CONJUNCT2 Cevaluate_cases)] >>
    fsrw_tac[DNF_ss][EXISTS_PROD] ) >>
  rw[] >>
  rw[Once (CONJUNCT2 Cevaluate_cases)] >>
  fsrw_tac[DNF_ss][EXISTS_PROD] >>
  disj2_tac >>
  qspecl_then[`cenv`,`s`,`env`,`exp`,`(s',Rval v)`]mp_tac(CONJUNCT1 evaluate_closed) >>
  simp[] >> strip_tac >> fs[] >>
  rpt (first_x_assum (qspec_then`m` mp_tac)) >>
  rw[] >>
  qmatch_assum_rename_tac`syneq FEMPTY (v_to_Cv m v) w`[] >>
  qmatch_assum_abbrev_tac`Cevaluate FEMPTY FEMPTY sa enva ea (sd,Rval w)` >>
  pop_assum kall_tac >>
  CONV_TAC SWAP_EXISTS_CONV >> qexists_tac`sd` >>
  CONV_TAC SWAP_EXISTS_CONV >> qexists_tac`w` >> rw[] >>
  qmatch_assum_abbrev_tac`Cevaluate_list FEMPTY FEMPTY sb enva eb (se,Rerr err)` >>
  pop_assum kall_tac >>
  qspecl_then[`FEMPTY`,`FEMPTY`,`sb`,`sd`,`enva`,`enva`,`eb`,`(se,Rerr err)`]mp_tac Cevaluate_list_any_syneq_any >>
  `∀v. v ∈ FRANGE enva ⇒ Cclosed FEMPTY v` by (
    unabbrev_all_tac >>
    match_mp_tac IN_FRANGE_alist_to_fmap_suff >>
    fsrw_tac[DNF_ss][MEM_MAP,env_to_Cenv_MAP,EVERY_MEM,FORALL_PROD] >>
    rw[] >> match_mp_tac (CONJUNCT1 v_to_Cv_closed) >> res_tac ) >>
  `(∀v. v ∈ FRANGE sa ⇒ Cclosed FEMPTY v) ∧
   (∀v. v ∈ FRANGE sb ⇒ Cclosed FEMPTY v)` by (
    unabbrev_all_tac >>
    fsrw_tac[DNF_ss][FRANGE_store_to_Cstore,MEM_MAP,EVERY_MEM] >>
    rw[] >> match_mp_tac(CONJUNCT1 v_to_Cv_closed) >> res_tac) >>
  `(free_vars FEMPTY ea ⊆ FDOM enva) ∧
   (BIGUNION (IMAGE (free_vars FEMPTY) (set eb)) ⊆ FDOM enva)` by (
    unabbrev_all_tac >>
    fsrw_tac[DNF_ss][env_to_Cenv_MAP,MAP_MAP_o,SUBSET_DEF,MEM_MAP,FORALL_PROD,EXISTS_PROD]) >>
  qspecl_then[`FEMPTY`,`FEMPTY`,`sa`,`enva`,`ea`,`(sd,Rval w)`]mp_tac(CONJUNCT1 Cevaluate_closed) >>
  simp[] >> strip_tac >>
  fsrw_tac[DNF_ss][FORALL_PROD] >>
  METIS_TAC[fmap_rel_syneq_trans])

val _ = export_theory()
