open HolKernel boolLib boolSimps bossLib quantHeuristicsLib pairTheory listTheory finite_mapTheory pred_setTheory lcsymtacs
open miscTheory intLangTheory compileTerminationTheory
val _ = new_theory"codeEnv"

val label_closures_no_bodies = store_thm("label_closures_no_bodies",
  ``(∀s Ce c. (∀b. b ∈ FRANGE c ⇒ (free_bods c b = {})) ⇒
            (free_bods c (SND (label_closures s Ce)) = {})) ∧
    (∀s Ces c. (∀b. b ∈ FRANGE c ⇒ (free_bods c b = {})) ⇒
            (BIGUNION (IMAGE (free_bods c) (set (SND (label_closures_list s Ces)))) = {})) ∧
    (∀s ns ls ds defs. EVERY (ISR o SND) ds ⇒ EVERY (ISR o SND) (SND (labelise s ns ls ds defs)))``,
  ho_match_mp_tac label_closures_ind >> rw[] >>
  TRY (rw[label_closures_def] >>
       fsrw_tac[ETA_ss][FILTER_EQ_NIL,EVERY_MAP,combinTheory.o_DEF,
                        FOLDL_UNION_BIGUNION,FOLDL_UNION_BIGUNION_paired] >>
       rw[FOLDL_UNION_BIGUNION_paired] >>
       rw[IMAGE_EQ_SING,FORALL_PROD] >>
       fs[EVERY_MEM,FORALL_PROD] >>
       fsrw_tac[QUANT_INST_ss[std_qp]][] >>
       rw[FLOOKUP_DEF] >>
       Cases_on `defs' = []` >> fs[] >> rw[] >>
       fsrw_tac[DNF_ss][FRANGE_DEF] >>
       PROVE_TAC[free_bods_DOMSUB_SUBSET,SUBSET_EMPTY])
  >- (
    rw[Once label_closures_def] >>
    Cases_on `cb` >> fs[label_closures_def] >> rw[] >> fs[] >> rw[] >>
    Cases_on `label_closures s x` >> fs[LET_THM] >>
    rw[] >> fs[] >> rw[] >>
    rw[FLOOKUP_DEF] >>
    fsrw_tac[DNF_ss][FRANGE_DEF] >>
    PROVE_TAC[free_bods_DOMSUB_SUBSET,SUBSET_EMPTY])
  >- (
    rw[label_closures_def] >>
    rw[rich_listTheory.EVERY_REVERSE] >>
    Cases_on `label_closures s Ce` >> fs[LET_THM] >>
    rw[] >> fs[] >>
    first_x_assum (qspec_then `c` mp_tac) >> rw[] >>
    first_x_assum (qspec_then `c` mp_tac) >> rw[] >>
    rw[]))

val subst_labs_def = tDefine "subst_labs"`
  (subst_labs c (CDecl xs) = CDecl xs) ∧
  (subst_labs c (CRaise er) = CRaise er) ∧
  (subst_labs c (CVar x) = CVar x) ∧
  (subst_labs c (CLit l) = CLit l) ∧
  (subst_labs c (CCon n es) = CCon n (MAP (subst_labs c) es)) ∧
  (subst_labs c (CTagEq e n) = CTagEq (subst_labs c e) n) ∧
  (subst_labs c (CProj e n) = CProj (subst_labs c e) n) ∧
  (subst_labs c (CLet xs es e) = CLet xs (MAP (subst_labs c) es) (subst_labs c e)) ∧
  (subst_labs c (CLetfun b xs defs e) = CLetfun b xs (MAP (λ(xs,cb). (xs,subst_lab c cb)) defs) (subst_labs c e)) ∧
  (subst_labs c (CFun xs cb) = CFun xs (subst_lab c cb)) ∧
  (subst_labs c (CCall e es) = CCall (subst_labs c e) (MAP (subst_labs c) es)) ∧
  (subst_labs c (CPrim2 op e1 e2) = CPrim2 op (subst_labs c e1) (subst_labs c e2)) ∧
  (subst_labs c (CIf e1 e2 e3) = CIf (subst_labs c e1) (subst_labs c e2) (subst_labs c e3)) ∧
  (subst_lab c (INR lab) = case FLOOKUP c lab of
    | SOME e => INL (subst_labs (c \\ lab) e)
    | NONE => INL ARB) ∧
  (subst_lab c (INL bod) = INL (subst_labs c bod))`(
  WF_REL_TAC `inv_image ($< LEX $<) (λx. case x of
    | INL (c,e) => (CARD (FDOM c), Cexp_size e)
    | INR (c,b) => (CARD (FDOM c), Cexp3_size b))` >>
  srw_tac[ARITH_ss][Cexp1_size_thm,Cexp4_size_thm] >>
  fsrw_tac[][FLOOKUP_DEF]>>
  MAP_EVERY (fn q => Q.ISPEC_THEN q mp_tac SUM_MAP_MEM_bound)
  [`Cexp_size`,`Cexp2_size`] >>
  rw[] >> res_tac >> fs[Cexp_size_def] >> srw_tac[ARITH_ss][] >>
  Cases_on `CARD (FDOM c)` >> fs[])
val _ = export_rewrites["subst_labs_def"];

val Cclosed_SUBMAP = store_thm("Cclosed_SUBMAP",
  ``∀v. Cclosed c v ⇒ ∀c'. c ⊑ c' ⇒ Cclosed c' v``,
  ho_match_mp_tac Cclosed_ind >>
  rw[] >> rw[Once Cclosed_cases] >- (
    match_mp_tac EVERY_MEM_MONO >>
    qmatch_assum_abbrev_tac `EVERY P vs` >>
    qexists_tac `P` >>
    rw[Abbr`P`] )
  >- (
    imp_res_tac free_vars_SUBMAP >>

val free_vars_subst_labs = store_thm("free_vars_subst_labs",
  ``(∀c e. (free_labs c e ⊆ FDOM c) ⇒ (free_vars FEMPTY (subst_labs c e) = free_vars c e)) ∧
    (∀c b. (cbod_fls c b ⊆ FDOM c) ⇒ (cbod_fvs FEMPTY (subst_lab c b) = cbod_fvs c b))``
  ho_match_mp_tac (theorem"subst_labs_ind") >>
  srw_tac[ETA_ss][FOLDL_UNION_BIGUNION,FOLDL_UNION_BIGUNION_paired] >>
  fs[LIST_TO_SET_MAP] >>
  TRY (
    TRY ( Cases_on `b` >> fs[FOLDL_UNION_BIGUNION_paired,LIST_TO_SET_MAP] ) >>
    rw[Once EXTENSION] >>
    fsrw_tac[DNF_ss][] >>
    fsrw_tac[DNF_ss][EXISTS_PROD] >>
    fsrw_tac[DNF_ss][BIGUNION_SUBSET] >>
    fsrw_tac[DNF_ss][FORALL_PROD] >>
    PROVE_TAC[] ) >>
  Cases_on `FLOOKUP c lab` >> fs[FLOOKUP_DEF] >>
  first_x_assum match_mp_tac >>

  DB.find"DOMSUB_SUB"
  free_labs_DOMSUB_SUBSET

val Cevaluate_subst_labs = store_thm("Cevaluate_subst_labs",
  ``∀c env exp res. Cevaluate c env exp res ⇒
      (∀v. v ∈ FRANGE env ⇒ Cclosed c v) ∧
      free_vars c exp ⊆ FDOM env ∧
      free_labs c exp ⊆ FDOM c ⇒
      ∃res'. Cevaluate FEMPTY env (subst_labs c exp) res' ∧ result_rel (syneq c) res res'``,
  ho_match_mp_tac Cevaluate_nice_strongind >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- (
    srw_tac[ETA_ss]
    [Cevaluate_list_with_Cevaluate
    ,FOLDL_UNION_BIGUNION
    ,Cevaluate_con
    ,Cevaluate_list_with_EVERY] >>
    fsrw_tac[DNF_ss][] >>
    qpat_assum `LENGTH es = LENGTH vs` assume_tac >>
    fs[ZIP_MAP,LAMBDA_PROD,EVERY_MAP] >>
    fsrw_tac[DNF_ss][] >>
    fsrw_tac[DNF_ss][BIGUNION_SUBSET] >>
    fsrw_tac[DNF_ss][EVERY_MEM,FORALL_PROD,MEM_ZIP,MEM_EL] >>
    rw[exists_list_GENLIST] >>
    fs[GSYM RIGHT_EXISTS_IMP_THM] >>
    fs[SKOLEM_THM] >>
    rw[Once syneq_cases] >- (
      pop_assum mp_tac >>
      fsrw_tac[][EL_ZIP,EL_MAP] ) >>
    fsrw_tac[DNF_ss][EVERY2_EVERY,EVERY_MEM,FORALL_PROD,MEM_ZIP] ) >>
  strip_tac >- (
    srw_tac[ETA_ss]
    [Cevaluate_list_with_Cevaluate
    ,FOLDL_UNION_BIGUNION
    ,Cevaluate_con
    ,Cevaluate_list_with_error] >>
    fsrw_tac[DNF_ss][] >>
    rpt (qpat_assum `X < LENGTH es` mp_tac) >>
    rpt strip_tac >>
    fsrw_tac[DNF_ss][BIGUNION_SUBSET,MEM_EL] >>
    qmatch_assum_rename_tac `Cevaluate FEMPTY env (subst_labs c (EL m es)) (Rerr err)`[] >>
    qexists_tac `m` >> fsrw_tac[ARITH_ss][EL_MAP] >>
    PROVE_TAC[]) >>
  strip_tac >- (
    rw[Cevaluate_tageq] >>
    fsrw_tac[DNF_ss][] >>
    fs[Q.SPECL[`c`,`CConv m vs`] syneq_cases] >> rw[] >>
    PROVE_TAC[syneq_refl] ) >>
  strip_tac >- rw[Cevaluate_tageq] >>
  strip_tac >- (
    rw[Cevaluate_proj] >>
    fsrw_tac[DNF_ss][] >>
    fs[Q.SPECL[`c`,`CConv m vs`] syneq_cases] >> rw[] >>
    fsrw_tac[DNF_ss][EVERY2_EVERY,EVERY_MEM,FORALL_PROD] >>
    qpat_assum `LENGTH vs = LENGTH X` assume_tac >>
    fsrw_tac [DNF_ss][MEM_ZIP] >>
    PROVE_TAC[syneq_refl] ) >>
  strip_tac >- rw[Cevaluate_proj] >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rw[Cevaluate_let_cons
      ,FOLDL_UNION_BIGUNION] >>
    fsrw_tac[DNF_ss,ETA_ss][] >>
    disj1_tac >>
    qmatch_assum_rename_tac `syneq c v w`[] >>
    CONV_TAC SWAP_EXISTS_CONV >> qexists_tac `w` >> fs[] >>
    Q.PAT_ABBREV_TAC`ee = CLet ns X Y` >>
    `every_result (Cclosed c) (Rval v)` by (
      match_mp_tac (MP_CANON Cevaluate_closed) >>
      PROVE_TAC[] ) >> fs[] >>
    qmatch_assum_abbrev_tac `P ⇒ Q` >>
    `P` by (
      qunabbrev_tac`P` >>
      fs[] >>
      conj_tac >- (
         match_mp_tac IN_FRANGE_DOMSUB_suff >> rw[] ) >>
      fsrw_tac[DNF_ss][SUBSET_DEF] >>
      PROVE_TAC[] ) >>
    fs[] >>
    qunabbrev_tac`Q` >> fs[] >>
    qmatch_assum_rename_tac `Cevaluate FEMPTY X ee res2` ["X"] >>
    qmatch_assum_abbrev_tac `Cevaluate FEMPTY env1 ee res2` >>
    qspecl_then[`FEMPTY`,`env1`,`ee`,`res2`] mp_tac Cevaluate_free_vars_env >>
    `free_vars FEMPTY ee ⊆ FDOM env1` by (
      unabbrev_all_tac >> fs[FOLDL_UNION_BIGUNION] >>
      fsrw_tac[DNF_ss][SUBSET_DEF,MEM_MAP]

    qspecl_then[`c`,`env`,`ee`,`res2`]
    Cevaluate_any_super_env

    qexists_tac `v` >>
    conj_tac >- rw[] >>
    first_x_assum match_mp_tac >>
    `every_result (Cclosed c) (Rval v)` by (
      match_mp_tac (MP_CANON Cevaluate_closed) >>
      PROVE_TAC[] ) >>
    fs[] >>
    fsrw_tac[DNF_ss][SUBSET_DEF] >>
    metis_tac[IN_FRANGE_DOMSUB_suff] ) >>
 strip_tac >- rw[Cevaluate_let_cons,FOLDL_UNION_BIGUNION] >>
 strip_tac >- (
   rw[] >>
   qpat_assum `LENGTH ns = LENGTH defs` assume_tac >>
   fs[FOLDL2_FUPDATE_LIST_paired,FOLDL_UNION_BIGUNION_paired] >>
   rw[Once Cevaluate_cases] >- (
     rw[MEM_MAP,FORALL_PROD] >>
     qmatch_rename_tac `INR l ≠ subst_lab c cb ∨ P`["P"] >>
     Cases_on `cb` >> fs[] ) >>
   rw[FOLDL2_FUPDATE_LIST_paired] >>
   fs[MAP2_MAP,FST_triple,MAP_ZIP]

(* ugh is this really necessary... << *)

val free_labsv_def = tDefine "free_labsv"`
  (free_labsv (CLitv _) = {}) ∧
  (free_labsv (CConv _ vs) = BIGUNION (IMAGE free_labsv (set vs))) ∧
  (free_labsv (CRecClos _ _ defs _) = IMAGE OUTR (set (FILTER ISR (MAP SND defs))))`
  (WF_REL_TAC `measure Cv_size` >>
   srw_tac[ARITH_ss][Cvs_size_thm] >>
   Q.ISPEC_THEN `Cv_size` imp_res_tac SUM_MAP_MEM_bound >>
   fsrw_tac[ARITH_ss][])
val _ = export_rewrites["free_labsv_def"]

(*
val Cevaluate_free_labs = store_thm("Cevaluate_free_labs",
  ``∀c env exp res. Cevaluate c env exp res ⇒
      ∀v. (res = Rval v) ⇒ free_labsv v ⊆ free_labs exp``,
  ho_match_mp_tac Cevaluate_nice_ind >>
  rw[]
>> *)

(* make closures carry a code environment domain and make sure they are closed with respect to it *)

val Cevaluate_any_code_env = store_thm("Cevaluate_any_code_env",
  ``∀c env exp res. Cevaluate c env exp res ⇒
      (∀l. l ∈ free_labs exp ⇒ l ∈ FDOM c)
      ⇒ ∀c'. (DRESTRICT c' (free_labs exp) = (DRESTRICT c (free_labs exp)))
        ⇒ Cevaluate c' env exp res``
  ho_match_mp_tac Cevaluate_nice_ind >>
  srw_tac[DNF_ss][FOLDL_FUPDATE_LIST,
  Cevaluate_con,Cevaluate_list_with_Cevaluate,
  Cevaluate_list_with_EVERY,
  Cevaluate_list_with_error,
  Cevaluate_tageq,
  Cevaluate_proj] >> fs[] >>
  TRY (
    match_mp_tac EVERY_MEM_MONO >>
    qmatch_assum_abbrev_tac `EVERY P l` >>
    qexists_tac `P` >>
    unabbrev_all_tac >>
    fs[FORALL_PROD] >>
    rw[MEM_ZIP] >>
    first_x_assum (match_mp_tac o MP_CANON) >>
    fsrw_tac[DNF_ss][MEM_EL] >>
    conj_tac >- metis_tac[] >>
    match_mp_tac DRESTRICT_SUBSET >>
    qmatch_assum_abbrev_tac `DRESTRICT c' s = DRESTRICT c s` >>
    qexists_tac `s` >> fs[Abbr`s`] >>
    srw_tac[DNF_ss][SUBSET_DEF,MEM_EL] >>
    PROVE_TAC[] ) >>
  TRY (
    qexists_tac `n` >> fs[] >>
    conj_tac >- (
      first_x_assum (match_mp_tac o MP_CANON) >>
      fs[MEM_EL] >>
      conj_tac >- metis_tac[] >>
      match_mp_tac DRESTRICT_SUBSET >>
      qmatch_assum_abbrev_tac `DRESTRICT c' s = DRESTRICT c s` >>
      qexists_tac `s` >> fs[Abbr`s`] >>
      srw_tac[DNF_ss][SUBSET_DEF,MEM_EL] >>
      PROVE_TAC[] ) >>
    qx_gen_tac `m` >> strip_tac >>
    qpat_assum `∀m. m < n ==> P` (qspec_then `m` mp_tac) >> fs[] >>
    disch_then (Q.X_CHOOSE_THEN `v` strip_assume_tac) >>
    qexists_tac `v` >>
    pop_assum (match_mp_tac o MP_CANON) >>
    `m < LENGTH es` by DECIDE_TAC >>
    fs[MEM_EL] >>
    conj_tac >- metis_tac[] >>
    match_mp_tac DRESTRICT_SUBSET >>
    qmatch_assum_abbrev_tac `DRESTRICT c' s = DRESTRICT c s` >>
    qexists_tac `s` >> fs[Abbr`s`] >>
    srw_tac[DNF_ss][SUBSET_DEF,MEM_EL] >>
    PROVE_TAC[] ) >>
  TRY (
    qexists_tac `m` >>
    PROVE_TAC[] ) >>
  TRY (
    rw[Once Cevaluate_cases] >>
    disj1_tac >>
    first_x_assum (qspec_then `c'` mp_tac) >>
    first_x_assum (qspec_then `c'` mp_tac) >>
    rw[] >>
    `DRESTRICT c' (free_labs exp) = DRESTRICT c (free_labs exp)` by (
      match_mp_tac DRESTRICT_SUBSET >>
      qmatch_assum_abbrev_tac `DRESTRICT c' s = DRESTRICT c s` >>
      qexists_tac `s` >> fs[Abbr`s`] ) >>
    fs[] >>
    map_every qexists_tac [`env'`,`ns'`,`defs`,`n`] >>
    fs[] >>
    rw[Cevaluate_list_with_Cevaluate,
       Cevaluate_list_with_EVERY] >>
    qexists_tac `vs` >> fs[] >>
    conj_tac >- (
      match_mp_tac EVERY_MEM_MONO >>
      qmatch_assum_abbrev_tac `EVERY P l` >>
      qexists_tac `P` >>
      unabbrev_all_tac >>
      fs[FORALL_PROD] >>
      rw[MEM_ZIP] >>
      first_x_assum (match_mp_tac o MP_CANON) >>
      fsrw_tac[DNF_ss][MEM_EL] >>
      conj_tac >- metis_tac[] >>
      match_mp_tac DRESTRICT_SUBSET >>
      qpat_assum `DRESTRICT c' (free_labs exp) = X` kall_tac >>
      qmatch_assum_abbrev_tac `DRESTRICT c' s = DRESTRICT c s` >>
      qexists_tac `s` >> fs[Abbr`s`] >>
      srw_tac[DNF_ss][SUBSET_DEF,MEM_EL] >>
      PROVE_TAC[] ) >>
    qho_match_abbrev_tac `Cevaluate c' exe (f c') res`
    `f c' = f c` by (
      unabbrev_all_tac >>
      Cases_on `cb` >> rw[] >>
      Cclosed_rules
      Cevaluate_closed
    first_x_assum (MATCH_MP_TAC o MP_CANON)


val label_closures_thm1 = store_thm("label_closures_thm1",
  ``(∀s1 Ce1 s2 Ce2. (label_closures s1 Ce1 = (s2,Ce2)) ⇒
      (∀c env res. Cevaluate c env Ce1 res ⇒ Cevaluate (c ⊌ s2.lbods) env Ce2 res)) ∧
    (∀s1 Ces1 s2 Ces2. (label_closures_list s1 Ces1 = (s2,Ces2)) ⇒
      (∀c env res. Cevaluate_list c env Ces1 res ⇒ Cevaluate_list (c ⊌ s2.lbods) env Ces2 res)) ∧
    (∀s ns ls ds defs s2 defs2. (labelise s ns ls ds defs = (s2,defs2)) ⇒
      T)``,
  ho_match_mp_tac label_closures_ind >>
  strip_tac >- rw[label_closures_def,Once Cevaluate_cases] >>
  strip_tac >- rw[label_closures_def,Once Cevaluate_cases] >>
  strip_tac >- rw[label_closures_def,Once Cevaluate_cases] >>
  strip_tac >- rw[label_closures_def,Once Cevaluate_cases] >>
  strip_tac >- (
    rw[label_closures_def,LET_THM] >>
    Cases_on `label_closures_list s1 Ces1` >> fs[] >>
    fs[Cevaluate_con] >> rw[Cevaluate_con]) >>
  strip_tac >- (
    rw[label_closures_def,LET_THM] >>
    Cases_on `label_closures s1 Ce1` >> fs[] >>
    fs[Cevaluate_tageq] >> rw[Cevaluate_tageq] >>
    PROVE_TAC[] ) >>
  strip_tac >- (
    rw[label_closures_def,LET_THM] >>
    Cases_on `label_closures s1 Ce1` >> fs[] >>
    fs[Cevaluate_proj] >> rw[Cevaluate_proj] >>
    PROVE_TAC[] ) >>
  strip_tac >- (
    rw[label_closures_def,LET_THM] >>
    qabbrev_tac`p = label_closures_list s1 Ces1` >>
    PairCases_on `p` >> fs[] >>
    qabbrev_tac`q = label_closures p0 Ce1` >>
    PairCases_on `q` >> fs[] >>
    rw[] >>

    fs[Once(SIMP_RULE(srw_ss())[](Q.SPECL[`c`,`env`,`CLet xs Ces1 Ce1`](CONJUNCT1 Cevaluate_cases)))] >>
    rw[Once(Q.SPECL[`c`,`env`,`CLet xs p1 q1`](CONJUNCT1 Cevaluate_cases))] >>
    fs[markerTheory.Abbrev_def,label_closures_def,LET_THM] >>
    qabbrev_tac`r = label_closures s1 e` >>
    PairCases_on `r` >> fs[] >>
    qabbrev_tac`pp = label_closures_list r0 es` >>
    PairCases_on `pp` >> fs[] >>
    fs[Once(Q.SPECL[`c`,`env|+(n,v)`,`CLet ns es Ce1`](CONJUNCT1 Cevaluate_cases))] >>
    fs[Cevaluate_list_with_Cevaluate,Cevaluate_list_with_cons] >>
    rw[] >> PROVE_TAC[]

    Cases_on `label_closures s1 e` >> fs[]

val _ = export_theory()
