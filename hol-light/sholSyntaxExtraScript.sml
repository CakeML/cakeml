open HolKernel boolLib boolSimps bossLib lcsymtacs sholSyntaxTheory miscLib
open SatisfySimps miscTheory pairTheory listTheory pred_setTheory finite_mapTheory alistTheory sortingTheory stringTheory relationTheory holSyntaxLibTheory
val _ = new_theory"sholSyntaxExtra"

val equation_11 = store_thm("equation_11",
  ``l1 === r1 = l2 === r2 ⇔ l1 = l2 ∧ r1 = r2``,
  rw[equation_def,EQ_IMP_THM])
val _ = export_rewrites["equation_11"]

val vfree_in_equation = store_thm("vfree_in_equation",
  ``VFREE_IN v (s === t) ⇔ (v = Equal (typeof s)) ∨ VFREE_IN v s ∨ VFREE_IN v t``,
  rw[equation_def,VFREE_IN_def] >> metis_tac[])

val type_ind = save_thm("type_ind",
  TypeBase.induction_of``:type``
  |> Q.SPECL[`K T`,`P`,`K T`,`K T`,`EVERY P`,`K T`]
  |> SIMP_RULE std_ss [EVERY_DEF]
  |> UNDISCH_ALL
  |> CONJUNCT1
  |> DISCH_ALL
  |> Q.GEN`P`)

val TYPE_SUBST_tyvars = store_thm("TYPE_SUBST_tyvars",
  ``∀ty tyin tyin'.
    (TYPE_SUBST tyin ty = TYPE_SUBST tyin' ty) ⇔
    ∀x. MEM x (tyvars ty) ⇒
        REV_ASSOCD (Tyvar x) tyin' (Tyvar x) =
        REV_ASSOCD (Tyvar x) tyin  (Tyvar x)``,
  ho_match_mp_tac type_ind >>
  simp[tyvars_def] >>
  conj_tac >- metis_tac[] >>
  Induct >> simp[] >>
  gen_tac >> strip_tac >> fs[] >>
  rpt gen_tac >> EQ_TAC >> strip_tac >> fs[] >>
  fs[MEM_LIST_UNION] >> metis_tac[])

val tvars_VSUBST_subset = store_thm("tvars_VSUBST_subset",
  ``∀t sub. set (tvars (VSUBST sub t)) ⊆ set (tvars t) ∪ set (FLAT (MAP (tvars o FST) sub))``,
  Induct >> simp[VSUBST_def,tvars_def] >- (
    rw[SUBSET_DEF,MEM_FLAT] >>
    Q.ISPECL_THEN[`sub`,`Var s t`,`Var s t`]mp_tac REV_ASSOCD_MEM >>
    rw[] >> fs[tvars_def] >>
    disj2_tac >> HINT_EXISTS_TAC >> simp[MEM_MAP] >>
    HINT_EXISTS_TAC >> simp[] )
  >- (
    fs[SUBSET_DEF,MEM_LIST_UNION] >>
    metis_tac[] )
  >- (
    rw[] >>
    fs[SUBSET_DEF,MEM_LIST_UNION,tvars_def,VSUBST_def] >>
    rw[] >> fs[] >>
    res_tac >> fs[tvars_def] >>
    fs[MEM_FLAT,MEM_MAP,MEM_FILTER,pairTheory.EXISTS_PROD] >>
    fsrw_tac[DNF_ss][] >> metis_tac[]))

val INST_CORE_tvars = store_thm("INST_CORE_tvars",
  ``∀env tyin t tyin'.
    (∀x. MEM x (tvars t) ⇒
         REV_ASSOCD (Tyvar x) tyin' (Tyvar x) =
         REV_ASSOCD (Tyvar x) tyin  (Tyvar x)) ∧
    (∀s s'. MEM (s,s') env ⇒
            ∃x ty. s = Var x ty ∧ s' = Var x (TYPE_SUBST tyin ty))
    ⇒
    INST_CORE env tyin t = INST_CORE env tyin' t``,
  ho_match_mp_tac INST_CORE_ind >>
  strip_tac >- (
    simp[INST_CORE_def] >>
    rw[] >> fs[tvars_def] >>
    metis_tac[TYPE_SUBST_tyvars] ) >>
  strip_tac >- (
    simp[INST_CORE_def] >>
    rw[] >> fs[tvars_def] >>
    metis_tac[TYPE_SUBST_tyvars] ) >>
  strip_tac >- (
    simp[INST_CORE_def] >>
    rw[] >> fs[tvars_def,MEM_LIST_UNION] >>
    rw[] >>
    TRY (
    `INST_CORE env tyin t = INST_CORE env tyin' t` by (
      first_x_assum match_mp_tac >>
      metis_tac[] )) >>
    TRY (
    `INST_CORE env tyin t' = INST_CORE env tyin' t'` by (
      first_x_assum match_mp_tac >>
      metis_tac[] )) >>
    fs[] ) >>
  simp[tvars_def,MEM_LIST_UNION] >>
  simp[INST_CORE_def] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  Q.PAT_ABBREV_TAC`env1 = X::env` >>
  Q.PAT_ABBREV_TAC`env2 = X::env` >>
  Q.PAT_ABBREV_TAC`env3 = X::env` >>
  Q.PAT_ABBREV_TAC`env4 = X::env` >>
  strip_tac >>
  `env1 = env3` by metis_tac[TYPE_SUBST_tyvars] >>
  `INST_CORE env1 tyin t = INST_CORE env1 tyin' t` by (
    first_x_assum match_mp_tac >>
    simp[] >> metis_tac[TYPE_SUBST_tyvars] ) >>
  `TYPE_SUBST tyin' ty = TYPE_SUBST tyin ty` by metis_tac[TYPE_SUBST_tyvars] >>
  Cases_on`IS_RESULT (INST_CORE env3 tyin t)`>>rfs[] >> fs[] >>
  Cases_on`CLASH (INST_CORE env3 tyin' t) = Var x (TYPE_SUBST tyin ty)`>>fs[] >>
  `INST_CORE [] tyin t = INST_CORE [] tyin' t` by (
    first_x_assum match_mp_tac >> simp[] ) >>
  `env2 = env4` by (
    simp[Abbr`env2`,Abbr`env4`]) >>
  fs[] >>
  Q.PAT_ABBREV_TAC`sub = [(Var X Y,Var A Z)]` >>
  `INST_CORE env4 tyin (VSUBST sub t) = INST_CORE env4 tyin' (VSUBST sub t)` by (
    first_x_assum match_mp_tac >>
    rw[] >- (
      imp_res_tac (SIMP_RULE std_ss [SUBSET_DEF] tvars_VSUBST_subset) >>
      fs[Abbr`sub`,tvars_def] ) >>
    metis_tac[] ) >>
  fs[])

val RACONV_welltyped = store_thm("RACONV_welltyped",
  ``∀t1 env t2.
    EVERY (λ(x,y). welltyped x ∧ welltyped y ∧ typeof x = typeof y) env ∧
    welltyped t1 ∧ RACONV env (t1,t2) ⇒
    welltyped t2``,
  Induct >>
  simp[Once RACONV_cases] >- (
    rw[] >> rw[WELLTYPED_CLAUSES] )
  >- (
    rw[WELLTYPED_CLAUSES] >>
    pop_assum mp_tac >>
    simp[Once RACONV_cases] >>
    rw[] >> rw[WELLTYPED_CLAUSES] >>
    metis_tac[RACONV_TYPE,FST,SND] )
  >- (
    rw[Once RACONV_cases] >>
    pop_assum mp_tac >>
    rw[Once RACONV_cases] >>
    rw[WELLTYPED_CLAUSES] >>
    first_x_assum match_mp_tac >>
    qmatch_assum_abbrev_tac`RACONV env' pp` >>
    qexists_tac`env'` >>
    simp[Abbr`env'`]))

val ACONV_welltyped = store_thm("ACONV_welltyped",
  ``∀t1 t2. ACONV t1 t2 ∧ welltyped t1 ⇒ welltyped t2``,
  rw[ACONV_def] >>
  metis_tac[RACONV_welltyped,EVERY_DEF])

val RACONV_TRANS = store_thm("RACONV_TRANS",
  ``∀env tp. RACONV env tp ⇒ ∀vs t. LENGTH vs = LENGTH env ∧ RACONV (ZIP(MAP SND env,vs)) (SND tp,t) ⇒ RACONV (ZIP(MAP FST env,vs)) (FST tp, t)``,
  ho_match_mp_tac RACONV_ind >> simp[RACONV] >>
  conj_tac >- (
    Induct >- simp[ALPHAVARS_def] >>
    Cases >> simp[ALPHAVARS_def] >>
    rw[] >> Cases_on`vs`>>fs[] >>
    Cases_on`t`>>fs[RACONV]>>
    fs[ALPHAVARS_def] >> rw[] >>
    metis_tac[RACONV] ) >>
  conj_tac >- ( rw[] >> Cases_on`t`>>fs[RACONV] ) >>
  conj_tac >- ( rw[] >> Cases_on`t`>>fs[RACONV] ) >>
  rw[] >>
  Cases_on`t`>>fs[RACONV]>>rw[]>>
  metis_tac[LENGTH,ZIP])

val ACONV_TRANS = store_thm("ACONV_TRANS",
  ``∀t1 t2 t3. ACONV t1 t2 ∧ ACONV t2 t3 ⇒ ACONV t1 t3``,
  rw[ACONV_def] >> imp_res_tac RACONV_TRANS >> fs[LENGTH_NIL])

val RACONV_SYM = store_thm("RACONV_SYM",
  ``∀env tp. RACONV env tp ⇒ RACONV (MAP (λ(x,y). (y,x)) env) (SND tp,FST tp)``,
  ho_match_mp_tac RACONV_ind >> simp[] >>
  conj_tac >- (
    Induct >> simp[ALPHAVARS_def,RACONV] >>
    Cases >> simp[] >>
    rw[] >> res_tac >> fs[RACONV]) >>
  simp[RACONV])

val ACONV_SYM = store_thm("ACONV_SYM",
  ``∀t1 t2. ACONV t1 t2 ⇒ ACONV t2 t1``,
  rw[ACONV_def] >> imp_res_tac RACONV_SYM >> fs[])

val bv_names_def = Define`
  bv_names (Var _ _) = [] ∧
  bv_names (Const _ _ _) = [] ∧
  bv_names (Comb s t) = bv_names s ++ bv_names t ∧
  bv_names (Abs x ty t) = x::bv_names t`
val _ = export_rewrites["bv_names_def"]

val dest_var_def = Define`
  dest_var (Var x ty) = (x,ty) ∧
  dest_var _ = ("",Tyvar "")`
val _ = export_rewrites["dest_var_def"]

val INST_CORE_NIL_IS_RESULT = store_thm("INST_CORE_NIL_IS_RESULT",
  ``∀tyin tm. welltyped tm ⇒ IS_RESULT (INST_CORE [] tyin tm)``,
  rw[] >>
  qspecl_then[`sizeof tm`,`tm`,`[]`,`tyin`]mp_tac INST_CORE_HAS_TYPE >>
  simp[] >> rw[] >> rw[] >> fs[REV_ASSOCD])

val TYPE_SUBST_NIL = store_thm("TYPE_SUBST_NIL",
  ``∀ty. TYPE_SUBST [] ty = ty``,
  ho_match_mp_tac type_ind >>
  simp[TYPE_SUBST_def,REV_ASSOCD,EVERY_MEM,LIST_EQ_REWRITE,EL_MAP,MEM_EL,GSYM LEFT_FORALL_IMP_THM])
val _ = export_rewrites["TYPE_SUBST_NIL"]

val VSUBST_NIL = store_thm("VSUBST_NIL",
  ``∀tm. VSUBST [] tm = tm``,
  Induct >> simp[VSUBST_def,REV_ASSOCD])
val _ = export_rewrites["VSUBST_NIL"]

val FLOOKUPD_def = Define`
  FLOOKUPD i v d = case FLOOKUP i v of NONE => d | SOME ty => ty`

val FLOOKUPD_FEMPTY = store_thm("FLOOKUPD_FEMPTY",
  ``FLOOKUPD FEMPTY v d = d``,
  rw[FLOOKUPD_def])
val _ = export_rewrites["FLOOKUPD_FEMPTY"]

val tyinst_def = tDefine "tyinst"`
  tyinst i (Tyvar v) = FLOOKUPD i v (Tyvar v) ∧
  tyinst i (Tyapp s tys) = Tyapp s (MAP (tyinst i) tys)`
  (WF_REL_TAC`measure (type_size o SND)` >>
   gen_tac >> Induct >> simp[term_size_def] >> rw[] >>
   res_tac >> fs[] >> simp[])
val tyinst_def = save_thm("tyinst_def",SIMP_RULE (std_ss++ETA_ss)[]tyinst_def)
val _ = export_rewrites["tyinst_def"]

val tyinst_tyinst = store_thm("tyinst_tyinst",
  ``∀ty i1 i2. tyinst i1 (tyinst i2 ty) = tyinst (tyinst i1 o_f i2 ⊌ i1) ty``,
  ho_match_mp_tac type_ind >>
  simp[] >>
  conj_tac >- (
    simp[FLOOKUPD_def,FLOOKUP_o_f,FLOOKUP_FUNION] >> rw[] >>
    BasicProvers.CASE_TAC >>
    simp[FLOOKUPD_def] ) >>
  simp[MAP_MAP_o,MAP_EQ_f,EVERY_MEM])

val simple_inst_def = Define`
  simple_inst tyin (Var x ty) = Var x (tyinst tyin ty) ∧
  simple_inst tyin (Const x ty g) = Const x (tyinst tyin ty) g ∧
  simple_inst tyin (Comb s t) = Comb (simple_inst tyin s) (simple_inst tyin t) ∧
  simple_inst tyin (Abs x ty t) = Abs x (tyinst tyin ty) (simple_inst tyin t)`
val _ = export_rewrites["simple_inst_def"]

val simple_inst_has_type = store_thm("simple_inst_has_type",
  ``∀tm tyin. welltyped tm ⇒ simple_inst tyin tm has_type (tyinst tyin (typeof tm))``,
  Induct >> rw[]
  >- rw[Once has_type_cases]
  >- rw[Once has_type_cases]
  >- (
    rw[Once has_type_cases] >> fs[] >>
    metis_tac[] )
  >- (
    rw[Once has_type_cases] ))

val simple_inst_compose = store_thm("simple_inst_compose",
  ``∀tm i1 i2. simple_inst i1 (simple_inst i2 tm) = simple_inst (tyinst i1 o_f i2 ⊌ i1) tm``,
  Induct >> simp[tyinst_tyinst])

val bv_names_simple_inst = store_thm("bv_names_simple_inst",
  ``∀tm tyin. bv_names (simple_inst tyin tm) = bv_names tm``,
  Induct >> simp[])
val _ = export_rewrites["bv_names_simple_inst"]

val simple_subst_def = Define`
  (simple_subst σ (Var s ty) = FLOOKUPD σ (s,ty) (Var s ty)) ∧
  (simple_subst σ (Const s ty g) = Const s ty g) ∧
  (simple_subst σ (Comb t1 t2) = Comb (simple_subst σ t1) (simple_subst σ t2)) ∧
  (simple_subst σ (Abs s ty tm) = Abs s ty (simple_subst (σ \\ (s,ty)) tm))`
val _ = export_rewrites["simple_subst_def"]

val simple_subst_FEMPTY = store_thm("simple_subst_FEMPTY",
  ``∀tm. simple_subst FEMPTY tm = tm``,
  Induct >> simp[])
val _ = export_rewrites["simple_subst_FEMPTY"]

val simple_subst_has_type = store_thm("simple_subst_has_type",
  ``∀tm ty.
      tm has_type ty ⇒
      ∀subst.
        FEVERY (λ((x,ty),tm). tm has_type ty) subst ⇒
        simple_subst subst tm has_type ty``,
  ho_match_mp_tac has_type_ind >>
  simp[] >> rw[] >- (
    fs[FLOOKUPD_def,FEVERY_DEF,FLOOKUP_DEF] >>
    rw[] >> res_tac >> fs[] >>
    rw[Once has_type_cases] )
  >- (
    rw[Once has_type_cases] )
  >- (
    rw[Once has_type_cases] >>
    metis_tac[] ) >>
  rw[Once has_type_cases] >>
  first_x_assum match_mp_tac >>
  fs[FEVERY_DEF,DOMSUB_FAPPLY_THM])

val ilist_to_fmap_def = Define`
  ilist_to_fmap ilist = FUN_FMAP (λp. REV_ASSOCD (UNCURRY Var p) ilist (UNCURRY Var p)) {(x,ty) | MEM (Var x ty) (MAP SND ilist)}`

val FLOOKUP_ilist_to_fmap = store_thm("FLOOKUP_ilist_to_fmap",
  ``∀ilist s ty.
    FLOOKUP (ilist_to_fmap ilist) (s,ty) = if MEM (Var s ty) (MAP SND ilist) then SOME (REV_ASSOCD (Var s ty) ilist (Var s ty)) else NONE``,
  rpt gen_tac >>
  simp[ilist_to_fmap_def] >>
  qmatch_abbrev_tac`FLOOKUP (FUN_FMAP f P) Y = X` >>
  `FINITE P` by (
    Q.ISPECL_THEN[`UNCURRY Var`,`P`,`set (MAP SND ilist)`]match_mp_tac FINITE_INJ >>
    simp[INJ_DEF,MEM_MAP,Abbr`P`,EXISTS_PROD,FORALL_PROD] ) >>
  simp[FLOOKUP_DEF,FUN_FMAP_DEF] >>
  simp[Abbr`P`,Abbr`X`,Abbr`Y`,Abbr`f`])

val VSUBST_frees = store_thm("VSUBST_frees",
  ``∀tm il1 il2. (∀n ty. VFREE_IN (Var n ty) tm ⇒
                    (MEM (Var n ty) (MAP SND il1) ⇔ MEM (Var n ty) (MAP SND il2)) ∧
                    (REV_ASSOCD (Var n ty) il1 (Var n ty) = REV_ASSOCD (Var n ty) il2 (Var n ty))) ∧
                 (∀s s'. MEM (s',s) il1 ∨ MEM (s',s) il2 ⇒ ∃x ty. s = Var x ty) ∧
                 ALL_DISTINCT (MAP SND il1) ∧ ALL_DISTINCT (MAP SND il2) ⇒
                 VSUBST il1 tm = VSUBST il2 tm``,
  Induct >> simp[] >> rw[VSUBST_def]
  >- metis_tac[] >- metis_tac[] >>
  qho_match_abbrev_tac`(if P1 then Q1 else R1) = if P2 then Q2 else R2` >>
  `P1 = P2` by (
    rw[Abbr`P1`,Abbr`P2`,EXISTS_MEM,FORALL_PROD] >>
    unabbrev_all_tac >> rw[MEM_FILTER] >> rw[EXISTS_PROD] >>
    rw[EQ_IMP_THM] >> fs[REV_ASSOCD_ALOOKUP] >>
    qmatch_assum_rename_tac`MEM (z,y) ill`[] >>
    `∃x ty. y = Var x ty` by metis_tac[] >>
    first_x_assum(qspecl_then[`x`,`ty`]mp_tac) >>
    (discharge_hyps >- (rw[] >> fs[])) >>
    strip_tac >|[
      pop_assum mp_tac,
      pop_assum (mp_tac o SYM)] >>
    (BasicProvers.CASE_TAC >- (
       fs[ALOOKUP_FAILS,MEM_MAP,UNCURRY,FORALL_PROD] )) >>
    simp[MEM_MAP,EXISTS_PROD] >>
    BasicProvers.VAR_EQ_TAC >>
    asm_simp_tac(srw_ss()++SATISFY_ss)[] >>
    (BasicProvers.CASE_TAC >- (
      fs[ALOOKUP_FAILS,MEM_MAP,UNCURRY,FORALL_PROD,EXISTS_PROD] >> metis_tac[])) >>
    strip_tac >>
    qpat_assum`ALOOKUP ls y = SOME q`mp_tac >>
    qmatch_assum_abbrev_tac`ALOOKUP ls y = SOME q` >>
    `ALL_DISTINCT (MAP FST ls)` by (
      simp[Abbr`ls`,MAP_MAP_o,combinTheory.o_DEF,UNCURRY] >>
      srw_tac[ETA_ss][] ) >>
    strip_tac >>
    `MEM (y,z) ls` by (
      simp[Abbr`ls`,MEM_MAP,EXISTS_PROD] ) >>
    imp_res_tac ALOOKUP_ALL_DISTINCT_MEM >> fs[] >>
    qunabbrev_tac`q` >>
    rpt BasicProvers.VAR_EQ_TAC >>
    qmatch_assum_rename_tac`MEM (q,y) ill`[] >>
    map_every qexists_tac[`q`,`y`] >> simp[] >>
    imp_res_tac ALOOKUP_MEM >>
    fs[MEM_MAP,UNCURRY] ) >>
  qunabbrev_tac`P1` >>
  pop_assum SUBST1_TAC >>
  `t'' = t'` by (
    unabbrev_all_tac >>
    first_x_assum match_mp_tac >>
    simp[MEM_FILTER,MEM_MAP,REV_ASSOCD_FILTER] >>
    conj_tac >- (
      fs[MEM_MAP,EXISTS_PROD] >>
      rw[] >> metis_tac[] ) >>
    conj_tac >- metis_tac[] >>
    simp[MAP_SND_FILTER_NEQ] >>
    simp[FILTER_ALL_DISTINCT]) >>
  map_every qunabbrev_tac[`t''`,`t'`,`z'`,`z`,`R2`,`R1`] >>
  fs[] >>
  qunabbrev_tac`P2` >> rw[] >>
  map_every qunabbrev_tac[`Q1`,`Q2`] >> rw[] >>
  first_x_assum match_mp_tac >>
  qmatch_assum_abbrev_tac`Abbrev (ilist''' = (Var z t,Var s t)::ilist'')` >>
  conj_tac >- (
    simp[Abbr`ilist'''`,Abbr`ilist''''`,REV_ASSOCD] >>
    unabbrev_all_tac >>
    simp[MEM_MAP,MEM_FILTER,EXISTS_PROD,REV_ASSOCD_FILTER] >>
    rw[] >> fs[] >>
    fs[MEM_MAP,EXISTS_PROD] ) >>
  conj_tac >- (
    unabbrev_all_tac >>
    simp[MEM_FILTER] >>
    metis_tac[] ) >>
  unabbrev_all_tac >> simp[] >>
  simp[MEM_MAP,MEM_FILTER,FORALL_PROD] >>
  simp[MAP_SND_FILTER_NEQ,FILTER_ALL_DISTINCT])

val ilist_to_fmap_DOMSUB = store_thm("ilist_to_fmap_DOMSUB",
  ``∀ilist x. ilist_to_fmap ilist \\ x = ilist_to_fmap (FILTER (λ(p,q). q ≠ Var (FST x) (SND x)) ilist)``,
  rw[FLOOKUP_EXT,FUN_EQ_THM,FORALL_PROD] >>
  rw[FLOOKUP_ilist_to_fmap,DOMSUB_FLOOKUP_THM,MEM_MAP,MEM_FILTER,UNCURRY] >>
  rfs[REV_ASSOCD_FILTER] >> rw[] >> fs[FORALL_PROD] >>
  Cases_on`x`>>Cases_on`y`>>fs[]>>rw[]>>metis_tac[])

val VSUBST_simple_subst = store_thm("VSUBST_simple_subst",
  ``∀tm ilist. DISJOINT (set (bv_names tm)) {y | ∃ty u. VFREE_IN (Var y ty) u ∧ MEM u (MAP FST ilist)} ∧
               (∀s s'. MEM (s',s) ilist ⇒ ∃x ty. s = Var x ty)
               ⇒ VSUBST ilist tm = simple_subst (ilist_to_fmap ilist) tm``,
  Induct >- (
    simp[] >>
    simp[VSUBST_def] >>
    simp[FLOOKUPD_def] >>
    simp[FLOOKUP_ilist_to_fmap] >>
    rw[] >>
    rw[REV_ASSOCD_ALOOKUP] >>
    BasicProvers.CASE_TAC >>
    imp_res_tac ALOOKUP_MEM >>
    fs[MEM_MAP,FORALL_PROD,UNCURRY,EXISTS_PROD] >>
    metis_tac[])
  >- simp[VSUBST_def]
  >- (
    simp[VSUBST_def] >> rw[] >>
    first_x_assum match_mp_tac >>
    fs[IN_DISJOINT] >>
    metis_tac[] ) >>
  simp[VSUBST_def] >>
  rpt gen_tac >> strip_tac >>
  BasicProvers.CASE_TAC >- (
    fs[EXISTS_MEM,MEM_FILTER,UNCURRY] >>
    `∃x ty. SND e = Var x ty` by metis_tac[pair_CASES,SND] >>
    first_x_assum(qspecl_then[`t`,`FST e`]mp_tac) >>
    simp[MEM_MAP] >>
    metis_tac[] ) >>
  simp[ilist_to_fmap_DOMSUB] >>
  first_x_assum match_mp_tac >>
  simp[MAP_SND_FILTER_NEQ,MEM_FILTER,MEM_MAP,EXISTS_PROD] >>
  fs[MEM_MAP,EXISTS_PROD,IN_DISJOINT] >>
  metis_tac[])

val dest_tyvar_def = Define`
  dest_tyvar (Tyvar x) = x`
val _ = export_rewrites["dest_tyvar_def"]

val tyin_to_fmap_def = Define`
  tyin_to_fmap tyin = alist_to_fmap (MAP (λ(v,k). (dest_tyvar k,v)) (FILTER (λ(v,k). ∃x. k = Tyvar x) tyin))`

val tyinst_TYPE_SUBST = store_thm("tyinst_TYPE_SUBST",
  ``∀ty tyin. TYPE_SUBST tyin ty = tyinst (tyin_to_fmap tyin) ty``,
  ho_match_mp_tac type_ind >>
  conj_tac >- (
    simp[REV_ASSOCD_ALOOKUP,FLOOKUPD_def,tyin_to_fmap_def] >> rw[] >>
    BasicProvers.CASE_TAC >> BasicProvers.CASE_TAC >>
    TRY (
      fs[ALOOKUP_FAILS] >>
      imp_res_tac ALOOKUP_MEM >>
      fs[MEM_MAP,EXISTS_PROD,MEM_FILTER] >>
      res_tac >> fs[] >>
      metis_tac[dest_tyvar_def] ) >>
    Induct_on`tyin` >> simp[] >>
    Cases >> simp[] >>
    rw[] >> fs[] ) >>
  rw[MAP_EQ_f,EVERY_MEM] >>
  metis_tac[])

val INST_CORE_simple_inst = store_thm("INST_CORE_simple_inst",
  ``∀env tyin tm.
      ALL_DISTINCT (bv_names tm ++ (MAP (FST o dest_var o SND) env)) ∧
      DISJOINT (set(bv_names tm)) {x | ∃ty. VFREE_IN (Var x ty) tm} ∧
      (∀s s'. MEM (s,s') env ⇒ ∃x ty. s = Var x ty ∧ s' = Var x (TYPE_SUBST tyin ty)) ∧
      (∀x ty ty'. VFREE_IN (Var x ty) tm ∧ MEM (Var x ty') (MAP FST env) ⇒ ty' = ty)
      ⇒ INST_CORE env tyin tm = Result (simple_inst (tyin_to_fmap tyin) tm)``,
  ho_match_mp_tac INST_CORE_ind >>
  conj_tac >- (
    simp[INST_CORE_def] >> rpt gen_tac >> strip_tac >>
    qspecl_then[`ty`,`tyin`]mp_tac tyinst_TYPE_SUBST >>
    simp[] >> rw[] >>
    imp_res_tac (REWRITE_RULE[PROVE[]``A ∨ B ⇔ ¬B ⇒ A``]REV_ASSOCD_MEM) >>
    qmatch_assum_abbrev_tac`MEM (p,q) env` >>
    first_x_assum(qspecl_then[`p`,`q`]mp_tac) >>
    simp[Abbr`q`] >> rw[] >>
    fs[MEM_MAP,EXISTS_PROD] >>
    metis_tac[] ) >>
  conj_tac >- (
    simp[INST_CORE_def] >> rw[] >>
    simp[tyinst_TYPE_SUBST]) >>
  conj_tac >- (
    rw[] >>
    rw[INST_CORE_def] >>
    `sres = Result (simple_inst (tyin_to_fmap tyin) tm)` by (
      first_x_assum match_mp_tac >>
      fs[ALL_DISTINCT_APPEND,IN_DISJOINT] >>
      metis_tac[] ) >>
    qunabbrev_tac`sres`>>simp[]>>fs[] >>
    `tres = Result (simple_inst (tyin_to_fmap tyin) tm')` by (
      first_x_assum match_mp_tac >>
      fs[ALL_DISTINCT_APPEND,IN_DISJOINT] >>
      metis_tac[] ) >>
    unabbrev_all_tac >> simp[] ) >>
  rw[] >>
  rw[INST_CORE_def] >>
  fs[] >>
  `tres = Result (simple_inst (tyin_to_fmap tyin) tm)` by (
    first_x_assum match_mp_tac >>
    conj_tac >- fs[ALL_DISTINCT_APPEND] >>
    conj_tac >- ( fs[IN_DISJOINT] >> metis_tac[] ) >>
    conj_tac >- metis_tac[] >>
    qx_genl_tac[`u`,`uy`,`uy'`] >>
    reverse(Cases_on`u=x ∧ uy' = ty`) >- (
      simp[] >> strip_tac >> fs[] >>
      TRY(first_x_assum match_mp_tac >> fs[] >> metis_tac[]) >>
      Cases_on`u≠x`>-metis_tac[]>>fs[]>>
      fs[MEM_MAP,FORALL_PROD,EXISTS_PROD] >>
      metis_tac[dest_var_def,FST] ) >>
    fs[]>>
    fs[MEM_MAP,FORALL_PROD,EXISTS_PROD] >>
    metis_tac[dest_var_def,FST] ) >>
  fs[] >>
  qunabbrev_tac`ty'` >>
  metis_tac[tyinst_TYPE_SUBST])

val INST_simple_inst = store_thm("INST_simple_inst",
  ``∀tyin tm.
      ALL_DISTINCT (bv_names tm) ∧
      DISJOINT (set (bv_names tm)) {x | ∃ty. VFREE_IN (Var x ty) tm}
      ⇒
      INST tyin tm = simple_inst (tyin_to_fmap tyin) tm``,
  rw[INST_def] >>
  qspecl_then[`[]`,`tyin`,`tm`]mp_tac INST_CORE_simple_inst >>
  simp[])

val rename_bvars_def = Define`
  rename_bvars names env (Var s ty) = (names, Var (FLOOKUPD (alist_to_fmap env) (s,ty) s) ty) ∧
  rename_bvars names env (Const s ty g) = (names, Const s ty g) ∧
  (rename_bvars names env (Comb t1 t2) =
     let (names,t1) = rename_bvars names env t1 in
     let (names,t2) = rename_bvars names env t2 in
     (names, Comb t1 t2)) ∧
  (rename_bvars [] env (Abs s ty tm) =
     let (names, tm) = rename_bvars [] env tm in
     (names, Abs s ty tm)) ∧
  (rename_bvars (s'::names) env (Abs s ty tm) =
     let (names,tm) = rename_bvars names (((s,ty),s')::env) tm in
     (names, Abs s' ty tm))`

val FST_rename_bvars = store_thm("FST_rename_bvars",
  ``∀names env tm. LENGTH (bv_names tm) ≤ LENGTH names ⇒ (FST (rename_bvars names env tm) = DROP (LENGTH (bv_names tm)) names)``,
  ho_match_mp_tac (theorem"rename_bvars_ind") >>
  simp[rename_bvars_def] >>
  rw[UNCURRY] >> rw[] >>
  Cases_on`rename_bvars names env tm` >> fs[] >>
  fsrw_tac[ARITH_ss][] >>
  REWRITE_TAC[Once arithmeticTheory.ADD_SYM] >>
  match_mp_tac rich_listTheory.DROP_DROP >>
  simp[])

val rename_bvars_RACONV = store_thm("rename_bvars_RACONV",
  ``∀names env tm.
    LENGTH (bv_names tm) ≤ LENGTH names ∧
    DISJOINT (set (MAP SND env ++ names)) (set (MAP (FST o FST) env ++ bv_names tm)) ∧
    DISJOINT (set (MAP SND env ++ names)) {x | ∃ty. VFREE_IN (Var x ty) tm} ∧
    ALL_DISTINCT (MAP SND env ++ names)
    ⇒ RACONV (MAP (λ((s,ty),s'). (Var s ty, Var s' ty)) env) (tm, SND (rename_bvars names env tm))``,
  ho_match_mp_tac (theorem"rename_bvars_ind") >>
  simp[rename_bvars_def,RACONV] >>
  conj_tac >- (
    gen_tac >>
    Induct >> simp[ALPHAVARS_def] >>
    qx_gen_tac`p` >> PairCases_on`p` >>
    simp[] >> rw[] >>
    simp[FLOOKUPD_def,FLOOKUP_UPDATE] >>
    Cases_on`s=p0`>>simp[]>-(
      Cases_on`ty=p1`>>simp[]>>rw[]>>
      fs[FLOOKUPD_def,IN_DISJOINT,ALL_DISTINCT_APPEND]>>
      metis_tac[]) >>
    BasicProvers.CASE_TAC>-(
      simp[] >>
      first_x_assum(qspecl_then[`s`,`ty`]mp_tac) >>
      simp[FLOOKUPD_def,FLOOKUP_UPDATE] >>
      fs[ALL_DISTINCT_APPEND,IN_DISJOINT] >>
      metis_tac[] ) >>
    imp_res_tac ALOOKUP_MEM >>
    fs[MEM_MAP,EXISTS_PROD,IN_DISJOINT] >>
    Cases_on`x=p2`>>simp[]>-(
      fs[ALL_DISTINCT_APPEND,MEM_MAP,EXISTS_PROD] >>
      metis_tac[] ) >>
    last_x_assum(qspecl_then[`s`,`ty`]mp_tac) >>
    simp[FLOOKUPD_def,FLOOKUP_UPDATE] >>
    fs[ALL_DISTINCT_APPEND,IN_DISJOINT] >>
    metis_tac[] ) >>
  conj_tac >- (
    rw[UNCURRY] >>
    simp[RACONV] >>
    conj_tac >> first_x_assum (match_mp_tac o MP_CANON) >>
    fs[ALL_DISTINCT_APPEND,IN_DISJOINT] >>
    TRY (
      qexists_tac`SND (rename_bvars names env tm)`>>simp[] >>
      qspecl_then[`names`,`env`,`tm`]mp_tac FST_rename_bvars >>
      discharge_hyps >- DECIDE_TAC >> strip_tac >>
      first_assum (assume_tac o Q.AP_TERM`LENGTH`) >>
      fs[LENGTH_DROP] >>
      `LENGTH (bv_names tm) ≤ LENGTH names` by DECIDE_TAC >>
      conj_tac >- DECIDE_TAC >>
      conj_tac >- (
        rw[] >> spose_not_then strip_assume_tac >>
        imp_res_tac rich_listTheory.MEM_DROP >>
        metis_tac[] ) >>
      conj_tac >- (
        rw[] >> spose_not_then strip_assume_tac >>
        imp_res_tac rich_listTheory.MEM_DROP >>
        metis_tac[] ) >>
      conj_tac >- metis_tac[ALL_DISTINCT_DROP] >>
      rw[] >> spose_not_then strip_assume_tac >>
      imp_res_tac rich_listTheory.MEM_DROP >>
      metis_tac[]) >>
    conj_tac >- DECIDE_TAC >> metis_tac[]) >>
  rw[UNCURRY] >>
  rw[RACONV] >>
  first_x_assum match_mp_tac >>
  simp[] >>
  fs[IN_DISJOINT,ALL_DISTINCT_APPEND] >>
  rfs[] >> metis_tac[])

val rename_bvars_ACONV = store_thm("rename_bvars_ACONV",
  ``∀names tm.
    LENGTH (bv_names tm) ≤ LENGTH names ∧ ALL_DISTINCT names ∧
    DISJOINT (set names) {x | MEM x (bv_names tm) ∨ ∃ty. VFREE_IN (Var x ty) tm}
    ⇒
    ACONV tm (SND (rename_bvars names [] tm))``,
  rw[ACONV_def] >>
  qspecl_then[`names`,`[]`,`tm`]mp_tac rename_bvars_RACONV >>
  simp[] >> disch_then match_mp_tac >>
  fs[IN_DISJOINT] >> metis_tac[])

val fresh_def = new_specification("fresh_def",["fresh"],
  IN_INFINITE_NOT_FINITE
  |> Q.ISPECL[`UNIV:string set`,`s:string set`]
  |> REWRITE_RULE[INST_TYPE[alpha|->``:char``]INFINITE_LIST_UNIV,IN_UNIV]
  |> SIMP_RULE(srw_ss())[GSYM RIGHT_EXISTS_IMP_THM]
  |> Q.GEN`s`
  |> SIMP_RULE(srw_ss())[SKOLEM_THM])

val fresh_union = store_thm("fresh_union",
  ``FINITE s ∧ FINITE t ⇒ fresh (s ∪ t) ∉ s ∧ fresh (s ∪ t) ∉ t``,
  metis_tac[fresh_def,FINITE_UNION,IN_UNION])

val fresh_names_exist = store_thm("fresh_names_exist",
  ``∀s n. FINITE (s:string set) ⇒ ∃names. LENGTH names = n ∧ ALL_DISTINCT names ∧ DISJOINT (set names) s``,
  gen_tac >> Induct >> strip_tac
  >- (qexists_tac`[]`>>simp[]) >> rw[] >> fs[] >>
  qexists_tac`fresh (s ∪ set names)::names` >>
  simp[fresh_union])

val FINITE_VFREE_IN = store_thm("FINITE_VFREE_IN",
  ``∀tm. FINITE {x | ∃ty. VFREE_IN (Var x ty) tm}``,
  Induct >> simp[] >- (
    qmatch_assum_abbrev_tac`FINITE s1` >>
    qpat_assum`FINITE s1`mp_tac >>
    qmatch_assum_abbrev_tac`FINITE s2` >>
    strip_tac >>
    qmatch_abbrev_tac`FINITE s3` >>
    qsuff_tac`s3 = s1 ∪ s2` >- metis_tac[FINITE_UNION] >>
    unabbrev_all_tac >> simp[EXTENSION] >> metis_tac[] ) >>
  rw[] >>
  qmatch_assum_abbrev_tac`FINITE a` >>
  qmatch_abbrev_tac`FINITE b` >>
  qsuff_tac`b ⊆ a` >- metis_tac[SUBSET_FINITE] >>
  unabbrev_all_tac >> simp[SUBSET_DEF] >>
  metis_tac[])
val _ = export_rewrites["FINITE_VFREE_IN"]

val FINITE_VFREE_IN_2 = store_thm("FINITE_VFREE_IN_2",
  ``∀tm. FINITE {(x,ty) | VFREE_IN (Var x ty) tm}``,
  Induct >> simp[] >- (
    rw[] >>
    qmatch_abbrev_tac`FINITE x` >>
    qsuff_tac`∃y. x = {y}`>-metis_tac[FINITE_SING] >>
    rw[EXTENSION,Abbr`x`,FORALL_PROD,EXISTS_PROD] >>
    metis_tac[] )
  >- (
    qmatch_assum_abbrev_tac`FINITE s1` >>
    qpat_assum`FINITE s1`mp_tac >>
    qmatch_assum_abbrev_tac`FINITE s2` >>
    strip_tac >>
    qmatch_abbrev_tac`FINITE s3` >>
    qsuff_tac`s3 = s1 ∪ s2` >- metis_tac[FINITE_UNION] >>
    unabbrev_all_tac >> simp[EXTENSION] >> metis_tac[] ) >>
  rw[] >>
  qmatch_assum_abbrev_tac`FINITE a` >>
  qmatch_abbrev_tac`FINITE b` >>
  qsuff_tac`b ⊆ a` >- metis_tac[SUBSET_FINITE] >>
  unabbrev_all_tac >> simp[SUBSET_DEF] >>
  metis_tac[])
val _ = export_rewrites["FINITE_VFREE_IN_2"]

val FINITE_VFREE_IN_list = store_thm("FINITE_VFREE_IN_list",
  ``∀ls. FINITE {x | ∃ty u. VFREE_IN (Var x ty) u ∧ MEM u ls}``,
  Induct >> simp[] >> rw[] >>
  qmatch_assum_abbrev_tac`FINITE s` >>
  qmatch_abbrev_tac`FINITE t` >>
  `t = s ∪ {x | ∃ty. VFREE_IN (Var x ty) h}` by (
    simp[EXTENSION,Abbr`t`,Abbr`s`] >>
    metis_tac[] ) >>
  pop_assum SUBST1_TAC >>
  simp[FINITE_UNION])
val _ = export_rewrites["FINITE_VFREE_IN_list"]

val bv_names_rename_bvars = store_thm("bv_names_rename_bvars",
  ``∀names env tm.
    LENGTH (bv_names tm) ≤ LENGTH names ⇒
    bv_names (SND (rename_bvars names env tm)) = TAKE (LENGTH (bv_names tm)) names``,
  ho_match_mp_tac(theorem"rename_bvars_ind")>>
  simp[rename_bvars_def] >>
  conj_tac >- (
    rw[UNCURRY] >>
    Cases_on`rename_bvars names env tm`>>fs[] >>
    `LENGTH (bv_names tm) ≤ LENGTH names` by DECIDE_TAC >> fs[] >>
    qspecl_then[`names`,`env`,`tm`]mp_tac FST_rename_bvars >>
    rw[] >> fs[] >>
    `LENGTH (bv_names tm') ≤ LENGTH names - LENGTH (bv_names tm)` by DECIDE_TAC >> fs[] >>
    simp[TAKE_SUM] ) >>
  rw[UNCURRY])

val fresh_term_def = new_specification("fresh_term_def",["fresh_term"],
  prove(``∃f. ∀s tm. FINITE s ⇒
                     ACONV tm (f s tm) ∧
                     ALL_DISTINCT (bv_names (f s tm)) ∧
                     DISJOINT (set (bv_names (f s tm))) s``,
    simp[GSYM SKOLEM_THM] >> rw[RIGHT_EXISTS_IMP_THM] >>
    qspecl_then[`s ∪ set (bv_names tm) ∪ {x | ∃ty. VFREE_IN (Var x ty) tm}`,`LENGTH (bv_names tm)`]mp_tac fresh_names_exist >> rw[] >>
    qexists_tac`SND (rename_bvars names [] tm)` >>
    conj_tac >- (
      match_mp_tac rename_bvars_ACONV >>
      fs[IN_DISJOINT] >>
      metis_tac[] ) >>
    qspecl_then[`names`,`[]`,`tm`]mp_tac bv_names_rename_bvars >>
    simp[TAKE_LENGTH_ID_rwt] >>
    fs[IN_DISJOINT] >>
    metis_tac[]))

val tyinst_tyvars1 = store_thm("tyinst_tyvars1",
  ``∀tyin ty tyin'. (∀v. MEM v (tyvars ty) ⇒ FLOOKUPD tyin' v (Tyvar v) = FLOOKUPD tyin v (Tyvar v)) ⇒
         tyinst tyin' ty = tyinst tyin ty``,
  ho_match_mp_tac(theorem"tyinst_ind") >> rw[tyvars_def] >>
  fs[MEM_FOLDR_LIST_UNION] >>
  simp[MAP_EQ_f] >> metis_tac[] )

val tyinst_tyvars = store_thm("tyinst_tyvars",
  ``∀ty tyin tyin'. (∀v. MEM v (tyvars ty) ⇒ FLOOKUPD tyin' v (Tyvar v) = FLOOKUPD tyin v (Tyvar v)) ⇔
         tyinst tyin' ty = tyinst tyin ty``,
  CONV_TAC(STRIP_QUANT_CONV(REWRITE_CONV[EQ_IMP_THM,tyinst_tyvars1])) >>
  ho_match_mp_tac type_ind >>
  simp[tyvars_def] >>
  rw[MEM_FOLDR_LIST_UNION,EVERY_MEM,MAP_EQ_f] >>
  metis_tac[])

val tyvars_tyinst = store_thm("tyvars_tyinst",
  ``∀ty tyin.
    set (tyvars (tyinst tyin ty)) = {v | ∃x. x ∈ set (tyvars ty) ∧ v ∈ set (tyvars (FLOOKUPD tyin x (Tyvar x)))}``,
  ho_match_mp_tac type_ind >>
  simp[tyvars_def] >>
  simp[EVERY_MEM,EXTENSION,MEM_FOLDR_LIST_UNION,MEM_MAP] >>
  rw[] >> metis_tac[])

val tyvars_typeof_subset_tvars = store_thm("tyvars_typeof_subset_tvars",
  ``∀tm ty. tm has_type ty ⇒ set (tyvars ty) ⊆ set (tvars tm)``,
  ho_match_mp_tac has_type_ind >>
  simp[tvars_def] >>
  simp[SUBSET_DEF,MEM_LIST_UNION,tyvars_def] >>
  metis_tac[])

val simple_inst_tvars = store_thm("simple_inst_tvars",
  ``∀tm i1 i2. simple_inst i1 tm = simple_inst i2 tm ⇔ (∀x. MEM x (tvars tm) ⇒ FLOOKUPD i1 x (Tyvar x) = FLOOKUPD i2 x (Tyvar x))``,
  Induct >> simp[tvars_def] >> simp[tyinst_tyvars] >> metis_tac[tyinst_tyvars])

val tyvars_ALL_DISTINCT = store_thm("tyvars_ALL_DISTINCT",
  ``∀ty. ALL_DISTINCT (tyvars ty)``,
  ho_match_mp_tac type_ind >>
  rw[tyvars_def] >>
  Induct_on`l` >> simp[] >>
  rw[ALL_DISTINCT_LIST_UNION])
val _ = export_rewrites["tyvars_ALL_DISTINCT"]

val tvars_ALL_DISTINCT = store_thm("tvars_ALL_DISTINCT",
  ``∀tm. ALL_DISTINCT (tvars tm)``,
  Induct >> simp[tvars_def,ALL_DISTINCT_LIST_UNION])
val _ = export_rewrites["tvars_ALL_DISTINCT"]

val tvars_simple_inst = store_thm("tvars_simple_inst",
  ``∀tm tyin. set (tvars (simple_inst tyin tm)) = {v | ∃x. MEM x (tvars tm) ∧ MEM v (tyvars (FLOOKUPD tyin x (Tyvar x)))}``,
  Induct >> simp[tyvars_tyinst,tvars_def] >>
  fs[EXTENSION] >> metis_tac[] )

val RACONV_tvars = store_thm("RACONV_tvars",
  ``∀env tp. RACONV env tp ⇒ (∀x1 ty1 x2 ty2. MEM (Var x1 ty1,Var x2 ty2) env ⇒ ty1 = ty2) ⇒ tvars (FST tp) = tvars (SND tp)``,
  ho_match_mp_tac RACONV_ind >>
  simp[tvars_def] >>
  conj_tac >- (
    Induct >> simp[ALPHAVARS_def] >>
    Cases >> rw[] >>
    metis_tac[] ) >>
  metis_tac[])

val ACONV_tvars = store_thm("ACONV_tvars",
  ``∀t1 t2. ACONV t1 t2 ⇒ tvars t1 = tvars t2``,
  rw[ACONV_def] >> metis_tac[RACONV_tvars,MEM,FST,SND])

val simple_inst_raconv = store_thm("simple_inst_raconv",
  ``∀env tp. RACONV env tp ⇒
      ∀tyin.
        (∀s s'. MEM (s,s') env ⇒ ∃x x' ty. s = Var x ty ∧ s' = Var x' ty) ∧
        ALL_DISTINCT (MAP (FST o dest_var o FST) env ++ bv_names (FST tp)) ∧
        ALL_DISTINCT (MAP (FST o dest_var o SND) env ++ bv_names (SND tp)) ∧
        (∀x ty. VFREE_IN (Var x ty) (FST tp) ⇒ x ∉ set (bv_names (FST tp)) ∧
            ∀ty'. MEM (Var x ty') (MAP FST env) ⇒ ty' = ty) ∧
        (∀x ty. VFREE_IN (Var x ty) (SND tp) ⇒ x ∉ set (bv_names (SND tp)) ∧
            ∀ty'. MEM (Var x ty') (MAP SND env) ⇒ ty' = ty)
        ⇒
        RACONV (MAP (λ(x,y). (simple_inst tyin x, simple_inst tyin y)) env)
               (simple_inst tyin (FST tp), simple_inst tyin (SND tp))``,
  ho_match_mp_tac RACONV_ind >>
  conj_tac >- (
    Induct >> simp[ALPHAVARS_def,RACONV] >>
    Cases >> simp[] >> rw[] >> rw[] >>
    `∃x x' ty. q = Var x ty ∧ r = Var x' ty` by metis_tac[] >>
    rpt BasicProvers.VAR_EQ_TAC >> simp[] >>
    `ty1 = ty2` by (
      imp_res_tac ALPHAVARS_MEM >>
      metis_tac[FST,SND,term_11] ) >>
    BasicProvers.VAR_EQ_TAC >>
    Cases_on`x1=x` >- fs[] >>
    Cases_on`x2=x'` >- fs[] >>
    asm_simp_tac(srw_ss())[] >>
    last_x_assum mp_tac >>
    simp_tac(srw_ss())[] >>
    simp_tac(srw_ss())[RACONV] >>
    disch_then (match_mp_tac o MP_CANON) >>
    metis_tac[]) >>
  conj_tac >- rw[RACONV] >>
  conj_tac >- (
    rw[RACONV] >>
    first_x_assum match_mp_tac >>
    fs[ALL_DISTINCT_APPEND] >>
    metis_tac[] ) >>
  rw[] >>
  simp_tac(srw_ss())[RACONV] >>
  first_x_assum match_mp_tac >>
  conj_tac >- metis_tac[] >>
  rpt(qpat_assum`ALL_DISTINCT X`mp_tac) >>
  simp_tac(srw_ss())[ALL_DISTINCT_APPEND] >>
  ntac 2 strip_tac >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  conj_tac >>
  rpt gen_tac >> strip_tac >>
  (conj_tac >- metis_tac[]) >>
  fs[MEM_MAP,EXISTS_PROD] >>
  fs[FORALL_PROD,GSYM LEFT_FORALL_IMP_THM] >>
  metis_tac[dest_var_def,FST])

val simple_inst_aconv = store_thm("simple_inst_aconv",
  ``∀t1 t2 tyin. ACONV t1 t2 ∧
      ALL_DISTINCT (bv_names t1) ∧ ALL_DISTINCT (bv_names t2) ∧
      (∀x ty. VFREE_IN (Var x ty) t1 ⇒ x ∉ set (bv_names t1)) ∧
      (∀x ty. VFREE_IN (Var x ty) t2 ⇒ x ∉ set (bv_names t2))
    ⇒
      ACONV (simple_inst tyin t1) (simple_inst tyin t2)``,
  rw[ACONV_def] >>
  qspecl_then[`[]`,`(t1,t2)`]mp_tac simple_inst_raconv >>
  rw[] >> metis_tac[])

val VFREE_IN_simple_inst = store_thm("VFREE_IN_simple_inst",
  ``∀tm tyin.
    ALL_DISTINCT (bv_names tm) ∧
    DISJOINT (set (bv_names tm)) {x | ∃ty. VFREE_IN (Var x ty) tm}
    ⇒
    ∀x ty. VFREE_IN (Var x ty) (simple_inst tyin tm) ⇔ ∃ty0. VFREE_IN (Var x ty0) tm ∧ ty = tyinst tyin ty0``,
  Induct >> simp[]
  >- metis_tac[]
  >- (
    fs[IN_DISJOINT,ALL_DISTINCT_APPEND] >>
    metis_tac[] ) >>
  rw[] >> fs[IN_DISJOINT] >>
  rw[EQ_IMP_THM] >>
  metis_tac[])

val RACONV_VFREE_IN = store_thm("RACONV_VFREE_IN",
  ``∀env tp. RACONV env tp ⇒
      ∀x ty.
      VFREE_IN (Var x ty) (FST tp) ⇒ ∃x' ty'. VFREE_IN (Var x' ty') (SND tp) ∧ ALPHAVARS env (Var x ty,Var x' ty')``,
  ho_match_mp_tac RACONV_ind >>
  simp[] >>
  conj_tac >- ( rw[] >> metis_tac[] ) >>
  rw[ALPHAVARS_def] >>
  metis_tac[])

val ACONV_VFREE_IN = store_thm("ACONV_VFREE_IN",
  ``∀t1 t2 x ty. ACONV t1 t2 ∧ VFREE_IN (Var x ty) t1 ⇒ VFREE_IN (Var x ty) t2``,
  rw[ACONV_def] >> imp_res_tac RACONV_VFREE_IN >> fs[ALPHAVARS_def])

val tvars_VFREE_IN_subset = store_thm("tvars_VFREE_IN_subset",
  ``∀tm s. VFREE_IN s tm ⇒ set (tvars s) ⊆ set (tvars tm)``,
  Induct >> simp[tvars_def] >>
  fs[SUBSET_DEF] >> metis_tac[])

val (subtype_rules,subtype_ind,subtype_cases) = Hol_reln`
  MEM ty ls ⇒ subtype ty (Tyapp n ls)`

val RTC_subtype_Tyvar = store_thm("RTC_subtype_Tyvar",
  ``∀n. subtype^* ty (Tyvar n) ⇒ (ty = Tyvar n)``,
  simp[Once RTC_CASES2] >> simp[subtype_cases])
val _ = export_rewrites["RTC_subtype_Tyvar"]

val RTC_subtype_Tyapp = store_thm("RTC_subtype_Tyapp",
  ``∀ty n ls. subtype^* ty (Tyapp n ls) ⇔ (ty = Tyapp n ls) ∨ ∃a. MEM a ls ∧ subtype^* ty a``,
  simp[Once RTC_CASES2] >> rw[subtype_cases] >> METIS_TAC[] )

val (subterm_rules,subterm_ind,subterm_cases) = Hol_reln`
  subterm s (Comb s t) ∧
  subterm t (Comb s t) ∧
  subterm tm (Abs x ty tm) ∧
  subterm (Var x ty) (Abs x ty tm)`

val RTC_subterm_Var = store_thm("RTC_subterm_Var",
  ``∀t x ty. subterm^* t (Var x ty) ⇔ (t = Var x ty)``,
  simp[Once RTC_CASES2] >> simp[subterm_cases])
val _ = export_rewrites["RTC_subterm_Var"]

val RTC_subterm_Const = store_thm("RTC_subterm_Const",
  ``∀t x ty g. subterm^* t (Const x ty g) ⇔ (t = Const x ty g)``,
  simp[Once RTC_CASES2] >> simp[subterm_cases])
val _ = export_rewrites["RTC_subterm_Const"]

val RTC_subterm_Comb = store_thm("RTC_subterm_Comb",
  ``∀t t1 t2. subterm^* t (Comb t1 t2) ⇔ (t = Comb t1 t2) ∨ subterm^* t t1 ∨ subterm^* t t2``,
  rw[Once RTC_CASES2] >>
  simp[subterm_cases] >>
  METIS_TAC[])

val RTC_subterm_Abs = store_thm("RTC_subterm_Abs",
  ``∀t x ty tm. subterm^* t (Abs x ty tm) ⇔ (t = Abs x ty tm) ∨ (t = Var x ty) ∨ subterm^* t tm``,
  simp[Once RTC_CASES2] >>
  simp[subterm_cases] >>
  METIS_TAC[RTC_subterm_Var])

val _ = export_theory()
