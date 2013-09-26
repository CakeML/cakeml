open HolKernel boolLib boolSimps SatisfySimps bossLib lcsymtacs miscTheory pred_setTheory pairTheory listTheory finite_mapTheory alistTheory sholSyntaxTheory modelSetTheory
val _ = numLib.prefer_num()
val _ = new_theory"sholSemantics"

val discharge_hyps =
  match_mp_tac(PROVE[]``(p ∧ (q ==> r)) ==> ((p ==> q) ==> r)``) >> conj_tac

val discharge_hyps_keep =
  match_mp_tac(PROVE[]``(p ∧ (p ∧ q ==> r)) ==> ((p ==> q) ==> r)``) >> conj_tac

val FEVERY_SUBMAP = store_thm("FEVERY_SUBMAP",
  ``FEVERY P fm /\ fm0 SUBMAP fm ==> FEVERY P fm0``,
  SRW_TAC[][FEVERY_DEF,SUBMAP_DEF])

val FEVERY_ALL_FLOOKUP = store_thm("FEVERY_ALL_FLOOKUP",
  ``∀P f. FEVERY P f ⇔ ∀k v. FLOOKUP f k = SOME v ⇒ P (k,v)``,
  SRW_TAC[][FEVERY_DEF,FLOOKUP_DEF])

val MEM_LIST_INSERT = store_thm("MEM_LIST_INSERT",
  ``∀l x. set (LIST_INSERT x l) = x INSERT set l``,
  Induct >> simp[LIST_INSERT_def] >> rw[] >>
  rw[EXTENSION] >> metis_tac[])

val MEM_LIST_UNION = store_thm("MEM_LIST_UNION",
  ``∀l1 l2. set (LIST_UNION l1 l2) = set l1 ∪ set l2``,
  Induct >> fs[LIST_UNION_def,MEM_LIST_INSERT] >>
  rw[EXTENSION] >> metis_tac[])

val MEM_FOLDR_LIST_UNION = store_thm("MEM_FOLDR_LIST_UNION",
  ``∀ls x f b. MEM x (FOLDR (λx y. LIST_UNION (f x) y) b ls) ⇔ MEM x b ∨ ∃y. MEM y ls ∧ MEM x (f y)``,
  Induct >> simp[MEM_LIST_UNION] >> metis_tac[])

val ALL_DISTINCT_LIST_UNION = store_thm("ALL_DISTINCT_LIST_UNION",
  ``∀l1 l2. ALL_DISTINCT l2 ⇒ ALL_DISTINCT (LIST_UNION l1 l2)``,
  Induct >> fs[LIST_UNION_def,LIST_INSERT_def] >> rw[])

val ALOOKUP_ALL_DISTINCT_EL = store_thm("ALOOKUP_ALL_DISTINCT_EL",
  ``∀ls n. n < LENGTH ls ∧ ALL_DISTINCT (MAP FST ls) ⇒ ALOOKUP ls (FST (EL n ls)) = SOME (SND (EL n ls))``,
  Induct >> simp[] >>
  Cases >> simp[] >>
  Cases >> simp[] >>
  rw[] >> fs[MEM_MAP] >>
  metis_tac[MEM_EL])

val find_index_is_MEM = store_thm("find_index_is_MEM",
  ``∀x ls n j. find_index x ls n = SOME j ⇒ MEM x ls``,
  metis_tac[find_index_NOT_MEM,optionTheory.NOT_SOME_NONE])

val find_index_MAP_inj = store_thm("find_index_MAP_inj",
  ``∀ls x n f. (∀y. MEM y ls ⇒ (f x = f y) ⇒ x = y) ⇒ (find_index (f x) (MAP f ls) n = find_index x ls n)``,
  Induct >- simp[find_index_def] >>
  rw[] >> rw[find_index_def] >>
  metis_tac[])

val find_index_shift_0 = store_thm("find_index_shift_0",
  ``∀ls x k. find_index x ls k = OPTION_MAP (λx. x + k) (find_index x ls 0)``,
  Induct >> simp_tac(srw_ss())[find_index_def] >>
  rpt gen_tac >>
  Cases_on`h=x` >- (
    BasicProvers.VAR_EQ_TAC >>
    simp_tac(srw_ss())[] ) >>
  pop_assum mp_tac >>
  simp_tac(srw_ss())[] >>
  strip_tac >>
  first_assum(qspecl_then[`x`,`k+1`]mp_tac) >>
  first_x_assum(qspecl_then[`x`,`1`]mp_tac) >>
  rw[] >>
  Cases_on`find_index x ls 0`>>rw[] >>
  simp[])

val find_index_shift = store_thm("find_index_shift",
  ``∀ls x k j. (find_index x ls k = SOME j) ⇒ j ≥ k ∧ ∀n. find_index x ls n = SOME (j-k+n)``,
  Induct >> simp[find_index_def] >> rw[] >> res_tac >> fsrw_tac[ARITH_ss][])

val LIST_UNION_NIL = store_thm("LIST_UNION_NIL",
  ``∀l2. (LIST_UNION [] l2 = l2)``,
  simp[LIST_UNION_def] )
val _ = export_rewrites["LIST_UNION_NIL"]

val set_LIST_UNION = store_thm("set_LIST_UNION",
  ``∀l1 l2. set (LIST_UNION l1 l2) = set l1 ∪ set l2``,
  rw[EXTENSION,MEM_LIST_UNION])
val _ = export_rewrites["set_LIST_UNION"]

val vfree_in_equation = store_thm("vfree_in_equation",
  ``VFREE_IN v (s === t) ⇔ (v = Equal (typeof s)) ∨ VFREE_IN v s ∨ VFREE_IN v t``,
  rw[equation_def,VFREE_IN_def] >> metis_tac[])

val type_ind =
  TypeBase.induction_of``:type``
  |> Q.SPECL[`K T`,`P`,`K T`,`K T`,`EVERY P`]
  |> SIMP_RULE std_ss [EVERY_DEF]
  |> UNDISCH_ALL
  |> CONJUNCT1
  |> DISCH_ALL
  |> Q.GEN`P`

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

val ALPHAVARS_MEM = store_thm("ALPHAVARS_MEM",
  ``∀env tp. ALPHAVARS env tp ⇒ MEM tp env ∨ (FST tp = SND tp)``,
   Induct >> simp[ALPHAVARS_def] >> rw[] >> res_tac >> simp[])

val INST_CORE_NIL_IS_RESULT = store_thm("INST_CORE_NIL_IS_RESULT",
  ``∀tyin tm. welltyped tm ⇒ IS_RESULT (INST_CORE [] tyin tm)``,
  rw[] >>
  qspecl_then[`sizeof tm`,`tm`,`[]`,`tyin`]mp_tac INST_CORE_HAS_TYPE >>
  simp[] >> rw[] >> rw[] >> fs[REV_ASSOCD])

val NOT_IS_CLASH_IS_RESULT = store_thm("NOT_IS_CLASH_IS_RESULT",
  ``∀x. IS_CLASH x ⇔ ¬IS_RESULT x``,
  Cases >> simp[])

val RESULT_eq_suff = prove(
  ``x = Result y ⇒ RESULT x = y``,
  Cases_on`x`>>simp[])

val TYPE_SUBST_NIL = store_thm("TYPE_SUBST_NIL",
  ``∀ty. TYPE_SUBST [] ty = ty``,
  ho_match_mp_tac type_ind >>
  simp[TYPE_SUBST_def,REV_ASSOCD,EVERY_MEM,LIST_EQ_REWRITE,EL_MAP,MEM_EL,GSYM LEFT_FORALL_IMP_THM])
val _ = export_rewrites["TYPE_SUBST_NIL"]

val VSUBST_NIL = store_thm("VSUBST_NIL",
  ``∀tm. VSUBST [] tm = tm``,
  Induct >> simp[VSUBST_def,REV_ASSOCD])
val _ = export_rewrites["VSUBST_NIL"]

val REV_ASSOCD_ALOOKUP = store_thm("REV_ASSOCD_ALOOKUP",
  ``∀ls x d. REV_ASSOCD x ls d = case ALOOKUP (MAP (λ(x,y). (y,x)) ls) x of NONE => d | SOME y => y``,
  Induct >> simp[REV_ASSOCD] >>
  Cases >> simp[REV_ASSOCD] >> rw[])

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

val GENLIST_NIL = store_thm("GENLIST_NIL",
  ``∀f n. (GENLIST f n = []) ⇔ n = 0``,
  GEN_TAC THEN Induct THEN SRW_TAC[][GENLIST_CONS])

val MAP_SND_FILTER_NEQ = store_thm("MAP_SND_FILTER_NEQ",
  ``MAP SND (FILTER (λ(x,y). y ≠ z) ls) =
    FILTER ($<> z) (MAP SND ls)``,
  Q.ISPECL_THEN[`$<> z`,`SND:('b#'a)->'a`,`ls`]mp_tac rich_listTheory.FILTER_MAP >> rw[] >>
  AP_TERM_TAC >> AP_THM_TAC >> AP_TERM_TAC >>
  simp[FUN_EQ_THM,FORALL_PROD,EQ_IMP_THM])

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

val ALL_DISTINCT_DROP = store_thm("ALL_DISTINCT_DROP",
  ``∀ls n. ALL_DISTINCT ls ⇒ ALL_DISTINCT (DROP n ls)``,
  Induct >> simp[] >> rw[])

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

val type_valuation_def = Define`
  type_valuation τ ⇔ ∀x. x ∈ FRANGE τ ⇒ ∃y. y <: x`

val type_valuation_FEMPTY = store_thm("type_valuation_FEMPTY",
  ``type_valuation FEMPTY``, rw[type_valuation_def])
val _ = export_rewrites["type_valuation_FEMPTY"]

val (semantics_rules,semantics_ind,semantics_cases) = xHol_reln"semantics"`
  (FLOOKUP τ s = SOME m ⇒ typeset τ (Tyvar s) m) ∧

  (typeset τ (Tyapp (Typrim "bool" 0) []) boolset) ∧

  (typeset τ x mx ∧ typeset τ y my
   ⇒
   typeset τ (Tyapp (Typrim "->" 2) [x;y]) (funspace mx my)) ∧

  (p = fresh_term {} p0 ∧ closed p0 ∧
   LENGTH (tvars p) = LENGTH args ∧
   tyin = alist_to_fmap(ZIP (tvars p, args)) ∧
   p has_type Fun rty Bool ∧
   (∀τ. type_valuation τ ∧ set (tvars (simple_inst tyin p)) ⊆ FDOM τ ⇒
      ∃mrty mp w.
        typeset τ (tyinst tyin rty) mrty ∧
        semantics FEMPTY τ (simple_inst tyin p) mp ∧
        w <: mrty ∧ holds mp w) ∧
   typeset τ (tyinst tyin rty) mrty ∧
   semantics FEMPTY τ (simple_inst tyin p) mp ∧
   w <: mrty ∧ holds mp w
   ⇒
   typeset τ (Tyapp (Tydefined op p0) args) (mrty suchthat holds mp)) ∧

  (FLOOKUP σ (s,ty) = SOME m
   ⇒
   semantics σ τ (Var s ty) m) ∧

  (typeset τ ty mty
   ⇒
   semantics σ τ (Const "=" (Fun ty (Fun ty Bool)) Prim)
    (abstract mty (funspace mty boolset)
       (λx. abstract mty boolset (λy. boolean (x = y))))) ∧

  (typeset τ ty mty
   ⇒
   semantics σ τ (Const "@" (Fun (Fun ty Bool) ty) Prim)
     (abstract (funspace mty boolset) mty
       (λp. let mp = (mty suchthat holds p) in
            ch (if ∃x. x <: mp then mp else mty)))) ∧

  (t = fresh_term {} t0 ∧ welltyped t ∧ closed t ∧
   set(tvars t) ⊆ set (tyvars (typeof t)) ∧
   tyinst tyin (typeof t) = ty ∧
   semantics FEMPTY τ (simple_inst tyin t) mt
   ⇒
   semantics σ τ (Const s ty (Defined t0)) mt) ∧

  (typeset τ (Tyapp (Tydefined op p0) args) maty ∧
   p = fresh_term {} p0 ∧
   tyin = alist_to_fmap(ZIP (tvars p, args)) ∧
   simple_inst tyin p has_type Fun rty Bool ∧
   typeset τ rty mrty
   ⇒
   semantics σ τ (Const s (Fun (Tyapp (Tydefined op p0) args) rty) (Tyrep op p0))
    (abstract maty mrty (λx. x))) ∧

  (typeset τ (Tyapp (Tydefined op p0) args) maty ∧
   p = fresh_term {} p0 ∧
   tyin = alist_to_fmap(ZIP (tvars p, args)) ∧
   simple_inst tyin p has_type Fun rty Bool ∧
   typeset τ rty mrty ∧
   semantics FEMPTY τ (simple_inst tyin p) mp
   ⇒
   semantics σ τ (Const s (Fun rty (Tyapp (Tydefined op p0) args)) (Tyabs op p0))
    (abstract mrty maty (λx. if holds mp x then x else ch maty))) ∧

  (semantics σ τ t1 m1 ∧
   semantics σ τ t2 m2 ∧
   welltyped (Comb t1 t2)
   ⇒
   semantics σ τ (Comb t1 t2) (apply m1 m2)) ∧

  (typeset τ ty mty ∧
   b has_type tyb ∧
   typeset τ tyb mtyb ∧
   (∀m. m <: mty ⇒ (mb m) <: mtyb ∧ semantics (σ|+((s,ty),m)) τ b (mb m))
   ⇒
   semantics σ τ (Abs s ty b) (abstract mty mtyb mb))`

val typeset_Bool = store_thm("typeset_Bool",
  ``typeset τ Bool ty ⇔ ty = boolset``,
  simp[Once semantics_cases])
val _ = export_rewrites["typeset_Bool"]

val term_valuation_def = Define`
  term_valuation τ σ ⇔
    FEVERY (λ(v,m). ∃mty. typeset τ (SND v) mty ∧ m <: mty) σ`

val term_valuation_FEMPTY = store_thm("term_valuation_FEMPTY",
  ``term_valuation τ FEMPTY``,
  rw[term_valuation_def,FEVERY_DEF])
val _ = export_rewrites["term_valuation_FEMPTY"]

val term_valuation_FUPDATE = store_thm("term_valuation_FUPDATE",
  ``∀τ σ kv mty. term_valuation τ σ ∧ typeset τ (SND(FST kv)) mty ∧ (SND kv) <: mty ⇒ term_valuation τ (σ |+ kv)``,
  rw[term_valuation_def] >>
  Cases_on`kv` >>
  match_mp_tac(CONJUNCT2 FEVERY_STRENGTHEN_THM) >>
  fs[] >> metis_tac[])

val term_valuation_FUPDATE_LIST = store_thm("term_valuation_FUPDATE_LIST",
  ``∀ls τ σ. term_valuation τ σ ∧ EVERY (λ(v,m). ∃mty. typeset τ (SND v) mty ∧ m <: mty) ls ⇒ term_valuation τ (σ |++ ls)``,
  Induct >> simp[FUPDATE_LIST_THM] >>
  Cases>>fs[]>>rw[]>>
  first_x_assum match_mp_tac >> rw[] >>
  match_mp_tac term_valuation_FUPDATE >>
  rw[] >> metis_tac[])

val type_valuation_reduce = store_thm("type_valuation_reduce",
  ``∀τ τ'. type_valuation τ' ∧ τ ⊑ τ' ⇒ type_valuation τ``,
  rw[type_valuation_def,IN_FRANGE,SUBMAP_DEF] >> metis_tac[])

val term_valuation_reduce = store_thm("term_valuation_reduce",
  ``∀τ σ σ'. term_valuation τ σ' ∧ σ ⊑ σ' ⇒ term_valuation τ σ``,
  metis_tac[term_valuation_def,FEVERY_SUBMAP])

val typeset_inhabited = store_thm("typeset_inhabited",
  ``∀ty τ mty. type_valuation τ ∧ typeset τ ty mty ⇒ ∃m. m <: mty``,
  ho_match_mp_tac type_ind >>
  conj_tac >- (
    simp[type_valuation_def] >>
    simp[Once semantics_cases] >>
    simp[FLOOKUP_DEF,FRANGE_DEF] >>
    metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  simp[Once semantics_cases] >>
  rw[] >- metis_tac[BOOLEAN_IN_BOOLSET]
  >- (
    match_mp_tac FUNSPACE_INHABITED >>
    fs[] >> metis_tac[] ) >>
  simp[suchthat_def] >>
  metis_tac[] )

val semantics_11 = store_thm("semantics_11",
  ``(∀τ ty mty. typeset τ ty mty ⇒
        ∀mty'. type_valuation τ ∧ typeset τ ty mty' ⇒ mty' = mty) ∧
    (∀σ τ t mt. semantics σ τ t mt ⇒
        ∀mt'. type_valuation τ ∧ semantics σ τ t mt' ⇒ mt' = mt)``,
  ho_match_mp_tac semantics_ind >>
  conj_tac >- simp[Once semantics_cases] >>
  conj_tac >- simp[Once semantics_cases] >>
  conj_tac >- (
    rpt gen_tac >> strip_tac >>
    simp[Once semantics_cases] >>
    PROVE_TAC[] ) >>
  conj_tac >- (
    rpt gen_tac >> strip_tac >>
    simp[Once semantics_cases] >> rw[] >>
    imp_res_tac WELLTYPED_LEMMA >>
    fs[] ) >>
  conj_tac >- simp[Once semantics_cases] >>
  conj_tac >- (
    rpt gen_tac >> strip_tac >>
    simp[Once semantics_cases] >> rw[] >> rw[]) >>
  conj_tac >- (
    rpt gen_tac >> strip_tac >>
    simp[Once semantics_cases] >> rw[] >> rw[]) >>
  conj_tac >- (
    rpt gen_tac >> strip_tac >>
    simp[Once semantics_cases] >> rw[] >> rw[] >>
    qmatch_assum_abbrev_tac`welltyped t` >>
    `simple_inst tyin t = simple_inst tyin' t` by (
      simp[simple_inst_tvars] >>
      fs[SUBSET_DEF] >>
      metis_tac[tyinst_tyvars] ) >>
    fs[] ) >>
  conj_tac >- (
    rpt gen_tac >> strip_tac >>
    simp_tac std_ss [Once semantics_cases] >>
    rw[] >> fs[]) >>
  conj_tac >- (
    rpt gen_tac >> strip_tac >>
    simp_tac (srw_ss()) [Once semantics_cases] >>
    rpt strip_tac >>
    BasicProvers.VAR_EQ_TAC >> fs[]) >>
  conj_tac >- (
    rpt gen_tac >> strip_tac >>
    simp_tac std_ss [Once semantics_cases] >>
    simp_tac (srw_ss()) [] >>
    rw[] >> metis_tac[] ) >>
  rpt gen_tac >>
  strip_tac >>
  simp_tac std_ss [Once semantics_cases] >>
  rw[] >>
  imp_res_tac WELLTYPED_LEMMA >>
  rw[] >>
  match_mp_tac ABSTRACT_EQ >>
  conj_tac >- metis_tac[typeset_inhabited] >>
  fs[] >> res_tac >> fs[])

val typeset_tyvars = store_thm("typeset_tyvars",
  ``(∀τ1 ty m. typeset τ1 ty m ⇒ ∀τ2. (∀x. x ∈ set(tyvars ty) ∧ x ∈ FDOM τ1 ⇒ FLOOKUP τ1 x = FLOOKUP τ2 x) ⇒ typeset τ2 ty m) ∧
    (∀σ τ1 tm m. semantics σ τ1 tm m ⇒ ∀τ2. (∀x. x ∈ set(tvars tm) ∧ x ∈ FDOM τ1 ⇒ FLOOKUP τ1 x = FLOOKUP τ2 x) ⇒ semantics σ τ2 tm m)``,
  ho_match_mp_tac (theorem"semantics_strongind") >> simp[] >>
  conj_tac >- (
    ntac 2 (simp[Once semantics_cases]) >>
    simp[FLOOKUP_DEF,SUBMAP_DEF,tyvars_def] ) >>
  conj_tac >- (
    rpt gen_tac >> strip_tac >>
    simp[Once semantics_cases] >> rw[] >>
    fs[tyvars_def,MEM_LIST_UNION] >>
    metis_tac[] ) >>
  conj_tac >- (
    rpt gen_tac >> strip_tac >>
    simp[Once semantics_cases] >> rw[] >>
    fs[tyvars_def,MEM_LIST_UNION] >>
    qmatch_assum_rename_tac`w <: mrty`[] >>
    qmatch_assum_rename_tac`holds mp w`[] >>
    map_every qexists_tac[`mp`,`mrty`,`rty`,`w`] >> simp[] >>
    fs[MEM_FOLDR_LIST_UNION] >>
    conj_tac >- metis_tac[] >>
    conj_tac >- (
      first_x_assum match_mp_tac >>
      simp[tyvars_tyinst] >>
      simp[FLOOKUPD_def] >>
      rw[] >>
      first_x_assum match_mp_tac >>
      rw[] >>
      ntac 2 (pop_assum mp_tac) >>
      BasicProvers.CASE_TAC >- (
        fs[ALOOKUP_FAILS] >>
        rfs[MEM_ZIP] >>
        imp_res_tac tyvars_typeof_subset_tvars >>
        fs[SUBSET_DEF,tyvars_def] >>
        metis_tac[MEM_EL] ) >>
      imp_res_tac ALOOKUP_MEM >>
      rfs[MEM_ZIP] >>
      imp_res_tac tyvars_typeof_subset_tvars >>
      fs[SUBSET_DEF,tyvars_def] >>
      metis_tac[MEM_EL] ) >>
    first_x_assum match_mp_tac >>
    simp[tvars_simple_inst] >>
    simp[FLOOKUPD_def] >>
    rw[] >>
    first_x_assum match_mp_tac >>
    rw[] >>
    ntac 2 (pop_assum mp_tac) >>
    BasicProvers.CASE_TAC >- (
      fs[ALOOKUP_FAILS] >>
      rfs[MEM_ZIP] >>
      imp_res_tac tyvars_typeof_subset_tvars >>
      fs[SUBSET_DEF,tyvars_def] >>
      metis_tac[MEM_EL] ) >>
    imp_res_tac ALOOKUP_MEM >>
    rfs[MEM_ZIP] >>
    imp_res_tac tyvars_typeof_subset_tvars >>
    fs[SUBSET_DEF,tyvars_def] >>
    metis_tac[MEM_EL] ) >>
  conj_tac >- (
    simp[tvars_def] >>
    simp[Once semantics_cases] ) >>
  conj_tac >- (
    rw[tvars_def,tyvars_def] >>
    simp[Once semantics_cases] >>
    metis_tac[] ) >>
  conj_tac >- (
    rw[tvars_def,tyvars_def] >>
    simp[Once semantics_cases] >>
    metis_tac[] ) >>
  conj_tac >- (
    rw[tvars_def,tyvars_def] >>
    simp[Once semantics_cases] >>
    qexists_tac`tyin` >> rw[] >>
    first_x_assum match_mp_tac >>
    fs[tyvars_tyinst,tvars_simple_inst] >>
    rw[] >>
    first_x_assum match_mp_tac >>
    fs[SUBSET_DEF] >>
    metis_tac[] ) >>
  conj_tac >- (
    rw[tvars_def,tyvars_def] >>
    simp[Once semantics_cases] >>
    metis_tac[] ) >>
  conj_tac >- (
    rw[tvars_def,tyvars_def] >>
    simp[Once semantics_cases] >>
    qpat_assum`typeset X Y m`(strip_assume_tac o SIMP_RULE(srw_ss())[Once semantics_cases]) >>
    map_every qexists_tac[`m`,`m'`,`m''`] >>
    rw[] >>
    first_x_assum match_mp_tac >>
    rw[] >>
    first_x_assum match_mp_tac >>
    rw[MEM_FOLDR_LIST_UNION] >>
    fs[tvars_simple_inst,FLOOKUPD_def] >>
    ntac 2 (pop_assum mp_tac) >>
    BasicProvers.CASE_TAC >- (
      fs[ALOOKUP_FAILS,tyvars_def] >>
      rfs[MEM_ZIP] >>
      imp_res_tac tyvars_typeof_subset_tvars >>
      fs[SUBSET_DEF,tyvars_def] >>
      metis_tac[MEM_EL] ) >>
    imp_res_tac ALOOKUP_MEM >>
    rfs[MEM_ZIP] >>
    imp_res_tac tyvars_typeof_subset_tvars >>
    fs[SUBSET_DEF,tyvars_def] >>
    metis_tac[MEM_EL] ) >>
  conj_tac >- (
    rw[tvars_def] >>
    simp[Once semantics_cases] >>
    metis_tac[] ) >>
  rw[tvars_def] >>
  simp[Once semantics_cases] >>
  map_every qexists_tac[`mb`,`m`,`m'`,`ty'`] >>
  rw[] >>
  first_x_assum match_mp_tac >>
  rw[] >>
  imp_res_tac tyvars_typeof_subset_tvars >>
  fs[SUBSET_DEF])

val typeset_closes_over = store_thm("typeset_closes_over",
  ``(∀τ ty m. typeset τ ty m ⇒ type_valuation τ ⇒ set (tyvars ty) ⊆ FDOM τ) ∧
    (∀σ τ tm m. semantics σ τ tm m ⇒
      type_valuation τ ∧ (∀s m ty. (s,ty) ∈ FDOM σ ⇒ set (tyvars ty) ⊆ FDOM τ)
      ⇒ set (tvars tm) ⊆ FDOM τ)``,
  ho_match_mp_tac (theorem"semantics_strongind") >>
  simp[tyvars_def] >>
  conj_tac >- ( rw[Once semantics_cases,FLOOKUP_DEF] ) >>
  conj_tac >- (
    rpt gen_tac >> strip_tac >> strip_tac >>
    fs[SUBSET_DEF,MEM_LIST_UNION,MEM_FOLDR_LIST_UNION,EVERY_MEM] >>
    fs[SIMP_RULE std_ss[EXTENSION]tyvars_tyinst] >>
    fs[GSYM LEFT_FORALL_IMP_THM] >> rw[] >>
    qmatch_assum_abbrev_tac`∀x. MEM x (tvars (simple_inst tyin tm)) ⇒ x ∈ FDOM τ` >>
    qspecl_then[`tm`,`tyin`]mp_tac tvars_simple_inst >>
    simp[EXTENSION,PROVE[]``¬P ∨ ¬Q ⇔ Q ⇒ ¬P``] >>
    rw[] >>
    `∃n. n < LENGTH args ∧ y = EL n args` by metis_tac[MEM_EL] >>
    first_x_assum match_mp_tac >> simp[] >>
    qexists_tac`EL n (tvars tm)` >>
    conj_tac >- metis_tac[MEM_EL] >>
    simp[FLOOKUPD_def,Abbr`tyin`] >>
    BasicProvers.CASE_TAC >- (
      fs[ALOOKUP_FAILS] >>
      rfs[MEM_ZIP] >>
      metis_tac[] ) >>
    Q.ISPECL_THEN[`ZIP(tvars tm,args)`,`n`]mp_tac ALOOKUP_ALL_DISTINCT_EL >>
    discharge_hyps >- simp[MAP_ZIP] >> rw[EL_ZIP]) >>
  conj_tac >- (
    rw[FLOOKUP_DEF,tvars_def] >>
    metis_tac[] ) >>
  conj_tac >- (
    rw[MEM_EL,tvars_def,tyvars_def] ) >>
  conj_tac >- (
    rw[MEM_EL,tvars_def,tyvars_def] ) >>
  conj_tac >- (
    rw[tyvars_tyinst,SUBSET_DEF,tvars_def] >> fs[] >>
    qmatch_assum_abbrev_tac`∀x. MEM x (tvars (simple_inst tyin tm)) ⇒ x ∈ FDOM τ` >>
    last_x_assum match_mp_tac >>
    simp[tvars_simple_inst] >>
    metis_tac[tyvars_typeof_subset_tvars,WELLTYPED,MAP,SUBSET_DEF] ) >>
  rw[tvars_def,tyvars_def] >>
  metis_tac[typeset_inhabited])

val semantics_raconv = store_thm("semantics_raconv",
  ``∀env tp.
      RACONV env tp ⇒
      ∀σ1 σ2 τ.
        type_valuation τ ∧
        term_valuation τ σ1 ∧
        term_valuation τ σ2 ∧
        (∀x1 ty1 x2 ty2.
          ALPHAVARS env (Var x1 ty1,Var x2 ty2) ⇒
            (semantics σ1 τ (Var x1 ty1) =
             semantics σ2 τ (Var x2 ty2))) ∧
        EVERY (λ(x,y). welltyped x ∧ welltyped y ∧ typeof x = typeof y) env ∧
        welltyped (FST tp) ∧ welltyped (SND tp)
        ⇒
        (semantics σ1 τ (FST tp) =
         semantics σ2 τ (SND tp))``,
  ho_match_mp_tac RACONV_strongind >>
  simp[FORALL_PROD] >>
  conj_tac >- (
    rw[] >>
    simp[Once FUN_EQ_THM] >>
    simp[Once semantics_cases] >>
    simp[Once semantics_cases,SimpRHS] ) >>
  conj_tac >- (
    rw[] >>
    simp[Once FUN_EQ_THM] >>
    simp[Once semantics_cases] >>
    simp[Once semantics_cases,SimpRHS] >>
    simp[Once (CONJUNCT1 semantics_cases)] >>
    simp[Once (CONJUNCT1 semantics_cases),SimpRHS] >>
    srw_tac[DNF_ss][] >> rfs[] >>
    `semantics σ1 τ s1 = semantics σ2 τ s2` by metis_tac[] >>
    `semantics σ1 τ t1 = semantics σ2 τ t2` by metis_tac[] >>
    simp[] ) >>
  rw[] >>
  simp[Once FUN_EQ_THM] >>
  simp[Once semantics_cases] >>
  simp[Once semantics_cases,SimpRHS] >>
  rw[] >>
  rw[EQ_IMP_THM] >>
  map_every qexists_tac[`mb`,`mty`,`mtyb`,`tyb`] >>
  simp[] >>
  qmatch_assum_abbrev_tac`RACONV env' (t1,t2)` >>
  qspecl_then[`env'`,`t1,t2`]mp_tac RACONV_TYPE >>
  simp[Abbr`env'`] >> strip_tac >>
  (conj_tac >- metis_tac[WELLTYPED,WELLTYPED_LEMMA]) >>
  rw[] >>
  first_x_assum(qspec_then`m`mp_tac) >> rw[] >>
  qmatch_abbrev_tac`semantics σ2' τ tq mm` >>
  qmatch_assum_abbrev_tac`semantics σ1' τ tp mm` >>
  (qsuff_tac`semantics σ1' τ tp = semantics σ2' τ tq` >- metis_tac[]) >>
  (first_x_assum match_mp_tac ORELSE (match_mp_tac EQ_SYM >> first_x_assum match_mp_tac)) >>
  fs[term_valuation_def] >>
  (conj_tac >- (
    simp[Abbr`σ2'`,Abbr`σ1'`] >>
    match_mp_tac (CONJUNCT2 FEVERY_STRENGTHEN_THM) >>
    simp[] >> metis_tac[] )) >>
  (conj_tac >- (
    simp[Abbr`σ2'`,Abbr`σ1'`] >>
    match_mp_tac (CONJUNCT2 FEVERY_STRENGTHEN_THM) >>
    simp[] >> metis_tac[] )) >>
  simp[ALPHAVARS_def] >>
  (rw[] >- (
    simp[FUN_EQ_THM] >>
    simp[Once semantics_cases] >>
    simp[Once semantics_cases,SimpRHS] >>
    simp[FLOOKUP_DEF,Abbr`σ1'`,Abbr`σ2'`] )) >>
  qmatch_assum_rename_tac`ALPHAVARS env (Var va vta, Var vb vtb)`[] >>
  first_x_assum(qspecl_then[`va`,`vta`,`vb`,`vtb`]mp_tac) >>
  simp[] >>
  simp[FUN_EQ_THM,Once(CONJUNCT2 semantics_cases)] >>
  simp[Once(CONJUNCT2 semantics_cases)] >>
  simp[Once(CONJUNCT2 semantics_cases)] >>
  simp[Once(CONJUNCT2 semantics_cases)] >>
  simp[Abbr`σ1'`,Abbr`σ2'`,FLOOKUP_UPDATE])

val semantics_aconv = store_thm("semantics_aconv",
  ``∀σ τ s t.
      type_valuation τ ∧ term_valuation τ σ ∧ welltyped s ∧ ACONV s t
      ⇒ semantics σ τ s = semantics σ τ t``,
  rw[] >> imp_res_tac ACONV_welltyped >>
  fs[ACONV_def]  >>
  qspecl_then[`[]`,`s,t`] mp_tac semantics_raconv >>
  rw[] >> first_x_assum match_mp_tac >> rw[] >>
  fs[ALPHAVARS_def])

val semantics_typeset = store_thm("semantics_typeset",
  ``(∀τ ty mty. typeset τ ty mty ⇒ type_valuation τ ⇒ ∃mt. mt <: mty) ∧
    (∀σ τ t mt. semantics σ τ t mt ⇒
        type_valuation τ ∧ term_valuation τ σ ⇒
           ∃mty. welltyped t ∧ typeset τ (typeof t) mty ∧ mt <: mty)``,
  ho_match_mp_tac (theorem"semantics_strongind") >>
  simp[INDSET_INHABITED,FUNSPACE_INHABITED] >>
  conj_tac >- (
    simp[type_valuation_def] >>
    simp[FLOOKUP_DEF,FRANGE_DEF] >>
    metis_tac[] ) >>
  conj_tac >- metis_tac[BOOLEAN_IN_BOOLSET] >>
  conj_tac >- ( rw[suchthat_def] >> metis_tac[] ) >>
  conj_tac >- (
    simp[] >> rw[] >>
    fs[term_valuation_def] >>
    imp_res_tac FEVERY_FLOOKUP >>
    fs[] >> metis_tac[]) >>
  conj_tac >- (
    rw[] >>
    rw[Once semantics_cases] >>
    rw[Once (Q.SPECL[`τ`,`Fun X Y`](CONJUNCT1 semantics_cases))] >>
    fsrw_tac[DNF_ss][] >>
    rpt(qexists_tac`mty`)>>simp[]>>
    match_mp_tac ABSTRACT_IN_FUNSPACE >> rw[] >>
    match_mp_tac ABSTRACT_IN_FUNSPACE >> rw[] >>
    rw[BOOLEAN_IN_BOOLSET]) >>
  conj_tac >- (
    rw[] >>
    rw[Once semantics_cases] >>
    rw[Once (Q.SPECL[`τ`,`Fun X Y`](CONJUNCT1 semantics_cases))] >>
    fsrw_tac[DNF_ss][] >>
    rpt(qexists_tac`mty`)>>simp[]>>
    match_mp_tac ABSTRACT_IN_FUNSPACE >> rw[] >>
    fs[suchthat_def] >> rw[] >- (
      qmatch_abbrev_tac`ch s <: mty` >>
      `ch s <: s` by (
        match_mp_tac ch_def >>
        simp[Abbr`s`,suchthat_def] >>
        metis_tac[] ) >>
      fs[Abbr`s`,suchthat_def] ) >>
    match_mp_tac ch_def >>
    metis_tac[] ) >>
  conj_tac >- (
    rw[] >> fs[] >>
    qmatch_assum_abbrev_tac`welltyped (inst tyin tm)` >>
    qspecl_then[`tm`,`tyin`]mp_tac simple_inst_has_type >> rw[] >>
    imp_res_tac(CONJUNCT1 typeset_closes_over) >> fs[] >>
    metis_tac[WELLTYPED_LEMMA,typeset_tyvars,MEM]) >>
  conj_tac >- (
    rw[] >> fs[] >>
    rw[Once semantics_cases] >>
    fsrw_tac[DNF_ss][] >>
    qmatch_assum_rename_tac`mt <: maty`[] >>
    qmatch_assum_rename_tac`typeset τ ty mtt`[] >>
    map_every qexists_tac[`maty`,`mtt`] >>
    rw[] >>
    match_mp_tac ABSTRACT_IN_FUNSPACE >> simp[] >>
    qpat_assum`typeset τ (X Y) Z` mp_tac >> rw[Once semantics_cases] >>
    fs[suchthat_def] >>
    qmatch_assum_abbrev_tac`(simple_inst tyin tm) has_type fty` >>
    qspecl_then[`tm`,`tyin`]mp_tac simple_inst_has_type >> simp[] >>
    discharge_hyps >- metis_tac[welltyped_def] >>
    rw[] >> imp_res_tac WELLTYPED_LEMMA >>
    fs[Abbr`fty`] >> rw[] >>
    metis_tac[semantics_11,type_valuation_FEMPTY]) >>
  conj_tac >- (
    rw[] >> fs[] >>
    rw[Once semantics_cases] >>
    fsrw_tac[DNF_ss][] >>
    qmatch_assum_rename_tac`typeset τ ty mm`[] >>
    map_every qexists_tac[`mm`,`mty`] >> rw[] >>
    match_mp_tac ABSTRACT_IN_FUNSPACE >>
    qpat_assum`typeset τ (X Y args) Z` mp_tac >> rw[Once semantics_cases] >>
    qmatch_assum_abbrev_tac`(simple_inst tyin tm) has_type fty` >>
    qspecl_then[`tm`,`tyin`]mp_tac simple_inst_has_type >> simp[] >>
    discharge_hyps >- metis_tac[welltyped_def] >>
    rw[] >> imp_res_tac WELLTYPED_LEMMA >>
    fs[Abbr`fty`] >> rw[] >- (
      fs[suchthat_def] >>
      metis_tac[semantics_11,type_valuation_FEMPTY,term_valuation_FEMPTY] ) >>
    match_mp_tac ch_def >>
    fs[suchthat_def] >>
    metis_tac[] ) >>
  conj_tac >- (
    rw[] >> fs[] >>
    fs[Once (Q.SPECL[`τ`,`Fun X Y`](CONJUNCT1 semantics_cases))] >> rw[] >>
    qexists_tac`my` >> simp[] >>
    match_mp_tac APPLY_IN_RANSPACE >>
    metis_tac[semantics_11]) >>
  rw[] >> fs[] >>
  simp[Once semantics_cases] >>
  res_tac >>
  pop_assum mp_tac >>
  discharge_hyps >- (
    match_mp_tac term_valuation_FUPDATE >>
    rw[] >> metis_tac[] ) >>
  rw[] >>
  fsrw_tac[DNF_ss][] >>
  imp_res_tac WELLTYPED_LEMMA >> rw[] >>
  imp_res_tac semantics_11 >> rw[] >>
  qmatch_assum_rename_tac`typeset τ (typeof t) tty`[] >>
  map_every qexists_tac[`mty`,`tty`] >> rw[] >>
  match_mp_tac ABSTRACT_IN_FUNSPACE >> rw[])

val semantics_frees = store_thm("semantics_frees",
  ``∀τ1 τ2 σ1 σ2 t.
      type_valuation τ1 ∧ type_valuation τ2 ∧
      (∀x. MEM x (tvars t) ⇒ FLOOKUP τ1 x = FLOOKUP τ2 x) ∧
      (∀x ty. VFREE_IN (Var x ty) t ⇒ (FLOOKUP σ1 (x,ty) = FLOOKUP σ2 (x,ty)))
      ⇒ semantics σ1 τ1 t = semantics σ2 τ2 t``,
  gen_tac >> (CONV_TAC (RESORT_FORALL_CONV List.rev)) >> Induct
  >- (
    rw[FUN_EQ_THM] >>
    rw[Once semantics_cases] >>
    rw[Once semantics_cases] )
  >- (
    rw[FUN_EQ_THM,tvars_def] >>
    rw[Once semantics_cases] >>
    rw[Once semantics_cases,SimpRHS]>>
    rw[EQ_IMP_THM] >- (
      fs[tyvars_def] >>
      metis_tac[typeset_tyvars] )
    >- (
      fs[tyvars_def] >>
      metis_tac[typeset_tyvars] )
    >- (
      fs[SUBSET_DEF] >>
      fs[tyvars_tyinst] >>
      metis_tac[typeset_tyvars,SIMP_RULE(srw_ss())[EXTENSION]tvars_simple_inst] )
    >- (
      fs[tyvars_def] >>
      metis_tac[tyvars_def,typeset_tyvars] )
    >- (
      fs[tyvars_def] >>
      map_every qexists_tac[`maty`,`mp`,`mrty`] >>
      simp[] >>
      conj_tac >- metis_tac[tyvars_def,typeset_tyvars] >>
      conj_tac >- metis_tac[typeset_tyvars] >>
      match_mp_tac(MP_CANON(CONJUNCT2 typeset_tyvars)) >>
      qexists_tac`τ1` >> simp[] >>
      rw[] >>
      first_x_assum match_mp_tac >>
      fs[tvars_simple_inst,MEM_FOLDR_LIST_UNION] >>
      ntac 2 (pop_assum mp_tac) >>
      simp[FLOOKUPD_def] >>
      qpat_assum`typeset X Y maty`mp_tac >>
      simp[Once semantics_cases] >> strip_tac >>
      BasicProvers.CASE_TAC >- (
        rfs[ALOOKUP_FAILS,tyvars_def,MEM_ZIP] >>
        metis_tac[MEM_EL] ) >>
      imp_res_tac ALOOKUP_MEM >>
      rfs[MEM_ZIP] >>
      metis_tac[MEM_EL] )
    >- (
      fs[tyvars_def] >>
      metis_tac[typeset_tyvars] )
    >- (
      fs[tyvars_def] >>
      metis_tac[typeset_tyvars] )
    >- (
      fs[SUBSET_DEF] >>
      fs[tyvars_tyinst] >>
      metis_tac[typeset_tyvars,SIMP_RULE(srw_ss())[EXTENSION]tvars_simple_inst] )
    >- (
      fs[tyvars_def] >>
      metis_tac[tyvars_def,typeset_tyvars] )
    >- (
      fs[tyvars_def] >>
      map_every qexists_tac[`maty`,`mp`,`mrty`] >>
      simp[] >>
      conj_tac >- metis_tac[tyvars_def,typeset_tyvars] >>
      conj_tac >- metis_tac[typeset_tyvars] >>
      match_mp_tac(MP_CANON(CONJUNCT2 typeset_tyvars)) >>
      qexists_tac`τ2` >> simp[] >>
      rw[] >>
      match_mp_tac EQ_SYM >>
      first_x_assum match_mp_tac >>
      fs[tvars_simple_inst,MEM_FOLDR_LIST_UNION] >>
      ntac 2 (pop_assum mp_tac) >>
      simp[FLOOKUPD_def] >>
      qpat_assum`typeset X Y maty`mp_tac >>
      simp[Once semantics_cases] >> strip_tac >>
      BasicProvers.CASE_TAC >- (
        rfs[ALOOKUP_FAILS,tyvars_def,MEM_ZIP] >>
        metis_tac[MEM_EL] ) >>
      imp_res_tac ALOOKUP_MEM >>
      rfs[MEM_ZIP] >>
      metis_tac[MEM_EL] ))
  >- (
    rw[FUN_EQ_THM,tvars_def] >>
    rw[Once semantics_cases] >>
    rw[Once semantics_cases,SimpRHS] >>
    metis_tac[]) >>
  rw[FUN_EQ_THM,tvars_def] >>
  rw[Once semantics_cases] >>
  rw[Once semantics_cases,SimpRHS] >>
  rw[EQ_IMP_THM] >>
  map_every qexists_tac[`mb`,`mty`,`mtyb`,`tyb`] >>
  rw[] >>
  TRY(qmatch_abbrev_tac `typeset X t mty` >> metis_tac[typeset_tyvars]) >>
  TRY(qmatch_abbrev_tac `typeset X tyb mtyb` >>
    imp_res_tac WELLTYPED_LEMMA >> rw[] >>
    match_mp_tac (MP_CANON(CONJUNCT1 typeset_tyvars)) >>
    HINT_EXISTS_TAC >>
    rw[] >>
    metis_tac[tyvars_typeof_subset_tvars,SUBSET_DEF]) >>
  first_x_assum(qspec_then`m`mp_tac) >> rw[] >>
  qmatch_abbrev_tac`semantics (f |+ z) τ tt mm` >>
  qmatch_assum_abbrev_tac`semantics (g |+ z) τ' tt mm` >>
  (qsuff_tac`semantics (f|+z) τ tt = semantics (g|+z) τ' tt` >- rw[]) >>
  (first_x_assum match_mp_tac ORELSE
   (match_mp_tac EQ_SYM >> first_x_assum match_mp_tac)) >>
  simp[Abbr`z`,FLOOKUP_UPDATE] >>
  metis_tac[])

val closes_def = Define`
  closes s t tm ⇔
    set (tvars tm) ⊆ t ∧
    (∀x ty. VFREE_IN (Var x ty) tm ⇒ (x,ty) ∈ s)`

val closes_extend = store_thm("closes_extend",
  ``∀σ τ t σ' τ'. closes σ τ t ∧ σ ⊆ σ' ∧ τ ⊆ τ' ⇒ closes σ' τ' t``,
  rw[SUBMAP_DEF,closes_def,SUBSET_DEF])

val semantics_closes = prove(
  ``(∀τ ty m. typeset τ ty m ⇒ T) ∧
    (∀σ τ t m. semantics σ τ t m ⇒ type_valuation τ ∧ term_valuation τ σ ⇒ closes (FDOM σ) (FDOM τ) t)``,
  ho_match_mp_tac(theorem"semantics_strongind") >> simp[] >>
  conj_tac >- (
    simp[Once semantics_cases,FLOOKUP_DEF,closes_def] >>
    simp[term_valuation_def,FEVERY_DEF,FORALL_PROD] >>
    rw[tvars_def] >> metis_tac[typeset_closes_over] ) >>
  conj_tac >- (
    rw[closes_def,tyvars_def,tvars_def] >>
    metis_tac[typeset_closes_over] ) >>
  conj_tac >- (
    rw[closes_def,tyvars_def,tvars_def] >>
    metis_tac[typeset_closes_over] ) >>
  conj_tac >- (
    rw[closes_def,tvars_def] >>
    fs[tyvars_tyinst,SUBSET_DEF,GSYM LEFT_FORALL_IMP_THM] >>
    qmatch_assum_abbrev_tac`∀x. MEM x (tvars (inst tyin tm)) ⇒ x ∈ FDOM τ` >>
    qspecl_then[`tm`,`tyin`]strip_assume_tac tvars_simple_inst >>
    rfs[EXTENSION] >>
    imp_res_tac WELLTYPED >>
    imp_res_tac tyvars_typeof_subset_tvars >>
    fs[SUBSET_DEF] >>
    metis_tac[] ) >>
  conj_tac >- (
    rw[closes_def,tyvars_def,tvars_def] >>
    TRY (metis_tac[typeset_closes_over,FDOM_FEMPTY,SUBSET_EMPTY,EMPTY_SUBSET]) >>
    fs[SUBSET_DEF,MEM_FOLDR_LIST_UNION] >>
    qpat_assum`typeset τ (X Y) Z`mp_tac >>
    simp[Once semantics_cases] >> rw[] >>
    qmatch_assum_abbrev_tac`simple_inst tyin tm has_type pty` >>
    imp_res_tac typeset_closes_over >> fs[] >>
    fs[tyvars_tyinst,SUBSET_DEF,GSYM LEFT_FORALL_IMP_THM] >>
    fs[Abbr`tyin`,FLOOKUPD_def] >>
    `∃n. y = EL n args ∧ n < LENGTH args` by metis_tac[MEM_EL] >>
    first_x_assum(qspecl_then[`x`,`EL n (tvars tm)`]mp_tac) >>
    BasicProvers.CASE_TAC >- (
      fs[ALOOKUP_FAILS] >> rfs[MEM_ZIP] >> metis_tac[] ) >>
    qspec_then`tm`strip_assume_tac tvars_ALL_DISTINCT >>
    qmatch_assum_abbrev_tac`ALOOKUP ls a = SOME z` >>
    Q.ISPECL_THEN[`ls`,`n`]strip_assume_tac ALOOKUP_ALL_DISTINCT_EL >>
    rfs[MAP_ZIP,Abbr`ls`,EL_ZIP] >> rpt BasicProvers.VAR_EQ_TAC >> simp[] >>
    qmatch_assum_abbrev_tac`simple_inst tyin tm has_type pty` >>
    fs[tvars_simple_inst,GSYM LEFT_FORALL_IMP_THM] >>
    first_x_assum(qspecl_then[`x`,`a`]mp_tac) >>
    simp[Abbr`a`] >> rw[] >>
    ntac 2 (pop_assum mp_tac) >>
    simp[FLOOKUPD_def,Abbr`tyin`] >>
    metis_tac[MEM_EL]) >>
  conj_tac >- (
    rw[closes_def,tyvars_def,tvars_def] >>
    TRY (metis_tac[typeset_closes_over,FDOM_FEMPTY,SUBSET_EMPTY,EMPTY_SUBSET]) >>
    fs[SUBSET_DEF,MEM_FOLDR_LIST_UNION] >>
    qpat_assum`typeset τ (X Y) Z`mp_tac >>
    simp[Once semantics_cases] >> rw[] >>
    qmatch_assum_abbrev_tac`simple_inst tyin tm has_type pty` >>
    imp_res_tac typeset_closes_over >> fs[] >>
    fs[tyvars_tyinst,SUBSET_DEF,GSYM LEFT_FORALL_IMP_THM] >>
    fs[Abbr`tyin`,FLOOKUPD_def] >>
    `∃n. y = EL n args ∧ n < LENGTH args` by metis_tac[MEM_EL] >>
    first_x_assum(qspecl_then[`x`,`EL n (tvars tm)`]mp_tac) >>
    BasicProvers.CASE_TAC >- (
      fs[ALOOKUP_FAILS] >> rfs[MEM_ZIP] >> metis_tac[] ) >>
    qspec_then`tm`strip_assume_tac tvars_ALL_DISTINCT >>
    qmatch_assum_abbrev_tac`ALOOKUP ls a = SOME z` >>
    Q.ISPECL_THEN[`ls`,`n`]strip_assume_tac ALOOKUP_ALL_DISTINCT_EL >>
    rfs[MAP_ZIP,Abbr`ls`,EL_ZIP] >> rpt BasicProvers.VAR_EQ_TAC >> simp[] >>
    qmatch_assum_abbrev_tac`simple_inst tyin tm has_type pty` >>
    fs[tvars_simple_inst,GSYM LEFT_FORALL_IMP_THM] >>
    first_x_assum(qspecl_then[`x`,`a`]mp_tac) >>
    simp[Abbr`a`] >> rw[] >>
    ntac 2 (pop_assum mp_tac) >>
    simp[FLOOKUPD_def,Abbr`tyin`] >>
    metis_tac[MEM_EL]) >>
  conj_tac >- (
    rw[closes_def,tvars_def] >> fs[] >> metis_tac[] ) >>
  (
    fs[closes_def,tvars_def] >>
    rpt gen_tac >> strip_tac >> strip_tac >>
    simp[GSYM CONJ_ASSOC] >>
    conj_tac >- metis_tac[typeset_closes_over] >> fs[] >>
    qmatch_assum_rename_tac`typeset τ ty mty`[] >>
    `∃m. m <: mty` by metis_tac[typeset_inhabited] >>
    first_x_assum(qspec_then`m`mp_tac)>>simp[]>>strip_tac>>
    pop_assum mp_tac >>
    discharge_hyps >- (
      match_mp_tac term_valuation_FUPDATE >>
      simp[] >> metis_tac[] ) >>
    rw[] >> metis_tac[]))
val semantics_closes = save_thm("semantics_closes",MP_CANON (CONJUNCT2 semantics_closes))

val closes_Comb = store_thm("closes_Comb",
  ``∀env σ τ t1 t2. closes σ τ (Comb t1 t2) ⇔ closes σ τ t1 ∧ closes σ τ t2``,
  rw[closes_def,tvars_def] >> metis_tac[])
val _ = export_rewrites["closes_Comb"]

val closes_Abs = store_thm("closes_Abs",
  ``∀s t x ty tm. closes s t (Abs x ty tm) ⇔ set (tyvars ty) ⊆ t ∧ closes ((x,ty)INSERT s) t tm``,
  rw[closes_def,SUBSET_DEF,GSYM LEFT_FORALL_IMP_THM,FORALL_PROD,EXISTS_PROD,tvars_def] >>
  metis_tac[])
val _ = export_rewrites["closes_Abs"]

val closes_Const = store_thm("closes_Const",
  ``∀σ τ s ty c. closes σ τ (Const s ty c) ⇔ set (tyvars ty) ⊆ τ``,
  rw[closes_def,tvars_def])
val _ = export_rewrites["closes_Const"]

val closes_Var = store_thm("closes_Var",
  ``∀σ τ n ty. closes σ τ (Var n ty) ⇔ set (tyvars ty) ⊆ τ ∧ (n,ty) ∈ σ``,
  rw[closes_def,tvars_def])
val _ = export_rewrites["closes_Var"]

val closes_equation = store_thm("closes_equation",
  ``l has_type ty ∧ r has_type ty ⇒
  (closes σ τ (l === r) ⇔ closes σ τ l ∧ closes σ τ r)``,
  rw[closes_def,equation_def,tyvars_def,tvars_def] >> rw[EQ_IMP_THM] >>
  imp_res_tac tyvars_typeof_subset_tvars >>
  fs[SUBSET_DEF] >> metis_tac[WELLTYPED_LEMMA] )

val semantics_extend = store_thm("semantics_extend",
  ``∀σ τ t m σ' τ'. type_valuation τ' ∧
                    term_valuation τ σ ∧
                    term_valuation τ' σ' ∧
                 semantics σ τ t m ∧ σ ⊑ σ' ∧ τ ⊑ τ'
                 ⇒ semantics σ' τ' t m``,
  rw[] >>
  imp_res_tac type_valuation_reduce >>
  `closes (FDOM σ) (FDOM τ) t` by metis_tac[semantics_closes] >>
  qsuff_tac`semantics σ' τ' t = semantics σ τ t`>-rw[] >>
  match_mp_tac semantics_frees >>
  fs[closes_def,SUBSET_DEF,SUBMAP_DEF,FLOOKUP_DEF])

val semantics_reduce = store_thm("semantics_reduce",
  ``∀σ τ t m τ' σ'. type_valuation τ' ∧ term_valuation τ' σ' ∧
                 semantics σ' τ' t m ∧ σ ⊑ σ' ∧ τ ⊑ τ' ∧
                 closes (FDOM σ) (FDOM τ) t
                 ⇒ semantics σ τ t m``,
  rw[] >>
  imp_res_tac term_valuation_reduce >>
  imp_res_tac type_valuation_reduce >>
  qsuff_tac`semantics σ τ t = semantics σ' τ' t`>-rw[] >>
  match_mp_tac semantics_frees >> simp[] >>
  fs[closes_def,SUBSET_DEF,FORALL_PROD,FLOOKUP_DEF,SUBMAP_DEF])

val typeset_extend = store_thm("typeset_extend",
  ``∀τ ty mty τ'. typeset τ ty mty ∧ τ ⊑ τ' ⇒ typeset τ' ty mty``,
  rw[] >>
  match_mp_tac (MP_CANON(CONJUNCT1 typeset_tyvars)) >>
  qexists_tac`τ` >>
  fs[SUBMAP_DEF,FLOOKUP_DEF] >>
  imp_res_tac typeset_closes_over >>
  fs[SUBSET_DEF])

val typeset_reduce = store_thm("typeset_reduce",
  ``∀τ ty mty τ'. typeset τ' ty mty ∧ set (tyvars ty) ⊆ FDOM τ ∧ τ ⊑ τ' ⇒ typeset τ ty mty``,
  rw[] >>
  match_mp_tac (MP_CANON(CONJUNCT1 typeset_tyvars)) >>
  qexists_tac`τ'` >>
  fs[SUBMAP_DEF,FLOOKUP_DEF,SUBSET_DEF])

val type_has_meaning_def = Define`
  type_has_meaning ty ⇔ ∀τ. type_valuation τ ∧ set (tyvars ty) ⊆ FDOM τ ⇒ ∃m. typeset τ ty m`

val type_has_meaning_Bool = store_thm("type_has_meaning_Bool",
  ``type_has_meaning Bool``,
  rw[type_has_meaning_def])
val _ = export_rewrites["type_has_meaning_Bool"]

val covering_type_valuation_exists = store_thm("covering_type_valuation_exists",
  ``∀s. FINITE s ⇒ ∀τ. ∃τ'. τ ⊑ τ' ∧ s ⊆ FDOM τ' ∧ (type_valuation τ ⇒ type_valuation τ')``,
  ho_match_mp_tac FINITE_INDUCT >>
  rw[] >- metis_tac[SUBMAP_REFL] >>
  first_x_assum(qspec_then`τ`strip_assume_tac) >>
  Cases_on`e ∈ FDOM τ'` >- metis_tac[] >>
  qexists_tac`τ' |+ (e,boolset)` >>
  simp[] >>
  fs[type_valuation_def,IN_FRANGE,FAPPLY_FUPDATE_THM] >>
  metis_tac[SUBMAP_FUPDATE_EQN,SUBMAP_TRANS,BOOLEAN_IN_BOOLSET])

val type_has_meaning_Fun = store_thm("type_has_meaning_Fun",
  ``∀dty rty. type_has_meaning (Fun dty rty) ⇔ type_has_meaning dty ∧ type_has_meaning rty``,
  rw[type_has_meaning_def,tyvars_def] >>
  rw[Once semantics_cases] >>
  metis_tac[covering_type_valuation_exists,typeset_reduce,SUBMAP_DEF,SUBSET_DEF,FINITE_LIST_TO_SET])
val _ = export_rewrites["type_has_meaning_Fun"]

val typeset_has_meaning = prove(
  ``(∀τ ty m. typeset τ ty m ⇒ type_valuation τ ⇒ type_has_meaning ty) ∧
    (∀σ τ t m. semantics σ τ t m ⇒ T)``,
  ho_match_mp_tac (theorem"semantics_strongind") >> simp[] >>
  conj_tac >- (
    simp[type_has_meaning_def,tyvars_def] >>
    simp[Once semantics_cases,FLOOKUP_DEF] ) >>
  rw[type_has_meaning_def,tyvars_def] >>
  simp[Once semantics_cases] >> fs[] >>
  CONV_TAC(RESORT_EXISTS_CONV List.rev) >>
  CONV_TAC(RESORT_EXISTS_CONV (fn ls => (tl ls)@[hd ls])) >>
  qexists_tac`rty` >> rw[] >>
  first_x_assum match_mp_tac >>
  rw[] >>
  fs[SUBSET_DEF,MEM_FOLDR_LIST_UNION,GSYM LEFT_FORALL_IMP_THM] >>
  rw[tvars_simple_inst] >>
  first_x_assum match_mp_tac >>
  fs[FLOOKUPD_def] >>
  pop_assum mp_tac >>
  BasicProvers.CASE_TAC >- (
    rfs[ALOOKUP_FAILS,MEM_ZIP,tyvars_def] >>
    metis_tac[MEM_EL] ) >>
  imp_res_tac ALOOKUP_MEM >>
  rfs[MEM_ZIP] >>
  metis_tac[MEM_EL])
val typeset_has_meaning = save_thm("typeset_has_meaning",MP_CANON(CONJUNCT1 typeset_has_meaning))

val semantics_frees_exists = store_thm("semantics_frees_exists",
  ``(∀τ1 ty m. typeset τ1 ty m ⇒
      ∀τ2. type_valuation τ1 ∧ type_valuation τ2 ∧ (∀x. x ∈ set(tyvars ty) ⇒ x ∈ FDOM τ2) ⇒ ∃m2. typeset τ2 ty m2) ∧
    (∀σ1 τ1 tm m. semantics σ1 τ1 tm m ⇒
      ∀σ2 τ2. type_valuation τ1 ∧ type_valuation τ2 ∧
              term_valuation τ1 σ1 ∧ term_valuation τ2 σ2 ∧
              (∀x. MEM x (tvars tm) ⇒ x ∈ FDOM τ2) ∧
              (∀x ty. VFREE_IN (Var x ty) tm ⇒ ((x,ty) ∈ FDOM σ2))
              ⇒
        ∃m2. semantics σ2 τ2 tm m2)``,
  ho_match_mp_tac (theorem"semantics_strongind") >> simp[] >>
  conj_tac >- (
    ntac 2 (simp[Once semantics_cases]) >>
    simp[FLOOKUP_DEF,SUBMAP_DEF,tyvars_def] ) >>
  conj_tac >- (
    rpt gen_tac >> strip_tac >>
    simp[Once semantics_cases] >> rw[] >>
    fs[tyvars_def,MEM_LIST_UNION] >>
    metis_tac[] ) >>
  conj_tac >- (
    rpt gen_tac >> strip_tac >>
    simp[Once semantics_cases] >> rw[] >>
    fs[tyvars_def,MEM_LIST_UNION] >>
    qmatch_assum_rename_tac`w <: mrty`[] >>
    qmatch_assum_rename_tac`holds mp w`[] >>
    qmatch_assum_abbrev_tac`typeset τ1 (tyinst tyin rty) mrty` >>
    qpat_assum`∀τ2. X t2 ⇒ ∃m2. typeset τ2 Y m2`(qspec_then`τ2`mp_tac) >>
    fs[MEM_FOLDR_LIST_UNION] >>
    simp[tyvars_tyinst] >>
    discharge_hyps >- (
      simp[FLOOKUPD_def,Abbr`tyin`] >>
      rw[] >>
      fs[GSYM LEFT_FORALL_IMP_THM] >>
      first_x_assum (match_mp_tac o MP_CANON) >>
      rw[] >>
      ntac 2 (pop_assum mp_tac) >>
      BasicProvers.CASE_TAC >- (
        fs[ALOOKUP_FAILS] >>
        rfs[MEM_ZIP] >>
        imp_res_tac tyvars_typeof_subset_tvars >>
        fs[SUBSET_DEF,tyvars_def] >>
        metis_tac[MEM_EL] ) >>
      imp_res_tac ALOOKUP_MEM >>
      rfs[MEM_ZIP] >>
      imp_res_tac tyvars_typeof_subset_tvars >>
      fs[SUBSET_DEF,tyvars_def] >>
      metis_tac[MEM_EL] ) >>
    strip_tac >>
    CONV_TAC(RESORT_EXISTS_CONV (fn ls => (tl ls)@[hd ls])) >>
    map_every qexists_tac[`m2`,`rty`] >>
    rw[] >>
    last_x_assum(qspec_then`τ2`mp_tac) >>
    simp[] >>
    discharge_hyps >- (
      simp[tvars_simple_inst,SUBSET_DEF] >>
      simp[FLOOKUPD_def,Abbr`tyin`] >>
      rw[] >>
      fs[GSYM LEFT_FORALL_IMP_THM] >>
      first_x_assum (match_mp_tac o MP_CANON) >>
      rw[] >>
      pop_assum mp_tac >>
      BasicProvers.CASE_TAC >- (
        fs[ALOOKUP_FAILS] >>
        rfs[MEM_ZIP] >>
        imp_res_tac tyvars_typeof_subset_tvars >>
        fs[SUBSET_DEF,tyvars_def] >>
        metis_tac[MEM_EL] ) >>
      imp_res_tac ALOOKUP_MEM >>
      rfs[MEM_ZIP] >>
      rw[] >>
      metis_tac[MEM_EL]) >>
    rw[] >>
    metis_tac[semantics_11] ) >>
  conj_tac >- (
    simp[tvars_def] >>
    simp[Once semantics_cases] >>
    simp[FLOOKUP_DEF]) >>
  conj_tac >- (
    rw[tvars_def,tyvars_def] >>
    simp[Once semantics_cases] ) >>
  conj_tac >- (
    rw[tvars_def,tyvars_def] >>
    simp[Once semantics_cases] ) >>
  conj_tac >- (
    rw[tvars_def,tyvars_def] >>
    simp[Once semantics_cases] >>
    first_x_assum(qspecl_then[`FEMPTY`,`τ2`]mp_tac) >>
    simp[] >>
    discharge_hyps >- (
      fs[tyvars_tyinst,tvars_simple_inst] >>
      fs[SUBSET_DEF] >>
      conj_tac >- metis_tac[] >>
      fs[VFREE_IN_simple_inst,fresh_term_def]) >>
    metis_tac[] ) >>
  conj_tac >- (
    rw[tvars_def,tyvars_def,MEM_FOLDR_LIST_UNION] >>
    simp[Once semantics_cases] >>
    metis_tac[] ) >>
  conj_tac >- (
    rw[tvars_def,tyvars_def,MEM_FOLDR_LIST_UNION] >>
    simp[Once semantics_cases] >>
    last_x_assum(qspec_then`τ2`mp_tac) >>
    simp[] >> strip_tac >>
    qexists_tac`m2` >> simp[] >>
    last_x_assum(qspec_then`τ2`mp_tac) >>
    simp[] >>
    disch_then(qx_choose_then`m3`strip_assume_tac) >>
    CONV_TAC SWAP_EXISTS_CONV >>
    qexists_tac`m3` >> rw[] >>
    first_x_assum match_mp_tac >>
    simp[] >>
    simp[tvars_simple_inst,FLOOKUPD_def] >>
    qmatch_assum_abbrev_tac`simple_inst tyin tm has_type Fun ty Bool` >>
    `closed p0` by fs[Once semantics_cases] >>
    `ACONV p0 tm` by simp[Abbr`tm`,fresh_term_def] >>
    `closed tm` by metis_tac[ACONV_VFREE_IN,ACONV_SYM] >>
    reverse(rw[]) >- (
      `ALL_DISTINCT(bv_names tm)` by simp[Abbr`tm`,fresh_term_def] >>
      rw[VFREE_IN_simple_inst,fresh_term_def] ) >>
    first_x_assum (match_mp_tac o MP_CANON) >>
    rw[] >>
    pop_assum mp_tac >>
    `LENGTH args = LENGTH (tvars tm)` by (
      fs[Once semantics_cases] ) >>
    BasicProvers.CASE_TAC >- (
      fs[ALOOKUP_FAILS,tyvars_def] >>
      rfs[MEM_ZIP] >>
      metis_tac[MEM_EL] ) >>
    imp_res_tac ALOOKUP_MEM >>
    rfs[MEM_ZIP] >>
    rw[] >>
    metis_tac[MEM_EL] ) >>
  conj_tac >- (
    rw[tvars_def] >>
    simp[Once semantics_cases] >>
    metis_tac[] ) >>
  rw[tvars_def] >>
  simp[Once semantics_cases] >>
  last_x_assum(qspec_then`τ2`mp_tac) >> rw[] >>
  last_x_assum(qspec_then`τ2`mp_tac) >> simp[] >>
  discharge_hyps >- (
    metis_tac[tyvars_typeof_subset_tvars,SUBSET_DEF] ) >>
  rw[] >>
  CONV_TAC(RESORT_EXISTS_CONV List.rev) >>
  map_every qexists_tac[`ty'`,`m2'`,`m2`] >> rw[] >>
  rw[GSYM SKOLEM_THM] >>
  rw[RIGHT_EXISTS_IMP_THM] >>
  `∃z. z <: m` by metis_tac[typeset_inhabited] >>
  first_x_assum(qspec_then`z`mp_tac) >>
  rw[] >>
  qmatch_assum_rename_tac`z2 <: m2`[] >>
  first_x_assum(qspecl_then[`σ2|+((s,ty),z2)`,`τ2`]mp_tac) >>
  simp[] >>
  `term_valuation τ2 (σ2 |+ ((s,ty),z2))` by (
    match_mp_tac term_valuation_FUPDATE >>
    simp[] >> metis_tac[] ) >>
  discharge_hyps >- (
    simp[] >>
    conj_tac >- (
      match_mp_tac term_valuation_FUPDATE >>
      simp[] >> metis_tac[] ) >>
    metis_tac[] ) >>
  disch_then(qx_choose_then`m3`strip_assume_tac) >>
  qexists_tac`m3` >> rw[] >>
  metis_tac[semantics_typeset,WELLTYPED,WELLTYPED_LEMMA,semantics_11])

(*
val typeset_Tydefined_ACONV = store_thm("typeset_Tydefined_ACONV",
  ``∀τ op p1 p2 args mty.
    typeset τ (Tyapp (Tydefined op p1) args) mty ∧ ACONV p1 p2 ⇒
    typeset τ (Tyapp (Tydefined op p2) args) mty``,
  rw[Once semantics_cases] >>
  rw[Once semantics_cases] >>
  map_every qexists_tac[`mp`,`mrty`,`rty`,`w`] >>
  simp[] >>
  qspecl_then[`{}`,`p1`]mp_tac fresh_term_def >>
  qspecl_then[`{}`,`p2`]mp_tac fresh_term_def >>
  simp[] >> ntac 2 strip_tac >>
  imp_res_tac ACONV_tvars >> fs[] >>
  conj_asm1_tac >- (
    metis_tac[ACONV_VFREE_IN,ACONV_SYM] ) >>
  conj_asm1_tac >- (
    metis_tac[ACONV_TYPE,ACONV_welltyped,WELLTYPED_LEMMA,WELLTYPED,ACONV_TRANS,ACONV_SYM] ) >>
  qmatch_abbrev_tac`semantics s t u mp` >>
  qmatch_assum_abbrev_tac`semantics s t v mp` >>
  qsuff_tac`semantics s t u = semantics s t v`>-rw[] >>
  match_mp_tac semantics_aconv >>
  unabbrev_all_tac >> simp[] >>
  conj_tac >- metis_tac[simple_inst_has_type,welltyped_def] >>
  match_mp_tac simple_inst_aconv >>
  simp[fresh_term_def] >>
  conj_tac >- metis_tac[ACONV_SYM,ACONV_TRANS] >>
  imp_res_tac semantics_closes >> fs[] >>
  fs[closes_def] >>
  qmatch_assum_abbrev_tac`closed (simple_inst tyin tm)` >>
  qspecl_then[`tm`,`tyin`]mp_tac VFREE_IN_simple_inst >>
  discharge_hyps >- (
    simp[Abbr`tm`,IN_DISJOINT] >>
    metis_tac[fresh_term_def,ACONV_VFREE_IN,ACONV_SYM] ) >>
  fs[] >> metis_tac[ACONV_VFREE_IN,ACONV_SYM])

val tac =
  qho_match_abbrev_tac`apply (apply (abstract a b f) x) y = z` >>
  `apply (abstract a b f) x = f x` by (
    match_mp_tac APPLY_ABSTRACT >>
    unabbrev_all_tac >> simp[] >>
    TRY (conj_tac >- metis_tac[semantics_typeset,semantics_11]) >>
    match_mp_tac ABSTRACT_IN_FUNSPACE >>
    metis_tac[semantics_typeset,WELLTYPED,BOOLEAN_IN_BOOLSET] ) >>
  simp[Abbr`f`,Abbr`b`] >>
  qho_match_abbrev_tac`apply (abstract a b f) y = z` >>
  `apply (abstract a b f) y = f y `  by (
    match_mp_tac APPLY_ABSTRACT >>
    unabbrev_all_tac >> simp[] >>
    metis_tac[semantics_typeset,semantics_11,BOOLEAN_IN_BOOLSET] ) >>
  unabbrev_all_tac >> simp[]

val semantics_equation = store_thm("semantics_equation",
  ``∀env σ τ s t ty mty ms mt mst.
    type_valuation τ ∧ term_valuation τ σ ∧
    semantics σ τ s ms ∧ semantics σ τ t mt ∧
    typeof s = typeof t ∧
    boolean (ms = mt) = mst
    ⇒ semantics σ τ (s === t) mst``,
  rw[equation_def] >>
  simp[Once semantics_cases] >>
  simp[Once semantics_cases] >>
  simp[Once semantics_cases] >>
  srw_tac[DNF_ss][] >>
  qspecl_then[`σ`,`τ`,`s`,`ms`]mp_tac(CONJUNCT2 semantics_typeset) >>
  qspecl_then[`σ`,`τ`,`t`,`mt`]mp_tac(CONJUNCT2 semantics_typeset) >>
  rw[] >>
  imp_res_tac semantics_11 >> rw[] >>
  map_every qexists_tac[`mt`,`ms`,`mty`] >> simp[] >>
  match_mp_tac EQ_SYM >> tac)

val semantics_equation_imp = store_thm("semantics_equation_imp",
  ``∀σ τ s t mst.
    type_valuation τ ∧ term_valuation τ σ ∧
    semantics σ τ (s === t) mst ⇒
    ∃ms mt.
    semantics σ τ s ms ∧ semantics σ τ t mt ∧
    typeof s = typeof t ∧
    boolean (ms = mt) = mst``,
  rw[equation_def] >>
  fs[Q.SPECL[`σ`,`τ`,`Comb X Y`](CONJUNCT2 semantics_cases)] >>
  fs[Q.SPECL[`σ`,`τ`,`Const X Y Z`](CONJUNCT2 semantics_cases)] >>
  qmatch_assum_rename_tac`semantics σ τ s ms`[] >> rw[] >>
  qmatch_assum_rename_tac`semantics σ τ t mt`[] >>
  map_every qexists_tac[`ms`,`mt`] >> rw[] >>
  match_mp_tac EQ_SYM >> tac)

val has_meaning_def = Define`
  has_meaning t ⇔
    (∃τ σ. type_valuation τ ∧ term_valuation τ σ ∧ closes (FDOM σ) (FDOM τ) t) ∧
    ∀τ σ. type_valuation τ ∧
          term_valuation τ σ ∧
          closes (FDOM σ) (FDOM τ) t
          ⇒ ∃m. semantics σ τ t m`

val has_meaning_welltyped = store_thm("has_meaning_welltyped",
  ``∀tm. has_meaning tm ⇒ welltyped tm``,
  rw[has_meaning_def] >> metis_tac[semantics_typeset])

val covering_sigma_exists = store_thm("covering_sigma_exists",
  ``∀τ σ t. type_valuation τ ∧ term_valuation τ σ ∧
            (∀x ty. VFREE_IN (Var x ty) t ⇒ ∃mty. typeset τ ty mty) ⇒
      ∃σ'. σ ⊑ σ' ∧
      (∀x ty. VFREE_IN (Var x ty) t ⇒ (x,ty) ∈ FDOM σ') ∧
      term_valuation τ σ'``,
  qsuff_tac`∀s:(string#type) set. FINITE s ⇒
    ∀τ σ. type_valuation τ ∧ term_valuation τ σ ∧ (∀x ty. (x,ty) ∈ s ⇒ ∃mty. typeset τ ty mty)⇒
      ∃σ'. σ ⊑ σ' ∧ s ⊆ FDOM σ' ∧ term_valuation τ σ'` >- (
    rw[] >>
    first_x_assum(qspec_then`{(x,ty) | VFREE_IN (Var x ty) t}`mp_tac) >>
    simp[] >> rw[SUBSET_DEF,FORALL_PROD] >> metis_tac[] ) >>
  ho_match_mp_tac FINITE_INDUCT >>
  rw[] >- metis_tac[SUBMAP_REFL] >>
  first_x_assum(qspecl_then[`τ`,`σ`]strip_assume_tac) >>
  rfs[] >>
  pop_assum mp_tac >>
  discharge_hyps >- metis_tac[] >> strip_tac >>
  Cases_on`e ∈ FDOM σ'` >- metis_tac[] >>
  `∃m mty. typeset τ (SND e) mty ∧ m <: mty` by (
    metis_tac[SND,pair_CASES,typeset_inhabited] ) >>
  qexists_tac`σ' |+ (e,m)` >>
  simp[] >>
  fs[SUBMAP_DEF,FAPPLY_FUPDATE_THM] >>
  conj_tac >- (rw[] >> metis_tac[]) >> rw[] >>
  match_mp_tac term_valuation_FUPDATE >> rw[] >>
  metis_tac[])

val closing_envs_exist = store_thm("closing_envs_exist",
  ``∀σ τ tm. type_valuation τ ∧ term_valuation τ σ ∧
             (∀x ty. VFREE_IN (Var x ty) tm ⇒ ∃mty. typeset τ ty mty)
                 ⇒
      ∃σ' τ'.
        σ ⊑ σ' ∧ τ ⊑ τ' ∧ closes (FDOM σ') (FDOM τ') tm ∧
        type_valuation τ' ∧ term_valuation τ' σ'``,
  rw[closes_def] >>
  Q.ISPEC_THEN`set (tvars tm)`mp_tac covering_type_valuation_exists >>
  simp[] >>
  disch_then(qspec_then`τ`mp_tac) >>
  disch_then(qx_choose_then`τ'`strip_assume_tac) >>
  qspecl_then[`τ'`,`σ`,`tm`]mp_tac covering_sigma_exists >>
  discharge_hyps >- (
    fs[term_valuation_def,FEVERY_DEF] >>
    metis_tac[typeset_extend] ) >>
  strip_tac >>
  qexists_tac`σ'` >>
  qexists_tac`τ'` >>
  simp[])

val has_meaning_Var = store_thm("has_meaning_Var",
  ``∀x ty. has_meaning (Var x ty) ⇔ type_has_meaning ty``,
  rw[has_meaning_def] >>
  simp[Once semantics_cases,FLOOKUP_DEF] >>
  rw[EQ_IMP_THM] >> rw[type_has_meaning_def] >- (
    fs[term_valuation_def,FEVERY_DEF] >>
    metis_tac[SND,typeset_tyvars_typeset_exists,SUBSET_DEF] ) >>
  Q.ISPEC_THEN`set (tyvars ty)`mp_tac covering_type_valuation_exists >>
  simp[] >> (disch_then(qspec_then`FEMPTY`(qx_choose_then`τ`strip_assume_tac))) >> fs[] >>
  qspecl_then[`FEMPTY`,`τ`,`Var x ty`]mp_tac closing_envs_exist >>
  simp[] >>
  discharge_hyps >-
    metis_tac[type_has_meaning_def] >>
  metis_tac[])
val _ = export_rewrites["has_meaning_Var"]

val has_meaning_Comb = store_thm("has_meaning_Comb",
  ``∀s t. has_meaning (Comb s t) ⇔ welltyped (Comb s t) ∧ has_meaning s ∧ has_meaning t``,
  rw[] >> EQ_TAC >> strip_tac >- (
    imp_res_tac has_meaning_welltyped >>
    fs[] >>
    fs[has_meaning_def] >>
    fs[Q.SPECL[`X`,`Y`,`Comb A B`](CONJUNCT2 semantics_cases)] >>
    simp[GSYM CONJ_ASSOC] >> conj_tac >- metis_tac[] >>
    simp[Once CONJ_SYM] >> simp[GSYM CONJ_ASSOC] >> conj_tac >- metis_tac[] >>
    simp[GSYM FORALL_AND_THM,GSYM IMP_CONJ_THM,GSYM AND_IMP_INTRO] >>
    rpt gen_tac >> ntac 2 strip_tac >>
    conj_tac >>
    qmatch_abbrev_tac`closes dσ' dτ' u ⇒ X` >>
    strip_tac >> qunabbrev_tac`X` >>
    qpat_assum`welltyped u`mp_tac >>
    qmatch_assum_abbrev_tac`welltyped v` >>
    strip_tac >>
    Q.ISPEC_THEN`set(tvars v)`mp_tac covering_type_valuation_exists >>
    rw[] >> pop_assum(qspec_then`τ'`mp_tac) >> rw[] >>
    qspecl_then[`σ'`,`τ''`,`v`]mp_tac closing_envs_exist >>
    (discharge_hyps >- (
      simp[] >>
      conj_tac >- (
        fs[term_valuation_def,FEVERY_DEF] >>
        metis_tac[typeset_extend] ) >>
      fs[closes_def,term_valuation_def,FEVERY_DEF] >>
      rw[] >>
      imp_res_tac tvars_VFREE_IN_subset >>
      fs[tvars_def] >>
      metis_tac[typeset_tyvars_typeset_exists,SUBSET_DEF,SND])) >>
    disch_then(qx_choosel_then[`σ''`,`τ'''`]strip_assume_tac) >>
    first_x_assum(qspecl_then[`τ'''`,`σ''`]mp_tac) >>
    simp[] >>
    (discharge_hyps >- metis_tac[closes_extend,SUBMAP_DEF,SUBSET_DEF]) >>
    metis_tac[semantics_reduce,SUBMAP_TRANS] ) >>
  fs[has_meaning_def] >>
  conj_tac >- (
    Q.ISPEC_THEN`set(tvars t)`mp_tac covering_type_valuation_exists >>
    simp[] >> (disch_then(qspec_then`τ`(qx_choose_then`τt`strip_assume_tac))) >> rfs[] >>
    qspecl_then[`σ`,`τt`,`t`]mp_tac closing_envs_exist >>
    simp[] >>
    discharge_hyps >- (
      conj_tac >- (
        fs[term_valuation_def,FEVERY_DEF] >>
        metis_tac[typeset_extend] ) >>
      rw[] >>
      match_mp_tac typeset_tyvars_typeset_exists >>
      fs[closes_def,term_valuation_def,FEVERY_DEF] >>
      imp_res_tac tvars_VFREE_IN_subset >> fs[tvars_def] >>
      metis_tac[SND,SUBSET_DEF] ) >>
    metis_tac[closes_extend,SUBMAP_DEF,SUBSET_DEF] ) >>
  rpt gen_tac >> strip_tac >>
  last_x_assum(qspecl_then[`τ''`,`σ''`]mp_tac) >> simp[] >>
  disch_then(qx_choosel_then[`m1`]strip_assume_tac) >>
  last_x_assum(qspecl_then[`τ''`,`σ''`]mp_tac) >> simp[] >>
  disch_then(qx_choosel_then[`m2`]strip_assume_tac) >>
  simp[Once semantics_cases] >>
  map_every qexists_tac[`m1`,`m2`] >>
  simp[])
val _ = export_rewrites["has_meaning_Comb"]

val has_meaning_Abs = store_thm("has_meaning_Abs",
  ``∀x ty t. has_meaning (Abs x ty t) ⇔ type_has_meaning ty ∧ has_meaning t``,
  rpt gen_tac >>
  EQ_TAC >- (
    simp[has_meaning_def] >>
    strip_tac >>
    first_x_assum(qspecl_then[`τ`,`σ`]mp_tac) >>
    simp[] >>
    simp[Once semantics_cases] >> strip_tac >>
    `∃m. m <: mty` by metis_tac[typeset_inhabited] >>
    first_x_assum(qspec_then`m`mp_tac) >>
    simp[] >> strip_tac >>
    `term_valuation τ (σ|+((x,ty),m))` by (
      match_mp_tac term_valuation_FUPDATE >>
      simp[] >> metis_tac[] ) >>
    conj_tac >- metis_tac[semantics_typeset,typeset_has_meaning] >>
    conj_tac >- metis_tac[FDOM_FUPDATE] >>
    rw[] >>
    match_mp_tac semantics_frees_exists >>
    map_every qexists_tac[`τ`,`σ|+((x,ty),m)`,`mb m`] >>
    simp[] >>
    fs[closes_def,SUBSET_DEF] ) >>
  rw[has_meaning_def] >- (
    Q.ISPEC_THEN`set (tyvars ty)`mp_tac covering_type_valuation_exists >>
    simp[] >> (disch_then(qspec_then`τ`mp_tac)) >>
    strip_tac >> rfs[] >>
    map_every qexists_tac[`τ'`,`σ`] >>
    simp[] >>
    conj_tac >- (
      fs[term_valuation_def,FEVERY_DEF] >>
      metis_tac[typeset_extend] ) >>
    match_mp_tac closes_extend >>
    fs[SUBMAP_DEF,SUBSET_DEF] >>
    metis_tac[] ) >>
  simp[Once semantics_cases] >>
  `∃mty. typeset τ' ty mty` by metis_tac[type_has_meaning_def] >>
  CONV_TAC (RESORT_EXISTS_CONV List.rev) >>
  `welltyped t ∧ ∃mtyb. typeset τ (typeof t) mtyb` by (
    metis_tac[semantics_typeset] ) >>
  `∃mtyb'. typeset τ' (typeof t) mtyb'` by (
    match_mp_tac typeset_tyvars_typeset_exists >>
    fs[WELLTYPED] >>
    imp_res_tac tyvars_typeof_subset_tvars >>
    fs[closes_def,SUBSET_DEF] >>
    metis_tac[] ) >>
  map_every qexists_tac[`typeof t`,`mtyb'`,`mty`] >>
  simp[GSYM WELLTYPED] >>
  simp[GSYM SKOLEM_THM] >>
  qx_gen_tac`z` >>
  simp[RIGHT_EXISTS_IMP_THM] >>
  strip_tac >>
  first_x_assum(qspecl_then[`τ'`,`σ' |+ ((x,ty),z)`]mp_tac) >>
  discharge_hyps >- (
    simp[] >>
    metis_tac[term_valuation_FUPDATE,FST,SND] ) >>
  disch_then(qx_choosel_then[`y`] strip_assume_tac) >>
  qexists_tac`y` >> simp[] >>
  metis_tac[semantics_typeset,term_valuation_FUPDATE,FST,SND,WELLTYPED_LEMMA,semantics_11])
val _ = export_rewrites["has_meaning_Abs"]

val semantics_has_meaning = prove(
  ``(∀τ ty m. typeset τ ty m ⇒ T) ∧
    (∀σ τ t m. semantics σ τ t m ⇒ term_valuation τ σ ∧ type_valuation τ ⇒ has_meaning t)``,
  ho_match_mp_tac (theorem"semantics_strongind") >> simp[] >>
  conj_tac >- (
    simp[has_meaning_def,Once semantics_cases] >> rw[FLOOKUP_DEF] >>
    fs[term_valuation_def,type_has_meaning_def,FEVERY_DEF] >>
    metis_tac[typeset_tyvars_typeset_exists,SND,SUBSET_DEF]) >>
  conj_tac >- (
    rw[has_meaning_def,tyvars_def] >- (
      Q.ISPEC_THEN`set (tyvars ty)`mp_tac covering_type_valuation_exists >>
      simp[] >> disch_then(qspec_then`τ`mp_tac) >>
      rw[] >>
      fs[term_valuation_def,FEVERY_DEF] >>
      metis_tac[typeset_extend] ) >>
    rw[Once semantics_cases] >>
    imp_res_tac typeset_has_meaning >>
    fs[type_has_meaning_def,tyvars_def] ) >>
  conj_tac >- (
    rw[has_meaning_def,tyvars_def] >- (
      Q.ISPEC_THEN`set (tyvars ty)`mp_tac covering_type_valuation_exists >>
      simp[] >> disch_then(qspec_then`τ`mp_tac) >>
      rw[] >>
      fs[term_valuation_def,FEVERY_DEF] >>
      metis_tac[typeset_extend] ) >>
    rw[Once semantics_cases] >>
    imp_res_tac typeset_has_meaning >>
    fs[type_has_meaning_def,tyvars_def] ) >>
  conj_tac >- (
    rw[has_meaning_def] >- (
      fs[closes_def,tvars_simple_inst,tyvars_tyinst] >>
      fs[SUBSET_DEF] >>
      metis_tac[tyvars_typeof_subset_tvars,SUBSET_DEF,WELLTYPED] ) >>
    rw[Once semantics_cases] >>
    metis_tac[] ) >>
  conj_tac >- (
    rw[has_meaning_def] >- (
      imp_res_tac typeset_closes_over >>
      fs[tyvars_def] >>
      metis_tac[] ) >>
    rw[Once semantics_cases] >>
    CONV_TAC SWAP_EXISTS_CONV >>
    HINT_EXISTS_TAC >> rw[] >>
    imp_res_tac typeset_has_meaning >>
    fs[type_has_meaning_def] >>
    first_x_assum match_mp_tac >>
    fs[tyvars_def] ) >>
  conj_tac >- (
    rw[has_meaning_def] >- (
      imp_res_tac typeset_closes_over >>
      fs[tyvars_def] >>
      metis_tac[] ) >>
    rw[Once semantics_cases] >>
    CONV_TAC (RESORT_EXISTS_CONV List.rev) >>
    HINT_EXISTS_TAC >>
    qexists_tac`m'` >> rw[] >>
    imp_res_tac typeset_has_meaning >>
    fs[type_has_meaning_def] >>
    first_x_assum match_mp_tac >>
    fs[tyvars_def] ) >>
  rw[has_meaning_def] >- (
    fs[term_valuation_def,type_has_meaning_def,FEVERY_DEF] >>
    metis_tac[typeset_tyvars_typeset_exists,SND,SUBSET_DEF]) >>
  `∃a. a <: m` by metis_tac[typeset_inhabited] >>
  first_x_assum(qspec_then`a`mp_tac) >> rw[] >>
  pop_assum mp_tac >>
  (discharge_hyps_keep >- (
    match_mp_tac term_valuation_FUPDATE >>
    simp[] >> metis_tac[])) >>
  rw[])
val semantics_has_meaning = save_thm("semantics_has_meaning",MP_CANON (CONJUNCT2 semantics_has_meaning))

val closes_aconv = store_thm("closes_aconv",
  ``∀t1 t2 s t. ACONV t1 t2 ∧ closes s t t1 ⇒ closes s t t2``,
  rw[closes_def] >>
  metis_tac[ACONV_tvars,ACONV_VFREE_IN,ACONV_SYM])

val has_meaning_aconv = store_thm("has_meaning_aconv",
  ``∀t t'. has_meaning t ∧ ACONV t t' ⇒ has_meaning t'``,
  rw[] >>
  imp_res_tac has_meaning_welltyped >>
  fs[has_meaning_def] >> rw[] >>
  metis_tac[semantics_aconv,ACONV_SYM,closes_aconv,ACONV_welltyped])

val type_valuation_union = store_thm("type_valuation_union",
  ``type_valuation t1 ∧ type_valuation t2 ⇒ type_valuation (t1 ⊌ t2)``,
  rw[type_valuation_def,IN_FRANGE,FUNION_DEF] >> rw[] >>
  metis_tac[])

val term_valuation_extend_type = store_thm("term_valuation_extend_type",
  ``∀s t t'. term_valuation t s ∧ t ⊑ t' ⇒ term_valuation t' s``,
  rw[term_valuation_def,FEVERY_DEF] >> metis_tac[typeset_extend])

val equation_has_meaning = store_thm("equation_has_meaning",
  ``∀s t ty. has_meaning s ∧ has_meaning t ∧ typeof s = typeof t ⇒ has_meaning (s === t)``,
  rw[] >>
  imp_res_tac has_meaning_welltyped >>
  rfs[WELLTYPED] >>
  rw[has_meaning_def] >- (
    fs[has_meaning_def] >>
    last_x_assum(qspecl_then[`τ`,`σ`]mp_tac) >> simp[] >>
    disch_then(qx_choosel_then[`ms`]strip_assume_tac) >>
    qspecl_then[`σ`,`τ ⊌ τ'`,`t`]mp_tac closing_envs_exist >>
    discharge_hyps >- (
      simp[type_valuation_union] >>
      reverse conj_tac >- (
        fs[closes_def,term_valuation_def,FEVERY_DEF] >>
        metis_tac[typeset_tyvars_typeset_exists,typeset_closes_over,SUBSET_DEF,SND,FUNION_DEF,IN_UNION] ) >>
      fs[term_valuation_def,FEVERY_DEF] >>
      rw[] >> res_tac >>
      qexists_tac`mty` >> rw[] >>
      match_mp_tac typeset_tyvars >>
      qexists_tac`τ` >>
      rw[FLOOKUP_FUNION] >>
      BasicProvers.CASE_TAC >>
      fs[FLOOKUP_DEF] ) >>
    disch_then(qx_choosel_then[`σt`,`τt`]strip_assume_tac) >>
    map_every qexists_tac[`τt`,`σt`] >>
    rw[] >>
    match_mp_tac(MP_CANON(GEN_ALL(DISCH_ALL(snd(EQ_IMP_RULE(UNDISCH_ALL closes_equation))))))>>
    qexists_tac`typeof t` >>
    rw[] >>
    match_mp_tac closes_extend >>
    map_every qexists_tac[`FDOM σ`,`FDOM τ`] >>
    fs[SUBMAP_DEF,SUBSET_DEF] ) >>
  fs[has_meaning_def] >>
  `closes (FDOM σ) (FDOM τ) s ∧
   closes (FDOM σ) (FDOM τ) t` by
    metis_tac[closes_equation] >>
  `∃ms mt. semantics σ τ s ms ∧ semantics σ τ t mt` by metis_tac[] >>
  qexists_tac`boolean (ms = mt)` >>
  match_mp_tac semantics_equation >>
  metis_tac[])

val equation_has_meaning_iff = store_thm("equation_has_meaning_iff",
  ``∀s t. has_meaning (s === t) ⇔ has_meaning s ∧ has_meaning t ∧ typeof s = typeof t``,
  rw[] >> reverse EQ_TAC >- metis_tac[equation_has_meaning] >>
  simp[has_meaning_def] >> strip_tac >>
  simp[GSYM CONJ_ASSOC] >>
  `welltyped s ∧ welltyped t ∧ typeof s = typeof t` by
    metis_tac[semantics_equation_imp,semantics_typeset] >>
  simp[] >>
  conj_tac >- metis_tac[closes_equation,WELLTYPED] >>
  simp[Once CONJ_SYM] >>
  simp[GSYM CONJ_ASSOC] >>
  conj_tac >- metis_tac[closes_equation,WELLTYPED] >>
  simp[GSYM FORALL_AND_THM,GSYM IMP_CONJ_THM,GSYM AND_IMP_INTRO] >>
  qx_genl_tac[`t0`,`s0`] >> ntac 2 strip_tac >>
  conj_tac >>
  qmatch_abbrev_tac`closes fs0 ft0 u ⇒ X` >> strip_tac >>
  qpat_assum`welltyped u`mp_tac >>
  qmatch_assum_abbrev_tac`welltyped v` >> strip_tac >>
  qspecl_then[`s0`,`t0 ⊌ τ`,`v`]mp_tac closing_envs_exist >>
  (discharge_hyps >- (
    simp[type_valuation_union] >>
    `closes (FDOM σ) (FDOM τ) v` by metis_tac[closes_equation,WELLTYPED] >>
    reverse conj_tac >- (
      fs[closes_def,term_valuation_def,FEVERY_DEF] >>
      PROVE_TAC[typeset_tyvars_typeset_exists,typeset_closes_over,SUBSET_DEF,SND,FUNION_DEF,IN_UNION] ) >>
    fs[closes_def,term_valuation_def,FEVERY_DEF,SUBSET_DEF] >>
    rw[] >>
    qsuff_tac`t0 ⊑ t0 ⊌ τ`>-metis_tac[typeset_extend] >>
    simp[SUBMAP_DEF,FUNION_DEF] )) >>
  disch_then(qx_choosel_then[`σt`,`τt`]strip_assume_tac) >>
  first_x_assum(qspecl_then[`τt`,`σt`]mp_tac) >>
  (discharge_hyps >- (
    simp[] >>
    qsuff_tac`closes (FDOM σt) (FDOM τt) u` >- (
      metis_tac[closes_equation,WELLTYPED] ) >>
    match_mp_tac closes_extend >>
    map_every qexists_tac[`fs0`,`ft0`] >>
    simp[Abbr`fs0`,Abbr`ft0`] >>
    fs[SUBMAP_DEF,SUBSET_DEF] )) >>
  `t0 ⊑ τt` by (
    metis_tac[SUBMAP_TRANS,SUBMAP_FUNION,SUBMAP_REFL] ) >>
  PROVE_TAC[semantics_equation_imp,semantics_reduce])

val _ = Parse.add_infix("|=",450,Parse.NONASSOC)

val sequent_def = xDefine"sequent"`
  h |= c ⇔ EVERY (λt. t has_type Bool) (c::h) ∧
           EVERY has_meaning (c::h) ∧
           ∀σ τ. type_valuation τ ∧
                 term_valuation τ σ ∧
                 EVERY (λt. semantics σ τ t true) h ∧
                 closes (FDOM σ) (FDOM τ) c
                 ⇒
                 semantics σ τ c true`

val ASSUME_correct = store_thm("ASSUME_correct",
  ``∀p. has_meaning p ∧ p has_type Bool ⇒ [p] |= p``,
  rw[sequent_def])

val REFL_correct = store_thm("REFL_correct",
  ``∀t. has_meaning t ⇒ [] |= t === t``,
  rw[sequent_def,EQUATION_HAS_TYPE_BOOL,has_meaning_welltyped,equation_has_meaning] >>
  match_mp_tac semantics_equation >>
  imp_res_tac has_meaning_welltyped >>
  fs[has_meaning_def,WELLTYPED] >>
  imp_res_tac closes_equation >>
  simp[boolean_def] >>
  metis_tac[])

val has_meaning_subterm = store_thm("has_meaning_subterm",
  ``∀tm. has_meaning tm ⇒ ∀st. VFREE_IN st tm ⇒ has_meaning st``,
  Induct >> rw[] >> fs[])

val binary_inference_rule = store_thm("binary_inference_rule",
  ``∀h1 h2 p1 p2 q.
    (p1 has_type Bool ∧ p2 has_type Bool ⇒ q has_type Bool) ∧
    (has_meaning p1 ∧ has_meaning p2 ⇒ has_meaning q) ∧
    (∀σ τ. type_valuation τ ∧ term_valuation τ σ ∧
           semantics σ τ p1 true ∧ semantics σ τ p2 true ∧
           closes (FDOM σ) (FDOM τ) q ⇒
           semantics σ τ q true) ∧
    h1 |= p1 ∧ h2 |= p2
    ⇒ TERM_UNION h1 h2 |= q``,
  rpt gen_tac >> strip_tac >>
  fs[sequent_def,ALL_BOOL_TERM_UNION] >>
  conj_tac >- (
    fs[EVERY_MEM] >>
    metis_tac[TERM_UNION_NONEW,TERM_UNION_THM,has_meaning_aconv] ) >>
  rw[] >>
  `∀x ty. VFREE_IN (Var x ty) p1 ⇒ type_has_meaning ty` by
    metis_tac[has_meaning_subterm,has_meaning_Var] >>
  `∀x ty. VFREE_IN (Var x ty) p2 ⇒ type_has_meaning ty` by
    metis_tac[has_meaning_subterm,has_meaning_Var] >>
  `∀x ty. VFREE_IN (Var x ty) q ⇒ type_has_meaning ty` by
    metis_tac[has_meaning_subterm,has_meaning_Var] >>
  Q.ISPEC_THEN`set(tvars p1)`mp_tac covering_type_valuation_exists >> simp[] >>
  disch_then(qspec_then`τ`(qx_choose_then`τ0`strip_assume_tac)) >>
  qspecl_then[`σ`,`τ0`,`p1`]mp_tac closing_envs_exist >> rfs[] >>
  discharge_hyps >- (
    conj_tac >- metis_tac[term_valuation_extend_type] >>
    rw[] >> imp_res_tac tvars_VFREE_IN_subset >> fs[tvars_def] >>
    metis_tac[type_has_meaning_def,SUBSET_TRANS] ) >>
  disch_then(qx_choosel_then[`σ1`,`τ1`]strip_assume_tac) >>
  `EVERY (λt. semantics σ1 τ1 t true) h1` by (
    fs[EVERY_MEM] >> rw[] >>
    `∃t'. ACONV t t' ∧ semantics σ τ t' true` by metis_tac[TERM_UNION_THM] >>
    `semantics σ τ t true` by metis_tac[semantics_aconv,has_meaning_welltyped] >>
    metis_tac[semantics_extend,SUBMAP_TRANS] ) >>
  `semantics σ1 τ1 p1 true` by (
    first_x_assum match_mp_tac >>
    simp[] ) >>
  Q.ISPEC_THEN`set(tvars p2)`mp_tac covering_type_valuation_exists >> simp[] >>
  disch_then(qspec_then`τ1`(qx_choose_then`τ00`strip_assume_tac)) >>
  qspecl_then[`σ1`,`τ00`,`p2`]mp_tac closing_envs_exist >> rfs[] >>
  discharge_hyps >- (
    conj_tac >- metis_tac[term_valuation_extend_type] >>
    rw[] >> imp_res_tac tvars_VFREE_IN_subset >> fs[tvars_def] >>
    metis_tac[type_has_meaning_def,SUBSET_TRANS] ) >>
  disch_then(qx_choosel_then[`σ2`,`τ2`]strip_assume_tac) >>
  `EVERY (λt. semantics σ2 τ2 t true) h2` by (
    fs[EVERY_MEM] >> rw[] >>
    `∃t'. ACONV t t' ∧ semantics σ τ t' true` by metis_tac[TERM_UNION_THM] >>
    `semantics σ τ t true` by metis_tac[semantics_aconv,has_meaning_welltyped] >>
    metis_tac[semantics_extend,SUBMAP_TRANS] ) >>
  `semantics σ2 τ2 p2 true` by (
    first_x_assum match_mp_tac >>
    simp[] ) >>
  Q.ISPEC_THEN`set(tvars q)`mp_tac covering_type_valuation_exists >> simp[] >>
  disch_then(qspec_then`τ2`(qx_choose_then`τ000`strip_assume_tac)) >>
  qspecl_then[`σ2`,`τ000`,`q`]mp_tac closing_envs_exist >> rfs[] >>
  discharge_hyps >- (
    conj_tac >- metis_tac[term_valuation_extend_type] >>
    rw[] >> imp_res_tac tvars_VFREE_IN_subset >> fs[tvars_def] >>
    metis_tac[type_has_meaning_def,SUBSET_TRANS] ) >>
  disch_then(qx_choosel_then[`σ3`,`τ3`]strip_assume_tac) >>
  `semantics σ3 τ3 p1 true` by (
    match_mp_tac semantics_extend >>
    metis_tac[SUBMAP_TRANS] ) >>
  `semantics σ3 τ3 p2 true` by (
    match_mp_tac semantics_extend >>
    metis_tac[SUBMAP_TRANS] ) >>
  match_mp_tac semantics_reduce >>
  map_every qexists_tac[`τ3`,`σ3`] >>
  simp[] >>
  metis_tac[SUBMAP_TRANS])

val TRANS_correct = store_thm("TRANS_correct",
  ``∀h1 h2 l m1 m2 r.
      h1 |= l === m1 ∧ h2 |= m2 === r ∧ ACONV m1 m2
      ⇒ TERM_UNION h1 h2 |= l === r``,
  rw[] >> match_mp_tac binary_inference_rule >>
  map_every qexists_tac[`l === m1`,`m2 === r`] >>
  simp[EQUATION_HAS_TYPE_BOOL] >>
  conj_tac >- metis_tac[ACONV_TYPE] >>
  conj_tac >- (
    fs[equation_has_meaning_iff] >>
    metis_tac[has_meaning_welltyped,ACONV_TYPE] ) >>
  rw[] >>
  match_mp_tac semantics_equation >>
  qspecl_then[`σ`,`τ`,`l`,`m1`,`true`]mp_tac semantics_equation_imp >> simp[] >>
  disch_then(qx_choosel_then[`ml`,`mm1`]strip_assume_tac) >>
  qspecl_then[`σ`,`τ`,`m2`,`r`,`true`]mp_tac semantics_equation_imp >> simp[] >>
  disch_then(qx_choosel_then[`mm2`,`mr`]strip_assume_tac) >>
  map_every qexists_tac[`ml`,`mr`] >>
  `semantics σ τ m1 mm2` by metis_tac[semantics_aconv,semantics_typeset] >>
  `mm1 = mm2` by metis_tac[semantics_11] >>
  `typeof m1 = typeof m2` by metis_tac[ACONV_TYPE,semantics_typeset] >>
  fs[BOOLEAN_EQ_TRUE])

val MK_COMB_correct = store_thm("MK_COMB_correct",
  ``∀h1 h2 l1 r1 l2 r2.
      h1 |= l1 === r1 ∧ h2 |= l2 === r2 ∧
      (∃rty. typeof l1 = Fun (typeof l2) rty)
      ⇒ TERM_UNION h1 h2 |= Comb l1 l2 === Comb r1 r2``,
  rw[] >>
  match_mp_tac binary_inference_rule >>
  map_every qexists_tac[`l1 === r1`,`l2 === r2`] >>
  conj_tac >- (
    rw[EQUATION_HAS_TYPE_BOOL] >>
    metis_tac[] ) >>
  conj_tac >- (
    rw[equation_has_meaning_iff] >>
    simp[has_meaning_Comb] >>
    metis_tac[has_meaning_welltyped ] ) >>
  rw[] >>
  match_mp_tac semantics_equation >>
  qspecl_then[`σ`,`τ`,`l1`,`r1`,`true`]mp_tac semantics_equation_imp >> simp[] >>
  disch_then(qx_choosel_then[`ml1`,`mr1`]strip_assume_tac) >>
  qspecl_then[`σ`,`τ`,`l2`,`r2`,`true`]mp_tac semantics_equation_imp >> simp[] >>
  disch_then(qx_choosel_then[`ml2`,`mr2`]strip_assume_tac) >>
  simp[Once semantics_cases] >>
  simp[Once (Q.SPECL[`X`,`Y`,`Comb A Z`](CONJUNCT2 semantics_cases))] >>
  simp_tac(srw_ss()++DNF_ss)[] >>
  map_every qexists_tac[`ml1`,`ml2`,`rty`,`mr1`,`mr2`,`rty`] >>
  simp[] >> fs[] >>
  simp[CONJ_ASSOC] >>
  conj_tac >- (
    metis_tac[semantics_typeset,codomain_rwt] ) >>
  fs[BOOLEAN_EQ_TRUE])

val EQ_MP_correct = store_thm("EQ_MP_correct",
  ``∀h1 h2 p q p'.
      h1 |= p === q ∧ h2 |= p' ∧ ACONV p p' ⇒
      TERM_UNION h1 h2 |= q``,
  rw[] >>
  match_mp_tac binary_inference_rule >>
  map_every qexists_tac[`p === q`,`p'`] >>
  simp[EQUATION_HAS_TYPE_BOOL] >>
  conj_tac >- metis_tac[ACONV_welltyped,ACONV_TYPE,WELLTYPED,WELLTYPED_LEMMA] >>
  conj_tac >- metis_tac[equation_has_meaning_iff] >>
  rw[] >>
  qspecl_then[`σ`,`τ`,`p`,`q`,`true`]mp_tac semantics_equation_imp >>
  rw[] >>
  fs[sequent_def,EQUATION_HAS_TYPE_BOOL] >>
  fs[BOOLEAN_EQ_TRUE] >>
  `ms = true` by metis_tac[semantics_aconv,semantics_11] >>
  rw[])

val BETA_correct = store_thm("BETA_correct",
  ``∀x ty t. type_has_meaning ty ∧ has_meaning t ⇒ [] |= Comb (Abs x ty t) (Var x ty) === t``,
  simp[sequent_def,EQUATION_HAS_TYPE_BOOL] >>
  rpt gen_tac >> strip_tac >>
  conj_asm1_tac >- metis_tac[has_meaning_welltyped] >>
  simp[equation_has_meaning_iff,has_meaning_Comb,has_meaning_Abs,has_meaning_Var] >>
  rw[] >>
  match_mp_tac semantics_equation >>
  simp[BOOLEAN_EQ_TRUE] >>
  simp[Once semantics_cases] >>
  simp[Once semantics_cases] >>
  simp[Once (Q.SPECL[`X`,`Y`,`Var A B`](CONJUNCT2 semantics_cases))] >>
  srw_tac[DNF_ss][FLOOKUP_DEF] >>
  qmatch_assum_abbrev_tac`closes fs ft (l === r)` >>
  `closes fs ft l ∧ closes fs ft r` by (
    fs[WELLTYPED] >>
    `l has_type (typeof r)` by (
      simp[Abbr`l`,Once has_type_cases] >>
      simp[Once has_type_cases] >>
      simp[Once has_type_cases] ) >>
    metis_tac[closes_equation] ) >>
  unabbrev_all_tac >>
  fs[type_has_meaning_def,has_meaning_def] >>
  `∃mty. typeset τ ty mty` by metis_tac[] >>
  CONV_TAC (RESORT_EXISTS_CONV List.rev) >>
  `∃mtyb. typeset τ (typeof t) mtyb` by (
    metis_tac[semantics_typeset] ) >>
  map_every qexists_tac[`typeof t`,`mtyb`,`mty`] >>
  simp[GSYM WELLTYPED] >>
  qmatch_abbrev_tac`G` >>
  qpat_assum`∀x y. P ∧ Q ⇒ R`mp_tac >>
  simp[GSYM RIGHT_EXISTS_IMP_THM] >>
  simp[SKOLEM_THM] >>
  disch_then(qx_choose_then`mf`strip_assume_tac) >>
  simp[Abbr`G`] >>
  qexists_tac`λz. mf τ (σ |+ ((x,ty),z))` >>
  simp[CONJ_ASSOC,GSYM FORALL_AND_THM,GSYM IMP_CONJ_THM] >>
  conj_asm1_tac >- (
    qx_gen_tac`z` >> strip_tac >>
    first_x_assum(qspecl_then[`τ`,`σ |+ ((x,ty),z)`]mp_tac) >>
    discharge_hyps_keep >- (
      simp[] >>
      metis_tac[term_valuation_FUPDATE,FST,SND]) >>
    strip_tac >>
    reverse conj_asm2_tac >- (
      match_mp_tac semantics_reduce >>
      map_every qexists_tac[`τ`,`σ|+((x,ty),z)`] >>
      simp[] ) >>
    metis_tac[semantics_typeset,semantics_11] ) >>
  `σ ' (x,ty) <: mty` by (
    qpat_assum`term_valuation τ σ`(fn th=> ASSUME_TAC th >> mp_tac th) >>
    simp_tac std_ss [term_valuation_def,FEVERY_DEF] >>
    disch_then(qspec_then`x,ty`mp_tac) >>
    simp[] >>
    metis_tac[semantics_11] ) >>
  qmatch_abbrev_tac`semantics σ τ t (apply (abstract mty mtyb f) e)` >>
  `apply (abstract mty mtyb f) e = f e` by (
    match_mp_tac APPLY_ABSTRACT >>
    simp[Abbr`f`,Abbr`e`] ) >>
  simp[Abbr`f`,Abbr`e`] >>
  metis_tac[FUPDATE_ELIM])

val ABS_correct = store_thm("ABS_correct",
  ``∀x ty h l r.
    ¬EXISTS (VFREE_IN (Var x ty)) h ∧ h |= l === r ∧ type_has_meaning ty ⇒
    h |= Abs x ty l === Abs x ty r``,
  rw[] >>
  fs[sequent_def,EQUATION_HAS_TYPE_BOOL,equation_has_meaning_iff,has_meaning_Abs] >> rw[] >>
  match_mp_tac semantics_equation >> simp[] >>
  simp[Once semantics_cases] >>
  simp[Once (Q.SPECL[`X`,`Y`,`Abs A B Z`](CONJUNCT2 semantics_cases))] >>
  srw_tac[DNF_ss][BOOLEAN_EQ_TRUE] >>
  qmatch_assum_abbrev_tac`closes fs ft (fl === fr)` >>
  `closes fs ft fl ∧ closes fs ft fr` by (
    qsuff_tac`∃ty. fl has_type ty ∧ fr has_type ty` >- metis_tac[closes_equation] >>
    qexists_tac`Fun ty (typeof l)` >>
    simp[Abbr`fl`,Abbr`fr`,Once has_type_cases] >>
    fs[WELLTYPED] >> simp[Once has_type_cases] ) >>
  `set (tyvars ty) ⊆ ft` by (
    fs[Abbr`fl`,closes_def] ) >>
  `∃mty. typeset τ ty mty` by metis_tac[type_has_meaning_def] >>
  qabbrev_tac`σ0 = σ \\ (x,ty)` >>
  `term_valuation τ σ0` by (
    fs[term_valuation_def,Abbr`σ0`] >>
    fs[FEVERY_DEF] >>
    simp[DOMSUB_FAPPLY_THM] ) >>
  `EVERY (λt. semantics σ0 τ t true) h` by (
    fs[EVERY_MEM] >> rw[] >>
    match_mp_tac semantics_reduce >>
    map_every qexists_tac[`τ`,`σ`] >> simp[] >>
    conj_tac >- metis_tac[SUBMAP_DOMSUB] >>
    simp[Abbr`σ0`] >>
    `closes fs ft t` by metis_tac[semantics_closes] >>
    fs[closes_def]) >>
  `∀z. z <: mty ⇒
      term_valuation τ (σ0 |+ ((x,ty),z)) ∧
      semantics (σ0 |+ ((x,ty),z)) τ (l === r) true` by (
    gen_tac >> strip_tac >>
    conj_asm1_tac >- metis_tac[term_valuation_FUPDATE,FST,SND] >>
    first_x_assum match_mp_tac >> simp[] >>
    conj_tac >- (
      fs[EVERY_MEM] >> rw[] >>
      match_mp_tac semantics_extend >>
      map_every qexists_tac[`σ0`,`τ`] >>
      simp[] >> simp[Abbr`σ0`] ) >>
    match_mp_tac(MP_CANON(GEN_ALL(DISCH_ALL(snd(EQ_IMP_RULE(UNDISCH closes_equation)))))) >>
    fs[WELLTYPED,Abbr`σ0`,closes_def] >>
    qexists_tac`typeof r`>>simp[]>>
    fs[Abbr`fl`,Abbr`fr`,tvars_def] >>
    metis_tac[]) >>
  `∃m. ∀z. z <: mty ⇒
    semantics (σ0 |+ ((x,ty),z)) τ l (m z) ∧
    semantics (σ0 |+ ((x,ty),z)) τ r (m z)` by (
      simp[GSYM SKOLEM_THM,RIGHT_EXISTS_IMP_THM] >> rw[] >>
      first_x_assum(qspec_then`z`mp_tac) >> rw[] >>
      imp_res_tac semantics_equation_imp >>
      fs[BOOLEAN_EQ_TRUE] >>
      metis_tac[] ) >>
  `∃z. z <: mty` by metis_tac[typeset_inhabited] >>
  `∃mtyb. typeset τ (typeof l) mtyb` by metis_tac[semantics_typeset] >>
  map_every qexists_tac[`m`,`mty`,`mtyb`,`typeof l`,`m`,`mty`,`mtyb`,`typeof l`] >>
  simp[] >> fs[WELLTYPED] >>
  metis_tac[semantics_typeset,semantics_11,FUPDATE_PURGE])

val DEDUCT_ANTISYM_correct = store_thm("DEDUCT_ANTISYM_correct",
  ``∀h1 p1 h2 p2.
      h1 |= p1 ∧ h2 |= p2 ⇒
      TERM_UNION (FILTER ($~ o ACONV p2) h1)
                 (FILTER ($~ o ACONV p1) h2)
      |= p1 === p2``,
  rw[] >>
  fs[sequent_def,EQUATION_HAS_TYPE_BOOL] >>
  imp_res_tac has_meaning_welltyped >>
  imp_res_tac WELLTYPED_LEMMA >>
  fs[] >>
  simp[equation_has_meaning_iff] >>
  simp[CONJ_ASSOC] >>
  conj_tac >- (
    fs[EVERY_MEM] >>
    metis_tac[TERM_UNION_NONEW,MEM_FILTER] ) >>
  rpt gen_tac >>
  qspecl_then[`FDOM σ`,`FDOM τ`,`p1`,`p2`,`Bool`]mp_tac(Q.GENL[`ty`,`r`,`l`,`τ`,`σ`]closes_equation) >>
  rw[] >>
  match_mp_tac semantics_equation >>
  simp[BOOLEAN_EQ_TRUE] >>
  fs[EVERY_MEM] >>
  rpt(first_x_assum(qspecl_then[`σ`,`τ`]mp_tac)) >> simp[] >>
  qmatch_abbrev_tac`(a ⇒ b) ⇒ (c ⇒ d) ⇒ e` >>
  `∀x y ls. MEM x (FILTER ($~ o ACONV y) ls) ⇔ ¬ACONV y x ∧ MEM x ls` by simp[MEM_FILTER] >>
  `d ⇒ a` by (
    unabbrev_all_tac >> rw[] >>
    Cases_on`ACONV p2 t`>-metis_tac[semantics_aconv] >>
    metis_tac[TERM_UNION_THM,semantics_aconv,welltyped_def] ) >>
  `b ⇒ c` by (
    unabbrev_all_tac >> rw[] >>
    Cases_on`ACONV p1 t`>-metis_tac[semantics_aconv] >>
    metis_tac[TERM_UNION_THM,semantics_aconv,welltyped_def] ) >>
  ntac 2 strip_tac >>
  `a = d ∧ b = d ∧ c = d` by metis_tac[] >> fs[] >>
  Cases_on`d` >> fs[markerTheory.Abbrev_def] >- metis_tac[] >>
  `∃m1 m2. semantics σ τ p1 m1 ∧ semantics σ τ p2 m2` by (
    metis_tac[has_meaning_def,semantics_reduce] ) >>
  metis_tac[semantics_typeset,typeset_Bool,WELLTYPED_LEMMA,IN_BOOL])

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

val semantics_simple_subst = store_thm("semantics_simple_subst",
  ``∀tm subst ss σ τ.
      DISJOINT (set (bv_names tm)) {y | ∃ty u. VFREE_IN (Var y ty) u ∧ u ∈ FRANGE subst} ∧
      FEVERY (λ((x,ty),tm). tm has_type ty) subst ∧
      FDOM subst = FDOM ss ∧
      FEVERY (λ(v,m). semantics σ τ (subst ' v) m) ss ∧
      closes (FDOM (ss ⊌ σ)) (FDOM τ) tm ∧
      welltyped tm ∧
      type_valuation τ
      ⇒
      semantics σ τ (simple_subst subst tm) = semantics (ss ⊌ σ) τ tm``,
  Induct >- (
    rpt gen_tac >> simp[] >>
    Cases_on`(s,t) ∈ FDOM ss` >- (
      rw[] >>
      simp[FLOOKUPD_def,FUN_EQ_THM] >> rw[] >>
      fs[FEVERY_DEF,FLOOKUP_DEF,SUBSET_DEF] >>
      simp[Once semantics_cases,SimpRHS] >>
      fs[FLOOKUP_DEF,FUNION_DEF] >>
      metis_tac[semantics_11] ) >>
    rw[] >>
    simp[FLOOKUPD_def,FUN_EQ_THM] >> rw[] >>
    fs[FEVERY_DEF,FLOOKUP_DEF,SUBSET_DEF] >>
    simp[Once semantics_cases,SimpRHS] >>
    simp[Once semantics_cases] >>
    fs[FLOOKUP_DEF,FUNION_DEF])
  >- (
    rw[] >>
    simp[FUN_EQ_THM] >>
    simp[Once semantics_cases] >>
    simp[Once semantics_cases,SimpRHS] )
  >- (
    rw[] >>
    simp[FUN_EQ_THM] >>
    simp[Once semantics_cases] >>
    simp[Once semantics_cases,SimpRHS] >>
    `simple_subst subst tm has_type (typeof tm) ∧
     simple_subst subst tm' has_type (typeof tm')` by (
       fs[WELLTYPED] >>
       metis_tac[simple_subst_has_type] ) >>
    imp_res_tac WELLTYPED_LEMMA >>
    pop_assum(assume_tac o SYM) >>
    fs[] >> simp[WELLTYPED] >>
    metis_tac[] ) >>
  rw[] >>
  simp[FUN_EQ_THM] >>
  simp[Once semantics_cases] >>
  simp[Once semantics_cases,SimpRHS] >>
  rw[] >>
  rw[EQ_IMP_THM] >>
  map_every qexists_tac[`mb`,`mty`,`mtyb`,`tyb`] >>
  rw[] >>
  TRY (
    qmatch_assum_abbrev_tac`simple_subst sub tm has_type tyb` >>
    qsuff_tac`tyb = typeof tm` >- metis_tac[WELLTYPED] >>
    qsuff_tac`simple_subst sub tm has_type (typeof tm)` >- metis_tac[WELLTYPED_LEMMA] >>
    match_mp_tac (MP_CANON simple_subst_has_type) >>
    fs[WELLTYPED] >>
    fs[FEVERY_DEF,Abbr`sub`,DOMSUB_FAPPLY_THM] ) >>
  TRY (
    match_mp_tac (MP_CANON simple_subst_has_type) >>
    fs[FEVERY_DEF,DOMSUB_FAPPLY_THM] ) >>
  qmatch_abbrev_tac`semantics sx τ stm mm` >>
  first_x_assum(qspec_then`m`mp_tac) >> rw[] >>
  qmatch_assum_abbrev_tac`semantics sy τ ttm mm` >>
  qsuff_tac`semantics sx τ stm = semantics sy τ ttm` >- rw[] >>
  first_x_assum(qspecl_then[`subst \\ (s,t)`,`ss \\ (s,t)`,`σ |+ ((s,t),m)`,`τ`]mp_tac) >>
  (discharge_hyps >- (
    simp[] >>
    fs[FEVERY_DEF,DOMSUB_FAPPLY_THM] >>
    conj_tac >- (
      fs[IN_DISJOINT,IN_FRANGE,DOMSUB_FAPPLY_THM] >>
      metis_tac[] ) >>
    reverse conj_tac >- (
      fs[closes_def] >>
      metis_tac[] ) >>
    rw[] >>
    ((qsuff_tac`semantics σ τ (subst ' x) = semantics sx τ (subst ' x)` >- metis_tac[])
     ORELSE
     (qsuff_tac`semantics σ τ (subst ' x) = semantics sy τ (subst ' x)` >- metis_tac[])) >>
    match_mp_tac semantics_frees >>
    simp[] >>
    fs[IN_FRANGE,FLOOKUP_DEF,Abbr`sx`,FAPPLY_FUPDATE_THM,Abbr`sy`] >>
    metis_tac[] )) >>
  rw[] >>
  rw[Abbr`sy`,GSYM FUNION_FUPDATE_1,Abbr`sx`] >>
  rpt (AP_TERM_TAC ORELSE AP_THM_TAC) >>
  simp[GSYM fmap_EQ_THM] >>
  simp[FUNION_DEF,FAPPLY_FUPDATE_THM] >>
  (conj_tac >- (
    simp[EXTENSION] >>
    metis_tac[] )) >>
  simp[DOMSUB_FAPPLY_THM] >>
  metis_tac[] )

val ALPHAVARS_FILTER_REFL = store_thm("ALPHAVARS_FILTER_REFL",
  ``∀env t. EVERY (UNCURRY $=) (FILTER (λ(x,y). t = x ∨ t = y) env) ⇒ ALPHAVARS env (t,t)``,
  Induct >> simp[ALPHAVARS_def] >>
  Cases >> simp[] >> rw[] >> fs[])

val _ = Hol_datatype` dbterm =
    dbVar of string => type
  | dbBound of num
  | dbConst of string => type => const_tag
  | dbComb of dbterm => dbterm
  | dbAbs of type => dbterm`

val bind_def = Define`
  (bind v n (dbVar x ty) = if v = (x,ty) then dbBound n else dbVar x ty) ∧
  bind v n (dbBound m) = dbBound m ∧
  bind v n (dbConst x ty g) = dbConst x ty g ∧
  bind v n (dbComb t1 t2) = dbComb (bind v n t1) (bind v n t2) ∧
  bind v n (dbAbs ty tm) = dbAbs ty (bind v (n+1) tm)`
val _ = export_rewrites["bind_def"]

val db_def = Define`
  db (Var x ty) = dbVar x ty ∧
  db (Const x ty g) = dbConst x ty g ∧
  db (Comb t1 t2) = dbComb (db t1) (db t2) ∧
  db (Abs x ty tm) = dbAbs ty (bind (x,ty) 0 (db tm))`
val _ = export_rewrites["db_def"]

val dbVSUBST_def = Define`
  dbVSUBST ilist (dbVar x ty) = REV_ASSOCD (dbVar x ty) ilist (dbVar x ty) ∧
  dbVSUBST ilist (dbBound m) = dbBound m ∧
  dbVSUBST ilist (dbConst x ty g) = dbConst x ty g ∧
  dbVSUBST ilist (dbComb t1 t2) = dbComb (dbVSUBST ilist t1) (dbVSUBST ilist t2) ∧
  dbVSUBST ilist (dbAbs ty t) = dbAbs ty (dbVSUBST ilist t)`
    (*
    let ilist' = FILTER (λ(s',s). s ≠ dbVar x ty) ilist in
    let t' = dbVSUBST ilist' t in
    dbAbs ty t'
    *)
    (*
    if EXISTS (λ(s',s). dbVFREE_IN (dbVar x ty) s' ∧ dbVFREE_IN s t) ilist'
    then
      let z = VARIANT ???? in
      let ilist'' = (dbVar z ty,dbVar x ty)::ilist'
      in dbAbs ty (dbVSUBST ilist'' t)
    else dbAbs ty t'
    *)
val _ = export_rewrites["dbVSUBST_def"]

val dbVFREE_IN_def = Define`
  (dbVFREE_IN v (dbVar x ty) ⇔ dbVar x ty = v) ∧
  (dbVFREE_IN v (dbBound n) ⇔ F) ∧
  (dbVFREE_IN v (dbConst x ty g) ⇔ dbConst x ty g = v) ∧
  (dbVFREE_IN v (dbComb t1 t2) ⇔ (dbVFREE_IN v t1 ∨ dbVFREE_IN v t2)) ∧
  (dbVFREE_IN v (dbAbs ty t) ⇔ dbVFREE_IN v t)`
val _ = export_rewrites["dbVFREE_IN_def"]

val bind_not_free = store_thm("bind_not_free",
  ``∀t n v. ¬dbVFREE_IN (UNCURRY dbVar v) t ⇒ bind v n t = t``,
  Induct >> simp[] >> rw[])

val bind_dbVSUBST = store_thm("bind_dbVSUBST",
  ``∀tm v n ls.
    (UNCURRY dbVar v) ∉ set (MAP SND ls) ∧
    (∀k. dbVFREE_IN k tm ∧ MEM k (MAP SND ls) ⇒
        ¬dbVFREE_IN (UNCURRY dbVar v) (REV_ASSOCD k ls k))
    ⇒
    bind v n (dbVSUBST ls tm) = dbVSUBST ls (bind v n tm)``,
  Induct >> simp[] >>
  CONV_TAC (RESORT_FORALL_CONV List.rev) >>
  rw[] >- (
    `REV_ASSOCD (dbVar s t) ls (dbVar s t) = dbVar s t` by (
      fs[MEM_MAP,EXISTS_PROD] >>
      metis_tac[REV_ASSOCD_MEM,MEM_MAP] ) >>
    rw[] ) >>
  Induct_on`ls` >- simp[REV_ASSOCD] >>
  Cases >> simp[REV_ASSOCD] >> strip_tac >>
  rw[] >> metis_tac[bind_not_free])

val bind_dbVSUBST_cons = store_thm("bind_dbVSUBST_cons",
  ``∀tm z x n ls.
    ¬dbVFREE_IN (UNCURRY dbVar z) (dbVSUBST ls (bind x n tm))
    ⇒
    bind z n (dbVSUBST ((UNCURRY dbVar z,UNCURRY dbVar x)::ls) tm) = dbVSUBST ls (bind x n tm)``,
  Induct >> simp[] >>
  CONV_TAC (RESORT_FORALL_CONV List.rev) >>
  rw[REV_ASSOCD] >>fs[] >- (
    Cases_on`z`>>fs[] ) >>
  Cases_on`z`>>fs[] >- (
    Cases_on`x`>>fs[] ) >>
  match_mp_tac bind_not_free >> fs[] )

val dbVSUBST_frees = store_thm("dbVSUBST_frees",
  ``∀tm ls ls'.
    (∀k. dbVFREE_IN k tm ⇒ REV_ASSOCD k ls k = REV_ASSOCD k ls' k)
     ⇒
      dbVSUBST ls tm = dbVSUBST ls' tm``,
  Induct >> simp[])

val dbVFREE_IN_bind = store_thm("dbVFREE_IN_bind",
  ``∀tm x v n b. dbVFREE_IN x (bind v n tm) ⇔ (x ≠ UNCURRY dbVar v) ∧ dbVFREE_IN x tm``,
  Induct >> simp[] >> rw[] >- metis_tac[]
  >- (
    Cases_on`x`>>fs[]>>
    Cases_on`v`>>fs[]>>
    metis_tac[])
  >- (
    Cases_on`x`>>fs[]>>
    Cases_on`v`>>fs[]) >>
  Cases_on`v`>>fs[]>>
  Cases_on`x=dbVar q r`>>fs[])

val dbVFREE_IN_VFREE_IN = store_thm("dbVFREE_IN_VFREE_IN",
  ``∀tm x. dbVFREE_IN (db x) (db tm) ⇔ VFREE_IN x tm``,
  Induct >> simp[VFREE_IN_def] >- (
    gen_tac >> Cases >> simp[VFREE_IN_def] )
  >- (
    gen_tac >> Cases >> simp[VFREE_IN_def] ) >>
  simp[dbVFREE_IN_bind] >>
  gen_tac >> Cases >> simp[] >>
  metis_tac[] )

val MAP_db_FILTER_neq = store_thm("MAP_db_FILTER_neq",
  ``∀ls z ty. MAP (λ(x,y). (db x, db y)) (FILTER (λ(x,y). y ≠ Var z ty) ls) = FILTER (λ(x,y). y ≠ dbVar z ty) (MAP (λ(x,y). (db x, db y)) ls)``,
  Induct >> simp[] >>
  Cases >> simp[] >>
  rw[] >-( Cases_on`r`>>fs[] ) >> fs[])

val REV_ASSOCD_MAP_db = store_thm("REV_ASSOCD_MAP_db",
  ``∀ls k ky.
    (∀k v. MEM (v,k) ls ⇒ ∃x ty. k = Var x ty)
    ⇒
    REV_ASSOCD (dbVar k ky) (MAP (λ(x,y). (db x, db y)) ls) (dbVar k ky) = db (REV_ASSOCD (Var k ky) ls (Var k ky))``,
  Induct >> simp[REV_ASSOCD] >>
  Cases >> simp[REV_ASSOCD] >>
  rw[] >> fs[] >- (
    Cases_on`r`>>fs[]>>rw[] ) >>
  `∃x ty. r = Var x ty` by metis_tac[] >> fs[] >>
  metis_tac[])

val dbVFREE_IN_dbVSUBST = store_thm("dbVFREE_IN_dbVSUBST",
  ``∀tm u uty ilist.
      dbVFREE_IN (dbVar u uty) (dbVSUBST ilist tm) ⇔
      ∃y ty. dbVFREE_IN (dbVar y ty) tm ∧
             dbVFREE_IN (dbVar u uty)
               (REV_ASSOCD (dbVar y ty) ilist (dbVar y ty))``,
  Induct >> simp[] >> rw[] >> metis_tac[])

val VSUBST_dbVSUBST = store_thm("VSUBST_dbVSUBST",
  ``∀tm ilist.
    (∀k v. MEM (v,k) ilist ⇒ ∃x ty. k = Var x ty)
    ⇒
    db (VSUBST ilist tm) = dbVSUBST (MAP (λ(x,y). (db x, db y)) ilist) (db tm)``,
  Induct >- (
    simp[VSUBST_def] >>
    gen_tac >> Induct >>
    simp[REV_ASSOCD] >>
    Cases >> simp[REV_ASSOCD] >>
    strip_tac >>
    qpat_assum`p ⇒ qq`mp_tac >>
    discharge_hyps >- metis_tac[] >> strip_tac >>
    rw[] >> fs[] >>
    Cases_on`r`>>fs[] )
  >- simp[VSUBST_def]
  >- (
    simp[VSUBST_def] >>
    metis_tac[] ) >>
  rw[VSUBST_def] >>
  reverse(rw[]) >- (
    first_x_assum(qspec_then`ilist'`mp_tac) >>
    discharge_hyps >- (
      simp[Abbr`ilist'`,MEM_FILTER] >>
      metis_tac[] ) >>
    rw[Abbr`t'`] >>
    qmatch_abbrev_tac`bind v n (dbVSUBST ls tt) = X` >>
    qspecl_then[`tt`,`v`,`n`,`ls`]mp_tac bind_dbVSUBST >>
    discharge_hyps >- (
      fs[MEM_MAP,EVERY_MEM,EXISTS_PROD,FORALL_PROD,Abbr`ls`,GSYM LEFT_FORALL_IMP_THM,Abbr`ilist'`,MEM_FILTER] >>
      qunabbrev_tac`v` >>
      conj_tac >- (
        gen_tac >> Cases >> simp[] >>
        metis_tac[] ) >>
      qx_gen_tac`k` >> strip_tac >> simp[] >>
      simp[MAP_db_FILTER_neq] >>
      simp[REV_ASSOCD_FILTER] >>
      qmatch_assum_rename_tac`k = db u`[] >>
      `∃x ty. u = Var x ty` by metis_tac[] >>
      qspecl_then[`ilist`,`x`,`ty`]mp_tac REV_ASSOCD_MAP_db >>
      discharge_hyps >- metis_tac[] >>
      simp[] >> strip_tac >>
      BasicProvers.CASE_TAC >- (
        qmatch_abbrev_tac`¬dbVFREE_IN (dbVar s t) (db tz)` >>
        qspecl_then[`tz`,`Var s t`]mp_tac dbVFREE_IN_VFREE_IN >>
        simp[] >> strip_tac >>
        rpt BasicProvers.VAR_EQ_TAC >>
        spose_not_then strip_assume_tac >>
        metis_tac[REV_ASSOCD_MEM,VFREE_IN_def,dbVFREE_IN_VFREE_IN] ) >>
      fs[] ) >>
    rw[Abbr`ls`,Abbr`ilist'`] >>
    match_mp_tac dbVSUBST_frees >>
    simp[MAP_db_FILTER_neq,REV_ASSOCD_FILTER] >>
    rw[Abbr`v`] >>
    fs[dbVFREE_IN_bind]) >>
  first_x_assum(qspec_then`ilist''`mp_tac) >>
  discharge_hyps >- (
    simp[Abbr`ilist''`,Abbr`ilist'`,MEM_FILTER] >>
    metis_tac[] ) >>
  qunabbrev_tac`ilist''` >> rw[] >>
  qmatch_abbrev_tac`bind v n (dbVSUBST ((zz,x)::ls) tt) = X` >>
  qspecl_then[`tt`,`(z,t)`,`(s,t)`,`n`,`ls`]mp_tac bind_dbVSUBST_cons >>
  simp[Abbr`v`] >>
  discharge_hyps >- (
    qunabbrev_tac`zz` >>
    simp[dbVFREE_IN_dbVSUBST] >>
    simp[dbVFREE_IN_bind] >>
    rpt gen_tac >>
    qspecl_then[`ilist'`,`y`,`ty`]mp_tac REV_ASSOCD_MAP_db >>
    discharge_hyps >- (
      simp[Abbr`ilist'`,MEM_FILTER] >>
      metis_tac[] ) >>
    rw[] >>
    qmatch_assum_abbrev_tac`tv = db tu` >>
    qspecl_then[`tu`,`Var z t`]mp_tac dbVFREE_IN_VFREE_IN >>
    rw[] >>
    qspecl_then[`tm`,`Var y ty`]mp_tac dbVFREE_IN_VFREE_IN >>
    rw[Abbr`tt`] >>
    spose_not_then strip_assume_tac >>
    qsuff_tac`VFREE_IN (Var z t) t'`>-
      metis_tac[VARIANT_THM] >>
    simp[Abbr`tu`,Abbr`t'`,VFREE_IN_VSUBST] >>
    metis_tac[] ) >>
  rw[] >>
  simp[Abbr`ls`] >>
  match_mp_tac dbVSUBST_frees >>
  simp[Abbr`ilist'`,MAP_db_FILTER_neq,REV_ASSOCD_FILTER] >>
  rw[Abbr`x`] >>
  fs[dbVFREE_IN_bind])

val dbterm_def = Define`
  (dbterm env (Var s ty) =
     case find_index (s,ty) env 0 of SOME n => dbBound n | NONE => dbVar s ty) ∧
  (dbterm env (Const s ty g) = dbConst s ty g) ∧
  (dbterm env (Comb t1 t2) = dbComb (dbterm env t1) (dbterm env t2)) ∧
  (dbterm env (Abs x ty t) = dbAbs ty (dbterm ((x,ty)::env) t))`
val _ = export_rewrites["dbterm_def"]

val bind_list_aux_def = Define`
  bind_list_aux n [] tm = tm ∧
  bind_list_aux n (v::vs) tm = bind_list_aux (n+1) vs (bind v n tm)`
val _ = export_rewrites["bind_list_aux_def"]

val bind_list_aux_clauses = store_thm("bind_list_aux_clauses",
  ``(∀env m. bind_list_aux m env (dbBound n) = dbBound n) ∧
    (∀env m. bind_list_aux m env (dbConst x ty g) = dbConst x ty g) ∧
    (∀env m t1 t2. bind_list_aux m env (dbComb t1 t2) = dbComb (bind_list_aux m env t1) (bind_list_aux m env t2)) ∧
    (∀env m ty tm. bind_list_aux m env (dbAbs ty tm) = dbAbs ty (bind_list_aux (m+1) env tm))``,
  rpt conj_tac >> Induct >> simp[])

val dbterm_bind = store_thm("dbterm_bind",
  ``∀tm env. dbterm env tm = bind_list_aux 0 env (db tm)``,
  Induct >> simp[bind_list_aux_clauses] >>
  gen_tac >>
  Q.SPEC_TAC(`0`,`n`) >>
  Induct_on`env` >> simp[find_index_def] >>
  Cases >> simp[] >>
  rw[] >> rw[bind_list_aux_clauses])

val dbterm_db = store_thm("dbterm_db",
  ``∀tm. dbterm [] tm = db tm``,
  rw[dbterm_bind])

val dbterm_RACONV = store_thm("dbterm_RACONV",
  ``∀t1 env1 t2 env2. dbterm env1 t1 = dbterm env2 t2 ∧ LENGTH env1 = LENGTH env2 ⇒
      RACONV (ZIP(MAP (UNCURRY Var) env1,MAP (UNCURRY Var) env2)) (t1,t2)``,
  Induct >- (
    ntac 2 gen_tac >> simp[] >>
    Cases >> simp[RACONV] >>
    TRY (BasicProvers.CASE_TAC >> simp[] >> NO_TAC) >>
    Induct_on`env1` >- (
      simp[find_index_def,LENGTH_NIL_SYM,ALPHAVARS_def] ) >>
    gen_tac >> Cases >> simp[] >>
    simp[find_index_def,ALPHAVARS_def] >>
    Cases_on`h`>>Cases_on`h'`>>simp[] >>
    simp[Once find_index_shift_0] >>
    simp[Once find_index_shift_0,SimpRHS] >>
    rpt BasicProvers.CASE_TAC >> fs[] >> rw[] >> fs[] )
  >- (
    simp[] >> ntac 2 gen_tac >>
    Cases >> simp[RACONV] >>
    gen_tac >> BasicProvers.CASE_TAC >> simp[] )
  >- (
    simp[] >>
    gen_tac >> Cases >> simp[RACONV] >>
    gen_tac >> BasicProvers.CASE_TAC >> simp[] ) >>
  simp[] >>
  ntac 2 gen_tac >>
  Cases >> simp[RACONV] >- (
    gen_tac >> BasicProvers.CASE_TAC >> simp[] ) >>
  rw[] >> res_tac >> fs[])

val RACONV_dbterm = store_thm("RACONV_dbterm",
  ``∀env tp. RACONV env tp ⇒
    (∀vp. MEM vp env ⇒ (∃x ty. (FST vp = Var x ty)) ∧ (∃x ty. (SND vp = Var x ty)))
     ⇒ dbterm (MAP (dest_var o FST) env) (FST tp) = dbterm (MAP (dest_var o SND) env) (SND tp)``,
  ho_match_mp_tac RACONV_ind >> rw[] >> rw[] >>
  TRY (
    first_x_assum match_mp_tac >>
    rw[] >> rw[] ) >>
  Induct_on`env` >> simp[ALPHAVARS_def] >>
  rw[] >> rw[] >- rw[find_index_def] >> fs[] >>
  simp[find_index_def] >>
  `∃x ty. FST h = Var x ty` by metis_tac[] >>
  `∃y tz. SND h = Var y tz` by metis_tac[] >>
  simp[] >>
  simp[Once find_index_shift_0] >>
  simp[Once find_index_shift_0,SimpRHS] >>
  rpt BasicProvers.CASE_TAC >> fs[] >> rw[] >> fs[])

val dbterm_ACONV = store_thm("dbterm_ACONV",
  ``∀t1 t2. ACONV t1 t2 ⇔ dbterm [] t1 = dbterm [] t2``,
  rw[ACONV_def,EQ_IMP_THM] >- (
    qspecl_then[`[]`,`t1,t2`]mp_tac RACONV_dbterm >> simp[] ) >>
  qspecl_then[`t1`,`[]`,`t2`,`[]`]mp_tac dbterm_RACONV >>
  simp[])

val ACONV_db = store_thm("ACONV_db",
  ``∀t1 t2. ACONV t1 t2 ⇔ db t1 = db t2``,
  metis_tac[dbterm_ACONV,dbterm_db])

val ACONV_VSUBST = store_thm("ACONV_VSUBST",
  ``∀t1 t2 ilist.
    (∀k v. MEM (v,k) ilist ⇒ ∃x ty. k = Var x ty) ∧
    ACONV t1 t2 ⇒
    ACONV (VSUBST ilist t1) (VSUBST ilist t2)``,
  rw[ACONV_db] >> metis_tac[VSUBST_dbVSUBST])

val has_meaning_VSUBST = store_thm("has_meaning_VSUBST",
  ``∀tm ilist.
    has_meaning tm ∧
    (∀v k. MEM (v,k) ilist ⇒ has_meaning v ∧ ∃x ty. k = Var x ty ∧ v has_type ty)
    ⇒ has_meaning (VSUBST ilist tm)``,
  Induct >- (
    simp[VSUBST_def] >>
    gen_tac >> Induct >>
    simp[REV_ASSOCD] >>
    Cases >> simp[REV_ASSOCD] >>
    rw[] >> fs[] >> metis_tac[] )
  >- (
    simp[VSUBST_def] )
  >- (
    simp[VSUBST_def] >>
    rw[] >>
    TRY (
      match_mp_tac VSUBST_WELLTYPED >>
      metis_tac[] ) >>
    TRY (
      qexists_tac`rty` >>
      metis_tac[VSUBST_HAS_TYPE,type_11,WELLTYPED_LEMMA,WELLTYPED] ) >>
    first_x_assum match_mp_tac >>
    metis_tac[]) >>
  rw[] >> fs[] >>
  rw[VSUBST_def] >>
  rw[] >>
  rw[Abbr`t'`] >>
  first_x_assum match_mp_tac >>
  unabbrev_all_tac >>
  simp[MEM_FILTER] >>
  metis_tac[has_meaning_Var,has_type_cases])

val simple_subst_frees = store_thm("simple_subst_frees",
  ``∀tm s1 s2.
    (∀x ty. VFREE_IN (Var x ty) tm ⇒ FLOOKUP s1 (x,ty) = FLOOKUP s2 (x,ty))
    ⇒
    simple_subst s1 tm = simple_subst s2 tm``,
  Induct >> simp[FLOOKUPD_def] >> rw[] >>
  first_x_assum match_mp_tac >>
  simp[DOMSUB_FLOOKUP_THM] >>
  rw[] >> fs[])

val tvars_VSUBST_lookup = store_thm("tvars_VSUBST_lookup",
  ``∀tm ilist x ty. VFREE_IN (Var x ty) tm ⇒ set (tvars (REV_ASSOCD (Var x ty) ilist (Var x ty))) ⊆ set (tvars (VSUBST ilist tm))``,
  Induct >> simp[VSUBST_def,tvars_def] >- (
    fs[SUBSET_DEF] >>
    metis_tac[] ) >>
  rw[tvars_def] >>
  qmatch_abbrev_tac`X ⊆ Y ∪ set (tvars (VSUBST ls tm))` >>
  first_x_assum(qspecl_then[`ls`,`x`,`ty`]mp_tac) >>
  unabbrev_all_tac >>
  simp[SUBSET_DEF,REV_ASSOCD,REV_ASSOCD_FILTER])

val closes_VSUBST_lookup = store_thm("closes_VSUBST_lookup",
  ``closes s t (VSUBST ilist tm) ∧
    VFREE_IN (Var x ty) tm
    ⇒
    closes s t (REV_ASSOCD (Var x ty) ilist (Var x ty))``,
  rw[closes_def] >- (
    metis_tac[tvars_VSUBST_lookup,SUBSET_TRANS] ) >>
  first_x_assum match_mp_tac >>
  rw[VFREE_IN_VSUBST] >>
  metis_tac[])

val tvars_subset_VSUBST = store_thm("tvars_subset_VSUBST",
  ``∀tm ilist.
    (∀k v. MEM (v,k) ilist ⇒ ∃x ty. k = Var x ty ∧ v has_type ty)
    ⇒
    set (tvars tm) ⊆ set (tvars (VSUBST ilist tm))``,
  Induct >> rw[VSUBST_def,tvars_def] >- (
    simp[REV_ASSOCD_ALOOKUP] >>
    BasicProvers.CASE_TAC >> simp[tvars_def] >>
    imp_res_tac ALOOKUP_MEM >>
    fs[MEM_MAP,EXISTS_PROD] >>
    res_tac >> fs[] >> rw[] >>
    metis_tac[tyvars_typeof_subset_tvars] ) >>
  TRY ( fs[SUBSET_DEF] >> NO_TAC) >>
  rw[tvars_def,Abbr`t'`] >>
  qmatch_abbrev_tac`X ⊆ Y ∪ Z` >>
  (qsuff_tac`X ⊆ Z` >- (simp[SUBSET_DEF])) >>
  unabbrev_all_tac >>
  first_x_assum match_mp_tac >>
  simp[MEM_FILTER] >>
  metis_tac[has_type_cases])

val INST_correct = store_thm("INST_correct",
  ``∀ilist h c.
      (∀s s'. MEM (s',s) ilist ⇒ has_meaning s' ∧ ∃x ty. (s = Var x ty) ∧ s' has_type ty) ∧ h |= c
      ⇒
      (MAP (VSUBST ilist) h) |= VSUBST ilist c``,
  rw[] >>
  fs[sequent_def] >>
  conj_asm1_tac >- (
    conj_tac >- (
      match_mp_tac VSUBST_HAS_TYPE >>
      metis_tac[] ) >>
    fs[EVERY_MEM,MEM_MAP] >>
    metis_tac[VSUBST_HAS_TYPE] ) >>
  conj_tac >- (
    conj_tac >- (
      match_mp_tac has_meaning_VSUBST >>
      metis_tac[] ) >>
    fs[EVERY_MEM,MEM_MAP] >>
    metis_tac[has_meaning_VSUBST] ) >>
  rw[] >>
  qabbrev_tac`tm = fresh_term {x | ∃ty u. VFREE_IN (Var x ty) u ∧ MEM u (MAP FST ilist)} c` >>
  `ACONV c tm` by simp[fresh_term_def,Abbr`tm`] >>
  qspecl_then[`c`,`tm`,`ilist`]mp_tac ACONV_VSUBST >>
  discharge_hyps >- metis_tac[] >> strip_tac >>
  qsuff_tac`semantics σ τ (VSUBST ilist tm) true` >- (
    metis_tac[semantics_aconv,welltyped_def] ) >>
  `VSUBST ilist tm = simple_subst (ilist_to_fmap ilist) tm` by (
    match_mp_tac VSUBST_simple_subst >>
    simp[fresh_term_def,Abbr`tm`] >>
    metis_tac[] ) >>
  simp[] >>
  qabbrev_tac`subst = DRESTRICT (ilist_to_fmap ilist) {(x,ty) | VFREE_IN (Var x ty) c ∨ ∃t. MEM t h ∧ VFREE_IN (Var x ty) t}` >>
  `simple_subst (ilist_to_fmap ilist) tm = simple_subst subst tm` by (
    match_mp_tac simple_subst_frees >>
    simp[Abbr`subst`,FLOOKUP_DRESTRICT] >>
    metis_tac[VFREE_IN_ACONV] ) >>
  `∀k v. FLOOKUP subst k = SOME v ⇒ ∃m. semantics σ τ v m` by (
    simp[Abbr`subst`,FLOOKUP_DRESTRICT] >>
    Cases >> simp[FLOOKUP_ilist_to_fmap] >>
    simp[REV_ASSOCD_ALOOKUP] >>
    BasicProvers.CASE_TAC >- (
      fs[ALOOKUP_FAILS,MEM_MAP,FORALL_PROD,EXISTS_PROD] ) >>
    `has_meaning x` by (
      imp_res_tac ALOOKUP_MEM >>
      fs[MEM_MAP,EXISTS_PROD] >>
      metis_tac[] ) >>
    pop_assum mp_tac >>
    simp[has_meaning_def] >>
    strip_tac >>
    strip_tac >>
    first_x_assum match_mp_tac >>
    simp[] >>
    `x = REV_ASSOCD (Var q r) ilist (Var q r)` by (
      simp[REV_ASSOCD_ALOOKUP] ) >>
    fs[EVERY_MAP] >> fs[EVERY_MEM] >>
    metis_tac[closes_VSUBST_lookup,semantics_closes] ) >>
  pop_assum mp_tac >>
  simp[GSYM RIGHT_EXISTS_IMP_THM,SKOLEM_THM] >>
  disch_then(qx_choose_then`ssf`strip_assume_tac) >>
  qabbrev_tac`ss = FUN_FMAP (λk. ssf k (subst ' k)) (FDOM subst)` >>
  qspecl_then[`tm`,`subst`,`ss`,`σ`,`τ`]mp_tac semantics_simple_subst >>
  `FDOM subst = FDOM ss` by (
    unabbrev_all_tac >> simp[] ) >>
  `closes (FDOM (ss ⊌ σ)) (FDOM τ) tm` by (
    fs[closes_def] >>
    conj_tac >- (
      metis_tac[tvars_subset_VSUBST,ACONV_tvars,SUBSET_DEF] ) >>
    fs[Abbr`ss`] >>
    rw[] >>
    `VFREE_IN (Var x ty) c` by metis_tac[ACONV_VFREE_IN,ACONV_SYM] >>
    fs[VFREE_IN_VSUBST,GSYM LEFT_FORALL_IMP_THM] >>
    Cases_on`(x,ty) ∈ FDOM ss`>>simp[] >>
    first_x_assum match_mp_tac >>
    map_every qexists_tac[`x`,`ty`] >>
    simp[REV_ASSOCD_ALOOKUP] >>
    BasicProvers.CASE_TAC >> simp[] >>
    imp_res_tac ALOOKUP_MEM >>
    qpat_assum`X = FDOM ss`(assume_tac o SYM) >>
    fs[Abbr`subst`,FDOM_DRESTRICT] >>
    `FLOOKUP (ilist_to_fmap ilist) (x,ty) = NONE` by fs[FLOOKUP_DEF] >>
    fs[FLOOKUP_ilist_to_fmap,MEM_MAP,EXISTS_PROD] ) >>
  `FEVERY (λ((x,ty),tm). tm has_type ty) subst` by (
    simp[FEVERY_ALL_FLOOKUP] >>
    simp[Abbr`subst`,FLOOKUP_DRESTRICT] >>
    simp[FORALL_PROD,FLOOKUP_ilist_to_fmap] >>
    rw[] >>
    metis_tac[REV_ASSOCD_MEM,term_11,has_type_cases] ) >>
  `FEVERY (λ(v,m). semantics σ τ (subst ' v) m) ss` by (
    simp[FEVERY_ALL_FLOOKUP] >>
    simp[Abbr`ss`,FLOOKUP_FUN_FMAP] >>
    fs[FLOOKUP_DEF] ) >>
  discharge_hyps >- (
    conj_tac >- (
      qmatch_assum_abbrev_tac`Abbrev(tm = fresh_term s c)` >>
      `DISJOINT (set (bv_names tm)) s` by (
        simp[Abbr`tm`,Abbr`s`,fresh_term_def] ) >>
      fs[Abbr`s`,IN_DISJOINT,FRANGE_FLOOKUP] >>
      simp[Abbr`subst`,FLOOKUP_DRESTRICT] >>
      simp[FORALL_PROD,FLOOKUP_ilist_to_fmap] >>
      spose_not_then strip_assume_tac >>
      qsuff_tac`MEM u (MAP FST ilist)`>-metis_tac[] >>
      BasicProvers.VAR_EQ_TAC >>
      simp[REV_ASSOCD_ALOOKUP] >>
      BasicProvers.CASE_TAC >- (
        fs[ALOOKUP_FAILS,MEM_MAP,FORALL_PROD,EXISTS_PROD] ) >>
      imp_res_tac ALOOKUP_MEM >>
      fs[MEM_MAP,EXISTS_PROD] >>
      metis_tac[] ) >>
    simp[] >>
    metis_tac[ACONV_welltyped,welltyped_def] ) >>
  rw[] >>
  `term_valuation τ (ss ⊌ σ)` by (
    fs[term_valuation_def,FEVERY_ALL_FLOOKUP,FLOOKUP_FUNION] >>
    rpt gen_tac >>
    BasicProvers.CASE_TAC >> simp[] >>
    rw[] >>
    fs[Abbr`ss`,FLOOKUP_FUN_FMAP] >>
    `FLOOKUP subst k = SOME (subst ' k)` by simp[FLOOKUP_DEF] >>
    `semantics σ τ (subst ' k) v` by metis_tac[] >>
    qspecl_then[`σ`,`τ`,`subst ' k`,`v`]mp_tac(CONJUNCT2 semantics_typeset) >>
    simp[term_valuation_def,FEVERY_ALL_FLOOKUP] >>
    qsuff_tac`typeof (subst ' k) = SND k` >- metis_tac[] >>
    qsuff_tac`MEM (subst ' k,UNCURRY Var k) ilist` >- (
      strip_tac >> res_tac >> Cases_on`k` >> fs[] >>
      metis_tac[has_meaning_welltyped,WELLTYPED_LEMMA] ) >>
    qabbrev_tac`w = subst ' k` >>
    Cases_on`k` >>
    fs[Abbr`subst`,FLOOKUP_DRESTRICT,FLOOKUP_ilist_to_fmap] >>
    rw[] >>
    simp[REV_ASSOCD_ALOOKUP] >>
    BasicProvers.CASE_TAC >>
    fs[ALOOKUP_FAILS,MEM_MAP,EXISTS_PROD] >>
    imp_res_tac ALOOKUP_MEM >>
    fs[MEM_MAP,EXISTS_PROD] ) >>
  qsuff_tac`semantics (ss ⊌ σ) τ c true` >- metis_tac[semantics_aconv,welltyped_def] >>
  first_x_assum match_mp_tac >>
  simp[] >> fs[] >>
  reverse conj_tac >- metis_tac[closes_aconv,ACONV_SYM] >>
  fs[EVERY_MAP] >>
  fs[EVERY_MEM] >>
  rw[] >>
  `semantics σ τ (VSUBST ilist t) true` by metis_tac[] >>
  qmatch_assum_abbrev_tac`Abbrev(tm = fresh_term s c)` >>
  qabbrev_tac`th = fresh_term s t` >>
  `ACONV t th` by simp[Abbr`th`,Abbr`s`,fresh_term_def] >>
  qsuff_tac`semantics (ss ⊌ σ) τ th true` >-  metis_tac[semantics_aconv,welltyped_def] >>
  `semantics (ss ⊌ σ) τ th = semantics σ τ (simple_subst subst th)` by (
    match_mp_tac EQ_SYM >>
    match_mp_tac semantics_simple_subst >>
    conj_tac >- (
      `DISJOINT (set (bv_names th)) s` by (
        simp[Abbr`th`,Abbr`s`,fresh_term_def] ) >>
      fs[Abbr`s`,IN_DISJOINT,FRANGE_FLOOKUP] >>
      simp[Abbr`subst`,FLOOKUP_DRESTRICT] >>
      simp[FORALL_PROD,FLOOKUP_ilist_to_fmap] >>
      spose_not_then strip_assume_tac >>
      qsuff_tac`MEM u (MAP FST ilist)`>-metis_tac[] >>
      BasicProvers.VAR_EQ_TAC >>
      simp[REV_ASSOCD_ALOOKUP] >>
      BasicProvers.CASE_TAC >- (
        fs[ALOOKUP_FAILS,MEM_MAP,FORALL_PROD,EXISTS_PROD] ) >>
      imp_res_tac ALOOKUP_MEM >>
      fs[MEM_MAP,EXISTS_PROD] >>
      metis_tac[] ) >>
    simp[] >>
    reverse conj_tac >- (
      metis_tac[ACONV_welltyped,welltyped_def] ) >>
    `closes (FDOM σ) (FDOM τ) (VSUBST ilist t)` by metis_tac[semantics_closes] >>
    fs[closes_def] >>
    conj_tac >- (
      metis_tac[tvars_subset_VSUBST,ACONV_tvars,SUBSET_DEF] ) >>
    fs[Abbr`ss`] >>
    rw[] >>
    `VFREE_IN (Var x ty) t` by metis_tac[ACONV_VFREE_IN,ACONV_SYM] >>
    fs[VFREE_IN_VSUBST,GSYM LEFT_FORALL_IMP_THM] >>
    Cases_on`(x,ty) ∈ FDOM ss`>>simp[] >>
    first_x_assum match_mp_tac >>
    map_every qexists_tac[`x`,`ty`] >>
    simp[REV_ASSOCD_ALOOKUP] >>
    BasicProvers.CASE_TAC >> simp[] >>
    imp_res_tac ALOOKUP_MEM >>
    qpat_assum`X = FDOM ss`(assume_tac o SYM) >>
    fs[Abbr`subst`,FDOM_DRESTRICT] >>
    `FLOOKUP (ilist_to_fmap ilist) (x,ty) = NONE` by fs[FLOOKUP_DEF] >>
    fs[FLOOKUP_ilist_to_fmap,MEM_MAP,EXISTS_PROD] >>
    metis_tac[]) >>
  simp[] >>
  `simple_subst subst th = simple_subst (ilist_to_fmap ilist) th` by (
    match_mp_tac simple_subst_frees >>
    simp[Abbr`subst`,FLOOKUP_DRESTRICT] >>
    rw[] >>
    metis_tac[VFREE_IN_ACONV] ) >>
  `simple_subst (ilist_to_fmap ilist) th = VSUBST ilist th` by (
    match_mp_tac EQ_SYM >>
    match_mp_tac VSUBST_simple_subst >>
    simp[Abbr`th`,Abbr`s`,fresh_term_def] >>
    metis_tac[] ) >>
  metis_tac[semantics_aconv,ACONV_VSUBST,welltyped_def])

val tyinst_tyinst = store_thm("tyinst_tyinst",
  ``∀ty i1 i2. tyinst i1 (tyinst i2 ty) = tyinst (tyinst i1 o_f i2 ⊌ i1) ty``,
  ho_match_mp_tac type_ind >>
  simp[] >>
  conj_tac >- (
    simp[FLOOKUPD_def,FLOOKUP_o_f,FLOOKUP_FUNION] >> rw[] >>
    BasicProvers.CASE_TAC >>
    simp[FLOOKUPD_def] ) >>
  simp[MAP_MAP_o,MAP_EQ_f,EVERY_MEM])

val simple_inst_compose = store_thm("simple_inst_compose",
  ``∀tm i1 i2. simple_inst i1 (simple_inst i2 tm) = simple_inst (tyinst i1 o_f i2 ⊌ i1) tm``,
  Induct >> simp[tyinst_tyinst])

val ALOOKUP_ZIP_MAP_SND = store_thm("ALOOKUP_ZIP_MAP_SND",
  ``∀l1 l2 k f. LENGTH l1 = LENGTH l2 ⇒
      ALOOKUP (ZIP(l1,MAP f l2)) = OPTION_MAP f o (ALOOKUP (ZIP(l1,l2)))``,
  Induct >> simp[LENGTH_NIL,LENGTH_NIL_SYM,FUN_EQ_THM] >>
  gen_tac >> Cases >> simp[] >> rw[] >> rw[])

val tyinst_FEMPTY = store_thm("tyinst_FEMPTY",
 ``∀ty. tyinst FEMPTY ty = ty``,
 ho_match_mp_tac type_ind >> simp[EVERY_MEM,MAP_EQ_ID])
val _ = export_rewrites["tyinst_FEMPTY"]

val bv_names_simple_inst = store_thm("bv_names_simple_inst",
  ``∀tm tyin. bv_names (simple_inst tyin tm) = bv_names tm``,
  Induct >> simp[])
val _ = export_rewrites["bv_names_simple_inst"]

val semantics_simple_inst = store_thm("semantics_simple_inst",
  ``(∀τi ty m. typeset τi ty m ⇒
       ∀τ tyin.
         (∀a. MEM a (tyvars ty) ⇒ typeset τ (tyinst tyin (Tyvar a)) (τi ' a))
         ⇒
         typeset τ (tyinst tyin ty) m) ∧
    (∀σi τi tm m. semantics σi τi tm m ⇒
        ∀σ τ tyin.
          (∀a. MEM a (tvars tm) ⇒ typeset τ (tyinst tyin (Tyvar a)) (τi ' a)) ∧
          (∀x ty. VFREE_IN (Var x ty) tm ⇒ FLOOKUP σi (x,ty) = FLOOKUP σ (x,tyinst tyin ty)) ∧
          ALL_DISTINCT (bv_names tm) ∧
          DISJOINT (set (bv_names tm)) {x | ∃ty. VFREE_IN (Var x ty) tm}
          ⇒
          semantics σ τ (simple_inst tyin tm) m)``,
  ho_match_mp_tac (theorem"semantics_strongind") >>
  conj_tac >- simp[tyvars_def,FLOOKUP_DEF] >>
  conj_tac >- simp[tyvars_def] >>
  conj_tac >- (
    simp[tyvars_def] >> rw[] >>
    simp[Once semantics_cases] >>
    metis_tac[] ) >>
  conj_tac >- (
    rw[tyvars_def] >>
    simp[Once semantics_cases] >>
    qmatch_assum_rename_tac`w <: mp`[] >>
    map_every qexists_tac[`m`,`mp`,`rty`,`w`] >>
    simp[] >>
    fs[MEM_FOLDR_LIST_UNION,tyinst_tyinst,simple_inst_compose] >>
    conj_tac >- (
      qmatch_abbrev_tac`typeset FEMPTY (tyinst (alist_to_fmap (ZIP (tvars tm,MAP (tyinst tyin) args))) rty) mp` >>
      pop_assum kall_tac >>
      first_x_assum(qspecl_then[`FEMPTY`,`tyin`]mp_tac) >>
      discharge_hyps >- (
        imp_res_tac typeset_closes_over >>
        fs[SUBSET_DEF] ) >>
      qmatch_abbrev_tac`typeset FEMPTY t1 mp ⇒ typeset FEMPTY t2 mp` >>
      qsuff_tac`t1 = t2`>-rw[] >>
      unabbrev_all_tac >>
      simp[GSYM tyinst_tyvars] >>
      simp[FLOOKUPD_def,FLOOKUP_o_f,FLOOKUP_FUNION] >>
      rw[] >>
      BasicProvers.CASE_TAC >- (
        fs[ALOOKUP_FAILS] >>
        imp_res_tac tyvars_typeof_subset_tvars >>
        fs[tyvars_def,SUBSET_DEF] >>
        fs[MEM_ZIP,MEM_EL] >>
        metis_tac[LENGTH_ZIP,EL_ZIP] ) >>
      BasicProvers.CASE_TAC >- (
        fs[ALOOKUP_FAILS] >>
        imp_res_tac ALOOKUP_MEM >>
        rfs[MEM_ZIP] >>
        metis_tac[] ) >>
      rfs[ALOOKUP_ZIP_MAP_SND] ) >>
    first_x_assum(qspecl_then[`FEMPTY`,`FEMPTY`,`tyin'`]mp_tac) >>
    discharge_hyps >- (
      simp[] >>
      imp_res_tac semantics_closes >> fs[] >>
      fs[closes_def] >>
      simp[fresh_term_def]) >>
    qmatch_abbrev_tac`semantics FEMPTY FEMPTY t1 m ⇒ semantics FEMPTY FEMPTY t2 m` >>
    qsuff_tac`t1 = t2`>-rw[]>>
    unabbrev_all_tac >>
    simp[simple_inst_tvars] >>
    simp[FLOOKUPD_def,FLOOKUP_o_f,FLOOKUP_FUNION] >>
    rw[] >>
    BasicProvers.CASE_TAC >- (
      fs[ALOOKUP_FAILS] >>
      imp_res_tac tyvars_typeof_subset_tvars >>
      fs[tyvars_def,SUBSET_DEF] >>
      fs[MEM_ZIP,MEM_EL] >>
      metis_tac[LENGTH_ZIP,EL_ZIP] ) >>
    BasicProvers.CASE_TAC >- (
      fs[ALOOKUP_FAILS] >>
      imp_res_tac ALOOKUP_MEM >>
      rfs[MEM_ZIP] >>
      metis_tac[] ) >>
    rfs[ALOOKUP_ZIP_MAP_SND] ) >>
  conj_tac >- (
    rw[] >>
    simp[Once semantics_cases] ) >>
  conj_tac >- (
    rw[tvars_def,tyvars_def] >>
    simp[Once semantics_cases] >>
    qexists_tac`m` >> simp[] ) >>
  conj_tac >- (
    rw[tvars_def,tyvars_def] >>
    simp[Once semantics_cases] >>
    qexists_tac`m` >> simp[] ) >>
  conj_tac >- (
    rw[tvars_def] >>
    simp[Once semantics_cases] >>
    rw[tyinst_tyinst] >>
    fs[simple_inst_compose] >>
    qho_match_abbrev_tac`∃x. tyinst a z = tyinst x z ∧ c x` >>
    qexists_tac`a` >>
    unabbrev_all_tac >> simp[] >>
    first_x_assum match_mp_tac >>
    simp[fresh_term_def] >>
    imp_res_tac semantics_closes >>
    fs[closes_def] ) >>
  conj_tac >- (
    rw[tvars_def,tyvars_def,MEM_FOLDR_LIST_UNION] >>
    simp[Once semantics_cases] >>
    map_every qexists_tac[`m`,`m'`] >>
    simp[] >>
    `tyinst tyin' ty = tyinst FEMPTY ty` by (
      match_mp_tac tyinst_tyvars1 >>
      imp_res_tac typeset_closes_over >>
      fs[SUBSET_DEF] ) >>
    rw[] >>
    qmatch_abbrev_tac`simple_inst tyin tm has_type tt` >>
    `MAP (tyinst tyin') args = args` by (
      simp[MAP_EQ_ID] >>
      rw[] >>
      CONV_TAC(RAND_CONV(ONCE_REWRITE_CONV[GSYM tyinst_FEMPTY])) >>
      match_mp_tac tyinst_tyvars1 >>
      rw[] >>
      qpat_assum`typeset τi X m`mp_tac >>
      simp[Once semantics_cases] >> strip_tac >>
      imp_res_tac typeset_closes_over >> fs[] >>
      qmatch_assum_abbrev_tac`tvars (simple_inst ti tm) = []` >>
      qspecl_then[`tm`,`ti`]mp_tac tvars_simple_inst >>
      simp[EXTENSION] >>
      `∃n. n < LENGTH args ∧ x = EL n args` by metis_tac[MEM_EL] >>
      disch_then(qspecl_then[`v`,`EL n (tvars tm)`]mp_tac) >>
      strip_tac >- metis_tac[MEM_EL] >>
      pop_assum mp_tac >>
      simp[FLOOKUPD_def,Abbr`ti`] >>
      Q.ISPECL_THEN[`ZIP(tvars tm,args)`,`n`]mp_tac ALOOKUP_ALL_DISTINCT_EL >>
      discharge_hyps >- simp[MAP_ZIP] >>
      simp[EL_ZIP] >>
      metis_tac[] ) >>
    fs[] ) >>
  conj_tac >- (
    rw[tvars_def,tyvars_def,MEM_FOLDR_LIST_UNION] >>
    simp[Once semantics_cases] >>
    map_every qexists_tac[`m`,`m'`,`m''`] >>
    simp[] >>
    `tyinst tyin' ty = tyinst FEMPTY ty` by (
      match_mp_tac tyinst_tyvars1 >>
      imp_res_tac typeset_closes_over >>
      fs[SUBSET_DEF] ) >>
    simp[] >>
    `MAP (tyinst tyin') args = args` by (
      simp[MAP_EQ_ID] >>
      rw[] >>
      CONV_TAC(RAND_CONV(ONCE_REWRITE_CONV[GSYM tyinst_FEMPTY])) >>
      match_mp_tac tyinst_tyvars1 >>
      rw[] >>
      qpat_assum`typeset τi X m`mp_tac >>
      simp[Once semantics_cases] >> strip_tac >>
      imp_res_tac typeset_closes_over >> fs[] >>
      qmatch_assum_abbrev_tac`tvars (simple_inst ti tm) = []` >>
      qspecl_then[`tm`,`ti`]mp_tac tvars_simple_inst >>
      simp[EXTENSION] >>
      `∃n. n < LENGTH args ∧ x = EL n args` by metis_tac[MEM_EL] >>
      disch_then(qspecl_then[`v`,`EL n (tvars tm)`]mp_tac) >>
      strip_tac >- metis_tac[MEM_EL] >>
      pop_assum mp_tac >>
      simp[FLOOKUPD_def,Abbr`ti`] >>
      Q.ISPECL_THEN[`ZIP(tvars tm,args)`,`n`]mp_tac ALOOKUP_ALL_DISTINCT_EL >>
      discharge_hyps >- simp[MAP_ZIP] >>
      simp[EL_ZIP] >>
      metis_tac[] ) >>
    simp[] ) >>
  conj_tac >- (
    rw[tvars_def] >>
    simp[Once semantics_cases] >>
    map_every qexists_tac[`m`,`m'`] >>
    simp[] >>
    fs[ALL_DISTINCT_APPEND,IN_DISJOINT] >>
    conj_tac >- metis_tac[] >>
    conj_tac >- metis_tac[] >>
    conj_asm1_tac >- metis_tac[simple_inst_has_type,welltyped_def] >>
    conj_asm1_tac >- metis_tac[simple_inst_has_type,welltyped_def] >>
    qspecl_then[`tm`,`tyin`]mp_tac simple_inst_has_type >>
    qspecl_then[`tm'`,`tyin`]mp_tac simple_inst_has_type >>
    rw[] >>
    imp_res_tac WELLTYPED_LEMMA >>
    rw[] ) >>
  rw[tvars_def] >>
  simp[Once semantics_cases] >>
  map_every qexists_tac[`mb`,`m`,`m'`] >>
  qspecl_then[`tm`,`tyin`]mp_tac simple_inst_has_type >>
  discharge_hyps >- metis_tac[welltyped_def] >>
  rw[] >>
  qexists_tac`tyinst tyin (typeof tm)` >>
  simp[] >>
  conj_asm1_tac >- (
    imp_res_tac WELLTYPED_LEMMA >>
    rw[] >>
    first_x_assum match_mp_tac >>
    metis_tac[tyvars_typeof_subset_tvars,SUBSET_DEF] ) >>
  qx_gen_tac`z` >> strip_tac >>
  first_x_assum(qspec_then`z`mp_tac) >>
  simp[] >> strip_tac >>
  first_x_assum match_mp_tac >>
  conj_tac >- metis_tac[] >>
  fs[IN_DISJOINT] >>
  reverse conj_tac >- metis_tac[] >>
  qx_genl_tac[`x`,`tx`] >> strip_tac >>
  reverse(Cases_on`s=x`) >- simp[FLOOKUP_UPDATE] >>
  reverse(Cases_on`tx=ty`) >> simp[FLOOKUP_UPDATE] >> rw[] >>
  metis_tac[])

val dbINST_def = Define`
  dbINST tyin (dbVar x ty) = dbVar x (TYPE_SUBST tyin ty) ∧
  dbINST tyin (dbBound n) = dbBound n ∧
  dbINST tyin (dbConst x ty g) = dbConst x (TYPE_SUBST tyin ty) g ∧
  dbINST tyin (dbComb t1 t2) = dbComb (dbINST tyin t1) (dbINST tyin t2) ∧
  dbINST tyin (dbAbs ty t) = dbAbs (TYPE_SUBST tyin ty) (dbINST tyin t)`
val _ = export_rewrites["dbINST_def"]

val dbINST_bind = store_thm("dbINST_bind",
  ``∀tm v n ls.
      (∀ty. dbVFREE_IN (dbVar (FST v) ty) tm ∧ (TYPE_SUBST ls ty = TYPE_SUBST ls (SND v)) ⇒ ty = SND v)
      ⇒ dbINST ls (bind v n tm) = bind (FST v,TYPE_SUBST ls (SND v)) n (dbINST ls tm)``,
  Induct >> simp[] >>
  Cases_on`v`>>simp[] >>
  rpt strip_tac >>
  BasicProvers.CASE_TAC >> fs[] >>
  BasicProvers.CASE_TAC >> fs[])

val dbVSUBST_nil = store_thm("dbVSUBST_nil",
  ``∀tm. dbVSUBST [] tm = tm``,
  Induct >> simp[REV_ASSOCD])
val _ = export_rewrites["dbVSUBST_nil"]

val INST_CORE_dbINST = store_thm("INST_CORE_dbINST",
  ``∀tm tyin env tmi.
      welltyped tm ∧ (∀s s'. MEM (s,s') env ⇒ ∃x ty. s = Var x ty ∧ s' = Var x (TYPE_SUBST tyin ty)) ∧
      INST_CORE env tyin tm = Result tmi ⇒
        db tmi = dbINST tyin (db tm)``,
  completeInduct_on`sizeof tm` >> Cases >> simp[] >- (
    strip_tac >>
    simp[INST_CORE_def] >>
    rw[] >> rw[] )
  >- (
    strip_tac >> rw[INST_CORE_def] >> rw[] )
  >- (
    strip_tac >>
    simp[INST_CORE_def] >>
    rw[] >> fs[] >>
    qmatch_assum_rename_tac`typeof t1 = Fun (typeof t2) rty`[] >>
    first_assum(qspec_then`sizeof t1`mp_tac) >>
    first_x_assum(qspec_then`sizeof t2`mp_tac) >>
    simp[] >>
    disch_then(qspec_then`t2`strip_assume_tac) >>
    disch_then(qspec_then`t1`strip_assume_tac) >>
    rfs[] >>
    Cases_on`INST_CORE env tyin t1` >>fs[] >>
    Cases_on`INST_CORE env tyin t2`>>fs[] >>
    metis_tac[] ) >>
  strip_tac >>
  simp[INST_CORE_def] >>
  rw[] >> fs[] >>
  qmatch_assum_rename_tac`welltyped tm`[] >>
  qmatch_assum_abbrev_tac`IS_RESULT X` >>
  Cases_on`X`>>
  pop_assum(assume_tac o SYM o SIMP_RULE std_ss [markerTheory.Abbrev_def]) >> fs[] >- (
    qmatch_abbrev_tac`bind (x,TYPE_SUBST tyin ty) 0 (db tt) = X` >>
    pop_assum mp_tac >> ntac 3 (pop_assum kall_tac) >> strip_tac >>
    qspecl_then[`db tm`,`x,ty`,`0`,`tyin`]mp_tac dbINST_bind >>
    discharge_hyps >- (
      qx_gen_tac`ty2` >>
      qspecl_then[`tm`,`Var x ty2`]mp_tac dbVFREE_IN_VFREE_IN >>
      rw[] >>
      qmatch_assum_abbrev_tac`INST_CORE env' tyin tm = Y` >>
      qspecl_then[`sizeof tm`,`tm`,`env'`,`tyin`]mp_tac INST_CORE_HAS_TYPE >>
      discharge_hyps >- (
        simp[Abbr`env'`] >>
        metis_tac[] ) >>
      simp[Abbr`Y`] >>
      simp[Abbr`env'`,REV_ASSOCD] >>
      strip_tac >>
      last_x_assum(qspecl_then[`x`,`ty2`]mp_tac) >>
      simp[] ) >>
    rw[] >>
    qmatch_assum_abbrev_tac`INST_CORE env' tyin tm = Y` >>
    first_x_assum(qspec_then`sizeof tm`mp_tac) >> simp[] >>
    disch_then(qspec_then`tm`mp_tac) >> simp[] >>
    disch_then(qspecl_then[`tyin`,`env'`,`tt`]mp_tac) >>
    simp[Abbr`env'`] >>
    discharge_hyps >- metis_tac[] >>
    rw[] ) >>
  qmatch_abbrev_tac`bind (z,TYPE_SUBST tyin ty) 0 (db tt) = dbINST tyin (bind (x,ty) 0 (db tm))` >>
  ntac 3 (pop_assum kall_tac) >>
  qspecl_then[`db tm`,`z,ty`,`x,ty`,`0`,`[]`]mp_tac bind_dbVSUBST_cons >>
  discharge_hyps >- (
    simp[] >>
    simp[dbVFREE_IN_bind] >>
    `∃tmi. INST_CORE [] tyin tm = Result tmi` by (
      Cases_on`INST_CORE [] tyin tm`>>simp[] >>
      imp_res_tac INST_CORE_NIL_IS_RESULT >>
      pop_assum(qspec_then`tyin`strip_assume_tac) >>
      rfs[] ) >> fs[] >>
    first_x_assum(qspec_then`sizeof tm`mp_tac) >> simp[] >>
    disch_then(qspec_then`tm`mp_tac) >> simp[] >>
    disch_then(qspecl_then[`tyin`,`[]`,`tmi`]mp_tac) >>
    rw[] >>
    spose_not_then strip_assume_tac >>
    qspecl_then[`tm`,`Var z ty`]mp_tac dbVFREE_IN_VFREE_IN >>
    simp[] >>
    qspecl_then[`sizeof tm`,`tm`,`[]`,`tyin`]mp_tac INST_CORE_HAS_TYPE >>
    simp[] >> strip_tac >>
    first_x_assum(qspecl_then[`z`,`TYPE_SUBST tyin ty`]mp_tac) >>
    simp[VARIANT_THM,Abbr`z`] >>
    metis_tac[] ) >>
  simp[] >> disch_then(strip_assume_tac o SYM) >> simp[] >>
  qmatch_assum_abbrev_tac`INST_CORE env' tyin tv = Result tt` >>
  `sizeof tv = sizeof tm` by (
    simp[Abbr`tv`] >>
    match_mp_tac SIZEOF_VSUBST >>
    simp[] ) >>
  first_x_assum(qspec_then`sizeof tv`mp_tac) >> simp[] >>
  disch_then(qspec_then`tv`mp_tac) >> simp[] >>
  disch_then(qspecl_then[`tyin`,`env'`,`tt`]mp_tac) >>
  `welltyped tv` by (
    simp[Abbr`tv`] >>
    match_mp_tac VSUBST_WELLTYPED >>
    simp[] >> simp[Once has_type_cases] ) >>
  discharge_hyps >- (
    simp[Abbr`env'`] >>
    metis_tac[] ) >>
  rw[] >>
  qspecl_then[`tm`,`[Var z ty,Var x ty]`]mp_tac VSUBST_dbVSUBST >>
  simp[] >> disch_then(strip_assume_tac o SYM) >> simp[] >>
  qspecl_then[`db tv`,`z,ty`,`0`,`tyin`]mp_tac dbINST_bind >>
  discharge_hyps >- (
    simp[] >>
    qx_gen_tac`ty2` >>
    qspecl_then[`tv`,`Var z ty2`]mp_tac dbVFREE_IN_VFREE_IN >>
    rw[] >>
    qspecl_then[`sizeof tv`,`tv`,`env'`,`tyin`]mp_tac INST_CORE_HAS_TYPE >>
    discharge_hyps >- (
      simp[Abbr`env'`] >>
      metis_tac[] ) >>
    simp[] >>
    simp[Abbr`env'`,REV_ASSOCD] >>
    strip_tac >>
    last_x_assum(qspecl_then[`z`,`ty2`]mp_tac) >>
    simp[] ) >>
  simp[])

val INST_dbINST = store_thm("INST_dbINST",
  ``∀tm tyin.
      welltyped tm ⇒
      db (INST tyin tm) = dbINST tyin (db tm)``,
  rw[INST_def] >>
  imp_res_tac INST_CORE_NIL_IS_RESULT >>
  pop_assum(qspec_then`tyin`strip_assume_tac) >>
  Cases_on`INST_CORE [] tyin tm`>>fs[] >>
  qspecl_then[`tm`,`tyin`,`[]`,`t`]mp_tac INST_CORE_dbINST >>
  simp[])

val ACONV_INST = store_thm("ACONV_INST",
  ``∀t1 t2 tyin. welltyped t1 ∧ ACONV t1 t2 ⇒ ACONV (INST tyin t1) (INST tyin t2)``,
  rw[] >> imp_res_tac ACONV_welltyped >>
  fs[ACONV_db] >> imp_res_tac INST_dbINST >> rw[] )

val INST_HAS_TYPE = store_thm("INST_HAS_TYPE",
  ``∀tm tyin ty. tm has_type ty ⇒ INST tyin tm has_type (TYPE_SUBST tyin ty)``,
  rw[INST_def] >>
  `welltyped tm` by metis_tac[welltyped_def] >>
  imp_res_tac INST_CORE_NIL_IS_RESULT >>
  pop_assum(qspec_then`tyin`strip_assume_tac) >>
  Cases_on`INST_CORE [] tyin tm`>>fs[] >>
  qspecl_then[`sizeof tm`,`tm`,`[]`,`tyin`]mp_tac INST_CORE_HAS_TYPE >>
  rw[] >>
  metis_tac[WELLTYPED_LEMMA])

val type_has_meaning_TYPE_SUBST = store_thm("type_has_meaning_TYPE_SUBST",
  ``∀ty tyin.
    type_has_meaning ty ∧
    EVERY type_has_meaning (MAP FST tyin)
    ⇒
    type_has_meaning (TYPE_SUBST tyin ty)``,
  rw[type_has_meaning_def] >>
  fs[tyinst_TYPE_SUBST] >>
  fs[EVERY_MEM,MEM_MAP,EXISTS_PROD,GSYM LEFT_FORALL_IMP_THM,type_has_meaning_def] >>
  qabbrev_tac`ti = FUN_FMAP (λa. @m. typeset τ (tyinst (tyin_to_fmap tyin) (Tyvar a)) m) (set (tyvars ty))` >>
  `∀a. MEM a (tyvars ty) ⇒ ∃x. typeset τ (FLOOKUPD (tyin_to_fmap tyin) a (Tyvar a)) x` by (
    rw[] >>
    fs[tyvars_tyinst,SUBSET_DEF,GSYM LEFT_FORALL_IMP_THM] >>
    fs[FLOOKUPD_def,tyin_to_fmap_def] >>
    BasicProvers.CASE_TAC >- (
      simp[Once semantics_cases,FLOOKUP_DEF] >>
      first_x_assum match_mp_tac >>
      qexists_tac`a` >> simp[tyvars_def] ) >>
    imp_res_tac ALOOKUP_MEM >>
    fs[MEM_MAP,EXISTS_PROD,MEM_FILTER] >>
    BasicProvers.VAR_EQ_TAC >> fs[] >>
    BasicProvers.VAR_EQ_TAC >>
    last_x_assum(qspecl_then[`x`,`Tyvar a`]mp_tac) >>
    simp[] >>
    disch_then(qspec_then`τ`mp_tac) >>
    simp[] >>
    discharge_hyps >- (
      rw[] >>
      first_x_assum match_mp_tac >>
      qexists_tac`a` >>
      simp[] ) >>
    simp[] ) >>
  `type_valuation ti` by (
    simp[type_valuation_def,Abbr`ti`] >>
    rw[] >>
    SELECT_ELIM_TAC >>
    simp[] >>
    metis_tac[typeset_inhabited] ) >>
  first_x_assum(qspec_then`ti`mp_tac) >>
  simp[] >>
  discharge_hyps >- simp[Abbr`ti`] >>
  strip_tac >> qexists_tac`m` >>
  match_mp_tac (MP_CANON (CONJUNCT1 semantics_simple_inst)) >>
  HINT_EXISTS_TAC >>
  simp[] >>
  rw[] >>
  simp[Abbr`ti`,FUN_FMAP_DEF] >>
  SELECT_ELIM_TAC >> simp[] )

val has_meaning_simple_inst = store_thm("has_meaning_simple_inst",
  ``∀tm tyin.
      has_meaning tm ∧
      ALL_DISTINCT (bv_names tm) ∧
      DISJOINT (set (bv_names tm)) {x | ∃ty. VFREE_IN (Var x ty) tm} ∧
     (∀ty. ty ∈ FRANGE tyin ⇒ type_has_meaning ty)
     ⇒ has_meaning (simple_inst tyin tm)``,
  rw[] >>
  match_mp_tac semantics_has_meaning >>
  qabbrev_tac`τ = FUN_FMAP (K boolset) (set (tvars (simple_inst tyin tm)))` >>
  `type_valuation τ` by (
    simp[type_valuation_def] >>
    simp[Abbr`τ`] >>
    metis_tac[BOOLEAN_IN_BOOLSET] ) >>
  `∃τi. (FDOM τi = set (tvars tm)) ∧ (∀a. MEM a (tvars tm) ⇒ typeset τ (tyinst tyin (Tyvar a)) (τi ' a))` by (
    qexists_tac`FUN_FMAP (λa. @m. typeset τ (tyinst tyin (Tyvar a)) m) (set (tvars tm))` >>
    simp[] >> rw[] >>
    simp[FUN_FMAP_DEF] >>
    SELECT_ELIM_TAC >> simp[] >>
    simp[FLOOKUPD_def] >>
    BasicProvers.CASE_TAC >- (
      simp[Once semantics_cases] >>
      simp[Abbr`τ`,FLOOKUP_FUN_FMAP] >>
      simp[tvars_simple_inst,FLOOKUPD_def] >>
      qexists_tac`a`>>simp[tyvars_def] ) >>
    `x ∈ FRANGE tyin` by metis_tac[FRANGE_FLOOKUP] >>
    res_tac >> pop_assum mp_tac >>
    simp_tac std_ss [type_has_meaning_def] >>
    disch_then match_mp_tac >>
    simp[] >>
    simp[Abbr`τ`,tvars_simple_inst] >>
    simp[SUBSET_DEF,FLOOKUPD_def] >> rw[] >>
    qexists_tac`a`>>simp[] ) >>
  `type_valuation τi` by (
    simp[type_valuation_def,IN_FRANGE] >>
    metis_tac[typeset_inhabited] ) >>
  qabbrev_tac`σ = FUN_FMAP (λ(x,ty). @x. ∃m. typeset τ ty m ∧ x <: m) {(x,ty) | VFREE_IN (Var x ty) (simple_inst tyin tm)}` >>
  `term_valuation τ σ` by (
    simp[term_valuation_def,FEVERY_ALL_FLOOKUP] >>
    simp[Abbr`σ`,FLOOKUP_FUN_FMAP,GSYM LEFT_FORALL_IMP_THM] >>
    simp[VFREE_IN_simple_inst,GSYM LEFT_FORALL_IMP_THM] >>
    qx_genl_tac[`x`,`ty`] >> rw[] >>
    `∃m. typeset τi ty m` by (
      imp_res_tac has_meaning_subterm >> fs[] >>
      fs[type_has_meaning_def] >>
      pop_assum match_mp_tac >>
      simp[] >>
      imp_res_tac tvars_VFREE_IN_subset >>
      fs[SUBSET_DEF,tvars_def] ) >>
    `typeset τ (tyinst tyin ty) m` by (
      match_mp_tac(MP_CANON(CONJUNCT1 semantics_simple_inst)) >>
      qexists_tac`τi` >>
      simp[] >> rw[] >> fs[] >>
      first_x_assum match_mp_tac >>
      imp_res_tac tvars_VFREE_IN_subset >>
      fs[SUBSET_DEF,tvars_def] ) >>
    qexists_tac`m` >>
    simp[] >>
    SELECT_ELIM_TAC >>
    metis_tac[typeset_inhabited,semantics_11] ) >>
  `∃σi. FDOM σi = { (x,ty) | VFREE_IN (Var x ty) tm } ∧
    (∀x ty. VFREE_IN (Var x ty) tm ⇒ FLOOKUP σi (x,ty) = FLOOKUP σ (x,tyinst tyin ty))` by (
    qexists_tac`FUN_FMAP (λ(x,ty). σ ' (x,tyinst tyin ty)) { (x,ty) | VFREE_IN (Var x ty) tm }` >>
    simp[FLOOKUP_FUN_FMAP] >>
    simp[FLOOKUP_DEF] >>
    simp[Abbr`σ`,VFREE_IN_simple_inst] >>
    metis_tac[] ) >>
  `term_valuation τi σi` by (
    simp[term_valuation_def,FEVERY_ALL_FLOOKUP] >>
    qx_gen_tac`k` >>
    PairCases_on`k` >>
    reverse(Cases_on`VFREE_IN (Var k0 k1) tm`) >- (
      simp[FLOOKUP_DEF] ) >>
    simp[] >>
    simp[Abbr`σ`,FLOOKUP_FUN_FMAP] >>
    strip_tac >>
    `type_has_meaning k1` by (
      imp_res_tac has_meaning_subterm >> fs[] ) >>
    fs[type_has_meaning_def] >>
    pop_assum(qspec_then`τi`mp_tac) >>
    discharge_hyps >- (
      simp[] >>
      imp_res_tac tvars_VFREE_IN_subset >>
      fs[tvars_def] ) >>
    strip_tac >>
    qexists_tac`m` >> simp[] >>
    SELECT_ELIM_TAC >>
    `typeset τ (tyinst tyin k1) m` by (
      match_mp_tac(MP_CANON(CONJUNCT1 semantics_simple_inst)) >>
      simp[] >>
      imp_res_tac tvars_VFREE_IN_subset >>
      fs[tvars_def,SUBSET_DEF] >>
      metis_tac[] ) >>
    metis_tac[typeset_inhabited,semantics_11] ) >>
  `∃m. semantics σi τi tm m` by (
    fs[has_meaning_def] >>
    first_x_assum match_mp_tac >>
    simp[] >>
    simp[closes_def] ) >>
  map_every qexists_tac[`σ`,`τ`,`m`] >>
  simp[] >>
  match_mp_tac(MP_CANON(CONJUNCT2 semantics_simple_inst)) >>
  map_every qexists_tac[`σi`,`τi`] >>
  simp[])

val IN_FRANGE_tyin_to_fmap_suff = store_thm("IN_FRANGE_tyin_to_fmap_suff",
  ``∀P tyin. (∀x. MEM x (MAP FST tyin) ⇒ P x) ⇒ (∀x. x ∈ FRANGE (tyin_to_fmap tyin) ⇒ P x)``,
  rw[FRANGE_FLOOKUP,tyin_to_fmap_def] >>
  imp_res_tac ALOOKUP_MEM >>
  fs[MEM_MAP,MEM_FILTER,EXISTS_PROD] >>
  rw[] >> fs[GSYM LEFT_FORALL_IMP_THM] >>
  metis_tac[])

val INST_TYPE_correct = store_thm("INST_TYPE_correct",
  ``∀h c tyin.
      h |= c ∧ EVERY type_has_meaning (MAP FST tyin)
      ⇒
      (MAP (INST tyin) h) |= INST tyin c``,
  simp[sequent_def] >>
  rpt gen_tac >> strip_tac >>
  conj_asm1_tac >- (
    fs[EVERY_MEM,MEM_MAP,GSYM LEFT_FORALL_IMP_THM] >>
    `TYPE_SUBST tyin Bool = Bool` by simp[] >>
    metis_tac[INST_HAS_TYPE] ) >>
  `welltyped c ∧ EVERY welltyped h` by (
    fs[EVERY_MEM] >> metis_tac[welltyped_def] ) >>
  qabbrev_tac`tm = fresh_term {x | ∃ty. VFREE_IN (Var x ty) c} c` >>
  qabbrev_tac`tms = MAP (λt. fresh_term {x | ∃ty. VFREE_IN (Var x ty) t} t) h` >>
  `ACONV c tm` by simp[Abbr`tm`,fresh_term_def] >>
  `EVERY (UNCURRY ACONV) (ZIP(h,tms))` by (
    fs[EVERY_MEM,Abbr`tms`,FORALL_PROD,MEM_ZIP,GSYM LEFT_FORALL_IMP_THM,EL_MAP] >>
    simp[fresh_term_def] ) >>
  `{x | ∃ty. VFREE_IN (Var x ty) tm } = {x | ∃ty. VFREE_IN (Var x ty) c}` by (
    simp[EXTENSION] >> metis_tac[VFREE_IN_ACONV] ) >>
  `EVERY (λ(c,tm). {x | ∃ty. VFREE_IN (Var x ty) tm } = {x | ∃ty. VFREE_IN (Var x ty) c}) (ZIP(h,tms))` by (
    fs[EVERY_MEM,Abbr`tms`,FORALL_PROD,MEM_ZIP,GSYM LEFT_FORALL_IMP_THM,EL_MAP] >>
    simp[EXTENSION] >> metis_tac[VFREE_IN_ACONV] ) >>
  `has_meaning tm` by metis_tac[has_meaning_aconv] >>
  `EVERY has_meaning tms` by (
    fs[EVERY_MEM,Abbr`tms`,FORALL_PROD,MEM_ZIP,GSYM LEFT_FORALL_IMP_THM,EL_MAP] >>
    fs[MEM_MAP,EXISTS_PROD,GSYM LEFT_FORALL_IMP_THM] >>
    fs[MEM_EL,GSYM LEFT_FORALL_IMP_THM] >>
    metis_tac[has_meaning_aconv] ) >>
  `ACONV (INST tyin tm) (INST tyin c)` by metis_tac[ACONV_INST,ACONV_SYM] >>
  `EVERY (λ(c,tm). ACONV (INST tyin tm) (INST tyin c)) (ZIP(h,tms))` by (
    fs[EVERY_MEM,Abbr`tms`,FORALL_PROD,MEM_ZIP,GSYM LEFT_FORALL_IMP_THM,EL_MAP] >>
    fs[MEM_EL,GSYM LEFT_FORALL_IMP_THM] >>
    metis_tac[ACONV_INST,ACONV_SYM] ) >>
  `INST tyin tm = simple_inst (tyin_to_fmap tyin) tm` by (
    match_mp_tac INST_simple_inst >>
    simp[Abbr`tm`,fresh_term_def] ) >>
  `EVERY (λtm. INST tyin tm = simple_inst (tyin_to_fmap tyin) tm) tms` by (
    fs[EVERY_MEM,Abbr`tms`,FORALL_PROD,MEM_ZIP,GSYM LEFT_FORALL_IMP_THM,EL_MAP] >>
    fs[MEM_EL,GSYM LEFT_FORALL_IMP_THM,EL_MAP] >>
    rw[] >>
    match_mp_tac INST_simple_inst >>
    simp[fresh_term_def] ) >>
  conj_asm1_tac >- (
    fs[EVERY_MEM,MEM_MAP,GSYM LEFT_FORALL_IMP_THM] >>
    fs[MEM_ZIP,EXISTS_PROD,Abbr`tms`,GSYM LEFT_FORALL_IMP_THM,EL_MAP] >>
    fs[MEM_EL,GSYM LEFT_FORALL_IMP_THM,EL_MAP] >>
    rw[] >>
    match_mp_tac has_meaning_aconv >|[
      qexists_tac`INST tyin tm`,
      res_tac >>
      qmatch_assum_abbrev_tac`INST tyin tmh = X` >>
      qunabbrev_tac`X` >>
      qexists_tac`INST tyin tmh` >>
      qunabbrev_tac`tmh`] >> simp[] >>
    match_mp_tac has_meaning_simple_inst >>
    simp[Abbr`tm`,fresh_term_def] >>
    ho_match_mp_tac IN_FRANGE_tyin_to_fmap_suff >>
    simp[MEM_MAP,GSYM LEFT_FORALL_IMP_THM] >>
    fs[MEM_EL,GSYM LEFT_FORALL_IMP_THM,EL_MAP]) >>
  rw[] >>
  `semantics σ τ (INST tyin c) = semantics σ τ (INST tyin tm)` by (
    metis_tac[semantics_aconv,ACONV_welltyped,simple_inst_has_type,welltyped_def] ) >>
  `EVERY (λ(c,tm). semantics σ τ (INST tyin c) = semantics σ τ (INST tyin tm)) (ZIP(h,tms))` by (
    fs[EVERY_MEM,Abbr`tms`,FORALL_PROD,MEM_ZIP,GSYM LEFT_FORALL_IMP_THM,EL_MAP] >>
    fs[MEM_MAP,EXISTS_PROD,GSYM LEFT_FORALL_IMP_THM] >>
    fs[MEM_EL,GSYM LEFT_FORALL_IMP_THM] >>
    metis_tac[semantics_aconv,ACONV_welltyped,simple_inst_has_type,welltyped_def] ) >>
  simp[] >>
  match_mp_tac(MP_CANON (CONJUNCT2 semantics_simple_inst)) >>
  qabbrev_tac`τi = FUN_FMAP (λa. @m. typeset τ (tyinst (tyin_to_fmap tyin) (Tyvar a)) m) (BIGUNION (set (MAP (set o tvars) (c::h))))` >>
  qmatch_assum_abbrev_tac`Abbrev(τi = FUN_FMAP ff ss)` >>
  `FINITE ss` by (
    simp[Abbr`ss`,MEM_MAP] >>
    rw[] >> rw[] ) >>
  `type_valuation τi ∧ (∀a. MEM a (tvars c) ∨ (∃t. MEM t h ∧ MEM a (tvars t)) ⇒ ∃x. typeset τ (FLOOKUPD (tyin_to_fmap tyin) a (Tyvar a)) x)` by (
    simp[type_valuation_def] >>
    simp[FRANGE_FLOOKUP] >>
    simp[Abbr`τi`,FLOOKUP_FUN_FMAP] >>
    simp[Abbr`ff`,Abbr`ss`,MEM_MAP] >>
    simp[GSYM LEFT_FORALL_IMP_THM] >>
    simp[CONJ_COMM] >>
    simp[GSYM LEFT_FORALL_IMP_THM,GSYM AND_IMP_INTRO] >>
    simp[AND_IMP_INTRO] >>
    conj_asm1_tac >- (
      gen_tac >>
      simp[FLOOKUPD_def] >>
      strip_tac >>
      BasicProvers.CASE_TAC >- (
        simp[Once semantics_cases] >>
        fs[closes_def] >>
        `tvars (INST tyin c) = tvars (INST tyin tm)` by metis_tac[ACONV_tvars] >>
        fs[] >> rfs[tvars_simple_inst] >>
        fs[SUBSET_DEF,FLOOKUPD_def] >>
        simp[FLOOKUP_DEF] >>
        first_x_assum match_mp_tac >>
        qexists_tac`a` >>
        simp[tyvars_def] >>
        metis_tac[ACONV_tvars] )
      >- (
        fs[tyin_to_fmap_def] >>
        imp_res_tac ALOOKUP_MEM >>
        fs[EVERY_MEM,MEM_MAP,MEM_FILTER,EXISTS_PROD] >>
        rw[] >> fs[GSYM LEFT_FORALL_IMP_THM] >>
        res_tac >> fs[type_has_meaning_def] >>
        first_x_assum match_mp_tac >>
        fs[closes_def] >>
        `tvars (INST tyin c) = tvars (INST tyin tm)` by metis_tac[ACONV_tvars] >>
        fs[] >> rfs[tvars_simple_inst] >>
        fs[SUBSET_DEF,FLOOKUPD_def] >>
        rw[] >>
        first_x_assum match_mp_tac >>
        qmatch_assum_rename_tac`MEM v (tvars c)`[] >>
        qexists_tac`v` >>
        simp[] >>
        metis_tac[ACONV_tvars] )
      >- (
        simp[Once semantics_cases] >>
        `semantics σ τ (INST tyin t) true` by (
          fs[EVERY_MAP] >> fs[EVERY_MEM] >> metis_tac[]) >>
        `∃n. n < LENGTH h ∧ t = EL n h` by metis_tac[MEM_EL] >>
        `semantics σ τ (INST tyin (EL n tms)) true` by (
          fs[EVERY_MEM,MEM_ZIP,FORALL_PROD,GSYM LEFT_FORALL_IMP_THM,Abbr`tms`,EL_MAP] >>
          metis_tac[] ) >>
        `ACONV t (EL n tms)` by (
          fs[EVERY_MEM,MEM_ZIP,FORALL_PROD,GSYM LEFT_FORALL_IMP_THM,Abbr`tms`] ) >>
        `ACONV (INST tyin (EL n tms)) (INST tyin t) ∧ (INST tyin (EL n tms) = simple_inst (tyin_to_fmap tyin) (EL n tms))` by (
          fs[EVERY_MEM,FORALL_PROD,MEM_ZIP,Abbr`tms`,EL_MAP,MEM_MAP,GSYM LEFT_FORALL_IMP_THM] >>
          fs[MEM_EL,EL_MAP,GSYM LEFT_FORALL_IMP_THM] >>
          metis_tac[] ) >>
        `closes (FDOM σ) (FDOM τ) (INST tyin (EL n tms))`
            by metis_tac[semantics_closes] >>
        fs[closes_def] >>
        `tvars (INST tyin t) = tvars (INST tyin (EL n tms))` by metis_tac[ACONV_tvars] >>
        fs[] >> rfs[tvars_simple_inst] >>
        fs[SUBSET_DEF,FLOOKUPD_def] >>
        simp[FLOOKUP_DEF] >>
        first_x_assum match_mp_tac >>
        qexists_tac`a` >>
        simp[tyvars_def] >>
        metis_tac[ACONV_tvars] )
      >- (
        `semantics σ τ (INST tyin t) true` by (
          fs[EVERY_MAP] >> fs[EVERY_MEM] >> metis_tac[]) >>
        `∃n. n < LENGTH h ∧ t = EL n h` by metis_tac[MEM_EL] >>
        `semantics σ τ (INST tyin (EL n tms)) true` by (
          fs[EVERY_MEM,MEM_ZIP,FORALL_PROD,GSYM LEFT_FORALL_IMP_THM,Abbr`tms`,EL_MAP] >>
          metis_tac[] ) >>
        `ACONV t (EL n tms)` by (
          fs[EVERY_MEM,MEM_ZIP,FORALL_PROD,GSYM LEFT_FORALL_IMP_THM,Abbr`tms`] ) >>
        `ACONV (INST tyin (EL n tms)) (INST tyin t) ∧ (INST tyin (EL n tms) = simple_inst (tyin_to_fmap tyin) (EL n tms))` by (
          fs[EVERY_MEM,FORALL_PROD,MEM_ZIP,Abbr`tms`,EL_MAP,MEM_MAP,GSYM LEFT_FORALL_IMP_THM] >>
          fs[MEM_EL,EL_MAP,GSYM LEFT_FORALL_IMP_THM] >>
          metis_tac[] ) >>
        `closes (FDOM σ) (FDOM τ) (INST tyin (EL n tms))`
            by metis_tac[semantics_closes] >>
        fs[tyin_to_fmap_def] >>
        imp_res_tac ALOOKUP_MEM >>
        fs[EVERY_MEM,MEM_MAP,MEM_FILTER,EXISTS_PROD] >>
        rw[] >> fs[GSYM LEFT_FORALL_IMP_THM] >>
        res_tac >> fs[type_has_meaning_def] >>
        first_x_assum match_mp_tac >>
        fs[closes_def] >>
        `tvars (INST tyin (EL n h)) = tvars (INST tyin (EL n tms))` by metis_tac[ACONV_tvars] >>
        fs[] >> rfs[tvars_simple_inst] >>
        fs[SUBSET_DEF,FLOOKUPD_def] >>
        rw[] >>
        first_x_assum match_mp_tac >>
        qmatch_assum_rename_tac`MEM v (tvars (EL n h))`[] >>
        qexists_tac`v` >>
        simp[] >>
        metis_tac[ACONV_tvars] ))>>
    qx_genl_tac[`v`,`t`] >> rw[] >>
    SELECT_ELIM_TAC >>
    metis_tac[typeset_inhabited]) >>
  `∀a. MEM a (tvars tm) ∨ (∃t. MEM t h ∧ MEM a (tvars t)) ⇒
       typeset τ (tyinst (tyin_to_fmap tyin) (Tyvar a)) (τi ' a)` by (
    `tvars tm = tvars c` by metis_tac[ACONV_tvars] >>
    rw[] >- (
      `a ∈ ss` by (rw[Abbr`ss`] >> metis_tac[]) >>
      rw[Abbr`τi`,FUN_FMAP_DEF,Abbr`ff`] >>
      SELECT_ELIM_TAC >> simp[] ) >>
    `a ∈ ss` by (rw[Abbr`ss`,MEM_MAP] >> metis_tac[]) >>
    rw[Abbr`τi`,FUN_FMAP_DEF,Abbr`ff`] >>
    SELECT_ELIM_TAC >> simp[] >>
    metis_tac[]) >>
  qabbrev_tac`σi = FUN_FMAP (λ(x,ty). @m. FLOOKUP σ (x,tyinst (tyin_to_fmap tyin) ty) = SOME m) {(x,ty) | ∃t. VFREE_IN (Var x ty) t ∧ MEM t (c::h)}` >>
  qmatch_assum_abbrev_tac`Abbrev(σi = FUN_FMAP ft st)` >>
  `FINITE st` by (
    `st = BIGUNION (IMAGE (λt. {(x,ty) | VFREE_IN (Var x ty) t}) (set(c::h)))` by (
      simp[Abbr`st`,Once EXTENSION,EXISTS_PROD,FORALL_PROD] >> srw_tac[DNF_ss][] ) >>
    rw[] >> rw[] ) >>
  `∀x ty. (x,ty) ∈ st ⇒ ∃m. FLOOKUP σ (x,tyinst (tyin_to_fmap tyin) ty) = SOME m` by (
    simp[Abbr`st`,GSYM LEFT_FORALL_IMP_THM] >>
    rw[] >- (
      fs[closes_def,FLOOKUP_DEF] >>
      first_x_assum match_mp_tac >>
      qmatch_abbrev_tac`VFREE_IN v ti` >>
      qmatch_assum_abbrev_tac`ACONV tj ti` >>
      qsuff_tac`VFREE_IN v tj` >- metis_tac[VFREE_IN_ACONV] >>
      simp[Abbr`tj`] >>
      qmatch_abbrev_tac`VFREE_IN v (simple_inst tyi tm)` >>
      qspecl_then[`tm`,`tyi`]mp_tac VFREE_IN_simple_inst >>
      discharge_hyps >- (
        simp[Abbr`tm`,fresh_term_def] ) >>
      rw[Abbr`v`] >>
      metis_tac[VFREE_IN_ACONV] ) >>
    `semantics σ τ (INST tyin t) true` by fs[EVERY_MAP,EVERY_MEM] >>
    `closes (FDOM σ) (FDOM τ) (INST tyin t)` by metis_tac[semantics_closes] >>
    fs[closes_def,FLOOKUP_DEF] >>
    first_x_assum match_mp_tac >>
    `∃n. n < LENGTH h ∧ t = EL n h` by metis_tac[MEM_EL] >>
    `ACONV (INST tyin (EL n h)) (INST tyin (EL n tms))` by (
      fs[EVERY_MEM,MEM_EL,GSYM LEFT_FORALL_IMP_THM,EL_ZIP,Abbr`tms`] >>
      metis_tac[ACONV_SYM] ) >>
    BasicProvers.VAR_EQ_TAC >>
    qmatch_abbrev_tac`VFREE_IN v ti` >>
    qmatch_assum_abbrev_tac`ACONV ti tj` >>
    qsuff_tac`VFREE_IN v tj` >- metis_tac[VFREE_IN_ACONV] >>
    simp[Abbr`tj`,Abbr`tms`,EL_MAP] >>
    fs[EVERY_MAP] >> fs[EVERY_MEM] >>
    qmatch_abbrev_tac`VFREE_IN v (simple_inst tyi th)` >>
    qspecl_then[`th`,`tyi`]mp_tac VFREE_IN_simple_inst >>
    discharge_hyps >- (
      fs[MEM_ZIP,FORALL_PROD,GSYM LEFT_FORALL_IMP_THM,EL_MAP] >>
      simp[Abbr`th`,fresh_term_def] ) >>
    rw[Abbr`v`] >>
    fs[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM,FORALL_PROD,EL_MAP] >>
    metis_tac[VFREE_IN_ACONV] ) >>
  `∀x ty. VFREE_IN (Var x ty) tm ∨ (∃t. VFREE_IN (Var x ty) t ∧ MEM t h) ⇒
      FLOOKUP σi (x,ty) = FLOOKUP σ (x,tyinst (tyin_to_fmap tyin) ty)` by (
    rw[] >- (
      `VFREE_IN (Var x ty) c` by metis_tac[VFREE_IN_ACONV] >>
      simp[Abbr`σi`,FLOOKUP_FUN_FMAP] >> simp[Abbr`st`] >>
      reverse BasicProvers.CASE_TAC >- metis_tac[] >>
      simp[Abbr`ft`] >>
      SELECT_ELIM_TAC >>
      simp[] ) >>
    simp[Abbr`σi`,FLOOKUP_FUN_FMAP] >> simp[Abbr`st`] >>
    reverse BasicProvers.CASE_TAC >- metis_tac[] >>
    simp[Abbr`ft`] >>
    SELECT_ELIM_TAC >>
    simp[] ) >>
  `term_valuation τi σi` by (
    simp[term_valuation_def,FEVERY_ALL_FLOOKUP] >>
    simp[Abbr`σi`,FLOOKUP_FUN_FMAP] >>
    simp[Abbr`st`,Abbr`ft`,GSYM LEFT_FORALL_IMP_THM] >>
    rpt gen_tac >>
    reverse(Cases_on`type_has_meaning ty`) >- (
      rw[] >>
      `has_meaning (Var x ty)` by (
        imp_res_tac has_meaning_subterm >>
        fs[EVERY_MEM] >> res_tac >>
        imp_res_tac has_meaning_subterm >>
        fs[]) >>
      fs[] ) >>
    reverse(Cases_on`set (tyvars ty) ⊆ FDOM τi`) >- (
      rfs[Abbr`τi`,FUN_FMAP_DEF,Abbr`ss`] >>
      fs[SUBSET_DEF,MEM_MAP] >>
      rw[] >> imp_res_tac tvars_VFREE_IN_subset >>
      fs[SUBSET_DEF,tvars_def] >>
      metis_tac[] ) >>
    `∃mty. typeset τi ty mty` by (
      fs[type_has_meaning_def] ) >>
    fs[FLOOKUPD_def] >>
    fs[term_valuation_def,FEVERY_ALL_FLOOKUP] >>
    qmatch_abbrev_tac`P ⇒ Q` >>
    strip_tac >>
    qunabbrev_tac`Q` >>
    qexists_tac`mty` >>
    simp[] >>
    SELECT_ELIM_TAC >>
    conj_tac >- metis_tac[] >>
    qx_gen_tac`z` >> strip_tac >>
    qmatch_assum_abbrev_tac`FLOOKUP σ k = SOME z` >>
    first_x_assum(qspecl_then[`k`,`z`]mp_tac) >>
    rw[Abbr`k`] >>
    qspecl_then[`τi`,`ty`,`mty`]mp_tac(CONJUNCT1 semantics_simple_inst) >>
    simp[] >>
    disch_then(qspecl_then[`τ`,`tyin_to_fmap tyin`]mp_tac) >>
    discharge_hyps >- (
      rw[] >>
      last_x_assum(qspec_then`a`kall_tac) >>
      last_x_assum(qspec_then`a`mp_tac) >>
      simp[FLOOKUPD_def] >>
      disch_then match_mp_tac >>
      qpat_assum`Abbrev(T = X)`mp_tac >>
      simp[markerTheory.Abbrev_def] >>
      rw[] >>
      imp_res_tac tvars_VFREE_IN_subset >>
      fs[tvars_def,SUBSET_DEF] >>
      metis_tac[ACONV_tvars] ) >>
    metis_tac[semantics_11] ) >>
  map_every qexists_tac[`σi`,`τi`] >>
  simp[] >>
  reverse conj_tac >- (
    simp[Abbr`tm`,fresh_term_def] ) >>
  qsuff_tac`semantics σi τi c true` >- metis_tac[semantics_aconv] >>
  first_x_assum match_mp_tac >>
  simp[] >>
  reverse conj_tac >- (
    simp[closes_def] >>
    simp[Abbr`τi`,Abbr`σi`] >>
    simp[Abbr`ss`,Abbr`st`] >>
    metis_tac[] ) >>
  simp[EVERY_MEM] >>
  rw[] >>
  `∃n. n < LENGTH h ∧ t = EL n h` by metis_tac[MEM_EL] >>
  `ACONV (EL n h) (EL n tms)` by (
    fs[EVERY_MEM,MEM_ZIP,GSYM LEFT_FORALL_IMP_THM,Abbr`tms`] ) >>
  `welltyped t` by fs[EVERY_MEM] >>
  qsuff_tac`semantics σi τi (EL n tms) true` >- metis_tac[semantics_aconv] >>
  `semantics σ τ (INST tyin t) true` by (
    fs[EVERY_MEM,MEM_MAP,GSYM LEFT_FORALL_IMP_THM] ) >>
  `semantics σ τ (simple_inst (tyin_to_fmap tyin) (EL n tms)) true` by (
    rfs[EVERY_MEM,MEM_MAP,GSYM LEFT_FORALL_IMP_THM] >>
    fs[MEM_ZIP,FORALL_PROD,Abbr`tms`,EL_MAP,GSYM LEFT_FORALL_IMP_THM,MEM_MAP] >>
    metis_tac[] ) >>
  `has_meaning (EL n tms)` by (
    match_mp_tac has_meaning_aconv >>
    qexists_tac`EL n h` >>
    fs[EVERY_MEM] ) >>
  `∃m. semantics σi τi (EL n tms) m` by (
    fs[has_meaning_def] >>
    first_x_assum match_mp_tac >>
    simp[] >>
    fs[closes_def] >>
    simp[Abbr`τi`,Abbr`σi`] >>
    simp[Abbr`ss`,Abbr`st`,SUBSET_DEF,MEM_MAP] >>
    metis_tac[VFREE_IN_ACONV,ACONV_tvars] ) >>
  qspecl_then[`σi`,`τi`,`EL n tms`,`m`]mp_tac(CONJUNCT2 semantics_simple_inst) >>
  simp[] >>
  disch_then(qspecl_then[`σ`,`τ`,`tyin_to_fmap tyin`]mp_tac) >>
  discharge_hyps >- (
    conj_tac >- (
      rw[] >> fs[] >>
      metis_tac[ACONV_tvars] ) >>
    conj_tac >- metis_tac[VFREE_IN_ACONV] >>
    fs[EVERY_MEM,MEM_ZIP,GSYM LEFT_FORALL_IMP_THM,EXISTS_PROD,Abbr`tms`,EL_MAP,fresh_term_def] ) >>
  metis_tac[semantics_11])

(*
val new_basic_definition_correct = store_thm("new_basic_definition_correct",
  ``∀r ty n. has_meaning r ∧ closed r ∧ set(tvars r) ⊆ set(tyvars ty) ∧ r has_type ty
    ⇒ [] |= (Const n ty (Defined r) === r)``,
  simp[sequent_def,EQUATION_HAS_TYPE_BOOL,welltyped_def,equation_has_meaning_iff] >>
  rpt gen_tac >> strip_tac >>
  conj_asm1_tac >- metis_tac[WELLTYPED_LEMMA] >> simp[] >> pop_assum kall_tac >>
  conj_tac >- (
    match_mp_tac semantics_has_meaning >>
    fs[has_meaning_def] >>
    simp[Once semantics_cases] >>
    map_every qexists_tac[`σ`,`τ`] >> simp[] >>

    first_x_assum(qspecl_then[`τ`,`FEMPTY`]mp_tac) >>
    fs[closes_def] >>
    strip_tac >>

*)
*)

val _ = export_theory()
