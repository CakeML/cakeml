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

(*
val simple_subst_compose = store_thm("simple_subst_compose",
  ``∀tm σ1 σ2. simple_subst σ2 (simple_subst σ1 tm) = simple_subst ((simple_subst σ2 o_f σ1) ⊌ σ2) tm``,
  Induct >- (
    simp[FLOOKUPD_def,FLOOKUP_FUNION,FLOOKUP_o_f] >> rw[] >>
    BasicProvers.CASE_TAC >>
    BasicProvers.CASE_TAC >>
    simp[FLOOKUPD_def] ) >> simp[] >>
    )
*)

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
               (∀s s'. MEM (s',s) ilist ⇒ ∃x ty. s = Var x ty) ∧
               ALL_DISTINCT (MAP SND ilist)
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
  simp[MAP_SND_FILTER_NEQ,FILTER_ALL_DISTINCT,MEM_FILTER,MEM_MAP,EXISTS_PROD] >>
  fs[MEM_MAP,EXISTS_PROD,IN_DISJOINT] >>
  metis_tac[])

val dest_tyvar_def = Define`
  dest_tyvar (Tyvar x) = x`
val _ = export_rewrites["dest_tyvar_def"]

val tyin_to_fmap_def = Define`
  tyin_to_fmap tyin = alist_to_fmap (MAP (λ(v,k). (dest_tyvar k,v)) tyin)`

val tyinst_TYPE_SUBST = store_thm("tyinst_TYPE_SUBST",
  ``∀ty tyin. (∀s s'. MEM (s,s') tyin ⇒ ∃v. s' = Tyvar v) ⇒ TYPE_SUBST tyin ty = tyinst (tyin_to_fmap tyin) ty``,
  ho_match_mp_tac type_ind >>
  conj_tac >- (
    simp[REV_ASSOCD_ALOOKUP,FLOOKUPD_def,tyin_to_fmap_def] >> rw[] >>
    BasicProvers.CASE_TAC >> BasicProvers.CASE_TAC >>
    TRY (
      fs[ALOOKUP_FAILS] >>
      imp_res_tac ALOOKUP_MEM >>
      fs[MEM_MAP,EXISTS_PROD] >>
      res_tac >> fs[] >>
      metis_tac[dest_tyvar_def] ) >>
    fs[ALOOKUP_LEAST_EL] >> rw[] >>
    fs[MEM_EL] >> rw[] >>
    numLib.LEAST_ELIM_TAC >>
    conj_tac >- metis_tac[] >> rw[] >>
    numLib.LEAST_ELIM_TAC >>
    conj_tac >- metis_tac[] >> rw[] >>
    `¬(n < n'')` by metis_tac[] >>
    `¬(n' < n''')` by metis_tac[] >>
    fs[EL_MAP] >> rfs[EL_MAP] >>
    fs[UNCURRY,GSYM LEFT_FORALL_IMP_THM] >>
    `∃v. SND (EL n' tyin) = Tyvar v` by metis_tac[SND,pair_CASES] >>
    fs[] >>
    `¬(n < n''')` by (
      strip_tac >>
      first_x_assum(qspec_then`n`mp_tac) >>
      simp[EL_MAP,UNCURRY] >>
      metis_tac[dest_tyvar_def] ) >>
    `¬(n' < n'')` by (
      strip_tac >>
      last_x_assum(qspec_then`n'`mp_tac) >>
      simp[EL_MAP,UNCURRY] ) >>
    `n''' < LENGTH tyin` by DECIDE_TAC >>
    fs[EL_MAP,UNCURRY] >>
    `∃v'. SND (EL n''' tyin) = Tyvar v'` by metis_tac[SND,pair_CASES] >>
    fs[] >> rw[] >>
    `¬(n''' < n'')` by (
      strip_tac >>
      last_x_assum(qspec_then`n'''`mp_tac) >>
      simp[EL_MAP,UNCURRY] ) >>
    simp[EL_MAP,UNCURRY] >>
    `n'' < LENGTH tyin` by DECIDE_TAC >>
    fs[EL_MAP,UNCURRY] >>
    `¬(n'' < n''')` by (
      strip_tac >>
      first_x_assum(qspec_then`n''`mp_tac) >>
      simp[EL_MAP,UNCURRY] >>
      metis_tac[dest_tyvar_def]) >>
    `n'' = n'''` by DECIDE_TAC >>
    rw[] ) >>
  rw[MAP_EQ_f,EVERY_MEM] >>
  metis_tac[])

val INST_CORE_simple_inst = store_thm("INST_CORE_simple_inst",
  ``∀env tyin tm.
      ALL_DISTINCT (bv_names tm ++ (MAP (FST o dest_var o SND) env)) ∧
      DISJOINT (set(bv_names tm)) {x | ∃ty. VFREE_IN (Var x ty) tm} ∧
      (∀s s'. MEM (s,s') tyin ⇒ ∃v. s' = Tyvar v) ∧
      (∀s s'. MEM (s,s') env ⇒ ∃x ty. s = Var x ty ∧ s' = Var x (TYPE_SUBST tyin ty)) ∧
      (∀x ty ty'. VFREE_IN (Var x ty) tm ∧ MEM (Var x ty') (MAP FST env) ⇒ ty' = ty)
      ⇒ INST_CORE env tyin tm = Result (simple_inst (tyin_to_fmap tyin) tm)``,
  ho_match_mp_tac INST_CORE_ind >>
  conj_tac >- (
    simp[INST_CORE_def] >> rpt gen_tac >> strip_tac >>
    qspecl_then[`ty`,`tyin`]mp_tac tyinst_TYPE_SUBST >>
    discharge_hyps >- metis_tac[] >> simp[] >> rw[] >>
    imp_res_tac (REWRITE_RULE[PROVE[]``A ∨ B ⇔ ¬B ⇒ A``]REV_ASSOCD_MEM) >>
    qmatch_assum_abbrev_tac`MEM (p,q) env` >>
    first_x_assum(qspecl_then[`p`,`q`]mp_tac) >>
    simp[Abbr`q`] >> rw[] >>
    fs[MEM_MAP,EXISTS_PROD] >>
    metis_tac[] ) >>
  conj_tac >- (
    simp[INST_CORE_def] >> rw[] >>
    match_mp_tac tyinst_TYPE_SUBST >>
    metis_tac[] ) >>
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
      DISJOINT (set (bv_names tm)) {x | ∃ty. VFREE_IN (Var x ty) tm} ∧
      (∀s s'. MEM (s,s') tyin ⇒ ∃v. s' = Tyvar v)
      ⇒
      INST tyin tm = simple_inst (tyin_to_fmap tyin) tm``,
  rw[INST_def] >>
  qspecl_then[`[]`,`tyin`,`tm`]mp_tac INST_CORE_simple_inst >>
  simp[] >> discharge_hyps >- metis_tac[] >> rw[])

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

(* not true: application with operator with variable type is not welltyped
val simple_inst_welltyped = store_thm("simple_inst_welltyped",
  ``∀tm tyin. welltyped (simple_inst tyin tm) ⇔ welltyped tm``,
  reverse(rw[EQ_IMP_THM])>-metis_tac[simple_inst_has_type,WELLTYPED,WELLTYPED_LEMMA]>>
  pop_assum mp_tac >> map_every qid_spec_tac[`tyin`,`tm`] >>
  Induct >> rw[]
  >- metis_tac[]
  >- metis_tac[]
  >- (
    res_tac >>
    imp_res_tac simple_inst_has_type >>
    `TYPE_SUBST tyin (typeof tm) = Fun (typeof (simple_inst tyin tm')) rty` by metis_tac[WELLTYPED_LEMMA]
  metis_tac[WELLTYPED,WELLTYPED_LEMMA,simple_inst_has_type]
*)

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

val (semantics_rules,semantics_ind,semantics_cases) = xHol_reln"semantics"`
  (FLOOKUP τ s = SOME m ⇒ typeset τ (Tyvar s) m) ∧

  (typeset τ (Tyapp (Typrim "bool" 0) []) boolset) ∧

  (typeset τ x mx ∧ typeset τ y my
   ⇒
   typeset τ (Tyapp (Typrim "->" 2) [x;y]) (funspace mx my)) ∧

  (p = fresh_term {} p0 ∧
   LENGTH (tvars p) = LENGTH args ∧
   tyin = alist_to_fmap(ZIP (tvars p, args)) ∧
   p has_type Fun rty Bool ∧
   typeset FEMPTY (tyinst tyin rty) mrty ∧
   semantics FEMPTY FEMPTY (simple_inst tyin p) mp ∧
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
   semantics FEMPTY FEMPTY (simple_inst tyin t) mt
   ⇒
   semantics σ τ (Const s ty (Defined t0)) mt) ∧

  (p = fresh_term {} p0 ∧
   typeset τ (Tyapp (Tydefined op p) args) maty ∧
   tyin = alist_to_fmap(ZIP (tvars p, args)) ∧
   simple_inst tyin p has_type Fun rty Bool ∧
   typeset FEMPTY rty mrty
   ⇒
   semantics σ τ (Const s (Fun (Tyapp (Tydefined op p0) args) rty) (Tyrep op p0))
    (abstract maty mrty (λx. x))) ∧

  (p = fresh_term {} p0 ∧
   typeset τ (Tyapp (Tydefined op p) args) maty ∧
   tyin = alist_to_fmap(ZIP (tvars p, args)) ∧
   simple_inst tyin p has_type Fun rty Bool ∧
   typeset FEMPTY rty mrty ∧
   semantics FEMPTY FEMPTY (simple_inst tyin p) mp
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

val type_valuation_def = Define`
  type_valuation τ ⇔ ∀x. x ∈ FRANGE τ ⇒ ∃y. y <: x`

val type_valuation_FEMPTY = store_thm("type_valuation_FEMPTY",
  ``type_valuation FEMPTY``, rw[type_valuation_def])
val _ = export_rewrites["type_valuation_FEMPTY"]

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

val typeset_tyvars = prove(
  ``(∀τ1 ty m. typeset τ1 ty m ⇒ ∀τ2. (∀x. x ∈ set(tyvars ty) ⇒ FLOOKUP τ1 x = FLOOKUP τ2 x) ⇒ typeset τ2 ty m) ∧
    (∀σ τ tm m. semantics σ τ tm m ⇒ T)``,
  ho_match_mp_tac (theorem"semantics_strongind") >> simp[] >>
  conj_tac >- (
    ntac 2 (simp[Once semantics_cases]) >>
    simp[FLOOKUP_DEF,SUBMAP_DEF,tyvars_def] ) >>
  conj_tac >- (
    rpt gen_tac >> strip_tac >>
    simp[Once semantics_cases] >> rw[] >>
    fs[tyvars_def,MEM_LIST_UNION] >>
    metis_tac[] ) >>
  rpt gen_tac >> strip_tac >>
  simp[Once semantics_cases] >> rw[] >>
  fs[tyvars_def,MEM_LIST_UNION] >>
  qmatch_assum_rename_tac`w <: mrty`[] >>
  qmatch_assum_rename_tac`holds mp w`[] >>
  map_every qexists_tac[`mp`,`mrty`,`rty`,`w`] >> simp[])
val typeset_tyvars = save_thm("typeset_tyvars",MP_CANON(CONJUNCT1 typeset_tyvars))

val typeset_tyvars_typeset_exists = prove(
  ``(∀τ1 ty m. typeset τ1 ty m ⇒ ∀τ2. (∀x. x ∈ set(tyvars ty) ⇒ x ∈ FDOM τ1 ⇒ x ∈ FDOM τ2) ⇒ ∃m2. typeset τ2 ty m2) ∧
    (∀σ τ tm m. semantics σ τ tm m ⇒ T)``,
  ho_match_mp_tac (theorem"semantics_strongind") >> simp[] >>
  conj_tac >- (
    ntac 2 (simp[Once semantics_cases]) >>
    simp[FLOOKUP_DEF,SUBMAP_DEF,tyvars_def] ) >>
  conj_tac >- (
    rpt gen_tac >> strip_tac >>
    simp[Once semantics_cases] >> rw[] >>
    fs[tyvars_def,MEM_LIST_UNION] >>
    metis_tac[] ) >>
  rpt gen_tac >> strip_tac >>
  simp[Once semantics_cases] >> rw[] >>
  fs[tyvars_def,MEM_LIST_UNION] >>
  qmatch_assum_rename_tac`w <: mrty`[] >>
  qmatch_assum_rename_tac`holds mp w`[] >>
  map_every qexists_tac[`mp`,`mrty`,`rty`,`w`] >> simp[])
val typeset_tyvars_typeset_exists = save_thm("typeset_tyvars_typeset_exists",MP_CANON(CONJUNCT1 typeset_tyvars_typeset_exists))

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

val typeset_closes_over = store_thm("typeset_closes_over",
  ``(∀τ ty m. typeset τ ty m ⇒ set (tyvars ty) ⊆ FDOM τ) ∧
    (∀σ τ tm m. semantics σ τ tm m ⇒
      type_valuation τ ∧ (∀s m ty. (s,ty) ∈ FDOM σ ⇒ set (tyvars ty) ⊆ FDOM τ)
      ⇒ set (tvars tm) ⊆ FDOM τ)``,
  ho_match_mp_tac (theorem"semantics_strongind") >>
  simp[tyvars_def] >>
  conj_tac >- ( rw[Once semantics_cases,FLOOKUP_DEF] ) >>
  conj_tac >- (
    rpt gen_tac >> strip_tac >>
    fs[SUBSET_DEF,MEM_LIST_UNION,MEM_FOLDR_LIST_UNION,EVERY_MEM] >>
    fs[SIMP_RULE std_ss[EXTENSION]tyvars_tyinst] >>
    fs[GSYM LEFT_FORALL_IMP_THM] >> rw[] >>
    qmatch_assum_abbrev_tac`tvars (inst tyin tm) = []` >>
    qspecl_then[`tm`,`tyin`]mp_tac tvars_simple_inst >>
    simp[EXTENSION,PROVE[]``¬P ∨ ¬Q ⇔ Q ⇒ ¬P``] >>
    rw[] >>
    `∃n. n < LENGTH args ∧ y = EL n args` by metis_tac[MEM_EL] >>
    first_x_assum(qspecl_then[`x`,`EL n (tvars tm)`]mp_tac) >>
    discharge_hyps >- (
      simp[FLOOKUPD_def,Abbr`tyin`] >>
      BasicProvers.CASE_TAC >- (
        fs[ALOOKUP_FAILS] >>
        rfs[MEM_ZIP] >>
        metis_tac[] ) >>
      Q.ISPECL_THEN[`ZIP(tvars tm,args)`,`n`]mp_tac ALOOKUP_ALL_DISTINCT_EL >>
      discharge_hyps >- simp[MAP_ZIP] >> rw[EL_ZIP] ) >>
    metis_tac[MEM_EL] ) >>
  conj_tac >- (
    rw[FLOOKUP_DEF,tvars_def] >>
    metis_tac[] ) >>
  conj_tac >- (
    rw[MEM_EL,tvars_def,tyvars_def] ) >>
  conj_tac >- (
    rw[MEM_EL,tvars_def,tyvars_def] ) >>
  conj_tac >- (
    rw[tyvars_tyinst,SUBSET_DEF,tvars_def] >>
    qmatch_assum_abbrev_tac`tvars (inst tyin tm) = []` >>
    qspecl_then[`tm`,`tyin`]mp_tac tvars_simple_inst >>
    simp[EXTENSION,PROVE[]``¬P ∨ ¬Q ⇔ Q ⇒ ¬P``] >>
    qmatch_assum_rename_tac`MEM x (tyvars (FLOOKUPD tyin y (Tyvar y)))`[] >>
    disch_then(qspecl_then[`x`,`y`]mp_tac) >>
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

(* not true.
  (λ(x:'a). x:'b) aconv (λ(y:'a). x:'b) but
 ~(λ(x:'b). x:'b) aconv (λ(y:'b). x:'b)

need to restrict to "good" (fresh) terms

val simple_inst_raconv = store_thm("simple_inst_raconv",
  ``∀env tp. RACONV env tp ⇒
      ∀tyin.
        (∀x1 ty1 x2 ty2. MEM (Var x1 ty1,Var x2 ty2) env ⇒ ty1 = ty2) ⇒
        RACONV (MAP (λ(x,y). (simple_inst tyin x, simple_inst tyin y)) env)
               (simple_inst tyin (FST tp), simple_inst tyin (SND tp))``,
  ho_match_mp_tac RACONV_ind >> simp[RACONV] >>
  conj_tac >- (
    Induct >> simp[ALPHAVARS_def] >>
    Cases >> simp[] >> rw[] >> rw[] >>
    res_tac >> pop_assum mp_tac >>
    discharge_hyps >- metis_tac[] >>
    rw[] >>
    `ty1 = ty2` by metis_tac[ALPHAVARS_MEM,FST,SND,term_11] >>
    rw[] >>
    Cases_on`q`>>Cases_on`r`>>fs[]
  res_tac
*)

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
    metis_tac[ACONV_TYPE,ACONV_welltyped,WELLTYPED_LEMMA,WELLTYPED,ACONV_TRANS,ACONV_SYM] ) >>
  qmatch_abbrev_tac`semantics s t u mp` >>
  qmatch_assum_abbrev_tac`semantics s t v mp` >>
  qsuff_tac`semantics s t u = semantics s t v`>-rw[] >>
  match_mp_tac semantics_aconv >>
  unabbrev_all_tac >> simp[] >>
  conj_tac >- metis_tac[simple_inst_has_type,welltyped_def] >>
*)

(*
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
    rw[] >>
    qmatch_assum_abbrev_tac`welltyped (inst tyin tm)` >>
    qspecl_then[`tm`,`tyin`]mp_tac simple_inst_has_type >> rw[] >>
    imp_res_tac(CONJUNCT1 typeset_closes_over) >> fs[] >>
    metis_tac[WELLTYPED_LEMMA,typeset_tyvars,MEM]) >>
  conj_tac >- (
    rw[] >>
    rw[Once semantics_cases] >>
    fsrw_tac[DNF_ss][] >>
    qmatch_assum_rename_tac`mt <: maty`[] >>
    map_every qexists_tac[`mty`,`maty`] >>

    rw[] >- (

      metis_tac[typeset_tyvars,typeset_closes_over,SUBSET_DEF,FDOM_FEMPTY,NOT_IN_EMPTY] ) >>
    match_mp_tac ABSTRACT_IN_FUNSPACE >> simp[] >>
    qpat_assum`typeset τ (X Y) Z` mp_tac >> rw[Once semantics_cases] >>
    fs[suchthat_def] >>
    qmatch_assum_abbrev_tac`dbhas_type (dbinst tyin tm) fty` >>
    qspecl_then[`tm`,`Fun rty Bool`]mp_tac dbhas_type_dbinst >> simp[] >>
    disch_then(qspec_then`tyin`strip_assume_tac) >>
    imp_res_tac dbhas_type_11 >>
    fs[Abbr`fty`] >> rw[] >>
    metis_tac[semantics_11,type_valuation_FEMPTY]) >>
  conj_tac >- (
    rw[] >>
    rw[Once dbhas_type_cases] >>
    rw[Once semantics_cases] >>
    fsrw_tac[DNF_ss][] >>
    imp_res_tac dbhas_type_11 >> rw[] >>
    qmatch_assum_rename_tac`typeset FEMPTY ty mm`[] >>
    map_every qexists_tac[`mm`,`mty`] >> rw[] >-
      metis_tac[typeset_tyvars,typeset_closes_over,SUBSET_DEF,FDOM_FEMPTY,NOT_IN_EMPTY] >>
    match_mp_tac ABSTRACT_IN_FUNSPACE >>
    qpat_assum`typeset τ (X Y) Z` mp_tac >> rw[Once semantics_cases] >>
    qmatch_assum_abbrev_tac`dbhas_type (dbinst tyin tm) fty` >>
    qspecl_then[`tm`,`Fun rty Bool`]mp_tac dbhas_type_dbinst >> simp[] >>
    disch_then(qspec_then`tyin`strip_assume_tac) >>
    imp_res_tac dbhas_type_11 >>
    fs[Abbr`fty`] >> rw[] >- (
      fs[suchthat_def] >>
      metis_tac[semantics_11,type_valuation_FEMPTY,term_valuation_FEMPTY] ) >>
    match_mp_tac ch_def >>
    fs[suchthat_def] >>
    metis_tac[] ) >>
  conj_tac >- (
    rw[] >> fs[] >>
    qpat_assum`dbwelltyped Y`mp_tac >>
    simp[dbwelltyped_def] >>
    simp[Once dbhas_type_cases] >>
    disch_then(qx_choosel_then[`dty`,`rty`]strip_assume_tac) >>
    simp[Once dbhas_type_cases] >>
    fsrw_tac[DNF_ss][] >>
    qexists_tac`dty` >>
    CONV_TAC SWAP_EXISTS_CONV >>
    qexists_tac`rty` >> rw[] >>
    imp_res_tac dbhas_type_11 >> rw[] >>
    fs[Once (Q.SPECL[`τ`,`Fun X Y`](CONJUNCT1 semantics_cases))] >> rw[] >>
    qexists_tac`my` >>
    imp_res_tac semantics_11 >>
    rpt BasicProvers.VAR_EQ_TAC >>
    simp[] >>
    match_mp_tac APPLY_IN_RANSPACE >>
    qmatch_assum_rename_tac`typeset τ rty mx`[] >>
    qexists_tac`mx` >> simp[]) >>
  rw[] >> fs[] >>
  simp[Once dbhas_type_cases] >>
  fsrw_tac[DNF_ss][] >>
  simp[Once semantics_cases] >>
  fsrw_tac[DNF_ss][] >>
  res_tac >>
  `good_env τ ((ty,mt)::env)` by ( fs[good_env_def] >> metis_tac[] ) >> fs[] >>
  imp_res_tac dbhas_type_11 >> rw[] >>
  imp_res_tac semantics_11 >> rw[] >>
  qmatch_assum_rename_tac`dbhas_type t tty`[] >>
  qmatch_assum_rename_tac`typeset τ tty mtt `[] >>
  map_every qexists_tac[`tty`,`mty`,`mtt`] >> rw[] >>
  match_mp_tac ABSTRACT_IN_FUNSPACE >> rw[])

val tyvars_subset_dbtvars = store_thm("tyvars_subset_dbtvars",
  ``∀tm ty. dbhas_type tm ty ⇒ set (tyvars ty) ⊆ set (dbtvars tm)``,
  ho_match_mp_tac dbhas_type_ind >>
  simp[] >>
  simp[SUBSET_DEF,MEM_LIST_UNION,tyvars_def,MEM_FLAT,MEM_MAP] >>
  metis_tac[MEM_EL])

val (good_bvs_rules,good_bvs_ind,good_bvs_cases) = Hol_reln`
  good_bvs env (dbFree s ty) ∧
  (n < LENGTH env ∧ (EL n env = ty) ⇒ good_bvs env (dbVar n ty)) ∧
  good_bvs env (dbConst s ty g) ∧
  (good_bvs env t1 ∧ good_bvs env t2 ⇒ good_bvs env (dbComb t1 t2)) ∧
  (good_bvs (ty::env) tm ⇒ good_bvs env (dbAbs ty tm))`

val good_bvs_dbComb = store_thm("good_bvs_dbComb",
  ``∀env t1 t2. good_bvs env (dbComb t1 t2) ⇔ good_bvs env t1 ∧ good_bvs env t2``,
  rw[Once good_bvs_cases])
val _ = export_rewrites["good_bvs_dbComb"]

val good_bvs_dbConst = store_thm("good_bvs_dbConst",
  ``∀env s ty g. good_bvs env (dbConst s ty g)``,
  rw[Once good_bvs_cases])
val _ = export_rewrites["good_bvs_dbConst"]

val good_bvs_dbbv = store_thm("good_bvs_dbbv",
  ``∀env tm. good_bvs env tm ⇒ ∀n ty. MEM (n,ty) (dbbv tm) ⇒ n < LENGTH env ∧ EL n env = ty``,
  ho_match_mp_tac good_bvs_ind >>
  simp[MEM_MAP,MEM_FILTER,EXISTS_PROD] >>
  conj_tac >- metis_tac[] >>
  rpt gen_tac >> strip_tac >>
  simp[GSYM LEFT_FORALL_IMP_THM] >>
  CONV_TAC SWAP_FORALL_CONV >>
  Cases >> simp[] >> rw[] >> res_tac >> fs[])

val dbbv_good_bvs = store_thm("dbbv_good_bvs",
  ``∀tm env. (∃ρ. good_bvs ρ tm) ∧ (∀n ty. MEM (n,ty) (dbbv tm) ⇒ n < LENGTH env ∧ EL n env = ty) ⇒ good_bvs env tm``,
  Induct >> simp[]
  >- (simp[Once good_bvs_cases] >> simp[Once good_bvs_cases])
  >- (simp[Once good_bvs_cases] >> simp[Once good_bvs_cases])
  >- metis_tac[] >>
  rw[Once good_bvs_cases] >>
  rw[Once good_bvs_cases] >>
  first_x_assum match_mp_tac >>
  conj_tac >- metis_tac[] >>
  fs[MEM_MAP,MEM_FILTER,EXISTS_PROD,GSYM LEFT_FORALL_IMP_THM] >>
  Cases >> rw[] >- (
    imp_res_tac good_bvs_dbbv >> fs[] ) >>
  res_tac >> fs[])

val semantics_fvs = store_thm("semantics_fvs",
  ``∀τ env σ1 σ2 t.
      type_valuation τ ∧
      (∀x ty. MEM (x,ty) (dbfv t) ⇒ (FLOOKUP σ1 (x,ty) = FLOOKUP σ2 (x,ty)))
      ⇒ semantics env σ1 τ t = semantics env σ2 τ t``,
  gen_tac >> (CONV_TAC (RESORT_FORALL_CONV List.rev)) >> Induct
  >- (
    rw[FUN_EQ_THM] >>
    rw[Once semantics_cases] >>
    rw[Once semantics_cases] )
  >- (
    rw[FUN_EQ_THM] >>
    rw[Once semantics_cases] >>
    rw[Once semantics_cases] )
  >- (
    rw[FUN_EQ_THM] >>
    rw[Once semantics_cases] >>
    rw[Once semantics_cases,SimpRHS] )
  >- (
    rw[FUN_EQ_THM] >>
    rw[Once semantics_cases] >>
    rw[Once semantics_cases,SimpRHS] >>
    metis_tac[]) >>
  rw[FUN_EQ_THM] >>
  rw[Once semantics_cases] >>
  rw[Once semantics_cases,SimpRHS] >>
  rw[EQ_IMP_THM] >>
  map_every qexists_tac[`mb`,`mty`,`mtyb`,`tyb`] >>
  rw[] >> metis_tac[])

val semantics_bvs = store_thm("semantics_bvs",
  ``∀t ρ1 ρ2 σ τ.
      (∀n ty. MEM (n,ty) (dbbv t) ⇒ (n < LENGTH ρ1 ⇔ n < LENGTH ρ2) ∧ (n < LENGTH ρ1 ⇒ EL n ρ1 = EL n ρ2))
    ⇒ semantics ρ1 σ τ t = semantics ρ2 σ τ t``,
  Induct >- (
    simp[Once good_bvs_cases] >>
    simp[Once good_bvs_cases] >>
    simp[FUN_EQ_THM] >>
    simp[Once semantics_cases] >>
    simp[Once semantics_cases] )
  >- (
    simp[FUN_EQ_THM] >>
    simp[Once semantics_cases] >>
    simp[Once semantics_cases] >>
    metis_tac[])
  >- (
    simp[FUN_EQ_THM] >>
    simp[Once semantics_cases] >>
    simp[Once semantics_cases,SimpRHS] )
  >- (
    simp[] >> rw[] >>
    simp[FUN_EQ_THM] >>
    simp[Once semantics_cases] >>
    simp[Once semantics_cases,SimpRHS] >>
    srw_tac[DNF_ss][] >>
    metis_tac[] ) >>
  (
    simp[] >>
    rw[MEM_MAP,MEM_FILTER,EXISTS_PROD,GSYM LEFT_FORALL_IMP_THM] >>
    simp[FUN_EQ_THM] >>
    simp[Once semantics_cases] >>
    simp[Once semantics_cases,SimpRHS] >>
    srw_tac[DNF_ss][] >>
    rw[EQ_IMP_THM] >>
    map_every qexists_tac[`mb`,`mty`,`mtyb`,`tyb`] >>
    rw[] >>
    first_x_assum(qspec_then`x`mp_tac) >> rw[] >>
    qmatch_abbrev_tac`semantics (z::ρa) σ τ t y` >>
    qmatch_assum_abbrev_tac`semantics (z::ρb) σ τ t y` >>
    (qsuff_tac`semantics (z::ρa) σ τ t = semantics (z::ρb) σ τ t` >- metis_tac[]) >>
    (first_x_assum (match_mp_tac o MP_CANON) ORELSE
     (match_mp_tac EQ_SYM >> first_x_assum (match_mp_tac o MP_CANON))) >>
    Cases >> rw[] >>
    res_tac >> fs[] ))

val semantics_frees = store_thm("semantics_frees",
  ``∀t ρ1 ρ2 σ1 σ2 τ.
      type_valuation τ ∧
      (∀x ty. MEM (x,ty) (dbfv t) ⇒ (FLOOKUP σ1 (x,ty) = FLOOKUP σ2 (x,ty))) ∧
      (∀n ty. MEM (n,ty) (dbbv t) ⇒ (n < LENGTH ρ1 ⇔ n < LENGTH ρ2) ∧ (n < LENGTH ρ1 ⇒ EL n ρ1 = EL n ρ2))
    ⇒ semantics ρ1 σ1 τ t = semantics ρ2 σ2 τ t``,
  metis_tac[semantics_bvs,semantics_fvs])

val closes_def = Define`
  closes env (σ:string#type|->V) (τ:string|->V) t ⇔
    set (dbtvars t) ⊆ FDOM τ ∧
    set (FLAT (MAP tyvars env)) ⊆ FDOM τ ∧
    set (dbfv t) ⊆ FDOM σ ∧
    good_bvs env t`

val semantics_closes = prove(
  ``(∀τ ty m. typeset τ ty m ⇒ T) ∧
    (∀env σ τ t m. semantics env σ τ t m ⇒ type_valuation τ ∧ term_valuation τ σ ∧ good_env τ env ⇒ closes (MAP FST env) σ τ t)``,
  ho_match_mp_tac(theorem"semantics_strongind") >> simp[] >>
  conj_tac >- (
    simp[Once semantics_cases,FLOOKUP_DEF,closes_def] >>
    simp[term_valuation_def,FEVERY_DEF,FORALL_PROD] >>
    rw[] >- metis_tac[typeset_closes_over] >>
    fs[good_env_def,SUBSET_DEF,MEM_FLAT,MEM_MAP,EXISTS_PROD,EVERY_MEM,FORALL_PROD] >>
    rw[] >- metis_tac[typeset_closes_over,SUBSET_DEF] >>
    rw[Once good_bvs_cases]) >>
  conj_tac >- (
    simp[Once semantics_cases,FLOOKUP_DEF,closes_def] >>
    rw[good_env_def,EVERY_MEM,SUBSET_DEF,MEM_FLAT,MEM_MAP,EXISTS_PROD,FORALL_PROD,EL_MAP] >>
    rw[Once good_bvs_cases,EL_MAP] >>
    metis_tac[typeset_closes_over,SUBSET_DEF,MEM_EL]) >>
  conj_tac >- (
    rw[closes_def,tyvars_def,good_env_def] >>
    fs[EVERY_MEM,SUBSET_DEF,MEM_FLAT,MEM_MAP,EXISTS_PROD,FORALL_PROD] >>
    metis_tac[typeset_closes_over,SUBSET_DEF] ) >>
  conj_tac >- (
    rw[closes_def,tyvars_def,good_env_def] >>
    fs[EVERY_MEM,SUBSET_DEF,MEM_FLAT,MEM_MAP,EXISTS_PROD,FORALL_PROD] >>
    metis_tac[typeset_closes_over,SUBSET_DEF] ) >>
  conj_tac >- (
    rw[closes_def] >- (
      fs[tyvars_tyinst,SUBSET_DEF] >>
      qspecl_then[`dbterm [] t`,`tyin`]strip_assume_tac dbtvars_dbinst >>
      rfs[EXTENSION] >>
      fs[dbtvars_dbterm] >>
      imp_res_tac WELLTYPED >>
      imp_res_tac dbhas_type_dbterm >>
      first_x_assum(qspec_then`[]`strip_assume_tac) >> fs[] >>
      imp_res_tac dbhas_type_11 >> rw[] >>
      imp_res_tac tyvars_typeof_subset_tvars >>
      fs[SUBSET_DEF] >>
      metis_tac[] ) >>
    fs[good_env_def,EVERY_MEM,SUBSET_DEF,MEM_FLAT,MEM_MAP,EXISTS_PROD,FORALL_PROD] >>
    metis_tac[typeset_closes_over,SUBSET_DEF] ) >>
  conj_tac >- (
    rw[closes_def,tyvars_def] >>
    TRY (metis_tac[typeset_closes_over,FDOM_FEMPTY,SUBSET_EMPTY,EMPTY_SUBSET]) >- (
      fs[SUBSET_DEF,MEM_FOLDR_LIST_UNION] >>
      qpat_assum`typeset τ (X Y) Z`mp_tac >>
      simp[Once semantics_cases] >> rw[] >>
      qmatch_assum_abbrev_tac`dbhas_type (dbinst tyin (dbterm [] p)) pty` >>
      imp_res_tac typeset_closes_over >> fs[] >>
      qspecl_then[`rty`,`tyin`]strip_assume_tac tyvars_tyinst >>
      rfs[EXTENSION] >>
      fs[Abbr`tyin`,FLOOKUPD_def] >>
      `∃n. y = EL n args ∧ n < LENGTH args` by metis_tac[MEM_EL] >>
      first_x_assum(qspecl_then[`x`,`EL n (tvars p)`]mp_tac) >>
      BasicProvers.CASE_TAC >- (
        fs[ALOOKUP_FAILS] >> rfs[MEM_ZIP] >> metis_tac[] ) >>
      qspec_then`p`strip_assume_tac tvars_ALL_DISTINCT >>
      qmatch_assum_abbrev_tac`ALOOKUP ls a = SOME z` >>
      Q.ISPECL_THEN[`ls`,`n`]strip_assume_tac ALOOKUP_ALL_DISTINCT_EL >>
      rfs[MAP_ZIP,Abbr`ls`,EL_ZIP] >> rpt BasicProvers.VAR_EQ_TAC >> simp[] >>
      qmatch_assum_abbrev_tac`dbhas_type (dbinst tyin (dbterm [] p)) pty` >>
      qspecl_then[`dbterm [] p`,`tyin`]strip_assume_tac dbtvars_dbinst >>
      rfs[EXTENSION] >>
      fs[dbtvars_dbterm] >> rw[] >>
      first_x_assum(qspecl_then[`x`,`a`]mp_tac) >>
      simp[Abbr`a`] >> rw[] >- metis_tac[MEM_EL] >>
      pop_assum mp_tac >>
      simp[FLOOKUPD_def,Abbr`tyin`]) >>
    fs[good_env_def,EVERY_MEM,SUBSET_DEF,MEM_FLAT,MEM_MAP,EXISTS_PROD,FORALL_PROD] >>
    metis_tac[typeset_closes_over,SUBSET_DEF] ) >>
  conj_tac >- (
    rw[closes_def,tyvars_def] >>
    TRY (metis_tac[typeset_closes_over,FDOM_FEMPTY,SUBSET_EMPTY,EMPTY_SUBSET]) >- (
      fs[SUBSET_DEF,MEM_FOLDR_LIST_UNION] >>
      qpat_assum`typeset τ (X Y) Z`mp_tac >>
      simp[Once semantics_cases] >> rw[] >>
      qmatch_assum_abbrev_tac`dbhas_type (dbinst tyin (dbterm [] p)) pty` >>
      imp_res_tac typeset_closes_over >> fs[] >>
      qspecl_then[`rty`,`tyin`]strip_assume_tac tyvars_tyinst >>
      rfs[EXTENSION] >>
      fs[Abbr`tyin`,FLOOKUPD_def] >>
      `∃n. y = EL n args ∧ n < LENGTH args` by metis_tac[MEM_EL] >>
      first_x_assum(qspecl_then[`x`,`EL n (tvars p)`]mp_tac) >>
      BasicProvers.CASE_TAC >- (
        fs[ALOOKUP_FAILS] >> rfs[MEM_ZIP] >> metis_tac[] ) >>
      qspec_then`p`strip_assume_tac tvars_ALL_DISTINCT >>
      qmatch_assum_abbrev_tac`ALOOKUP ls a = SOME z` >>
      Q.ISPECL_THEN[`ls`,`n`]strip_assume_tac ALOOKUP_ALL_DISTINCT_EL >>
      rfs[MAP_ZIP,Abbr`ls`,EL_ZIP] >> rpt BasicProvers.VAR_EQ_TAC >> simp[] >>
      qmatch_assum_abbrev_tac`dbhas_type (dbinst tyin (dbterm [] p)) pty` >>
      qspecl_then[`dbterm [] p`,`tyin`]strip_assume_tac dbtvars_dbinst >>
      rfs[EXTENSION] >>
      fs[dbtvars_dbterm] >> rw[] >>
      first_x_assum(qspecl_then[`x`,`a`]mp_tac) >>
      simp[Abbr`a`] >> rw[] >- metis_tac[MEM_EL] >>
      pop_assum mp_tac >>
      simp[FLOOKUPD_def,Abbr`tyin`]) >>
    fs[good_env_def,EVERY_MEM,SUBSET_DEF,MEM_FLAT,MEM_MAP,EXISTS_PROD,FORALL_PROD] >>
    metis_tac[typeset_closes_over,SUBSET_DEF] ) >>
  conj_tac >- (
    rw[closes_def] >> fs[] >> metis_tac[] ) >>
  (
    fs[closes_def] >>
    rpt gen_tac >> strip_tac >> strip_tac >>
    simp[GSYM CONJ_ASSOC] >>
    conj_tac >- metis_tac[typeset_closes_over] >> fs[] >>
    qmatch_assum_rename_tac`dbhas_type t tty`[] >>
    qmatch_assum_rename_tac`typeset τ tty mtty`[] >>
    qmatch_assum_rename_tac`typeset τ ty mty`[] >>
    `∃m. m <: mty` by metis_tac[typeset_inhabited] >>
    first_x_assum(qspec_then`m`mp_tac)>>simp[]>>strip_tac>>
    `good_env τ ((ty,m)::env)` by (
      pop_assum kall_tac >>
      fs[good_env_def,EVERY_MEM,SUBSET_DEF,MEM_FLAT,MEM_MAP,EXISTS_PROD,FORALL_PROD] >>
      metis_tac[] ) >>
    fs[] >>
    rw[Once good_bvs_cases]))
val semantics_closes = save_thm("semantics_closes",MP_CANON (CONJUNCT2 semantics_closes))

val good_bvs_extend = store_thm("good_bvs_extend",
  ``∀env t. good_bvs env t ⇒ ∀env'. good_bvs (env++env') t``,
  ho_match_mp_tac good_bvs_ind >>
  rw[] >> rw[Once good_bvs_cases] >>
  simp[rich_listTheory.EL_APPEND1])

val closes_extend = store_thm("closes_extend",
  ``∀env σ τ t env' σ' τ'. closes env σ τ t ∧ σ ⊑ σ' ∧ env ≼ env' ∧ τ ⊑ τ' ∧ set(FLAT(MAP tyvars env')) ⊆ FDOM τ' ⇒ closes env' σ' τ' t``,
  rw[SUBMAP_DEF,closes_def,SUBSET_DEF] >>
  imp_res_tac rich_listTheory.IS_PREFIX_LENGTH >>
  fs[rich_listTheory.IS_PREFIX_APPEND] >> rw[] >>
  fs[good_bvs_extend] >> res_tac >> simp[] )

val dbeq_def = Define`
  dbeq ty s t = dbComb (dbComb (dbConst "=" (Fun ty (Fun ty Bool)) Prim) s) t`

val equation_dbeq = store_thm("equation_dbeq",
  ``∀s t env. dbterm env (s === t) = dbeq (typeof s) (dbterm env s) (dbterm env t)``,
  rw[equation_def,dbeq_def])

val tac =
  qho_match_abbrev_tac`apply (apply (abstract a b f) x) y = z` >>
  `apply (abstract a b f) x = f x` by (
    match_mp_tac APPLY_ABSTRACT >>
    unabbrev_all_tac >> simp[] >>
    TRY(conj_tac >- metis_tac[semantics_typeset,semantics_11,dbhas_type_11]) >>
    match_mp_tac ABSTRACT_IN_FUNSPACE >>
    metis_tac[semantics_typeset,WELLTYPED,BOOLEAN_IN_BOOLSET] ) >>
  simp[Abbr`f`,Abbr`b`] >>
  qho_match_abbrev_tac`apply (abstract a b f) y = z` >>
  `apply (abstract a b f) y = f y `  by (
    match_mp_tac APPLY_ABSTRACT >>
    unabbrev_all_tac >> simp[] >>
    metis_tac[semantics_typeset,semantics_11,dbhas_type_11,BOOLEAN_IN_BOOLSET] ) >>
  unabbrev_all_tac >> simp[]

val semantics_equation = store_thm("semantics_equation",
  ``∀env σ τ s t ty mty ms mt mst.
    type_valuation τ ∧ term_valuation τ σ ∧ good_env τ env ∧
    semantics env σ τ s ms ∧ semantics env σ τ t mt ∧
    dbhas_type s ty ∧
    dbhas_type t ty ∧
    boolean (ms = mt) = mst
    ⇒ semantics env σ τ (dbeq ty s t) mst``,
  rw[dbeq_def] >>
  simp[Once semantics_cases] >>
  simp[Once semantics_cases] >>
  simp[Once semantics_cases] >>
  srw_tac[DNF_ss][dbwelltyped_def] >>
  simp[Once dbhas_type_cases] >>
  simp[Once dbhas_type_cases] >>
  simp[Once dbhas_type_cases] >>
  simp[Once dbhas_type_cases] >>
  simp[Once dbhas_type_cases] >>
  qspecl_then[`env`,`σ`,`τ`,`s`,`ms`]mp_tac(CONJUNCT2 semantics_typeset) >>
  qspecl_then[`env`,`σ`,`τ`,`t`,`mt`]mp_tac(CONJUNCT2 semantics_typeset) >>
  rw[] >>
  imp_res_tac dbhas_type_11 >> rw[] >>
  imp_res_tac semantics_11 >> rw[] >>
  map_every qexists_tac[`mt`,`ms`,`mty`] >> simp[] >>
  match_mp_tac EQ_SYM >> tac)

val semantics_equation_imp = store_thm("semantics_equation_imp",
  ``∀env σ τ s t ty mst.
    type_valuation τ ∧ term_valuation τ σ ∧ good_env τ env ∧
    semantics env σ τ (dbeq ty s t) mst ⇒
    ∃ms mt.
    semantics env σ τ s ms ∧ semantics env σ τ t mt ∧
    dbhas_type s ty ∧
    dbhas_type t ty ∧
    boolean (ms = mt) = mst``,
  rw[dbeq_def] >>
  fs[Q.SPECL[`env`,`σ`,`τ`,`dbComb X Y`](CONJUNCT2 semantics_cases)] >>
  fs[Q.SPECL[`env`,`σ`,`τ`,`dbConst X Y Z`](CONJUNCT2 semantics_cases)] >>
  fs[dbwelltyped_def] >>
  fs[Q.SPECL[`dbComb Y Z`]dbhas_type_cases] >>
  fs[Q.SPECL[`dbConst Y Z A`]dbhas_type_cases] >>
  qmatch_assum_rename_tac`semantics env σ τ s ms`[] >> rw[] >>
  qmatch_assum_rename_tac`semantics env σ τ t mt`[] >>
  map_every qexists_tac[`ms`,`mt`] >> rw[] >>
  match_mp_tac EQ_SYM >> tac)

val term_valuation_reduce = store_thm("term_valuation_reduce",
  ``∀τ σ σ'. term_valuation τ σ' ∧ σ ⊑ σ' ⇒ term_valuation τ σ``,
  metis_tac[term_valuation_def,FEVERY_SUBMAP])

val semantics_extend = store_thm("semantics_extend",
  ``∀ρ σ τ t m ρ' σ'. type_valuation τ ∧ term_valuation τ σ' ∧ good_env τ ρ ∧
                 semantics ρ σ τ t m ∧ σ ⊑ σ' ∧ ρ ≼ ρ'
                 ⇒ semantics ρ' σ' τ t m``,
  rw[] >>
  imp_res_tac term_valuation_reduce >>
  `closes (MAP FST ρ) σ τ t` by metis_tac[semantics_closes] >>
  qsuff_tac`semantics ρ' σ' τ t = semantics ρ σ τ t`>-rw[] >>
  match_mp_tac semantics_frees >>
  fs[closes_def,SUBSET_DEF,SUBMAP_DEF,FLOOKUP_DEF,rich_listTheory.IS_PREFIX_APPEND] >>
  imp_res_tac good_bvs_dbbv >> fs[] >>
  rw[] >> res_tac >> fs[] >> simp[] >>
  simp[rich_listTheory.EL_APPEND1])

val semantics_reduce = store_thm("semantics_reduce",
  ``∀ρ σ τ t m ρ' σ'. type_valuation τ ∧ term_valuation τ σ' ∧
                 semantics ρ' σ' τ t m ∧ σ ⊑ σ' ∧ ρ ≼ ρ' ∧
                 closes (MAP FST ρ) σ τ t
                 ⇒ semantics ρ σ τ t m``,
  rw[] >>
  imp_res_tac term_valuation_reduce >>
  qsuff_tac`semantics ρ σ τ t = semantics ρ' σ' τ t`>-rw[] >>
  match_mp_tac semantics_frees >> simp[] >>
  fs[closes_def,SUBSET_DEF,FORALL_PROD,FLOOKUP_DEF,SUBMAP_DEF,rich_listTheory.IS_PREFIX_APPEND] >>
  imp_res_tac good_bvs_dbbv >> rw[] >> res_tac >> fs[] >> rw[] >>
  simp[rich_listTheory.EL_APPEND1])

val typeset_extend = store_thm("typeset_extend",
  ``∀τ ty mty τ'. typeset τ ty mty ∧ τ ⊑ τ' ⇒ typeset τ' ty mty``,
  rw[] >>
  match_mp_tac typeset_tyvars >>
  qexists_tac`τ` >>
  fs[SUBMAP_DEF,FLOOKUP_DEF] >>
  imp_res_tac typeset_closes_over >>
  fs[SUBSET_DEF])

val typeset_reduce = store_thm("typeset_reduce",
  ``∀τ ty mty τ'. typeset τ' ty mty ∧ set (tyvars ty) ⊆ FDOM τ ∧ τ ⊑ τ' ⇒ typeset τ ty mty``,
  rw[] >>
  match_mp_tac typeset_tyvars >>
  qexists_tac`τ'` >>
  fs[SUBMAP_DEF,FLOOKUP_DEF,SUBSET_DEF])

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

val type_has_meaning_def = Define`
  type_has_meaning ty ⇔ ∀τ. type_valuation τ ∧ set (tyvars ty) ⊆ FDOM τ ⇒ ∃m. typeset τ ty m`

val type_has_meaning_Bool = store_thm("type_has_meaning_Bool",
  ``type_has_meaning Bool``,
  rw[type_has_meaning_def])
val _ = export_rewrites["type_has_meaning_Bool"]

val type_has_meaning_Fun = store_thm("type_has_meaning_Fun",
  ``∀dty rty. type_has_meaning (Fun dty rty) ⇔ type_has_meaning dty ∧ type_has_meaning rty``,
  rw[type_has_meaning_def,tyvars_def] >>
  rw[Once semantics_cases] >>
  metis_tac[covering_type_valuation_exists,typeset_reduce,SUBMAP_DEF,SUBSET_DEF,FINITE_LIST_TO_SET])
val _ = export_rewrites["type_has_meaning_Fun"]

val typeset_has_meaning = prove(
  ``(∀τ ty m. typeset τ ty m ⇒ type_has_meaning ty) ∧
    (∀env σ τ t m. semantics env σ τ t m ⇒ T)``,
  ho_match_mp_tac (theorem"semantics_strongind") >> simp[] >>
  conj_tac >- (
    simp[type_has_meaning_def,tyvars_def] >>
    simp[Once semantics_cases,FLOOKUP_DEF] ) >>
  rw[type_has_meaning_def,tyvars_def] >>
  simp[Once semantics_cases] >>
  metis_tac[])
val typeset_has_meaning = save_thm("typeset_has_meaning",CONJUNCT1 typeset_has_meaning)

val has_meaning_def = Define`
  has_meaning t ⇔
    (∃ρ τ σ. type_valuation τ ∧ term_valuation τ σ ∧ good_env τ ρ ∧ closes (MAP FST ρ) σ τ t) ∧
    ∀τ σ env. type_valuation τ ∧
              term_valuation τ σ ∧
              good_env τ env ∧
              closes (MAP FST env) σ τ t
            ⇒ ∃m. semantics env σ τ t m`

val closes_dbComb = store_thm("closes_dbComb",
  ``∀env σ τ t1 t2. closes env σ τ (dbComb t1 t2) ⇔ closes env σ τ t1 ∧ closes env σ τ t2``,
  rw[closes_def] >> metis_tac[])
val _ = export_rewrites["closes_dbComb"]

val closes_dbAbs = store_thm("closes_dbAbs",
  ``∀env σ τ ty tm. closes env σ τ (dbAbs ty tm) ⇔ set (tyvars ty) ⊆ FDOM τ ∧ closes (ty::env) σ τ tm``,
  rw[closes_def,SUBSET_DEF,MEM_MAP,MEM_FILTER,GSYM LEFT_FORALL_IMP_THM,FORALL_PROD,EXISTS_PROD] >>
  rw[EQ_IMP_THM] >> res_tac >> rw[] >> fsrw_tac[ARITH_ss][rich_listTheory.EL_CONS] >- (
    pop_assum mp_tac >> rw[Once good_bvs_cases] ) >>
  rw[Once good_bvs_cases])
val _ = export_rewrites["closes_dbAbs"]

val closes_dbConst = store_thm("closes_dbConst",
  ``∀env σ τ s ty c. closes env σ τ (dbConst s ty c) ⇔ set (tyvars ty) ⊆ FDOM τ ∧ set (FLAT (MAP tyvars env)) ⊆ FDOM τ``,
  rw[closes_def] >> rw[Once good_bvs_cases])
val _ = export_rewrites["closes_dbConst"]

val closes_dbFree = store_thm("closes_dbFree",
  ``∀env σ τ s ty. closes env σ τ (dbFree s ty) ⇔ set (tyvars ty) ⊆ FDOM τ ∧ set (FLAT (MAP tyvars env)) ⊆ FDOM τ ∧ (s,ty) ∈ FDOM σ``,
  rw[closes_def,Once good_bvs_cases])
val _ = export_rewrites["closes_dbFree"]

val closes_dbVar = store_thm("closes_dbVar",
  ``∀env σ τ n ty. closes env σ τ (dbVar n ty) ⇔ set (tyvars ty) ⊆ FDOM τ ∧ set (FLAT (MAP tyvars env)) ⊆ FDOM τ ∧ n < LENGTH env ∧ EL n env = ty``,
  rw[closes_def,Once good_bvs_cases] >> metis_tac[])
val _ = export_rewrites["closes_dbVar"]

val closes_dbeq = store_thm("closes_dbeq",
  ``(dbhas_type l ty) ∧ (dbhas_type r ty)	⇒
  (closes env σ τ (dbeq ty l r) ⇔ closes env σ τ l ∧ closes env σ τ r)``,
  rw[closes_def,dbeq_def,tyvars_def] >> rw[EQ_IMP_THM] >>
  imp_res_tac tyvars_subset_dbtvars >>
  fs[SUBSET_DEF] >> metis_tac[MAP_MAP_o] )

val covering_sigma_exists = store_thm("covering_sigma_exists",
  ``∀τ σ t. ∃σ'. σ ⊑ σ' ∧ set (dbfv t) ⊆ FDOM σ' ∧
      (type_valuation τ ∧ term_valuation τ σ ∧ (∀p. MEM p (dbfv t) ⇒ ∃mty. typeset τ (SND p) mty) ⇒ term_valuation τ σ')``,
  qsuff_tac`∀s:(string#type) set. FINITE s ⇒
    ∀τ σ. ∃σ'. σ ⊑ σ' ∧ s ⊆ FDOM σ' ∧ (type_valuation τ ∧ term_valuation τ σ ∧ (∀p. p ∈ s ⇒ ∃mty. typeset τ (SND p) mty)⇒ term_valuation τ σ')`
    >- metis_tac[FINITE_LIST_TO_SET] >>
  ho_match_mp_tac FINITE_INDUCT >>
  rw[] >- metis_tac[SUBMAP_REFL] >>
  first_x_assum(qspecl_then[`τ`,`σ`]strip_assume_tac) >>
  Cases_on`e ∈ FDOM σ'` >- metis_tac[] >>
  reverse(Cases_on`term_valuation τ σ`) >> fs[] >- (
    qexists_tac`σ' |+ (e,ARB)` >>
    rw[] >> fs[SUBMAP_DEF,FAPPLY_FUPDATE_THM] >> rw[] >>
    metis_tac[] ) >>
  qexists_tac`σ' |+ (e,@m. ∃mty. typeset τ (SND e) mty ∧ m <: mty)` >>
  simp[] >>
  fs[SUBMAP_DEF,FAPPLY_FUPDATE_THM] >>
  conj_tac >- (rw[] >> metis_tac[]) >> rw[] >>
  match_mp_tac term_valuation_FUPDATE >> rw[] >>
  first_x_assum(qspec_then`e`strip_assume_tac) >> fs[] >>
  qexists_tac`mty` >> rw[] >>
  SELECT_ELIM_TAC >>
  metis_tac[typeset_inhabited,semantics_11])

val covering_env_exists = store_thm("covering_env_exists",
  ``∀s. FINITE s ⇒
      (∀n ty1 ty2. (n,ty1) ∈ s ∧ (n,ty2) ∈ s ⇒ ty1 = ty2) ⇒
      ∀τ env.
        type_valuation τ ∧ good_env τ env ∧
        (∀n ty. (n,ty) ∈ s ⇒ ∃mty. typeset τ ty mty) ∧
        (∀n ty. (n,ty) ∈ s ∧ n < LENGTH env ⇒ FST (EL n env) = ty) ⇒
        ∃env'.
          env ≼ env' ∧
          (∀n ty. (n,ty) ∈ s ⇒ n < LENGTH env' ∧ FST (EL n env') = ty) ∧
          good_env τ env'``,
  rw[] >>
  qexists_tac`env ++ GENLIST (λi. case some ty. (LENGTH env + i,ty) ∈ s of
                                       SOME ty => (ty, @m. ∃mty. typeset τ ty mty ∧ m <: mty)
                                       | NONE => (Bool,boolean F))
                             (LEAST m. ∀n ty. (n,ty) ∈ s ⇒ n < m)` >>
  numLib.LEAST_ELIM_TAC >>
  conj_tac >- (
    qpat_assum`FINITE s`mp_tac >>
    rpt(pop_assum kall_tac) >>
    qid_spec_tac`s` >>
    ho_match_mp_tac FINITE_INDUCT >>
    rw[] >>
    qexists_tac`if FST e < n then n else SUC (FST e)` >>
    rw[] >> fs[] >> simp[] >>
    res_tac >> simp[] ) >>
  simp[] >>
  gen_tac >> strip_tac >>
  conj_tac >- (
    rw[] >> res_tac >> simp[] >>
    Cases_on`n' < LENGTH env`>>simp[rich_listTheory.EL_APPEND1,rich_listTheory.EL_APPEND2] >>
    qho_match_abbrev_tac`D (option_CASE ($some P) A B) = ty` >>
    qho_match_abbrev_tac`Q ($some P)` >>
    map_every qunabbrev_tac[`D`,`B`,`A`] >>
    match_mp_tac optionTheory.some_intro >>
    simp[Abbr`P`,Abbr`Q`] >> rw[] >>
    metis_tac[] ) >>
  fs[good_env_def] >>
  simp[EVERY_GENLIST,UNCURRY] >>
  rw[] >>
  qho_match_abbrev_tac`∃mty. typeset τ (FST p) mty ∧ (SND p) <: mty` >>
  qho_match_abbrev_tac`B p` >>
  qunabbrev_tac`p` >>
  qho_match_abbrev_tac`B (option_CASE ($some P) X Y)` >>
  qho_match_abbrev_tac`Q ($some P)` >>
  map_every qunabbrev_tac[`B`,`X`,`Y`] >>
  match_mp_tac optionTheory.some_intro >>
  simp[Abbr`P`,Abbr`Q`] >> rw[BOOLEAN_IN_BOOLSET] >>
  res_tac >>
  qexists_tac`mty` >> rw[] >>
  SELECT_ELIM_TAC >>
  metis_tac[typeset_inhabited,semantics_11])

val closing_envs_exist = store_thm("closing_envs_exist",
  ``∀env σ τ tm. (∃ρ. good_bvs ρ tm) ∧ type_valuation τ ∧ term_valuation τ σ ∧ good_env τ env  ∧
                 (∀n ty. MEM (n,ty) (dbbv tm) ∧ n < LENGTH env ⇒ FST (EL n env) = ty) ∧
                 (∀n ty1 ty2. MEM (n,ty1) (dbbv tm) ∧ MEM (n,ty2) (dbbv tm) ⇒ ty1 = ty2) ∧
                 (∀x n ty. MEM (x,ty) (dbfv tm) ∨ (x,ty) ∈ FDOM σ ∨ MEM (n,ty) (dbbv tm) ⇒ ∃mty. typeset τ ty mty)
                 ⇒
      ∃env' σ' τ'.
        env ≼ env' ∧ σ ⊑ σ' ∧ τ ⊑ τ' ∧ closes (MAP FST env') σ' τ' tm ∧
        type_valuation τ' ∧ term_valuation τ' σ' ∧ good_env τ' env'``,
  rw[closes_def] >>
  qspec_then`set (dbbv tm)`mp_tac covering_env_exists >>
  simp[] >>
  discharge_hyps >- metis_tac[] >>
  disch_then(qspecl_then[`τ`,`env`]mp_tac) >>
  simp[] >>
  discharge_hyps >- metis_tac[] >>
  strip_tac >>
  qexists_tac`env'` >>
  Q.ISPEC_THEN`set (dbtvars tm) ∪ set (FLAT (MAP tyvars (MAP FST env')))`mp_tac covering_type_valuation_exists >>
  simp[] >>
  disch_then(qspec_then`τ`mp_tac) >>
  disch_then(qx_choose_then`τ'`strip_assume_tac) >>
  qspecl_then[`τ'`,`σ`,`tm`]mp_tac covering_sigma_exists >>
  rfs[] >>
  strip_tac >>
  qexists_tac`σ'` >>
  qexists_tac`τ'` >>
  simp[] >>
  conj_tac >- (
    match_mp_tac dbbv_good_bvs >>
    conj_tac >- metis_tac[] >>
    metis_tac[EL_MAP,LENGTH_MAP] ) >>
  conj_tac >- (
    first_x_assum match_mp_tac >>
    conj_tac >- (
      fs[term_valuation_def,FEVERY_DEF] >>
      rw[] >> res_tac >>
      qexists_tac`mty` >> simp[] >>
      match_mp_tac typeset_tyvars >>
      qexists_tac`τ` >> simp[] >>
      imp_res_tac(CONJUNCT1 typeset_closes_over) >>
      fs[SUBSET_DEF,FLOOKUP_DEF,SUBMAP_DEF] ) >>
    rw[] >>
    `∃mty. typeset τ (SND p) mty` by metis_tac[pair_CASES,SND] >>
    qexists_tac`mty` >> simp[] >>
    match_mp_tac typeset_tyvars >>
    qexists_tac`τ` >> simp[] >>
    imp_res_tac(CONJUNCT1 typeset_closes_over) >>
    fs[SUBSET_DEF,FLOOKUP_DEF,SUBMAP_DEF] ) >>
  fs[good_env_def,EVERY_MEM] >>
  rw[] >> res_tac >>
  fs[UNCURRY] >>
  qexists_tac`mty` >> simp[] >>
  match_mp_tac typeset_tyvars >>
  qexists_tac`τ` >> simp[] >>
  imp_res_tac(CONJUNCT1 typeset_closes_over) >>
  fs[SUBSET_DEF,FLOOKUP_DEF,SUBMAP_DEF] )

(*
not true: the env can vary on the prefix of bvs that don't occur
val good_bvs_prefix = store_thm("good_bvs_prefix",
  ``∀env tm. good_bvs env tm ⇒ ∃env0. good_bvs env0 tm ∧ ∀env'. good_bvs env' tm ⇒ env0 ≼ env'``,
  ho_match_mp_tac good_bvs_ind >> simp[] >>
  conj_tac >- (
    simp[Once good_bvs_cases] >>
    simp[Once good_bvs_cases] >>
    qexists_tac`[]` >> simp[] ) >>
  conj_tac >- (
    simp[Once good_bvs_cases] >>
    simp[Once good_bvs_cases] >>
    rw[]
    simp[SKOLEM_THM]
*)

val has_meaning_welltyped = store_thm("has_meaning_welltyped",
  ``∀t. has_meaning t ⇒ dbwelltyped t``,
  rw[has_meaning_def,dbwelltyped_def] >> metis_tac[semantics_typeset] )

val has_meaning_dbFree = store_thm("has_meaning_dbFree",
  ``∀x ty. has_meaning (dbFree x ty) ⇔ type_has_meaning ty``,
  rw[type_has_meaning_def,has_meaning_def] >>
  simp[Once semantics_cases,FLOOKUP_DEF] >>
  rw[EQ_IMP_THM] >- (
    fs[term_valuation_def,FEVERY_DEF] >> res_tac >> fs[] >>
    match_mp_tac typeset_tyvars_typeset_exists >>
    fs[SUBSET_DEF] >> metis_tac[] ) >>
  Q.ISPEC_THEN`set (tyvars ty)`mp_tac covering_type_valuation_exists >> rw[] >>
  pop_assum(qspec_then`FEMPTY`mp_tac) >> rw[] >>
  `∃mty. typeset τ' ty mty` by metis_tac[] >>
  `∃z. z <: mty` by metis_tac[typeset_inhabited] >>
  map_every qexists_tac[`[]`,`τ'`,`FEMPTY|+((x,ty),z)`] >>
  rw[] >>
  match_mp_tac term_valuation_FUPDATE >>
  rw[] >> metis_tac[])

val has_meaning_dbVar = store_thm("has_meaning_dbVar",
  ``∀x ty. has_meaning (dbVar x ty) ⇔ type_has_meaning ty``,
  rw[type_has_meaning_def,has_meaning_def] >>
  simp[Once semantics_cases,FLOOKUP_DEF] >>
  rw[EQ_IMP_THM] >- (
    fs[good_env_def,EVERY_DEF,EVERY_MEM] >>
    first_x_assum(qspec_then`EL x ρ`mp_tac) >>
    discharge_hyps >- metis_tac[MEM_EL] >>
    Cases_on`EL x ρ` >> fs[EL_MAP] >> rw[] >>
    match_mp_tac typeset_tyvars_typeset_exists >>
    rfs[EL_MAP] >> fs[] >>
    fs[SUBSET_DEF] >> metis_tac[] ) >>
  TRY (
    rw[EL_MAP] >>
    metis_tac[FST,SND,pair_CASES,PAIR_EQ] ) >>
  Q.ISPEC_THEN`set (tyvars ty)`mp_tac covering_type_valuation_exists >> rw[] >>
  pop_assum(qspec_then`FEMPTY`mp_tac) >> rw[] >>
  `∃mty. typeset τ' ty mty` by metis_tac[] >>
  `∃z. z <: mty` by metis_tac[typeset_inhabited] >>
  map_every qexists_tac[`REPLICATE (SUC x) (ty,z)`,`τ'`,`FEMPTY`] >>
  rw[good_env_def,rich_listTheory.LENGTH_REPLICATE] >>
  Q.ISPECL_THEN[`ty,z`,`SUC x`]mp_tac rich_listTheory.EVERY_REPLICATE >>
  rw[EVERY_MEM,UNCURRY] >>
  rw[EL_MAP,rich_listTheory.LENGTH_REPLICATE] >>
  rw[SUBSET_DEF,MEM_FLAT,MEM_MAP] >>
  res_tac >> rw[] >> fs[] >> fs[SUBSET_DEF] >> TRY(metis_tac[]) >>
  fs[MEM_EL] >>
  metis_tac[FST,rich_listTheory.LENGTH_REPLICATE,prim_recTheory.LESS_SUC_REFL])

(*
not true?
e.g. s = (dbVar 0 bool) and t = (dbVar 0 ind)
*)
(*
val has_meaning_dbComb = store_thm("has_meaning_dbComb",
  ``∀s t. has_meaning (dbComb s t) ⇔ has_meaning s ∧ has_meaning t``,
  rw[] >> EQ_TAC >> strip_tac >- (
    imp_res_tac has_meaning_welltyped >>
    fs[has_meaning_def] >>
    fs[Once (Q.SPECL[`X`,`Y`,`Z`,`dbComb A B`](CONJUNCT2 semantics_cases))] >>
    simp[GSYM CONJ_ASSOC] >> conj_tac >- metis_tac[] >>
    simp[Once CONJ_SYM,GSYM CONJ_ASSOC] >>
    conj_tac >- metis_tac[] >>
    simp[GSYM FORALL_AND_THM,GSYM IMP_CONJ_THM,GSYM AND_IMP_INTRO] >>
    rpt gen_tac >> ntac 3 strip_tac >>
    `∀n ty1 ty2. MEM (n,ty1) (dbbv s ++ dbbv t) ∧
                 MEM (n,ty2) (dbbv s ++ dbbv t) ⇒ ty1 = ty2` by (
      fs[closes_def] >>
      metis_tac[good_bvs_dbbv,EL_MAP] ) >>
    conj_tac >> strip_tac >|[
    (* need to replace elements of env that are in dbbv s but not dbbv t *)
    qspecl_then[`env`,`σ'`,`τ'`,`s`]mp_tac closing_envs_exist
    ,
    qspecl_then[`env`,`σ'`,`τ'`,`t`]mp_tac closing_envs_exist
    ] >>
    simp[] >>
    (discharge_hyps >- (
       fs[closes_def] >>
       conj_tac >- metis_tac[] >>
       conj_tac >- metis_tac[good_bvs_dbbv,EL_MAP] >>
       conj_tac >- metis_tac[good_bvs_dbbv,EL_MAP] >>
       fs[term_valuation_def,FEVERY_DEF,FORALL_PROD,SUBSET_DEF] >>
       fs[good_env_def,EVERY_MEM,FORALL_PROD] >>
       rw[] >- metis_tac[]
       >- metis_tac[] >>
       `∃x. MEM (ty,x) env` by (
         imp_res_tac good_bvs_dbbv >>
         rfs[EL_MAP] >>
         simp[MEM_EL] >>
         metis_tac[pair_CASES,PAIR_EQ,FST] ) >>
       metis_tac[] )) >>
    disch_then(qx_choosel_then[`env1`,`σ1`,`τ1`]strip_assume_tac) >>
    first_x_assum(qspecl_then[`τ1`,`σ1`,`env1`]mp_tac) >>
    simp[] >>
    `set (FLAT (MAP tyvars (MAP FST env1))) ⊆ FDOM τ1` by (
      fs[good_env_def,EVERY_MEM,SUBSET_DEF,FORALL_PROD,MEM_FLAT,MEM_MAP,EXISTS_PROD] >>
      rw[] >> res_tac >>
      imp_res_tac typeset_closes_over >>
      fs[SUBSET_DEF] ) >>
    discharge_hyps >- metis_tac[closes_extend]

    good_env_def

         imp_res_tac good_bvs_dbbv
         fs[
    first_x_assum(qspecl_then[`τ'`,`σ'`,`env`]

    first_x_assum(qspecl_then[`τ`,`σ`]mp_tac) >>
    simp[] >> strip_tac >>
    metis_tac[semantics_closes_over] ) >>
  fs[has_meaning_def] >> rpt gen_tac >> strip_tac >>
  last_x_assum(qspecl_then[`τ`,`σ`]mp_tac) >> simp[] >>
  disch_then(qx_choosel_then[`σ1`,`m1`]strip_assume_tac) >>
  last_x_assum(qspecl_then[`τ`,`σ1`]mp_tac) >> simp[] >>
  disch_then(qx_choosel_then[`σ2`,`m2`]strip_assume_tac) >>
  simp[Once semantics_cases] >>
  simp_tac(srw_ss()++DNF_ss)[] >>
  map_every qexists_tac[`σ2`,`m1`,`m2`] >>
  simp[] >>
  metis_tac[SUBMAP_TRANS,closes_over_extend,semantics_extend_term_valuation])
*)

(*
val has_meaning_Abs = store_thm("has_meaning_Abs",
  ``∀x ty t. has_meaning (Abs x ty t) ⇔ type_has_meaning ty ∧ has_meaning t``,
  rw[EQ_IMP_THM] >> fs[type_has_meaning_def,has_meaning_def] >>
  fs[Q.SPECL[`X`,`Y`,`Abs x ty t`](CONJUNCT2 semantics_cases)] >> rw[] >>
  (qmatch_assum_rename_tac`term_valuation τ σ`[] ORELSE
   (qabbrev_tac`σ:string#type|->V = FEMPTY` >>
    `term_valuation τ σ` by simp[Abbr`σ`]))
  >- (
    first_x_assum(qspecl_then[`τ`,`σ`]mp_tac) >> simp[] >>
    simp_tac(srw_ss()++DNF_ss)[] >>
    rpt gen_tac >> strip_tac >> metis_tac[] )
  >- (
    first_x_assum(qspecl_then[`τ`,`σ`]mp_tac) >> simp[] >>
    simp_tac(srw_ss()++DNF_ss)[] >>
    rpt gen_tac >> strip_tac >>
    Cases_on`(x,ty) ∈ FDOM σ'` >- (
      `σ' ' (x,ty) <: mty` by (
        fs[term_valuation_def,FEVERY_DEF] >>
        res_tac >> fs[] >>
        imp_res_tac semantics_11 >> fs[] ) >>
      `σ' |+ ((x,ty),σ' ' (x,ty)) = σ'` by (
        metis_tac[FUPDATE_ELIM] ) >>
      metis_tac[SUBMAP_REFL,semantics_closes_over] ) >>
    `∃z. z <: mty` by metis_tac[typeset_inhabited] >>
    map_every qexists_tac[`σ' |+ ((x,ty),z)`,`mb z`] >>
    conj_asm1_tac >- metis_tac[SUBMAP_FUPDATE_EQN,SUBMAP_TRANS] >>
    conj_tac >- (
      fs[term_valuation_def] >>
      match_mp_tac(CONJUNCT2 FEVERY_STRENGTHEN_THM) >>
      fs[] >> metis_tac[] ) >>
    metis_tac[semantics_closes_over] ) >>
  simp_tac(srw_ss()++DNF_ss)[] >>
  first_assum(qspecl_then[`τ`,`σ`]mp_tac) >>
  ntac 2 (pop_assum mp_tac) >> simp_tac std_ss [] >> ntac 2 strip_tac >>
  strip_tac >>
  qexists_tac`σ'` >> simp[] >>
  `∃mty. typeset τ ty mty` by metis_tac[] >>
  `∃tyb mtyb. t has_type tyb ∧ typeset τ tyb mtyb` by metis_tac[semantics_typeset,WELLTYPED] >>
  CONV_TAC (RESORT_EXISTS_CONV List.rev) >>
  map_every qexists_tac[`tyb`,`mtyb`,`mty`] >> simp[] >>
  simp[GSYM FORALL_AND_THM] >>
  simp[GSYM SKOLEM_THM] >>
  qx_gen_tac`z` >>
  simp[GSYM IMP_CONJ_THM] >>
  simp[RIGHT_EXISTS_IMP_THM] >>
  strip_tac >>
  first_x_assum(qspecl_then[`τ`,`σ' |+ ((x,ty),z)`]mp_tac) >>
  discharge_hyps >- metis_tac[term_valuation_FUPDATE,FST,SND] >>
  disch_then(qx_choosel_then[`σ''`,`y`] strip_assume_tac) >>
  qexists_tac`y` >>
  conj_tac >- metis_tac[semantics_typeset,WELLTYPED_LEMMA,semantics_11] >>
  match_mp_tac semantics_reduce_term_valuation >>
  HINT_EXISTS_TAC >> simp[])

val semantics_has_meaning = prove(
  ``(∀τ ty m. typeset τ ty m ⇒ T) ∧
    (∀env σ τ t m. semantics env σ τ t m ⇒ type_valuation τ ⇒ has_meaning t)``,
  ho_match_mp_tac (theorem"semantics_strongind") >> simp[] >>
  conj_tac >- (
    simp[has_meaning_def,Once semantics_cases] >> rw[FLOOKUP_DEF] ) >>
  conj_tac >- (
    rw[has_meaning_def,Once semantics_cases] >> rw[EL_MAP] >>
    metis_tac[PAIR_EQ,pair_CASES,FST,SND]) >>
  conj_tac >- (
    rw[has_meaning_def] >>
    rw[Once semantics_cases] >>
    imp_res_tac typeset_has_meaning >>
    fs[type_has_meaning_def,tyvars_def] ) >>
  conj_tac >- (
    rw[has_meaning_def] >>
    rw[Once semantics_cases] >>
    imp_res_tac typeset_has_meaning >>
    fs[type_has_meaning_def,tyvars_def] ) >>
  conj_tac >- (
    rw[has_meaning_def] >>
    rw[Once semantics_cases] >>
    metis_tac[] ) >>
  conj_tac >- (
    rw[has_meaning_def] >>
    rw[Once semantics_cases] >>
    CONV_TAC SWAP_EXISTS_CONV >>
    HINT_EXISTS_TAC >> rw[] >>
    imp_res_tac typeset_has_meaning >>
    fs[type_has_meaning_def] >>
    first_x_assum match_mp_tac >>
    fs[tyvars_def] ) >>
  conj_tac >- (
    rw[has_meaning_def] >>
    rw[Once semantics_cases] >>
    CONV_TAC (RESORT_EXISTS_CONV List.rev) >>
    HINT_EXISTS_TAC >>
    qexists_tac`m'` >> rw[] >>
    imp_res_tac typeset_has_meaning >>
    fs[type_has_meaning_def] >>
    first_x_assum match_mp_tac >>
    fs[tyvars_def] ) >>
  conj_tac >- (
    rw[has_meaning_def] >>
    simp[Once semantics_cases] >>
    metis_tac[] ) >>
  rw[has_meaning_def] >>
  rw[Once semantics_cases] >>
  imp_res_tac typeset_has_meaning >>
  fs[type_has_meaning_def] >>
  `∃m1. typeset τ' ty m1` by metis_tac[] >>
  `∃m2. typeset τ' ty' m2` by (
    first_x_assum match_mp_tac >> rw[] >>
    fs[closes_def] >>
    imp_res_tac tyvars_subset_dbtvars >>
    fs[SUBSET_DEF] ) >>
  CONV_TAC (RESORT_EXISTS_CONV List.rev) >>
  map_every qexists_tac[`ty'`,`m2`,`m1`] >> rw[] >>
  `∃z. z <: m` by metis_tac[typeset_inhabited] >>
  first_x_assum(qspec_then`z`mp_tac) >> rw[] >>
  rw[GSYM SKOLEM_THM] >>
  rw[RIGHT_EXISTS_IMP_THM] >>
  first_x_assum(qspecl_then[`τ'`,`σ'`,`(ty,x)::env'`]mp_tac) >>
  simp[] >>
  discharge_hyps_keep >- (
    fs[good_env_def] >>
    metis_tac[] ) >>
  strip_tac >>
  qexists_tac`m''` >> rw[] >>
  metis_tac[semantics_typeset,semantics_11,dbhas_type_11])
val semantics_has_meaning = save_thm("semantics_has_meaning",MP_CANON (CONJUNCT2 semantics_has_meaning))
*)

(*
val has_meaning_aconv = store_thm("has_meaning_aconv",
  ``∀t t'. has_meaning t ∧ ACONV t t' ⇒ has_meaning t'``,
  rw[] >>
  imp_res_tac has_meaning_welltyped >>
  fs[has_meaning_def] >> rw[] >>
  metis_tac[semantics_aconv,closes_over_aconv,ACONV_welltyped])
*)

(*
val equation_has_meaning = store_thm("equation_has_meaning",
  ``∀s t ty env. has_meaning s ∧ has_meaning t ∧ dbhas_type env s ty ∧ dbhas_type env t ty ⇒ has_meaning (dbeq ty s t)``,
  rw[has_meaning_def] >>
  first_x_assum(qspecl_then[`τ`,`σ`]mp_tac) >> simp[] >>
  disch_then(qx_choosel_then[`σ1`,`m1`]strip_assume_tac) >>
  first_x_assum(qspecl_then[`τ`,`σ1`]mp_tac) >> simp[] >>
  disch_then(qx_choosel_then[`σ2`,`m2`]strip_assume_tac) >>
  map_every qexists_tac[`σ2`,`boolean(m1=m2)`] >>
  conj_asm1_tac >- metis_tac[SUBMAP_TRANS] >>
  conj_asm1_tac >- metis_tac[term_valuation_reduce] >>
  simp[closes_over_equation] >>
  conj_tac >- metis_tac[closes_over_extend] >>
  match_mp_tac semantics_equation >> simp[] >>
  map_every qexists_tac[`m2`,`m1`] >> simp[boolean_def] >>
  metis_tac[semantics_extend_term_valuation])

val equation_has_meaning_iff = store_thm("equation_has_meaning_iff",
  ``∀s t. has_meaning (s === t) ⇔ has_meaning s ∧ has_meaning t ∧ typeof s = typeof t``,
  rw[] >> reverse EQ_TAC >- metis_tac[equation_has_meaning] >>
  simp[has_meaning_def] >> strip_tac >>
  simp[CONJ_ASSOC] >>
  simp[GSYM FORALL_AND_THM,GSYM IMP_CONJ_THM] >>
  reverse conj_tac >- (
    strip_assume_tac a_type_valuation_exists >>
    first_x_assum(qspecl_then[`τ`,`FEMPTY`]mp_tac) >>
    simp[SUBMAP_FEMPTY] >>
    disch_then(qx_choosel_then[`σ`,`me`]strip_assume_tac) >>
    `welltyped (s === t)` by metis_tac[semantics_typeset] >>
    fs[equation_def]) >>
  rpt gen_tac >> strip_tac >>
  first_x_assum(qspecl_then[`τ`,`σ`]mp_tac) >> simp[] >>
  strip_tac >> fs[closes_over_equation] >>
  pop_assum mp_tac >>
  simp[Once (CONJUNCT2 semantics_cases),equation_def] >>
  simp[Once (CONJUNCT2 semantics_cases)] >> rw[] >>
  metis_tac[])

val _ = Parse.add_infix("|=",450,Parse.NONASSOC)

val sequent_def = xDefine"sequent"`
  h |= c ⇔ EVERY (λt. t has_type Bool) (c::h) ∧
           EVERY has_meaning (c::h) ∧
           ∀σ τ. type_valuation τ ∧
                 term_valuation τ σ ∧
                 EVERY (λt. semantics σ τ t true) h ∧
                 σ closes_over c
                 ⇒
                 semantics σ τ c true`

val ASSUME_correct = store_thm("ASSUME_correct",
  ``∀p. has_meaning p ∧ p has_type Bool ⇒ [p] |= p``,
  rw[sequent_def])

val REFL_correct = store_thm("REFL_correct",
  ``∀t. has_meaning t ⇒ [] |= t === t``,
  rw[sequent_def,EQUATION_HAS_TYPE_BOOL,has_meaning_welltyped,equation_has_meaning] >>
  match_mp_tac semantics_equation >>
  fs[has_meaning_def,closes_over_equation] >>
  simp[boolean_def] >>
  metis_tac[semantics_reduce_term_valuation])

val binary_inference_rule = store_thm("binary_inference_rule",
  ``∀h1 h2 p1 p2 q.
    (p1 has_type Bool ∧ p2 has_type Bool ⇒ q has_type Bool) ∧
    (has_meaning p1 ∧ has_meaning p2 ⇒ has_meaning q) ∧
    (∀σ τ. type_valuation τ ∧ term_valuation τ σ ∧
           semantics σ τ p1 true ∧ semantics σ τ p2 true ∧
           σ closes_over q ⇒
           semantics σ τ q true) ∧
    h1 |= p1 ∧ h2 |= p2
    ⇒ TERM_UNION h1 h2 |= q``,
  rpt gen_tac >> strip_tac >>
  fs[sequent_def,ALL_BOOL_TERM_UNION] >>
  conj_tac >- (
    fs[EVERY_MEM] >>
    metis_tac[TERM_UNION_NONEW,TERM_UNION_THM,has_meaning_aconv] ) >>
  rw[] >>
  `∃σ1 m1. σ ⊑ σ1 ∧ term_valuation τ σ1 ∧ σ1 closes_over p1 ∧ semantics σ1 τ p1 m1` by
    metis_tac[has_meaning_def] >>
  `∃σ2 m2. σ1 ⊑ σ2 ∧ term_valuation τ σ2 ∧ σ2 closes_over p2 ∧ semantics σ2 τ p2 m2` by
    metis_tac[has_meaning_def] >>
  `semantics σ2 τ p1 m1` by metis_tac[semantics_extend_term_valuation] >>
  `σ2 closes_over p1` by metis_tac[closes_over_extend] >>
  `σ ⊑ σ2` by metis_tac[SUBMAP_TRANS] >>
  `semantics σ2 τ p1 true ∧ semantics σ2 τ p2 true` by (
    conj_tac >>
    first_x_assum match_mp_tac >> simp[] >>
    fs[EVERY_MEM] >>
    metis_tac[TERM_UNION_THM,semantics_aconv,welltyped_def
             ,TERM_UNION_NONEW,semantics_extend_term_valuation]) >>
  `m1 = true ∧ m2 = true` by metis_tac[semantics_11] >>
  `semantics σ2 τ q true` by (
    first_x_assum match_mp_tac >>
    simp[] >> metis_tac[closes_over_extend] ) >>
  metis_tac[semantics_reduce_term_valuation])

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
  fs[closes_over_equation] >>
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
  disch_then(qx_choosel_then[`sig`,`sem`]strip_assume_tac) >>
  simp[Abbr`G`] >>
  qexists_tac`λz. sem τ (σ |+ ((x,ty),z))` >>
  simp[CONJ_ASSOC,GSYM FORALL_AND_THM,GSYM IMP_CONJ_THM] >>
  conj_asm1_tac >- (
    qx_gen_tac`z` >> strip_tac >>
    first_x_assum(qspecl_then[`τ`,`σ |+ ((x,ty),z)`]mp_tac) >>
    discharge_hyps >- metis_tac[term_valuation_FUPDATE,FST,SND] >>
    strip_tac >>
    reverse conj_asm2_tac >- (
      match_mp_tac semantics_reduce_term_valuation >>
      qexists_tac`sig τ (σ |+ ((x,ty),z))` >>
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
  `∃mty. typeset τ ty mty` by metis_tac[type_has_meaning_def] >>
  fs[closes_over_equation] >>
  qabbrev_tac`σ0 = σ \\ (x,ty)` >>
  `term_valuation τ σ0` by (
    fs[term_valuation_def,Abbr`σ0`] >>
    fs[FEVERY_DEF] >>
    simp[DOMSUB_FAPPLY_THM] ) >>
  `EVERY (λt. semantics σ0 τ t true) h` by (
    fs[EVERY_MEM] >> rw[] >>
    match_mp_tac semantics_reduce_term_valuation >>
    qexists_tac`σ` >> simp[] >>
    conj_tac >- metis_tac[SUBMAP_DOMSUB] >>
    simp[Abbr`σ0`] >>
    metis_tac[semantics_closes_over] ) >>
  `∀z. z <: mty ⇒
      term_valuation τ (σ0 |+ ((x,ty),z)) ∧
      semantics (σ0 |+ ((x,ty),z)) τ (l === r) true` by (
    gen_tac >> strip_tac >>
    conj_asm1_tac >- metis_tac[term_valuation_FUPDATE,FST,SND] >>
    first_x_assum match_mp_tac >> simp[] >>
    conj_tac >- (
      fs[EVERY_MEM] >> rw[] >>
      match_mp_tac semantics_extend_term_valuation >>
      qexists_tac`σ0` >>
      simp[] >> simp[Abbr`σ0`] ) >>
    simp[Abbr`σ0`] >> metis_tac[] ) >>
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
  simp[closes_over_equation] >>
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
    metis_tac[has_meaning_def,semantics_reduce_term_valuation] ) >>
  metis_tac[semantics_typeset,typeset_Bool,WELLTYPED_LEMMA,IN_BOOL])

val welltyped_VSUBST = store_thm("welltyped_VSUBST",
  ``∀tm ilist.
      (∀s s'. MEM (s',s) ilist ⇒ ∃x ty. s = Var x ty ∧ s' has_type ty) ⇒
      (welltyped (VSUBST ilist tm) ⇔ welltyped tm)``,
  qsuff_tac `∀tm ilist.
      (∀s s'. MEM (s',s) ilist ⇒ ∃x ty. s = Var x ty ∧ s' has_type ty) ⇒
      welltyped (VSUBST ilist tm) ⇒ welltyped tm` >- metis_tac[VSUBST_WELLTYPED] >>
  Induct >> simp[VSUBST_def]
  >- (
    rw[] >>
    metis_tac[VSUBST_HAS_TYPE,WELLTYPED_LEMMA,WELLTYPED] )
  >- (
    rw[] >>
    first_x_assum (match_mp_tac o MP_CANON) >>
    qmatch_assum_abbrev_tac`welltyped (VSUBST ilist1 tm)` >>
    qexists_tac`ilist1` >>
    rw[Abbr`ilist1`] >- rw[Once has_type_cases] >>
    fs[MEM_FILTER]))

(*
val semantics_has_meaning = store_thm("semantics_has_meaning",
  ``(∀τ ty mty. typeset τ ty mty ⇒ type_has_meaning ty) ∧
    (∀σ τ tm mtm. semantics σ τ tm mtm ⇒ has_meaning tm)``,
  ho_match_mp_tac (theorem"semantics_strongind") >>
  conj_tac >- (
    rw[type_has_meaning_def] >>
    rw[Once semantics_cases] ) >>
  conj_tac >- (
    rw[type_has_meaning_def] ) >>
  conj_tac >- (
    rw[type_has_meaning_def] >>
    rw[Once semantics_cases] >>
    metis_tac[] ) >>
  conj_tac >- (
    rw[type_has_meaning_def,has_meaning_def] >>
    rw[Once semantics_cases] >>
    first_x_assum(qspecl_then[`τ'`,`FEMPTY`]mp_tac) >>
    simp[] >>
    disch_then(qx_choosel_then[`σ`,`m`]strip_assume_tac) >>
    qmatch_assum_abbrev_tac`semantics FEMPTY τ pp mtm` >>
    `semantics FEMPTY t' pp m
*)

val VFREE_IN_has_meaning = store_thm("VFREE_IN_has_meaning",
  ``∀t2 t1. has_meaning t2 ∧ VFREE_IN t1 t2 ⇒ has_meaning t1``,
  Induct
  >- simp[VFREE_IN_def]
  >- simp[VFREE_IN_def]
  >- (simp[VFREE_IN_def,has_meaning_Comb] >> metis_tac[])
  >- simp[VFREE_IN_def,has_meaning_Abs])

val semantics_VSUBST = store_thm("semantics_VSUBST",
  ``∀tm ilist σ τ.
      type_valuation τ ∧ term_valuation τ σ ∧
      (∀s s'. MEM (s',s) ilist ⇒ has_meaning s' ∧ ∃x ty. s = Var x ty ∧ s' has_type ty)
      ∧ σ closes_over (VSUBST ilist tm)
      ⇒
      semantics σ τ (VSUBST ilist tm) =
      semantics (σ |++ (REVERSE (MAP (λ(s',s). (dest_var s, @m. semantics σ τ s' m)) ilist))) τ tm``,
  Induct >- (
    gen_tac >>
    Induct >- (
      simp[VSUBST_def,REV_ASSOCD,FUPDATE_LIST_THM] ) >>
    Cases >> fs[VSUBST_def,REV_ASSOCD,FUPDATE_LIST_THM] >>
    rw[] >- (
      simp[FUN_EQ_THM] >>
      simp[Q.SPECL[`X`,`Y`,`Var A B`](CONJUNCT2 semantics_cases)] >>
      simp[FUPDATE_LIST_APPEND,FUPDATE_LIST_THM,FLOOKUP_UPDATE] >>
      SELECT_ELIM_TAC >>
      reverse conj_tac >- metis_tac[semantics_11] >>
      fs[has_meaning_def] >>
      metis_tac[semantics_reduce_term_valuation] ) >>
    fs[FUN_EQ_THM,Q.SPECL[`X`,`Y`,`Var s t`](CONJUNCT2 semantics_cases)] >>
    simp[FUPDATE_LIST_APPEND,FUPDATE_LIST_THM,FLOOKUP_UPDATE] >>
    `∃rs rty. r = Var rs rty` by metis_tac[] >> fs[] >>
    first_x_assum match_mp_tac >>
    metis_tac[])
  >- (
    rw[VSUBST_def] >>
    simp[FUN_EQ_THM] >>
    simp[Once semantics_cases] >>
    simp[Once semantics_cases,SimpRHS] )
  >- (
    rw[VSUBST_def] >>
    simp[FUN_EQ_THM] >>
    simp[Once semantics_cases] >>
    simp[Once semantics_cases,SimpRHS] >>
    srw_tac[DNF_ss][] >>
    EQ_TAC >> strip_tac >>
    map_every qexists_tac[`mt`,`mu`,`rty`] >> simp[] >>
    rw[] >> TRY (
      qmatch_abbrev_tac`semantics σ1 τ t1 m1` >>
      qmatch_assum_abbrev_tac`semantics σ2 τ t2 m1` >>
      qsuff_tac`semantics σ2 τ t2 = semantics σ1 τ t1` >- metis_tac[] >>
      unabbrev_all_tac >>
      (first_x_assum match_mp_tac ORELSE (match_mp_tac EQ_SYM >> first_x_assum match_mp_tac)) >>
      metis_tac[] ) >>
    metis_tac[welltyped_VSUBST,VSUBST_HAS_TYPE,WELLTYPED,WELLTYPED_LEMMA] )
  >- (*
    rpt gen_tac >> strip_tac >>
    fs[VSUBST_def,LET_THM] >>
    Q.PAT_ABBREV_TAC`ilist1 = FILTER X ilist` >>
    Q.PAT_ABBREV_TAC`z = VARIANT X s t` >>
    Q.PAT_ABBREV_TAC`ilist2 = X::ilist1` >>
    Q.PAT_ABBREV_TAC`P = EXISTS X ilist1` >>
    simp[FUN_EQ_THM] >> qx_gen_tac`m` >>
    simp[PROVE[]``semantics σ τ (if P then Y else Z) m = if P then semantics σ τ Y m else semantics σ τ Z m``] >>
    Q.PAT_ABBREV_TAC`ls:((string#type)#V)list = REVERSE (MAP X ilist)` >>
    simp[Once semantics_cases] >>
    simp[Once semantics_cases,SimpRHS] >>
    simp[Q.SPECL[`X`,`Y`,`Abs s t Z`](CONJUNCT2 semantics_cases)] >>
    `∀s s'. MEM (s',s) ilist1 ⇒ has_meaning s' ∧ (∃x ty. s = Var x ty ∧ s' has_type ty)` by (
      unabbrev_all_tac >> simp[MEM_FILTER] >> metis_tac[]) >>
    `∀s s'. MEM (s',s) ilist2 ⇒ (∃x ty. s = Var x ty ∧ s' has_type ty)` by (
      unabbrev_all_tac >> simp[MEM_FILTER] >>
      rw[] >> rw[Once has_type_cases]) >>
    reverse(Cases_on`P`)>>fs[]>-(
      EQ_TAC >> strip_tac >- (
        map_every qexists_tac[`mb`,`mty`,`mtyb`,`tyb`] >> simp[] >>
        conj_tac >- (
         `welltyped (VSUBST ilist1 tm)` by metis_tac[welltyped_def] >>
         `welltyped tm` by metis_tac[welltyped_VSUBST] >>
         `tyb = typeof tm` by metis_tac[VSUBST_HAS_TYPE,WELLTYPED_LEMMA,WELLTYPED] >>
         metis_tac[WELLTYPED] ) >>
        rw[] >>
      first_x_assum(qspecl_then[`ilist1`,`σ |+ ((s,t),x)`,`τ`]mp_tac) >>
      discharge_hyps >- (
        simp[] >>
        conj_tac >- metis_tac[term_valuation_FUPDATE,FST,SND] >>
        metis_tac[] ) >>
      Q.PAT_ABBREV_TAC`ls1:((string#type)#V)list = REVERSE X` >>
      `σ |+ ((s,t),x) |++ ls1 = (σ |++ ls1) |+ ((s,t),x)` by (
        match_mp_tac FUPDATE_FUPDATE_LIST_COMMUTES >>
        simp[Abbr`ls1`,rich_listTheory.MAP_REVERSE,MAP_MAP_o,combinTheory.o_DEF,LAMBDA_PROD] >>
        simp[Abbr`ilist1`,MEM_MAP,MEM_FILTER,FORALL_PROD] >>
        map_every qx_gen_tac[`r`,`v`] >>
        Cases_on`(r,v) ∈ set ilist`>>fs[]>>
        `∃x y. v = Var x y` by metis_tac[] >>
        fs[] >> metis_tac[] ) >>
      simp[] >>
      `term_valuation τ ((σ |++ ls1) |+ ((s,t),x))` by (
        match_mp_tac term_valuation_FUPDATE >> simp[] >>
        qexists_tac`mty`>>simp[] >>
        match_mp_tac term_valuation_FUPDATE_LIST >>
        simp[Abbr`ls1`] >>
        simp[EVERY_MEM,FORALL_PROD,MEM_MAP] >>
        simp[Abbr`ilist1`,MEM_FILTER,EXISTS_PROD] >>
        simp_tac(srw_ss()++DNF_ss)[]

        term_valuation_def
        FEVERY_FUPDATE_LIST_suff

      qsuff_tac`
      semantics_vfree_in
      `ls1 = ls` by (
        simp[Abbr`ls1`,Abbr`ls`,Abbr`ilist1`] >>
        rich_listTheory.MAP_FILTER
        simp[MAP_EQ_f]
        `∃
      print_apropos``x |+ y |++ z``
        
    discharge_hyps >- (
      simp[] >>
      conj_tac >- (
        simp[Abbr`ilist1`,MEM_FILTER] >>
        metis_tac[] ) >>
      Cases_on`P`>>fs[VFREE_IN_VSUBST,Abbr`ilist2`,REV_ASSOCD] >> rw[]
    reverse(Cases_on`P`)>>fs[]>-(

      simp[Once


    rw[VSUBST_def] >> rw[] >>
    simp[FUN_EQ_THM] >>
    rw[Once semantics_cases] >>
    rw[Once semantics_cases,SimpRHS] >>
    EQ_TAC >> strip_tac >>
    map_every qexists_tac[`mb`,`mty`,`mtyb`,`tyb`] >> simp[] >>
    (conj_tac >- (
       TRY (
         TRY(qunabbrev_tac`t'`) >>
         qmatch_assum_abbrev_tac`VSUBST ilist2 tm has_type tyb` >>
         `welltyped (VSUBST ilist2 tm)` by metis_tac[welltyped_def] >>
         `welltyped tm` by metis_tac[welltyped_VSUBST] >>
         `tyb = typeof tm` by metis_tac[VSUBST_HAS_TYPE,WELLTYPED_LEMMA,WELLTYPED] >>
         metis_tac[WELLTYPED] ) >>
       metis_tac[welltyped_VSUBST,VSUBST_HAS_TYPE,WELLTYPED,WELLTYPED_LEMMA,welltyped_def] ))
    >- (
      first_x_assum(qspecl_then[`ilist''`,`σ`,`τ`]mp_tac) >>
      discharge_hyps >- (
        simp[] >>
        conj_tac >- (
          fs[Abbr`ilist''`,Abbr`ilist'`,MEM_FILTER] >>
          rw[] >>
          fs[EXISTS_MEM,MEM_FILTER,EXISTS_PROD] >>
          metis_tac[VFREE_IN_has_meaning,has_meaning_Var] ) >>
        fs[LET_THM]
        simp[Abbr`ilist''`,Abbr`ilist'`,VFREE_IN_VSUBST,REV_ASSOCD] >>
        rw[] >> pop_assum mp_tac >> rw[] >>
        metis_tac[]
      simp[Q.SPECL[`X`,`Y`,`Var V Z`](CONJUNCT2 semantics_cases),FLOOKUP_DEF]
        metis_tac[]

    >- (
      qx_gen_tac`y` >> strip_tac >> fs[LET_THM] >>
      first_x_assum(qspecl_then[`ilist''`,`σ |+ ((z,t),y)`,`τ`]mp_tac) >>
      discharge_hyps >- (
        simp[] >>
        conj_tac >- metis_tac[term_valuation_FUPDATE,FST,SND] >>
        conj_tac >- (
          fs[Abbr`ilist''`,Abbr`ilist'`,MEM_FILTER] >>
          rw[] >>
          fs[EXISTS_MEM,MEM_FILTER,EXISTS_PROD] >>
          metis_tac[VFREE_IN_has_meaning,has_meaning_Var] ) >>
        metis_tac[] ) >>
      simp[Abbr`ilist''`,FUPDATE_LIST_APPEND,FUPDATE_LIST_THM] >>
      simp[Q.SPECL[`X`,`Y`,`Var V Z`](CONJUNCT2 semantics_cases),FLOOKUP_DEF]

        rw[]
      simp[FUPDATE_LIST_APPEND,FUPDATE_LIST_THM]
      ???? ))
    >- (
      qx_gen_tac`y` >> strip_tac >>
      first_x_assum(qspecl_then[`ilist''`,`σ |+ ((z,t),y)`,`τ`,`λa. if a = Var z t then y else m a`]mp_tac) >>
      discharge_hyps >- (
        simp[] >>
        conj_tac >- metis_tac[term_valuation_FUPDATE,FST,SND] >>
        simp[Abbr`ilist''`,Abbr`ilist'`,MEM_FILTER] >>
        rw[] >> TRY( simp[Once semantics_cases,FLOOKUP_DEF] >> NO_TAC) >>
        fs[EXISTS_MEM,MEM_FILTER,EXISTS_PROD]
        metis_tac[semantics_extend_term_valuation
     *)
   cheat)
*)
*)

val _ = export_theory()
