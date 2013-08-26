open HolKernel boolLib boolSimps bossLib lcsymtacs miscTheory pred_setTheory pairTheory listTheory finite_mapTheory alistTheory sholSyntaxTheory modelSetTheory
val _ = numLib.prefer_num()
val _ = new_theory"sholSemantics"

val discharge_hyps =
  match_mp_tac(PROVE[]``(p ∧ (q ==> r)) ==> ((p ==> q) ==> r)``) >> conj_tac

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

val simple_inst_def = Define`
  simple_inst tyin (Var x ty) = Var x (TYPE_SUBST tyin ty) ∧
  simple_inst tyin (Const x ty g) = Const x (TYPE_SUBST tyin ty) g ∧
  simple_inst tyin (Comb s t) = Comb (simple_inst tyin s) (simple_inst tyin t) ∧
  simple_inst tyin (Abs x ty t) = Abs x (TYPE_SUBST tyin ty) (simple_inst tyin t)`
val _ = export_rewrites["simple_inst_def"]

val simple_inst_has_type = store_thm("simple_inst_has_type",
  ``∀tm tyin ty. welltyped tm ⇒ simple_inst tyin tm has_type (TYPE_SUBST tyin (typeof tm))``,
  Induct >> rw[]
  >- rw[Once has_type_cases]
  >- rw[Once has_type_cases]
  >- (
    rw[Once has_type_cases] >> fs[] >>
    metis_tac[] )
  >- (
    rw[Once has_type_cases] ))

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

val REV_ASSOCD_ALOOKUP = store_thm("REV_ASSOCD_ALOOKUP",
  ``∀ls x d. REV_ASSOCD x ls d = case ALOOKUP (MAP (λ(x,y). (y,x)) ls) x of NONE => d | SOME y => y``,
  Induct >> simp[REV_ASSOCD] >>
  Cases >> simp[REV_ASSOCD] >> rw[])

val _ = Hol_datatype`
  dbterm = dbFree of string => type
         | dbVar of num => type
         | dbConst of string => type => const_tag
         | dbComb of dbterm => dbterm
         | dbAbs of type => dbterm`

val dbterm_def = Define`
  (dbterm env (Var s ty) =
     case find_index (s,ty) env 0 of SOME n => dbVar n ty | NONE => dbFree s ty) ∧
  (dbterm env (Const s ty g) = dbConst s ty g) ∧
  (dbterm env (Comb t1 t2) = dbComb (dbterm env t1) (dbterm env t2)) ∧
  (dbterm env (Abs x ty t) = dbAbs ty (dbterm ((x,ty)::env) t))`
val _ = export_rewrites["dbterm_def"]

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

val dbinst_def = Define`
  dbinst tyin (dbFree x ty) = dbFree x (tyinst tyin ty) ∧
  dbinst tyin (dbVar n ty) = dbVar n (tyinst tyin ty) ∧
  dbinst tyin (dbConst x ty g) = dbConst x (tyinst tyin ty) g ∧
  dbinst tyin (dbComb s t) = dbComb (dbinst tyin s) (dbinst tyin t) ∧
  dbinst tyin (dbAbs ty t) = dbAbs (tyinst tyin ty) (dbinst tyin t)`
val _ = export_rewrites["dbinst_def"]

val dbsubst_def = Define`
  (dbsubst σ (dbFree s ty) = FLOOKUPD σ (s,ty) (dbFree s ty)) ∧
  (dbsubst σ (dbVar n ty) = dbVar n ty) ∧
  (dbsubst σ (dbConst s ty g) = dbConst s ty g) ∧
  (dbsubst σ (dbComb t1 t2) = dbComb (dbsubst σ t1) (dbsubst σ t2)) ∧
  (dbsubst σ (dbAbs ty tm) = dbAbs ty (dbsubst σ tm))`
val _ = export_rewrites["dbsubst_def"]

val dbsubst_FEMPTY = store_thm("dbsubst_FEMPTY",
  ``∀tm. dbsubst FEMPTY tm = tm``,
  Induct >> simp[])
val _ = export_rewrites["dbsubst_FEMPTY"]

val dbsubst_dbsubst = store_thm("dbsubst_dbsubst",
  ``∀tm σ1 σ2. dbsubst σ2 (dbsubst σ1 tm) = dbsubst ((dbsubst σ2 o_f σ1) ⊌ σ2) tm``,
  Induct >- (
    simp[FLOOKUPD_def,FLOOKUP_FUNION,FLOOKUP_o_f] >> rw[] >>
    BasicProvers.CASE_TAC >>
    BasicProvers.CASE_TAC >>
    simp[FLOOKUPD_def] ) >> simp[])

val find_index_shift = store_thm("find_index_shift",
  ``∀ls x k j. (find_index x ls k = SOME j) ⇒ j ≥ k ∧ ∀n. find_index x ls n = SOME (j-k+n)``,
  Induct >> simp[find_index_def] >> rw[] >> res_tac >> fsrw_tac[ARITH_ss][])

val dbterm_env_shift = store_thm("dbterm_env_shift",
  ``∀tm e1 e0. (∀x ty n. VFREE_IN (Var x ty) tm ∧ find_index (x,ty) (e1++e0) 0 = SOME n ⇒ n < LENGTH e1)
      ⇒ dbterm (e1++e0) tm = dbterm e1 tm``,
  Induct >- (
    simp[find_index_def] >> rw[] >>
    BasicProvers.CASE_TAC >- (
      fs[GSYM find_index_NOT_MEM] >>
      BasicProvers.CASE_TAC >>
      metis_tac[find_index_NOT_MEM,optionTheory.NOT_SOME_NONE] ) >>
    fs[] >>
    Q.ISPECL_THEN[`e1`,`s,t`,`e0`,`0`,`x`]mp_tac find_index_APPEND1 >> rw[] )
  >- simp[]
  >- ( simp[] >> metis_tac[] ) >>
  fs[EVERY_MEM,FORALL_PROD] >> rw[] >>
  first_x_assum(qspecl_then[`(s,t)::e1`,`e0`]mp_tac) >>
  simp[find_index_def] >>
  disch_then match_mp_tac >>
  rw[] >> simp[] >>
  Q.ISPECL_THEN[`e1++e0`,`x,ty`,`1`,`n`]mp_tac find_index_shift >>
  simp[] >> rw[] >>
  pop_assum(qspec_then`0`mp_tac) >> simp[] >>
  rw[] >> Cases_on`n`>>fs[] >> metis_tac[])

val dbilist_def = Define`
  dbilist ilist = alist_to_fmap (MAP (λ(k,v). dest_var k, dbterm [] v) (MAP (λ(v,k). (k,v)) ilist))`

val dbilist_thm = store_thm("dbilist_thm",
  ``∀ilist x ty.
    (∀k v. MEM (v,k) ilist ⇒ ∃x ty. k = Var x ty) ⇒
    (FLOOKUP (dbilist ilist) (x,ty) =
     if MEM (Var x ty) (MAP SND ilist) then SOME (dbterm [] (REV_ASSOCD (Var x ty) ilist (Var x ty))) else NONE)``,
  rw[dbilist_def,ALOOKUP_FAILS,MEM_MAP,EXISTS_PROD] >- (
    rw[REV_ASSOCD_ALOOKUP] >>
    BasicProvers.CASE_TAC >>
    fs[ALOOKUP_FAILS,MEM_MAP,EXISTS_PROD] >>
    fs[MEM_EL,ALOOKUP_LEAST_EL] >>
    rfs[EL_MAP,UNCURRY] >>
    qpat_assum`X = EL n ilist`(assume_tac o SYM) >>
    qpat_assum`Var x ty = X`(assume_tac o SYM) >>
    conj_tac >- ( qexists_tac`n` >> simp[EL_MAP,UNCURRY] ) >>
    rw[] >>
    numLib.LEAST_ELIM_TAC >>
    conj_tac >- ( qexists_tac`n` >> simp[EL_MAP,UNCURRY] ) >>
    rw[] >>
    `¬(n < n'')` by (
      strip_tac >>
      first_x_assum(qspec_then`n`mp_tac) >>
      simp[EL_MAP,UNCURRY] ) >>
    `n'' < LENGTH ilist` by DECIDE_TAC >>
    fs[EL_MAP,UNCURRY] >>
    fs[GSYM LEFT_FORALL_IMP_THM] >>
    numLib.LEAST_ELIM_TAC >>
    conj_tac >- ( qexists_tac`n` >> simp[EL_MAP,UNCURRY] ) >>
    rw[] >>
    `¬(n'' < n''')` by (
      strip_tac >>
      first_x_assum(qspec_then`n''`mp_tac) >>
      simp[EL_MAP,UNCURRY] >>
      res_tac >> Cases_on`EL n'' ilist`>>fs[] >>fs[]) >>
    `n''' < LENGTH ilist` by DECIDE_TAC >>
    fs[EL_MAP,UNCURRY] >>
    `¬(n''' < n'')` by (
      strip_tac >>
      last_x_assum(qspec_then`n'''`mp_tac) >>
      simp[EL_MAP,UNCURRY] ) >>
    `n'' = n'''` by DECIDE_TAC >>
    simp[] ) >>
  spose_not_then strip_assume_tac >>
  res_tac >> fs[] >> metis_tac[])

val VSUBST_NIL = store_thm("VSUBST_NIL",
  ``∀tm. VSUBST [] tm = tm``,
  Induct >> simp[VSUBST_def,REV_ASSOCD])
val _ = export_rewrites["VSUBST_NIL"]

val RACONV_dbterm = store_thm("RACONV_dbterm",
  ``∀env tp. RACONV env tp ⇒
    (∀vp. MEM vp env ⇒ (∃x x' ty. (vp = (Var x ty, Var x' ty))))
     ⇒ dbterm (MAP (dest_var o FST) env) (FST tp) = dbterm (MAP (dest_var o SND) env) (SND tp)``,
  ho_match_mp_tac RACONV_ind >> rw[] >> rw[] >>
  TRY (
    first_x_assum match_mp_tac >>
    rw[] >> rw[] ) >>
  Induct_on`env` >> simp[ALPHAVARS_def] >>
  rw[] >> rw[] >- (
    rw[find_index_def] >>
    metis_tac[PAIR_EQ,term_11] ) >> fs[] >>
  simp[find_index_def] >>
  `∃x x' ty. h = (Var x ty, Var x' ty)` by metis_tac[] >> simp[] >>
  simp[Once find_index_shift_0] >>
  simp[Once find_index_shift_0,SimpRHS] >>
  rpt BasicProvers.CASE_TAC >> fs[] >> rw[] >> fs[])

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

val dbterm_ACONV = store_thm("dbterm_ACONV",
  ``∀t1 t2. ACONV t1 t2 ⇔ dbterm [] t1 = dbterm [] t2``,
  rw[ACONV_def,EQ_IMP_THM] >- (
    qspecl_then[`[]`,`t1,t2`]mp_tac RACONV_dbterm >> simp[] ) >>
  qspecl_then[`t1`,`[]`,`t2`,`[]`]mp_tac dbterm_RACONV >>
  simp[])

val dbfv_def = Define`
  dbfv (dbFree s ty) = [(s,ty)] ∧
  dbfv (dbVar _ _) = [] ∧
  dbfv (dbConst _ _ _) = [] ∧
  dbfv (dbComb t1 t2) = dbfv t1 ++ dbfv t2 ∧
  dbfv (dbAbs _ tm) = dbfv tm`
val _ = export_rewrites["dbfv_def"]

val dbbv_def = Define`
  dbbv (dbFree s ty) = [] ∧
  dbbv (dbVar n ty) = [(n,ty)] ∧
  dbbv (dbConst _ _ _) = [] ∧
  dbbv (dbComb t1 t2) = dbbv t1 ++ dbbv t2 ∧
  dbbv (dbAbs _ tm) = MAP (λ(n,ty). (PRE n,ty)) (FILTER ($< 0 o FST) (dbbv tm))`
val _ = export_rewrites["dbbv_def"]

val fresh_def = Define`
  fresh ls ty = let n = LEAST n. (REPLICATE n (ARB:char),ty) ∉ set ls in (REPLICATE n (ARB:char),ty)`

val fresh_thm = store_thm("fresh_thm",
  ``∀ls ty. fresh ls ty ∉ set ls``,
  rw[fresh_def,LET_THM] >>
  numLib.LEAST_ELIM_TAC >> rw[] >>
  spose_not_then strip_assume_tac >>
  qsuff_tac`INFINITE (set ls)` >- simp[] >>
  REWRITE_TAC[infinite_num_inj] >>
  qexists_tac`λn. REPLICATE n ARB,ty` >>
  simp[INJ_DEF] >> rw[] >>
  metis_tac[rich_listTheory.LENGTH_REPLICATE])

val fresh_ty = store_thm("fresh_ty",
  ``∀ls ty. SND(fresh ls ty) = ty``,
  rw[fresh_def] >> rw[])

(*
val undb_def = Define`
  (undb env (dbFree s ty) = Var s ty) ∧
  (undb env (dbVar n) = UNCURRY Var (EL n env)) ∧
  (undb env (dbConst s ty g) = Const s ty g) ∧
  (undb env (dbComb t1 t2) = Comb (undb env t1) (undb env t2)) ∧
  (undb env (dbAbs ty tm) =
     let (x,ty) = fresh (env ++ dbfv tm) ty in
     Abs x ty (undb ((x,ty)::env) tm))`
val _ = export_rewrites["undb_def"]

val dbterm_undb = store_thm("dbterm_undb",
  ``∀tm env. set (dbbv tm) ⊆ count (LENGTH env) ∧ DISJOINT (set (dbfv tm)) (set env) ∧ ALL_DISTINCT env
    ⇒ (dbterm env (undb env tm) = tm)``,
  Induct >- (
    simp[] >> rw[] >>
    BasicProvers.CASE_TAC >>
    metis_tac[find_index_is_MEM] )
  >- rw[UNCURRY]
  >- rw[]
  >- rw[] >>
  rw[] >>
  rw[] >- metis_tac[fresh_ty,SND] >>
  first_x_assum match_mp_tac >>
  fs[SUBSET_DEF,IN_DISJOINT,MEM_MAP,GSYM LEFT_FORALL_IMP_THM,MEM_FILTER] >>
  conj_tac >- (
    rw[] >>
    res_tac >>
    qmatch_assum_rename_tac`MEM z Y`["Y"] >>
    Cases_on`z`>>fsrw_tac[ARITH_ss][] ) >>
  conj_tac >- (
    qx_gen_tac`z` >>
    Cases_on`z=(x,ty)`>>simp[]>>
    metis_tac[fresh_thm,MEM_APPEND] ) >>
  metis_tac[fresh_thm,MEM_APPEND])
*)

(*
val dbbv_dbterm = store_thm("dbbv_dbterm",
  ``∀tm env. set (dbbv (dbterm env tm)) ⊆ count (LENGTH env)``,
  Induct >- (
    simp[SUBSET_DEF] >>
    rpt gen_tac >>
    BasicProvers.CASE_TAC >> simp[] >>
    imp_res_tac find_index_LESS_LENGTH >>
    fs[] )
  >- rw[]
  >- rw[] >>
  rw[] >>
  fs[SUBSET_DEF,MEM_MAP,GSYM LEFT_FORALL_IMP_THM,MEM_FILTER] >>
  rw[] >> res_tac >> fs[] >>
  Cases_on`y`>>fs[])
*)

(*
val VSUBST_RACONV = store_thm("VSUBST_RACONV",
  ``∀env tp. RACONV env tp ⇒ ∀ilist. RACONV (MAP (λ(x,y). VSUBST ilist x, VSUBST ilist y) env) (VSUBST ilist (FST tp), VSUBST ilist (SND tp))``,
  ho_match_mp_tac RACONV_ind >>
  conj_tac >- (
    Induct >- (
      simp[ALPHAVARS_def,VSUBST_def,RACONV_REFL] ) >>
    Cases >> simp[ALPHAVARS_def] >>
    rw[VSUBST_def] >>
    rw[VSUBST_def] >>
*)

(*
val dbterm_rename = store_thm("dbterm_rename",
  ``∀tm x x' ty env ilist.
      ¬VFREE_IN (Var x' ty) tm ∧
      Var x ty ∉ set (MAP SND ilist) ∧

      ⇒
      dbterm ((x',ty)::env) (VSUBST ((Var x' ty,Var x ty)::ilist) tm) =
      dbterm ((x,ty)::env) (VSUBST ilist tm)``,
  Induct >- (
    simp[VSUBST_def] >>
    rw[REV_ASSOCD,find_index_def] >- (
      Q.ISPECL_THEN[`ilist`,`Var s t`,`Var s t`]mp_tac REV_ASSOCD_MEM >>
      rw[] >> fs[find_index_def] >>
      fs[MEM_MAP,EXISTS_PROD] >> metis_tac[] )
    dbterm_env_shift

val dbterm_VSUBST = store_thm("dbterm_VSUBST",
  ``∀tm ilist env.
      (∀k v. MEM (v,k) ilist ⇒
             ∃x ty. k = Var x ty ∧
                    (∀x ty. MEM (x,ty) env ⇒ ¬VFREE_IN (Var x ty) v)) ⇒
      dbterm env (VSUBST (FILTER (λ(v,k). dest_var k ∉ set env) ilist) tm) =
      dbsubst (dbilist ilist) (dbterm env tm)``,
  Induct >- (
    simp[VSUBST_def] >> rw[] >>
    match_mp_tac EQ_SYM >>
    BasicProvers.CASE_TAC >- (
      fs[GSYM find_index_NOT_MEM] >>
      qspecl_then[`ilist`,`s`,`t`]mp_tac dbilist_thm >>
      discharge_hyps >- metis_tac[] >>
      rw[] >- (
        rw[REV_ASSOCD_FILTER] >>
        qmatch_abbrev_tac`dbterm [] a = dbterm env a` >>
        qspecl_then[`a`,`[]`,`env`]mp_tac dbterm_env_shift >>
        discharge_hyps >- (
          rw[] >>
          Cases_on`a = Var s t` >> simp[] >- (
            spose_not_then strip_assume_tac >>
            imp_res_tac find_index_is_MEM >>
            metis_tac[] ) >>
          `MEM (a,Var s t) ilist` by metis_tac[REV_ASSOCD_MEM] >>
          spose_not_then strip_assume_tac >>
          first_x_assum(qspecl_then[`Var s t`,`a`]mp_tac) >>
          simp[] >>
          metis_tac[find_index_is_MEM] ) >>
        rw[] ) >>
      rw[REV_ASSOCD_FILTER] >>
      qmatch_abbrev_tac`dbFree s t = dbterm env a` >>
      Cases_on`a = Var s t`>>simp[] >- (
        BasicProvers.CASE_TAC >>
        metis_tac[find_index_is_MEM] ) >>
      `MEM (a,Var s t) ilist` by metis_tac[REV_ASSOCD_MEM] >>
      fs[MEM_MAP,EXISTS_PROD] >>
      metis_tac[] ) >>
    simp[REV_ASSOCD_FILTER] >> rw[] >>
    metis_tac[find_index_is_MEM] )
  >- rw[VSUBST_def]
  >- rw[VSUBST_def] >>
  rw[] >>
  rw[VSUBST_def] >>
  rw[] >- (
    fs[EXISTS_MEM,Abbr`ilist'`,MEM_FILTER,EXISTS_PROD] >>
    qmatch_assum_abbrev_tac`Abbrev(t' = VSUBST (FILTER P ilist') tm)` >>
    cheat ) >>
  simp[Abbr`t'`] >>
  first_x_assum(qspecl_then[`ilist`,`(s,t)::env`]mp_tac) >>
  discharge_hyps >- (
    simp[] >> rw[] >>
    res_tac >> simp[] >>
    reverse(rw[]) >- metis_tac[] >>
    fs[Abbr`ilist'`,EXISTS_MEM,EVERY_MEM,MEM_FILTER,FORALL_PROD] >>
    Cases_on`MEM (s,t) env`>-metis_tac[] >>
    first_x_assum(qspecl_then[`
*)

(*
val dbterm_rename = store_thm("dbterm_rename",
  ``∀tm env x x' ty.
      ¬VFREE_IN (Var x' ty) tm ⇒
      dbterm ((x',ty)::env) (VSUBST [(Var x' ty,Var x ty)] tm) =
      dbterm ((x,ty)::env) tm``,
  Induct >- (
    simp[VSUBST_def,REV_ASSOCD,find_index_def] >>
    rw[find_index_def] >> rw[] )
  >- rw[VSUBST_def]
  >- rw[VSUBST_def]
  >- (
     simp[VSUBST_def] >>
     rpt gen_tac >> strip_tac >- (
       rpt BasicProvers.VAR_EQ_TAC >> simp[] >>
       rw[] >- (
         fs[] >>

val dbterm_rename_bvars = store_thm("dbterm_rename_bvars",
  ``∀tm env ilist.
    (∀k v. MEM (v,k) ilist ⇒ ∃x x' ty. k = Var x ty ∧ v = Var x' ty ∧ MEM (x,ty) env) ⇒
    dbterm (MAP (λ(x,ty). dest_var(REV_ASSOCD (Var x ty) ilist (Var x ty))) env) (VSUBST ilist tm) =
    dbterm env tm``,
  Induct >- (
    simp[VSUBST_def,REV_ASSOCD_ALOOKUP] >>
    rw[] >>
    BasicProvers.CASE_TAC >- (
      fs[ALOOKUP_FAILS,MEM_MAP,EXISTS_PROD] >>
      BasicProvers.CASE_TAC >- (
        fs[GSYM find_index_NOT_MEM,MEM_MAP,EXISTS_PROD] >>
        pop_assum(qspecl_then[`s`,`t`]mp_tac) >>
        BasicProvers.CASE_TAC >> simp[] >- (
          rw[] >>
          BasicProvers.CASE_TAC >>
          imp_res_tac find_index_is_MEM ) >>
        BasicProvers.CASE_TAC >> simp[] >>
        imp_res_tac find_index_is_MEM >>
        imp_res_tac ALOOKUP_MEM >>
        fs[MEM_MAP,EXISTS_PROD] >>
        res_tac >> fs[] ) >>
      BasicProvers.CASE_TAC >- (
        fs[GSYM find_index_NOT_MEM] >>
        imp_res_tac find_index_is_MEM >>
        fs[MEM_MAP,EXISTS_PROD] >>
        qpat_assum`X = Y`mp_tac >>
        BasicProvers.CASE_TAC >> simp[] >- (
          fs[ALOOKUP_FAILS,MEM_MAP,EXISTS_PROD] >>
          metis_tac[] ) >>
        imp_res_tac ALOOKUP_MEM >>
        fs[MEM_MAP,EXISTS_PROD] >>
        res_tac >> fs[] >> rw[] >>

          simp[GSM find_index_NOT_MEM]
          fs[ALOOKUP_FAILS]
*)

(*
val dbterm_VSUBST = store_thm("dbterm_VSUBST",
  ``∀tm env ilist env'.
      (∀k v. MEM (v,k) ilist ⇒
        ∃x ty. k = Var x ty ∧
               (∀x ty. MEM (x,ty) env ⇒ ¬VFREE_IN (Var x ty) v) ∧
               (MEM (x,ty) env ⇒ ∃x'. v = Var x' ty ∧ ¬VFREE_IN v tm)) ∧
      (env' = MAP (λ(x,ty). dest_var(REV_ASSOCD (Var x ty) ilist (Var x ty))) env)
      ⇒
      dbterm env' (VSUBST ilist tm) =
      dbsubst (dbilist ilist) (dbterm env tm)``,
  Induct >- (
    rw[VSUBST_def,REV_ASSOCD_ALOOKUP] >>
    match_mp_tac EQ_SYM >>
    BasicProvers.CASE_TAC >> simp[] >- (
      qspecl_then[`ilist`,`s`,`t`]mp_tac dbilist_thm >>
      discharge_hyps >- metis_tac[] >>
      rw[REV_ASSOCD_ALOOKUP] >- (
        BasicProvers.CASE_TAC >>
        fs[ALOOKUP_FAILS,find_index_def,MEM_MAP,EXISTS_PROD] >>
        qmatch_abbrev_tac`dbterm [] x = dbterm e x` >>
        qspecl_then[`x`,`[]`,`e`]mp_tac dbterm_env_shift >>
        discharge_hyps >- (
          rw[] >>
          imp_res_tac ALOOKUP_MEM >>
          fs[MEM_MAP,EXISTS_PROD] >>
          res_tac >> fs[] >>
          rpt BasicProvers.VAR_EQ_TAC >>
          fs[GSYM find_index_NOT_MEM] >> rfs[] >> rw[] >>
          spose_not_then strip_assume_tac >>
          imp_res_tac find_index_is_MEM >>
          fs[Abbr`e`,MEM_MAP,EXISTS_PROD] >>
          ntac 2 (pop_assum mp_tac) >>
          BasicProvers.CASE_TAC >> simp[] >- metis_tac[] >> rw[] >>
          imp_res_tac ALOOKUP_MEM >>
          fs[MEM_MAP,EXISTS_PROD] >>
          res_tac >> fs[] >>
          rpt BasicProvers.VAR_EQ_TAC >>
          rfs[] >> rw[] >>
          spose_not_then strip_assume_tac >> fs[] >>
          rpt BasicProvers.VAR_EQ_TAC >>
          fs[] >> rw[] >>
          metis_tac[]
*)

(*
val dbterm_VSUBST = store_thm("dbterm_VSUBST",
  ``∀tm env ilist env'.
      (∀k v. MEM (v,k) ilist ⇒
        ∃x ty. k = Var x ty ∧
               (REV_ASSOCD k ilist k = v ⇒
                 EVERY ($~ o combin$C VFREE_IN v o UNCURRY Var) env ∧
                 (MEM (x,ty) env ⇒
                    ∃e x'. env = (x,ty)::e ∧ ilist = [(v,k)] ∧ v = Var x' ty))) ∧
      (env' = if ∃k v e. ilist = [(v,k)] ∧ env = (dest_var k)::e then (dest_var (FST(HD ilist)))::(TL env) else env)
      ⇒
      dbterm env' (VSUBST ilist tm) =
      dbsubst (dbilist ilist) (dbterm env tm)``,
  Induct >- (
    simp[VSUBST_def] >> rpt gen_tac >>
    simp[REV_ASSOCD_ALOOKUP] >>
    strip_tac >>
    match_mp_tac EQ_SYM >>
    BasicProvers.CASE_TAC >> simp[] >- (
      qspecl_then[`ilist`,`s`,`t`]mp_tac dbilist_thm >>
      discharge_hyps >- metis_tac[] >>
      simp[MEM_MAP,EXISTS_PROD] >> strip_tac >>
      fs[GSYM find_index_NOT_MEM] >>
      Cases_on`ALOOKUP (MAP (λ(x,y). (y,x)) ilist) (Var s t)` >- (
        fs[ALOOKUP_FAILS,MEM_MAP,EXISTS_PROD] >>
        rw[] >> fs[] >> rw[] >> fs[] >> rw[find_index_def]
        ) >>
      simp[REV_ASSOCD_ALOOKUP] >>
        BasicProvers.CASE_TAC >> simp[] >>
        BasicProvers.CASE_TAC >> simp[] >>
        BasicProvers.CASE_TAC >> simp[] >- (
          qmatch_abbrev_tac`dbterm [] x = dbterm env x` >>
          qspecl_then[`x`,`[]`,`env`]mp_tac dbterm_env_shift >>simp[] >>
          discharge_hyps >- (
            simp[Abbr`env`,find_index_def] >>
            imp_res_tac ALOOKUP_MEM >>
            pop_assum mp_tac >>
            simp[MEM_MAP,EXISTS_PROD] >> strip_tac >>
            first_x_assum(qspecl_then[`Var s t`,`x`]mp_tac) >>
            simp[] >> strip_tac >>
            rw[] >> rw[] >>
            qpat_assum`EVERY X Y`mp_tac >>
            simp[EVERY_MEM,FORALL_PROD] >>
            metis_tac[find_index_is_MEM] ) >>
          rw[] ) >>
        qmatch_abbrev_tac`dbterm [] x = dbterm env x` >>
        qspecl_then[`x`,`[]`,`env`]mp_tac dbterm_env_shift >>simp[] >>
        discharge_hyps >- (
          simp[Abbr`env`,find_index_def] >>
          imp_res_tac ALOOKUP_MEM >>
          ntac 2 (pop_assum mp_tac) >>
          simp[MEM_MAP,EXISTS_PROD] >> ntac 2 strip_tac >>
          first_assum(qspecl_then[`Var s t`,`x`]mp_tac) >>
          first_x_assum(qspecl_then[`Var q r`,`x'`]mp_tac) >>
          simp[] >> ntac 2 strip_tac >>
          rpt BasicProvers.VAR_EQ_TAC >> simp[] >>
          qpat_assum`¬VFREE_IN X Y`mp_tac >>
          qpat_assum`¬VFREE_IN X Y`mp_tac >>
          simp[] >> ntac 2 strip_tac >>
          qpat_assum`MEM X Y`mp_tac >> simp[] >>
          spose_not_then strip_assume_tac >>
          rpt BasicProvers.VAR_EQ_TAC >>
          pop_assum mp_tac >> simp[] >>
          qpat_assum`MEM X Y`mp_tac >> simp[] >>
          qpat_assum`MEM X Y`mp_tac >> simp[] >>
          fs[] ) >>
        rw[] ) >>
      `ALOOKUP (MAP (λ(x,y). (y,x)) ilist) (Var s t) = NONE` by (
        simp[ALOOKUP_FAILS,MEM_MAP,EXISTS_PROD] >> metis_tac[] ) >>
      simp[] >>
      BasicProvers.CASE_TAC >> simp[find_index_def] >>
      BasicProvers.CASE_TAC >>
      BasicProvers.CASE_TAC >> fs[] >>
      fs[find_index_def] >>
      imp_res_tac ALOOKUP_MEM >> fs[MEM_MAP,EXISTS_PROD] >>
      first_x_assum(qspecl_then[`Var q r`,`x`]mp_tac) >>
      simp[] >> rw[] >- (
        spose_not_then strip_assume_tac >> fs[] >> rw[] >> fs[]

        rpt BasicProvers.VAR_EQ_TAC
      res_tac >> fs[] >>
      rpt BasicProvers.VAR_EQ_TAC >>
      fs[] >>
      rpt BasicProvers.VAR_EQ_TAC >>
      qpat_assum`¬VFREE_IN X Y`mp_tac >>
      simp[] >> strip_tac >>
      qpat_assum`MEM X Y`mp_tac >> simp[] >>
      qpat_assum`ALOOKUP X Y = Z`mp_tac >> simp[] >>
      qpat_assum`ALOOKUP X Y = Z`mp_tac >> simp[] >>
      rw[]>>fs[]>>rfs[]>>
      fs[dbilist_def,find_index_def]

      fs[ALOOKUP_FAILS,find_index_def] >>
      BasicProvers.CASE_TAC >> simp[find_index_def] >- (
        fs[ALOOKUP_FAILS,MEM_MAP,EXISTS_PROD] >>
        BasicProvers.CASE_TAC >>
        imp_res_tac ALOOKUP_MEM >>
        fs[MEM_MAP,EXISTS_PROD] >>
        res_tac >> rfs[] >> fs[] >>
        metis_tac[] ) >>
      BasicProvers.CASE_TAC >- (
        fs[ALOOKUP_FAILS,MEM_MAP,EXISTS_PROD] >>
        imp_res_tac ALOOKUP_MEM >>
        fs[MEM_MAP,EXISTS_PROD] >>
        metis_tac[dest_var_def] ) >>
      fs[ALOOKUP_LEAST_EL,MEM_EL] >> rw[] >>
      numLib.LEAST_ELIM_TAC >>
      conj_tac >- metis_tac[] >> rw[] >>
      rfs[EL_MAP,UNCURRY] >>
      `¬(n < n'')` by (
        strip_tac >> first_x_assum(qspec_then`n`mp_tac) >> simp[EL_MAP,UNCURRY] ) >>
      `n'' < LENGTH ilist` by DECIDE_TAC >> fs[EL_MAP,UNCURRY] >>
      numLib.LEAST_ELIM_TAC >>
      conj_tac >- (qexists_tac`n'`>>simp[EL_MAP,UNCURRY]) >> rw[] >>
      qpat_assum`Var s t = X`(assume_tac o SYM) >> fs[] >>
      `¬(n' < n''')` by (
        strip_tac >> first_x_assum(qspec_then`n'`mp_tac) >> simp[EL_MAP,UNCURRY] ) >>
      `n''' < LENGTH ilist` by DECIDE_TAC >> fs[EL_MAP,UNCURRY] >>
      qpat_assum`(s,t) = X`(assume_tac o SYM) >> fs[] >>
      `¬(n''' < n'')` by (
        strip_tac >> last_x_assum(qspec_then`n'''`mp_tac) >> simp[EL_MAP,UNCURRY] >>
        fs[GSYM LEFT_FORALL_IMP_THM] >> res_tac >>
        Cases_on`EL n''' ilist`>>fs[] >> fs[] ) >>
      `¬(n'' < n''')` by (
        strip_tac >> first_x_assum(qspec_then`n''`mp_tac) >> simp[EL_MAP,UNCURRY] ) >>
      `n'' = n'''` by DECIDE_TAC >> simp[] ) >>
    Cases_on`h`>>simp[]>>
    simp[find_index_def] >>
    BasicProvers.CASE_TAC >> simp[] >- (
      fs[ALOOKUP_FAILS,MEM_MAP,EXISTS_PROD] >>
      BasicProvers.CASE_TAC >> simp[find_index_def] >- (
        fs[ALOOKUP_FAILS,MEM_MAP,EXISTS_PROD] >>
        rw[]>>fs[] >> BasicProvers.CASE_TAC>>fs[] >>
        BasicProvers.CASE_TAC >>
        imp_res_tac ALOOKUP_MEM >>
        fs[MEM_MAP,EXISTS_PROD] >> rw[] >>
        res_tac >> rfs[] >> fs[] >>
        metis_tac[] ) >>
      rw[] >- (
        imp_res_tac ALOOKUP_MEM >>
        fs[MEM_MAP,EXISTS_PROD] >>
        metis_tac[] ) >>
      BasicProvers.CASE_TAC >> simp[]


        fs[GSYM find_index_NOT_MEM] >>
        fs[MEM_MAP,EXISTS_PROD] >>
        BasicProvers.CASE_TAC >> simp[] >- (
          fs[GSYM find_index_NOT_MEM] >>
          BasicProvers.CASE_TAC >> simp[] >>
          imp_res_tac ALOOKUP_MEM >>
          fs[MEM_MAP,EXISTS_PROD] >>
          res_tac >> fs[] >>
          metis_tac[] ) >>
        imp_res_tac find_index_is_MEM >>
        simp[] >>
        BasicProvers.CASE_TAC >> simp[] >>
        imp_res_tac ALOOKUP_MEM >>
        fs[MEM_MAP,EXISTS_PROD] >>
        metis_tac[] ) >>
      BasicProvers.CASE_TAC >> simp[] >- (
        fs[GSYM find_index_NOT_MEM] >>
        imp_res_tac find_index_is_MEM >>
        fs[MEM_MAP,EXISTS_PROD] >>
        qpat_assum`(s,t) = X`(mp_tac o SYM)>>
        BasicProvers.CASE_TAC >> simp[] >> rw[] >> fs[] >>
        imp_res_tac ALOOKUP_MEM >>
        fs[MEM_MAP,EXISTS_PROD] >>
        res_tac >> rfs[] >> rw[] >> rfs[] >> rw[] >> rfs[] >> rw[] >>
        fs[EVERY_MEM,FORALL_PROD] >>
        BasicProvers.CASE_TAC >> simp[] >>
        fs[ALOOKUP_FAILS,MEM_MAP,EXISTS_PROD]

      qmatch_assum_abbrev_tac`find_index st (MAP f ls) 0 = SOME x` >>
      Q.ISPECL_THEN[`ls`,`st`,`0`,`f`]mp_tac find_index_MAP_inj >>
      discharge_hyps >- (
        simp[Abbr`st`,Abbr`f`] >>
        simp[FORALL_PROD] >>
        qx_genl_tac[`a`,`b`] >>
        strip_tac >>
        BasicProvers.CASE_TAC >> simp[] >- (
          BasicProvers.CASE_TAC >> simp[] >>
          imp_res_tac ALOOKUP_MEM >>
          fs[MEM_MAP,EXISTS_PROD] >>
          res_tac >> rfs[] >>
          rpt BasicProvers.VAR_EQ_TAC >> rfs[] >>
          rw[] >>
          fs[EVERY_MEM,FORALL_PROD]

      imp_res_tac find_index_is_MEM >>
      fs[MEM_MAP,EXISTS_PROD] >>
      qpat_assum`(s,t) = X`(assume_tac o SYM)>>fs[]>>
      pop_assum mp_tac >>
      BasicProvers.CASE_TAC >> simp[] >- (
        rw[] >>
        BasicProvers.CASE_TAC >> simp[]
        imp_res_tac find_index_is_MEM >>
        fs[MEM_MAP,EXISTS_PROD] 
        hrk

        qmatch_assum_abbrev_tac`find_index (s,t) (MAP f env) 0 = NONE` >>
        `MEM (f (s,t)) (MAP f env)` by metis_tac[MEM_MAP] >>
        pop_assum mp_tac >>
        simp[Abbr`f`] >>
        BasicProvers.CASE_TAC >> simp[MEM_MAP,EXISTS_PROD] >- (
          rw[] >>
          BasicProvers.CASE_TAC >> simp[] >>
          fs[ALOOKUP_FAILS,MEM_MAP,EXISTS_PROD]

    BasicProvers.CASE_TAC >> simp[] >- (
      BasicProvers.CASE_TAC >- (
        fs[ALOOKUP_FAILS,MEM_MAP,EXISTS_PROD] >>
        imp_res_tac ALOOKUP_MEM >>
        fs[MEM_MAP,EXISTS_PROD] >>
        metis_tac[dest_var_def] ) >>
      fs[ALOOKUP_LEAST_EL,MEM_EL] >>
      rfs[EL_MAP,UNCURRY] >> rw[] >>
      numLib.LEAST_ELIM_TAC >>
      conj_tac >- ( qexists_tac`n` >> simp[EL_MAP,UNCURRY] ) >> rw[] >>
      `¬(n < n'')` by (
        strip_tac >>
        first_x_assum(qspec_then`n`mp_tac) >>
        simp[EL_MAP,UNCURRY] ) >>
      `n'' < LENGTH ilist` by DECIDE_TAC >>
      fs[EL_MAP,UNCURRY] >>
      numLib.LEAST_ELIM_TAC >>
      conj_tac >- ( qexists_tac`n'` >> simp[EL_MAP,UNCURRY] ) >> rw[] >>
      `¬(n' < n''')` by (
        strip_tac >>
        first_x_assum(qspec_then`n'`mp_tac) >>
        simp[EL_MAP,UNCURRY] ) >>
      `n''' < LENGTH ilist` by DECIDE_TAC >>
      fs[EL_MAP,UNCURRY] >>
      qpat_assum`(s,t) = X`(assume_tac o SYM) >> fs[] >>
      qpat_assum`Var s t = X`(assume_tac o SYM) >> fs[] >>
      `¬(n'' < n''')` by (
        strip_tac >>
        first_x_assum(qspec_then`n''`mp_tac) >>
        simp[EL_MAP,UNCURRY] ) >>
      `¬(n''' < n'')` by (
        strip_tac >>
        last_x_assum(qspec_then`n'''`mp_tac) >>
        simp[EL_MAP,UNCURRY] >>
        `∃x y. SND(EL n''' ilist) = Var x y` by metis_tac[pair_CASES,SND] >>
        fs[] ) >>
      `n'' = n'''` by DECIDE_TAC >> rw[] >>
      fs[GSYM LEFT_FORALL_IMP_THM] >> rw[] >>
      rfs[] >> rw[] >>
      qspecl_then[`FST(EL n'' ilist)`,`[]`,`env`]mp_tac dbterm_env_shift >>
      simp[] >> disch_then match_mp_tac >>
      first_x_assum(qspecl_then[`SND(EL n'' ilist)`,`FST(EL n'' ilist)`,`n''`]mp_tac) >>
      Cases_on`EL n'' ilist`>>simp[]>> rw[] >> fs[] >> BasicProvers.VAR_EQ_TAC >> fs[] >>
      spose_not_then strip_assume_tac >>
      Q.ISPECL_THEN[`env`,`x,ty`,`0`]mp_tac find_index_NOT_MEM >>
*)

(*
val dbterm_subst_nil = store_thm("dbterm_subst_nil",
  ``∀x k env. dbterm k env x = dbsubst (alist_to_fmap (GENLIST (λi. (EL i env,dbVar (k+i))) (LENGTH env))) (dbterm k [] x)``,
  Induct >- (
    simp[find_index_def] >> rw[] >>
    BasicProvers.CASE_TAC >- (
      fs[GSYM find_index_NOT_MEM] >>
      BasicProvers.CASE_TAC >>
      imp_res_tac ALOOKUP_MEM >>
      fs[MEM_GENLIST,MEM_EL] >>
      metis_tac[] ) >>
    BasicProvers.CASE_TAC >- (
      fs[ALOOKUP_FAILS,MEM_GENLIST] >>
      metis_tac[find_index_NOT_MEM,optionTheory.NOT_SOME_NONE,MEM_EL] ) >>
    fs[ALOOKUP_LEAST_EL,find_index_LEAST_EL] >> rw[] >>
    fs[MEM_EL] >> rfs[EL_MAP] >>
    numLib.LEAST_ELIM_TAC >> conj_tac >- metis_tac[] >> rw[] >>
    `¬(n' < n'')` by metis_tac[] >>
    numLib.LEAST_ELIM_TAC >> conj_tac >- (
      qexists_tac`n''` >> simp[EL_MAP] ) >>
    rw[] >>
    `¬(n'' < n''')` by (
      strip_tac >>
      first_x_assum(qspec_then`n''`mp_tac) >>
      simp[EL_MAP] ) >>
    simp[EL_MAP] >>
    `¬(n''' < n'')` by (
      strip_tac >>
      last_x_assum(qspec_then`n'''`mp_tac) >>
      simp[] >>
      `n''' < LENGTH env` by DECIDE_TAC >>
      fs[EL_MAP] ) >>
    DECIDE_TAC )
  >- simp[]
  >- (
    simp_tac(srw_ss())[] >>
    metis_tac[] ) >>
  simp_tac(srw_ss())[] >>
  rpt gen_tac >>
  first_assum(qspecl_then[`k`,`(s,t)::env`]mp_tac) >>
  first_x_assum(qspecl_then[`k`,`[(s,t)]`]mp_tac) >>
  rw[] >>
  simp[GENLIST_CONS,arithmeticTheory.ADD1,combinTheory.o_DEF]
  simp[dbsubst_dbsubst] >>
  simp[GSYM FUPDATE_EQ_FUNION]
*)

(*
val dbterm_VSUBST = store_thm("dbterm_VSUBST",
  ``∀tm k env ilist.
      (∀s s'. MEM (s,s') ilist ⇒ ∃x ty. s' = Var x ty) ⇒
      dbterm k env (VSUBST ilist tm) =
      dbsubst (alist_to_fmap (GENLIST (λi. (EL i env,dbVar (k+i))) (LENGTH env)))
        (dbsubst (alist_to_fmap (MAP (λ(v,x). (dest_var x,dbterm (k + LENGTH env) [] v)) ilist))
          (dbterm (k + LENGTH env) [] tm))``,
  Induct
  >- (
    simp[VSUBST_def,find_index_def] >> rw[] >>
    Q.PAT_ABBREV_TAC`ls:((string#type)#dbterm)list = MAP X ilist` >>
    simp[REV_ASSOCD_ALOOKUP] >>
    BasicProvers.CASE_TAC >> simp[] >- (
      `ALOOKUP ls (s,t) = NONE` by (
        fs[ALOOKUP_FAILS,Abbr`ls`,MEM_MAP,FORALL_PROD] >>
        spose_not_then strip_assume_tac >>
        res_tac >> fs[] >> metis_tac[] ) >>
      simp[] >>
      simp[ALOOKUP_LEAST_EL,find_index_LEAST_EL] >>
      simp[MEM_MAP,MEM_GENLIST,EXISTS_PROD] >>
      simp[MEM_EL] >> rw[] >>
      numLib.LEAST_ELIM_TAC >> conj_tac >- metis_tac[] >> rw[] >>
      numLib.LEAST_ELIM_TAC >> conj_tac >- (
        qexists_tac`n` >> simp[EL_MAP] ) >> rw[] >>
      `¬(n < n')` by metis_tac[] >>
      `¬(n' < n'')` by (
        strip_tac >> res_tac >>
        `n' < LENGTH env` by DECIDE_TAC >>
        fs[EL_MAP] ) >>
      `n'' < LENGTH env` by DECIDE_TAC >>
      fs[EL_MAP] >>
      `¬(n'' < n')` by metis_tac[] >>
      `n' = n''` by DECIDE_TAC >>
      simp[] ) >>
    `ALOOKUP ls (s,t) = SOME (dbterm (k + LENGTH env) [] x)` by (
      fs[ALOOKUP_LEAST_EL,MEM_MAP,EXISTS_PROD,Abbr`ls`] >>
      fs[MEM_EL] >>
      qpat_assum`X = EL n ilist`(assume_tac o SYM) >>
      conj_tac >- metis_tac[dest_var_def] >> rw[] >>
      numLib.LEAST_ELIM_TAC >>
      conj_tac >- ( qexists_tac`n` >> simp[EL_MAP,UNCURRY] ) >>
      rw[] >>
      `¬(n < n')` by (
        strip_tac >>
        first_x_assum(qspec_then`n`mp_tac) >>
        simp[EL_MAP,UNCURRY] ) >>
      `n' < LENGTH ilist` by DECIDE_TAC >>
      fs[EL_MAP,UNCURRY] >>
      numLib.LEAST_ELIM_TAC >>
      conj_tac >- ( qexists_tac`n` >> simp[EL_MAP,UNCURRY] ) >>
      rw[] >>
      `¬(n < n'')` by (
        strip_tac >>
        first_x_assum(qspec_then`n`mp_tac) >>
        simp[EL_MAP,UNCURRY] ) >>
      `n'' < LENGTH ilist` by DECIDE_TAC >>
      fs[EL_MAP,UNCURRY] >>
      `¬(n'' < n')` by (
        strip_tac >>
        last_x_assum(qspec_then`n''`mp_tac) >>
        simp[EL_MAP,UNCURRY] ) >>
      `¬(n' < n'')` by (
        strip_tac >>
        first_x_assum(qspec_then`n'`mp_tac) >>
        simp[EL_MAP,UNCURRY] >>
        `∃x ty. SND (EL n' ilist) = Var x ty` by (
          first_x_assum match_mp_tac >>
          qexists_tac`FST (EL n' ilist)` >>
          qexists_tac`n'` >>
          simp[] ) >>
        fs[] ) >>
      `n' = n''` by DECIDE_TAC >>
      fs[] ) >>
    simp[] >>

    rpt (pop_assum kall_tac) >>
    qid_spec_tac`k` >>
    Induct_on`env` >> simp[] >>
    simp[GENLIST_CONS,combinTheory.o_DEF]

val dbterm_VSUBST = store_thm("dbterm_VSUBST",
  ``∀tm env ilist.
    (∀s s'. MEM (s,s') ilist ⇒
      ∃x ty. s' = Var x ty ∧
             (MEM (x,ty) env ⇒ ∃x'. s = Var x' ty)) ⇒
    dbterm (MAP (λ(x,ty). dest_var(REV_ASSOCD (Var x ty) ilist (Var x ty))) env) (VSUBST ilist tm) =
    dbsubst (FEMPTY |++ (REVERSE (MAP (λ(v,k). (dest_var k,dbterm env v)) ilist))) (dbterm env tm)``,
  Induct >- (
    simp[VSUBST_def] >>
    CONV_TAC(RESORT_FORALL_CONV(List.rev)) >>
    Induct >- (
      simp[REV_ASSOCD,FUPDATE_LIST_THM] >>
      simp[prove(``MAP (λ(x,ty). (x,ty)) env = env``,simp[LIST_EQ_REWRITE,EL_MAP,UNCURRY])]) >>
    Cases >> simp[REV_ASSOCD,FUPDATE_LIST_APPEND,FUPDATE_LIST_THM] >>
    rw[] >- (
      BasicProvers.CASE_TAC >> simp[FLOOKUP_UPDATE] >>
      metis_tac[find_index_NOT_MEM,optionTheory.NOT_SOME_NONE] ) >>
    BasicProvers.CASE_TAC >> simp[FLOOKUP_UPDATE] >- (
      `∃x ty. r = Var x ty` by metis_tac[] >> fs[] >>
      first_x_assum(qspecl_then[`env`,`s`] mp_tac) >>
      (discharge_hyps >- ( simp[] >> metis_tac[] )) >>
      simp[] ) >>
    first_x_assum(qspecl_then[`env`,`s`] mp_tac) >>
    discharge_hyps >- ( simp[] >> metis_tac[] ) >>
    simp[] )
  >- ( simp[VSUBST_def] )
  >- (
    simp[VSUBST_def] >> rw[] >>
    first_x_assum match_mp_tac >>
    metis_tac[] ) >>
  rw[VSUBST_def] >>
  rw[] >- (
    first_x_assum(qspecl_then[`(z,t)::env`,`ilist''`]mp_tac) >>
    discharge_hyps >- (
      fs[Abbr`ilist''`,IN_DISJOINT] >>
      fs[Abbr`ilist'`,MEM_FILTER] >>
      rw[] >- metis_tac[] >>
      fs[MEM_MAP,FORALL_PROD,MEM_FILTER] >>
      Cases_on`x=(s,t)`>>fs[] >- (
        fs[EXISTS_MEM,MEM_FILTER,EXISTS_PROD] >>
        conj_tac >- (
          simp[Abbr`z`] >>
          cheat ) >>
        first_x_assum(qspecl_then[`s`,`t`]mp_tac) >>
        rw[] >>
        first_x_assum(qspecl_then[`Vark
          simp[]


val dbterm_INST_CORE = store_thm("dbterm_INST_CORE",
  ``∀env tyin tm.
      welltyped tm ∧
      (∀s s'. MEM (s,s') env ⇒ ∃x ty. s = Var x ty ∧ s' = Var x (TYPE_SUBST tyin ty)) ∧
      IS_RESULT (INST_CORE env tyin tm)
  ⇒ let bvs = MAP (dest_var o FST) env in
    let bvsi = MAP (dest_var o SND) env in
    (dbterm bvsi (RESULT (INST_CORE env tyin tm)) = dbinst tyin (dbterm bvs tm))``
  ho_match_mp_tac INST_CORE_ind >>
  conj_tac >- (
    simp[INST_CORE_def] >>
    rw[REV_ASSOCD] >>
    qho_match_abbrev_tac`P 0 = Q 0` >>
    qsuff_tac`∀n. P n = Q n`>-rw[]>>
    unabbrev_all_tac >> simp[] >>
    Induct_on`env` >> simp[REV_ASSOCD,find_index_def] >>
    Cases >> simp[REV_ASSOCD] >> rw[] >> fs[] >>
    `∃qq qy. q = Var qq qy` by metis_tac[] >> fs[] >>
    `r = Var qq (TYPE_SUBST tyin qy)` by metis_tac[term_11] >> fs[] >>
    rw[] ) >>
  conj_tac >- (
    simp[INST_CORE_def] ) >>
  conj_tac >- (
    simp[INST_CORE_def] >>
    rw[] >> fs[] >>
    metis_tac[NOT_IS_CLASH_IS_RESULT] ) >>
  simp[INST_CORE_def] >>
  rw[] >> fs[] >- (
    qmatch_assum_abbrev_tac`IS_RESULT (INST_CORE env' tyin tm)` >>
    qspecl_then[`sizeof tm`,`tm`,`env'`,`tyin`]mp_tac INST_CORE_HAS_TYPE >>
    discharge_hyps >- (
      simp[Abbr`env'`] >>
      metis_tac[] ) >>
    `∀X. INST_CORE env' tyin tm ≠ Clash X` by metis_tac[NOT_IS_CLASH_IS_RESULT,IS_CLASH_def] >> fs[] >>
    strip_tac >> fs[] >>
    first_x_assum match_mp_tac >>
    rw[] >> metis_tac[] ) >>
  qmatch_assum_abbrev_tac`¬IS_RESULT (INST_CORE env' tyin tm)` >>
  `∃x. INST_CORE env' tyin tm = Clash x` by (
    Cases_on`INST_CORE env' tyin tm`>>fs[] ) >>
  fs[] >> rw[] >>
  qmatch_assum_abbrev_tac`IS_RESULT (INST_CORE env'' tyin tm')` >>
  `∃r. INST_CORE env'' tyin tm' = Result r` by (
    Cases_on`INST_CORE env'' tyin tm'`>>fs[]) >>
  fs[] >> rw[] >>
  `welltyped tm'` by (
    simp[Abbr`tm'`] >>
    match_mp_tac VSUBST_WELLTYPED >>
    simp[] >> simp[Once has_type_cases] ) >> fs[] >>
  `IS_RESULT (INST_CORE [] tyin tm)` by metis_tac[INST_CORE_NIL_IS_RESULT] >> fs[] >>
  qmatch_assum_abbrev_tac`P ⇒ (Q = R)` >>
  `P` by ( unabbrev_all_tac >> rw[] >> metis_tac[] ) >>
  fs[] >>
  map_every qunabbrev_tac[`Q`,`R`] >>
  ntac 2 (pop_assum kall_tac) >>


val dbterm_INST = store_thm("dbterm_INST",
  ``∀tm tyin. welltyped tm ⇒ (dbterm [] (INST tyin tm) = dbinst tyin (dbterm [] tm))``,
  Induct >- (
    simp[INST_def,INST_CORE_def] >>
    rw[REV_ASSOCD,find_index_def] )
  >- (
    simp[INST_def,INST_CORE_def] )
  >- (
    simp[INST_def,INST_CORE_def] >>
    fs[INST_def] >> rw[] >>
    metis_tac[NOT_IS_CLASH_IS_RESULT,INST_CORE_NIL_IS_RESULT] )
  >- (
    simp[INST_def,INST_CORE_def] >>
    fs[INST_def] >> rw[]
*)

(*
val bv_names_ALL_DISTINCT_exists_RACONV = store_thm("bv_names_ALL_DISTINCT_exists_RACONV"
  ``∀tm env.
      (∀s s'. MEM (s,s') env ⇒ s = s' ∨ ¬VFREE_IN s' tm) ∧
      (∀s s'. MEM (s,s') env ⇒ ∃x x' ty. s = Var x ty ∧ s' = Var x' ty) (* ∧
      ALL_DISTINCT (MAP (FST o dest_var o FST) env) ∧
      ALL_DISTINCT (MAP (FST o dest_var o SND) env)  *)
      ⇒
      ∃tm'. RACONV env (tm,tm')
       ∧ ALL_DISTINCT (bv_names tm)
      (*∧
        ALL_DISTINCT ((MAP (FST o dest_var o FST) env) ++ bv_names tm) ∧
        ALL_DISTINCT ((MAP (FST o dest_var o SND) env) ++ bv_names tm)*) ``,
  Induct >- (
    rw[] >>
    rpt (pop_assum mp_tac) >>
    Induct_on`env` >- (
      simp[] >>
      qexists_tac`Var s t` >>
      simp[RACONV,ALPHAVARS_def] ) >>
    Cases >> rw[] >> fs[] >>
    `∃tm. RACONV env (Var s t,tm)` by metis_tac[] >>
    fs[Once RACONV_cases] >>
    rw[ALPHAVARS_def] >>
    `∃x y. r = Var x y` by metis_tac[] >> fs[] >>
    metis_tac[] )
  >- (
    rw[] >>
    qexists_tac`Const s t c` >>
    rw[RACONV] )
  >- (
    rw[ALL_DISTINCT_APPEND] >>
    last_x_assum(qspec_then`env`mp_tac) >>
    discharge_hyps >- metis_tac[]

    Cases >> simp[] >> rpt strip_tac >>
    fs[] >>
    fs[Once RACONV_cases] >>
    rw[ALPHAVARS_def] >>
    map_every qexists_tac[`ty2`,`x2`] >> rw[] >>
    RACONV
    Cases_on`q = Var s t` >- (
      qexists_tac`r` >> fs[] >>
      first_x_assum(qspecl_then[`q`,`r`]mp_tac) >>
      simp[] >> rw[] >>
      rw[RACONV] >> rw[ALPHAVARS_def] ) >>
    fs[] >>
    qexists_tac`tm'` >>
    qpat_assum`RACONV X Y`mp_tac >>
    simp[Once RACONV_cases] >>
    rw[] >>
    rw[RACONV] >>
    rw[ALPHAVARS_def] >>
    Cases_on`Var s t = Var x2 ty2`>- (
      fs[] >>
      spose_not_then strip_assume_tac >> fs[] >>
      rw[]
    imp_res_
    spose_not_then strip_assume_tac >> fs[] >>
    Cases_on`q=r`>>fs[]
    print_find"ALPHAV"

val bv_names_ALL_DISTINCT_exists = store_thm("bv_names_ALL_DISTINCT_exists",
  ``∀tm ls. ALL_DISTINCT ls ⇒ ∃tm'. ACONV tm tm' ∧ ALL_DISTINCT (ls ++ bv_names tm')``,
  Induct >- (
    simp[ALL_DISTINCT_APPEND] >>
    rw[ACONV_def] >>
    qexists_tac`Var s t`>>rw[RACONV,ALPHAVARS_def] )
  >- (
    rw[ACONV_def] >>
    qexists_tac`Const s t c` >>
    rw[RACONV] )
  >- (
    rw[ACONV_def] >>
    last_x_assum(qspec_then`ls`mp_tac) >> simp[] >>
    disch_then(qx_choose_then`tm1`strip_assume_tac) >>
    last_x_assum(qspec_then`ls ++ bv_names tm1`mp_tac) >> simp[] >>
    disch_then(qx_choose_then`tm2`strip_assume_tac) >>
    qexists_tac`Comb tm1 tm2` >>
    fs[RACONV,ACONV_def])
  >- (
    rw[ACONV_def] >>
    reverse(Cases_on`s ∈ set ls`) >- (
      last_x_assum(qspec_then`ls++[s]`mp_tac) >>
      discharge_hyps >- simp[ALL_DISTINCT_APPEND] >>
      disch_then(qx_choose_then`tm1`strip_assume_tac) >>
      qexists_tac`Abs s t tm1` >>
      fs[ACONV_def,RACONV]
*)


(*
val RACONV_SWAP = store_thm("RACONV_SWAP",
  ``∀tm ty x1 x2. RACONV [Var x1 ty,Var x2 ty] (tm,VSUBST [(Var x2 ty,Var x1 ty)] tm)``
  Induct >- (
    simp[VSUBST_def,RACONV,REV_ASSOCD] >>
    rw[RACONV] >>
    rw[ALPHAVARS_def] >>
    fs[]
    metis_tac[]
      pop_assum mp_tac >>
      map_every qid_spec_tac[`ty1`,`x1`,`t`,`s`,`env`] >>
      Induct >> simp[ALPHAVARS_def] >>
      Cases >> simp[] >> rw[] >>
      Cases_on`q= Var s t`>>fs[]
      metis_tac[]
    ALPHAVARS_MEM
    simp[ALPHAVARS_def]
    rw[ALPHA
RACONV_rules
print_find"VSUBST"

val bv_ALL_DISTINCT_exists = store_thm("bv_ALL_DISTINCT_exists",
  ``∀tm ls. ALL_DISTINCT ls ⇒ ∃tm'. ACONV tm tm' ∧ ALL_DISTINCT (ls ++ bv tm')``,
  Induct >- (
    simp[ALL_DISTINCT_APPEND] >>
    rw[ACONV_def] >>
    qexists_tac`Var s t`>>rw[RACONV,ALPHAVARS_def] )
  >- (
    rw[ACONV_def] >>
    qexists_tac`Const s t c` >>
    rw[RACONV] )
  >- (
    rw[ACONV_def] >>
    last_x_assum(qspec_then`ls`mp_tac) >> simp[] >>
    disch_then(qx_choose_then`tm1`strip_assume_tac) >>
    last_x_assum(qspec_then`ls ++ bv tm1`mp_tac) >> simp[] >>
    disch_then(qx_choose_then`tm2`strip_assume_tac) >>
    qexists_tac`Comb tm1 tm2` >>
    fs[RACONV,ACONV_def])
  >- (
    rw[ACONV_def] >>
    reverse(Cases_on`(s,t) ∈ set ls`) >- (
      last_x_assum(qspec_then`ls++[s,t]`mp_tac) >>
      discharge_hyps >- simp[ALL_DISTINCT_APPEND] >>
      disch_then(qx_choose_then`tm1`strip_assume_tac) >>
      qexists_tac`Abs s t tm1` >>
      fs[ACONV_def,RACONV]

      rw[]
      simp[ALL
      RACONV
      print_find"ACONV"
    last_x_assum(qspec_then`ls`mp_tac) >> simp[] >>

    disch_then(qx_choose_then`tm1`strip_assume_tac) >>
    qexists_tac`Abs s t tm1` >>
    fs[ACONV_def,RACONV]


    rw[ALL_DISTINCT_APPEND]
  print_find"ACONV"
*)

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

(*
val INST_CORE_Clash = store_thm("INST_CORE_Clash",
  ``∀env tyin tm x xty. INST_CORE env tyin tm = Clash (Var x xty) ⇒ ∃ty. xty = TYPE_SUBST tyin ty ∧ VFREE_IN (Var x ty) tm``,
  ho_match_mp_tac INST_CORE_ind >>
  conj_tac >- ( simp[INST_CORE_def] >> rw[]) >>
  conj_tac >- simp[INST_CORE_def] >>
  conj_tac >- ( simp[INST_CORE_def] >> rw[] >> metis_tac[]) >>
  simp[INST_CORE_def] >> rw[] >> fs[]
  >- metis_tac[]
  >- metis_tac[] >>
  fs[VFREE_IN_VSUBST,REV_ASSOCD] >>
  qpat_assum`VFREE_IN X (Y Z)` mp_tac >>
  reverse(rw[] >> fs[])
  >- metis_tac[]
  >- metis_tac[] >>
  qmatch_assum_abbrev_tac`¬IS_RESULT X` >>
  Cases_on`X` >> fs[markerTheory.Abbrev_def] >> rw[] >>
  qexists_tac`ty` >> simp[] >> rfs[] >>
  simp[VFREE_IN_def]
  type_of``VARIANT``
  print_apropos``VARIANT``
  VARIANT_THM
*)

(*
Unfortunately, the conjecture below is probably not true.

Even when restricted to closed terms, simple_inst can behave differently from INST.
Example: simple_inst [α|->t] (λ(x:α). (λ(x:t). (x:α))) = (λx:t. (λx:t. (x:t)))
                INST [α|->t] (λ(x:α). (λ(x:t). (x:α))) = (λx':t. (λ(x:t). (x':t)))

So perhaps we could first rename all bound variables apart then call simple_inst in the semantics.
(Alternatively just assert renaming is always possible by existentially quantifying the α-equivalent term.)

Do free variables make a difference at all?
Yes:     simple_inst [α|->t] (λ(x:t). (x:α)) = (λ(x:t). (x:t))
                INST [α|->t] (λ(x:t). (x:α)) = (λ(x':t). (x:t))

So the restriction to closed terms is necessary.

val INST_CORE_simple_inst = store_thm("INST_CORE_simple_inst",
  ``∀env tyin tm. welltyped tm ∧
      (∀s s'. MEM (s,s') env ⇒ ∃x ty. s = Var x ty ∧ s' = Var x (TYPE_SUBST tyin ty)) ∧
      (∀x ty. VFREE_IN (Var x ty) tm ⇒ REV_ASSOCD (Var x (TYPE_SUBST tyin ty)) env (Var x ty) = Var x ty) ⇒
      INST_CORE env tyin tm = Result(simple_inst tyin tm)``,
  ho_match_mp_tac INST_CORE_ind >>
  conj_tac >- (
    rw[INST_CORE_def] >> rw[] >>
    first_x_assum(qspec_then`ty`strip_assume_tac)>>
    unabbrev_all_tac >> fs[]) >>
  conj_tac >- rw[INST_CORE_def] >>
  conj_tac >- (
    rw[INST_CORE_def] >>
    unabbrev_all_tac >> rw[] >> fs[] >>
    metis_tac[NOT_IS_CLASH_IS_RESULT,IS_RESULT_def,RESULT_eq_suff]) >>
  rpt gen_tac >> strip_tac >> simp[] >> strip_tac >>
  simp_tac std_ss [INST_CORE_def] >>
  Q.PAT_ABBREV_TAC`ty' = TYPE_SUBST tyin ty` >>
  simp_tac std_ss [LET_THM] >>
  qabbrev_tac`env' = (Var x ty, Var x ty')::env` >>
  qabbrev_tac`tres = INST_CORE env' tyin tm` >>
  Q.PAT_ABBREV_TAC`x' = VARIANT X x ty'` >>
  Q.PAT_ABBREV_TAC`env'' = X::env` >> fs[] >>
  qspecl_then[`sizeof tm`,`tm`,`env'`,`tyin`]mp_tac INST_CORE_HAS_TYPE >>
  simp[] >>
  discharge_hyps >- ( simp[Abbr`env'`] >> metis_tac[] ) >>
  qmatch_abbrev_tac`A ∨ B ⇒ C` >>
  qsuff_tac`(A ⇒ C) ∧ (B ⇒ C)` >- (rpt (pop_assum kall_tac) >> PROVE_TAC[]) >>
  reverse conj_tac >- (
    map_every qunabbrev_tac[`A`,`B`,`C`] >>
    strip_tac >>
    `tres = Result (simple_inst tyin tm)` by (
      first_x_assum match_mp_tac >>
      simp[REV_ASSOCD,Abbr`env'`,Abbr`ty'`] >>
      rw[] >> metis_tac[] ) >>
    simp[] ) >>
  map_every qunabbrev_tac[`A`,`B`,`C`] >>
  disch_then(qx_choosel_then[`v`,`vy`]strip_assume_tac) >>
  `CLASH tres = Var x ty'` by (
    simp[] >> pop_assum mp_tac >>
    simp[Abbr`env'`,REV_ASSOCD] >>
    Cases_on`x=v`>>simp[]>>
    Cases_on`ty = vy`>>simp[Abbr`ty'`]>>
    rw[] ) >>
  simp[] >>
*)

(*
val INST_CORE_simple_inst = store_thm("INST_CORE_simple_inst",
  ``∀env tyin tm. welltyped tm ∧
      (∀s s'. MEM (s,s') env ⇒ ∃x ty. s = Var x ty ∧ s' = Var x (TYPE_SUBST tyin ty)) ∧
      (∀x ty. VFREE_IN (Var x ty) tm ⇒ REV_ASSOCD (Var x (TYPE_SUBST tyin ty)) env (Var x ty) = Var x ty) ∧
      ALL_DISTINCT (bv tm) ∧ ALL_DISTINCT (MAP SND env) ⇒
      INST_CORE env tyin tm = Result(simple_inst tyin tm)``,
  ho_match_mp_tac INST_CORE_ind >>
  conj_tac >- ( rw[INST_CORE_def] >> rw[]) >>
  conj_tac >- rw[INST_CORE_def] >>
  conj_tac >- (
    rw[INST_CORE_def] >>
    unabbrev_all_tac >> rw[] >> fs[] >>
    metis_tac[NOT_IS_CLASH_IS_RESULT,IS_RESULT_def,RESULT_eq_suff,ALL_DISTINCT_APPEND]) >>
  rpt gen_tac >> strip_tac >> simp[] >> strip_tac >>
  simp_tac std_ss [INST_CORE_def] >>
  Q.PAT_ABBREV_TAC`ty' = TYPE_SUBST tyin ty` >>
  simp_tac std_ss [LET_THM] >>
  qabbrev_tac`env' = (Var x ty, Var x ty')::env` >>
  qabbrev_tac`tres = INST_CORE env' tyin tm` >>
  Q.PAT_ABBREV_TAC`x' = VARIANT X x ty'` >>
  Q.PAT_ABBREV_TAC`env'' = X::env` >> fs[] >>
  `tres = Result (simple_inst tyin tm)` by (
    first_x_assum match_mp_tac >>
    conj_tac >- metis_tac[] >>
    conj_tac >-(
      qx_genl_tac[`v`,`vy`] >> strip_tac >>
      fs[Abbr`env'`,REV_ASSOCD] >>
      rw[]
      
    qx_gen
  qspecl_then[`sizeof tm`,`tm`,`env'`,`tyin`]mp_tac INST_CORE_HAS_TYPE >>
  simp[] >>
  discharge_hyps >- ( simp[Abbr`env'`] >> metis_tac[] ) >>
  qmatch_abbrev_tac`A ∨ B ⇒ C` >>
  qsuff_tac`(A ⇒ C) ∧ (B ⇒ C)` >- (rpt (pop_assum kall_tac) >> PROVE_TAC[]) >>
  reverse conj_tac >- (
    map_every qunabbrev_tac[`A`,`B`,`C`] >>
*)

val (dbhas_type_rules,dbhas_type_ind,dbhas_type_cases) = Hol_reln`
  (dbhas_type (dbVar n ty) ty) ∧
  (dbhas_type (dbFree s ty) ty) ∧
  (dbhas_type (dbConst s ty g) ty) ∧
  (dbhas_type t1 (Fun dty rty) ∧
   dbhas_type t2 dty
   ⇒
   dbhas_type (dbComb t1 t2) rty) ∧
  (dbhas_type tm rty
   ⇒
   dbhas_type (dbAbs dty tm) (Fun dty rty))`

val dbwelltyped_def = Define`
  dbwelltyped tm = ∃ty. dbhas_type tm ty`

val dbhas_type_dbinst = store_thm("dbhas_type_dbinst",
  ``∀tm ty. dbhas_type tm ty ⇒
      ∀tyin. dbhas_type (dbinst tyin tm) (tyinst tyin ty)``,
  ho_match_mp_tac dbhas_type_ind >>
  conj_tac >- simp[Once dbhas_type_cases,EL_MAP] >>
  conj_tac >- simp[Once dbhas_type_cases] >>
  conj_tac >- simp[Once dbhas_type_cases] >>
  conj_tac >- (
    rw[] >>
    simp[Once dbhas_type_cases] >>
    metis_tac[] ) >>
  rw[] >> simp[Once dbhas_type_cases])

(*
val dbinst_dbhas_type = store_thm("dbinst_dbhas_type",
  ``∀tm tyin env ty.
      dbhas_type (MAP (TYPE_SUBST tyin) env) (dbinst tyin tm) (TYPE_SUBST tyin ty) ⇒
      ∃ty0. dbhas_type env tm ty0 ∧ (TYPE_SUBST tyin ty0 = TYPE_SUBST tyin ty)``,
   Induct >> simp[] >- (
     simp[Once dbhas_type_cases] >>
     simp[Once dbhas_type_cases] )
   >- (
     simp[Once dbhas_type_cases] >>
     simp[Once dbhas_type_cases] >>
     simp[EL_MAP] )
   >- (
     simp[Once dbhas_type_cases] >>
     simp[Once dbhas_type_cases] )
   >- (
     simp[Once dbhas_type_cases] >>
     rw[] >>
     simp[Once dbhas_type_cases] >>
     last_x_assum(qspecl_then[`tyin`,`env`,`dty`]mp_tac)
     metis_tac[TYPE_SUBST_def]
     res_tac
     )
*)

val dbhas_type_dbterm = store_thm("dbhas_type_dbterm",
  ``∀tm env ty. tm has_type ty ⇔ dbhas_type (dbterm env tm) ty``,
  Induct >- (
    simp[Once has_type_cases] >>
    rw[EQ_IMP_THM] >- (
      BasicProvers.CASE_TAC >- (
        simp[Once dbhas_type_cases] ) >>
      simp[Once dbhas_type_cases] ) >>
    pop_assum mp_tac >>
    BasicProvers.CASE_TAC >>
    simp[Once dbhas_type_cases] )
  >- rw[Once dbhas_type_cases,Once has_type_cases]
  >- (
    rw[] >>
    rw[Once dbhas_type_cases] >>
    rw[Once has_type_cases] >>
    metis_tac[] ) >>
  rw[Once dbhas_type_cases] >>
  rw[Once has_type_cases] >>
  rw[EQ_IMP_THM] >>
  metis_tac[SND,MAP])

val dbtvars_def = Define`
  dbtvars (dbFree _ ty) = tyvars ty ∧
  dbtvars (dbVar _ ty) = tyvars ty ∧
  dbtvars (dbConst _ ty _) = tyvars ty ∧
  dbtvars (dbComb t1 t2) = LIST_UNION (dbtvars t1) (dbtvars t2) ∧
  dbtvars (dbAbs ty t) = LIST_UNION (tyvars ty) (dbtvars t)`
val _ = export_rewrites["dbtvars_def"]

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

val dbinst_tvars = store_thm("dbinst_tvars",
  ``∀tm tyin tyin'. (∀v. MEM v (dbtvars tm) ⇒ FLOOKUPD tyin' v (Tyvar v) = FLOOKUPD tyin v (Tyvar v)) ⇒
       dbinst tyin tm = dbinst tyin' tm``,
  Induct >- ( simp[] >> metis_tac[tyinst_tyvars] )
  >- (simp[] >> metis_tac[tyinst_tyvars])
  >- (simp[] >> metis_tac[tyinst_tyvars])
  >- ( simp[] >> simp[MEM_LIST_UNION] ) >>
  rw[MEM_LIST_UNION] >>
  metis_tac[tyinst_tyvars])

val dbtvars_dbterm = store_thm("dbtvars_dbterm",
  ``∀tm env. set (dbtvars (dbterm env tm)) = set (tvars tm)``,
  Induct >- (
    simp[] >> rw[] >>
    BasicProvers.CASE_TAC >> simp[] >>
    simp[tvars_def] )
  >- simp[tvars_def]
  >- (
    simp[tvars_def] >>
    fs[SUBSET_DEF,MEM_LIST_UNION,MEM_FLAT,MEM_MAP,EXISTS_PROD] >>
    metis_tac[] ) >>
  rw[tvars_def] >>
  fs[SUBSET_DEF,MEM_LIST_UNION,MEM_FLAT,MEM_MAP,EXISTS_PROD] >> rw[] >>
  res_tac >> fs[] >>
  metis_tac[])

val dbhas_type_11 = store_thm("dbhas_type_11",
  ``∀tm ty. dbhas_type tm ty ⇒ ∀ty'. dbhas_type tm ty' ⇒ ty' = ty``,
  ho_match_mp_tac dbhas_type_ind >>
  rpt conj_tac >>
  rpt gen_tac >> TRY strip_tac >>
  simp[Once dbhas_type_cases] >>
  TRY ( rw[] >> res_tac >> fs[] >> NO_TAC) >>
  TRY (pop_assum mp_tac >> simp[Once dbhas_type_cases]>> NO_TAC))

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

val (semantics_rules,semantics_ind,semantics_cases) = xHol_reln"semantics"`
  (FLOOKUP τ s = SOME m ⇒ typeset τ (Tyvar s) m) ∧

  (typeset τ (Tyapp (Typrim "bool" 0) []) boolset) ∧

  (typeset τ x mx ∧ typeset τ y my
   ⇒
   typeset τ (Tyapp (Typrim "->" 2) [x;y]) (funspace mx my)) ∧

  (LENGTH (tvars p) = LENGTH args ∧
   tyin = alist_to_fmap(ZIP (tvars p, args)) ∧
   dbhas_type (dbterm [] p) (Fun rty Bool) ∧
   typeset FEMPTY (tyinst tyin rty) mrty ∧
   semantics [] FEMPTY FEMPTY (dbinst tyin (dbterm [] p)) mp ∧
   w <: mrty ∧ holds mp w
   ⇒
   typeset τ (Tyapp (Tydefined op p) args) (mrty suchthat holds mp)) ∧

  (FLOOKUP σ (s,ty) = SOME m
   ⇒
   semantics env σ τ (dbFree s ty) m) ∧

  (n < LENGTH env ∧ EL n env = (ty,m)
   ⇒
   semantics env σ τ (dbVar n ty) m) ∧

  (typeset τ ty mty
   ⇒
   semantics env σ τ (dbConst "=" (Fun ty (Fun ty Bool)) Prim)
    (abstract mty (funspace mty boolset)
       (λx. abstract mty boolset (λy. boolean (x = y))))) ∧

  (typeset τ ty mty
   ⇒
   semantics env σ τ (dbConst "@" (Fun (Fun ty Bool) ty) Prim)
     (abstract (funspace mty boolset) mty
       (λp. let mp = (mty suchthat holds p) in
            ch (if ∃x. x <: mp then mp else mty)))) ∧

  (welltyped t ∧ closed t ∧
   set(tvars t) ⊆ set (tyvars (typeof t)) ∧
   dbhas_type (dbterm [] t) ty0 ∧ tyinst tyin ty0 = ty ∧
   semantics [] FEMPTY FEMPTY (dbinst tyin (dbterm [] t)) mt
   ⇒
   semantics env σ τ (dbConst s ty (Defined t)) mt) ∧

  (typeset τ (Tyapp (Tydefined op p) args) maty ∧
   tyin = alist_to_fmap(ZIP (tvars p, args)) ∧
   dbhas_type (dbinst tyin (dbterm [] p)) (Fun rty Bool) ∧
   typeset FEMPTY rty mrty
   ⇒
   semantics env σ τ (dbConst s (Fun (Tyapp (Tydefined op p) args) rty) (Tyrep op p))
    (abstract maty mrty (λx. x))) ∧

  (typeset τ (Tyapp (Tydefined op p) args) maty ∧
   tyin = alist_to_fmap(ZIP (tvars p, args)) ∧
   dbhas_type (dbinst tyin (dbterm [] p)) (Fun rty Bool) ∧
   typeset FEMPTY rty mrty ∧
   semantics [] FEMPTY FEMPTY (dbinst tyin (dbterm [] p)) mp
   ⇒
   semantics env σ τ (dbConst s (Fun rty (Tyapp (Tydefined op p) args)) (Tyabs op p))
    (abstract mrty maty (λx. if holds mp x then x else ch maty))) ∧

  (semantics env σ τ t1 m1 ∧
   semantics env σ τ t2 m2 ∧
   dbwelltyped (dbComb t1 t2)
   ⇒
   semantics env σ τ (dbComb t1 t2) (apply m1 m2)) ∧

  (typeset τ ty mty ∧
   dbhas_type b tyb ∧
   typeset τ tyb mtyb ∧
   (∀x. x <: mty ⇒ (mb x) <: mtyb ∧ semantics ((ty,x)::env) σ τ b (mb x))
   ⇒
   semantics env σ τ (dbAbs ty b) (abstract mty mtyb mb))`

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

val good_env_def = Define`
  good_env τ env = EVERY (λ(ty,m). ∃mty. typeset τ ty mty ∧ m <: mty) env`

val good_env_nil = store_thm("good_env_nil",
  ``good_env τ []``,
  rw[good_env_def])
val _ = export_rewrites["good_env_nil"]

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
    (∀env σ τ t mt. semantics env σ τ t mt ⇒
        ∀mt'. type_valuation τ ∧ semantics env σ τ t mt' ⇒ mt' = mt)``,
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
    `Fun rty Bool = Fun rty' Bool` by (
      metis_tac[dbhas_type_dbterm,MAP,WELLTYPED_LEMMA] ) >>
    fs[] ) >>
  conj_tac >- simp[Once semantics_cases] >>
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
    `ty0' = ty0 ∧ ty0 = typeof t` by metis_tac[dbhas_type_dbterm,MAP,WELLTYPED_LEMMA] >> rw[] >>
    `dbinst tyin (dbterm [] t) = dbinst tyin' (dbterm [] t)` by (
      match_mp_tac dbinst_tvars >>
      simp[SIMP_RULE(srw_ss())[EXTENSION]dbtvars_dbterm] >>
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
  imp_res_tac dbhas_type_11 >>
  rw[] >>
  match_mp_tac ABSTRACT_EQ >>
  conj_tac >- metis_tac[typeset_inhabited] >>
  fs[] >> res_tac >> fs[])

val typeset_tyvars = prove(
  ``(∀τ1 ty m. typeset τ1 ty m ⇒ ∀τ2. (∀x. x ∈ set(tyvars ty) ⇒ FLOOKUP τ1 x = FLOOKUP τ2 x) ⇒ typeset τ2 ty m) ∧
    (∀env σ τ tm m. semantics env σ τ tm m ⇒ T)``,
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

val dbtvars_dbinst = store_thm("dbtvars_dbinst",
  ``∀tm tyin. set (dbtvars (dbinst tyin tm)) = {v | ∃x. MEM x (dbtvars tm) ∧ MEM v (tyvars (FLOOKUPD tyin x (Tyvar x)))}``,
  Induct >> simp[tyvars_tyinst] >>
  fs[EXTENSION] >> metis_tac[] )

val typeset_closes_over = store_thm("typeset_closes_over",
  ``(∀τ ty m. typeset τ ty m ⇒ set (tyvars ty) ⊆ FDOM τ) ∧
    (∀env σ τ tm m. semantics env σ τ tm m ⇒
      type_valuation τ ∧ (∀s m ty. (s,ty) ∈ FDOM σ ∨ MEM (ty,m) env ⇒ set (tyvars ty) ⊆ FDOM τ)
      ⇒ set (dbtvars tm) ⊆ FDOM τ)``,
  ho_match_mp_tac (theorem"semantics_strongind") >>
  simp[tyvars_def] >>
  conj_tac >- ( rw[Once semantics_cases,FLOOKUP_DEF] ) >>
  conj_tac >- (
    rpt gen_tac >> strip_tac >>
    fs[SUBSET_DEF,MEM_LIST_UNION,MEM_FOLDR_LIST_UNION,EVERY_MEM] >>
    fs[SIMP_RULE std_ss[EXTENSION]tyvars_tyinst] >>
    fs[GSYM LEFT_FORALL_IMP_THM] >> rw[] >>
    qmatch_assum_abbrev_tac`dbtvars (dbinst tyin tm) = []` >>
    qspecl_then[`tm`,`tyin`]mp_tac dbtvars_dbinst >>
    simp[EXTENSION,PROVE[]``¬P ∨ ¬Q ⇔ Q ⇒ ¬P``] >>
    rw[] >>
    `∃n. n < LENGTH args ∧ y = EL n args` by metis_tac[MEM_EL] >>
    first_x_assum(qspecl_then[`x`,`EL n (tvars p)`]mp_tac) >>
    discharge_hyps >- (
      simp[FLOOKUPD_def,Abbr`tyin`] >>
      BasicProvers.CASE_TAC >- (
        fs[ALOOKUP_FAILS] >>
        rfs[MEM_ZIP] >>
        metis_tac[] ) >>
      Q.ISPECL_THEN[`ZIP(tvars p,args)`,`n`]mp_tac ALOOKUP_ALL_DISTINCT_EL >>
      discharge_hyps >- simp[MAP_ZIP] >> rw[EL_ZIP] ) >>
    qspecl_then[`p`,`[]`]mp_tac dbtvars_dbterm >>
    simp[EXTENSION] >>
    metis_tac[MEM_EL] ) >>
  conj_tac >- (
    rw[FLOOKUP_DEF] >>
    metis_tac[] ) >>
  conj_tac >- (
    rw[MEM_EL] >>
    metis_tac[] ) >>
  conj_tac >- (
    rw[tyvars_tyinst,SUBSET_DEF] >>
    qmatch_assum_abbrev_tac`dbtvars (dbinst tyin tm) = []` >>
    qspecl_then[`tm`,`tyin`]mp_tac dbtvars_dbinst >>
    simp[EXTENSION,PROVE[]``¬P ∨ ¬Q ⇔ Q ⇒ ¬P``] >>
    qmatch_assum_rename_tac`MEM x (tyvars (FLOOKUPD tyin y (Tyvar y)))`[] >>
    disch_then(qspecl_then[`x`,`y`]mp_tac) >>
    rw[Abbr`tm`,dbtvars_dbterm] >>
    metis_tac[tyvars_typeof_subset_tvars,dbhas_type_dbterm,MAP,SUBSET_DEF] ) >>
  conj_tac >- ( rw[] >> metis_tac[] ) >>
  rw[] >> metis_tac[typeset_inhabited])

val semantics_typeset = store_thm("semantics_typeset",
  ``(∀τ ty mty. typeset τ ty mty ⇒ type_valuation τ ⇒ ∃mt. mt <: mty) ∧
    (∀env σ τ t mt. semantics env σ τ t mt ⇒
        type_valuation τ ∧ term_valuation τ σ ∧ good_env τ env ⇒
           ∃ty mty. dbhas_type t ty ∧ typeset τ ty mty ∧ mt <: mty)``,
  ho_match_mp_tac (theorem"semantics_strongind") >>
  simp[INDSET_INHABITED,FUNSPACE_INHABITED] >>
  conj_tac >- (
    simp[type_valuation_def] >>
    simp[FLOOKUP_DEF,FRANGE_DEF] >>
    metis_tac[] ) >>
  conj_tac >- metis_tac[BOOLEAN_IN_BOOLSET] >>
  conj_tac >- ( rw[suchthat_def] >> metis_tac[] ) >>
  conj_tac >- (
    simp[Once dbhas_type_cases] >> rw[] >>
    fs[term_valuation_def] >>
    imp_res_tac FEVERY_FLOOKUP >>
    fs[] >> metis_tac[]) >>
  conj_tac >- (
    simp[Once dbhas_type_cases,good_env_def,EVERY_MEM,MEM_EL,FORALL_PROD,EL_MAP] >>
    metis_tac[FST,SND,pair_CASES] ) >>
  conj_tac >- (
    rw[Once dbhas_type_cases] >>
    rw[Once semantics_cases] >>
    rw[Once (Q.SPECL[`τ`,`Fun X Y`](CONJUNCT1 semantics_cases))] >>
    fsrw_tac[DNF_ss][] >>
    rpt(qexists_tac`mty`)>>simp[]>>
    match_mp_tac ABSTRACT_IN_FUNSPACE >> rw[] >>
    match_mp_tac ABSTRACT_IN_FUNSPACE >> rw[] >>
    metis_tac[BOOLEAN_IN_BOOLSET] ) >>
  conj_tac >- (
    rw[Once dbhas_type_cases] >>
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
    rw[Once dbhas_type_cases] >>
    qspecl_then[`dbterm [] t`,`ty0`]mp_tac dbhas_type_dbinst >> simp[] >>
    disch_then(qspec_then`tyin`strip_assume_tac) >>
    imp_res_tac dbhas_type_11 >> rw[] >>
    imp_res_tac(CONJUNCT1 typeset_closes_over) >> fs[] >>
    metis_tac[typeset_tyvars,MEM]) >>
  conj_tac >- (
    rw[] >>
    rw[Once dbhas_type_cases] >>
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

(*
semantics_bvs to change the env?
would need dbwelltyped to allow env change too
*)

val tyvars_subset_dbtvars = store_thm("tyvars_subset_dbtvars",
  ``∀tm ty. dbhas_type tm ty ⇒ set (tyvars ty) ⊆ set (dbtvars tm)``,
  ho_match_mp_tac dbhas_type_ind >>
  simp[] >>
  simp[SUBSET_DEF,MEM_LIST_UNION,tyvars_def,MEM_FLAT,MEM_MAP] >>
  metis_tac[MEM_EL])

val closes_def = Define`
  closes env σ τ t ⇔
    set (dbtvars t) ⊆ FDOM τ ∧
    set (FLAT (MAP (tyvars o FST) env)) ⊆ FDOM τ ∧
    set (dbfv t) ⊆ FDOM σ ∧
    (∀n ty. MEM (n,ty) (dbbv t) ⇒ n < LENGTH env ∧ FST (EL n env) = ty)`

val semantics_closes = prove(
  ``(∀τ ty m. typeset τ ty m ⇒ T) ∧
    (∀env σ τ t m. semantics env σ τ t m ⇒ type_valuation τ ∧ term_valuation τ σ ∧ good_env τ env ⇒ closes env σ τ t)``,
  ho_match_mp_tac(theorem"semantics_strongind") >> simp[] >>
  conj_tac >- (
    simp[Once semantics_cases,FLOOKUP_DEF,closes_def] >>
    simp[term_valuation_def,FEVERY_DEF,FORALL_PROD] >>
    rw[] >- metis_tac[typeset_closes_over] >>
    fs[good_env_def,SUBSET_DEF,MEM_FLAT,MEM_MAP,EXISTS_PROD,EVERY_MEM,FORALL_PROD] >>
    rw[] >> metis_tac[typeset_closes_over,SUBSET_DEF]) >>
  conj_tac >- (
    simp[Once semantics_cases,FLOOKUP_DEF,closes_def] >>
    rw[good_env_def,EVERY_MEM,SUBSET_DEF,MEM_FLAT,MEM_MAP,EXISTS_PROD,FORALL_PROD] >>
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
    fsrw_tac[DNF_ss][SUBSET_DEF,MEM_MAP,MEM_FILTER] >>
    fs[good_env_def,EVERY_MEM,SUBSET_DEF,MEM_FLAT,MEM_MAP,EXISTS_PROD,FORALL_PROD] >>
    conj_tac >> CONV_TAC SWAP_FORALL_CONV >> Cases >> simp[] >> rw[] >> res_tac >> fs[]))
val semantics_closes = save_thm("semantics_closes",MP_CANON (CONJUNCT2 semantics_closes))

(*
val closes_extend = store_thm("closes_extend",
  ``∀env σ τ t env' σ' τ'. closes env σ τ t ∧ σ ⊑ σ' ∧ env ≼ env' ∧ τ ⊑ τ' ⇒ closes env' σ' τ' t``,
  rw[SUBMAP_DEF,closes_def,SUBSET_DEF] >>
  imp_res_tac rich_listTheory.IS_PREFIX_LENGTH >>
  fs[rich_listTheory.IS_PREFIX_APPEND] >> rw[] >>
  fs[] >> res_tac >> simp[] >>
*)

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

(*
val term_valuation_reduce = store_thm("term_valuation_reduce",
  ``∀τ σ σ'. term_valuation τ σ' ∧ σ ⊑ σ' ⇒ term_valuation τ σ``,
  metis_tac[term_valuation_def,FEVERY_SUBMAP])

val semantics_extend_term_valuation = store_thm("semantics_extend_term_valuation",
  ``∀σ τ t m σ'. type_valuation τ ∧ term_valuation τ σ' ∧
                 semantics σ τ t m ∧ σ ⊑ σ'
                 ⇒ semantics σ' τ t m``,
  rw[] >>
  imp_res_tac term_valuation_reduce >>
  `welltyped t` by metis_tac[semantics_typeset] >>
  `σ closes_over t` by metis_tac[semantics_closes_over] >>
  qsuff_tac`semantics σ' τ t = semantics σ τ t`>-rw[] >>
  match_mp_tac semantics_vfree_in >> simp[] >>
  fs[SUBMAP_DEF,FLOOKUP_DEF])

val semantics_reduce_term_valuation = store_thm("semantics_reduce_term_valuation",
  ``∀σ τ t m σ'. type_valuation τ ∧ term_valuation τ σ' ∧
                 semantics σ' τ t m ∧ σ ⊑ σ' ∧
                 σ closes_over t
                 ⇒ semantics σ τ t m``,
  rw[] >>
  imp_res_tac term_valuation_reduce >>
  `welltyped t` by metis_tac[semantics_typeset] >>
  qsuff_tac`semantics σ τ t = semantics σ' τ t`>-rw[] >>
  match_mp_tac semantics_vfree_in >> simp[] >>
  fs[SUBMAP_DEF,FLOOKUP_DEF])
*)

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
  ``∀τ ty. ∃τ'. τ ⊑ τ' ∧ set (tyvars ty) ⊆ FDOM τ' ∧ (type_valuation τ ⇒ type_valuation τ')``,
  qsuff_tac`∀s:string set. FINITE s ⇒ ∀τ. ∃τ'. τ ⊑ τ' ∧ s ⊆ FDOM τ' ∧ (type_valuation τ ⇒ type_valuation τ')`
    >- metis_tac[FINITE_LIST_TO_SET] >>
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
  metis_tac[covering_type_valuation_exists,typeset_reduce,SUBMAP_DEF,SUBSET_DEF])
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
  has_meaning t =
    ∀τ σ env. type_valuation τ ∧
              term_valuation τ σ ∧
              good_env τ env ∧
              closes env σ τ t
            ⇒ ∃m. semantics env σ τ t m`

val closes_dbComb = store_thm("closes_dbComb",
  ``∀env σ τ t1 t2. closes env σ τ (dbComb t1 t2) ⇔ closes env σ τ t1 ∧ closes env σ τ t2``,
  rw[closes_def] >> metis_tac[])
val _ = export_rewrites["closes_dbComb"]

(*
val closes_dbAbs = store_thm("closes_dbAbs",
  ``∀env σ τ ty tm. closes env σ τ (dbAbs ty tm) ⇔ set (tyvars ty) ⊆ FDOM τ ∧ ∃e. closes (e::env) σ τ tm``,
  rw[closes_def,SUBSET_DEF,MEM_MAP,MEM_FILTER,GSYM LEFT_FORALL_IMP_THM] >>
  rw[EQ_IMP_THM] >> res_tac >>
  rw[EXISTS_PROD] >> TRY (qexists_tac`ty`) >> rw[] >>
  res_tac >> DECIDE_TAC)
val _ = export_rewrites["closes_dbAbs"]

val closes_dbConst = store_thm("closes_dbConst",
  ``∀env σ τ s ty c. closes env σ τ (dbConst s ty c) ⇔ set (tyvars ty) ⊆ FDOM τ ∧ set (FLAT (MAP (tyvars o FST) env)) ⊆ FDOM τ``,
  rw[closes_def])
val _ = export_rewrites["closes_dbConst"]

val closes_dbFree = store_thm("closes_dbFree",
  ``∀env σ τ s ty. closes env σ τ (dbFree s ty) ⇔ set (tyvars ty) ⊆ FDOM τ ∧ set (FLAT (MAP (tyvars o FST) env)) ⊆ FDOM τ ∧ (s,ty) ∈ FDOM σ``,
  rw[closes_def])
val _ = export_rewrites["closes_dbFree"]

val closes_dbVar = store_thm("closes_dbVar",
  ``∀env σ τ n. closes env σ τ (dbVar n) ⇔ set (FLAT (MAP (tyvars o FST) env)) ⊆ FDOM τ ∧ n < LENGTH env``,
  rw[closes_def])
val _ = export_rewrites["closes_dbVar"]

val closes_dbeq = store_thm("closes_dbeq",
  ``(dbhas_type (MAP FST env) l ty) ∧
    (dbhas_type (MAP FST env) r ty)	⇒
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
  ``∀τ env t. ∃env'. env ≼ env' ∧ set (dbbv t) ⊆ count (LENGTH env') ∧ (good_env τ env ⇒ good_env τ env')`` ,
  qsuff_tac`∀s:num set. FINITE s ⇒
    ∀τ env. ∃env'. env ≼ env' ∧ s ⊆ count (LENGTH env') ∧ (good_env τ env ⇒ good_env τ env')`
    >- metis_tac[FINITE_LIST_TO_SET] >>
  ho_match_mp_tac FINITE_INDUCT >>
  rw[] >- metis_tac[rich_listTheory.IS_PREFIX_REFL] >>
  first_x_assum(qspecl_then[`τ`,`env`]strip_assume_tac) >>
  Cases_on`e < LENGTH env'` >- metis_tac[rich_listTheory.IS_PREFIX_REFL] >>
  qexists_tac`env'++(REPLICATE (SUC (e - LENGTH env')) (Bool,boolean F))` >>
  rw[rich_listTheory.IS_PREFIX_APPEND,rich_listTheory.LENGTH_REPLICATE]
  >- fs[rich_listTheory.IS_PREFIX_APPEND]
  >- simp[]
  >- (simp[] >> fs[SUBSET_DEF] >> rw[] >> res_tac >> simp[] ) >>
  Q.ISPECL_THEN[`Bool,boolean F`,`SUC(e-LENGTH env')`]strip_assume_tac rich_listTheory.EVERY_REPLICATE >>
  fs[good_env_def,EVERY_MEM] >> rw[] >> res_tac >> rw[] >> rw[BOOLEAN_IN_BOOLSET])
*)

(*
not true: ((dbVar 0) (dbFree "x" a)) has semantics when env = [Fun a b],
          but not when env = [a].
          so, should has_meaning have welltyped in the precondition?
          should dbVars carry types?
val semantics_has_meaning = prove(
  ``(∀τ ty m. typeset τ ty m ⇒ T) ∧
    (∀env σ τ t m. semantics env σ τ t m ⇒ has_meaning t)``,
  ho_match_mp_tac (theorem"semantics_strongind") >> simp[] >>
  conj_tac >- (
    simp[has_meaning_def,Once semantics_cases] >> rw[FLOOKUP_DEF] ) >>
  conj_tac >- (
    rw[has_meaning_def,Once semantics_cases] ) >>
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
    first_x_assum(qspecl_then[`τ'`,`σ'`,`env'`]mp_tac) >> rw[] >>
    first_x_assum(qspecl_then[`τ'`,`σ'`,`env'`]mp_tac) >> rw[] >>
    HINT_EXISTS_TAC >> rw[] >>
    qexists_tac`m''`>>rw[] >>

    dbhas_type_11
    closes_def
    dbhas_type_cases
    fs[dbwelltyped_def] >>
    fs[Once dbhas_type_cases] >>
    qspecl_then[`env'`,`σ'`,`τ'`,`t`,`m'''`]mp_tac (CONJUNCT2 semantics_typeset) >>
    qspecl_then[`env'`,`σ'`,`τ'`,`t'`,`m''`]mp_tac (CONJUNCT2 semantics_typeset) >>
    rw[] >>
    imp_res_tac typeset_has_meaning >>
    fs[type_has_meaning_def]
    type_has_meaning_def
    type_has_meaning_Fun
*)

(*
val has_meaning_welltyped = store_thm("has_meaning_welltyped",
  ``∀t. has_meaning t ⇒ ∃env. dbwelltyped env t``,
  rw[has_meaning_def] >>
  semantics_typeset
  metis_tac[a_type_valuation_exists,semantics_typeset
           ,term_valuation_def,CONJUNCT1 FEVERY_STRENGTHEN_THM
           ,SUBMAP_FEMPTY])
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

val has_meaning_Var = store_thm("has_meaning_Var",
  ``∀x ty. has_meaning (Var x ty) ⇔ type_has_meaning ty``,
  rw[type_has_meaning_def,has_meaning_def] >>
  simp[Once semantics_cases,FLOOKUP_DEF] >>
  rw[EQ_IMP_THM] >- (
    first_x_assum(qspecl_then[`τ`,`FEMPTY`]mp_tac) >>
    simp[SUBMAP_FEMPTY] >>
    simp[term_valuation_def,FEVERY_DEF,FORALL_PROD] >>
    metis_tac[] ) >>
  Cases_on`(x,ty) ∈ FDOM σ`>-metis_tac[SUBMAP_REFL] >>
  `∃mty. typeset τ ty mty` by metis_tac[] >>
  `∃m. m <: mty` by metis_tac[typeset_inhabited] >>
  qexists_tac`σ |+ ((x,ty),m)` >>
  simp[] >>
  metis_tac[term_valuation_FUPDATE,FST,SND])

val has_meaning_Comb = store_thm("has_meaning_Comb",
  ``∀s t. has_meaning (Comb s t) ⇔ has_meaning s ∧ has_meaning t ∧ welltyped (Comb s t)``,
  rw[] >> EQ_TAC >> strip_tac >- (
    imp_res_tac has_meaning_welltyped >>
    fs[WELLTYPED_CLAUSES] >>
    fs[has_meaning_def] >>
    simp[GSYM FORALL_AND_THM,GSYM IMP_CONJ_THM] >>
    rpt gen_tac >> strip_tac >>
    first_x_assum(qspecl_then[`τ`,`σ`]mp_tac) >>
    simp[] >> strip_tac >>
    fs[Once (Q.SPECL[`X`,`Y`,`COMB A B`](CONJUNCT2 semantics_cases))] >>
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

val _ = export_theory()
