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

val _ = Hol_datatype`
  dbterm = dbFree of string => type
         | dbVar of num
         | dbConst of string => type => const_tag
         | dbComb of dbterm => dbterm
         | dbAbs of type => dbterm`

val dbterm_def = Define`
  (dbterm k env (Var s ty) =
     case find_index (s,ty) env k of SOME n => dbVar n | NONE => dbFree s ty) ∧
  (dbterm k env (Const s ty g) = dbConst s ty g) ∧
  (dbterm k env (Comb t1 t2) = dbComb (dbterm k env t1) (dbterm k env t2)) ∧
  (dbterm k env (Abs x ty t) = dbAbs ty (dbterm k ((x,ty)::env) t))`
val _ = export_rewrites["dbterm_def"]

val dbinst_def = Define`
  dbinst tyin (dbFree x ty) = dbFree x (TYPE_SUBST tyin ty) ∧
  dbinst tyin (dbVar n) = dbVar n ∧
  dbinst tyin (dbConst x ty g) = dbConst x (TYPE_SUBST tyin ty) g ∧
  dbinst tyin (dbComb s t) = dbComb (dbinst tyin s) (dbinst tyin t) ∧
  dbinst tyin (dbAbs ty t) = dbAbs (TYPE_SUBST tyin ty) (dbinst tyin t)`
val _ = export_rewrites["dbinst_def"]

val dbsubst_def = Define`
  (dbsubst σ (dbFree s ty) =
     case FLOOKUP σ (s,ty) of SOME tm => tm | NONE => dbFree s ty) ∧
  (dbsubst σ (dbVar n) = dbVar n) ∧
  (dbsubst σ (dbConst s ty g) = dbConst s ty g) ∧
  (dbsubst σ (dbComb t1 t2) = dbComb (dbsubst σ t1) (dbsubst σ t2)) ∧
  (dbsubst σ (dbAbs ty tm) = dbAbs ty (dbsubst σ tm))`
val _ = export_rewrites["dbsubst_def"]

val dbsubst_FEMPTY = store_thm("dbsubst_FEMPTY",
  ``∀tm. dbsubst FEMPTY tm = tm``,
  Induct >> simp[])
val _ = export_rewrites["dbsubst_FEMPTY"]

val REV_ASSOCD_ALOOKUP = store_thm("REV_ASSOCD_ALOOKUP",
  ``∀ls x d. REV_ASSOCD x ls d = case ALOOKUP (MAP (λ(x,y). (y,x)) ls) x of NONE => d | SOME y => y``,
  Induct >> simp[REV_ASSOCD] >>
  Cases >> simp[REV_ASSOCD] >> rw[])

val dbsubst_dbsubst = store_thm("dbsubst_dbsubst",
  ``∀tm σ1 σ2. dbsubst σ2 (dbsubst σ1 tm) = dbsubst ((dbsubst σ2 o_f σ1) ⊌ σ2) tm``,
  Induct >- (
    simp[FLOOKUP_FUNION,FLOOKUP_o_f] >> rw[] >>
    BasicProvers.CASE_TAC >>
    BasicProvers.CASE_TAC >>
    simp[] ) >> simp[])

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

val (semantics_rules,semantics_ind,semantics_cases) = xHol_reln"semantics"`
  (FLOOKUP τ s = SOME m ⇒ typeset τ (Tyvar s) m) ∧

  (typeset τ (Tyapp (Typrim "bool" 0) []) boolset) ∧

  (typeset τ x mx ∧ typeset τ y my
   ⇒
   typeset τ (Tyapp (Typrim "->" 2) [x;y]) (funspace mx my)) ∧

  (LENGTH (tvars p) = LENGTH args ∧
   tyin = ZIP (args, MAP Tyvar (STRING_SORT (tvars p))) ∧
   semantics FEMPTY FEMPTY (INST tyin p) mp ∧ w <: mrty ∧ holds mp w ∧
   INST tyin p has_type Fun rty Bool ∧ typeset τ rty mrty
   ⇒
   typeset τ (Tyapp (Tydefined op p) args) (mrty suchthat holds mp)) ∧

  (FLOOKUP σ (n,ty) = SOME m
   ⇒
   semantics σ τ (Var n ty) m) ∧

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

  (welltyped t ∧ closed t ∧
   set(tvars t) ⊆ set (tyvars (typeof t)) ∧
   INST tyin t has_type ty ∧
   semantics FEMPTY FEMPTY (INST tyin t) mt
   ⇒
   semantics σ τ (Const s ty (Defined t)) mt) ∧

  (typeset τ (Tyapp (Tydefined op p) args) maty ∧
   tyin = ZIP(args, MAP Tyvar (STRING_SORT (tvars p))) ∧
   INST tyin p has_type Fun rty Bool ∧ typeset τ rty mrty
   ⇒
   semantics σ τ (Const s (Fun (Tyapp (Tydefined op p) args) rty) (Tyrep op p))
    (abstract maty mrty (λx. x))) ∧

  (typeset τ (Tyapp (Tydefined op p) args) maty ∧
   tyin = ZIP(args, MAP Tyvar (STRING_SORT (tvars p))) ∧
   INST tyin p has_type Fun rty Bool ∧ typeset τ rty mrty ∧
   semantics FEMPTY FEMPTY (INST tyin p) mp
   ⇒
   semantics σ τ (Const s (Fun rty (Tyapp (Tydefined op p) args)) (Tyabs op p))
    (abstract mrty maty (λx. if holds mp x then x else ch maty))) ∧

  (semantics σ τ t mt ∧
   semantics σ τ u mu ∧
   welltyped (Comb t u)
   ⇒
   semantics σ τ (Comb t u) (apply mt mu)) ∧

  (typeset τ ty mty ∧
   b has_type tyb ∧
   typeset τ tyb mtyb ∧
   (∀x. x <: mty ⇒ (mb x) <: mtyb ∧ semantics (σ |+ ((n,ty),x)) τ b (mb x))
   ⇒
   semantics σ τ (Abs n ty b) (abstract mty mtyb mb))`

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
    `Fun ty Bool = Fun rty Bool` by (
      metis_tac[WELLTYPED_LEMMA] ) >>
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
    qspecl_then[`sizeof t`,`t`,`[]`,`tyin`]mp_tac INST_CORE_HAS_TYPE >>
    qspecl_then[`sizeof t`,`t`,`[]`,`tyin'`]mp_tac INST_CORE_HAS_TYPE >>
    simp[] >> ntac 2 strip_tac >> fs[INST_def] >>
    `INST_CORE [] tyin' t = INST_CORE [] tyin t` by (
      match_mp_tac INST_CORE_tvars >>
      fs[SUBSET_DEF] >>
      imp_res_tac WELLTYPED_LEMMA >> rw[] >> fs[] >>
      metis_tac[TYPE_SUBST_tyvars] ) >>
    fs[] ) >>
  conj_tac >- (
    rpt gen_tac >> strip_tac >>
    simp_tac std_ss [Once semantics_cases] >>
    rw[] >> metis_tac[] ) >>
  conj_tac >- (
    rpt gen_tac >> strip_tac >>
    simp_tac (srw_ss()) [Once semantics_cases] >>
    rpt strip_tac >>
    BasicProvers.VAR_EQ_TAC >>
    `mrty = mty'` by metis_tac[] >>
    `maty = mty` by metis_tac[] >>
    qsuff_tac`mp = mt`>-metis_tac[] >>
    first_x_assum match_mp_tac >>
    simp[] ) >>
  conj_tac >- (
    rpt gen_tac >> strip_tac >>
    simp_tac std_ss [Once semantics_cases] >>
    simp_tac (srw_ss()) [] >>
    rw[] >> metis_tac[] ) >>
  rpt gen_tac >>
  strip_tac >>
  simp_tac std_ss [Once semantics_cases] >>
  rw[] >>
  imp_res_tac WELLTYPED_LEMMA >> rw[] >>
  match_mp_tac ABSTRACT_EQ >>
  conj_tac >- metis_tac[typeset_inhabited] >>
  fs[] >> res_tac >> fs[])

(*
val typeset_tyvars = store_thm("typeset_tyvars",
  ``∀ty τ1 τ2 m. typeset τ1 ty m ∧ (∀x. x ∈ set(tyvars ty) ⇒ FLOOKUP τ1 x = FLOOKUP τ2 x) ⇒ typeset τ2 ty m``,
  ho_match_mp_tac type_ind >>
  conj_tac >- (
    ntac 2 (simp[Once semantics_cases]) >>
    simp[FLOOKUP_DEF,SUBMAP_DEF,tyvars_def] >>
    rw[]) >>
  rpt gen_tac >> strip_tac >>
  simp[Once semantics_cases] >> rw[] >>
  simp[Once semantics_cases] >>
  fs[tyvars_def,MEM_LIST_UNION] >- metis_tac[] >>
  map_every qexists_tac[`mp`,`mrty`,`rty`,`w`] >> simp[] >>
  fs[EVERY_MEM] >>
  qmatch_assum_abbrev_tac`INST tyin p has_type Fun rty Bool` >>
  qspecl_then[`sizeof p`,`p`,`

  INST_CORE_HAS_TYPE
  metis_tac[]

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
    simp[Once has_type_cases] >> rw[] >>
    fs[term_valuation_def] >>
    imp_res_tac FEVERY_FLOOKUP >>
    fs[] >> metis_tac[]) >>
  conj_tac >- (
    rw[Once has_type_cases] >>
    rw[Once semantics_cases] >>
    rw[Once (Q.SPECL[`τ`,`Fun X Y`](CONJUNCT1 semantics_cases))] >>
    fsrw_tac[DNF_ss][] >>
    rpt(qexists_tac`mty`)>>simp[]>>
    match_mp_tac ABSTRACT_IN_FUNSPACE >> rw[] >>
    match_mp_tac ABSTRACT_IN_FUNSPACE >> rw[] >>
    metis_tac[BOOLEAN_IN_BOOLSET] ) >>
  conj_tac >- (
    rw[Once has_type_cases] >>
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
    imp_res_tac WELLTYPED_LEMMA >> fs[] >> rw[] >>
    fs[term_valuation_def,FEVERY_DEF] >>
    metis_tac[WELLTYPED_LEMMA] ) >>
  conj_tac >- (
    rw[] >>
    imp_res_tac WELLTYPED_LEMMA >> fs[] >> rw[] >>
    qpat_assum`typeset τ (X Y) Z` mp_tac >> rw[Once semantics_cases] >>
    imp_res_tac semantics_11 >>
    rpt BasicProvers.VAR_EQ_TAC >>
    rw[Once semantics_cases] >>
    fsrw_tac[DNF_ss][] >>
    rw[Once semantics_cases] >>
    fsrw_tac[DNF_ss][] >>
    qmatch_assum_rename_tac`typeset τ ty my`[] >>
    map_every qexists_tac[`my`,`mp`,`mrty`,`rty`,`w`] >>
    simp[] >>
    match_mp_tac ABSTRACT_IN_FUNSPACE >>
    fs[suchthat_def] >>
    imp_res_tac WELLTYPED_LEMMA >>
    fs[] >> rw[] >> imp_res_tac semantics_11 >> rw[] ) >>
  conj_tac >- (
    rw[] >>
    imp_res_tac WELLTYPED_LEMMA >> fs[] >> rw[] >>
    qpat_assum`typeset τ (X Y) Z` mp_tac >> rw[Once semantics_cases] >>
    qpat_assum`typeset τ (X Y) Z` mp_tac >> rw[Once semantics_cases] >>
    imp_res_tac semantics_11 >>
    rpt BasicProvers.VAR_EQ_TAC >>
    rw[Once semantics_cases] >>
    fsrw_tac[DNF_ss][] >>
    rw[Once (Q.SPECL[`τ`,`X Y Z`](CONJUNCT1 semantics_cases))] >>
    fsrw_tac[DNF_ss][] >>
    qmatch_assum_rename_tac`typeset τ ty my`[] >>
    map_every qexists_tac[`my`,`mp`,`mrty`,`rty`,`w`] >>
    simp[] >>
    match_mp_tac ABSTRACT_IN_FUNSPACE >>
    rw[] >>
    rw[] >- (
      fs[suchthat_def] >>
      imp_res_tac WELLTYPED_LEMMA >> fs[] >>
      rpt BasicProvers.VAR_EQ_TAC >>
      imp_res_tac semantics_11 >>
      rpt BasicProvers.VAR_EQ_TAC >>
      rw[] ) >>
    match_mp_tac ch_def >>
    fs[suchthat_def] >>
    metis_tac[] ) >>
  conj_tac >- (
    rw[] >> fs[] >>
    fs[Once (Q.SPECL[`τ`,`Fun X Y`](CONJUNCT1 semantics_cases))] >>
    imp_res_tac semantics_11 >>
    rpt BasicProvers.VAR_EQ_TAC >>
    qexists_tac`my` >> simp[] >>
    match_mp_tac APPLY_IN_RANSPACE >>
    qmatch_assum_rename_tac`typeset τ (typeof u) tu`[] >>
    qexists_tac`tu` >> simp[]) >>
  rw[] >> fs[] >>
  simp[Once semantics_cases] >>
  imp_res_tac WELLTYPED_LEMMA >>
  fs[WELLTYPED] >> fsrw_tac[DNF_ss][] >>
  BasicProvers.VAR_EQ_TAC >>
  qmatch_assum_rename_tac`typeset τ (typeof t) mtt`[] >>
  map_every qexists_tac[`mty`,`mtt`] >> rw[] >>
  match_mp_tac ABSTRACT_IN_FUNSPACE >> rw[])

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
    simp[] >>
    EQ_TAC >>
    strip_tac >>
    map_every qexists_tac[`mt`,`mu`] >> rw[] >>
    `∃msy. typeset τ (typeof s2) msy ∧ mt <: msy` by metis_tac[semantics_typeset,WELLTYPED] >>
    `∃msy. typeset τ (typeof s1) msy ∧ mt <: msy` by metis_tac[semantics_typeset,WELLTYPED] >>
    rfs[Once(Q.SPECL[`τ`,`Fun X Y`](CONJUNCT1 semantics_cases))] >>
    metis_tac[] ) >>
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
  first_x_assum(qspec_then`x`mp_tac) >> rw[] >>
  qmatch_abbrev_tac`semantics σ2' τ tq m` >>
  qmatch_assum_abbrev_tac`semantics σ1' τ tp m` >>
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

val semantics_vfree_in = store_thm("semantics_vfree_in",
  ``∀τ σ1 σ2 t.
      type_valuation τ ∧
      term_valuation τ σ1 ∧ term_valuation τ σ2 ∧
      welltyped t ∧
      (∀x ty. VFREE_IN (Var x ty) t ⇒ (FLOOKUP σ1 (x,ty) = FLOOKUP σ2 (x,ty)))
      ⇒ semantics σ1 τ t = semantics σ2 τ t``,
  gen_tac >> (CONV_TAC (RESORT_FORALL_CONV List.rev)) >> Induct
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
  rw[] >>
  (qsuff_tac`semantics (σ1 |+ ((s,t),x)) τ t' = semantics (σ2 |+ ((s,t),x)) τ t'` >- metis_tac[]) >>
  first_x_assum match_mp_tac >>
  fs[term_valuation_def] >>
  rw[FLOOKUP_UPDATE] >>
  TRY (
    match_mp_tac (CONJUNCT2 FEVERY_STRENGTHEN_THM) >>
    fs[] >> metis_tac[] ) >>
  fs[] )

val _ = Parse.add_infix("closes_over",450,Parse.NONASSOC)
val _ = Parse.overload_on("closes_over",``λσ t. ∀x ty. VFREE_IN (Var x ty) t ⇒ (x,ty) ∈ FDOM σ``)

val semantics_closes_over = store_thm("semantics_closes_over",
  ``∀t σ τ m. type_valuation τ ∧ semantics σ τ t m ⇒ σ closes_over t``,
  Induct
  >- (
    simp[Once semantics_cases,FLOOKUP_DEF] )
  >- (
    simp[Once semantics_cases] )
  >- (
    simp[Once semantics_cases] >>
    rw[] >> metis_tac[])
  >- (
    simp[Once semantics_cases] >>
    rpt gen_tac >> strip_tac >>
    `∃x. x <: mty` by metis_tac[typeset_inhabited] >>
    res_tac >>
    fs[FDOM_FUPDATE] >>
    metis_tac[]))

val closes_over_aconv = store_thm("closes_over_aconv",
  ``∀σ t t'. σ closes_over t ∧ ACONV t t' ⇒ σ closes_over t'``,
  rw[] >> metis_tac[VFREE_IN_ACONV])

val closes_over_equation = store_thm("closes_over_equation",
  ``σ closes_over l === r ⇔ σ closes_over l ∧ σ closes_over r``,
  rw[vfree_in_equation] >> metis_tac[])

val closes_over_extend = store_thm("closes_over_extend",
  ``∀σ t σ'. σ closes_over t ∧ σ ⊑ σ' ⇒ σ' closes_over t``,
  rw[SUBMAP_DEF])

val tac =
  qho_match_abbrev_tac`apply (apply (abstract a b f) x) y = z` >>
  `apply (abstract a b f) x = f x` by (
    match_mp_tac APPLY_ABSTRACT >>
    unabbrev_all_tac >> simp[] >>
    conj_tac >- metis_tac[semantics_typeset,semantics_11,WELLTYPED] >>
    match_mp_tac ABSTRACT_IN_FUNSPACE >>
    metis_tac[semantics_typeset,WELLTYPED,BOOLEAN_IN_BOOLSET] ) >>
  simp[Abbr`f`,Abbr`b`] >>
  qho_match_abbrev_tac`apply (abstract a b f) y = z` >>
  `apply (abstract a b f) y = f y `  by (
    match_mp_tac APPLY_ABSTRACT >>
    unabbrev_all_tac >> simp[] >>
    metis_tac[semantics_typeset,semantics_11,WELLTYPED,BOOLEAN_IN_BOOLSET] ) >>
  unabbrev_all_tac >> simp[]

val semantics_equation = store_thm("semantics_equation",
  ``∀σ τ s t mty ms mt mst.
    type_valuation τ ∧ term_valuation τ σ ∧
    semantics σ τ s ms ∧ semantics σ τ t mt ∧
    (typeof s = typeof t) ∧ boolean (ms = mt) = mst
    ⇒ semantics σ τ (s === t) mst``,
  rw[equation_def] >>
  simp[Once semantics_cases] >>
  simp[Once semantics_cases] >>
  simp[Once semantics_cases] >>
  srw_tac[DNF_ss][] >>
  imp_res_tac semantics_typeset >> simp[] >>
  map_every qexists_tac[`mt`,`ms`,`mty`] >> simp[] >>
  match_mp_tac EQ_SYM >> tac)

val semantics_equation_imp = store_thm("semantics_equation_imp",
  ``∀σ τ s t mst.
    type_valuation τ ∧ term_valuation τ σ ∧ semantics σ τ (s === t) mst ⇒
    ∃ms mt.
    semantics σ τ s ms ∧ semantics σ τ t mt ∧
    (typeof s = typeof t) ∧ boolean (ms = mt) = mst``,
  rw[equation_def] >>
  fs[Q.SPECL[`σ`,`τ`,`Comb X Y`](CONJUNCT2 semantics_cases)] >>
  fs[Q.SPECL[`σ`,`τ`,`Equal X`](CONJUNCT2 semantics_cases)] >>
  qmatch_assum_rename_tac`semantics σ τ s ms`[] >> rw[] >>
  qmatch_assum_rename_tac`semantics σ τ t mt`[] >>
  map_every qexists_tac[`ms`,`mt`] >> rw[] >>
  match_mp_tac EQ_SYM >> tac)

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

val type_has_meaning_def = Define`
  type_has_meaning ty ⇔ ∀τ. type_valuation τ ⇒ ∃m. typeset τ ty m`

(*  prove by induction on types or on typeset (ignoring semantics)? ∀τ ty m. typeset τ ty m ⇒ type_has_meaning ty *)

(* use this instead:

val has_meaning_def = Define`
  has_meaning t = ∀τ σ. type_valuation τ ∧ term_valuation τ σ ∧ σ closes_over t ⇒ semantics σ τ t m`

*)

(* and prove the extension in the definition below is possible as a separate theorem  *)

val has_meaning_def = Define`
  has_meaning t = ∀τ σ. type_valuation τ ∧ term_valuation τ σ ⇒
    ∃σ' m. σ ⊑ σ' ∧ term_valuation τ σ' ∧ σ' closes_over t ∧
           semantics σ' τ t m`

(*

can we prove this too?: ∀σ τ t m. semantics σ τ t m ⇒ has_meaning t

*)

val has_meaning_welltyped = store_thm("has_meaning_welltyped",
  ``∀t. has_meaning t ⇒ welltyped t``,
  rw[has_meaning_def] >>
  metis_tac[a_type_valuation_exists,semantics_typeset
           ,term_valuation_def,CONJUNCT1 FEVERY_STRENGTHEN_THM
           ,SUBMAP_FEMPTY])

val has_meaning_aconv = store_thm("has_meaning_aconv",
  ``∀t t'. has_meaning t ∧ ACONV t t' ⇒ has_meaning t'``,
  rw[] >>
  imp_res_tac has_meaning_welltyped >>
  fs[has_meaning_def] >> rw[] >>
  metis_tac[semantics_aconv,closes_over_aconv,ACONV_welltyped])

val equation_has_meaning = store_thm("equation_has_meaning",
  ``∀s t. has_meaning s ∧ has_meaning t ∧ typeof s = typeof t ⇒ has_meaning (s === t)``,
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
