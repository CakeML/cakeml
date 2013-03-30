open HolKernel bossLib boolLib boolSimps pairTheory listTheory rich_listTheory pred_setTheory finite_mapTheory SatisfySimps arithmeticTheory quantHeuristicsLib lcsymtacs
open MiniMLTheory miscTheory miniMLExtraTheory compileTerminationTheory
val _ = new_theory "intLang"

(* Cevaluate functional equations *)

val Cevaluate_raise = store_thm(
"Cevaluate_raise",
``∀c s env err res. Cevaluate c s env (CRaise err) res = (res = (s, Rerr (Rraise err)))``,
rw[Once Cevaluate_cases])

val Cevaluate_lit = store_thm(
"Cevaluate_lit",
``∀c s env l res. Cevaluate c s env (CLit l) res = (res = (s, Rval (CLitv l)))``,
rw[Once Cevaluate_cases])

val Cevaluate_var = store_thm(
"Cevaluate_var",
``∀c s env vn res. Cevaluate c s env (CVar vn) res = (vn < LENGTH env ∧ (res = (s, Rval (EL vn env))))``,
rw[Once Cevaluate_cases] >> PROVE_TAC[])

val Cevaluate_fun = store_thm(
"Cevaluate_fun",
``∀c s env b res. Cevaluate c s env (CFun b) res =
  (∀l. (b = INR l) ⇒ l ∈ FDOM c ∧ ((c ' l).nz = 1) ∧ ((c ' l).ez = LENGTH env)) ∧
  (res = (s, Rval (CRecClos env [b] 0)))``,
rw[Once Cevaluate_cases] >> metis_tac[])

val _ = export_rewrites["Cevaluate_raise","Cevaluate_lit","Cevaluate_var","Cevaluate_fun"]

val Cevaluate_con = store_thm(
"Cevaluate_con",
``∀c s env cn es res. Cevaluate c s env (CCon cn es) res =
(∃s' vs. Cevaluate_list c s env es (s', Rval vs) ∧ (res = (s', Rval (CConv cn vs)))) ∨
(∃s' err. Cevaluate_list c s env es (s', Rerr err) ∧ (res = (s', Rerr err)))``,
rw[Once Cevaluate_cases] >> PROVE_TAC[])

val Cevaluate_tageq = store_thm(
"Cevaluate_tageq",
``∀c s env exp n res. Cevaluate c s env (CTagEq exp n) res =
  (∃s' m vs. Cevaluate c s env exp (s', Rval (CConv m vs)) ∧ (res = (s', Rval (CLitv (Bool (n = m)))))) ∨
  (∃s' err. Cevaluate c s env exp (s', Rerr err) ∧ (res = (s', Rerr err)))``,
rw[Once Cevaluate_cases] >> PROVE_TAC[])

val Cevaluate_let = store_thm(
"Cevaluate_let",
``∀c s env e b res. Cevaluate c s env (CLet e b) res =
(∃s' v. Cevaluate c s env e (s', Rval v) ∧
     Cevaluate c s' (v::env) b res) ∨
(∃s' err. Cevaluate c s env e (s', Rerr err) ∧ (res = (s', Rerr err)))``,
rw[Once Cevaluate_cases] >> PROVE_TAC[])

val Cevaluate_proj = store_thm(
"Cevaluate_proj",
``∀c s env exp n res. Cevaluate c s env (CProj exp n) res =
  (∃s' m vs. Cevaluate c s env exp (s', Rval (CConv m vs)) ∧ (n < LENGTH vs) ∧ (res = (s', Rval (EL n vs)))) ∨
  (∃s' err. Cevaluate c s env exp (s', Rerr err) ∧ (res = (s', Rerr err)))``,
rw[Once Cevaluate_cases] >> PROVE_TAC[])

(* syneq (almost) equivalence relation lemmas *)

(* TODO: move *)
val syneq_rules = CompileTheory.syneq_rules
val el_check_def = CompileTheory.el_check_def

val syneq_sym = store_thm("syneq_sym",
  ``(∀c1 c2 x y. syneq c1 c2 x y ⇒ syneq c2 c1 y x) ∧
    (∀c1 c2 k env1 env2 v1 v2. syneq_var c1 c2 k env1 env2 v1 v2 ⇒ syneq_var c2 c1 k env2 env1 v2 v1) ∧
    (∀c1 c2 k env1 env2 exp1 exp2. syneq_exp c1 c2 k env1 env2 exp1 exp2 ⇒ syneq_exp c2 c1 k env2 env1 exp2 exp1) ∧
    (∀c1 c2 env1 env2 defs1 defs2 cb1 cb2. syneq_cb c1 c2 env1 env2 defs1 defs2 cb1 cb2 ⇒ syneq_cb c2 c1 env2 env1 defs2 defs1 cb2 cb1)``,
  ho_match_mp_tac syneq_ind >>
  strip_tac >- rw[Once syneq_cases] >>
  strip_tac >- (
    rw[] >> simp[Once syneq_cases] >>
    fs[EVERY2_EVERY,EVERY_MEM,MEM_ZIP,FORALL_PROD] >>
    pop_assum mp_tac >> fs[MEM_ZIP] >>
    PROVE_TAC[]) >>
  strip_tac >- ( rw[] >> rw[Once syneq_cases] ) >>
  strip_tac >- rw[Once syneq_cases] >>
  strip_tac >- rw[Once syneq_cases] >>
  strip_tac >- (
    rw[] >> rw[Once syneq_cases] >>
    fs[optionTheory.OPTREL_def] ) >>
  strip_tac >- (
    rw[] >> rw[Once syneq_cases] >>
    fs[EVERY2_EVERY,EVERY_MEM,MEM_ZIP,FORALL_PROD] >>
    pop_assum mp_tac >> fs[MEM_ZIP] >>
    PROVE_TAC[]) >>
  strip_tac >- ( rw[] >> rw[Once syneq_cases] ) >>
  strip_tac >- ( rw[] >> rw[Once syneq_cases] ) >>
  strip_tac >- ( rw[] >> rw[Once syneq_cases] ) >>
  strip_tac >- ( rw[] >> rw[Once syneq_cases] ) >>
  strip_tac >- (
    rw[] >> rw[Once syneq_cases] >>
    fs[EVERY2_EVERY,EVERY_MEM,MEM_ZIP,FORALL_PROD] >>
    pop_assum mp_tac >> fs[MEM_ZIP] >>
    PROVE_TAC[]) >>
  strip_tac >- ( rw[] >> rw[Once syneq_cases] ) >>
  strip_tac >- ( rw[] >> rw[Once syneq_cases] ) >>
  strip_tac >- ( rw[] >> rw[Once syneq_cases] ) >>
  strip_tac >- (
    rw[] >> simp[Once syneq_cases] >>
    fs[EVERY2_EVERY,EVERY_MEM,MEM_ZIP,FORALL_PROD] >>
    ntac 2 (pop_assum mp_tac) >> fs[MEM_ZIP] >>
    PROVE_TAC[]) >>
  strip_tac >- ( rw[] >> rw[Once syneq_cases] ) >>
  strip_tac >- (
    rw[] >> rw[Once syneq_cases] >>
    fs[EVERY2_EVERY,EVERY_MEM,MEM_ZIP,FORALL_PROD] >>
    pop_assum mp_tac >> fs[MEM_ZIP] >>
    PROVE_TAC[]) >>
  strip_tac >- ( rw[] >> rw[Once syneq_cases] ) >>
  strip_tac >- ( rw[] >> rw[Once syneq_cases] ) >>
  strip_tac >- ( rw[] >> rw[Once syneq_cases] ) >>
  strip_tac >- ( rw[] >> rw[Once syneq_cases] ) >>
  strip_tac >- ( rw[] >> rw[Once syneq_cases] ) >>
  strip_tac >- ( rw[] >> rw[Once syneq_cases] ) >>
  strip_tac >- ( rw[] >> rw[Once syneq_cases] ) >>
  rw[] >> rw[Once syneq_cases])

val syneq_trans = store_thm("syneq_trans",
  ``(∀c1 c2 x y. syneq c1 c2 x y ⇒ ∀c3 z. syneq c2 c3 y z ⇒ syneq c1 c3 x z) ∧
    (∀c1 c2 k env1 env2 v1 v2. syneq_var c1 c2 k env1 env2 v1 v2 ⇒
      ∀c3 env3 v3. syneq_var c2 c3 k env2 env3 v2 v3 ⇒ syneq_var c1 c3 k env1 env3 v1 v3) ∧
    (∀c1 c2 k env1 env2 e1 e2. syneq_exp c1 c2 k env1 env2 e1 e2 ⇒
      ∀c3 env3 e3. syneq_exp c2 c3 k env2 env3 e2 e3 ⇒ syneq_exp c1 c3 k env1 env3 e1 e3) ∧
    (∀c1 c2 env1 env2 d1 d2 e1 e2. syneq_cb c1 c2 env1 env2 d1 d2 e1 e2 ⇒
      ∀c3 env3 d3 e3. syneq_cb c2 c3 env2 env3 d2 d3 e2 e3 ⇒ syneq_cb c1 c3 env1 env3 d1 d3 e1 e3)``,
  ho_match_mp_tac syneq_ind >>
  strip_tac >- ( ntac 2 (rw[Once syneq_cases] ) ) >>
  strip_tac >- (
    rw[] >> pop_assum mp_tac >>
    simp[Once syneq_cases] >> strip_tac >>
    simp[Once syneq_cases] >>
    fs[EVERY2_EVERY,EVERY_MEM,MEM_ZIP] >> rw[] >>
    rpt (qpat_assum` LENGTH X = LENGTH Y` mp_tac) >>
    ntac 2 strip_tac >>
    fs[MEM_ZIP,FORALL_PROD] >>
    PROVE_TAC[] ) >>
  strip_tac >- (
    rw[] >> pop_assum mp_tac >>
    simp[Once syneq_cases] >> strip_tac >>
    simp[Once syneq_cases] ) >>
  strip_tac >- ( ntac 2 (rw[Once syneq_cases] ) ) >>
  strip_tac >- (
    ntac 2 (rw[Once syneq_cases] ) >>
    fs[optionTheory.OPTREL_def,el_check_def] >>
    spose_not_then strip_assume_tac >>
    fsrw_tac[ARITH_ss][] ) >>
  strip_tac >- (
    rw[] >> pop_assum mp_tac >>
    simp[Once syneq_cases] >> strip_tac >>
    simp[Once syneq_cases] >>
    fs[optionTheory.OPTREL_def,el_check_def] >>
    fsrw_tac[ARITH_ss][] ) >>
  strip_tac >- (
    rw[] >> pop_assum mp_tac >>
    simp[Once syneq_cases] >> strip_tac >>
    simp[Once syneq_cases] >>
    fs[EVERY2_EVERY,EVERY_MEM,MEM_ZIP] >> rw[] >>
    rpt (qpat_assum` LENGTH X = LENGTH Y` mp_tac) >>
    ntac 2 strip_tac >>
    fs[MEM_ZIP,FORALL_PROD] >>
    PROVE_TAC[] ) >>
  strip_tac >- ( ntac 2 (rw[Once syneq_cases] ) ) >>
  strip_tac >- (
    rw[] >> pop_assum mp_tac >>
    simp[Once syneq_cases] >> strip_tac >>
    simp[Once syneq_cases] ) >>
  strip_tac >- (
    rw[] >> pop_assum mp_tac >>
    simp[Once syneq_cases] >> strip_tac >>
    simp[Once syneq_cases] ) >>
  strip_tac >- (
    rw[] >> pop_assum mp_tac >>
    simp[Once syneq_cases] >> strip_tac >>
    simp[Once syneq_cases] ) >>
  strip_tac >- (
    rw[] >> pop_assum mp_tac >>
    simp[Once syneq_cases] >> strip_tac >>
    simp[Once syneq_cases] >>
    fs[EVERY2_EVERY,EVERY_MEM,MEM_ZIP] >> rw[] >>
    rpt (qpat_assum` LENGTH X = LENGTH Y` mp_tac) >>
    ntac 2 strip_tac >>
    fs[MEM_ZIP,FORALL_PROD] >>
    PROVE_TAC[] ) >>
  strip_tac >- (
    rw[] >> pop_assum mp_tac >>
    simp[Once syneq_cases] >> strip_tac >>
    simp[Once syneq_cases] ) >>
  strip_tac >- (
    rw[] >> pop_assum mp_tac >>
    simp[Once syneq_cases] >> strip_tac >>
    simp[Once syneq_cases] ) >>
  strip_tac >- (
    rw[] >> pop_assum mp_tac >>
    simp[Once syneq_cases] >> strip_tac >>
    simp[Once syneq_cases] ) >>
  strip_tac >- (
    rw[] >> pop_assum mp_tac >>
    simp[Once syneq_cases] >> strip_tac >>
    simp[Once syneq_cases] >>
    fs[EVERY2_EVERY,EVERY_MEM,MEM_ZIP] >> rw[] >>
    rpt (qpat_assum` LENGTH X = LENGTH Y` mp_tac) >>
    ntac 2 strip_tac >>
    fs[MEM_ZIP,FORALL_PROD] >>
    PROVE_TAC[] ) >>
  strip_tac >- (
    rw[] >> pop_assum mp_tac >>
    simp[Once syneq_cases] >> strip_tac >>
    simp[Once syneq_cases] ) >>
  strip_tac >- (
    rw[] >> pop_assum mp_tac >>
    simp[Once syneq_cases] >> strip_tac >>
    simp[Once syneq_cases] >>
    fs[EVERY2_EVERY,EVERY_MEM,MEM_ZIP] >> rw[] >>
    rpt (qpat_assum` LENGTH X = LENGTH Y` mp_tac) >>
    ntac 2 strip_tac >>
    fs[MEM_ZIP,FORALL_PROD] >>
    PROVE_TAC[] ) >>
  strip_tac >- (
    rw[] >> pop_assum mp_tac >>
    simp[Once syneq_cases] >> strip_tac >>
    simp[Once syneq_cases] ) >>
  strip_tac >- (
    rw[] >> pop_assum mp_tac >>
    simp[Once syneq_cases] >> strip_tac >>
    simp[Once syneq_cases] ) >>
  strip_tac >- (
    rw[] >> pop_assum mp_tac >>
    simp[Once syneq_cases] >> strip_tac >>
    simp[Once syneq_cases] ) >>
  strip_tac >- (
    rw[] >> pop_assum mp_tac >>
    simp[Once syneq_cases] >> strip_tac >>
    simp[Once syneq_cases] ) >>
  strip_tac >- (
    rw[] >> pop_assum mp_tac >>
    simp[Once syneq_cases] >> strip_tac >>
    simp[Once syneq_cases] >> rw[] ) >>
  strip_tac >- (
    rw[] >> pop_assum mp_tac >>
    simp[Once syneq_cases] >> strip_tac >>
    simp[Once syneq_cases] ) >>
  strip_tac >- (
    rw[] >> pop_assum mp_tac >>
    simp[Once syneq_cases] >> strip_tac >>
    simp[Once syneq_cases] ) >>
  rw[] >> pop_assum mp_tac >>
  simp[Once syneq_cases] >> strip_tac >>
  simp[Once syneq_cases] )

val result_rel_syneq_trans = save_thm(
"result_rel_syneq_trans",
result_rel_trans
|> Q.GEN`R`
|> Q.ISPEC`syneq c c`
|> SIMP_RULE std_ss [GSYM AND_IMP_INTRO]
|> UNDISCH
|> (fn th => PROVE_HYP (PROVE[syneq_trans](hd(hyp th))) th)
|> SIMP_RULE std_ss [AND_IMP_INTRO])

val result_rel_syneq_sym = save_thm(
"result_rel_syneq_sym",
result_rel_sym
|> Q.GEN`R`
|> Q.ISPEC`syneq c c`
|> SIMP_RULE std_ss[syneq_sym])

val fmap_rel_syneq_trans = save_thm(
"fmap_rel_syneq_trans",
fmap_rel_trans
|> Q.GEN`R`
|> Q.ISPEC`syneq c c`
|> SIMP_RULE std_ss [GSYM AND_IMP_INTRO]
|> UNDISCH
|> (fn th => PROVE_HYP (PROVE[syneq_trans](hd(hyp th))) th)
|> SIMP_RULE std_ss [AND_IMP_INTRO])

val fmap_rel_syneq_sym = save_thm(
"fmap_rel_syneq_sym",
fmap_rel_sym
|> Q.GEN`R`
|> Q.ISPEC`syneq c c`
|> SIMP_RULE std_ss[syneq_sym])

val syneq_ov = store_thm("syneq_ov",
  ``(∀v1 v2 c1 c2. syneq c1 c2 v1 v2 ⇒ ∀m s. Cv_to_ov m s v1 = Cv_to_ov m s v2) ∧
    (∀vs1 vs2 c1 c2. EVERY2 (syneq c1 c2) vs1 vs2 ⇒ ∀m s. EVERY2 (λv1 v2. Cv_to_ov m s v1 = Cv_to_ov m s v2) vs1 vs2)``,
  ho_match_mp_tac(TypeBase.induction_of``:Cv``) >>
  rw[] >> pop_assum mp_tac >>
  simp[Once syneq_cases] >>
  rw[] >> rw[] >>
  rw[MAP_EQ_EVERY2] >>
  fs[EVERY2_EVERY,EVERY_MEM,FORALL_PROD] >>
  rw[] >> TRY (
    first_x_assum (match_mp_tac o MP_CANON) >>
    metis_tac[] ) >>
  metis_tac[])

val syneq_lit_loc = store_thm("syneq_lit_loc",
  ``(syneq c1 c2 (CLitv l1) v2 = (v2 = CLitv l1)) ∧
    (syneq c1 c2 v1 (CLitv l2) = (v1 = CLitv l2)) ∧
    (syneq c1 c2 (CLoc n1) v2 = (v2 = CLoc n1)) ∧
    (syneq c1 c2 v1 (CLoc n2) = (v1 = CLoc n2))``,
  rpt(simp[Once syneq_cases]))
val _ = export_rewrites["syneq_lit_loc"]

(* Misc. int lang lemmas *)

val good_cmap_def = Define`
  good_cmap cenv m =
    ∀c1 n1 c2 n2 s.
      MEM (c1,(n1,s)) cenv ∧
      MEM (c2,(n2,s)) cenv ∧
      (FAPPLY m c1 = FAPPLY m c2) ⇒ (c1 = c2)`

val Cevaluate_list_LENGTH = store_thm("Cevaluate_list_LENGTH",
  ``∀exps c s env s' vs. Cevaluate_list c s env exps (s', Rval vs) ⇒ (LENGTH vs = LENGTH exps)``,
  Induct >> rw[LENGTH_NIL] >> pop_assum mp_tac >>
  rw[Once Cevaluate_cases] >>
  fsrw_tac[DNF_ss][] >>
  first_x_assum match_mp_tac >>
  srw_tac[SATISFY_ss][])

val FINITE_free_vars = store_thm(
"FINITE_free_vars",
``(∀t. FINITE (free_vars t)) ∧ (∀b. FINITE (cbod_fvs b))``,
ho_match_mp_tac free_vars_ind >>
rw[free_vars_def] >>
rw[FOLDL_UNION_BIGUNION] >>
TRY (match_mp_tac IMAGE_FINITE >> match_mp_tac FINITE_DIFF) >>
metis_tac[])
val _ = export_rewrites["FINITE_free_vars"]

val find_index_ALL_DISTINCT_EL = store_thm(
"find_index_ALL_DISTINCT_EL",
``∀ls n m. ALL_DISTINCT ls ∧ n < LENGTH ls ⇒ (find_index (EL n ls) ls m = SOME (m + n))``,
Induct >- rw[] >>
gen_tac >> Cases >>
srw_tac[ARITH_ss][find_index_def] >>
metis_tac[MEM_EL])
val _ = export_rewrites["find_index_ALL_DISTINCT_EL"]

val find_index_LESS_LENGTH = store_thm(
"find_index_LESS_LENGTH",
``∀ls n m i. (find_index n ls m = SOME i) ⇒ (i < m + LENGTH ls)``,
Induct >> rw[find_index_def] >>
res_tac >>
srw_tac[ARITH_ss][arithmeticTheory.ADD1])

val Cevaluate_store_SUBSET = store_thm("Cevaluate_store_SUBSET",
  ``(∀c s env exp res. Cevaluate c s env exp res ⇒ LENGTH s ≤ LENGTH (FST res)) ∧
    (∀c s env exps res. Cevaluate_list c s env exps res ⇒ LENGTH s ≤ LENGTH (FST res))``,
  ho_match_mp_tac Cevaluate_ind >> rw[] >>
  TRY (PROVE_TAC [LESS_EQ_TRANS]) >- (
    Cases_on`uop`>>rw[]>>srw_tac[ARITH_ss][] >>
    Cases_on`v`>>rw[] ) >>
  Cases_on`v1`>>rw[])

val all_Clocs_def = tDefine "all_Clocs"`
  (all_Clocs (CLitv _) = {}) ∧
  (all_Clocs (CConv _ vs) = BIGUNION (IMAGE all_Clocs (set vs))) ∧
  (all_Clocs (CRecClos env _ _) = BIGUNION (IMAGE all_Clocs (set env))) ∧
  (all_Clocs (CLoc n) = {n})`
  (WF_REL_TAC`measure Cv_size` >>
   srw_tac[ARITH_ss][Cv1_size_thm] >>
   Q.ISPEC_THEN`Cv_size`imp_res_tac SUM_MAP_MEM_bound >>
   fsrw_tac[ARITH_ss][])
val _ = export_rewrites["all_Clocs_def"]

val CevalPrim2_Clocs = store_thm("CevaluatePrim2_Clocs",
  ``∀p2 v1 v2 v. (CevalPrim2 p2 v1 v2 = Rval v) ⇒ (all_Clocs v = {})``,
  Cases >> fs[] >> Cases >> fs[] >>
  TRY (Cases_on`l` >> fs[] >> Cases >> fs[] >> Cases_on `l` >> fs[] >> rw[] >> rw[]) >>
  Cases >> fs[] >> rw[] >> rw[])

(* TODO: move *)
val ccenv_def = CompileTheory.ccenv_def
val _ = export_rewrites["compileTermination.ceenv_def"]
val _ = export_rewrites["Compile.ccenv_def"]

val good_cebind_def = Define`
  (good_cebind ez nz (CERef n) = 0 < n ∧ n ≤ nz) ∧
  (good_cebind ez nz (CEEnv n) = n < ez)`

val all_Clocs_ceenv = store_thm("all_Clocs_ceenv",
  ``∀env defs x. good_cebind (LENGTH env) (LENGTH defs) x ⇒
  all_Clocs (ceenv env defs x) ⊆ BIGUNION (IMAGE all_Clocs (set env))``,
  ntac 2 gen_tac >> Cases >> simp[SUBSET_DEF,MEM_EL,good_cebind_def] >>
  srw_tac[DNF_ss][] >> metis_tac[])

val good_ccbind_def = Define`
  (good_ccbind az ez nz env (CCArg n) = 2 ≤ n ∧ n ≤ 2+az) ∧
  (good_ccbind az ez nz env (CCRef n) =
   ∃v. (el_check n env = SOME (CERef v)) ∧
       good_cebind ez nz (CERef v)) ∧
  (good_ccbind az ez nz env (CCEnv n) =
   ∃v. (el_check n env = SOME (CEEnv v)) ∧
       good_cebind ez nz (CEEnv v))`

val all_Clocs_ccenv = store_thm("all_Clocs_ccenv",
  ``good_ccbind (LENGTH vs) (LENGTH cenv) (LENGTH defs) env x ⇒
    all_Clocs (ccenv vs env cenv defs k x) ⊆ BIGUNION (IMAGE all_Clocs (set (vs ++ cenv)))``,
  Cases_on`x`>>rw[]>>
  fsrw_tac[DNF_ss][good_ccbind_def,SUBSET_DEF,good_cebind_def,el_check_def] >- (
    srw_tac[DNF_ss][MEM_EL] >>
    disj1_tac >>
    pop_assum mp_tac >>
    fsrw_tac[ARITH_ss][EL_REVERSE,PRE_SUB1] >>
    strip_tac >>
    qmatch_assum_abbrev_tac `x ∈ all_Clocs (EL y vs)` >>
    qexists_tac`y` >>
    simp[Abbr`y`] ) >>
  metis_tac[MEM_EL])

val good_cd_def = Define`
  good_cd cd = EVERY (good_ccbind cd.cd.az cd.ez cd.nz cd.cd.ceenv) cd.cd.ccenv ∧
               free_vars cd.cd.body ⊆ count (LENGTH cd.cd.ccenv)`

val Cevaluate_Clocs = store_thm("Cevaluate_Clocs",
  ``(∀c s env exp res. Cevaluate c s env exp res ⇒
     (∀d. d ∈ FRANGE c ⇒ good_cd d) ∧
     BIGUNION (IMAGE all_Clocs (set env)) ⊆ count (LENGTH s) ∧
     BIGUNION (IMAGE all_Clocs (set s)) ⊆ count (LENGTH s)
     ⇒
     BIGUNION (IMAGE all_Clocs (set (FST res))) ⊆ count (LENGTH (FST res)) ∧
     ∀v. (SND res = Rval v) ⇒ all_Clocs v ⊆ count (LENGTH (FST res))) ∧
    (∀c s env exps res. Cevaluate_list c s env exps res ⇒
     (∀d. d ∈ FRANGE c ⇒ good_cd d) ∧
     BIGUNION (IMAGE all_Clocs (set env)) ⊆ count (LENGTH s) ∧
     BIGUNION (IMAGE all_Clocs (set s)) ⊆ count (LENGTH s)
     ⇒
     BIGUNION (IMAGE all_Clocs (set (FST res))) ⊆ count (LENGTH (FST res)) ∧
     ∀vs. (SND res = Rval vs) ⇒ BIGUNION (IMAGE all_Clocs (set vs)) ⊆ count (LENGTH (FST res)))``,
  ho_match_mp_tac Cevaluate_strongind >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    rpt gen_tac >> strip_tac >>
    fs[] >> rfs[] >>
    first_x_assum match_mp_tac >>
    fsrw_tac[DNF_ss][SUBSET_DEF] >>
    metis_tac[Cevaluate_store_SUBSET,FST,LESS_LESS_EQ_TRANS] ) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rw[] >>
    fsrw_tac[DNF_ss][SUBSET_DEF,MEM_EL] >>
    PROVE_TAC[] ) >>
  strip_tac >- rw[] >>
  strip_tac >- srw_tac[ETA_ss][] >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- (
    srw_tac[ETA_ss][] >>
    fsrw_tac[DNF_ss][SUBSET_DEF,MEM_EL] >>
    PROVE_TAC[] ) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >> strip_tac >>
    fs[] >> rfs[] >>
    first_x_assum match_mp_tac >>
    fsrw_tac[DNF_ss][SUBSET_DEF] >>
    metis_tac[Cevaluate_store_SUBSET,LESS_LESS_EQ_TRANS,FST] ) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rpt gen_tac >> ntac 2 strip_tac >>
    fs[] >> rfs[] >>
    first_x_assum match_mp_tac >>
    fsrw_tac[DNF_ss][SUBSET_DEF,MEM_GENLIST] >>
    PROVE_TAC[] ) >>
  strip_tac >- srw_tac[ETA_ss][] >>
  strip_tac >- (
    rpt gen_tac >> ntac 2 strip_tac >>
    fs[] >> rfs[] >>
    first_x_assum match_mp_tac >>
    fsrw_tac[DNF_ss][SUBSET_DEF] >>
    Cases_on`cb`>>fs[LET_THM] >- (
      PairCases_on`x`>>fs[]>>
      fsrw_tac[DNF_ss][MEM_GENLIST]>>
      imp_res_tac Cevaluate_store_SUBSET >>
      fs[] >> metis_tac[LESS_LESS_EQ_TRANS] ) >>
    fsrw_tac[DNF_ss][MEM_MAP,IN_FRANGE] >>
    fs[good_cd_def,EVERY_MEM] >>
    imp_res_tac Cevaluate_store_SUBSET >>
    fsrw_tac[DNF_ss][] >>
    metis_tac[SIMP_RULE(srw_ss()++DNF_ss)[SUBSET_DEF]all_Clocs_ccenv,LESS_LESS_EQ_TRANS] ) >>
  strip_tac >- (
    rw[] >> fs[] >> rfs[] >>
    first_x_assum match_mp_tac >>
    fsrw_tac[DNF_ss][SUBSET_DEF] >>
    metis_tac[Cevaluate_store_SUBSET,LESS_LESS_EQ_TRANS,FST] ) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rpt gen_tac >> ntac 2 strip_tac >>
    Cases_on`uop`>>fs[LET_THM] >- (
      fsrw_tac[DNF_ss][SUBSET_DEF] >>
      rw[] >> res_tac >>
      fsrw_tac[ARITH_ss][]) >>
    Cases_on`v`>>fs[] >>
    rw[el_check_def] >>
    fsrw_tac[DNF_ss][SUBSET_DEF,MEM_EL] >>
    PROVE_TAC[] ) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rw[] >> imp_res_tac CevalPrim2_Clocs >> rw[] ) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    ntac 6 gen_tac >>
    Cases >> fs[] >>
    gen_tac >> ntac 2 strip_tac >>
    fs[] >>
    fsrw_tac[DNF_ss][SUBSET_DEF] >>
    rw[] >> imp_res_tac MEM_LUPDATE >>
    fsrw_tac[DNF_ss][] >> res_tac) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rpt gen_tac >> ntac 2 strip_tac >>
    fs[] >> rfs[] >>
    first_x_assum match_mp_tac >>
    fsrw_tac[DNF_ss][SUBSET_DEF] >>
    metis_tac[Cevaluate_store_SUBSET,LESS_LESS_EQ_TRANS,FST]) >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rpt gen_tac >> ntac 2 strip_tac >>
    fs[] >> rfs[] >>
    fsrw_tac[DNF_ss][SUBSET_DEF] >>
    metis_tac[Cevaluate_store_SUBSET,LESS_LESS_EQ_TRANS,FST]) >>
  strip_tac >- rw[] >>
  rw[] >> fs[] >> rfs[] >>
  fsrw_tac[DNF_ss][SUBSET_DEF] >>
  metis_tac[Cevaluate_store_SUBSET,LESS_LESS_EQ_TRANS,FST])

(* simple cases of syneq preservation *)

val Cv_ind = store_thm("Cv_ind",
  ``∀P. (∀l. P (CLitv l)) ∧ (∀n vs. EVERY P vs ⇒ P (CConv n vs)) ∧
        (∀env defs n. EVERY P env ⇒ P (CRecClos env defs n)) ∧
        (∀n. P (CLoc n)) ⇒
        ∀v. P v``,
  rw[] >>
  qsuff_tac `(∀v. P v) ∧ (∀vs. EVERY P vs)` >- rw[] >>
  ho_match_mp_tac(TypeBase.induction_of``:Cv``) >>
  simp[])

val syneq_no_closures = store_thm("syneq_no_closures",
``∀v1 v2 c1 c2. syneq c1 c2 v1 v2 ⇒ (no_closures v2 = no_closures v1)``,
  ho_match_mp_tac Cv_ind >>
  rw[] >> pop_assum mp_tac >>
  simp[Once syneq_cases] >>
  rw[] >> rw[] >>
  srw_tac[ETA_ss][] >>
  fsrw_tac[DNF_ss][EVERY2_EVERY,EVERY_MEM,FORALL_PROD] >>
  pop_assum mp_tac >>
  fsrw_tac[DNF_ss][MEM_ZIP,MEM_EL] >>
  metis_tac[])

val no_closures_syneq_equal = store_thm("no_closures_syneq_equal",
``∀v1 v2 c1 c2. syneq c1 c2 v1 v2 ⇒ no_closures v1 ⇒ (v1 = v2)``,
  ho_match_mp_tac Cv_ind >>
  rw[] >>
  pop_assum mp_tac >> simp[Once syneq_cases] >>
  pop_assum mp_tac >> simp[Once syneq_cases] >>
  rw[] >> fsrw_tac[ETA_ss,DNF_ss][EVERY2_EVERY,EVERY_MEM,FORALL_PROD] >>
  ntac 2 (pop_assum mp_tac) >>
  fsrw_tac[DNF_ss][MEM_ZIP,MEM_EL,LIST_EQ_REWRITE] >>
  metis_tac[])

val CevalPrim2_syneq = store_thm(
"CevalPrim2_syneq",
``∀v1 v2 c1 c2. syneq c1 c2 v1 v2 ⇒
    ∀p v. (CevalPrim2 p v v1 = CevalPrim2 p v v2) ∧
          (CevalPrim2 p v1 v = CevalPrim2 p v2 v)``,
ho_match_mp_tac Cv_ind >>
strip_tac >- ( rw[Once syneq_cases] ) >>
strip_tac >- (
  gen_tac >> qx_gen_tac`vs1` >>
  strip_tac >>
  simp[Once syneq_cases] >>
  rpt gen_tac >> strip_tac >>
  `no_closures (CConv cn vs1) = no_closures (CConv cn vs2)` by (
    match_mp_tac syneq_no_closures >>
    simp[Once syneq_cases] >>
    fsrw_tac[][EVERY2_EVERY,EVERY_MEM,FORALL_PROD] >>
    qpat_assum`LENGTH vs1 = x`assume_tac >>
    fsrw_tac[DNF_ss][MEM_ZIP] >>
    PROVE_TAC[syneq_sym]) >>
  `no_closures (CConv cn vs2) ⇒ (vs1 = vs2)` by (
    strip_tac >>
    qsuff_tac `CConv cn vs1 = CConv cn vs2` >- rw[] >>
    match_mp_tac (MP_CANON no_closures_syneq_equal) >>
    rw[Once syneq_cases] >> PROVE_TAC[] ) >>
  fs[] >>
  Cases >> Cases >> TRY (Cases_on `l`) >> rw[] ) >>
strip_tac >- (
  rpt gen_tac >> strip_tac >>
  simp[Once syneq_cases] >>
  rpt gen_tac >> strip_tac >>
  Cases >> Cases >> TRY (Cases_on `l`) >> rw[] ) >>
simp[Once syneq_cases])

val doPrim2_syneq = store_thm(
"doPrim2_syneq",
``∀v1 v2 c1 c2. syneq c1 c2 v1 v2 ⇒
    ∀b ty op v. (doPrim2 b ty op v v1 = doPrim2 b ty op v v2) ∧
                (doPrim2 b ty op v1 v = doPrim2 b ty op v2 v)``,
ho_match_mp_tac Cv_ind >>
rw[] >> pop_assum mp_tac >>
simp[Once syneq_cases] >> rw[] >>
Cases_on `v` >> rw[])

(* TODO: move *)
val LIST_REL_EVERY2 = store_thm("LIST_REL_EVERY2",
  ``LIST_REL = EVERY2``,
  SRW_TAC[][FUN_EQ_THM] THEN
  METIS_TAC[EVERY2_EVERY,LIST_REL_EVERY_ZIP])

val EVERY2_LUPDATE_same = store_thm("EVERY2_LUPDATE_same",
  ``!P l1 l2 v1 v2 n. P v1 v2 /\ EVERY2 P l1 l2 ==>
    EVERY2 P (LUPDATE v1 n l1) (LUPDATE v2 n l2)``,
  GEN_TAC THEN Induct THEN
  SRW_TAC[][LUPDATE_def] THEN
  Cases_on`n`THEN SRW_TAC[][LUPDATE_def])

val CevalUpd_syneq = store_thm(
"CevalUpd_syneq",
``∀c1 c2 s1 v1 v2 s2 w1 w2.
  syneq c1 c2 v1 w1 ∧ syneq c1 c2 v2 w2 ∧ LIST_REL (syneq c1 c2) s1 s2 ⇒
  LIST_REL (syneq c1 c2) (FST (CevalUpd s1 v1 v2)) (FST (CevalUpd s2 w1 w2)) ∧
  result_rel (syneq c1 c2) (SND (CevalUpd s1 v1 v2)) (SND (CevalUpd s2 w1 w2))``,
  ntac 3 gen_tac >>
  Cases >> simp[] >>
  ntac 2 gen_tac >>
  Cases >> simp[] >>
  rw[] >> TRY (
    fs[LIST_REL_EVERY2] >>
    match_mp_tac EVERY2_LUPDATE_same >>
    rw[] ) >>
  PROVE_TAC[LIST_REL_LENGTH])

(* Closed values *)

val (Cclosed_rules,Cclosed_ind,Cclosed_cases) = Hol_reln`
(Cclosed c (CLitv l)) ∧
(EVERY (Cclosed c) vs ⇒ Cclosed c (CConv cn vs)) ∧
((EVERY (Cclosed c) env) ∧
 n < LENGTH defs ∧
 (∀cb. MEM cb defs ⇒
   (∀v. LENGTH defs + v ∈ cbod_fvs cb ⇒ v < LENGTH env) ∧
   (∀l. (cb = INR l) ⇒ l ∈ FDOM c
     ∧ ((c ' l).nz = LENGTH defs)
     ∧ ((c ' l).ez = LENGTH env)))
⇒ Cclosed c (CRecClos env defs n)) ∧
(Cclosed c (CLoc m))`

val Cclosed_lit_loc = store_thm("Cclosed_lit_loc",
  ``Cclosed c (CLitv l) ∧
    Cclosed c (CLoc n)``,
  rw[Cclosed_rules])
val _ = export_rewrites["Cclosed_lit_loc"]

val doPrim2_closed = store_thm(
"doPrim2_closed",
``∀c b ty op v1 v2. every_result (Cclosed c) (doPrim2 b ty op v1 v2)``,
ntac 4 gen_tac >>
Cases >> TRY (Cases_on `l`) >>
Cases >> TRY (Cases_on `l`) >>
rw[])
val _ = export_rewrites["doPrim2_closed"];

val CevalPrim2_closed = store_thm(
"CevalPrim2_closed",
``∀c p2 v1 v2. every_result (Cclosed c) (CevalPrim2 p2 v1 v2)``,
gen_tac >> Cases >> rw[])
val _ = export_rewrites["CevalPrim2_closed"];

val CevalPrim1_closed = store_thm(
"CevalPrim1_closed",
``∀c uop s v. EVERY (Cclosed c) s ∧ Cclosed c v ⇒
  EVERY (Cclosed c) (FST (CevalPrim1 uop s v)) ∧
  every_result (Cclosed c) (SND (CevalPrim1 uop s v))``,
gen_tac >> Cases >> rw[LET_THM,Cclosed_rules] >> rw[]
>- ( Cases_on`v`>>fs[] )
>- ( Cases_on`v`>>fs[] >>
  rw[el_check_def] >>
  fsrw_tac[DNF_ss][EVERY_MEM,MEM_EL]))

val CevalUpd_closed = store_thm(
"CevalUpd_closed",
``(∀c s v1 v2. Cclosed c v2 ⇒ every_result (Cclosed c) (SND (CevalUpd s v1 v2))) ∧
  (∀c s v1 v2. EVERY (Cclosed c) s ∧ Cclosed c v2 ⇒
    EVERY (Cclosed c) (FST (CevalUpd s v1 v2)))``,
  conj_tac >>
  ntac 2 gen_tac >>
  Cases >> simp[] >- rw[] >>
  rpt gen_tac >> strip_tac >>
  rw[] >>
  fsrw_tac[DNF_ss][EVERY_MEM] >> rw[] >>
  imp_res_tac MEM_LUPDATE >> fs[])

val Cclosed_bundle = store_thm("Cclosed_bundle",
  ``Cclosed c (CRecClos cenv defs n) ∧ n < LENGTH defs ⇒
    ∀m. m < LENGTH defs ⇒ Cclosed c (CRecClos cenv defs m)``,
  simp[Once Cclosed_cases] >>
  simp[Once Cclosed_cases] >>
  metis_tac[])

val Cevaluate_closed = store_thm("Cevaluate_closed",
  ``(∀c s env exp res. Cevaluate c s env exp res
     ⇒ (∀d. d ∈ FRANGE c ⇒ good_cd d)
     ∧ free_vars exp ⊆ count (LENGTH env)
     ∧ EVERY (Cclosed c) env
     ∧ EVERY (Cclosed c) s
     ⇒
     EVERY (Cclosed c) (FST res) ∧
     every_result (Cclosed c) (SND res)) ∧
    (∀c s env exps ress. Cevaluate_list c s env exps ress
     ⇒ (∀d. d ∈ FRANGE c ⇒ good_cd d)
     ∧ BIGUNION (IMAGE free_vars (set exps)) ⊆ count (LENGTH env)
     ∧ EVERY (Cclosed c) env
     ∧ EVERY (Cclosed c) s
     ⇒
     EVERY (Cclosed c) (FST ress) ∧
     every_result (EVERY (Cclosed c)) (SND ress))``,
  ho_match_mp_tac Cevaluate_ind >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rpt gen_tac >> ntac 2 strip_tac >>
    fsrw_tac[DNF_ss][] >>
    rfs[] >>
    conj_tac >>
    first_x_assum(match_mp_tac o MP_CANON) >>
    fsrw_tac[DNF_ss][SUBSET_DEF] >>
    Cases >> fsrw_tac[ARITH_ss][] >>
    rw[] >> res_tac >> fs[]) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rw[] >> fsrw_tac[DNF_ss][EVERY_MEM,MEM_EL] ) >>
  strip_tac >- ( rw[] >> rw[Once Cclosed_cases]) >>
  strip_tac >- (
    srw_tac[ETA_ss][FOLDL_UNION_BIGUNION] >> fs[] >>
    rw[Once Cclosed_cases] ) >>
  strip_tac >- (
    srw_tac[ETA_ss][FOLDL_UNION_BIGUNION] ) >>
  strip_tac >- ( rw[] >> rw[Once Cclosed_cases]) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rw[] >> fs[] >>
    fsrw_tac[DNF_ss][Q.SPECL[`c`,`CConv m vs`] Cclosed_cases,EVERY_MEM,MEM_EL] ) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rpt gen_tac >> ntac 2 strip_tac >>
    first_x_assum match_mp_tac >>
    fsrw_tac[DNF_ss][SUBSET_DEF] >>
    Cases >> fsrw_tac[ARITH_ss][] >>
    rw[] >> res_tac >> fs[]) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rpt gen_tac >> ntac 2 strip_tac >>
    fs[FOLDL_FUPDATE_LIST,FOLDL_UNION_BIGUNION] >>
    first_x_assum match_mp_tac >>
    fsrw_tac[DNF_ss][SUBSET_DEF,LET_THM] >>
    conj_tac >- (
      rw[] >> res_tac >>
      fsrw_tac[ARITH_ss][] ) >>
    lrw[EVERY_REVERSE,EVERY_GENLIST] >>
    simp[Once Cclosed_cases] >>
    fs[EVERY_MEM] >>
    ntac 3 strip_tac >- (
      rw[] >> res_tac >>
      fsrw_tac[ARITH_ss][] ) >>
    metis_tac[]) >>
  strip_tac >- (
    rw[] >>
    rw[Once Cclosed_cases] >>
    fsrw_tac[DNF_ss][SUBSET_DEF] >>
    res_tac >> fsrw_tac[ARITH_ss][]) >>
  strip_tac >- (
    rpt gen_tac >> ntac 2 strip_tac >>
    fs[FOLDL_UNION_BIGUNION] >>
    first_x_assum match_mp_tac >>
    fsrw_tac[DNF_ss][SUBSET_DEF] >>
    Cases_on`cb`>>fs[LET_THM] >- (
      PairCases_on`x`>>fs[]>>
      simp[EVERY_REVERSE,EVERY_GENLIST] >>
      reverse conj_tac >- (
        conj_tac >- metis_tac[Cclosed_bundle] >>
        fs[Once Cclosed_cases] ) >>
      fs[Once Cclosed_cases] >>
      first_x_assum(qspec_then`INL (x0,x1)`mp_tac) >>
      `MEM (INL (x0,x1)) defs` by (rw[MEM_EL] >> PROVE_TAC[]) >>
      res_tac >> rw[] >>
      fsrw_tac[ARITH_ss,DNF_ss][] >>
      res_tac >>
      Cases_on`x < LENGTH vs`>>fsrw_tac[ARITH_ss][] >>
      Cases_on`x - LENGTH vs < LENGTH defs`>>fsrw_tac[ARITH_ss][] >>
      qsuff_tac`x - LENGTH vs - LENGTH defs < LENGTH cenv` >- DECIDE_TAC >>
      qsuff_tac`x - LENGTH vs - LENGTH defs + LENGTH defs = x - LENGTH vs` >- metis_tac[] >>
      DECIDE_TAC ) >>
    simp[EVERY_REVERSE,EVERY_MAP] >>
    fsrw_tac[DNF_ss][IN_FRANGE] >>
    fsrw_tac[DNF_ss][good_cd_def,SUBSET_DEF] >>
    fs[EVERY_MEM] >>
    ntac 2 strip_tac >>
    qmatch_assum_rename_tac`MEM z (c ' l).cd.ccenv`[] >>
    rfs[] >> fsrw_tac[DNF_ss][] >>
    first_x_assum(qspecl_then[`l`,`z`]mp_tac) >>
    simp[] >>
    Cases_on`z`>>simp[good_ccbind_def] >- (
      rw[] >>
      qmatch_rename_tac`Cclosed c (EL (k-2) (REVERSE vs))`[] >>
      simp[EL_REVERSE,PRE_SUB1] >>
      qmatch_abbrev_tac`Cclosed c (EL v vs)` >>
      qsuff_tac `v < LENGTH vs` >- (fs[MEM_EL] >> PROVE_TAC[]) >>
      simp[Abbr`v`] )
    >- (
      rw[el_check_def] >> rw[] >>
      qpat_assum`Cclosed c (CRecClos x y z)`mp_tac >>
      simp[Once Cclosed_cases] >>
      simp[EVERY_MEM] >>
      disch_then(match_mp_tac o CONJUNCT1) >>
      fs[good_cebind_def,MEM_EL] >>
      PROVE_TAC[] )
    >- (
      rw[el_check_def] >> rw[] >>
      match_mp_tac (MP_CANON Cclosed_bundle) >>
      fs[good_cebind_def] >>
      simp[] )) >>
  strip_tac >- (
    rpt gen_tac >> ntac 2 strip_tac >>
    fsrw_tac[ETA_ss][FOLDL_UNION_BIGUNION] ) >>
  strip_tac >- (
    rpt gen_tac >> ntac 2 strip_tac >>
    fsrw_tac[ETA_ss][FOLDL_UNION_BIGUNION] ) >>
  strip_tac >- (
    rpt gen_tac >> ntac 2 strip_tac >>
    full_simp_tac std_ss [free_vars_def,every_result_def] >>
    metis_tac[CevalPrim1_closed]) >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rw[] >- (
      match_mp_tac (MP_CANON (CONJUNCT2 CevalUpd_closed)) >>
      rw[]) >>
    match_mp_tac (CONJUNCT1 CevalUpd_closed) >>
    rw[] ) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rpt gen_tac >> ntac 2 strip_tac >>
    first_x_assum match_mp_tac >>
    fs[] >> rw[] ) >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rpt gen_tac >> ntac 2 strip_tac >>
    full_simp_tac std_ss [] >>
    fs[] ) >>
  strip_tac >- (
    rpt gen_tac >> ntac 2 strip_tac >>
    full_simp_tac std_ss [] >>
    fs[] ) >>
  rpt gen_tac >> ntac 2 strip_tac >>
  full_simp_tac std_ss [] >>
  fs[] )

(* Cevaluate when environment changes *)

val final0 =
  qsuff_tac `env0 ⊌ env1 = env1` >- PROVE_TAC[] >>
  rw[GSYM SUBMAP_FUNION_ABSORPTION] >>
  rw[Abbr`env0`,Abbr`env1`,SUBMAP_DEF,DRESTRICT_DEF,FUNION_DEF,FUN_FMAP_DEF,pairTheory.UNCURRY,FAPPLY_FUPDATE_THM] >>
  fsrw_tac[boolSimps.DNF_ss,SATISFY_ss][FUN_FMAP_DEF,pairTheory.UNCURRY,MEM_EL,fmap_rel_def] >>
  metis_tac[]

val Cevaluate_any_env = store_thm(
"Cevaluate_any_env",
``(∀c d s env exp res. Cevaluate c d s env exp res ⇒
   free_vars c exp ⊆ FDOM env ∧
   (∀v. v ∈ FRANGE env ⇒ Cclosed c v) ∧
   (∀v. v ∈ FRANGE s ⇒ Cclosed c v)
   ⇒
     ∀s' env'. fmap_rel (syneq c) env env' ∧ (∀v. v ∈ FRANGE env' ⇒ Cclosed c v) ∧
               fmap_rel (syneq c) s s' ∧ (∀v. v ∈ FRANGE s' ⇒ Cclosed c v) ⇒
       ∀env''. (∀v. v ∈ FRANGE env'' ⇒ Cclosed c v) ⇒
         ∃res'. Cevaluate c d s' ((DRESTRICT env' (free_vars c exp)) ⊌ env'') exp res' ∧
                fmap_rel (syneq c) (FST res) (FST res') ∧
                (result_rel (syneq c)) (SND res) (SND res')) ∧
  (∀c d s env exps ress. Cevaluate_list c d s env exps ress ⇒
   BIGUNION (IMAGE (free_vars c) (set exps)) ⊆ FDOM env ∧
   (∀v. v ∈ FRANGE env ⇒ Cclosed c v) ∧
   (∀v. v ∈ FRANGE s ⇒ Cclosed c v)
   ⇒
    ∀s' env'. fmap_rel (syneq c) env env' ∧ (∀v. v ∈ FRANGE env' ⇒ Cclosed c v) ∧
              fmap_rel (syneq c) s s' ∧ (∀v. v ∈ FRANGE s' ⇒ Cclosed c v) ⇒
      ∀env''. (∀v. v ∈ FRANGE env'' ⇒ Cclosed c v) ⇒
        ∃ress'. Cevaluate_list c d s' ((DRESTRICT env' (BIGUNION (IMAGE (free_vars c) (set exps)))) ⊌ env'') exps ress' ∧
                fmap_rel (syneq c) (FST ress) (FST ress') ∧
                (result_rel (EVERY2 (syneq c))) (SND ress) (SND ress'))``,
ho_match_mp_tac Cevaluate_strongind >>
strip_tac >- rw[] >>
strip_tac >- (
  rw[] >>
  rw[Once Cevaluate_cases] >>
  srw_tac[DNF_ss][] >>
  disj1_tac >>
  fsrw_tac[DNF_ss][EXISTS_PROD] >>
  Q.PAT_ABBREV_TAC `env1 = X ⊌ env''` >>
  qmatch_assum_rename_tac`fmap_rel (syneq c) env env0`[] >>
  qmatch_assum_rename_tac`fmap_rel (syneq c) s s0`[] >>
  first_x_assum(qspecl_then[`s0`,`env0`,`env1`]mp_tac) >>
  simp[] >>
  `∀v. v ∈ FRANGE env1 ⇒ Cclosed c v` by (
    qunabbrev_tac`env1` >>
    match_mp_tac IN_FRANGE_FUNION_suff >> simp[] >>
    match_mp_tac IN_FRANGE_DRESTRICT_suff >> simp[] ) >>
  rw[] >>
  qmatch_assum_rename_tac`fmap_rel (syneq c) s2 s3`[] >>
  qmatch_assum_rename_tac`syneq c v v3`[] >>
  map_every qexists_tac[`s3`,`v3`] >> rw[] >>
  qmatch_assum_abbrev_tac`Cevaluate c d s0 env2 exp res` >>
  qsuff_tac`env1 = env2`>-rw[] >>
  unabbrev_all_tac >>
  rw[GSYM SUBMAP_FUNION_ABSORPTION] >>
  match_mp_tac SUBMAP_FUNION >>
  disj1_tac >>
  match_mp_tac DRESTRICT_SUBSET_SUBMAP >>
  rw[] ) >>
strip_tac >- (
  rw[] >>
  rw[Once Cevaluate_cases] >>
  fsrw_tac[DNF_ss][EXISTS_PROD] >>
  disj2_tac >> disj1_tac >>
  Q.PAT_ABBREV_TAC `env1 = X ⊌ env''` >>
  qmatch_assum_rename_tac`fmap_rel (syneq c) env env0`[] >>
  qmatch_assum_rename_tac`fmap_rel (syneq c) s s0`[] >>
  `∀v. v ∈ FRANGE env1 ⇒ Cclosed c v` by (
    qunabbrev_tac`env1` >>
    match_mp_tac IN_FRANGE_FUNION_suff >> simp[] >>
    match_mp_tac IN_FRANGE_DRESTRICT_suff >> simp[] ) >>
  POP_ASSUM_LIST(map_every ASSUME_TAC) >>
  first_x_assum(qspecl_then[`s0`,`env0`,`env1`]mp_tac) >>
  rw[] >>
  qmatch_assum_rename_tac`Cevaluate c d s2 (env |+ X) e2 res`["X"] >>
  qmatch_assum_rename_tac`fmap_rel (syneq c) s2 s3`[] >>
  CONV_TAC (RESORT_EXISTS_CONV List.rev) >>
  map_every qexists_tac[`n`,`s3`] >>
  qmatch_assum_abbrev_tac`Cevaluate c d s0 env2 exp rr` >>
  `env1 = env2` by (
    unabbrev_all_tac >>
    rw[GSYM SUBMAP_FUNION_ABSORPTION] >>
    match_mp_tac SUBMAP_FUNION >>
    disj1_tac >>
    match_mp_tac DRESTRICT_SUBSET_SUBMAP >>
    rw[] ) >>
  simp[] >>
  Q.PAT_ABBREV_TAC`ln = CLitv X` >>
  first_x_assum(qspecl_then[`s3`,`env0 |+ (x,ln)`,`env2 |+ (x,ln)`]mp_tac) >>
  qspecl_then[`c`,`d`,`s`,`env`,`exp`,`(s2,Rerr(Rraise(Int_error n)))`]mp_tac(CONJUNCT1 Cevaluate_closed) >>
  simp[] >> strip_tac >>
  qmatch_abbrev_tac`(P⇒Q)⇒R`>>
  `P` by (
    map_every qunabbrev_tac[`P`,`Q`,`R`] >>
    fsrw_tac[DNF_ss][SUBSET_DEF] >>
    conj_tac >- metis_tac[] >>
    match_mp_tac IN_FRANGE_DOMSUB_suff >>
    rw[] ) >>
  simp[] >>
  map_every qunabbrev_tac[`P`,`Q`,`R`] >>
  qspecl_then[`c`,`d`,`s0`,`env2`,`exp`,`rr`]mp_tac(CONJUNCT1 Cevaluate_closed) >>
  `free_vars c exp ⊆ FDOM env2` by (
    unabbrev_all_tac >>
    rw[FDOM_DRESTRICT] >>
    fsrw_tac[DNF_ss][SUBSET_DEF] >>
    fs[fmap_rel_def] ) >>
  simp[Abbr`rr`] >> strip_tac >>
  qmatch_abbrev_tac`(P⇒Q)⇒R`>>
  `P` by (
    map_every qunabbrev_tac[`P`,`Q`,`R`] >>
    conj_tac >- (
      match_mp_tac fmap_rel_FUPDATE_same >>
      rw[] ) >>
    simp[Abbr`ln`] >>
    fsrw_tac[DNF_ss][] >>
    match_mp_tac IN_FRANGE_DOMSUB_suff >>
    rw[] ) >>
  simp[] >>
  map_every qunabbrev_tac[`P`,`Q`,`R`] >>
  qmatch_abbrev_tac`(P⇒Q)⇒R`>>
  `P` by (
    map_every qunabbrev_tac[`P`,`Q`,`R`] >>
    simp[Abbr`ln`] >>
    fsrw_tac[DNF_ss][] >>
    match_mp_tac IN_FRANGE_DOMSUB_suff >>
    rw[] ) >>
  simp[] >>
  map_every qunabbrev_tac[`P`,`Q`,`R`] >>
  strip_tac >>
  qmatch_assum_abbrev_tac`Cevaluate c d s3 env3 e2 rr` >>
  qmatch_assum_rename_tac`Abbrev (rr = (s4,r4))`[] >>
  `env3 = env2 |+ (x,ln)` by (
    qunabbrev_tac`env3` >>
    Q.PAT_ABBREV_TAC`env3 = DRESTRICT env0 Y` >>
    simp[GSYM SUBMAP_FUNION_ABSORPTION] >>
    `env3 \\ x ⊑ env2` by (
      qpat_assum`env1 = env2`(SUBST1_TAC o SYM) >>
      unabbrev_all_tac >>
      rpt (pop_assum kall_tac) >>
      match_mp_tac SUBMAP_FUNION >>
      disj1_tac >>
      simp[DRESTRICT_DOMSUB] >>
      match_mp_tac DRESTRICT_SUBSET_SUBMAP >>
      srw_tac[DNF_ss][SUBSET_DEF]) >>
    rw[GSYM SUBMAP_FUNION_ABSORPTION] >- (
      match_mp_tac SUBMAP_mono_FUPDATE >>
      fs[Once SUBMAP_DOMSUB_gen]) >>
    match_mp_tac SUBMAP_TRANS >>
    qexists_tac `env3 |+ (x,ln)` >>
    conj_tac >- (
      simp[Abbr`env3`,FDOM_DRESTRICT] ) >>
    match_mp_tac SUBMAP_mono_FUPDATE >>
    fs[Once SUBMAP_DOMSUB_gen]) >>
  PROVE_TAC[] ) >>
strip_tac >- (
  rpt strip_tac >>
  rw[Once Cevaluate_cases] >>
  fsrw_tac[DNF_ss][EXISTS_PROD] >>
  disj2_tac >>
  qmatch_assum_rename_tac`fmap_rel (syneq c) env env0`[] >>
  qmatch_assum_rename_tac`fmap_rel (syneq c) s s0`[] >>
  Q.PAT_ABBREV_TAC`env1 = DRESTRICT env0 X ⊌ Y` >>
  first_x_assum(qspecl_then[`s0`,`env0`,`env1`]mp_tac) >>
  `∀v. v ∈ FRANGE env1 ⇒ Cclosed c v` by (
    simp[Abbr`env1`] >>
    match_mp_tac IN_FRANGE_FUNION_suff >> simp[] >>
    match_mp_tac IN_FRANGE_DRESTRICT_suff >> rw[] ) >>
  simp[] >>
  Q.PAT_ABBREV_TAC`env2 = X ⊌ env1` >>
  `env2 = env1` by (
    unabbrev_all_tac >>
    rw[GSYM SUBMAP_FUNION_ABSORPTION] >>
    match_mp_tac SUBMAP_FUNION >>
    disj1_tac >>
    match_mp_tac DRESTRICT_SUBSET_SUBMAP >>
    rw[] ) >>
  rw[] ) >>
strip_tac >- rw[DRESTRICT_DEF,FUNION_DEF,fmap_rel_def] >>
strip_tac >- rw[] >>
strip_tac >- (
  rw[Cevaluate_con,FOLDL_UNION_BIGUNION] >>
  fsrw_tac[DNF_ss,ETA_ss][] >>
  rw[Once syneq_cases] >>
  full_simp_tac(pure_ss++(QUANT_INST_ss[pair_default_qp]))[] >>
  metis_tac[]) >>
strip_tac >- (
  rw[Cevaluate_con,FOLDL_UNION_BIGUNION] >>
  fsrw_tac[DNF_ss,ETA_ss][] >>
  full_simp_tac(pure_ss++(QUANT_INST_ss[pair_default_qp]))[] >>
  fs[]) >>
strip_tac >- (
  rw[Cevaluate_tageq] >>
  fsrw_tac[DNF_ss][result_rel_def] >>
  CONV_TAC SWAP_EXISTS_CONV >>
  qexists_tac `m` >> fs[Once syneq_cases] >>
  full_simp_tac(pure_ss++(QUANT_INST_ss[pair_default_qp]))[] >>
  fs[] >> metis_tac[]) >>
strip_tac >- (
  rw[Cevaluate_tageq,result_rel_def] >>
  full_simp_tac(pure_ss++(QUANT_INST_ss[pair_default_qp]))[] >>
  fsrw_tac[DNF_ss][] ) >>
strip_tac >- (
  rw[Cevaluate_proj] >>
  fsrw_tac[DNF_ss][result_rel_def] >>
  full_simp_tac(pure_ss++(QUANT_INST_ss[pair_default_qp]))[] >>
  fs[Q.SPECL[`c`,`CConv m vs`]syneq_cases] >>
  first_x_assum (qspecl_then[`s''`,`env'`,`env''`]mp_tac) >>
  fsrw_tac[DNF_ss][] >>
  qx_gen_tac`s1` >>
  qx_gen_tac`vs1` >>
  strip_tac >>
  map_every qexists_tac [`s1`,`m`,`vs1`] >>
  fs[EVERY2_EVERY] >>
  pop_assum mp_tac >>
  srw_tac[DNF_ss][EVERY_MEM,MEM_ZIP,FORALL_PROD]) >>
strip_tac >- (
  rw[Cevaluate_proj,result_rel_def] >>
  full_simp_tac(pure_ss++(QUANT_INST_ss[pair_default_qp]))[] >>
  rw[] ) >>
strip_tac >- (
  fs[Cevaluate_let,FOLDL_UNION_BIGUNION,
     DRESTRICT_DEF,FUNION_DEF] >>
  rpt gen_tac >>
  strip_tac >> strip_tac >>
  fsrw_tac[DNF_ss,SATISFY_ss][SUBSET_DEF] >>
  qx_gen_tac `s''` >>
  qx_gen_tac `env'` >>
  qx_gen_tac `env''` >>
  strip_tac >>
  strip_tac >>
  disj1_tac >>
  Q.PAT_ABBREV_TAC `env1 = X ⊌ env''` >>
  POP_ASSUM_LIST (map_every ASSUME_TAC) >>
  first_x_assum (qspecl_then [`s''`,`env'`,`env1`] mp_tac) >>
  `∀v. v ∈ FRANGE env1 ⇒ Cclosed c v` by (
    unabbrev_all_tac >>
    match_mp_tac IN_FRANGE_FUNION_suff >> simp[] >>
    match_mp_tac IN_FRANGE_DRESTRICT_suff >> simp[]) >>
  rw[] >>
  qmatch_assum_abbrev_tac `Cevaluate c d s'' (env0 ⊌ env1) ee rr` >>
  qmatch_assum_rename_tac `syneq c v v2`[] >>
  CONV_TAC (RESORT_EXISTS_CONV List.rev) >>
  qexists_tac `v2` >>
  PairCases_on`rr`>>fs[] >>rw[] >>
  qexists_tac `rr0` >>
  simp_tac(srw_ss())[RIGHT_EXISTS_AND_THM,GSYM CONJ_ASSOC] >>
  conj_tac >- final0 >>
  qmatch_assum_rename_tac`Cevaluate c d s' (env |+ (n,v)) b res`[] >>
  `∀x. x ∈ free_vars c b ⇒ (x = n) ∨ x ∈ FDOM env` by (
    PROVE_TAC[] ) >> fs[] >>
  first_x_assum (qspecl_then [`rr0`,`env' |+ (n,v2)`, `env1 |+ (n,v2)`] mp_tac) >>
  asm_simp_tac bool_ss [fmap_rel_FUPDATE_same,syneq_refl] >>
  `Cclosed c v2 ∧ (∀v. v ∈ FRANGE rr0 ⇒ Cclosed c v)` by (
    qspecl_then[`c`,`d`,`s''`,`env0⊌env1`,`ee`,`(rr0,Rval v2)`]mp_tac(CONJUNCT1 Cevaluate_closed) >>
    fs[Abbr`ee`] >>
    qmatch_abbrev_tac`(P ⇒ Q) ⇒ R` >>
    `P` by (
      unabbrev_all_tac >>
      fsrw_tac[][SUBSET_DEF,fmap_rel_def,FDOM_DRESTRICT] >>
      match_mp_tac IN_FRANGE_FUNION_suff >>
      conj_tac >- (
        match_mp_tac IN_FRANGE_DRESTRICT_suff >> rw[] ) >>
      match_mp_tac IN_FRANGE_FUNION_suff >> fs[] >>
      match_mp_tac IN_FRANGE_DRESTRICT_suff >> rw[] ) >>
    rw[Abbr`Q`,Abbr`R`] ) >>
  `∀v. v ∈ FRANGE (env' |+ (n,v2)) ⇒ Cclosed c v` by (
    match_mp_tac IN_FRANGE_FUPDATE_suff >> rw[]) >>
  `∀v. v ∈ FRANGE (env1 |+ (n,v2)) ⇒ Cclosed c v` by (
    match_mp_tac IN_FRANGE_FUPDATE_suff >> rw[]) >>
  `∀v. v ∈ FRANGE (env \\ n) ⇒ Cclosed c v` by (
    match_mp_tac IN_FRANGE_DOMSUB_suff >> fs[] ) >>
  `Cclosed c v ∧ (∀v. v ∈ FRANGE s' ⇒ Cclosed c v)` by (
    qspecl_then[`c`,`d`,`s`,`env`,`ee`,`(s',Rval v)`]mp_tac(CONJUNCT1 Cevaluate_closed) >>
    fs[Abbr`ee`] >>
    qmatch_abbrev_tac`(P ⇒ Q) ⇒ R` >>
    `P` by (
      unabbrev_all_tac >>
      fsrw_tac[][SUBSET_DEF,fmap_rel_def,FDOM_DRESTRICT] ) >>
    rw[Abbr`Q`,Abbr`R`] ) >>
  asm_simp_tac bool_ss [] >>
  strip_tac >>
  PairCases_on`res` >> PairCases_on`res''` >> full_simp_tac std_ss [] >>
  qmatch_assum_rename_tac `result_rel (syneq c) res1 r1`[] >>
  qmatch_assum_rename_tac `fmap_rel (syneq c) res0 r0`[] >>
  qexists_tac `(r0,r1)` >> asm_simp_tac(srw_ss())[] >>
  qunabbrev_tac `env1` >>
  Q.PAT_ABBREV_TAC `env1 = X |+ (n,v2)` >>
  qunabbrev_tac `env0` >>
  qmatch_assum_abbrev_tac `Cevaluate c d rr0 (env0 ⊌ env1) b (r0,r1)` >>
  final0 ) >>
strip_tac >- (
  srw_tac[DNF_ss][Cevaluate_let,FOLDL_UNION_BIGUNION] >>
  disj2_tac >> fs[] >>
  full_simp_tac(pure_ss++(QUANT_INST_ss[pair_default_qp]))[] >>
  first_x_assum (qspecl_then [`s''`,`env'`] mp_tac) >> rw[] >>
  Q.PAT_ABBREV_TAC `env1 = X ⊌ env''` >>
  `∀v. v ∈ FRANGE env1 ⇒ Cclosed c v` by (
    unabbrev_all_tac >>
    match_mp_tac IN_FRANGE_FUNION_suff >> simp[] >>
    match_mp_tac IN_FRANGE_DRESTRICT_suff >> rw[] ) >>
  first_x_assum (qspec_then `env1` mp_tac) >> rw[] >>
  qmatch_assum_abbrev_tac `Cevaluate c d s'' (env0 ⊌ env1) ee rr` >>
  final0) >>
strip_tac >- (
  rw[FOLDL_UNION_BIGUNION_paired] >>
  rw[Once Cevaluate_cases] >>
  qpat_assum `LENGTH ns = LENGTH defs` assume_tac >>
  fs[FOLDL_FUPDATE_LIST,FDOM_FUPDATE_LIST,FOLDL2_FUPDATE_LIST_paired] >>
  fsrw_tac[DNF_ss][MAP2_MAP,MAP_ZIP,FST_triple,MAP_MAP_o,combinTheory.o_DEF] >>
  `free_vars c exp ⊆ FDOM env ∪ set ns` by (
    fsrw_tac[DNF_ss][SUBSET_DEF,pairTheory.FORALL_PROD] >>
    PROVE_TAC[] ) >>
  fs[] >> fsrw_tac[SATISFY_ss][] >>
  qho_match_abbrev_tac `∃res'. (Cevaluate c d s' (env0 |++ (ls0 env0)) exp res') ∧
    fmap_rel (syneq c) (FST res) (FST res') ∧
    result_rel (syneq c) (SND res) (SND res')` >>
  `fmap_rel (syneq c) (env |++ (ls0 env)) (env' |++ (ls0 env0))` by (
    unabbrev_all_tac >> fs[] >>
    match_mp_tac fmap_rel_FUPDATE_LIST_same >>
    fs[MAP_ZIP,MAP_MAP_o,combinTheory.o_DEF] >>
    fs[LIST_REL_EL_EQN,EL_MAP,EL_ZIP] >>
    qx_gen_tac `n` >> strip_tac >>
    rw[pairTheory.UNCURRY] >>
    rw[syneq_cases,EVERY_MEM,pairTheory.FORALL_PROD] >>
    fs[fmap_rel_def,optionTheory.OPTREL_def,FLOOKUP_DEF] >>
    `v ∈ FDOM env` by (
      fsrw_tac[DNF_ss][SUBSET_DEF,pairTheory.FORALL_PROD,MEM_EL] >>
      fsrw_tac[DNF_ss][pairTheory.UNCURRY,MEM_EL] >>
      metis_tac[pairTheory.FST,pairTheory.SND] ) >> fs[] >>
    qmatch_abbrev_tac `(v ∈ FDOM (DRESTRICT env0 ss) ∨ v ∈ FDOM env2) ∧ syneq c (env ' v) (env1 ' v)` >>
    `v ∈ ss` by (
      srw_tac[DNF_ss][Abbr`ss`,pairTheory.EXISTS_PROD] >>
      fsrw_tac[DNF_ss][SUBSET_DEF,pairTheory.UNCURRY,MEM_EL] >>
      metis_tac[pairTheory.FST,pairTheory.SND]) >>
    fs[DRESTRICT_DEF] >>
    rw[FUNION_DEF,DRESTRICT_DEF] ) >>
  first_x_assum (qspecl_then [`s'`,`env' |++ (ls0 env0)`,`env0 |++ ls0 env0`] mp_tac) >>
  `∀v. v ∈ FRANGE env0 ⇒ Cclosed c v` by (
    unabbrev_all_tac >>
    match_mp_tac IN_FRANGE_FUNION_suff >> simp[] >>
    match_mp_tac IN_FRANGE_DRESTRICT_suff >> rw[] ) >>
  `∀v. MEM v (MAP SND (ls0 env0)) ⇒ Cclosed c v` by (
    unabbrev_all_tac >>
    fsrw_tac[DNF_ss][MEM_MAP,pairTheory.FORALL_PROD,MEM_ZIP,EL_MAP] >>
    qx_gen_tac `n` >> strip_tac >> rw[EL_ZIP] >> rw[pairTheory.UNCURRY] >>
    asm_simp_tac(srw_ss())[Once Cclosed_cases] >>
    rw[DRESTRICT_DEF] >>
    fsrw_tac[DNF_ss][SUBSET_DEF,MEM_EL,pairTheory.UNCURRY] >>
    metis_tac[pairTheory.FST,pairTheory.SND,fmap_rel_def] ) >>
  `∀v. v ∈ FRANGE (env' |++ ls0 env0) ⇒ Cclosed c v` by (
    match_mp_tac IN_FRANGE_FUPDATE_LIST_suff >> fs[] ) >>
  `∀v. v ∈ FRANGE (env0 |++ ls0 env0) ⇒ Cclosed c v` by (
    match_mp_tac IN_FRANGE_FUPDATE_LIST_suff >> fs[] ) >>
  fs[] >>
  Q.PAT_ABBREV_TAC `P = ∀v. v ∈ FRANGE xxx ⇒ Cclosed c v` >>
  `P` by (
    qunabbrev_tac`P` >>
    ho_match_mp_tac IN_FRANGE_FUPDATE_LIST_suff >>
    srw_tac[][MAP_ZIP,LENGTH_ZIP,MEM_MAP,MEM_ZIP] >>
    rw[EL_MAP,EL_ZIP] >> rw[pairTheory.UNCURRY] >>
    rw[Once Cclosed_cases,SUBSET_DEF] >>
    fsrw_tac[DNF_ss][SUBSET_DEF] >>
    TRY (first_x_assum match_mp_tac >> fsrw_tac[DNF_ss][MEM_EL] >> PROVE_TAC[]) >>
    qmatch_assum_rename_tac `EL i defs = (xs,b)`[] >>
    first_x_assum (qspecl_then [`x`,`EL i defs`] mp_tac) >>
    fs[] >> PROVE_TAC[MEM_EL] ) >>
  fs[Abbr`ls0`] >>
  ntac 7 (pop_assum kall_tac) >>
  disch_then (Q.X_CHOOSE_THEN `res'` strip_assume_tac) >>
  qexists_tac `res'` >> fs[] >>
  unabbrev_all_tac >>
  qmatch_abbrev_tac `Cevaluate c d s' env1 ee rr` >>
  qmatch_assum_abbrev_tac `Cevaluate c d s' (env0 ⊌ env1) ee rr` >>
  qsuff_tac `env0 ⊌ env1 = env1` >- PROVE_TAC[] >>
  rw[GSYM SUBMAP_FUNION_ABSORPTION] >>
  unabbrev_all_tac >>
  ntac 3 (pop_assum kall_tac) >>
  fs[SUBMAP_DEF] >>
  qx_gen_tac `x` >> strip_tac >>
  qpat_assum `LENGTH ns = LENGTH defs` assume_tac >>
  conj_tac >- (
    fsrw_tac[DNF_ss][DRESTRICT_DEF,FDOM_FUPDATE_LIST,pairTheory.EXISTS_PROD,MAP_MAP_o,MEM_MAP,MEM_ZIP,LENGTH_ZIP,MEM_EL,EL_ZIP] >>
    PROVE_TAC[EL_ZIP,pairTheory.PAIR_EQ,pairTheory.pair_CASES] ) >>
  Cases_on `MEM x ns` >- (
    fsrw_tac[DNF_ss][DRESTRICT_DEF] >>
    match_mp_tac FUPDATE_LIST_APPLY_MEM >>
    fs[LENGTH_ZIP,MAP_ZIP,MEM_EL,MAP_MAP_o,combinTheory.o_DEF] >>
    qexists_tac `n` >>
    qpat_assum `n < LENGTH ns` mp_tac >>
    fs[] >> strip_tac >>
    reverse conj_tac >- (
      fs[EL_ALL_DISTINCT_EL_EQ] ) >>
    fs[EL_MAP] >>
    match_mp_tac FUPDATE_LIST_APPLY_MEM >>
    fs[MAP_ZIP,LENGTH_ZIP,MAP_MAP_o,combinTheory.o_DEF] >>
    qexists_tac `n` >> fs[] >>
    reverse conj_tac >- (
      fs[EL_ALL_DISTINCT_EL_EQ] ) >>
    fs[EL_MAP] ) >>
  fs[DRESTRICT_DEF,FDOM_FUPDATE_LIST,MAP_ZIP,MAP_MAP_o,combinTheory.o_DEF] >>
  match_mp_tac FUPDATE_LIST_APPLY_NOT_MEM_matchable >>
  fs[MAP_ZIP,MAP_MAP_o,combinTheory.o_DEF] >>
  match_mp_tac FUPDATE_LIST_APPLY_NOT_MEM_matchable >>
  fs[MAP_ZIP,MAP_MAP_o,combinTheory.o_DEF] >>
  fs[DRESTRICT_DEF,FUNION_DEF] ) >>
strip_tac >- (
  srw_tac[DNF_ss][] >>
  rw[syneq_cases,FLOOKUP_DEF] >>
  rw[DRESTRICT_DEF,optionTheory.OPTREL_def] >>
  `v ∈ FDOM env` by fs[SUBSET_DEF] >> fs[] >>
  fs[fmap_rel_def] >>
  rw[DRESTRICT_DEF,FUNION_DEF] ) >>
strip_tac >- (
  rpt gen_tac >> strip_tac >>
  rw[FOLDL_UNION_BIGUNION] >>
  qmatch_assum_rename_tac `fmap_rel (syneq c) env env2`[] >>
  qmatch_assum_rename_tac `fmap_rel (syneq c) s s2`[] >>
  rw[Once Cevaluate_cases] >>
  fsrw_tac[DNF_ss][] >>
  disj1_tac >>
  fsrw_tac[DNF_ss][Q.SPECL[`c`,`CRecClos env' ns defs n`]syneq_cases] >>
  qpat_assum `∀s env2 env0. fmap_rel (syneq c) env nv0 ∧ Z ⇒ P` (qspecl_then [`s2`,`env2`] mp_tac) >>
  fsrw_tac[DNF_ss][] >> rw[] >>
  Q.PAT_ABBREV_TAC `env0 = (X ⊌ Y : string |-> Cv) ` >>
  `∀v. v ∈ FRANGE env0 ⇒ Cclosed c v` by (
    unabbrev_all_tac >>
    match_mp_tac IN_FRANGE_FUNION_suff >> simp[] >>
    match_mp_tac IN_FRANGE_DRESTRICT_suff >> rw[]) >>
  first_x_assum (qspec_then `env0` mp_tac) >> fs[] >>
  full_simp_tac(pure_ss++(QUANT_INST_ss[pair_default_qp]))[] >>
  rw[] >>
  qmatch_assum_rename_tac `fmap_rel (syneq c) s' s3`[] >>
  qmatch_assum_abbrev_tac `Cevaluate c d s2 env1 exp (s3,Rval (CRecClos env3 ns defs n))` >>
  CONV_TAC SWAP_EXISTS_CONV >> qexists_tac `env3` >>
  CONV_TAC SWAP_EXISTS_CONV >> qexists_tac `ns` >>
  CONV_TAC SWAP_EXISTS_CONV >> qexists_tac `defs` >>
  CONV_TAC SWAP_EXISTS_CONV >> qexists_tac `n` >>
  `env1 = env0` by (
    unabbrev_all_tac >>
    rw[GSYM SUBMAP_FUNION_ABSORPTION] >>
    rw[SUBMAP_DEF,DRESTRICT_DEF,FUNION_DEF] ) >>
  unabbrev_all_tac >>
  fsrw_tac[DNF_ss][] >>
  fsrw_tac[ETA_ss][] >>
  pop_assum kall_tac >>
  qexists_tac`s3` >> simp[] >>
  `(∀v. v ∈ FRANGE s' ⇒ Cclosed c v) ∧
   Cclosed c (CRecClos env' ns defs n)` by (
    qspecl_then[`c`,`d`,`s`,`env`,`exp`,`(s',Rval (CRecClos env' ns defs n))`]mp_tac(CONJUNCT1 Cevaluate_closed) >>
    rw[] ) >> fs[] >>
  `(∀v. v ∈ FRANGE s3 ⇒ Cclosed c v) ∧
   Cclosed c (CRecClos env2' ns defs n)` by (
    qmatch_assum_abbrev_tac`Cevaluate c d s2 env4 exp (s3,vv)` >>
    qspecl_then[`c`,`d`,`s2`,`env4`,`exp`,`(s3,vv)`]mp_tac(CONJUNCT1 Cevaluate_closed) >>
    map_every qunabbrev_tac[`env4`,`vv`] >>
    simp[FDOM_DRESTRICT] >>
    fsrw_tac[DNF_ss][SUBSET_DEF] >>
    fs[fmap_rel_def] ) >>
  Q.PAT_ABBREV_TAC`env3 = X ⊌ env'''` >>
  POP_ASSUM_LIST (map_every ASSUME_TAC) >>
  first_x_assum (qspecl_then[`s3`,`env2`,`env3`]mp_tac) >>
  `∀v. v ∈ FRANGE env3 ⇒ Cclosed c v` by (
    qunabbrev_tac`env3` >>
    match_mp_tac IN_FRANGE_FUNION_suff >> simp[] >>
    match_mp_tac IN_FRANGE_DRESTRICT_suff >> rw[] ) >>
  simp[] >>
  disch_then(Q.X_CHOOSE_THEN`v2`mp_tac) >>
  disch_then(Q.X_CHOOSE_THEN`s4`strip_assume_tac) >>
  qexists_tac`i`>>simp[] >>
  map_every qexists_tac [`s4`,`v2`] >>
  qmatch_assum_abbrev_tac `Cevaluate_list c d s3 env4 exps rr` >>
  `env4 = env3` by (
    map_every qunabbrev_tac[`env4`,`env3`] >>
    rw[GSYM SUBMAP_FUNION_ABSORPTION] >>
    match_mp_tac SUBMAP_FUNION >>
    disj1_tac >>
    match_mp_tac DRESTRICT_SUBSET_SUBMAP >>
    rw[] ) >>
  qunabbrev_tac`rr` >>
  fs[] >>
  ntac 2 (pop_assum kall_tac) >>
  fs[EVERY2_EVERY] >>
  `EVERY (Cclosed c) vs ∧
   (∀v. v ∈ FRANGE s'' ⇒ Cclosed c v)` by (
    qspecl_then[`c`,`d`,`s'`,`env`,`exps`,`(s'',Rval vs)`]mp_tac(CONJUNCT2 Cevaluate_closed) >>
    simp[] ) >>
  `EVERY (Cclosed c) v2 ∧
   (∀v. v ∈ FRANGE s4 ⇒ Cclosed c v)` by (
     qspecl_then[`c`,`d`,`s3`,`env3`,`exps`,`(s4,Rval v2)`]mp_tac(CONJUNCT2 Cevaluate_closed) >>
     simp[] >>
     fs[Abbr`env3`,FDOM_DRESTRICT] >>
     fs[fmap_rel_def] >>
     fsrw_tac[DNF_ss][SUBSET_DEF] ) >>
  fs[Once(Q.SPECL[`c`,`CRecClos env2' ns defs n`] Cclosed_cases)] >>
  `∀v. v ∈ FRANGE (extend_rec_env env' env' ns defs xs vs) ⇒ Cclosed c v` by (
    fs[extend_rec_env_def,FOLDL2_FUPDATE_LIST,FOLDL_FUPDATE_LIST] >>
    match_mp_tac IN_FRANGE_FUPDATE_LIST_suff >>
    fsrw_tac[DNF_ss][MAP_ZIP,MAP2_MAP,SND_pair,FST_pair,MEM_EL,LENGTH_ZIP,EVERY_MEM] >>
    match_mp_tac IN_FRANGE_FUPDATE_LIST_suff >>
    fsrw_tac[DNF_ss][MAP_ZIP,MAP2_MAP,SND_pair,FST_pair,MEM_EL,LENGTH_ZIP,MAP_MAP_o,EL_MAP] >>
    rw[Once Cclosed_cases,MEM_EL] >> fs[] >>
    PROVE_TAC[] ) >>
  fs[] >>
  qunabbrev_tac`env3` >>
  qabbrev_tac`env3 = extend_rec_env env2' env2' ns defs xs v2` >>
  qmatch_assum_abbrev_tac `Cevaluate c d s'' X exp' res` >>
  qunabbrev_tac`X` >>
  `i < LENGTH defs` by (
    Cases_on`ns=[]`>>fs[] >>
    imp_res_tac find_index_LESS_LENGTH >>
    fs[] >> rfs[] ) >>
  `free_vars c exp' ⊆ FDOM env' ∪ set ns ∪ set xs` by (
    fsrw_tac[DNF_ss][SUBSET_DEF] >>
    first_x_assum (qspecl_then [`i`,`xs`,`cb`] mp_tac) >>
    rw[] >> fs[EVERY_MEM] >>
    `MEM (xs,cb) defs` by (rw[MEM_EL] >> qexists_tac `i` >> rw[] >> PROVE_TAC[] ) >>
    fsrw_tac[DNF_ss][optionTheory.OPTREL_def,FLOOKUP_DEF,FORALL_PROD] >>
    first_x_assum (qspecl_then [`xs`,`cb`] mp_tac) >> rw[] >>
    pop_assum (qspec_then `x` mp_tac) >> rw[] >>
    Cases_on`ns=[]`>>fs[]>>
    TRY(qunabbrev_tac`exp'`) >> Cases_on `cb` >> fs[] >>
    fs[FLOOKUP_DEF] >> rw[] >>
    `x ∈ free_vars (c \\ y) (c ' y)` by
      metis_tac[free_vars_DOMSUB,SUBSET_DEF,IN_UNION] >>
    ntac 3 (pop_assum mp_tac) >> rw[] >> fs[] >>
    fsrw_tac[DNF_ss][MEM_EL] >>
    metis_tac[]) >>
  fs[] >>
  qabbrev_tac `env4 =
    extend_rec_env env2' (DRESTRICT env2' (free_vars c exp' DIFF set xs DIFF set ns) ⊌ env') ns defs xs v2` >>
  `∀v. v ∈ FRANGE env4 ⇒ Cclosed c v` by (
    unabbrev_all_tac >>
    fs[extend_rec_env_def,FOLDL2_FUPDATE_LIST,FOLDL_FUPDATE_LIST] >>
    match_mp_tac IN_FRANGE_FUPDATE_LIST_suff >>
    fsrw_tac[DNF_ss][MAP_ZIP,MAP2_MAP,SND_pair,FST_pair,MEM_EL,EVERY_MEM] >>
    match_mp_tac IN_FRANGE_FUPDATE_LIST_suff >>
    fsrw_tac[DNF_ss][MAP_ZIP,MAP2_MAP,SND_pair,FST_pair,MEM_EL,MAP_MAP_o,EL_MAP] >>
    conj_tac >- (
      match_mp_tac IN_FRANGE_FUNION_suff >> fs[] >>
      match_mp_tac IN_FRANGE_DRESTRICT_suff >> fs[] ) >>
    simp_tac(srw_ss())[Once Cclosed_cases,MEM_EL] >>
    fsrw_tac[DNF_ss][] >>
    conj_tac >- metis_tac[] >>
    fsrw_tac[DNF_ss][SUBSET_DEF] >>
    metis_tac[]) >>
  first_x_assum (qspecl_then[`s4`,`env4`,`env3`]mp_tac) >>
  `∀v. v ∈ FRANGE env3 ⇒ Cclosed c v` by (
    unabbrev_all_tac >>
    fs[extend_rec_env_def,FOLDL2_FUPDATE_LIST,FOLDL_FUPDATE_LIST] >>
    match_mp_tac IN_FRANGE_FUPDATE_LIST_suff >>
    fsrw_tac[DNF_ss][MAP_ZIP,MAP2_MAP,SND_pair,FST_pair,MEM_EL,EVERY_MEM] >>
    match_mp_tac IN_FRANGE_FUPDATE_LIST_suff >>
    fsrw_tac[DNF_ss][MAP_ZIP,MAP2_MAP,SND_pair,FST_pair,MEM_EL,MAP_MAP_o,EL_MAP] >>
    simp_tac(srw_ss())[Once Cclosed_cases,MEM_EL] >>
    fsrw_tac[DNF_ss][] >>
    conj_tac >- metis_tac[] >>
    fsrw_tac[DNF_ss][SUBSET_DEF] >>
    metis_tac[] ) >>
  fs[] >>
  Q.PAT_ABBREV_TAC `P = fmap_rel (syneq c) X Y` >>
  `P` by (
    unabbrev_all_tac >>
    match_mp_tac fmap_rel_extend_rec_env_same >>
    fs[LIST_REL_EL_EQN] >>
    fs[fmap_rel_def,DRESTRICT_DEF,FUNION_DEF,GSYM SUBSET_UNION_ABSORPTION] >>
    conj_tac >- (
      conj_tac >- (fsrw_tac[DNF_ss][SUBSET_DEF] >> metis_tac[]) >>
      rw[] >>
      fs[FLOOKUP_DEF,optionTheory.OPTREL_def] >>
      `MEM (xs,cb) defs` by (rw[MEM_EL] >> qexists_tac `i` >> rw[] >> PROVE_TAC[] ) >>
      fsrw_tac[DNF_ss][EVERY_MEM,FORALL_PROD] >>
      first_x_assum (qspecl_then [`xs`,`cb`] mp_tac) >> fs[] >>
      first_x_assum (qspecl_then [`i`,`xs`,`cb`] mp_tac) >> fs[] >>
      Cases_on `cb` >> fs[] >- metis_tac[] >>
      Cases_on `ns = []` >> fs[] >>
      rw[FLOOKUP_DEF] >> fs[] >>
      `x ∈ free_vars (c \\ y) (c ' y)` by
        metis_tac[free_vars_DOMSUB,IN_UNION,SUBSET_DEF] >>
      fsrw_tac[DNF_ss][SUBSET_DEF] >>
      TRY(first_x_assum (qspecl_then [`i`,`xs`,`y`] mp_tac) >> fs[]) >>
      metis_tac []) >>
    qpat_assum`LENGTH vs = LENGTH v2`assume_tac >>
    fs[EVERY_MEM,pairTheory.FORALL_PROD,MEM_ZIP] >>
    fsrw_tac[DNF_ss][] >>
    simp_tac(srw_ss())[Once syneq_cases] >>
    fs[EVERY_MEM,pairTheory.FORALL_PROD] >>
    rw[] >>
    fs[FLOOKUP_DEF,optionTheory.OPTREL_def] >>
    fs[FUNION_DEF,DRESTRICT_DEF] >>
    metis_tac[syneq_refl,syneq_sym] ) >>
  fs[] >>
  disch_then (Q.X_CHOOSE_THEN `rr` strip_assume_tac) >>
  qmatch_assum_abbrev_tac `Cevaluate c d s4 (env0 ⊌ env1) ee rrr` >>
  qsuff_tac `env0 ⊌ env1 = env1` >- (
    Cases_on`cb`>>fs[FLOOKUP_DEF] >> rw[] >> fs[] >>
    METIS_TAC[SND]) >>
  rw[GSYM SUBMAP_FUNION_ABSORPTION] >>
  qunabbrev_tac `env0` >>
  qunabbrev_tac `env1` >>
  qunabbrev_tac `env4` >>
  rw[Once extend_rec_env_FUNION] >>
  qunabbrev_tac `env3` >>
  rw[DRESTRICTED_FUNION] >>
  rw[DIFF_UNION,DRESTRICT_DEF] >>
  Q.PAT_ABBREV_TAC `ss = free_vars c ee DIFF Y DIFF Z DIFF ZZ` >>
  `ss = {}` by (
    unabbrev_all_tac >>
    rw[EXTENSION] >>
    fs[SUBSET_DEF,fmap_rel_def] >>
    Cases_on `MEM x xs` >> fs[] >>
    Cases_on `MEM x ns` >> fs[] >>
    Cases_on `x ∈ FDOM env2'` >> fs[] >>
    Cases_on `ns = []` >> fs[] >> rw[] >>
    TRY(first_x_assum (qspecl_then [`i`,`xs`,`cb`] mp_tac)) >>
    TRY(first_x_assum (qspecl_then [`i`,`xs`,`cb`] mp_tac)) >>
    fs[] >>
    Cases_on `cb` >> fs[] >- METIS_TAC[] >>
    rw[FLOOKUP_DEF] >>
    fs[FLOOKUP_DEF] >> rfs[] >>
    rpt (pop_assum (qspec_then `x` mp_tac)) >> fs[] >>
    PROVE_TAC[free_vars_DOMSUB,IN_UNION,SUBSET_DEF]) >>
  rw[DRESTRICT_IS_FEMPTY,FUNION_FEMPTY_2] >>
  rw[DIFF_COMM] >>
  Q.ISPECL_THEN [`extend_rec_env env2' FEMPTY ns defs xs v2`,`env2'`,`free_vars c ee`] (mp_tac o GSYM) DRESTRICTED_FUNION >>
  rw[DIFF_UNION,DIFF_COMM] >>
  rw[GSYM extend_rec_env_FUNION]) >>
strip_tac >- (
  rw[FOLDL_UNION_BIGUNION] >>
  qmatch_assum_rename_tac `fmap_rel (syneq c) env env2`[] >>
  qmatch_assum_rename_tac `fmap_rel (syneq c) s s2`[] >>
  rw[Once Cevaluate_cases] >>
  fsrw_tac[DNF_ss][] >>
  disj2_tac >> disj1_tac >>
  fsrw_tac[DNF_ss][Q.SPECL[`c`,`CRecClos env' ns' defs n`]syneq_cases] >>
  qpat_assum `∀s env2 env0. fmap_rel (syneq c) env nv0 ∧ Z ⇒ P` (qspecl_then [`s2`,`env2`] mp_tac) >>
  fsrw_tac[DNF_ss][] >> rw[] >>
  Q.PAT_ABBREV_TAC `env0 = (X ⊌ Y : string |-> Cv) ` >>
  `∀v. v ∈ FRANGE env0 ⇒ Cclosed c v` by (
    unabbrev_all_tac >>
    match_mp_tac IN_FRANGE_FUNION_suff >> simp[] >>
    match_mp_tac IN_FRANGE_DRESTRICT_suff >> rw[]) >>
  first_x_assum (qspec_then `env0` mp_tac) >> fs[] >>
  full_simp_tac(pure_ss++(QUANT_INST_ss[pair_default_qp]))[] >>
  rw[] >>
  qmatch_assum_rename_tac `fmap_rel (syneq c) s' s3`[] >>
  qmatch_assum_abbrev_tac `Cevaluate c d s2 env1 exp (s3,Rval v3)` >>
  map_every qexists_tac[`s3`,`v3`] >>
  `env1 = env0` by (
    unabbrev_all_tac >>
    rw[GSYM SUBMAP_FUNION_ABSORPTION] >>
    rw[SUBMAP_DEF,DRESTRICT_DEF,FUNION_DEF] ) >>
  unabbrev_all_tac >>
  fsrw_tac[DNF_ss][] >>
  fsrw_tac[ETA_ss][] >>
  pop_assum kall_tac >>
  Q.PAT_ABBREV_TAC`env3 = X ⊌ env''` >>
  first_x_assum (qspecl_then[`s3`,`env2`,`env3`]mp_tac) >>
  `(∀v. v ∈ FRANGE s' ⇒ Cclosed c v) ∧ Cclosed c v` by (
    qspecl_then[`c`,`d`,`s`,`env`,`exp`,`(s',Rval v)`]mp_tac(CONJUNCT1 Cevaluate_closed) >>
    rw[] ) >> fs[] >>
  `(∀v. v ∈ FRANGE s3 ⇒ Cclosed c v) ∧ Cclosed c v'` by (
    qmatch_assum_abbrev_tac`Cevaluate c d s2 env3 exp (s3,vv)` >>
    qspecl_then[`c`,`d`,`s2`,`env3`,`exp`,`(s3,vv)`]mp_tac(CONJUNCT1 Cevaluate_closed) >>
    map_every qunabbrev_tac[`env3`,`vv`] >>
    simp[FDOM_DRESTRICT] >>
    fsrw_tac[DNF_ss][SUBSET_DEF] >>
    fs[fmap_rel_def] ) >>
  simp[] >>
  Q.PAT_ABBREV_TAC`env1 = X ⊌ env3` >>
  qsuff_tac`env1 = env3` >- rw[] >>
  unabbrev_all_tac >>
  rw[GSYM SUBMAP_FUNION_ABSORPTION] >>
  match_mp_tac SUBMAP_FUNION >>
  disj1_tac >>
  match_mp_tac DRESTRICT_SUBSET_SUBMAP >>
  rw[]) >>
strip_tac >- (
  rw[FOLDL_UNION_BIGUNION] >>
  rw[Once Cevaluate_cases] >>
  fsrw_tac[DNF_ss][] >>
  disj2_tac >> disj2_tac >>
  Q.PAT_ABBREV_TAC`env1 = Z : string |-> Cv` >>
  first_x_assum (qspecl_then [`s''`,`env'`,`env1`] mp_tac) >> rw[] >>
  `∀v. v ∈ FRANGE env1 ⇒ Cclosed c v` by (
    unabbrev_all_tac >>
    ho_match_mp_tac IN_FRANGE_FUNION_suff >> fs[] >>
    ho_match_mp_tac IN_FRANGE_DRESTRICT_suff >> fs[] ) >> fs[] >>
  unabbrev_all_tac >>
  fs[DRESTRICT_FUNION,FUNION_ASSOC] >>
  fs[UNION_ASSOC] >>
  Cases_on`res'`>>fs[]>>
  fsrw_tac[SATISFY_ss][]) >>
strip_tac >- (
  rw[] >>
  rw[Once Cevaluate_cases] >>
  fsrw_tac[DNF_ss][] >>
  disj1_tac >>
  qmatch_assum_rename_tac`fmap_rel (syneq c) env env1`[] >>
  qmatch_assum_rename_tac`fmap_rel (syneq c) s s1`[] >>
  first_x_assum(qspecl_then[`s1`,`env1`,`env''`]mp_tac) >>
  simp[] >>
  disch_then(Q.X_CHOOSE_THEN`r`strip_assume_tac) >>
  PairCases_on`r`>>fs[] >>
  map_every qexists_tac[`r0`,`v'`] >>
  simp[] >>
  Cases_on`uop`>>fs[LET_THM] >- (
    simp[Once syneq_cases] >>
    conj_asm2_tac >- (
      simp[] >>
      match_mp_tac fmap_rel_FUPDATE_same >>
      rw[] ) >>
    AP_TERM_TAC >>
    fs[fmap_rel_def] ) >>
  qmatch_assum_rename_tac`syneq c v1 v2`[] >>
  Cases_on`v1`>>TRY(Cases_on`l`)>>
  Cases_on`v2`>>TRY(Cases_on`l`)>>
  fs[Once syneq_cases] >>
  fs[fmap_rel_def,FLOOKUP_DEF] >>
  rw[] ) >>
strip_tac >- (
  rw[] >>
  rw[Once Cevaluate_cases] >>
  fsrw_tac[DNF_ss][] >>
  disj2_tac >>
  qmatch_assum_rename_tac`fmap_rel (syneq c) env env1`[] >>
  qmatch_assum_rename_tac`fmap_rel (syneq c) s s1`[] >>
  first_x_assum(qspecl_then[`s1`,`env1`,`env''`]mp_tac) >>
  simp[] >>
  disch_then(Q.X_CHOOSE_THEN`r`strip_assume_tac) >>
  PairCases_on`r`>>fs[] >>
  qexists_tac`r0`>>rw[] ) >>
strip_tac >- (
  rw[] >>
  rw[Once Cevaluate_cases] >>
  fsrw_tac[DNF_ss][] >>
  disj1_tac >>
  qmatch_assum_rename_tac `fmap_rel (syneq c) env env2`[] >>
  qmatch_assum_rename_tac `fmap_rel (syneq c) s s2`[] >>
  Q.PAT_ABBREV_TAC `env3 = (DRESTRICT env2 X) ⊌ Y` >>
  `∀v. v ∈ FRANGE env3 ⇒ Cclosed c v` by (
    unabbrev_all_tac >>
    match_mp_tac IN_FRANGE_FUNION_suff >> fs[] >>
    match_mp_tac IN_FRANGE_DRESTRICT_suff >> fs[] ) >>
  first_x_assum (qspecl_then [`s2`,`env2`,`env3`] mp_tac) >>
  fs[DRESTRICT_IS_FEMPTY,FUNION_FEMPTY_1] >> rw[] >>
  fs[EVERY2_EVERY] >>
  qmatch_assum_rename_tac `syneq c v1 w1`[] >>
  qmatch_assum_rename_tac `syneq c v2 w2`[] >>
  Cases_on`ress'`>>fs[]>>rw[] >>
  qmatch_assum_rename_tac `fmap_rel (syneq c) s' s3`[] >>
  map_every qexists_tac [`s3`,`w1`,`w2`] >>
  fs[] >>
  `DRESTRICT env2 (free_vars c e1 ∪ free_vars c e2) ⊌ env3 = env3` by (
    rw[GSYM SUBMAP_FUNION_ABSORPTION] >>
    unabbrev_all_tac >>
    match_mp_tac SUBMAP_FUNION >>
    disj1_tac >> rw[] ) >>
  fs[] >>
  qsuff_tac `CevalPrim2 p2 v1 v2 = CevalPrim2 p2 w1 w2` >- rw[] >>
  PROVE_TAC[CevalPrim2_syneq,syneq_refl,syneq_trans]) >>
strip_tac >- (
  rw[] >>
  rw[Once Cevaluate_cases] >>
  fsrw_tac[DNF_ss][] >>
  disj2_tac >>
  full_simp_tac(pure_ss++(QUANT_INST_ss[pair_default_qp]))[] >>
  first_x_assum (match_mp_tac o MP_CANON) >>
  rw[] ) >>
strip_tac >- (
  rw[] >>
  rw[Once Cevaluate_cases] >>
  fsrw_tac[DNF_ss][] >>
  disj1_tac >>
  qmatch_assum_rename_tac `fmap_rel (syneq c) env env2`[] >>
  qmatch_assum_rename_tac `fmap_rel (syneq c) s s2`[] >>
  Q.PAT_ABBREV_TAC `env3 = (DRESTRICT env2 X) ⊌ Y` >>
  `∀v. v ∈ FRANGE env3 ⇒ Cclosed c v` by (
    unabbrev_all_tac >>
    match_mp_tac IN_FRANGE_FUNION_suff >> fs[] >>
    match_mp_tac IN_FRANGE_DRESTRICT_suff >> fs[] ) >>
  first_x_assum (qspecl_then [`s2`,`env2`,`env3`] mp_tac) >>
  fs[DRESTRICT_IS_FEMPTY,FUNION_FEMPTY_1] >> rw[] >>
  fs[EVERY2_EVERY] >>
  qmatch_assum_rename_tac `syneq c v1 w1`[] >>
  qmatch_assum_rename_tac `syneq c v2 w2`[] >>
  Cases_on`ress'`>>fs[]>>rw[] >>
  qmatch_assum_rename_tac `fmap_rel (syneq c) s' s3`[] >>
  map_every qexists_tac [`s3`,`w1`,`w2`] >>
  fs[] >>
  `DRESTRICT env2 (free_vars c e1 ∪ free_vars c e2) ⊌ env3 = env3` by (
    rw[GSYM SUBMAP_FUNION_ABSORPTION] >>
    unabbrev_all_tac >>
    match_mp_tac SUBMAP_FUNION >>
    disj1_tac >> rw[] ) >>
  fs[] >>
  match_mp_tac CevalUpd_syneq >>
  rw[]) >>
strip_tac >- (
  rw[] >>
  rw[Once Cevaluate_cases] >>
  fsrw_tac[DNF_ss][] >>
  disj2_tac >>
  full_simp_tac(pure_ss++(QUANT_INST_ss[pair_default_qp]))[] >>
  first_x_assum (match_mp_tac o MP_CANON) >>
  rw[] ) >>
strip_tac >- (
  rpt gen_tac >>
  rpt strip_tac >>
  fsrw_tac[DNF_ss][] >>
  qmatch_assum_rename_tac `fmap_rel (syneq c) env env2`[] >>
  qmatch_assum_rename_tac `fmap_rel (syneq c) s s2`[] >>
  Q.PAT_ABBREV_TAC `env3 = (DRESTRICT env2 X) ⊌ Y` >>
  `∀v. v ∈ FRANGE env3 ⇒ Cclosed c v` by (
    unabbrev_all_tac >>
    match_mp_tac IN_FRANGE_FUNION_suff >> fs[] >>
    match_mp_tac IN_FRANGE_DRESTRICT_suff >> fs[] ) >>
  rw[Once Cevaluate_cases] >>
  fsrw_tac[DNF_ss][] >>
  disj1_tac >>
  fs[Q.SPECL[`c`,`CLitv(Bool b1)`]syneq_cases] >>
  CONV_TAC (RESORT_EXISTS_CONV List.rev) >> qexists_tac `b1` >>
  `free_vars c (if b1 then e2 else e3) ⊆ FDOM env` by rw[] >>
  POP_ASSUM_LIST (map_every ASSUME_TAC) >>
  first_x_assum (qspecl_then [`s2`,`env2`,`env3`] mp_tac) >>
  fs[] >>
  `DRESTRICT env2 (free_vars c exp) ⊌ env3 = env3` by (
    rw[GSYM SUBMAP_FUNION_ABSORPTION] >>
    unabbrev_all_tac >>
    match_mp_tac SUBMAP_FUNION >>
    disj1_tac >>
    match_mp_tac DRESTRICT_SUBSET_SUBMAP >>
    srw_tac[DNF_ss][SUBSET_DEF]) >> fs[] >>
  full_simp_tac(pure_ss++(QUANT_INST_ss[pair_default_qp]))[] >>
  disch_then(Q.X_CHOOSE_THEN`s3`strip_assume_tac) >>
  first_x_assum (qspecl_then [`s3`,`env2`,`env3`] mp_tac) >>
  fs[] >>
  `∀v. v ∈ FRANGE s' ⇒ Cclosed c v` by (
    qspecl_then[`c`,`d`,`s`,`env`,`exp`,`(s',Rval(CLitv(Bool b1)))`]mp_tac(CONJUNCT1 Cevaluate_closed) >>
    rw[] ) >>
  `∀v. v ∈ FRANGE s3 ⇒ Cclosed c v` by (
    qspecl_then[`c`,`d`,`s2`,`env3`,`exp`,`s3,Rval(CLitv(Bool b1))`]mp_tac(CONJUNCT1 Cevaluate_closed) >>
    `free_vars c exp ⊆ FDOM env3` by (
     rw[Abbr`env3`,FDOM_DRESTRICT] >>
     fsrw_tac[DNF_ss][SUBSET_DEF,fmap_rel_def] ) >>
    rw[] ) >>
  simp[] >>
  `DRESTRICT env2 (free_vars c (if b1 then e2 else e3)) ⊌ env3 = env3` by (
    rw[GSYM SUBMAP_FUNION_ABSORPTION] >>
    unabbrev_all_tac >>
    match_mp_tac SUBMAP_FUNION >>
    disj1_tac >>
    match_mp_tac DRESTRICT_SUBSET_SUBMAP >>
    srw_tac[DNF_ss][SUBSET_DEF]) >> fs[] >>
  metis_tac[]) >>
strip_tac >- (
  rw[] >>
  rw[Once Cevaluate_cases] >>
  fsrw_tac[DNF_ss][] >>
  disj2_tac >>
  qmatch_assum_rename_tac `fmap_rel (syneq c) env env2`[] >>
  qmatch_assum_rename_tac `fmap_rel (syneq c) s s2`[] >>
  Q.PAT_ABBREV_TAC `env3 = (DRESTRICT env2 X) ⊌ Y` >>
  `∀v. v ∈ FRANGE env3 ⇒ Cclosed c v` by (
    unabbrev_all_tac >>
    match_mp_tac IN_FRANGE_FUNION_suff >> fs[] >>
    match_mp_tac IN_FRANGE_DRESTRICT_suff >> fs[] ) >>
  first_x_assum (qspecl_then [`s2`,`env2`,`env3`] mp_tac) >>
  fs[] >>
  `DRESTRICT env2 (free_vars c exp) ⊌ env3 = env3` by (
    rw[GSYM SUBMAP_FUNION_ABSORPTION] >>
    unabbrev_all_tac >>
    match_mp_tac SUBMAP_FUNION >>
    disj1_tac >>
    match_mp_tac DRESTRICT_SUBSET_SUBMAP >>
    srw_tac[DNF_ss][SUBSET_DEF]) >> fs[] >>
  full_simp_tac(pure_ss++(QUANT_INST_ss[pair_default_qp]))[]) >>
strip_tac >- ( rw[] >> rw[Once Cevaluate_cases] ) >>
strip_tac >- (
  rw[] >>
  rw[Once Cevaluate_cases] >>
  fsrw_tac[DNF_ss][] >>
  full_simp_tac(pure_ss++(QUANT_INST_ss[pair_default_qp]))[] >>
  qmatch_assum_rename_tac`fmap_rel (syneq c) env env2`[] >>
  qmatch_assum_rename_tac`fmap_rel (syneq c) s s2`[] >>
  POP_ASSUM_LIST (map_every ASSUME_TAC) >>
  Q.PAT_ABBREV_TAC`env3 = (DRESTRICT env2 X) ⊌ Y` >>
  first_x_assum (qspecl_then[`s2`,`env2`,`env3`]mp_tac) >>
  `∀v. v ∈ FRANGE env3 ⇒ Cclosed c v` by (
    simp[Abbr`env3`] >>
    match_mp_tac IN_FRANGE_FUNION_suff >> simp[] >>
    match_mp_tac IN_FRANGE_DRESTRICT_suff >> rw[] ) >>
  simp[] >>
  `DRESTRICT env2 (free_vars c exp) ⊌ env3 = env3` by (
    rw[GSYM SUBMAP_FUNION_ABSORPTION] >>
    rw[Abbr`env3`] >>
    match_mp_tac SUBMAP_FUNION >>
    disj1_tac >>
    match_mp_tac DRESTRICT_SUBSET_SUBMAP >>
    rw[] ) >> simp[] >>
  disch_then(Q.X_CHOOSE_THEN`w`mp_tac) >>
  disch_then(Q.X_CHOOSE_THEN`s4`strip_assume_tac) >>
  first_x_assum (qspecl_then[`s4`,`env2`,`env3`]mp_tac) >>
  `∀v. v ∈ FRANGE s4 ⇒ Cclosed c v` by (
    qspecl_then[`c`,`d`,`s2`,`env3`,`exp`,`(s4,Rval w)`]mp_tac(CONJUNCT1 Cevaluate_closed) >>
    `free_vars c exp ⊆ FDOM env3` by (
      simp[Abbr`env3`,FDOM_DRESTRICT] >>
      fsrw_tac[DNF_ss][SUBSET_DEF,fmap_rel_def] ) >>
    rw[] ) >>
  `∀v. v ∈ FRANGE s' ⇒ Cclosed c v` by (
    qspecl_then[`c`,`d`,`s`,`env`,`exp`,`(s',Rval v)`]mp_tac(CONJUNCT1 Cevaluate_closed) >>
    rw[] ) >>
  simp[] >>
  `DRESTRICT env2 (BIGUNION (IMAGE (free_vars c) (set exps))) ⊌ env3 = env3` by (
    rw[GSYM SUBMAP_FUNION_ABSORPTION] >>
    rw[Abbr`env3`] >>
    match_mp_tac SUBMAP_FUNION >>
    disj1_tac >>
    match_mp_tac DRESTRICT_SUBSET_SUBMAP >>
    rw[] ) >>
  simp[] >> metis_tac[] ) >>
strip_tac >- (
  rw[] >>
  rw[Once Cevaluate_cases] >>
  fsrw_tac[DNF_ss][] >>
  disj1_tac >>
  full_simp_tac(pure_ss++(QUANT_INST_ss[pair_default_qp]))[] >>
  qmatch_assum_rename_tac`fmap_rel (syneq c) env env2`[] >>
  qmatch_assum_rename_tac`fmap_rel (syneq c) s s2`[] >>
  Q.PAT_ABBREV_TAC`env3 = (DRESTRICT env2 X) ⊌ Y` >>
  first_x_assum (qspecl_then[`s2`,`env2`,`env3`]mp_tac) >>
  `∀v. v ∈ FRANGE env3 ⇒ Cclosed c v` by (
    simp[Abbr`env3`] >>
    match_mp_tac IN_FRANGE_FUNION_suff >> simp[] >>
    match_mp_tac IN_FRANGE_DRESTRICT_suff >> rw[] ) >>
  simp[] >>
  `DRESTRICT env2 (free_vars c exp) ⊌ env3 = env3` by (
    rw[GSYM SUBMAP_FUNION_ABSORPTION] >>
    rw[Abbr`env3`] >>
    match_mp_tac SUBMAP_FUNION >>
    disj1_tac >>
    match_mp_tac DRESTRICT_SUBSET_SUBMAP >>
    rw[] ) >> simp[] ) >>
rw[] >>
rw[Once Cevaluate_cases] >>
fsrw_tac[DNF_ss][] >>
disj2_tac >>
full_simp_tac(pure_ss++(QUANT_INST_ss[pair_default_qp]))[] >>
qmatch_assum_rename_tac`fmap_rel (syneq c) env env2`[] >>
qmatch_assum_rename_tac`fmap_rel (syneq c) s s2`[] >>
POP_ASSUM_LIST (map_every ASSUME_TAC) >>
Q.PAT_ABBREV_TAC`env3 = (DRESTRICT env2 X) ⊌ Y` >>
first_x_assum (qspecl_then[`s2`,`env2`,`env3`]mp_tac) >>
`∀v. v ∈ FRANGE env3 ⇒ Cclosed c v` by (
  simp[Abbr`env3`] >>
  match_mp_tac IN_FRANGE_FUNION_suff >> simp[] >>
  match_mp_tac IN_FRANGE_DRESTRICT_suff >> rw[] ) >>
simp[] >>
`DRESTRICT env2 (free_vars c exp) ⊌ env3 = env3` by (
  rw[GSYM SUBMAP_FUNION_ABSORPTION] >>
  rw[Abbr`env3`] >>
  match_mp_tac SUBMAP_FUNION >>
  disj1_tac >>
  match_mp_tac DRESTRICT_SUBSET_SUBMAP >>
  rw[] ) >> simp[] >>
disch_then(Q.X_CHOOSE_THEN`w`mp_tac) >>
disch_then(Q.X_CHOOSE_THEN`s4`strip_assume_tac) >>
first_x_assum (qspecl_then[`s4`,`env2`,`env3`]mp_tac) >>
`∀v. v ∈ FRANGE s4 ⇒ Cclosed c v` by (
  qspecl_then[`c`,`d`,`s2`,`env3`,`exp`,`(s4,Rval w)`]mp_tac(CONJUNCT1 Cevaluate_closed) >>
  `free_vars c exp ⊆ FDOM env3` by (
    simp[Abbr`env3`,FDOM_DRESTRICT] >>
    fsrw_tac[DNF_ss][SUBSET_DEF,fmap_rel_def] ) >>
  rw[] ) >>
`∀v. v ∈ FRANGE s' ⇒ Cclosed c v` by (
  qspecl_then[`c`,`d`,`s`,`env`,`exp`,`(s',Rval v)`]mp_tac(CONJUNCT1 Cevaluate_closed) >>
  rw[] ) >>
simp[] >>
`DRESTRICT env2 (BIGUNION (IMAGE (free_vars c) (set exps))) ⊌ env3 = env3` by (
  rw[GSYM SUBMAP_FUNION_ABSORPTION] >>
  rw[Abbr`env3`] >>
  match_mp_tac SUBMAP_FUNION >>
  disj1_tac >>
  match_mp_tac DRESTRICT_SUBSET_SUBMAP >>
  rw[] ) >>
simp[] >> metis_tac[])

val Cevaluate_FUPDATE = store_thm(
"Cevaluate_FUPDATE",
``∀c d s env exp res k v. Cevaluate c d s env exp res ∧
 (free_vars c exp ⊆ FDOM env) ∧
 (∀v. v ∈ FRANGE env ⇒ Cclosed c v) ∧
 (∀v. v ∈ FRANGE s ⇒ Cclosed c v) ∧
 k ∉ free_vars c exp ∧ Cclosed c v
 ⇒ ∃res'. Cevaluate c d s (env |+ (k,v)) exp res' ∧
   fmap_rel (syneq c) (FST res) (FST res') ∧
   result_rel (syneq c) (SND res) (SND res')``,
rw[] >>
`∀w. w ∈ FRANGE (env |+ (k,v)) ⇒ Cclosed c w` by (
  fsrw_tac[DNF_ss][FRANGE_DEF,DOMSUB_FAPPLY_THM] ) >>
qsuff_tac `(env |+ (k,v) = (DRESTRICT env (free_vars c exp)) ⊌ (env |+ (k,v)))`
>- (
  disch_then SUBST1_TAC >>
  match_mp_tac (MP_CANON (CONJUNCT1 Cevaluate_any_env)) >>
  map_every qexists_tac[`s`,`env`] >>
  rw[] ) >>
rw[GSYM SUBMAP_FUNION_ABSORPTION] >>
rw[SUBMAP_DEF,FUNION_DEF,FUN_FMAP_DEF,DRESTRICT_DEF,FAPPLY_FUPDATE_THM] >>
fs[SUBSET_DEF] >> rw[] >> fs[])

val Cevaluate_free_vars_env = save_thm(
"Cevaluate_free_vars_env",
Cevaluate_any_env
|> CONJUNCT1
|> SPEC_ALL
|> SIMP_RULE (srw_ss()) [GSYM AND_IMP_INTRO]
|> UNDISCH_ALL
|> Q.SPECL [`s`,`env`]
|> SIMP_RULE (srw_ss()) [GSYM AND_IMP_INTRO]
|> UNDISCH_ALL
|> Q.SPEC `FEMPTY`
|> SIMP_RULE (srw_ss()) [FUNION_FEMPTY_2]
|> DISCH_ALL
|> Q.GENL [`res`,`exp`,`env`,`s`,`d`,`c`]
|> SIMP_RULE (srw_ss()) [AND_IMP_INTRO,GSYM CONJ_ASSOC])

val Cevaluate_super_env = store_thm(
"Cevaluate_super_env",
``∀ss c d s env exp res.
  Cevaluate c d s (DRESTRICT env (free_vars c exp)) exp res ∧
  free_vars c exp ⊆ ss ∧
  free_vars c exp ⊆ FDOM env ∧
  (∀v. v ∈ FRANGE (DRESTRICT env ss) ⇒ Cclosed c v) ∧
  (∀v. v ∈ FRANGE s ⇒ Cclosed c v)
  ⇒ ∃res'. Cevaluate c d s (DRESTRICT env ss) exp res' ∧
           fmap_rel (syneq c) (FST res) (FST res') ∧
           result_rel (syneq c) (SND res) (SND res')``,
rw[] >>
qmatch_assum_abbrev_tac `Cevaluate c d s e1 exp res` >>
qspecl_then[`c`,`d`,`s`,`e1`,`exp`,`res`]mp_tac(CONJUNCT1 Cevaluate_any_env) >> rw[] >>
`free_vars c exp ⊆ FDOM e1` by ( fs[Abbr`e1`,DRESTRICT_DEF] ) >>
`∀v. v ∈ FRANGE e1 ⇒ Cclosed c v` by (
  fsrw_tac[DNF_ss][Abbr`e1`,FRANGE_DEF,DRESTRICT_DEF,SUBSET_DEF] ) >>
fs[] >> rfs[] >>
first_x_assum (qspecl_then [`s`,`e1`] mp_tac) >> rw[] >>
first_x_assum (qspec_then `DRESTRICT env ss` mp_tac) >>
fs[] >> rw[] >>
unabbrev_all_tac >>
Q.PAT_ABBREV_TAC`env1 = DRESTRICT env ss` >>
qmatch_assum_abbrev_tac `Cevaluate c d s (env0 ⊌ env1) exp res'` >>
qsuff_tac `env1 = env0 ⊌ env1` >- metis_tac[] >>
rw[GSYM SUBMAP_FUNION_ABSORPTION] >>
fsrw_tac[][Abbr`env0`,Abbr`env1`,SUBMAP_DEF,SUBSET_DEF,DRESTRICT_DEF] >> rw[])

val Cevaluate_any_super_env = save_thm(
"Cevaluate_any_super_env",
Cevaluate_super_env
|> Q.SPECL[`FDOM (env:string|->Cv)`,`c`,`d`,`s`,`env:string|->Cv`]
|> SIMP_RULE(srw_ss())[DRESTRICT_FDOM,GSYM AND_IMP_INTRO]
|> SPEC_ALL |> UNDISCH_ALL |> DISCH_ALL
|> Q.GENL[`res`,`exp`,`env`,`s`,`d`,`c`]
|> SIMP_RULE(srw_ss())[AND_IMP_INTRO])

val Cevaluate_any_syneq_store = save_thm(
"Cevaluate_any_syneq_store",
Cevaluate_any_env
|> CONJUNCT1
|> SPEC_ALL
|> UNDISCH_ALL
|> Q.SPECL[`s'`,`env`]
|> UNDISCH_ALL
|> Q.SPEC`env`
|> DISCH_ALL
|> SIMP_RULE(srw_ss())[DRESTRICT_FUNION_SAME]
|> SIMP_RULE(srw_ss())[AND_IMP_INTRO]
|> Q.GENL[`res`,`exp`,`env`,`s'`,`s`,`d`,`c`])

val Cevaluate_any_syneq_env = save_thm(
"Cevaluate_any_syneq_env",
Cevaluate_any_env
|> CONJUNCT1
|> SPEC_ALL
|> UNDISCH_ALL
|> Q.SPECL[`s`,`env'`]
|> UNDISCH_ALL
|> Q.SPEC`env'`
|> DISCH_ALL
|> SIMP_RULE (srw_ss()) [DRESTRICT_FUNION_SAME]
|> SIMP_RULE (srw_ss()) [AND_IMP_INTRO,GSYM CONJ_ASSOC]
|> Q.GENL[`res`,`exp`,`env'`,`env`,`s`,`d`,`c`])

val Cevaluate_any_syneq_any = save_thm(
"Cevaluate_any_syneq_any",
Cevaluate_any_env
|> CONJUNCT1
|> SPEC_ALL
|> UNDISCH_ALL
|> Q.SPECL[`s'`,`env'`]
|> UNDISCH_ALL
|> Q.SPEC`env'`
|> DISCH_ALL
|> SIMP_RULE (srw_ss()) [DRESTRICT_FUNION_SAME]
|> SIMP_RULE (srw_ss()) [AND_IMP_INTRO,GSYM CONJ_ASSOC]
|> Q.GENL[`res`,`exp`,`env'`,`env`,`s'`,`s`,`d`,`c`])

val Cevaluate_list_any_syneq_any = save_thm(
"Cevaluate_list_any_syneq_any",
Cevaluate_any_env
|> CONJUNCT2
|> SPEC_ALL
|> UNDISCH_ALL
|> Q.SPECL[`s'`,`env'`]
|> UNDISCH_ALL
|> Q.SPEC`env'`
|> DISCH_ALL
|> SIMP_RULE (srw_ss()) [DRESTRICT_FUNION_SAME]
|> SIMP_RULE (srw_ss()) [AND_IMP_INTRO,GSYM CONJ_ASSOC]
|> Q.GENL[`ress`,`exps`,`env'`,`env`,`s'`,`s`,`d`,`c`])

val Cevaluate_FUPDATE_Rerr = save_thm(
"Cevaluate_FUPDATE_Rerr",
Cevaluate_FUPDATE
|> Q.SPECL[`c`,`d`,`s`,`env`,`exp`,`(s',Rerr err)`]
|> SIMP_RULE (srw_ss()) [EXISTS_PROD]
|> Q.GENL[`err`,`s'`,`exp`,`env`,`s`,`d`,`c`])

(* Cevaluate deterministic *)

val Cevaluate_determ = store_thm("Cevaluate_determ",
  ``(∀c d s env exp res. Cevaluate c d s env exp res ⇒ ∀res'. Cevaluate c d s env exp res' ⇒ (res' = res)) ∧
    (∀c d s env exps ress. Cevaluate_list c d s env exps ress ⇒ ∀ress'. Cevaluate_list c d s env exps ress' ⇒ (ress' = ress))``,
  ho_match_mp_tac Cevaluate_ind >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    rw[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][FORALL_PROD] >>
    res_tac >> fs[] ) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    rw[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][FORALL_PROD] >>
    TRY(Cases_on`res'`)>>
    res_tac >> fs[] ) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    rw[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][FORALL_PROD] >>
    res_tac >> fs[] >>
    rw[] >> fs[] ) >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rw[Cevaluate_con] >>
    res_tac >> fs[]) >>
  strip_tac >- (
    rw[Cevaluate_con] >>
    res_tac >> fs[]) >>
  strip_tac >- (
    rw[Cevaluate_tageq] >>
    res_tac >> fs[]) >>
  strip_tac >- (
    rw[Cevaluate_tageq] >>
    res_tac >> fs[]) >>
  strip_tac >- (
    rw[Cevaluate_proj] >>
    res_tac >> fs[]) >>
  strip_tac >- (
    rw[Cevaluate_proj] >>
    res_tac >> fs[]) >>
  strip_tac >- (
    rw[Cevaluate_let] >>
    res_tac >> fs[]) >>
  strip_tac >- (
    rw[Cevaluate_let] >>
    res_tac >> fs[]) >>
  strip_tac >- (
    rw[] >>
    pop_assum mp_tac >>
    rw[Once Cevaluate_cases]) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    simp[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][] >>
    rw[] >>
    res_tac >> fs[] >> rw[] >>
    res_tac >> fs[] >> rw[] >>
    Cases_on`cb`>>fs[]>>rw[]) >>
  strip_tac >- (
    rw[] >>
    pop_assum mp_tac >>
    rw[Once Cevaluate_cases] >>
    res_tac >> fs[] >> rw[] >>
    res_tac >> fs[]) >>
  strip_tac >- (
    rw[] >>
    pop_assum mp_tac >>
    rw[Once Cevaluate_cases] >>
    res_tac >> fs[]) >>
  strip_tac >- (
    rw[] >>
    pop_assum mp_tac >>
    rw[Once Cevaluate_cases] >>
    res_tac >> fs[]) >>
  strip_tac >- (
    rw[] >>
    pop_assum mp_tac >>
    rw[Once Cevaluate_cases] >>
    res_tac >> fs[]) >>
  strip_tac >- (
    rw[] >>
    pop_assum mp_tac >>
    rw[Once Cevaluate_cases] >>
    res_tac >> fs[]) >>
  strip_tac >- (
    rw[] >>
    pop_assum mp_tac >>
    rw[Once Cevaluate_cases] >>
    res_tac >> fs[]) >>
  strip_tac >- (
    rw[] >>
    pop_assum mp_tac >>
    rw[Once Cevaluate_cases] >>
    res_tac >> fs[]) >>
  strip_tac >- (
    rw[] >>
    pop_assum mp_tac >>
    rw[Once Cevaluate_cases] >>
    res_tac >> fs[]) >>
  strip_tac >- (
    rw[] >>
    pop_assum mp_tac >>
    rw[Once Cevaluate_cases] >>
    res_tac >> fs[]) >>
  strip_tac >- (
    rw[] >>
    pop_assum mp_tac >>
    rw[Once Cevaluate_cases] >>
    res_tac >> fs[]) >>
  strip_tac >- rw[Once Cevaluate_cases] >>
  strip_tac >- (
    rw[] >>
    pop_assum mp_tac >>
    rw[Once Cevaluate_cases] >>
    res_tac >> fs[] >> rw[] >>
    res_tac >> fs[] ) >>
  strip_tac >- (
    rw[] >>
    pop_assum mp_tac >>
    rw[Once Cevaluate_cases] >>
    res_tac >> fs[] >> rw[] ) >>
  rw[] >>
  pop_assum mp_tac >>
  rw[Once Cevaluate_cases] >>
  res_tac >> fs[] >> rw[] >>
  res_tac >> fs[])

val _ = export_theory()
