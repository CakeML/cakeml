open HolKernel bossLib boolLib boolSimps pairTheory listTheory pred_setTheory finite_mapTheory SatisfySimps arithmeticTheory quantHeuristicsLib lcsymtacs
open MiniMLTheory miscTheory miniMLExtraTheory compileTerminationTheory
val _ = new_theory "intLang"

(* Cevaluate functional equations *)

val Cevaluate_raise = store_thm(
"Cevaluate_raise",
``∀c d s env err res. Cevaluate c d s env (CRaise err) res = (res = (s, Rerr (Rraise err)))``,
rw[Once Cevaluate_cases])

val Cevaluate_lit = store_thm(
"Cevaluate_lit",
``∀c d s env l res. Cevaluate c d s env (CLit l) res = (res = (s, Rval (CLitv l)))``,
rw[Once Cevaluate_cases])

val Cevaluate_var = store_thm(
"Cevaluate_var",
``∀c d s env vn res. Cevaluate c d s env (CVar vn) res = (vn ∈ FDOM env ∧ (res = (s, Rval (env ' vn))))``,
rw[Once Cevaluate_cases] >> PROVE_TAC[])

val Cevaluate_fun = store_thm(
"Cevaluate_fun",
``∀c d s env ns b res. Cevaluate c d s env (CFun ns b) res =
  (∀l. (b = INR l) ⇒ l ∈ FDOM c ∧ (FLOOKUP d l = SOME (cbod_fvs c b ∩ FDOM env DIFF (set ns),[],ns,0))) ∧
  (res = (s, Rval (CRecClos env [] [(ns,b)] "")))``,
rw[Once Cevaluate_cases] >> metis_tac[])

val _ = export_rewrites["Cevaluate_raise","Cevaluate_lit","Cevaluate_var","Cevaluate_fun"]

val Cevaluate_con = store_thm(
"Cevaluate_con",
``∀c d s env cn es res. Cevaluate c d s env (CCon cn es) res =
(∃s' vs. Cevaluate_list c d s env es (s', Rval vs) ∧ (res = (s', Rval (CConv cn vs)))) ∨
(∃s' err. Cevaluate_list c d s env es (s', Rerr err) ∧ (res = (s', Rerr err)))``,
rw[Once Cevaluate_cases] >> PROVE_TAC[])

val Cevaluate_tageq = store_thm(
"Cevaluate_tageq",
``∀c d s env exp n res. Cevaluate c d s env (CTagEq exp n) res =
  (∃s' m vs. Cevaluate c d s env exp (s', Rval (CConv m vs)) ∧ (res = (s', Rval (CLitv (Bool (n = m)))))) ∨
  (∃s' err. Cevaluate c d s env exp (s', Rerr err) ∧ (res = (s', Rerr err)))``,
rw[Once Cevaluate_cases] >> PROVE_TAC[])

val Cevaluate_let = store_thm(
"Cevaluate_let",
``∀c d s env n e b res. Cevaluate c d s env (CLet n e b) res =
(∃s' v. Cevaluate c d s env e (s', Rval v) ∧
     Cevaluate c d s' (env |+ (n,v)) b res) ∨
(∃s' err. Cevaluate c d s env e (s', Rerr err) ∧ (res = (s', Rerr err)))``,
rw[Once Cevaluate_cases] >> PROVE_TAC[])

val Cevaluate_proj = store_thm(
"Cevaluate_proj",
``∀c d s env exp n res. Cevaluate c d s env (CProj exp n) res =
  (∃s' m vs. Cevaluate c d s env exp (s', Rval (CConv m vs)) ∧ (n < LENGTH vs) ∧ (res = (s', Rval (EL n vs)))) ∨
  (∃s' err. Cevaluate c d s env exp (s', Rerr err) ∧ (res = (s', Rerr err)))``,
rw[Once Cevaluate_cases] >> PROVE_TAC[])

(* syneq equivalence relation lemmas *)

val syneq_refl = store_thm(
"syneq_refl",
``∀c x. syneq c x x``,
gen_tac >> (
(TypeBase.induction_of``:Cv``)
|> Q.SPECL [`W (syneq c)`,`FEVERY ((W (syneq c)) o SND)`,`EVERY (W (syneq c))`]
|> SIMP_RULE(srw_ss())[]
|> UNDISCH_ALL
|> CONJUNCT1
|> DISCH_ALL
|> match_mp_tac) >>
rw[] >> rw[syneq_cases] >>
fsrw_tac[DNF_ss]
[EVERY2_EVERY,MEM_ZIP,MEM_EL,EVERY_MEM,
 pairTheory.FORALL_PROD,pairTheory.UNCURRY] >>
rw[] >>
Cases_on `FLOOKUP env v` >> fs[optionTheory.OPTREL_def] >>
fsrw_tac[DNF_ss][FLOOKUP_DEF,FRANGE_DEF] >>
PROVE_TAC[])
val _ = export_rewrites["syneq_refl"]

val syneq_sym = store_thm(
"syneq_sym",
``∀c x y. syneq c x y ⇒ syneq c y x``,
ho_match_mp_tac syneq_ind >> rw[] >>
rw[syneq_cases] >- (
  fs[EVERY2_EVERY,EVERY_MEM,MEM_ZIP,
     pairTheory.FORALL_PROD] >>
  pop_assum mp_tac >>
  fs[MEM_ZIP] >>
  PROVE_TAC[] )
>>
  fs[EVERY_MEM,pairTheory.FORALL_PROD,optionTheory.OPTREL_def] >>
  metis_tac[] )

val syneq_trans = store_thm(
"syneq_trans",
``∀c x y. syneq c x y ⇒ ∀z. syneq c y z ⇒ syneq c x z``,
ho_match_mp_tac syneq_ind >> rw[] >>
pop_assum mp_tac >>
rw[syneq_cases] >- (
  fs[EVERY2_EVERY,EVERY_MEM,MEM_ZIP] >>
  rpt (qpat_assum` LENGTH X = LENGTH Y` mp_tac) >>
  ntac 2 strip_tac >>
  fs[MEM_ZIP,pairTheory.FORALL_PROD] >>
  PROVE_TAC[] )
>- (
  Cases_on`defs`>>fs[]>>
  Cases_on`t`>>fs[]>>
  Cases_on`h`>>fs[]>>
  fs[optionTheory.OPTREL_def,EVERY_MEM,
     pairTheory.FORALL_PROD] >>
  reverse(Cases_on`q=xs`)>>fs[]>-metis_tac[]>>
  reverse(Cases_on`r=b`)>>fs[]>-metis_tac[]>>
  reverse(Cases_on`xs=xs'`)>>fs[]>-metis_tac[]>>
  reverse(Cases_on`b=b'`)>>fs[]>-metis_tac[]>>
  srw_tac[DNF_ss][]>>
  map_every qexists_tac[`q`,`b`]>>rw[]>>
  metis_tac[optionTheory.option_CASES,
            optionTheory.NOT_SOME_NONE,
            optionTheory.SOME_11] )
>- (
  Cases_on`find_index d ns 0`>>fs[]>>
  Cases_on`EL x defs`>>fs[]>>
  reverse(Cases_on`q=xs`)>>fs[]>-metis_tac[]>>
  reverse(Cases_on`r=b`)>>fs[]>-metis_tac[]>>
  reverse(Cases_on`xs=xs'`)>>fs[]>-metis_tac[]>>
  reverse(Cases_on`b=b'`)>>fs[]>-metis_tac[]>>
  srw_tac[DNF_ss][]>>
  map_every qexists_tac[`q`,`b`]>>rw[]>>
  fs[optionTheory.OPTREL_def,EVERY_MEM,
     pairTheory.FORALL_PROD] >>
  metis_tac[optionTheory.option_CASES,
            optionTheory.NOT_SOME_NONE,
            optionTheory.SOME_11] ))

val result_rel_syneq_trans = save_thm(
"result_rel_syneq_trans",
result_rel_trans
|> Q.GEN`R`
|> Q.ISPEC`syneq c`
|> SIMP_RULE std_ss [GSYM AND_IMP_INTRO]
|> UNDISCH
|> PROVE_HYP (SIMP_RULE (std_ss++DNF_ss) [](Q.SPEC`c`syneq_trans))
|> SIMP_RULE std_ss [AND_IMP_INTRO])

val result_rel_syneq_sym = save_thm(
"result_rel_syneq_sym",
result_rel_sym
|> Q.GEN`R`
|> Q.ISPEC`syneq c`
|> SIMP_RULE std_ss[syneq_sym])

val fmap_rel_syneq_trans = save_thm(
"fmap_rel_syneq_trans",
fmap_rel_trans
|> Q.GEN`R`
|> Q.ISPEC`syneq c`
|> SIMP_RULE std_ss [GSYM AND_IMP_INTRO]
|> UNDISCH
|> PROVE_HYP (SIMP_RULE (std_ss++DNF_ss) [](Q.SPEC`c`syneq_trans))
|> SIMP_RULE std_ss [AND_IMP_INTRO])

val fmap_rel_syneq_sym = save_thm(
"fmap_rel_syneq_sym",
fmap_rel_sym
|> Q.GEN`R`
|> Q.ISPEC`syneq c`
|> SIMP_RULE std_ss[syneq_sym])

val syneq_ov = store_thm("syneq_ov",
  ``∀c v1 v2. syneq c v1 v2 ⇒ ∀m s. Cv_to_ov m s v1 = Cv_to_ov m s v2``,
  ho_match_mp_tac syneq_ind >>
  rw[MAP_EQ_EVERY2] >>
  fs[EVERY2_EVERY] >>
  qmatch_assum_abbrev_tac`EVERY P l` >>
  match_mp_tac (MP_CANON MONO_EVERY) >>
  rw[Abbr`P`,UNCURRY])

(* Misc. int lang lemmas *)

val good_cmap_def = Define`
  good_cmap cenv m =
    ∀c1 n1 c2 n2 s.
      MEM (c1,(n1,s)) cenv ∧
      MEM (c2,(n2,s)) cenv ∧
      (FAPPLY m c1 = FAPPLY m c2) ⇒ (c1 = c2)`

val Cevaluate_list_LENGTH = store_thm("Cevaluate_list_LENGTH",
  ``∀exps c d s env s' vs. Cevaluate_list c d s env exps (s', Rval vs) ⇒ (LENGTH vs = LENGTH exps)``,
  Induct >> rw[LENGTH_NIL] >> pop_assum mp_tac >>
  rw[Once Cevaluate_cases] >>
  fsrw_tac[DNF_ss][] >>
  first_x_assum match_mp_tac >>
  srw_tac[SATISFY_ss][])

val FINITE_Cpat_vars = store_thm(
"FINITE_Cpat_vars",
``∀p. FINITE (Cpat_vars p)``,
ho_match_mp_tac Cpat_vars_ind >>
rw[FOLDL_UNION_BIGUNION] >>
PROVE_TAC[])
val _ = export_rewrites["FINITE_Cpat_vars"]

val FINITE_free_vars = store_thm(
"FINITE_free_vars",
``(∀c t. FINITE (free_vars c t)) ∧ (∀c b. FINITE (cbod_fvs c b))``,
ho_match_mp_tac free_vars_ind >>
rw[free_vars_def] >>
TRY (Cases_on `FLOOKUP c l` >> rw[] >> NO_TAC) >>
qmatch_rename_tac `FINITE (FOLDL XXX YYY ls)` ["XXX","YYY"] >>
qmatch_abbrev_tac `FINITE (FOLDL ff s0 ls)` >>
qsuff_tac `∀s0. FINITE s0 ⇒ FINITE (FOLDL ff s0 ls)` >- rw[Abbr`s0`] >>
Induct_on `ls` >> rw[Abbr`s0`] >>
first_assum (ho_match_mp_tac o MP_CANON) >>
rw[Abbr`ff`] >>
TRY (Cases_on `h` >> rw[]) >>
metis_tac[])
val _ = export_rewrites["FINITE_free_vars"]

val free_vars_DOMSUB_SUBSET = store_thm("free_vars_DOMSUB_SUBSET",
  ``(∀c e l. free_vars (c \\ l) e ⊆ free_vars c e) ∧
    (∀c b l. cbod_fvs (c \\ l) b ⊆ cbod_fvs c b)``,
  ho_match_mp_tac free_vars_ind >>
  rw[FOLDL_UNION_BIGUNION,FOLDL_UNION_BIGUNION_paired] >>
  fsrw_tac[DNF_ss][SUBSET_DEF] >>
  fsrw_tac[DNF_ss][pairTheory.FORALL_PROD,pairTheory.EXISTS_PROD] >>
  TRY (PROVE_TAC[]) >>
  fsrw_tac[DNF_ss][FLOOKUP_DEF] >> rw[] >>
  fsrw_tac[][DOMSUB_FAPPLY_THM] >>
  PROVE_TAC[DOMSUB_COMMUTES])

val free_vars_DOMSUB = store_thm("free_vars_DOMSUB",
  ``(∀c e l. (l ∈ FDOM c) ⇒ (free_vars c e ⊆ free_vars (c \\ l) e ∪ free_vars (c \\ l) (c ' l))) ∧
    (∀c b l. (l ∈ FDOM c) ⇒ (cbod_fvs c b ⊆ cbod_fvs (c \\ l) b ∪ cbod_fvs (c \\ l) (INL (c ' l))))``,
  ho_match_mp_tac free_vars_ind >>
  rw[FOLDL_UNION_BIGUNION,FOLDL_UNION_BIGUNION_paired] >>
  fsrw_tac[DNF_ss][SUBSET_DEF] >>
  fsrw_tac[DNF_ss][pairTheory.FORALL_PROD,pairTheory.EXISTS_PROD] >>
  TRY (PROVE_TAC[]) >>
  BasicProvers.EVERY_CASE_TAC >>
  fsrw_tac[DNF_ss][FLOOKUP_DEF] >> rw[] >>
  fsrw_tac[][DOMSUB_FAPPLY_THM] >>
  PROVE_TAC[DOMSUB_COMMUTES,free_vars_DOMSUB_SUBSET,SUBSET_DEF])

val free_vars_SUBMAP = store_thm("free_vars_SUBMAP",
  ``(∀c1 e c2. c1 ⊑ c2 ⇒ free_vars c1 e ⊆ free_vars c2 e) ∧
    (∀c1 b c2. c1 ⊑ c2 ⇒ cbod_fvs c1 b ⊆ cbod_fvs c2 b)``,
  ho_match_mp_tac free_vars_ind >>
  rw[FOLDL_UNION_BIGUNION,FOLDL_UNION_BIGUNION_paired] >>
  fsrw_tac[DNF_ss][SUBSET_DEF] >>
  fsrw_tac[DNF_ss][SUBMAP_DEF] >>
  fsrw_tac[DNF_ss][pairTheory.EXISTS_PROD,pairTheory.FORALL_PROD] >>
  fsrw_tac[DNF_ss][FLOOKUP_DEF] >> rw[] >>
  fsrw_tac[DNF_ss][DOMSUB_FAPPLY_THM] >>
  metis_tac[])

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

val fmap_rel_extend_rec_env_same = store_thm(
"fmap_rel_extend_rec_env_same",
``fmap_rel R env1 env2 ∧ LIST_REL R vs1 vs2 ∧ (LENGTH ns = LENGTH vs1) ∧
  (∀b. MEM b rs ⇒ R (CRecClos cenv1 rs defs b) (CRecClos cenv2 rs defs b))
  ⇒ fmap_rel R
      (extend_rec_env cenv1 env1 rs defs ns vs1)
      (extend_rec_env cenv2 env2 rs defs ns vs2)``,
rw[extend_rec_env_def,FOLDL_FUPDATE_LIST,FOLDL2_FUPDATE_LIST,LIST_REL_EL_EQN] >>
rw[MAP2_MAP,FST_pair,SND_pair,MAP_ZIP] >>
match_mp_tac fmap_rel_FUPDATE_LIST_same >>
rw[MAP_ZIP,LENGTH_ZIP,LIST_REL_EL_EQN] >>
match_mp_tac fmap_rel_FUPDATE_LIST_same >>
rw[MAP_ZIP,LENGTH_ZIP,LIST_REL_EL_EQN,EL_MAP,MAP_MAP_o,combinTheory.o_DEF] >>
fsrw_tac[DNF_ss][MEM_EL])

val FDOM_extend_rec_env = store_thm(
"FDOM_extend_rec_env",
``(LENGTH ns = LENGTH vs) ⇒ (FDOM (extend_rec_env cenv' env' ns' defs ns vs) = FDOM env' ∪ (set ns') ∪ (set ns))``,
rw[extend_rec_env_def,FOLDL_FUPDATE_LIST,FOLDL2_FUPDATE_LIST,FDOM_FUPDATE_LIST] >>
rw[MAP2_MAP,FST_pair,SND_pair,MAP_ZIP,MAP_MAP_o,combinTheory.o_DEF])
val _ = export_rewrites["FDOM_extend_rec_env"]

val extend_rec_env_FUNION = store_thm(
"extend_rec_env_FUNION",
``(LENGTH n = LENGTH v) ⇒
  (extend_rec_env env f ns defs n v = extend_rec_env env FEMPTY ns defs n v ⊌ f)``,
rw[extend_rec_env_def,FOLDL2_FUPDATE_LIST,FOLDL_FUPDATE_LIST] >>
rw[MAP2_MAP,MAP_ZIP,FST_pair,SND_pair] >>
fs[GSYM fmap_EQ_THM] >>
conj_tac >- (
  rw[FDOM_FUPDATE_LIST,MAP_ZIP,MAP2_MAP,FST_pair,SND_pair] >>
  PROVE_TAC[UNION_COMM,UNION_ASSOC] ) >>
qx_gen_tac `x` >>
strip_tac >>
Cases_on `MEM x n` >- (
  Q.PAT_ABBREV_TAC `(f1 : string |-> Cv) = FEMPTY |++ MAP zz ns` >>
  `x ∈ FDOM (f1 |++ ZIP (n,v))` by (
    rw[FDOM_FUPDATE_LIST,MAP_ZIP] ) >>
  rw[Once FUNION_DEF,SimpRHS] >>
  match_mp_tac FUPDATE_SAME_LIST_APPLY >>
  rw[MAP_ZIP] ) >>
ho_match_mp_tac FUPDATE_LIST_APPLY_NOT_MEM_matchable >>
fs[MAP_ZIP] >>
Cases_on `MEM x ns` >- (
  Q.PAT_ABBREV_TAC `(f1 : string |-> Cv) = FEMPTY |++ MAP zz ns` >>
  `x ∈ FDOM (f1 |++ ZIP (n,v))` by (
    rw[FDOM_FUPDATE_LIST,MAP_ZIP,Abbr`f1`,MAP_MAP_o,MEM_MAP] ) >>
  rw[Once FUNION_DEF] >>
  match_mp_tac FUPDATE_LIST_APPLY_NOT_MEM_matchable >>
  rw[MAP_ZIP,Abbr`f1`] >>
  match_mp_tac FUPDATE_SAME_LIST_APPLY >>
  srw_tac[DNF_ss][MEM_MAP,MAP_MAP_o] ) >>
rw[FUNION_DEF,FDOM_FUPDATE_LIST,MAP_ZIP,MAP_MAP_o,MEM_MAP] >>
match_mp_tac EQ_SYM >>
match_mp_tac FUPDATE_LIST_APPLY_NOT_MEM_matchable >>
srw_tac[DNF_ss][MAP_MAP_o,MEM_MAP])

val Cevaluate_store_SUBSET = store_thm("Cevaluate_store_SUBSET",
  ``(∀c d s env exp res. Cevaluate c d s env exp res ⇒ FDOM s ⊆ FDOM (FST res)) ∧
    (∀c d s env exps res. Cevaluate_list c d s env exps res ⇒ FDOM s ⊆ FDOM (FST res))``,
  ho_match_mp_tac Cevaluate_ind >> rw[] >>
  TRY (PROVE_TAC [SUBSET_TRANS]) >- (
    Cases_on`uop`>>rw[]>>rw[] >>
    fsrw_tac[DNF_ss][SUBSET_DEF] >>
    Cases_on`v`>>rw[] ) >>
  Cases_on`v1`>>rw[] >>
  fsrw_tac[DNF_ss][SUBSET_DEF])

val all_Clocs_def = tDefine "all_Clocs"`
  (all_Clocs (CLitv _) = {}) ∧
  (all_Clocs (CConv _ vs) = BIGUNION (IMAGE all_Clocs (set vs))) ∧
  (all_Clocs (CRecClos env _ _ _) = BIGUNION (IMAGE all_Clocs (FRANGE env))) ∧
  (all_Clocs (CLoc n) = {n})`
  (WF_REL_TAC`measure Cv_size` >>
   srw_tac[ARITH_ss][fmap_size_def,FRANGE_DEF,Cvs_size_thm] >>
   Q.ISPEC_THEN`Cv_size`imp_res_tac SUM_MAP_MEM_bound >>
   fsrw_tac[ARITH_ss][] >>
   qmatch_abbrev_tac `(q:num) < a + (y + (w + (z + 1)))` >>
   qsuff_tac `q ≤ a` >- fsrw_tac[ARITH_ss][] >>
   unabbrev_all_tac >>
   qmatch_abbrev_tac `y <= SIGMA f (FDOM env)` >>
   match_mp_tac LESS_EQ_TRANS >>
   qexists_tac `f x` >>
   conj_tac >- srw_tac[ARITH_ss][o_f_FAPPLY,Abbr`y`,Abbr`f`] >>
   match_mp_tac SUM_IMAGE_IN_LE >>
   rw[])
val _ = export_rewrites["all_Clocs_def"]

val CevalPrim2_Clocs = store_thm("CevaluatePrim2_Clocs",
  ``∀p2 v1 v2 v. (CevalPrim2 p2 v1 v2 = Rval v) ⇒ (all_Clocs v = {})``,
  Cases >> fs[] >> Cases >> fs[] >>
  TRY (Cases_on`l` >> fs[] >> Cases >> fs[] >> Cases_on `l` >> fs[] >> rw[] >> rw[]) >>
  rw[] >> rw[])

val Cevaluate_Clocs = store_thm("Cevaluate_Clocs",
  ``(∀c d s env exp res. Cevaluate c d s env exp res ⇒
     BIGUNION (IMAGE all_Clocs (FRANGE env)) ⊆ FDOM s ∧
     BIGUNION (IMAGE all_Clocs (FRANGE s)) ⊆ FDOM s
     ⇒
     BIGUNION (IMAGE all_Clocs (FRANGE (FST res))) ⊆ FDOM (FST res) ∧
     ∀v. (SND res = Rval v) ⇒ all_Clocs v ⊆ FDOM (FST res)) ∧
    (∀c d s env exps res. Cevaluate_list c d s env exps res ⇒
     BIGUNION (IMAGE all_Clocs (FRANGE env)) ⊆ FDOM s ∧
     BIGUNION (IMAGE all_Clocs (FRANGE s)) ⊆ FDOM s
     ⇒
     BIGUNION (IMAGE all_Clocs (FRANGE (FST res))) ⊆ FDOM (FST res) ∧
     ∀vs. (SND res = Rval vs) ⇒ BIGUNION (IMAGE all_Clocs (set vs)) ⊆ FDOM (FST res))``,
  ho_match_mp_tac Cevaluate_strongind >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    rpt gen_tac >> strip_tac >>
    fs[] >> rfs[] >>
    first_x_assum match_mp_tac >>
    fsrw_tac[DNF_ss][SUBSET_DEF,IN_FRANGE,DOMSUB_FAPPLY_THM] >>
    metis_tac[Cevaluate_store_SUBSET,SUBSET_DEF,FST] ) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rw[] >>
    fsrw_tac[DNF_ss][IN_FRANGE,SUBSET_DEF] >>
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
    fsrw_tac[DNF_ss][SUBSET_DEF,IN_FRANGE,DOMSUB_FAPPLY_THM] >>
    metis_tac[Cevaluate_store_SUBSET,SUBSET_DEF,FST] ) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rpt gen_tac >> ntac 2 strip_tac >>
    fs[] >> rfs[] >>
    first_x_assum match_mp_tac >>
    rfs[FOLDL2_FUPDATE_LIST_paired,MAP2_MAP,FST_triple,MAP_ZIP] >>
    fsrw_tac[DNF_ss][SUBSET_DEF] >>
    map_every qx_gen_tac [`x`,`y`] >>
    strip_tac >>
    qpat_assum `x ∈ Y` mp_tac >>
    pop_assum mp_tac >>
    qid_spec_tac`y` >>
    ho_match_mp_tac IN_FRANGE_FUPDATE_LIST_suff >>
    fs[MAP_ZIP,AND_IMP_INTRO] >>
    conj_tac >- PROVE_TAC[] >>
    fsrw_tac[DNF_ss][MEM_MAP,FORALL_PROD] >>
    PROVE_TAC[] ) >>
  strip_tac >- (
    rpt gen_tac >> ntac 2 strip_tac >>
    fs[] >> rfs[] >>
    first_x_assum match_mp_tac >>
    rfs[FOLDL_FUPDATE_LIST] >>
    fsrw_tac[DNF_ss][SUBSET_DEF] >>
    map_every qx_gen_tac [`x`,`y`] >>
    strip_tac >>
    qpat_assum `x ∈ Y` mp_tac >>
    pop_assum mp_tac >>
    qid_spec_tac`y` >>
    ho_match_mp_tac IN_FRANGE_FUPDATE_LIST_suff >>
    fs[MAP_ZIP,AND_IMP_INTRO] >>
    conj_tac >- PROVE_TAC[] >>
    fsrw_tac[DNF_ss][MEM_MAP,FORALL_PROD] >>
    PROVE_TAC[] ) >>
  strip_tac >- srw_tac[ETA_ss][] >>
  strip_tac >- (
    rpt gen_tac >> ntac 2 strip_tac >>
    fs[] >> rfs[] >>
    first_x_assum match_mp_tac >>
    simp[extend_rec_env_def,FOLDL2_FUPDATE_LIST,FOLDL_FUPDATE_LIST,MAP2_MAP,FST_pair,SND_pair,MAP_ZIP] >>
    imp_res_tac Cevaluate_store_SUBSET >> fs[] >>
    fsrw_tac[ETA_ss][] >>
    reverse conj_tac >- PROVE_TAC[SUBSET_TRANS] >>
    fsrw_tac[DNF_ss][SUBSET_DEF] >>
    map_every qx_gen_tac [`x`,`y`] >>
    strip_tac >>
    qpat_assum `x ∈ Y` mp_tac >>
    pop_assum mp_tac >>
    qid_spec_tac`y` >>
    ho_match_mp_tac IN_FRANGE_FUPDATE_LIST_suff >>
    simp[MAP_ZIP] >>
    reverse conj_tac >- PROVE_TAC[SUBSET_TRANS] >>
    ho_match_mp_tac IN_FRANGE_FUPDATE_LIST_suff >>
    fsrw_tac[DNF_ss][MAP_MAP_o,combinTheory.o_DEF,MEM_MAP,EXISTS_PROD] >>
    PROVE_TAC[] ) >>
  strip_tac >- (
    rw[] >> fs[] >> rfs[] >>
    first_x_assum match_mp_tac >>
    metis_tac[Cevaluate_store_SUBSET,SUBSET_TRANS,FST] ) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rpt gen_tac >> ntac 2 strip_tac >>
    Cases_on`uop`>>fs[LET_THM] >- (
      fsrw_tac[DNF_ss][SUBSET_DEF] >>
      map_every qx_gen_tac [`x`,`y`] >>
      strip_tac >>
      qpat_assum `x ∈ Y` mp_tac >>
      pop_assum mp_tac >>
      qid_spec_tac`y` >>
      ho_match_mp_tac IN_FRANGE_DOMSUB_suff >>
      PROVE_TAC[] ) >>
    Cases_on`v`>>fs[] >>
    BasicProvers.CASE_TAC >>
    fsrw_tac[DNF_ss][SUBSET_DEF,IN_FRANGE,FLOOKUP_DEF] >>
    PROVE_TAC[] ) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rw[] >> imp_res_tac CevalPrim2_Clocs >> rw[] ) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    ntac 7 gen_tac >>
    Cases >> fs[] >>
    gen_tac >> ntac 2 strip_tac >>
    fs[] >>
    fsrw_tac[DNF_ss][SUBSET_DEF] >>
    map_every qx_gen_tac [`x`,`y`] >>
    strip_tac >>
    qpat_assum `x ∈ Y` mp_tac >>
    pop_assum mp_tac >>
    qid_spec_tac`y` >>
    ho_match_mp_tac IN_FRANGE_DOMSUB_suff >>
    PROVE_TAC[] ) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rpt gen_tac >> ntac 2 strip_tac >>
    fs[] >> rfs[] >>
    first_x_assum match_mp_tac >>
    metis_tac[SUBSET_TRANS,Cevaluate_store_SUBSET,FST]) >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rpt gen_tac >> ntac 2 strip_tac >>
    fs[] >> rfs[] >>
    metis_tac[SUBSET_TRANS,Cevaluate_store_SUBSET,FST]) >>
  strip_tac >- rw[] >>
  rw[] >> fs[] >> rfs[] >>
  metis_tac[SUBSET_TRANS,Cevaluate_store_SUBSET,FST])

(* simple cases of syneq preservation *)

val syneq_no_closures = store_thm(
"syneq_no_closures",
``∀c v1 v2. syneq c v1 v2 ⇒ (no_closures v2 = no_closures v1)``,
ho_match_mp_tac syneq_ind >>
rw[EVERY2_EVERY] >>
pop_assum mp_tac >>
srw_tac[DNF_ss][EVERY_MEM,pairTheory.FORALL_PROD,MEM_ZIP] >>
srw_tac[DNF_ss][MEM_EL])

val no_closures_syneq_equal = store_thm(
"no_closures_syneq_equal",
``∀c v1 v2. syneq c v1 v2 ⇒ no_closures v1 ⇒ (v1 = v2)``,
ho_match_mp_tac syneq_ind >>
srw_tac[ETA_ss][EVERY2_EVERY] >>
qpat_assum `LENGTH X = Y` assume_tac >>
fs[EVERY_MEM,pairTheory.FORALL_PROD] >>
rw[LIST_EQ_REWRITE] >>
first_x_assum (match_mp_tac o MP_CANON) >>
fsrw_tac[DNF_ss][MEM_ZIP] >>
fsrw_tac[DNF_ss][MEM_EL] >>
PROVE_TAC[])

val CevalPrim2_syneq = store_thm(
"CevalPrim2_syneq",
``∀c v1 v2. syneq c v1 v2 ⇒
    ∀p v. (CevalPrim2 p v v1 = CevalPrim2 p v v2) ∧
          (CevalPrim2 p v1 v = CevalPrim2 p v2 v)``,
ho_match_mp_tac (CompileTheory.syneq_strongind) >>
strip_tac >- (
  gen_tac >> Cases >> Cases >> rw[] ) >>
strip_tac >- (
  rpt gen_tac >> strip_tac >>
  `EVERY2 (syneq c) vs1 vs2` by (
    fs[EVERY2_EVERY] >>
    pop_assum mp_tac >>
    match_mp_tac EVERY_MONOTONIC >>
    fs[pairTheory.FORALL_PROD] ) >>
  `no_closures (CConv cn vs1) = no_closures (CConv cn vs2)` by (
    match_mp_tac syneq_no_closures >>
    qexists_tac `c` >>
    match_mp_tac syneq_sym >>
    rw[Once syneq_cases] ) >>
  `no_closures (CConv cn vs2) ⇒ (vs1 = vs2)` by (
    strip_tac >>
    qsuff_tac `CConv cn vs1 = CConv cn vs2` >- rw[] >>
    match_mp_tac (MP_CANON no_closures_syneq_equal) >>
    rw[Once syneq_cases] >> PROVE_TAC[] ) >>
  Cases >> Cases >> TRY (Cases_on `l`) >> rw[] ) >>
strip_tac >- (
  rpt gen_tac >> strip_tac >>
  Cases >> Cases >> TRY (Cases_on `l`) >> rw[] ) >>
ntac 3 gen_tac >> Cases >> TRY (Cases_on `l`) >> rw[] )

val doPrim2_syneq = store_thm(
"doPrim2_syneq",
``∀c v1 v2. syneq c v1 v2 ⇒
    ∀b ty op v. (doPrim2 b ty op v v1 = doPrim2 b ty op v v2) ∧
                (doPrim2 b ty op v1 v = doPrim2 b ty op v2 v)``,
ho_match_mp_tac (CompileTheory.syneq_strongind) >> rw[] >>
Cases_on `v` >> rw[] >>
Cases_on `l` >> rw[])

val CevalUpd_syneq = store_thm(
"CevalUpd_syneq",
``∀c s1 v1 v2 s2 w1 w2.
  syneq c v1 w1 ∧ syneq c v2 w2 ∧ fmap_rel (syneq c) s1 s2 ⇒
  fmap_rel (syneq c) (FST (CevalUpd s1 v1 v2)) (FST (CevalUpd s2 w1 w2)) ∧
  result_rel (syneq c) (SND (CevalUpd s1 v1 v2)) (SND (CevalUpd s2 w1 w2))``,
  ntac 2 gen_tac >>
  Cases >> simp[] >>
  ntac 2 gen_tac >>
  Cases >> simp[] >>
  simp[Once syneq_cases] >>
  rw[] >> TRY (
    match_mp_tac fmap_rel_FUPDATE_same >>
    rw[] ) >>
  simp[fmap_rel_def] >>
  PROVE_TAC[])

(* Closed values *)

val (Cclosed_rules,Cclosed_ind,Cclosed_cases) = Hol_reln`
(Cclosed c (CLitv l)) ∧
(EVERY (Cclosed c) vs ⇒ Cclosed c (CConv cn vs)) ∧
((∀v. v ∈ FRANGE env ⇒ Cclosed c v) ∧
 ((ns = []) ⇒
  ∃xs cb. (defs = [(xs,cb)]) ∧
    cbod_fvs c cb ⊆ FDOM env ∪ set xs ∧
    (∀l. (cb = INR l) ⇒ l ∈ FDOM c)) ∧
 ((ns ≠ []) ⇒
  (LENGTH ns = LENGTH defs) ∧
  ALL_DISTINCT ns ∧
  MEM n ns ∧
  (∀i xs cb. i < LENGTH ns ∧ (EL i defs = (xs,cb)) ⇒
     cbod_fvs c cb ⊆ FDOM env ∪ set ns ∪ set xs ∧
     (∀l. (cb = INR l) ⇒ l ∈ FDOM c)))
  ⇒ Cclosed c (CRecClos env ns defs n)) ∧
(Cclosed c (CLoc m))`

val Cclosed_lit = store_thm("Cclosed_lit",
  ``Cclosed c (CLitv l)``,
  rw[Cclosed_rules])
val _ = export_rewrites["Cclosed_lit"]

val doPrim2_closed = store_thm(
"doPrim2_closed",
``∀c b ty op v1 v2. every_result (Cclosed c) (doPrim2 b ty op v1 v2)``,
ntac 4 gen_tac >>
Cases >> TRY (Cases_on `l`) >>
Cases >> TRY (Cases_on `l`) >>
rw[Cclosed_rules])
val _ = export_rewrites["doPrim2_closed"];

val CevalPrim2_closed = store_thm(
"CevalPrim2_closed",
``∀c p2 v1 v2. every_result (Cclosed c) (CevalPrim2 p2 v1 v2)``,
gen_tac >> Cases >> rw[Cclosed_rules])
val _ = export_rewrites["CevalPrim2_closed"];

val CevalPrim1_closed = store_thm(
"CevalPrim1_closed",
``∀c uop s v. (∀v. v ∈ FRANGE s ⇒ Cclosed c v) ∧ Cclosed c v ⇒
(∀w. w ∈ FRANGE (FST (CevalPrim1 uop s v)) ⇒ Cclosed c w) ∧
  every_result (Cclosed c) (SND (CevalPrim1 uop s v))``,
gen_tac >> Cases >> rw[LET_THM,Cclosed_rules] >> rw[] >- (
  pop_assum mp_tac >>
  match_mp_tac IN_FRANGE_DOMSUB_suff >> rw[] )
>- ( Cases_on`v`>>fs[] )
>- ( Cases_on`v`>>fs[] >>
  BasicProvers.CASE_TAC >> rw[] >>
  fs[IN_FRANGE,FLOOKUP_DEF] >>
  metis_tac[]))

val CevalUpd_closed = store_thm(
"CevalUpd_closed",
``(∀c s v1 v2. Cclosed c v2 ⇒ every_result (Cclosed c) (SND (CevalUpd s v1 v2))) ∧
  (∀c s v1 v2. (∀v. v ∈ FRANGE s ⇒ Cclosed c v) ∧ Cclosed c v2 ⇒
    (∀v. v ∈ FRANGE (FST (CevalUpd s v1 v2)) ⇒ Cclosed c v))``,
  conj_tac >>
  ntac 2 gen_tac >>
  Cases >> simp[] >- rw[] >>
  rpt gen_tac >> strip_tac >>
  BasicProvers.CASE_TAC >>
  match_mp_tac IN_FRANGE_FUPDATE_suff >>
  rw[])

val Cevaluate_closed = store_thm("Cevaluate_closed",
  ``(∀c d s env exp res. Cevaluate c d s env exp res
     ⇒ free_vars c exp ⊆ FDOM env
     ∧ (∀v. v ∈ FRANGE env ⇒ Cclosed c v)
     ∧ (∀v. v ∈ FRANGE s ⇒ Cclosed c v)
     ⇒
     (∀v. v ∈ FRANGE (FST res) ⇒ Cclosed c v) ∧
     every_result (Cclosed c) (SND res)) ∧
    (∀c d s env exps ress. Cevaluate_list c d s env exps ress
     ⇒ BIGUNION (IMAGE (free_vars c) (set exps)) ⊆ FDOM env
     ∧ (∀v. v ∈ FRANGE env ⇒ Cclosed c v)
     ∧ (∀v. v ∈ FRANGE s ⇒ Cclosed c v)
     ⇒
     (∀v. v ∈ FRANGE (FST ress) ⇒ Cclosed c v) ∧
     every_result (EVERY (Cclosed c)) (SND ress))``,
  ho_match_mp_tac Cevaluate_ind >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rpt gen_tac >> ntac 2 strip_tac >>
    fsrw_tac[DNF_ss][] >>
    rfs[] >>
    conj_tac >- (
      rw[] >>
      qpat_assum`∀x. P ⇒ Q x ⇒ R x`(match_mp_tac o MP_CANON) >>
      fsrw_tac[DNF_ss][SUBSET_DEF] >>
      conj_tac >- metis_tac[] >>
      match_mp_tac IN_FRANGE_DOMSUB_suff >> rw[] ) >>
    first_x_assum match_mp_tac >>
    fsrw_tac[DNF_ss][SUBSET_DEF] >>
    conj_tac >- metis_tac[] >>
    match_mp_tac IN_FRANGE_DOMSUB_suff >> rw[] ) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rw[] >> fsrw_tac[DNF_ss][FRANGE_DEF] ) >>
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
    fsrw_tac[DNF_ss][SUBSET_DEF,IN_FRANGE,DOMSUB_FAPPLY_THM] >>
    fsrw_tac[][FAPPLY_FUPDATE_THM] >>
    metis_tac[] ) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rpt gen_tac >> ntac 2 strip_tac >>
    fs[FOLDL_UNION_BIGUNION_paired] >>
    qpat_assum `LENGTH ns = X` assume_tac >>
    fs[FOLDL2_FUPDATE_LIST_paired,FDOM_FUPDATE_LIST,MAP2_MAP,FST_triple,MAP_ZIP] >>
    first_x_assum match_mp_tac >>
    fsrw_tac[DNF_ss][SUBSET_DEF] >>
    conj_tac >- PROVE_TAC[] >>
    match_mp_tac IN_FRANGE_FUPDATE_LIST_suff >>
    fs[MAP_ZIP] >>
    fs[MEM_MAP,pairTheory.EXISTS_PROD] >>
    fsrw_tac[DNF_ss][MEM_ZIP,MEM_EL] >>
    rw[Once Cclosed_cases] >>
    pop_assum (assume_tac o SYM) >> fs[] >> rw[] >>
    TRY (first_x_assum match_mp_tac >> PROVE_TAC[]) >>
    fsrw_tac[DNF_ss][SUBSET_DEF] >>
    qx_gen_tac `x` >>
    srw_tac[DNF_ss][] >>
    first_x_assum (qspecl_then [`x`,`n`] mp_tac) >>
    rw[] >> PROVE_TAC[] ) >>
  strip_tac >- (
    rpt gen_tac >> ntac 2 strip_tac >>
    fs[FOLDL_FUPDATE_LIST,FOLDL_UNION_BIGUNION_paired] >>
    first_x_assum match_mp_tac >>
    fs[FDOM_FUPDATE_LIST,MAP_MAP_o,combinTheory.o_DEF] >>
    fsrw_tac[DNF_ss][FRANGE_DEF,SUBSET_DEF,FDOM_FUPDATE_LIST,MAP_MAP_o,combinTheory.o_DEF] >>
    conj_tac >- PROVE_TAC[] >>
    qho_match_abbrev_tac `(∀x. P x ⇒ R x) ∧ (∀x. Q x ⇒ R x)` >>
    qsuff_tac `∀x. Q x ∨ (¬Q x ∧ P x) ⇒ R x` >- PROVE_TAC[] >>
    gen_tac >>
    unabbrev_all_tac >> rw[] >>
    ho_match_mp_tac FUPDATE_LIST_APPLY_HO_THM >|[
      disj1_tac >>
      fsrw_tac[DNF_ss][EL_MAP,MAP_ZIP,LENGTH_ZIP,MEM_EL,EL_ZIP] >>
      qpat_assum `LENGTH ns = LENGTH defs` assume_tac >>
      qexists_tac `n` >> fs[LENGTH_ZIP,EL_MAP,EL_ZIP] >>
      fs[EL_ALL_DISTINCT_EL_EQ] >>
      rw[Once Cclosed_cases,MEM_EL] >>
      fsrw_tac[DNF_ss][SUBSET_DEF,FRANGE_DEF,EL_ALL_DISTINCT_EL_EQ,LENGTH_NIL_SYM]
      >- PROVE_TAC[] >- PROVE_TAC[] >>
      TRY (first_x_assum match_mp_tac >> PROVE_TAC[]) >>
      qmatch_assum_rename_tac `EL i defs = (xs,b)`[] >>
      qx_gen_tac `x` >>
      first_x_assum (qspecl_then [`x`,`i`] mp_tac) >>
      fs[] >> PROVE_TAC[],
     disj2_tac >>
     fs[MAP_ZIP,MEM_MAP,MEM_ZIP,LENGTH_ZIP,pairTheory.EXISTS_PROD,MEM_EL] >>
     PROVE_TAC[]
    ]) >>
  strip_tac >- (
    rw[] >>
    rw[Once Cclosed_cases] >>
    fs[SUBSET_DEF] >> rw[] >> fs[] >>
    PROVE_TAC[] ) >>
  strip_tac >- (
    rpt gen_tac >> ntac 2 strip_tac >>
    fs[FOLDL_UNION_BIGUNION] >>
    first_x_assum match_mp_tac >>
    conj_tac >- (
      rw[] >>
      fs[Q.SPECL[`c`,`CRecClos env' ns' defs n`]Cclosed_cases] >>
      Cases_on`ns'=[]`>>fs[] >>
      TRY(first_x_assum (qspecl_then [`i`,`ns`] mp_tac) >> rw[]) >>
      Cases_on `cb` >> fs[] >>
      imp_res_tac find_index_LESS_LENGTH >> pop_assum mp_tac >>
      fs[] >> rw[] >> fs[] >>
      fs[FLOOKUP_DEF] >>
      imp_res_tac free_vars_DOMSUB >>
      fsrw_tac[DNF_ss][SUBSET_DEF] >>
      PROVE_TAC[]) >>
    fs[extend_rec_env_def,FOLDL2_FUPDATE_LIST,FOLDL_FUPDATE_LIST] >>
    fsrw_tac[ETA_ss][] >>
    rw[] >> pop_assum mp_tac >>
    match_mp_tac IN_FRANGE_FUPDATE_LIST_suff >>
    fs[MAP2_MAP,FST_pair,SND_pair,MAP_ZIP] >>
    conj_tac >- (
      match_mp_tac IN_FRANGE_FUPDATE_LIST_suff >>
      fs[MAP_MAP_o,combinTheory.o_DEF] >>
      conj_tac >- (
        fs[Q.SPECL[`c`,`CRecClos env' ns' defs n`]Cclosed_cases] ) >>
      fsrw_tac[DNF_ss][MEM_MAP] >>
      fs[Q.SPECL[`c`,`CRecClos env' ns' defs n`]Cclosed_cases] >>
      rw[MEM_EL] >> PROVE_TAC[] ) >>
    fs[] >>
    qpat_assum `LENGTH es = X` assume_tac >>
    fs[EVERY_MEM,pairTheory.FORALL_PROD,MEM_ZIP]) >>
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
      map_every qexists_tac[`s'`,`v1`,`v2`] >> rw[] ) >>
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
  fsrw_tac[DNF_ss][MAP2_MAP,MAP_ZIP,FST_triple] >>
  `free_vars c exp ⊆ FDOM env ∪ set ns` by (
    fsrw_tac[DNF_ss][SUBSET_DEF,pairTheory.FORALL_PROD] >>
    PROVE_TAC[] ) >>
  fs[FDOM_DRESTRICT] >> fsrw_tac[SATISFY_ss][] >>
  qho_match_abbrev_tac `∃res'. (P ∧ Cevaluate c d s' (env0 |++ (ls0 env0)) exp res') ∧
    fmap_rel (syneq c) (FST res) (FST res') ∧
    result_rel (syneq c) (SND res) (SND res')` >>
  `P` by (
    unabbrev_all_tac >>
    `FDOM env' = FDOM env` by fs[fmap_rel_def] >> fs[] >>
    rpt gen_tac >> strip_tac >> res_tac >> fs[] >>
    full_simp_tac std_ss [SUBSET_DEF,EXTENSION,IN_INTER,IN_DIFF,IN_UNION] >>
    gen_tac >> EQ_TAC >- (
      strip_tac >> asm_simp_tac std_ss [] >>
      disj1_tac >> disj2_tac >>
      fsrw_tac[DNF_ss][FORALL_PROD,EXISTS_PROD] >>
      map_every qexists_tac[`xs`,`INR l`] >>
      rw[FLOOKUP_DEF] >>
      metis_tac[free_vars_DOMSUB,SUBSET_DEF,IN_UNION] ) >>
    asm_simp_tac std_ss [] >>
    fsrw_tac[DNF_ss][FORALL_PROD] >>
    first_x_assum(qspecl_then[`x`,`xs`,`INR l`]mp_tac) >>
    rw[FLOOKUP_DEF] >>
    metis_tac[free_vars_DOMSUB,SUBSET_DEF,IN_UNION] ) >>
  simp[Abbr`P`] >> pop_assum kall_tac >>
  `fmap_rel (syneq c) (env |++ (ls0 env)) (env' |++ (ls0 env0))` by (
    unabbrev_all_tac >> fs[] >>
    match_mp_tac fmap_rel_FUPDATE_LIST_same >>
    fs[MAP_ZIP] >>
    fs[LIST_REL_EL_EQN,EL_MAP,EL_ZIP] >>
    qx_gen_tac `n` >> strip_tac >>
    rw[pairTheory.UNCURRY] >>
    rw[syneq_cases,EVERY_MEM,pairTheory.FORALL_PROD] >>
    Cases_on`ns=[]`>-(fs[LENGTH_NIL_SYM]>>rfs[]) >>fs[] >>
    `∃xs b. EL n defs = (xs,b)`by (Cases_on`EL n defs`>>fs[]>>metis_tac[])>>
    map_every qexists_tac [`xs`,`b`] >> fs[] >>
    qx_gen_tac`v` >> strip_tac >>
    `v ∈ FDOM env` by (
      fsrw_tac[DNF_ss][SUBSET_DEF,pairTheory.FORALL_PROD,MEM_EL] >>
      fsrw_tac[DNF_ss][pairTheory.UNCURRY,MEM_EL] >>
      metis_tac[pairTheory.FST,pairTheory.SND] ) >> fs[] >>
    fs[fmap_rel_def,optionTheory.OPTREL_def,FLOOKUP_DEF] >>
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
    qabbrev_tac `z = EL n defs` >> PairCases_on`z` >> rw[] >>
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
    Cases_on`EL n defs` >>
    rw[Once Cclosed_cases,SUBSET_DEF] >>
    TRY (first_x_assum match_mp_tac >> fsrw_tac[DNF_ss][MEM_EL] >> PROVE_TAC[]) >>
    fsrw_tac[DNF_ss][SUBSET_DEF] >>
    qmatch_assum_rename_tac `EL n defs = (xs,b)`[] >>
    first_x_assum (qspecl_then [`x`,`EL n defs`] mp_tac) >>
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
  rw[FOLDL_UNION_BIGUNION_paired] >>
  rw[Once Cevaluate_cases] >>
  qpat_assum `LENGTH ns = LENGTH defs` assume_tac >>
  fs[FOLDL_FUPDATE_LIST,FDOM_FUPDATE_LIST,FOLDL2_FUPDATE_LIST_paired] >>
  fsrw_tac[DNF_ss][MAP2_MAP,MAP_ZIP,FST_triple,MAP_MAP_o,combinTheory.o_DEF] >>
  `free_vars c exp ⊆ FDOM env ∪ set ns` by (
    fsrw_tac[DNF_ss][SUBSET_DEF,pairTheory.FORALL_PROD] >>
    PROVE_TAC[] ) >>
  fs[] >> fsrw_tac[SATISFY_ss][] >>
  qho_match_abbrev_tac `∃res'. (P ∧ Cevaluate c d s' (env0 |++ (ls0 env0)) exp res') ∧
    fmap_rel (syneq c) (FST res) (FST res') ∧
    result_rel (syneq c) (SND res) (SND res')` >>
  `P` by (
    unabbrev_all_tac >> rw[] >>
    res_tac >> fs[FDOM_DRESTRICT] >>
    simp_tac std_ss [EXTENSION] >>
    gen_tac >>
    fsrw_tac[DNF_ss][SUBSET_DEF,FORALL_PROD,EXISTS_PROD] >>
    first_x_assum(qspecl_then[`x`,`xs`,`INR l`]mp_tac) >>
    `MEM (xs,INR l) defs` by (rw[MEM_EL] >> PROVE_TAC[]) >>
    rw[FLOOKUP_DEF] >>
    EQ_TAC >- (
      strip_tac >> fs[fmap_rel_def] >>
      disj1_tac >> disj2_tac >>
      map_every qexists_tac[`xs`,`INR l`] >>
      rw[FLOOKUP_DEF] >>
      metis_tac[free_vars_DOMSUB,IN_UNION,SUBSET_DEF] ) >>
    fsrw_tac[DNF_ss][] >>
    metis_tac[free_vars_DOMSUB,IN_UNION,SUBSET_DEF] ) >>
  simp[Abbr`P`] >> pop_assum kall_tac >>
  `fmap_rel (syneq c) (env |++ (ls0 env)) (env' |++ (ls0 env0))` by (
    unabbrev_all_tac >> fs[] >>
    match_mp_tac fmap_rel_FUPDATE_LIST_same >>
    fs[MAP_ZIP,MAP_MAP_o,combinTheory.o_DEF] >>
    fs[LIST_REL_EL_EQN,EL_MAP,EL_ZIP] >>
    qx_gen_tac `n` >> strip_tac >>
    rw[pairTheory.UNCURRY] >>
    Cases_on`ns=[]`>-(fs[LENGTH_NIL_SYM]>>rfs[]) >>fs[] >>
    `∃xs b. EL n defs = (xs,b)`by (Cases_on`EL n defs`>>fs[]>>metis_tac[])>>
    map_every qexists_tac [`xs`,`b`] >> fs[] >>
    qx_gen_tac`v` >> strip_tac >>
    `v ∈ FDOM env` by (
      fsrw_tac[DNF_ss][SUBSET_DEF,pairTheory.FORALL_PROD,MEM_EL] >>
      fsrw_tac[DNF_ss][pairTheory.UNCURRY,MEM_EL] >>
      metis_tac[pairTheory.FST,pairTheory.SND] ) >> fs[] >>
    fs[fmap_rel_def,optionTheory.OPTREL_def,FLOOKUP_DEF] >>
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
  srw_tac[DNF_ss][] >- (
    fs[FLOOKUP_DEF,FDOM_DRESTRICT,fmap_rel_def] >>
    fsrw_tac[DNF_ss][EXTENSION,SUBSET_DEF] >>
    metis_tac[] ) >>
  rw[syneq_cases,FLOOKUP_DEF] >>
  rw[DRESTRICT_DEF,optionTheory.OPTREL_def] >>
  map_every qexists_tac[`xs`,`cb`] >> rw[] >>
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
  qmatch_assum_abbrev_tac `Cevaluate c d s2 env1 exp (s3,Rval (CRecClos env3 ns' defs n))` >>
  CONV_TAC SWAP_EXISTS_CONV >> qexists_tac `env3` >>
  CONV_TAC SWAP_EXISTS_CONV >> qexists_tac `ns'` >>
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
   Cclosed c (CRecClos env' ns' defs n)` by (
    qspecl_then[`c`,`d`,`s`,`env`,`exp`,`(s',Rval (CRecClos env' ns' defs n))`]mp_tac(CONJUNCT1 Cevaluate_closed) >>
    rw[] ) >> fs[] >>
  `(∀v. v ∈ FRANGE s3 ⇒ Cclosed c v) ∧
   Cclosed c (CRecClos env2' ns' defs n)` by (
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
  fs[Once(Q.SPECL[`c`,`CRecClos env2' ns' defs n`] Cclosed_cases)] >>
  `∀v. v ∈ FRANGE (extend_rec_env env' env' ns' defs ns vs) ⇒ Cclosed c v` by (
    fs[extend_rec_env_def,FOLDL2_FUPDATE_LIST,FOLDL_FUPDATE_LIST] >>
    match_mp_tac IN_FRANGE_FUPDATE_LIST_suff >>
    fsrw_tac[DNF_ss][MAP_ZIP,MAP2_MAP,SND_pair,FST_pair,MEM_EL,LENGTH_ZIP,EVERY_MEM] >>
    match_mp_tac IN_FRANGE_FUPDATE_LIST_suff >>
    fsrw_tac[DNF_ss][MAP_ZIP,MAP2_MAP,SND_pair,FST_pair,MEM_EL,LENGTH_ZIP,MAP_MAP_o,EL_MAP] >>
    rw[Once Cclosed_cases,MEM_EL] >> fs[] >>
    PROVE_TAC[] ) >>
  fs[] >>
  qunabbrev_tac`env3` >>
  qabbrev_tac`env3 = extend_rec_env env2' env2' ns' defs ns v2` >>
  qmatch_assum_abbrev_tac `Cevaluate c d s'' X exp' res` >>
  qunabbrev_tac`X` >>
  `i < LENGTH defs` by (
    Cases_on`ns'=[]`>>fs[] >>
    imp_res_tac find_index_LESS_LENGTH >>
    fs[] >> rfs[] ) >>
  `free_vars c exp' ⊆ FDOM env' ∪ set ns' ∪ set ns` by (
    fsrw_tac[DNF_ss][SUBSET_DEF] >>
    first_x_assum (qspecl_then [`i`,`ns`,`cb`] mp_tac) >>
    rw[] >> fs[EVERY_MEM] >>
    `MEM (ns,cb) defs` by (rw[MEM_EL] >> qexists_tac `i` >> rw[] >> PROVE_TAC[] ) >>
    fsrw_tac[DNF_ss][optionTheory.OPTREL_def,FLOOKUP_DEF,FORALL_PROD] >>
    first_x_assum (qspecl_then [`i`,`ns`,`cb`] mp_tac) >> rw[] >>
    pop_assum (qspec_then `x` mp_tac) >> rw[] >>
    Cases_on`ns'=[]`>>fs[]>>
    TRY(qunabbrev_tac`exp'`) >> Cases_on `cb` >> fs[] >>
    fs[FLOOKUP_DEF] >> rw[] >>
    `x ∈ free_vars (c \\ y) (c ' y)` by
      metis_tac[free_vars_DOMSUB,SUBSET_DEF,IN_UNION] >>
    ntac 3 (pop_assum mp_tac) >> rw[] >> fs[] >>
    fsrw_tac[DNF_ss][MEM_EL] >>
    metis_tac[]) >>
  fs[] >>
  qabbrev_tac `env4 =
    extend_rec_env env2' (DRESTRICT env2' (free_vars c exp' DIFF set ns DIFF set ns') ⊌ env') ns' defs ns v2` >>
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
      `MEM (ns,cb) defs` by (rw[MEM_EL] >> qexists_tac `i` >> rw[] >> PROVE_TAC[] ) >>
      fsrw_tac[DNF_ss][EVERY_MEM,FORALL_PROD] >>
      first_x_assum (qspecl_then [`i`,`ns`,`cb`] mp_tac) >> fs[] >>
      first_x_assum (qspecl_then [`i`,`ns`,`cb`] mp_tac) >> fs[] >>

      Cases_on `cb` >> fs[] >- (Cases_on`ns' = []` >> fs[] >> metis_tac[]) >>

      Cases_on `ns' = []` >> fs[] >>
      rw[FLOOKUP_DEF] >> fs[] >>
      `x ∈ free_vars (c \\ y) (c ' y)` by
        metis_tac[free_vars_DOMSUB,IN_UNION,SUBSET_DEF] >>
      fsrw_tac[DNF_ss][SUBSET_DEF] >>
      TRY(first_x_assum (qspecl_then [`i`,`ns`,`y`] mp_tac) >> fs[]) >>
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
    Cases_on`cb`>>fs[FLOOKUP_DEF] >> rw[] >> fs[]
    >- metis_tac[SND]
    >- (
      qpat_assum `X = d ' y` (assume_tac o SYM) >>
      rw[] >> fsrw_tac[DNF_ss][EVERY_MEM,FORALL_PROD,MEM_EL] >>
      first_x_assum (qspecl_then[`ns`,`INR y`,`i`]mp_tac) >>
      rw[FLOOKUP_DEF,optionTheory.OPTREL_def] >>
      REWRITE_TAC[GSYM CONJ_ASSOC] >>
      simp[RIGHT_EXISTS_AND_THM] >>
      conj_tac >- (
        simp[EXTENSION,MEM_EL] >>
        METIS_TAC[SND] ) >>
      metis_tac[SND] ) >>
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
    Cases_on `MEM x ns` >> fs[] >>
    Cases_on `MEM x ns'` >> fs[] >>
    Cases_on `x ∈ FDOM env2'` >> fs[] >>
    Cases_on `ns' = []` >> fs[] >> rw[] >>
    TRY(first_x_assum (qspecl_then [`i`,`ns`,`cb`] mp_tac)) >>
    TRY(first_x_assum (qspecl_then [`i`,`ns`,`cb`] mp_tac)) >>
    fs[] >>
    Cases_on `cb` >> fs[] >- METIS_TAC[] >>
    rw[FLOOKUP_DEF] >>
    fs[FLOOKUP_DEF] >> rfs[] >>
    rpt (pop_assum (qspec_then `x` mp_tac)) >> fs[] >>
    PROVE_TAC[free_vars_DOMSUB,IN_UNION,SUBSET_DEF]) >>
  rw[DRESTRICT_IS_FEMPTY,FUNION_FEMPTY_2] >>
  rw[DIFF_COMM] >>
  Q.ISPECL_THEN [`extend_rec_env env2' FEMPTY ns' defs ns v2`,`env2'`,`free_vars c ee`] (mp_tac o GSYM) DRESTRICTED_FUNION >>
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
  Cases_on`v'`>>fs[] >>
  qmatch_assum_rename_tac`LENGTH t = 1`[] >>
  Cases_on`t`>>fs[] >> fs[LENGTH_NIL] >> rw[] >>
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
  Cases_on`v'`>>fs[] >>
  qmatch_assum_rename_tac`LENGTH t = 1`[] >>
  Cases_on`t`>>fs[] >> fs[LENGTH_NIL] >> rw[] >>
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
