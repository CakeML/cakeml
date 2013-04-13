open HolKernel bossLib boolLib boolSimps pairTheory listTheory rich_listTheory pred_setTheory finite_mapTheory relationTheory SatisfySimps arithmeticTheory quantHeuristicsLib lcsymtacs
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

(* syneq equivalence relation lemmas *)

(* TODO: move *)
(*val syneq_cds_def = CompileTheory.syneq_cds_def*)
fun RATOR_X_ASSUM t ttac (g as (asl,w)) = UNDISCH_THEN (first (can (match_term t) o fst o strip_comb) asl) ttac g
fun rator_x_assum q ttac = Q_TAC (C RATOR_X_ASSUM ttac) q
fun RATOR_ASSUM t ttac (g as (asl,w)) = ttac (ASSUME (first (can (match_term t) o fst o strip_comb) asl)) g
fun rator_assum q ttac = Q_TAC (C RATOR_ASSUM ttac) q
val rev_assum_list = POP_ASSUM_LIST (MAP_EVERY ASSUME_TAC)
fun last_x_assum x = rev_assum_list >> first_x_assum x >> rev_assum_list
fun qx_choosel_then [] ttac = ttac
  | qx_choosel_then (q::qs) ttac = Q.X_CHOOSE_THEN q (qx_choosel_then qs ttac)

val Cv_ind = store_thm("Cv_ind",
  ``∀P. (∀l. P (CLitv l)) ∧ (∀n vs. EVERY P vs ⇒ P (CConv n vs)) ∧
        (∀env defs n. EVERY P env ⇒ P (CRecClos env defs n)) ∧
        (∀n. P (CLoc n)) ⇒
        ∀v. P v``,
  rw[] >>
  qsuff_tac `(∀v. P v) ∧ (∀vs. EVERY P vs)` >- rw[] >>
  ho_match_mp_tac(TypeBase.induction_of``:Cv``) >>
  simp[])

val syneq_lit_loc = store_thm("syneq_lit_loc",
  ``(syneq c1 c2 (CLitv l1) v2 = (v2 = CLitv l1)) ∧
    (syneq c1 c2 v1 (CLitv l2) = (v1 = CLitv l2)) ∧
    (syneq c1 c2 (CLoc n1) v2 = (v2 = CLoc n1)) ∧
    (syneq c1 c2 v1 (CLoc n2) = (v1 = CLoc n2))``,
  rw[] >> fs[Once syneq_cases] >> rw[EQ_IMP_THM])
val _ = export_rewrites["syneq_lit_loc"]

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
``∀ls n m i. (find_index n ls m = SOME i) ⇒ (m <= i) ∧ (i < m + LENGTH ls)``,
Induct >> rw[find_index_def] >>
res_tac >>
srw_tac[ARITH_ss][arithmeticTheory.ADD1])

val Cexp_only_ind =
   TypeBase.induction_of``:Cexp``
|> Q.SPECL[`P`,`K T`,`K T`,`K T`,`EVERY P`]
|> SIMP_RULE (srw_ss())[]
|> UNDISCH_ALL
|> CONJUNCT1
|> DISCH_ALL
|> Q.GEN`P`

val syneq_defs_refl = hd(rev(CONJUNCTS syneq_exp_rules))

val syneq_exp_refl = store_thm("syneq_exp_refl",
  ``(∀e c z V. (∀v. v < z ⇒ V v v) ⇒ syneq_exp c c z z V e e)``,
  ho_match_mp_tac Cexp_only_ind >>
  strip_tac >- (
    rw[Once syneq_exp_cases] >>
    fsrw_tac[DNF_ss][EVERY2_EVERY,EVERY_MEM,FORALL_PROD,MEM_ZIP,EL_MAP] >>
    rw[] >> Cases_on `FST (EL n l) < z` >> fsrw_tac[ARITH_ss][]) >>
  strip_tac >- rw[Once syneq_exp_cases] >>
  strip_tac >- (
    rw[] >> rw[Once syneq_exp_cases] >>
    first_x_assum match_mp_tac >>
    Cases >> srw_tac[ARITH_ss][] ) >>
  strip_tac >- (
    rw[Once syneq_exp_cases] >>
    Cases_on`n < z` >> fsrw_tac[ARITH_ss][] ) >>
  strip_tac >- rw[Once syneq_exp_cases] >>
  strip_tac >- (
    rw[] >> rw[Once syneq_exp_cases] >>
    fsrw_tac[DNF_ss][EVERY2_EVERY,EVERY_MEM,MEM_ZIP,MEM_EL] ) >>
  strip_tac >- ( rw[] >> rw[Once syneq_exp_cases] ) >>
  strip_tac >- ( rw[] >> rw[Once syneq_exp_cases] ) >>
  strip_tac >- (
    rw[] >> rw[Once syneq_exp_cases] >>
    first_x_assum match_mp_tac >>
    Cases >> srw_tac[ARITH_ss][] ) >>
  strip_tac >- (
    rw[] >> rw[Once syneq_exp_cases] >>
    qexists_tac`λv1 v2. v1 < LENGTH l ∧ (v2 = v1)` >>
    conj_tac >- (
      match_mp_tac syneq_defs_refl >>
      simp[] ) >>
    first_x_assum match_mp_tac >>
    srw_tac[ARITH_ss][] >>
    Cases_on`v < LENGTH l`>>fsrw_tac[ARITH_ss][]) >>
  strip_tac >- (
    rw[] >> rw[Once syneq_exp_cases] >>
    qexists_tac`λv1 v2. (v1,v2) = (0,0)` >> rw[] >>
    match_mp_tac syneq_defs_refl >>
    simp[FUN_EQ_THM]) >>
  strip_tac >- (
    rw[] >> rw[Once syneq_exp_cases] >>
    fsrw_tac[DNF_ss][EVERY2_EVERY,EVERY_MEM,MEM_ZIP,MEM_EL]) >>
  strip_tac >- ( rw[] >> rw[Once syneq_exp_cases] ) >>
  strip_tac >- ( rw[] >> rw[Once syneq_exp_cases] ) >>
  strip_tac >- ( rw[] >> rw[Once syneq_exp_cases] ) >>
  strip_tac >- ( rw[] >> rw[Once syneq_exp_cases] ))

val syneq_refl = store_thm("syneq_refl",
  ``∀v c. syneq c c v v``,
  ho_match_mp_tac Cv_ind >> rw[] >>
  simp[Once syneq_cases] >>
  fsrw_tac[DNF_ss][EVERY_MEM,EVERY2_EVERY,FORALL_PROD,MEM_ZIP,MEM_EL] >>
  Cases_on`n < LENGTH defs`>>fsrw_tac[ARITH_ss][]>>
  map_every qexists_tac[`λv1 v2. v1 < LENGTH env ∧ (v2 = v1)`,`λv1 v2. v1 < LENGTH defs ∧ (v2 = v1)`] >>
  simp[] >>
  match_mp_tac syneq_defs_refl >>
  simp[])
val _ = export_rewrites["syneq_refl"]

val inv_syneq_cb_V = store_thm("inv_syneq_cb_V",
  ``inv (syneq_cb_V az r1 r2 V V') = syneq_cb_V az r2 r1 (inv V) (inv V')``,
  simp[FUN_EQ_THM,syneq_cb_V_def,inv_DEF] >>
  srw_tac[DNF_ss][] >>
  PROVE_TAC[])

val syneq_exp_sym = store_thm("syneq_exp_sym",
  ``(∀c1 c2 ez1 ez2 V exp1 exp2. syneq_exp c1 c2 ez1 ez2 V exp1 exp2 ⇒ syneq_exp c2 c1 ez2 ez1 (inv V) exp2 exp1) ∧
    (∀c1 c2 ez1 ez2 V defs1 defs2 V'. syneq_defs c1 c2 ez1 ez2 V defs1 defs2 V' ⇒ syneq_defs c2 c1 ez2 ez1 (inv V) defs2 defs1 (inv V'))``,
  ho_match_mp_tac syneq_exp_ind >>
  strip_tac >- (
    rw[] >>
    rw[Once syneq_exp_cases] >>
    fsrw_tac[DNF_ss][EVERY2_EVERY,EVERY_MEM,inv_DEF] >>
    pop_assum mp_tac >>
    fsrw_tac[DNF_ss][MEM_ZIP,EL_MAP] >>
    rw[] >> res_tac >> fs[]) >>
  strip_tac >- ( rw[Once syneq_exp_cases]) >>
  strip_tac >- (
    rw[] >> rw[Once syneq_exp_cases] >>
    pop_assum mp_tac >>
    qmatch_abbrev_tac`a ==> b` >>
    qsuff_tac`a = b` >- rw[] >>
    unabbrev_all_tac >>
    rpt AP_THM_TAC >> rpt AP_TERM_TAC >>
    simp[FUN_EQ_THM,inv_DEF] >>
    PROVE_TAC[]) >>
  strip_tac >- ( rw[] >> rw[Once syneq_exp_cases,inv_DEF] ) >>
  strip_tac >- ( rw[] >> rw[Once syneq_exp_cases] ) >>
  strip_tac >- (
    rw[] >> rw[Once syneq_exp_cases] >>
    fs[EVERY2_EVERY,EVERY_MEM,FORALL_PROD,inv_DEF] >>
    pop_assum mp_tac >> simp[MEM_ZIP] >>
    fsrw_tac[DNF_ss][]) >>
  strip_tac >- ( rw[] >> rw[Once syneq_exp_cases] ) >>
  strip_tac >- ( rw[] >> rw[Once syneq_exp_cases] ) >>
  strip_tac >- (
    rw[] >> rw[Once syneq_exp_cases] >>
    pop_assum mp_tac >>
    qmatch_abbrev_tac`a ==> b` >>
    qsuff_tac`a = b` >- rw[] >>
    unabbrev_all_tac >>
    rpt AP_THM_TAC >> rpt AP_TERM_TAC >>
    simp[FUN_EQ_THM,inv_DEF] >>
    PROVE_TAC[]) >>
  strip_tac >- (
    rw[] >> rw[Once syneq_exp_cases] >>
    qexists_tac`inv V'` >> simp[] >>
    pop_assum mp_tac >>
    qmatch_abbrev_tac`a ==> b` >>
    qsuff_tac`a = b` >- rw[] >>
    unabbrev_all_tac >> fs[] >>
    rpt AP_THM_TAC >> rpt AP_TERM_TAC >>
    simp[FUN_EQ_THM,inv_DEF] >>
    PROVE_TAC[]) >>
  strip_tac >- (
    rw[] >> rw[Once syneq_exp_cases] >>
    qexists_tac`inv V'` >>
    fs[inv_DEF]) >>
  strip_tac >- (
    rw[] >> simp[Once syneq_exp_cases] >>
    fs[EVERY2_EVERY,EVERY_MEM,MEM_ZIP,FORALL_PROD] >>
    ntac 2 (pop_assum mp_tac) >> fs[MEM_ZIP] >>
    PROVE_TAC[]) >>
  strip_tac >- ( rw[] >> rw[Once syneq_exp_cases] ) >>
  strip_tac >- (
    rw[] >> rw[Once syneq_exp_cases] >>
    fs[EVERY2_EVERY,EVERY_MEM,MEM_ZIP,FORALL_PROD] >>
    pop_assum mp_tac >> fs[MEM_ZIP] >>
    PROVE_TAC[]) >>
  strip_tac >- ( rw[] >> rw[Once syneq_exp_cases] ) >>
  strip_tac >- ( rw[] >> rw[Once syneq_exp_cases] ) >>
  rw[] >>
  rw[Once syneq_exp_cases] >>
  fs[inv_DEF,FUN_EQ_THM] >>
  fs[inv_syneq_cb_V] >>
  metis_tac[])

val syneq_sym = store_thm("syneq_sym",
  ``∀c1 c2 x y. syneq c1 c2 x y ⇒ syneq c2 c1 y x``,
  ho_match_mp_tac syneq_ind >> rw[] >- (
    rw[] >> simp[Once syneq_cases] >>
    fs[EVERY2_EVERY,EVERY_MEM,MEM_ZIP,FORALL_PROD] >>
    pop_assum mp_tac >> fs[MEM_ZIP] >>
    PROVE_TAC[]) >>
  rw[] >> rw[Once syneq_cases] >>
  map_every qexists_tac[`inv V`,`inv V'`] >>
  simp[inv_DEF] >>
  PROVE_TAC[syneq_exp_sym])

val syneq_exp_mono_V = store_thm("syneq_exp_mono_V",
  ``(∀c1 c2 ez1 ez2 V exp1 exp2. syneq_exp c1 c2 ez1 ez2 V exp1 exp2 ⇒ ∀V'. (∀x y. V x y ∧ x < ez1 ∧ y < ez2 ⇒ V' x y) ⇒ syneq_exp c1 c2 ez1 ez2 V' exp1 exp2) ∧
    (∀c1 c2 ez1 ez2 V defs1 defs2 U. syneq_defs c1 c2 ez1 ez2 V defs1 defs2 U ⇒
     ∀V'. (∀x y. V x y ∧ x < ez1 ∧ y < ez2 ⇒ V' x y) ⇒ syneq_defs c1 c2 ez1 ez2 V' defs1 defs2 U)``,
  ho_match_mp_tac syneq_exp_ind >>
  rw[] >> simp[Once syneq_exp_cases] >> rfs[] >>
  TRY ( first_x_assum (match_mp_tac o MP_CANON) >>
        simp[] >>
        srw_tac[ARITH_ss][] >>
        fsrw_tac[ARITH_ss][] >>
        PROVE_TAC[] ) >>
  TRY (
    rator_x_assum`EVERY2`mp_tac >>
    match_mp_tac EVERY2_mono >>
    simp[] ) >>
  TRY (
    qexists_tac`U` >> simp[] >>
    first_x_assum match_mp_tac >>
    simp[] >> rw[] >>
    fsrw_tac[ARITH_ss][] >> NO_TAC) >>
  TRY ( disj2_tac >> PROVE_TAC[] ) >>
  rw[] >> fs[] >>
  disj1_tac >>
  rpt gen_tac >> strip_tac >>
  last_x_assum(qspecl_then[`n1`,`n2`]mp_tac) >>
  simp[] >> strip_tac >>
  rpt (qpat_assum`A = B`(mp_tac o SYM)) >>
  rw[] >>
  first_x_assum (match_mp_tac o MP_CANON) >>
  simp[syneq_cb_V_def] >>
  srw_tac[ARITH_ss][] >>
  fsrw_tac[ARITH_ss][] >>
  first_x_assum match_mp_tac >>
  Cases_on`EL n1 defs1`>>
  TRY (qmatch_assum_rename_tac`EL n1 defs1 = INL p`[] >> PairCases_on`p`) >>
  fs[syneq_cb_aux_def,LET_THM,UNCURRY] >>
  Cases_on`EL n2 defs2`>>
  TRY (qmatch_assum_rename_tac`EL n2 defs2 = INL p`[] >> PairCases_on`p`) >>
  fs[syneq_cb_aux_def,LET_THM,UNCURRY] >>
  rw[] >> rpt (qpat_assum `X = CCEnv Y` mp_tac) >> srw_tac[ARITH_ss][] >>
  fsrw_tac[DNF_ss,ARITH_ss][EVERY_MEM,MEM_EL] >> rw[] )

val syneq_cb_V_refl = store_thm("syneq_cb_V_refl",
  ``(∀x. (b(f-a) = CCEnv x) ⇒ c x x) ∧ (∀x. (b(f-a) = CCRef x) ⇒ d x x) ⇒
    syneq_cb_V a b b c d f f``,
  simp[syneq_cb_V_def] >>
  Cases_on`f < a`>>fsrw_tac[ARITH_ss][] >>
  Cases_on`b (f-a)`>>rw[])

val syneq_cb_aux_lemma = prove(
  ``(syneq_cb_aux c n d z b = (t,az,e,j,r)) ∧ (r y = CCEnv k) ⇒ k < z``,
  Cases_on`b`>>TRY(PairCases_on`x`)>>rw[syneq_cb_aux_def,UNCURRY,LET_THM]>>fs[]>>
  pop_assum mp_tac >> rw[] >>
  fsrw_tac[ARITH_ss][])

val syneq_exp_trans = store_thm("syneq_exp_trans",
  ``(∀c1 c2 ez1 ez2 V e1 e2. syneq_exp c1 c2 ez1 ez2 V e1 e2 ⇒
      ∀c3 ez3 V' e3. syneq_exp c2 c3 ez2 ez3 V' e2 e3 ⇒ syneq_exp c1 c3 ez1 ez3 (V' O V) e1 e3) ∧
    (∀c1 c2 ez1 ez2 V d1 d2 U. syneq_defs c1 c2 ez1 ez2 V d1 d2 U ⇒
      ∀c3 ez3 V' d3 U'. syneq_defs c2 c3 ez2 ez3 V' d2 d3 U' ⇒ syneq_defs c1 c3 ez1 ez3 (V' O V) d1 d3 (U' O U))``,
  ho_match_mp_tac syneq_exp_ind >>
  strip_tac >- (
    rw[] >> pop_assum mp_tac >>
    simp[Once syneq_exp_cases] >>
    simp[Once syneq_exp_cases] >>
    fs[EVERY2_EVERY,EVERY_MEM,FORALL_PROD] >> rw[] >> rw[] >>
    rpt (qpat_assum` LENGTH X = LENGTH Y` mp_tac) >> rpt strip_tac >>
    fsrw_tac[DNF_ss][MEM_ZIP,EL_MAP,FST_pair,O_DEF] >> rw[] >>
    first_x_assum(qspec_then`n`mp_tac) >> rw[] >>
    first_x_assum(qspec_then`n`mp_tac) >> rw[] >>
    fsrw_tac[ARITH_ss][] >>
    PROVE_TAC[] ) >>
  strip_tac >- ( ntac 2 (rw[Once syneq_exp_cases] ) ) >>
  strip_tac >- (
    rw[] >> pop_assum mp_tac >>
    simp[Once syneq_exp_cases] >> strip_tac >>
    simp[Once syneq_exp_cases] >>
    res_tac >>
    match_mp_tac (MP_CANON(CONJUNCT1(syneq_exp_mono_V))) >>
    HINT_EXISTS_TAC >>
    simp[O_DEF] >>
    srw_tac[DNF_ss,ARITH_ss][] >>
    metis_tac[]) >>
  strip_tac >- (
    rw[] >> pop_assum mp_tac >>
    simp[Once syneq_exp_cases] >> strip_tac >>
    simp[Once syneq_exp_cases,O_DEF] >> PROVE_TAC[]) >>
  strip_tac >- (
    rw[] >> pop_assum mp_tac >>
    simp[Once syneq_exp_cases] >> strip_tac >>
    simp[Once syneq_exp_cases] ) >>
  strip_tac >- (
    rw[] >> pop_assum mp_tac >>
    simp[Once syneq_exp_cases] >> strip_tac >>
    simp[Once syneq_exp_cases] >>
    fs[EVERY2_EVERY,EVERY_MEM,MEM_ZIP] >> rw[] >>
    rpt (qpat_assum` LENGTH X = LENGTH Y` mp_tac) >>
    rpt strip_tac >>
    fs[MEM_ZIP,FORALL_PROD] >>
    PROVE_TAC[syneq_exp_rules] ) >>
  strip_tac >- (
    rw[] >> pop_assum mp_tac >>
    simp[Once syneq_exp_cases] >> strip_tac >>
    simp[Once syneq_exp_cases] >>
    PROVE_TAC[syneq_exp_rules]) >>
  strip_tac >- (
    rw[] >> pop_assum mp_tac >>
    simp[Once syneq_exp_cases] >> strip_tac >>
    simp[Once syneq_exp_cases] >>
    PROVE_TAC[syneq_exp_rules]) >>
  strip_tac >- (
    rw[] >> pop_assum mp_tac >>
    simp[Once syneq_exp_cases] >> strip_tac >>
    simp[Once syneq_exp_cases] >>
    res_tac >>
    match_mp_tac (MP_CANON(CONJUNCT1(syneq_exp_mono_V))) >>
    HINT_EXISTS_TAC >>
    simp[O_DEF] >>
    srw_tac[DNF_ss,ARITH_ss][] >>
    metis_tac[]) >>
  strip_tac >- (
    rw[] >> pop_assum mp_tac >>
    simp[Once syneq_exp_cases] >> strip_tac >>
    simp[Once syneq_exp_cases] >>
    res_tac >>
    HINT_EXISTS_TAC >> simp[] >>
    match_mp_tac (MP_CANON(CONJUNCT1(syneq_exp_mono_V))) >>
    HINT_EXISTS_TAC >>
    simp[O_DEF] >>
    srw_tac[DNF_ss,ARITH_ss][] >>
    fsrw_tac[ARITH_ss][] >>
    metis_tac[]) >>
  strip_tac >- (
    rw[] >> pop_assum mp_tac >>
    simp[Once syneq_exp_cases] >> strip_tac >>
    simp[Once syneq_exp_cases] >>
    res_tac >>
    HINT_EXISTS_TAC >>
    simp[O_DEF] >>
    metis_tac[]) >>
  strip_tac >- (
    rw[] >> pop_assum mp_tac >>
    simp[Once syneq_exp_cases] >> strip_tac >>
    simp[Once syneq_exp_cases] >>
    fs[EVERY2_EVERY,EVERY_MEM,MEM_ZIP] >> rw[] >>
    rpt (qpat_assum` LENGTH X = LENGTH Y` mp_tac) >>
    rpt strip_tac >>
    fs[MEM_ZIP,FORALL_PROD] >>
    PROVE_TAC[syneq_exp_refl] ) >>
  strip_tac >- (
    rw[] >> pop_assum mp_tac >>
    simp[Once syneq_exp_cases] >> strip_tac >>
    simp[Once syneq_exp_cases] >>
    metis_tac[syneq_exp_refl]) >>
  strip_tac >- (
    rw[] >> pop_assum mp_tac >>
    simp[Once syneq_exp_cases] >> strip_tac >>
    simp[Once syneq_exp_cases] >>
    metis_tac[syneq_exp_refl]) >>
  strip_tac >- (
    rw[] >> pop_assum mp_tac >>
    simp[Once syneq_exp_cases] >> strip_tac >>
    simp[Once syneq_exp_cases] >>
    metis_tac[syneq_exp_refl]) >>
  strip_tac >- (
    rw[] >> pop_assum mp_tac >>
    simp[Once syneq_exp_cases] >> strip_tac >>
    simp[Once syneq_exp_cases] >>
    metis_tac[syneq_exp_refl]) >>
  strip_tac >- (
    rw[] >>
    pop_assum mp_tac >>
    simp[Once syneq_exp_cases] >>
    fsrw_tac[DNF_ss][] >>
    reverse conj_asm1_tac >- (
      rw[] >>
      first_x_assum match_mp_tac >>
      rw[] >> res_tac >> rw[] >>
      Q.PAT_ABBREV_TAC`p = syneq_cb_aux X Y Z ez2 A` >>
      PairCases_on`p` >> simp[] >>
      match_mp_tac syneq_exp_refl >>
      rw[] >>
      match_mp_tac syneq_cb_V_refl >>
      qpat_assum`Abbrev X` mp_tac >>
      Cases_on`EL n1 d2`>>
      TRY(PairCases_on`x`)>>
      simp[syneq_cb_aux_def,UNCURRY,markerTheory.Abbrev_def] >>
      srw_tac[ARITH_ss][] ) >>
    strip_tac >>
    simp[Once syneq_exp_cases] >>
    fsrw_tac[DNF_ss][O_DEF] >>
    disj1_tac >>
    rw[] >> TRY (res_tac >> NO_TAC) >>
    qmatch_assum_rename_tac`U' n0 n3`[] >>
    qmatch_assum_rename_tac`U' n2 n3`[] >>
    ntac 3 (last_x_assum(qspecl_then[`n1`,`n2`]mp_tac)) >> rw[] >>
    ntac 3 (last_x_assum(qspecl_then[`n2`,`n3`]mp_tac)) >> rw[] >>
    rpt (qpat_assum`A = B`(mp_tac o SYM)) >>
    rw[] >>
    first_x_assum(qspecl_then[`c3`,`az+j2'`,`syneq_cb_V az r1' r2' V' U'`,`e2'`]mp_tac) >>
    rw[] >>
    match_mp_tac (MP_CANON(CONJUNCT1 (syneq_exp_mono_V))) >>
    HINT_EXISTS_TAC >>
    simp[syneq_cb_V_def,O_DEF] >>
    srw_tac[ARITH_ss][] >>
    fsrw_tac[ARITH_ss][] >> rw[] >>
    metis_tac[] ) >>
  rw[] >> pop_assum mp_tac >>
  simp[Once syneq_exp_cases] >>
  fsrw_tac[DNF_ss][] >>
  reverse conj_asm1_tac >- (
    rw[] >>
    first_x_assum match_mp_tac >>
    rw[] >>
    Q.PAT_ABBREV_TAC`p = syneq_cb_aux X Y Z ez1 A` >>
    PairCases_on`p` >> simp[] >>
    match_mp_tac syneq_exp_refl >>
    rw[] >>
    match_mp_tac syneq_cb_V_refl >>
    qpat_assum`Abbrev X` mp_tac >>
    Cases_on`EL n1 d1`>>
    TRY(PairCases_on`x`)>>
    simp[syneq_cb_aux_def,UNCURRY,markerTheory.Abbrev_def] >>
    srw_tac[ARITH_ss][] ) >>
  strip_tac >>
  simp[Once syneq_exp_cases] >>
  fsrw_tac[DNF_ss][O_DEF] >>
  disj1_tac >>
  rw[] >> TRY (res_tac >> NO_TAC) >>
  first_x_assum(qspecl_then[`n1`,`n2`]mp_tac) >> rw[] >>
  rpt (qpat_assum`A = B`(mp_tac o SYM)) >>
  rw[] >>
  match_mp_tac (MP_CANON(CONJUNCT1 (syneq_exp_mono_V))) >>
  HINT_EXISTS_TAC >>
  simp[syneq_cb_V_def,O_DEF] >>
  srw_tac[ARITH_ss][] >>
  fsrw_tac[ARITH_ss][] >> rw[] >>
  TRY (metis_tac[] ) >>
  qsuff_tac`j1' < ez1`>-metis_tac[] >>
  metis_tac[syneq_cb_aux_lemma])

val syneq_trans = store_thm("syneq_trans",
  ``∀c1 c2 x y. syneq c1 c2 x y ⇒ ∀c3 z. syneq c2 c3 y z ⇒ syneq c1 c3 x z``,
  ho_match_mp_tac syneq_ind >> rw[] >- (
    rw[] >> pop_assum mp_tac >>
    simp[Once syneq_cases] >> strip_tac >>
    simp[Once syneq_cases] >>
    fs[EVERY2_EVERY,EVERY_MEM,MEM_ZIP] >> rw[] >>
    rpt (qpat_assum` LENGTH X = LENGTH Y` mp_tac) >>
    rpt strip_tac >>
    fs[MEM_ZIP,FORALL_PROD] >>
    PROVE_TAC[syneq_refl] ) >>
  rw[] >> pop_assum mp_tac >>
  simp[Once syneq_cases] >> strip_tac >>
  simp[Once syneq_cases] >> rw[] >>
  qexists_tac`V'' O V` >>
  qexists_tac`V''' O V'` >>
  simp[O_DEF] >> (
  conj_tac >- PROVE_TAC[syneq_exp_trans] ) >>
  TRY conj_tac >>
  TRY (PROVE_TAC[syneq_exp_trans]))

val result_rel_syneq_refl = save_thm(
"result_rel_syneq_refl",
result_rel_refl
|> Q.GEN`R`
|> Q.ISPEC`syneq c c`
|> SIMP_RULE std_ss [syneq_refl])
val _ = export_rewrites["result_rel_syneq_refl"]

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

(* TODO: move *)
val EVERY2_trans = store_thm("EVERY2_trans",
  ``(!x y z. R x y /\ R y z ==> R x z) ==>
    !x y z. EVERY2 R x y /\ EVERY2 R y z ==> EVERY2 R x z``,
  SRW_TAC[][EVERY2_EVERY,EVERY_MEM,FORALL_PROD] THEN
  REPEAT (Q.PAT_ASSUM`LENGTH X = Y`MP_TAC) THEN
  REPEAT STRIP_TAC THEN
  FULL_SIMP_TAC (srw_ss()++DNF_ss) [MEM_ZIP] THEN
  METIS_TAC[])

val EVERY2_sym = store_thm("EVERY2_sym",
  ``(!x y. R1 x y ==> R2 y x) ==> !x y. EVERY2 R1 x y ==> EVERY2 R2 y x``,
  SRW_TAC[][EVERY2_EVERY,EVERY_MEM,FORALL_PROD] THEN
  (Q.PAT_ASSUM`LENGTH X = Y`MP_TAC) THEN
  STRIP_TAC THEN
  FULL_SIMP_TAC (srw_ss()++DNF_ss) [MEM_ZIP])

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

val EVERY2_refl = store_thm("EVERY2_refl",
  ``(!x. MEM x ls ==> R x x) ==> (EVERY2 R ls ls)``,
  Induct_on`ls` >>rw[])

val EVERY2_syneq_refl = save_thm("EVERY2_syneq_refl",
EVERY2_refl
|> Q.GEN`R`
|> Q.ISPEC`syneq c c`
|> SIMP_RULE std_ss [syneq_refl])
val _ = export_rewrites["EVERY2_syneq_refl"]

val EVERY2_syneq_exp_refl = store_thm("EVERY2_syneq_exp_refl",
  ``(!x. x < z ⇒ V x x) ⇒ EVERY2 (syneq_exp c c z z V) ls ls``,
  strip_tac >>
  match_mp_tac EVERY2_refl >>
  rpt strip_tac >>
  match_mp_tac syneq_exp_refl >>
  first_assum ACCEPT_TAC)

val EVERY2_syneq_trans = save_thm(
"EVERY2_syneq_trans",
EVERY2_trans
|> Q.GEN`R`
|> Q.ISPEC`syneq c c`
|> SIMP_RULE std_ss [GSYM AND_IMP_INTRO]
|> UNDISCH
|> (fn th => PROVE_HYP (PROVE[syneq_trans](hd(hyp th))) th)
|> SIMP_RULE std_ss [AND_IMP_INTRO])

val EVERY2_syneq_sym = save_thm(
"EVERY2_syneq_sym",
EVERY2_sym
|> Q.GENL[`R2`,`R1`]
|> Q.ISPECL[`syneq c1 c2`,`syneq c2 c1`]
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

val Cevaluate_Clocs = store_thm("Cevaluate_Clocs",
  ``(∀c s env exp res. Cevaluate c s env exp res ⇒
     BIGUNION (IMAGE all_Clocs (set env)) ⊆ count (LENGTH s) ∧
     BIGUNION (IMAGE all_Clocs (set s)) ⊆ count (LENGTH s)
     ⇒
     BIGUNION (IMAGE all_Clocs (set (FST res))) ⊆ count (LENGTH (FST res)) ∧
     ∀v. (SND res = Rval v) ⇒ all_Clocs v ⊆ count (LENGTH (FST res))) ∧
    (∀c s env exps res. Cevaluate_list c s env exps res ⇒
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
    fsrw_tac[DNF_ss][MEM_MAP,IN_FRANGE,UNCURRY] >>
    rfs[] >>
    imp_res_tac Cevaluate_store_SUBSET >>
    fsrw_tac[ARITH_ss][] >>
    reverse conj_tac >- metis_tac[LESS_LESS_EQ_TRANS] >>
    conj_tac >- metis_tac[LESS_LESS_EQ_TRANS] >>
    fsrw_tac[DNF_ss][EVERY_MEM,MEM_EL] >>
    metis_tac[LESS_LESS_EQ_TRANS]) >>
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

val CevalPrim2_syneq_equal = store_thm(
"CevalPrim2_syneq_equal",
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
val EVERY2_RC_same = store_thm("EVERY2_RC_same",
  ``EVERY2 (RC R) l l``,
  srw_tac[DNF_ss][EVERY2_EVERY,EVERY_MEM,MEM_ZIP,relationTheory.RC_DEF])
val _ = export_rewrites["EVERY2_RC_same"]
val syneq_strongind = CompileTheory.syneq_strongind

val CevalPrim2_syneq = store_thm("CevalPrim2_syneq",
  ``∀c1 c2 p2 v11 v21 v12 v22.
    syneq c1 c2 v11 v12 ∧ syneq c1 c2 v21 v22 ⇒
    result_rel (syneq c1 c2) (CevalPrim2 p2 v11 v21) (CevalPrim2 p2 v12 v22)``,
  ntac 2 gen_tac >>
  Cases >> simp[] >>
  Cases >> Cases >>
  simp[] >>
  TRY ( simp[Once syneq_cases] >> fsrw_tac[DNF_ss][] >> NO_TAC) >>
  TRY ( simp[Once syneq_cases] >> simp[Once syneq_cases,SimpR``$/\``] >> fsrw_tac[DNF_ss][] >> NO_TAC) >>
  TRY (Cases_on`l` >> Cases_on`l'` >> simp[] >> fsrw_tac[DNF_ss][i0_def] >> rw[] >> NO_TAC) >>
  TRY ( rw[] >> NO_TAC ) >>
  TRY (
    rw[] >>
    spose_not_then strip_assume_tac >>
    imp_res_tac syneq_no_closures >>
    fs[Once syneq_cases] >> rw[] >>
    metis_tac[NOT_EVERY] ) >>
  simp[Once syneq_cases] >>
  simp[Once syneq_cases] >>
  rpt strip_tac >>
  srw_tac[ETA_ss][] >>
  fsrw_tac[DNF_ss][EVERY_MEM,EVERY2_EVERY,FORALL_PROD,EXISTS_MEM] >>
  rfs[MEM_ZIP] >>
  fsrw_tac[DNF_ss][MEM_EL] >>
  metis_tac[no_closures_syneq_equal,syneq_no_closures,LIST_EQ_REWRITE])

val CevalPrim1_syneq = store_thm("CevalPrim1_syneq",
  ``∀c1 c2 uop s1 s2 v1 v2. EVERY2 (syneq c1 c2) s1 s2 ∧ syneq c1 c2 v1 v2 ⇒
    EVERY2 (syneq c1 c2) (FST (CevalPrim1 uop s1 v1)) (FST (CevalPrim1 uop s2 v2)) ∧
    result_rel (syneq c1 c2) (SND (CevalPrim1 uop s1 v1)) (SND (CevalPrim1 uop s2 v2))``,
  ntac 2 gen_tac >>
  Cases >- (
    simp[] >> rw[] >> fs[EVERY2_EVERY] >> lrw[GSYM ZIP_APPEND] ) >>
  ntac 2 gen_tac >>
  Cases >> simp[Once syneq_cases] >>
  fsrw_tac[DNF_ss][] >>
  rw[el_check_def,EVERY2_EVERY] >>
  rfs[EVERY_MEM,MEM_ZIP,FORALL_PROD] >>
  fsrw_tac[DNF_ss][])

val CevalUpd_syneq = store_thm(
"CevalUpd_syneq",
``∀c1 c2 s1 v1 v2 s2 w1 w2.
  syneq c1 c2 v1 w1 ∧ syneq c1 c2 v2 w2 ∧ EVERY2 (syneq c1 c2) s1 s2 ⇒
  EVERY2 (syneq c1 c2) (FST (CevalUpd s1 v1 v2)) (FST (CevalUpd s2 w1 w2)) ∧
  result_rel (syneq c1 c2) (SND (CevalUpd s1 v1 v2)) (SND (CevalUpd s2 w1 w2))``,
  ntac 3 gen_tac >>
  Cases >> simp[] >>
  ntac 2 gen_tac >>
  Cases >> simp[] >>
  rw[] >> TRY (
    match_mp_tac EVERY2_LUPDATE_same >>
    rw[] ) >>
  PROVE_TAC[EVERY2_EVERY])

val Cevaluate_syneq = store_thm("Cevaluate_syneq",
  ``(∀c1 s1 env1 exp1 res1. Cevaluate c1 s1 env1 exp1 res1 ⇒
      ∀c2 ez1 ez2 V s2 env2 exp2 res2.
        syneq_exp c1 c2 (LENGTH env1) (LENGTH env2) V exp1 exp2
      ∧ (∀v1 v2. V v1 v2 ∧ v1 < LENGTH env1 ∧ v2 < LENGTH env2 ⇒ syneq c1 c2 (EL v1 env1) (EL v2 env2))
      ∧ EVERY2 (syneq c1 c2) s1 s2
      ⇒ ∃res2.
        Cevaluate c2 s2 env2 exp2 res2 ∧
        EVERY2 (syneq c1 c2) (FST res1) (FST res2) ∧
        result_rel (syneq c1 c2) (SND res1) (SND res2)) ∧
    (∀c1 s1 env1 es1 res1. Cevaluate_list c1 s1 env1 es1 res1 ⇒
      ∀c2 ez1 ez2 V s2 env2 es2 res2.
        EVERY2 (syneq_exp c1 c2 (LENGTH env1) (LENGTH env2) V) es1 es2
      ∧ (∀v1 v2. V v1 v2 ∧ v1 < LENGTH env1 ∧ v2 < LENGTH env2 ⇒ syneq c1 c2 (EL v1 env1) (EL v2 env2))
      ∧ EVERY2 (syneq c1 c2) s1 s2
      ⇒ ∃res2.
        Cevaluate_list c2 s2 env2 es2 res2 ∧
        EVERY2 (syneq c1 c2) (FST res1) (FST res2) ∧
        result_rel (EVERY2 (syneq c1 c2)) (SND res1) (SND res2))``,
  ho_match_mp_tac Cevaluate_strongind >>
  strip_tac >- ( simp[Once syneq_exp_cases] >> rw[] >> rw[] ) >>
  strip_tac >- (
    rw[] >>
    rator_x_assum`syneq_exp`mp_tac >>
    simp[Once (syneq_exp_cases)] >>
    fsrw_tac[DNF_ss][] >>
    map_every qx_gen_tac[`e`,`b`] >>
    rw[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][] >>
    first_x_assum(qspecl_then[`c2`,`V`,`s2'`,`env2`,`e`]mp_tac) >>
    simp[EXISTS_PROD] >> metis_tac[] ) >>
  strip_tac >- (
    rw[] >>
    rator_x_assum`syneq_exp`mp_tac >>
    simp[Once (syneq_exp_cases)] >>
    fsrw_tac[DNF_ss][] >>
    map_every qx_gen_tac[`e`,`b`] >>
    rw[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][] >>
    disj2_tac >> disj1_tac >>
    last_x_assum(qspecl_then[`c2`,`V`,`s2`,`env2`,`e`]mp_tac) >>
    simp[EXISTS_PROD] >> fsrw_tac[DNF_ss][] >>
    qx_gen_tac`s3` >> strip_tac >>
    qmatch_assum_abbrev_tac`syneq_exp c1 c2 (k1+1) (k2+1) V' e' b` >>
    first_x_assum(qspecl_then[`c2`,`V'`,`s3`,`CLitv (IntLit n)::env2`,`b`]mp_tac) >>
    simp[Abbr`V'`,ADD1] >>
    fsrw_tac[DNF_ss,ARITH_ss][] >>
    qmatch_abbrev_tac`(p ⇒ q) ⇒ r` >>
    `p` by (
      map_every qunabbrev_tac[`p`,`q`,`r`] >>
      rpt conj_tac >> Cases >> simp[] >>
      Cases >> simp[ADD1] >> PROVE_TAC[] ) >>
    simp[] >>
    map_every qunabbrev_tac[`p`,`q`,`r`] >>
    simp[EXISTS_PROD] >>
    metis_tac[] ) >>
  strip_tac >- (
    rw[] >>
    rator_x_assum`syneq_exp`mp_tac >>
    simp[Once (syneq_exp_cases)] >>
    fsrw_tac[DNF_ss][] >>
    map_every qx_gen_tac[`e`,`b`] >>
    rw[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][] >>
    disj2_tac >>
    first_x_assum(qspecl_then[`c2`,`V`,`s2'`,`env2`,`e`]mp_tac) >>
    simp[EXISTS_PROD] >> metis_tac[] ) >>
  strip_tac >- (
    rw[] >>
    rator_x_assum`syneq_exp`mp_tac >>
    simp[Once (syneq_exp_cases)] >>
    rw[] >> simp[] >> metis_tac[syneq_exp_refl]) >>
  strip_tac >- (
    simp[Once syneq_exp_cases] >>
    rw[] >> rw[] ) >>
  strip_tac >- (
    rw[] >>
    rator_x_assum`syneq_exp`mp_tac >>
    simp[Once (syneq_exp_cases)] >>
    fsrw_tac[DNF_ss][] >>
    qx_gen_tac`es2` >>
    strip_tac >>
    simp[Once syneq_cases] >>
    simp[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][] >>
    fsrw_tac[DNF_ss][EXISTS_PROD] >>
    first_x_assum match_mp_tac >>
    metis_tac[]) >>
  strip_tac >- (
    rw[] >>
    rator_x_assum`syneq_exp`mp_tac >>
    simp[Once (syneq_exp_cases)] >>
    fsrw_tac[DNF_ss][] >>
    rw[] >>
    simp[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][EXISTS_PROD] >>
    first_x_assum match_mp_tac >>
    TRY (metis_tac[]) >>
    qexists_tac`$=` >> simp[] >>
    simp[EVERY2_EVERY,EVERY_MEM,MEM_ZIP,FORALL_PROD] >>
    rw[] >> rw[syneq_exp_refl] ) >>
  strip_tac >- (
    rw[] >>
    rator_x_assum`syneq_exp`mp_tac >>
    simp[Once (syneq_exp_cases)] >>
    fsrw_tac[DNF_ss][] >>
    qx_gen_tac`e2` >> rw[] >>
    simp[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][EXISTS_PROD] >>
    first_x_assum(qspecl_then[`c2`,`V`,`s2`,`env2`,`e2`]mp_tac) >>
    simp[Once(syneq_cases)] >>
    fsrw_tac[DNF_ss][] >>
    metis_tac[]) >>
  strip_tac >- (
    rw[] >>
    rator_x_assum`syneq_exp`mp_tac >>
    simp[Once (syneq_exp_cases)] >>
    fsrw_tac[DNF_ss][] >>
    simp[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][EXISTS_PROD] >>
    rw[] >- (
      first_x_assum match_mp_tac >>
      metis_tac[syneq_exp_refl] ) >>
    simp[Once Cevaluate_cases] >>
    first_x_assum match_mp_tac >>
    metis_tac[syneq_exp_refl] ) >>
  strip_tac >- (
    rw[] >>
    rator_x_assum`syneq_exp`mp_tac >>
    simp[Once (syneq_exp_cases)] >>
    fsrw_tac[DNF_ss][] >>
    simp[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][EXISTS_PROD] >>
    qx_gen_tac`e2` >> rw[] >>
    first_x_assum(qspecl_then[`c2`,`V`,`s2`,`env2`,`e2`]mp_tac) >>
    simp[Once (syneq_cases)] >>
    rw[] >>
    fsrw_tac[DNF_ss][EVERY2_EVERY,EVERY_MEM,FORALL_PROD] >>
    metis_tac[syneq_refl,MEM_ZIP]) >>
  strip_tac >- (
    rw[] >>
    rator_x_assum`syneq_exp`mp_tac >>
    simp[Once (syneq_exp_cases)] >>
    fsrw_tac[DNF_ss][] >>
    simp[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][EXISTS_PROD] >>
    metis_tac[syneq_exp_refl] ) >>
  strip_tac >- (
    rw[] >>
    rator_x_assum`syneq_exp`mp_tac >>
    simp[Once (syneq_exp_cases)] >>
    fsrw_tac[DNF_ss][] >>
    map_every qx_gen_tac[`e`,`b`] >>
    rw[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][] >>
    disj1_tac >>
    last_x_assum(qspecl_then[`c2`,`V`,`s2`,`env2`,`e`]mp_tac) >>
    simp[EXISTS_PROD] >> fsrw_tac[DNF_ss][] >>
    map_every qx_gen_tac[`s3`,`v3`] >> strip_tac >>
    qmatch_assum_abbrev_tac`syneq_exp c1 c2 (k1+1) (k2+1) V' e' b` >>
    first_x_assum(qspecl_then[`c2`,`V'`,`s3`,`v3::env2`,`b`]mp_tac) >>
    simp[Abbr`V'`,ADD1] >>
    fsrw_tac[DNF_ss,ARITH_ss][] >>
    qmatch_abbrev_tac`(p ⇒ q) ⇒ r` >>
    `p` by (
      map_every qunabbrev_tac[`p`,`q`,`r`] >>
      rpt conj_tac >> Cases >> simp[] >>
      Cases >> simp[ADD1] >> PROVE_TAC[] ) >>
    simp[] >>
    map_every qunabbrev_tac[`p`,`q`,`r`] >>
    simp[EXISTS_PROD] >>
    metis_tac[] ) >>
  strip_tac >- (
    rw[] >>
    rator_x_assum`syneq_exp`mp_tac >>
    simp[Once (syneq_exp_cases)] >>
    fsrw_tac[DNF_ss][] >>
    simp[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][] >- (
      rw[] >> disj2_tac >>
      fsrw_tac[DNF_ss][EXISTS_PROD] >>
      first_x_assum match_mp_tac >>
      metis_tac[syneq_exp_refl] ) >>
    map_every qx_gen_tac[`e2`,`b2`] >>
    rw[] >> fsrw_tac[DNF_ss][] >>
    first_x_assum(qspecl_then[`c2`,`V`,`s2`,`env2`,`e2`]mp_tac) >>
    simp[EXISTS_PROD] >> metis_tac[] ) >>
  strip_tac >- (
    rw[] >>
    rator_x_assum`syneq_exp`mp_tac >>
    simp[Once (syneq_exp_cases)] >>
    fsrw_tac[DNF_ss][] >>
    map_every qx_gen_tac[`defs2`,`b2`,`U`] >>
    strip_tac >>
    simp[Once Cevaluate_cases] >>
    simp[GSYM CONJ_ASSOC] >>
    simp[RIGHT_EXISTS_AND_THM] >>
    conj_tac >- (
      rator_x_assum`syneq_defs`mp_tac >>
      simp[Once syneq_exp_cases] >>
      fsrw_tac[DNF_ss][] ) >>
    first_x_assum match_mp_tac >>
    simp[] >> rfs[] >>
    simp[ADD_SYM] >>
    HINT_EXISTS_TAC >>
    simp[] >>
    rw[] >>
    lrw[EL_APPEND1,EL_APPEND2,REVERSE_GENLIST,EL_GENLIST] >>
    simp[Once syneq_cases] >>
    qexists_tac`λv1 v2. V v1 v2 ∧ v1 < LENGTH env1 ∧ v2 < LENGTH env2` >> rw[] >>
    qexists_tac`U` >> simp[PRE_SUB1] >>
    match_mp_tac (MP_CANON (CONJUNCT2 (syneq_exp_mono_V))) >>
    qexists_tac`V` >> simp[]) >>
  strip_tac >- (
    rw[] >>
    rator_x_assum`syneq_exp`mp_tac >>
    simp[Once (syneq_exp_cases)] >>
    rw[] >> simp[] >>
    simp[Once syneq_cases] >>
    conj_tac >- (
      rator_x_assum`syneq_defs`mp_tac >>
      simp[Once syneq_exp_cases] >>
      fsrw_tac[DNF_ss][] ) >>
    qexists_tac`λv1 v2. v1 < LENGTH env1 ∧ v2 < LENGTH env2 ∧ V v1 v2`>>rw[]>>
    qexists_tac`V'` >> simp[] >>
    match_mp_tac(MP_CANON(CONJUNCT2(syneq_exp_mono_V))) >>
    metis_tac[] ) >>
  strip_tac >- (
    rw[] >>
    rator_x_assum`syneq_exp`mp_tac >>
    simp[Once (syneq_exp_cases)] >>
    fsrw_tac[DNF_ss][] >>
    map_every qx_gen_tac[`e2`,`es2`] >>
    strip_tac >>
    simp[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][] >>
    disj1_tac >>
    last_x_assum(qspecl_then[`c2`,`V`,`s2`,`env2`,`e2`]mp_tac) >>
    simp[GSYM AND_IMP_INTRO] >> disch_then(mp_tac o UNDISCH_ALL) >>
    simp[EXISTS_PROD] >>
    simp[Once syneq_cases] >>
    simp_tac(std_ss++DNF_ss)[] >>
    map_every qx_gen_tac[`s2'`,`V'`,`cenv2`,`defs2`,`d2`,`U`] >>
    strip_tac >> qmatch_assum_rename_tac`U d1 d2`[] >>
    CONV_TAC(RESORT_EXISTS_CONV (fn ls => (List.drop(ls,2)@List.take(ls,2)))) >>
    map_every qexists_tac[`s2'`,`cenv2`,`defs2`,`d2`] >>
    simp[] >>
    first_x_assum(qspecl_then[`c2`,`V`,`s2'`,`env2`,`es2`]mp_tac) >>
    simp[] >>
    simp[GSYM AND_IMP_INTRO] >> disch_then(mp_tac o UNDISCH_ALL) >>
    simp[EXISTS_PROD] >>
    simp_tac(std_ss++DNF_ss)[] >>
    map_every qx_gen_tac[`s2''`,`vs2`] >>
    strip_tac >>
    CONV_TAC(RESORT_EXISTS_CONV (fn ls => (List.drop(ls,2)@List.take(ls,2)))) >>
    map_every qexists_tac[`s2''`,`vs2`] >>
    rator_assum`syneq_defs`mp_tac >>
    simp_tac std_ss [Once syneq_exp_cases] >>
    reverse strip_tac >- (
      fsrw_tac[][LET_THM] >>
      Cases_on`EL d1 defs`>>TRY(qmatch_assum_rename_tac`EL d1 defs = INL z`[]>>Cases_on`z`)>>
      fs[syneq_cb_aux_def,LET_THM,UNCURRY] >- (
        rw[] >> fs[EVERY2_EVERY] >>
        fsrw_tac[DNF_ss][EXISTS_PROD] >>
        first_x_assum match_mp_tac >>
        simp[] >>
        qexists_tac`$=` >>
        simp[syneq_exp_refl] >>
        rfs[EVERY_MEM,MEM_ZIP,FORALL_PROD] >>
        fsrw_tac[DNF_ss][] >>
        qx_gen_tac`v` >> strip_tac >>
        fs[]>>rfs[] >>
        Cases_on`v < LENGTH vs2`>>
        lrw[REVERSE_GENLIST,EL_APPEND1,EL_APPEND2,EL_REVERSE] >>
        Cases_on`v < LENGTH vs2 + LENGTH defs`>>
        lrw[EL_APPEND2,LENGTH_REVERSE,EL_APPEND1,LENGTH_GENLIST] >>
        simp[Once syneq_cases] >>
        qexists_tac`λv1 v2. v1 < LENGTH cenv ∧ v2 < LENGTH cenv ∧ V' v1 v2` >>
        qexists_tac`λv1 v2. v1 < LENGTH defs ∧ (v2 = v1)` >>
        simp[] >>
        match_mp_tac(MP_CANON(CONJUNCT2(syneq_exp_mono_V))) >>
        qexists_tac`V'` >>
        simp[] ) >>
      rw[] >> fs[EVERY2_EVERY] >>
      fsrw_tac[DNF_ss][EXISTS_PROD] >>
      first_x_assum match_mp_tac >>
      simp[] >>
      qexists_tac`$=` >>
      simp[syneq_exp_refl] >>
      rfs[EVERY_MEM,MEM_ZIP,FORALL_PROD] >>
      fsrw_tac[DNF_ss][] >>
      qx_gen_tac`v` >> strip_tac >>
      fs[]>>rfs[] >>
      Cases_on`v < LENGTH vs2`>>
      lrw[REVERSE_GENLIST,EL_APPEND1,EL_APPEND2,EL_REVERSE] >>
      Cases_on`v = LENGTH vs2`>>
      lrw[EL_APPEND2,LENGTH_REVERSE,EL_APPEND1,LENGTH_GENLIST] >- (
        simp[Once syneq_cases] >>
        qexists_tac`λv1 v2. v1 < (c1 ' y).ez ∧ v2 < (c1 ' y).ez ∧ V' v1 v2`>>simp[] >>
        qexists_tac`λv1 v2. v1 < (c1 ' y).nz ∧ (v2 = v1)` >>simp[] >>
        match_mp_tac(MP_CANON(CONJUNCT2(syneq_exp_mono_V))) >>
        qexists_tac`V'` >> simp[]) >>
      Cases_on`v < LENGTH vs2 + 1 + LENGTH (FST (c1 ' y).cd.ceenv)` >>
      lrw[EL_APPEND2,LENGTH_REVERSE,EL_APPEND1,LENGTH_GENLIST,EL_MAP] >- (
        simp[Once syneq_cases] >>
        qexists_tac`λv1 v2. v1 < (c1 ' y).ez ∧ v2 < (c1 ' y).ez ∧ V' v1 v2`>>simp[] >>
        qexists_tac`λv1 v2. v1 < (c1 ' y).nz ∧ (v2 = v1)` >>simp[] >>
        match_mp_tac(MP_CANON(CONJUNCT2(syneq_exp_mono_V))) >>
        qexists_tac`V'`>>simp[]) >>
      first_x_assum match_mp_tac >>
      first_x_assum match_mp_tac >>
      fsrw_tac[DNF_ss][MEM_EL] >>
      last_x_assum match_mp_tac >>
      simp[] ) >>
    pop_assum(qspecl_then[`d1`,`d2`]mp_tac) >>
    simp[] >>
    Cases_on`EL d2 defs2` >- (
      Cases_on`x`>> simp[syneq_cb_aux_def] >>
      Cases_on`EL d1 defs` >- (
        Cases_on`x`>>fs[syneq_cb_aux_def] >>
        simp[] >> fs[] >> rw[] >>
        `LENGTH vs2 = LENGTH vs` by fs[EVERY2_EVERY] >> fs[] >>
        fs[EXISTS_PROD] >>
        first_x_assum match_mp_tac >>
        fs[AC ADD_ASSOC ADD_SYM] >>
        rator_x_assum`syneq_exp`mp_tac >>
        Q.PAT_ABBREV_TAC`V2 = syneq_cb_V A B C D E` >>
        strip_tac >>
        qexists_tac`V2` >>
        simp[] >> rfs[] >>
        rpt gen_tac >>
        pop_assum kall_tac >>
        fs[EVERY2_EVERY,EVERY_MEM,FORALL_PROD] >>
        fsrw_tac[DNF_ss][MEM_ZIP] >>
        simp[Abbr`V2`,syneq_cb_V_def] >> rw[] >>
        TRY(`v1=v2` by (
          ntac 7 (pop_assum mp_tac) >>
          rpt (pop_assum kall_tac) >>
          ntac 4 strip_tac >>
          REWRITE_TAC[SUB_PLUS] >>
          simp[] >> NO_TAC ) >>
          qpat_assum`LENGTH defs2 - X = Y`kall_tac) >>
        lrw[EL_APPEND1,EL_APPEND2,EL_REVERSE,PRE_SUB1] >>
        TRY (first_x_assum match_mp_tac >> simp[] >> NO_TAC) >>
        simp[Once syneq_cases] >>
        map_every qexists_tac[`V'`,`U`] >>
        qpat_assum`U X Y`mp_tac >>
        fsrw_tac[DNF_ss,ARITH_ss][] >>
        metis_tac[] ) >>
      fs[syneq_cb_aux_def,LET_THM,UNCURRY] >>
      rw[] >>
      qpat_assum`LENGTH vs = X`(assume_tac o SYM) >>fs[] >>
      `LENGTH vs2 = LENGTH vs` by fs[EVERY2_EVERY] >> fs[] >>
      fs[EXISTS_PROD] >>
      first_x_assum match_mp_tac >>
      rator_x_assum`syneq_exp`mp_tac >>
      Q.PAT_ABBREV_TAC`V2 = syneq_cb_V A B C D E` >>
      strip_tac >>
      qexists_tac`V2` >>
      simp[] >> rfs[] >>
      fsrw_tac[ARITH_ss][] >>
      pop_assum kall_tac >>
      fs[EVERY2_EVERY,EVERY_MEM,FORALL_PROD] >>
      fsrw_tac[DNF_ss][MEM_ZIP] >>
      simp[Abbr`V2`,syneq_cb_V_def] >> rw[] >>
      lrw[EL_APPEND1,EL_APPEND2,EL_REVERSE,PRE_SUB1,EL_MAP] >>
      TRY (first_x_assum match_mp_tac >> simp[] >> NO_TAC) >- (
        `v1 = LENGTH vs` by fsrw_tac[ARITH_ss][] >> rw[] >>
        simp[Once syneq_cases] >>
        map_every qexists_tac[`V'`,`U`] >>
        qpat_assum`U X Y`mp_tac >>
        simp[] >> metis_tac[] ) >>
      simp[Once syneq_cases] >>
      map_every qexists_tac[`V'`,`U`] >>
      qpat_assum`U X Y`mp_tac >>
      simp[] >> metis_tac[] ) >>
    Cases_on`EL d1 defs` >- (
      Cases_on`x`>>fs[syneq_cb_aux_def,LET_THM,UNCURRY] >>
      rw[] >>
      qpat_assum`LENGTH vs = X`(assume_tac o SYM) >>fs[] >>
      `LENGTH vs2 = LENGTH vs` by fs[EVERY2_EVERY] >> fs[] >>
      fs[EXISTS_PROD] >>
      first_x_assum match_mp_tac >>
      rator_x_assum`syneq_exp`mp_tac >>
      qho_match_abbrev_tac`syneq_exp c1 c2 ez1 ez2 V2 ee1 ee2 ⇒ P` >>
      strip_tac >> simp[Abbr`P`] >>
      qexists_tac`V2` >>
      simp[Abbr`ez1`,Abbr`ez2`] >> rfs[] >>
      fsrw_tac[ARITH_ss][] >>
      pop_assum kall_tac >>
      fs[EVERY2_EVERY,EVERY_MEM,FORALL_PROD] >>
      fsrw_tac[DNF_ss][MEM_ZIP] >>
      simp[Abbr`V2`,syneq_cb_V_def] >> rw[] >>
      lrw[EL_APPEND1,EL_APPEND2,EL_REVERSE,PRE_SUB1,EL_MAP] >>
      TRY (first_x_assum match_mp_tac >> simp[] >> NO_TAC) >- (
        `v2 = LENGTH vs` by fsrw_tac[ARITH_ss][] >> rw[] >>
        simp[Once syneq_cases] >>
        map_every qexists_tac[`V'`,`U`] >>
        qpat_assum`U X Y`mp_tac >>
        simp[] >> metis_tac[] ) >>
      simp[Once syneq_cases] >>
      map_every qexists_tac[`V'`,`U`] >>
      qpat_assum`U X Y`mp_tac >>
      simp[] >> metis_tac[] ) >>
    fs[syneq_cb_aux_def,LET_THM,UNCURRY] >>
    rw[] >>
    qpat_assum`LENGTH vs = X`(assume_tac o SYM) >>fs[] >>
    `LENGTH vs2 = LENGTH vs` by fs[EVERY2_EVERY] >> fs[] >>
    fs[EXISTS_PROD] >>
    first_x_assum match_mp_tac >>
    rator_x_assum`syneq_exp`mp_tac >>
    qho_match_abbrev_tac`syneq_exp c1 c2 ez1 ez2 V2 ee1 ee2 ⇒ P` >>
    strip_tac >> simp[Abbr`P`] >>
    qexists_tac`V2` >>
    simp[Abbr`ez1`,Abbr`ez2`] >> rfs[] >>
    fsrw_tac[ARITH_ss][] >>
    pop_assum kall_tac >>
    fs[EVERY2_EVERY,EVERY_MEM,FORALL_PROD] >>
    fsrw_tac[DNF_ss][MEM_ZIP] >>
    `LENGTH vs = LENGTH vs2` by rw[] >>
    qpat_assum`LENGTH vs = Y.az`kall_tac >>
    qpat_assum`LENGTH vs2 = Y.az`(assume_tac o SYM) >>
    simp[Abbr`V2`,syneq_cb_V_def] >> rw[] >>
    lrw[EL_APPEND1,EL_APPEND2,EL_REVERSE,PRE_SUB1,EL_MAP] >>
    TRY (first_x_assum match_mp_tac >> simp[] >> NO_TAC) >>
    TRY (
      fsrw_tac[ARITH_ss,DNF_ss][MEM_EL] >>
      qmatch_assum_abbrev_tac`~(EL X ls < LENGTH Y)` >>
      `EL X ls < LENGTH Y` by (
        first_x_assum match_mp_tac >>
        simp[Abbr`X`] ) >>
      fs[] >> NO_TAC)
    >- (
      `v1 = LENGTH vs2` by fsrw_tac[ARITH_ss][] >> rw[] >>
      `v2 = LENGTH vs2` by fsrw_tac[ARITH_ss][] >> rw[] >>
      simp[Once syneq_cases] >>
      map_every qexists_tac[`V'`,`U`] >>
      simp[] >> metis_tac[] )
    >- (
      `v1 = LENGTH vs2` by fsrw_tac[ARITH_ss][] >> rw[] >>
      simp[Once syneq_cases] >>
      map_every qexists_tac[`V'`,`U`] >>
      simp[] >> metis_tac[] )
    >- (
      `v2 = LENGTH vs2` by fsrw_tac[ARITH_ss][] >> rw[] >>
      simp[Once syneq_cases] >>
      map_every qexists_tac[`V'`,`U`] >>
      simp[] >> metis_tac[] )
    >- (
      simp[Once syneq_cases] >>
      map_every qexists_tac[`V'`,`U`] >>
      simp[] >> metis_tac[] )) >>
  strip_tac >- (
    rw[] >>
    rator_x_assum`syneq_exp`mp_tac >>
    simp[Once (syneq_exp_cases)] >>
    fsrw_tac[DNF_ss][] >>
    map_every qx_gen_tac[`e2`,`es2`] >>
    rw[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][] >>
    disj2_tac >> disj1_tac >>
    last_x_assum(qspecl_then[`c2`,`V`,`s2`,`env2`,`e2`]mp_tac) >>
    simp[GSYM AND_IMP_INTRO] >>
    disch_then(mp_tac o UNDISCH_ALL) >>
    fsrw_tac[DNF_ss][EXISTS_PROD,FORALL_PROD] >>
    metis_tac[] ) >>
  strip_tac >- (
    rw[] >>
    rator_x_assum`syneq_exp`mp_tac >>
    simp[Once (syneq_exp_cases)] >>
    fsrw_tac[DNF_ss][] >>
    map_every qx_gen_tac[`e2`,`es2`] >>
    rw[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][] >>
    disj2_tac >> disj2_tac >>
    fsrw_tac[DNF_ss][EXISTS_PROD] >>
    metis_tac[]) >>
  strip_tac >- (
    rw[] >>
    rator_x_assum`syneq_exp`mp_tac >>
    simp[Once (syneq_exp_cases)] >>
    fsrw_tac[DNF_ss][] >>
    rw[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][] >>
    disj1_tac >>
    fsrw_tac[DNF_ss][EXISTS_PROD] >>
    metis_tac[CevalPrim1_syneq] ) >>
  strip_tac >- (
    rw[] >>
    rator_x_assum`syneq_exp`mp_tac >>
    simp[Once (syneq_exp_cases)] >>
    fsrw_tac[DNF_ss][] >>
    rw[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][] >>
    fsrw_tac[DNF_ss][EXISTS_PROD] >>
    metis_tac[] ) >>
  strip_tac >- (
    rw[] >>
    rator_x_assum`syneq_exp`mp_tac >>
    simp[Once (syneq_exp_cases)] >>
    fsrw_tac[DNF_ss][] >>
    rw[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][EXISTS_PROD] >>
    disj1_tac >>
    metis_tac[CevalPrim2_syneq] ) >>
  strip_tac >- (
    rw[] >>
    rator_x_assum`syneq_exp`mp_tac >>
    simp[Once (syneq_exp_cases)] >>
    fsrw_tac[DNF_ss][] >>
    rw[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][] >>
    fsrw_tac[DNF_ss][EXISTS_PROD] >>
    metis_tac[] ) >>
  strip_tac >- (
    rw[] >>
    rator_x_assum`syneq_exp`mp_tac >>
    simp[Once (syneq_exp_cases)] >>
    fsrw_tac[DNF_ss][] >>
    rw[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][] >>
    disj1_tac >>
    fsrw_tac[DNF_ss][EXISTS_PROD] >>
    metis_tac[CevalUpd_syneq] ) >>
  strip_tac >- (
    rw[] >>
    rator_x_assum`syneq_exp`mp_tac >>
    simp[Once (syneq_exp_cases)] >>
    fsrw_tac[DNF_ss][] >>
    rw[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][] >>
    fsrw_tac[DNF_ss][EXISTS_PROD] >>
    metis_tac[] ) >>
  strip_tac >- (
    rw[] >> (
    rator_x_assum`syneq_exp`mp_tac >>
    simp[Once (syneq_exp_cases)] >>
    fsrw_tac[DNF_ss][] >>
    rw[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][] >>
    fsrw_tac[DNF_ss][EXISTS_PROD] >>
    disj1_tac >>
    last_x_assum(qspecl_then[`c2`,`V`,`s2`,`env2`,`e12`]mp_tac) >>
    simp[GSYM AND_IMP_INTRO] >> disch_then(mp_tac o UNDISCH_ALL) >>
    rw[] >>
    qmatch_assum_abbrev_tac`Cevaluate c2 s2 env2 e12 (s3,Rval (CLitv (Bool b)))` >>
    CONV_TAC(RESORT_EXISTS_CONV List.rev) >>
    map_every qexists_tac[`b`,`s3`] >>
    simp[Abbr`b`] >>
    CONV_TAC SWAP_EXISTS_CONV >>
    first_x_assum match_mp_tac >>
    metis_tac[] )) >>
  strip_tac >- (
    rw[] >>
    rator_x_assum`syneq_exp`mp_tac >>
    simp[Once (syneq_exp_cases)] >>
    fsrw_tac[DNF_ss][] >>
    rw[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][EXISTS_PROD] >>
    disj2_tac >>
    first_x_assum match_mp_tac >>
    metis_tac[] ) >>
  strip_tac >- ( rw[] >> simp[Once Cevaluate_cases] ) >>
  strip_tac >- (
    rw[] >>
    simp[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][EXISTS_PROD] >>
    qmatch_assum_rename_tac`syneq_exp c1 c2 (LENGTH env1) (LENGTH env2) V e1 e2`[] >>
    last_x_assum(qspecl_then[`c2`,`V`,`s2`,`env2`,`e2`]mp_tac) >>
    simp[GSYM AND_IMP_INTRO] >> disch_then(mp_tac o UNDISCH_ALL) >>
    fsrw_tac[DNF_ss][] >>
    map_every qx_gen_tac[`s3`,`v3`] >>
    strip_tac >>
    CONV_TAC SWAP_EXISTS_CONV >> qexists_tac`s3` >>
    CONV_TAC SWAP_EXISTS_CONV >> qexists_tac`v3` >>
    simp[] >>
    first_x_assum match_mp_tac >>
    metis_tac[] ) >>
  strip_tac >- (
    rw[] >>
    simp[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][EXISTS_PROD] >>
    disj1_tac >>
    first_x_assum match_mp_tac >>
    metis_tac[] ) >>
  rw[] >>
  simp[Once Cevaluate_cases] >>
  fsrw_tac[DNF_ss][EXISTS_PROD] >>
  disj2_tac >>
  qmatch_assum_rename_tac`syneq_exp c1 c2 (LENGTH env1) (LENGTH env2) V e1 e2`[] >>
  last_x_assum(qspecl_then[`c2`,`V`,`s2`,`env2`,`e2`]mp_tac) >>
  simp[GSYM AND_IMP_INTRO] >> disch_then(mp_tac o UNDISCH_ALL) >>
  fsrw_tac[DNF_ss][] >>
  map_every qx_gen_tac[`s3`,`v3`] >>
  strip_tac >>
  CONV_TAC SWAP_EXISTS_CONV >> qexists_tac`s3` >>
  CONV_TAC SWAP_EXISTS_CONV >> qexists_tac`v3` >>
  simp[] >>
  first_x_assum match_mp_tac >>
  metis_tac[] )

(* Closed values *)

val (Cclosed_rules,Cclosed_ind,Cclosed_cases) = Hol_reln`
(Cclosed c (CLitv l)) ∧
(EVERY (Cclosed c) vs ⇒ Cclosed c (CConv cn vs)) ∧
((EVERY (Cclosed c) env) ∧
 n < LENGTH defs ∧
 (∀az b. MEM (INL (az,b)) defs ⇒
    ∀v. v ∈ free_vars b ⇒ v < az + LENGTH defs + LENGTH env) ∧
 (∀l. MEM (INR l) defs
   ⇒ l ∈ FDOM c
   ∧ ((c ' l).nz = LENGTH defs)
   ∧ ((c ' l).ez = LENGTH env)
   ∧ closed_cd (c ' l).cd)
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
     ⇒ free_vars exp ⊆ count (LENGTH env)
     ∧ FEVERY (closed_cd o closure_extra_data_cd o SND) c
     ∧ EVERY (Cclosed c) env
     ∧ EVERY (Cclosed c) s
     ⇒
     EVERY (Cclosed c) (FST res) ∧
     every_result (Cclosed c) (SND res)) ∧
    (∀c s env exps ress. Cevaluate_list c s env exps ress
     ⇒ BIGUNION (IMAGE free_vars (set exps)) ⊆ count (LENGTH env)
     ∧ FEVERY (closed_cd o closure_extra_data_cd o SND) c
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
    fsrw_tac[DNF_ss][EVERY_MEM,FEVERY_DEF] >>
    map_every qx_gen_tac[`az`,`b`,`v`] >>
    rw[] >>
    Cases_on`v<az`>>fsrw_tac[ARITH_ss][]>>
    rpt (first_x_assum(qspecl_then[`INL (az,b)`,`v-az`]mp_tac)) >>
    simp[] >> fsrw_tac[DNF_ss][] >>
    simp[GSYM FORALL_AND_THM,AND_IMP_INTRO] >>
    disch_then(qspec_then`v`mp_tac) >>
    simp[] >> fsrw_tac[ARITH_ss][] ) >>
  strip_tac >- (
    rw[] >>
    simp[Once Cclosed_cases] >>
    fsrw_tac[DNF_ss][SUBSET_DEF,PRE_SUB1] >>
    rw[] >> fsrw_tac[DNF_ss][FEVERY_DEF] >>
    Cases_on`v≤az`>>fsrw_tac[ARITH_ss][]) >>
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
      last_x_assum(qspecl_then[`x0`,`x1`]mp_tac) >>
      `MEM (INL (x0,x1)) defs` by (rw[MEM_EL] >> PROVE_TAC[]) >>
      fsrw_tac[ARITH_ss,DNF_ss][]) >>
    fsrw_tac[DNF_ss][UNCURRY,SUBSET_DEF] >>
    simp[EVERY_REVERSE,EVERY_MAP] >>
    fsrw_tac[DNF_ss][IN_FRANGE] >>
    fsrw_tac[DNF_ss][EVERY_MEM,FEVERY_DEF] >>
    fs[(Q.SPECL[`c`,`CRecClos cenv defs d`]Cclosed_cases)] >>
    qmatch_assum_rename_tac`EL n defs = INR z`[] >>
    reverse conj_tac >- (
      conj_tac >- metis_tac[] >>
      fsrw_tac[DNF_ss][EVERY_MEM,MEM_EL] ) >>
    fsrw_tac[DNF_ss,ARITH_ss][closed_cd_def,MEM_EL]) >>
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

(* mkshift *)

(* labels in an expression (but not recursively) *)
val free_labs_def0 = tDefine "free_labs"`
  (free_labs (CDecl xs) = {}) ∧
  (free_labs (CRaise er) = {}) ∧
  (free_labs (CHandle e1 e2) = free_labs e1 ∪ free_labs e2) ∧
  (free_labs (CVar x) = {}) ∧
  (free_labs (CLit li) = {}) ∧
  (free_labs (CCon cn es) = (BIGUNION (IMAGE (free_labs) (set es)))) ∧
  (free_labs (CTagEq e n) = (free_labs e)) ∧
  (free_labs (CProj e n) = (free_labs e)) ∧
  (free_labs (CLet e eb) = (free_labs e)∪(free_labs eb)) ∧
  (free_labs (CLetrec defs e) = (BIGUNION(IMAGE free_labs (IMAGE (SND o OUTL)(set(FILTER ISL defs)))))∪(IMAGE OUTR (set (FILTER ISR defs)))∪(free_labs e)) ∧
  (free_labs (CFun (INL (_,e))) = free_labs e) ∧
  (free_labs (CFun (INR l)) = {l}) ∧
  (free_labs (CCall e es) = BIGUNION (IMAGE (free_labs) (set (e::es)))) ∧
  (free_labs (CPrim1 _ e) = free_labs e) ∧
  (free_labs (CPrim2 op e1 e2) = (free_labs e1)∪(free_labs e2)) ∧
  (free_labs (CUpd e1 e2) = (free_labs e1)∪(free_labs e2)) ∧
  (free_labs (CIf e1 e2 e3) = (free_labs e1)∪(free_labs e2)∪(free_labs e3))`(
  WF_REL_TAC `measure Cexp_size` >>
  srw_tac[ARITH_ss][Cexp4_size_thm,Cexp1_size_thm,SUM_MAP_Cexp2_size_thm] >>
  Q.ISPEC_THEN `Cexp_size` imp_res_tac SUM_MAP_MEM_bound >>
  Q.ISPEC_THEN `pair_size SUC Cexp_size o OUTL` imp_res_tac SUM_MAP_MEM_bound >>
  fsrw_tac[ARITH_ss][] >>
  Cases_on`OUTL x`>>fsrw_tac[ARITH_ss][basicSizeTheory.pair_size_def])
val free_labs_def = save_thm("free_labs_def",SIMP_RULE(std_ss++ETA_ss)[GSYM IMAGE_COMPOSE]free_labs_def0)
val _ = Parse.overload_on("free_labs_defs",``λdefs. (BIGUNION(IMAGE (free_labs o SND o OUTL)(set (FILTER ISL defs)))) ∪ IMAGE OUTR (set (FILTER ISR defs))``)
val _ = Parse.overload_on("free_labs_list",``λes. BIGUNION (IMAGE free_labs (set es))``)
val _ = export_rewrites["free_labs_def"]

val mkshift_thm = store_thm("mkshift_thm",
 ``∀f k e c z1 z2 V.
   k ≤ z1 ∧ k ≤ z2 ∧
   (∀x. x < k ⇒ V x x) ∧
   (∀x. k ≤ x ∧ x < z1 ⇒ V x (f(x-k)+k) ∧ (f(x-k)+k) < z2) ∧
   free_vars e ⊆ count z1 ∧
   (free_labs e = {})
   ⇒ syneq_exp c c z1 z2 V e (mkshift f k e)``,
 ho_match_mp_tac mkshift_ind >>
 strip_tac >- (
   rw[SUBSET_DEF,MEM_MAP] >>
   rw[Once syneq_exp_cases] >>
   simp[EVERY2_EVERY,EVERY_MEM,FORALL_PROD,MEM_ZIP] >>
   rw[] >> simp[EL_MAP] >>
   fsrw_tac[DNF_ss][EXISTS_PROD,FORALL_PROD] >>
   Cases_on`EL n vs`>> fsrw_tac[DNF_ss,ARITH_ss][MEM_EL] >>
   rw[] >> fsrw_tac[ARITH_ss][] >>
   res_tac >> rfs[] >>
   fsrw_tac[ARITH_ss][] ) >>
 strip_tac >- rw[Once syneq_exp_cases] >>
 strip_tac >- (
   rw[] >>
   rw[Once syneq_exp_cases] >>
   first_x_assum match_mp_tac >>
   fsrw_tac[ARITH_ss,QUANT_INST_ss[num_qp]][SUBSET_DEF,PRE_SUB1,ADD1] >>
   conj_tac >> Cases >> fsrw_tac[ARITH_ss][ADD1] >> rw[] >>
   `k+ f (n - k) < z2` by metis_tac[] >>
   fsrw_tac[ARITH_ss][] ) >>
 strip_tac >- (
   rw[] >>
   rw[Once syneq_exp_cases] >>
   fsrw_tac[ARITH_ss][] ) >>
 strip_tac >- rw[Once syneq_exp_cases] >>
 strip_tac >- (
   rw[] >>
   rw[Once syneq_exp_cases] >>
   fsrw_tac[DNF_ss][FOLDL_UNION_BIGUNION,SUBSET_DEF,EVERY2_EVERY,EVERY_MEM,FORALL_PROD,MEM_ZIP] >>
   fsrw_tac[DNF_ss][EL_MAP,MEM_EL] >> rw[] >>
   first_x_assum (match_mp_tac o MP_CANON) >>
   fsrw_tac[ARITH_ss][] >>
   fsrw_tac[DNF_ss][IMAGE_EQ_SING,MEM_EL] >>
   metis_tac[]) >>
 strip_tac >- ( rw[] >> rw[Once syneq_exp_cases] ) >>
 strip_tac >- ( rw[] >> rw[Once syneq_exp_cases] ) >>
 strip_tac >- (
   rw[] >>
   rw[Once syneq_exp_cases] >>
   first_x_assum match_mp_tac >>
   fsrw_tac[ARITH_ss,QUANT_INST_ss[num_qp]][SUBSET_DEF,PRE_SUB1,ADD1] >>
   conj_tac >> Cases >> fsrw_tac[ARITH_ss][ADD1] >> rw[] >>
   `k+ f (n - k) < z2` by metis_tac[] >>
   fsrw_tac[ARITH_ss][] ) >>
 strip_tac >- (
   simp[FOLDL_UNION_BIGUNION] >> rw[] >- (
     `defs=[]` by (
       fs[FILTER_EQ_NIL,EVERY_MEM] >>
       Cases_on`defs`>>fs[] >>
       rpt(first_x_assum(qspec_then`h`mp_tac)) >>
       Cases_on`h`>>rw[] ) >>
     fs[] >>
     rw[Once syneq_exp_cases] >>
     qexists_tac`λv1 v2. F` >>
     simp[Once syneq_exp_cases] ) >>
   rw[Once syneq_exp_cases] >>
   qexists_tac`λv1 v2. v1 < LENGTH defs ∧ (v2 = v1)` >>
   simp[] >>
   reverse conj_tac >- (
     first_x_assum match_mp_tac >>
     simp[] >>
     conj_tac >- (
       srw_tac[ARITH_ss][] >>
       Cases_on`x < LENGTH defs`>>fsrw_tac[ARITH_ss][] ) >>
     conj_tac >- (
       gen_tac >> strip_tac >>
       first_x_assum(qspec_then`x-LENGTH defs`mp_tac) >>
       simp[] ) >>
     fsrw_tac[ARITH_ss,DNF_ss][SUBSET_DEF] >>
     qx_gen_tac`x` >> strip_tac >>
     rpt(first_x_assum(qspec_then`x`mp_tac)) >>
     simp[] ) >>
   simp[Once syneq_exp_cases] >>
   disj1_tac >>
   conj_tac >- (
     fs[FILTER_EQ_NIL] >>
     fs[EVERY_MEM,MEM_MAP] >>
     full_simp_tac(srw_ss()++QUANT_INST_ss[sum_qp])[] >>
     gen_tac >> disch_then(Q.X_CHOOSE_THEN`p`mp_tac) >>
     Cases_on`p`>>simp[] ) >>
   rw[EL_MAP] >>
   fs[IMAGE_EQ_SING,MEM_FILTER] >>
   fs[FILTER_EQ_NIL,MEM_EL,EVERY_MEM] >>
   first_x_assum(qspec_then`EL v2 defs`(mp_tac o SIMP_RULE(srw_ss()++DNF_ss)[])) >>
   disch_then(qspec_then`v2`mp_tac) >>
   Cases_on`EL v2 defs`>>rw[] >>
   qmatch_assum_rename_tac`EL v2 defs = INL p`[] >>
   PairCases_on`p`>>simp[syneq_cb_aux_def] >>
   fsrw_tac[DNF_ss][] >>
   first_x_assum(qspecl_then[`p0`,`p1`,`v2`]mp_tac) >>
   simp[] >>
   disch_then match_mp_tac >>
   simp[] >>
   conj_tac >- srw_tac[ARITH_ss][syneq_cb_V_def] >>
   reverse conj_tac >- (
     fsrw_tac[DNF_ss,ARITH_ss][SUBSET_DEF] >>
     conj_tac >- (
       qx_gen_tac`x` >> strip_tac >>
       first_x_assum(qspec_then`INL (p0,p1)`mp_tac) >>
       first_x_assum(qspec_then`INL (p0,p1)`mp_tac) >>
       `MEM (INL (p0,p1)) defs` by (rw[MEM_EL] >> PROVE_TAC[]) >>
       fsrw_tac[DNF_ss][] >> rw[] >>
       rpt(first_x_assum(qspec_then`x`mp_tac)) >>
       simp[] ) >>
     first_x_assum(qspec_then`v2`mp_tac) >>
     simp[] ) >>
   reverse conj_tac >- (
     srw_tac[ARITH_ss][] >>
     rw[AC ADD_ASSOC ADD_SYM] >>
     REWRITE_TAC[Once ADD_ASSOC] >>
     CONV_TAC(LAND_CONV(LAND_CONV(REWRITE_CONV[Once ADD_SYM]))) >>
     REWRITE_TAC[Once (GSYM ADD_ASSOC)] >>
     simp[] >>
     REWRITE_TAC[Once (ADD_ASSOC)] >>
     simp[] >>
     `x - (k + (p0 + LENGTH defs)) = (x - (p0 + LENGTH defs)) - k` by srw_tac[ARITH_ss][] >>
     pop_assum SUBST1_TAC >>
     first_x_assum match_mp_tac >>
     simp[] ) >>
   srw_tac[ARITH_ss][syneq_cb_V_def] >- (
     `x - (k + (p0 + LENGTH defs)) = (x - (p0 + LENGTH defs)) - k` by fsrw_tac[ARITH_ss][] >>
     pop_assum SUBST1_TAC >>
     first_x_assum match_mp_tac >>
     fsrw_tac[ARITH_ss][] ) >>
   spose_not_then strip_assume_tac >>
   qpat_assum`~(x < y)`mp_tac >> simp[] >>
   rw[AC ADD_ASSOC ADD_SYM] >>
   REWRITE_TAC[Once ADD_ASSOC] >>
   CONV_TAC(LAND_CONV(LAND_CONV(REWRITE_CONV[Once ADD_SYM]))) >>
   REWRITE_TAC[Once (GSYM ADD_ASSOC)] >>
   simp[] >>
   REWRITE_TAC[Once (ADD_ASSOC)] >>
   simp[] >>
   `x - (k + (p0 + LENGTH defs)) = (x - (p0 + LENGTH defs)) - k` by srw_tac[ARITH_ss][] >>
   pop_assum SUBST1_TAC >>
   first_x_assum match_mp_tac >>
   simp[] ) >>
 strip_tac >- (
   simp[] >> rw[] >>
   Cases_on`cb`>>fs[] >>
   PairCases_on`x`>>fs[] >>
   rw[Once syneq_exp_cases] >>
   qexists_tac`λv1 v2. (v1 = 0) ∧ (v2 = 0)` >>
   simp[] >>
   simp[Once syneq_exp_cases] >>
   disj1_tac >>
   simp[syneq_cb_aux_def] >>
   fsrw_tac[ARITH_ss][] >>
   first_x_assum match_mp_tac >>
   simp[] >>
   conj_tac >- srw_tac[ARITH_ss][syneq_cb_V_def] >>
   conj_tac >- (
     srw_tac[ARITH_ss][syneq_cb_V_def] >- (
       `x - (k + (x0 + 1)) = (x - (x0 + 1)) - k` by fsrw_tac[ARITH_ss][] >>
       pop_assum SUBST1_TAC >>
       fsrw_tac[DNF_ss][] >>
       first_x_assum match_mp_tac >>
       fsrw_tac[ARITH_ss][] ) >>
     spose_not_then strip_assume_tac >>
     qpat_assum`~(x < y)`mp_tac >> simp[] >>
     rw[AC ADD_ASSOC ADD_SYM] >>
     REWRITE_TAC[Once ADD_ASSOC] >>
     CONV_TAC(LAND_CONV(LAND_CONV(REWRITE_CONV[Once ADD_SYM]))) >>
     REWRITE_TAC[Once (GSYM ADD_ASSOC)] >>
     simp[] >>
     REWRITE_TAC[Once (ADD_ASSOC)] >>
     simp[] >>
     `x - (k + (x0 + 1)) = (x - (x0 + 1)) - k` by fsrw_tac[ARITH_ss][] >>
     pop_assum SUBST1_TAC >>
     fsrw_tac[DNF_ss][] >>
     first_x_assum match_mp_tac >>
     fsrw_tac[ARITH_ss][] ) >>
   fsrw_tac[DNF_ss,ARITH_ss][SUBSET_DEF,PRE_SUB1] >>
   qx_gen_tac`x` >>strip_tac >>
   rpt(first_x_assum(qspec_then`x`mp_tac)) >>
   simp[] ) >>
 strip_tac >- (
   simp[FOLDL_UNION_BIGUNION] >>
   rpt gen_tac >> strip_tac >>
   Q.PAT_ABBREV_TAC`P = X ∨ Y` >>
   rw[] >>
   rw[Once syneq_exp_cases] >>
   simp[EVERY2_EVERY,EVERY_MEM,FORALL_PROD,MEM_ZIP] >>
   rw[] >> simp[EL_MAP] >>
   fsrw_tac[DNF_ss][EXISTS_PROD,FORALL_PROD] >>
   first_x_assum (match_mp_tac o MP_CANON) >>
   simp[MEM_EL] >>
   fsrw_tac[DNF_ss][SUBSET_DEF,MEM_EL] >>
   qexists_tac`n` >> simp[] >>
   fs[markerTheory.Abbrev_def] >> rw[] >> fs[IMAGE_EQ_SING,MEM_EL] >>
   metis_tac[] ) >>
 strip_tac >- ( rw[] >> rw[Once syneq_exp_cases] ) >>
 strip_tac >- ( rw[] >> rw[Once syneq_exp_cases] ) >>
 strip_tac >- ( rw[] >> rw[Once syneq_exp_cases] ) >>
 strip_tac >- ( rw[] >> rw[Once syneq_exp_cases] ))

val free_vars_mkshift = store_thm("free_vars_mkshift",
  ``∀f k e. free_vars (mkshift f k e) = IMAGE (λv. if v < k then v else f (v-k) + k) (free_vars e)``,
  ho_match_mp_tac mkshift_ind >>
  strip_tac >- (
    srw_tac[DNF_ss][EXTENSION,MEM_MAP,EXISTS_PROD] >>
    metis_tac[] ) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rw[EXTENSION] >>
    rw[EQ_IMP_THM]
    >- metis_tac[]
    >- (
      fsrw_tac[ARITH_ss][PRE_SUB1] >>
      qexists_tac`v-1` >>
      fsrw_tac[ARITH_ss][] >>
      disj2_tac >>
      qexists_tac`v` >>
      fsrw_tac[ARITH_ss][] )
    >- (
      disj1_tac >>
      qexists_tac`v` >>
      srw_tac[ARITH_ss][] )
    >- (
      fsrw_tac[ARITH_ss][PRE_SUB1] >>
      disj2_tac >>
      srw_tac[ARITH_ss][]
      >- metis_tac[] >>
      fsrw_tac[ARITH_ss][] >>
      qmatch_assum_rename_tac`z:num ≠ 0`[] >>
      qexists_tac`k + f (z - (k + 1)) + 1` >>
      simp[] >>
      qexists_tac`z` >>
      simp[] )) >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rw[FOLDL_UNION_BIGUNION] >>
    fsrw_tac[DNF_ss][Once EXTENSION] >>
    fsrw_tac[DNF_ss][MEM_MAP,EQ_IMP_THM] >>
    metis_tac[] ) >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rw[EXTENSION] >>
    rw[EQ_IMP_THM]
    >- metis_tac[]
    >- (
      fsrw_tac[ARITH_ss][PRE_SUB1] >>
      qexists_tac`v-1` >>
      fsrw_tac[ARITH_ss][] >>
      disj2_tac >>
      qexists_tac`v` >>
      fsrw_tac[ARITH_ss][] )
    >- (
      disj1_tac >>
      qexists_tac`v` >>
      srw_tac[ARITH_ss][] )
    >- (
      fsrw_tac[ARITH_ss][PRE_SUB1] >>
      disj2_tac >>
      srw_tac[ARITH_ss][]
      >- metis_tac[] >>
      fsrw_tac[ARITH_ss][] >>
      qmatch_assum_rename_tac`z:num ≠ 0`[] >>
      qexists_tac`k + f (z - (k + 1)) + 1` >>
      simp[] >>
      qexists_tac`z` >>
      simp[] )) >>
  strip_tac >- (
    simp[] >>
    rw[FOLDL_UNION_BIGUNION] >>
    rw[Once EXTENSION] >>
    fsrw_tac[DNF_ss][] >>
    rw[EQ_IMP_THM] >- (
      rw[] >> fsrw_tac[ARITH_ss][] >>
      disj1_tac >>
      qexists_tac`v` >>
      simp[] )
    >- (
      fs[MEM_MAP] >> rw[] >>
      qmatch_assum_rename_tac`MEM cb defs`[] >>
      disj2_tac >>
      qexists_tac`cb` >>
      simp[]>>
      Cases_on`cb`>>fs[] >>
      PairCases_on`x`>>fs[] >>
      first_x_assum(qspecl_then[`x0`,`x1`]mp_tac) >>
      simp[Once EXTENSION] >> rw[] >>
      qmatch_assum_rename_tac`z ∈ free_vars X`["X"] >>
      first_x_assum(qspec_then`z`mp_tac) >>
      fsrw_tac[ARITH_ss][] >>
      srw_tac[ARITH_ss][] >>
      srw_tac[ARITH_ss][] >>
      fsrw_tac[ARITH_ss][] >>
      qexists_tac`v - x0` >> simp[] >>
      qexists_tac`v`>>simp[] )
    >- (
      disj1_tac >>
      qexists_tac`m` >>
      srw_tac[ARITH_ss][] )
    >- (
      disj2_tac >>
      Cases_on`cb`>>fs[]>>
      simp[MEM_MAP] >>
      fsrw_tac[DNF_ss][] >>
      PairCases_on`x`>>fs[] >>
      BasicProvers.VAR_EQ_TAC >>
      qmatch_assum_rename_tac`z ∈ free_vars x1`[] >>
      CONV_TAC SWAP_EXISTS_CONV >>
      qexists_tac`INL (x0,x1)` >> simp[] >>
      srw_tac[ARITH_ss][] >- (
        qexists_tac`z-x0` >>
        simp[] >>
        qexists_tac`z` >>
        simp[] >>
        first_x_assum(qspecl_then[`x0`,`x1`]mp_tac) >>
        simp[Once EXTENSION] >> strip_tac >>
        qexists_tac`z` >>
        srw_tac[ARITH_ss][] ) >>
      Q.PAT_ABBREV_TAC`vv = k + Z` >>
      qexists_tac`vv+LENGTH defs` >>
      simp[] >>
      qexists_tac`vv + LENGTH defs + x0` >>
      simp[] >>
      first_x_assum(qspecl_then[`x0`,`x1`]mp_tac) >>
      simp[Once EXTENSION] >> strip_tac >>
      qexists_tac`z` >>
      simp[Abbr`vv`] )) >>
  strip_tac >- (
    rw[] >>
    Cases_on`cb`>>simp[] >>
    PairCases_on`x`>>simp[]>>
    simp[Once EXTENSION,PRE_SUB1]>>
    srw_tac[ARITH_ss][EQ_IMP_THM] >- (
      fs[Once EXTENSION] >>
      fsrw_tac[DNF_ss][] >>
      qexists_tac`v` >>
      srw_tac[ARITH_ss][] ) >>
    fs[Once EXTENSION] >>
    fsrw_tac[DNF_ss][] >>
    qexists_tac`m` >>
    srw_tac[ARITH_ss][] ) >>
  strip_tac >- (
    rw[FOLDL_UNION_BIGUNION] >>
    fsrw_tac[DNF_ss][Once EXTENSION] >>
    fsrw_tac[DNF_ss][MEM_MAP,EQ_IMP_THM] >>
    metis_tac[] ) >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- rw[])
val _ = export_rewrites["free_vars_mkshift"]

val free_vars_shift = store_thm("free_vars_shift",
  ``free_vars (shift k n e) = IMAGE (λv. if v < n then v else k + v) (free_vars e)``,
  simp[shift_def])
val _ = export_rewrites["free_vars_shift"]

val free_labs_mkshift = store_thm("free_labs_mkshift",
  ``∀f k e. free_labs (mkshift f k e) = free_labs e``,
  ho_match_mp_tac mkshift_ind >> rw[] >>
  TRY (
    fsrw_tac[DNF_ss][Once EXTENSION,MEM_MAP,MEM_FILTER] >>
    metis_tac[] )
  >- (
    unabbrev_all_tac >> simp[] >>
    fsrw_tac[DNF_ss][Once EXTENSION,MEM_FILTER,MEM_MAP] >>
    srw_tac[DNF_ss][EQ_IMP_THM] >>
    full_simp_tac(srw_ss()++QUANT_INST_ss[sum_qp])[EXISTS_PROD] >>
    TRY (Cases_on`OUTL cb` >> Cases_on`cb`) >> fs[] >>
    TRY (qmatch_assum_rename_tac`ISL z`[]>>Cases_on`OUTL z`>>Cases_on`z`) >> fs[] >>
    TRY (qmatch_assum_rename_tac`ISR z`[]>>Cases_on`z`) >> fs[] >>
    TRY ( res_tac >> fsrw_tac[ARITH_ss][] >> metis_tac[] ) >>
    TRY (
      disj1_tac >>
      disj1_tac >>
      qmatch_assum_abbrev_tac`MEM cb defs` >>
      qexists_tac`cb` >>
      simp[Abbr`cb`] >>
      res_tac >>
      fsrw_tac[ARITH_ss][] >>
      NO_TAC ) >>
    TRY (
      disj1_tac >>
      disj2_tac >>
      qmatch_assum_abbrev_tac`MEM cb defs` >>
      qexists_tac`cb` >>
      simp[Abbr`cb`] >>
      res_tac >>
      fsrw_tac[ARITH_ss][] >>
      NO_TAC )) >>
  Cases_on`cb`>>fs[] >>
  Cases_on`x`>>fs[])
val _ = export_rewrites["free_labs_mkshift"]

val free_labs_shift = store_thm("free_labs_shift",
  ``free_labs (shift k n e) = free_labs e``,
  simp[shift_def])
val _ = export_rewrites["free_labs_shift"]

(* Cevaluate deterministic *)

val Cevaluate_determ = store_thm("Cevaluate_determ",
  ``(∀c s env exp res. Cevaluate c s env exp res ⇒ ∀res'. Cevaluate c s env exp res' ⇒ (res' = res)) ∧
    (∀c s env exps ress. Cevaluate_list c s env exps ress ⇒ ∀ress'. Cevaluate_list c s env exps ress' ⇒ (ress' = ress))``,
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
    Cases_on`cb`>|[Cases_on`x`,ALL_TAC]>>fs[UNCURRY]>>
    rw[] >>
    res_tac >> fs[] >> rw[] >> rfs[] >> rw[] >>
    res_tac >> fs[] >> rw[] >>
    fs[LET_THM,UNCURRY]) >>
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
