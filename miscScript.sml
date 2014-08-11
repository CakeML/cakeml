open HolKernel bossLib boolLib boolSimps lcsymtacs miscLib
open optionTheory listTheory pred_setTheory finite_mapTheory alistTheory rich_listTheory arithmeticTheory pairTheory sortingTheory relationTheory bitTheory sptreeTheory

(* Misc. lemmas (without any compiler constants) *)
val _ = new_theory "misc"
val _ = ParseExtras.temp_tight_equality()

(* TODO: move/categorize *)

val o_f_FUNION = store_thm("o_f_FUNION",
  ``f o_f (f1 ⊌ f2) = (f o_f f1) ⊌ (f o_f f2)``,
  simp[GSYM fmap_EQ_THM,FUNION_DEF] >>
  rw[o_f_FAPPLY]);

val IS_SOME_EXISTS = store_thm("IS_SOME_EXISTS",
  ``∀opt. IS_SOME opt ⇔ ∃x. opt = SOME x``,
  Cases >> simp[])

val FDOM_FOLDR_DOMSUB = store_thm("FDOM_FOLDR_DOMSUB",
  ``∀ls fm. FDOM (FOLDR (λk m. m \\ k) fm ls) = FDOM fm DIFF set ls``,
  Induct >> simp[] >>
  ONCE_REWRITE_TAC[EXTENSION] >>
  simp[] >> metis_tac[])

val LIST_TO_SET_EQ_SING = store_thm("LIST_TO_SET_EQ_SING",
  ``∀x ls. (set ls = {x}) ⇔ ls ≠ [] ∧ EVERY ($= x) ls``,
  gen_tac >> Induct >> simp[] >>
  simp[Once EXTENSION,EVERY_MEM] >>
  metis_tac[])

val INSERT_EQ_SING = store_thm("INSERT_EQ_SING",
  ``∀s x y. (x INSERT s = {y}) ⇔ ((x = y) ∧ s ⊆ {y})``,
  rw[SUBSET_DEF,EXTENSION] >> metis_tac[])

val REPLICATE_GENLIST = store_thm("REPLICATE_GENLIST",
  ``!n x. REPLICATE n x = GENLIST (K x) n``,
  Induct THEN SRW_TAC[][rich_listTheory.REPLICATE,GENLIST_CONS])

val domain_nat_set_from_list = store_thm("domain_nat_set_from_list",
  ``∀ls ns. domain (FOLDL (λs n. insert n () s) ns ls) = domain ns ∪ set ls``,
  Induct >> simp[sptreeTheory.domain_insert] >>
  rw[EXTENSION] >> metis_tac[])
val _ = export_rewrites["domain_nat_set_from_list"]

val wf_nat_set_from_list = store_thm("wf_nat_set_from_list",
  ``∀ls ns. wf ns ⇒ wf (FOLDL (λs n. insert n z s) ns ls)``,
  Induct >> simp[] >> rw[sptreeTheory.wf_insert])

val BIT_11 = store_thm("BIT_11",
  ``∀n m. (BIT n = BIT m) ⇔ (n = m)``,
  simp[EQ_IMP_THM] >>
  Induct >> simp[BIT0_ODD,FUN_EQ_THM] >- (
    Cases >> simp[] >>
    qexists_tac`1` >> simp[GSYM BIT_DIV2,BIT_ZERO] ) >>
  simp[GSYM BIT_DIV2] >>
  Cases >> simp[GSYM BIT_DIV2] >- (
    qexists_tac`1` >>
    simp[BIT_ZERO] >>
    simp[BIT_def,BITS_THM] ) >>
  rw[] >>
  first_x_assum MATCH_MP_TAC >>
  simp[FUN_EQ_THM] >>
  gen_tac >>
  first_x_assum(qspec_then`x*2`mp_tac) >>
  simp[arithmeticTheory.MULT_DIV])

val BIT_11_2 = store_thm("BIT_11_2",
  ``∀n m. (∀z. (z < 2 ** (MAX n m)) ⇒ (BIT n z ⇔ BIT m z)) ⇔ (n = m)``,
  simp[Once EQ_IMP_THM] >>
  Induct >- (
    simp[] >>
    Cases >> simp[] >>
    qexists_tac`2 ** SUC n - 1` >>
    simp[BIT_EXP_SUB1] ) >>
  Cases >> simp[] >- (
    qexists_tac`2 ** SUC n - 1` >>
    simp[BIT_EXP_SUB1] ) >>
  strip_tac >>
  first_x_assum MATCH_MP_TAC >>
  qx_gen_tac`z` >>
  first_x_assum(qspec_then`z*2`mp_tac) >>
  simp[GSYM BIT_DIV2,arithmeticTheory.MULT_DIV] >>
  rw[] >> first_x_assum MATCH_MP_TAC >>
  fs[arithmeticTheory.MAX_DEF] >>
  rw[] >> fs[] >>
  simp[arithmeticTheory.EXP])

val binary_induct = store_thm("binary_induct",
  ``∀P. P (0:num) ∧ (∀n. P n ⇒ P (2*n) ∧ P (2*n+1)) ⇒ ∀n. P n``,
  gen_tac >> strip_tac >>
  completeInduct_on`n` >>
  Cases_on`n=0`>>simp[]>>
  `n DIV 2 < n ∧ ((n = 2 * (n DIV 2)) ∨ (n = 2 * (n DIV 2) + 1))` by (
    simp[DIV_MULT_THM2] >>
    `n MOD 2 < 2` by (
      MATCH_MP_TAC arithmeticTheory.MOD_LESS >>
      simp[] ) >>
    simp[] ) >>
  metis_tac[])

val BIT_TIMES2 = store_thm("BIT_TIMES2",
  ``BIT z (2 * n) ⇔ 0 < z ∧ BIT (PRE z) n``,
  Cases_on`z`>>simp[]>-(
    simp[BIT0_ODD] >>
    simp[arithmeticTheory.ODD_EVEN] >>
    simp[arithmeticTheory.EVEN_DOUBLE] ) >>
  qmatch_rename_tac`BIT (SUC z) (2 * n) ⇔ BIT z n`[] >>
  qspecl_then[`z`,`n`,`1`]mp_tac BIT_SHIFT_THM >>
  simp[arithmeticTheory.ADD1])

val BIT_TIMES2_1 = store_thm("BIT_TIMES2_1",
  ``∀n z. BIT z (2 * n + 1) ⇔ (z=0) ∨ BIT z (2 * n)``,
  Induct >> simp[] >- (
    simp[BIT_ZERO] >>
    Cases_on`z`>>simp[BIT0_ODD] >>
    simp[GSYM BIT_DIV2,BIT_ZERO] ) >>
  Cases >> simp[BIT0_ODD] >- (
    simp[arithmeticTheory.ODD_EXISTS,arithmeticTheory.ADD1] >>
    metis_tac[] ) >>
  simp[GSYM BIT_DIV2] >>
  qspec_then`2`mp_tac arithmeticTheory.ADD_DIV_RWT >>
  simp[] >>
  disch_then(qspecl_then[`2 * SUC n`,`1`]mp_tac) >>
  simp[] >>
  simp[arithmeticTheory.MOD_EQ_0_DIVISOR] >>
  metis_tac[] )

val LOG2_TIMES2 = store_thm("LOG2_TIMES2",
  ``0 < n ⇒ (LOG2 (2 * n) = SUC (LOG2 n))``,
  rw[LOG2_def] >>
  qspecl_then[`1`,`2`,`n`]mp_tac logrootTheory.LOG_EXP >>
  simp[arithmeticTheory.ADD1])

val LOG2_TIMES2_1 = store_thm("LOG2_TIMES2_1",
  ``∀n. 0 < n ⇒ (LOG2 (2 * n + 1) = LOG2 (2 * n))``,
  rw[LOG2_def] >>
  MATCH_MP_TAC logrootTheory.LOG_UNIQUE >>
  simp[GSYM LOG2_def,LOG2_TIMES2] >>
  simp[arithmeticTheory.EXP] >>
  conj_tac >- (
    MATCH_MP_TAC arithmeticTheory.LESS_EQ_TRANS >>
    qexists_tac`2*n` >> simp[] >>
    qspec_then`n`mp_tac logrootTheory.LOG_MOD >>
    simp[] >> strip_tac >>
    qmatch_assum_abbrev_tac`n = X` >>
    qsuff_tac`2 ** LOG2 n ≤ X` >- rw[] >>
    qunabbrev_tac`X` >>
    simp[LOG2_def] ) >>
  simp[GSYM arithmeticTheory.ADD1] >>
  match_mp_tac arithmeticTheory.LESS_NOT_SUC >>
  `4:num = 2 * 2` by simp[] >>
  pop_assum SUBST1_TAC >>
  REWRITE_TAC[Once (GSYM arithmeticTheory.MULT_ASSOC)] >>
  simp[] >>
  conj_asm1_tac >- (
    qspec_then`n`mp_tac logrootTheory.LOG_MOD >>
    simp[] >> strip_tac >>
    qmatch_assum_abbrev_tac`n = X` >>
    qsuff_tac`X < 2 * 2 ** LOG2 n` >- rw[] >>
    qunabbrev_tac`X` >>
    simp[LOG2_def] >>
    qmatch_abbrev_tac`(a:num) + b < 2 * a` >>
    qsuff_tac`n MOD a < a` >- simp[] >>
    MATCH_MP_TAC arithmeticTheory.MOD_LESS >>
    simp[Abbr`a`] ) >>
  qmatch_abbrev_tac`X ≠ Y` >>
  qsuff_tac`EVEN X ∧ ODD Y` >- metis_tac[arithmeticTheory.EVEN_ODD] >>
  conj_tac >- (
    simp[Abbr`X`,arithmeticTheory.EVEN_EXISTS] >>
    qexists_tac`2 * 2 ** LOG2 n` >>
    simp[] ) >>
  simp[Abbr`Y`,arithmeticTheory.ODD_EXISTS] >>
  metis_tac[])

val C_BIT_11 = store_thm("C_BIT_11",
  ``∀n m. (∀z. (z ≤ LOG2 (MAX n m)) ⇒ (BIT z n ⇔ BIT z m)) ⇔ (n = m)``,
  simp[Once EQ_IMP_THM] >>
  ho_match_mp_tac binary_induct >>
  simp[] >>
  conj_tac >- (
    Cases >> simp[] >>
    qexists_tac`LOG2 (SUC n)` >>
    simp[BIT_LOG2,BIT_ZERO] ) >>
  gen_tac >> strip_tac >>
  simp[BIT_TIMES2,BIT_TIMES2_1] >>
  rw[] >- (
    Cases_on`n=0`>>fs[]>-(
      Cases_on`m=0`>>fs[]>>
      first_x_assum(qspec_then`LOG2 m`mp_tac)>>simp[BIT_ZERO] >>
      simp[BIT_LOG2]) >>
    `¬ODD m` by (
      simp[SYM BIT0_ODD] >>
      first_x_assum(qspec_then`0`mp_tac) >>
      simp[] ) >>
    fs[arithmeticTheory.ODD_EVEN] >>
    fs[arithmeticTheory.EVEN_EXISTS] >>
    simp[arithmeticTheory.EQ_MULT_LCANCEL] >>
    first_x_assum MATCH_MP_TAC >>
    rw[] >>
    first_x_assum(qspec_then`SUC z`mp_tac) >>
    discharge_hyps >- (
      fs[arithmeticTheory.MAX_DEF] >>
      rw[] >> fs[] >> simp[LOG2_TIMES2] ) >>
    simp[BIT_TIMES2] ) >>
  Cases_on`n=0`>>fs[]>-(
    fs[BIT_ZERO] >>
    Cases_on`m=0`>>fs[BIT_ZERO] >>
    Cases_on`m=1`>>fs[]>>
    first_x_assum(qspec_then`LOG2 m`mp_tac) >>
    simp[arithmeticTheory.MAX_DEF,BIT_LOG2] >>
    spose_not_then strip_assume_tac >>
    qspec_then`m`mp_tac logrootTheory.LOG_MOD >>
    simp[GSYM LOG2_def] ) >>
  `ODD m` by (
    simp[SYM BIT0_ODD] >>
    first_x_assum(qspec_then`0`mp_tac) >>
    simp[] ) >>
  fs[arithmeticTheory.ODD_EXISTS,arithmeticTheory.ADD1] >>
  simp[arithmeticTheory.EQ_MULT_LCANCEL] >>
  first_x_assum MATCH_MP_TAC >>
  rw[] >>
  first_x_assum(qspec_then`SUC z`mp_tac) >>
  discharge_hyps >- (
    fs[arithmeticTheory.MAX_DEF] >>
    rw[] >> fs[] >> simp[LOG2_TIMES2_1,LOG2_TIMES2] ) >>
  simp[BIT_TIMES2_1,BIT_TIMES2])

val BIT_num_from_bin_list_leading = store_thm("BIT_num_from_bin_list_leading",
  ``∀l x. EVERY ($> 2) l ∧ LENGTH l ≤ x ⇒ ¬BIT x (num_from_bin_list l)``,
  simp[numposrepTheory.num_from_bin_list_def] >>
  rw[] >>
  MATCH_MP_TAC NOT_BIT_GT_TWOEXP >>
  MATCH_MP_TAC arithmeticTheory.LESS_LESS_EQ_TRANS >>
  qexists_tac`2 ** LENGTH l` >>
  simp[numposrepTheory.l2n_lt] )

val least_from_def = Define`
  least_from P n = if (∃x. P x ∧ n ≤ x) then $LEAST (λx. P x ∧ n ≤ x) else $LEAST P`

val LEAST_thm = store_thm("LEAST_thm",
  ``$LEAST P = least_from P 0``,
  rw[least_from_def,ETA_AX])

val least_from_thm = store_thm("least_from_thm",
  ``least_from P n = if P n then n else least_from P (n+1)``,
  rw[least_from_def] >>
  numLib.LEAST_ELIM_TAC >> rw[] >> fs[] >> res_tac >>
  TRY(metis_tac[arithmeticTheory.LESS_OR_EQ]) >- (
    numLib.LEAST_ELIM_TAC >> rw[] >> fs[] >- metis_tac[] >>
    qmatch_rename_tac`a = b`[] >>
    `n ≤ b` by DECIDE_TAC >>
    Cases_on`b < a` >-metis_tac[] >>
    spose_not_then strip_assume_tac >>
    `a < b` by DECIDE_TAC >>
    `¬(n + 1 ≤ a)` by metis_tac[] >>
    `a = n` by DECIDE_TAC >>
    fs[] )
  >- (
    Cases_on`n+1≤x`>-metis_tac[]>>
    `x = n` by DECIDE_TAC >>
    fs[] )
  >- (
    `¬(n ≤ x)` by metis_tac[] >>
    `x = n` by DECIDE_TAC >>
    fs[] ))

val FILTER_F = store_thm("FILTER_F",
  ``∀ls. FILTER (λx. F) ls = []``,
  Induct >> simp[])
val _ = export_rewrites["FILTER_F"]

val OPTREL_SOME = store_thm("OPTREL_SOME",
  ``(!R x y. OPTREL R (SOME x) y <=> (?z. y = SOME z /\ R x z)) /\
    (!R x y. OPTREL R x (SOME y) <=> (?z. x = SOME z /\ R z y))``,
    rw[optionTheory.OPTREL_def])

val LIST_REL_O = store_thm("LIST_REL_O",
  ``∀R1 R2 l1 l2. LIST_REL (R1 O R2) l1 l2 ⇔ ∃l3. LIST_REL R2 l1 l3 ∧ LIST_REL R1 l3 l2``,
  rpt gen_tac >>
  simp[EVERY2_EVERY,EVERY_MEM,EQ_IMP_THM,GSYM AND_IMP_INTRO,MEM_ZIP,PULL_EXISTS,O_DEF] >>
  rw[] >- (
    fs[GSYM RIGHT_EXISTS_IMP_THM,SKOLEM_THM] >>
    qexists_tac`GENLIST f (LENGTH l2)` >>
    simp[MEM_ZIP,PULL_EXISTS] ) >>
  metis_tac[])

val OPTREL_O_lemma = prove(
  ``∀R1 R2 l1 l2. OPTREL (R1 O R2) l1 l2 ⇔ ∃l3. OPTREL R2 l1 l3 ∧ OPTREL R1 l3 l2``,
  rw[optionTheory.OPTREL_def,EQ_IMP_THM,O_DEF,PULL_EXISTS] >> metis_tac[])

val OPTREL_O = store_thm("OPTREL_O",
  ``∀R1 R2. OPTREL (R1 O R2) = OPTREL R1 O OPTREL R2``,
  rw[FUN_EQ_THM,OPTREL_O_lemma,O_DEF])

val FUNPOW_mono = store_thm("FUNPOW_mono",
  ``(∀x y. R1 x y ⇒ R2 x y) ∧
    (∀R1 R2. (∀x y. R1 x y ⇒ R2 x y) ⇒ ∀x y. f R1 x y ⇒ f R2 x y) ⇒
    ∀n x y. FUNPOW f n R1 x y ⇒ FUNPOW f n R2 x y``,
  strip_tac >> Induct >> simp[] >>
  simp[arithmeticTheory.FUNPOW_SUC] >>
  first_x_assum match_mp_tac >> rw[])

val OPTREL_trans = store_thm("OPTREL_trans",
  ``∀R x y z. (∀a b c. (x = SOME a) ∧ (y = SOME b) ∧ (z = SOME c) ∧ R a b ∧ R b c ⇒ R a c)
    ∧ OPTREL R x y ∧ OPTREL R y z ⇒ OPTREL R x z``,
  rw[optionTheory.OPTREL_def])

val UPDATE_LIST_def = Define`
  UPDATE_LIST = FOLDL (combin$C (UNCURRY UPDATE))`
val _ = Parse.add_infix("=++",500,Parse.LEFT)
val _ = Parse.overload_on("=++",``UPDATE_LIST``)

val UPDATE_LIST_THM = store_thm("UPDATE_LIST_THM",
  ``∀f. (f =++ [] = f) ∧ ∀h t. (f =++ (h::t) = (FST h =+ SND h) f =++ t)``,
  rw[UPDATE_LIST_def,pairTheory.UNCURRY])

val APPLY_UPDATE_LIST_ALOOKUP = store_thm("APPLY_UPDATE_LIST_ALOOKUP",
  ``∀ls f x. (f =++ ls) x = case ALOOKUP (REVERSE ls) x of NONE => f x | SOME y => y``,
  Induct >> simp[UPDATE_LIST_THM,ALOOKUP_APPEND] >>
  Cases >> simp[combinTheory.APPLY_UPDATE_THM] >>
  rw[] >> BasicProvers.CASE_TAC)

val IS_SUFFIX_CONS = store_thm("IS_SUFFIX_CONS",
  ``∀l1 l2 a. IS_SUFFIX l1 l2 ⇒ IS_SUFFIX (a::l1) l2``,
  rw[rich_listTheory.IS_SUFFIX_APPEND] >>
  qexists_tac`a::l` >>rw[])

val SORTED_weaken = store_thm("SORTED_weaken",
  ``∀R R' ls. SORTED R ls /\ (!x y. MEM x ls /\ MEM y ls /\ R x y ==> R' x y)
      ==> SORTED R' ls``,
  NTAC 2 GEN_TAC THEN
  Induct THEN SRW_TAC[][] THEN
  Cases_on`ls` THEN
  FULL_SIMP_TAC(srw_ss())[sortingTheory.SORTED_DEF] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  METIS_TAC[])

val INFINITE_INJ_NOT_SURJ = store_thm("INFINITE_INJ_NOT_SURJ",
  ``∀s. INFINITE s ⇔ (s ≠ ∅) ∧ (∃f. INJ f s s ∧ ¬SURJ f s s)``,
  rw[EQ_IMP_THM] >- (
    PROVE_TAC[INFINITE_INHAB,MEMBER_NOT_EMPTY] )
  >- (
    fs[infinite_num_inj] >>
    qexists_tac`λx. if ∃n. x = f n then f (SUC (LEAST n. x = f n)) else x` >>
    conj_asm1_tac >- (
      fs[INJ_IFF] >>
      conj_asm1_tac >- rw[] >>
      rw[] >- (
        numLib.LEAST_ELIM_TAC >>
        conj_tac >- PROVE_TAC[] >>
        rw[] ) >>
      numLib.LEAST_ELIM_TAC >>
      rw[] >>
      metis_tac[] ) >>
    fs[SURJ_DEF,INJ_IFF] >>
    qexists_tac`f 0` >>
    simp[] >>
    rw[] >>
    metis_tac[]) >>
  fs[SURJ_DEF] >- (fs[INJ_IFF] >> metis_tac[]) >>
  simp[infinite_num_inj] >>
  qexists_tac`λn. FUNPOW f n x` >>
  simp[INJ_IFF] >>
  conj_asm1_tac >- (
    Induct >>
    simp[arithmeticTheory.FUNPOW_SUC] >>
    fs[INJ_IFF] ) >>
  Induct >> simp[] >- (
    Cases >> simp[arithmeticTheory.FUNPOW_SUC] >>
    metis_tac[] ) >>
  Cases >> simp[arithmeticTheory.FUNPOW_SUC] >> fs[INJ_IFF] >>
  metis_tac[] )

val MAP_SND_FILTER_NEQ = store_thm("MAP_SND_FILTER_NEQ",
  ``MAP SND (FILTER (λ(x,y). y ≠ z) ls) =
    FILTER ($<> z) (MAP SND ls)``,
  Q.ISPECL_THEN[`$<> z`,`SND:('b#'a)->'a`,`ls`]mp_tac rich_listTheory.FILTER_MAP >> rw[] >>
  AP_TERM_TAC >> AP_THM_TAC >> AP_TERM_TAC >>
  simp[FUN_EQ_THM,FORALL_PROD,EQ_IMP_THM])

val ALL_DISTINCT_DROP = store_thm("ALL_DISTINCT_DROP",
  ``∀ls n. ALL_DISTINCT ls ⇒ ALL_DISTINCT (DROP n ls)``,
  Induct >> simp[] >> rw[])

val FEVERY_SUBMAP = store_thm("FEVERY_SUBMAP",
  ``FEVERY P fm /\ fm0 SUBMAP fm ==> FEVERY P fm0``,
  SRW_TAC[][FEVERY_DEF,SUBMAP_DEF])

val FEVERY_ALL_FLOOKUP = store_thm("FEVERY_ALL_FLOOKUP",
  ``∀P f. FEVERY P f ⇔ ∀k v. (FLOOKUP f k = SOME v) ⇒ P (k,v)``,
  SRW_TAC[][FEVERY_DEF,FLOOKUP_DEF])

val ALOOKUP_ALL_DISTINCT_EL = store_thm("ALOOKUP_ALL_DISTINCT_EL",
  ``∀ls n. n < LENGTH ls ∧ ALL_DISTINCT (MAP FST ls) ⇒ (ALOOKUP ls (FST (EL n ls)) = SOME (SND (EL n ls)))``,
  Induct >> simp[] >>
  Cases >> simp[] >>
  Cases >> simp[] >>
  rw[] >> fs[MEM_MAP] >>
  metis_tac[MEM_EL])

val ALOOKUP_ZIP_MAP_SND = store_thm("ALOOKUP_ZIP_MAP_SND",
  ``∀l1 l2 k f. (LENGTH l1 = LENGTH l2) ⇒
      (ALOOKUP (ZIP(l1,MAP f l2)) = OPTION_MAP f o (ALOOKUP (ZIP(l1,l2))))``,
  Induct >> simp[LENGTH_NIL,LENGTH_NIL_SYM,FUN_EQ_THM] >>
  gen_tac >> Cases >> simp[] >> rw[] >> rw[])

val ALOOKUP_FILTER = store_thm("ALOOKUP_FILTER",
  ``∀ls x. ALOOKUP (FILTER (λ(k,v). P k) ls) x =
           if P x then ALOOKUP ls x else NONE``,
  Induct >> simp[] >> Cases >> simp[] >> rw[] >> fs[] >> metis_tac[])

val find_index_def = Define`
  (find_index _ [] _ = NONE) ∧
  (find_index y (x::xs) n = if x = y then SOME n else find_index y xs (n+1))`

val find_index_NOT_MEM = store_thm("find_index_NOT_MEM",
  ``∀ls x n. ¬MEM x ls = (find_index x ls n = NONE)``,
  Induct >> rw[find_index_def])

val find_index_MEM = store_thm("find_index_MEM",
  ``!ls x n. MEM x ls ==> ?i. (find_index x ls n = SOME (n+i)) /\ i < LENGTH ls /\ (EL i ls = x)``,
  Induct >> rw[find_index_def] >- (
    qexists_tac`0`>>rw[] ) >>
  first_x_assum(qspecl_then[`x`,`n+1`]mp_tac) >>
  rw[]>>qexists_tac`SUC i`>>srw_tac[ARITH_ss][ADD1])

val find_index_LEAST_EL = store_thm("find_index_LEAST_EL",
  ``∀ls x n. find_index x ls n = if MEM x ls then SOME (n + (LEAST n. x = EL n ls)) else NONE``,
  Induct >- rw[find_index_def] >>
  simp[find_index_def] >>
  rpt gen_tac >>
  Cases_on`h=x`>>fs[] >- (
    numLib.LEAST_ELIM_TAC >>
    conj_tac >- (qexists_tac`0` >> rw[]) >>
    Cases >> rw[] >>
    first_x_assum (qspec_then`0`mp_tac) >> rw[] ) >>
  rw[] >>
  numLib.LEAST_ELIM_TAC >>
  conj_tac >- metis_tac[MEM_EL,MEM] >>
  rw[] >>
  Cases_on`n`>>fs[ADD1] >>
  numLib.LEAST_ELIM_TAC >>
  conj_tac >- metis_tac[] >>
  rw[] >>
  qmatch_rename_tac`m = n`[] >>
  Cases_on`m < n` >- (res_tac >> fs[]) >>
  Cases_on`n < m` >- (
    `n + 1 < m + 1` by DECIDE_TAC >>
    res_tac >> fs[GSYM ADD1] ) >>
  DECIDE_TAC )

val find_index_LESS_LENGTH = store_thm(
"find_index_LESS_LENGTH",
``∀ls n m i. (find_index n ls m = SOME i) ⇒ (m <= i) ∧ (i < m + LENGTH ls)``,
Induct >> rw[find_index_def] >>
res_tac >>
srw_tac[ARITH_ss][arithmeticTheory.ADD1])

val find_index_ALL_DISTINCT_EL = store_thm(
"find_index_ALL_DISTINCT_EL",
``∀ls n m. ALL_DISTINCT ls ∧ n < LENGTH ls ⇒ (find_index (EL n ls) ls m = SOME (m + n))``,
Induct >- rw[] >>
gen_tac >> Cases >>
srw_tac[ARITH_ss][find_index_def] >>
metis_tac[MEM_EL])
val _ = export_rewrites["find_index_ALL_DISTINCT_EL"]

val find_index_ALL_DISTINCT_EL_eq = store_thm("find_index_ALL_DISTINCT_EL_eq",
  ``∀ls. ALL_DISTINCT ls ⇒ ∀x m i. (find_index x ls m = SOME i) =
      ∃j. (i = m + j) ∧ j < LENGTH ls ∧ (x = EL j ls)``,
  rw[EQ_IMP_THM] >- (
    imp_res_tac find_index_LESS_LENGTH >>
    fs[find_index_LEAST_EL] >> srw_tac[ARITH_ss][] >>
    numLib.LEAST_ELIM_TAC >>
    conj_tac >- PROVE_TAC[MEM_EL] >>
    fs[EL_ALL_DISTINCT_EL_EQ] ) >>
  PROVE_TAC[find_index_ALL_DISTINCT_EL])

val find_index_APPEND_same = store_thm("find_index_APPEND_same",
  ``!l1 n m i l2. (find_index n l1 m = SOME i) ==> (find_index n (l1 ++ l2) m = SOME i)``,
  Induct >> rw[find_index_def])

val find_index_ALL_DISTINCT_REVERSE = store_thm("find_index_ALL_DISTINCT_REVERSE",
  ``∀ls x m j. ALL_DISTINCT ls ∧ (find_index x ls m = SOME j) ⇒ (find_index x (REVERSE ls) m = SOME (m + LENGTH ls + m - j - 1))``,
  rw[] >> imp_res_tac find_index_ALL_DISTINCT_EL_eq >>
  `ALL_DISTINCT (REVERSE ls)` by rw[ALL_DISTINCT_REVERSE] >>
  simp[find_index_ALL_DISTINCT_EL_eq] >>
  rw[] >> fsrw_tac[ARITH_ss][] >> rw[] >>
  qmatch_assum_rename_tac`z < LENGTH ls`[] >>
  qexists_tac`LENGTH ls - z - 1` >>
  lrw[EL_REVERSE,PRE_SUB1])

val THE_find_index_suff = store_thm("THE_find_index_suff",
  ``∀P x ls n. (∀m. m < LENGTH ls ⇒ P (m + n)) ∧ MEM x ls ⇒
    P (THE (find_index x ls n))``,
  rw[] >>
  imp_res_tac find_index_MEM >>
  pop_assum(qspec_then`n`mp_tac) >>
  srw_tac[DNF_ss,ARITH_ss][])

val find_index_APPEND1 = store_thm("find_index_APPEND1",
  ``∀l1 n l2 m i. (find_index n (l1 ++ l2) m = SOME i) ∧ (i < m+LENGTH l1) ⇒ (find_index n l1 m = SOME i)``,
  Induct >> simp[find_index_def] >- (
    spose_not_then strip_assume_tac >>
    imp_res_tac find_index_LESS_LENGTH >>
    DECIDE_TAC ) >>
  rw[] >> res_tac >>
  first_x_assum match_mp_tac >>
  simp[])

val find_index_APPEND2 = store_thm("find_index_APPEND2",
  ``∀l1 n l2 m i. (find_index n (l1 ++ l2) m = SOME i) ∧ (m + LENGTH l1 ≤ i) ⇒ (find_index n l2 (m+LENGTH l1) = SOME i)``,
  Induct >> simp[find_index_def] >>
  rw[] >> fsrw_tac[ARITH_ss][] >>
  res_tac >> fsrw_tac[ARITH_ss][ADD1])

val find_index_is_MEM = store_thm("find_index_is_MEM",
  ``∀x ls n j. (find_index x ls n = SOME j) ⇒ MEM x ls``,
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

val find_index_APPEND = store_thm("find_index_APPEND",
  ``∀l1 l2 x n. find_index x (l1 ++ l2) n =
    case find_index x l1 n of
    | NONE => find_index x l2 (n + LENGTH l1)
    | SOME x => SOME x``,
  Induct >> simp[find_index_def] >> rw[] >>
  BasicProvers.CASE_TAC >>
  simp[arithmeticTheory.ADD1])

val find_index_in_FILTER_ZIP_EQ = store_thm("find_index_in_FILTER_ZIP_EQ",
  ``∀P l1 l2 x n1 n2 v1 j1 j2.
      (LENGTH l1 = LENGTH v1) ∧
      (FILTER (P o FST) (ZIP(l1,v1)) = l2) ∧
      (find_index x l1 n1 = SOME (n1+j1)) ∧
      (find_index x (MAP FST l2) n2 = SOME (n2+j2)) ∧
      P x
      ⇒
      j1 < LENGTH l1 ∧ j2 < LENGTH l2 ∧
      (EL j1 (ZIP(l1,v1)) = EL j2 l2)``,
  gen_tac >> Induct >> simp[find_index_def] >>
  rpt gen_tac >>
  BasicProvers.CASE_TAC >- (
    strip_tac >> fs[] >>
    Cases_on`j1`>>fsrw_tac[ARITH_ss][]>>
    fs[find_index_def] >>
    Cases_on`j2`>>fsrw_tac[ARITH_ss][] >>
    Cases_on`v1`>>fsrw_tac[ARITH_ss][find_index_def]) >>
  strip_tac >>
  Cases_on`v1`>>fs[] >>
  Cases_on`P h`>>fs[find_index_def] >- (
    rfs[] >>
    imp_res_tac find_index_LESS_LENGTH >>
    fsrw_tac[ARITH_ss][] >>
    first_x_assum(qspecl_then[`x`,`n1+1`]mp_tac) >>
    simp[] >>
    disch_then(qspecl_then[`n2+1`,`t`]mp_tac) >> simp[] >>
    Cases_on`j1=0`>>fsrw_tac[ARITH_ss][]>>
    Cases_on`j2=0`>>fsrw_tac[ARITH_ss][]>>
    disch_then(qspecl_then[`PRE j1`,`PRE j2`]mp_tac) >>
    simp[rich_listTheory.EL_CONS] ) >>
  first_x_assum(qspecl_then[`x`,`n1+1`]mp_tac) >>
  simp[] >>
  disch_then(qspecl_then[`n2`,`t`]mp_tac) >> simp[] >>
  imp_res_tac find_index_LESS_LENGTH >>
  fsrw_tac[ARITH_ss][] >>
  Cases_on`j1=0`>>fsrw_tac[ARITH_ss][]>>
  disch_then(qspec_then`PRE j1`mp_tac) >>
  simp[rich_listTheory.EL_CONS] )

val ALOOKUP_find_index_SOME = prove(
  ``∀env. (ALOOKUP env k = SOME v) ⇒
      ∀m. ∃i. (find_index k (MAP FST env) m = SOME (m+i)) ∧
          (v = EL i (MAP SND env))``,
  Induct >> simp[] >> Cases >> rw[find_index_def] >-
    (qexists_tac`0`>>simp[]) >> fs[] >>
  first_x_assum(qspec_then`m+1`mp_tac)>>rw[]>>rw[]>>
  qexists_tac`SUC i`>>simp[])
|> SPEC_ALL |> UNDISCH_ALL |> Q.SPEC`0` |> DISCH_ALL |> SIMP_RULE (srw_ss())[]
val ALOOKUP_find_index_SOME = store_thm("ALOOKUP_find_index_SOME",
  ``(ALOOKUP env k = SOME v) ⇒
    ∃i. (find_index k (MAP FST env) 0 = SOME i) ∧
        i < LENGTH env ∧ (v = SND (EL i env))``,
  rw[] >> imp_res_tac ALOOKUP_find_index_SOME >>
  imp_res_tac find_index_LESS_LENGTH >> fs[EL_MAP])
val ALOOKUP_find_index_NONE = store_thm("ALOOKUP_find_index_NONE",
  ``(ALOOKUP env k = NONE) ⇒ (find_index k (MAP FST env) m = NONE)``,
  rw[ALOOKUP_FAILS] >> rw[GSYM find_index_NOT_MEM,MEM_MAP,EXISTS_PROD])

val ALOOKUP_APPEND_same = store_thm("ALOOKUP_APPEND_same",
  ``∀l1 l2 l. (ALOOKUP l1 = ALOOKUP l2) ==> (ALOOKUP (l1 ++ l) = ALOOKUP (l2 ++ l))``,
  rw[ALOOKUP_APPEND,FUN_EQ_THM])

val ALOOKUP_ALL_DISTINCT_PERM_same = store_thm("ALOOKUP_ALL_DISTINCT_PERM_same",
  ``∀l1 l2. ALL_DISTINCT (MAP FST l1) ∧ PERM (MAP FST l1) (MAP FST l2) ∧ (set l1 = set l2) ⇒ (ALOOKUP l1 = ALOOKUP l2)``,
  simp[EXTENSION] >>
  rw[FUN_EQ_THM] >>
  Cases_on`ALOOKUP l2 x` >- (
    imp_res_tac ALOOKUP_FAILS >>
    imp_res_tac MEM_PERM >>
    fs[FORALL_PROD,MEM_MAP,EXISTS_PROD] >>
    metis_tac[ALOOKUP_FAILS] ) >>
  qmatch_assum_rename_tac`ALOOKUP l2 x = SOME p`[] >>
  imp_res_tac ALOOKUP_MEM >>
  `ALL_DISTINCT (MAP FST l2)` by (
    metis_tac[ALL_DISTINCT_PERM]) >>
  imp_res_tac ALOOKUP_ALL_DISTINCT_MEM >>
  metis_tac[])

val ALL_DISTINCT_PERM_ALOOKUP_ZIP = store_thm("ALL_DISTINCT_PERM_ALOOKUP_ZIP",
  ``∀l1 l2 l3. ALL_DISTINCT (MAP FST l1) ∧ PERM (MAP FST l1) l2
    ⇒ (set l1 = set (ZIP (l2, MAP (THE o ALOOKUP (l1 ++ l3)) l2)))``,
  rw[EXTENSION,FORALL_PROD,EQ_IMP_THM] >- (
    qmatch_assum_rename_tac`MEM (x,y) l1`[] >>
    imp_res_tac PERM_LENGTH >> fs[] >>
    simp[MEM_ZIP] >>
    imp_res_tac MEM_PERM >>
    fs[MEM_MAP,EXISTS_PROD] >>
    `MEM x l2` by metis_tac[] >>
    `∃m. m < LENGTH l2 ∧ (x = EL m l2)` by metis_tac[MEM_EL] >>
    qexists_tac`m`>>simp[]>>
    simp[EL_MAP] >>
    imp_res_tac ALOOKUP_ALL_DISTINCT_MEM >>
    rw[ALOOKUP_APPEND] ) >>
  qmatch_rename_tac`MEM (x,y) l1`[] >>
  imp_res_tac PERM_LENGTH >>
  fs[MEM_ZIP] >>
  simp[EL_MAP] >>
  imp_res_tac MEM_PERM >>
  fs[MEM_EL,GSYM LEFT_FORALL_IMP_THM] >>
  first_x_assum(qspec_then`n`mp_tac) >>
  discharge_hyps >- simp[] >>
  disch_then(Q.X_CHOOSE_THEN`m`strip_assume_tac) >>
  qexists_tac`m` >>
  simp[EL_MAP] >>
  Cases_on`EL m l1`>>simp[ALOOKUP_APPEND] >>
  BasicProvers.CASE_TAC >- (
    imp_res_tac ALOOKUP_FAILS >>
    metis_tac[MEM_EL] ) >>
  metis_tac[MEM_EL,ALOOKUP_ALL_DISTINCT_MEM,optionTheory.THE_DEF])

val PERM_ZIP = store_thm("PERM_ZIP",
  ``∀l1 l2. PERM l1 l2 ⇒ ∀a b c d. (l1 = ZIP(a,b)) ∧ (l2 = ZIP(c,d)) ∧ (LENGTH a = LENGTH b) ∧ (LENGTH c = LENGTH d) ⇒
    PERM a c ∧ PERM b d``,
  ho_match_mp_tac PERM_IND >>
  conj_tac >- (
    Cases >> simp[LENGTH_NIL_SYM] >>
    Cases >> simp[LENGTH_NIL_SYM] >>
    Cases >> simp[LENGTH_NIL_SYM] ) >>
  conj_tac >- (
    Cases >> rpt gen_tac >> strip_tac >>
    Cases>>simp[LENGTH_NIL_SYM] >>
    Cases>>simp[LENGTH_NIL_SYM] >>
    Cases>>simp[LENGTH_NIL_SYM] >>
    Cases>>simp[LENGTH_NIL_SYM] >>
    metis_tac[PERM_MONO]) >>
  conj_tac >- (
    ntac 2 Cases >> rpt gen_tac >> strip_tac >>
    Cases>>simp[LENGTH_NIL_SYM] >>
    Cases>>simp[LENGTH_NIL_SYM] >>
    Cases>>simp[LENGTH_NIL_SYM] >>
    Cases>>simp[LENGTH_NIL_SYM] >>
    strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
    qmatch_assum_rename_tac`LENGTH a = LENGTH b`[] >>
    pop_assum mp_tac >>
    qmatch_assum_rename_tac`LENGTH c = LENGTH d`[] >>
    strip_tac >>
    Cases_on`a`>>fs[LENGTH_NIL_SYM]>>
    Cases_on`b`>>fs[LENGTH_NIL_SYM]>>
    Cases_on`c`>>fs[LENGTH_NIL_SYM]>>
    Cases_on`d`>>fs[LENGTH_NIL_SYM]>>
    metis_tac[PERM_SWAP_AT_FRONT] ) >>
  `∀l. l = ZIP (MAP FST l, MAP SND l)` by (
    simp[ZIP_MAP] >>
    simp[LIST_EQ_REWRITE,EL_MAP] ) >>
  gen_tac >> qx_gen_tac`ll` >>
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  last_x_assum(qspecl_then[`a`,`b`,`MAP FST ll`,`MAP SND ll`]mp_tac) >>
  simp[] >> strip_tac >>
  last_x_assum(qspecl_then[`MAP FST ll`,`MAP SND ll`,`c`,`d`]mp_tac) >>
  simp[] >> strip_tac >>
  metis_tac[PERM_TRANS])

val PERM_BIJ = store_thm("PERM_BIJ",
  ``∀l1 l2. PERM l1 l2 ⇒ ∃f. (BIJ f (count(LENGTH l1)) (count(LENGTH l1)) ∧ (l2 = GENLIST (λi. EL (f i) l1) (LENGTH l1)))``,
  ho_match_mp_tac PERM_IND >> simp[BIJ_EMPTY] >>
  conj_tac >- (
    simp[GENLIST_CONS] >>
    rw[combinTheory.o_DEF] >>
    qexists_tac`λi. case i of 0 => 0 | SUC i => SUC(f i)` >>
    simp[EL_CONS,PRE_SUB1] >>
    fs[BIJ_IFF_INV] >>
    conj_tac >- ( Cases >> simp[] ) >>
    qexists_tac`λi. case i of 0 => 0 | SUC i => SUC(g i)` >>
    conj_tac >- ( Cases >> simp[] ) >>
    conj_tac >- ( Cases >> simp[] ) >>
    ( Cases >> simp[] )) >>
  conj_tac >- (
    simp[GENLIST_CONS] >>
    rw[combinTheory.o_DEF] >>
    qexists_tac`λi. case i of 0 => 1 | SUC 0 => 0 | SUC(SUC n) => SUC(SUC(f n))` >>
    simp[PRE_SUB1,EL_CONS] >>
    REWRITE_TAC[ONE] >> simp[] >>
    fs[BIJ_IFF_INV] >>
    conj_tac >- (Cases >> simp[]>> Cases_on`n`>>simp[]) >>
    qexists_tac`λi. case i of 0 => 1 | SUC 0 => 0 | SUC(SUC n) => SUC(SUC(g n))` >>
    simp[] >>
    conj_tac >- (Cases >> simp[]>> Cases_on`n`>>simp[]) >>
    conj_tac >- (Cases >> simp[]>> TRY(Cases_on`n`)>>simp[] >> REWRITE_TAC[ONE]>>simp[]) >>
    (Cases >> simp[]>> TRY(Cases_on`n`)>>simp[] >> REWRITE_TAC[ONE]>>simp[])) >>
  ntac 2 (rw[LENGTH_GENLIST]) >>
  simp[LIST_EQ_REWRITE,EL_GENLIST] >>
  fs[LENGTH_GENLIST] >>
  qexists_tac`f o f'` >>
  simp[combinTheory.o_DEF] >>
  fs[BIJ_IFF_INV] >>
  qexists_tac`g' o g` >>
  simp[combinTheory.o_DEF] )

val EXISTS_LIST_EQ_MAP = store_thm("EXISTS_LIST_EQ_MAP",
  ``∀ls f. EVERY (λx. ∃y. x = f y) ls ⇒ ∃l. ls = MAP f l``,
  Induct >> simp[] >> rw[] >> res_tac >> qexists_tac`y::l`>>simp[])

val LIST_TO_SET_FLAT = store_thm("LIST_TO_SET_FLAT",
  ``!ls. set (FLAT ls) = BIGUNION (set (MAP set ls))``,
  Induct >> simp[])

val MEM_SING_APPEND = store_thm("MEM_SING_APPEND",
  ``(∀a c. d ≠ a ++ [b] ++ c) ⇔ ¬MEM b d``,
  rw[EQ_IMP_THM] >>
  spose_not_then strip_assume_tac >>
  fs[] >>
  fs[MEM_EL] >>
  first_x_assum(qspecl_then[`TAKE n d`,`DROP (n+1) d`]mp_tac) >>
  lrw[LIST_EQ_REWRITE] >>
  Cases_on`x<n`>>simp[EL_APPEND1,EL_TAKE]>>
  Cases_on`x=n`>>simp[EL_APPEND1,EL_APPEND2,EL_TAKE]>>
  simp[EL_DROP])

val MEM_APPEND_lemma = store_thm("MEM_APPEND_lemma",
  ``∀a b c d x. (a ++ [x] ++ b = c ++ [x] ++ d) ∧ x ∉ set b ∧ x ∉ set a ⇒ (a = c) ∧ (b = d)``,
  rw[APPEND_EQ_APPEND_MID] >> fs[] >>
  fs[APPEND_EQ_SING])

val RTC_RINTER = store_thm("RTC_RINTER",
  ``!R1 R2 x y. RTC (R1 RINTER R2) x y ⇒ ((RTC R1) RINTER (RTC R2)) x y``,
  ntac 2 gen_tac >>
  match_mp_tac RTC_INDUCT >>
  simp[RINTER] >>
  metis_tac[RTC_CASES1] )

val RTC_invariant = store_thm("RTC_invariant",
  ``!R P. (!x y. P x /\ R x y ==> P y) ==> !x y. RTC R x y ==> P x ==> RTC (R RINTER (\x y. P x /\ P y)) x y``,
  rpt gen_tac >> strip_tac >>
  ho_match_mp_tac RTC_INDUCT >>
  rw[] >> res_tac >> fs[] >>
  simp[Once RTC_CASES1] >>
  disj2_tac >>
  HINT_EXISTS_TAC >>
  simp[RINTER])

val RTC_RSUBSET = store_thm("RTC_RSUBSET",
  ``!R1 R2. R1 RSUBSET R2 ==> (RTC R1) RSUBSET (RTC R2)``,
  simp[RSUBSET] >> rpt gen_tac >> strip_tac >>
  ho_match_mp_tac RTC_INDUCT >>
  simp[] >>
  metis_tac[RTC_CASES1])

val EL_LENGTH_APPEND_rwt = store_thm("EL_LENGTH_APPEND_rwt",
  ``¬NULL l2 ∧ (n = LENGTH l1) ⇒  (EL n (l1++l2) = HD l2)``,
  metis_tac[EL_LENGTH_APPEND])

val MAP_FST_funs = store_thm("MAP_FST_funs",
  ``MAP (λ(x,y,z). x) funs = MAP FST funs``,
  lrw[MAP_EQ_f,FORALL_PROD])

val PERM_PART = store_thm("PERM_PART",
  ``∀P L l1 l2 p q. ((p,q) = PART P L l1 l2) ⇒ PERM (L ++ (l1 ++ l2)) (p++q)``,
  GEN_TAC THEN Induct >>
  simp[PART_DEF] >> rw[] >- (
    first_x_assum(qspecl_then[`h::l1`,`l2`,`p`,`q`]mp_tac) >>
    simp[] >>
    REWRITE_TAC[Once CONS_APPEND] >>
    strip_tac >>
    REWRITE_TAC[Once CONS_APPEND] >>
    full_simp_tac std_ss [APPEND_ASSOC] >>
    metis_tac[PERM_REWR,PERM_APPEND] ) >>
  first_x_assum(qspecl_then[`l1`,`h::l2`,`p`,`q`]mp_tac) >>
  simp[] >>
  REWRITE_TAC[Once CONS_APPEND] >>
  strip_tac >>
  REWRITE_TAC[Once CONS_APPEND] >>
  full_simp_tac std_ss [APPEND_ASSOC] >>
  metis_tac[PERM_REWR,PERM_APPEND,APPEND_ASSOC] )

val PERM_PARTITION = store_thm("PERM_PARTITION",
  ``∀P L A B. ((A,B) = PARTITION P L) ==> PERM L (A ++ B)``,
  METIS_TAC[PERM_PART,PARTITION_DEF,APPEND_NIL])

val EVERY2_REVERSE = store_thm("EVERY2_REVERSE",
  ``!R l1 l2. EVERY2 R l1 l2 ==> EVERY2 R (REVERSE l1) (REVERSE l2)``,
  rw[EVERY2_EVERY,EVERY_MEM,FORALL_PROD] >>
  rfs[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM,EL_REVERSE] >>
  first_x_assum match_mp_tac >>
  simp[])

val transitive_LESS = store_thm("transitive_LESS",
  ``transitive ($< : (num->num->bool))``,
  rw[relationTheory.transitive_def] >> PROVE_TAC[LESS_TRANS])
val _ = export_rewrites["transitive_LESS"]

val BIGUNION_IMAGE_set_SUBSET = store_thm("BIGUNION_IMAGE_set_SUBSET",
  ``(BIGUNION (IMAGE f (set ls)) ⊆ s) =
    (∀x. MEM x ls ⇒ f x ⊆ s)``,
  srw_tac[DNF_ss][SUBSET_DEF] >> metis_tac[])

val OPTION_EVERY_def = Define`
  (OPTION_EVERY P NONE = T) /\
  (OPTION_EVERY P (SOME v) = P v)`
val _ = export_rewrites["OPTION_EVERY_def"]
val OPTION_EVERY_cong = store_thm("OPTION_EVERY_cong",
  ``!o1 o2 P1 P2. (o1 = o2) /\ (!x. (o2 = SOME x) ==> (P1 x = P2 x)) ==>
                  (OPTION_EVERY P1 o1 = OPTION_EVERY P2 o2)``,
  Cases THEN SRW_TAC[][] THEN SRW_TAC[][])
val _ = DefnBase.export_cong"OPTION_EVERY_cong"
val OPTION_EVERY_mono = store_thm("OPTION_EVERY_mono",
  ``(!x. P x ==> Q x) ==> OPTION_EVERY P op ==> OPTION_EVERY Q op``,
  Cases_on `op` THEN SRW_TAC[][])
val _ = IndDefLib.export_mono"OPTION_EVERY_mono"

val option_case_NONE_F = store_thm("option_case_NONE_F",
  ``(case X of NONE => F | SOME x => P x) = (∃x. (X = SOME x) ∧ P x)``,
  Cases_on`X`>>rw[])

val IS_PREFIX_THM = store_thm("IS_PREFIX_THM",
 ``!l2 l1. IS_PREFIX l1 l2 <=> (LENGTH l2 <= LENGTH l1) /\ !n. n < LENGTH l2 ==> (EL n l2 = EL n l1)``,
 Induct THEN SRW_TAC[][IS_PREFIX] THEN
 Cases_on`l1`THEN SRW_TAC[][EQ_IMP_THM] THEN1 (
   Cases_on`n`THEN SRW_TAC[][EL_CONS] THEN
   FULL_SIMP_TAC(srw_ss()++ARITH_ss)[] )
 THEN1 (
   POP_ASSUM(Q.SPEC_THEN`0`MP_TAC)THEN SRW_TAC[][] )
 THEN1 (
   FIRST_X_ASSUM(Q.SPEC_THEN`SUC n`MP_TAC)THEN SRW_TAC[][] ))

val SUM_MAP_PLUS = store_thm("SUM_MAP_PLUS",
  ``∀f g ls. SUM (MAP (λx. f x + g x) ls) = SUM (MAP f ls) + SUM (MAP g ls)``,
  ntac 2 gen_tac >> Induct >> simp[])

val TAKE_PRE_LENGTH = store_thm("TAKE_PRE_LENGTH",
  ``!ls. ls <> [] ==> (TAKE (PRE (LENGTH ls)) ls = FRONT ls)``,
  Induct THEN SRW_TAC[][LENGTH_NIL] THEN
  FULL_SIMP_TAC(srw_ss())[FRONT_DEF,PRE_SUB1])

val DROP_LENGTH_NIL_rwt = store_thm("DROP_LENGTH_NIL_rwt",
  ``!l m. (m = LENGTH l) ==> (DROP m l = [])``,
  lrw[DROP_LENGTH_NIL])

val TAKE_LENGTH_ID_rwt = store_thm("TAKE_LENGTH_ID_rwt",
  ``!l m. (m = LENGTH l) ==> (TAKE m l = l)``,
  lrw[TAKE_LENGTH_ID])

val DROP_EL_CONS = store_thm("DROP_EL_CONS",
  ``!ls n. n < LENGTH ls ==> (DROP n ls = EL n ls :: DROP (n + 1) ls)``,
  Induct >> lrw[EL_CONS,PRE_SUB1])

val TAKE_EL_SNOC = store_thm("TAKE_EL_SNOC",
  ``!ls n. n < LENGTH ls ==> (TAKE (n + 1) ls = SNOC (EL n ls) (TAKE n ls))``,
  HO_MATCH_MP_TAC SNOC_INDUCT >>
  CONJ_TAC THEN1 SRW_TAC[][] THEN
  REPEAT STRIP_TAC THEN
  Cases_on`n = LENGTH ls` THEN1 (
    lrw[EL_LENGTH_SNOC,TAKE_SNOC,TAKE_APPEND1,EL_APPEND1,EL_APPEND2,TAKE_APPEND2] ) THEN
  `n < LENGTH ls` by fsrw_tac[ARITH_ss][ADD1] THEN
  lrw[TAKE_SNOC,TAKE_APPEND1,EL_APPEND1])

val ZIP_DROP = store_thm("ZIP_DROP",
  ``!a b n. n <= LENGTH a /\ (LENGTH a = LENGTH b) ==>
      (ZIP (DROP n a,DROP n b) = DROP n (ZIP (a,b)))``,
  Induct THEN SRW_TAC[][LENGTH_NIL_SYM,ADD1] THEN
  Cases_on`b` THEN FULL_SIMP_TAC(srw_ss())[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  FULL_SIMP_TAC(srw_ss()++ARITH_ss)[])

val EVERY2_DROP = store_thm("EVERY2_DROP",
  ``∀R l1 l2 n. EVERY2 R l1 l2 ∧ n <= LENGTH l1 ==> EVERY2 R (DROP n l1) (DROP n l2)``,
  rw[EVERY2_EVERY,ZIP_DROP] >>
  match_mp_tac (MP_CANON EVERY_DROP) >>
  rw[] >> PROVE_TAC[])

val REVERSE_DROP = store_thm("REVERSE_DROP",
  ``!ls n. n <= LENGTH ls ==> (REVERSE (DROP n ls) = REVERSE (LASTN (LENGTH ls - n) ls))``,
  HO_MATCH_MP_TAC SNOC_INDUCT THEN
  SRW_TAC[][LASTN] THEN
  Cases_on`n = SUC (LENGTH ls)` THEN1 (
    lrw[DROP_LENGTH_NIL_rwt,ADD1,LASTN] ) THEN
  lrw[DROP_APPEND1,LASTN_APPEND1])

val FUPDATE_LIST_CANCEL = store_thm("FUPDATE_LIST_CANCEL",
  ``!ls1 fm ls2.
    (!k. MEM k (MAP FST ls1) ==> MEM k (MAP FST ls2))
    ==> (fm |++ ls1 |++ ls2 = fm |++ ls2)``,
  Induct THEN SRW_TAC[][FUPDATE_LIST_THM] THEN
  Cases_on`h` THEN
  MATCH_MP_TAC FUPDATE_FUPDATE_LIST_MEM THEN
  FULL_SIMP_TAC(srw_ss())[])

val FUPDATE_EQ_FUNION = store_thm("FUPDATE_EQ_FUNION",
  ``∀fm kv. fm |+ kv = (FEMPTY |+ kv) ⊌ fm``,
  gen_tac >> Cases >>
  simp[GSYM fmap_EQ_THM,FDOM_FUPDATE,FAPPLY_FUPDATE_THM,FUNION_DEF] >>
  simp[EXTENSION])

val GENLIST_EL = store_thm("GENLIST_EL",
  ``!ls f n. (n = LENGTH ls) /\ (!i. i < n ==> (f i = EL i ls)) ==>
             (GENLIST f n = ls)``,
  lrw[LIST_EQ_REWRITE])

val fmap_rel_OPTREL_FLOOKUP = store_thm("fmap_rel_OPTREL_FLOOKUP",
  ``fmap_rel R f1 f2 = ∀k. OPTREL R (FLOOKUP f1 k) (FLOOKUP f2 k)``,
  rw[fmap_rel_def,optionTheory.OPTREL_def,FLOOKUP_DEF,EXTENSION] >>
  PROVE_TAC[])

val FUPDATE_LIST_APPEND_COMMUTES = store_thm("FUPDATE_LIST_APPEND_COMMUTES",
  ``!l1 l2 fm. DISJOINT (set (MAP FST l1)) (set (MAP FST l2)) ⇒ (fm |++ l1 |++ l2 = fm |++ l2 |++ l1)``,
  Induct >- rw[FUPDATE_LIST_THM] >>
  Cases >> rw[FUPDATE_LIST_THM] >>
  metis_tac[FUPDATE_FUPDATE_LIST_COMMUTES])

val LENGTH_FILTER_LESS = store_thm("LENGTH_FILTER_LESS",
  ``!P ls. EXISTS ($~ o P) ls ==> LENGTH (FILTER P ls) < LENGTH ls``,
  GEN_TAC THEN Induct THEN SRW_TAC[][] THEN
  MATCH_MP_TAC LESS_EQ_IMP_LESS_SUC THEN
  MATCH_ACCEPT_TAC LENGTH_FILTER_LEQ)

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

val EVERY2_LUPDATE_same = store_thm("EVERY2_LUPDATE_same",
  ``!P l1 l2 v1 v2 n. P v1 v2 /\ EVERY2 P l1 l2 ==>
    EVERY2 P (LUPDATE v1 n l1) (LUPDATE v2 n l2)``,
  GEN_TAC THEN Induct THEN
  SRW_TAC[][LUPDATE_def] THEN
  Cases_on`n`THEN SRW_TAC[][LUPDATE_def] THEN
  Cases_on`l2`THEN FULL_SIMP_TAC(srw_ss())[LUPDATE_def])

val EVERY2_refl = store_thm("EVERY2_refl",
  ``(!x. MEM x ls ==> R x x) ==> (EVERY2 R ls ls)``,
  Induct_on`ls` >>rw[])

val EVERY2_APPEND = store_thm("EVERY2_APPEND",
  ``EVERY2 R l1 l2 /\ EVERY2 R l3 l4 <=> EVERY2 R (l1 ++ l3) (l2 ++ l4) /\ (LENGTH l1 = LENGTH l2) /\ (LENGTH l3 = LENGTH l4)``,
  rw[EVERY2_EVERY,EVERY_MEM] >>
  metis_tac[ZIP_APPEND,MEM_APPEND])

val EVERY2_APPEND_suff = store_thm("EVERY2_APPEND_suff",
  ``EVERY2 R l1 l2 ∧ EVERY2 R l3 l4 ⇒ EVERY2 R (l1 ++ l3) (l2 ++ l4)``,
  metis_tac[EVERY2_APPEND])

val EVERY2_THM = store_thm("EVERY2_THM",
  ``(!P ys. EVERY2 P [] ys = (ys = [])) /\
    (!P yys x xs. EVERY2 P (x::xs) yys = ?y ys. (yys = y::ys) /\ (P x y) /\ (EVERY2 P xs ys)) /\
    (!P xs. EVERY2 P xs [] = (xs = [])) /\
    (!P xxs y ys. EVERY2 P xxs (y::ys) = ?x xs. (xxs = x::xs) /\ (P x y) /\ (EVERY2 P xs ys))``,
  REPEAT CONJ_TAC THEN GEN_TAC THEN TRY (
    SRW_TAC[][EVERY2_EVERY,LENGTH_NIL] THEN
    SRW_TAC[][EQ_IMP_THM] THEN NO_TAC ) THEN
  Cases THEN SRW_TAC[][EVERY2_EVERY])
val _ = export_rewrites["EVERY2_THM"]

val LIST_REL_trans = store_thm("LIST_REL_trans",
  ``∀l1 l2 l3. (∀n. n < LENGTH l1 ∧ R (EL n l1) (EL n l2) ∧ R (EL n l2) (EL n l3) ⇒ R (EL n l1) (EL n l3)) ∧
      LIST_REL R l1 l2 ∧ LIST_REL R l2 l3 ⇒ LIST_REL R l1 l3``,
  Induct >> simp[] >> rw[] >> fs[] >> rw[] >- (
    first_x_assum(qspec_then`0`mp_tac)>>rw[] ) >>
  first_x_assum match_mp_tac >>
  qexists_tac`ys` >> rw[] >>
  first_x_assum(qspec_then`SUC n`mp_tac)>>simp[])

val LIST_REL_APPEND_SING = store_thm("LIST_REL_APPEND_SING",
  ``LIST_REL R (l1 ++ [x1]) (l2 ++ [x2]) ⇔
    LIST_REL R l1 l2 ∧ R x1 x2``,
  rw[EQ_IMP_THM] >> TRY (
    match_mp_tac EVERY2_APPEND_suff >> simp[]) >>
  imp_res_tac EVERY2_APPEND >> fs[])
val _ = export_rewrites["LIST_REL_APPEND_SING"]

val LUPDATE_APPEND2 = store_thm("LUPDATE_APPEND2",
  ``∀l1 l2 n x. LENGTH l1 ≤ n ⇒ (LUPDATE x n (l1 ++ l2) = l1 ++ (LUPDATE x (n-LENGTH l1) l2))``,
  rw[] >> simp[LIST_EQ_REWRITE] >>
  qx_gen_tac`z` >>
  simp[EL_LUPDATE] >> rw[] >>
  simp[EL_APPEND2,EL_LUPDATE] >> fs[] >>
  Cases_on`z < LENGTH l1`>>fs[]>>
  simp[EL_APPEND1,EL_APPEND2,EL_LUPDATE])

val LUPDATE_APPEND1 = store_thm("LUPDATE_APPEND1",
  ``∀l1 l2 n x. n < LENGTH l1 ⇒ (LUPDATE x n (l1 ++ l2) = (LUPDATE x n l1) ++ l2)``,
  rw[] >> simp[LIST_EQ_REWRITE] >>
  qx_gen_tac`z` >>
  simp[EL_LUPDATE] >> rw[] >>
  simp[EL_APPEND2,EL_LUPDATE] >> fs[] >>
  Cases_on`z < LENGTH l1`>>fs[]>>
  simp[EL_APPEND1,EL_APPEND2,EL_LUPDATE])

val LUPDATE_MAP = store_thm("LUPDATE_MAP",
``!x n l f. MAP f (LUPDATE x n l) = LUPDATE (f x) n (MAP f l)``,
 Induct_on `l` >> rw [LUPDATE_def] >> Cases_on `n` >> fs [LUPDATE_def])

val SWAP_REVERSE = store_thm("SWAP_REVERSE",
  ``!l1 l2. (l1 = REVERSE l2) = (l2 = REVERSE l1)``,
  SRW_TAC[][EQ_IMP_THM])

val SWAP_REVERSE_SYM = store_thm("SWAP_REVERSE_SYM",
  ``!l1 l2. (REVERSE l1 = l2) = (l1 = REVERSE l2)``,
  metis_tac[SWAP_REVERSE])

val EVERY2_RC_same = store_thm("EVERY2_RC_same",
  ``EVERY2 (RC R) l l``,
  srw_tac[DNF_ss][EVERY2_EVERY,EVERY_MEM,MEM_ZIP,relationTheory.RC_DEF])
val _ = export_rewrites["EVERY2_RC_same"]

val CARD_UNION_LE = store_thm("CARD_UNION_LE",
  ``FINITE s ∧ FINITE t ⇒ CARD (s ∪ t) ≤ CARD s + CARD t``,
  rw[] >> imp_res_tac CARD_UNION >> fsrw_tac[ARITH_ss][])

val IMAGE_SUBSET_gen = store_thm("IMAGE_SUBSET_gen",
  ``∀f s u t. s ⊆ u ∧ (IMAGE f u ⊆ t) ⇒ IMAGE f s ⊆ t``,
  simp[SUBSET_DEF] >> metis_tac[])

val FLOOKUP_DRESTRICT = store_thm("FLOOKUP_DRESTRICT",
  ``!fm s k. FLOOKUP (DRESTRICT fm s) k = if k IN s then FLOOKUP fm k else NONE``,
  SRW_TAC[][FLOOKUP_DEF,DRESTRICT_DEF] THEN FULL_SIMP_TAC std_ss [])

val IMAGE_EL_count_LENGTH = store_thm("IMAGE_EL_count_LENGTH",
  ``∀f ls. IMAGE (λn. f (EL n ls)) (count (LENGTH ls)) = IMAGE f (set ls)``,
  rw[EXTENSION,MEM_EL] >> PROVE_TAC[])

val GENLIST_EL_MAP = store_thm("GENLIST_EL_MAP",
  ``!f ls. GENLIST (λn. f (EL n ls)) (LENGTH ls) = MAP f ls``,
  gen_tac >> Induct >> rw[GENLIST_CONS,combinTheory.o_DEF])

val LENGTH_FILTER_LEQ_MONO = store_thm("LENGTH_FILTER_LEQ_MONO",
  ``!P Q. (!x. P x ==> Q x) ==> !ls. (LENGTH (FILTER P ls) <= LENGTH (FILTER Q ls))``,
  rpt gen_tac >> strip_tac >>
  Induct >> rw[] >>
  fsrw_tac[ARITH_ss][] >>
  PROVE_TAC[])

val CARD_REST = store_thm("CARD_REST",
  ``!s. FINITE s /\ s <> {} ==> (CARD (REST s) = CARD s - 1)``,
  SRW_TAC[][] THEN
  IMP_RES_TAC CHOICE_INSERT_REST THEN
  POP_ASSUM (fn th => CONV_TAC (RAND_CONV (REWRITE_CONV [Once(SYM th)]))) THEN
  Q.SPEC_THEN`REST s`MP_TAC CARD_INSERT THEN SRW_TAC[][] THEN
  FULL_SIMP_TAC(srw_ss())[REST_DEF])

val LIST_EQ_MAP_PAIR = store_thm("LIST_EQ_MAP_PAIR",
  ``!l1 l2. (MAP FST l1 = MAP FST l2) /\ (MAP SND l1 = MAP SND l2) ==> (l1 = l2)``,
  SRW_TAC[][MAP_EQ_EVERY2,EVERY2_EVERY,EVERY_MEM,LIST_EQ_REWRITE,FORALL_PROD] THEN
  REV_FULL_SIMP_TAC (srw_ss()++DNF_ss) [MEM_ZIP] THEN
  METIS_TAC[pair_CASES,PAIR_EQ])

val FUPDATE_LIST_ALL_DISTINCT_PERM = store_thm("FUPDATE_LIST_ALL_DISTINCT_PERM",
  ``!ls ls' fm. ALL_DISTINCT (MAP FST ls) /\ PERM ls ls' ==> (fm |++ ls = fm |++ ls')``,
  Induct >> rw[] >>
  fs[sortingTheory.PERM_CONS_EQ_APPEND] >>
  rw[FUPDATE_LIST_THM] >>
  PairCases_on`h` >> fs[] >>
  imp_res_tac FUPDATE_FUPDATE_LIST_COMMUTES >>
  match_mp_tac EQ_TRANS >>
  qexists_tac `(fm |++ (M ++ N)) |+ (h0,h1)` >>
  conj_tac >- metis_tac[sortingTheory.ALL_DISTINCT_PERM,sortingTheory.PERM_MAP] >>
  rw[FUPDATE_LIST_APPEND] >>
  `h0 ∉ set (MAP FST N)` by metis_tac[sortingTheory.PERM_MEM_EQ,MEM_MAP,MEM_APPEND] >>
  imp_res_tac FUPDATE_FUPDATE_LIST_COMMUTES >>
  rw[FUPDATE_LIST_THM])

val ALL_DISTINCT_MEM_ZIP_MAP = store_thm("ALL_DISTINCT_MEM_ZIP_MAP",
  ``!f x ls. ALL_DISTINCT ls ==> (MEM x (ZIP (ls, MAP f ls)) <=> MEM (FST x) ls /\ (SND x = f (FST x)))``,
  GEN_TAC THEN Cases THEN
  SRW_TAC[][MEM_ZIP,FORALL_PROD] THEN
  SRW_TAC[][EQ_IMP_THM] THEN
  SRW_TAC[][EL_MAP,MEM_EL] THEN
  FULL_SIMP_TAC (srw_ss()) [EL_ALL_DISTINCT_EL_EQ,MEM_EL] THEN
  METIS_TAC[EL_MAP])

val IMAGE_FRANGE = store_thm("IMAGE_FRANGE",
  ``!f fm. IMAGE f (FRANGE fm) = FRANGE (f o_f fm)``,
  SRW_TAC[][EXTENSION] THEN
  EQ_TAC THEN1 PROVE_TAC[o_f_FRANGE] THEN
  SRW_TAC[][FRANGE_DEF] THEN
  SRW_TAC[][o_f_FAPPLY] THEN
  PROVE_TAC[])

val SUBMAP_mono_FUPDATE = store_thm("SUBMAP_mono_FUPDATE",
  ``!f g x y. f \\ x SUBMAP g \\ x ==> f |+ (x,y) SUBMAP g |+ (x,y)``,
  SRW_TAC[][SUBMAP_FUPDATE])

val SUBMAP_DOMSUB_gen = store_thm("SUBMAP_DOMSUB_gen",
  ``!f g k. f \\ k SUBMAP g <=> f \\ k SUBMAP g \\ k``,
  SRW_TAC[][SUBMAP_DEF,EQ_IMP_THM,DOMSUB_FAPPLY_THM])

val DOMSUB_SUBMAP = store_thm("DOMSUB_SUBMAP",
  ``!f g x. f SUBMAP g /\ x NOTIN FDOM f ==> f SUBMAP g \\ x``,
  SRW_TAC[][SUBMAP_DEF,DOMSUB_FAPPLY_THM] THEN
  SRW_TAC[][] THEN METIS_TAC[])

val DRESTRICT_DOMSUB = store_thm("DRESTRICT_DOMSUB",
  ``!f s k. DRESTRICT f s \\ k = DRESTRICT f (s DELETE k)``,
  SRW_TAC[][GSYM fmap_EQ_THM,FDOM_DRESTRICT] THEN1 (
    SRW_TAC[][EXTENSION] THEN METIS_TAC[] ) THEN
  SRW_TAC[][DOMSUB_FAPPLY_THM] THEN
  SRW_TAC[][DRESTRICT_DEF])

val fmap_rel_trans = store_thm("fmap_rel_trans",
  ``(!x y z. R x y /\ R y z ==> R x z) ==>
    !x y z. fmap_rel R x y /\ fmap_rel R y z ==>
              fmap_rel R x z``,
  SRW_TAC[][fmap_rel_def] THEN METIS_TAC[])

val fmap_rel_sym = store_thm("fmap_rel_sym",
  ``(!x y. R x y ==> R y x) ==>
    !x y. fmap_rel R x y ==> fmap_rel R y x``,
  SRW_TAC[][fmap_rel_def])

val FOLDL_invariant = store_thm("FOLDL_invariant",
  ``!P f ls a. (P a) /\ (!x y . MEM y ls /\ P x ==> P (f x y)) ==> P (FOLDL f a ls)``,
  NTAC 2 GEN_TAC THEN
  Induct THEN SRW_TAC[][])

val FOLDL_invariant_rest = store_thm("FOLDL_invariant_rest",
  ``∀P f ls a. P ls a ∧ (∀x n. n < LENGTH ls ∧ P (DROP n ls) x ⇒ P (DROP (SUC n) ls) (f x (EL n ls))) ⇒ P [] (FOLDL f a ls)``,
  ntac 2 gen_tac >>
  Induct >> rw[] >>
  first_x_assum match_mp_tac >>
  conj_tac >- (
    first_x_assum (qspecl_then[`a`,`0`] mp_tac) >> rw[] ) >>
  rw[] >> first_x_assum (qspecl_then[`x`,`SUC n`] mp_tac) >> rw[])

val between_def = Define`
  between x y z ⇔ x:num ≤ z ∧ z < y`

val TAKE_SUM = store_thm("TAKE_SUM",
  ``!n m l. n + m <= LENGTH l ==> (TAKE (n + m) l = TAKE n l ++ TAKE m (DROP n l))``,
  Induct_on `l` THEN SRW_TAC[][] THEN SRW_TAC[][] THEN
  Cases_on `n` THEN FULL_SIMP_TAC(srw_ss()++ARITH_ss)[ADD1])

val ALL_DISTINCT_FILTER_EL_IMP = store_thm("ALL_DISTINCT_FILTER_EL_IMP",
  ``!P l n1 n2. ALL_DISTINCT (FILTER P l) /\
    n1 < LENGTH l /\ n2 < LENGTH l /\
    (P (EL n1 l)) /\ (EL n1 l = EL n2 l) ==> (n1 = n2)``,
  GEN_TAC THEN Induct THEN1 SRW_TAC[][] THEN
  SRW_TAC[][] THEN FULL_SIMP_TAC(srw_ss())[MEM_FILTER]
  THEN1 PROVE_TAC[] THEN
  Cases_on `n1` THEN Cases_on `n2` THEN
  FULL_SIMP_TAC(srw_ss())[MEM_EL] THEN
  PROVE_TAC[] )

val SUC_LEAST = store_thm("SUC_LEAST",
  ``!x. P x ==> (SUC ($LEAST P) = LEAST x. 0 < x /\ P (PRE x))``,
  GEN_TAC THEN STRIP_TAC THEN
  numLib.LEAST_ELIM_TAC THEN
  STRIP_TAC THEN1 PROVE_TAC[] THEN
  numLib.LEAST_ELIM_TAC THEN
  STRIP_TAC THEN1 (
    Q.EXISTS_TAC `SUC x` THEN
    SRW_TAC[][] ) THEN
  Q.X_GEN_TAC`nn` THEN
  STRIP_TAC THEN
  Q.X_GEN_TAC`m` THEN
  `?n. nn = SUC n` by ( Cases_on `nn` THEN SRW_TAC[][] THEN DECIDE_TAC ) THEN
  SRW_TAC[][] THEN
  FULL_SIMP_TAC(srw_ss())[] THEN
  `~(n < m)` by PROVE_TAC[] THEN
  `~(SUC m < SUC n)` by (
    SPOSE_NOT_THEN STRIP_ASSUME_TAC THEN
    RES_TAC THEN
    FULL_SIMP_TAC(srw_ss())[] ) THEN
  DECIDE_TAC)

val fmap_linv_def = Define`
  fmap_linv f1 f2 ⇔ (FDOM f2 = FRANGE f1) /\ (!x. x IN FDOM f1 ==> (FLOOKUP f2 (FAPPLY f1 x) = SOME x))`

val fmap_linv_unique = store_thm("fmap_linv_unique",
  ``!f f1 f2. fmap_linv f f1 /\ fmap_linv f f2 ==> (f1 = f2)``,
  SRW_TAC[][fmap_linv_def,GSYM fmap_EQ_THM] THEN
  FULL_SIMP_TAC(srw_ss())[FRANGE_DEF,FLOOKUP_DEF] THEN
  PROVE_TAC[])

val INJ_has_fmap_linv = store_thm("INJ_has_fmap_linv",
  ``INJ (FAPPLY f) (FDOM f) (FRANGE f) ==> ?g. fmap_linv f g``,
  STRIP_TAC THEN
  Q.EXISTS_TAC `FUN_FMAP (\x. @y. FLOOKUP f y = SOME x) (FRANGE f)` THEN
  SRW_TAC[][fmap_linv_def,FLOOKUP_FUN_FMAP,FRANGE_DEF] THEN1 PROVE_TAC[] THEN
  SELECT_ELIM_TAC THEN
  FULL_SIMP_TAC (srw_ss()) [INJ_DEF,FRANGE_DEF,FLOOKUP_DEF])

val has_fmap_linv_inj = store_thm("has_fmap_linv_inj",
  ``(?g. fmap_linv f g) = (INJ (FAPPLY f) (FDOM f) (FRANGE f))``,
  Tactical.REVERSE EQ_TAC THEN1 PROVE_TAC[INJ_has_fmap_linv] THEN
  SRW_TAC[][fmap_linv_def,INJ_DEF,EQ_IMP_THM]
  THEN1 ( SRW_TAC[][FRANGE_DEF] THEN PROVE_TAC[] )
  THEN1 ( FULL_SIMP_TAC(srw_ss())[FLOOKUP_DEF] THEN PROVE_TAC[] ))

val fmap_linv_FAPPLY = store_thm("fmap_linv_FAPPLY",
  ``fmap_linv f g /\ x IN FDOM f ==> (g ' (f ' x) = x)``,
  SRW_TAC[][fmap_linv_def,FLOOKUP_DEF])

val FLAT_EQ_NIL = store_thm("FLAT_EQ_NIL",
  ``!ls. (FLAT ls = []) = (EVERY ($= []) ls)``,
  Induct THEN SRW_TAC[][EQ_IMP_THM])

val ALL_DISTINCT_MAP_INJ = store_thm("ALL_DISTINCT_MAP_INJ",
  ``!ls f. (!x y. MEM x ls /\ MEM y ls /\ (f x = f y) ==> (x = y)) /\ ALL_DISTINCT ls  ==> ALL_DISTINCT (MAP f ls)``,
  Induct THEN SRW_TAC[][MEM_MAP] THEN PROVE_TAC[])

val o_f_cong = store_thm("o_f_cong",
  ``!f fm f' fm'.
    (fm = fm') /\
    (!v. v IN FRANGE fm ==> (f v = f' v))
    ==> (f o_f fm = f' o_f fm')``,
  SRW_TAC[DNF_ss][GSYM fmap_EQ_THM,FRANGE_DEF])
val _ = DefnBase.export_cong"o_f_cong"

val DRESTRICT_SUBSET_SUBMAP_gen = store_thm("DRESTRICT_SUBSET_SUBMAP_gen",
  ``!f1 f2 s t. DRESTRICT f1 s ⊑ DRESTRICT f2 s ∧ t ⊆ s
    ==> DRESTRICT f1 t ⊑ DRESTRICT f2 t``,
  rw[SUBMAP_DEF,DRESTRICT_DEF,SUBSET_DEF])

val SUBSET_DIFF_EMPTY = store_thm("SUBSET_DIFF_EMPTY",
  ``!s t. (s DIFF t = {}) = (s SUBSET t)``,
  SRW_TAC[][EXTENSION,SUBSET_DEF] THEN PROVE_TAC[])

val DIFF_INTER_SUBSET = store_thm("DIFF_INTER_SUBSET",
  ``!r s t. r SUBSET s ==> (r DIFF s INTER t = r DIFF t)``,
  SRW_TAC[][EXTENSION,SUBSET_DEF] THEN PROVE_TAC[])

val UNION_DIFF_2 = store_thm("UNION_DIFF_2",
  ``!s t. (s UNION (s DIFF t) = s)``,
  SRW_TAC[][EXTENSION] THEN PROVE_TAC[])

val DRESTRICT_FUNION_SAME = store_thm("DRESTRICT_FUNION_SAME",
  ``!fm s. FUNION (DRESTRICT fm s) fm = fm``,
  SRW_TAC[][GSYM SUBMAP_FUNION_ABSORPTION])

val REVERSE_ZIP = store_thm("REVERSE_ZIP",
  ``!l1 l2. (LENGTH l1 = LENGTH l2) ==>
    (REVERSE (ZIP (l1,l2)) = ZIP (REVERSE l1, REVERSE l2))``,
  Induct THEN SRW_TAC[][LENGTH_NIL_SYM] THEN
  Cases_on `l2` THEN FULL_SIMP_TAC(srw_ss())[] THEN
  SRW_TAC[][GSYM ZIP_APPEND])

val EVERY2_REVERSE1 = store_thm("EVERY2_REVERSE1",
  ``∀l1 l2. EVERY2 R l1 (REVERSE l2) ⇔ EVERY2 R (REVERSE l1) l2``,
  rpt gen_tac >> EQ_TAC >>
  simp[EVERY2_EVERY] >> rpt strip_tac >>
  ONCE_REWRITE_TAC[GSYM EVERY_REVERSE] >>
  simp[REVERSE_ZIP])

val LENGTH_o_REVERSE = store_thm("LENGTH_o_REVERSE",
  ``(LENGTH o REVERSE = LENGTH) /\
    (LENGTH o REVERSE o f = LENGTH o f)``,
  SRW_TAC[][FUN_EQ_THM])

val REVERSE_o_REVERSE = store_thm("REVERSE_o_REVERSE",
  ``(REVERSE o REVERSE o f = f)``,
  SRW_TAC[][FUN_EQ_THM])

val GENLIST_PLUS_APPEND = store_thm("GENLIST_PLUS_APPEND",
  ``GENLIST ($+ a) n1 ++ GENLIST ($+ (n1 + a)) n2 = GENLIST ($+ a) (n1 + n2)``,
  rw[Once ADD_SYM,SimpRHS] >>
  srw_tac[ARITH_ss][GENLIST_APPEND] >>
  srw_tac[ETA_ss][ADD_ASSOC])

val count_add = store_thm("count_add",
  ``!n m. count (n + m) = count n UNION IMAGE ($+ n) (count m)``,
  SRW_TAC[ARITH_ss][EXTENSION,EQ_IMP_THM] THEN
  Cases_on `x < n` THEN SRW_TAC[ARITH_ss][] THEN
  Q.EXISTS_TAC `x - n` THEN
  SRW_TAC[ARITH_ss][])

val plus_compose = store_thm("plus_compose",
  ``!n:num m. $+ n o $+ m = $+ (n + m)``,
  SRW_TAC[ARITH_ss][FUN_EQ_THM])

val LIST_TO_SET_GENLIST = store_thm("LIST_TO_SET_GENLIST",
  ``!f n. LIST_TO_SET (GENLIST f n) = IMAGE f (count n)``,
  SRW_TAC[][EXTENSION,MEM_GENLIST] THEN PROVE_TAC[])

val DRESTRICT_EQ_DRESTRICT_SAME = store_thm("DRESTRICT_EQ_DRESTRICT_SAME",
  ``(DRESTRICT f1 s = DRESTRICT f2 s) ⇔
    (s INTER FDOM f1 = s INTER FDOM f2) /\
    (!x. x IN FDOM f1 /\ x IN s ==> (f1 ' x = f2 ' x))``,
  SRW_TAC[][DRESTRICT_EQ_DRESTRICT,SUBMAP_DEF,DRESTRICT_DEF,EXTENSION] THEN
  PROVE_TAC[])

val MEM_ZIP_MEM_MAP = store_thm("MEM_ZIP_MEM_MAP",
  ``(LENGTH (FST ps) = LENGTH (SND ps)) /\ MEM p (ZIP ps)
    ==> MEM (FST p) (FST ps) /\ MEM (SND p) (SND ps)``,
  Cases_on `p` >> Cases_on `ps` >> SRW_TAC[][] >>
  REV_FULL_SIMP_TAC(srw_ss())[MEM_ZIP,MEM_EL] THEN
  PROVE_TAC[])

val DISJOINT_GENLIST_PLUS = store_thm("DISJOINT_GENLIST_PLUS",
  ``DISJOINT x (set (GENLIST ($+ n) (a + b))) ==>
    DISJOINT x (set (GENLIST ($+ n) a)) /\
    DISJOINT x (set (GENLIST ($+ (n + a)) b))``,
  rw[GSYM GENLIST_PLUS_APPEND] >>
  metis_tac[DISJOINT_SYM,ADD_SYM])

(* TODO: use for Cevaluate_any_env?*)
val DRESTRICT_FUNION_SUBSET = store_thm("DRESTRICT_FUNION_SUBSET",
  ``s2 ⊆ s1 ⇒ ∃h. (DRESTRICT f s1 ⊌ g = DRESTRICT f s2 ⊌ h)``,
  strip_tac >>
  qexists_tac `DRESTRICT f s1 ⊌ g` >>
  match_mp_tac EQ_SYM >>
  REWRITE_TAC[GSYM SUBMAP_FUNION_ABSORPTION] >>
  rw[SUBMAP_DEF,DRESTRICT_DEF,FUNION_DEF] >>
  fs[SUBSET_DEF])

(* TODO: move elsewhere? export as rewrite? *)
val IN_option_rwt = store_thm(
"IN_option_rwt",
``(x ∈ case opt of NONE => {} | SOME y => Q y) ⇔
  (∃y. (opt = SOME y) ∧ x ∈ Q y)``,
Cases_on `opt` >> rw[EQ_IMP_THM])

val IN_option_rwt2 = store_thm(
"IN_option_rwt2",
``x ∈ option_CASE opt {} s ⇔ ∃y. (opt = SOME y) ∧ x ∈ s y``,
Cases_on `opt` >> rw[])

(* Re-expressing folds *)

val FOLDL2_FUPDATE_LIST = store_thm(
"FOLDL2_FUPDATE_LIST",
``!f1 f2 bs cs a. (LENGTH bs = LENGTH cs) ⇒
  (FOLDL2 (λfm b c. fm |+ (f1 b c, f2 b c)) a bs cs =
   a |++ ZIP (MAP2 f1 bs cs, MAP2 f2 bs cs))``,
SRW_TAC[][FUPDATE_LIST,FOLDL2_FOLDL,MAP2_MAP,ZIP_MAP,MAP_ZIP,
          rich_listTheory.FOLDL_MAP,rich_listTheory.LENGTH_MAP2,
          LENGTH_ZIP,pairTheory.LAMBDA_PROD])

val FOLDL2_FUPDATE_LIST_paired = store_thm(
"FOLDL2_FUPDATE_LIST_paired",
``!f1 f2 bs cs a. (LENGTH bs = LENGTH cs) ⇒
  (FOLDL2 (λfm b (c,d). fm |+ (f1 b c d, f2 b c d)) a bs cs =
   a |++ ZIP (MAP2 (λb. UNCURRY (f1 b)) bs cs, MAP2 (λb. UNCURRY (f2 b)) bs cs))``,
rw[FOLDL2_FOLDL,MAP2_MAP,ZIP_MAP,MAP_ZIP,LENGTH_ZIP,
   pairTheory.UNCURRY,pairTheory.LAMBDA_PROD,FUPDATE_LIST,
   rich_listTheory.FOLDL_MAP])

val FOLDR_CONS_triple = store_thm(
"FOLDR_CONS_triple",
``!f ls a. FOLDR (\(x,y,z) w. f x y z :: w) a ls = (MAP (\(x,y,z). f x y z) ls)++a``,
GEN_TAC THEN
Induct THEN1 SRW_TAC[][] THEN
Q.X_GEN_TAC `p` THEN
PairCases_on `p` THEN
SRW_TAC[][])

val FOLDR_CONS_5tup = store_thm(
"FOLDR_CONS_5tup",
``!f ls a. FOLDR (\(c,d,x,y,z) w. f c d x y z :: w) a ls = (MAP (\(c,d,x,y,z). f c d x y z) ls)++a``,
GEN_TAC THEN
Induct THEN1 SRW_TAC[][] THEN
Q.X_GEN_TAC `p` THEN
PairCases_on `p` THEN
SRW_TAC[][])

val FOLDR_transitive_property = store_thm(
"FOLDR_transitive_property",
``!P ls f a. P [] a /\ (!n a. n < LENGTH ls /\ P (DROP (SUC n) ls) a ==> P (DROP n ls) (f (EL n ls) a)) ==> P ls (FOLDR f a ls)``,
GEN_TAC THEN Induct THEN SRW_TAC[][] THEN
`P ls (FOLDR f a ls)` by (
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  SRW_TAC[][] THEN
  Q.MATCH_ASSUM_RENAME_TAC `P (DROP (SUC n) ls) b` [] THEN
  FIRST_X_ASSUM (Q.SPECL_THEN [`SUC n`,`b`] MP_TAC) THEN
  SRW_TAC[][] ) THEN
FIRST_X_ASSUM (Q.SPEC_THEN `0` MP_TAC) THEN
SRW_TAC[][])

(* Re-expressing curried lambdas *)

val FST_triple = store_thm(
"FST_triple",
``(λ(n,ns,b). n) = FST``,
rw[FUN_EQ_THM,pairTheory.UNCURRY])

val FST_5tup = store_thm(
"FST_5tup",
``(λ(n,ns,b,x,y). n) = FST``,
rw[FUN_EQ_THM,pairTheory.UNCURRY])

val SND_triple = store_thm(
"SND_triple",
``(λ(n,ns,b). f ns b) = UNCURRY f o SND``,
rw[FUN_EQ_THM,pairTheory.UNCURRY])

val FST_pair = store_thm(
"FST_pair",
``(λ(n,v). n) = FST``,
rw[FUN_EQ_THM,pairTheory.UNCURRY])

val SND_pair = store_thm(
"SND_pair",
``(λ(n,v). v) = SND``,
rw[FUN_EQ_THM,pairTheory.UNCURRY])

val SND_FST_pair = store_thm(
"SND_FST_pair",
``(λ((n,m),c).m) = SND o FST``,
rw[FUN_EQ_THM,pairTheory.UNCURRY])

val MAP_ZIP_SND_triple = store_thm(
"MAP_ZIP_SND_triple",
``(LENGTH l1 = LENGTH l2) ⇒ (MAP (λ(x,y,z). f y z) (ZIP(l1,l2)) = MAP (UNCURRY f) l2)``,
strip_tac >> (
MAP_ZIP
|> Q.GEN`g`
|> Q.ISPEC `UNCURRY (f:'b->'c->'d)`
|> SIMP_RULE(srw_ss())[combinTheory.o_DEF,pairTheory.LAMBDA_PROD]
|> UNDISCH_ALL
|> CONJUNCTS
|> Lib.el 4
|> MATCH_ACCEPT_TAC))

(* Specialisations to identity function *)

val INJ_I = store_thm(
"INJ_I",
``∀s t. INJ I s t ⇔ s ⊆ t``,
SRW_TAC[][INJ_DEF,SUBSET_DEF])

val MAP_KEYS_I = store_thm(
"MAP_KEYS_I",
``∀fm. MAP_KEYS I fm = fm``,
rw[GSYM fmap_EQ_THM,MAP_KEYS_def,EXTENSION] >>
metis_tac[MAP_KEYS_def,INJ_I,SUBSET_UNIV,combinTheory.I_THM])
val _ = export_rewrites["MAP_KEYS_I"]

val MAP_EQ_ID = store_thm(
"MAP_EQ_ID",
``!f ls. (MAP f ls = ls) = (!x. MEM x ls ==> (f x = x))``,
PROVE_TAC[MAP_EQ_f,MAP_ID,combinTheory.I_THM])

(* Specialisations to FEMPTY *)

val FUN_FMAP_FAPPLY_FEMPTY_FAPPLY = store_thm(
"FUN_FMAP_FAPPLY_FEMPTY_FAPPLY",
``FINITE s ==> (FUN_FMAP ($FAPPLY FEMPTY) s ' x = FEMPTY ' x)``,
Cases_on `x IN s` >>
rw[FUN_FMAP_DEF,NOT_FDOM_FAPPLY_FEMPTY])
val _ = export_rewrites["FUN_FMAP_FAPPLY_FEMPTY_FAPPLY"]

(* FUPDATE_LIST stuff *)

val FUPDATE_LIST_APPLY_NOT_MEM_matchable = store_thm(
"FUPDATE_LIST_APPLY_NOT_MEM_matchable",
``!kvl f k v. ~MEM k (MAP FST kvl) /\ (v = f ' k) ==> ((f |++ kvl) ' k = v)``,
PROVE_TAC[FUPDATE_LIST_APPLY_NOT_MEM])

val FUPDATE_LIST_APPLY_HO_THM = store_thm(
"FUPDATE_LIST_APPLY_HO_THM",
``∀P f kvl k.
(∃n. n < LENGTH kvl ∧ (k = EL n (MAP FST kvl)) ∧ P (EL n (MAP SND kvl)) ∧
     (∀m. n < m ∧ m < LENGTH kvl ⇒ EL m (MAP FST kvl) ≠ k)) ∨
(¬MEM k (MAP FST kvl) ∧ P (f ' k))
⇒ (P ((f |++ kvl) ' k))``,
metis_tac[FUPDATE_LIST_APPLY_MEM,FUPDATE_LIST_APPLY_NOT_MEM])

val FUPDATE_SAME_APPLY = store_thm(
"FUPDATE_SAME_APPLY",
``(x = FST kv) \/ (fm1 ' x = fm2 ' x) ==> ((fm1 |+ kv) ' x = (fm2 |+ kv) ' x)``,
Cases_on `kv` >> rw[FAPPLY_FUPDATE_THM])

val FUPDATE_SAME_LIST_APPLY = store_thm(
"FUPDATE_SAME_LIST_APPLY",
``!kvl fm1 fm2 x. MEM x (MAP FST kvl) ==> ((fm1 |++ kvl) ' x = (fm2 |++ kvl) ' x)``,
ho_match_mp_tac SNOC_INDUCT >>
conj_tac >- rw[] >>
rw[FUPDATE_LIST,FOLDL_SNOC] >>
match_mp_tac FUPDATE_SAME_APPLY >>
qmatch_rename_tac `(y = FST p) \/ Z` ["Z"] >>
Cases_on `y = FST p` >> rw[] >>
first_x_assum match_mp_tac >>
fs[MEM_MAP] >>
PROVE_TAC[])

val FUPDATE_LIST_ALL_DISTINCT_APPLY_MEM = store_thm(
"FUPDATE_LIST_ALL_DISTINCT_APPLY_MEM",
``!P ls k v fm. ALL_DISTINCT (MAP FST ls) ∧
  MEM (k,v) ls ∧
  P v ⇒
  P ((fm |++ ls) ' k)``,
rw[] >>
ho_match_mp_tac FUPDATE_LIST_APPLY_HO_THM >>
disj1_tac >>
fs[EL_ALL_DISTINCT_EL_EQ,MEM_EL] >>
qpat_assum `(k,v) = X` (assume_tac o SYM) >>
qexists_tac `n` >> rw[EL_MAP] >>
first_x_assum (qspecl_then [`n`,`m`] mp_tac) >>
rw[EL_MAP] >> spose_not_then strip_assume_tac >>
rw[] >> fs[])

val FUPDATE_LIST_ALL_DISTINCT_REVERSE = store_thm("FUPDATE_LIST_ALL_DISTINCT_REVERSE",
  ``∀ls. ALL_DISTINCT (MAP FST ls) ⇒ ∀fm. fm |++ (REVERSE ls) = fm |++ ls``,
  Induct >- rw[] >>
  qx_gen_tac `p` >> PairCases_on `p` >>
  rw[FUPDATE_LIST_APPEND,FUPDATE_LIST_THM] >>
  fs[] >>
  rw[FUPDATE_FUPDATE_LIST_COMMUTES])

(* FRANGE subset stuff *)

val IN_FRANGE = store_thm(
"IN_FRANGE",
``!f v. v IN FRANGE f ⇔ ?k. k IN FDOM f /\ (f ' k = v)``,
SRW_TAC[][FRANGE_DEF])

val IN_FRANGE_FLOOKUP = store_thm("IN_FRANGE_FLOOKUP",
``!f v. v IN FRANGE f ⇔ ∃k. FLOOKUP f k = SOME v``,
rw[IN_FRANGE,FLOOKUP_DEF])

val ALOOKUP_IN_FRANGE = store_thm("ALOOKUP_IN_FRANGE",
  ``∀ls k v. (ALOOKUP ls k = SOME v) ⇒ v ∈ FRANGE (alist_to_fmap ls)``,
  Induct >> simp[] >> Cases >> simp[] >> rw[] >>
  simp[IN_FRANGE,DOMSUB_FAPPLY_THM] >>
  full_simp_tac std_ss [Once(SYM (CONJUNCT1 ALOOKUP_EQ_FLOOKUP)),FLOOKUP_DEF] >>
  fs[] >> METIS_TAC[])

val FRANGE_FUPDATE_LIST_SUBSET = store_thm(
"FRANGE_FUPDATE_LIST_SUBSET",
``∀ls fm. FRANGE (fm |++ ls) ⊆ FRANGE fm ∪ (set (MAP SND ls))``,
Induct >- rw[FUPDATE_LIST_THM] >>
qx_gen_tac `p` >> qx_gen_tac `fm` >>
pop_assum (qspec_then `fm |+ p` mp_tac) >>
srw_tac[DNF_ss][SUBSET_DEF] >>
first_x_assum (qspec_then `x` mp_tac) >> fs[FUPDATE_LIST_THM] >>
rw[] >> fs[] >>
PairCases_on `p` >>
fsrw_tac[DNF_ss][FRANGE_FLOOKUP,FLOOKUP_UPDATE] >>
pop_assum mp_tac >> rw[] >>
PROVE_TAC[])

val IN_FRANGE_FUPDATE_LIST_suff = store_thm(
"IN_FRANGE_FUPDATE_LIST_suff",
``(∀v. v ∈ FRANGE fm ⇒ P v) ∧ (∀v. MEM v (MAP SND ls) ⇒ P v) ⇒
    ∀v. v ∈ FRANGE (fm |++ ls) ⇒ P v``,
rw[] >>
imp_res_tac(SIMP_RULE(srw_ss())[SUBSET_DEF]FRANGE_FUPDATE_LIST_SUBSET) >>
PROVE_TAC[])

val FRANGE_FUNION_SUBSET = store_thm(
"FRANGE_FUNION_SUBSET",
``FRANGE (f1 ⊌ f2) ⊆ FRANGE f1 ∪ FRANGE f2``,
srw_tac[DNF_ss][FRANGE_DEF,SUBSET_DEF,FUNION_DEF] >>
PROVE_TAC[])

val IN_FRANGE_FUNION_suff = store_thm(
"IN_FRANGE_FUNION_suff",
``(∀v. v ∈ FRANGE f1 ⇒ P v) ∧ (∀v. v ∈ FRANGE f2 ⇒ P v) ⇒
  (∀v. v ∈ FRANGE (f1 ⊌ f2) ⇒ P v)``,
rw[] >>
imp_res_tac(SIMP_RULE(srw_ss())[SUBSET_DEF]FRANGE_FUNION_SUBSET) >>
PROVE_TAC[])

val FRANGE_DOMSUB_SUBSET = store_thm(
"FRANGE_DOMSUB_SUBSET",
``FRANGE (fm \\ k) ⊆ FRANGE fm``,
srw_tac[DNF_ss][FRANGE_DEF,SUBSET_DEF,DOMSUB_FAPPLY_THM] >>
PROVE_TAC[])

val IN_FRANGE_DOMSUB_suff = store_thm(
"IN_FRANGE_DOMSUB_suff",
``(∀v. v ∈ FRANGE fm ⇒ P v) ⇒ (∀v. v ∈ FRANGE (fm \\ k) ⇒ P v)``,
rw[] >>
imp_res_tac(SIMP_RULE(srw_ss())[SUBSET_DEF]FRANGE_DOMSUB_SUBSET) >>
PROVE_TAC[])

val FRANGE_DRESTRICT_SUBSET = store_thm(
"FRANGE_DRESTRICT_SUBSET",
``FRANGE (DRESTRICT fm s) ⊆ FRANGE fm``,
srw_tac[DNF_ss][FRANGE_DEF,SUBSET_DEF,DRESTRICT_DEF] >>
PROVE_TAC[])

val IN_FRANGE_DRESTRICT_suff = store_thm(
"IN_FRANGE_DRESTRICT_suff",
``(∀v. v ∈ FRANGE fm ⇒ P v) ⇒ (∀v. v ∈ FRANGE (DRESTRICT fm s) ⇒ P v)``,
rw[] >>
imp_res_tac(SIMP_RULE(srw_ss())[SUBSET_DEF]FRANGE_DRESTRICT_SUBSET) >>
PROVE_TAC[])

val FRANGE_alist_to_fmap_SUBSET = store_thm(
"FRANGE_alist_to_fmap_SUBSET",
``FRANGE (alist_to_fmap ls) ⊆ IMAGE SND (set ls)``,
srw_tac[DNF_ss][FRANGE_DEF,SUBSET_DEF,pairTheory.EXISTS_PROD] >>
qmatch_assum_rename_tac `MEM z (MAP FST ls)`[] >>
qexists_tac `z` >>
match_mp_tac alist_to_fmap_FAPPLY_MEM >>
rw[])

val IN_FRANGE_alist_to_fmap_suff = store_thm(
"IN_FRANGE_alist_to_fmap_suff",
``(∀v. MEM v (MAP SND ls) ⇒ P v) ⇒ (∀v. v ∈ FRANGE (alist_to_fmap ls) ⇒ P v)``,
rw[] >>
imp_res_tac(SIMP_RULE(srw_ss())[SUBSET_DEF]FRANGE_alist_to_fmap_SUBSET) >>
fs[MEM_MAP] >>
PROVE_TAC[])

val FRANGE_FUPDATE_SUBSET = store_thm(
"FRANGE_FUPDATE_SUBSET",
``FRANGE (fm |+ kv) ⊆ FRANGE fm ∪ {SND kv}``,
Cases_on `kv` >>
rw[FRANGE_DEF,SUBSET_DEF,DOMSUB_FAPPLY_THM] >>
rw[] >> PROVE_TAC[])

val IN_FRANGE_FUPDATE_suff = store_thm(
"IN_FRANGE_FUPDATE_suff",
`` (∀v. v ∈ FRANGE fm ⇒ P v) ∧ (P (SND kv))
⇒ (∀v. v ∈ FRANGE (fm |+ kv) ⇒ P v)``,
rw[] >>
imp_res_tac(SIMP_RULE(srw_ss())[SUBSET_DEF]FRANGE_FUPDATE_SUBSET) >>
fs[])

val IN_FRANGE_o_f_suff = store_thm("IN_FRANGE_o_f_suff",
  ``(∀v. v ∈ FRANGE fm ⇒ P (f v)) ⇒ ∀v. v ∈ FRANGE (f o_f fm) ⇒ P v``,
  rw[IN_FRANGE] >> rw[] >> first_x_assum match_mp_tac >> PROVE_TAC[])

(* DRESTRICT stuff *)

val DRESTRICT_SUBMAP_gen = store_thm(
"DRESTRICT_SUBMAP_gen",
``f SUBMAP g ==> DRESTRICT f P SUBMAP g``,
SRW_TAC[][SUBMAP_DEF,DRESTRICT_DEF])

val DRESTRICT_SUBSET_SUBMAP = store_thm(
"DRESTRICT_SUBSET_SUBMAP",
``s1 SUBSET s2 ==> DRESTRICT f s1 SUBMAP DRESTRICT f s2``,
SRW_TAC[][SUBMAP_DEF,SUBSET_DEF,DRESTRICT_DEF])

val DRESTRICTED_FUNION = store_thm(
"DRESTRICTED_FUNION",
``∀f1 f2 s. DRESTRICT (f1 ⊌ f2) s = DRESTRICT f1 s ⊌ DRESTRICT f2 (s DIFF FDOM f1)``,
rw[GSYM fmap_EQ_THM,DRESTRICT_DEF,FUNION_DEF] >> rw[] >>
rw[EXTENSION] >> PROVE_TAC[])

val FRANGE_DRESTRICT_SUBSET = store_thm(
"FRANGE_DRESTRICT_SUBSET",
``FRANGE (DRESTRICT fm s) ⊆ FRANGE fm``,
SRW_TAC[][FRANGE_DEF,SUBSET_DEF,DRESTRICT_DEF] THEN
SRW_TAC[][] THEN PROVE_TAC[])

val DRESTRICT_FDOM = store_thm(
"DRESTRICT_FDOM",
``!f. DRESTRICT f (FDOM f) = f``,
SRW_TAC[][GSYM fmap_EQ_THM,DRESTRICT_DEF])

(* alist MAP stuff *)

val alist_to_fmap_MAP_matchable = store_thm(
"alist_to_fmap_MAP_matchable",
``∀f1 f2 al mal v. INJ f1 (set (MAP FST al)) UNIV ∧
  (mal = MAP (λ(x,y). (f1 x,f2 y)) al) ∧
  (v = MAP_KEYS f1 (f2 o_f alist_to_fmap al)) ⇒
  (alist_to_fmap mal = v)``,
METIS_TAC[alist_to_fmap_MAP])

val MAP_values_fmap_to_alist = store_thm(
"MAP_values_fmap_to_alist",
``∀f fm. MAP (λ(k,v). (k, f v)) (fmap_to_alist fm) = fmap_to_alist (f o_f fm)``,
rw[fmap_to_alist_def,MAP_MAP_o,MAP_EQ_f])

val alist_to_fmap_MAP_values = store_thm(
"alist_to_fmap_MAP_values",
``∀f al. alist_to_fmap (MAP (λ(k,v). (k, f v)) al) = f o_f (alist_to_fmap al)``,
rw[] >>
Q.ISPECL_THEN [`I:γ->γ`,`f`,`al`] match_mp_tac alist_to_fmap_MAP_matchable >>
rw[INJ_I])

val set_MAP_FST_fmap_to_alist = store_thm(
"set_MAP_FST_fmap_to_alist",
``set (MAP FST (fmap_to_alist fm)) = FDOM fm``,
METIS_TAC[fmap_to_alist_to_fmap,FDOM_alist_to_fmap])
val _ = export_rewrites["set_MAP_FST_fmap_to_alist"]

(* Misc. *)

val EVERY2_MAP = store_thm("EVERY2_MAP",
  ``(EVERY2 P (MAP f l1) l2 = EVERY2 (λx y. P (f x) y) l1 l2) ∧
    (EVERY2 Q l1 (MAP g l2) = EVERY2 (λx y. Q x (g y)) l1 l2)``,
  rw[EVERY2_EVERY] >>
  Cases_on `LENGTH l1 = LENGTH l2` >> fs[] >>
  rw[ZIP_MAP,EVERY_MEM,MEM_MAP] >>
  srw_tac[DNF_ss][pairTheory.FORALL_PROD] >>
  PROVE_TAC[])

val exists_list_GENLIST = store_thm(
"exists_list_GENLIST",
``(∃ls. P ls) = (∃n f. P (GENLIST f n))``,
rw[EQ_IMP_THM] >- (
  map_every qexists_tac [`LENGTH ls`,`combin$C EL ls`] >>
  qmatch_abbrev_tac `P ls2` >>
  qsuff_tac `ls2 = ls` >- rw[] >>
  rw[LIST_EQ_REWRITE,Abbr`ls2`] ) >>
PROVE_TAC[])

val LESS_1 = store_thm(
"LESS_1",
``x < 1 ⇔ (x = 0:num)``,
DECIDE_TAC)
val _ = export_rewrites["LESS_1"]

val IMAGE_EQ_SING = store_thm("IMAGE_EQ_SING",
  ``(IMAGE f s = {z}) <=> (s <> {}) /\ !x. x IN s ==> (f x = z)``,
  EQ_TAC >>
  srw_tac[DNF_ss][EXTENSION] >>
  PROVE_TAC[])

val EVERY_MEM_MONO = store_thm("EVERY_MEM_MONO",
  ``∀P Q l. (∀x. MEM x l ∧ P x ⇒ Q x) ∧ EVERY P l ⇒ EVERY Q l``,
  ntac 2 gen_tac >> Induct >> rw[])

val EVERY2_MEM_MONO = store_thm("EVERY2_MEM_MONO",
  ``∀P Q l1 l2. (∀x. MEM x (ZIP (l1,l2)) ∧ UNCURRY P x ⇒ UNCURRY Q x) ∧ EVERY2 P l1 l2 ⇒ EVERY2 Q l1 l2``,
  rw[EVERY2_EVERY] >> match_mp_tac EVERY_MEM_MONO >> PROVE_TAC[])

val DRESTRICT_SUBSET = store_thm("DRESTRICT_SUBSET",
  ``∀f1 f2 s t.
    (DRESTRICT f1 s = DRESTRICT f2 s) ∧ t ⊆ s ⇒
    (DRESTRICT f1 t = DRESTRICT f2 t)``,
  rw[DRESTRICT_EQ_DRESTRICT]
    >- metis_tac[DRESTRICT_SUBSET_SUBMAP,SUBMAP_TRANS]
    >- metis_tac[DRESTRICT_SUBSET_SUBMAP,SUBMAP_TRANS] >>
  fsrw_tac[DNF_ss][SUBSET_DEF,EXTENSION] >>
  metis_tac[])

val f_o_f_FUPDATE_compose = store_thm("f_o_f_FUPDATE_compose",
  ``∀f1 f2 k x v. x ∉ FDOM f1 ∧ x ∉ FRANGE f2 ⇒
    (f1 |+ (x,v) f_o_f f2 |+ (k,x) = (f1 f_o_f f2) |+ (k,v))``,
  rw[GSYM fmap_EQ_THM,f_o_f_DEF,FAPPLY_FUPDATE_THM] >>
  simp[] >> rw[] >> fs[] >> rw[EXTENSION] >>
  fs[IN_FRANGE] >> rw[]
  >- PROVE_TAC[]
  >- PROVE_TAC[] >>
  qmatch_assum_rename_tac`y <> k`[] >>
  `y ∈ FDOM (f1 f_o_f f2)` by rw[f_o_f_DEF] >>
  rw[f_o_f_DEF])

  (* --------- SO additions --------- *)
val alookup_distinct_reverse = Q.store_thm ("alookup_distinct_reverse",
`!l k. ALL_DISTINCT (MAP FST l) ⇒ (ALOOKUP (REVERSE l) k = ALOOKUP l k)`,
 Induct_on `l` >>
 rw [] >>
 PairCases_on `h` >>
 fs [] >>
 BasicProvers.EVERY_CASE_TAC >>
 fs [ALOOKUP_APPEND] >>
 rw [] >>
 BasicProvers.EVERY_CASE_TAC >>
 fs [] >>
 imp_res_tac ALOOKUP_MEM >>
 fs [MEM_MAP] >>
 metis_tac [FST]);

val fevery_funion = Q.store_thm ("fevery_funion",
`!P m1 m2. FEVERY P m1 ∧ FEVERY P m2 ⇒ FEVERY P (FUNION m1 m2)`,
 rw [FEVERY_ALL_FLOOKUP, FLOOKUP_FUNION] >>
 BasicProvers.EVERY_CASE_TAC >>
 fs []);

val flookup_fupdate_list = Q.store_thm ("flookup_fupdate_list",
`!l k m.
  FLOOKUP (m |++ l) k =
  case ALOOKUP (REVERSE l) k of
     | SOME v => SOME v
     | NONE => FLOOKUP m k`,
 ho_match_mp_tac ALOOKUP_ind >>
 rw [FUPDATE_LIST_THM, ALOOKUP_def, FLOOKUP_UPDATE] >>
 BasicProvers.FULL_CASE_TAC >>
 fs [ALOOKUP_APPEND] >>
 BasicProvers.EVERY_CASE_TAC >>
 fs [FLOOKUP_UPDATE] >>
 rw [] >>
 imp_res_tac FLOOKUP_FUPDATE_LIST_ALOOKUP_NONE >>
 imp_res_tac FLOOKUP_FUPDATE_LIST_ALOOKUP_SOME >>
 fs [FLOOKUP_UPDATE]);

val fmap_eq_flookup = Q.store_thm ("fmap_eq_flookup",
`!m1 m2. (m1 = m2) = !k. FLOOKUP m1 k = FLOOKUP m2 k`,
 rw [FLOOKUP_DEF, GSYM fmap_EQ_THM] >>
 eq_tac >>
 rw [EXTENSION]
 >- metis_tac [NOT_SOME_NONE]
 >- (Cases_on `x ∉ FDOM m2` >>
     fs []
     >- metis_tac [NOT_SOME_NONE]
     >- metis_tac [SOME_11]));

val mem_exists_set = Q.store_thm ("mem_exists_set",
`!x y l. MEM (x,y) l ⇒ ∃z. (x = FST z) ∧ z ∈ set l`,
Induct_on `l` >>
rw [] >>
metis_tac [FST]);

val nub_def = Define `
(nub [] = []) ∧
(nub (x::l) =
  if MEM x l then
    nub l
  else
    x :: nub l)`;

val nub_set = Q.store_thm ("nub_set",
`!l. set l = set (nub l)`,
Induct >>
rw [nub_def, EXTENSION] >>
metis_tac []);

val all_distinct_nub = Q.store_thm ("all_distinct_nub",
`!l. ALL_DISTINCT (nub l)`,
Induct >>
rw [nub_def] >>
metis_tac [nub_set]);

val fupdate_list_map = Q.store_thm ("fupdate_list_map",
`!l f x y.
  x ∈ FDOM (FEMPTY |++ l)
   ⇒
     ((FEMPTY |++ MAP (\(a,b). (a, f b)) l) ' x = f ((FEMPTY |++ l) ' x))`,
     rpt gen_tac >>
     Q.ISPECL_THEN[`FST`,`f o SND`,`l`,`FEMPTY:α|->γ`]mp_tac(GSYM finite_mapTheory.FOLDL_FUPDATE_LIST) >>
     simp[LAMBDA_PROD] >>
     disch_then kall_tac >>
     qid_spec_tac`l` >>
     ho_match_mp_tac SNOC_INDUCT >>
     simp[FUPDATE_LIST_THM] >>
     simp[FOLDL_SNOC,FORALL_PROD,FAPPLY_FUPDATE_THM,FDOM_FUPDATE_LIST,MAP_SNOC,finite_mapTheory.FUPDATE_LIST_SNOC] >>
     rw[] >> rw[])

val fdom_fupdate_list2 = Q.store_thm ("fdom_fupdate_list2",
`∀kvl fm. FDOM (fm |++ kvl) = (FDOM fm DIFF set (MAP FST kvl)) ∪ set (MAP FST kvl)`,
rw [FDOM_FUPDATE_LIST, EXTENSION] >>
metis_tac []);

val map_fst = Q.store_thm ("map_fst",
`!l f. MAP FST (MAP (\(x,y). (x, f y)) l) = MAP FST l`,
Induct_on `l` >>
rw [] >>
PairCases_on `h` >>
fs []);

val every_count_list = Q.store_thm ("every_count_list",
`!P n. EVERY P (COUNT_LIST n) = (!m. m < n ⇒ P m)`,
Induct_on `n` >>
rw [COUNT_LIST_def, EVERY_MAP] >>
eq_tac >>
rw [] >>
Cases_on `m` >>
rw [] >>
`n' < n` by decide_tac >>
metis_tac []);

val filter_helper = Q.prove (
`!x l1 l2. ~MEM x l2 ⇒ (MEM x (FILTER (\x. x ∉ set l2) l1) = MEM x l1)`,
Induct_on `l1` >>
rw [] >>
metis_tac []);

val nub_append = Q.store_thm ("nub_append",
`!l1 l2.
  nub (l1++l2) = nub (FILTER (\x. ~MEM x l2) l1) ++ nub l2`,
Induct_on `l1` >>
rw [nub_def] >>
fs [] >>
BasicProvers.FULL_CASE_TAC >>
rw [] >>
metis_tac [filter_helper]);

val list_to_set_diff = Q.store_thm ("list_to_set_diff",
`!l1 l2. set l2 DIFF set l1 = set (FILTER (\x. x ∉ set l1) l2)`,
Induct_on `l2` >>
rw []);

val card_eqn_help = Q.prove (
`!l1 l2. CARD (set l2) - CARD (set l1 ∩ set l2) = CARD (set (FILTER (\x. x ∉ set l1) l2))`,
rw [Once INTER_COMM] >>
SIMP_TAC list_ss [GSYM CARD_DIFF] >>
metis_tac [list_to_set_diff]);

val length_nub_append = Q.store_thm ("length_nub_append",
`!l1 l2. LENGTH (nub (l1 ++ l2)) = LENGTH (nub l1) + LENGTH (nub (FILTER (\x. ~MEM x l1) l2))`,
rw [GSYM ALL_DISTINCT_CARD_LIST_TO_SET, all_distinct_nub, GSYM nub_set] >>
fs [FINITE_LIST_TO_SET, CARD_UNION_EQN] >>
ASSUME_TAC (Q.SPECL [`l1`, `l2`] card_eqn_help) >>
`CARD (set l1 ∩ set l2) ≤ CARD (set l2)` 
           by metis_tac [CARD_INTER_LESS_EQ, FINITE_LIST_TO_SET, INTER_COMM] >>
decide_tac);

val fmap_to_list = Q.store_thm ("fmap_to_list",
`!m. ?l. ALL_DISTINCT (MAP FST l) ∧ (m = FEMPTY |++ l)`,
ho_match_mp_tac fmap_INDUCT >>
rw [FUPDATE_LIST_THM] >|
[qexists_tac `[]` >>
     rw [FUPDATE_LIST_THM],
 qexists_tac `(x,y)::l` >>
     rw [FUPDATE_LIST_THM] >>
     fs [FDOM_FUPDATE_LIST] >>
     rw [FUPDATE_FUPDATE_LIST_COMMUTES] >>
     fs [LIST_TO_SET_MAP] >>
     metis_tac [FST]]);

val every_zip_snd = Q.store_thm ("every_zip_snd",
`!l1 l2 P.
(LENGTH l1 = LENGTH l2) ⇒
(EVERY (\x. P (SND x)) (ZIP (l1,l2)) = EVERY P l2)`,
Induct_on `l1` >>
rw [] >>
Cases_on `l2` >>
fs []);

val every_zip_fst = Q.store_thm ("every_zip_fst",
`!l1 l2 P.
(LENGTH l1 = LENGTH l2) ⇒
(EVERY (\x. P (FST x)) (ZIP (l1,l2)) = EVERY P l1)`,
Induct_on `l1` >>
rw [] >>
Cases_on `l2` >>
fs []);

val flookup_thm = Q.store_thm ("flookup_thm",
`!f x v. ((FLOOKUP f x = NONE) = (x ∉ FDOM f)) ∧
         ((FLOOKUP f x = SOME v) = (x ∈ FDOM f ∧ (f ' x = v)))`,
rw [FLOOKUP_DEF]);

val count_add1 = Q.store_thm ("count_add1",
`!n. count (n + 1) = n INSERT count n`,
metis_tac [COUNT_SUC, arithmeticTheory.ADD1]);

val count_list_sub1 = Q.store_thm ("count_list_sub1",
`!n. (n ≠ 0) ⇒ (COUNT_LIST n = 0::MAP SUC (COUNT_LIST (n - 1)))`,
Induct_on `n` >>
ONCE_REWRITE_TAC [COUNT_LIST_def] >>
fs []);

val el_map_count = Q.store_thm ("el_map_count",
`!n f m. n < m ⇒ (EL n (MAP f (COUNT_LIST m)) = f n)`,
Induct_on `n` >>
rw [] >>
Cases_on `m` >>
fs [COUNT_LIST_def] >>
`n < SUC n'` by decide_tac >>
res_tac >>
fs [COUNT_LIST_def] >>
pop_assum (fn _ => all_tac) >>
pop_assum (mp_tac o GSYM o Q.SPEC `f o SUC`) >>
rw [MAP_MAP_o]);

val mem_to_flookup = Q.store_thm ("mem_to_flookup",
`!x y l. ALL_DISTINCT (MAP FST l) ∧ MEM (x,y) l ⇒ (FLOOKUP (FEMPTY |++ l) x = SOME y)`,
 Induct_on `l` >>
 rw [] >>
 fs [flookup_fupdate_list] >>
 BasicProvers.EVERY_CASE_TAC >>
 fs [ALOOKUP_APPEND] >>
 BasicProvers.EVERY_CASE_TAC >>
 fs [] >>
 imp_res_tac ALOOKUP_MEM >>
 imp_res_tac alookup_distinct_reverse >>
 fs [] >>
 res_tac >>
 BasicProvers.EVERY_CASE_TAC >>
 fs [MEM_MAP] >>
 rw [] >>
 metis_tac [FST]);

val el_append3 = Q.store_thm ("el_append3",
`!l1 x l2. EL (LENGTH l1) (l1++ [x] ++ l2) = x`,
Induct_on `l1` >>
rw [] >>
rw []);

val lupdate_append = Q.store_thm ("lupdate_append",
`!x n l1 l2. n < LENGTH l1 ⇒ (LUPDATE x n (l1++l2) = LUPDATE x n l1 ++ l2)`,
 Induct_on `l1` >>
 rw [] >>
 Cases_on `n` >>
 rw [LUPDATE_def] >>
 fs []);

val lupdate_append2 = Q.store_thm ("lupdate_append2",
`!v l1 x l2 l3. LUPDATE v (LENGTH l1) (l1++[x]++l2) = l1++[v]++l2`,
 Induct_on `l1` >>
 rw [LUPDATE_def])

val fupdate_list_funion = store_thm("fupdate_list_funion",
``!m l. m|++l = FUNION (FEMPTY |++l) m``,
 Induct_on `l`
 >- rw [FUPDATE_LIST, FUNION_FEMPTY_1] >> 
 REWRITE_TAC [FUPDATE_LIST_THM] >>
 rpt GEN_TAC >>
 pop_assum (qspecl_then [`m|+h`] mp_tac) >>
 rw [] >>
 rw [fmap_eq_flookup, FLOOKUP_FUNION] >>
 BasicProvers.EVERY_CASE_TAC >>
 PairCases_on `h` >>
 fs [FLOOKUP_UPDATE, flookup_fupdate_list] >>
 BasicProvers.EVERY_CASE_TAC >>
 fs []);

val ZIP_COUNT_LIST = store_thm("ZIP_COUNT_LIST",
  ``(n = LENGTH l1) ⇒
    (ZIP (l1,COUNT_LIST n) = GENLIST (λn. (EL n l1, n)) (LENGTH l1))``,
    simp[LIST_EQ_REWRITE,LENGTH_COUNT_LIST,EL_ZIP,EL_COUNT_LIST])

val FUPDATE_EQ_FUPDATE_LIST = store_thm("FUPDATE_EQ_FUPDATE_LIST",
  ``∀fm kv. fm |+ kv = fm |++ [kv]``,
  rw[FUPDATE_LIST_THM])

val fmap_inverse_def = Define `
fmap_inverse m1 m2 =
  !k. k ∈ FDOM m1 ⇒ ?v. (FLOOKUP m1 k = SOME v) ∧ (FLOOKUP m2 v = SOME k)`;

val map_some_eq = Q.store_thm ("map_some_eq",
`!l1 l2. (MAP SOME l1 = MAP SOME l2) ⇔ (l1 = l2)`,
 Induct_on `l1` >>
 rw [] >>
 Cases_on `l2` >>
 rw []);

val map_some_eq_append = Q.store_thm ("map_some_eq_append",
`!l1 l2 l3. (MAP SOME l1 ++ MAP SOME l2 = MAP SOME l3) ⇔ (l1 ++ l2 = l3)`,
metis_tac [map_some_eq, MAP_APPEND]);

val _ = augment_srw_ss [rewrites [map_some_eq,map_some_eq_append]];

val fupdate_list_foldr = Q.store_thm ("fupdate_list_foldr",
`!m l. FOLDR (λ(k,v) env. env |+ (k,v)) m l = m |++ REVERSE l`,
 Induct_on `l` >>
 rw [FUPDATE_LIST] >>
 PairCases_on `h` >>
 rw [FOLDL_APPEND]);

val fupdate_list_foldl = Q.store_thm ("fupdate_list_foldl",
`!m l. FOLDL (λenv (k,v). env |+ (k,v)) m l = m |++ l`,
 Induct_on `l` >>
 rw [FUPDATE_LIST] >>
 PairCases_on `h` >>
 rw []);

val disjoint_drestrict = Q.store_thm ("disjoint_drestrict",
`!s m. DISJOINT s (FDOM m) ⇒ (DRESTRICT m (COMPL s) = m)`,
 rw [fmap_eq_flookup, FLOOKUP_DRESTRICT] >>
 Cases_on `k ∉ s` >>
 rw [] >>
 fs [DISJOINT_DEF, EXTENSION, FLOOKUP_DEF] >>
 metis_tac []);

val compl_insert = Q.store_thm ("compl_insert",
`!s x. COMPL (x INSERT s) = COMPL s DELETE x`,
 rw [EXTENSION] >>
 metis_tac []);

val drestrict_iter_list = Q.store_thm ("drestrict_iter_list",
`!m l. FOLDR (\k m. m \\ k) m l = DRESTRICT m (COMPL (set l))`,
 Induct_on `l` >>
 rw [DRESTRICT_UNIV, compl_insert, DRESTRICT_DOMSUB]);

val _ = export_theory()
