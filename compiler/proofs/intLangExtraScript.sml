open HolKernel bossLib boolLib miscLib boolSimps pairTheory listTheory rich_listTheory pred_setTheory finite_mapTheory relationTheory SatisfySimps arithmeticTheory quantHeuristicsLib lcsymtacs
open miscTheory semanticsExtraTheory CompilerLibTheory CompilerPrimitivesTheory IntLangTheory ToIntLangTheory compilerTerminationTheory
val _ = new_theory "intLangExtra"

(* TODO: move?*)

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

val THE_find_index_suff = store_thm("THE_find_index_suff",
  ``∀P x ls n. (∀m. m < LENGTH ls ⇒ P (m + n)) ∧ MEM x ls ⇒
    P (THE (find_index x ls n))``,
  rw[] >>
  imp_res_tac find_index_MEM >>
  pop_assum(qspec_then`n`mp_tac) >>
  srw_tac[DNF_ss,ARITH_ss][])

val the_find_index_suff = store_thm("the_find_index_suff",
  ``∀P d x ls n. (∀m. m < LENGTH ls ⇒ P (m + n)) ∧ MEM x ls ⇒
    P (the d (find_index x ls n))``,
  rw[] >>
  imp_res_tac find_index_MEM >>
  pop_assum(qspec_then`n`mp_tac) >>
  srw_tac[DNF_ss,ARITH_ss][])

val free_labs_list_MAP = store_thm("free_labs_list_MAP",
  ``∀es ez. free_labs_list ez es = FLAT (MAP (free_labs ez) es)``,
  Induct >> rw[])

val free_labs_defs_MAP = store_thm("free_labs_defs_MAP",
  ``∀defs ez nz ix. free_labs_defs ez nz ix defs = FLAT (GENLIST (λi. free_labs_def ez nz (ix + i) (EL i defs)) (LENGTH defs))``,
  Induct >> rw[GENLIST_CONS] >>
  rw[LIST_EQ_REWRITE,LENGTH_FLAT] >>
  ntac 2 AP_TERM_TAC >>
  simp[LIST_EQ_REWRITE,ADD1])

val no_labs_list_MAP = store_thm("no_labs_list_MAP",
  ``∀es. no_labs_list es = EVERY no_labs es``,
  Induct >> rw[])
val all_labs_list_MAP = store_thm("all_labs_list_MAP",
  ``∀es. all_labs_list es = EVERY all_labs es``,
  Induct >> rw[])
val no_labs_defs_MAP = store_thm("no_labs_defs_MAP",
  ``∀es. no_labs_defs es = EVERY no_labs_def es``,
  Induct >> rw[])
val all_labs_defs_MAP = store_thm("all_labs_defs_MAP",
  ``∀es. all_labs_defs es = EVERY all_labs_def es``,
  Induct >> rw[])
val _ = export_rewrites["no_labs_list_MAP","all_labs_list_MAP","no_labs_defs_MAP","all_labs_defs_MAP"]

val vlabs_def = Define`
  (vlabs (CLitv _) = {}) ∧
  (vlabs (CConv _ vs) = vlabs_list vs) ∧
  (vlabs (CRecClos env defs _) = vlabs_list env ∪ set (free_labs_defs (LENGTH env) (LENGTH defs) 0 defs)) ∧
  (vlabs (CLoc _) = {}) ∧
  (vlabs_list [] = {}) ∧
  (vlabs_list (v::vs) = vlabs v ∪ vlabs_list vs)`
val _ = export_rewrites["vlabs_def"]

val vlabs_list_MAP = store_thm("vlabs_list_MAP",
 ``∀vs. vlabs_list vs = BIGUNION (IMAGE vlabs (set vs))``,
 Induct >> rw[])

val vlabs_list_APPEND = store_thm("vlabs_list_APPEND",
  ``vlabs_list (l1 ++ l2) = vlabs_list l1 ∪ vlabs_list l2``,
  rw[vlabs_list_MAP])

val vlabs_list_REVERSE = store_thm("vlabs_list_REVERSE",
  ``vlabs_list (REVERSE ls) = vlabs_list ls``,
  rw[vlabs_list_MAP])

val no_vlabs_def = Define`
  (no_vlabs (CLitv _) = T) ∧
  (no_vlabs (CConv _ vs) = no_vlabs_list vs) ∧
  (no_vlabs (CRecClos env defs _) ⇔ no_vlabs_list env ∧ no_labs_defs defs) ∧
  (no_vlabs (CLoc _) = T) ∧
  (no_vlabs_list [] = T) ∧
  (no_vlabs_list (v::vs) ⇔ no_vlabs v ∧ no_vlabs_list vs)`
val _ = export_rewrites["no_vlabs_def"]

val all_vlabs_def = Define`
  (all_vlabs (CLitv _) = T) ∧
  (all_vlabs (CConv _ vs) = all_vlabs_list vs) ∧
  (all_vlabs (CRecClos env defs _) ⇔ all_vlabs_list env ∧ all_labs_defs defs) ∧
  (all_vlabs (CLoc _) = T) ∧
  (all_vlabs_list [] = T) ∧
  (all_vlabs_list (v::vs) ⇔ all_vlabs v ∧ all_vlabs_list vs)`
val _ = export_rewrites["all_vlabs_def"]

val no_vlabs_list_MAP = store_thm("no_vlabs_list_MAP",
  ``∀vs. no_vlabs_list vs = EVERY no_vlabs vs``,
  Induct >> rw[])
val all_vlabs_list_MAP = store_thm("all_vlabs_list_MAP",
  ``∀vs. all_vlabs_list vs = EVERY all_vlabs vs``,
  Induct >> rw[])
val _ = export_rewrites["no_vlabs_list_MAP","all_vlabs_list_MAP"]

val _ = Parse.overload_on("vlabs_menv",``λmenv. BIGUNION (IMAGE vlabs_list (FRANGE menv))``)

val Cevaluate_vlabs = store_thm("Cevaluate_vlabs",
  ``(∀menv s env exp res. Cevaluate menv s env exp res ⇒
        (vlabs_list (FST res) ⊆ vlabs_menv menv ∪ vlabs_list s ∪ vlabs_list env ∪ set (free_labs (LENGTH env) exp)) ∧
        (∀v. (SND res = Cval v) ⇒ vlabs v ⊆ vlabs_menv menv ∪ vlabs_list s ∪ vlabs_list env ∪ set (free_labs (LENGTH env) exp)) ∧
        (∀v. (SND res = Cexc (Craise v)) ⇒ vlabs v ⊆ vlabs_menv menv ∪ vlabs_list s ∪ vlabs_list env ∪ set (free_labs (LENGTH env) exp))) ∧
    (∀menv s env es res. Cevaluate_list menv s env es res ⇒
        (vlabs_list (FST res) ⊆ vlabs_menv menv ∪ vlabs_list s ∪ vlabs_list env ∪ set (free_labs_list (LENGTH env) es)) ∧
        (∀vs. (SND res = Cval vs) ⇒ vlabs_list vs ⊆ vlabs_menv menv ∪ vlabs_list s ∪ vlabs_list env ∪ set (free_labs_list (LENGTH env) es)) ∧
        (∀v. (SND res = Cexc (Craise v)) ⇒ vlabs v ⊆ vlabs_menv menv ∪ vlabs_list s ∪ vlabs_list env ∪ set (free_labs_list (LENGTH env) es)))``,
  ho_match_mp_tac Cevaluate_ind >>
  strip_tac >- srw_tac[DNF_ss][SUBSET_DEF] >>
  strip_tac >- srw_tac[DNF_ss][SUBSET_DEF] >>
  strip_tac >- ( srw_tac[DNF_ss][SUBSET_DEF] >> metis_tac[] ) >>
  strip_tac >- ( srw_tac[DNF_ss][SUBSET_DEF,ADD1] >> metis_tac[] ) >>
  strip_tac >- ( srw_tac[DNF_ss][SUBSET_DEF] >> metis_tac[] ) >>
  strip_tac >- (
    srw_tac[DNF_ss][EVERY_MEM,MEM_EL,SUBSET_DEF,vlabs_list_MAP] >>
    PROVE_TAC[] ) >>
  strip_tac >- (
    srw_tac[DNF_ss][EVERY_MEM,MEM_EL,SUBSET_DEF,IN_FRANGE,FLOOKUP_DEF,vlabs_list_MAP] >>
    PROVE_TAC[] ) >>
  strip_tac >- ( srw_tac[DNF_ss][SUBSET_DEF] >> metis_tac[] ) >>
  strip_tac >- ( srw_tac[DNF_ss][SUBSET_DEF] >> metis_tac[] ) >>
  strip_tac >- ( srw_tac[DNF_ss][SUBSET_DEF] >> metis_tac[] ) >>
  strip_tac >- ( srw_tac[DNF_ss][SUBSET_DEF] >> metis_tac[] ) >>
  strip_tac >- ( srw_tac[DNF_ss][SUBSET_DEF] >> metis_tac[] ) >>
  strip_tac >- (
    srw_tac[DNF_ss][SUBSET_DEF,EVERY_MEM,MEM_EL,vlabs_list_MAP] >>
    metis_tac[] ) >>
  strip_tac >- ( srw_tac[DNF_ss][SUBSET_DEF] >> metis_tac[] ) >>
  strip_tac >- ( srw_tac[DNF_ss][SUBSET_DEF,ADD1] >> metis_tac[] ) >>
  strip_tac >- ( srw_tac[DNF_ss][SUBSET_DEF] >> metis_tac[] ) >>
  strip_tac >- (
    srw_tac[DNF_ss][SUBSET_DEF,MEM_FLAT,MEM_MAP,MEM_GENLIST,vlabs_list_MAP] >>
    metis_tac[ADD_SYM] ) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    BasicProvers.EVERY_CASE_TAC >> rfs[] >>
    qmatch_abbrev_tac`a ⊆ b ∧ c` >>
    qmatch_assum_abbrev_tac`a ⊆ b'` >>
    (qsuff_tac`b' ⊆ b`>-metis_tac[SUBSET_TRANS]) >>
    unabbrev_all_tac >>
    qmatch_abbrev_tac`m ∪ a ∪ b ∪ c ⊆ d` >>
    qmatch_assum_abbrev_tac`a ⊆ m ∪ e ∪ f ∪ g` >>
    qmatch_assum_abbrev_tac`e ⊆ m ∪ h ∪ f ∪ i` >>
    `h ⊆ d` by metis_tac[SUBSET_DEF,IN_UNION] >>
    `f ⊆ d` by metis_tac[SUBSET_DEF,IN_UNION] >>
    `i ⊆ d` by metis_tac[SUBSET_DEF,IN_UNION] >>
    `m ⊆ d` by  metis_tac[SUBSET_DEF,IN_UNION] >>
    `e ⊆ d` by (
      ntac 4 (pop_assum mp_tac) >>
      last_x_assum mp_tac >>
      rpt (pop_assum kall_tac) >>
      srw_tac[DNF_ss][SUBSET_DEF] >> metis_tac[] ) >>
    `g ⊆ d` by metis_tac[SUBSET_DEF,IN_UNION] >>
    `a ⊆ d` by ( fsrw_tac[DNF_ss][SUBSET_DEF] >> metis_tac[] ) >|
    [
      `b ⊆ d` by (
        rw[Abbr`b`,vlabs_list_MAP] >>
        TRY (
          Q.PAT_ABBREV_TAC`ls:Cv list = GENLIST X Y` >>
          srw_tac[DNF_ss][SUBSET_DEF,MEM_GENLIST,Abbr`ls`] >>
          metis_tac[SUBSET_DEF,IN_UNION] ) >>
        rw[GSYM vlabs_list_MAP] >>
        qmatch_abbrev_tac`vlabs_list X ⊆ d` >>
        fsrw_tac[DNF_ss][SUBSET_DEF] >>
        metis_tac[]) >>
      qmatch_assum_abbrev_tac`set j ⊆ m ∪ h ∪ f ∪ i` >>
      `c ⊆ set j` by (
        rw[SUBSET_DEF,Abbr`c`,Abbr`j`,free_labs_defs_MAP,MEM_FLAT,MEM_GENLIST] >>
        srw_tac[DNF_ss][] >>
        qexists_tac`n` >> simp[] >>
        fsrw_tac[ARITH_ss][] ) >>
      match_mp_tac SUBSET_TRANS >>
      qexists_tac`d` >>
      conj_tac >- (
        fsrw_tac[DNF_ss][SUBSET_DEF] >>
        metis_tac[] ) >>
      simp[Abbr`d`] >>
      metis_tac[SUBSET_UNION,UNION_COMM,UNION_ASSOC]
    ,
      `b ⊆ d` by (
        rw[Abbr`b`,vlabs_list_MAP] >>
        TRY (
          Q.PAT_ABBREV_TAC`ls:Cv list = MAP (CRecClos X Y) Z` >>
          srw_tac[DNF_ss][SUBSET_DEF,MEM_GENLIST,MEM_MAP,Abbr`ls`] >>
          fsrw_tac[DNF_ss][EVERY_MEM] >>
          metis_tac[SUBSET_DEF,IN_UNION,MEM_EL] ) >>
        TRY (
          Q.PAT_ABBREV_TAC`ls:Cv list = MAP X Z` >>
          srw_tac[DNF_ss][SUBSET_DEF,MEM_GENLIST,MEM_MAP,Abbr`ls`] >>
          fsrw_tac[DNF_ss][vlabs_list_MAP,EVERY_MEM] >>
          fsrw_tac[DNF_ss][SUBSET_DEF,Abbr`d`] >>
          metis_tac[MEM_EL] ) >>
        rw[GSYM vlabs_list_MAP] >>
        TRY(qmatch_abbrev_tac`vlabs_list X ⊆ d`) >>
        fsrw_tac[DNF_ss][SUBSET_DEF] >>
        metis_tac[]) >>
      qmatch_assum_abbrev_tac`set j ⊆ m ∪ h ∪ f ∪ i` >>
      `c ⊆ set j` by (
        rw[SUBSET_DEF,Abbr`c`,Abbr`j`,free_labs_defs_MAP,MEM_FLAT,MEM_GENLIST] >>
        srw_tac[DNF_ss][] >>
        qexists_tac`n` >> simp[] >>
        fsrw_tac[ARITH_ss][] ) >>
      match_mp_tac SUBSET_TRANS >>
      qexists_tac`d` >>
      conj_tac >- (
        fsrw_tac[DNF_ss][SUBSET_DEF] >>
        metis_tac[] ) >>
      simp[Abbr`d`] >>
      metis_tac[SUBSET_UNION,UNION_COMM,UNION_ASSOC]
    ]) >>
  strip_tac >- ( srw_tac[DNF_ss][SUBSET_DEF] >> metis_tac[] ) >>
  strip_tac >- ( srw_tac[DNF_ss][SUBSET_DEF] >> metis_tac[] ) >>
  strip_tac >- (
    ntac 3 gen_tac >>
    Cases >> ntac 2 gen_tac >>
    Cases >> rw[] >>
    fs[el_check_def,EVERY_MEM] >>
    BasicProvers.EVERY_CASE_TAC >>
    fsrw_tac[DNF_ss][SUBSET_DEF,vlabs_list_MAP] >>
    metis_tac[MEM_EL]) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    ntac 3 gen_tac >>
    Cases >> ntac 3 gen_tac >>
    Cases >> TRY (Cases_on`l`) >> Cases >> TRY (Cases_on`l`) >> rw[] ) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    ntac 6 gen_tac >>
    Cases >> rw[] >> fs[] >>
    fs[EVERY_MEM] >>
    fsrw_tac[DNF_ss][SUBSET_DEF,vlabs_list_MAP] >>
    metis_tac[MEM_LUPDATE] ) >>
  strip_tac >- rw[] >>
  strip_tac >- ( srw_tac[DNF_ss][SUBSET_DEF] >> metis_tac[] ) >>
  strip_tac >- ( srw_tac[DNF_ss][SUBSET_DEF] >> metis_tac[] ) >>
  strip_tac >- ( srw_tac[DNF_ss][SUBSET_DEF] >> metis_tac[] ) >>
  strip_tac >- ( srw_tac[DNF_ss][SUBSET_DEF] >> metis_tac[] ) >>
  strip_tac >- ( srw_tac[DNF_ss][SUBSET_DEF] >> metis_tac[] ) >>
  strip_tac >- ( srw_tac[DNF_ss][SUBSET_DEF] >> metis_tac[] ))

val no_vlabs_menv_def = Define`no_vlabs_menv menv = ∀env. env ∈ (FRANGE menv) ⇒ no_vlabs_list env`
val all_vlabs_menv_def = Define`all_vlabs_menv menv = ∀env. env ∈ (FRANGE menv) ⇒ all_vlabs_list env`

val Cevaluate_no_vlabs = store_thm("Cevaluate_no_vlabs",
  ``(∀menv s env exp res. Cevaluate menv s env exp res ⇒ no_vlabs_menv menv ∧ no_vlabs_list s ∧ no_vlabs_list env ∧ no_labs exp ⇒
        no_vlabs_list (FST res) ∧ (∀v. (SND res = Cval v) ⇒ no_vlabs v) ∧ (∀v. (SND res = Cexc (Craise v)) ⇒ no_vlabs v)) ∧
    (∀menv s env es res. Cevaluate_list menv s env es res ⇒ no_vlabs_menv menv ∧ no_vlabs_list s ∧ no_vlabs_list env ∧ no_labs_list es ⇒
        no_vlabs_list (FST res) ∧ (∀vs. (SND res = Cval vs) ⇒ no_vlabs_list vs) ∧ (∀v. (SND res = Cexc (Craise v)) ⇒ no_vlabs v))``,
  ho_match_mp_tac Cevaluate_ind >>
  strip_tac >- fsrw_tac[DNF_ss][EVERY_MEM,MEM_EL] >>
  strip_tac >- fsrw_tac[DNF_ss][EVERY_MEM,MEM_EL] >>
  strip_tac >- fsrw_tac[DNF_ss][EVERY_MEM,MEM_EL] >>
  strip_tac >- simp[] >>
  strip_tac >- simp[] >>
  strip_tac >- fsrw_tac[DNF_ss][EVERY_MEM,MEM_EL] >>
  strip_tac >- fsrw_tac[DNF_ss][EVERY_MEM,MEM_EL,IN_FRANGE,FLOOKUP_DEF,no_vlabs_menv_def] >>
  strip_tac >- fsrw_tac[DNF_ss][EVERY_MEM,MEM_EL] >>
  strip_tac >- fsrw_tac[DNF_ss][EVERY_MEM,MEM_EL] >>
  strip_tac >- fsrw_tac[DNF_ss][EVERY_MEM,MEM_EL] >>
  strip_tac >- fsrw_tac[DNF_ss][EVERY_MEM,MEM_EL] >>
  strip_tac >- fsrw_tac[DNF_ss][EVERY_MEM,MEM_EL] >>
  strip_tac >- fsrw_tac[DNF_ss][EVERY_MEM,MEM_EL] >>
  strip_tac >- fsrw_tac[DNF_ss][EVERY_MEM,MEM_EL] >>
  strip_tac >- simp[] >>
  strip_tac >- fsrw_tac[DNF_ss][EVERY_MEM,MEM_EL] >>
  strip_tac >- (
    simp[] >>
    simp_tac pure_ss [EVERY_MEM,MEM_EL,GSYM LEFT_FORALL_IMP_THM] >>
    simp[] >> rw[] >> fsrw_tac[DNF_ss][EVERY_MEM,MEM_EL] ) >>
  strip_tac >- (
    rpt gen_tac >> ntac 2 strip_tac >> fs[] >> rfs[] >>
    BasicProvers.EVERY_CASE_TAC >> rfs[EVERY_REVERSE] >> fs[EVERY_REVERSE] >>
    first_x_assum match_mp_tac >>
    simp[EVERY_MAP,EVERY_GENLIST] >>
    fsrw_tac[DNF_ss][EVERY_MEM,MEM_EL] >>
    metis_tac[no_labs_def] ) >>
  strip_tac >- fsrw_tac[DNF_ss][EVERY_MEM,MEM_EL] >>
  strip_tac >- fsrw_tac[DNF_ss][EVERY_MEM,MEM_EL] >>
  strip_tac >- (
    ntac 3 gen_tac >>
    Cases >> ntac 2 gen_tac >>
    Cases >> rw[] >>
    fs[el_check_def,EVERY_MEM] >>
    BasicProvers.EVERY_CASE_TAC >>
    fsrw_tac[DNF_ss][EVERY_MEM,MEM_EL] >>
    metis_tac[MEM_EL]) >>
  strip_tac >- fsrw_tac[DNF_ss][EVERY_MEM,MEM_EL] >>
  strip_tac >- (
    ntac 3 gen_tac >>
    Cases >> ntac 3 gen_tac >>
    Cases >> TRY (Cases_on`l`) >> Cases >> TRY (Cases_on`l`) >> rw[] ) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    ntac 6 gen_tac >>
    Cases >> rw[] >> fs[] >>
    fs[EVERY_MEM] >>
    fsrw_tac[DNF_ss][EVERY_MEM] >>
    metis_tac[MEM_LUPDATE] ) >>
  strip_tac >- fsrw_tac[DNF_ss][EVERY_MEM,MEM_EL] >>
  strip_tac >- (
    ntac 7 gen_tac >>
    Cases >> fsrw_tac[DNF_ss][EVERY_MEM,MEM_EL] ) >>
  strip_tac >- fsrw_tac[DNF_ss][EVERY_MEM,MEM_EL] >>
  strip_tac >- fsrw_tac[DNF_ss][EVERY_MEM,MEM_EL] >>
  strip_tac >- ( rw[] >> fsrw_tac[DNF_ss][EVERY_MEM,MEM_EL] ) >>
  strip_tac >- fsrw_tac[DNF_ss][EVERY_MEM,MEM_EL] >>
  strip_tac >- fsrw_tac[DNF_ss][EVERY_MEM,MEM_EL])

val Cevaluate_all_vlabs = store_thm("Cevaluate_all_vlabs",
  ``(∀menv s env exp res. Cevaluate menv s env exp res ⇒ all_vlabs_menv menv ∧ all_vlabs_list s ∧ all_vlabs_list env ∧ all_labs exp ⇒
        all_vlabs_list (FST res) ∧ (∀v. (SND res = Cval v) ⇒ all_vlabs v) ∧ (∀v. (SND res = Cexc (Craise v)) ⇒ all_vlabs v)) ∧
    (∀menv s env es res. Cevaluate_list menv s env es res ⇒ all_vlabs_menv menv ∧ all_vlabs_list s ∧ all_vlabs_list env ∧ all_labs_list es ⇒
        all_vlabs_list (FST res) ∧ (∀vs. (SND res = Cval vs) ⇒ all_vlabs_list vs) ∧ (∀v. (SND res = Cexc (Craise v)) ⇒ all_vlabs v))``,
  ho_match_mp_tac Cevaluate_ind >>
  strip_tac >- fsrw_tac[DNF_ss][EVERY_MEM,MEM_EL] >>
  strip_tac >- fsrw_tac[DNF_ss][EVERY_MEM,MEM_EL] >>
  strip_tac >- fsrw_tac[DNF_ss][EVERY_MEM,MEM_EL] >>
  strip_tac >- simp[] >>
  strip_tac >- simp[] >>
  strip_tac >- fsrw_tac[DNF_ss][EVERY_MEM,MEM_EL] >>
  strip_tac >- fsrw_tac[DNF_ss][EVERY_MEM,MEM_EL,IN_FRANGE,FLOOKUP_DEF,all_vlabs_menv_def] >>
  strip_tac >- fsrw_tac[DNF_ss][EVERY_MEM,MEM_EL] >>
  strip_tac >- fsrw_tac[DNF_ss][EVERY_MEM,MEM_EL] >>
  strip_tac >- fsrw_tac[DNF_ss][EVERY_MEM,MEM_EL] >>
  strip_tac >- fsrw_tac[DNF_ss][EVERY_MEM,MEM_EL] >>
  strip_tac >- fsrw_tac[DNF_ss][EVERY_MEM,MEM_EL] >>
  strip_tac >- fsrw_tac[DNF_ss][EVERY_MEM,MEM_EL] >>
  strip_tac >- fsrw_tac[DNF_ss][EVERY_MEM,MEM_EL] >>
  strip_tac >- simp[] >>
  strip_tac >- fsrw_tac[DNF_ss][EVERY_MEM,MEM_EL] >>
  strip_tac >- (
    simp[] >>
    simp_tac pure_ss [EVERY_MEM,MEM_EL,GSYM LEFT_FORALL_IMP_THM] >>
    simp[] >> rw[] >> fsrw_tac[DNF_ss][EVERY_MEM,MEM_EL] ) >>
  strip_tac >- (
    rpt gen_tac >> ntac 2 strip_tac >> fs[] >> rfs[] >>
    BasicProvers.EVERY_CASE_TAC >> rfs[EVERY_REVERSE] >> fs[EVERY_REVERSE] >>
    first_x_assum match_mp_tac >>
    simp[EVERY_MAP,EVERY_GENLIST] >>
    fsrw_tac[DNF_ss][EVERY_MEM,MEM_EL] >>
    metis_tac[all_labs_def] ) >>
  strip_tac >- fsrw_tac[DNF_ss][EVERY_MEM,MEM_EL] >>
  strip_tac >- fsrw_tac[DNF_ss][EVERY_MEM,MEM_EL] >>
  strip_tac >- (
    ntac 3 gen_tac >>
    Cases >> ntac 2 gen_tac >>
    Cases >> rw[] >>
    fs[el_check_def,EVERY_MEM] >>
    BasicProvers.EVERY_CASE_TAC >>
    fsrw_tac[DNF_ss][EVERY_MEM,MEM_EL] >>
    metis_tac[MEM_EL]) >>
  strip_tac >- fsrw_tac[DNF_ss][EVERY_MEM,MEM_EL] >>
  strip_tac >- (
    ntac 3 gen_tac >>
    Cases >> ntac 3 gen_tac >>
    Cases >> TRY (Cases_on`l`) >> Cases >> TRY (Cases_on`l`) >> rw[] ) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    ntac 6 gen_tac >>
    Cases >> rw[] >> fs[] >>
    fs[EVERY_MEM] >>
    fsrw_tac[DNF_ss][EVERY_MEM] >>
    metis_tac[MEM_LUPDATE] ) >>
  strip_tac >- fsrw_tac[DNF_ss][EVERY_MEM,MEM_EL] >>
  strip_tac >- (
    ntac 7 gen_tac >>
    Cases >> fsrw_tac[DNF_ss][EVERY_MEM,MEM_EL] ) >>
  strip_tac >- fsrw_tac[DNF_ss][EVERY_MEM,MEM_EL] >>
  strip_tac >- fsrw_tac[DNF_ss][EVERY_MEM,MEM_EL] >>
  strip_tac >- ( rw[] >> fsrw_tac[DNF_ss][EVERY_MEM,MEM_EL] ) >>
  strip_tac >- fsrw_tac[DNF_ss][EVERY_MEM,MEM_EL] >>
  strip_tac >- fsrw_tac[DNF_ss][EVERY_MEM,MEM_EL])

(* TODO: move *)
val set_lunion = store_thm("set_lunion",
  ``∀l1 l2. set (lunion l1 l2) = set l1 ∪ set l2``,
  Induct >> simp[lunion_def] >> rw[EXTENSION] >> metis_tac[])
val _ = export_rewrites["set_lunion"]

val set_lshift = store_thm("set_lshift",
  ``∀ls n. set (lshift n ls) = { m-n | m | m ∈ set ls ∧ n ≤ m}``,
  Induct >> rw[lshift_def,EXTENSION,MEM_MAP,MEM_FILTER,EQ_IMP_THM] >>
  srw_tac[ARITH_ss,SATISFY_ss][] >> fsrw_tac[ARITH_ss][] >>
  TRY(qexists_tac`h`>>simp[]>>NO_TAC)>>
  TRY(qexists_tac`v`>>simp[]>>NO_TAC)>>
  TRY(qexists_tac`m`>>simp[]>>NO_TAC))
val _ = export_rewrites["set_lshift"]

val free_vars_list_MAP = store_thm("free_vars_list_MAP",
  ``∀es. set (free_vars_list es) = set (FLAT (MAP free_vars es))``,
  Induct >> simp[])

val free_vars_defs_MAP = store_thm("free_vars_defs_MAP",
  ``∀n defs. set (free_vars_defs n defs) = set (FLAT (MAP (free_vars_def n) defs))``,
  gen_tac >> Induct >> simp[])

(* TODO: move? *)
val Cexc_rel_def = Define`
  (Cexc_rel R (Craise v1) (Craise v2) = R v1 v2) ∧
  (Cexc_rel R Ctype_error Ctype_error = T) ∧
  (Cexc_rel _ _ _ = F)`
val _ = export_rewrites["Cexc_rel_def"]

val Cresult_rel_def = Define`
(Cresult_rel R1 R2 (Cval v1) (Cval v2) = R1 v1 v2) ∧
(Cresult_rel R1 R2 (Cexc e1) (Cexc e2) = Cexc_rel R2 e1 e2) ∧
(Cresult_rel _ _ _ _ = F)`
val _ = export_rewrites["Cresult_rel_def"]

val Cexc_rel_Craise1 = store_thm("Cexc_rel_Craise1",
  ``Cexc_rel R (Craise v) e = ∃v'. (e = Craise v') ∧ R v v'``,
  Cases_on`e`>>rw[])
val Cexc_rel_Craise2 = store_thm("Cexc_rel_Craise2",
  ``Cexc_rel R e (Craise v) = ∃v'. (e = Craise v') ∧ R v' v``,
  Cases_on`e`>>rw[])
val Cexc_rel_Ctype_error = store_thm("Cexc_rel_Ctype_error",
  ``(Cexc_rel R Ctype_error e = (e = Ctype_error)) ∧
    (Cexc_rel R e Ctype_error = (e = Ctype_error))``,
  Cases_on`e`>>rw[])
val _ = export_rewrites["Cexc_rel_Craise1","Cexc_rel_Craise2","Cexc_rel_Ctype_error"]

val Cresult_rel_Cval = store_thm(
"Cresult_rel_Cval",
``Cresult_rel R1 R2 (Cval v) r = ∃v'. (r = Cval v') ∧ R1 v v'``,
Cases_on `r` >> rw[])
val Cresult_rel_Cexc1 = store_thm(
"Cresult_rel_Cexc1",
``Cresult_rel R1 R2 (Cexc e) r = ∃e'. (r = Cexc e') ∧ Cexc_rel R2 e e'``,
Cases_on `r` >> rw[EQ_IMP_THM])
val Cresult_rel_Cexc2 = store_thm(
"Cresult_rel_Cexc2",
``Cresult_rel R1 R2 r (Cexc e) = ∃e'. (r = Cexc e') ∧ Cexc_rel R2 e' e``,
Cases_on `r` >> rw[EQ_IMP_THM])
val _ = export_rewrites["Cresult_rel_Cval","Cresult_rel_Cexc1","Cresult_rel_Cexc2"]

val Cexc_rel_refl = store_thm(
"Cexc_rel_refl",
  ``(∀x. R x x) ⇒ ∀x. Cexc_rel R x x``,
strip_tac >> Cases >> rw[])
val _ = export_rewrites["Cexc_rel_refl"]

val Cresult_rel_refl = store_thm(
"Cresult_rel_refl",
``(∀x. R1 x x) ∧ (∀x. R2 x x) ⇒ ∀x. Cresult_rel R1 R2 x x``,
strip_tac >> Cases >> rw[])
val _ = export_rewrites["Cresult_rel_refl"]

val Cexc_rel_trans = store_thm(
"Cexc_rel_trans",
``(∀x y z. R x y ∧ R y z ⇒ R x z) ⇒ (∀x y z. Cexc_rel R x y ∧ Cexc_rel R y z ⇒ Cexc_rel R x z)``,
rw[] >>
Cases_on `x` >> fs[] >> rw[] >> fs[] >> PROVE_TAC[])

val Cresult_rel_trans = store_thm(
"Cresult_rel_trans",
``(∀x y z. R1 x y ∧ R1 y z ⇒ R1 x z) ∧ (∀x y z. R2 x y ∧ R2 y z ⇒ R2 x z) ⇒ (∀x y z. Cresult_rel R1 R2 x y ∧ Cresult_rel R1 R2 y z ⇒ Cresult_rel R1 R2 x z)``,
rw[] >>
Cases_on `x` >> fs[] >> rw[] >> fs[] >> PROVE_TAC[Cexc_rel_trans])

val Cexc_rel_sym = store_thm(
"Cexc_rel_sym",
``(∀x y. R x y ⇒ R y x) ⇒ (∀x y. Cexc_rel R x y ⇒ Cexc_rel R y x)``,
rw[] >> Cases_on `x` >> fs[])

val Cresult_rel_sym = store_thm(
"Cresult_rel_sym",
``(∀x y. R1 x y ⇒ R1 y x) ∧ (∀x y. R2 x y ⇒ R2 y x) ⇒ (∀x y. Cresult_rel R1 R2 x y ⇒ Cresult_rel R1 R2 y x)``,
rw[] >> Cases_on `x` >> fs[Cexc_rel_sym])

val every_Cresult_def = Define`
  (every_Cresult P1 P2 (Cval v) = P1 v) ∧
  (every_Cresult P1 P2 (Cexc (Craise v)) = P2 v) ∧
  (every_Cresult P1 P2 (Cexc Ctype_error) = T)`
val _ = export_rewrites["every_Cresult_def"]

val every_Cresult_P1 = store_thm("every_Cresult_P1",
  ``every_Cresult P1 P2 (Cexc e) ⇒ every_Cresult P1' P2 (Cexc e)``,
  Cases_on`e`>> rw[])
val _ = export_rewrites["every_Cresult_P1"]

val Cmap_result_def = Define`
  (Cmap_result f (Rval v) = Cval (f v)) ∧
  (Cmap_result f (Rerr (Rraise Bind_error)) = Cexc (Craise CBind_excv)) ∧
  (Cmap_result f (Rerr (Rraise Div_error)) = Cexc (Craise CDiv_excv)) ∧
  (Cmap_result f (Rerr (Rraise (Int_error n))) = Cexc (Craise (CLitv (IntLit n)))) ∧
  (Cmap_result f (Rerr Rtype_error) = Cexc Ctype_error)`
val _ = export_rewrites["Cmap_result_def"]

(* Cevaluate functional equations *)

val Cevaluate_lit = store_thm(
"Cevaluate_lit",
``∀menv s env l res. Cevaluate menv s env (CLit l) res = (res = (s, Cval (CLitv l)))``,
rw[Once Cevaluate_cases])

val Cevaluate_var = store_thm(
"Cevaluate_var",
``∀menv s env vn res. Cevaluate menv s env (CVar (Short vn)) res = (vn < LENGTH env ∧ (res = (s, Cval (EL vn env))))``,
rw[Once Cevaluate_cases] >> PROVE_TAC[])

val _ = export_rewrites["Cevaluate_lit","Cevaluate_var"]

val Cevaluate_con = store_thm(
"Cevaluate_con",
``∀menv s env cn es res. Cevaluate menv s env (CCon cn es) res ⇔
(∃s' vs. Cevaluate_list menv s env es (s', Cval vs) ∧ (res = (s', Cval (CConv cn vs)))) ∨
(∃s' err. Cevaluate_list menv s env es (s', Cexc err) ∧ (res = (s', Cexc err)))``,
rw[Once Cevaluate_cases] >> PROVE_TAC[])

val Cevaluate_tageq = store_thm(
"Cevaluate_tageq",
``∀menv s env exp n res. Cevaluate menv s env (CTagEq exp n) res ⇔
  (∃s' m vs. Cevaluate menv s env exp (s', Cval (CConv m vs)) ∧ (res = (s', Cval (CLitv (Bool (n = m)))))) ∨
  (∃s' err. Cevaluate menv s env exp (s', Cexc err) ∧ (res = (s', Cexc err)))``,
rw[Once Cevaluate_cases] >> PROVE_TAC[])

val Cevaluate_let = store_thm(
"Cevaluate_let",
``∀menv s env e b res. Cevaluate menv s env (CLet e b) res ⇔
(∃s' v. Cevaluate menv s env e (s', Cval v) ∧
     Cevaluate menv s' (v::env) b res) ∨
(∃s' err. Cevaluate menv s env e (s', Cexc err) ∧ (res = (s', Cexc err)))``,
rw[Once Cevaluate_cases] >> PROVE_TAC[])

val Cevaluate_proj = store_thm(
"Cevaluate_proj",
``∀menv s env exp n res. Cevaluate menv s env (CProj exp n) res ⇔
  (∃s' m vs. Cevaluate menv s env exp (s', Cval (CConv m vs)) ∧ (n < LENGTH vs) ∧ (res = (s', Cval (EL n vs)))) ∨
  (∃s' err. Cevaluate menv s env exp (s', Cexc err) ∧ (res = (s', Cexc err)))``,
rw[Once Cevaluate_cases] >> PROVE_TAC[])

(* syneq equivalence relation lemmas *)

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
  ``(syneq (CLitv l1) v2 = (v2 = CLitv l1)) ∧
    (syneq v1 (CLitv l2) = (v1 = CLitv l2)) ∧
    (syneq (CLoc n1) v2 = (v2 = CLoc n1)) ∧
    (syneq v1 (CLoc n2) = (v1 = CLoc n2))``,
  rw[] >> fs[Once syneq_cases] >> rw[EQ_IMP_THM])
val _ = export_rewrites["syneq_lit_loc"]

val Cexp_only_ind =
   TypeBase.induction_of``:Cexp``
|> Q.SPECL[`P`,`K T`,`K T`,`K T`,`EVERY P`]
|> SIMP_RULE (srw_ss())[]
|> UNDISCH_ALL
|> CONJUNCT1
|> DISCH_ALL
|> Q.GEN`P`

val syneq_exp_refl = store_thm("syneq_exp_refl",
  ``(∀e z V. (∀v. v < z ⇒ V v v) ⇒ syneq_exp z z V e e) ∧
    (∀defs z V U d1. (∀v. v < z ⇒ V v v) ∧ (∀v1 v2. U v1 v2 = (v1 < LENGTH (d1++defs) ∧ (v2 = v1))) ∧
      EVERY (λd. (∀cd az e. (d = (cd,az,e)) ⇒ ∀z V. (∀v. v < z ⇒ V v v) ⇒ syneq_exp z z V e e)) d1 ⇒
      syneq_defs z z V (d1++defs) (d1++defs) U) ∧
    (∀d z V U. (∀v. v < z ⇒ V v v) ∧  (∀v1 v2. U v1 v2 = ((v1 = 0) ∧ (v2 = 0))) ⇒
      (∀cd az e. (d = (cd,az,e)) ⇒ ∀z V. (∀v. v < z ⇒ V v v) ⇒ syneq_exp z z V e e) ∧
      syneq_defs z z V [d] [d] U) ∧
    (∀(x:num#Cexp) z V. (∀v. v < z ⇒ V v v) ⇒ syneq_exp z z V (SND x) (SND x)) ∧
    (∀es z V. (∀v. v < z ⇒ V v v) ⇒ EVERY2 (syneq_exp z z V) es es)``,
  ho_match_mp_tac (TypeBase.induction_of``:Cexp``) >>
  strip_tac >- ( rw[] >> rw[Once syneq_exp_cases] ) >>
  strip_tac >- (
    rw[] >> rw[Once syneq_exp_cases] >>
    first_x_assum match_mp_tac >> simp[] >>
    Cases >> srw_tac[ARITH_ss][] ) >>
  strip_tac >- (
    rw[Once syneq_exp_cases] >>
    Cases_on`i`>>fs[]>>
    Cases_on`a < z` >> fsrw_tac[ARITH_ss][] ) >>
  strip_tac >- rw[Once syneq_exp_cases] >>
  strip_tac >- (
    rw[] >> rw[Once syneq_exp_cases] >>
    fsrw_tac[DNF_ss][EVERY2_EVERY,EVERY_MEM,MEM_ZIP,MEM_EL] ) >>
  strip_tac >- ( rw[] >> rw[Once syneq_exp_cases] ) >>
  strip_tac >- ( rw[] >> rw[Once syneq_exp_cases] ) >>
  strip_tac >- (
    rw[] >> rw[Once syneq_exp_cases] >>
    first_x_assum match_mp_tac >> simp[] >>
    Cases >> srw_tac[ARITH_ss][] ) >>
  strip_tac >- (
    rw[] >> rw[Once syneq_exp_cases] >>
    qexists_tac`λv1 v2. v1 < LENGTH defs ∧ (v2 = v1)` >>
    conj_tac >- (
      fsrw_tac[DNF_ss][] >>
      `defs = [] ++ defs` by rw[] >>
      POP_ASSUM SUBST1_TAC >>
      first_x_assum match_mp_tac >>
      simp[] ) >>
    first_x_assum match_mp_tac >>
    srw_tac[ARITH_ss][] >>
    Cases_on`v < LENGTH defs`>>fsrw_tac[ARITH_ss][]) >>
  strip_tac >- (
    rw[] >> rw[Once syneq_exp_cases] >>
    fsrw_tac[DNF_ss][EVERY2_EVERY,EVERY_MEM,MEM_ZIP,MEM_EL]) >>
  strip_tac >- ( rw[] >> rw[Once syneq_exp_cases] ) >>
  strip_tac >- ( rw[] >> rw[Once syneq_exp_cases] ) >>
  strip_tac >- ( rw[] >> rw[Once syneq_exp_cases] ) >>
  strip_tac >- ( rw[] >> rw[Once syneq_exp_cases] ) >>
  strip_tac >- (
    rw[] >>
    simp[Once syneq_exp_cases] >>
    rpt gen_tac >> strip_tac >>
    res_tac >> fs[] >>
    fs[EVERY_MEM,MEM_EL] >>
    fsrw_tac[DNF_ss][] >>
    qabbrev_tac`p = EL n1 d1` >>
    PairCases_on`p`>>fs[syneq_cb_aux_def,LET_THM,UNCURRY] >>
    Cases_on`p0`>>TRY(PairCases_on`x`)>>fs[syneq_cb_aux_def] >- (
      first_x_assum (match_mp_tac o MP_CANON) >>
      qexists_tac`n1` >> simp[] >>
      simp[syneq_cb_V_def] >>
      srw_tac[ARITH_ss][] ) >>
    conj_tac >- (
      strip_tac >>
      first_x_assum (match_mp_tac o MP_CANON) >>
      qexists_tac`n1`>>simp[]>>
      simp[syneq_cb_V_def] >>
      srw_tac[ARITH_ss][] ) >>
    conj_tac >- (
      simp[EVERY_MEM,MEM_EL] >>
      PROVE_TAC[] ) >>
    simp[EVERY_MEM,MEM_EL] >>
    PROVE_TAC[] ) >>
  strip_tac >- (
    rw[] >>
    fsrw_tac[DNF_ss][] >>
    `d1 ++ d::defs = (d1 ++ [d]) ++ defs` by rw[] >>
    pop_assum SUBST1_TAC >>
    first_x_assum match_mp_tac >>
    simp[] >>
    rw[] >>
    first_x_assum (match_mp_tac o MP_CANON) >>
    simp[] >>
    qexists_tac`0`>>simp[] >>
    qexists_tac`λv1 v2. (v1 = 0) ∧ (v2 = 0)` >> simp[] ) >>
  strip_tac >- (
    rw[] >> fs[] >>
    simp[Once syneq_exp_cases] >>
    PairCases_on`x`>>Cases_on`o'`>>TRY(PairCases_on`x`)>>fs[syneq_cb_aux_def] >- (
      first_x_assum match_mp_tac >>
      simp[syneq_cb_V_def] >>
      srw_tac[ARITH_ss][] ) >>
    strip_tac >>
    reverse conj_tac >- (
      fsrw_tac[DNF_ss][EVERY_MEM] ) >>
    first_x_assum match_mp_tac >>
    fsrw_tac[DNF_ss][EVERY_MEM,MEM_EL] >>
    srw_tac[ARITH_ss][syneq_cb_V_def] ) >>
  strip_tac >- (
    rw[] >> fs[] >>
    simp[Once syneq_exp_cases] >>
    simp[syneq_cb_aux_def,UNCURRY] ) >>
  strip_tac >- simp[] >>
  strip_tac >- rw[])

val syneq_defs_refl = store_thm("syneq_defs_refl",
  ``∀z V U defs. (∀v. v < z ⇒ V v v) ∧ (∀v1 v2. U v1 v2 ⇔ (v1 < LENGTH defs) ∧ (v2 = v1)) ⇒
    syneq_defs z z V defs defs U``,
  rw[] >>
  `defs = [] ++ defs` by rw[] >>
  pop_assum SUBST1_TAC >>
  match_mp_tac (CONJUNCT1 (CONJUNCT2 syneq_exp_refl)) >>
  simp[])

val syneq_refl = store_thm("syneq_refl",
  ``∀v. syneq v v``,
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

val syneq_exp_mono_V = store_thm("syneq_exp_mono_V",
  ``(∀ez1 ez2 V exp1 exp2. syneq_exp ez1 ez2 V exp1 exp2 ⇒ ∀V'. (∀x y. V x y ∧ x < ez1 ∧ y < ez2 ⇒ V' x y) ⇒ syneq_exp ez1 ez2 V' exp1 exp2) ∧
    (∀ez1 ez2 V defs1 defs2 U. syneq_defs ez1 ez2 V defs1 defs2 U ⇒
     ∀V'. (∀x y. V x y ∧ x < ez1 ∧ y < ez2 ⇒ V' x y) ⇒ syneq_defs ez1 ez2 V' defs1 defs2 U)``,
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
  TRY ( PROVE_TAC[] ) >>
  rpt gen_tac >> strip_tac >>
  last_x_assum(qspecl_then[`n1`,`n2`]mp_tac) >>
  simp[] >> strip_tac >>
  rpt (qpat_assum`A = B`(mp_tac o SYM)) >>
  reverse(rw[]) >- (
    fs[] >> fs[EVERY_MEM] >> rw[] >>
    first_x_assum match_mp_tac >>
    rfs[] >>
    Cases_on`b'`>>
    fs[syneq_cb_aux_def,LET_THM,UNCURRY,EVERY_MEM] ) >>
  fsrw_tac[DNF_ss][] >>
  first_x_assum (match_mp_tac o MP_CANON) >>
  simp[syneq_cb_V_def] >>
  srw_tac[ARITH_ss][] >>
  fsrw_tac[ARITH_ss][] >>
  first_x_assum match_mp_tac >>
  qabbrev_tac`p1 = EL n1 defs1` >>
  qabbrev_tac`p2 = EL n2 defs2` >>
  PairCases_on`p1`>>
  PairCases_on`p2`>>
  Cases_on`p10`>>TRY(PairCases_on`x'`)>>
  fs[syneq_cb_aux_def,LET_THM,UNCURRY] >>
  Cases_on`p20`>>TRY(PairCases_on`x'`)>>
  fs[syneq_cb_aux_def,LET_THM,UNCURRY] >>
  rw[] >> rpt (qpat_assum `X = CCEnv Y` mp_tac) >> srw_tac[ARITH_ss][] >>
  fsrw_tac[DNF_ss,ARITH_ss][EVERY_MEM,MEM_EL] >> rw[] )

val syneq_exp_sym_no_labs = store_thm("syneq_exp_sym_no_labs",
  ``(∀ez1 ez2 V exp1 exp2. syneq_exp ez1 ez2 V exp1 exp2 ⇒ no_labs exp2 ⇒ syneq_exp ez2 ez1 (inv V) exp2 exp1) ∧
    (∀ez1 ez2 V defs1 defs2 V'. syneq_defs ez1 ez2 V defs1 defs2 V' ⇒ no_labs_defs defs2 ⇒ syneq_defs ez2 ez1 (inv V) defs2 defs1 (inv V'))``,
  ho_match_mp_tac syneq_exp_ind >>
  strip_tac >- ( rw[] >> rw[Once syneq_exp_cases]) >>
  strip_tac >- (
    rw[] >> rw[Once syneq_exp_cases] >>
    match_mp_tac (MP_CANON (CONJUNCT1 syneq_exp_mono_V)) >>
    fs[] >> HINT_EXISTS_TAC >>
    simp[inv_DEF] >> Cases >> simp[] ) >>
  strip_tac >- ( rw[] >> rw[Once syneq_exp_cases,inv_DEF] ) >>
  strip_tac >- ( rw[] >> rw[Once syneq_exp_cases,inv_DEF] ) >>
  strip_tac >- ( rw[] >> rw[Once syneq_exp_cases] ) >>
  strip_tac >- (
    rw[] >> rw[Once syneq_exp_cases] >>
    fs[EVERY2_EVERY,EVERY_MEM,FORALL_PROD,inv_DEF] >>
    rfs[MEM_ZIP] >> rw[] >>
    fsrw_tac[DNF_ss][MEM_EL]) >>
  strip_tac >- ( rw[] >> rw[Once syneq_exp_cases] ) >>
  strip_tac >- ( rw[] >> rw[Once syneq_exp_cases] ) >>
  strip_tac >- (
    rw[] >> rw[Once syneq_exp_cases] >>
    match_mp_tac (MP_CANON (CONJUNCT1 syneq_exp_mono_V)) >>
    fs[] >> HINT_EXISTS_TAC >>
    simp[inv_DEF] >> Cases >> simp[] ) >>
  strip_tac >- (
    rw[] >> rw[Once syneq_exp_cases] >>
    qexists_tac`inv V'` >> simp[] >>
    fs[] >>
    match_mp_tac (MP_CANON(CONJUNCT1 syneq_exp_mono_V)) >>
    HINT_EXISTS_TAC >> simp[] >>
    simp[inv_DEF] >>
    rw[] >> simp[]) >>
  strip_tac >- (
    rw[] >> simp[Once syneq_exp_cases] >> fs[] >>
    fs[EVERY2_EVERY,EVERY_MEM,MEM_ZIP,FORALL_PROD] >> rfs[MEM_ZIP] >>
    fsrw_tac[DNF_ss][MEM_EL]) >>
  strip_tac >- ( rw[] >> rw[Once syneq_exp_cases] ) >>
  strip_tac >- ( rw[] >> rw[Once syneq_exp_cases] ) >>
  strip_tac >- ( rw[] >> rw[Once syneq_exp_cases] ) >>
  strip_tac >- ( rw[] >> rw[Once syneq_exp_cases] ) >>
  rw[] >>
  simp[Once syneq_exp_cases] >>
  simp[inv_DEF] >>
  rpt gen_tac >> strip_tac >>
  first_x_assum(qspecl_then[`n2`,`n1`]mp_tac) >>
  simp[] >> strip_tac >>
  ntac 2(qpat_assum`X = Y`(mp_tac o SYM)) >>
  ntac 2 strip_tac >> simp[] >>
  conj_asm1_tac >- (
    rw[] >> fs[EVERY_MEM,MEM_EL,GSYM LEFT_FORALL_IMP_THM] >>
    `no_labs_def (SOME d,e)` by PROVE_TAC[] >> fs[] ) >>
  strip_tac >> fs[inv_syneq_cb_V] >>
  conj_tac >- (
    first_x_assum match_mp_tac >>
    Cases_on`EL n1 defs2`>>fs[] >>
    Cases_on`q`>>PairCases_on`r`>>fs[syneq_cb_aux_def]>>
    fs[EVERY_MEM,MEM_EL,GSYM LEFT_FORALL_IMP_THM] >>
    last_x_assum(qspec_then`n1`mp_tac) >> simp[] ) >>
  rpt gen_tac >> strip_tac >>
  fs[EVERY_MEM,MEM_EL,GSYM LEFT_FORALL_IMP_THM])

val syneq_sym_no_vlabs = store_thm("syneq_sym_no_vlabs",
  ``∀x y. syneq x y ⇒ no_vlabs y ⇒ syneq y x``,
  ho_match_mp_tac syneq_ind >> rw[] >- (
    rw[] >> simp[Once syneq_cases] >>
    fs[EVERY2_EVERY,EVERY_MEM,MEM_ZIP,FORALL_PROD] >>
    rfs[MEM_ZIP,MEM_EL] >> PROVE_TAC[]) >>
  rw[] >> rw[Once syneq_cases] >>
  map_every qexists_tac[`inv V`,`inv V'`] >>
  simp[inv_DEF] >>
  PROVE_TAC[syneq_exp_sym_no_labs,no_labs_defs_MAP,EVERY_MEM,MEM_EL])

(*
val result_rel_syneq_sym = save_thm(
"result_rel_syneq_sym",
result_rel_sym
|> Q.GEN`R`
|> Q.ISPEC`syneq c`
|> SIMP_RULE std_ss[syneq_sym])

val EVERY2_syneq_sym = save_thm(
"EVERY2_syneq_sym",
EVERY2_sym
|> Q.GENL[`R2`,`R1`]
|> Q.ISPECL[`syneq c`,`syneq c`]
|> SIMP_RULE std_ss[syneq_sym])
*)

val syneq_cb_V_refl = store_thm("syneq_cb_V_refl",
  ``(∀x. (b(f-a) = CCEnv x) ⇒ c x x) ∧ (∀x. (b(f-a) = CCRef x) ⇒ d x x) ⇒
    syneq_cb_V a b b c d f f``,
  simp[syneq_cb_V_def] >>
  Cases_on`f < a`>>fsrw_tac[ARITH_ss][] >>
  Cases_on`b (f-a)`>>rw[])

val syneq_cb_aux_lemma = prove(
  ``(syneq_cb_aux n d z b = (t,az,e,j,r)) ∧ (r y = CCEnv k) ⇒ k < z``,
  PairCases_on`b`>>Cases_on`b0`>>TRY(PairCases_on`x`)>>rw[syneq_cb_aux_def,UNCURRY,LET_THM]>>fs[]>>
  pop_assum mp_tac >> rw[] >>
  fsrw_tac[ARITH_ss][])

val syneq_exp_trans = store_thm("syneq_exp_trans",
  ``(∀ez1 ez2 V e1 e2. syneq_exp ez1 ez2 V e1 e2 ⇒
      ∀ez3 V' e3. syneq_exp ez2 ez3 V' e2 e3 ⇒ syneq_exp ez1 ez3 (V' O V) e1 e3) ∧
    (∀ez1 ez2 V d1 d2 U. syneq_defs ez1 ez2 V d1 d2 U ⇒
      ∀ez3 V' d3 U'. syneq_defs ez2 ez3 V' d2 d3 U' ⇒ syneq_defs ez1 ez3 (V' O V) d1 d3 (U' O U))``,
  ho_match_mp_tac syneq_exp_ind >>
  strip_tac >- ( rw[] >> pop_assum mp_tac >> ntac 2 (rw[Once syneq_exp_cases] ) ) >>
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
    fs[EVERY2_EVERY,EVERY_MEM,MEM_ZIP] >> rw[] >>
    rpt (qpat_assum` LENGTH X = LENGTH Y` mp_tac) >>
    rpt strip_tac >>
    fs[MEM_ZIP,FORALL_PROD] >>
    PROVE_TAC[] ) >>
  strip_tac >- (
    rw[] >> pop_assum mp_tac >>
    simp[Once syneq_exp_cases] >> strip_tac >>
    simp[Once syneq_exp_cases] >>
    metis_tac[]) >>
  strip_tac >- (
    rw[] >> pop_assum mp_tac >>
    simp[Once syneq_exp_cases] >> strip_tac >>
    simp[Once syneq_exp_cases] >>
    metis_tac[]) >>
  strip_tac >- (
    rw[] >> pop_assum mp_tac >>
    simp[Once syneq_exp_cases] >> strip_tac >>
    simp[Once syneq_exp_cases] >>
    metis_tac[]) >>
  strip_tac >- (
    rw[] >> pop_assum mp_tac >>
    simp[Once syneq_exp_cases] >> strip_tac >>
    simp[Once syneq_exp_cases] >>
    metis_tac[]) >>
  strip_tac >- (
    rw[] >>
    pop_assum mp_tac >>
    simp[Once syneq_exp_cases] >>
    fsrw_tac[DNF_ss][] >>
    strip_tac >>
    simp[Once syneq_exp_cases] >>
    fsrw_tac[DNF_ss][O_DEF] >>
    rw[] >> TRY (res_tac >> NO_TAC) >>
    qmatch_assum_rename_tac`U' n0 n3`[] >>
    qmatch_assum_rename_tac`U' n2 n3`[] >>
    ntac 3 (last_x_assum(qspecl_then[`n1`,`n2`]mp_tac)) >> rw[] >>
    ntac 3 (last_x_assum(qspecl_then[`n2`,`n3`]mp_tac)) >> rw[] >>
    rpt (qpat_assum`A = B`(mp_tac o SYM)) >>
    simp[] >> ntac 4 strip_tac >>
    reverse conj_tac >- (
      simp[GSYM FORALL_AND_THM,GSYM IMP_CONJ_THM] >>
      rpt gen_tac >> ntac 2 strip_tac >>
      fs[] >> rfs[] >>
      fs[EVERY_MEM] >>
      metis_tac[] ) >>
    first_x_assum(qspecl_then[`az+j2'`,`syneq_cb_V az r1' r2' V' U'`,`e2'`]mp_tac) >>
    rw[] >> rfs[] >>
    match_mp_tac (MP_CANON(CONJUNCT1 (syneq_exp_mono_V))) >>
    fs[] >> rfs[] >>
    HINT_EXISTS_TAC >>
    simp[syneq_cb_V_def,O_DEF] >>
    srw_tac[ARITH_ss][] >>
    fsrw_tac[ARITH_ss][] >> rw[] >>
    metis_tac[] ))

val syneq_trans = store_thm("syneq_trans",
  ``∀x y. syneq x y ⇒ ∀z. syneq y z ⇒ syneq x z``,
  ho_match_mp_tac syneq_ind >> rw[] >- (
    rw[] >> pop_assum mp_tac >>
    simp[Once syneq_cases] >> strip_tac >>
    simp[Once syneq_cases] >>
    fs[EVERY2_EVERY,EVERY_MEM,MEM_ZIP] >> rw[] >>
    rpt (qpat_assum` LENGTH X = LENGTH Y` mp_tac) >>
    rpt strip_tac >>
    fs[MEM_ZIP,FORALL_PROD] >>
    PROVE_TAC[] ) >>
  rw[] >> pop_assum mp_tac >>
  simp[Once syneq_cases] >> strip_tac >>
  simp[Once syneq_cases] >> rw[] >>
  qexists_tac`V'' O V` >>
  qexists_tac`V''' O V'` >>
  simp[O_DEF] >> (
  conj_tac >- PROVE_TAC[syneq_exp_trans] ) >>
  TRY conj_tac >>
  TRY (PROVE_TAC[syneq_exp_trans]))

val EVERY2_syneq_refl = save_thm("EVERY2_syneq_refl",
EVERY2_refl
|> Q.GEN`R`
|> Q.ISPEC`syneq`
|> SIMP_RULE std_ss [syneq_refl])
val _ = export_rewrites["EVERY2_syneq_refl"]

val EVERY2_syneq_exp_refl = store_thm("EVERY2_syneq_exp_refl",
  ``(!x. x < z ⇒ V x x) ⇒ EVERY2 (syneq_exp z z V) ls ls``,
  strip_tac >>
  match_mp_tac EVERY2_refl >>
  rpt strip_tac >>
  match_mp_tac (CONJUNCT1 syneq_exp_refl) >>
  first_assum ACCEPT_TAC)

val EVERY2_syneq_trans = save_thm(
"EVERY2_syneq_trans",
EVERY2_trans
|> Q.GEN`R`
|> Q.ISPEC`syneq`
|> SIMP_RULE std_ss [GSYM AND_IMP_INTRO]
|> UNDISCH
|> (fn th => PROVE_HYP (PROVE[syneq_trans](hd(hyp th))) th)
|> SIMP_RULE std_ss [AND_IMP_INTRO])

val result_rel_syneq_refl = save_thm(
"result_rel_syneq_refl",
result_rel_refl
|> Q.GEN`R`
|> Q.ISPEC`syneq`
|> SIMP_RULE std_ss [syneq_refl])
val _ = export_rewrites["result_rel_syneq_refl"]

val Cresult_rel_syneq_refl = save_thm(
"Cresult_rel_syneq_refl",
Cresult_rel_refl
|> Q.GENL[`R2`,`R1`]
|> Q.ISPECL[`syneq`,`syneq`]
|> SIMP_RULE std_ss [syneq_refl])
val _ = export_rewrites["Cresult_rel_syneq_refl"]

val Cresult_rel_list_syneq_refl = save_thm(
"Cresult_rel_list_syneq_refl",
Cresult_rel_refl
|> Q.GENL[`R2`,`R1`]
|> Q.ISPECL[`EVERY2 syneq`,`syneq`]
|> SIMP_RULE std_ss [syneq_refl,EVERY2_syneq_refl])
val _ = export_rewrites["Cresult_rel_syneq_refl"]

val result_rel_syneq_trans = save_thm(
"result_rel_syneq_trans",
result_rel_trans
|> Q.GEN`R`
|> Q.ISPEC`syneq`
|> SIMP_RULE std_ss [GSYM AND_IMP_INTRO]
|> UNDISCH
|> (fn th => PROVE_HYP (PROVE[syneq_trans](hd(hyp th))) th)
|> SIMP_RULE std_ss [AND_IMP_INTRO])

val Cresult_rel_syneq_trans = save_thm(
"Cresult_rel_syneq_trans",
Cresult_rel_trans
|> Q.GENL[`R2`,`R1`]
|> Q.ISPECL[`syneq`,`syneq`]
|> SIMP_RULE std_ss [GSYM AND_IMP_INTRO]
|> UNDISCH |> UNDISCH
|> (fn th => PROVE_HYP (PROVE[syneq_trans](hd(hyp th))) th)
|> SIMP_RULE std_ss [AND_IMP_INTRO])

val Cresult_rel_list_syneq_trans = save_thm(
"Cresult_rel_list_syneq_trans",
Cresult_rel_trans
|> Q.GENL[`R2`,`R1`]
|> Q.ISPECL[`EVERY2 syneq`,`syneq`]
|> SIMP_RULE std_ss [GSYM AND_IMP_INTRO]
|> UNDISCH |> UNDISCH
|> (fn th => PROVE_HYP (PROVE[syneq_trans](hd(hyp th))) th)
|> (fn th => PROVE_HYP (PROVE[EVERY2_syneq_trans](hd(hyp th))) th)
|> SIMP_RULE std_ss [AND_IMP_INTRO])

val syneq_ov = store_thm("syneq_ov",
  ``(∀v1 v2. syneq v1 v2 ⇒ ∀m s. Cv_to_ov m s v1 = Cv_to_ov m s v2) ∧
    (∀vs1 vs2. EVERY2 (syneq) vs1 vs2 ⇒ ∀m s. EVERY2 (λv1 v2. Cv_to_ov m s v1 = Cv_to_ov m s v2) vs1 vs2)``,
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
  good_cmap (cenv:envC) m ⇔
    ALL_DISTINCT (MAP FST cenv) ∧
    ∀p1 p2.
      MEM p1 cenv ∧ MEM p2 cenv ⇒
      (FST p1) ∈ FDOM m ∧ (FST p2) ∈ FDOM m ∧
      ((FAPPLY m (FST p1) = FAPPLY m (FST p2)) ⇒ (p1 = p2))`

val Cevaluate_list_LENGTH = store_thm("Cevaluate_list_LENGTH",
  ``∀exps menv s env s' vs. Cevaluate_list menv s env exps (s', Cval vs) ⇒ (LENGTH vs = LENGTH exps)``,
  Induct >> rw[LENGTH_NIL] >> pop_assum mp_tac >>
  rw[Once Cevaluate_cases] >>
  fsrw_tac[DNF_ss][] >>
  first_x_assum match_mp_tac >>
  srw_tac[SATISFY_ss][])

val MAP_SND_free_labs_any_ez = store_thm("MAP_SND_free_labs_any_ez",
  ``(∀ez e ez'. MAP SND (free_labs ez e) = MAP SND (free_labs ez' e)) ∧
    (∀ez es ez'. MAP SND (free_labs_list ez es) = MAP SND (free_labs_list ez' es)) ∧
    (∀ez nz ix defs ez'. MAP SND (free_labs_defs ez nz ix defs) = MAP SND (free_labs_defs ez' nz ix defs)) ∧
    (∀ez nz ix def ez'. MAP SND (free_labs_def ez nz ix def) = MAP SND (free_labs_def ez' nz ix def))``,
  ho_match_mp_tac free_labs_ind >> rw[] >> metis_tac[])

val Cevaluate_store_SUBSET = store_thm("Cevaluate_store_SUBSET",
  ``(∀menv s env exp res. Cevaluate menv s env exp res ⇒ LENGTH s ≤ LENGTH (FST res)) ∧
    (∀menv s env exps res. Cevaluate_list menv s env exps res ⇒ LENGTH s ≤ LENGTH (FST res))``,
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
  ``∀p2 v1 v2 v. ((CevalPrim2 p2 v1 v2 = Cval v) ∨ (CevalPrim2 p2 v1 v2 = Cexc (Craise v))) ⇒ (all_Clocs v = {})``,
  Cases >> fs[] >> Cases >> fs[] >>
  TRY (Cases_on`l` >> fs[] >> Cases >> fs[] >> Cases_on `l` >> fs[] >> rw[] >> rw[]) >>
  Cases >> fs[] >> rw[] >> rw[])

val Cevaluate_Clocs = store_thm("Cevaluate_Clocs",
  ``(∀menv s env exp res. Cevaluate menv s env exp res ⇒
     BIGUNION (IMAGE (BIGUNION o IMAGE all_Clocs o set) (FRANGE menv)) ⊆ count (LENGTH s) ∧
     BIGUNION (IMAGE all_Clocs (set env)) ⊆ count (LENGTH s) ∧
     BIGUNION (IMAGE all_Clocs (set s)) ⊆ count (LENGTH s)
     ⇒
     BIGUNION (IMAGE all_Clocs (set (FST res))) ⊆ count (LENGTH (FST res)) ∧
     (∀v. (SND res = Cval v) ⇒ all_Clocs v ⊆ count (LENGTH (FST res))) ∧
     (∀v. (SND res = Cexc (Craise v)) ⇒ all_Clocs v ⊆ count (LENGTH (FST res)))) ∧
    (∀menv s env exps res. Cevaluate_list menv s env exps res ⇒
     BIGUNION (IMAGE (BIGUNION o IMAGE all_Clocs o set) (FRANGE menv)) ⊆ count (LENGTH s) ∧
     BIGUNION (IMAGE all_Clocs (set env)) ⊆ count (LENGTH s) ∧
     BIGUNION (IMAGE all_Clocs (set s)) ⊆ count (LENGTH s)
     ⇒
     BIGUNION (IMAGE all_Clocs (set (FST res))) ⊆ count (LENGTH (FST res)) ∧
     (∀vs. (SND res = Cval vs) ⇒ BIGUNION (IMAGE all_Clocs (set vs)) ⊆ count (LENGTH (FST res))) ∧
     (∀v. (SND res = Cexc (Craise v)) ⇒ all_Clocs v ⊆ count (LENGTH (FST res))))``,
  ho_match_mp_tac Cevaluate_strongind >>
  strip_tac >- rw[] >>
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
  strip_tac >- (
    rw[] >>
    fsrw_tac[DNF_ss][SUBSET_DEF,MEM_EL,IN_FRANGE,FLOOKUP_DEF] >>
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
  strip_tac >- (
    rpt gen_tac >> ntac 2 strip_tac >>
    fs[] >> rfs[] >>
    first_x_assum match_mp_tac >>
    imp_res_tac Cevaluate_store_SUBSET >>
    conj_tac >- (
      match_mp_tac SUBSET_TRANS >>
      qexists_tac`count (LENGTH s)` >>
      simp[] >> simp[SUBSET_DEF] >>
      fs[] >> simp[] ) >>
    qpat_assum`P ⇒ Q`mp_tac >>
    discharge_hyps >- (
      fsrw_tac[DNF_ss][SUBSET_DEF] >>
      metis_tac[LESS_LESS_EQ_TRANS] ) >>
    simp[] >> strip_tac >>
    PairCases_on`def`>>Cases_on`def0`>>fs[LET_THM] >- (
      fsrw_tac[DNF_ss][SUBSET_DEF] >>
      fsrw_tac[DNF_ss][MEM_GENLIST]>>
      fs[] >> metis_tac[LESS_LESS_EQ_TRANS] ) >>
    fsrw_tac[DNF_ss][SUBSET_DEF] >>
    PairCases_on`x`>>
    fsrw_tac[DNF_ss][MEM_MAP,IN_FRANGE,UNCURRY] >>
    rfs[] >>
    fsrw_tac[ARITH_ss][] >>
    fsrw_tac[DNF_ss][EVERY_MEM,MEM_EL] >>
    metis_tac[LESS_LESS_EQ_TRANS]) >>
  strip_tac >- (
    simp[] >> rpt gen_tac >> strip_tac >> strip_tac >>
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
    qpat_assum`P ⇒ Q`mp_tac >>
    imp_res_tac Cevaluate_store_SUBSET >>
    discharge_hyps >- (
      fsrw_tac[DNF_ss][SUBSET_DEF] >>
      metis_tac[LESS_LESS_EQ_TRANS] ) >>
    simp[] >> strip_tac >>
    fsrw_tac[DNF_ss][SUBSET_DEF] >>
    metis_tac[LESS_LESS_EQ_TRANS]) >>
  strip_tac >- rw[] >>
  rw[] >> fs[] >> rfs[] >>
  imp_res_tac Cevaluate_store_SUBSET >>
  qpat_assum`P ⇒ Q`mp_tac >>
  discharge_hyps >- (
    fsrw_tac[DNF_ss][SUBSET_DEF] >>
    metis_tac[LESS_LESS_EQ_TRANS] ) >>
  simp[] >> strip_tac >>
  fsrw_tac[DNF_ss][SUBSET_DEF] >>
  metis_tac[LESS_LESS_EQ_TRANS])

(* simple cases of syneq preservation *)

val syneq_no_closures = store_thm("syneq_no_closures",
``∀v1 v2. syneq v1 v2 ⇒ (no_closures v2 = no_closures v1)``,
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
``∀v1 v2. syneq v1 v2 ⇒ no_closures v1 ⇒ (v1 = v2)``,
  ho_match_mp_tac Cv_ind >>
  rw[] >>
  pop_assum mp_tac >> simp[Once syneq_cases] >>
  pop_assum mp_tac >> simp[Once syneq_cases] >>
  rw[] >> fsrw_tac[ETA_ss,DNF_ss][EVERY2_EVERY,EVERY_MEM,FORALL_PROD] >>
  ntac 2 (pop_assum mp_tac) >>
  fsrw_tac[DNF_ss][MEM_ZIP,MEM_EL,LIST_EQ_REWRITE] >>
  metis_tac[])

val doPrim2_syneq = store_thm(
"doPrim2_syneq",
``∀v1 v2. syneq v1 v2 ⇒
    ∀ty op v. (doPrim2 ty op v v1 = doPrim2 ty op v v2) ∧
              (doPrim2 ty op v1 v = doPrim2 ty op v2 v)``,
ho_match_mp_tac Cv_ind >>
rw[] >> pop_assum mp_tac >>
simp[Once syneq_cases] >> rw[] >>
Cases_on `v` >> rw[])

val CevalPrim2_syneq = store_thm("CevalPrim2_syneq",
  ``∀p2 v11 v21 v12 v22.
    syneq v11 v12 ∧ syneq v21 v22 ⇒
    Cresult_rel syneq syneq (CevalPrim2 p2 v11 v21) (CevalPrim2 p2 v12 v22)``,
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
  ``∀uop s1 s2 v1 v2. EVERY2 (syneq) s1 s2 ∧ syneq v1 v2 ⇒
    EVERY2 (syneq) (FST (CevalPrim1 uop s1 v1)) (FST (CevalPrim1 uop s2 v2)) ∧
    Cresult_rel syneq syneq (SND (CevalPrim1 uop s1 v1)) (SND (CevalPrim1 uop s2 v2))``,
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
``∀s1 v1 v2 s2 w1 w2.
  syneq v1 w1 ∧ syneq v2 w2 ∧ EVERY2 (syneq) s1 s2 ⇒
  EVERY2 (syneq) (FST (CevalUpd s1 v1 v2)) (FST (CevalUpd s2 w1 w2)) ∧
  Cresult_rel syneq syneq (SND (CevalUpd s1 v1 v2)) (SND (CevalUpd s2 w1 w2))``,
  gen_tac >>
  Cases >> simp[] >>
  ntac 2 gen_tac >>
  Cases >> simp[] >>
  rw[] >> TRY (
    match_mp_tac EVERY2_LUPDATE_same >>
    rw[] ) >>
  PROVE_TAC[EVERY2_EVERY])

val Cevaluate_syneq = store_thm("Cevaluate_syneq",
  ``(∀menv s1 env1 exp1 res1. Cevaluate menv s1 env1 exp1 res1 ⇒
      ∀ez1 ez2 V s2 env2 exp2 res2.
        syneq_exp (LENGTH env1) (LENGTH env2) V exp1 exp2
      ∧ (∀v1 v2. V v1 v2 ∧ v1 < LENGTH env1 ∧ v2 < LENGTH env2 ⇒ syneq (EL v1 env1) (EL v2 env2))
      ∧ EVERY2 (syneq) s1 s2
      ⇒ ∃res2.
        Cevaluate menv s2 env2 exp2 res2 ∧
        EVERY2 (syneq) (FST res1) (FST res2) ∧
        Cresult_rel syneq syneq (SND res1) (SND res2)) ∧
    (∀menv s1 env1 es1 res1. Cevaluate_list menv s1 env1 es1 res1 ⇒
      ∀ez1 ez2 V s2 env2 es2 res2.
        EVERY2 (syneq_exp (LENGTH env1) (LENGTH env2) V) es1 es2
      ∧ (∀v1 v2. V v1 v2 ∧ v1 < LENGTH env1 ∧ v2 < LENGTH env2 ⇒ syneq (EL v1 env1) (EL v2 env2))
      ∧ EVERY2 (syneq) s1 s2
      ⇒ ∃res2.
        Cevaluate_list menv s2 env2 es2 res2 ∧
        EVERY2 (syneq) (FST res1) (FST res2) ∧
        Cresult_rel (EVERY2 (syneq)) syneq (SND res1) (SND res2))``,
  ho_match_mp_tac Cevaluate_strongind >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    simp[Once syneq_exp_cases] >>
    fsrw_tac[DNF_ss][] >>
    rw[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][EXISTS_PROD] >>
    metis_tac[]) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    simp[Once syneq_exp_cases] >>
    fsrw_tac[DNF_ss][] >>
    rw[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][EXISTS_PROD] >>
    metis_tac[]) >>
  strip_tac >- (
    rw[] >>
    rator_x_assum`syneq_exp`mp_tac >>
    simp[Once (syneq_exp_cases)] >>
    fsrw_tac[DNF_ss][] >>
    map_every qx_gen_tac[`e`,`b`] >>
    rw[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][] >>
    first_x_assum(qspecl_then[`V`,`s2'`,`env2`,`e`]mp_tac) >>
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
    last_x_assum(qspecl_then[`V`,`s2`,`env2`,`e`]mp_tac) >>
    simp[EXISTS_PROD] >> fsrw_tac[DNF_ss][] >>
    map_every qx_gen_tac[`s3`,`u`] >> strip_tac >>
    qmatch_assum_abbrev_tac`syneq_exp (k1+1) (k2+1) V' e' b` >>
    first_x_assum(qspecl_then[`V'`,`s3`,`u::env2`,`b`]mp_tac) >>
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
    first_x_assum(qspecl_then[`V`,`s2'`,`env2`,`e`]mp_tac) >>
    simp[EXISTS_PROD] >> metis_tac[] ) >>
  strip_tac >- (
    rw[] >>
    rator_x_assum`syneq_exp`mp_tac >>
    simp[Once (syneq_exp_cases)] >>
    rw[] >> simp[] >> metis_tac[]) >>
  strip_tac >- (
    rw[] >>
    rator_x_assum`syneq_exp`mp_tac >>
    simp[Once (syneq_exp_cases)] >>
    rw[Once Cevaluate_cases]) >>
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
    rw[] >> rw[] ) >>
  strip_tac >- (
    rw[] >>
    rator_x_assum`syneq_exp`mp_tac >>
    simp[Once (syneq_exp_cases)] >>
    fsrw_tac[DNF_ss][] >>
    qx_gen_tac`e2` >> rw[] >>
    simp[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][EXISTS_PROD] >>
    first_x_assum(qspecl_then[`V`,`s2`,`env2`,`e2`]mp_tac) >>
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
      metis_tac[] ) >>
    simp[Once Cevaluate_cases] >>
    first_x_assum match_mp_tac >>
    metis_tac[] ) >>
  strip_tac >- (
    rw[] >>
    rator_x_assum`syneq_exp`mp_tac >>
    simp[Once (syneq_exp_cases)] >>
    fsrw_tac[DNF_ss][] >>
    simp[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][EXISTS_PROD] >>
    qx_gen_tac`e2` >> rw[] >>
    first_x_assum(qspecl_then[`V`,`s2`,`env2`,`e2`]mp_tac) >>
    simp[Once (syneq_cases)] >>
    rw[] >>
    fsrw_tac[DNF_ss][EVERY2_EVERY,EVERY_MEM,FORALL_PROD] >>
    metis_tac[MEM_ZIP]) >>
  strip_tac >- (
    rw[] >>
    rator_x_assum`syneq_exp`mp_tac >>
    simp[Once (syneq_exp_cases)] >>
    fsrw_tac[DNF_ss][] >>
    simp[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][EXISTS_PROD] >>
    metis_tac[] ) >>
  strip_tac >- (
    rw[] >>
    rator_x_assum`syneq_exp`mp_tac >>
    simp[Once (syneq_exp_cases)] >>
    fsrw_tac[DNF_ss][] >>
    map_every qx_gen_tac[`e`,`b`] >>
    rw[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][] >>
    disj1_tac >>
    last_x_assum(qspecl_then[`V`,`s2`,`env2`,`e`]mp_tac) >>
    simp[EXISTS_PROD] >> fsrw_tac[DNF_ss][] >>
    map_every qx_gen_tac[`s3`,`v3`] >> strip_tac >>
    qmatch_assum_abbrev_tac`syneq_exp (k1+1) (k2+1) V' e' b` >>
    first_x_assum(qspecl_then[`V'`,`s3`,`v3::env2`,`b`]mp_tac) >>
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
    fsrw_tac[DNF_ss][] >>
    map_every qx_gen_tac[`e2`,`b2`] >>
    rw[] >> fsrw_tac[DNF_ss][] >>
    first_x_assum(qspecl_then[`V`,`s2`,`env2`,`e2`]mp_tac) >>
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
    fsrw_tac[DNF_ss][] >>
    map_every qx_gen_tac[`e2`,`es2`] >>
    strip_tac >>
    simp[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][] >>
    disj1_tac >>
    last_x_assum(qspecl_then[`V`,`s2`,`env2`,`e2`]mp_tac) >>
    simp[GSYM AND_IMP_INTRO] >> disch_then(mp_tac o UNDISCH_ALL) >>
    simp[EXISTS_PROD] >>
    simp[Once syneq_cases] >>
    simp_tac(std_ss++DNF_ss)[] >>
    map_every qx_gen_tac[`s2'`,`V'`,`cenv2`,`defs2`,`d2`,`U`] >>
    strip_tac >> qmatch_assum_rename_tac`U d1 d2`[] >>
    CONV_TAC(RESORT_EXISTS_CONV (fn ls => (List.drop(ls,2)@List.take(ls,2)))) >>
    map_every qexists_tac[`s2'`,`cenv2`,`defs2`,`d2`] >>
    simp[] >>
    first_x_assum(qspecl_then[`V`,`s2'`,`env2`,`es2`]mp_tac) >>
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
    strip_tac >>
    pop_assum(qspecl_then[`d1`,`d2`]mp_tac) >>
    simp[] >>
    qabbrev_tac`p1 = EL d1 defs` >>
    qabbrev_tac`p2 = EL d2 defs2` >>
    PairCases_on`p1`>>PairCases_on`p2` >> fs[] >>
    Cases_on`p20` >- (
      simp[syneq_cb_aux_def] >>
      Cases_on`p10` >- (
        fs[syneq_cb_aux_def] >>
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
      fs[syneq_cb_aux_def,LET_THM,UNCURRY] ) >>
    Cases_on`p10` >- (
      PairCases_on`x`>>fs[syneq_cb_aux_def,LET_THM,UNCURRY] >>
      rw[] >>
      `LENGTH vs2 = LENGTH vs` by fs[EVERY2_EVERY] >> fs[] >>
      fs[EXISTS_PROD] >>
      first_x_assum match_mp_tac >>
      rator_x_assum`syneq_exp`mp_tac >>
      qho_match_abbrev_tac`syneq_exp ez1 ez2 V2 ee1 ee2 ⇒ P` >>
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
    fs[] >> strip_tac >> rw[] >>
    PairCases_on`x` >>
    fs[syneq_cb_aux_def,LET_THM,UNCURRY] >>
    rw[] >>
    `LENGTH vs2 = LENGTH vs` by fs[EVERY2_EVERY] >> fs[] >>
    fs[EXISTS_PROD] >>
    rfs[] >>
    first_x_assum match_mp_tac >>
    rator_x_assum`syneq_exp`mp_tac >>
    qho_match_abbrev_tac`syneq_exp ez ez V2 ee ee ⇒ P` >>
    strip_tac >> simp[Abbr`P`] >>
    qexists_tac`V2` >>
    simp[Abbr`ez`] >> rfs[] >>
    fsrw_tac[ARITH_ss][] >>
    pop_assum kall_tac >>
    fs[EVERY2_EVERY,EVERY_MEM,FORALL_PROD] >>
    fsrw_tac[DNF_ss][MEM_ZIP] >>
    `LENGTH vs = LENGTH vs2` by rw[] >>
    qunabbrev_tac`V2` >>
    fsrw_tac[ARITH_ss][] >>
    simp[syneq_cb_V_def] >> rw[] >>
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
    last_x_assum(qspecl_then[`V`,`s2`,`env2`,`e2`]mp_tac) >>
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
    metis_tac[CevalPrim2_syneq,syneq_lit_loc] ) >>
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
    last_x_assum(qspecl_then[`V`,`s2`,`env2`,`e12`]mp_tac) >>
    simp[GSYM AND_IMP_INTRO] >> disch_then(mp_tac o UNDISCH_ALL) >>
    rw[] >>
    qmatch_assum_abbrev_tac`Cevaluate menv s2 env2 e12 (s3,Cval (CLitv (Bool b)))` >>
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
    qmatch_assum_rename_tac`syneq_exp (LENGTH env1) (LENGTH env2) V e1 e2`[] >>
    last_x_assum(qspecl_then[`V`,`s2`,`env2`,`e2`]mp_tac) >>
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
  qmatch_assum_rename_tac`syneq_exp (LENGTH env1) (LENGTH env2) V e1 e2`[] >>
  last_x_assum(qspecl_then[`V`,`s2`,`env2`,`e2`]mp_tac) >>
  simp[GSYM AND_IMP_INTRO] >> disch_then(mp_tac o UNDISCH_ALL) >>
  fsrw_tac[DNF_ss][] >>
  map_every qx_gen_tac[`s3`,`v3`] >>
  strip_tac >>
  CONV_TAC SWAP_EXISTS_CONV >> qexists_tac`s3` >>
  CONV_TAC SWAP_EXISTS_CONV >> qexists_tac`v3` >>
  simp[] >>
  first_x_assum match_mp_tac >>
  metis_tac[] )

val Cevaluate_any_syneq_store = store_thm("Cevaluate_any_syneq_store",
  ``∀menv s s' env exp res. Cevaluate menv s env exp res ∧ EVERY2 (syneq) s s' ⇒
      ∃res'. Cevaluate menv s' env exp res' ∧ EVERY2 (syneq) (FST res) (FST res') ∧ Cresult_rel syneq syneq (SND res) (SND res')``,
    rw[] >>
    qspecl_then[`menv`,`s`,`env`,`exp`,`res`]mp_tac (CONJUNCT1 Cevaluate_syneq) >> simp[] >>
    disch_then(qspecl_then[`$=`,`s'`,`env`,`exp`]mp_tac) >> simp[syneq_exp_refl])

val Cevaluate_list_any_syneq_any = store_thm("Cevaluate_list_any_syneq_any",
  ``∀menv s1 s2 env1 env2 e res. Cevaluate_list menv s1 env1 e res ∧ EVERY2 (syneq) s1 s2 ∧ EVERY2 (syneq) env1 env2 ⇒
      ∃res2. Cevaluate_list menv s2 env2 e res2 ∧ EVERY2 (syneq) (FST res) (FST res2) ∧ Cresult_rel (EVERY2 (syneq)) syneq (SND res) (SND res2)``,
    rw[] >>
    qspecl_then[`menv`,`s1`,`env1`,`e`,`res`]mp_tac (CONJUNCT2 Cevaluate_syneq) >> simp[] >>
    `LENGTH env1 = LENGTH env2` by fs[EVERY2_EVERY] >>
    disch_then(qspecl_then[`$=`,`s2`,`env2`,`e`]mp_tac) >> simp[syneq_exp_refl] >>
    discharge_hyps >- (
      fsrw_tac[DNF_ss][EVERY2_EVERY,EVERY_MEM,FORALL_PROD,MEM_ZIP,syneq_exp_refl] ) >> simp[])

(* Closed values *)

val (Cclosed_rules,Cclosed_ind,Cclosed_cases) = Hol_reln`
(Cclosed (CLitv l)) ∧
(EVERY (Cclosed) vs ⇒ Cclosed (CConv cn vs)) ∧
((EVERY (Cclosed) env) ∧
 n < LENGTH defs ∧
 (∀cd az b. MEM ((cd,az,b)) defs ⇒
    IS_NONE cd ∧ no_labs b ∧
    set (free_vars b) ⊆ count (az + LENGTH defs + LENGTH env))
⇒ Cclosed (CRecClos env defs n)) ∧
(Cclosed (CLoc m))`

val Cclosed_lit_loc = store_thm("Cclosed_lit_loc",
  ``Cclosed (CLitv l) ∧
    Cclosed (CLoc n)``,
  rw[Cclosed_rules])
val _ = export_rewrites["Cclosed_lit_loc"]

val doPrim2_closed = store_thm(
"doPrim2_closed",
``∀ty op v1 v2. every_Cresult Cclosed Cclosed (doPrim2 ty op v1 v2)``,
ntac 2 gen_tac >>
Cases >> TRY (Cases_on `l`) >>
Cases >> TRY (Cases_on `l`) >>
rw[] >> rw[Cclosed_cases])
val _ = export_rewrites["doPrim2_closed"];

val CevalPrim2_closed = store_thm(
"CevalPrim2_closed",
``∀p2 v1 v2. every_Cresult Cclosed Cclosed (CevalPrim2 p2 v1 v2)``,
Cases >> rw[])
val _ = export_rewrites["CevalPrim2_closed"];

val CevalPrim1_closed = store_thm(
"CevalPrim1_closed",
``∀uop s v. EVERY (Cclosed) s ∧ Cclosed v ⇒
  EVERY (Cclosed) (FST (CevalPrim1 uop s v)) ∧
  every_Cresult Cclosed Cclosed (SND (CevalPrim1 uop s v))``,
Cases >> rw[LET_THM,Cclosed_rules] >> rw[]
>- ( Cases_on`v`>>fs[] )
>- ( Cases_on`v`>>fs[] >>
  rw[el_check_def] >>
  fsrw_tac[DNF_ss][EVERY_MEM,MEM_EL]))

val CevalUpd_closed = store_thm(
"CevalUpd_closed",
``(∀s v1 v2. Cclosed v2 ⇒ every_Cresult Cclosed Cclosed (SND (CevalUpd s v1 v2))) ∧
  (∀s v1 v2. EVERY (Cclosed) s ∧ Cclosed v2 ⇒
    EVERY (Cclosed) (FST (CevalUpd s v1 v2)))``,
  conj_tac >>
  gen_tac >>
  Cases >> simp[] >- rw[] >>
  rpt gen_tac >> strip_tac >>
  rw[] >>
  fsrw_tac[DNF_ss][EVERY_MEM] >> rw[] >>
  imp_res_tac MEM_LUPDATE >> fs[])

val Cevaluate_closed = store_thm("Cevaluate_closed",
  ``(∀s env exp res. Cevaluate s env exp res
     ⇒ set (free_vars exp) ⊆ count (LENGTH env)
     ∧ no_labs exp
     ∧ EVERY (Cclosed) env
     ∧ EVERY (Cclosed) s
     ⇒
     EVERY (Cclosed) (FST res) ∧
     every_Cresult Cclosed (Cclosed) (SND res)) ∧
    (∀s env exps ress. Cevaluate_list s env exps ress
     ⇒ set (free_vars_list exps) ⊆ count (LENGTH env)
     ∧ no_labs_list exps
     ∧ EVERY (Cclosed) env
     ∧ EVERY (Cclosed) s
     ⇒
     EVERY (Cclosed) (FST ress) ∧
     every_Cresult (EVERY (Cclosed)) Cclosed (SND ress))``,
  ho_match_mp_tac Cevaluate_ind >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rpt gen_tac >> ntac 2 strip_tac >>
    fsrw_tac[DNF_ss][ADD1] >>
    rfs[] >>
    conj_tac >>
    first_x_assum(match_mp_tac o MP_CANON) >>
    fsrw_tac[DNF_ss][SUBSET_DEF,MEM_MAP,MEM_FILTER] >>
    Cases >> fsrw_tac[ARITH_ss][] >>
    rw[] >> res_tac >> fs[ADD1]) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rw[] >> fsrw_tac[DNF_ss][EVERY_MEM,MEM_EL] ) >>
  strip_tac >- ( rw[] >> rw[Once Cclosed_cases]) >>
  strip_tac >- (
    srw_tac[ETA_ss][FOLDL_UNION_BIGUNION] >> fs[] >>
    rw[Once Cclosed_cases] ) >>
  strip_tac >- (
    srw_tac[ETA_ss][FOLDL_UNION_BIGUNION] >> fs[] >>
    metis_tac[every_Cresult_P1]) >>
  strip_tac >- ( rw[] >> rw[Once Cclosed_cases]) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rw[] >> fs[] >>
    fsrw_tac[DNF_ss][Q.SPECL[`CConv m vs`] Cclosed_cases,EVERY_MEM,MEM_EL] ) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rpt gen_tac >> ntac 2 strip_tac >>
    first_x_assum match_mp_tac >>
    fsrw_tac[DNF_ss][SUBSET_DEF,ADD1,MEM_MAP,MEM_FILTER] >>
    Cases >> fsrw_tac[ARITH_ss][] >>
    rw[] >> res_tac >> fs[ADD1]) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rpt gen_tac >> ntac 2 strip_tac >>
    fs[FOLDL_FUPDATE_LIST,FOLDL_UNION_BIGUNION] >>
    first_x_assum match_mp_tac >>
    fsrw_tac[DNF_ss][SUBSET_DEF,LET_THM,MEM_MAP,MEM_FILTER] >>
    conj_tac >- (
      rw[] >> res_tac >>
      fsrw_tac[ARITH_ss][] ) >>
    lrw[EVERY_REVERSE,EVERY_GENLIST] >>
    simp[Once Cclosed_cases] >>
    fsrw_tac[DNF_ss][EVERY_MEM,free_vars_defs_MAP] >>
    fsrw_tac[DNF_ss][free_labs_defs_MAP,MEM_FLAT,MEM_GENLIST] >>
    conj_asm1_tac >- (
      rw[] >> res_tac >> Cases_on`cd`>>fs[]) >>
    simp[GSYM FORALL_AND_THM] >> rpt gen_tac >>
    simp[RIGHT_FORALL_IMP_THM,GSYM IMP_CONJ_THM] >>
    strip_tac >>
    res_tac >> fs[] >> BasicProvers.VAR_EQ_TAC >> fs[] >>
    fsrw_tac[DNF_ss][SUBSET_DEF,MEM_MAP] >>
    rpt strip_tac >> res_tac >>
    fsrw_tac[DNF_ss][SUBSET_DEF,MEM_MAP,MEM_FILTER] >>
    res_tac >>
    fsrw_tac[ARITH_ss][]) >>
  strip_tac >- (
    rpt gen_tac >> ntac 2 strip_tac >>
    fs[FOLDL_UNION_BIGUNION] >>
    first_x_assum match_mp_tac >>
    fsrw_tac[DNF_ss][SUBSET_DEF] >>
    PairCases_on`def`>>Cases_on`def0`>>fs[LET_THM] >- (
      simp[EVERY_REVERSE,EVERY_GENLIST] >>
      fs[Once Cclosed_cases] >>
      `MEM (NONE,def1,def2) defs` by metis_tac[MEM_EL] >>
      res_tac >> fsrw_tac[ARITH_ss][] >>
      fsrw_tac[DNF_ss][SUBSET_DEF] >>
      metis_tac[]) >>
    fs[Once Cclosed_cases] >>
    last_x_assum(qspecl_then[`SOME x`,`def1`,`def2`]mp_tac) >>
    discharge_hyps >- PROVE_TAC[MEM_EL] >>
    simp[]) >>
  strip_tac >- (
    rpt gen_tac >> ntac 2 strip_tac >>
    fsrw_tac[ETA_ss][FOLDL_UNION_BIGUNION] >>
    metis_tac[every_Cresult_P1]) >>
  strip_tac >- (
    rpt gen_tac >> ntac 2 strip_tac >>
    fsrw_tac[ETA_ss][FOLDL_UNION_BIGUNION] ) >>
  strip_tac >- (
    rpt gen_tac >> ntac 2 strip_tac >>
    full_simp_tac std_ss [free_vars_def,every_result_def] >>
    fs[] >> metis_tac[CevalPrim1_closed]) >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- ( rw[] >> metis_tac[every_Cresult_P1] ) >>
  strip_tac >- (
    rw[] >- (
      match_mp_tac (MP_CANON (CONJUNCT2 CevalUpd_closed)) >>
      rw[]) >>
    match_mp_tac (CONJUNCT1 CevalUpd_closed) >>
    rw[] ) >>
  strip_tac >- ( rw[] >> metis_tac[every_Cresult_P1] ) >>
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
    fs[] >> metis_tac[every_Cresult_P1]) >>
  rpt gen_tac >> ntac 2 strip_tac >>
  full_simp_tac std_ss [] >>
  fs[] )

(* mkshift *)

val mkshift_thm = store_thm("mkshift_thm",
 ``∀f k e z1 z2 V.
   k ≤ z1 ∧ k ≤ z2 ∧
   (∀x. MEM x (free_vars e) ∧ x < k ⇒ V x x) ∧
   (∀x. MEM x (free_vars e) ∧ k ≤ x ∧ x < z1 ⇒ V x (f(x-k)+k) ∧ (f(x-k)+k) < z2) ∧
   set (free_vars e) ⊆ count z1 ∧ no_labs e
   ⇒ syneq_exp z1 z2 V e (mkshift f k e)``,
 ho_match_mp_tac mkshift_ind >>
 strip_tac >- (rw[] >> rw[Once syneq_exp_cases]) >>
 strip_tac >- (
   rw[] >>
   rw[Once syneq_exp_cases] >>
   first_x_assum match_mp_tac >>
   fsrw_tac[ARITH_ss,QUANT_INST_ss[num_qp]][SUBSET_DEF,PRE_SUB1,ADD1,MEM_MAP,MEM_FILTER,GSYM LEFT_FORALL_IMP_THM] >>
   conj_tac >> TRY conj_tac >> Cases >> fsrw_tac[ARITH_ss][ADD1] >> rw[] >>
   res_tac >> fsrw_tac[ARITH_ss][]) >>
 strip_tac >- (
   rw[] >>
   rw[Once syneq_exp_cases] >>
   fsrw_tac[ARITH_ss][] ) >>
 strip_tac >- rw[Once syneq_exp_cases] >>
 strip_tac >- (
   rw[] >>
   rw[Once syneq_exp_cases] >>
   fsrw_tac[DNF_ss][FOLDL_UNION_BIGUNION,SUBSET_DEF,EVERY2_EVERY,EVERY_MEM,FORALL_PROD,MEM_ZIP,free_labs_list_MAP,MEM_FLAT,MEM_MAP] >>
   fsrw_tac[DNF_ss][free_vars_list_MAP,MEM_FLAT,MEM_MAP] >>
   fsrw_tac[DNF_ss][EL_MAP,MEM_EL] >> rw[]) >>
 strip_tac >- ( rw[] >> rw[Once syneq_exp_cases] ) >>
 strip_tac >- ( rw[] >> rw[Once syneq_exp_cases] ) >>
 strip_tac >- (
   rw[] >>
   rw[Once syneq_exp_cases] >>
   first_x_assum match_mp_tac >>
   fsrw_tac[ARITH_ss,QUANT_INST_ss[num_qp]][SUBSET_DEF,PRE_SUB1,ADD1,MEM_MAP,MEM_FILTER,GSYM LEFT_FORALL_IMP_THM] >>
   conj_tac >> TRY conj_tac >> Cases >> fsrw_tac[ARITH_ss][ADD1] >> rw[] >>
   res_tac >> fsrw_tac[ARITH_ss][]) >>
 strip_tac >- (
   simp[FOLDL_UNION_BIGUNION] >> rw[] >>
   rw[Once syneq_exp_cases] >>
   qexists_tac`λv1 v2. v1 < LENGTH defs ∧ (v2 = v1)` >>
   simp[] >>
   reverse conj_tac >- (
     first_x_assum match_mp_tac >>
     simp[] >>
     conj_tac >- (
       fsrw_tac[DNF_ss,ARITH_ss][MEM_MAP,MEM_FILTER,free_vars_defs_MAP] >>
       srw_tac[ARITH_ss][] >>
       Cases_on`x < LENGTH defs`>>fsrw_tac[ARITH_ss][]) >>
     conj_tac >- (
       gen_tac >> strip_tac >>
       first_x_assum(qspec_then`x-LENGTH defs`mp_tac) >>
       simp[] >>
       discharge_hyps >- (
         fsrw_tac[DNF_ss][SUBSET_DEF,free_vars_defs_MAP,MEM_MAP,MEM_FILTER,MEM_FLAT] >>
         disj2_tac >>
         qexists_tac`x` >>
         simp[] ) >>
       simp[]) >>
     fsrw_tac[ARITH_ss,DNF_ss][SUBSET_DEF,MEM_MAP,MEM_FILTER] >>
     qx_gen_tac`x` >> strip_tac >>
     rpt(first_x_assum(qspec_then`x`mp_tac)) >>
     simp[] ) >>
   simp[Once syneq_exp_cases] >>
   rw[EL_MAP] >>
   fs[free_labs_defs_MAP,EVERY_MEM,MEM_FLAT,MEM_GENLIST] >>
   qabbrev_tac`p = EL v2 defs` >>
   PairCases_on`p` >>
   reverse (Cases_on`p0`)>>simp[] >- (
    `MEM(SOME x,p1,p2)defs`by metis_tac[MEM_EL] >>
    res_tac >> fs[] ) >>
   simp[syneq_cb_aux_def] >>
   first_x_assum(qspecl_then[`p1`,`p2`]mp_tac) >>
   simp[] >> disch_then (match_mp_tac o MP_CANON) >>
   simp[] >>
   conj_tac >- metis_tac[MEM_EL] >>
   conj_tac >- (
     srw_tac[ARITH_ss][syneq_cb_V_def] >>
     REWRITE_TAC[SUB_PLUS] >>
     last_x_assum match_mp_tac >>
     simp[free_vars_defs_MAP] >>
     simp_tac(srw_ss()++DNF_ss)[] >>
     disj1_tac >>
     fsrw_tac[DNF_ss][MEM_FLAT,MEM_MAP,MEM_FILTER,free_vars_defs_MAP] >>
     qexists_tac`EL v2 defs` >>
     simp[MEM_MAP,MEM_FILTER] >>
     conj_tac >- metis_tac[MEM_EL] >>
     qexists_tac`x`>>simp[]) >>
   reverse conj_tac >- (
     fsrw_tac[DNF_ss,ARITH_ss][SUBSET_DEF,MEM_MAP,MEM_FILTER] >>
     conj_tac >- (
       qx_gen_tac`x` >> strip_tac >>
       fsrw_tac[DNF_ss,ARITH_ss][free_vars_defs_MAP,MEM_MAP,MEM_FILTER,MEM_FLAT] >>
       Cases_on`x<p1+LENGTH defs`>-simp[]>>
       (first_x_assum(qspecl_then[`x-p1-LENGTH defs`,`EL v2 defs`]mp_tac)) >>
       simp[MEM_MAP,MEM_FILTER] >>
       discharge_hyps >- ( conj_tac >- metis_tac[MEM_EL] >> qexists_tac`x` >> simp[] ) >>
       simp[] ) >>
     `MEM (NONE,p1,p2) defs` by metis_tac[MEM_EL] >>
     res_tac >> fs[]) >>
   srw_tac[ARITH_ss][syneq_cb_V_def] >- (
     fsrw_tac[ARITH_ss,DNF_ss][free_vars_defs_MAP,MEM_MAP,MEM_FILTER,MEM_FLAT] >>
     `x - (p1 + LENGTH defs) = x - p1 - LENGTH defs` by fsrw_tac[ARITH_ss][] >> pop_assum SUBST1_TAC >>
     `x - (k + (p1 + LENGTH defs)) = x - p1 - LENGTH defs - k` by fsrw_tac[ARITH_ss][] >> pop_assum SUBST1_TAC >>
     last_x_assum match_mp_tac >>
     qexists_tac`EL v2 defs` >> simp[MEM_MAP,MEM_FILTER] >>
     conj_tac >- metis_tac[MEM_EL] >>
     qexists_tac`x` >> simp[]) >>
   spose_not_then strip_assume_tac >>
   qpat_assum`~(x < y)`mp_tac >> simp[] >>
   fsrw_tac[DNF_ss,ARITH_ss][MEM_MAP,MEM_FILTER,MEM_FLAT,free_vars_defs_MAP] >>
   rw[AC ADD_ASSOC ADD_SYM] >>
   REWRITE_TAC[Once ADD_ASSOC] >>
   CONV_TAC(LAND_CONV(LAND_CONV(REWRITE_CONV[Once ADD_SYM]))) >>
   REWRITE_TAC[Once (GSYM ADD_ASSOC)] >>
   simp[] >>
   REWRITE_TAC[Once (ADD_ASSOC)] >>
   simp[] >>
   `x - (k + (p1 + LENGTH defs)) = x - p1 - LENGTH defs - k` by srw_tac[ARITH_ss][] >>
   pop_assum SUBST1_TAC >>
   last_x_assum match_mp_tac >>
   qexists_tac`EL v2 defs`>>simp[MEM_MAP,MEM_FILTER] >>
   conj_tac >- metis_tac[MEM_EL] >>
   qexists_tac`x` >> simp[]) >>
 strip_tac >- (
   rw[] >>
   rw[Once syneq_exp_cases] >>
   simp[EVERY2_EVERY,EVERY_MEM,FORALL_PROD,MEM_ZIP] >>
   rw[] >> simp[EL_MAP] >>
   fsrw_tac[DNF_ss][EXISTS_PROD,FORALL_PROD] >>
   first_x_assum (match_mp_tac o MP_CANON) >>
   `MEM (EL n es) es` by metis_tac[MEM_EL] >>
   simp[] >>
   fsrw_tac[DNF_ss][free_vars_list_MAP,MEM_FLAT,MEM_MAP] >>
   conj_tac >- metis_tac[] >>
   conj_tac >- metis_tac[ADD_SYM] >>
   fsrw_tac[DNF_ss][SUBSET_DEF,EVERY_MEM,MEM_FLAT,MEM_MAP] >>
   metis_tac[]) >>
 strip_tac >- ( rw[] >> rw[Once syneq_exp_cases] ) >>
 strip_tac >- ( rw[] >> rw[Once syneq_exp_cases] ) >>
 strip_tac >- ( rw[] >> rw[Once syneq_exp_cases] ) >>
 strip_tac >- ( rw[] >> rw[Once syneq_exp_cases] ))

val free_vars_mkshift = store_thm("free_vars_mkshift",
  ``∀f k e. set (free_vars (mkshift f k e)) = IMAGE (λv. if v < k then v else f (v-k) + k) (set (free_vars e))``,
  ho_match_mp_tac mkshift_ind >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rw[EXTENSION,MEM_MAP,MEM_FILTER] >>
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
      fsrw_tac[ARITH_ss,DNF_ss][] >>
      qexists_tac`m`>>simp[])) >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rw[free_vars_list_MAP] >>
    fsrw_tac[DNF_ss][Once EXTENSION,MEM_FLAT,MEM_MAP] >>
    fsrw_tac[DNF_ss][MEM_MAP,EQ_IMP_THM] >>
    metis_tac[] ) >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rw[EXTENSION] >>
    rw[EQ_IMP_THM]
    >- metis_tac[]
    >- (
      fsrw_tac[ARITH_ss][PRE_SUB1,MEM_MAP,MEM_FILTER] >>
      res_tac >>
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
      fsrw_tac[ARITH_ss][PRE_SUB1,MEM_MAP,MEM_FILTER,EQ_IMP_THM,GSYM LEFT_FORALL_IMP_THM,FORALL_AND_THM] >>
      res_tac >>
      srw_tac[ARITH_ss][] >>
      fsrw_tac[ARITH_ss][]
      >- (
        disj2_tac >>
        qexists_tac`m` >>
        simp[] )
      >- (
        disj2_tac >>
        fsrw_tac[ARITH_ss][] >>
        qexists_tac`k + (f (m - (k + 1))) + 1` >>
        simp[] ) >>
      Cases_on`k`>> fsrw_tac[ARITH_ss][] >>
      Cases_on`m`>>fsrw_tac[ARITH_ss][] >>
      disj2_tac >>
      qexists_tac`SUC (f n)`>>simp[ADD1])) >>
  strip_tac >- (
    simp[] >> rw[] >>
    simp[free_vars_defs_MAP] >>
    simp[LIST_TO_SET_MAP] >>
    qmatch_abbrev_tac`a ∪ b = c ∪ d` >>
    `b = d` by (
      unabbrev_all_tac >>
      simp[Once EXTENSION,MEM_FILTER] >>
      gen_tac >>
      srw_tac[DNF_ss][EQ_IMP_THM] >- (
        qexists_tac`v` >> simp[] ) >>
      qexists_tac`m` >> simp[] ) >>
    `a = c` by (
      unabbrev_all_tac >>
      simp[Once EXTENSION,MEM_FLAT,MEM_MAP] >>
      srw_tac[DNF_ss][EQ_IMP_THM] >- (
        BasicProvers.EVERY_CASE_TAC >- (
          qmatch_assum_rename_tac`MEM (NONE,az,b) defs`[] >>
          first_x_assum(qspecl_then[`az`,`b`]mp_tac) >>
          simp[] >> strip_tac >> fs[] >>
          fsrw_tac[DNF_ss][MEM_MAP,MEM_FILTER] >>
          rw[] >> fsrw_tac[ARITH_ss][] >>
          qexists_tac`v - (az + LENGTH defs)` >>
          simp[] >>
          HINT_EXISTS_TAC >> simp[] >>
          simp[MEM_MAP,MEM_FILTER] >>
          qexists_tac`v` >> simp[] ) >>
        qmatch_assum_rename_tac`MEM (SOME p,q,r) defs`[] >>
        PairCases_on`p` >>
        fs[] ) >>
      HINT_EXISTS_TAC >>
      simp[] >>
      qmatch_assum_rename_tac`MEM d defs`[] >>
      PairCases_on`d` >> simp[] >>
      Cases_on`d0`>>simp[]>>fs[]>>
      fsrw_tac[DNF_ss][MEM_MAP,MEM_FILTER] >>
      qexists_tac`m` >> simp[] ) >>
    simp[] ) >>
  strip_tac >- (
    rw[free_vars_list_MAP] >>
    fsrw_tac[DNF_ss][Once EXTENSION] >>
    fsrw_tac[DNF_ss][MEM_MAP,MEM_FLAT,EQ_IMP_THM] >>
    metis_tac[] ) >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- rw[])
val _ = export_rewrites["free_vars_mkshift"]

val free_vars_shift = store_thm("free_vars_shift",
  ``set (free_vars (shift k n e)) = IMAGE (λv. if v < n then v else k + v) (set (free_vars e))``,
  simp[shift_def])
val _ = export_rewrites["free_vars_shift"]

val free_labs_mkshift = store_thm("free_labs_mkshift",
  ``∀f k e ez. free_labs ez (mkshift f k e) = free_labs ez e``,
  ho_match_mp_tac mkshift_ind >> rw[free_labs_list_MAP] >> rw[] >>
  TRY (
    AP_TERM_TAC >>
    simp[MAP_MAP_o,MAP_EQ_f] >>
    simp[FORALL_PROD] >>
    Cases >> simp[] >>
    rw[] >> res_tac >>
    fsrw_tac[ARITH_ss][] >>
    NO_TAC ) >>
  TRY (
    qunabbrev_tac`defs'` >>
    simp[free_labs_defs_MAP] >>
    AP_TERM_TAC >>
    simp[Once LIST_EQ_REWRITE] >>
    rpt strip_tac >>
    simp[EL_MAP] >>
    fsrw_tac[DNF_ss][MEM_EL] >>
    qabbrev_tac`p = EL x defs` >>
    PairCases_on`p`>>fs[]>>
    Cases_on`p0`>>fs[]>>
    first_x_assum(qspecl_then[`p1`,`p2`,`ez+ns+p1`,`x`]mp_tac)>>
    simp[] ) >>
  PairCases_on`cb` >> simp[] >>
  Cases_on`cb0`>>simp[] >> fsrw_tac[ARITH_ss][])
val _ = export_rewrites["free_labs_mkshift"]

val free_labs_shift = store_thm("free_labs_shift",
  ``(free_labs ez (shift k n e)) = (free_labs ez e)``,
  simp[shift_def])
val _ = export_rewrites["free_labs_shift"]

val no_labs_mkshift = store_thm("no_labs_mkshift",
  ``∀f k e. no_labs (mkshift f k e) = no_labs e``,
  ho_match_mp_tac mkshift_ind >>
  srw_tac[DNF_ss][EVERY_MEM,MEM_MAP,LET_THM] >- (
    rw[EQ_IMP_THM] >- (
      res_tac >> BasicProvers.EVERY_CASE_TAC >> fs[] >>
      res_tac >> rfs[] ) >>
    BasicProvers.EVERY_CASE_TAC >> fs[] >>
    res_tac >> fs[] ) >>
  BasicProvers.EVERY_CASE_TAC >> fs[])
val _ = export_rewrites["no_labs_mkshift"]

val no_labs_shift = store_thm("no_labs_shift",
  ``(no_labs (shift k n e)) = no_labs e``,
  simp[shift_def])
val _ = export_rewrites["no_labs_shift"]

val all_labs_mkshift = store_thm("all_labs_mkshift",
  ``∀f k e. all_labs (mkshift f k e) = all_labs e``,
  ho_match_mp_tac mkshift_ind >>
  srw_tac[DNF_ss][EVERY_MEM,MEM_MAP,LET_THM] >- (
    rw[EQ_IMP_THM] >- (
      res_tac >> BasicProvers.EVERY_CASE_TAC >> fs[] >>
      res_tac >> rfs[] ) >>
    BasicProvers.EVERY_CASE_TAC >> fs[] >>
    res_tac >> fs[] ) >>
  BasicProvers.EVERY_CASE_TAC >> fs[])
val _ = export_rewrites["all_labs_mkshift"]

val all_labs_shift = store_thm("all_labs_shift",
  ``(all_labs (shift k n e)) = all_labs e``,
  simp[shift_def])
val _ = export_rewrites["all_labs_shift"]

(* code environment stuff

val closed_code_env_def = Define`
  closed_code_env c = ∀x. x ∈ FRANGE c ⇒ free_labs x.body ⊆ FDOM c`

val closed_code_env_FEMPTY = store_thm("closed_code_env_FEMPTY",
  ``closed_code_env FEMPTY``,
  rw[closed_code_env_def])
val _ = export_rewrites["closed_code_env_FEMPTY"]

val syneq_cb_aux_mono_c = store_thm("syneq_cb_aux_mono_c",
  ``∀c c' n nz z d.
    (∀x. x ∈ free_labs_defs [d] ⇒ (FLOOKUP c' x = FLOOKUP c x)) ⇒
    (syneq_cb_aux c' n nz z d = syneq_cb_aux c n nz z d)``,
  rpt strip_tac >>
  Cases_on`d`>>TRY(PairCases_on`x`)>>fs[syneq_cb_aux_def,FLOOKUP_DEF]>>
  pop_assum mp_tac >> rw[LET_THM,UNCURRY] >>
  fs[NOT_FDOM_FAPPLY_FEMPTY])

val syneq_exp_c_SUBMAP = store_thm("syneq_exp_c_SUBMAP",
  ``(∀c z1 z2 V e1 e2. syneq_exp c z1 z2 V e1 e2 ⇒
      ∀c'. c ⊑ c' ∧ (free_labs e1 = {}) ∧ free_labs e2 ⊆ FDOM c ∧ closed_code_env c ⇒ syneq_exp c' z1 z2 V e1 e2) ∧
    (∀c z1 z2 V defs1 defs2 U. syneq_defs c z1 z2 V defs1 defs2 U ⇒
      ∀c'. c ⊑ c' ∧ (free_labs_defs defs1 = {}) ∧ free_labs_defs defs2 ⊆ FDOM c ∧ closed_code_env c ⇒ syneq_defs c' z1 z2 V defs1 defs2 U)``,
  ho_match_mp_tac syneq_exp_ind >>
  strip_tac >- rw[Once syneq_exp_cases] >>
  strip_tac >- rw[Once syneq_exp_cases] >>
  strip_tac >- ( rw[] >> rw[Once syneq_exp_cases] ) >>
  strip_tac >- rw[Once syneq_exp_cases] >>
  strip_tac >- rw[Once syneq_exp_cases] >>
  strip_tac >- (
    rw[] >>
    rw[Once syneq_exp_cases] >>
    fsrw_tac[DNF_ss][EVERY2_EVERY,EVERY_MEM,FORALL_PROD] >>
    qpat_assum`LENGTH es1 = X`assume_tac >>
    fsrw_tac[DNF_ss][MEM_ZIP,MEM_EL,SUBSET_DEF,IMAGE_EQ_SING] >>
    metis_tac[] ) >>
  strip_tac >- ( rw[] >> rw[Once syneq_exp_cases] ) >>
  strip_tac >- ( rw[] >> rw[Once syneq_exp_cases] ) >>
  strip_tac >- ( rw[] >> rw[Once syneq_exp_cases] ) >>
  strip_tac >- (
    rw[] >>
    fsrw_tac[DNF_ss][] >>
    simp[Once syneq_exp_cases] >- PROVE_TAC[] >>
    qexists_tac`U` >>
    conj_tac >>
    fsrw_tac[ARITH_ss][] >>
    first_x_assum match_mp_tac >>
    fsrw_tac[DNF_ss][SUBSET_DEF]) >>
  strip_tac >- (
    simp[] >>
    rpt gen_tac >>
    simp_tac(srw_ss()++DNF_ss)[] >>
    rpt gen_tac >> strip_tac >>
    strip_tac >>
    simp[Once syneq_exp_cases] >>
    qexists_tac`U` >> simp[] >>
    first_x_assum match_mp_tac >>
    Cases_on`cb1`>>TRY(PairCases_on`x`)>>
    fsrw_tac[DNF_ss][]) >>
  strip_tac >- (
    rw[] >>
    rw[Once syneq_exp_cases] >>
    fsrw_tac[DNF_ss][EVERY2_EVERY,EVERY_MEM,FORALL_PROD] >>
    qpat_assum`LENGTH es1 = X`assume_tac >>
    fsrw_tac[DNF_ss][MEM_ZIP,MEM_EL,SUBSET_DEF,IMAGE_EQ_SING] >>
    metis_tac[] ) >>
  strip_tac >- ( rw[] >> rw[Once syneq_exp_cases] ) >>
  strip_tac >- ( rw[] >> rw[Once syneq_exp_cases] ) >>
  strip_tac >- ( rw[] >> rw[Once syneq_exp_cases] ) >>
  strip_tac >- ( rw[] >> rw[Once syneq_exp_cases] ) >>
  strip_tac >- (
    rw[] >>
    simp[Once syneq_exp_cases] >- (
      fs[SUBMAP_DEF,EVERY_MEM] >> metis_tac[] ) >>
    fs[IMAGE_EQ_SING] >>
    qmatch_assum_abbrev_tac`P <=> Q` >>
    `P` by (
      unabbrev_all_tac >>
      fsrw_tac[][EVERY_MEM,MEM_FILTER,SUBMAP_DEF] >>
      first_x_assum(qspec_then`INR l`(mp_tac o GEN_ALL)) >> simp[] >> strip_tac >>
      metis_tac[MEM_EL] ) >>
    fs[Abbr`P`,Abbr`Q`] >>
    conj_tac >- (
      fsrw_tac[][EVERY_MEM,MEM_FILTER,SUBMAP_DEF] >> metis_tac[] ) >>
    rpt gen_tac >> strip_tac >>
    fsrw_tac[SATISFY_ss][] >>
    qpat_assum`∀n1 n2. U n1 n2 ⇒ P`(qspecl_then[`n1`,`n2`]mp_tac) >>
    simp[] >> strip_tac >>
    qspecl_then[`c`,`c'`,`n1`,`LENGTH defs1`,`z1`,`EL n1 defs1`]mp_tac syneq_cb_aux_mono_c >>
    discharge_hyps >- (
      fsrw_tac[DNF_ss,SATISFY_ss][FLOOKUP_DEF,SUBMAP_DEF,SUBSET_DEF,MEM_FILTER,MEM_EL] ) >>
    qspecl_then[`c`,`c'`,`n2`,`LENGTH defs2`,`z2`,`EL n2 defs2`]mp_tac syneq_cb_aux_mono_c >>
    discharge_hyps >- (
      fsrw_tac[DNF_ss][FLOOKUP_DEF,SUBMAP_DEF,SUBSET_DEF,MEM_FILTER,MEM_EL] >>
      metis_tac[] ) >>
    disch_then SUBST1_TAC >>
    disch_then SUBST1_TAC >>
    ntac 2 (qpat_assum`X = Y`(mp_tac o SYM)) >>
    simp[] >> ntac 3 strip_tac >> fs[] >>
    reverse conj_tac >- (
      gen_tac >> strip_tac >>
      fs[MEM_EL] >> res_tac >> fs[] >> rfs[] ) >>
    first_x_assum match_mp_tac >> simp[] >>
    conj_tac >- (
      Cases_on`EL n1 defs1`>>TRY(PairCases_on`x`)>>fs[syneq_cb_aux_def,MEM_EL] >- (
        first_x_assum(qspec_then`EL n1 defs1`mp_tac) >> simp[] >>
        disch_then match_mp_tac >> metis_tac[] ) >>
      first_x_assum(qspec_then`EL n1 defs1`mp_tac) >> simp[] >>
      metis_tac[] ) >>
    fsrw_tac[DNF_ss][FLOOKUP_DEF,SUBMAP_DEF,SUBSET_DEF,MEM_FILTER,MEM_EL] >>
    qx_gen_tac`z` >> strip_tac >>
    qpat_assum`∀x n. P ∧ n < LENGTH defs2 ⇒ Q`(qspecl_then[`z`,`n2`]mp_tac) >>
    Cases_on`EL n2 defs2`>>TRY(PairCases_on`x`)>>fs[syneq_cb_aux_def] >>
    Cases_on`y=z`>>rw[] >>
    fs[LET_THM,UNCURRY,closed_code_env_def,IN_FRANGE,SUBSET_DEF] >>
    metis_tac[] ))

val syneq_c_SUBMAP = store_thm("syneq_c_SUBMAP",
  ``∀c v1 v2. syneq c v1 v2 ⇒ ∀c'. closed_code_env c ∧ c ⊑ c' ∧ (vlabs v1 = {}) ∧ (vlabs v2 ⊆ FDOM c) ⇒ syneq c' v1 v2``,
  ho_match_mp_tac syneq_ind >> simp[] >>
  strip_tac >- (
    rw[] >>
    simp[Once syneq_cases] >>
    fs[EVERY2_EVERY,EVERY_MEM] >>
    rfs[MEM_ZIP,FORALL_PROD,IMAGE_EQ_SING] >>
    fs[GSYM LEFT_FORALL_IMP_THM,MEM_EL,SUBSET_DEF] >>
    metis_tac[]) >>
  rpt gen_tac >>
  Q.PAT_ABBREV_TAC`h1 = (P = []) ∨ Q` >>
  Q.PAT_ABBREV_TAC`h2 = (P = []) ∨ Q` >>
  rw[] >> rw[Once syneq_cases] >>
  map_every qexists_tac[`V`,`V'`] >>
  fs[IMAGE_EQ_SING,MEM_EL,GSYM LEFT_FORALL_IMP_THM] >>
  (conj_tac >- (
    rpt gen_tac >> strip_tac >>
    fsrw_tac[DNF_ss][] >>
    conj_tac >- PROVE_TAC[] >>
    conj_tac >- PROVE_TAC[] >>
    first_x_assum (match_mp_tac o MP_CANON) >>
    fsrw_tac[DNF_ss][SUBSET_DEF,MEM_EL] >>
    metis_tac[prim_recTheory.NOT_LESS_0,LENGTH_NIL])) >> simp[] >>
  match_mp_tac(MP_CANON (CONJUNCT2 syneq_exp_c_SUBMAP)) >>
  HINT_EXISTS_TAC >> simp[] >>
  simp[IMAGE_EQ_SING,MEM_EL,GSYM LEFT_FORALL_IMP_THM] >>
  PROVE_TAC[])

val syneq_exp_c_syneq = store_thm("syneq_exp_c_syneq",
  ``(∀c z1 z2 V e1 e2. syneq_exp c z1 z2 V e1 e2 ⇒
     ∀k cd. (free_labs e1 = {}) (* ∧ free_labs e2 ⊆ FDOM c ∧ closed_code_env c *) ∧ k ∈ FDOM c ∧
       (cd.az = (c ' k).az) ∧
       (cd.nz = (c ' k).nz) ∧
       (cd.ez = (c ' k).ez) ∧
       (cd.ix = (c ' k).ix) ∧
       (cd.ceenv = (c ' k).ceenv) ∧
       (let y = LENGTH (FST (c ' k).ceenv) + LENGTH (SND (c ' k).ceenv) + (c ' k).az + 1 in
        syneq_exp (c |+ (k,cd)) y y $= (c ' k).body cd.body) ⇒
          syneq_exp (c |+ (k,cd)) z1 z2 V e1 e2) ∧
    (∀c z1 z2 V defs1 defs2 U. syneq_defs c z1 z2 V defs1 defs2 U ⇒
      ∀k cd. (free_labs_defs defs1 = {}) (* ∧ free_labs_defs defs2 ⊆ FDOM c ∧ closed_code_env c *) ∧ k ∈ FDOM c ∧
       (cd.az = (c ' k).az) ∧
       (cd.nz = (c ' k).nz) ∧
       (cd.ez = (c ' k).ez) ∧
       (cd.ix = (c ' k).ix) ∧
       (cd.ceenv = (c ' k).ceenv) ∧
       (let y = LENGTH (FST (c ' k).ceenv) + LENGTH (SND (c ' k).ceenv) + (c ' k).az + 1 in
        syneq_exp (c |+ (k,cd)) y y $= (c ' k).body cd.body) ⇒
          syneq_defs (c |+ (k,cd)) z1 z2 V defs1 defs2 U)``,
  ho_match_mp_tac syneq_exp_ind >>
  strip_tac >- (rw[] >> rw[Once syneq_exp_cases]) >>
  strip_tac >- (rw[] >> rw[Once syneq_exp_cases]) >>
  strip_tac >- (rw[] >> rw[Once syneq_exp_cases] >> metis_tac[]) >>
  strip_tac >- (rw[] >> rw[Once syneq_exp_cases]) >>
  strip_tac >- (rw[] >> rw[Once syneq_exp_cases]) >>
  strip_tac >- (
    rw[] >>
    rw[Once syneq_exp_cases] >>
    fsrw_tac[DNF_ss][EVERY2_EVERY,EVERY_MEM,FORALL_PROD,IMAGE_EQ_SING] >>
    rfs[MEM_ZIP,MEM_EL] >>
    fsrw_tac[DNF_ss][SUBSET_DEF,MEM_EL] >>
    metis_tac[]) >>
  strip_tac >- (rw[] >> rw[Once syneq_exp_cases] >> metis_tac[]) >>
  strip_tac >- (rw[] >> rw[Once syneq_exp_cases] >> metis_tac[]) >>
  strip_tac >- (rw[] >> rw[Once syneq_exp_cases] >> metis_tac[]) >>
  strip_tac >- (
    rw[] >>
    rw[Once syneq_exp_cases] >>
    qexists_tac`U`>>simp[] >>fs[] >>
    metis_tac[]) >>
  strip_tac >- (
    rw[] >>
    rw[Once syneq_exp_cases] >>
    qexists_tac`U`>>simp[]>>
    metis_tac[]) >>
  strip_tac >- (
    rw[] >>
    rw[Once syneq_exp_cases] >>
    fsrw_tac[DNF_ss][EVERY2_EVERY,EVERY_MEM,FORALL_PROD,IMAGE_EQ_SING] >>
    rfs[MEM_ZIP,MEM_EL] >>
    fsrw_tac[DNF_ss][SUBSET_DEF,MEM_EL] >>
    metis_tac[]) >>
  strip_tac >- (rw[] >> rw[Once syneq_exp_cases] >> metis_tac[]) >>
  strip_tac >- (rw[] >> rw[Once syneq_exp_cases] >> metis_tac[]) >>
  strip_tac >- (rw[] >> rw[Once syneq_exp_cases] >> metis_tac[]) >>
  strip_tac >- (rw[] >> rw[Once syneq_exp_cases] >> metis_tac[]) >>
  rw[] >>
  simp[Once syneq_exp_cases] >- (
    fs[FAPPLY_FUPDATE_THM,EVERY_MEM] >>
    metis_tac[] ) >>
  fs[IMAGE_EQ_SING] >>
  qmatch_assum_abbrev_tac`P <=> Q` >>
  `P` by (
    unabbrev_all_tac >>
    rpt gen_tac >> strip_tac >>
    first_x_assum(qspec_then`EL i defs1`mp_tac) >>
    simp[MEM_EL] >>
    metis_tac[]) >>
  fs[Abbr`Q`] >>
  conj_tac >- (
    fsrw_tac[][EVERY_MEM,IMAGE_EQ_SING] >>
    metis_tac[FAPPLY_FUPDATE_THM] ) >>
  ntac 2 gen_tac >> strip_tac >>
  first_x_assum(qspecl_then[`n1`,`n2`]mp_tac) >>
  simp[] >> strip_tac >>
  ntac 2 (qpat_assum `X = Y`(mp_tac o SYM)) >>
  rw[] >>
  first_assum(qspec_then`INR l`(mp_tac o GEN_ALL)) >> simp_tac(srw_ss())[MEM_EL] >> strip_tac >>
  reverse(Cases_on`EL n1 defs1`)>>TRY(PairCases_on`x`)>>fs[syneq_cb_aux_def,LET_THM] >- (
    metis_tac[] ) >>
  Cases_on`EL n2 defs2`>>TRY(PairCases_on`x`)>>fs[syneq_cb_aux_def,LET_THM] >- (
    rfs[] >>
    first_x_assum match_mp_tac >>
    simp[] >> fsrw_tac[ARITH_ss][] >>
    fs[MEM_EL] >> res_tac >> rfs[] ) >>
  fs[UNCURRY] >>
  rpt (BasicProvers.VAR_EQ_TAC) >>
  conj_tac >- metis_tac[] >>
  conj_tac >- (
    simp[FAPPLY_FUPDATE_THM] >>
    metis_tac[] ) >>
  conj_tac >- (
    simp[FAPPLY_FUPDATE_THM] >>
    metis_tac[] ) >>
  conj_tac >- (
    fs[EVERY_MEM] >>
    Cases_on`y=k`>>fs[FAPPLY_FUPDATE_THM] ) >>
  conj_tac >- (
    fs[EVERY_MEM] >>
    Cases_on`y=k`>>fs[FAPPLY_FUPDATE_THM] ) >>
  Q.PAT_ABBREV_TAC`sc = syneq_cb_V X Y Z A` >>
  conj_tac >- ( Cases_on`y=k`>>fs[FAPPLY_FUPDATE_THM] ) >>
  fs[] >> rfs[] >>
  first_x_assum(qspecl_then[`k`,`cd`]mp_tac) >>
  simp[] >>
  `free_labs e1 = {}` by (
    first_x_assum(qspec_then`EL n1 defs1`mp_tac) >>
    simp[MEM_EL] >> metis_tac[] ) >>
  discharge_hyps >- fsrw_tac[ARITH_ss][] >>
  strip_tac >>
  reverse(Cases_on`y=k`)>>fs[FAPPLY_FUPDATE_THM]>-(
    simp[Abbr`sc`] ) >>
  qmatch_assum_abbrev_tac `syneq_exp c2k z1k z2k sck e1 bk` >>
  qmatch_assum_abbrev_tac `syneq_exp c2k zj zj $= bk cd.body` >>
  qspecl_then[`c2k`,`z1k`,`z2k`,`sck`,`e1`,`bk`]mp_tac(CONJUNCT1 syneq_exp_trans) >>
  simp[] >>
  disch_then(qspecl_then[`z2k`,`$=`,`cd.body`]mp_tac) >>
  `sck = sc U` by (
    simp[Abbr`sck`,Abbr`sc`,FUN_EQ_THM] ) >>
  `z2k = zj` by (
    simp[Abbr`z2k`,Abbr`zj`] ) >>
  simp[])

*)

(* Cevaluate deterministic *)

val Cevaluate_determ = store_thm("Cevaluate_determ",
  ``(∀s env exp res. Cevaluate s env exp res ⇒ ∀res'. Cevaluate s env exp res' ⇒ (res' = res)) ∧
    (∀s env exps ress. Cevaluate_list s env exps ress ⇒ ∀ress'. Cevaluate_list s env exps ress' ⇒ (ress' = ress))``,
  ho_match_mp_tac Cevaluate_ind >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    rw[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][FORALL_PROD] >>
    res_tac >> fs[] ) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    rw[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][FORALL_PROD] >>
    res_tac >> fs[] ) >>
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
    rpt gen_tac >> strip_tac >>
    simp[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][] >>
    PairCases_on`def`>>fs[]>>
    Cases_on`def0`>>fs[]>|[ALL_TAC,PairCases_on`x`]>>fs[UNCURRY]>>
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
