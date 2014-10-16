open HolKernel bossLib boolLib miscLib boolSimps pairTheory listTheory rich_listTheory pred_setTheory finite_mapTheory relationTheory SatisfySimps arithmeticTheory quantHeuristicsLib lcsymtacs
open miscTheory libTheory evalPropsTheory intLangTheory toIntLangTheory compilerTerminationTheory
open exhLangProofTheory patLangProofTheory

val _ = new_theory "intLangExtra"

(* free/all/no_labs *)

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
  (vlabs (CVectorv vs) = vlabs_list vs) ∧
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
  (no_vlabs (CVectorv vs) = no_vlabs_list vs) ∧
  (no_vlabs (CRecClos env defs _) ⇔ no_vlabs_list env ∧ no_labs_defs defs) ∧
  (no_vlabs (CLoc _) = T) ∧
  (no_vlabs_list [] = T) ∧
  (no_vlabs_list (v::vs) ⇔ no_vlabs v ∧ no_vlabs_list vs)`
val _ = export_rewrites["no_vlabs_def"]

val all_vlabs_def = Define`
  (all_vlabs (CLitv _) = T) ∧
  (all_vlabs (CConv _ vs) = all_vlabs_list vs) ∧
  (all_vlabs (CVectorv vs) = all_vlabs_list vs) ∧
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

val vlabs_csg_def = Define
  `vlabs_csg csg = vlabs_list (store_vs (SND(FST csg))) ∪ vlabs_list (MAP THE (FILTER IS_SOME (SND csg)))`

val CvFromList_vlabs = store_thm("CvFromList_vlabs",
  ``∀v x. CvFromList v = SOME x ⇒ vlabs_list x = vlabs v``,
  ho_match_mp_tac CvFromList_ind >> rw[CvFromList_def] >> rw[vlabs_def] >>
  BasicProvers.EVERY_CASE_TAC >> fs[] >> rw[])

val Cexplode_vlabs = store_thm("Cexplode_vlabs[simp]",
  ``∀ls. vlabs (Cexplode ls) = {}``,
  Induct >> simp[Cexplode_def])

val tac =
  TRY (
    qmatch_assum_rename_tac`x ∈ vlabs (EL n ls)`[] >>
    first_x_assum(qspecl_then[`x`,`EL n ls`]mp_tac) >>
    discharge_hyps >- (
      simp[MEM_EL] >> metis_tac[] ) >>
    metis_tac[] ) >>
  TRY (
    qmatch_assum_rename_tac`x ∈ vlabs v`[] >>
    qmatch_assum_rename_tac`EL n ls = Refv v`[] >>
    first_x_assum(qspecl_then[`x`,`v`,`Refv v`]mp_tac) >>
    simp[] >>
    discharge_hyps >- (
      simp[MEM_EL] >> metis_tac[] ) >>
    metis_tac[] ) >>
  TRY (
    qmatch_assum_rename_tac`x ∈ vlabs v`[] >>
    qmatch_assum_rename_tac`MEM v (store_v_vs ls)`[] >>
    qmatch_assum_rename_tac`MEM ls l2`[] >>
    first_x_assum(qspecl_then[`x`,`v`,`ls`]mp_tac) >>
    simp[] >> NO_TAC ) >>
  TRY (
    qmatch_assum_rename_tac`x ∈ vlabs (THE v)`[] >>
    qmatch_assum_rename_tac`MEM v ls`[] >>
    first_x_assum(qspecl_then[`x`,`v`]mp_tac) >>
    simp[] >> NO_TAC ) >>
  TRY (
    imp_res_tac MEM_LUPDATE_E >> fs[] >>
    qmatch_assum_rename_tac`x ∈ vlabs v`[] >>
    qmatch_assum_rename_tac`MEM v l`[] >>
    qmatch_assum_rename_tac`EL n ls = Varray l`[] >>
    first_x_assum(qspecl_then[`x`,`v`,`EL n ls`]mp_tac) >>
    simp[] >>
    (discharge_hyps >- (
       simp[MEM_EL] >> metis_tac[] )) >>
    simp[] >>
    metis_tac[] )

val Cevaluate_vlabs = store_thm("Cevaluate_vlabs",
  ``(∀s env exp res. Cevaluate s env exp res ⇒
        (vlabs_csg (FST res) ⊆ vlabs_csg s ∪ vlabs_list env ∪ set (free_labs (LENGTH env) exp)) ∧
        (∀v. (SND res = Rval v) ⇒ vlabs v ⊆ vlabs_csg s ∪ vlabs_list env ∪ set (free_labs (LENGTH env) exp)) ∧
        (∀v. (SND res = Rerr (Rraise v)) ⇒ vlabs v ⊆ vlabs_csg s ∪ vlabs_list env ∪ set (free_labs (LENGTH env) exp))) ∧
    (∀s env es res. Cevaluate_list s env es res ⇒
        (vlabs_csg (FST res) ⊆ vlabs_csg s ∪ vlabs_list env ∪ set (free_labs_list (LENGTH env) es)) ∧
        (∀vs. (SND res = Rval vs) ⇒ vlabs_list vs ⊆ vlabs_csg s ∪ vlabs_list env ∪ set (free_labs_list (LENGTH env) es)) ∧
        (∀v. (SND res = Rerr (Rraise v)) ⇒ vlabs v ⊆ vlabs_csg s ∪ vlabs_list env ∪ set (free_labs_list (LENGTH env) es)))``,
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
    srw_tac[DNF_ss][vlabs_csg_def,SUBSET_DEF,vlabs_list_MAP,MEM_MAP,MEM_FILTER,PULL_EXISTS] >>
    PROVE_TAC[optionTheory.IS_SOME_DEF,optionTheory.THE_DEF,MEM_EL]) >>
  strip_tac >- ( srw_tac[DNF_ss][SUBSET_DEF] >> metis_tac[] ) >>
  strip_tac >- ( srw_tac[DNF_ss][SUBSET_DEF] >> metis_tac[] ) >>
  strip_tac >- ( srw_tac[DNF_ss][SUBSET_DEF] >> metis_tac[] ) >>
  strip_tac >- (
    srw_tac[DNF_ss][SUBSET_DEF,ADD1] >> metis_tac[] ) >>
  strip_tac >- ( srw_tac[DNF_ss][SUBSET_DEF] >> metis_tac[] ) >>
  strip_tac >- (
    srw_tac[DNF_ss][SUBSET_DEF,MEM_FLAT,MEM_MAP,MEM_GENLIST,vlabs_list_MAP] >>
    metis_tac[ADD_SYM] ) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    qpat_assum`(T,LENGTH vs,env',exp') = X`mp_tac >>
    PairCases_on`def` >> simp[] >>
    BasicProvers.CASE_TAC >> TRY (PairCases_on`x`) >> simp[] >>
    strip_tac >> fs[] >>
    qmatch_abbrev_tac`a ⊆ b ∧ c` >>
    qmatch_assum_abbrev_tac`a ⊆ b'` >>
    (qsuff_tac`b' ⊆ b`>-metis_tac[SUBSET_TRANS]) >>
    unabbrev_all_tac >>
    qmatch_abbrev_tac`m ∪ a ∪ b ⊆ d` >>
    qmatch_assum_abbrev_tac`vlabs_csg (X,g) ⊆ e ∪ f ∪ h` >>
    `m = vlabs_csg (X,g)` by ( simp[Abbr`m`,vlabs_csg_def,Abbr`X`] ) >>
    qmatch_assum_abbrev_tac`e ⊆ c ∪ f ∪ i` >>
    `e ⊆ d` by metis_tac[SUBSET_DEF,IN_UNION] >>
    `f ⊆ d` by metis_tac[SUBSET_DEF,IN_UNION] >>
    `i ⊆ d` by metis_tac[SUBSET_DEF,IN_UNION] >>
    `h ⊆ d` by metis_tac[SUBSET_DEF,IN_UNION] >>
    `c ⊆ d` by metis_tac[SUBSET_DEF,IN_UNION] >|[
      `a ⊆ d` by (
        simp[Abbr`a`,vlabs_list_APPEND,vlabs_list_REVERSE] >>
        reverse conj_tac >- metis_tac[SUBSET_DEF,IN_UNION] >>
        conj_tac >- metis_tac[SUBSET_DEF,IN_UNION] >>
        qpat_assum`vlabs_list cenv ⊆ Z`mp_tac >>
        simp[vlabs_list_MAP,SUBSET_DEF,PULL_EXISTS,MEM_GENLIST] >>
        metis_tac[SUBSET_DEF,IN_UNION] ) >>
      `b ⊆ d` by (
        qmatch_assum_abbrev_tac`set Y ⊆ c ∪ f ∪ i` >>
        qsuff_tac`b ⊆ set Y` >- metis_tac[SUBSET_DEF,IN_UNION] >>
        simp[Abbr`b`,Abbr`Y`,free_labs_defs_MAP,SUBSET_DEF,MEM_FLAT,MEM_GENLIST,PULL_EXISTS] >>
        rw[] >> qexists_tac`n` >> simp[] >>
        fsrw_tac[ARITH_ss][] )
      ,
      `a ⊆ d` by (
        simp[Abbr`a`,vlabs_list_APPEND,vlabs_list_REVERSE] >>
        simp[GSYM CONJ_ASSOC] >>
        conj_tac >- metis_tac[SUBSET_DEF,IN_UNION] >>
        conj_tac >- metis_tac[SUBSET_DEF,IN_UNION] >>
        `vlabs_list cenv ⊆ d` by metis_tac[SUBSET_DEF,IN_UNION] >>
        conj_tac >- (
          qmatch_assum_abbrev_tac`set Y ⊆ c ∪ f ∪ i` >>
          metis_tac[SUBSET_DEF,IN_UNION] ) >>
        conj_tac >- (
          qpat_assum`vlabs_list cenv ⊆ Z`mp_tac >>
          simp[vlabs_list_MAP,SUBSET_DEF,PULL_EXISTS,MEM_GENLIST,MEM_MAP] >>
          qmatch_assum_abbrev_tac`set Y ⊆ c ∪ f ∪ i` >>
          metis_tac[SUBSET_DEF,IN_UNION] ) >>
        match_mp_tac SUBSET_TRANS >>
        qexists_tac`vlabs_list cenv` >> simp[] >>
        simp[vlabs_list_MAP,SUBSET_DEF,PULL_EXISTS,MEM_MAP,MEM_EL] >>
        fs[EVERY_MEM,MEM_EL,PULL_EXISTS] >>
        metis_tac[] ) >>
      `b ⊆ d` by (
        qmatch_assum_abbrev_tac`set Y ⊆ c ∪ f ∪ i` >>
        qsuff_tac`b ⊆ set Y` >- metis_tac[SUBSET_DEF,IN_UNION] >>
        simp[Abbr`b`,Abbr`Y`,free_labs_defs_MAP,SUBSET_DEF,MEM_FLAT,MEM_GENLIST,PULL_EXISTS] >>
        rw[] >> qexists_tac`n` >> simp[] )
      ] >>
    fsrw_tac[DNF_ss][SUBSET_DEF] >>
    metis_tac[]) >>
  strip_tac >- ( srw_tac[DNF_ss][SUBSET_DEF] >> metis_tac[] ) >>
  strip_tac >- ( srw_tac[DNF_ss][SUBSET_DEF] >> metis_tac[] ) >>
  strip_tac >- ( srw_tac[DNF_ss][SUBSET_DEF] >> metis_tac[] ) >>
  strip_tac >- (
    ntac 2 gen_tac >>
    reverse Cases
    >- ( rw[] >> BasicProvers.EVERY_CASE_TAC >> fs[] >> rw[] )
    >- ( rw[] >> Cases_on`v` >> fs[] >> Cases_on`l` >> fs[] >> rw[] )
    >- (
      rw[] >> BasicProvers.EVERY_CASE_TAC >> fs[] >> rw[] >>
      imp_res_tac CvFromList_vlabs >> rw[] )
    >- (
      rw[] >>
      fsrw_tac[DNF_ss][SUBSET_DEF,vlabs_list_MAP,vlabs_csg_def] >>
      rw[] >- metis_tac[] >>
      fs[MEM_MAP,MEM_FILTER,MEM_LUPDATE] >>
      fs[PULL_EXISTS] >>
      metis_tac[MEM_EL]) >>
    ntac 4 gen_tac >>
    Cases >> rw[] >>
    fs[el_check_def,EVERY_MEM] >>
    BasicProvers.EVERY_CASE_TAC >>
    fsrw_tac[DNF_ss][SUBSET_DEF,vlabs_list_MAP,vlabs_csg_def,store_vs_def] >> rw[] >>
    fs[MEM_FLAT,MEM_MAP,PULL_EXISTS,MEM_FILTER] >> rw[] >>
    fs[vlabs_list_MAP] >> rw[] >> tac >>
    metis_tac[])>>
  strip_tac >- rw[] >>
  strip_tac >- (
    rw [] >> PairCases_on`s'` >> Cases_on `p2` >> fs [] >> rw[] >> fs[LET_THM,UNCURRY] >>
    TRY (
      qmatch_assum_rename_tac`SND(CevalPrim2s s0 op v1 v2) = res`["res"] >>
      Cases_on`op`>>Cases_on`v1`>>Cases_on`v2`>>fs[CevalPrim2s_def] >>
      TRY(Cases_on`l:lit`)>>TRY(Cases_on`l':lit`)>>fs[CevalPrim2s_def] >>
      pop_assum mp_tac >> rw[] >>
      fs[vlabs_csg_def,store_vs_def,FILTER_APPEND] >>
      BasicProvers.EVERY_CASE_TAC >> fs[] >> rw[] >>
      fs[vlabs_list_MAP,SUBSET_DEF,PULL_EXISTS,MEM_FLAT,MEM_MAP,MEM_FILTER,REPLICATE_GENLIST,MEM_GENLIST] >>
      fs[libTheory.el_check_def] >>
      qmatch_assum_rename_tac`EL n s0 = Varray l`[] >> rw[] >>
      fs[GSYM AND_IMP_INTRO] >>
      last_x_assum(fn th => first_x_assum(mp_tac o MATCH_MP th)) >>
      disch_then(qspec_then`EL n s0`mp_tac) >>
      discharge_hyps >- metis_tac[MEM_EL] >>
      simp[] >>
      discharge_hyps >- (
        rfs[MEM_EL,integerTheory.INT_ABS] >>
        qexists_tac`Num i` >> simp[] ) >>
      simp[] ) >>
    TRY (
      (qmatch_assum_rename_tac`CevalPrim2s s0 op v1 v2 = (s',res)`[] ORELSE
       qmatch_assum_rename_tac`SND(CevalPrim2s s0 op v1 v2) = res`["res"]) >>
      Cases_on`op`>>Cases_on`v1`>>Cases_on`v2`>>fs[CevalPrim2s_def] >>
      TRY(Cases_on`l:lit`)>>TRY(Cases_on`l':lit`)>>fs[CevalPrim2s_def] >>
      pop_assum mp_tac >> rw[] >>
      fs[vlabs_csg_def,store_vs_def,FILTER_APPEND] >>
      BasicProvers.EVERY_CASE_TAC >> fs[] >> rw[] >>
      fs[vlabs_list_MAP,SUBSET_DEF,PULL_EXISTS,MEM_FLAT,MEM_MAP,MEM_FILTER,REPLICATE_GENLIST,MEM_GENLIST] >>
      metis_tac[]) >>
    qmatch_assum_rename_tac`CevalPrim2p op v1 v2 = res`["res"] >>
    Cases_on`op`>>fs[CevalPrim2p_def]>>
    TRY (Cases_on `v1` >> Cases_on `v2` >> fs [] >> TRY(Cases_on `l:lit`) >> TRY (Cases_on `l':lit`) >>
         fs [] >> rw [] >>
         pop_assum mp_tac >> rw[] >> fs[] >>
         fs[vlabs_list_MAP,SUBSET_DEF,PULL_EXISTS,MEM_EL,NOT_LESS_EQUAL] >>
         metis_tac[]) >>
    Cases_on `do_Ceq v1 v2` >> fs [] >> rw []) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rw[] >>
    Cases_on`b`>>Cases_on`v2`>>fs[]>>
    TRY(Cases_on`l:lit`)>>fs[]>>
    Cases_on`v1`>>fs[]>>
    pop_assum mp_tac >> rw[] >>
    TRY(
      Cases_on`v3`>>fs[]>>
      Cases_on`l`>>fs[]>>
      BasicProvers.EVERY_CASE_TAC>>fs[]>>rw[]>>
      fsrw_tac[DNF_ss][vlabs_csg_def,store_vs_def,SUBSET_DEF,vlabs_list_MAP,MEM_MAP,PULL_EXISTS,MEM_FILTER] >>
      metis_tac[MEM_LUPDATE_E,is_Refv_def,dest_Refv_def] ) >>
    BasicProvers.EVERY_CASE_TAC >>
    fsrw_tac[DNF_ss][SUBSET_DEF,vlabs_list_MAP,vlabs_csg_def,store_vs_def,MEM_MAP,PULL_EXISTS,MEM_FILTER,MEM_FLAT] >> rw[] >>
    fs[el_check_def] >>
    imp_res_tac MEM_LUPDATE_E >> rw[] >> fs[] >>
    tac >>
    Cases_on`v3`>>fs[]>>(TRY(Cases_on`l:lit`>>fs[]))>>rw[]>>tac>>
    BasicProvers.EVERY_CASE_TAC >>
    fsrw_tac[DNF_ss][SUBSET_DEF,vlabs_list_MAP,vlabs_csg_def,store_vs_def,MEM_MAP,PULL_EXISTS,MEM_FILTER,MEM_FLAT] >> rw[] >>
    fs[el_check_def] >>
    imp_res_tac MEM_LUPDATE_E >> rw[] >> fs[] >>
    tac ) >>
  strip_tac >- rw[] >>
  strip_tac >- ( srw_tac[DNF_ss][SUBSET_DEF] >> metis_tac[] ) >>
  strip_tac >- ( srw_tac[DNF_ss][SUBSET_DEF] >> metis_tac[] ) >>
  strip_tac >- (
    srw_tac[DNF_ss][SUBSET_DEF,vlabs_csg_def,store_vs_def,FILTER_APPEND,vlabs_list_APPEND] >>
    fs[vlabs_list_MAP,MEM_MAP,MEM_FILTER,MEM_GENLIST] >> fs[]) >>
  strip_tac >- ( srw_tac[DNF_ss][SUBSET_DEF] >> metis_tac[] ) >>
  strip_tac >- ( srw_tac[DNF_ss][SUBSET_DEF] >> metis_tac[] ) >>
  strip_tac >- ( srw_tac[DNF_ss][SUBSET_DEF] >> metis_tac[] ) >>
  strip_tac >- ( srw_tac[DNF_ss][SUBSET_DEF] >> metis_tac[] ));

val no_vlabs_csg_def = Define`no_vlabs_csg csg ⇔
  no_vlabs_list (store_vs (SND (FST csg))) ∧
  no_vlabs_list (MAP THE (FILTER IS_SOME (SND csg)))`
val all_vlabs_csg_def = Define`all_vlabs_csg csg ⇔
  all_vlabs_list (store_vs (SND (FST csg))) ∧
  all_vlabs_list (MAP THE (FILTER IS_SOME (SND csg)))`

val CvFromList_no_vlabs = prove(
  ``∀v x. CvFromList v = SOME x ⇒ (EVERY no_vlabs x ⇔ no_vlabs v)``,
  ho_match_mp_tac CvFromList_ind >> rw[CvFromList_def] >> rw[no_vlabs_def] >>
  BasicProvers.EVERY_CASE_TAC >> fs[] >> rw[])

val CvFromList_all_vlabs = prove(
  ``∀v x. CvFromList v = SOME x ⇒ (EVERY all_vlabs x ⇔ all_vlabs v)``,
  ho_match_mp_tac CvFromList_ind >> rw[CvFromList_def] >> rw[all_vlabs_def] >>
  BasicProvers.EVERY_CASE_TAC >> fs[] >> rw[])

val Cexplode_no_vlabs = prove(
  ``∀ls. no_vlabs (Cexplode ls)``,
  Induct >> simp[Cexplode_def])

val Cexplode_all_vlabs = prove(
  ``∀ls. all_vlabs (Cexplode ls)``,
  Induct >> simp[Cexplode_def])

val tac1 =
  ho_match_mp_tac Cevaluate_ind >>
  strip_tac >- fsrw_tac[DNF_ss][EVERY_MEM,MEM_EL] >>
  strip_tac >- fsrw_tac[DNF_ss][EVERY_MEM,MEM_EL] >>
  strip_tac >- fsrw_tac[DNF_ss][EVERY_MEM,MEM_EL] >>
  strip_tac >- simp[] >>
  strip_tac >- simp[] >>
  strip_tac >- fsrw_tac[DNF_ss][EVERY_MEM,MEM_EL] >>
  strip_tac >- (
    fsrw_tac[DNF_ss][EVERY_MEM,no_vlabs_csg_def,all_vlabs_csg_def,store_vs_def,MEM_MAP,MEM_FILTER] >>
    rw[MEM_EL,PULL_EXISTS] >>
    rpt (first_x_assum(qspec_then`n`mp_tac)) >>
    simp[] ) >>
  strip_tac >- fsrw_tac[DNF_ss][EVERY_MEM,MEM_EL] >>
  strip_tac >- fsrw_tac[DNF_ss][EVERY_MEM,MEM_EL] >>
  strip_tac >- fsrw_tac[DNF_ss][EVERY_MEM,MEM_EL] >>
  strip_tac >- (
    rpt gen_tac >> ntac 2 strip_tac >> fs[] >> rfs[] >>
    BasicProvers.EVERY_CASE_TAC >> rfs[EVERY_REVERSE] >> fs[EVERY_REVERSE] ) >>
  strip_tac >- simp[] >>
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
    fs[no_vlabs_csg_def,all_vlabs_csg_def,store_vs_def] >>
    metis_tac[no_labs_def,all_labs_def] ) >>
  strip_tac >- fsrw_tac[DNF_ss][EVERY_MEM,MEM_EL] >>
  strip_tac >- fsrw_tac[DNF_ss][EVERY_MEM,MEM_EL] >>
  strip_tac >- fsrw_tac[DNF_ss][EVERY_MEM,MEM_EL] >>
  strip_tac >- (
    ntac 2 gen_tac >>
    reverse Cases
    >- (
      simp[] >> rw[] >>
      BasicProvers.EVERY_CASE_TAC >> fs[] >> rw[] )
    >- (
      simp[] >> rw[] >>
      Cases_on`v`>>fs[]>>Cases_on`l`>>fs[]>>rw[Cexplode_no_vlabs,Cexplode_all_vlabs])
    >- (
      simp[] >> rw[] >>
      BasicProvers.EVERY_CASE_TAC >> fs[] >> rw[] >>
      imp_res_tac CvFromList_no_vlabs >>
      imp_res_tac CvFromList_all_vlabs)
    >- (
      simp[] >> rw[] >>
      fs[no_vlabs_csg_def,all_vlabs_csg_def,store_vs_def,EVERY_MAP,EVERY_MEM,MEM_FILTER,MEM_LUPDATE,PULL_EXISTS] >>
      Cases >> simp[] >> rw[] >> rw[] >>
      metis_tac[MEM_EL,optionTheory.IS_SOME_DEF,optionTheory.THE_DEF] ) >>
    ntac 4 gen_tac >>
    Cases >> rw[] >>
    fs[el_check_def,EVERY_MEM] >>
    TRY (
      pop_assum mp_tac >> BasicProvers.CASE_TAC>>fs[]>>
      BasicProvers.CASE_TAC>>rw[]>>
      fs[no_vlabs_csg_def,all_vlabs_csg_def,store_vs_def] >>
      fs[EVERY_MAP,EVERY_MEM,MEM_FILTER,MEM_FLAT,PULL_EXISTS,MEM_MAP] >>
      metis_tac[MEM_EL,store_v_vs_def,MEM] ) >>
    TRY (
      fsrw_tac[DNF_ss][no_vlabs_csg_def,all_vlabs_csg_def,store_vs_def] >>
      fs[EVERY_MAP,EVERY_MEM,MEM_FILTER] >>
      NO_TAC ) >>
    BasicProvers.EVERY_CASE_TAC >>
    fsrw_tac[DNF_ss][EVERY_MEM,MEM_EL] >>
    fsrw_tac[DNF_ss][no_vlabs_csg_def,all_vlabs_csg_def,store_vs_def] >>
    fsrw_tac[DNF_ss][EVERY_MAP,EVERY_FILTER] >>
    fs[EVERY_MEM] >>
    TRY(
      gen_tac >> strip_tac >>
      qmatch_assum_rename_tac`nn < LENGTH ll + 1`[] >>
      Cases_on`nn < LENGTH ll`>>simp[EL_APPEND1,EL_APPEND2]>>
      `nn = LENGTH ll`by simp[] >> simp[] >>
      simp[EVERY_MEM] ) >>
    rw[] >>
    metis_tac[MEM_EL]) >>
  strip_tac >- fsrw_tac[DNF_ss][EVERY_MEM,MEM_EL] >>
  strip_tac >- (
    rw [] >> PairCases_on`s'` >> Cases_on `p2` >> fs [] >> rw[] >> fs[LET_THM,UNCURRY] >>
    TRY (
      (qmatch_assum_rename_tac`CevalPrim2s s0 op v1 v2 = (s',res)`[] ORELSE
       qmatch_assum_rename_tac`SND(CevalPrim2s s0 op v1 v2) = res`["res"]) >>
      Cases_on`op`>>Cases_on`v1`>>Cases_on`v2`>>fs[CevalPrim2s_def] >>
      TRY(Cases_on`l:lit`)>>TRY(Cases_on`l':lit`)>>fs[CevalPrim2s_def] >>
      pop_assum mp_tac >> rw[] >>
      fs[no_vlabs_csg_def,all_vlabs_csg_def,store_vs_def,FILTER_APPEND] >>
      BasicProvers.EVERY_CASE_TAC >> fs[] >> rw[] >>
      simp[EVERY_REPLICATE] >>
      fs[EVERY_MEM,MEM_FLAT,MEM_MAP,PULL_EXISTS,el_check_def] >>
      qmatch_assum_rename_tac`EL n s0 = Varray l`[] >>
      rfs[integerTheory.INT_ABS] >>
      last_x_assum(qspecl_then[`EL (Num i) l`,`EL n s0`]match_mp_tac) >>
      simp[MEM_EL] >> fs[arithmeticTheory.NOT_LESS_EQUAL] >> metis_tac[]) >>
    qmatch_assum_rename_tac`CevalPrim2p op v1 v2 = res`["res"] >>
    Cases_on`op`>>fs[CevalPrim2p_def]>>
    TRY (Cases_on `v1` >> Cases_on `v2` >> fs [] >> TRY(Cases_on `l:lit`) >> TRY (Cases_on `l':lit`) >>
         fs [] >> rw [] >>
         pop_assum mp_tac >> rw[] >> fs[] >>
         fs[EVERY_MEM,PULL_EXISTS,MEM_EL,NOT_LESS_EQUAL] >>
         NO_TAC) >>
    Cases_on `do_Ceq v1 v2` >> fs [] >> rw []) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rw[] >>
    Cases_on`b`>>Cases_on`v2`>>fs[]>>
    TRY(Cases_on`l:lit`)>>fs[]>>
    Cases_on`v1`>>fs[]>>
    pop_assum mp_tac >> rw[] >>
    TRY(
      Cases_on`v3`>>fs[]>>
      Cases_on`l`>>fs[]>>
      BasicProvers.EVERY_CASE_TAC>>fs[]>>rw[]>>
      fsrw_tac[DNF_ss][no_vlabs_csg_def,all_vlabs_csg_def,store_vs_def,SUBSET_DEF,no_vlabs_list_MAP,all_vlabs_list_MAP,MEM_MAP,PULL_EXISTS,MEM_FILTER,EVERY_MAP,EVERY_MEM] >>
      metis_tac[MEM_LUPDATE_E,is_Refv_def,dest_Refv_def] ) >>
    BasicProvers.EVERY_CASE_TAC >>
    fsrw_tac[DNF_ss][SUBSET_DEF,no_vlabs_list_MAP,all_vlabs_list_MAP,no_vlabs_csg_def,all_vlabs_csg_def,store_vs_def,MEM_MAP,PULL_EXISTS,MEM_FILTER,EVERY_MAP,EVERY_FILTER,EVERY_MEM,MEM_FLAT] >> rw[] >>
    imp_res_tac MEM_LUPDATE_E >> fs[] >> rw[] >>
    TRY(metis_tac[]) >>
    TRY (
      Cases_on`v3`>>fs[]>>(TRY(Cases_on`l:lit`>>fs[]))>>rw[]>>
      BasicProvers.EVERY_CASE_TAC >> fs[]>>rw[]>>
      TRY(metis_tac[])>>
      imp_res_tac MEM_LUPDATE_E >> fs[] >> rw[] >>
      metis_tac[] ) >>
    imp_res_tac MEM_LUPDATE_E >> fs[] >> rw[] >>
    fs[el_check_def] >> last_x_assum match_mp_tac >>
    TRY (first_assum(match_exists_tac o concl) >> simp[]) >>
    qmatch_assum_rename_tac`EL n ls = Varray l`[] >>
    qexists_tac`EL n ls` >> simp[] >>
    metis_tac[MEM_EL] ) >>
  strip_tac >- fsrw_tac[DNF_ss][EVERY_MEM,MEM_EL] >>
  strip_tac >- (
    ntac 6 gen_tac >>
    Cases >> fsrw_tac[DNF_ss][EVERY_MEM,MEM_EL] ) >>
  strip_tac >- fsrw_tac[DNF_ss][EVERY_MEM,MEM_EL] >>
  strip_tac >- fsrw_tac[DNF_ss][no_vlabs_csg_def,all_vlabs_csg_def,store_vs_def,EVERY_MAP,EVERY_FILTER,EVERY_GENLIST] >>
  strip_tac >- fsrw_tac[DNF_ss][EVERY_MEM,MEM_EL] >>
  strip_tac >- ( rw[] >> fsrw_tac[DNF_ss][EVERY_MEM,MEM_EL] ) >>
  strip_tac >- fsrw_tac[DNF_ss][EVERY_MEM,MEM_EL] >>
  strip_tac >- fsrw_tac[DNF_ss][EVERY_MEM,MEM_EL]

val Cevaluate_no_vlabs = store_thm("Cevaluate_no_vlabs",
  ``(∀s env exp res. Cevaluate s env exp res ⇒ no_vlabs_csg s ∧ no_vlabs_list env ∧ no_labs exp ⇒
        no_vlabs_csg (FST res) ∧ (∀v. (SND res = Rval v) ⇒ no_vlabs v) ∧ (∀v. (SND res = Rerr (Rraise v)) ⇒ no_vlabs v)) ∧
    (∀s env es res. Cevaluate_list s env es res ⇒ no_vlabs_csg s ∧ no_vlabs_list env ∧ no_labs_list es ⇒
        no_vlabs_csg (FST res) ∧ (∀vs. (SND res = Rval vs) ⇒ no_vlabs_list vs) ∧ (∀v. (SND res = Rerr (Rraise v)) ⇒ no_vlabs v))``,
  tac1)

val Cevaluate_all_vlabs = store_thm("Cevaluate_all_vlabs",
  ``(∀s env exp res. Cevaluate s env exp res ⇒ all_vlabs_csg s ∧ all_vlabs_list env ∧ all_labs exp ⇒
        all_vlabs_csg (FST res) ∧ (∀v. (SND res = Rval v) ⇒ all_vlabs v) ∧ (∀v. (SND res = Rerr (Rraise v)) ⇒ all_vlabs v)) ∧
    (∀s env es res. Cevaluate_list s env es res ⇒ all_vlabs_csg s ∧ all_vlabs_list env ∧ all_labs_list es ⇒
        all_vlabs_csg (FST res) ∧ (∀vs. (SND res = Rval vs) ⇒ all_vlabs_list vs) ∧ (∀v. (SND res = Rerr (Rraise v)) ⇒ all_vlabs v))``,
  tac1)

(* Cevaluate functional equations *)

val Cevaluate_lit = store_thm(
"Cevaluate_lit",
``∀s env l res. Cevaluate s env (CLit l) res = (res = (s, Rval (CLitv l)))``,
rw[Once Cevaluate_cases])

val Cevaluate_var = store_thm(
"Cevaluate_var",
``∀s env vn res. Cevaluate s env (CVar vn) res = (vn < LENGTH env ∧ (res = (s, Rval (EL vn env))))``,
rw[Once Cevaluate_cases] >> PROVE_TAC[])

val _ = export_rewrites["Cevaluate_lit","Cevaluate_var"]

val Cimplode_cases = store_thm("Cimplode_cases",
  ``∀v w. Cimplode v = SOME w ⇔
          v = CConv nil_tag [] ∧ w = [] ∨
          ∃c vs y.
            v = CConv cons_tag [CLitv (Char c); vs] ∧
            Cimplode vs = SOME y ∧
            w = c::y``,
  ho_match_mp_tac Cimplode_ind >>
  rw[Cimplode_def] >>
  rw[EQ_IMP_THM] >>
  BasicProvers.EVERY_CASE_TAC >> fs[] >> rw[])

(* syneq equivalence relation lemmas *)

val Cv_ind = store_thm("Cv_ind",
  ``∀P. (∀l. P (CLitv l)) ∧
        (∀n vs. EVERY P vs ⇒ P (CConv n vs)) ∧
        (∀n vs. EVERY P vs ⇒ P (CVectorv vs)) ∧
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
    Cases_on`n < z` >> fsrw_tac[ARITH_ss][] ) >>
  strip_tac >- rw[Once syneq_exp_cases] >>
  strip_tac >- rw[Once syneq_exp_cases] >>
  strip_tac >- (
    rw[] >> rw[Once syneq_exp_cases] >>
    fsrw_tac[DNF_ss][EVERY2_EVERY,EVERY_MEM,MEM_ZIP,MEM_EL] ) >>
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
  strip_tac >- rw[]);

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
  strip_tac >- ( rw[] >> rw[Once syneq_exp_cases,inv_DEF] ) >>
  strip_tac >- (
    rw[] >> rw[Once syneq_exp_cases] >>
    fs[EVERY2_EVERY,EVERY_MEM,FORALL_PROD,inv_DEF] >>
    rfs[MEM_ZIP] >> rw[] >>
    fsrw_tac[DNF_ss][MEM_EL]) >>
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
  ho_match_mp_tac syneq_ind >> rw[] >>
  TRY (
    rw[] >> simp[Once syneq_cases] >>
    fs[EVERY2_EVERY,EVERY_MEM,MEM_ZIP,FORALL_PROD] >>
    rfs[MEM_ZIP,MEM_EL] >> PROVE_TAC[]) >>
  rw[] >> rw[Once syneq_cases] >>
  map_every qexists_tac[`inv V`,`inv V'`] >>
  simp[inv_DEF] >>
  PROVE_TAC[syneq_exp_sym_no_labs,no_labs_defs_MAP,EVERY_MEM,MEM_EL])

val EVERY2_syneq_sym_no_vlabs = save_thm(
"EVERY2_syneq_sym_no_vlabs",
EVERY2_sym
|> Q.GENL[`R2`,`R1`]
|> Q.ISPECL[`λx y. no_vlabs y ∧ syneq x y`,`syneq`]
|> SIMP_RULE std_ss[syneq_sym_no_vlabs])

val syneq_exp_sym_all_labs = store_thm("syneq_exp_sym_all_labs",
  ``(∀ez1 ez2 V exp1 exp2. syneq_exp ez1 ez2 V exp1 exp2 ⇒ all_labs exp1 ⇒ syneq_exp ez2 ez1 (inv V) exp2 exp1) ∧
    (∀ez1 ez2 V defs1 defs2 V'. syneq_defs ez1 ez2 V defs1 defs2 V' ⇒ all_labs_defs defs1 ⇒ syneq_defs ez2 ez1 (inv V) defs2 defs1 (inv V'))``,
  ho_match_mp_tac syneq_exp_ind >>
  strip_tac >- ( rw[] >> rw[Once syneq_exp_cases]) >>
  strip_tac >- (
    rw[] >> rw[Once syneq_exp_cases] >>
    match_mp_tac (MP_CANON (CONJUNCT1 syneq_exp_mono_V)) >>
    fs[] >> HINT_EXISTS_TAC >>
    simp[inv_DEF] >> Cases >> simp[] ) >>
  strip_tac >- ( rw[] >> rw[Once syneq_exp_cases,inv_DEF] ) >>
  strip_tac >- ( rw[] >> rw[Once syneq_exp_cases,inv_DEF] ) >>
  strip_tac >- ( rw[] >> rw[Once syneq_exp_cases,inv_DEF] ) >>
  strip_tac >- (
    rw[] >> rw[Once syneq_exp_cases] >>
    fs[EVERY2_EVERY,EVERY_MEM,FORALL_PROD,inv_DEF] >>
    rfs[MEM_ZIP] >> rw[] >>
    fsrw_tac[DNF_ss][MEM_EL]) >>
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
    Cases_on`EL n2 defs1`>>fs[]>>
    Cases_on`q`>>fs[] >>
    `all_labs_def (NONE,r)` by PROVE_TAC[] >>
    fs[] ) >>
  strip_tac >> fs[inv_syneq_cb_V] >>
  conj_tac >- (
    first_x_assum match_mp_tac >>
    Cases_on`EL n2 defs1`>>fs[] >>
    Cases_on`q`>>PairCases_on`r`>>fs[syneq_cb_aux_def]>>
    fs[EVERY_MEM,MEM_EL,GSYM LEFT_FORALL_IMP_THM] >>
    last_x_assum(qspec_then`n2`mp_tac) >> simp[] >>
    rfs[] >> PairCases_on`x`>>fs[] >>
    fs[syneq_cb_aux_def]) >>
  rpt gen_tac >> strip_tac >>
  fs[EVERY_MEM,MEM_EL,GSYM LEFT_FORALL_IMP_THM])

val syneq_sym_all_vlabs = store_thm("syneq_sym_all_vlabs",
  ``∀x y. syneq x y ⇒ all_vlabs x ⇒ syneq y x``,
  ho_match_mp_tac syneq_ind >> rw[] >>
  TRY (
    rw[] >> simp[Once syneq_cases] >>
    fs[EVERY2_EVERY,EVERY_MEM,MEM_ZIP,FORALL_PROD] >>
    rfs[MEM_ZIP,MEM_EL] >> PROVE_TAC[]) >>
  rw[] >> rw[Once syneq_cases] >>
  map_every qexists_tac[`inv V`,`inv V'`] >>
  simp[inv_DEF] >>
  PROVE_TAC[syneq_exp_sym_all_labs,all_labs_defs_MAP,EVERY_MEM,MEM_EL])

val EVERY2_syneq_sym_all_vlabs = save_thm(
"EVERY2_syneq_sym_all_vlabs",
EVERY2_sym
|> Q.GENL[`R2`,`R1`]
|> Q.ISPECL[`λx y. all_vlabs x ∧ syneq x y`,`syneq`]
|> SIMP_RULE std_ss[syneq_sym_all_vlabs])

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
  ho_match_mp_tac syneq_ind >> rw[] >>
  TRY (
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
|> Q.GENL[`R2`,`R1`]
|> Q.ISPEC`syneq`
|> SIMP_RULE std_ss [syneq_refl])
(*val _ = export_rewrites["result_rel_syneq_refl"]*)

val result_rel_syneq_trans = save_thm(
"result_rel_syneq_trans",
result_rel_trans
|> Q.GEN`R1`
|> Q.ISPEC`syneq`
|> SIMP_RULE std_ss [GSYM AND_IMP_INTRO]
|> UNDISCH
|> (fn th => PROVE_HYP (PROVE[syneq_trans](hd(hyp th))) th)
|> SIMP_RULE std_ss [AND_IMP_INTRO]
|> Q.GEN`R2`)

(*
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
*)

(* Misc. int lang lemmas *)

(*
val good_cmap_def = Define`
  good_cmap cenv m ⇔
    ALL_DISTINCT (MAP FST cenv) ∧
    NONE ∈ FDOM m ∧
    FLOOKUP m (SOME (Short "Bind")) = SOME bind_exc_cn ∧
    FLOOKUP m (SOME (Short "Div")) = SOME div_exc_cn ∧
    FLOOKUP m (SOME (Short "Eq")) = SOME eq_exc_cn ∧
    (!p1. MEM p1 cenv ⇒ FAPPLY m (SOME (FST p1)) ≠ FAPPLY m NONE) ∧
    ∀p1 p2.
      MEM p1 cenv ∧ MEM p2 cenv ⇒
      SOME (FST p1) ∈ FDOM m ∧ SOME (FST p2) ∈ FDOM m ∧
      ((FAPPLY m (SOME (FST p1)) = FAPPLY m (SOME (FST p2))) ⇒ (p1 = p2))`
*)

val Cevaluate_list_LENGTH = store_thm("Cevaluate_list_LENGTH",
  ``∀exps s env s' vs. Cevaluate_list s env exps (s', Rval vs) ⇒ (LENGTH vs = LENGTH exps)``,
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
  ``(∀s env exp res. Cevaluate s env exp res ⇒ LENGTH (SND (FST s)) ≤ LENGTH (SND (FST (FST res)))) ∧
    (∀s env exps res. Cevaluate_list s env exps res ⇒ LENGTH (SND (FST s)) ≤ LENGTH (SND (FST (FST res))))``,
  ho_match_mp_tac Cevaluate_ind >> rw[] >>
  TRY (PROVE_TAC [LESS_EQ_TRANS]) >- (
    Cases_on`uop`>>fs[]>>srw_tac[ARITH_ss][] >>
    Cases_on`v`>>fs[] >>
    BasicProvers.EVERY_CASE_TAC >>
    fsrw_tac[ARITH_ss][] >>
    Cases_on`l`>>fs[])
  >- (
    PairCases_on`s'`>>
    Cases_on`p2`>>fs[LET_THM,UNCURRY] >>
    qmatch_rename_tac`X ≤ LENGTH (FST (CevalPrim2s s0 op v1 v2))`["X"] >>
    Cases_on`op`>>Cases_on`v2`>>fs[]>>Cases_on`l`>>fs[]>>rw[]>> simp[] >>
    Cases_on`v1`>>fs[]>>Cases_on`l`>>fs[]>>
    rw[] >> simp[] ) >>
  qmatch_assum_rename_tac`X = CevalUpd b s0 v1 v2 v3`["X"] >>
  Cases_on`b`>>Cases_on`v2`>>fs[]>>
  Cases_on`l`>>fs[]>>
  Cases_on`v1`>>fs[] >>
  TRY (
    Cases_on`v3`>>fs[]>>
    Cases_on`l`>>fs[]>>
    BasicProvers.EVERY_CASE_TAC>>fs[] ) >>
  BasicProvers.EVERY_CASE_TAC>>fs[] )

(*
val mvars_def = tDefine"mvars"`
  (mvars (CRaise e) = mvars e) ∧
  (mvars (CHandle e1 e2) = mvars e1 ∪ mvars e2) ∧
  (mvars (CVar (Short _)) = {}) ∧
  (mvars (CVar (Long mn x)) = {(mn,x)}) ∧
  (mvars (CLit _) = {}) ∧
  (mvars (CCon _ es) = mvars_list es) ∧
  (mvars (CTagEq e _) = mvars e) ∧
  (mvars (CProj e _) = mvars e) ∧
  (mvars (CLet e eb) = mvars e ∪ mvars eb) ∧
  (mvars (CLetrec defs e) = mvars_defs defs ∪ mvars e) ∧
  (mvars (CCall _ e es) = mvars e ∪ mvars_list es) ∧
  (mvars (CPrim1 _ e) = mvars e) ∧
  (mvars (CPrim2 _ e1 e2) = mvars e1 ∪ mvars e2) ∧
  (mvars (CUpd e1 e2) = mvars e1 ∪ mvars e2) ∧
  (mvars (CIf e1 e2 e3) = mvars e1 ∪ mvars e2 ∪ mvars e3) ∧
  (mvars_list [] = {}) ∧
  (mvars_list (e::es) = mvars e ∪ mvars_list es) ∧
  (mvars_defs [] = {}) ∧
  (mvars_defs (d::ds) = mvars_def d ∪ mvars_defs ds) ∧
  (mvars_def (_,_,e) = mvars e)`
  (WF_REL_TAC `inv_image $< (λx. case x of
    | INL e => Cexp_size e
    | INR (INL es) => Cexp4_size es
    | INR (INR (INL (defs))) => Cexp1_size defs
    | INR (INR (INR (def))) => Cexp2_size def)`)
val _ = export_rewrites["mvars_def"]
*)

val doPrim2_CLitv_type_error = store_thm("doPrim2_CLitv_type_error",
  ``doPrim2 ty op (CLitv l) (CConv n vs) = Rerr Rtype_error ∧
    doPrim2 ty op (CLitv l) (CRecClos env defs s) = Rerr Rtype_error``,
  Cases_on`l`>>rw[])
val _ = export_rewrites["doPrim2_CLitv_type_error"]

(*
(* Clocs *)

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
  Cases >> fs[] >>
  TRY (Cases >> Cases >> fs [] >>Cases_on`l` >> TRY(Cases_on `l'`) >> fs[] >> rw[] >> rw[] >> NO_TAC) >>
  rw [] >> Cases_on `do_Ceq v1 v2` >> fs [] >> rw []);

val Cevaluate_Clocs = store_thm("Cevaluate_Clocs",
  ``(∀menv s env exp res. Cevaluate menv s env exp res ⇒
     BIGUNION (IMAGE (BIGUNION o IMAGE all_Clocs o set) (FRANGE menv)) ⊆ count (LENGTH (SND s)) ∧
     BIGUNION (IMAGE all_Clocs (set env)) ⊆ count (LENGTH (SND s)) ∧
     BIGUNION (IMAGE all_Clocs (set (SND s))) ⊆ count (LENGTH (SND s))
     ⇒
     BIGUNION (IMAGE all_Clocs (set (SND (FST res)))) ⊆ count (LENGTH (SND (FST res))) ∧
     (∀v. (SND res = Cval v) ⇒ all_Clocs v ⊆ count (LENGTH (SND (FST res)))) ∧
     (∀v. (SND res = Cexc (Craise v)) ⇒ all_Clocs v ⊆ count (LENGTH (SND (FST res))))) ∧
    (∀menv s env exps res. Cevaluate_list menv s env exps res ⇒
     BIGUNION (IMAGE (BIGUNION o IMAGE all_Clocs o set) (FRANGE menv)) ⊆ count (LENGTH (SND s)) ∧
     BIGUNION (IMAGE all_Clocs (set env)) ⊆ count (LENGTH (SND s)) ∧
     BIGUNION (IMAGE all_Clocs (set (SND s))) ⊆ count (LENGTH (SND s))
     ⇒
     BIGUNION (IMAGE all_Clocs (set (SND (FST res)))) ⊆ count (LENGTH (SND (FST res))) ∧
     (∀vs. (SND res = Cval vs) ⇒ BIGUNION (IMAGE all_Clocs (set vs)) ⊆ count (LENGTH (SND (FST res)))) ∧
     (∀v. (SND res = Cexc (Craise v)) ⇒ all_Clocs v ⊆ count (LENGTH (SND (FST res)))))``,
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
      qexists_tac`count (LENGTH (SND s))` >>
      simp[] >> simp[SUBSET_DEF] >>
      fs[] >> simp[] ) >>
    qpat_assum`P ⇒ Q ∧ R`mp_tac >>
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
    qpat_assum`P ⇒ Q ∧ R`mp_tac >>
    discharge_hyps >- (
      fsrw_tac[DNF_ss][SUBSET_DEF] >>
      metis_tac[Cevaluate_store_SUBSET,LESS_LESS_EQ_TRANS,FST] ) >>
    simp[] ) >>
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
    ntac 7 gen_tac >>
    Cases >> fs[] >>
    gen_tac >> ntac 2 strip_tac >>
    fs[] >>
    fsrw_tac[DNF_ss][SUBSET_DEF] >>
    rw[] >> imp_res_tac MEM_LUPDATE_E >>
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
  metis_tac[LESS_LESS_EQ_TRANS]);
*)

(* syneq preservation *)

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
Cases_on `v` >> rw[] >>
Cases_on`l` >> rw[])

val syneq_do_Ceq = Q.prove (
`(∀v1 v1' v2 v2'. syneq v1 v2 ∧ syneq v1' v2' ⇒ do_Ceq v1 v1' = do_Ceq v2 v2') ∧
 (∀vs1 vs1' vs2 vs2'. LIST_REL syneq vs1 vs2 ∧ LIST_REL syneq vs1' vs2' ⇒ do_Ceq_list vs1 vs1' = do_Ceq_list vs2 vs2')`,
 ho_match_mp_tac do_Ceq_ind >>
 rw [] >>
 fs [Once syneq_cases] >>
 rw [] >>
 fs [do_Ceq_def] >>
 imp_res_tac LIST_REL_LENGTH >> fs[] >>
 rw[] >> fs[PULL_EXISTS] >>
 fs[Q.SPEC`CConv X Y`syneq_cases,Q.SPEC`CVectorv X`syneq_cases,PULL_EXISTS,do_Ceq_def] >>
 rfs[] >>
 res_tac >> simp[] >>
 BasicProvers.CASE_TAC >> rw[] >> fs[])

val CevalPrim2_syneq = store_thm("CevalPrim2_syneq",
  ``∀s1 s2 p2 v11 v21 v12 v22.
    csg_rel syneq s1 s2 ∧ syneq v11 v12 ∧ syneq v21 v22 ⇒
    csg_rel syneq (FST (CevalPrim2 s1 p2 v11 v21)) (FST (CevalPrim2 s2 p2 v12 v22)) ∧
    result_rel syneq syneq (SND (CevalPrim2 s1 p2 v11 v21)) (SND (CevalPrim2 s2 p2 v12 v22))``,
  ntac 2 gen_tac >>
  PairCases_on`s1` >> PairCases_on`s2` >>
  gen_tac >>
  `∃op. p2 = P2p op ∨ ∃op. p2 = P2s op` by (Cases_on`p2`>>simp[]) >>
  qmatch_assum_rename_tac`p2 = X op`["X"] >>
  Cases_on`op` >> simp[] >>
  Cases >> TRY(Cases_on`l:lit`>>simp[]) >>
  Cases >> TRY(Cases_on`l:lit`>>simp[]) >>
  rpt(Cases >> TRY(Cases_on`l:lit`>>simp[])) >>
  simp[] >>
  TRY ( simp[Once syneq_cases] >> fsrw_tac[DNF_ss][] >> NO_TAC) >>
  TRY ( simp[Once syneq_cases] >> simp[Once syneq_cases,SimpR``$/\``] >> fsrw_tac[DNF_ss][] >> NO_TAC) >>
  TRY (Cases_on`l` >> Cases_on`l'` >> simp[] >> fsrw_tac[DNF_ss][] >> rw[] >> NO_TAC) >>
  TRY (
    rw[] >>
    spose_not_then strip_assume_tac >>
    imp_res_tac syneq_no_closures >>
    fs[Once syneq_cases] >> rw[] >>
    metis_tac[NOT_EVERY] ) >>
  TRY (
    simp[Once syneq_cases] >> rw[] >>
    BasicProvers.CASE_TAC >> simp[] >> rw[] >>
    rfs[LIST_REL_EL_EQN] >>
    first_x_assum match_mp_tac >> simp[] >>
    NO_TAC) >>
  TRY (
    rw[] >>
    fs[csg_rel_def] >>
    fs[LIST_REL_EL_EQN] >>
    rw[el_check_def] >> rfs[] >> res_tac >>
    BasicProvers.CASE_TAC >> fs[sv_rel_cases] >>
    rw[] >> fs[] >> rfs[integerTheory.INT_ABS] >>
    fsrw_tac[ARITH_ss][LIST_REL_EL_EQN] >>
    NO_TAC) >>
  TRY (
    Cases_on`l':lit`>>simp[]>>rw[]>>
    fs[csg_rel_def] >>
    fs[Once syneq_cases] >>
    fs[LIST_REL_EL_EQN,LENGTH_REPLICATE,EL_REPLICATE] >>
    simp[Once syneq_cases,LIST_REL_EL_EQN,PULL_EXISTS] >>
    metis_tac[]) >>
  simp[Once syneq_cases] >>
  simp[Once syneq_cases] >>
  rpt strip_tac >>
  srw_tac[ETA_ss][] >>
  imp_res_tac syneq_do_Ceq >>
  rw [] >>
  fs[EVERY2_EVERY] >> rfs[] >>
  fs[csg_rel_def,LIST_REL_EL_EQN] >>
  BasicProvers.EVERY_CASE_TAC >>
  rfs[el_check_def] >>
  metis_tac[sv_rel_def]);

val CvFromList_syneq = prove(
  ``∀l1 l2 n l3. syneq l1 l2 ∧ CvFromList l1 = SOME l3 ⇒
      ∃l4. CvFromList l2 = SOME l4 ∧ LIST_REL syneq l3 l4``,
  ho_match_mp_tac CvFromList_ind >>
  simp[CvFromList_def] >> rw[] >- (
    fs[Once syneq_cases] >>
    simp[CvFromList_def] ) >>
  last_x_assum mp_tac >>
  simp[Once syneq_cases] >> rw[] >>
  simp[CvFromList_def] >>
  last_x_assum mp_tac >>
  BasicProvers.CASE_TAC >> rw[] >>
  res_tac >> simp[])

val CvFromList_syneq_sym = prove(
  ``∀l2 l1 n l3. syneq l1 l2 ∧ CvFromList l2 = SOME l3 ⇒
      ∃l4. CvFromList l1 = SOME l4 ∧ LIST_REL syneq l4 l3``,
  ho_match_mp_tac CvFromList_ind >>
  simp[CvFromList_def] >> rw[] >- (
    fs[Once syneq_cases] >>
    simp[CvFromList_def] ) >>
  last_x_assum mp_tac >>
  simp[Once syneq_cases] >> rw[] >>
  simp[CvFromList_def] >>
  last_x_assum mp_tac >>
  BasicProvers.CASE_TAC >> rw[] >>
  res_tac >> simp[])

val Cimplode_syneq = prove(
  ``∀v1 v2. syneq v1 v2 ⇒ Cimplode v1 = Cimplode v2``,
  ho_match_mp_tac Cimplode_ind >> rw[Cimplode_def] >>
  fs[Q.SPEC`CConv X Y`syneq_cases] >> rw[Cimplode_def] >>
  fs[Q.SPEC`CVectorv X`syneq_cases,Q.SPEC`CRecClos A B C`syneq_cases] >>
  rw[Cimplode_def] >> res_tac >> BasicProvers.CASE_TAC)

val CevalPrim1_syneq = store_thm("CevalPrim1_syneq",
  ``∀uop s1 s2 v1 v2. EVERY2 (sv_rel syneq) (FST s1) (FST s2) ∧ LIST_REL (OPTREL syneq) (SND s1) (SND s2) ∧ syneq v1 v2 ⇒
    EVERY2 (sv_rel syneq) (FST (FST (CevalPrim1 uop s1 v1))) (FST (FST (CevalPrim1 uop s2 v2))) ∧
    LIST_REL (OPTREL syneq) (SND (FST (CevalPrim1 uop s1 v1))) (SND (FST (CevalPrim1 uop s2 v2))) ∧
    result_rel syneq syneq (SND (CevalPrim1 uop s1 v1)) (SND (CevalPrim1 uop s2 v2))``,
  Cases_on`s1`>>Cases_on`s2`>>
  Cases >- (
    simp[] >> rw[] >> fs[EVERY2_EVERY] >> lrw[GSYM ZIP_APPEND] ) >>
  Cases >> simp[Once syneq_cases] >>
  fsrw_tac[DNF_ss][] >>
  TRY (
    rw[CvFromList_def] >>
    BasicProvers.CASE_TAC >>
    BasicProvers.CASE_TAC >>
    simp[] >>
    imp_res_tac CvFromList_syneq >>
    imp_res_tac CvFromList_syneq_sym >>
    fs[Q.SPEC`CConv X Y`syneq_cases,PULL_EXISTS] >>
    fs[Q.SPECL[`ZZ`,`CConv X Y`]syneq_cases,PULL_EXISTS] >>
    simp[Q.SPEC`CVectorv Y`syneq_cases] >>
    metis_tac[optionTheory.NOT_SOME_NONE,optionTheory.SOME_11] ) >>
  TRY (
    Cases_on`l:lit`>>rw[]>>NO_TAC) >>
  TRY (
    simp[Cimplode_def] >>
    Q.PAT_ABBREV_TAC`X = Cimplode Y` >> rw[Abbr`X`] >>
    BasicProvers.CASE_TAC >>
    TRY(BasicProvers.CASE_TAC) >> simp[]>>
    imp_res_tac(
      SIMP_RULE(srw_ss())[Q.SPEC`CConv A B`syneq_cases](Q.SPECL[`CConv A B`,`CConv A C`]Cimplode_syneq)) >>
    fs[] >> NO_TAC) >>
  rw[el_check_def,EVERY2_EVERY] >>
  rfs[EVERY_MEM,MEM_ZIP,FORALL_PROD] >>
  fsrw_tac[DNF_ss][] >>
  fs[EL_LUPDATE,optionTheory.OPTREL_def] >> rw[] >>
  TRY ( res_tac >> fs[] >> NO_TAC ) >>
  TRY (
    spose_not_then strip_assume_tac >>
    fs[EVERY_MEM] >> rfs[MEM_ZIP,PULL_EXISTS,optionTheory.OPTREL_def] >>
    res_tac >> fs[] >> NO_TAC) >>
  rw[Once syneq_cases] >>
  TRY (
    BasicProvers.EVERY_CASE_TAC >> fs[] >>
    metis_tac[sv_rel_def,LIST_REL_LENGTH] ) >>
  simp[EVERY2_EVERY,EVERY_MEM,MEM_ZIP,FORALL_PROD,PULL_EXISTS] >>
  metis_tac[])

val CevalUpd_syneq = store_thm("CevalUpd_syneq",
  ``∀b s1 v1 v2 v3 s2 w1 w2 w3.
    syneq v1 w1 ∧ syneq v2 w2 ∧ syneq v3 w3 ∧ EVERY2 (sv_rel syneq) s1 s2 ⇒
    EVERY2 (sv_rel syneq) (FST (CevalUpd b s1 v1 v2 v3)) (FST (CevalUpd b s2 w1 w2 w3)) ∧
    result_rel syneq syneq (SND (CevalUpd b s1 v1 v2 v3)) (SND (CevalUpd b s2 w1 w2 w3))``,
  rpt gen_tac >>
  Cases_on`b`>>
  Cases_on`v2` >> TRY(Cases_on`l:lit`) >> simp[] >>
  Cases_on`v1` >> TRY(Cases_on`l:lit`) >> simp[] >>
  Cases_on`v3` >> TRY(Cases_on`l:lit`) >> simp[] >>
  fs[Q.SPEC`CConv X Y`syneq_cases] >> rw[] >>
  fs[Q.SPEC`CVectorv Y`syneq_cases] >> rw[] >>
  fs[Q.SPEC`CRecClos X Y Z`syneq_cases] >> rw[] >>
  BasicProvers.EVERY_CASE_TAC >>
  fs[el_check_def,LIST_REL_EL_EQN,EL_LUPDATE] >> rw[] >>
  simp[Q.SPEC`CConv X Y`syneq_cases,LIST_REL_EL_EQN] >>
  simp[Q.SPEC`CRecClos X Y Z`syneq_cases] >>
  simp[Q.SPEC`CVectorv Y`syneq_cases,LIST_REL_EL_EQN] >>
  simp[EL_LUPDATE] >> rw[] >>
  simp[Q.SPEC`CConv X Y`syneq_cases,LIST_REL_EL_EQN] >>
  simp[Q.SPEC`CRecClos X Y Z`syneq_cases] >>
  simp[Q.SPEC`CVectorv Y`syneq_cases,LIST_REL_EL_EQN] >>
  metis_tac[sv_rel_def,LIST_REL_EL_EQN] )

val Cevaluate_count_greater = store_thm("Cevaluate_count_greater",
  ``(∀cs env exp res. Cevaluate cs env exp res ⇒ FST (FST (FST res)) ≤ FST (FST cs)) ∧
    (∀cs env exps res. Cevaluate_list cs env exps res ⇒ FST (FST (FST res)) ≤ FST (FST cs))``,
  ho_match_mp_tac Cevaluate_ind >> srw_tac[ARITH_ss][]>>
  PairCases_on`s'`>>Cases_on`p2`>>fs[LET_THM,UNCURRY])

val Cevaluate_syneq = store_thm("Cevaluate_syneq",
  ``(∀s1 env1 exp1 res1. Cevaluate s1 env1 exp1 res1 ⇒
      ∀ez1 ez2 V s2 env2 exp2 res2.
        syneq_exp (LENGTH env1) (LENGTH env2) V exp1 exp2
      ∧ (∀v1 v2. V v1 v2 ∧ v1 < LENGTH env1 ∧ v2 < LENGTH env2 ⇒ syneq (EL v1 env1) (EL v2 env2))
      ∧ csg_rel syneq s1 s2
      ⇒ ∃res2.
        Cevaluate s2 env2 exp2 res2 ∧
        csg_rel syneq (FST res1) (FST res2) ∧
        result_rel syneq syneq (SND res1) (SND res2)) ∧
    (∀s1 env1 es1 res1. Cevaluate_list s1 env1 es1 res1 ⇒
      ∀ez1 ez2 V s2 env2 es2 res2.
        EVERY2 (syneq_exp (LENGTH env1) (LENGTH env2) V) es1 es2
      ∧ (∀v1 v2. V v1 v2 ∧ v1 < LENGTH env1 ∧ v2 < LENGTH env2 ⇒ syneq (EL v1 env1) (EL v2 env2))
      ∧ csg_rel syneq s1 s2
      ⇒ ∃res2.
        Cevaluate_list s2 env2 es2 res2 ∧
        csg_rel syneq (FST res1) (FST res2) ∧
        result_rel (EVERY2 (syneq)) syneq (SND res1) (SND res2))``,
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
    simp[EXISTS_PROD] >> fsrw_tac[DNF_ss][] >> rw[] >>
    first_assum (match_exists_tac o concl) >> simp[] >>
    first_x_assum(exists_suff_gen_then mp_tac) >>
    simp[ADD1,GSYM AND_IMP_INTRO] >>
    disch_then(fn th => (first_x_assum(mp_tac o MATCH_MP th))) >>
    simp[AND_IMP_INTRO] >>
    disch_then(exists_suff_then mp_tac) >>
    simp[] >>
    discharge_hyps >- (
      Cases >> simp[] >>
      Cases >> simp[ADD1] >> PROVE_TAC[] ) >>
    simp[EXISTS_PROD] ) >>
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
    simp[EXISTS_PROD] >>
    Cases_on`err`>>fs[]) >>
  strip_tac >- (
    rw[] >>
    rator_x_assum`syneq_exp`mp_tac >>
    simp[Once (syneq_exp_cases)] >>
    rw[] >> simp[] >> metis_tac[]) >>
  strip_tac >- (
    simp[FORALL_PROD] >> rw[] >>
    rator_x_assum`syneq_exp`mp_tac >>
    simp[Once (syneq_exp_cases)] >>
    rw[Once Cevaluate_cases] >>
    fs[EXISTS_PROD,PULL_EXISTS,csg_rel_def] >>
    fs[EVERY2_EVERY,EVERY_MEM,FORALL_PROD,optionTheory.OPTREL_def] >>
    rfs[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM] >>
    metis_tac[optionTheory.NOT_SOME_NONE,optionTheory.SOME_11]) >>
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
    map_every qx_gen_tac[`e`,`b`] >>
    rw[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][] >>
    disj1_tac >>
    last_x_assum(qspecl_then[`V`,`s2`,`env2`,`e`]mp_tac) >>
    simp[EXISTS_PROD] >> fsrw_tac[DNF_ss][] >> rw[] >>
    first_assum (match_exists_tac o concl) >> simp[] >>
    first_x_assum(exists_suff_gen_then mp_tac) >>
    simp[ADD1,GSYM AND_IMP_INTRO] >>
    disch_then(fn th => (first_x_assum(mp_tac o MATCH_MP th))) >>
    simp[AND_IMP_INTRO] >>
    disch_then(exists_suff_then mp_tac) >>
    simp[] >>
    TRY( discharge_hyps >- ( Cases >> simp[] >> Cases >> simp[] )) >>
    simp[EXISTS_PROD]) >>
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
    simp[] >> rpt gen_tac >> strip_tac >>
    rpt gen_tac >> strip_tac >>
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
    map_every qx_gen_tac[`s2'a`,`s2'b`,`s2'c`,`V'`,`cenv2`,`defs2`,`d2`,`U`] >>
    strip_tac >> qmatch_assum_rename_tac`U d1 d2`[] >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    first_x_assum(exists_suff_gen_then mp_tac) >>
    simp[GSYM AND_IMP_INTRO] >>
    disch_then(fn th => (first_x_assum(mp_tac o MATCH_MP th))) >>
    simp[AND_IMP_INTRO] >>
    disch_then(exists_suff_then mp_tac) >> simp[] >>
    simp[EXISTS_PROD] >>
    simp_tac(std_ss++DNF_ss)[] >>
    map_every qx_gen_tac[`s2''a`,`s2''b`,`s2''c`,`vs2`] >>
    strip_tac >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    rator_assum`syneq_defs`mp_tac >>
    simp_tac std_ss [Once syneq_exp_cases] >>
    strip_tac >>
    pop_assum(qspecl_then[`d1`,`d2`]mp_tac) >>
    simp[] >>
    qabbrev_tac`p1 = EL d1 defs` >>
    qabbrev_tac`p2 = EL d2 defs2` >>
    PairCases_on`p1`>>PairCases_on`p2` >> fs[] >>
    fs[csg_rel_def] >>
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
        TRY (fs[csg_rel_def,EVERY2_EVERY,EVERY_MEM,FORALL_PROD] >>NO_TAC) >>
        simp[Once syneq_cases] >>
        map_every qexists_tac[`V'`,`U`] >>
        qpat_assum`U X Y`mp_tac >>
        fsrw_tac[DNF_ss,ARITH_ss][] >>
        metis_tac[] ) >>
      fs[syneq_cb_aux_def,LET_THM,UNCURRY] ) >>
    Cases_on`p10` >- (
      PairCases_on`x`>>fs[syneq_cb_aux_def,LET_THM,UNCURRY] >>
      Q.PAT_ABBREV_TAC`count'' = if ck then X else (Y:num)` >>
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
      TRY (fs[csg_rel_def,EVERY2_EVERY,EVERY_MEM,FORALL_PROD] >>NO_TAC) >>
      simp[Once syneq_cases] >>
      map_every qexists_tac[`V'`,`U`] >>
      qpat_assum`U X Y`mp_tac >>
      simp[] >> metis_tac[] ) >>
    Q.PAT_ABBREV_TAC`count'' = if ck then X else (Y:num)` >>
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
    TRY (fs[csg_rel_def,EVERY2_EVERY,EVERY_MEM,FORALL_PROD] >>NO_TAC) >>
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
    strip_tac >>
    simp[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][] >>
    disj2_tac >> disj1_tac >>
    last_x_assum(qspecl_then[`V`,`s2`,`env2`,`e2`]mp_tac) >>
    simp[GSYM AND_IMP_INTRO] >> disch_then(mp_tac o UNDISCH_ALL) >>
    simp[EXISTS_PROD] >>
    simp[Once syneq_cases] >>
    simp_tac(std_ss++DNF_ss)[] >> rw[] >>
    qmatch_assum_rename_tac`U d1 d2`[] >>
    first_assum (match_exists_tac o concl) >> simp[] >>
    first_x_assum(exists_suff_gen_then mp_tac) >>
    simp[ADD1,GSYM AND_IMP_INTRO] >>
    disch_then(fn th => (first_x_assum(mp_tac o MATCH_MP th))) >>
    simp[AND_IMP_INTRO] >>
    disch_then(exists_suff_then mp_tac) >>
    simp[EXISTS_PROD,csg_rel_def] >>
    metis_tac[]) >>
  strip_tac >- (
    rw[] >>
    rator_x_assum`syneq_exp`mp_tac >>
    simp[Once (syneq_exp_cases)] >>
    fsrw_tac[DNF_ss][] >>
    map_every qx_gen_tac[`e2`,`es2`] >>
    rw[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][] >>
    disj2_tac >> disj2_tac >> disj1_tac >>
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
    disj2_tac >> disj2_tac >> disj2_tac >>
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
    first_x_assum(qspecl_then[`V`,`s2`,`env2`,`e2`]mp_tac) >>
    simp[] >> rw[] >>
    first_assum (match_exists_tac o concl) >> simp[] >>
    fs[csg_rel_def] >>
    metis_tac[CevalPrim1_syneq,FST,SND,pair_CASES,PAIR_EQ]) >>
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
    fs[GSYM AND_IMP_INTRO] >>
    rpt(first_x_assum(fn th => first_x_assum (strip_assume_tac o MATCH_MP th))) >>
    first_assum(split_pair_match o concl) >> fs[] >>
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
    fs[GSYM AND_IMP_INTRO] >>
    rpt(first_x_assum(fn th => first_x_assum (strip_assume_tac o MATCH_MP th))) >>
    first_assum(split_pair_match o concl) >> fs[] >>
    fs[csg_rel_def] >>
    metis_tac[CevalUpd_syneq,FST,SND,pair_CASES,PAIR_EQ]) >>
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
    first_assum (match_exists_tac o concl) >>
    simp[] >>
    first_x_assum match_mp_tac >> simp[] >>
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
  strip_tac >- (
    simp[FORALL_PROD,EXISTS_PROD,csg_rel_def] >> rw[] >>
    rator_x_assum`syneq_exp`mp_tac >>
    simp[Once syneq_exp_cases] >> rw[] >>
    rw[Once Cevaluate_cases] >>
    match_mp_tac EVERY2_APPEND_suff >> rw[] >>
    match_mp_tac EVERY2_refl >> rw[] ) >>
  strip_tac >- ( rw[] >> simp[Once Cevaluate_cases] ) >>
  strip_tac >- (
    rw[] >>
    simp[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][EXISTS_PROD] >>
    qmatch_assum_rename_tac`syneq_exp (LENGTH env1) (LENGTH env2) V e1 e2`[] >>
    last_x_assum(qspecl_then[`V`,`s2`,`env2`,`e2`]mp_tac) >>
    simp[GSYM AND_IMP_INTRO] >> disch_then(mp_tac o UNDISCH_ALL) >>
    fsrw_tac[DNF_ss][] >> rw[] >>
    first_assum (match_exists_tac o concl) >> simp[] >>
    first_x_assum match_mp_tac >> simp[] >>
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
  fsrw_tac[DNF_ss][] >> rw[] >>
  first_assum (match_exists_tac o concl) >> simp[] >>
  first_x_assum match_mp_tac >>
  simp[] >> metis_tac[] )

(*
val Cevaluate_any_syneq_store = store_thm("Cevaluate_any_syneq_store",
  ``∀s s' env exp res. Cevaluate s env exp res ∧ FST s = FST s' ∧ EVERY2 (syneq) (SND s) (SND s') ⇒
      ∃res'. Cevaluate s' env exp res' ∧ FST (FST res) = FST (FST res') ∧ EVERY2 (syneq) (SND (FST res)) (SND (FST res')) ∧ Cresult_rel syneq syneq (SND res) (SND res')``,
    rw[] >>
    qspecl_then[`menv`,`s`,`env`,`exp`,`res`]mp_tac (CONJUNCT1 Cevaluate_syneq) >> simp[] >>
    disch_then(qspecl_then[`$=`,`menv`,`s'`,`env`,`exp`]mp_tac) >> simp[syneq_exp_refl])

val Cevaluate_list_any_syneq_any = store_thm("Cevaluate_list_any_syneq_any",
  ``∀menv1 menv2 s1 s2 env1 env2 e res. Cevaluate_list menv1 s1 env1 e res ∧ FST s1 = FST s2 ∧ EVERY2 (syneq) (SND s1) (SND s2) ∧ EVERY2 (syneq) env1 env2 ∧ fmap_rel (LIST_REL syneq) menv1 menv2 ⇒
      ∃res2. Cevaluate_list menv2 s2 env2 e res2 ∧ FST (FST res) = FST (FST res2) ∧ EVERY2 (syneq) (SND (FST res)) (SND (FST res2)) ∧ Cresult_rel (EVERY2 (syneq)) syneq (SND res) (SND res2)``,
    rw[] >>
    qspecl_then[`menv1`,`s1`,`env1`,`e`,`res`]mp_tac (CONJUNCT2 Cevaluate_syneq) >> simp[] >>
    `LENGTH env1 = LENGTH env2` by fs[EVERY2_EVERY] >>
    disch_then(qspecl_then[`$=`,`menv2`,`s2`,`env2`,`e`]mp_tac) >> simp[syneq_exp_refl] >>
    discharge_hyps >- (
      fsrw_tac[DNF_ss][EVERY2_EVERY,EVERY_MEM,FORALL_PROD,MEM_ZIP,syneq_exp_refl] ) >> simp[])
*)

(* Closed values *)

val (Cclosed_rules,Cclosed_ind,Cclosed_cases) = Hol_reln`
(Cclosed (CLitv l)) ∧
(EVERY (Cclosed) vs ⇒ Cclosed (CConv cn vs)) ∧
(EVERY (Cclosed) vs ⇒ Cclosed (CVectorv vs)) ∧
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
``∀ty op v1 v2. every_result Cclosed Cclosed (doPrim2 ty op v1 v2)``,
ntac 2 gen_tac >>
Cases >> TRY (Cases_on `l`) >>
Cases >> TRY (Cases_on `l`) >>
rw[] >> rw[Cclosed_cases])
val _ = export_rewrites["doPrim2_closed"];

val CevalPrim2_closed = store_thm("CevalPrim2_closed",
  ``∀s p2 v1 v2.
    csg_every Cclosed s ∧ Cclosed v1 ⇒
    csg_every Cclosed (FST (CevalPrim2 s p2 v1 v2)) ∧
    every_result Cclosed Cclosed (SND (CevalPrim2 s p2 v1 v2))``,
  rpt gen_tac >>
  PairCases_on`s` >>
  `∃op. p2 = P2p op ∨ ∃op'. p2 = P2s op'` by (Cases_on`p2`>>simp[]) >>
  qmatch_assum_rename_tac`p2 = X op`["X"] >>
  Cases_on`op`>>simp[UNCURRY] >- (
    Cases_on `do_Ceq v1 v2` >>
    rw [Cclosed_cases]) >>
  TRY(
    Cases_on`v2`>>simp[]>>Cases_on`l:lit`>>simp[]>>rw[]>>
    fs[csg_every_def,EVERY_MEM,REPLICATE_GENLIST,MEM_GENLIST,PULL_EXISTS] >>
    NO_TAC) >>
  Cases_on`v1`>>Cases_on`v2`>>simp[]>>
  TRY(Cases_on`l:lit`)>>TRY(Cases_on`l':lit`)>>simp[] >>
  BasicProvers.EVERY_CASE_TAC >> simp[] >>
  simp[csg_every_def] >>
  TRY (
    fs[EVERY_MEM,MEM_EL,PULL_EXISTS,el_check_def] >> rw[] >>
    last_x_assum(qspec_then`n`mp_tac) >> simp[] >>
    simp[EVERY_MEM,PULL_EXISTS,MEM_EL] >> NO_TAC) >>
  simp[Once Cclosed_cases,EVERY_MEM,MEM_EL,PULL_EXISTS] >> rw[] >>
  first_x_assum match_mp_tac >> fs[] >> simp[])

val CvFromList_closed = prove(
  ``∀v x. Cclosed v ⇒ CvFromList v = SOME x ⇒ EVERY Cclosed x``,
  ho_match_mp_tac CvFromList_ind >> simp[CvFromList_def] >> rw[] >>
  last_x_assum mp_tac >> simp[Once Cclosed_cases] >> rw[] >> fs[] >>
  BasicProvers.EVERY_CASE_TAC >> fs[] >> rw[])

val Cexplode_closed = prove(
  ``∀ls. Cclosed (Cexplode ls)``,
  Induct >> simp[Cexplode_def,Once Cclosed_cases])

val CevalPrim1_closed = store_thm("CevalPrim1_closed",
  ``∀s uop v. EVERY (sv_every Cclosed) (FST s) ∧ EVERY (OPTION_EVERY Cclosed) (SND s) ∧ Cclosed v ⇒
    EVERY (sv_every Cclosed) (FST (FST (CevalPrim1 uop s v))) ∧
    EVERY (OPTION_EVERY Cclosed) (SND(FST (CevalPrim1 uop s v))) ∧
    every_result Cclosed Cclosed (SND (CevalPrim1 uop s v))``,
  Cases >> Cases >> rw[LET_THM,Cclosed_rules] >> rw[] >>
  Cases_on`v`>>fs[] >>
  rw[el_check_def] >>
  fsrw_tac[DNF_ss][EVERY_MEM,MEM_EL] >>
  rw[EL_LUPDATE] >>
  simp[CvFromList_def] >>
  BasicProvers.EVERY_CASE_TAC >> simp[] >-
    metis_tac[sv_every_def]
  >- (
    rator_x_assum`Cclosed`mp_tac >>
    simp[Once Cclosed_cases,EVERY_MEM,MEM_EL,PULL_EXISTS]) >>
  imp_res_tac CvFromList_closed >>
  simp[Once Cclosed_cases] >>
  Cases_on`l`>>fs[Cexplode_def,Cexplode_closed])

val CevalUpd_closed = store_thm("CevalUpd_closed",
  ``(∀b s v1 v2 v3. Cclosed v2 ⇒ every_result Cclosed Cclosed (SND (CevalUpd b s v1 v2 v3))) ∧
    (∀b s v1 v2 v3. EVERY (sv_every Cclosed) s ∧ Cclosed v2 ∧ Cclosed v3 ⇒ EVERY (sv_every Cclosed) (FST (CevalUpd b s v1 v2 v3)))``,
  conj_tac >> rpt gen_tac >>
  Cases_on`b`>>Cases_on`v2`>>simp[] >>
  Cases_on`l`>>simp[]>>
  Cases_on`v1`>>simp[]>>rw[]>>
  BasicProvers.EVERY_CASE_TAC >> fs[]>>
  TRY(
    Cases_on`v3`>>simp[]>>
    Cases_on`l`>>simp[]>>
    BasicProvers.EVERY_CASE_TAC>>simp[]>>
    fs[EVERY_MEM] >>
    metis_tac[MEM_LUPDATE_E,sv_every_def]) >>
  fs[EVERY_MEM,el_check_def] >>
  metis_tac[MEM_LUPDATE_E,sv_every_def,MEM_EL,EVERY_MEM] )

val Cevaluate_closed = store_thm("Cevaluate_closed",
  ``(∀s env exp res. Cevaluate s env exp res
     ⇒ set (free_vars exp) ⊆ count (LENGTH env)
     ∧ no_labs exp
     ∧ EVERY (Cclosed) env
     ∧ csg_every Cclosed s
     ⇒
     csg_every Cclosed (FST res) ∧
     every_result Cclosed (Cclosed) (SND res)) ∧
    (∀s env exps ress. Cevaluate_list s env exps ress
     ⇒ set (free_vars_list exps) ⊆ count (LENGTH env)
     ∧ no_labs_list exps
     ∧ EVERY (Cclosed) env
     ∧ csg_every Cclosed s
     ⇒
     csg_every Cclosed (FST ress) ∧
     every_result (EVERY (Cclosed)) Cclosed (SND ress))``,
  ho_match_mp_tac Cevaluate_ind >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rpt gen_tac >> ntac 2 strip_tac >>
    fsrw_tac[DNF_ss][ADD1] >>
    rfs[] >>
    rpt conj_tac >>
    last_x_assum(match_mp_tac o MP_CANON) >>
    fsrw_tac[DNF_ss][SUBSET_DEF,MEM_MAP,MEM_FILTER] >>
    Cases >> fsrw_tac[ARITH_ss][] >>
    rw[] >> res_tac >> fs[ADD1]) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rw[] >> fsrw_tac[DNF_ss][EVERY_MEM,MEM_EL] ) >>
  strip_tac >- (
    rw[] >>
    PairCases_on`s` >> fs[csg_every_def] >>
    fsrw_tac[DNF_ss][EVERY_MEM,MEM_EL] >> PROVE_TAC[OPTION_EVERY_def]) >>
  strip_tac >- ( rw[] >> rw[Once Cclosed_cases]) >>
  strip_tac >- (
    srw_tac[ETA_ss][FOLDL_UNION_BIGUNION] >> fs[] >>
    rw[Once Cclosed_cases] ) >>
  strip_tac >- (
    srw_tac[ETA_ss][FOLDL_UNION_BIGUNION] >> fs[]) >>
  strip_tac >- (
    rpt gen_tac >> ntac 2 strip_tac >>
    first_x_assum match_mp_tac >>
    fsrw_tac[DNF_ss][SUBSET_DEF,ADD1,MEM_MAP,MEM_FILTER] >>
    BasicProvers.CASE_TAC >> simp[] >>
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
      fs[csg_every_def] >>
      metis_tac[]) >>
    fs[Once Cclosed_cases] >>
    last_x_assum(qspecl_then[`SOME x`,`def1`,`def2`]mp_tac) >>
    discharge_hyps >- PROVE_TAC[MEM_EL] >>
    simp[]) >>
  strip_tac >- (
    rpt gen_tac >> ntac 2 strip_tac >>
    fsrw_tac[ETA_ss][FOLDL_UNION_BIGUNION]) >>
  strip_tac >- (
    rpt gen_tac >> ntac 2 strip_tac >>
    fsrw_tac[ETA_ss][FOLDL_UNION_BIGUNION]) >>
  strip_tac >- (
    rpt gen_tac >> ntac 2 strip_tac >>
    fsrw_tac[ETA_ss][FOLDL_UNION_BIGUNION] ) >>
  strip_tac >- (
    rpt gen_tac >> ntac 2 strip_tac >>
    full_simp_tac std_ss [free_vars_def,every_result_def] >>
    PairCases_on`s`>>fs[csg_every_def] >>
    fs[] >> metis_tac[CevalPrim1_closed,FST,SND]) >>
  strip_tac >- rw[] >>
  strip_tac >- (rw[] >> metis_tac[CevalPrim2_closed]) >>
  strip_tac >- ( rw[] >> metis_tac[] ) >>
  strip_tac >- (
    rw[] >>
    PairCases_on`s`>>fs[csg_every_def] >>
    metis_tac[CevalUpd_closed,FST,SND]) >>
  strip_tac >- ( rw[] >> metis_tac[] ) >>
  strip_tac >- (
    rpt gen_tac >> ntac 2 strip_tac >>
    first_x_assum match_mp_tac >>
    fs[] >> rw[] ) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rw[] >>
    PairCases_on`cs`>>fs[csg_every_def]>>
    rw[EVERY_MEM,MEM_GENLIST] >>
    rw[OPTION_EVERY_def] ) >>
  strip_tac >- (
    rpt gen_tac >> ntac 2 strip_tac >>
    full_simp_tac std_ss [] >>
    fs[] ) >>
  strip_tac >- (
    rpt gen_tac >> ntac 2 strip_tac >>
    full_simp_tac std_ss [] >>
    fs[] >> metis_tac[]) >>
  strip_tac >- (
    rpt gen_tac >> ntac 2 strip_tac >>
    full_simp_tac std_ss [] >>
    fs[] >> metis_tac[]) >>
  rpt gen_tac >> ntac 2 strip_tac >>
  full_simp_tac std_ss [] >>
  fs[] )

(*
val closed_Clocs_def = Define`
  closed_Clocs Cmenv Cenv Cs ⇔
    (BIGUNION (IMAGE (BIGUNION o IMAGE all_Clocs o set) (FRANGE Cmenv)) ⊆ count (LENGTH Cs)) ∧
    (BIGUNION (IMAGE all_Clocs (set Cs)) ⊆ count (LENGTH Cs)) ∧
    (BIGUNION (IMAGE all_Clocs (set Cenv)) ⊆ count (LENGTH Cs))`

val Cevaluate_closed_Clocs = store_thm("Cevaluate_closed_Clocs",
  ``∀menv s env exp res.
    closed_Clocs menv env (SND s) ∧
    Cevaluate menv s env exp res
    ⇒
    closed_Clocs menv env (SND(FST res)) ∧
    (∀v. SND res = Cval v ∨ SND res = Cexc (Craise v) ⇒ all_Clocs v ⊆ count (LENGTH (SND (FST res))))``,
  rw[closed_Clocs_def] >>
  TRY (
    match_mp_tac SUBSET_TRANS >>
    HINT_EXISTS_TAC >> simp[] >>
    qspecl_then[`menv`,`s`,`env`,`exp`,`res`]mp_tac(CONJUNCT1 Cevaluate_store_SUBSET) >>
    simp[SUBSET_DEF] ) >>
  qspecl_then[`menv`,`s`,`env`,`exp`,`res`]mp_tac(CONJUNCT1 Cevaluate_Clocs) >>
  simp[])
*)

val good_cd_def = Define`
  good_cd ((ez,nz,ix),(l,cc,recs,envs),az,b) ⇔
    EVERY (λv. v < ez) envs ∧
    set (free_vars b) ⊆ count (LENGTH cc) ∧
    ∃e e'. (cc,(recs,envs),e') = (bind_fv (az,e) nz ix)`

val code_env_cd_def = Define`
  code_env_cd code (x,(l,ccenv,ce),(az,b)) ⇔
    good_cd (x,(l,ccenv,ce),(az,b)) ∧
    ∃cs bc0 cc bc1.
      ((compile (MAP CTEnv ccenv) (TCTail az 0) 0 cs b).out = cc ++ cs.out) ∧
      EVERY (combin$C $< cs.next_label o dest_Label) (FILTER is_Label bc0) ∧ l < cs.next_label ∧
      (code = bc0 ++ Label l :: (REVERSE cc) ++ bc1)`

val closed_vlabs_def = Define`
  closed_vlabs env csg code ⇔
    all_vlabs_csg csg ∧ all_vlabs_list env ∧
    (∀cd. cd ∈ vlabs_csg csg ⇒ code_env_cd code cd) ∧
    (∀cd. cd ∈ vlabs_list env ⇒ code_env_cd code cd)`

val Cevaluate_closed_vlabs = store_thm("Cevaluate_closed_vlabs",
  ``∀s env exp res code.
    closed_vlabs env s code ∧
    Cevaluate s env exp res ∧ all_labs exp ∧
    (∀cd. MEM cd (free_labs (LENGTH env) exp) ⇒ code_env_cd code cd)
    ⇒
    closed_vlabs env (FST res) code ∧
    (∀v. SND res = Rval v ∨ SND res = Rerr (Rraise v) ⇒
      all_vlabs v ∧
      vlabs v ⊆ vlabs_csg s ∪ vlabs_list env ∪ set (free_labs (LENGTH env) exp))``,
  rpt gen_tac >>
  simp[closed_vlabs_def] >>
  strip_tac >>
  qspecl_then[`s`,`env`,`exp`,`res`]mp_tac(CONJUNCT1 Cevaluate_vlabs)>>
  qspecl_then[`s`,`env`,`exp`,`res`]mp_tac(CONJUNCT1 Cevaluate_all_vlabs)>>
  simp[] >>
  rw[] >> fs[SUBSET_DEF] >>
  metis_tac[])

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
 strip_tac >- rw[Once syneq_exp_cases] >>
 strip_tac >- (
   rw[] >>
   rw[Once syneq_exp_cases] >>
   fsrw_tac[DNF_ss][FOLDL_UNION_BIGUNION,SUBSET_DEF,EVERY2_EVERY,EVERY_MEM,FORALL_PROD,MEM_ZIP,free_labs_list_MAP,MEM_FLAT,MEM_MAP] >>
   fsrw_tac[DNF_ss][free_vars_list_MAP,MEM_FLAT,MEM_MAP] >>
   fsrw_tac[DNF_ss][EL_MAP,MEM_EL] >> rw[]) >>
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
 strip_tac >- ( rw[] >> rw[Once syneq_exp_cases] ) >>
 strip_tac >- ( rw[] >> rw[Once syneq_exp_cases] ))

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

val all_labs_free_labs = store_thm("all_labs_free_labs",
  ``(∀e. all_labs e ⇒ ∀z. all_labs_list (MAP (SND o SND o SND) (free_labs z e))) ∧
    (∀es. all_labs_list es ⇒ ∀z. all_labs_list (MAP (SND o SND o SND) (free_labs_list z es))) ∧
    (∀ds. all_labs_defs ds ⇒ ∀x y z. all_labs_list (MAP (SND o SND o SND) (free_labs_defs x y z ds))) ∧
    (∀d. all_labs_def d ⇒ ∀x y z. all_labs_list (MAP (SND o SND o SND) (free_labs_def x y z d)))``,
  ho_match_mp_tac all_labs_ind >>
  simp[free_labs_list_MAP,FORALL_PROD])

val free_labs_free_labs = store_thm("free_labs_free_labs",
  ``(∀z e. IMAGE (FST o FST o SND)
             (BIGUNION (IMAGE ((λp. set (free_labs (LENGTH(FST(SND(FST p)))) (SND(SND p)))) o SND) (set (free_labs z e))))
         ⊆ IMAGE (FST o FST o SND) (set (free_labs z e))) ∧
    (∀z es. IMAGE (FST o FST o SND)
             (BIGUNION (IMAGE ((λp. set (free_labs (LENGTH(FST(SND(FST p)))) (SND(SND p)))) o SND) (set (free_labs_list z es))))
         ⊆ IMAGE (FST o FST o SND) (set (free_labs_list z es))) ∧
    (∀x y z ds.
           IMAGE (FST o FST o SND)
             (BIGUNION (IMAGE ((λp. set (free_labs (LENGTH(FST(SND(FST p)))) (SND(SND p)))) o SND) (set (free_labs_defs x y z ds))))
         ⊆ IMAGE (FST o FST o SND) (set (free_labs_defs x y z ds))) ∧
    (∀x y z d.
           IMAGE (FST o FST o SND)
             (BIGUNION (IMAGE ((λp. set (free_labs (LENGTH(FST(SND(FST p)))) (SND(SND p)))) o SND) (set (free_labs_def x y z d))))
         ⊆ IMAGE (FST o FST o SND) (set (free_labs_def x y z d)))``,
  ho_match_mp_tac free_labs_ind >> simp[] >> rw[] >>
  TRY(fsrw_tac[DNF_ss][SUBSET_DEF] >> metis_tac[]) >>
  qmatch_abbrev_tac`a ⊆ l INSERT b` >>
  qsuff_tac`a = b`>-(rw[SUBSET_DEF]>>metis_tac[]) >>
  unabbrev_all_tac >>
  simp[IMAGE_COMPOSE,GSYM LIST_TO_SET_MAP] >>
  metis_tac[MAP_SND_free_labs_any_ez])

val shift_thm =
  mkshift_thm
  |> Q.SPEC`λv. v + n`
  |> SIMP_RULE std_ss [GSYM shift_def]
  |> Q.GEN`n`

val syneq_exp_shift_both = store_thm("syneq_exp_shift_both",
  ``∀z1 z2 V e1 e2 n k z1' z2' V'. syneq_exp z1 z2 V e1 e2 ∧
      set (free_vars e1) ⊆ count z1 ∧ k ≤ z1 ∧ no_labs e1 ∧
      set (free_vars e2) ⊆ count z2 ∧ k ≤ z2 ∧ no_labs e2 ∧
      (let R = λx y. if x < k then y = x else y = x+n in
         (∀x y. (R O V O inv R) x y ⇒ V' x y)) ∧
      k ≤ z1' ∧ k ≤ z2' ∧
      (∀x. MEM x (free_vars e1) ∧ k ≤ x ⇒ x+n < z1') ∧
      (∀x. MEM x (free_vars e2) ∧ k ≤ x ⇒ x+n < z2')
      ⇒
      syneq_exp z1' z2' V' (shift n k e1) (shift n k e2)``,
  rw[] >>
  match_mp_tac (MP_CANON (CONJUNCT1 syneq_exp_mono_V)) >>
  qabbrev_tac`R = λx y. if x < k then y = x else y = x + n` >>
  qexists_tac`(R O V) O (inv R)` >>
  conj_tac >- (
    match_mp_tac (MP_CANON (CONJUNCT1 syneq_exp_trans)) >>
    map_every qexists_tac[`z1`,`e1`] >>
    conj_tac >- (
      match_mp_tac (MP_CANON (CONJUNCT1 syneq_exp_sym_no_labs)) >>
      simp[] >>
      match_mp_tac shift_thm >>
      simp[] >>
      simp[Abbr`R`] >>
      fsrw_tac[ARITH_ss][] ) >>
    match_mp_tac (MP_CANON (CONJUNCT1 syneq_exp_trans)) >>
    first_assum (match_exists_tac o concl) >> simp[] >>
    match_mp_tac shift_thm >>
    simp[] >>
    simp[Abbr`R`] >>
    fsrw_tac[ARITH_ss][] ) >>
  fs[LET_THM,O_ASSOC])

(*
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

(* Cevaluate deterministic *)

val Cevaluate_determ = store_thm("Cevaluate_determ",
  ``(∀menv s env exp res. Cevaluate menv s env exp res ⇒ ∀res'. Cevaluate menv s env exp res' ⇒ (res' = res)) ∧
    (∀menv s env exps ress. Cevaluate_list menv s env exps ress ⇒ ∀ress'. Cevaluate_list menv s env exps ress' ⇒ (ress' = ress))``,
  ho_match_mp_tac Cevaluate_ind >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    rw[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][Once FORALL_PROD] >>
    res_tac >> fs[] ) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    rw[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][Once FORALL_PROD] >>
    res_tac >> fs[] ) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    rw[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][Once FORALL_PROD] >>
    res_tac >> fs[] ) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    rw[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][Once FORALL_PROD] >>
    TRY(Cases_on`res'`)>>
    res_tac >> fs[] ) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    rw[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][Once FORALL_PROD] >>
    res_tac >> fs[] >>
    rw[] >> fs[] ) >>
  strip_tac >- rw[] >>
  strip_tac >- rw[Once Cevaluate_cases] >>
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
    res_tac >> fs[] >>
    qpat_assum`(x,y)=z`(assume_tac o SYM) >> fs[]) >>
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
    res_tac >> fs[] >>
    qpat_assum`(x,y)=z`(assume_tac o SYM) >> fs[]) >>
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
*)

val _ = export_theory()
