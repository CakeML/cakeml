open HolKernel bossLib boolLib boolSimps lcsymtacs listTheory pairTheory pred_setTheory arithmeticTheory
open miscLib miscTheory evalPropsTheory patLangTheory intLangTheory toIntLangTheory compilerTerminationTheory intLangExtraTheory semanticPrimitivesTheory
open exhLangProofTheory patLangProofTheory free_varsTheory
val _ = new_theory "intLangProof"

val vs_to_Cvs_MAP = store_thm("vs_to_Cvs_MAP",
  ``∀vs. vs_to_Cvs vs = MAP v_to_Cv vs``,
  Induct >> simp[])
val _ = export_rewrites["vs_to_Cvs_MAP"]

val result_rel_syneq_syneq_trans =
  result_rel_trans
  |> Q.GENL[`R2`,`R1`]
  |> Q.ISPECL[`syneq`,`syneq`]
  |> UNDISCH_ALL
  |> prove_hyps_by(metis_tac[syneq_trans])

val sv_rel_syneq_refl = save_thm("sv_rel_syneq_refl",
  sv_rel_refl
  |> Q.ISPEC`syneq`
  |> SIMP_RULE std_ss [syneq_refl])
val _ = export_rewrites["sv_rel_syneq_refl"]

val sv_rel_syneq_trans =
  sv_rel_trans
  |> Q.ISPEC`syneq`
  |> UNDISCH
  |> prove_hyps_by(metis_tac[syneq_trans])

val csg_rel_syneq_trans =
  csg_rel_trans
  |> Q.ISPEC`syneq`
  |> UNDISCH_ALL
  |> prove_hyps_by(metis_tac[syneq_trans])

val EVERY2_OPTREL_syneq_trans =
  EVERY2_trans
  |> Q.GEN`R`
  |> Q.ISPEC`OPTREL syneq`
  |> UNDISCH_ALL
  |> prove_hyps_by(metis_tac[syneq_trans,OPTREL_trans])

val EVERY2_sv_rel_syneq_trans =
  EVERY2_trans
  |> Q.GEN`R`
  |> Q.ISPEC`sv_rel syneq`
  |> UNDISCH_ALL
  |> prove_hyps_by(metis_tac[sv_rel_syneq_trans])

val exc_rel_syneq_trans =
  exc_rel_trans
  |> Q.GEN`R` |> Q.ISPEC`syneq`
  |> UNDISCH_ALL
  |> prove_hyps_by(metis_tac[syneq_trans])

val no_labs_app_to_pat = store_thm("no_labs_app_to_il",
  ``∀op ls. EVERY no_labs ls ⇒ no_labs (app_to_il op ls)``,
  rw[] >>
  Cases_on`op`>>TRY(Cases_on`o'`)>>
  Cases_on`ls`>>fs[]>>
  Cases_on`t`>>fs[]>>
  TRY(Cases_on`t'`>>fs[])>>
  TRY(Cases_on`t`>>fs[])>>
  Cases_on`o''`>>fs[]>>
  BasicProvers.EVERY_CASE_TAC >> simp[])

val no_labs_exp_to_Cexp = store_thm("no_labs_exp_to_Cexp",
  ``(∀e. no_labs (exp_to_Cexp e)) ∧
    (∀es. no_labs_list (exps_to_Cexps es))``,
  ho_match_mp_tac(TypeBase.induction_of``:exp_pat``) >>
  rw[exp_to_Cexp_def,exps_to_Cexps_MAP] >>
  rw[EVERY_MAP,rich_listTheory.EVERY_REVERSE] >>
  TRY (unabbrev_all_tac >>
       fsrw_tac[DNF_ss][EVERY_MEM,MEM_MAP,FORALL_PROD] >>
       simp[UNCURRY] >> NO_TAC) >>
  metis_tac[no_labs_app_to_pat])
val _ = export_rewrites["no_labs_exp_to_Cexp"]

val no_vlabs_v_to_Cv = store_thm("no_vlabs_v_to_Cv",
  ``(∀v. no_vlabs (v_to_Cv v)) ∧
    (∀vs. no_vlabs_list (vs_to_Cvs vs))``,
  ho_match_mp_tac(TypeBase.induction_of(``:v_pat``)) >> simp[EVERY_MAP])
val _ = export_rewrites["no_vlabs_v_to_Cv"]

val v_to_Cv_closed = store_thm("v_to_Cv_closed",
  ``(∀v. closed_pat v ⇒ Cclosed (v_to_Cv v)) ∧
    (∀vs. EVERY closed_pat vs ⇒ EVERY Cclosed (vs_to_Cvs vs))``,
  ho_match_mp_tac(TypeBase.induction_of``:v_pat``) >>
  simp[] >> rw[] >-
    simp[Once Cclosed_cases] >>
  pop_assum mp_tac >>
  simp[Once closed_pat_cases] >>
  simp[Once Cclosed_cases] >- (
    simp[SUBSET_DEF,PULL_EXISTS] >>
    rw[] >> rw[] >> simp[] >> res_tac >> simp[] ) >>
  rw[MEM_MAP] >> rw[] >>
  fs[EVERY_MEM] >> res_tac >>
  fsrw_tac[ARITH_ss][])

val use_assum_tac =
  first_assum (split_pair_match o concl) >> fs[] >>
  first_assum (match_exists_tac o concl) >> simp[]

val syneq_tac =
  first_x_assum(mp_tac o MATCH_MP(CONJUNCT1 Cevaluate_syneq)) >>
  disch_then(exists_suff_gen_then mp_tac) >>
  disch_then(qspec_then`$=`(exists_suff_then mp_tac)) >>
  simp[syneq_exp_refl] >> strip_tac

fun spec_args_of_then P ttac th (g as (_,w)) =
  let
    val t = find_term (P o fst o strip_comb)  w
    val (_,args) = strip_comb t
  in
    ttac (SPECL args th)
  end g

val shift_thm =
  mkshift_thm
  |> Q.SPEC`λv. v + n`
  |> SIMP_RULE std_ss [GSYM shift_def]
  |> Q.GEN`n`

val spec_shift_then_mp_tac =
  spec_args_of_then (equal``shift``) mp_tac shift_thm

val syneq_shift_tac =
  spec_shift_then_mp_tac >>
  disch_then(qspecl_then[`LENGTH env`,`LENGTH env + 1`,`λx y. y = x+1`]mp_tac) >>
  simp[] >> strip_tac >>
  first_x_assum(mp_tac o MATCH_MP (CONJUNCT1 Cevaluate_syneq)) >>
  disch_then(exists_suff_gen_then mp_tac) >>
  simp[Once(GSYM AND_IMP_INTRO),ADD1] >>
  disch_then(fn th => first_x_assum(mp_tac o MATCH_MP th)) >>
  disch_then(exists_suff_then mp_tac) >>
  discharge_hyps >- (
    simp[rich_listTheory.EL_CONS,PRE_SUB1] ) >>
  strip_tac

val do_Ceq_correct = prove (
  ``(!v1 v2.
      (!b. (do_eq_pat v1 v2 = Eq_val b) ⇒ (do_Ceq (v_to_Cv v1) (v_to_Cv v2) = Eq_val b)) ∧
      ((do_eq_pat v1 v2 = Eq_closure) ⇒ (do_Ceq (v_to_Cv v1) (v_to_Cv v2) = Eq_closure))) ∧
    (!vs1 vs2.
      (!b. (do_eq_list_pat vs1 vs2 = Eq_val b) ⇒ (do_Ceq_list (vs_to_Cvs vs1) (vs_to_Cvs vs2) = Eq_val b)) ∧
      ((do_eq_list_pat vs1 vs2 = Eq_closure) ⇒ (do_Ceq_list (vs_to_Cvs vs1) (vs_to_Cvs vs2) = Eq_closure)))``,
  ho_match_mp_tac do_eq_pat_ind >>
  rw [do_eq_pat_def, v_to_Cv_def] >>
  rw [] >>
  Cases_on `do_eq_pat v1 v2` >> fs [] >>
  rw[]>>fs[])

fun tac w1 =
  ho_match_mp_tac syneq_ind >>
  rw [] >>
  Cases_on w1 >>
  fs [] >>
  Cases_on `n = cn` >>
  fs [] >>
  rpt (pop_assum mp_tac) >>
  Q.SPEC_TAC (`vs1`, `vs1`) >>
  Q.SPEC_TAC (`vs2`, `vs2`) >>
  Induct_on `l` >>
  rw [] >>
  Cases_on `vs2` >>
  fs [] >>
  rw [] >>
  fs [] >>
  TRY(fs[EVERY2_EVERY]>>NO_TAC)>>
  BasicProvers.CASE_TAC >>
  fs [] >>
  Cases_on `b` >>
  fs [] >>
  metis_tac[]

val do_Ceq_syneq1 = prove(
  ``!w1 w2. syneq w1 w2  ⇒ ∀w3. do_Ceq w1 w3 = do_Ceq w2 w3``,
  tac `w3`)

val do_Ceq_syneq2 = prove(
  ``!w2 w3. syneq w2 w3  ⇒ ∀w1. do_Ceq w1 w2 = do_Ceq w1 w3``,
  tac `w1`)

fun first_disj tac g =
  (tac ORELSE disj1_tac >> tac) g
  handle HOL_ERR _ => (disj2_tac >> first_disj tac) g

val app_to_il_err = prove(
  ``∀ls op s env res err.
      set (free_vars_list ls) ⊆ count (LENGTH env) ∧
      no_labs_list ls ∧
      Cevaluate_list s env ls res ∧
      SND res = Rerr err ⇒
      ∃s2 err2.
      Cevaluate s env (app_to_il op ls) (s2,Rerr err2) ∧
      csg_rel syneq (FST res) s2 ∧
      exc_rel syneq err err2
      ``,
  Cases >- ( rw[Once Cevaluate_cases] >> fs[] ) >>
  Cases_on`t`>- (
    rw[Once Cevaluate_cases,PULL_EXISTS] >> fs[] >>
    TRY(fs[Once (CONJUNCT2 Cevaluate_cases)] >> NO_TAC) >> rw[] >>
    Cases_on`op`>>rw[]>>
    TRY (
      srw_tac[DNF_ss][Once Cevaluate_cases] >>
      disj2_tac >>
      first_assum(match_exists_tac o concl) >> rw[] >>
      NO_TAC) >>
    Cases_on`o'`>>rw[]>>
    TRY (
      srw_tac[DNF_ss][Once Cevaluate_cases] >>
      disj2_tac >>
      first_assum(match_exists_tac o concl) >> rw[] >>
      NO_TAC) >>
    Cases_on`o''`>>rw[]>>
    TRY(first_assum(match_exists_tac o concl)) >> rw[] >>
    srw_tac[DNF_ss][Once Cevaluate_cases]>>
    TRY disj2_tac >>
    first_assum(match_exists_tac o concl) >> rw[]) >>
  Cases_on`t'` >- (
    rw[Once Cevaluate_cases,PULL_EXISTS] >> fs[] >> rw[] >>
    fs[Once (CONJUNCT2 Cevaluate_cases)] >>
    fs[Once (CONJUNCT2 Cevaluate_cases)] >>
    Cases_on`op`>>rw[]>>
    TRY(Q.PAT_ABBREV_TAC`X = CCon Y Z` >> unabbrev_all_tac >>
        rw[Once Cevaluate_cases] >> rw[Once Cevaluate_cases] >>
        rw[Once (CONJUNCT2 Cevaluate_cases)] >>
        rw[Once (CONJUNCT2 Cevaluate_cases)] >>
        srw_tac[DNF_ss][] >>
        TRY(
          disj1_tac >> first_assum(match_exists_tac o concl) >> rw[] ) >>
        disj2_tac >> first_assum(match_exists_tac o concl) >> rw[] >>
        first_assum(match_exists_tac o concl) >> rw[]) >>
    Cases_on`o'`>>rw[]>>
    TRY(Q.PAT_ABBREV_TAC`X = CCon Y Z` >> unabbrev_all_tac >>
        rw[Once Cevaluate_cases] >> rw[Once Cevaluate_cases] >>
        rw[Once (CONJUNCT2 Cevaluate_cases)] >>
        rw[Once (CONJUNCT2 Cevaluate_cases)] >>
        srw_tac[DNF_ss][] >>
        TRY(
          disj1_tac >> first_assum(match_exists_tac o concl) >> rw[] ) >>
        disj2_tac >> first_assum(match_exists_tac o concl) >> rw[] >>
        first_assum(match_exists_tac o concl) >> rw[]) >>
    Cases_on`o''`>>rw[]>>
    TRY(Q.PAT_ABBREV_TAC`X = CCon Y Z` >> unabbrev_all_tac >>
        rw[Once Cevaluate_cases] >> rw[Once Cevaluate_cases] >>
        rw[Once (CONJUNCT2 Cevaluate_cases)] >>
        rw[Once (CONJUNCT2 Cevaluate_cases)] >>
        srw_tac[DNF_ss][] >>
        TRY(
          disj1_tac >> first_assum(match_exists_tac o concl) >> rw[] ) >>
        disj2_tac >> first_assum(match_exists_tac o concl) >> rw[] >>
        first_assum(match_exists_tac o concl) >> rw[]) >>
    BasicProvers.EVERY_CASE_TAC >>
    rw[Once Cevaluate_cases] >>
    rpt(CHANGED_TAC(rw[Once (CONJUNCT2 Cevaluate_cases)])) >>
    srw_tac[DNF_ss][]
    >-(first_disj(first_assum(match_exists_tac o concl)) >> rw[])
    >-(first_disj(first_assum(match_exists_tac o concl)) >> rw[])
    >-(first_disj(first_assum(match_exists_tac o concl)) >> rw[])
    >-(first_disj(first_assum(match_exists_tac o concl)) >> rw[])
    >- (
      disj2_tac >>
      rw[Once Cevaluate_cases] >>
      rpt(CHANGED_TAC(rw[Once (CONJUNCT2 Cevaluate_cases)])) >>
      srw_tac[DNF_ss][] >>
      first_disj(first_assum(match_exists_tac o concl)) >> rw[])
    >-(first_disj(first_assum(match_exists_tac o concl)) >> rw[])
    >- (disj2_tac >>
      rw[Once Cevaluate_cases] >>
      rpt(CHANGED_TAC(rw[Once (CONJUNCT2 Cevaluate_cases)])) >>
      srw_tac[DNF_ss][] >>
      first_disj(first_assum(match_exists_tac o concl)) >> rw[])
    >-(first_disj(first_assum(match_exists_tac o concl)) >> rw[])
    >-(first_disj(first_assum(match_exists_tac o concl)) >> rw[])
    >-(first_disj(first_assum(match_exists_tac o concl)) >> rw[] >>
       first_assum(match_exists_tac o concl) >> rw[])
    >-(first_disj(first_assum(match_exists_tac o concl)) >> rw[] >>
       srw_tac[DNF_ss][Once Cevaluate_cases] >> disj2_tac >>
       syneq_shift_tac >>
       use_assum_tac)
    >-(first_disj(first_assum(match_exists_tac o concl)) >> rw[] >>
       first_assum(match_exists_tac o concl) >> rw[])
    >-(first_disj(first_assum(match_exists_tac o concl)) >> rw[] >>
       srw_tac[DNF_ss][Once Cevaluate_cases] >> disj2_tac >>
       syneq_shift_tac >>
       use_assum_tac)
    >- (disj2_tac >>
      rw[Once Cevaluate_cases] >>
      rpt(CHANGED_TAC(rw[Once (CONJUNCT2 Cevaluate_cases)])) >>
      srw_tac[DNF_ss][] >>
      first_disj(first_assum(match_exists_tac o concl)) >> rw[] >>
      first_disj(first_assum(match_exists_tac o concl)) >> rw[] )
    >-(first_disj(first_assum(match_exists_tac o concl)) >> rw[] >>
       srw_tac[DNF_ss][Once Cevaluate_cases] >> disj2_tac >>
       syneq_shift_tac >>
       use_assum_tac)
    >- (disj2_tac >>
      rw[Once Cevaluate_cases] >>
      rpt(CHANGED_TAC(rw[Once (CONJUNCT2 Cevaluate_cases)])) >>
      srw_tac[DNF_ss][] >>
      first_disj(first_assum(match_exists_tac o concl)) >> rw[] >>
      first_disj(first_assum(match_exists_tac o concl)) >> rw[] )
    >-(first_disj(first_assum(match_exists_tac o concl)) >> rw[] >>
       first_disj(first_assum(match_exists_tac o concl)) >> rw[])
    >-(disj2_tac >>
       first_disj(first_assum(match_exists_tac o concl)) >> rw[] >>
       first_disj(first_assum(match_exists_tac o concl)) >> rw[])
    >-(first_disj(first_assum(match_exists_tac o concl)) >> rw[] >>
       rw[Once Cevaluate_cases] >>
       rpt(CHANGED_TAC(rw[Once (CONJUNCT2 Cevaluate_cases)])) >>
       srw_tac[DNF_ss][] >> disj2_tac >>
       syneq_shift_tac >>
       use_assum_tac)
    >-(first_disj(first_assum(match_exists_tac o concl)) >> rw[] >>
       rw[Once Cevaluate_cases] >>
       rpt(CHANGED_TAC(rw[Once (CONJUNCT2 Cevaluate_cases)])) >>
       srw_tac[DNF_ss][] >> disj2_tac >>
       syneq_shift_tac >> use_assum_tac)
    >-(first_disj(first_assum(match_exists_tac o concl)) >> rw[] >>
       rw[Once Cevaluate_cases] >>
       rpt(CHANGED_TAC(rw[Once (CONJUNCT2 Cevaluate_cases)])) >>
       srw_tac[DNF_ss][] >> disj2_tac >>
       syneq_shift_tac >> use_assum_tac)
    >-(first_disj(first_assum(match_exists_tac o concl)) >> rw[] >>
       rw[Once Cevaluate_cases] >>
       rpt(CHANGED_TAC(rw[Once (CONJUNCT2 Cevaluate_cases)])) >>
       srw_tac[DNF_ss][] >> disj2_tac >>
       syneq_shift_tac >> use_assum_tac)
    >-(first_disj(first_assum(match_exists_tac o concl)) >> rw[] >>
       rw[Once Cevaluate_cases] >>
       rpt(CHANGED_TAC(rw[Once (CONJUNCT2 Cevaluate_cases)])) >>
       srw_tac[DNF_ss][] >> disj2_tac >>
       syneq_shift_tac >> use_assum_tac)) >>
  Cases_on`t`>- (
    rw[Once Cevaluate_cases,PULL_EXISTS] >> fs[] >> rw[] >>
    fs[Once (CONJUNCT2 Cevaluate_cases)] >>
    fs[Once (CONJUNCT2 Cevaluate_cases)] >>
    fs[Once (CONJUNCT2 Cevaluate_cases)] >>
    Cases_on`op`>>simp[]>>
    TRY(Q.PAT_ABBREV_TAC`X = CCon Y Z` >> unabbrev_all_tac >>
        rw[Once Cevaluate_cases] >> rw[Once Cevaluate_cases] >>
        rw[Once (CONJUNCT2 Cevaluate_cases)] >>
        rw[Once (CONJUNCT2 Cevaluate_cases)] >>
        rw[Once (CONJUNCT2 Cevaluate_cases)] >>
        srw_tac[DNF_ss][] >>
        TRY(first_disj(first_assum(match_exists_tac o concl))>>rw[]>>NO_TAC) >>
        TRY(first_disj(first_assum(match_exists_tac o concl))>>rw[]>>
            first_disj(first_assum(match_exists_tac o concl))>>rw[]>>NO_TAC) >>
        rpt disj2_tac >>
        first_disj(first_assum(match_exists_tac o concl))>>rw[]>>
        first_disj(first_assum(match_exists_tac o concl))>>rw[]>>
        first_disj(first_assum(match_exists_tac o concl))>>rw[]) >>
    Cases_on`o'`>>simp[]>>
    TRY(Q.PAT_ABBREV_TAC`X = CCon Y Z` >> unabbrev_all_tac >>
        rw[Once Cevaluate_cases] >> rw[Once Cevaluate_cases] >>
        rw[Once (CONJUNCT2 Cevaluate_cases)] >>
        rw[Once (CONJUNCT2 Cevaluate_cases)] >>
        rw[Once (CONJUNCT2 Cevaluate_cases)] >>
        srw_tac[DNF_ss][] >>
        TRY(first_disj(first_assum(match_exists_tac o concl))>>rw[]>>NO_TAC) >>
        TRY(first_disj(first_assum(match_exists_tac o concl))>>rw[]>>
            first_disj(first_assum(match_exists_tac o concl))>>rw[]>>NO_TAC) >>
        rpt disj2_tac >>
        first_disj(first_assum(match_exists_tac o concl))>>rw[]>>
        first_disj(first_assum(match_exists_tac o concl))>>rw[]>>
        first_disj(first_assum(match_exists_tac o concl))>>rw[]) >>
    Cases_on`o''`>>simp[]>>
    TRY(Q.PAT_ABBREV_TAC`X = CCon Y Z` >> unabbrev_all_tac >>
        rw[Once Cevaluate_cases] >> rw[Once Cevaluate_cases] >>
        rw[Once (CONJUNCT2 Cevaluate_cases)] >>
        rw[Once (CONJUNCT2 Cevaluate_cases)] >>
        rw[Once (CONJUNCT2 Cevaluate_cases)] >>
        srw_tac[DNF_ss][] >>
        TRY(first_disj(first_assum(match_exists_tac o concl))>>rw[]>>NO_TAC) >>
        TRY(first_disj(first_assum(match_exists_tac o concl))>>rw[]>>
            first_disj(first_assum(match_exists_tac o concl))>>rw[]>>NO_TAC) >>
        rpt disj2_tac >>
        first_disj(first_assum(match_exists_tac o concl))>>rw[]>>
        first_disj(first_assum(match_exists_tac o concl))>>rw[]>>
        first_disj(first_assum(match_exists_tac o concl))>>rw[]) >>
    srw_tac[DNF_ss][Once Cevaluate_cases] >>
    first_disj(first_assum(match_exists_tac o concl))>>rw[]>>
    srw_tac[DNF_ss][Once Cevaluate_cases] >>
    TRY(disj2_tac >> syneq_shift_tac >> use_assum_tac) >>
    disj1_tac >>
    pop_assum(assume_tac o EQT_INTRO) >>
    syneq_shift_tac >>
    use_assum_tac >>
    srw_tac[DNF_ss][Once Cevaluate_cases] >> disj2_tac >>
    spec_shift_then_mp_tac >>
    disch_then(qspecl_then[`LENGTH env`,`LENGTH env + 2`,`λx y. y = x+2`]mp_tac) >>
    simp[] >> strip_tac >>
    rator_x_assum`Cevaluate`(assume_tac o EQT_INTRO) >>
    first_x_assum(mp_tac o MATCH_MP (CONJUNCT1 Cevaluate_syneq)) >>
    disch_then(exists_suff_gen_then mp_tac) >>
    simp[Once(GSYM AND_IMP_INTRO),ADD1] >>
    disch_then(fn th => first_x_assum(mp_tac o MATCH_MP th)) >>
    disch_then(exists_suff_then mp_tac) >>
    (discharge_hyps >- (
       simp[rich_listTheory.EL_CONS,PRE_SUB1] )) >>
    strip_tac >>
    use_assum_tac ) >>
  Cases >> rw[] >>
  TRY(Q.PAT_ABBREV_TAC`X = CCon Y Z` >> unabbrev_all_tac >>
      rw[Once Cevaluate_cases] >>
      use_assum_tac) >>
  Cases_on`o'`>>rw[]>>
  TRY(Q.PAT_ABBREV_TAC`X = CCon Y Z` >> unabbrev_all_tac >>
      rw[Once Cevaluate_cases] >>
      use_assum_tac) >>
  Cases_on`o''`>>rw[]>>
  Q.PAT_ABBREV_TAC`X = CCon Y Z` >> unabbrev_all_tac >>
  rw[Once Cevaluate_cases] >>
  use_assum_tac)

val CvFromList_correct = prove(
  ``∀v ls. v_to_list_pat v = SOME ls ⇒
           CvFromList (v_to_Cv v) = SOME (vs_to_Cvs ls)``,
  ho_match_mp_tac v_to_list_pat_ind >>
  simp[v_to_list_pat_def,CvFromList_def] >>
  rw[] >> BasicProvers.EVERY_CASE_TAC >> fs[] >> rw[])

val CvFromList_syneq = prove(
  ``∀v1 v2. syneq v1 v2 ⇒ OPTREL (LIST_REL syneq) (CvFromList v1) (CvFromList v2)``,
  ho_match_mp_tac CvFromList_ind >>
  rw[CvFromList_def] >>
  TRY(fs[Once syneq_cases,CvFromList_def]>>NO_TAC)>>
  fs[Q.SPEC`CConv X Y`syneq_cases] >> rw[] >>
  rw[CvFromList_def] >>
  first_x_assum(fn th => first_x_assum(strip_assume_tac o MATCH_MP th)) >>
  BasicProvers.CASE_TAC >> fs[optionTheory.OPTREL_def])

val exp_to_Cexp_correct = store_thm("exp_to_Cexp_correct",
  ``(∀ck env s e res. evaluate_pat ck env s e res ⇒
       ck ∧
       set (free_vars_pat e) ⊆ count (LENGTH env) ∧
       EVERY closed_pat env ∧ csg_closed_pat s ∧
       SND res ≠ Rerr Rtype_error ⇒
       ∃Cres.
       Cevaluate (map_count_store_genv v_to_Cv s) (vs_to_Cvs env) (exp_to_Cexp e) Cres ∧
       csg_rel syneq (map_count_store_genv v_to_Cv (FST res)) (FST Cres) ∧
       result_rel syneq syneq (map_result v_to_Cv v_to_Cv (SND res)) (SND Cres)) ∧
    (∀ck env s es res. evaluate_list_pat ck env s es res ⇒
       ck ∧
       set (free_vars_list_pat es) ⊆ count (LENGTH env) ∧
       EVERY closed_pat env ∧ csg_closed_pat s ∧
       SND res ≠ Rerr Rtype_error ⇒
       ∃Cres.
       Cevaluate_list (map_count_store_genv v_to_Cv s) (vs_to_Cvs env) (exps_to_Cexps es) Cres ∧
       csg_rel syneq (map_count_store_genv v_to_Cv (FST res)) (FST Cres) ∧
       result_rel (LIST_REL syneq) syneq (map_result vs_to_Cvs v_to_Cv (SND res)) (SND Cres))``,
  ho_match_mp_tac evaluate_pat_strongind >>
  strip_tac >- rw[Once Cevaluate_cases] >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    rw[Once Cevaluate_cases] >> fs[] >>
    srw_tac[DNF_ss][] >> disj1_tac >>
    first_assum (split_pair_match o concl) >> fs[] >>
    first_assum (match_exists_tac o concl) >> simp[]) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    rw[Once Cevaluate_cases] >> fs[] >>
    srw_tac[DNF_ss][] >> disj2_tac >>
    first_assum (split_pair_match o concl) >> fs[] >>
    first_assum (match_exists_tac o concl) >> simp[]) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    rw[Once Cevaluate_cases] >> fs[] >>
    srw_tac[DNF_ss][] >> disj1_tac >>
    first_assum (split_pair_match o concl) >> fs[] >>
    first_assum (match_exists_tac o concl) >> simp[]) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    rw[Once Cevaluate_cases] >> fs[] >>
    srw_tac[DNF_ss][] >> disj2_tac >> disj1_tac >>
    first_assum (split_pair_match o concl) >> fs[] >>
    first_assum (match_exists_tac o concl) >> simp[] >>
    qpat_assum`p ⇒ q`mp_tac >>
    discharge_hyps >- (
      conj_asm1_tac >- (
        fsrw_tac[ARITH_ss][SUBSET_DEF,ADD1,PULL_EXISTS] >>
        Cases >> simp[] ) >>
      imp_res_tac evaluate_pat_closed >> fs[]) >>
    strip_tac >>
    first_assum (mp_tac o MATCH_MP (CONJUNCT1 Cevaluate_syneq)) >>
    disch_then (exists_suff_gen_then mp_tac) >>
    disch_then (qspec_then`$=`mp_tac o CONV_RULE(SWAP_FORALL_CONV)) >>
    disch_then (exists_suff_then mp_tac) >>
    discharge_hyps >- ( simp[syneq_exp_refl] >> Cases >> simp[] ) >>
    metis_tac[result_rel_syneq_syneq_trans,csg_rel_syneq_trans]) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    rw[Once Cevaluate_cases] >> fs[] >>
    srw_tac[DNF_ss][] >> disj2_tac >>
    first_assum (split_pair_match o concl) >> fs[] >>
    metis_tac[]) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    rw[Once Cevaluate_cases] >>
    fs[] >> srw_tac[DNF_ss][] >>
    first_assum (split_pair_match o concl) >> fs[] >>
    simp[Once syneq_cases] >>
    metis_tac[]) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    rw[Once Cevaluate_cases] >> fs[] >>
    srw_tac[DNF_ss][] >>
    first_assum (split_pair_match o concl) >> fs[] >>
    metis_tac[]) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    simp[Once Cevaluate_cases,EL_MAP] ) >>
  strip_tac >- rw[Once Cevaluate_cases] >>
  strip_tac >- (
    simp[FORALL_PROD] >>
    rpt gen_tac >> strip_tac >>
    simp[Once Cevaluate_cases,PULL_EXISTS,EXISTS_PROD
        ,map_count_store_genv_def,EL_MAP]) >>
  strip_tac >- rw[Once Cevaluate_cases] >>
  strip_tac >- rw[Once Cevaluate_cases] >>
  strip_tac >- ( rw[Once Cevaluate_cases] >> simp[] ) >>
  strip_tac >- (
    simp[] >>
    rpt gen_tac >> rpt strip_tac >>
    fs[do_opapp_pat_def] >>
    Cases_on`vs`>>fs[]>>Cases_on`t`>>fs[]>>Cases_on`t'`>>fs[]>>rw[]>>
    Cases_on`es`>>fs[Once(CONJUNCT2 evaluate_pat_cases)]>>
    Cases_on`t`>>fs[Once(CONJUNCT2 evaluate_pat_cases)]>>
    Cases_on`t'`>>fs[Once(CONJUNCT2 evaluate_pat_cases)]>> rw[] >>
    simp[Once Cevaluate_cases] >>
    srw_tac[DNF_ss][] >> disj1_tac >>
    simp[Once(CONJUNCT2 Cevaluate_cases),PULL_EXISTS] >>
    simp[Once(CONJUNCT2 Cevaluate_cases),PULL_EXISTS] >>
    rator_x_assum`Cevaluate_list`mp_tac >>
    PairCases_on`Cres` >>
    simp[Once(CONJUNCT2 Cevaluate_cases),PULL_EXISTS] >> fs[] >>
    simp[Once(CONJUNCT2 Cevaluate_cases),PULL_EXISTS] >>
    simp[Once(CONJUNCT2 Cevaluate_cases),PULL_EXISTS] >> rw[] >>
    last_x_assum(mp_tac o MATCH_MP (CONJUNCT1 evaluate_pat_closed)) >> simp[] >> strip_tac >>
    last_x_assum(mp_tac o MATCH_MP (CONJUNCT1 evaluate_pat_closed)) >> simp[] >> strip_tac >>
    Cases_on`h`>>fs[LET_THM]>>rw[]>>
    qpat_assum`syneq (A X Y) Z`mp_tac >>
    simp[Once syneq_cases] >> rw[] >>
    qpat_assum`closed_pat (X Y)`mp_tac >>
    simp[Once closed_pat_cases] >> strip_tac >>
    use_assum_tac >>
    use_assum_tac >>
    qpat_assum`p ⇒ q`mp_tac >>
    (discharge_hyps >- (
      fsrw_tac[ARITH_ss][ADD1,csg_closed_pat_def,build_rec_env_pat_def,EVERY_GENLIST] >>
      fs[EVERY_MEM,MEM_EL,PULL_EXISTS] >>
      simp[Once closed_pat_cases,EVERY_MEM,MEM_EL,PULL_EXISTS])) >>
    strip_tac >>
    imp_res_tac csg_rel_count >>
    fsrw_tac[ARITH_ss][] >>
    simp[Once map_count_store_genv_def] >>
    simp[Once map_count_store_genv_def] >>
    last_x_assum (mp_tac o MATCH_MP (CONJUNCT1 Cevaluate_no_vlabs)) >>
    (discharge_hyps >- (
      simp[EVERY_MAP,no_vlabs_csg_def,store_vs_def,map_count_store_genv_def,EVERY_FILTER] >>
      simp[EVERY_MEM,MEM_FLAT,MEM_MAP,PULL_EXISTS] >> conj_tac >> TRY(CONV_TAC SWAP_FORALL_CONV) >>
      Cases >> simp[] >> simp[MEM_MAP,PULL_EXISTS] )) >>
    simp[Ntimes EVERY_MEM 2, Ntimes MEM_EL 2, PULL_EXISTS] >> strip_tac >>
    first_x_assum(qspec_then`d2`mp_tac) >>
    ntac 3 BasicProvers.CASE_TAC >> simp[] >> strip_tac >>
    rator_assum`syneq_defs`mp_tac >>
    simp_tac(srw_ss())[Once syneq_exp_cases] >>
    disch_then(fn th => first_assum(mp_tac o MATCH_MP th)) >> simp[] >>
    simp[syneq_cb_aux_def,EL_MAP] >> strip_tac >>
    BasicProvers.VAR_EQ_TAC >>
    rator_x_assum`syneq_exp`mp_tac >|[
      qmatch_abbrev_tac`syneq_exp z1 z2 U (shift 1 1 e3) e4 ⇒ Z` >>
      spec_shift_then_mp_tac >>
      disch_then(qspecl_then[`z1-1`,`z1`,`λx y. if x = 0 then y = 0 else y = x+1`]mp_tac) >>
      discharge_hyps >- (
        simp[Abbr`z1`,Abbr`e3`] >>
        qpat_assum`closed_pat (Closure_pat X Y)`mp_tac >>
        simp[Once closed_pat_cases] ) >>
      disch_then(mp_tac o (MATCH_MP (CONJUNCT1 syneq_exp_trans))) >>
      disch_then(qspecl_then[`z2`,`U`,`e4`]mp_tac) >>
      disch_then(fn th => disch_then(mp_tac o MATCH_MP th)) >>
      map_every qunabbrev_tac[`z1`,`z2`,`U`,`e3`,`e4`,`Z`],
      ALL_TAC] >>
    simp[] >> strip_tac >>
    first_x_assum(mp_tac o MATCH_MP (CONJUNCT1 Cevaluate_syneq)) >>
    disch_then(exists_suff_gen_then mp_tac) >>
    simp[ADD1,Once (GSYM AND_IMP_INTRO),build_rec_env_pat_def] >>
    disch_then(fn th => first_x_assum (mp_tac o MATCH_MP th)) >>
    disch_then(exists_suff_then mp_tac) >|[
      discharge_hyps >- (
        reverse conj_tac >- (
          fs[map_count_store_genv_def] >>
          qmatch_assum_rename_tac`csg_rel syneq (X,MAP f genv3) (FST Y)`["X","f"] >>
          PairCases_on`Y`>>fs[csg_rel_def] >>
          metis_tac[EVERY2_syneq_trans,EVERY2_OPTREL_syneq_trans] ) >>
        simp[relationTheory.O_DEF,PULL_EXISTS,syneq_cb_V_def] >>
        Cases >> Cases >> simp[ADD1] >>
        rw[] >>
        simp[rich_listTheory.EL_APPEND2] )
      ,
      discharge_hyps >- (
        reverse conj_tac >- (
          fs[map_count_store_genv_def] >>
          qmatch_assum_rename_tac`csg_rel syneq (X,MAP f genv3) (FST Y)`["X","f"] >>
          PairCases_on`Y`>>fs[csg_rel_def] >>
          metis_tac[EVERY2_syneq_trans,EVERY2_OPTREL_syneq_trans] ) >>
        simp[PULL_EXISTS,syneq_cb_V_def] >>
        Cases >> Cases >> simp[ADD1] >>
        rw[] >> simp[rich_listTheory.EL_APPEND1,rich_listTheory.EL_APPEND2] >>
        simp[EL_MAP] >>
        simp[Once syneq_cases] >>
        metis_tac[])
      ] >>
    metis_tac[result_rel_syneq_syneq_trans,csg_rel_syneq_trans]) >>
  strip_tac >- (
    simp[] >>
    rpt gen_tac >> rpt strip_tac >>
    fs[do_opapp_pat_def] >>
    Cases_on`vs`>>fs[]>>Cases_on`t`>>fs[]>>Cases_on`t'`>>fs[]>>rw[]>>
    Cases_on`es`>>fs[Once(CONJUNCT2 evaluate_pat_cases)]>>
    Cases_on`t`>>fs[Once(CONJUNCT2 evaluate_pat_cases)]>>
    Cases_on`t'`>>fs[Once(CONJUNCT2 evaluate_pat_cases)]>> rw[] >>
    simp[Once Cevaluate_cases] >>
    srw_tac[DNF_ss][] >> fs[] >>
    disj2_tac >> disj1_tac >>
    rator_x_assum`Cevaluate_list`mp_tac >>
    PairCases_on`Cres` >> fs[] >>
    simp[Once(CONJUNCT2 Cevaluate_cases),PULL_EXISTS] >>
    simp[Once(CONJUNCT2 Cevaluate_cases),PULL_EXISTS] >>
    simp[Once(CONJUNCT2 Cevaluate_cases),PULL_EXISTS] >>
    simp[Once(CONJUNCT2 Cevaluate_cases),PULL_EXISTS] >>
    simp[Once(CONJUNCT2 Cevaluate_cases),PULL_EXISTS] >>
    gen_tac >> strip_tac >>
    Cases_on`h`>>fs[LET_THM]>>rw[]>>
    qpat_assum`syneq (A X Y) Z`mp_tac >>
    simp[Once syneq_cases] >> rw[] >>
    use_assum_tac >>
    imp_res_tac csg_rel_count >>
    fs[map_count_store_genv_def] >>
    use_assum_tac ) >>
  strip_tac >- simp[] >>
  strip_tac >- (
    rw[] >> fs[] >>
    first_x_assum(mp_tac o MATCH_MP (CONJUNCT2 evaluate_pat_closed)) >>
    simp[] >> strip_tac >>
    PairCases_on`s2` >>
    PairCases_on`Cres`>>
    imp_res_tac do_app_pat_cases >> fs[do_app_pat_def] >> rw[] >> fs[] >> rw[] >>
    rator_x_assum`Cevaluate_list`mp_tac >>
    Cases_on`es`>>simp[Once (CONJUNCT2 Cevaluate_cases)]>>
    TRY(Cases_on`t:exp_pat list`)>>simp[Once (CONJUNCT2 Cevaluate_cases),PULL_EXISTS]>>
    TRY(Cases_on`t':exp_pat list` >> simp[Once (CONJUNCT2 Cevaluate_cases),PULL_EXISTS]) >>
    rw[] (* opn *) >- (
      BasicProvers.CASE_TAC >- (
        simp[Once Cevaluate_cases] >>
        srw_tac[DNF_ss][Once(CONJUNCT2 Cevaluate_cases)] >>
        srw_tac[DNF_ss][Once(CONJUNCT2 Cevaluate_cases)] >>
        srw_tac[DNF_ss][Once(CONJUNCT2 Cevaluate_cases)] >>
        disj1_tac >>
        use_assum_tac >>
        syneq_tac >>
        use_assum_tac >>
        qmatch_assum_rename_tac`opn_to_prim2 op = X`["X"] >>
        Cases_on`op`>> fs[opn_to_prim2_def] >>
        rpt BasicProvers.VAR_EQ_TAC >> simp[] >> fs[opn_lookup_def] >>
        metis_tac[csg_rel_syneq_trans] ) >>
      simp[Once Cevaluate_cases] >>
      srw_tac[DNF_ss][] >> disj1_tac >>
      use_assum_tac >>
      simp[Once Cevaluate_cases] >>
      srw_tac[DNF_ss][] >> disj1_tac >>
      syneq_shift_tac >>
      use_assum_tac >>
      simp[Once Cevaluate_cases] >>
      srw_tac[DNF_ss][] >> disj1_tac >>
      simp[Once Cevaluate_cases] >>
      srw_tac[DNF_ss][Once(CONJUNCT2 Cevaluate_cases)] >>
      simp_tac(srw_ss()++DNF_ss)[Once(CONJUNCT2 Cevaluate_cases)] >>
      simp_tac(srw_ss()++DNF_ss)[Once(CONJUNCT2 Cevaluate_cases)] >>
      qmatch_assum_rename_tac`opn_to_prim2 op = X`["X"] >>
      simp[lit_same_type_def] >>
      Cases_on`op`>>fs[opn_to_prim2_def] >>
      rpt BasicProvers.VAR_EQ_TAC >> simp[] >> fs[opn_lookup_def] >>
      rw[] >> fs[prim_exn_pat_def] >> TRY (
        srw_tac[DNF_ss][Once Cevaluate_cases] >>
        disj1_tac >>
        srw_tac[DNF_ss][Once Cevaluate_cases] >>
        srw_tac[DNF_ss][Once Cevaluate_cases] >>
        metis_tac[csg_rel_syneq_trans] ) >>
      simp[Once Cevaluate_cases] >>
      srw_tac[DNF_ss,ARITH_ss][Once(CONJUNCT2 Cevaluate_cases),ADD1] >>
      srw_tac[DNF_ss][Once(CONJUNCT2 Cevaluate_cases)] >>
      srw_tac[DNF_ss][Once(CONJUNCT2 Cevaluate_cases)] >>
      metis_tac[csg_rel_syneq_trans] )
    >- (* opb *)(
      BasicProvers.CASE_TAC >>
      simp[Once Cevaluate_cases] >>
      srw_tac[DNF_ss][] >>
      TRY (
        srw_tac[DNF_ss][Once(CONJUNCT2 Cevaluate_cases)] >>
        srw_tac[DNF_ss][Once(CONJUNCT2 Cevaluate_cases)] >>
        srw_tac[DNF_ss][Once(CONJUNCT2 Cevaluate_cases)] >>
        (use_assum_tac ORELSE (
          simp[Once Cevaluate_cases] >>
          srw_tac[DNF_ss][Once(CONJUNCT2 Cevaluate_cases)] >>
          srw_tac[DNF_ss][Once(CONJUNCT2 Cevaluate_cases)] >>
          srw_tac[DNF_ss][Once(CONJUNCT2 Cevaluate_cases)] >>
          REWRITE_TAC[Once CONJ_COMM] >>
          use_assum_tac )) >>
        syneq_tac >>
        use_assum_tac >>
        rpt BasicProvers.VAR_EQ_TAC >> fs[opb_lookup_def] >>
        TRY (
          conj_tac >- metis_tac[csg_rel_syneq_trans] >>
          intLib.COOPER_TAC ) >>
        metis_tac[csg_rel_syneq_trans] ) >>
      use_assum_tac >>
      simp[Once Cevaluate_cases] >>
      srw_tac[DNF_ss][] >>
      syneq_shift_tac >>
      use_assum_tac >>
      simp[Once Cevaluate_cases] >>
      srw_tac[DNF_ss][Once(CONJUNCT2 Cevaluate_cases)] >>
      srw_tac[DNF_ss][Once(CONJUNCT2 Cevaluate_cases)] >>
      simp_tac(srw_ss()++DNF_ss)[Once(CONJUNCT2 Cevaluate_cases)] >>
      fsrw_tac[ARITH_ss][opb_lookup_def] >>
      TRY (
        simp[Once Cevaluate_cases] >>
        srw_tac[DNF_ss][Once(CONJUNCT2 Cevaluate_cases)] >>
        srw_tac[DNF_ss][Once(CONJUNCT2 Cevaluate_cases)] >>
        simp[Once(CONJUNCT2 Cevaluate_cases)] >>
        conj_tac >- metis_tac[csg_rel_syneq_trans] >>
        intLib.COOPER_TAC ) >>
      metis_tac[csg_rel_syneq_trans,integerTheory.int_gt] )
    >- (* eq *)(
      simp[Once Cevaluate_cases] >>
      srw_tac[DNF_ss][] >>
      simp[Once Cevaluate_cases] >>
      srw_tac[DNF_ss][Once(CONJUNCT2 Cevaluate_cases)] >>
      srw_tac[DNF_ss][Once(CONJUNCT2 Cevaluate_cases)] >>
      srw_tac[DNF_ss][Once(CONJUNCT2 Cevaluate_cases)] >>
      REWRITE_TAC[Once CONJ_COMM] >> disj1_tac >>
      use_assum_tac >>
      syneq_tac >>
      use_assum_tac >>
      simp[Once Cevaluate_cases] >>
      srw_tac[DNF_ss][] >> disj1_tac >>
      simp[Once Cevaluate_cases] >>
      srw_tac[DNF_ss][] >>
      Q.PAT_ABBREV_TAC`Ce = do_Ceq X Y` >>
      Cases_on`do_eq_pat v1 v2`>>fs[]>>
      `Ce = do_eq_pat v1 v2` by (
        metis_tac[do_Ceq_correct,do_Ceq_syneq1,do_Ceq_syneq2] ) >>
      simp[] >>
      rpt BasicProvers.VAR_EQ_TAC >>
      simp[Once Cevaluate_cases,PULL_EXISTS,prim_exn_pat_def] >>
      simp[Once Cevaluate_cases] >>
      simp[Once Cevaluate_cases] >>
      simp[Once Cevaluate_cases] >>
      simp[Once Cevaluate_cases] >>
      metis_tac[csg_rel_syneq_trans,result_rel_syneq_syneq_trans])
    >- (* Up1 *) (
      simp[Once Cevaluate_cases] >>
      srw_tac[DNF_ss][] >>
      srw_tac[DNF_ss][Once(CONJUNCT2 Cevaluate_cases)] >>
      srw_tac[DNF_ss][Once(CONJUNCT2 Cevaluate_cases)] >>
      srw_tac[DNF_ss][Once(CONJUNCT2 Cevaluate_cases)] >>
      disj1_tac >>
      use_assum_tac >>
      syneq_tac >>
      use_assum_tac >>
      simp[Once Cevaluate_cases] >>
      fs[semanticPrimitivesTheory.store_assign_def] >>
      fs[csg_rel_def,map_count_store_genv_def] >>
      imp_res_tac EVERY2_LENGTH >> fs[] >>
      simp[libTheory.el_check_def] >>
      BasicProvers.CASE_TAC >> fs[] >>
      rpt BasicProvers.VAR_EQ_TAC >> simp[] >>
      BasicProvers.EVERY_CASE_TAC >>
      fs[store_v_same_type_def] >>
      BasicProvers.EVERY_CASE_TAC >> fs[] >>
      rpt BasicProvers.VAR_EQ_TAC >> simp[] >>
      TRY(
        reverse conj_tac >- metis_tac[EVERY2_OPTREL_syneq_trans] >>
        rfs[EVERY2_EVERY,EVERY_MEM] >>
        fs[MEM_ZIP,PULL_EXISTS,EL_MAP,EL_LUPDATE] >>
        rw[] >> metis_tac[syneq_trans,sv_rel_syneq_trans]) >>
      fs[LIST_REL_EL_EQN,EL_MAP] >>
      metis_tac[sv_rel_def,map_sv_def,store_v_nchotomy])
    >- (* CDer *) (
      srw_tac[DNF_ss][Once Cevaluate_cases] >>
      disj1_tac >>
      use_assum_tac >>
      fs[semanticPrimitivesTheory.store_lookup_def,
         libTheory.el_check_def] >>
      BasicProvers.EVERY_CASE_TAC >> fs[] >>
      rpt BasicProvers.VAR_EQ_TAC >>
      fs[map_count_store_genv_def,csg_rel_def,LIST_REL_EL_EQN,EL_MAP] >>
      metis_tac[sv_rel_def,map_sv_def])
    >- (* CRef *)(
      fs[store_alloc_def,LET_THM] >>
      srw_tac[DNF_ss][Once Cevaluate_cases] >>
      use_assum_tac >>
      fs[csg_rel_def,map_count_store_genv_def,LIST_REL_EL_EQN])
    >- (* CInitG *)(
      srw_tac[DNF_ss][Once Cevaluate_cases] >>
      disj1_tac >>
      use_assum_tac >>
      BasicProvers.EVERY_CASE_TAC >>
      fs[csg_rel_def,map_count_store_genv_def] >> rw[] >>
      fsrw_tac[ARITH_ss][EVERY2_EVERY,EVERY_MEM] >>
      rfs[MEM_ZIP,PULL_EXISTS,EL_MAP] >>
      simp[EL_LUPDATE] >> rw[] >>
      rw[optionTheory.OPTREL_def] >>
      fs[optionTheory.OPTREL_def] >>
      metis_tac[optionTheory.NOT_SOME_NONE])
    >- (* CRefB *) (
      srw_tac[DNF_ss][Once Cevaluate_cases] >>
      disj1_tac >> use_assum_tac >>
      srw_tac[DNF_ss][Once Cevaluate_cases] >>
      disj1_tac >>
      syneq_shift_tac >>
      use_assum_tac >>
      srw_tac[DNF_ss][Once Cevaluate_cases] >>
      disj1_tac >>
      srw_tac[DNF_ss][Once Cevaluate_cases] >>
      simp[Once Cevaluate_cases] >>
      simp[Once Cevaluate_cases] >>
      simp[Once Cevaluate_cases] >>
      fs[LET_THM,store_alloc_def] >>
      rw[]>>fs[]>>
      srw_tac[DNF_ss][Once Cevaluate_cases,prim_exn_pat_def]>>
      srw_tac[DNF_ss][Once Cevaluate_cases]>>
      srw_tac[DNF_ss][Once Cevaluate_cases]>>
      TRY(disj1_tac >> metis_tac[csg_rel_syneq_trans]) >>
      simp[Once Cevaluate_cases] >>
      fs[csg_rel_def,map_count_store_genv_def] >>
      metis_tac[EVERY2_OPTREL_syneq_trans,EVERY2_sv_rel_syneq_trans,LIST_REL_LENGTH,LENGTH_MAP] )
    >- (* CDerB *) (
      srw_tac[DNF_ss][Once Cevaluate_cases] >>
      disj1_tac >> use_assum_tac >>
      srw_tac[DNF_ss][Once Cevaluate_cases] >>
      disj1_tac >>
      syneq_shift_tac >>
      use_assum_tac >>
      srw_tac[DNF_ss][Once Cevaluate_cases] >>
      disj1_tac >>
      srw_tac[DNF_ss][Once Cevaluate_cases] >>
      simp[Once Cevaluate_cases] >>
      simp[Once Cevaluate_cases] >>
      simp[Once Cevaluate_cases] >>
      fs[LET_THM,store_lookup_def] >>
      BasicProvers.EVERY_CASE_TAC>>fs[]>>rw[]>>
      srw_tac[DNF_ss][Once Cevaluate_cases] >>
      TRY disj1_tac >>
      srw_tac[DNF_ss][Once Cevaluate_cases] >>
      simp[Once Cevaluate_cases,prim_exn_pat_def]
      >- metis_tac[csg_rel_syneq_trans] >>
      srw_tac[DNF_ss][Once Cevaluate_cases] >>
      srw_tac[DNF_ss][Once Cevaluate_cases] >>
      simp[Once Cevaluate_cases,libTheory.el_check_def] >>
      fs[csg_rel_def,map_count_store_genv_def,EXISTS_PROD] >>
      imp_res_tac LIST_REL_LENGTH >> fs[] >>
      `sv_rel syneq (map_sv v_to_Cv (EL lnum s21)) (EL lnum res21)` by (
        fs[LIST_REL_EL_EQN,EL_MAP] >>
        metis_tac[map_sv_def,sv_rel_syneq_trans] ) >>
      rfs[sv_rel_cases] >>
      `∀z. Num (ABS i) ≥ z ⇔ ¬(i < &z)` by (
        simp[integerTheory.INT_ABS,GREATER_EQ,integerTheory.int_ge,
             integerTheory.INT_NOT_LT,EQ_IMP_THM,integerTheory.LE_NUM_OF_INT] >>
        metis_tac[integerTheory.INT_LE,integerTheory.INT_OF_NUM,integerTheory.int_le] ) >>
      first_x_assum(qspec_then`LENGTH l`strip_assume_tac) >>
      rfs[] >>
      srw_tac[DNF_ss][Once Cevaluate_cases] >>
      srw_tac[DNF_ss][Once Cevaluate_cases] >>
      simp[Once Cevaluate_cases] >>
      srw_tac[DNF_ss][Once Cevaluate_cases] >>
      simp[Once Cevaluate_cases,libTheory.el_check_def] >>
      metis_tac[EVERY2_OPTREL_syneq_trans,EVERY2_sv_rel_syneq_trans] )
    >- (* CLenB *) (
      srw_tac[DNF_ss][Once Cevaluate_cases] >>
      disj1_tac >> use_assum_tac >>
      fs[semanticPrimitivesTheory.store_lookup_def,libTheory.el_check_def] >>
      BasicProvers.EVERY_CASE_TAC >> fs[] >> rw[] >>
      fs[csg_rel_def,map_count_store_genv_def,LIST_REL_EL_EQN,EL_MAP] >>
      metis_tac[sv_rel_def,map_sv_def])
    >- (* Aw8update *) (
      Cases_on`t`>>fs[Once(CONJUNCT2 Cevaluate_cases)] >>
      srw_tac[DNF_ss][Once Cevaluate_cases] >> disj1_tac >>
      use_assum_tac >>
      srw_tac[DNF_ss][Once Cevaluate_cases] >> disj1_tac >>
      spec_shift_then_mp_tac >>
      disch_then(qspecl_then[`LENGTH env`,`LENGTH env + 1`,`λx y. y = x+1`]mp_tac) >>
      simp[] >> strip_tac >>
      rator_x_assum`Cevaluate`mp_tac >>
      first_x_assum(mp_tac o MATCH_MP (CONJUNCT1 Cevaluate_syneq)) >>
      ntac 2 strip_tac >>
      first_x_assum(exists_suff_gen_then mp_tac) >>
      simp[Once(GSYM AND_IMP_INTRO),ADD1] >>
      disch_then(fn th => first_x_assum(mp_tac o MATCH_MP th)) >>
      disch_then(exists_suff_then mp_tac) >>
      discharge_hyps >- (
        simp[rich_listTheory.EL_CONS,PRE_SUB1] ) >>
      strip_tac >>
      use_assum_tac >>
      srw_tac[DNF_ss][Once Cevaluate_cases] >> disj1_tac >>
      spec_shift_then_mp_tac >>
      disch_then(qspecl_then[`LENGTH env`,`LENGTH env + 2`,`λx y. y = x+2`]mp_tac) >>
      simp[] >> strip_tac >>
      rator_x_assum`Cevaluate`mp_tac >>
      first_x_assum(mp_tac o MATCH_MP (CONJUNCT1 Cevaluate_syneq)) >>
      ntac 2 strip_tac >>
      first_x_assum(exists_suff_gen_then mp_tac) >>
      simp[Once(GSYM AND_IMP_INTRO),ADD1] >>
      disch_then(fn th => first_x_assum(mp_tac o MATCH_MP th)) >>
      disch_then(exists_suff_then mp_tac) >>
      discharge_hyps >- (
        simp[rich_listTheory.EL_CONS,PRE_SUB1] ) >>
      strip_tac >>
      use_assum_tac >>
      fs[semanticPrimitivesTheory.store_lookup_def] >>
      qpat_assum`X = SOME Y`mp_tac >>
      BasicProvers.CASE_TAC >>
      qmatch_assum_rename_tac`lnum < LENGTH s21`[] >>
      Cases_on`EL lnum s21`>>simp[store_assign_def] >>
      strip_tac >>
      srw_tac[DNF_ss][Once Cevaluate_cases] >> disj1_tac >>
      srw_tac[DNF_ss][Once Cevaluate_cases] >>
      srw_tac[DNF_ss][Once Cevaluate_cases] >>
      simp[Once Cevaluate_cases] >>
      simp[Once Cevaluate_cases] >>
      BasicProvers.CASE_TAC >- (
        srw_tac[DNF_ss][Once Cevaluate_cases] >>
        srw_tac[DNF_ss][Once Cevaluate_cases] >>
        srw_tac[DNF_ss][Once Cevaluate_cases] >>
        simp[prim_exn_pat_def] >>
        metis_tac[csg_rel_syneq_trans] ) >>
      srw_tac[DNF_ss][Once Cevaluate_cases] >> disj1_tac >>
      srw_tac[DNF_ss][Once Cevaluate_cases] >>
      srw_tac[DNF_ss][Once Cevaluate_cases] >>
      simp[Once Cevaluate_cases] >>
      simp[Once Cevaluate_cases] >>
      simp[Once Cevaluate_cases] >>
      simp[libTheory.el_check_def] >>
      reverse BasicProvers.CASE_TAC >- (
        fs[csg_rel_def,LIST_REL_EL_EQN,map_count_store_genv_def] >> rw[] >>
        metis_tac[] ) >>
      BasicProvers.CASE_TAC >- (
        fs[csg_rel_def,LIST_REL_EL_EQN,map_count_store_genv_def,EL_MAP] >> rw[] >>
        metis_tac[sv_rel_cases,map_sv_def,sv_rel_def] ) >>
      TRY (
        fs[csg_rel_def,LIST_REL_EL_EQN,map_count_store_genv_def,EL_MAP] >> rw[] >>
        rpt(first_x_assum(qspec_then`lnum`mp_tac)) >>
        simp[sv_rel_cases] >> NO_TAC) >>
      simp[] >>
      qmatch_assum_rename_tac`EL lnum sz = W8array lz`[] >>
      `lz = l` by (
        fs[csg_rel_def,LIST_REL_EL_EQN,map_count_store_genv_def,EL_MAP] >> rw[] >>
        metis_tac[sv_rel_cases,map_sv_def,sv_rel_def] ) >>
      `Num (ABS i) ≥ LENGTH lz ⇔ ¬(i < &LENGTH lz)` by (
        simp[integerTheory.INT_ABS,GREATER_EQ,integerTheory.int_ge,
             integerTheory.INT_NOT_LT,EQ_IMP_THM,integerTheory.LE_NUM_OF_INT] >>
        metis_tac[integerTheory.INT_LE,integerTheory.INT_OF_NUM,integerTheory.int_le] ) >>
      reverse BasicProvers.CASE_TAC >- (
        rw[] >> fs[] >> rw[] >>
        rw[Once Cevaluate_cases] >>
        rw[Once Cevaluate_cases] >>
        rw[Once Cevaluate_cases] >>
        rw[Once Cevaluate_cases] >>
        rw[Once Cevaluate_cases,prim_exn_pat_def] >>
        metis_tac[csg_rel_syneq_trans] ) >>
      srw_tac[DNF_ss][Once Cevaluate_cases] >>
      srw_tac[DNF_ss][Once Cevaluate_cases] >>
      srw_tac[DNF_ss][Once Cevaluate_cases] >>
      simp[Once Cevaluate_cases] >>
      simp[Once Cevaluate_cases,libTheory.el_check_def] >>
      simp[GSYM integerTheory.INT_NOT_LT] >>
      fs[] >> rpt BasicProvers.VAR_EQ_TAC >> simp[] >>
      fs[csg_rel_def,map_count_store_genv_def] >>
      fs[store_v_same_type_def] >>
      rpt BasicProvers.VAR_EQ_TAC >> simp[] >>
      reverse conj_tac >- metis_tac[EVERY2_OPTREL_syneq_trans] >>
      simp[EVERY2_MAP] >>
      match_mp_tac EVERY2_LUPDATE_same >>
      fs[EVERY2_MAP] >>
      fs[LIST_REL_EL_EQN] >>
      metis_tac[sv_rel_syneq_trans] )
    >- (* CVfromList *) (
      srw_tac[DNF_ss][Once Cevaluate_cases] >>
      use_assum_tac >>
      imp_res_tac CvFromList_syneq >>
      imp_res_tac CvFromList_correct >>
      fs[optionTheory.OPTREL_def] >>
      simp[Once syneq_cases])
    >- (* CDerV *) (
      srw_tac[DNF_ss][Once Cevaluate_cases] >>
      disj1_tac >> use_assum_tac >>
      srw_tac[DNF_ss][Once Cevaluate_cases] >>
      disj1_tac >>
      syneq_shift_tac >>
      use_assum_tac >>
      srw_tac[DNF_ss][Once Cevaluate_cases] >>
      disj1_tac >>
      srw_tac[DNF_ss][Once Cevaluate_cases] >>
      simp[Once Cevaluate_cases] >>
      simp[Once Cevaluate_cases] >>
      simp[Once Cevaluate_cases] >>
      rw[]>>fs[]>>rw[]>>
      srw_tac[DNF_ss][Once Cevaluate_cases,prim_exn_pat_def]>>
      srw_tac[DNF_ss][Once Cevaluate_cases]>>
      srw_tac[DNF_ss][Once Cevaluate_cases]
      >-(disj1_tac >> metis_tac[csg_rel_syneq_trans]) >>
      simp[Once Cevaluate_cases] >>
      srw_tac[DNF_ss][Once Cevaluate_cases] >>
      simp[Once Cevaluate_cases] >>
      fs[Q.SPEC`CVectorv X`syneq_cases,LET_THM] >> simp[] >>
      BasicProvers.VAR_EQ_TAC >> fs[LET_THM] >>
      imp_res_tac LIST_REL_LENGTH >> fs[] >>
      fs[integerTheory.INT_ABS] >>
      fs[arithmeticTheory.GREATER_EQ] >>
      `i = &Num i` by (
        simp[integerTheory.INT_OF_NUM] >>
        intLib.COOPER_TAC ) >>
      pop_assum SUBST1_TAC >>
      simp[integerTheory.INT_LT] >>
      reverse(rw[]) >> fsrw_tac[ARITH_ss][] >> rw[] >>
      srw_tac[DNF_ss][Once Cevaluate_cases] >>
      srw_tac[DNF_ss][Once Cevaluate_cases] >>
      srw_tac[DNF_ss][Once Cevaluate_cases] >>
      rfs[integerTheory.INT_ABS] >>
      fsrw_tac[ARITH_ss][prim_exn_pat_def] >-
        metis_tac[csg_rel_syneq_trans] >>
      simp[Once Cevaluate_cases] >>
      conj_tac >- metis_tac[csg_rel_syneq_trans] >>
      fs[LIST_REL_EL_EQN,EL_MAP] >>
      first_x_assum match_mp_tac >>
      simp[] )
    >- (* CLenV *) (
      srw_tac[DNF_ss][Once Cevaluate_cases] >>
      use_assum_tac >>
      fs[Q.SPEC`CVectorv X`syneq_cases,LET_THM] >> simp[] >>
      imp_res_tac LIST_REL_LENGTH >> fs[] )
    >- (* CRefA *) (
      srw_tac[DNF_ss][Once Cevaluate_cases] >>
      disj1_tac >> use_assum_tac >>
      srw_tac[DNF_ss][Once Cevaluate_cases] >>
      disj1_tac >>
      syneq_shift_tac >>
      use_assum_tac >>
      srw_tac[DNF_ss][Once Cevaluate_cases] >>
      disj1_tac >>
      srw_tac[DNF_ss][Once Cevaluate_cases] >>
      simp[Once Cevaluate_cases] >>
      simp[Once Cevaluate_cases] >>
      simp[Once Cevaluate_cases] >>
      rw[]>>fs[]>>rw[]>>
      srw_tac[DNF_ss][Once Cevaluate_cases,prim_exn_pat_def]>>
      srw_tac[DNF_ss][Once Cevaluate_cases]>>
      srw_tac[DNF_ss][Once Cevaluate_cases]
      >-(disj1_tac >> metis_tac[csg_rel_syneq_trans]) >>
      simp[Once Cevaluate_cases] >>
      srw_tac[DNF_ss][Once Cevaluate_cases] >>
      simp[Once Cevaluate_cases] >>
      fs[store_alloc_def,LET_THM] >> simp[] >>
      BasicProvers.VAR_EQ_TAC >> fs[LET_THM] >>
      BasicProvers.VAR_EQ_TAC >>
      fs[csg_rel_def,map_count_store_genv_def] >>
      reverse conj_asm2_tac >- metis_tac[LIST_REL_LENGTH,LENGTH_MAP] >>
      reverse conj_tac >- metis_tac[EVERY2_OPTREL_syneq_trans] >>
      fs[EVERY2_MAP] >>
      fs[LIST_REL_EL_EQN,rich_listTheory.REPLICATE_GENLIST,integerTheory.INT_ABS] >>
      metis_tac[sv_rel_syneq_trans,syneq_trans] )
    >- (* CDerA *) (
      srw_tac[DNF_ss][Once Cevaluate_cases] >>
      disj1_tac >> use_assum_tac >>
      srw_tac[DNF_ss][Once Cevaluate_cases] >>
      disj1_tac >>
      syneq_shift_tac >>
      use_assum_tac >>
      srw_tac[DNF_ss][Once Cevaluate_cases] >>
      disj1_tac >>
      srw_tac[DNF_ss][Once Cevaluate_cases] >>
      simp[Once Cevaluate_cases] >>
      simp[Once Cevaluate_cases] >>
      simp[Once Cevaluate_cases] >>
      fs[LET_THM,store_lookup_def] >>
      BasicProvers.EVERY_CASE_TAC>>fs[]>>rw[]>>
      srw_tac[DNF_ss][Once Cevaluate_cases] >>
      TRY disj1_tac >>
      srw_tac[DNF_ss][Once Cevaluate_cases] >>
      simp[Once Cevaluate_cases,prim_exn_pat_def]
      >- metis_tac[csg_rel_syneq_trans] >>
      srw_tac[DNF_ss][Once Cevaluate_cases] >>
      srw_tac[DNF_ss][Once Cevaluate_cases] >>
      simp[Once Cevaluate_cases,libTheory.el_check_def] >>
      fs[csg_rel_def,map_count_store_genv_def,EXISTS_PROD] >>
      imp_res_tac LIST_REL_LENGTH >> fs[] >>
      `sv_rel syneq (map_sv v_to_Cv (EL lnum s21)) (EL lnum res21)` by (
        fs[LIST_REL_EL_EQN,EL_MAP] >>
        metis_tac[map_sv_def,sv_rel_syneq_trans] ) >>
      rfs[sv_rel_cases] >>
      `∀z. Num (ABS i) ≥ z ⇔ ¬(i < &z)` by (
        simp[integerTheory.INT_ABS,GREATER_EQ,integerTheory.int_ge,
             integerTheory.INT_NOT_LT,EQ_IMP_THM,integerTheory.LE_NUM_OF_INT] >>
        metis_tac[integerTheory.INT_LE,integerTheory.INT_OF_NUM,integerTheory.int_le] ) >>
      first_x_assum(qspec_then`LENGTH l`strip_assume_tac) >>
      `LENGTH l = LENGTH vs2` by (imp_res_tac LIST_REL_LENGTH >> fs[]) >> fs[] >>
      rfs[] >>
      srw_tac[DNF_ss][Once Cevaluate_cases] >>
      srw_tac[DNF_ss][Once Cevaluate_cases] >>
      simp[Once Cevaluate_cases] >>
      srw_tac[DNF_ss][Once Cevaluate_cases] >>
      simp[Once Cevaluate_cases,libTheory.el_check_def] >>
      rpt conj_tac >>
      TRY (
        qmatch_assum_rename_tac`EL lnum s21 = Varray l`[] >>
        qmatch_assum_abbrev_tac`LIST_REL R l1 Cres1` >>
        qmatch_assum_abbrev_tac`LIST_REL R Cres1 l2` >>
        `LIST_REL R l1 l2` by metis_tac[EVERY2_sv_rel_syneq_trans] >>
        fs[LIST_REL_EL_EQN] >>
        pop_assum(qspec_then`lnum`mp_tac) >>
        simp[Abbr`R`,sv_rel_cases,Abbr`l1`,EVERY2_MAP,EL_MAP] >>
        rw[LIST_REL_EL_EQN] >>
        first_x_assum match_mp_tac >>
        simp[] >> NO_TAC) >>
      metis_tac[EVERY2_OPTREL_syneq_trans,EVERY2_sv_rel_syneq_trans] )
    >- (* CLen *) (
      srw_tac[DNF_ss][Once Cevaluate_cases] >> disj1_tac >>
      use_assum_tac >>
      fs[store_lookup_def] >>
      qpat_assum`X = SOME Y`mp_tac >>
      IF_CASES_TAC >> simp[] >>
      BasicProvers.CASE_TAC >> strip_tac >>
      rpt BasicProvers.VAR_EQ_TAC >>
      conj_tac >- metis_tac[csg_rel_syneq_trans] >>
      fs[csg_rel_def,map_count_store_genv_def,LIST_REL_EL_EQN,libTheory.el_check_def] >>
      rpt(first_x_assum(qspec_then`n`mp_tac)) >> simp[EL_MAP] >>
      simp[sv_rel_cases] >> rw[] >> simp[] >>
      fs[LIST_REL_EL_EQN])
    >- (* Aupdate *) (
      Cases_on`t`>>fs[Once(CONJUNCT2 Cevaluate_cases)] >>
      srw_tac[DNF_ss][Once Cevaluate_cases] >> disj1_tac >>
      use_assum_tac >>
      srw_tac[DNF_ss][Once Cevaluate_cases] >> disj1_tac >>
      spec_shift_then_mp_tac >>
      disch_then(qspecl_then[`LENGTH env`,`LENGTH env + 1`,`λx y. y = x+1`]mp_tac) >>
      simp[] >> strip_tac >>
      rator_x_assum`Cevaluate`mp_tac >>
      first_x_assum(mp_tac o MATCH_MP (CONJUNCT1 Cevaluate_syneq)) >>
      ntac 2 strip_tac >>
      first_x_assum(exists_suff_gen_then mp_tac) >>
      simp[Once(GSYM AND_IMP_INTRO),ADD1] >>
      disch_then(fn th => first_x_assum(mp_tac o MATCH_MP th)) >>
      disch_then(exists_suff_then mp_tac) >>
      discharge_hyps >- (
        simp[rich_listTheory.EL_CONS,PRE_SUB1] ) >>
      strip_tac >>
      use_assum_tac >>
      srw_tac[DNF_ss][Once Cevaluate_cases] >> disj1_tac >>
      spec_shift_then_mp_tac >>
      disch_then(qspecl_then[`LENGTH env`,`LENGTH env + 2`,`λx y. y = x+2`]mp_tac) >>
      simp[] >> strip_tac >>
      rator_x_assum`Cevaluate`mp_tac >>
      first_x_assum(mp_tac o MATCH_MP (CONJUNCT1 Cevaluate_syneq)) >>
      ntac 2 strip_tac >>
      first_x_assum(exists_suff_gen_then mp_tac) >>
      simp[Once(GSYM AND_IMP_INTRO),ADD1] >>
      disch_then(fn th => first_x_assum(mp_tac o MATCH_MP th)) >>
      disch_then(exists_suff_then mp_tac) >>
      discharge_hyps >- (
        simp[rich_listTheory.EL_CONS,PRE_SUB1] ) >>
      strip_tac >>
      use_assum_tac >>
      fs[semanticPrimitivesTheory.store_lookup_def] >>
      qpat_assum`X = SOME Y`mp_tac >>
      BasicProvers.CASE_TAC >>
      qmatch_assum_rename_tac`lnum < LENGTH s21`[] >>
      Cases_on`EL lnum s21`>>simp[store_assign_def] >>
      strip_tac >>
      srw_tac[DNF_ss][Once Cevaluate_cases] >> disj1_tac >>
      srw_tac[DNF_ss][Once Cevaluate_cases] >>
      srw_tac[DNF_ss][Once Cevaluate_cases] >>
      simp[Once Cevaluate_cases] >>
      simp[Once Cevaluate_cases] >>
      BasicProvers.CASE_TAC >- (
        srw_tac[DNF_ss][Once Cevaluate_cases] >>
        srw_tac[DNF_ss][Once Cevaluate_cases] >>
        srw_tac[DNF_ss][Once Cevaluate_cases] >>
        simp[prim_exn_pat_def] >>
        metis_tac[csg_rel_syneq_trans] ) >>
      srw_tac[DNF_ss][Once Cevaluate_cases] >> disj1_tac >>
      srw_tac[DNF_ss][Once Cevaluate_cases] >>
      srw_tac[DNF_ss][Once Cevaluate_cases] >>
      simp[Once Cevaluate_cases] >>
      simp[Once Cevaluate_cases] >>
      simp[Once Cevaluate_cases] >>
      simp[libTheory.el_check_def] >>
      reverse BasicProvers.CASE_TAC >- (
        fs[csg_rel_def,LIST_REL_EL_EQN,map_count_store_genv_def] >> rw[] >>
        metis_tac[] ) >>
      BasicProvers.CASE_TAC >- (
        fs[csg_rel_def,LIST_REL_EL_EQN,map_count_store_genv_def,EL_MAP] >> rw[] >>
        metis_tac[sv_rel_cases,map_sv_def,sv_rel_def] ) >>
      TRY (
        fs[csg_rel_def,LIST_REL_EL_EQN,map_count_store_genv_def,EL_MAP] >> rw[] >>
        rpt(first_x_assum(qspec_then`lnum`mp_tac)) >>
        simp[sv_rel_cases] >> rw[] >> fs[] >> NO_TAC) >>
      simp[] >>
      qmatch_assum_rename_tac`EL lnum sz = Varray lz`[] >>
      `LIST_REL syneq (MAP v_to_Cv l) lz` by (
        fs[csg_rel_def,map_count_store_genv_def,EVERY2_MAP,LIST_REL_EL_EQN] >>
        rpt(first_x_assum(qspec_then`lnum`mp_tac)) >> simp[sv_rel_cases] >>
        simp[EVERY2_MAP,LIST_REL_EL_EQN,PULL_EXISTS] >> rw[] >>
        metis_tac[syneq_trans]) >>
      `Num (ABS i) ≥ LENGTH lz ⇔ ¬(i < &LENGTH lz)` by (
        simp[integerTheory.INT_ABS,GREATER_EQ,integerTheory.int_ge,
             integerTheory.INT_NOT_LT,EQ_IMP_THM,integerTheory.LE_NUM_OF_INT] >>
        metis_tac[integerTheory.INT_LE,integerTheory.INT_OF_NUM,integerTheory.int_le] ) >>
      reverse BasicProvers.CASE_TAC >- (
        rw[] >> fs[] >> rw[] >>
        rw[Once Cevaluate_cases] >>
        rw[Once Cevaluate_cases] >>
        rw[Once Cevaluate_cases] >>
        rw[Once Cevaluate_cases] >>
        simp[Once Cevaluate_cases,prim_exn_pat_def] >>
        imp_res_tac LIST_REL_LENGTH >> fs[] >>
        rpt BasicProvers.VAR_EQ_TAC >> simp[prim_exn_pat_def] >>
        metis_tac[csg_rel_syneq_trans] ) >>
      srw_tac[DNF_ss][Once Cevaluate_cases] >>
      srw_tac[DNF_ss][Once Cevaluate_cases] >>
      srw_tac[DNF_ss][Once Cevaluate_cases] >>
      simp[Once Cevaluate_cases] >>
      simp[Once Cevaluate_cases,libTheory.el_check_def] >>
      simp[GSYM integerTheory.INT_NOT_LT] >>
      imp_res_tac LIST_REL_LENGTH >> fs[] >>
      fs[store_v_same_type_def] >>
      rpt BasicProvers.VAR_EQ_TAC >> simp[prim_exn_pat_def] >>
      fs[csg_rel_def,map_count_store_genv_def] >>
      rpt BasicProvers.VAR_EQ_TAC >> simp[] >>
      reverse conj_tac >- metis_tac[EVERY2_OPTREL_syneq_trans] >>
      simp[EVERY2_MAP] >>
      match_mp_tac EVERY2_LUPDATE_same >>
      fs[EVERY2_MAP] >>
      fs[LIST_REL_EL_EQN] >>
      simp[EL_LUPDATE] >> rw[] >>
      metis_tac[sv_rel_syneq_trans,syneq_trans] )
    >- (* TagEq *) (
      srw_tac[DNF_ss][Once Cevaluate_cases] >>
      use_assum_tac >>
      fs[Q.SPEC`CConv X Y`syneq_cases] >>
      metis_tac[] )
    >- (* Proj *) (
      srw_tac[DNF_ss][Once Cevaluate_cases] >>
      use_assum_tac >>
      fs[Q.SPEC`CConv X Y`syneq_cases] >>
      simp[libTheory.el_check_def] >>
      fs[LIST_REL_EL_EQN,EL_MAP] >> rfs[] )) >>
  strip_tac >- simp[] >>
  strip_tac >- (
    simp[] >> rpt gen_tac >>
    strip_tac >> strip_tac >> fs[] >>
    (app_to_il_err
     |> CONV_RULE(STRIP_BINDER_CONV(SOME universal)(LAND_CONV(lift_conjunct_conv(same_const``Cevaluate_list`` o fst o strip_comb))))
     |> REWRITE_RULE[GSYM AND_IMP_INTRO]
     |> (fn th => (first_x_assum (mp_tac o MATCH_MP th)))) >>
    simp[] >> disch_then(qspec_then`op`mp_tac) >>
    REWRITE_TAC[GSYM exps_to_Cexps_MAP] >> simp[EVERY_MAP] >> strip_tac >>
    use_assum_tac >>
    metis_tac[csg_rel_syneq_trans,exc_rel_syneq_trans]) >>
  strip_tac >- (
    simp[] >>
    rpt gen_tac >> rpt strip_tac >>
    simp[Once Cevaluate_cases] >>
    srw_tac[DNF_ss][] >> disj1_tac >>
    fs[] >>
    first_assum(split_pair_match o concl) >> fs[] >>
    Cases_on`v`>>fs[do_if_pat_def]>>
    Cases_on`l`>>fs[]>>
    first_assum(match_exists_tac o concl) >> simp[] >>
    imp_res_tac evaluate_pat_closed >>
    rw[] >> fs[] >> rw[] >> fs[] >>
    syneq_tac >> use_assum_tac >>
    metis_tac[csg_rel_syneq_trans,result_rel_syneq_syneq_trans]) >>
  strip_tac >- simp[] >>
  strip_tac >- (
    simp[] >>
    rpt gen_tac >> rpt strip_tac >>
    simp[Once Cevaluate_cases] >>
    srw_tac[DNF_ss][] >> disj2_tac >> fs[] >>
    first_assum(split_pair_match o concl) >> fs[] >>
    first_assum(match_exists_tac o concl) >> fs[] ) >>
  strip_tac >- (
    simp[] >> rw[] >> fs[] >>
    simp[Once Cevaluate_cases] >>
    srw_tac[DNF_ss][] >> disj1_tac >>
    use_assum_tac >>
    qpat_assum`p ⇒ q`mp_tac >>
    discharge_hyps >- (
      imp_res_tac evaluate_pat_closed >> fs[] >>
      fs[SUBSET_DEF,PULL_EXISTS] >>
      Cases >> simp[] >> rw[] >>
      res_tac >> fsrw_tac[ARITH_ss][] ) >>
    strip_tac >>
    first_x_assum(mp_tac o MATCH_MP(CONJUNCT1 Cevaluate_syneq)) >>
    disch_then(exists_suff_gen_then mp_tac) >>
    disch_then(qspec_then`$=`(exists_suff_then mp_tac) o CONV_RULE SWAP_FORALL_CONV) >>
    simp[syneq_exp_refl] >>
    discharge_hyps >- ( Cases >> simp[] ) >>
    strip_tac >>
    use_assum_tac >>
    metis_tac[csg_rel_syneq_trans,result_rel_syneq_syneq_trans] ) >>
  strip_tac >- (
    simp[] >> rw[] >> fs[] >>
    simp[Once Cevaluate_cases] >>
    srw_tac[DNF_ss][] >> disj2_tac >>
    use_assum_tac ) >>
  strip_tac >- (
    simp[] >> rw[] >> fs[] >>
    simp[Once Cevaluate_cases] >>
    srw_tac[DNF_ss][] >> disj1_tac >>
    use_assum_tac >>
    imp_res_tac evaluate_pat_closed >> fs[] >>
    syneq_tac >> use_assum_tac >>
    metis_tac[csg_rel_syneq_trans,result_rel_syneq_syneq_trans]) >>
  strip_tac >- (
    simp[] >> rw[] >> fs[] >>
    simp[Once Cevaluate_cases] >>
    srw_tac[DNF_ss][] >> disj2_tac >>
    use_assum_tac ) >>
  strip_tac >- (
    simp[] >> rw[] >> fs[] >>
    simp[Once Cevaluate_cases] >>
    fs[build_rec_env_pat_def] >>
    qpat_assum`p ⇒ q`mp_tac >>
    discharge_hyps >- (
      fs[SUBSET_DEF,PULL_EXISTS,EVERY_GENLIST] >>
      conj_tac >- (
        qx_gen_tac`x`>>rw[] >>
        Cases_on`x < LENGTH funs`>>simp[]>>
        res_tac >> fsrw_tac[ARITH_ss][] ) >>
      simp[Once closed_pat_cases] >>
      fs[MEM_FLAT,MEM_MAP,PULL_EXISTS] >>
      simp[EVERY_MEM,SUBSET_DEF] >>
      ntac 2 (gen_tac >> strip_tac) >>
      qx_gen_tac`x`>>rw[] >>
      Cases_on`x < LENGTH funs + 1`>>simp[]>>
      res_tac >> fsrw_tac[ARITH_ss][] ) >>
    strip_tac >>
    fs[MAP_GENLIST,combinTheory.o_DEF,LET_THM] >>
    fsrw_tac[ETA_ss][] >>
    metis_tac[] ) >>
  strip_tac >- (
    rw[] >>
    simp[Once Cevaluate_cases] >>
    rw[map_count_store_genv_def,csg_rel_def] >>
    TRY(
      match_mp_tac EVERY2_refl >> simp[] ) >>
    match_mp_tac rich_listTheory.EVERY2_APPEND_suff >>
    simp[MAP_GENLIST,combinTheory.o_DEF] >>
    conj_tac >> match_mp_tac EVERY2_refl >>
    metis_tac[optionTheory.OPTREL_refl,syneq_refl] ) >>
  strip_tac >- (
    rw[] >> rw[Once Cevaluate_cases] ) >>
  strip_tac >- (
    rw[] >> rw[Once Cevaluate_cases] >>
    srw_tac[DNF_ss][] >> fs[] >>
    use_assum_tac >>
    imp_res_tac evaluate_pat_closed >> fs[] >>
    first_x_assum(mp_tac o MATCH_MP(CONJUNCT2 Cevaluate_syneq)) >>
    disch_then(exists_suff_gen_then mp_tac) >>
    disch_then(qspec_then`$=`(exists_suff_then mp_tac)) >>
    simp[syneq_exp_refl] >> strip_tac >>
    use_assum_tac >>
    metis_tac[csg_rel_syneq_trans,EVERY2_syneq_trans] ) >>
  strip_tac >- (
    rw[] >> rw[Once Cevaluate_cases] >>
    srw_tac[DNF_ss][] >> fs[] >>
    disj1_tac >>
    use_assum_tac ) >>
  rw[] >> rw[Once Cevaluate_cases] >>
  srw_tac[DNF_ss][] >> fs[] >>
  disj2_tac >>
  use_assum_tac >>
  imp_res_tac evaluate_pat_closed >> fs[] >>
  first_x_assum(mp_tac o MATCH_MP(CONJUNCT2 Cevaluate_syneq)) >>
  disch_then(exists_suff_gen_then mp_tac) >>
  disch_then(qspec_then`$=`(exists_suff_then mp_tac)) >>
  simp[syneq_exp_refl] >> strip_tac >>
  use_assum_tac >>
  metis_tac[csg_rel_syneq_trans,exc_rel_syneq_trans] )

val _ = export_theory()
