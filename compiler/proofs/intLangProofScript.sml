open HolKernel bossLib boolLib boolSimps lcsymtacs listTheory pairTheory pred_setTheory arithmeticTheory
open miscLib miscTheory patLangTheory intLangTheory toIntLangTheory compilerTerminationTheory intLangExtraTheory
open free_varsTheory
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

val exc_rel_syneq_trans =
  exc_rel_trans
  |> Q.GEN`R` |> Q.ISPEC`syneq`
  |> UNDISCH_ALL
  |> prove_hyps_by(metis_tac[syneq_trans])

val no_labs_exp_to_Cexp = store_thm("no_labs_exp_to_Cexp",
  ``(∀e. no_labs (exp_to_Cexp e)) ∧
    (∀es. no_labs_list (exps_to_Cexps es))``,
  ho_match_mp_tac exp_to_Cexp_ind >>
  rw[exp_to_Cexp_def,exps_to_Cexps_MAP] >>
  rw[EVERY_MAP,rich_listTheory.EVERY_REVERSE] >>
  TRY (unabbrev_all_tac >>
       fsrw_tac[DNF_ss][EVERY_MEM,MEM_MAP,FORALL_PROD] >>
       simp[UNCURRY] >> NO_TAC) >>
  BasicProvers.CASE_TAC >> rw[])
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
  metis_tac [])

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
    simp[Once Cevaluate_cases] >>
    srw_tac[DNF_ss][] >> fs[] >>
    use_assum_tac >>
    Cases_on`uop`>>
    fs[do_uapp_pat_def,LET_THM
      ,semanticPrimitivesTheory.store_alloc_def] >>
    TRY (
      qpat_assum`X = SOME y`mp_tac >>
      BasicProvers.CASE_TAC >>
      simp[semanticPrimitivesTheory.store_lookup_def] >>
      rw[] ) >>
    fs[] >> rw[compilerLibTheory.el_check_def] >>
    fs[csg_rel_def,map_count_store_genv_def] >> rw[] >>
    fsrw_tac[ARITH_ss][EVERY2_EVERY] >>
    TRY (
      qpat_assum`syneq (CConv X Y) Z`mp_tac >>
      simp[Once syneq_cases] >> strip_tac) >>
    simp[compilerLibTheory.el_check_def] >>
    fsrw_tac[ARITH_ss][EVERY2_EVERY,EVERY_MEM] >>
    rfs[MEM_ZIP,PULL_EXISTS,EL_MAP] >>
    simp[EL_LUPDATE] >> rw[] >>
    rw[optionTheory.OPTREL_def] >>
    fs[optionTheory.OPTREL_def] >>
    metis_tac[optionTheory.NOT_SOME_NONE]) >>
  strip_tac >- simp[] >>
  strip_tac >- (
    simp[] >>
    rpt gen_tac >> rpt strip_tac >>
    simp[Once Cevaluate_cases] >>
    srw_tac[DNF_ss][] >> fs[] >>
    disj2_tac >>
    first_assum (split_pair_match o concl) >> fs[] >>
    first_assum (match_exists_tac o concl) >> simp[] ) >>
  strip_tac >- (
    rw[] >> fs[] >>
    `csg_closed_pat s' ∧ closed_pat v1 ∧
     csg_closed_pat ((count',s3),genv3) ∧ closed_pat v2` by (
      imp_res_tac evaluate_pat_closed >> fs[] ) >> fs[] >>
    Cases_on`op = Opapp` >- (
      simp[] >>
      simp[Once Cevaluate_cases] >>
      srw_tac[DNF_ss][] >>
      disj1_tac >>
      first_assum(split_pair_match o concl) >> fs[] >>
      qpat_assum`syneq (v_to_Cv v1) X`mp_tac >>
      Cases_on`v1`>>fs[do_app_pat_def] >>
      simp[Once syneq_cases] >> rw[] >>
      first_assum(match_exists_tac o concl) >> simp[] >>
      simp[Once Cevaluate_cases] >>
      simp[Once (CONJUNCT2 Cevaluate_cases),PULL_EXISTS] >>
      first_assum(mp_tac o MATCH_MP (CONJUNCT1 Cevaluate_syneq)) >>
      disch_then(exists_suff_gen_then mp_tac) >>
      disch_then(qspec_then`$=`(exists_suff_then mp_tac)) >>
      simp[syneq_exp_refl] >> strip_tac >>
      first_assum(split_pair_match o concl) >> fs[] >>
      first_assum(match_exists_tac o concl) >> simp[] >>
      fs[bigStepTheory.dec_count_def] >>
      qpat_assum`p ⇒ q`mp_tac >>
      (discharge_hyps >- (
        qpat_assum`closed_pat (X Y)`mp_tac >>
        simp[Once closed_pat_cases,ADD1] >>
        fs[csg_closed_pat_def] >>
        simp[EVERY_MEM,build_rec_env_pat_def,MEM_GENLIST,PULL_EXISTS] >>
        simp[MEM_EL,PULL_EXISTS,SUBSET_DEF,AC ADD_ASSOC ADD_SYM] >>
        strip_tac >> simp[Once closed_pat_cases] >>
        simp[EVERY_MEM,MEM_EL,PULL_EXISTS,SUBSET_DEF,AC ADD_ASSOC ADD_SYM])) >>
      strip_tac >>
      imp_res_tac csg_rel_count >> fs[] >>
      simp[Once map_count_store_genv_def] >>
      simp[Once map_count_store_genv_def] >>
      last_x_assum (mp_tac o MATCH_MP (CONJUNCT1 Cevaluate_no_vlabs)) >>
      (discharge_hyps >- (
        simp[EVERY_MAP,no_vlabs_csg_def,map_count_store_genv_def,EVERY_FILTER] >>
        simp[EVERY_MEM] >> Cases >> simp[] )) >>
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
          Cases >> Cases >> simp[ADD1] >- metis_tac[syneq_trans] >>
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
          Cases >> Cases >> simp[ADD1] >- metis_tac[syneq_trans] >>
          rw[] >> simp[rich_listTheory.EL_APPEND1,rich_listTheory.EL_APPEND2] >>
          simp[EL_MAP] >>
          simp[Once syneq_cases] >>
          metis_tac[])
        ] >>
      metis_tac[result_rel_syneq_syneq_trans,csg_rel_syneq_trans]) >>
    Cases_on`op`>>simp[]>>fs[]>-(
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
        Cases_on`op`>>Cases_on`v1`>>TRY(Cases_on`l:lit`)>>Cases_on`v2`>>TRY(Cases_on`l:lit`)>>
        fs[opn_to_prim2_def,do_app_pat_def,bigStepTheory.dec_count_def] >>
        rpt BasicProvers.VAR_EQ_TAC >> simp[] >> fs[astTheory.opn_lookup_def] >>
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
      srw_tac[DNF_ss][Once(CONJUNCT2 Cevaluate_cases)] >>
      srw_tac[DNF_ss][Once(CONJUNCT2 Cevaluate_cases)] >>
      qmatch_assum_rename_tac`opn_to_prim2 op = X`["X"] >>
      Cases_on`op`>>Cases_on`v1`>>TRY(Cases_on`l:lit`)>>Cases_on`v2`>>TRY(Cases_on`l:lit`)>>
      fs[opn_to_prim2_def,do_app_pat_def,bigStepTheory.dec_count_def] >>
      rpt BasicProvers.VAR_EQ_TAC >> simp[] >> fs[astTheory.opn_lookup_def] >>
      rw[] >> fs[exn_env_pat_def] >> TRY (
        fs[SIMP_RULE(srw_ss())
           [SIMP_RULE(srw_ss())[](Q.SPECL[`ck`,`env`,`s`,`Con_pat X Y`](CONJUNCT1 evaluate_pat_cases))]
           (Q.SPECL[`ck`,`env`,`s`,`Raise_pat (Con_pat X Y)`](CONJUNCT1 evaluate_pat_cases))] >>
        fs[SIMP_RULE(srw_ss())
           [SIMP_RULE(srw_ss())[](Q.SPECL[`env`,`s`,`CCon X Y`](CONJUNCT1 Cevaluate_cases))]
           (Q.SPECL[`env`,`s`,`CRaise (CCon X Y)`](CONJUNCT1 Cevaluate_cases))] >>
        srw_tac[DNF_ss][Once(CONJUNCT2 Cevaluate_cases)] >> disj1_tac >>
        simp[Once syneq_cases] >>
        fs[Once(CONJUNCT2 evaluate_pat_cases)] >>
        metis_tac[csg_rel_syneq_trans] ) >>
      simp[Once Cevaluate_cases] >>
      srw_tac[DNF_ss,ARITH_ss][Once(CONJUNCT2 Cevaluate_cases),ADD1] >>
      srw_tac[DNF_ss][Once(CONJUNCT2 Cevaluate_cases)] >>
      srw_tac[DNF_ss][Once(CONJUNCT2 Cevaluate_cases)] >>
      disj1_tac >> fs[] >>
      metis_tac[csg_rel_syneq_trans] )
    >- (
      BasicProvers.CASE_TAC >>
      simp[Once Cevaluate_cases] >>
      srw_tac[DNF_ss][] >> disj1_tac >>
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
        fs[do_app_pat_def,bigStepTheory.dec_count_def]>>
        Cases_on`v1`>>TRY(Cases_on`l:lit`)>>Cases_on`v2`>>TRY(Cases_on`l:lit`)>> fs[] >>
        rpt BasicProvers.VAR_EQ_TAC >> fs[astTheory.opb_lookup_def] >>
        TRY (
          conj_tac >- metis_tac[csg_rel_syneq_trans] >>
          intLib.COOPER_TAC ) >>
        metis_tac[csg_rel_syneq_trans] ) >>
      use_assum_tac >>
      simp[Once Cevaluate_cases] >>
      srw_tac[DNF_ss][] >> disj1_tac >>
      syneq_shift_tac >>
      use_assum_tac >>
      simp[Once Cevaluate_cases] >>
      srw_tac[DNF_ss][Once(CONJUNCT2 Cevaluate_cases)] >>
      srw_tac[DNF_ss][Once(CONJUNCT2 Cevaluate_cases)] >>
      srw_tac[DNF_ss][Once(CONJUNCT2 Cevaluate_cases)] >>
      simp[ADD1] >> disj1_tac >>
      fs[bigStepTheory.dec_count_def,do_app_pat_def] >>
      Cases_on`v1`>>TRY(Cases_on`l:lit`)>>Cases_on`v2`>>TRY(Cases_on`l:lit`)>> fs[] >>
      rpt BasicProvers.VAR_EQ_TAC >> fs[astTheory.opb_lookup_def] >>
      TRY (
        simp[Once Cevaluate_cases] >>
        srw_tac[DNF_ss][Once(CONJUNCT2 Cevaluate_cases)] >>
        srw_tac[DNF_ss][Once(CONJUNCT2 Cevaluate_cases)] >>
        simp[Once(CONJUNCT2 Cevaluate_cases)] >>
        conj_tac >- metis_tac[csg_rel_syneq_trans] >>
        intLib.COOPER_TAC ) >>
      metis_tac[csg_rel_syneq_trans,integerTheory.int_gt] )
    >- (
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
      fs[do_app_pat_def] >>
      Q.PAT_ABBREV_TAC`Ce = do_Ceq X Y` >>
      Cases_on`do_eq_pat v1 v2`>>fs[]>>
      `Ce = do_eq_pat v1 v2` by (
        metis_tac[do_Ceq_correct,do_Ceq_syneq1,do_Ceq_syneq2] ) >>
      simp[] >>
      rpt BasicProvers.VAR_EQ_TAC >>
      fs[bigStepTheory.dec_count_def] >>
      simp[Once Cevaluate_cases] >>
      simp[Once Cevaluate_cases] >>
      simp[Once Cevaluate_cases] >>
      fs[exn_env_pat_def] >>
      fs[SIMP_RULE(srw_ss())
         [SIMP_RULE(srw_ss())[](Q.SPECL[`ck`,`env`,`s`,`Con_pat X Y`](CONJUNCT1 evaluate_pat_cases))]
         (Q.SPECL[`ck`,`env`,`s`,`Raise_pat (Con_pat X Y)`](CONJUNCT1 evaluate_pat_cases))] >>
      fs[SIMP_RULE(srw_ss())
         [SIMP_RULE(srw_ss())[](Q.SPECL[`env`,`s`,`CCon X Y`](CONJUNCT1 Cevaluate_cases))]
         (Q.SPECL[`env`,`s`,`CRaise (CCon X Y)`](CONJUNCT1 Cevaluate_cases))] >>
      rpt BasicProvers.VAR_EQ_TAC >>
      simp[Once Cevaluate_cases] >>
      simp[Once Cevaluate_cases] >>
      fs[Once(CONJUNCT2 Cevaluate_cases)] >>
      fs[Once(CONJUNCT2 evaluate_pat_cases)] >>
      metis_tac[csg_rel_syneq_trans,result_rel_syneq_syneq_trans])
    >- (
      simp[Once Cevaluate_cases] >>
      srw_tac[DNF_ss][] >>
      srw_tac[DNF_ss][Once(CONJUNCT2 Cevaluate_cases)] >>
      srw_tac[DNF_ss][Once(CONJUNCT2 Cevaluate_cases)] >>
      srw_tac[DNF_ss][Once(CONJUNCT2 Cevaluate_cases)] >>
      disj1_tac >>
      use_assum_tac >>
      syneq_tac >>
      use_assum_tac >>
      fs[do_app_pat_def] >>
      Cases_on`v1`>>fs[] >>
      fs[semanticPrimitivesTheory.store_assign_def] >>
      qmatch_assum_rename_tac`csg_rel syneq X (FST Y)`["X"]>>
      PairCases_on`Y`>>fs[csg_rel_def,map_count_store_genv_def] >>
      imp_res_tac EVERY2_LENGTH >> fs[] >>
      BasicProvers.CASE_TAC >> fs[] >>
      rpt BasicProvers.VAR_EQ_TAC >>
      fs[bigStepTheory.dec_count_def] >>
      reverse conj_tac >- metis_tac[EVERY2_OPTREL_syneq_trans] >>
      rfs[EVERY2_EVERY,EVERY_MEM] >>
      fs[MEM_ZIP,PULL_EXISTS,EL_MAP,EL_LUPDATE] >>
      rw[] >> metis_tac[syneq_trans] )) >>
  strip_tac >- (
    simp[] >> rw[] >>
    rw[Once Cevaluate_cases] >>
    srw_tac[DNF_ss][] >>
    disj2_tac >> disj1_tac >>
    simp[Once (CONJUNCT2 Cevaluate_cases)] >>
    simp[Once (CONJUNCT2 Cevaluate_cases)] >>
    simp[PULL_EXISTS] >>
    Cases_on`v1`>>fs[do_app_pat_def,LET_THM]>>rw[]>>
    first_assum(split_pair_match o concl) >> fs[] >>
    qpat_assum`syneq (CRecClos X Y Z) A`mp_tac >>
    simp[Once syneq_cases] >> rw[] >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    qpat_assum`p ⇒ q`mp_tac >>
    (discharge_hyps >- (
       imp_res_tac evaluate_pat_closed >> fs[])) >>
    strip_tac >>
    first_x_assum(mp_tac o MATCH_MP (CONJUNCT1 Cevaluate_syneq)) >>
    disch_then(exists_suff_gen_then mp_tac) >>
    disch_then(qspec_then`$=`(exists_suff_then mp_tac)) >>
    simp[syneq_exp_refl] >> strip_tac >>
    first_assum(split_pair_match o concl) >> fs[] >>
    qmatch_assum_rename_tac`csg_rel syneq (FST A) B`["B"] >>
    PairCases_on`A`>>fs[csg_rel_def,map_count_store_genv_def] >> rw[] >>
    first_assum(match_exists_tac o concl) >> fs[] >>
    metis_tac[EVERY2_syneq_trans,EVERY2_OPTREL_syneq_trans]) >>
  strip_tac >- simp[] >>
  strip_tac >- (
    simp[] >>
    rpt gen_tac >> rpt strip_tac >> fs[] >>
    `csg_closed_pat s'` by (imp_res_tac evaluate_pat_closed >> fs[]) >>
    Cases_on`op`>>fs[LET_THM] >- (
      BasicProvers.CASE_TAC >- (
        simp[Once Cevaluate_cases] >>
        srw_tac[DNF_ss][] >> disj2_tac >>
        simp[Once Cevaluate_cases] >>
        simp[Once (CONJUNCT2 Cevaluate_cases)] >>
        simp[Once (CONJUNCT2 Cevaluate_cases)] >>
        srw_tac[DNF_ss][] >> disj2_tac >>
        first_assum (split_pair_match o concl) >> fs[] >>
        first_assum (match_exists_tac o concl) >> simp[] >>
        first_x_assum(exists_suff_gen_then mp_tac o (MATCH_MP (CONJUNCT1 Cevaluate_syneq))) >>
        disch_then(qspec_then`$=`(exists_suff_then mp_tac)) >>
        simp[syneq_exp_refl] >> strip_tac >>
        first_assum (split_pair_match o concl) >> fs[] >>
        first_assum (match_exists_tac o concl) >> simp[] >>
        metis_tac[csg_rel_syneq_trans,exc_rel_syneq_trans] ) >>
      simp[Once Cevaluate_cases] >>
      srw_tac[DNF_ss][] >> disj1_tac >>
      first_assum (split_pair_match o concl) >> fs[] >>
      first_assum (match_exists_tac o concl) >> simp[] >>
      simp[Once Cevaluate_cases] >>
      srw_tac[DNF_ss][] >>
      disj2_tac >>
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
      simp[EXISTS_PROD] >> strip_tac >> fs[] >>
      first_assum(match_exists_tac o concl) >>
      metis_tac[csg_rel_syneq_trans,exc_rel_syneq_trans] )
    >- (
      BasicProvers.CASE_TAC >>
      simp[Once Cevaluate_cases] >>
      srw_tac[DNF_ss][] >>
      TRY (
        disj2_tac >>
        srw_tac[DNF_ss][Once(CONJUNCT2 Cevaluate_cases)] >>
        srw_tac[DNF_ss][Once(CONJUNCT2 Cevaluate_cases)] >>
        srw_tac[DNF_ss][Once(CONJUNCT2 Cevaluate_cases)] >>
        TRY (
          disj2_tac >>
          use_assum_tac >> syneq_tac >> use_assum_tac >>
          metis_tac[csg_rel_syneq_trans,exc_rel_syneq_trans] ) >>
        simp[Once Cevaluate_cases] >>
        srw_tac[DNF_ss][Once(CONJUNCT2 Cevaluate_cases)] >>
        disj2_tac >>
        srw_tac[DNF_ss][Once(CONJUNCT2 Cevaluate_cases)] >>
        srw_tac[DNF_ss][Once(CONJUNCT2 Cevaluate_cases)] >>
        srw_tac[DNF_ss][Once(CONJUNCT2 Cevaluate_cases)] >>
        disj2_tac >>
        use_assum_tac >> syneq_tac >> use_assum_tac >>
        metis_tac[csg_rel_syneq_trans,exc_rel_syneq_trans] ) >>
      disj1_tac >>
      use_assum_tac >>
      simp[Once Cevaluate_cases] >>
      srw_tac[DNF_ss][] >> disj2_tac >>
      syneq_shift_tac >>
      use_assum_tac >>
      metis_tac[csg_rel_syneq_trans,exc_rel_syneq_trans] )
    >- (
      simp[Once Cevaluate_cases] >>
      srw_tac[DNF_ss][] >> disj2_tac >>
      simp[Once Cevaluate_cases] >>
      srw_tac[DNF_ss][] >> disj2_tac >>
      srw_tac[DNF_ss][Once(CONJUNCT2 Cevaluate_cases)] >>
      srw_tac[DNF_ss][Once(CONJUNCT2 Cevaluate_cases)] >>
      srw_tac[DNF_ss][Once(CONJUNCT2 Cevaluate_cases)] >>
      disj2_tac >>
      use_assum_tac >> syneq_tac >> use_assum_tac >>
      metis_tac[csg_rel_syneq_trans,exc_rel_syneq_trans] )
    >- (
      simp[Once Cevaluate_cases] >>
      srw_tac[DNF_ss][] >> disj2_tac >>
      disj2_tac >> disj1_tac >>
      srw_tac[DNF_ss][Once(CONJUNCT2 Cevaluate_cases)] >>
      srw_tac[DNF_ss][Once(CONJUNCT2 Cevaluate_cases)] >>
      srw_tac[DNF_ss][Once(CONJUNCT2 Cevaluate_cases)] >>
      use_assum_tac >> syneq_tac >> use_assum_tac >>
      metis_tac[csg_rel_syneq_trans,exc_rel_syneq_trans] )
    >- (
      simp[Once Cevaluate_cases] >>
      srw_tac[DNF_ss][] >> disj2_tac >>
      srw_tac[DNF_ss][Once(CONJUNCT2 Cevaluate_cases)] >>
      srw_tac[DNF_ss][Once(CONJUNCT2 Cevaluate_cases)] >>
      srw_tac[DNF_ss][Once(CONJUNCT2 Cevaluate_cases)] >>
      disj2_tac >>
      use_assum_tac >> syneq_tac >> use_assum_tac >>
      metis_tac[csg_rel_syneq_trans,exc_rel_syneq_trans] )) >>
  strip_tac >- (
    simp[] >>
    rpt gen_tac >> rpt strip_tac >> fs[] >>
    Cases_on`op`>>simp[]>-(
      BasicProvers.CASE_TAC >- (
        simp[Once Cevaluate_cases] >>
        srw_tac[DNF_ss][] >> disj2_tac >>
        simp[Once (CONJUNCT2 Cevaluate_cases)] >>
        simp[Once (CONJUNCT2 Cevaluate_cases)] >>
        simp[Once (CONJUNCT2 Cevaluate_cases)] >>
        srw_tac[DNF_ss][] >> disj1_tac >>
        first_assum (split_pair_match o concl) >> fs[] >>
        first_assum (match_exists_tac o concl) >> simp[] ) >>
      simp[Once Cevaluate_cases] >>
      srw_tac[DNF_ss][] >> disj2_tac >>
      first_assum (split_pair_match o concl) >> fs[] >>
      first_assum (match_exists_tac o concl) >> simp[] )
    >- (
      BasicProvers.CASE_TAC >- (
        simp[Once Cevaluate_cases] >>
        srw_tac[DNF_ss][] >> disj2_tac >>
        simp[Once (CONJUNCT2 Cevaluate_cases)] >>
        simp[Once (CONJUNCT2 Cevaluate_cases)] >>
        simp[Once (CONJUNCT2 Cevaluate_cases)] >>
        srw_tac[DNF_ss][] >> disj1_tac >>
        first_assum (split_pair_match o concl) >> fs[] >>
        first_assum (match_exists_tac o concl) >> simp[] )
      >- (
        simp[Once Cevaluate_cases] >>
        srw_tac[DNF_ss][] >> disj2_tac >>
        first_assum (split_pair_match o concl) >> fs[] >>
        first_assum (match_exists_tac o concl) >> simp[] )
      >- (
        simp[Once Cevaluate_cases] >>
        srw_tac[DNF_ss][] >> disj2_tac >>
        simp[Once Cevaluate_cases] >>
        simp[Once Cevaluate_cases] >>
        srw_tac[DNF_ss][] >> disj1_tac >> disj2_tac >>
        simp[Once (CONJUNCT2 Cevaluate_cases)] >>
        simp[Once (CONJUNCT2 Cevaluate_cases)] >>
        simp[Once (CONJUNCT2 Cevaluate_cases)] >>
        srw_tac[DNF_ss][] >> disj1_tac >>
        first_assum (split_pair_match o concl) >> fs[] >>
        first_assum (match_exists_tac o concl) >> simp[] )
      >- (
        simp[Once Cevaluate_cases] >>
        srw_tac[DNF_ss][] >> disj2_tac >>
        first_assum (split_pair_match o concl) >> fs[] >>
        first_assum (match_exists_tac o concl) >> simp[] ))
    >- (
      simp[Once Cevaluate_cases] >>
      srw_tac[DNF_ss][] >> disj2_tac >>
      simp[Once Cevaluate_cases] >>
      srw_tac[DNF_ss][] >> disj2_tac >>
      simp[Once (CONJUNCT2 Cevaluate_cases)] >>
      simp[Once (CONJUNCT2 Cevaluate_cases)] >>
      simp[Once (CONJUNCT2 Cevaluate_cases)] >>
      srw_tac[DNF_ss][] >> disj1_tac >>
      first_assum (split_pair_match o concl) >> fs[] >>
      first_assum (match_exists_tac o concl) >> simp[] )
    >- (
      simp[Once Cevaluate_cases] >>
      srw_tac[DNF_ss][] >> disj2_tac >> disj2_tac >> disj2_tac >>
      first_assum (split_pair_match o concl) >> fs[] >>
      first_assum (match_exists_tac o concl) >> simp[] )
    >- (
      simp[Once Cevaluate_cases] >>
      srw_tac[DNF_ss][] >> disj2_tac >>
      simp[Once (CONJUNCT2 Cevaluate_cases)] >>
      simp[Once (CONJUNCT2 Cevaluate_cases)] >>
      simp[Once (CONJUNCT2 Cevaluate_cases)] >>
      srw_tac[DNF_ss][] >> disj1_tac >>
      first_assum (split_pair_match o concl) >> fs[] >>
      first_assum (match_exists_tac o concl) >> simp[] )
    ) >>
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
    match_mp_tac EVERY2_APPEND_suff >>
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
