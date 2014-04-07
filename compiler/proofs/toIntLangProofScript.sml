open HolKernel bossLib boolLib boolSimps lcsymtacs listTheory pairTheory
open miscLib miscTheory intLang4Theory intLangTheory toIntLangTheory compilerTerminationTheory intLangExtraTheory
open toIntLang4ProofTheory
val _ = new_theory "toIntLangProof"

val _ = export_rewrites["compilerTermination.exp_to_Cexp_def","toIntLang.v_to_Cv_def"]

val vs_to_Cvs_MAP = store_thm("vs_to_Cvs_MAP",
  ``∀vs. vs_to_Cvs vs = MAP v_to_Cv vs``,
  Induct >> simp[])
val _ = export_rewrites["vs_to_Cvs_MAP"]

val exps_to_Cexps_MAP = store_thm("exps_to_Cexps_MAP",
  ``∀es. exps_to_Cexps es = MAP exp_to_Cexp es``,
  Induct >> simp[])
val _ = export_rewrites["exps_to_Cexps_MAP"]

val result_rel_syneq_syneq_trans =
  result_rel_trans
  |> Q.GENL[`R2`,`R1`]
  |> Q.ISPECL[`syneq`,`syneq`]
  |> UNDISCH_ALL
  |> prove_hyps_by(metis_tac[syneq_trans])

val csg_i4_syneq_trans =
  csg_i4_trans
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

(*
val exp_to_Cexp_correct = store_thm("exp_to_Cexp_correct",
  ``(∀ck env s e res. evaluate_i4 ck env s e res ⇒
       ck ∧ SND res ≠ Rerr Rtype_error ⇒
       ∃Cres.
       Cevaluate (map_count_store_genv v_to_Cv s) (vs_to_Cvs env) (exp_to_Cexp e) Cres ∧
       csg_i4 syneq (map_count_store_genv v_to_Cv (FST res)) (FST Cres) ∧
       result_rel syneq syneq (map_result v_to_Cv v_to_Cv (SND res)) (SND Cres)) ∧
    (∀ck env s es res. evaluate_list_i4 ck env s es res ⇒
       ck ∧ SND res ≠ Rerr Rtype_error ⇒
       ∃Cres.
       Cevaluate_list (map_count_store_genv v_to_Cv s) (vs_to_Cvs env) (exps_to_Cexps es) Cres ∧
       csg_i4 syneq (map_count_store_genv v_to_Cv (FST res)) (FST Cres) ∧
       result_rel (LIST_REL syneq) syneq (map_result vs_to_Cvs v_to_Cv (SND res)) (SND Cres))``,
  ho_match_mp_tac evaluate_i4_ind >>
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
    first_assum (mp_tac o MATCH_MP (CONJUNCT1 Cevaluate_syneq)) >>
    disch_then (exists_suff_gen_then mp_tac) >>
    disch_then (qspec_then`$=`mp_tac o CONV_RULE(SWAP_FORALL_CONV)) >>
    disch_then (exists_suff_then mp_tac) >>
    discharge_hyps >- ( simp[syneq_exp_refl] >> Cases >> simp[] ) >>
    metis_tac[result_rel_syneq_syneq_trans,csg_i4_syneq_trans]) >>
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
    srw_tac[DNF_ss][] >>
    first_assum (split_pair_match o concl) >> fs[] >>
    first_assum (match_exists_tac o concl) >> simp[] >>
    cheat ) >>
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
    cheat ) >>
  strip_tac >- (
    simp[] >> rw[] >>
    rw[Once Cevaluate_cases] >>
    srw_tac[DNF_ss][] >>
    disj2_tac >> disj1_tac >>
    simp[Once (CONJUNCT2 Cevaluate_cases)] >>
    simp[Once (CONJUNCT2 Cevaluate_cases)] >>
    simp[PULL_EXISTS] >>
    Cases_on`v1`>>fs[do_app_i4_def,LET_THM]>>rw[]>>
    first_assum(split_pair_match o concl) >> fs[] >>
    qpat_assum`syneq (CRecClos X Y Z) A`mp_tac >>
    simp[Once syneq_cases] >> rw[] >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    first_x_assum(mp_tac o MATCH_MP (CONJUNCT1 Cevaluate_syneq)) >>
    disch_then(exists_suff_gen_then mp_tac) >>
    disch_then(qspec_then`$=`(exists_suff_then mp_tac)) >>
    simp[syneq_exp_refl] >> strip_tac >>
    first_assum(split_pair_match o concl) >> fs[] >>
    qmatch_assum_rename_tac`csg_i4 syneq (FST A) B`["B"] >>
    PairCases_on`A`>>fs[csg_i4_def,map_count_store_genv_def] >> rw[] >>
    first_assum(match_exists_tac o concl) >> fs[] >>
    metis_tac[EVERY2_syneq_trans,EVERY2_OPTREL_syneq_trans]) >>
  strip_tac >- simp[] >>
  strip_tac >- (
    simp[] >>
    rpt gen_tac >> rpt strip_tac >> fs[] >>
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
        metis_tac[csg_i4_syneq_trans,exc_rel_syneq_trans] ) >>
      simp[Once Cevaluate_cases] >>
      srw_tac[DNF_ss][] >> disj1_tac >>
      first_assum (split_pair_match o concl) >> fs[] >>
      first_assum (match_exists_tac o concl) >> simp[] >>
      simp[Once Cevaluate_cases] >>
      srw_tac[DNF_ss][] >>
      need syneq theorem about shift
*)

val _ = export_theory()
