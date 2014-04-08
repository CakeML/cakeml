open HolKernel bossLib boolLib boolSimps lcsymtacs listTheory pairTheory pred_setTheory arithmeticTheory
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

val shift_thm =
  mkshift_thm
  |> Q.SPEC`λv. v + n`
  |> SIMP_RULE std_ss [GSYM shift_def]
  |> Q.GEN`n`

fun spec_args_of_then P ttac th (g as (_,w)) =
  let
    val t = find_term (P o fst o strip_comb)  w
    val (_,args) = strip_comb t
  in
    ttac (SPECL args th)
  end g

val spec_shift_then_mp_tac =
  spec_args_of_then (equal``shift``) mp_tac shift_thm

(* TODO: move *)

val free_vars_i4_def = tDefine"free_vars_i4"`
  free_vars_i4 (Raise_i4 e) = free_vars_i4 e ∧
  free_vars_i4 (Handle_i4 e1 e2) = lunion (free_vars_i4 e1) (lshift 1 (free_vars_i4 e2)) ∧
  free_vars_i4 (Lit_i4 _) = [] ∧
  free_vars_i4 (Con_i4 _ es) = free_vars_list_i4 es ∧
  free_vars_i4 (Var_local_i4 n) = [n] ∧
  free_vars_i4 (Var_global_i4 _) = [] ∧
  free_vars_i4 (Fun_i4 e) = lshift 1 (free_vars_i4 e) ∧
  free_vars_i4 (Uapp_i4 _ e) = free_vars_i4 e ∧
  free_vars_i4 (App_i4 _ e1 e2) = lunion (free_vars_i4 e1) (free_vars_i4 e2) ∧
  free_vars_i4 (If_i4 e1 e2 e3) = lunion (free_vars_i4 e1) (lunion (free_vars_i4 e2) (free_vars_i4 e3)) ∧
  free_vars_i4 (Let_i4 e1 e2) = lunion (free_vars_i4 e1) (lshift 1 (free_vars_i4 e2)) ∧
  free_vars_i4 (Seq_i4 e1 e2) = lunion (free_vars_i4 e1) (free_vars_i4 e2) ∧
  free_vars_i4 (Letrec_i4 es e) = lunion (free_vars_defs_i4 (LENGTH es) es) (lshift (LENGTH es) (free_vars_i4 e)) ∧
  free_vars_i4 (Extend_global_i4 _) = [] ∧
  free_vars_list_i4 [] = [] ∧
  free_vars_list_i4 (e::es) = lunion (free_vars_i4 e) (free_vars_list_i4 es) ∧
  free_vars_defs_i4 _ [] = [] ∧
  free_vars_defs_i4 n (e::es) = lunion (lshift (n+1) (free_vars_i4 e)) (free_vars_defs_i4 n es)`
(WF_REL_TAC`inv_image $< (λx. case x of
  | INL e => exp_i4_size e
  | INR (INL es) => exp_i41_size es
  | INR (INR (_,es)) => exp_i41_size es)`)
val _ = export_rewrites["free_vars_i4_def"]

val free_vars_defs_i4_MAP = store_thm("free_vars_defs_i4_MAP",
  ``set (free_vars_defs_i4 n es) = set (lshift (n+1) (free_vars_list_i4 es))``,
  Induct_on`es`>>simp[] >> fs[EXTENSION] >>
  rw[EQ_IMP_THM] >> simp[] >> metis_tac[])

val free_vars_list_i4_MAP = store_thm("free_vars_list_i4_MAP",
  ``∀es. set (free_vars_list_i4 es) = set (FLAT (MAP free_vars_i4 es))``,
  Induct >> simp[])
val _ = export_rewrites["free_vars_defs_i4_MAP","free_vars_list_i4_MAP"]

val free_vars_exp_to_Cexp = store_thm("free_vars_exp_to_Cexp",
  ``(∀e. set (free_vars (exp_to_Cexp e)) = set (free_vars_i4 e)) ∧
    (∀es. set (free_vars_list (exps_to_Cexps es)) = set (free_vars_list_i4 es))``,
  ho_match_mp_tac exp_to_Cexp_ind >> simp[] >>
  strip_tac >- (
    rw[EXTENSION] >>
    rw[EQ_IMP_THM] >> rw[] >> fsrw_tac[ARITH_ss][] >>
    simp[PULL_EXISTS] >> HINT_EXISTS_TAC >> simp[] ) >>
  strip_tac >- (
    rw[] >>
    BasicProvers.CASE_TAC >> simp[] >>
    fs[EXTENSION] >> rw[EQ_IMP_THM] >> rw[] >> fsrw_tac[ARITH_ss][] >>
    spose_not_then strip_assume_tac >>
    first_x_assum(qspec_then`x+1`mp_tac) >> simp[] ) >>
  strip_tac >- (
    rw[] >>
    BasicProvers.CASE_TAC >> simp[] >>
    fs[EXTENSION] >> rw[EQ_IMP_THM] >> rw[] >> fsrw_tac[ARITH_ss][] >>
    spose_not_then strip_assume_tac >>
    first_x_assum(qspec_then`x+1`mp_tac) >> simp[] ) >>
  rpt gen_tac >> strip_tac >>
  fs[EXTENSION,free_vars_defs_MAP,free_vars_list_MAP] >>
  simp[MAP_MAP_o,combinTheory.o_DEF] >>
  fs[MEM_FLAT,MEM_MAP,PULL_EXISTS] >>
  rw[EQ_IMP_THM] >> rw[] >> fsrw_tac[ARITH_ss][] >>
  metis_tac[])
val _ = export_rewrites["free_vars_exp_to_Cexp"]

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

val (closed_i4_rules,closed_i4_ind,closed_i4_cases) = Hol_reln`
(closed_i4 (Litv_i4 l)) ∧
(EVERY (closed_i4) vs ⇒ closed_i4 (Conv_i4 cn vs)) ∧
(EVERY (closed_i4) env ∧ set (free_vars_i4 b) ⊆ count (LENGTH env + 1)
⇒ closed_i4 (Closure_i4 env b)) ∧
(EVERY (closed_i4) env ∧ d < LENGTH defs ∧
 EVERY (λe. set (free_vars_i4 e) ⊆ count (LENGTH env + LENGTH defs + 1)) defs
⇒ closed_i4 (Recclosure_i4 env defs d)) ∧
(closed_i4 (Loc_i4 n))`;

val closed_i4_lit_loc_conv = store_thm("closed_i4_lit_loc_conv",
  ``closed_i4 (Litv_i4 l) ∧ closed_i4 (Loc_i4 n) ∧
    (closed_i4 (Conv_i4 a bs) ⇔ EVERY closed_i4 bs)``,
  rw[closed_i4_cases])
val _ = export_rewrites["closed_i4_lit_loc_conv"]

val v_to_Cv_closed = store_thm("v_to_Cv_closed",
  ``(∀v. closed_i4 v ⇒ Cclosed (v_to_Cv v)) ∧
    (∀vs. EVERY closed_i4 vs ⇒ EVERY Cclosed (vs_to_Cvs vs))``,
  ho_match_mp_tac(TypeBase.induction_of``:v_i4``) >>
  simp[] >> rw[] >-
    simp[Once Cclosed_cases] >>
  pop_assum mp_tac >>
  simp[Once closed_i4_cases] >>
  simp[Once Cclosed_cases] >- (
    simp[SUBSET_DEF,PULL_EXISTS] >>
    rw[] >> rw[] >> simp[] >> res_tac >> simp[] ) >>
  rw[MEM_MAP] >> rw[] >>
  fs[EVERY_MEM] >> res_tac >>
  fsrw_tac[ARITH_ss][])

val csg_closed_i4_def = Define`
  csg_closed_i4 csg ⇔
    EVERY closed_i4 (SND(FST csg)) ∧
    EVERY (OPTION_EVERY closed_i4) (SND csg)`

val no_vlabs_v_to_Cv = store_thm("no_vlabs_v_to_Cv",
  ``(∀v. no_vlabs (v_to_Cv v)) ∧
    (∀vs. no_vlabs_list (vs_to_Cvs vs))``,
  ho_match_mp_tac(TypeBase.induction_of(``:v_i4``)) >> simp[EVERY_MAP])
val _ = export_rewrites["no_vlabs_v_to_Cv"]

val evaluate_i4_closed = store_thm("evaluate_i4_closed",
  ``(∀ck env s e res. evaluate_i4 ck env s e res ⇒
       set (free_vars_i4 e) ⊆ count (LENGTH env) ∧
       EVERY closed_i4 env ∧ csg_closed_i4 s ⇒
       csg_closed_i4 (FST res) ∧
       every_result closed_i4 closed_i4 (SND res)) ∧
    (∀ck env s es res. evaluate_list_i4 ck env s es res ⇒
       set (free_vars_list_i4 es) ⊆ count (LENGTH env) ∧
       EVERY closed_i4 env ∧ csg_closed_i4 s ⇒
       csg_closed_i4 (FST res) ∧
       every_result (EVERY closed_i4) closed_i4 (SND res))``,
  ho_match_mp_tac evaluate_i4_ind >> simp[] >>
  strip_tac >- (
    rpt gen_tac >> ntac 2 strip_tac >>
    first_x_assum match_mp_tac >> fs[] >>
    fsrw_tac[ARITH_ss][SUBSET_DEF,PULL_EXISTS] >>
    Cases>>simp[ADD1] >> rw[] >>
    res_tac >> fsrw_tac[ARITH_ss][]) >>
  strip_tac >- simp[EVERY_MEM,MEM_EL,PULL_EXISTS] >>
  strip_tac >- (
    simp[csg_closed_i4_def,EVERY_MEM,MEM_EL,PULL_EXISTS] >>
    rw[] >> first_x_assum(qspec_then`n`mp_tac) >> simp[] ) >>
  strip_tac >- (
    simp[Once closed_i4_cases,SUBSET_DEF,PULL_EXISTS] >>
    rpt gen_tac >> strip_tac >>
    Cases >> simp[] ) >>
  strip_tac >- (
    gen_tac >> Cases >>
    gen_tac >> Cases >>
    simp[do_uapp_i4_def
        ,semanticPrimitivesTheory.store_alloc_def
        ,semanticPrimitivesTheory.store_lookup_def] >>
    rw[] >> fs[] >>
    fs[csg_closed_i4_def] >>
    fs[EVERY_MEM,MEM_EL,PULL_EXISTS] >>
    BasicProvers.EVERY_CASE_TAC >> fs[] >>
    rw[EL_LUPDATE] >>
    rw[EVERY_MEM,MEM_EL,PULL_EXISTS] ) >>
  strip_tac >- (
    ntac 2 gen_tac >> Cases >>
    ntac 2 gen_tac >> Cases >>TRY(Cases_on`l:lit`)>>
    simp[do_app_i4_def] >>
    Cases >> TRY(Cases_on`l:lit`)>>
    simp[bigStepTheory.dec_count_def] >>
    rpt gen_tac >> ntac 2 strip_tac >> fs[] >>
    TRY(qpat_assum`X = SOME Y`mp_tac >>
        BasicProvers.CASE_TAC >> strip_tac >>
        rpt BasicProvers.VAR_EQ_TAC) >>
    first_x_assum match_mp_tac >>
    simp[exn_env_i4_def] >>
    TRY (
      rator_x_assum`closed_i4`mp_tac >>
      simp[Once closed_i4_cases] >>
      simp[ADD1] >> rfs[csg_closed_i4_def] ) >>
    fs[semanticPrimitivesTheory.store_assign_def] >>
    rpt BasicProvers.VAR_EQ_TAC >>
    TRY (
      rfs[csg_closed_i4_def,EVERY_MEM,PULL_EXISTS,MEM_EL,EL_LUPDATE] >>
      rw[] >> rw[EVERY_MEM,MEM_EL,PULL_EXISTS] >> NO_TAC) >>
    simp[build_rec_env_i4_def,EVERY_GENLIST] >>
    simp[EVERY_MEM,MEM_EL,PULL_EXISTS,AC ADD_ASSOC ADD_SYM] >>
    strip_tac >>
    simp[Once closed_i4_cases] >>
    simp[EVERY_MEM,MEM_EL,PULL_EXISTS,AC ADD_ASSOC ADD_SYM] ) >>
  strip_tac >- (
    ntac 3 gen_tac >>
    Cases >> simp[do_app_i4_def] ) >>
  strip_tac >- (
    ntac 4 gen_tac >>
    Cases >> simp[do_if_i4_def] >>
    Cases_on`l`>>simp[] >> rw[] ) >>
  strip_tac >- (
    rpt gen_tac >> ntac 2 strip_tac >>
    first_x_assum match_mp_tac >>
    fsrw_tac[DNF_ss][SUBSET_DEF,ADD1] >>
    Cases >> simp[ADD1] >> rw[] >> res_tac >>
    fsrw_tac[ARITH_ss][] ) >>
  strip_tac >- (
    rpt gen_tac >> ntac 2 strip_tac >>
    first_x_assum match_mp_tac >>
    fsrw_tac[DNF_ss][SUBSET_DEF,ADD1,build_rec_env_i4_def,EVERY_GENLIST] >>
    conj_tac >- (
      rw[] >>
      Cases_on`x < LENGTH funs`>>simp[] >>
      REWRITE_TAC[Once ADD_SYM] >>
      first_x_assum match_mp_tac >>
      simp[] ) >>
    simp[Once closed_i4_cases] >>
    fs[EVERY_MEM,SUBSET_DEF,MEM_FLAT,PULL_EXISTS,MEM_MAP] >>
    rw[] >>
    fsrw_tac[ARITH_ss][AC ADD_ASSOC ADD_SYM] >>
    Cases_on`x < LENGTH funs + 1`>>simp[] >>
    first_x_assum match_mp_tac >>
    simp[] >> metis_tac[] ) >>
  simp[csg_closed_i4_def,EVERY_GENLIST])

val exp_to_Cexp_correct = store_thm("exp_to_Cexp_correct",
  ``(∀ck env s e res. evaluate_i4 ck env s e res ⇒
       ck ∧
       set (free_vars_i4 e) ⊆ count (LENGTH env) ∧
       EVERY closed_i4 env ∧ csg_closed_i4 s ∧
       SND res ≠ Rerr Rtype_error ⇒
       ∃Cres.
       Cevaluate (map_count_store_genv v_to_Cv s) (vs_to_Cvs env) (exp_to_Cexp e) Cres ∧
       csg_i4 syneq (map_count_store_genv v_to_Cv (FST res)) (FST Cres) ∧
       result_rel syneq syneq (map_result v_to_Cv v_to_Cv (SND res)) (SND Cres)) ∧
    (∀ck env s es res. evaluate_list_i4 ck env s es res ⇒
       ck ∧
       set (free_vars_list_i4 es) ⊆ count (LENGTH env) ∧
       EVERY closed_i4 env ∧ csg_closed_i4 s ∧
       SND res ≠ Rerr Rtype_error ⇒
       ∃Cres.
       Cevaluate_list (map_count_store_genv v_to_Cv s) (vs_to_Cvs env) (exps_to_Cexps es) Cres ∧
       csg_i4 syneq (map_count_store_genv v_to_Cv (FST res)) (FST Cres) ∧
       result_rel (LIST_REL syneq) syneq (map_result vs_to_Cvs v_to_Cv (SND res)) (SND Cres))``,
  ho_match_mp_tac evaluate_i4_strongind >>
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
      imp_res_tac evaluate_i4_closed >> fs[]) >>
    strip_tac >>
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
    srw_tac[DNF_ss][] >> fs[] >>
    first_assum (split_pair_match o concl) >> fs[] >>
    first_assum (match_exists_tac o concl) >> simp[] >>
    cheat (* CevalPrim1_correct *)) >>
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
    `csg_closed_i4 s' ∧ closed_i4 v1 ∧
     csg_closed_i4 ((count',s3),genv3) ∧ closed_i4 v2` by (
      imp_res_tac evaluate_i4_closed >> fs[] ) >> fs[] >>
    Cases_on`op = Opapp` >- (
      simp[] >>
      simp[Once Cevaluate_cases] >>
      srw_tac[DNF_ss][] >>
      disj1_tac >>
      first_assum(split_pair_match o concl) >> fs[] >>
      qpat_assum`syneq (v_to_Cv v1) X`mp_tac >>
      Cases_on`v1`>>fs[do_app_i4_def] >>
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
        qpat_assum`closed_i4 (X Y)`mp_tac >>
        simp[Once closed_i4_cases,ADD1] >>
        fs[csg_closed_i4_def] >>
        simp[EVERY_MEM,build_rec_env_i4_def,MEM_GENLIST,PULL_EXISTS] >>
        simp[MEM_EL,PULL_EXISTS,SUBSET_DEF,AC ADD_ASSOC ADD_SYM] >>
        strip_tac >> simp[Once closed_i4_cases] >>
        simp[EVERY_MEM,MEM_EL,PULL_EXISTS,SUBSET_DEF,AC ADD_ASSOC ADD_SYM])) >>
      strip_tac >>
      imp_res_tac csg_i4_count >> fs[] >>
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
          qpat_assum`closed_i4 (Closure_i4 X Y)`mp_tac >>
          simp[Once closed_i4_cases] ) >>
        disch_then(mp_tac o (MATCH_MP (CONJUNCT1 syneq_exp_trans))) >>
        disch_then(qspecl_then[`z2`,`U`,`e4`]mp_tac) >>
        disch_then(fn th => disch_then(mp_tac o MATCH_MP th)) >>
        map_every qunabbrev_tac[`z1`,`z2`,`U`,`e3`,`e4`,`Z`],
        ALL_TAC] >>
      simp[] >> strip_tac >>
      first_x_assum(mp_tac o MATCH_MP (CONJUNCT1 Cevaluate_syneq)) >>
      disch_then(exists_suff_gen_then mp_tac) >>
      simp[ADD1,Once (GSYM AND_IMP_INTRO),build_rec_env_i4_def] >>
      disch_then(fn th => first_x_assum (mp_tac o MATCH_MP th)) >>
      disch_then(exists_suff_then mp_tac) >|[
        discharge_hyps >- (
          reverse conj_tac >- (
            fs[map_count_store_genv_def] >>
            qmatch_assum_rename_tac`csg_i4 syneq (X,MAP f genv3) (FST Y)`["X","f"] >>
            PairCases_on`Y`>>fs[csg_i4_def] >>
            metis_tac[EVERY2_syneq_trans,EVERY2_OPTREL_syneq_trans] ) >>
          simp[relationTheory.O_DEF,PULL_EXISTS,syneq_cb_V_def] >>
          Cases >> Cases >> simp[ADD1] >- metis_tac[syneq_trans] >>
          rw[] >>
          simp[rich_listTheory.EL_APPEND2] )
        ,
        discharge_hyps >- (
          reverse conj_tac >- (
            fs[map_count_store_genv_def] >>
            qmatch_assum_rename_tac`csg_i4 syneq (X,MAP f genv3) (FST Y)`["X","f"] >>
            PairCases_on`Y`>>fs[csg_i4_def] >>
            metis_tac[EVERY2_syneq_trans,EVERY2_OPTREL_syneq_trans] ) >>
          simp[PULL_EXISTS,syneq_cb_V_def] >>
          Cases >> Cases >> simp[ADD1] >- metis_tac[syneq_trans] >>
          rw[] >> simp[rich_listTheory.EL_APPEND1,rich_listTheory.EL_APPEND2] >>
          simp[EL_MAP] >>
          simp[Once syneq_cases] >>
          metis_tac[])
        ] >>
      metis_tac[result_rel_syneq_syneq_trans,csg_i4_syneq_trans]) >>
    cheat) >>
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
    qpat_assum`p ⇒ q`mp_tac >>
    (discharge_hyps >- (
       imp_res_tac evaluate_i4_closed >> fs[])) >>
    strip_tac >>
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
    `csg_closed_i4 s'` by (imp_res_tac evaluate_i4_closed >> fs[]) >>
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
      metis_tac[csg_i4_syneq_trans,exc_rel_syneq_trans] )
    >> cheat) >>
  cheat)

val _ = export_theory()
