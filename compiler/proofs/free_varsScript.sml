open HolKernel boolLib bossLib lcsymtacs pred_setTheory arithmeticTheory listTheory pairTheory finite_mapTheory rich_listTheory
open miscLib miscTheory boolSimps astTheory terminationTheory
open modLangTheory conLangTheory decLangTheory exhLangTheory patLangTheory toIntLangTheory compilerTerminationTheory
open modLangProofTheory conLangProofTheory exhLangProofTheory patLangProofTheory

val _ = new_theory"free_vars"

val IS_SOME_EXISTS = store_thm("IS_SOME_EXISTS",
  ``∀opt. IS_SOME opt ⇔ ∃x. opt = SOME x``,
  Cases >> simp[])

val FDOM_FOLDR_DOMSUB = store_thm("FDOM_FOLDR_DOMSUB",
  ``∀ls fm. FDOM (FOLDR (λk m. m \\ k) fm ls) = FDOM fm DIFF set ls``,
  Induct >> simp[] >>
  ONCE_REWRITE_TAC[EXTENSION] >>
  simp[] >> metis_tac[])

val vs_to_exh_MAP = store_thm("vs_to_exh_MAP",
  ``∀exh vs. vs_to_exh exh vs = MAP (v_to_exh exh) vs``,
  Induct_on`vs`>>simp[v_to_exh_def])

val env_to_exh_MAP = store_thm("env_to_exh_MAP",
  ``∀exh env. env_to_exh exh env = MAP (λ(x,e). (x, v_to_exh exh e)) env``,
  Induct_on`env`>>simp[v_to_exh_def] >> Cases >> simp[v_to_exh_def])

val alloc_defs_GENLIST = store_thm("alloc_defs_GENLIST",
  ``∀n ls. alloc_defs n ls = ZIP(ls,GENLIST(λx. x + n)(LENGTH ls))``,
  Induct_on`ls`>>simp[alloc_defs_def,GENLIST_CONS] >>
  simp[combinTheory.o_DEF,ADD1])

val pats_bindings_i2_MAP_Pvar_i2 = store_thm("pats_bindings_i2_MAP_Pvar_i2",
  ``∀ls ly. set (pats_bindings_i2 (MAP Pvar_i2 ls) ly) = set ls ∪ set ly``,
  Induct >> simp[pat_bindings_i2_def,EXTENSION] >> metis_tac[])

val (closed_exh_rules,closed_exh_ind,closed_exh_cases) = Hol_reln`
(closed_exh (Litv_exh l)) ∧
(EVERY (closed_exh) vs ⇒ closed_exh (Conv_exh cn vs)) ∧
(EVERY (closed_exh) (MAP SND env) ∧ free_vars_exh b ⊆ {x} ∪ set (MAP FST env)
⇒ closed_exh (Closure_exh env x b)) ∧
(EVERY (closed_exh) (MAP SND env) ∧ MEM d (MAP FST defs) ∧
 EVERY (λ(f,x,e). free_vars_exh e ⊆ {x} ∪ set (MAP FST defs) ∪ set (MAP FST env)) defs
⇒ closed_exh (Recclosure_exh env defs d)) ∧
(closed_exh (Loc_exh n))`;

val closed_exh_lit_loc_conv = store_thm("closed_exh_lit_loc_conv",
  ``closed_exh (Litv_exh l) ∧ closed_exh (Loc_exh n) ∧
    (closed_exh (Conv_exh a bs) ⇔ EVERY closed_exh bs)``,
  rw[closed_exh_cases])
val _ = export_rewrites["closed_exh_lit_loc_conv"]

val free_vars_pat_def = tDefine"free_vars_pat"`
  free_vars_pat (Raise_pat e) = free_vars_pat e ∧
  free_vars_pat (Handle_pat e1 e2) = lunion (free_vars_pat e1) (lshift 1 (free_vars_pat e2)) ∧
  free_vars_pat (Lit_pat _) = [] ∧
  free_vars_pat (Con_pat _ es) = free_vars_list_pat es ∧
  free_vars_pat (Var_local_pat n) = [n] ∧
  free_vars_pat (Var_global_pat _) = [] ∧
  free_vars_pat (Fun_pat e) = lshift 1 (free_vars_pat e) ∧
  free_vars_pat (Uapp_pat _ e) = free_vars_pat e ∧
  free_vars_pat (App_pat _ e1 e2) = lunion (free_vars_pat e1) (free_vars_pat e2) ∧
  free_vars_pat (If_pat e1 e2 e3) = lunion (free_vars_pat e1) (lunion (free_vars_pat e2) (free_vars_pat e3)) ∧
  free_vars_pat (Let_pat e1 e2) = lunion (free_vars_pat e1) (lshift 1 (free_vars_pat e2)) ∧
  free_vars_pat (Seq_pat e1 e2) = lunion (free_vars_pat e1) (free_vars_pat e2) ∧
  free_vars_pat (Letrec_pat es e) = lunion (free_vars_defs_pat (LENGTH es) es) (lshift (LENGTH es) (free_vars_pat e)) ∧
  free_vars_pat (Extend_global_pat _) = [] ∧
  free_vars_list_pat [] = [] ∧
  free_vars_list_pat (e::es) = lunion (free_vars_pat e) (free_vars_list_pat es) ∧
  free_vars_defs_pat _ [] = [] ∧
  free_vars_defs_pat n (e::es) = lunion (lshift (n+1) (free_vars_pat e)) (free_vars_defs_pat n es)`
(WF_REL_TAC`inv_image $< (λx. case x of
  | INL e => exp_pat_size e
  | INR (INL es) => exp_pat1_size es
  | INR (INR (_,es)) => exp_pat1_size es)`)
val _ = export_rewrites["free_vars_pat_def"]

val free_vars_defs_pat_MAP = store_thm("free_vars_defs_pat_MAP",
  ``set (free_vars_defs_pat n es) = set (lshift (n+1) (free_vars_list_pat es))``,
  Induct_on`es`>>simp[] >> fs[EXTENSION] >>
  rw[EQ_IMP_THM] >> simp[] >> metis_tac[])

val free_vars_list_pat_MAP = store_thm("free_vars_list_pat_MAP",
  ``∀es. set (free_vars_list_pat es) = set (FLAT (MAP free_vars_pat es))``,
  Induct >> simp[])
val _ = export_rewrites["free_vars_defs_pat_MAP","free_vars_list_pat_MAP"]

val free_vars_pat_sIf = store_thm("free_vars_pat_sIf",
  ``∀e1 e2 e3. set (free_vars_pat (sIf_pat e1 e2 e3)) ⊆ set (free_vars_pat (If_pat e1 e2 e3))``,
  rw[sIf_pat_def] >>
  BasicProvers.CASE_TAC >> simp[SUBSET_DEF] >>
  BasicProvers.CASE_TAC >> simp[] >> rw[])

val free_vars_ground_pat = store_thm("free_vars_ground_pat",
  ``(∀e n. ground_pat n e ⇒ set (free_vars_pat e) ⊆ count n) ∧
    (∀es n. ground_list_pat n es ⇒ set (free_vars_list_pat es) ⊆ count n)``,
  ho_match_mp_tac(TypeBase.induction_of(``:exp_pat``)) >>
  simp[] >>
  simp[SUBSET_DEF,PULL_EXISTS] >>
  rw[] >> res_tac >>
  DECIDE_TAC)

val free_vars_pat_sLet = store_thm("free_vars_pat_sLet",
  ``∀e1 e2. set (free_vars_pat (sLet_pat e1 e2)) ⊆ set (free_vars_pat (Let_pat e1 e2))``,
  rw[sLet_pat_thm,SUBSET_DEF] >>
  imp_res_tac(SIMP_RULE(srw_ss())[SUBSET_DEF]free_vars_ground_pat) >>
  fs[])

val free_vars_pat_Let_Els = store_thm("free_vars_pat_Let_Els",
  ``∀n k e. set (free_vars_pat (Let_Els_pat n k e)) ⊆ {x | x = n ∨ ∃y. MEM y (free_vars_pat e) ∧ k ≤ y ∧ x = y - k}``,
  ho_match_mp_tac Let_Els_pat_ind >>
  simp[Let_Els_pat_def,arithmeticTheory.ADD1,SUBSET_DEF] >>
  gen_tac >> Cases >> simp[Let_Els_pat_def] >> rw[] >>
  imp_res_tac(SIMP_RULE(srw_ss())[SUBSET_DEF]free_vars_pat_sLet) >>
  fs[] >> simp[] >- metis_tac[] >>
  res_tac >> simp[] >>
  disj2_tac >> HINT_EXISTS_TAC >> simp[])

val free_vars_pat_to_pat = store_thm("free_vars_pat_to_pat",
  ``(∀p. set (free_vars_pat (pat_to_pat p)) ⊆ {0}) ∧
    (∀n ps. set (free_vars_pat (pats_to_pat n ps)) ⊆ {x | n ≤ x ∧ x < n + LENGTH ps})``,
  ho_match_mp_tac pat_to_pat_ind >>
  simp[pat_to_pat_def] >>
  strip_tac >- (
    simp[SUBSET_DEF] >>
    rpt strip_tac >>
    imp_res_tac(SIMP_RULE(srw_ss())[SUBSET_DEF]free_vars_pat_sIf) >> fs[] >>
    imp_res_tac(SIMP_RULE(srw_ss())[SUBSET_DEF]free_vars_pat_Let_Els) >> fs[] >>
    res_tac >> simp[] ) >>
  strip_tac >- (
    simp[SUBSET_DEF] >>
    rpt strip_tac >>
    imp_res_tac(SIMP_RULE(srw_ss())[SUBSET_DEF]free_vars_pat_sLet) >> fs[] ) >>
  rw[SUBSET_DEF] >>
  imp_res_tac(SIMP_RULE(srw_ss())[SUBSET_DEF]free_vars_pat_sIf) >> fs[] >>
  imp_res_tac(SIMP_RULE(srw_ss())[SUBSET_DEF]free_vars_pat_sLet) >> fs[] >>
  rw[] >> res_tac >> simp[])

val free_vars_pat_exp_to_pat = store_thm("free_vars_pat_exp_to_pat",
  ``(∀ls e.
      IMAGE SOME (free_vars_exh e) ⊆ set ls ⇒
      set (free_vars_pat (exp_to_pat ls e)) ⊆ IMAGE (λx. THE (find_index (SOME x) ls 0)) (free_vars_exh e)) ∧
    (∀ls es.
      IMAGE SOME (free_vars_list_exh es) ⊆ set ls ⇒
      set (free_vars_list_pat (exps_to_pat ls es)) ⊆ IMAGE (λx. THE (find_index (SOME x) ls 0)) (free_vars_list_exh es)) ∧
    (∀ls funs.
      IMAGE SOME (free_vars_defs_exh funs) ⊆ set ls ⇒
      set (free_vars_list_pat (funs_to_pat ls funs)) ⊆ IMAGE (λx. THE (find_index (SOME x) ls 0)) (free_vars_defs_exh funs)) ∧
    (∀ls pes.
      IMAGE SOME (free_vars_pes_exh pes) ⊆ set ls ∧ ls ≠ [] ∧ (HD ls = NONE) ⇒
      set (free_vars_pat (pes_to_pat ls pes)) ⊆ IMAGE (λx. THE (find_index (SOME x) ls 0)) (free_vars_pes_exh pes))``,
  ho_match_mp_tac exp_to_pat_ind >> simp[SUBSET_DEF,PULL_EXISTS] >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >> strip_tac >> fs[find_index_def] >>
    fs[Q.SPEC`1`(CONV_RULE(RESORT_FORALL_CONV List.rev)find_index_shift_0)] >>
    gen_tac >> strip_tac >- metis_tac[] >>
    res_tac >> qpat_assum`m = X`mp_tac >>
    specl_args_of_then``find_index`` (CONV_RULE SWAP_FORALL_CONV find_index_MEM) mp_tac >>
    discharge_hyps >- metis_tac[] >>
    strip_tac >> fs[] >>
    metis_tac[optionTheory.THE_DEF] ) >>
  strip_tac >- (
    simp[optionTheory.option_case_compute] >>
    rw[] >>
    metis_tac[find_index_NOT_MEM,optionTheory.IS_SOME_DEF,optionTheory.option_CASES] ) >>
  strip_tac >- (
    simp[find_index_def] >>
    rpt gen_tac >> strip_tac >> strip_tac >>
    fs[Q.SPEC`1`(CONV_RULE(RESORT_FORALL_CONV List.rev)find_index_shift_0)] >>
    gen_tac >> strip_tac >>
    qpat_assum`p ⇒ q`mp_tac >>
    discharge_hyps >- metis_tac[] >>
    disch_then(qspec_then`m`mp_tac) >>
    simp[] >> strip_tac >>
    BasicProvers.EVERY_CASE_TAC >> fs[] >>
    HINT_EXISTS_TAC >> simp[] >>
    specl_args_of_then``find_index`` (CONV_RULE SWAP_FORALL_CONV find_index_MEM) mp_tac >>
    discharge_hyps >- metis_tac[] >> strip_tac >> fs[] ) >>
  strip_tac >- metis_tac[] >>
  strip_tac >- (
    rpt gen_tac >> rpt strip_tac >>
    imp_res_tac((SIMP_RULE(srw_ss())[SUBSET_DEF]free_vars_pat_sIf)) >>
    metis_tac[] ) >>
  strip_tac >- (
    simp[find_index_def] >>
    rpt gen_tac >> rpt strip_tac >>
    fs[Q.SPEC`1`(CONV_RULE(RESORT_FORALL_CONV List.rev)find_index_shift_0)] >>
    imp_res_tac((SIMP_RULE(srw_ss())[SUBSET_DEF]free_vars_pat_sLet)) >- metis_tac[] >>
    res_tac >> qpat_assum`m = X`mp_tac >>
    specl_args_of_then``find_index`` (CONV_RULE SWAP_FORALL_CONV find_index_MEM) mp_tac >>
    discharge_hyps >- metis_tac[] >>
    strip_tac >> fs[] >>
    metis_tac[optionTheory.THE_DEF] ) >>
  strip_tac >- (
    simp[find_index_def] >>
    rpt gen_tac >> rpt strip_tac >>
    fs[Q.SPEC`1`(CONV_RULE(RESORT_FORALL_CONV List.rev)find_index_shift_0)] >>
    imp_res_tac((SIMP_RULE(srw_ss())[SUBSET_DEF]free_vars_pat_sLet)) >- metis_tac[] >>
    qpat_assum`p ⇒ q`mp_tac >> discharge_hyps >- metis_tac[] >>
    disch_then(qspec_then`m`mp_tac) >>
    simp[] >> strip_tac >>
    BasicProvers.EVERY_CASE_TAC >> fs[] >>
    specl_args_of_then``find_index`` (CONV_RULE SWAP_FORALL_CONV find_index_MEM) mp_tac >>
    discharge_hyps >- metis_tac[] >> strip_tac >> fs[] >>
    metis_tac[optionTheory.THE_DEF] ) >>
  strip_tac >- metis_tac[] >>
  strip_tac >- (
    simp[pairTheory.pair_CASE_def,PULL_EXISTS] >>
    rpt gen_tac >> rpt strip_tac >>
    cheat ) >>
  strip_tac >- metis_tac[] >>
  strip_tac >- cheat >>
  strip_tac >- (
    rw[] >>
    BasicProvers.EVERY_CASE_TAC >> fs[] >>
    Cases_on`ls`>>fs[Once row_to_pat_nil,LET_THM,UNCURRY] >>
    simp[find_index_def] >>
    simp[Once find_index_shift_0] >>
    rw[] >> fs[] >>
    cheat ) >>
  rw[] >>
  Cases_on`ls`>>fs[] >> rw[] >>
  fs[find_index_def,PULL_EXISTS] >>
  reverse(imp_res_tac(SIMP_RULE(srw_ss())[SUBSET_DEF]free_vars_pat_sIf) >> fs[])
  >- metis_tac[]
  >- (
    BasicProvers.EVERY_CASE_TAC >> fs[] >>
    cheat ) >>
  cheat)

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
  strip_tac >- rw[] >>
  strip_tac >- (
    rw[free_vars_list_MAP] >>
    fsrw_tac[DNF_ss][Once EXTENSION,MEM_FLAT,MEM_MAP] >>
    fsrw_tac[DNF_ss][MEM_MAP,EQ_IMP_THM] >>
    metis_tac[] ) >>
  strip_tac >- (
    rw[EXTENSION] >- (
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
    metis_tac[]) >>
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
  strip_tac >- rw[] >>
  strip_tac >- rw[])
val _ = export_rewrites["free_vars_mkshift"]

val free_vars_shift = store_thm("free_vars_shift",
  ``set (free_vars (shift k n e)) = IMAGE (λv. if v < n then v else k + v) (set (free_vars e))``,
  simp[shift_def])
val _ = export_rewrites["free_vars_shift"]

val free_vars_exp_to_Cexp = store_thm("free_vars_exp_to_Cexp",
  ``(∀e. set (free_vars (exp_to_Cexp e)) = set (free_vars_pat e)) ∧
    (∀es. set (free_vars_list (exps_to_Cexps es)) = set (free_vars_list_pat es))``,
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

val (closed_pat_rules,closed_pat_ind,closed_pat_cases) = Hol_reln`
(closed_pat (Litv_pat l)) ∧
(EVERY (closed_pat) vs ⇒ closed_pat (Conv_pat cn vs)) ∧
(EVERY (closed_pat) env ∧ set (free_vars_pat b) ⊆ count (LENGTH env + 1)
⇒ closed_pat (Closure_pat env b)) ∧
(EVERY (closed_pat) env ∧ d < LENGTH defs ∧
 EVERY (λe. set (free_vars_pat e) ⊆ count (LENGTH env + LENGTH defs + 1)) defs
⇒ closed_pat (Recclosure_pat env defs d)) ∧
(closed_pat (Loc_pat n))`;

val closed_pat_lit_loc_conv = store_thm("closed_pat_lit_loc_conv",
  ``closed_pat (Litv_pat l) ∧ closed_pat (Loc_pat n) ∧
    (closed_pat (Conv_pat a bs) ⇔ EVERY closed_pat bs)``,
  rw[closed_pat_cases])
val _ = export_rewrites["closed_pat_lit_loc_conv"]

val csg_closed_pat_def = Define`
  csg_closed_pat csg ⇔
    EVERY closed_pat (SND(FST csg)) ∧
    EVERY (OPTION_EVERY closed_pat) (SND csg)`

val evaluate_pat_closed = store_thm("evaluate_pat_closed",
  ``(∀ck env s e res. evaluate_pat ck env s e res ⇒
       set (free_vars_pat e) ⊆ count (LENGTH env) ∧
       EVERY closed_pat env ∧ csg_closed_pat s ⇒
       csg_closed_pat (FST res) ∧
       every_result closed_pat closed_pat (SND res)) ∧
    (∀ck env s es res. evaluate_list_pat ck env s es res ⇒
       set (free_vars_list_pat es) ⊆ count (LENGTH env) ∧
       EVERY closed_pat env ∧ csg_closed_pat s ⇒
       csg_closed_pat (FST res) ∧
       every_result (EVERY closed_pat) closed_pat (SND res))``,
  ho_match_mp_tac evaluate_pat_ind >> simp[] >>
  strip_tac >- (
    rpt gen_tac >> ntac 2 strip_tac >>
    first_x_assum match_mp_tac >> fs[] >>
    fsrw_tac[ARITH_ss][SUBSET_DEF,PULL_EXISTS] >>
    Cases>>simp[ADD1] >> rw[] >>
    res_tac >> fsrw_tac[ARITH_ss][]) >>
  strip_tac >- simp[EVERY_MEM,MEM_EL,PULL_EXISTS] >>
  strip_tac >- (
    simp[csg_closed_pat_def,EVERY_MEM,MEM_EL,PULL_EXISTS] >>
    rw[] >> first_x_assum(qspec_then`n`mp_tac) >> simp[] ) >>
  strip_tac >- (
    simp[Once closed_pat_cases,SUBSET_DEF,PULL_EXISTS] >>
    rpt gen_tac >> strip_tac >>
    Cases >> simp[] ) >>
  strip_tac >- (
    gen_tac >> Cases >>
    gen_tac >> Cases >>
    simp[do_uapp_pat_def
        ,semanticPrimitivesTheory.store_alloc_def
        ,semanticPrimitivesTheory.store_lookup_def] >>
    rw[] >> fs[] >>
    fs[csg_closed_pat_def] >>
    fs[EVERY_MEM,MEM_EL,PULL_EXISTS] >>
    BasicProvers.EVERY_CASE_TAC >> fs[] >>
    rw[EL_LUPDATE] >>
    rw[EVERY_MEM,MEM_EL,PULL_EXISTS] ) >>
  strip_tac >- (
    ntac 2 gen_tac >> Cases >>
    ntac 2 gen_tac >> Cases >>TRY(Cases_on`l:lit`)>>
    simp[do_app_pat_def] >>
    Cases >> TRY(Cases_on`l:lit`)>>
    simp[bigStepTheory.dec_count_def] >>
    rpt gen_tac >> ntac 2 strip_tac >> fs[] >>
    TRY(qpat_assum`X = SOME Y`mp_tac >>
        BasicProvers.CASE_TAC >> strip_tac >>
        rpt BasicProvers.VAR_EQ_TAC) >>
    first_x_assum match_mp_tac >>
    simp[exn_env_pat_def] >>
    TRY (
      rator_x_assum`closed_pat`mp_tac >>
      simp[Once closed_pat_cases] >>
      simp[ADD1] >> rfs[csg_closed_pat_def] ) >>
    fs[semanticPrimitivesTheory.store_assign_def] >>
    rpt BasicProvers.VAR_EQ_TAC >>
    TRY (
      rfs[csg_closed_pat_def,EVERY_MEM,PULL_EXISTS,MEM_EL,EL_LUPDATE] >>
      rw[] >> rw[EVERY_MEM,MEM_EL,PULL_EXISTS] >> NO_TAC) >>
    simp[build_rec_env_pat_def,EVERY_GENLIST] >>
    simp[EVERY_MEM,MEM_EL,PULL_EXISTS,AC ADD_ASSOC ADD_SYM] >>
    strip_tac >>
    simp[Once closed_pat_cases] >>
    simp[EVERY_MEM,MEM_EL,PULL_EXISTS,AC ADD_ASSOC ADD_SYM] ) >>
  strip_tac >- (
    ntac 3 gen_tac >>
    Cases >> simp[do_app_pat_def] ) >>
  strip_tac >- (
    ntac 4 gen_tac >>
    Cases >> simp[do_if_pat_def] >>
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
    fsrw_tac[DNF_ss][SUBSET_DEF,ADD1,build_rec_env_pat_def,EVERY_GENLIST] >>
    conj_tac >- (
      rw[] >>
      Cases_on`x < LENGTH funs`>>simp[] >>
      REWRITE_TAC[Once ADD_SYM] >>
      first_x_assum match_mp_tac >>
      simp[] ) >>
    simp[Once closed_pat_cases] >>
    fs[EVERY_MEM,SUBSET_DEF,MEM_FLAT,PULL_EXISTS,MEM_MAP] >>
    rw[] >>
    fsrw_tac[ARITH_ss][AC ADD_ASSOC ADD_SYM] >>
    Cases_on`x < LENGTH funs + 1`>>simp[] >>
    first_x_assum match_mp_tac >>
    simp[] >> metis_tac[] ) >>
  simp[csg_closed_pat_def,EVERY_GENLIST])

val v_to_pat_closed = store_thm("v_to_pat_closed",
  ``(∀v. closed_exh v ⇒ closed_pat (v_to_pat v)) ∧
    (∀vs. EVERY closed_exh vs ⇒  EVERY closed_pat (vs_to_pat vs))``,
  ho_match_mp_tac v_to_pat_ind >>
  simp[v_to_exh_def] >>
  rw[] >- (
    simp[Once closed_pat_cases] >>
    pop_assum mp_tac >>
    simp[Once closed_exh_cases] >>
    strip_tac >>
    specl_args_of_then``exp_to_pat``(CONJUNCT1 free_vars_pat_exp_to_pat) mp_tac >>
    fs[SUBSET_DEF,PULL_EXISTS,EVERY_MAP,MEM_MAP,EVERY_MEM] >> rw[] >>
    res_tac >> rw[] >>
    qho_match_abbrev_tac`THE (find_index a ls n) < z` >>
    qho_match_abbrev_tac`P (THE (find_index a ls n))` >>
    match_mp_tac THE_find_index_suff >>
    simp[Abbr`P`,Abbr`n`,Abbr`z`,Abbr`ls`,Abbr`a`,MEM_MAP] ) >>
  simp[Once closed_pat_cases] >>
  pop_assum mp_tac >>
  simp[Once closed_exh_cases] >>
  strip_tac >>
  simp[funs_to_pat_MAP] >>
  fs[EVERY_MAP,EVERY_MEM,SUBSET_DEF,PULL_FORALL,FORALL_PROD,PULL_EXISTS,MEM_MAP,EXISTS_PROD] >>
  rpt gen_tac >> strip_tac >- metis_tac[] >>
  strip_tac >- (
    qho_match_abbrev_tac`the d (find_index a b c) < d` >>
    qho_match_abbrev_tac`P (the d (find_index a b c))` >>
    match_mp_tac the_find_index_suff >>
    simp[Abbr`P`,Abbr`a`,Abbr`d`,Abbr`c`,Abbr`b`,MEM_MAP] >>
    simp[EXISTS_PROD] >> metis_tac[] ) >>
  strip_tac >>
  specl_args_of_then``exp_to_pat``(CONJUNCT1 free_vars_pat_exp_to_pat) mp_tac >>
  fs[SUBSET_DEF,PULL_EXISTS,EVERY_MAP,MEM_MAP,EVERY_MEM,EXISTS_PROD] >>
  discharge_hyps >- metis_tac[] >> rw[] >>
  res_tac >> rw[] >>
  qho_match_abbrev_tac`THE (find_index a ls n) < z` >>
  qho_match_abbrev_tac`P (THE (find_index a ls n))` >>
  match_mp_tac THE_find_index_suff >>
  simp[Abbr`P`,Abbr`n`,Abbr`z`,Abbr`ls`,Abbr`a`,MEM_MAP,EXISTS_PROD] >>
  metis_tac[])

val free_vars_i2_def = tDefine"free_vars_i2"`
  free_vars_i2 (Raise_i2 e) = free_vars_i2 e ∧
  free_vars_i2 (Handle_i2 e pes) = free_vars_i2 e ∪ free_vars_pes_i2 pes ∧
  free_vars_i2 (Lit_i2 _) = {} ∧
  free_vars_i2 (Con_i2 _ es) = free_vars_list_i2 es ∧
  free_vars_i2 (Var_local_i2 n) = {n} ∧
  free_vars_i2 (Var_global_i2 _) = {} ∧
  free_vars_i2 (Fun_i2 x e) = free_vars_i2 e DIFF {x} ∧
  free_vars_i2 (Uapp_i2 _ e) = free_vars_i2 e ∧
  free_vars_i2 (App_i2 _ e1 e2) = free_vars_i2 e1 ∪ free_vars_i2 e2 ∧
  free_vars_i2 (If_i2 e1 e2 e3) = free_vars_i2 e1 ∪ free_vars_i2 e2 ∪ free_vars_i2 e3 ∧
  free_vars_i2 (Mat_i2 e pes) = free_vars_i2 e ∪ free_vars_pes_i2 pes ∧
  free_vars_i2 (Let_i2 bn e1 e2) = free_vars_i2 e1 ∪ (free_vars_i2 e2 DIFF (case bn of NONE => {} | SOME x => {x})) ∧
  free_vars_i2 (Letrec_i2 defs e) = (free_vars_defs_i2 defs ∪ free_vars_i2 e) DIFF set(MAP FST defs) ∧
  free_vars_i2 (Extend_global_i2 _) = {} ∧
  free_vars_list_i2 [] = {} ∧
  free_vars_list_i2 (e::es) = free_vars_i2 e ∪ free_vars_list_i2 es ∧
  free_vars_defs_i2 [] = {} ∧
  free_vars_defs_i2 ((f,x,e)::ds) = (free_vars_i2 e DIFF {x}) ∪ free_vars_defs_i2 ds ∧
  free_vars_pes_i2 [] = {} ∧
  free_vars_pes_i2 ((p,e)::pes) = (free_vars_i2 e DIFF (set (pat_bindings_i2 p []))) ∪ free_vars_pes_i2 pes`
(WF_REL_TAC`inv_image $< (λx. case x of
  | INL e => exp_i2_size e
  | INR (INL es) => exp_i26_size es
  | INR (INR (INL defs)) => exp_i21_size defs
  | INR (INR (INR pes)) => exp_i23_size pes)`)
val _ = export_rewrites["free_vars_i2_def"]

val free_vars_pes_i2_MAP = store_thm("free_vars_pes_i2_MAP",
  ``∀pes. free_vars_pes_i2 pes = BIGUNION (set (MAP (λ(p,e). free_vars_i2 e DIFF set (pat_bindings_i2 p [])) pes))``,
  Induct >> simp[] >> Cases >> simp[])

val pat_bindings_exh_pat_to_exh = store_thm("pat_bindings_exh_pat_to_exh",
  ``∀p ls. pat_bindings_exh (pat_to_exh p) ls = pat_bindings_i2 p ls``,
  ho_match_mp_tac pat_to_exh_ind >>
  simp[pat_bindings_i2_def,pat_to_exh_def,pat_bindings_exh_def,ETA_AX] >>
  Induct >> simp[pat_bindings_i2_def,pat_bindings_exh_def])
val _ = export_rewrites["pat_bindings_exh_pat_to_exh"]

val free_vars_exh_exp_to_exh = store_thm("free_vars_exh_exp_to_exh",
  ``(∀exh e. free_vars_exh (exp_to_exh exh e) = free_vars_i2 e) ∧
    (∀exh es. free_vars_list_exh (exps_to_exh exh es) = free_vars_list_i2 es) ∧
    (∀exh pes. free_vars_pes_exh (pat_exp_to_exh exh pes) = free_vars_pes_i2 pes) ∧
    (∀exh funs. free_vars_defs_exh (funs_to_exh exh funs) = free_vars_defs_i2 funs)``,
  ho_match_mp_tac exp_to_exh_ind >>
  simp[exp_to_exh_def] >>
  conj_tac >- (
    rw[add_default_def,pat_bindings_i2_def,free_vars_pes_i2_MAP] ) >>
  conj_tac >- (
    rw[add_default_def,pat_bindings_i2_def,free_vars_pes_i2_MAP] ) >>
  rw[funs_to_exh_MAP,MAP_MAP_o,combinTheory.o_DEF,UNCURRY,ETA_AX] )
val _ = export_rewrites["free_vars_exh_exp_to_exh"]

val (closed_i2_rules,closed_i2_ind,closed_i2_cases) = Hol_reln`
(closed_i2 (Litv_i2 l)) ∧
(EVERY (closed_i2) vs ⇒ closed_i2 (Conv_i2 cn vs)) ∧
(EVERY (closed_i2) (MAP SND env) ∧ free_vars_i2 b ⊆ {x} ∪ set (MAP FST env)
⇒ closed_i2 (Closure_i2 env x b)) ∧
(EVERY (closed_i2) (MAP SND env) ∧ MEM d (MAP FST defs) ∧
 EVERY (λ(f,x,e). free_vars_i2 e ⊆ {x} ∪ set (MAP FST defs) ∪ set (MAP FST env)) defs
⇒ closed_i2 (Recclosure_i2 env defs d)) ∧
(closed_i2 (Loc_i2 n))`;

val closed_i2_lit_loc_conv = store_thm("closed_i2_lit_loc_conv",
  ``closed_i2 (Litv_i2 l) ∧ closed_i2 (Loc_i2 n) ∧
    (closed_i2 (Conv_i2 a bs) ⇔ EVERY closed_i2 bs)``,
  rw[closed_i2_cases])
val _ = export_rewrites["closed_i2_lit_loc_conv"]

val v_to_exh_closed = store_thm("v_to_exh_closed",
  ``(∀exh v. closed_i2 v ⇒ closed_exh (v_to_exh exh v)) ∧
    (∀exh vs. EVERY closed_i2 vs ⇒  EVERY closed_exh (vs_to_exh exh vs)) ∧
    (∀exh env. EVERY closed_i2 (MAP SND env) ⇒ EVERY closed_exh (MAP SND (env_to_exh exh env)))``,
  ho_match_mp_tac v_to_exh_ind >> simp[v_to_exh_def] >>
  conj_tac >- (
    rpt gen_tac >> strip_tac >>
    simp[Once closed_i2_cases] >>
    simp[Once closed_exh_cases] >>
    simp[env_to_exh_MAP,MAP_MAP_o,combinTheory.o_DEF,UNCURRY,ETA_AX] ) >>
  rpt gen_tac >> strip_tac >>
  simp[Once closed_i2_cases] >>
  simp[Once closed_exh_cases] >>
  simp[funs_to_exh_MAP,EVERY_MAP,MAP_MAP_o,UNCURRY,combinTheory.o_DEF,ETA_AX] >>
  simp[LAMBDA_PROD,env_to_exh_MAP,MAP_MAP_o,UNCURRY,combinTheory.o_DEF,FST_pair])

val free_vars_i1_def = tDefine"free_vars_i1"`
  free_vars_i1 (Raise_i1 e) = free_vars_i1 e ∧
  free_vars_i1 (Handle_i1 e pes) = free_vars_i1 e ∪ free_vars_pes_i1 pes ∧
  free_vars_i1 (Lit_i1 _) = {} ∧
  free_vars_i1 (Con_i1 _ es) = free_vars_list_i1 es ∧
  free_vars_i1 (Var_local_i1 n) = {n} ∧
  free_vars_i1 (Var_global_i1 _) = {} ∧
  free_vars_i1 (Fun_i1 x e) = free_vars_i1 e DIFF {x} ∧
  free_vars_i1 (Uapp_i1 _ e) = free_vars_i1 e ∧
  free_vars_i1 (App_i1 _ e1 e2) = free_vars_i1 e1 ∪ free_vars_i1 e2 ∧
  free_vars_i1 (If_i1 e1 e2 e3) = free_vars_i1 e1 ∪ free_vars_i1 e2 ∪ free_vars_i1 e3 ∧
  free_vars_i1 (Mat_i1 e pes) = free_vars_i1 e ∪ free_vars_pes_i1 pes ∧
  free_vars_i1 (Let_i1 bn e1 e2) = free_vars_i1 e1 ∪ (free_vars_i1 e2 DIFF (case bn of NONE => {} | SOME x => {x})) ∧
  free_vars_i1 (Letrec_i1 defs e) = (free_vars_defs_i1 defs ∪ free_vars_i1 e) DIFF set(MAP FST defs) ∧
  free_vars_list_i1 [] = {} ∧
  free_vars_list_i1 (e::es) = free_vars_i1 e ∪ free_vars_list_i1 es ∧
  free_vars_defs_i1 [] = {} ∧
  free_vars_defs_i1 ((f,x,e)::ds) = (free_vars_i1 e DIFF {x}) ∪ free_vars_defs_i1 ds ∧
  free_vars_pes_i1 [] = {} ∧
  free_vars_pes_i1 ((p,e)::pes) = (free_vars_i1 e DIFF (set (pat_bindings p []))) ∪ free_vars_pes_i1 pes`
(WF_REL_TAC`inv_image $< (λx. case x of
  | INL e => exp_i1_size e
  | INR (INL es) => exp_i16_size es
  | INR (INR (INL defs)) => exp_i11_size defs
  | INR (INR (INR pes)) => exp_i13_size pes)`)
val _ = export_rewrites["free_vars_i1_def"]

val (closed_i1_rules,closed_i1_ind,closed_i1_cases) = Hol_reln`
(closed_i1 (Litv_i1 l)) ∧
(EVERY (closed_i1) vs ⇒ closed_i1 (Conv_i1 cn vs)) ∧
(EVERY (closed_i1) (MAP SND env) ∧ free_vars_i1 b ⊆ {x} ∪ set (MAP FST env)
⇒ closed_i1 (Closure_i1 (envC,env) x b)) ∧
(EVERY (closed_i1) (MAP SND env) ∧ MEM d (MAP FST defs) ∧
 EVERY (λ(f,x,e). free_vars_i1 e ⊆ {x} ∪ set (MAP FST defs) ∪ set (MAP FST env)) defs
⇒ closed_i1 (Recclosure_i1 (envC,env) defs d)) ∧
(closed_i1 (Loc_i1 n))`;

val closed_i1_lit_loc_conv = store_thm("closed_i1_lit_loc_conv",
  ``closed_i1 (Litv_i1 l) ∧ closed_i1 (Loc_i1 n) ∧
    (closed_i1 (Conv_i1 a bs) ⇔ EVERY closed_i1 bs)``,
  rw[closed_i1_cases])
val _ = export_rewrites["closed_i1_lit_loc_conv"]

val pat_bindings_i2_pat_to_i2 = store_thm("pat_bindings_i2_pat_to_i2",
  ``∀t p ls. pat_bindings_i2 (pat_to_i2 t p) ls = pat_bindings p ls``,
  ho_match_mp_tac pat_to_i2_ind >>
  simp[pat_bindings_def,pat_to_i2_def,pat_bindings_i2_def,ETA_AX] >>
  gen_tac >> Induct >> simp[pat_bindings_def,pat_bindings_i2_def])
val _ = export_rewrites["pat_bindings_i2_pat_to_i2"]

val free_vars_i2_exp_to_i2 = store_thm("free_vars_i2_exp_to_i2",
  ``(∀exh e. free_vars_i2 (exp_to_i2 exh e) = free_vars_i1 e) ∧
    (∀exh es. free_vars_list_i2 (exps_to_i2 exh es) = free_vars_list_i1 es) ∧
    (∀exh pes. free_vars_pes_i2 (pat_exp_to_i2 exh pes) = free_vars_pes_i1 pes) ∧
    (∀exh funs. free_vars_defs_i2 (funs_to_i2 exh funs) = free_vars_defs_i1 funs)``,
  ho_match_mp_tac exp_to_i2_ind >>
  simp[exp_to_i2_def] >>
  rw[funs_to_i2_MAP,MAP_MAP_o,combinTheory.o_DEF,UNCURRY,ETA_AX] )
val _ = export_rewrites["free_vars_i2_exp_to_i2"]

val v_to_i2_closed = store_thm("v_to_i2_closed",
  ``(∀g v1 v2. v_to_i2 g v1 v2 ⇒ closed_i1 v1 ⇒ closed_i2 v2) ∧
    (∀g v1 v2. vs_to_i2 g v1 v2 ⇒ EVERY closed_i1 v1 ⇒ EVERY closed_i2 v2) ∧
    (∀g v1 v2. env_to_i2 g v1 v2 ⇒
      set (MAP FST v1) = set (MAP FST v2) ∧
      (EVERY closed_i1 (MAP SND v1) ⇒ EVERY closed_i2 (MAP SND v2)))``,
  ho_match_mp_tac v_to_i2_ind >> simp[] >>
  conj_tac >- (
    rpt gen_tac >> strip_tac >>
    simp[Once closed_i1_cases] >>
    simp[Once closed_i2_cases] ) >>
  rpt gen_tac >> strip_tac >>
  simp[Once closed_i1_cases] >>
  simp[Once closed_i2_cases] >>
  simp[funs_to_i2_MAP,EVERY_MAP,MAP_MAP_o,UNCURRY,combinTheory.o_DEF,ETA_AX] >>
  simp[LAMBDA_PROD,MAP_MAP_o,UNCURRY,combinTheory.o_DEF,FST_pair])

val FV_def = tDefine "FV"`
  (FV (Raise e) = FV e) ∧
  (FV (Handle e pes) = FV e ∪ FV_pes pes) ∧
  (FV (Lit _) = {}) ∧
  (FV (Con _ ls) = FV_list ls) ∧
  (FV (Var id) = {id}) ∧
  (FV (Fun x e) = FV e DIFF {Short x}) ∧
  (FV (Uapp _ e) = FV e) ∧
  (FV (App _ e1 e2) = FV e1 ∪ FV e2) ∧
  (FV (Log _ e1 e2) = FV e1 ∪ FV e2) ∧
  (FV (If e1 e2 e3) = FV e1 ∪ FV e2 ∪ FV e3) ∧
  (FV (Mat e pes) = FV e ∪ FV_pes pes) ∧
  (FV (Let xo e b) = FV e ∪ (FV b DIFF (case xo of NONE => {} | SOME x => {Short x}))) ∧
  (FV (Letrec defs b) = FV_defs defs ∪ FV b DIFF set (MAP (Short o FST) defs)) ∧
  (FV_list [] = {}) ∧
  (FV_list (e::es) = FV e ∪ FV_list es) ∧
  (FV_pes [] = {}) ∧
  (FV_pes ((p,e)::pes) =
     (FV e DIFF (IMAGE Short (set (pat_bindings p [])))) ∪ FV_pes pes) ∧
  (FV_defs [] = {}) ∧
  (FV_defs ((_,x,e)::defs) =
     (FV e DIFF {Short x}) ∪ FV_defs defs)`
  (WF_REL_TAC `inv_image $< (λx. case x of
     | INL e => exp_size e
     | INR (INL es) => exp6_size es
     | INR (INR (INL pes)) => exp3_size pes
     | INR (INR (INR (defs))) => exp1_size defs)`)
val _ = export_rewrites["FV_def"]

val _ = Parse.overload_on("SFV",``λe. {x | Short x ∈ FV e}``)

val (closed_rules,closed_ind,closed_cases) = Hol_reln`
(closed (Litv l)) ∧
(EVERY closed vs ⇒ closed (Conv cn vs)) ∧
(EVERY closed (MAP SND envE) ∧
 EVERY closed (MAP SND (FLAT (MAP SND envM))) ∧
 FV b ⊆ (IMAGE Short ({x} ∪ set (MAP FST envE))) ∪ { Long mn x | ∃env. MEM (mn,env) envM ∧ MEM x (MAP FST env)}
⇒ closed (Closure (envM,envC,envE) x b)) ∧
(EVERY closed (MAP SND envE) ∧
 EVERY closed (MAP SND (FLAT (MAP SND envM))) ∧
 MEM d (MAP FST defs) ∧
 EVERY (λ(f,x,e). FV e ⊆ (IMAGE Short ({x} ∪ set (MAP FST defs) ∪ set (MAP FST envE))) ∪
                         { Long mn x | ∃env. MEM (mn,env) envM ∧ MEM x (MAP FST env) }) defs
⇒ closed (Recclosure (envM,envC,envE) defs d)) ∧
(closed (Loc n))`;

val closed_lit_loc_conv = store_thm("closed_lit_loc_conv",
  ``closed (Litv l) ∧ closed (Loc n) ∧
    (closed (Conv a bs) ⇔ EVERY closed bs)``,
  rw[closed_cases])
val _ = export_rewrites["closed_lit_loc_conv"]

val FV_defs_MAP = store_thm("FV_defs_MAP",
  ``∀ls. FV_defs ls = BIGUNION (IMAGE (λ(f,x,e). FV e DIFF {Short x}) (set ls))``,
  Induct_on`ls`>>simp[FORALL_PROD])

val free_vars_i1_exp_to_i1 = store_thm("free_vars_i1_exp_to_i1",
  ``(∀menv env e. free_vars_i1 (exp_to_i1 menv env e) = SFV e DIFF FDOM env) ∧
    (∀menv env es. free_vars_list_i1 (exps_to_i1 menv env es) = {x | Short x ∈ FV_list es} DIFF FDOM env) ∧
    (∀menv env pes. free_vars_pes_i1 (pat_exp_to_i1 menv env pes) = {x | Short x ∈ FV_pes pes} DIFF FDOM env) ∧
    (∀menv env funs. free_vars_defs_i1 (funs_to_i1 menv env funs) = {x | Short x ∈ FV_defs funs} DIFF FDOM env)``,
  ho_match_mp_tac exp_to_i1_ind >>
  simp[exp_to_i1_def] >> rpt conj_tac >>
  TRY (
    rpt gen_tac >> strip_tac >>
    TRY (BasicProvers.CASE_TAC >> fs[]) >>
    ONCE_REWRITE_TAC[EXTENSION] >>
    simp[] >> metis_tac[] ) >>
  TRY (
    rpt gen_tac >> BasicProvers.CASE_TAC >>
    fs[FLOOKUP_DEF] >> rw[] >> NO_TAC)
  >- (
    rpt gen_tac >> strip_tac >>
    simp[funs_to_i1_MAP] >>
    simp[MAP_MAP_o,FST_triple,combinTheory.o_DEF,UNCURRY,ETA_AX] >>
    ONCE_REWRITE_TAC[EXTENSION] >>
    simp[MEM_MAP,FDOM_FOLDR_DOMSUB] >>
    simp[FV_defs_MAP,PULL_EXISTS,EXISTS_PROD,MEM_MAP,FORALL_PROD] >>
    metis_tac[] )
  >- (
    rpt gen_tac >> strip_tac >>
    simp[FDOM_FOLDR_DOMSUB] >>
    ONCE_REWRITE_TAC[EXTENSION] >>
    simp[] >> metis_tac[] ))
val _ = export_rewrites["free_vars_i1_exp_to_i1"]

val v_to_i1_closed = store_thm("v_to_i1_closed",
  ``(∀g v1 v2. v_to_i1 g v1 v2 ⇒ closed v1 ⇒ closed_i1 v2) ∧
    (∀g v1 v2. vs_to_i1 g v1 v2 ⇒ EVERY closed v1 ⇒ EVERY closed_i1 v2) ∧
    (∀g v1 v2. env_to_i1 g v1 v2 ⇒
      set (MAP FST v1) = set (MAP FST v2) ∧
      (EVERY closed (MAP SND v1) ⇒ EVERY closed_i1 (MAP SND v2))) ∧
    (∀g m s e. global_env_inv_flat g m s e ⇒ T) ∧
    (∀g mods tops menv s env. global_env_inv g mods tops menv s env ⇒ T)``,
  ho_match_mp_tac v_to_i1_ind >> simp[] >>
  conj_tac >- (
    rpt gen_tac >> strip_tac >>
    simp[Once closed_cases] >>
    simp[Once closed_i1_cases] >>
    fs[SUBSET_DEF,PULL_EXISTS,FDOM_DRESTRICT] >>
    rw[] >> res_tac >> fs[] >> metis_tac[]) >>
  conj_tac >- (
    rpt gen_tac >> strip_tac >>
    simp[Once closed_cases] >>
    simp[Once closed_i1_cases] >>
    fs[SUBSET_DEF,PULL_EXISTS,FDOM_DRESTRICT] >>
    simp[funs_to_i1_MAP,MAP_MAP_o,combinTheory.o_DEF,UNCURRY,ETA_AX,EVERY_MAP] >>
    strip_tac >>
    match_mp_tac (MP_CANON (GEN_ALL MONO_EVERY)) >>
    HINT_EXISTS_TAC >> simp[] >>
    simp[FORALL_PROD,PULL_EXISTS,PULL_FORALL,FDOM_DRESTRICT] >>
    rw[] >> res_tac >> fs[] >>
    metis_tac[] ) >>
  rpt gen_tac >> strip_tac >>
  simp[Once closed_cases] >>
  simp[Once closed_i1_cases] >>
  strip_tac >>
  pop_assum mp_tac >>
  simp[EVERY_MEM] >>
  disch_then(qspec_then`x,y,e`mp_tac) >>
  discharge_hyps >- metis_tac[find_recfun_lookup,libPropsTheory.lookup_in3] >>
  simp[SUBSET_DEF,PULL_EXISTS] >>
  strip_tac >>
  qx_gen_tac`z` >> strip_tac >>
  first_x_assum(qspec_then`Short z`mp_tac) >>
  simp[] >>
  fs[FDOM_FUPDATE_LIST] >>
  rw[] >>
  fs[FLOOKUP_DEF,FDOM_FUPDATE_LIST] >>
  metis_tac[SUBSET_DEF] )

val FV_dec_def = Define`
  (FV_dec (Dlet p e) = FV (Mat e [(p,Lit ARB)])) ∧
  (FV_dec (Dletrec defs) = FV (Letrec defs (Lit ARB))) ∧
  (FV_dec (Dtype _) = {}) ∧
  (FV_dec (Dexn _ _) = {})`
val _ = export_rewrites["FV_dec_def"]

val new_dec_vs_def = Define`
  (new_dec_vs (Dtype _) = []) ∧
  (new_dec_vs (Dexn _ _) = []) ∧
  (new_dec_vs (Dlet p e) = pat_bindings p []) ∧
  (new_dec_vs (Dletrec funs) = MAP FST funs)`
val _ = export_rewrites["new_dec_vs_def"]

val _ = Parse.overload_on("new_decs_vs",``λdecs. FLAT (REVERSE (MAP new_dec_vs decs))``)

val FV_decs_def = Define`
  (FV_decs [] = {}) ∧
  (FV_decs (d::ds) = FV_dec d ∪ ((FV_decs ds) DIFF (set (MAP Short (new_dec_vs d)))))`

val FV_top_def = Define`
  (FV_top (Tdec d) = FV_dec d) ∧
  (FV_top (Tmod mn _ ds) = FV_decs ds)`
val _ = export_rewrites["FV_top_def"]

val free_vars_dec_i2_def = Define`
  free_vars_dec_i2 (Dlet_i2 n e) = free_vars_i2 e ∧
  free_vars_dec_i2 (Dletrec_i2 defs) = free_vars_i2 (Letrec_i2 defs (Lit_i2 ARB))`
val _ = export_rewrites["free_vars_dec_i2_def"]

(*
val new_dec_i2_vs_def = Define`
  (new_dec_i2_vs (Dlet_i2 n e) = []) ∧
  (new_dec_i2_vs (Dletrec_i2 funs) = MAP FST funs)`
val _ = export_rewrites["new_dec_i2_vs_def"]
*)

val free_vars_decs_i2_def = Define`
  free_vars_decs_i2 ls = free_vars_i2 (decs_to_i3 0 ls)`

val free_vars_prompt_i2_def = Define`
  free_vars_prompt_i2 (Prompt_i2 ds) = free_vars_decs_i2 ds`
val _ = export_rewrites["free_vars_prompt_i2_def"]

val free_vars_i2_init_globals = store_thm("free_vars_i2_init_globals",
  ``∀ls n. free_vars_i2 (init_globals ls n) = set ls``,
  Induct >> simp[init_globals_def,EXTENSION])
val _ = export_rewrites["free_vars_i2_init_globals"]

val free_vars_i2_init_global_funs = store_thm("free_vars_i2_init_global_funs",
  ``∀ls n. free_vars_i2 (init_global_funs n ls) = BIGUNION (set (MAP (λ(f,x,e). free_vars_i2 (Fun_i2 x e)) ls))``,
  Induct >> simp[FORALL_PROD,init_global_funs_def])

val free_vars_i2_decs_to_i3 = store_thm("free_vars_i2_decs_to_i3",
  ``∀l m. free_vars_i2 (decs_to_i3 m l) = free_vars_decs_i2 l``,
  Induct >> simp[decs_to_i3_def,free_vars_decs_i2_def] >>
  Cases >> simp[pat_bindings_i2_def,pats_bindings_i2_MAP_Pvar_i2] >>
  simp[free_vars_i2_init_global_funs])

val free_vars_i2_prompt_to_i3 = store_thm("free_vars_i2_prompt_to_i3",
  ``∀x s m p n e.
    prompt_to_i3 x s m p = (n,e) ⇒
    free_vars_i2 e = free_vars_prompt_i2 p``,
  rw[prompt_to_i3_def] >>
  BasicProvers.EVERY_CASE_TAC >>
  fs[LET_THM] >> rw[pat_bindings_i2_def] >>
  rw[free_vars_i2_decs_to_i3])

val free_vars_decs_i1_def = Define`
  free_vars_decs_i1 ds = free_vars_decs_i2 (SND(SND(decs_to_i2 ARB ds)))`

val free_vars_prompt_i1_def = Define`
  free_vars_prompt_i1 (Prompt_i1 mn decs) = free_vars_decs_i1 decs`

val free_vars_decs_i2_decs_to_i2_any = store_thm("free_vars_decs_i2_decs_to_i2_any",
  ``∀l a b. free_vars_decs_i2 (SND(SND (decs_to_i2 a l))) =
            free_vars_decs_i2 (SND(SND (decs_to_i2 b l)))``,
  Induct_on`l`>>simp[decs_to_i2_def] >>
  Cases >> simp[UNCURRY] >>
  fs[free_vars_decs_i2_def,decs_to_i3_def] >>
  simp[pat_bindings_i2_def,pats_bindings_i2_MAP_Pvar_i2] >>
  fs[free_vars_i2_decs_to_i3,free_vars_i2_init_global_funs] >>
  fs[EXTENSION,funs_to_i2_MAP,MAP_MAP_o,UNCURRY,combinTheory.o_DEF] >>
  metis_tac[])

val free_vars_prompt_to_i2 = store_thm("free_vars_prompt_to_i2",
  ``∀x p y z p2.
    prompt_to_i2 x p = (y,z,p2) ⇒
    free_vars_prompt_i2 p2 = free_vars_prompt_i1 p``,
  Cases_on`p`>>rw[prompt_to_i2_def,LET_THM,free_vars_prompt_i1_def] >>
  fs[UNCURRY] >> rw[free_vars_decs_i1_def] >>
  metis_tac[free_vars_decs_i2_decs_to_i2_any])

val free_vars_list_i1_MAP_Var_local_i1 = store_thm("free_vars_list_i1_MAP_Var_local_i1",
  ``∀ls. free_vars_list_i1 (MAP Var_local_i1 ls) = set ls``,
  Induct >> simp[EXTENSION])

val free_vars_dec_to_i1 = store_thm("free_vars_dec_to_i1",
  ``∀n a m e d. free_vars_decs_i1 [SND (SND (dec_to_i1 n a m e d))] =
                {x | Short x ∈ FV_dec d} DIFF FDOM e``,
  Cases_on`d`>>
  simp[free_vars_decs_i1_def,dec_to_i1_def,
       decs_to_i2_def,free_vars_decs_i2_def,decs_to_i3_def,
       pat_bindings_i2_def,pats_bindings_i2_MAP_Pvar_i2,
       free_vars_list_i1_MAP_Var_local_i1,
       funs_to_i1_MAP,free_vars_i2_init_global_funs,
       funs_to_i2_MAP,MAP_MAP_o,combinTheory.o_DEF,UNCURRY,
       FV_defs_MAP,PULL_EXISTS] >>
  simp[Once EXTENSION,PULL_EXISTS,MEM_MAP,FST_triple,alloc_defs_GENLIST] >>
  simp[(Q.ISPECL[`FST`,`SND`]FOLDL_FUPDATE_LIST|>SIMP_RULE(srw_ss())[LAMBDA_PROD])] >>
  simp[FDOM_FUPDATE_LIST,MAP_MAP_o,combinTheory.o_DEF,UNCURRY,ETA_AX,MAP_ZIP] >>
  rw[MEM_MAP,PULL_EXISTS] >>
  metis_tac[])

val free_vars_decs_to_i1 = store_thm("free_vars_decs_to_i1",
  ``∀n a m e d. free_vars_decs_i1 (SND (SND (decs_to_i1 n a m e d))) =
                {x | Short x ∈ FV_decs d} DIFF FDOM e``,
  Induct_on`d`>- (
    simp[FV_decs_def,decs_to_i1_def,free_vars_decs_i1_def,free_vars_decs_i2_def] >>
    simp[decs_to_i2_def,decs_to_i3_def] ) >>
  simp[FV_decs_def,decs_to_i1_def,UNCURRY,MEM_MAP] >>
  Cases >> simp[dec_to_i1_def] >>
  fs[free_vars_decs_i1_def,free_vars_decs_i2_def] >>
  fs[free_vars_i2_decs_to_i3] >>
  simp[decs_to_i1_def,decs_to_i2_def] >>
  simp[UNCURRY] >>
  fs[free_vars_decs_i2_def,decs_to_i3_def] >> simp[] >>
  fs[free_vars_i2_decs_to_i3,pat_bindings_i2_def,pats_bindings_i2_MAP_Pvar_i2] >>
  simp[(Q.ISPECL[`FST`,`SND`]FOLDL_FUPDATE_LIST|>SIMP_RULE(srw_ss())[LAMBDA_PROD])] >>
  simp[alloc_defs_GENLIST,free_vars_list_i1_MAP_Var_local_i1,FDOM_FUPDATE_LIST,
       MAP_MAP_o,combinTheory.o_DEF,UNCURRY,ETA_AX,MAP_ZIP,free_vars_i2_init_global_funs] >>
  TRY ( metis_tac[free_vars_decs_i2_decs_to_i2_any] ) >>
  simp[Once EXTENSION] >- metis_tac[] >>
  simp[funs_to_i1_MAP,funs_to_i2_MAP,MAP_MAP_o,combinTheory.o_DEF,UNCURRY
      ,FDOM_FUPDATE_LIST,ETA_AX,MAP_ZIP,FST_triple,MAP_REVERSE,MEM_MAP,PULL_EXISTS] >>
  simp[FV_defs_MAP,PULL_EXISTS,UNCURRY] >>
  metis_tac[])

val FV_top_to_i1 = store_thm("FV_top_to_i1",
  ``∀n m e t x y z p. top_to_i1 n m e t = (x,y,z,p) ⇒
      free_vars_prompt_i1 p = {x | Short x ∈ FV_top t} DIFF FDOM e``,
  Cases_on`t`>>simp[top_to_i1_def,UNCURRY] >>
  simp[free_vars_prompt_i1_def,free_vars_dec_to_i1] >>
  simp[free_vars_decs_to_i1])

val global_env_inv_inclusion = store_thm("global_env_inv_inclusion",
  ``∀genv mods tops menv s env.
     global_env_inv genv mods tops menv s env ⇒
     set (MAP FST env) DIFF s ⊆ FDOM tops ∧
     set (MAP FST menv) ⊆ FDOM mods``,
  rw[Once v_to_i1_cases,SUBSET_DEF] >>
  TRY (
    (libPropsTheory.lookup_notin
     |> SPEC_ALL |> EQ_IMP_RULE |> fst
     |> CONTRAPOS
     |> SIMP_RULE std_ss []
     |> imp_res_tac) >>
    fs[GSYM quantHeuristicsTheory.IS_SOME_EQ_NOT_NONE,IS_SOME_EXISTS] >>
    res_tac >> fs[FLOOKUP_DEF] >> NO_TAC) >>
  last_x_assum mp_tac >>
  simp[Once v_to_i1_cases] >> strip_tac >>
  (libPropsTheory.lookup_notin
   |> SPEC_ALL |> EQ_IMP_RULE |> fst
   |> CONTRAPOS
   |> SIMP_RULE std_ss []
   |> imp_res_tac) >>
  fs[GSYM quantHeuristicsTheory.IS_SOME_EQ_NOT_NONE,IS_SOME_EXISTS] >>
  res_tac >> fs[FLOOKUP_DEF] >> NO_TAC)

val genv_to_pat_closed = store_thm("genv_to_pat_closed",
  ``∀genv2.
    EVERY (OPTION_EVERY closed_exh) genv2 ⇒
    EVERY (OPTION_EVERY closed_pat)
      (MAP (OPTION_MAP v_to_pat) genv2)``,
  simp[EVERY_MEM,MEM_MAP,PULL_EXISTS] >>
  rpt gen_tac >> strip_tac >>
  Cases >> simp[] >> strip_tac >>
  res_tac >> fs[] >>
  metis_tac[v_to_pat_closed])

val genv_to_exh_closed = store_thm("genv_to_exh_closed",
  ``∀exh genv2.
    EVERY (OPTION_EVERY closed_i2) genv2 ⇒
    EVERY (OPTION_EVERY closed_exh)
      (MAP (OPTION_MAP (v_to_exh exh)) genv2)``,
  simp[EVERY_MEM,MEM_MAP,PULL_EXISTS] >>
  rpt gen_tac >> strip_tac >>
  Cases >> simp[] >> strip_tac >>
  res_tac >> fs[] >>
  metis_tac[v_to_exh_closed])

val genv_to_i2_closed = store_thm("genv_to_i2_closed",
  ``∀g x y. genv_to_i2 g x y ⇒ EVERY (OPTION_EVERY closed_i1) x ⇒ EVERY (OPTION_EVERY closed_i2) y``,
  ho_match_mp_tac genv_to_i2_ind >> simp[] >>
  metis_tac[v_to_i2_closed])

val global_env_inv_closed = store_thm("global_env_inv_closed",
  ``∀genv mods tops menv s env.
    global_env_inv genv mods tops menv s env ∧
    EVERY closed (MAP SND env) ∧
    EVERY closed (MAP SND (FLAT (MAP SND menv))) ∧
    (∀n. n < LENGTH genv ∧ IS_SOME (EL n genv) ⇒
         (∃x. x ∉ s ∧ IS_SOME (lookup x env) ∧ FLOOKUP tops x = SOME n) ∨
         (∃mn ee e x.
           lookup mn menv = SOME ee ∧
           IS_SOME (lookup x ee) ∧
           FLOOKUP mods mn = SOME e ∧
           FLOOKUP e x = SOME n))
    ⇒
    EVERY (OPTION_EVERY closed_i1) genv``,
  rw[Once v_to_i1_cases] >>
  rw[EVERY_MEM,MEM_EL] >>
  Cases_on`EL n genv`>>fs[] >>
  first_x_assum(qspec_then`n`mp_tac) >>
  simp[] >> simp[IS_SOME_EXISTS] >>
  strip_tac >- (
    res_tac >>
    rator_x_assum`global_env_inv_flat`mp_tac >>
    simp[Once v_to_i1_cases] >> rw[] >>
    res_tac >> fs[] >> rw[] >> fs[] >>
    fs[EVERY_MEM,PULL_EXISTS] >>
    metis_tac[v_to_i1_closed,libPropsTheory.lookup_in] ) >>
  first_x_assum(qspec_then`mn`mp_tac) >> simp[] >>
  simp[Once v_to_i1_cases] >>
  disch_then(fn th => first_assum (mp_tac o MATCH_MP th)) >>
  simp[] >>
  imp_res_tac libPropsTheory.lookup_in >>
  imp_res_tac libPropsTheory.lookup_in2 >>
  fs[EVERY_MEM,MAP_FLAT,MEM_MAP,PULL_EXISTS,MEM_FLAT] >>
  metis_tac[v_to_i1_closed])

val _ = export_theory()
