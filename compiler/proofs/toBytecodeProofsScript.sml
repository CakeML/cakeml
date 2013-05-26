open HolKernel bossLib boolLib boolSimps SatisfySimps listTheory rich_listTheory pairTheory pred_setTheory finite_mapTheory alistTheory relationTheory arithmeticTheory sortingTheory lcsymtacs quantHeuristicsLib quantHeuristicsLibAbbrev
open miscTheory miscLib CompilerLibTheory CompilerPrimitivesTheory IntLangTheory ToBytecodeTheory compilerTerminationTheory intLangExtraTheory toIntLangProofsTheory bytecodeTerminationTheory bytecodeEvalTheory bytecodeExtraTheory
val _ = numLib.prefer_num()
val _ = new_theory "toBytecodeProofs"

(* TODO: move? *)
val with_same_refs = store_thm("with_same_refs",
  ``(x with refs := x.refs) = x``,
  rw[bc_state_component_equality])
val _ = export_rewrites["with_same_refs"]

val with_same_code = store_thm("with_same_code",
  ``(x with code := x.code) = x``,
  rw[bc_state_component_equality])
val _ = export_rewrites["with_same_code"]

val with_same_pc = store_thm("with_same_pc",
  ``(x with pc := x.pc) = x``,
  rw[bc_state_component_equality])
val _ = export_rewrites["with_same_pc"]

val with_same_stack = store_thm("with_same_stack",
  ``(x with stack := x.stack) = x``,
  rw[bc_state_component_equality])
val _ = export_rewrites["with_same_stack"]

val _ = Hol_datatype`refs_data = <| sm : num list; cls : num |-> (Cv list # def list # num) |>`

val with_same_sm = store_thm("with_same_sm",
  ``rd with sm := rd.sm = rd``,
  rw[theorem"refs_data_component_equality"])
val _ = export_rewrites["with_same_sm"]

val (Cv_bv_rules,Cv_bv_ind,Cv_bv_cases) = Hol_reln`
  (Cv_bv pp (CLitv (IntLit k)) (Number k)) ∧
  (Cv_bv pp (CLitv (Bool b)) (bool_to_val b)) ∧
  (Cv_bv pp (CLitv Unit) unit_val) ∧
  ((el_check m (FST pp).sm = SOME p) ⇒ Cv_bv pp (CLoc m) (RefPtr p)) ∧
  (EVERY2 (Cv_bv pp) vs bvs ⇒ Cv_bv pp (CConv cn vs) (Block (cn+block_tag) bvs)) ∧
  ((pp = (rd,l2a)) ∧
   (el_check n defs = SOME (SOME (l,cc,(recs,envs)),azb)) ∧
   EVERY (λn. n < LENGTH defs) recs ∧
   EVERY (λn. n < LENGTH env) envs ∧
   (l2a l = SOME a) ∧
   benv_bvs pp bvs (recs,envs) env defs
   ⇒ Cv_bv pp (CRecClos env defs n) (Block closure_tag [CodePtr a; Block 0 bvs])) ∧
  ((pp = (rd,l2a)) ∧
   (ce= (recs,envs)) ∧
   (LENGTH bvs = LENGTH recs + LENGTH envs) ∧
   (∀i x bv. i < LENGTH recs ∧ (x = EL i recs) ∧ (bv = EL i bvs) ⇒
     x < LENGTH defs ∧
     ∃p. (bv = RefPtr p) ∧ ∃jenv jdefs jx. (FLOOKUP rd.cls p = SOME (jenv,jdefs,jx)) ∧ syneq (CRecClos jenv jdefs jx) (CRecClos env defs x)) ∧
   (∀i x bv. i < LENGTH envs ∧ (x = EL i envs) ∧ (bv = EL (LENGTH recs + i) bvs) ⇒
       x < LENGTH env ∧ Cv_bv pp (EL x env) bv)
   ⇒ benv_bvs pp bvs ce env defs)`

val Cv_bv_only_ind =
  Cv_bv_ind
|> SPEC_ALL
|> UNDISCH
|> CONJUNCT1
|> DISCH_ALL
|> Q.GEN`benv_bvs'`
|> Q.SPEC`K(K(K(K T)))`
|> SIMP_RULE std_ss []
|> GEN_ALL

val Cv_bv_ov = store_thm("Cv_bv_ov",
  ``∀m pp Cv bv. Cv_bv pp Cv bv ⇒ ∀s. ((FST pp).sm = s) ⇒ (Cv_to_ov m s Cv = bv_to_ov m bv)``,
  ntac 2 gen_tac >>
  ho_match_mp_tac Cv_bv_only_ind >>
  strip_tac >- rw[bv_to_ov_def] >>
  strip_tac >- (
    rw[bv_to_ov_def] >>
    Cases_on `b` >> fs[] ) >>
  strip_tac >- rw[bv_to_ov_def] >>
  strip_tac >- rw[bv_to_ov_def,el_check_def] >>
  strip_tac >- (
    rw[bv_to_ov_def] >>
    fsrw_tac[ARITH_ss][] >>
    rw[MAP_EQ_EVERY2] >>
    fs[EVERY2_EVERY] ) >>
  rw[bv_to_ov_def])

val _ = Parse.overload_on("mk_pp", ``λrd bs.
  (rd
  ,combin$C (bc_find_loc_aux bs.code bs.inst_length) 0
  )``)

val good_rd_def = Define`
  good_rd rd bs =
    FEVERY (λ(p,(env,defs,j)).
      p ∈ FDOM bs.refs ∧
      p ∉ set rd.sm ∧
      Cv_bv (mk_pp rd bs) (CRecClos env defs j) (bs.refs ' p))
    rd.cls`

val Cv_bv_strongind = theorem"Cv_bv_strongind"

val Cv_bv_syneq = store_thm("Cv_bv_syneq",
  ``(∀v1 bv. Cv_bv pp v1 bv ⇒ ∀v2. syneq v1 v2 ⇒ Cv_bv pp v2 bv) ∧
    (∀bvs ce env1 defs1. benv_bvs pp bvs ce env1 defs1 ⇒
      ∀env2 defs2 V U n1 n2 l cc azb.
        syneq_defs (LENGTH env1) (LENGTH env2) V defs1 defs2 U ∧ n1 < LENGTH defs1 ∧ n2 < LENGTH defs2 ∧ U n1 n2 ∧
        (EL n1 defs1 = (SOME (l,cc,ce),azb)) ∧ EVERY (λn. n < LENGTH defs1) (FST ce) ∧ EVERY (λn. n < LENGTH env1) (SND ce) ∧
        (∀v1 v2. V v1 v2 ⇒ v1 < LENGTH env1 ∧ v2 < LENGTH env2 ∧ syneq (EL v1 env1) (EL v2 env2))
        ⇒ benv_bvs pp bvs ce env2 defs2)``,
  ho_match_mp_tac (Cv_bv_strongind) >>
  strip_tac >- ( simp[Once Cv_bv_cases] ) >>
  strip_tac >- ( simp[Once Cv_bv_cases] ) >>
  strip_tac >- ( simp[Once Cv_bv_cases] ) >>
  strip_tac >- ( simp[Once Cv_bv_cases] ) >>
  strip_tac >- (
    rw[] >> pop_assum mp_tac >>
    simp[Once syneq_cases] >>
    rw[Once Cv_bv_cases] >>
    fsrw_tac[DNF_ss][EVERY2_EVERY,EVERY_MEM,FORALL_PROD] >>
    rfs[MEM_ZIP] >> fs[MEM_ZIP] >>
    fsrw_tac[DNF_ss][] ) >>
  strip_tac >- (
    rw[el_check_def,FLOOKUP_DEF] >>
    rator_x_assum`syneq`mp_tac >>
    simp[Once syneq_cases] >> rw[] >>
    simp[Once Cv_bv_cases,el_check_def,FLOOKUP_DEF] >>
    rator_assum`syneq_defs`mp_tac >>
    simp_tac(srw_ss())[Once syneq_exp_cases,EVERY_MEM] >>
    simp[] >> strip_tac >>
    first_x_assum(qspecl_then[`n`,`d2`]mp_tac) >>
    simp[] >> strip_tac >>
    simp[] >>
    Cases_on`azb` >> rfs[] >> fs[syneq_cb_aux_def] >> rfs[EVERY_MEM] >>
    first_x_assum match_mp_tac >>
    HINT_EXISTS_TAC >>
    HINT_EXISTS_TAC >>
    qexists_tac`n` >>
    srw_tac[SATISFY_ss][]) >>
  rw[] >>
  simp[Once Cv_bv_cases] >>
  rator_assum`syneq_defs`mp_tac >>
  simp_tac(srw_ss())[Once syneq_exp_cases,EVERY_MEM] >>
  strip_tac >>
  first_x_assum(qspecl_then[`n1`,`n2`]mp_tac) >>
  simp[] >>
  qabbrev_tac`p = EL n1 defs1`>>PairCases_on`p` >>
  Cases_on`p0`>>fs[]>>PairCases_on`x` >>
  strip_tac >>
  ntac 2 (qpat_assum`X = Y`(mp_tac o SYM)) >>
  simp[syneq_cb_aux_def] >>
  strip_tac >> strip_tac >> fs[] >>
  rpt BasicProvers.VAR_EQ_TAC >>
  `b` by (
    fs[syneq_cb_aux_def] >> rw[] >> rfs[] ) >>
  fs[] >>
  conj_tac >- (
    gen_tac >> strip_tac >>
    last_x_assum(qspec_then`i`mp_tac) >>
    simp[] >> strip_tac >>
    conj_asm1_tac >- (
      fs[syneq_cb_aux_def] >> rw[] >> rfs[] >>
      fs[EVERY_MEM,MEM_EL,GSYM LEFT_FORALL_IMP_THM] ) >>
    qsuff_tac`syneq (CRecClos env1 defs1 (EL i recs)) (CRecClos env2 defs2 (EL i recs))`>-(
      metis_tac[syneq_trans] ) >>
    simp[Once syneq_cases] >>
    HINT_EXISTS_TAC >>
    qexists_tac`U` >>
    simp[] >> conj_tac >- metis_tac[] >>
    first_x_assum match_mp_tac >>
    simp[MEM_EL] >> metis_tac[] ) >>
  gen_tac >> strip_tac >>
  qpat_assum`∀i. i < LENGTH envs ⇒ P ∧ Q`(qspec_then`i`mp_tac) >>
  simp[] >> strip_tac >>
  conj_asm1_tac >- (
    fs[syneq_cb_aux_def,EVERY_MEM,MEM_EL,GSYM LEFT_FORALL_IMP_THM] ) >>
  first_x_assum match_mp_tac >>
  fsrw_tac[DNF_ss][] >>
  first_x_assum match_mp_tac >>
  first_x_assum match_mp_tac >>
  simp[MEM_EL] >> metis_tac[])

val s_refs_def = Define`
  s_refs rd s bs ⇔
  good_rd rd bs ∧
  (LENGTH rd.sm = LENGTH s) ∧
  EVERY (λp. p ∈ FDOM bs.refs) rd.sm ∧
  ALL_DISTINCT rd.sm ∧
  EVERY2 (Cv_bv (mk_pp rd bs)) s (MAP (FAPPLY bs.refs) rd.sm)`

val s_refs_with_pc = store_thm("s_refs_with_pc",
  ``s_refs rd s (bs with pc := p) = s_refs rd s bs``,
  rw[s_refs_def,good_rd_def])

val s_refs_with_stack = store_thm("s_refs_with_stack",
  ``s_refs rd s (bs with stack := p) = s_refs rd s bs``,
  rw[s_refs_def,good_rd_def])

val Cenv_bs_def = Define`
  Cenv_bs rd s Cenv (renv:ctenv) sz bs ⇔
    (EVERY2
       (λCv b. case lookup_ct sz bs.stack (DRESTRICT bs.refs (FDOM rd.cls)) b of NONE => F
             | SOME bv => Cv_bv (mk_pp rd bs) Cv bv)
     Cenv renv) ∧
    s_refs rd s bs`

val Cenv_bs_syneq_store = store_thm("Cenv_bs_syneq_store",
  ``∀rd s Cenv renv sz bs s'. LIST_REL (syneq) s s' ∧ Cenv_bs rd s Cenv renv sz bs ⇒
           Cenv_bs rd s' Cenv renv sz bs``,
  rw[Cenv_bs_def] >>
  fs[s_refs_def] >>
  conj_asm1_tac >- metis_tac[EVERY2_EVERY] >>
  fs[EVERY2_EVERY,EVERY_MEM,FORALL_PROD] >>
  rfs[MEM_ZIP] >> fs[MEM_ZIP] >>
  fs[GSYM LEFT_FORALL_IMP_THM] >>
  metis_tac[Cv_bv_syneq,FST,SND])

val compile_varref_thm = store_thm("compile_varref_thm",
  ``∀bs bc0 code bc1 cls sz cs b bv bs'.
      ((compile_varref sz cs b).out = REVERSE code ++ cs.out) ∧
      (bs.code = bc0 ++ code ++ bc1) ∧
      (bs.pc = next_addr bs.inst_length bc0) ∧
      (lookup_ct sz bs.stack (DRESTRICT bs.refs cls) b = SOME bv) ∧
      (bs' = bs with <| stack := bv::bs.stack ; pc := next_addr bs.inst_length (bc0 ++ code)|>)
      ⇒
      bc_next^* bs bs'``,
  ntac 7 gen_tac >> Cases >> rw[] >>
  TRY(Cases_on`c`>>fs[])>>
  qpat_assum`X = REVERSE code`(assume_tac o SIMP_RULE std_ss [Once SWAP_REVERSE]) >> fs[] >>
  qmatch_assum_abbrev_tac `code = x::ls1` >>
  `bc_fetch bs = SOME x` by (
    match_mp_tac bc_fetch_next_addr >>
    map_every qexists_tac [`bc0`,`ls1++bc1`] >>
    rw[Abbr`x`,Abbr`ls1`]) >>
  TRY (
    qmatch_abbrev_tac `bc_next^* bs bs'` >>
    `(bc_eval1 bs = SOME bs')` by (
      rw[bc_eval1_def,Abbr`x`] >>
      rfs[el_check_def] >>
      rw[bc_eval_stack_def] >>
      srw_tac[ARITH_ss][bump_pc_def,SUM_APPEND,FILTER_APPEND,ADD1,Abbr`bs'`,Abbr`ls1`,bc_state_component_equality] >>
      NO_TAC) >>
    metis_tac[bc_eval1_thm,RTC_CASES1] )
  >- (
    rfs[el_check_def] >>
    qmatch_abbrev_tac `bc_next^* bs bs'` >>
    qpat_assum `X = SOME bv` mp_tac >>
    BasicProvers.EVERY_CASE_TAC >> rw[] >>
    qpat_assum `X = SOME bv` mp_tac >>
    BasicProvers.EVERY_CASE_TAC >> rw[] >>
    srw_tac[DNF_ss][RTC_eq_NRC] >>
    qexists_tac `SUC (SUC (SUC ZERO))` >> rw[NRC] >>
    srw_tac[DNF_ss][ALT_ZERO] >>
    rw[bc_eval1_thm] >>
    rw[Once bc_eval1_def,Abbr`x`] >>
    srw_tac[DNF_ss][] >>
    rw[bc_eval_stack_def] >>
    Q.PAT_ABBREV_TAC `bs0 = bump_pc bs with stack := st` >>
    qunabbrev_tac`ls1` >>
    fs[] >>
    qmatch_assum_abbrev_tac `bs.code = ls0 ++ [x;y;z] ++ bc1` >>
    `bc_fetch bs0 = SOME y` by (
      match_mp_tac bc_fetch_next_addr >>
      map_every qexists_tac [`ls0++[x]`,`z::bc1`] >>
      rw[Abbr`bs0`,Abbr`y`,bump_pc_def] >>
      srw_tac[ARITH_ss][FILTER_APPEND,SUM_APPEND,Abbr`x`] ) >>
    rw[Once bc_eval1_def,Abbr`y`] >>
    srw_tac[DNF_ss][] >>
    rw[bc_eval_stack_def,Abbr`bs0`] >>
    Q.PAT_ABBREV_TAC`bs0 = bump_pc X with stack := Y` >>
    qmatch_assum_abbrev_tac `bs.code = ls0 ++ [x;y;z] ++ bc1` >>
    `bc_fetch bs0 = SOME z` by (
      match_mp_tac bc_fetch_next_addr >>
      map_every qexists_tac [`ls0++[x;y]`,`bc1`] >>
      rw[Abbr`bs0`,bump_pc_def,Abbr`z`] >>
      srw_tac[ARITH_ss][FILTER_APPEND,SUM_APPEND,Abbr`y`,Abbr`x`] ) >>
    rw[bc_eval_stack_def] >>
    rw[bc_eval1_def,Abbr`bs0`,bump_pc_def,Abbr`z`] >>
    fs[FLOOKUP_DEF] >>
    unabbrev_all_tac >>
    fs[FDOM_DRESTRICT,DRESTRICT_DEF] >>
    srw_tac[ARITH_ss][FILTER_APPEND,SUM_APPEND,ADD1] )
  >- (
    rfs[el_check_def] >>
    qmatch_abbrev_tac `bc_next^* bs bs'` >>
    qpat_assum `X = SOME bv` mp_tac >>
    BasicProvers.EVERY_CASE_TAC >> rw[] >>
    rw[RTC_eq_NRC] >>
    qexists_tac `SUC (SUC ZERO)` >> rw[NRC] >>
    srw_tac[DNF_ss][ALT_ZERO] >>
    rw[bc_eval1_thm] >>
    rw[Once bc_eval1_def,Abbr`x`] >>
    rfs[el_check_def] >>
    rw[bc_eval_stack_def] >>
    qunabbrev_tac`ls1` >> fs[] >>
    qmatch_assum_abbrev_tac `bs.code = ls0 ++ [x;y] ++ bc1` >>
    qmatch_abbrev_tac `bc_eval1 bs0 = SOME bs'` >>
    `bc_fetch bs0 = SOME y` by (
      match_mp_tac bc_fetch_next_addr >>
      map_every qexists_tac [`ls0++[x]`,`bc1`] >>
      unabbrev_all_tac >> rw[bump_pc_def] >>
      srw_tac[ARITH_ss][FILTER_APPEND,SUM_APPEND] ) >>
    rw[bc_eval1_def,Abbr`y`] >>
    rw[bc_eval_stack_def,Abbr`bs0`,Abbr`bs'`] >>
    unabbrev_all_tac >>
    srw_tac[ARITH_ss][bump_pc_def,FILTER_APPEND,SUM_APPEND,ADD1] ))

val no_closures_Cv_bv_equal = store_thm("no_closures_Cv_bv_equal",
  ``∀pp cv bv. Cv_bv pp cv bv ⇒
      ∀cv' bv'. Cv_bv pp cv' bv' ∧
        no_closures cv ∧
        no_closures cv' ∧
        all_Clocs cv ⊆ count (LENGTH (FST pp).sm) ∧
        all_Clocs cv' ⊆ count (LENGTH (FST pp).sm) ∧
        ALL_DISTINCT (FST pp).sm
        ⇒ ((cv = cv') = (bv = bv'))``,
  gen_tac >> ho_match_mp_tac Cv_bv_only_ind >> rw[]
  >- (
    rw[EQ_IMP_THM] >> rw[] >>
    fs[Once Cv_bv_cases] )
  >- (
    rw[EQ_IMP_THM] >> rw[] >>
    Cases_on `b` >>
    fsrw_tac[ARITH_ss][Once Cv_bv_cases] >>
    Cases_on `b` >> fs[])
  >- (
    rw[EQ_IMP_THM] >>
    fs[Once Cv_bv_cases] >>
    fsrw_tac[ARITH_ss][] >>
    Cases_on`b` >> fsrw_tac[ARITH_ss][] )
  >- (
    rw[EQ_IMP_THM] >>
    fs[Once Cv_bv_cases,el_check_def] >> rw[] >>
    fs[EL_ALL_DISTINCT_EL_EQ]) >>
  rw[EQ_IMP_THM] >- (
    fs[Once (Q.SPEC`CConv cn vs`(CONJUNCT1 (SPEC_ALL Cv_bv_cases)))] >>
    rw[LIST_EQ_REWRITE] >>
    fs[EVERY2_EVERY] >>
    qpat_assum`LENGTH X = LENGTH bvs` assume_tac >>
    fsrw_tac[DNF_ss][EVERY_MEM,FORALL_PROD,MEM_ZIP] >>
    qpat_assum`LENGTH vs = X` assume_tac >>
    fsrw_tac[DNF_ss][MEM_EL] >>
    fsrw_tac[DNF_ss][SUBSET_DEF,MEM_EL] >>
    metis_tac[EL_ZIP] ) >>
  qpat_assum`Cv_bv X Y Z` mp_tac >>
  rw[Once Cv_bv_cases] >>
  fsrw_tac[ARITH_ss][] >>
  TRY (Cases_on `b` >> fsrw_tac[ARITH_ss][]) >>
  fsrw_tac[DNF_ss][EVERY2_EVERY,EVERY_MEM,FORALL_PROD] >>
  rpt (qpat_assum `LENGTH X = Y` mp_tac) >> rpt strip_tac >>
  fsrw_tac[DNF_ss][MEM_ZIP] >>
  rw[LIST_EQ_REWRITE] >> fsrw_tac[DNF_ss][MEM_EL] >>
  fsrw_tac[DNF_ss][SUBSET_DEF,MEM_EL] >>
  metis_tac[])

val prim2_to_bc_thm = store_thm("prim2_to_bc_thm",
  ``∀op v1 v2 v bs bc0 bc1 st bv1 bv2 pp.
    (bs.code = bc0 ++ [Stack (prim2_to_bc op)] ++ bc1) ∧
    (bs.pc = next_addr bs.inst_length bc0) ∧
    (v2 = CLitv(IntLit i0) ⇒ (op ≠ CDiv) ∧ (op ≠ CMod)) ∧
    (CevalPrim2 op v1 v2 = Cval v) ∧
    Cv_bv pp v1 bv1 ∧ Cv_bv pp v2 bv2 ∧
    (bs.stack = bv2::bv1::st) ∧
    all_Clocs v1 ⊆ count (LENGTH (FST pp).sm) ∧
    all_Clocs v2 ⊆ count (LENGTH (FST pp).sm) ∧
    ALL_DISTINCT (FST pp).sm
    ⇒ ∃bv.
      Cv_bv pp v bv ∧
      bc_next bs (bump_pc (bs with <|stack := bv::st|>))``,
  rw[] >>
  `bc_fetch bs = SOME (Stack (prim2_to_bc op))` by (
    match_mp_tac bc_fetch_next_addr >>
    map_every qexists_tac[`bc0`,`bc1`] >>
    rw[] ) >>
  rw[bc_eval1_thm] >>
  rw[bc_eval1_def] >>
  srw_tac[DNF_ss][] >>
  rw[bump_pc_with_stack] >>
  Cases_on `op` >>
  Cases_on `v1` >> TRY (Cases_on `l`) >>
  Cases_on `v2` >> TRY (Cases_on `l`) >>
  fs[] >> rw[] >> fs[Once Cv_bv_cases] >> rw[] >>
  BasicProvers.EVERY_CASE_TAC >>
  rw[bc_eval_stack_def] >> fs[i0_def] >>
  TRY (Cases_on `b` >> rw[]) >>
  TRY (Cases_on `b'` >> rw[]) >>
  srw_tac[ARITH_ss][] >>
  fs[EVERY2_EVERY,EVERY_MEM,FORALL_PROD] >>
  TRY (
    fsrw_tac[DNF_ss][EL_ALL_DISTINCT_EL_EQ,el_check_def] >>
    AP_THM_TAC >> AP_TERM_TAC >> AP_TERM_TAC >> AP_THM_TAC >>
    AP_TERM_TAC >> AP_THM_TAC >> AP_TERM_TAC >> AP_TERM_TAC >>
    metis_tac[] ) >>
  Cases_on `n=n'` >> rw[] >>
  AP_THM_TAC >> AP_TERM_TAC >> AP_TERM_TAC >> AP_THM_TAC >>
  AP_TERM_TAC >> AP_THM_TAC >> AP_TERM_TAC >> AP_TERM_TAC >>
  rw[LIST_EQ_REWRITE] >>
  rfs[MEM_ZIP] >>
  fsrw_tac[DNF_ss][MEM_EL] >>
  Cases_on `LENGTH bvs = LENGTH bvs'` >> rw[] >>
  fsrw_tac[DNF_ss][SUBSET_DEF,MEM_EL] >>
  metis_tac[SIMP_RULE(srw_ss()++DNF_ss)[SUBSET_DEF]no_closures_Cv_bv_equal] )

val is_Label_prim1_to_bc = store_thm("is_Label_prim1_to_bc",
  ``∀uop. ¬is_Label (prim1_to_bc uop)``,
  Cases >> rw[])
val _ = export_rewrites["is_Label_prim1_to_bc"]

val bc_fetch_with_stack = store_thm("bc_fetch_with_stack",
  ``bc_fetch (s with stack := st) = bc_fetch s``,
  rw[bc_fetch_def])

val bc_fetch_with_refs = store_thm("bc_fetch_with_refs",
  ``bc_fetch (s with refs := st) = bc_fetch s``,
  rw[bc_fetch_def])

val Cv_bv_SUBMAP = store_thm("Cv_bv_SUBMAP",
  ``∀pp.
    (∀v bv. Cv_bv pp v bv ⇒
      ∀rd l2a pp' rd'.
        (pp = (rd,l2a)) ∧
        (pp' = (rd',l2a)) ∧
        (rd.sm ≼ rd'.sm) ∧ (rd.cls ⊑ rd'.cls) ∧
        (∀p. p ∈ FDOM rd.cls ∧ p ∉ set rd.sm ⇒ p ∉ set rd'.sm)
        ⇒
        Cv_bv pp' v bv) ∧
    (∀benv cd env defs. benv_bvs pp benv cd env defs ⇒
      ∀rd l2a pp' rd'.
        (pp = (rd,l2a)) ∧
        (pp' = (rd',l2a)) ∧
        (rd.sm ≼ rd'.sm) ∧ (rd.cls ⊑ rd'.cls) ∧
        (∀p. p ∈ FDOM rd.cls ∧ p ∉ set rd.sm ⇒ p ∉ set rd'.sm)
        ⇒
        benv_bvs pp' benv cd env defs)``,
  gen_tac >> ho_match_mp_tac Cv_bv_ind >>
  strip_tac >- rw[Once Cv_bv_cases,LENGTH_NIL] >>
  strip_tac >- rw[Once Cv_bv_cases,LENGTH_NIL] >>
  strip_tac >- rw[Once Cv_bv_cases,LENGTH_NIL] >>
  strip_tac >- (
    rw[Once Cv_bv_cases,LENGTH_NIL] >>
    fs[el_check_def,IS_PREFIX_THM,EVERY2_EVERY,EVERY_MEM,FORALL_PROD,LENGTH_NIL] >>
    PROVE_TAC[LESS_LESS_EQ_TRANS]) >>
  strip_tac >- (
    rw[] >> rw[Once Cv_bv_cases,LENGTH_NIL] >>
    fs[FLOOKUP_DEF,IS_PREFIX_THM,EVERY2_EVERY,EVERY_MEM,FORALL_PROD,LENGTH_NIL] ) >>
  strip_tac >- ( rw[] >> simp[Once Cv_bv_cases] >> metis_tac[] ) >>
  rpt gen_tac >> strip_tac >> fs[] >>
  rpt gen_tac >> strip_tac >>
  simp[Once Cv_bv_cases] >>
  simp[GSYM FORALL_AND_THM] >> gen_tac >>
  rpt BasicProvers.VAR_EQ_TAC >> fs[] >>
  metis_tac[FLOOKUP_SUBMAP,ADD_SYM])

val prim1_to_bc_thm = store_thm("prim1_to_bc_thm",
  ``∀rd op s v1 s' v bs bc0 bc1 bce st bv1.
    (bs.code = bc0 ++ [prim1_to_bc op] ++ bc1) ∧
    (bs.pc = next_addr bs.inst_length bc0) ∧
    (CevalPrim1 op s v1 = (s', Cval v)) ∧
    Cv_bv (mk_pp rd (bs with code := bce)) v1 bv1 ∧
    (bs.stack = bv1::st) ∧
    s_refs rd s (bs with code := bce)
    ⇒ ∃bv rf sm'.
      let bs' = bs with <|stack := bv::st; refs := rf; pc := next_addr bs.inst_length (bc0 ++ [prim1_to_bc op])|> in
      let rd' = rd with sm := sm' in
      bc_next bs bs' ∧
      Cv_bv (mk_pp rd' (bs' with <| code := bce |>)) v bv ∧
      s_refs rd' s' (bs' with code := bce) ∧
      DRESTRICT bs.refs (COMPL (set rd.sm)) ⊑ DRESTRICT rf (COMPL (set sm')) ∧
      rd.sm ≼ sm'``,
  simp[] >> rw[] >>
  `bc_fetch bs = SOME (prim1_to_bc op)` by (
    match_mp_tac bc_fetch_next_addr >>
    map_every qexists_tac[`bc0`,`bc1`] >>
    rw[] ) >>
  simp[bc_eval1_thm] >>
  Cases_on`op`>>simp[bc_eval1_def,bump_pc_def,bc_fetch_with_stack,bc_fetch_with_refs] >>
  fs[LET_THM] >- (
    simp[bc_state_component_equality] >>
    qmatch_assum_abbrev_tac`CLoc n = v` >>
    Q.PAT_ABBREV_TAC`bn = LEAST n. n ∉ X` >>
    qexists_tac`rd.sm ++ [bn]` >>
    qpat_assum`X = s'`(assume_tac o SYM) >>
    qpat_assum`X = v`(assume_tac o SYM) >>
    simp[Once Cv_bv_cases] >>
    `n = LENGTH rd.sm` by fs[s_refs_def] >>
    simp[el_check_def,EL_APPEND2] >>
    `bn ∉ FDOM bs.refs` by (
      unabbrev_all_tac >>
      numLib.LEAST_ELIM_TAC >>
      simp[] >>
      PROVE_TAC[NOT_IN_FINITE,INFINITE_NUM_UNIV,FDOM_FINITE] ) >>
    simp[SUM_APPEND,FILTER_APPEND] >>
    conj_tac >- (
      fs[s_refs_def] >>
      conj_tac >- (
        full_simp_tac std_ss [good_rd_def,theorem"refs_data_accfupds"] >>
        fs[FEVERY_DEF,DOMSUB_NOT_IN_DOM,UNCURRY] >>
        rw[FAPPLY_FUPDATE_THM] >- PROVE_TAC[] >>
        match_mp_tac(MP_CANON(GEN_ALL(CONJUNCT1(SPEC_ALL Cv_bv_SUBMAP)))) >>
        qexists_tac`mk_pp rd (bs with code := bce)` >>
        simp[] >>
        metis_tac[EVERY_MEM] ) >>
      fs[fmap_rel_def,f_o_f_DEF,GSYM SUBSET_INTER_ABSORPTION] >>
      conj_asm1_tac >- (
        fsrw_tac[DNF_ss][SUBSET_DEF,FAPPLY_FUPDATE_THM,EXTENSION,EVERY_MEM] >>
        rw[] >> PROVE_TAC[] ) >>
      conj_tac >- (
        simp[ALL_DISTINCT_APPEND] >>
        fs[EVERY_MEM] >> PROVE_TAC[] ) >>
      match_mp_tac EVERY2_APPEND_suff >>
      simp[] >>
      conj_tac >- (
        fsrw_tac[DNF_ss][EVERY2_EVERY,EVERY_MEM,FORALL_PROD,MEM_ZIP] >>
        qx_gen_tac`m`>>strip_tac >>
        qpat_assum`∀m. m < LENGTH rd.sm ⇒ Q`(qspec_then`m`mp_tac)>>
        simp[EL_MAP,FAPPLY_FUPDATE_THM] >> fs[MEM_EL] >>
        rw[] >- PROVE_TAC[] >>
        match_mp_tac(MP_CANON(GEN_ALL(CONJUNCT1(SPEC_ALL Cv_bv_SUBMAP)))) >>
        qexists_tac`mk_pp rd (bs with code := bce)` >>
        simp[] >>
        fs[good_rd_def,FEVERY_DEF,UNCURRY] >>
        metis_tac[] ) >>
      match_mp_tac(MP_CANON(GEN_ALL(CONJUNCT1(SPEC_ALL Cv_bv_SUBMAP)))) >>
      qexists_tac`mk_pp rd (bs with code := bce)` >>
      simp[] >>
      fs[good_rd_def,FEVERY_DEF,UNCURRY] >>
      metis_tac[] ) >>
    simp[SUBMAP_DEF,DRESTRICT_DEF] >>
    rw[] >> rw[] >> fs[IN_FRANGE,DOMSUB_FAPPLY_THM] >> rw[] >> PROVE_TAC[]) >>
  Cases_on`v1`>>fs[] >>
  Cases_on`el_check n s`>>fs[]>>
  fs[Q.SPEC`CLoc n`(CONJUNCT1(SPEC_ALL(Cv_bv_cases)))] >>
  rw[] >> simp[bc_state_component_equality] >>
  qexists_tac`rd.sm`>>
  simp[s_refs_with_stack,s_refs_with_pc,SUM_APPEND,FILTER_APPEND] >>
  fs[s_refs_def,good_rd_def] >>
  fs[EVERY2_EVERY,EVERY_MEM,FORALL_PROD,el_check_def] >>
  conj_tac >- metis_tac[MEM_EL] >>
  first_x_assum match_mp_tac >>
  simp[MEM_ZIP] >>
  qexists_tac`n` >>
  simp[EL_MAP])

val compile_envref_next_label_inc = store_thm("compile_envref_next_label_inc",
  ``∀sz cs b. (compile_envref sz cs b).next_label = cs.next_label``,
  ntac 2 gen_tac >> Cases >> rw[])
val _ = export_rewrites["compile_envref_next_label_inc"]

val compile_varref_next_label_inc = store_thm("compile_varref_next_label_inc",
  ``∀sz cs b. (compile_varref sz cs b).next_label = cs.next_label``,
  ntac 2 gen_tac >> Cases >> rw[])
val _ = export_rewrites["compile_varref_next_label_inc"]

val lookup_ct_incsz = store_thm("lookup_ct_incsz",
  ``(lookup_ct (sz+1) (x::st) refs b =
     if (b = CTLet (sz+1)) then SOME x else
     lookup_ct sz st refs b)``,
  fs[GSYM ADD1] >>
  Cases_on `b` >> rw[] >>
  fsrw_tac[ARITH_ss][el_check_def] >>
  rw[SUB,GSYM ADD_SUC] >>
  fsrw_tac[ARITH_ss][] >>
  Cases_on`c`>>rw[el_check_def]>>
  fsrw_tac[ARITH_ss][EL_CONS,PRE_SUB1,ADD1])

val lookup_ct_imp_incsz = store_thm("lookup_ct_imp_incsz",
  ``(lookup_ct sz st refs b = SOME v) ⇒
    (lookup_ct (sz+1) (x::st) refs b = SOME v)``,
  fs[GSYM ADD1] >>
  Cases_on `b` >> rw[el_check_def] >>
  fsrw_tac[ARITH_ss][EL_CONS,PRE_SUB1,ADD1] >>
  Cases_on`c`>>rw[el_check_def] >>
  fsrw_tac[ARITH_ss][EL_CONS,PRE_SUB1,ADD1,el_check_def])

val lookup_ct_imp_incsz_many = store_thm("lookup_ct_imp_incsz_many",
  ``∀sz st refs b v st' sz' ls.
    (lookup_ct sz st refs b = SOME v) ∧
     sz ≤ sz' ∧ (st' = ls ++ st) ∧ (LENGTH ls = sz' - sz)
   ⇒ (lookup_ct sz' st' refs b = SOME v)``,
  Induct_on`sz' - sz` >- (
    rw[] >> `sz = sz'` by srw_tac[ARITH_ss][] >> fs[LENGTH_NIL] ) >>
  rw[] >> Cases_on`ls`>>fs[] >- fsrw_tac[ARITH_ss][] >>
  Cases_on`sz'`>>fs[ADD1] >>
  match_mp_tac lookup_ct_imp_incsz >>
  first_x_assum (match_mp_tac o MP_CANON) >>
  qexists_tac`sz` >>
  fsrw_tac[ARITH_ss][])

val lookup_ct_change_refs = store_thm("lookup_ct_change_refs",
  ``∀sz st rf rf' ct.
    (∀n vs p. (ct = CTEnv (CCRef n)) ∧ sz < LENGTH st ∧ (EL sz st = Block 0 vs) ∧ n < LENGTH vs ∧ (EL n vs = RefPtr p) ⇒
       (FLOOKUP rf' p = FLOOKUP rf p))
    ⇒ (lookup_ct sz st rf' ct = lookup_ct sz st rf ct)``,
  rw[LET_THM] >>
  Cases_on`ct`>>fs[] >> rw[] >>
  Cases_on`c`>>fs[el_check_def]>>
  Cases_on`EL sz st`>>fs[] >> rw[]>>fs[]>>
  BasicProvers.CASE_TAC>>fs[]>>
  BasicProvers.CASE_TAC>>fs[]>>
  BasicProvers.CASE_TAC>>fs[]>>
  BasicProvers.CASE_TAC>>fs[])

val compile_envref_append_out = store_thm("compile_envref_append_out",
  ``∀sz cs b. ∃bc. ((compile_envref sz cs b).out = bc ++ cs.out) ∧ (EVERY ($~ o is_Label) bc)``,
  ho_match_mp_tac compile_envref_ind >> rw[])

val compile_varref_append_out = store_thm("compile_varref_append_out",
  ``∀sz cs b. ∃bc. ((compile_varref sz cs b).out = bc ++ cs.out) ∧ (EVERY ($~ o is_Label) bc)``,
  ntac 2 gen_tac >> Cases >> rw[compile_envref_append_out])

val FOLDL_emit_ceref_thm = store_thm("FOLDL_emit_ceref_thm",
  ``∀ls z sz s.
      let (z',s') = FOLDL (emit_ceref z) (sz,s) ls in
      ∃code.
      (z' = sz + LENGTH ls) ∧
      (s'.out = REVERSE code ++ s.out) ∧
      EVERY ($~ o is_Label) code ∧ (s'.next_label = s.next_label) ∧
      ∀bs bc0 bc1 fs st.
        (bs.code = bc0 ++ code ++ bc1) ∧ (bs.pc = next_addr bs.inst_length bc0) ∧
        z ≤ sz ∧ EVERY (λn. sz-z+n < LENGTH bs.stack) ls
        ⇒
        bc_next^* bs (bs with <| stack := REVERSE (MAP (λn. EL ((sz-z)+n) bs.stack) ls) ++ bs.stack
                               ; pc := next_addr bs.inst_length (bc0 ++ code) |>)``,
  Induct >- (
    rw[Once SWAP_REVERSE,LET_THM] >>
    rpt (first_x_assum (mp_tac o SYM)) >> rw[]) >>
  qx_gen_tac`e` >> rw[] >>
  qmatch_assum_abbrev_tac`FOLDL (emit_ceref z) (sz + 1, s1) ls = X` >>
  first_x_assum(qspecl_then[`z`,`sz+1`,`s1`]mp_tac) >>
  simp[Abbr`X`,Abbr`s1`] >>
  disch_then(Q.X_CHOOSE_THEN`bc`strip_assume_tac) >> rw[] >>
  simp[Once SWAP_REVERSE] >> rw[] >>
  simp[Once RTC_CASES1] >> disj2_tac >>
  `bc_fetch bs = SOME(Stack(Load(sz-z+e)))` by (
    match_mp_tac bc_fetch_next_addr>>
    map_every qexists_tac[`bc0`,`bc++bc1`]>>
    simp[])>>
  simp[bc_eval1_thm,bc_eval1_def] >>
  simp[bc_eval_stack_def,bump_pc_def]>>
  qmatch_abbrev_tac`bc_next^* bs1 bs2` >>
  first_x_assum(qspecl_then[`bs1`,`bc0++[Stack(Load(sz-z+e))]`,`bc1`]mp_tac)>>
  simp[Abbr`bs1`]>>
  discharge_hyps >- (
    simp[ADD1,SUM_APPEND,FILTER_APPEND] >>
    fsrw_tac[ARITH_ss][EVERY_MEM] >>
    rw[] >> res_tac >> DECIDE_TAC ) >>
  rw[] >>
  qmatch_abbrev_tac`bc_next^* bs1 bs2` >>
  qmatch_assum_abbrev_tac`bc_next^* bs1' bs2'` >>
  `bs1' = bs1` by simp[bc_state_component_equality,Abbr`bs1'`,Abbr`bs1`,FILTER_APPEND,SUM_APPEND]>>
  `bs2' = bs2` by (
    simp[bc_state_component_equality,Abbr`bs2'`,Abbr`bs2`,Abbr`bs1`,FILTER_APPEND,SUM_APPEND,MAP_EQ_f] >>
    lrw[EL_CONS,PRE_SUB1] ) >>
  rw[])

val FOLDL_emit_ceenv_thm = store_thm("FOLDL_emit_ceenv_thm",
  ``∀ec env0 z s.
     let (z',s') = FOLDL (emit_ceenv env0) (z,s) ec in
     ∃code.
     (s'.out = REVERSE code ++ s.out) ∧
     EVERY ($~ o is_Label) code ∧ (s'.next_label = s.next_label) ∧
     ∀bs bc0 bc1 cls j.
       (bs.code = bc0 ++ code ++ bc1) ∧
       (bs.pc = next_addr bs.inst_length bc0) ∧
       EVERY (λn. n < LENGTH env0) ec ∧ j ≤ z ∧ j ≤ LENGTH bs.stack ∧
       EVERY (λn. IS_SOME (lookup_ct (z-j) (DROP j bs.stack) (DRESTRICT bs.refs cls) (EL n env0))) ec
       ⇒
       bc_next^* bs (bs with <| stack := (REVERSE (MAP (λn. THE (lookup_ct (z-j) (DROP j bs.stack) (DRESTRICT bs.refs cls) (EL n env0))) ec))++bs.stack
                              ; pc := next_addr bs.inst_length (bc0 ++ code) |>)``,
  Induct >- (
    rw[Once SWAP_REVERSE,LET_THM] >>
    rpt (first_x_assum (mp_tac o SYM)) >> rw[]) >>
  qx_gen_tac`e` >> rw[] >>
  qmatch_assum_abbrev_tac`FOLDL (emit_ceenv env0) (z + 1, s1) ec = X` >>
  first_x_assum(qspecl_then[`env0`,`z+1`,`s1`]mp_tac) >>
  simp[Abbr`X`,Abbr`s1`] >>
  disch_then(Q.X_CHOOSE_THEN`bc`strip_assume_tac) >> rw[] >>
  Q.PAT_ABBREV_TAC`ell:ctbind = X` >>
  qspecl_then[`z`,`s`,`ell`]mp_tac compile_varref_append_out >>
  disch_then(Q.X_CHOOSE_THEN`bcv`strip_assume_tac) >> rw[] >>
  simp[Once SWAP_REVERSE] >> rw[EVERY_REVERSE] >>
  `ell = EL e env0` by (
    simp[Abbr`ell`,el_check_def] ) >> rw[] >>
  Cases_on`lookup_ct (z-j) (DROP j bs.stack) (DRESTRICT bs.refs cls) (EL e env0)`>>fs[] >>
  `lookup_ct z bs.stack (DRESTRICT bs.refs cls) (EL e env0) = SOME x` by (
    match_mp_tac lookup_ct_imp_incsz_many >>
    map_every qexists_tac[`z-j`,`DROP j bs.stack`,`TAKE j bs.stack`] >>
    simp[LENGTH_TAKE] ) >>
  qspecl_then[`bs`,`bc0`,`REVERSE bcv`,`bc++bc1`,`cls`,`z`,`s`,`EL e env0`,`x`]mp_tac compile_varref_thm >>
  simp[] >> strip_tac >>
  match_mp_tac(SIMP_RULE std_ss [transitive_def] RTC_TRANSITIVE) >>
  HINT_EXISTS_TAC >> simp[] >>
  qmatch_abbrev_tac`bc_next^* bs1 bs2` >>
  first_x_assum(qspecl_then[`bs1`,`bc0++REVERSE bcv`,`bc1`,`cls`,`j+1`]mp_tac) >>
  discharge_hyps >- ( simp[Abbr`bs1`] ) >>
  rw[] >>
  qmatch_assum_abbrev_tac`bc_next^* bs1 bs2'` >>
  `bs2' = bs2` by (
    rw[Abbr`bs2'`,Abbr`bs2`,Abbr`bs1`] >>
    simp[bc_state_component_equality,MAP_EQ_f] ) >>
  fs[])

val cons_closure_thm = store_thm("cons_closure_thm",
  ``∀env0 sz nk s k refs envs.
      let (s',k') = cons_closure env0 sz nk (s,k) (refs,envs) in
      ∃code.
      (s'.out = REVERSE code ++ s.out) ∧
      EVERY ($~ o is_Label) code ∧ (s'.next_label = s.next_label) ∧
      (k' = k + 1) ∧
      ∀bs bc0 bc1 cls.
        (bs.code = bc0 ++ code ++ bc1) ∧
        (bs.pc = next_addr bs.inst_length bc0) ∧
        k < LENGTH bs.stack ∧ nk + nk ≤ LENGTH bs.stack ∧
        EVERY (λn. nk + n < LENGTH bs.stack) refs ∧
        EVERY (λn. n < LENGTH env0) envs ∧
        EVERY (λn. IS_SOME (lookup_ct sz (DROP (nk+nk) bs.stack) (DRESTRICT bs.refs cls) (EL n env0))) envs
        ⇒
        bc_next^* bs (bs with <| stack :=
          LUPDATE
          (Block closure_tag
            [EL k bs.stack;
             Block 0 (MAP (λn. EL (nk+n) bs.stack) refs ++
                      MAP (λn. THE (lookup_ct sz (DROP (nk+nk) bs.stack) (DRESTRICT bs.refs cls) (EL n env0))) envs)])
          k bs.stack
                               ; pc := next_addr bs.inst_length (bc0 ++ code) |>)``,
  simp[cons_closure_def,UNCURRY] >> rpt gen_tac >>
  Q.PAT_ABBREV_TAC`s0 = s with out := X` >>
  qspecl_then[`refs`,`nk+sz`,`2 * nk + (sz + 1)`,`s0`]mp_tac FOLDL_emit_ceref_thm >>
  simp[UNCURRY] >>
  disch_then(Q.X_CHOOSE_THEN`bc`strip_assume_tac) >>
  Q.PAT_ABBREV_TAC`s1 = FOLDL (emit_ceref Y) X refs` >>
  PairCases_on`s1` >> pop_assum (assume_tac o SYM o SIMP_RULE std_ss [markerTheory.Abbrev_def]) >>
  Q.PAT_ABBREV_TAC`s2 = FOLDL (emit_ceenv X) Y envs` >>
  PairCases_on`s2` >> pop_assum (assume_tac o SYM o SIMP_RULE std_ss [markerTheory.Abbrev_def]) >>
  qspecl_then[`envs`,`env0`,`s10`,`s11`]mp_tac FOLDL_emit_ceenv_thm >>
  simp[UNCURRY] >>
  disch_then(Q.X_CHOOSE_THEN`bc1`strip_assume_tac) >>
  fs[Abbr`s0`,Once SWAP_REVERSE] >>
  rpt (qpat_assum `X = Y.next_label` kall_tac) >>
  rpt(qpat_assum`X.out = Y`kall_tac) >>
  rpt gen_tac >> strip_tac >>
  simp[Once RTC_CASES1] >> disj2_tac >>
  `bc_fetch bs = SOME (Stack (Load k))` by (
    match_mp_tac bc_fetch_next_addr >>
    qexists_tac`bc0`>>rw[] ) >>
  simp[bc_eval1_thm,bc_eval1_def] >>
  simp[bc_eval_stack_def] >>
  simp[bump_pc_def] >>
  qmatch_abbrev_tac`bc_next^* bs1 bs2` >>
  last_x_assum(qspecl_then[`bs1`,`bc0 ++ [Stack (Load k)]`]mp_tac) >>
  simp[Abbr`bs1`] >>
  discharge_hyps >- (
    simp[SUM_APPEND,FILTER_APPEND,ADD1] >>
    fsrw_tac[ARITH_ss][EVERY_MEM] >>
    rw[] >> res_tac >> DECIDE_TAC ) >>
  simp_tac (srw_ss()) [FILTER_APPEND,SUM_APPEND,ADD1] >>
  strip_tac >>
  qmatch_assum_abbrev_tac`bc_next^* bs1 bs3` >>
  qsuff_tac`bc_next^* bs3 bs2` >- metis_tac[RTC_TRANSITIVE,transitive_def] >>
  qpat_assum`bc_next^* bs1 bs3` kall_tac >>
  qunabbrev_tac`bs1` >>
  qpat_assum`bc_fetch bs = X`kall_tac >>
  match_mp_tac(SIMP_RULE std_ss [transitive_def] RTC_TRANSITIVE) >>
  qpat_assum`bs.code = X` mp_tac >>
  Q.PAT_ABBREV_TAC`bc2:bc_inst list = [x;y;z]` >> strip_tac >>
  first_x_assum(qspecl_then[`bs3`,`bc0 ++ [Stack (Load k)] ++ bc`,`bc2 ++ bc1'`,`cls`,`LENGTH refs + 1 + 2 * nk`]mp_tac) >>
  discharge_hyps >- (
    simp[Abbr`bs3`,SUM_APPEND,FILTER_APPEND] >>
    fs[EVERY_MEM] >> simp[DROP_APPEND2] ) >>
  strip_tac >> HINT_EXISTS_TAC >> simp[] >>
  pop_assum kall_tac >>
  qpat_assum`bs.code = X`mp_tac >>
  qunabbrev_tac`bc2` >>
  Q.PAT_ABBREV_TAC`x = Cons 0 j` >>
  strip_tac >>
  simp[Abbr`bs3`] >>
  qmatch_abbrev_tac`bc_next^* bs3 bs2` >>
  `bc_fetch bs3 = SOME (Stack x)` by (
    match_mp_tac bc_fetch_next_addr >>
    rw[Abbr`bs3`] >>
    qexists_tac`bc0 ++ [Stack (Load k)] ++ bc ++ bc1` >>
    lrw[SUM_APPEND,FILTER_APPEND] ) >>
  simp[Once RTC_CASES1] >> disj2_tac >>
  simp[bc_eval1_thm,bc_eval1_def] >>
  simp_tac(srw_ss()++DNF_ss)[] >>
  qpat_assum`Abbrev (bs3 = X)`mp_tac >>
  Q.PAT_ABBREV_TAC`evs:bc_value list = (REVERSE (MAP X envs)) ++ Y` >>
  strip_tac >>
  qabbrev_tac`env = Block 0 (REVERSE evs)` >>
  qexists_tac`env::EL k bs.stack::bs.stack` >>
  conj_tac >- (
    simp[Abbr`x`,bc_eval_stack_def,Abbr`bs3`,ADD1] >>
    conj_tac >- simp[Abbr`evs`] >>
    `LENGTH envs + LENGTH refs = LENGTH evs` by simp[Abbr`evs`] >>
    pop_assum SUBST1_TAC >>
    REWRITE_TAC[Once CONS_APPEND] >>
    REWRITE_TAC[GSYM APPEND_ASSOC] >>
    REWRITE_TAC[DROP_LENGTH_APPEND,TAKE_LENGTH_APPEND] >>
    simp[Abbr`env`] ) >>
  rw[bump_pc_def,Abbr`bs3`] >>
  qpat_assum`bc_fetch X = Y`kall_tac >>
  qmatch_abbrev_tac`bc_next^* bs3 bs2` >>
  `bc_fetch bs3 = SOME (Stack (Cons 3 2))` by (
    match_mp_tac bc_fetch_next_addr >>
    rw[Abbr`bs3`] >>
    Q.PAT_ABBREV_TAC`ls = X ++ bc` >>
    qexists_tac`ls ++ bc1 ++ [Stack x]` >>
    lrw[SUM_APPEND,FILTER_APPEND,ADD1,Abbr`ls`] ) >>
  simp[Once RTC_CASES1] >> disj2_tac >>
  simp[bc_eval1_thm,bc_eval1_def] >>
  simp[bc_eval_stack_def,Abbr`bs3`,bump_pc_def] >>
  qpat_assum`bc_fetch X = Y`kall_tac >>
  qmatch_abbrev_tac`bc_next^* bs3 bs2` >>
  `bc_fetch bs3 = SOME (Stack (Store k))` by (
    match_mp_tac bc_fetch_next_addr >>
    rw[Abbr`bs3`] >>
    Q.PAT_ABBREV_TAC`ls = X ++ bc` >>
    qexists_tac`ls ++ bc1 ++ [Stack x; Stack (Cons 3 2)]` >>
    lrw[SUM_APPEND,FILTER_APPEND,ADD1,Abbr`ls`] ) >>
  simp[Once RTC_CASES1] >> disj2_tac >>
  simp[bc_eval1_thm,bc_eval1_def] >>
  simp[bc_eval_stack_def,Abbr`bs3`,bump_pc_def] >>
  qpat_assum`bc_fetch X = Y`kall_tac >>
  simp[Once RTC_CASES1] >> disj1_tac >>
  simp[Abbr`bs2`,bc_state_component_equality] >>
  simp[FILTER_APPEND,SUM_APPEND] >>
  simp[LIST_EQ_REWRITE] >>
  qx_gen_tac`z` >> strip_tac >>
  simp[EL_LUPDATE] >>
  rw[] >- (
    lrw[EL_APPEND1,EL_APPEND2,Abbr`env`,Abbr`evs`] >>
    qmatch_abbrev_tac`a++b=c++d` >>
    `a = c` by (
      lrw[Abbr`a`,Abbr`c`,MAP_EQ_f,EL_CONS,PRE_SUB1] ) >>
    simp[Abbr`a`,Abbr`c`,Abbr`d`,Abbr`b`] >>
    lrw[MAP_EQ_f,DROP_APPEND1,DROP_APPEND2] ) >>
  Cases_on`z < k`>> lrw[EL_APPEND1,EL_APPEND2,EL_TAKE,EL_DROP] )

val num_fold_make_ref_thm = store_thm("num_fold_make_ref_thm",
  ``∀x nz s.
    let s' = num_fold (λs. s with out := Ref::Stack (PushInt x)::s.out) s nz in
    ∃code.
    (s'.out = REVERSE code ++ s.out) ∧
    EVERY ($~ o is_Label) code ∧
    (s'.next_label = s.next_label) ∧
    ∀bs bc0 bc1.
    (bs.code = bc0 ++ code ++ bc1) ∧
    (bs.pc = next_addr bs.inst_length bc0)
    ⇒
    ∃ps.
    (LENGTH ps = nz)∧
    ALL_DISTINCT ps ∧
    (∀p. p ∈ set ps ⇒ p ∉ FDOM bs.refs) ∧
    bc_next^* bs
    (bs with <| stack := MAP RefPtr ps ++ bs.stack
              ; refs := bs.refs |++ REVERSE (MAP (λp. (p,Number x)) ps)
              ; pc := next_addr bs.inst_length (bc0 ++ code) |>)``,
  gen_tac >> Induct >- (
    rw[Once num_fold_def,Once SWAP_REVERSE] >> rw[] >>
    qexists_tac`[]` >> rw[FUPDATE_LIST_THM] >>
    rpt (pop_assum (mp_tac o SYM)) >> rw[] ) >>
  simp[Once num_fold_def] >> gen_tac >>
  Q.PAT_ABBREV_TAC`s' = s with out := X` >>
  first_x_assum(qspec_then`s'`mp_tac) >>
  simp[] >> rw[] >>
  fs[Abbr`s'`,Once SWAP_REVERSE] >>
  rw[] >>
  simp[Once RTC_CASES1] >>
  fsrw_tac[DNF_ss][] >> disj2_tac >>
  `bc_fetch bs = SOME (Stack (PushInt x))` by (
    match_mp_tac bc_fetch_next_addr >>
    qexists_tac`bc0`>>rw[] ) >>
  rw[bc_eval1_thm,bc_eval1_def,bc_eval_stack_def,bump_pc_def] >>
  simp[Once RTC_CASES1] >>
  fsrw_tac[DNF_ss][] >> disj2_tac >>
  REWRITE_TAC[CONJ_ASSOC] >>
  qho_match_abbrev_tac`∃ps u. (P0 ps ∧ bc_next bs1 u) ∧ P ps u` >>
  `bc_fetch bs1 = SOME Ref` by (
    match_mp_tac bc_fetch_next_addr >>
    qexists_tac`bc0++[Stack (PushInt x)]`>>rw[Abbr`bs1`] >>
    simp[SUM_APPEND,FILTER_APPEND]) >>
  rw[bc_eval1_thm,bc_eval1_def,bc_eval_stack_def,bump_pc_def,Abbr`bs1`,LET_THM,Abbr`P`] >>
  qho_match_abbrev_tac`∃ps. P0 ps ∧ bc_next^* bs1 (bs2 ps)` >>
  first_x_assum(qspecl_then[`bs1`,`bc0 ++ [Stack (PushInt x);Ref]`,`bc1`]mp_tac) >>
  simp[Abbr`bs1`,SUM_APPEND,FILTER_APPEND] >>
  disch_then(Q.X_CHOOSE_THEN`ps`strip_assume_tac) >>
  qmatch_assum_abbrev_tac`bc_next^* bs1 bs3` >>
  qabbrev_tac`pps = ps ++ [LEAST n. n ∉ FDOM bs.refs]` >>
  qexists_tac`pps` >>
  `bs3 = bs2 pps` by (
    simp[Abbr`bs3`,Abbr`bs2`,bc_state_component_equality,FILTER_APPEND,SUM_APPEND,Abbr`pps`] >>
    simp[REVERSE_APPEND,FUPDATE_LIST_THM] ) >>
  fs[Abbr`P0`] >>
  simp[Abbr`pps`,ALL_DISTINCT_APPEND] >> rw[] >> fs[] >>
  numLib.LEAST_ELIM_TAC >> simp[] >>
  metis_tac[NOT_IN_FINITE,FDOM_FINITE,INFINITE_NUM_UNIV])

val FOLDL_push_lab_thm = store_thm("FOLDL_push_lab_thm",
 ``∀(defs:def list) s ls s' ls'.
   (FOLDL push_lab (s,ls) defs = (s',ls'))
   ⇒
   ∃code.
   (s'.out = REVERSE code ++ s.out) ∧
   EVERY ($~ o is_Label) code ∧
   (s'.next_label = s.next_label) ∧
   ∀bs bc0 bc1.
     (bs.code = bc0 ++ code ++ bc1) ∧
     (bs.pc = next_addr bs.inst_length bc0) ∧
     EVERY (IS_SOME o FST) defs ∧
     EVERY (IS_SOME o bc_find_loc bs o Lab o FST o THE o FST) defs
     ⇒
     (ls' = (REVERSE (MAP (SND o SND o THE o FST) defs)) ++ ls) ∧
     bc_next^* bs (bs with <| stack :=  (REVERSE (MAP (CodePtr o THE o bc_find_loc bs o Lab o FST o THE o FST) defs))++bs.stack
                            ; pc := next_addr bs.inst_length (bc0 ++ code) |>)``,
  Induct >- (
    rw[Once SWAP_REVERSE] >>
    pop_assum(assume_tac o SYM) >> fs[] ) >>
  qx_gen_tac`def` >>
  PairCases_on`def` >>
  Cases_on`def0`>> TRY(PairCases_on`x`)>>rw[push_lab_def] >>
  qmatch_assum_abbrev_tac`FOLDL push_lab (ss,lss) defs = (s',ls')` >>
  first_x_assum(qspecl_then[`ss`,`lss`,`s'`,`ls'`]mp_tac) >> simp[] >>
  strip_tac >> fs[Abbr`ss`,Once SWAP_REVERSE,Abbr`lss`] >>
  rpt gen_tac >> strip_tac >>
  `bc_fetch bs = SOME (PushPtr (Lab x0))` by (
    match_mp_tac bc_fetch_next_addr >>
    qexists_tac`bc0`>>rw[] ) >>
  simp[Once RTC_CASES1] >>
  simp_tac (srw_ss()++DNF_ss)[] >> disj2_tac >>
  rw[bc_eval1_thm,bc_eval1_def,bump_pc_def] >>
  Cases_on`bc_find_loc bs (Lab x0)`>>fs[] >>
  qmatch_abbrev_tac`P ∧ bc_next^* bs1 bs2` >>
  first_x_assum(qspecl_then[`bs1`,`bc0 ++ [PushPtr (Lab x0)]`,`bc1`]mp_tac) >>
  discharge_hyps >- (
    unabbrev_all_tac >>
    simp[FILTER_APPEND,SUM_APPEND,ADD1] >>
    rfs[EVERY_MEM,bc_find_loc_def] ) >>
  simp[Abbr`P`] >> strip_tac >>
  qmatch_assum_abbrev_tac`bc_next^* bs1 bs2'` >>
  `bs2' = bs2` by (
    unabbrev_all_tac >>
    srw_tac[ARITH_ss][bc_state_component_equality,MAP_EQ_f,bc_find_loc_def,FILTER_APPEND,SUM_APPEND,ADD1] ) >>
  rw[])

val FOLDL_cons_closure_thm = store_thm("FOLDL_cons_closure_thm",
  ``∀ecs env0 sz nk s k.
    let (s',k') = FOLDL (cons_closure env0 sz nk) (s,k) ecs in
    ∃code.
    (s'.out = REVERSE code ++ s.out) ∧
    EVERY ($~ o is_Label) code ∧ (s'.next_label = s.next_label) ∧
    (k' = k + LENGTH ecs) ∧
    ∀bs bc0 bc1 cls.
    (bs.code = bc0 ++ code ++ bc1) ∧
    (bs.pc = next_addr bs.inst_length bc0) ∧
    (LENGTH ecs = nk - k) ∧ k ≤ nk ∧ nk + nk ≤ LENGTH bs.stack ∧
    EVERY (λ(recs,envs).
      EVERY (λn. n < LENGTH env0) envs ∧
      EVERY (λn. IS_SOME (lookup_ct sz (DROP (nk + nk) bs.stack) (DRESTRICT bs.refs cls) (EL n env0))) envs ∧
      EVERY (λn. nk + n < LENGTH bs.stack) recs) ecs
    ⇒
    let bvs = MAP2 (λp (recs,envs). Block closure_tag [p;
        Block 0
          (MAP (λn. EL (nk + n) bs.stack) recs ++
           MAP (λn. THE (lookup_ct sz (DROP (nk + nk) bs.stack) (DRESTRICT bs.refs cls) (EL n env0))) envs)])
              (TAKE (nk-k) (DROP k bs.stack)) ecs in
    bc_next^* bs
    (bs with <| stack := TAKE k bs.stack ++ bvs ++ (DROP nk bs.stack)
              ; pc := next_addr bs.inst_length (bc0 ++ code) |>)``,
  Induct >- (
    simp[Once SWAP_REVERSE,LENGTH_NIL_SYM,LENGTH_NIL] >> rw[] >>
    rpt (first_x_assum (mp_tac o SYM)) >> simp[] >>
    `k = nk` by fsrw_tac[ARITH_ss][] >> simp[]) >>
  qx_gen_tac`e` >> PairCases_on`e` >>
  fs[LET_THM,UNCURRY] >>
  rpt gen_tac >>
  qspecl_then[`env0`,`sz`,`nk`,`s`,`k`,`e0`,`e1`]mp_tac cons_closure_thm >>
  simp[UNCURRY] >>
  disch_then(Q.X_CHOOSE_THEN`bc`strip_assume_tac) >> simp[] >>
  qmatch_assum_abbrev_tac`(FST p).out = REVERSE bc ++ s.out` >>
  first_x_assum(qspecl_then[`env0`,`sz`,`nk`,`FST p`,`SND p`]mp_tac) >>
  disch_then(Q.X_CHOOSE_THEN`bcf`strip_assume_tac) >>
  PairCases_on`p`>>fs[Once SWAP_REVERSE,ADD1] >> simp[] >>
  rpt gen_tac >> strip_tac >>
  last_x_assum(qspecl_then[`bs`,`bc0`,`bcf ++ bc1`,`cls`]mp_tac) >>
  simp[] >>
  rw[] >>
  qmatch_assum_abbrev_tac`bc_next^* bs bs1` >>
  match_mp_tac(SIMP_RULE std_ss [transitive_def] RTC_TRANSITIVE) >>
  qexists_tac`bs1` >> simp[] >>
  qpat_assum`Abbrev(bs1 = X)`mp_tac >>
  Q.PAT_ABBREV_TAC`f1 = Block 3 Y` >> strip_tac >>
  first_x_assum(qspecl_then[`bs1`,`bc0 ++ bc`,`bc1`,`cls`]mp_tac) >>
  `DROP (2 * nk) (LUPDATE f1 k bs.stack) = DROP (2 * nk) bs.stack` by (
    lrw[LIST_EQ_REWRITE,EL_DROP,EL_LUPDATE] ) >>
  discharge_hyps >- ( simp[Abbr`bs1`] ) >>
  qmatch_abbrev_tac`bc_next^* bs1 bs2' ⇒ bc_next^* bs1 bs2` >>
  qsuff_tac`bs2' = bs2`>-rw[] >>
  simp[Abbr`bs2'`,Abbr`bs2`,bc_state_component_equality,Abbr`bs1`,MAP2_MAP] >>
  simp[LIST_EQ_REWRITE] >>
  qx_gen_tac`z` >> strip_tac >>
  Cases_on`z<k`>>lrw[EL_APPEND1,EL_TAKE,EL_LUPDATE] >>
  `TAKE (nk-k) (DROP k bs.stack) = EL k bs.stack::(TAKE(nk-k-1) (DROP (k+1) bs.stack))` by (
    lrw[LIST_EQ_REWRITE,EL_TAKE,EL_DROP] >>
    Cases_on`x=0`>>lrw[EL_CONS,PRE_SUB1,EL_TAKE,EL_DROP] ) >>
  simp[] >>
  Cases_on`z=k`>>lrw[EL_APPEND1,EL_APPEND2,EL_TAKE,EL_LUPDATE] >>
  REWRITE_TAC[GSYM APPEND_ASSOC] >>
  lrw[EL_APPEND2,EL_CONS,PRE_SUB1] >>
  `DROP nk (LUPDATE f1 k bs.stack) = DROP nk bs.stack` by (
    lrw[LIST_EQ_REWRITE,EL_DROP,EL_LUPDATE] ) >>
  `DROP (k+1) (LUPDATE f1 k bs.stack) = DROP (k+1) bs.stack` by (
    lrw[LIST_EQ_REWRITE,EL_DROP,EL_LUPDATE] ) >>
  simp[])

val num_fold_update_refptr_thm = store_thm("num_fold_update_refptr_thm",
  ``∀nz nk s k.
    let (s',k') = num_fold (update_refptr nk) (s,k) nz in
    ∃code.
    (s'.out = REVERSE code ++ s.out) ∧
    EVERY ($~ o is_Label) code ∧
    (s'.next_label = s.next_label) ∧
    (k' = k + nz) ∧
    ∀bs bc0 bc1 vs rs st.
    (bs.code = bc0 ++ code ++ bc1) ∧
    (bs.pc = next_addr bs.inst_length bc0) ∧
    (bs.stack = vs ++ (MAP RefPtr rs) ++ st) ∧
    (∀r. MEM r rs ⇒ r ∈ FDOM bs.refs) ∧ ALL_DISTINCT rs ∧
    (LENGTH rs = nk) ∧ (LENGTH vs = nk) ∧
    (k + nz = nk)
    ⇒
    bc_next^* bs
    (bs with <| refs := bs.refs |++ ZIP (DROP k rs,DROP k vs)
              ; pc := next_addr bs.inst_length (bc0 ++ code)|>)``,
  Induct >- (
    rw[Once num_fold_def,Once SWAP_REVERSE,LENGTH_NIL,FUPDATE_LIST_THM] >>
    rw[] >> fsrw_tac[ARITH_ss][FUPDATE_LIST_THM] >>
    metis_tac[DROP_LENGTH_NIL,ZIP,FUPDATE_LIST_THM,with_same_pc,with_same_refs,RTC_CASES1,MAP2]) >>
  rw[Once num_fold_def,update_refptr_def] >>
  first_x_assum(qspecl_then[`nk`,`s'''`,`k+1`]mp_tac) >>
  simp[] >> unabbrev_all_tac >> simp[] >>
  disch_then strip_assume_tac >>
  simp[Once SWAP_REVERSE] >>
  ntac 3 strip_tac >>
  map_every qx_gen_tac[`vvs`,`rrs`] >> rpt strip_tac >>
  qmatch_assum_abbrev_tac`bs.code = bc0 ++ ls ++ code ++ bc1` >>
  qpat_assum`X = (s'''',k')`kall_tac >>
  simp[Once RTC_CASES1] >> disj2_tac >>
  qmatch_assum_abbrev_tac`Abbrev (ls = [x1;x2;x3])` >>
  `bc_fetch bs = SOME x1` by (
    match_mp_tac bc_fetch_next_addr >>
    qexists_tac`bc0`>>rw[Abbr`x1`,Abbr`ls`] ) >>
  simp[bc_eval1_thm,bc_eval1_def,Abbr`x1`,bc_eval_stack_def,ADD1] >>
  fsrw_tac[ARITH_ss][ADD1] >>
  simp[bump_pc_def,EL_CONS,EL_APPEND1,PRE_SUB1,EL_APPEND2] >>
  qmatch_abbrev_tac`bc_next^* bs1 bs2` >>
  simp[Once RTC_CASES1] >> disj2_tac >>
  `bc_fetch bs1 = SOME x2` by (
    match_mp_tac bc_fetch_next_addr >>
    qexists_tac`bc0 ++ [HD ls]` >>
    lrw[Abbr`bs1`,Abbr`ls`,Abbr`x2`,SUM_APPEND,FILTER_APPEND] ) >>
  simp[bc_eval1_thm,bc_eval1_def,Abbr`x2`,bc_eval_stack_def] >>
  simp[Abbr`bs1`,bump_pc_def] >>
  lrw[EL_CONS,PRE_SUB1,EL_APPEND1] >>
  rpt (qpat_assum `bc_fetch X = Y` kall_tac) >>
  qmatch_abbrev_tac`bc_next^* bs1 bs2` >>
  simp[Once RTC_CASES1] >> disj2_tac >>
  `bc_fetch bs1 = SOME x3` by (
    match_mp_tac bc_fetch_next_addr >>
    qexists_tac`bc0 ++ [HD ls; HD(TL ls)]` >>
    lrw[Abbr`bs1`,Abbr`ls`,Abbr`x3`,SUM_APPEND,FILTER_APPEND] ) >>
  simp[bc_eval1_thm,bc_eval1_def,Abbr`x3`,bc_eval_stack_def,Abbr`bs1`,bump_pc_def] >>
  fsrw_tac[DNF_ss,ARITH_ss][] >>
  qpat_assum `bc_fetch X = Y` kall_tac >>
  simp[EL_MAP] >>
  conj_asm1_tac >- (
    first_x_assum match_mp_tac >>
    simp[MEM_EL] >>
    qexists_tac`k` >>
    simp[] ) >>
  qmatch_abbrev_tac`bc_next^* bs1 bs2` >>
  first_x_assum(qspecl_then[`bs1`,`bc0 ++ ls`,`bc1`,`vvs`,`rrs`,`st`]mp_tac) >>
  simp[Abbr`bs1`,Abbr`ls`,FILTER_APPEND,SUM_APPEND,ADD1] >>
  qmatch_abbrev_tac`bc_next^* bs3 bs4 ⇒ bc_next^* bs3 bs2` >>
  qsuff_tac `bs4 = bs2` >- rw[] >>
  unabbrev_all_tac >>
  simp[bc_state_component_equality,FILTER_APPEND,SUM_APPEND] >>
  `DROP k rrs = EL k rrs :: DROP (k + 1) rrs` by (
     simp[GSYM ADD1,DROP_CONS_EL] ) >>
  `DROP k vvs = EL k vvs :: DROP (k + 1) vvs` by (
     simp[GSYM ADD1,DROP_CONS_EL] ) >>
  simp[FUPDATE_LIST_THM])

val num_fold_store_thm = store_thm("num_fold_store_thm",
  ``∀nz k s. let s' = num_fold (λs. s with out := Stack (Store k)::s.out) s nz in
    ∃code.
      (s'.out = REVERSE code ++ s.out) ∧
      (s'.next_label = s.next_label) ∧
      EVERY ($~ o is_Label) code ∧
      ∀bs bc0 bc1 vs ws st.
      (bs.code = bc0 ++ code ++ bc1) ∧
      (bs.pc = next_addr bs.inst_length bc0) ∧
      (bs.stack = vs ++ ws ++ st) ∧
      (LENGTH vs -1 = k) ∧ nz ≤ LENGTH vs ∧ nz ≤ LENGTH ws
      ⇒
      bc_next^* bs
      (bs with <| stack := (DROP nz vs) ++ (TAKE nz vs) ++ (DROP nz ws) ++ st
                ; pc := next_addr bs.inst_length (bc0 ++ code) |>)``,
  Induct >- (
    rw[Once num_fold_def,Once SWAP_REVERSE] >>
    lrw[] >>
    metis_tac[RTC_CASES1,with_same_stack,with_same_pc] ) >>
  simp[Once num_fold_def] >> rw[] >>
  Q.PAT_ABBREV_TAC`s' = s with out := Y` >>
  first_x_assum(qspecl_then[`k`,`s'`]mp_tac) >>
  simp[] >>
  disch_then strip_assume_tac >>
  simp[Abbr`s'`,Once SWAP_REVERSE] >>
  rpt strip_tac >>
  Cases_on`vs=[]` >- (
    fsrw_tac[ARITH_ss][ADD1] ) >>
  `bc_fetch bs = SOME (Stack (Store k))`  by (
    match_mp_tac bc_fetch_next_addr >>
    qexists_tac`bc0` >> rw[] ) >>
  rw[Once RTC_CASES1] >> disj2_tac >>
  rw[bc_eval1_thm,bc_eval1_def] >>
  Cases_on`vs`>>fs[] >>
  simp[bc_eval_stack_def,bump_pc_def,ADD1] >>
  lrw[TAKE_APPEND1,DROP_APPEND1,DROP_APPEND2,ADD1] >>
  qmatch_abbrev_tac`bc_next^* bs1 bs2` >>
  fsrw_tac[ARITH_ss][ADD1] >>
  qmatch_assum_rename_tac`bs.stack = (v::(vs ++ ws ++ st))`[] >>
  rfs[] >>
  first_x_assum(qspecl_then[`bs1`,`bc0++[Stack (Store (LENGTH vs))]`,`bc1`,`vs++[v]`,`(DROP 1 ws)`,`st`]mp_tac) >>
  simp[Abbr`bs1`,SUM_APPEND,FILTER_APPEND] >>
  qmatch_abbrev_tac`bc_next^* bs1 bs4 ⇒ bc_next^* bs1 bs2` >>
  `bs4 = bs2` by (
    unabbrev_all_tac >>
    simp[bc_state_component_equality,SUM_APPEND,FILTER_APPEND] >>
    lrw[TAKE_TAKE,TAKE_APPEND1,DROP_DROP,DROP_APPEND1] ) >>
  rw[])

val compile_closures_thm = store_thm("compile_closures_thm",
  ``∀env sz s (defs:def list).
    let s' = compile_closures env sz s defs in
    ∃code.
      (s'.out = REVERSE code ++ s.out) ∧
      EVERY ($~ o is_Label) code ∧ (s'.next_label = s.next_label) ∧
      ∀bs bc0 bc1 cls.
        (bs.code = bc0 ++ code ++ bc1) ∧
        (bs.pc = next_addr bs.inst_length bc0) ∧
        EVERY (IS_SOME o FST) defs ∧
        EVERY (IS_SOME o bc_find_loc bs o Lab o FST o THE o FST) defs ∧
        EVERY ((λ(recs,envs).
          EVERY (λn. n < LENGTH env) envs ∧
          EVERY (λn. IS_SOME (lookup_ct sz bs.stack (DRESTRICT bs.refs cls) (EL n env))) envs ∧
          EVERY (λn. n < LENGTH defs) recs)
               o SND o SND o THE o FST) defs
        ⇒
        ∃rs.
        let bvs = MAP
        ((λ(l,cc,(recs,envs)). Block closure_tag
          [CodePtr (THE (bc_find_loc bs (Lab l)))
          ; Block 0 (MAP (λn. RefPtr (EL n rs)) recs ++
                     MAP (λn. THE (lookup_ct sz bs.stack (DRESTRICT bs.refs cls) (EL n env))) envs)])
        o THE o FST) defs in
        (LENGTH rs = LENGTH defs) ∧ ALL_DISTINCT rs ∧ (∀r. MEM r rs ⇒ r ∉ FDOM bs.refs) ∧
        bc_next^* bs
        (bs with <| stack := bvs++bs.stack
                  ; pc := next_addr bs.inst_length (bc0 ++ code)
                  ; refs := bs.refs |++ ZIP(rs,bvs)
                  |>)``,
  rw[compile_closures_def] >>
  qspecl_then[`i0`,`nk`,`s`]mp_tac num_fold_make_ref_thm >>
  simp[] >> disch_then(Q.X_CHOOSE_THEN`bmr`strip_assume_tac) >>
  qpat_assum`Abbrev (s' = X)`kall_tac >>
  qspecl_then[`REVERSE defs`,`s'`,`[]`,`s''`,`ecs`]mp_tac FOLDL_push_lab_thm >>
  simp[] >> disch_then(Q.X_CHOOSE_THEN`bpl`strip_assume_tac) >>
  qpat_assum`FOLDL (push_lab) X Y = Z`kall_tac >>
  qspecl_then[`ecs`,`env`,`sz`,`nk`,`s''`,`0`]mp_tac FOLDL_cons_closure_thm >>
  simp[] >> disch_then(Q.X_CHOOSE_THEN`bcc`strip_assume_tac) >>
  qpat_assum`FOLDL X Y ecs = Z`kall_tac >>
  qspecl_then[`nk`,`nk`,`s'''`,`0`]mp_tac num_fold_update_refptr_thm >>
  simp[] >> disch_then(Q.X_CHOOSE_THEN`bur`strip_assume_tac) >>
  qspecl_then[`nk`,`k''`,`s''''`]mp_tac num_fold_store_thm >>
  simp[] >> disch_then(Q.X_CHOOSE_THEN`bsr`strip_assume_tac) >>
  simp[Once SWAP_REVERSE] >>
  rpt strip_tac >>
  last_x_assum(qspecl_then[`bs`,`bc0`,`bpl ++ bcc ++ bur ++ bsr ++ bc1`]mp_tac)>>
  simp[] >> disch_then(Q.X_CHOOSE_THEN`rs`strip_assume_tac) >>
  qmatch_assum_abbrev_tac`bc_next^* bs bs1` >>
  last_x_assum(qspecl_then[`bs1`,`bc0++bmr`,`bcc ++ bur ++ bsr ++ bc1`]mp_tac)>>
  discharge_hyps >- (
    simp[Abbr`bs1`,EVERY_REVERSE] >>
    rfs[EVERY_MEM,bc_find_loc_def] ) >>
  strip_tac >>
  qmatch_assum_abbrev_tac`bc_next^* bs1 bs2` >>
  last_x_assum(qspecl_then[`bs2`,`bc0++bmr++bpl`,`bur ++ bsr ++ bc1`,`cls`]mp_tac)>>
  discharge_hyps >- (
    simp[Abbr`bs2`] >>
    conj_tac >- simp[Abbr`bs1`] >>
    conj_tac >- simp[Abbr`bs1`] >>
    simp[EVERY_REVERSE,MAP_REVERSE] >>
    fs[EVERY_MEM,MEM_MAP,GSYM LEFT_FORALL_IMP_THM] >>
    qx_gen_tac`e` >> strip_tac >>
    first_x_assum(qspec_then`e`mp_tac) >>
    simp[UNCURRY,Abbr`bs1`] >> strip_tac >>
    reverse conj_tac >- (
      rpt strip_tac >>
      `n < nk` by PROVE_TAC[]>>
      simp[] ) >>
    rpt strip_tac >>
    qmatch_abbrev_tac`IS_SOME lc` >>
    qsuff_tac`lc = lookup_ct sz bs.stack (DRESTRICT bs.refs cls) (EL n env)`>-rw[] >>
    simp[Abbr`lc`] >>
    Q.PAT_ABBREV_TAC`ls:bc_value list = DROP (2 * nk) st` >>
    `ls = bs.stack` by (
      lrw[Abbr`ls`,LIST_EQ_REWRITE,EL_DROP,EL_APPEND2] ) >>
    simp[] >>
    match_mp_tac lookup_ct_change_refs >>
    rw[] >>
    simp[FLOOKUP_DEF,FDOM_FUPDATE_LIST,MEM_MAP,EXISTS_PROD,DRESTRICT_DEF] >>
    `¬MEM p rs` by (
      `IS_SOME (lookup_ct sz bs.stack (DRESTRICT bs.refs cls) (EL n env))` by (
        first_x_assum match_mp_tac >> rw[] ) >>
      pop_assum mp_tac >>
      qpat_assum`EL n env = X`SUBST1_TAC >>
      simp[el_check_def,FLOOKUP_DEF,DRESTRICT_DEF] >> rw[] >>
      metis_tac[] ) >>
    simp[] >> rw[] >>
    match_mp_tac EQ_SYM >>
    match_mp_tac FUPDATE_LIST_APPLY_NOT_MEM_matchable >>
    simp[MAP_REVERSE,MAP_MAP_o,combinTheory.o_DEF] ) >>
  strip_tac >> rfs[] >>
  qmatch_assum_abbrev_tac`bc_next^* bs2 bs3` >>
  qpat_assum`Abbrev(bs3=X)`mp_tac >>
  simp[MAP_REVERSE] >>
  Q.PAT_ABBREV_TAC`vs:bc_value list = MAP2 X Y Z` >> strip_tac >>
  last_x_assum(qspecl_then[`bs3`,`bc0++bmr++bpl++bcc`,`bsr++bc1`,`vs`,`rs`,`bs.stack`]mp_tac) >>
  discharge_hyps >- (
    simp[Abbr`bs3`,Abbr`bs2`,Abbr`bs1`,GSYM MAP_REVERSE] >>
    conj_tac >- (
      REWRITE_TAC[GSYM APPEND_ASSOC] >>
      Q.PAT_ABBREV_TAC`ls = X ++ bs.stack` >>
      simp[Abbr`nk`,DROP_APPEND2] ) >>
    simp[FDOM_FUPDATE_LIST,MAP_REVERSE,MEM_MAP,EXISTS_PROD] >>
    simp[Abbr`vs`,Abbr`nk`,LENGTH_MAP2] ) >>
  strip_tac >>
  qmatch_assum_abbrev_tac`bc_next^* bs3 bs4` >>
  last_x_assum(qspecl_then[`bs4`,`bc0++bmr++bpl++bcc++bur`,`bc1`,`vs`,`MAP RefPtr rs`,`bs.stack`]mp_tac) >>
  discharge_hyps >- (
    simp[Abbr`bs4`,Abbr`bs3`,Abbr`bs2`,Abbr`bs1`,Abbr`k''`,GSYM MAP_REVERSE,Abbr`nk`] >>
    REWRITE_TAC[GSYM APPEND_ASSOC] >>
    Q.PAT_ABBREV_TAC`ls = MAP RefPtr rs ++ X` >>
    simp[DROP_APPEND2,Abbr`vs`,LENGTH_MAP2] ) >>
  strip_tac >>
  qmatch_assum_abbrev_tac`bc_next^* bs4 bs5` >>
  simp[markerTheory.Abbrev_def] >>
  qexists_tac`rs` >> simp[] >>
  qho_match_abbrev_tac`bc_next^* bs bs6` >>
  qsuff_tac`bs5 = bs6` >- metis_tac[RTC_TRANSITIVE,transitive_def] >>
  simp[Abbr`bs1`,Abbr`bs2`,Abbr`bs3`,Abbr`bs4`,Abbr`bs5`,Abbr`bs6`,bc_state_component_equality] >>
  rpt(qpat_assum`bc_next^* X Y`kall_tac)>>
  conj_asm1_tac >- (
    simp[Abbr`vs`,GSYM MAP_REVERSE,Abbr`nk`,TAKE_LENGTH_ID_rwt,DROP_LENGTH_NIL_rwt] >>
    REWRITE_TAC[GSYM APPEND_ASSOC] >>
    Q.PAT_ABBREV_TAC`ls = MAP RefPtr rs ++ X` >>
    simp[TAKE_APPEND2,EL_APPEND1,DROP_APPEND2,MAP2_MAP,TAKE_LENGTH_ID_rwt,DROP_LENGTH_NIL_rwt] >>
    simp[ZIP_MAP,MAP_MAP_o,combinTheory.o_DEF,MAP_EQ_f,UNCURRY] >>
    simp[bc_find_loc_def] >>
    simp[APPEND_LENGTH_EQ,MAP_EQ_f] >>
    gen_tac >> strip_tac >>
    conj_tac >> rpt strip_tac >- (
      simp[EL_APPEND2,Abbr`ls`] >>
      Cases_on`n < LENGTH rs`>>simp[EL_APPEND1,EL_MAP] >>
      fs[EVERY_MEM,UNCURRY] >>
      metis_tac[prim_recTheory.LESS_REFL] ) >>
    simp[Abbr`ls`,DROP_APPEND2] >>
    AP_TERM_TAC >>
    match_mp_tac lookup_ct_change_refs >>
    simp[] >> rw[] >> fs[FLOOKUP_DEF] >>
    simp[DRESTRICT_DEF,FDOM_FUPDATE_LIST,MEM_MAP,EXISTS_PROD] >>
    `¬MEM p rs` by (
      fs[EVERY_MEM,UNCURRY] >>
      spose_not_then strip_assume_tac >>
      res_tac >> rfs[el_check_def,FLOOKUP_DEF,DRESTRICT_DEF] ) >>
    rw[] >>
    match_mp_tac EQ_SYM >>
    match_mp_tac FUPDATE_LIST_APPLY_NOT_MEM_matchable >>
    simp[MAP_REVERSE,MAP_MAP_o,combinTheory.o_DEF] ) >>
  pop_assum (SUBST1_TAC o SYM) >>
  `LENGTH vs = LENGTH defs` by simp[Abbr`vs`,LENGTH_MAP2] >>
  simp[Abbr`nk`,DROP_LENGTH_NIL_rwt,TAKE_LENGTH_ID_rwt] >>
  match_mp_tac FUPDATE_LIST_CANCEL >>
  lrw[MEM_MAP,MEM_ZIP,EXISTS_PROD] >>
  fs[MEM_EL] >> PROVE_TAC[] )

val compile_closures_next_label_inc = store_thm("compile_closures_next_label_inc",
  ``∀env sz cs (defs:def list). (compile_closures env sz cs defs).next_label = cs.next_label``,
  rpt gen_tac >>
  qspecl_then[`env`,`sz`,`cs`,`defs`]strip_assume_tac compile_closures_thm >>
  fs[LET_THM])
val _ = export_rewrites["compile_closures_next_label_inc"]

val _ = Parse.overload_on("retbc",``λj k. [Stack (Pops (k + 1)); Stack (Load 1); Stack (Store (j + 2)); Stack (Pops (j + 1)); Return]``)
val _ = Parse.overload_on("jmpbc",``λn j k. [Stack (Load (n + k + 2)); Stack (Load (n + 1)); Stack (El 1); Stack (Load (n + 2)); Stack (El 0);
                                             Stack (Shift (n + 4) (k + j + 3)); JumpPtr]``)
val _ = Parse.overload_on("callbc",``λn. [Stack (Load n); Stack (El 1); Stack (Load (n + 1)); Stack (El 0); CallPtr]``)

val pushret_append_out = store_thm("pushret_append_out",
  ``∀t s. ∃bc. ((pushret t s).out = bc ++ s.out) ∧ EVERY ($~ o is_Label) bc ∧
   (∀j k. (t = TCTail j k) ⇒ ∃bc0. bc = REVERSE (retbc j k) ++ bc0)``,
  Cases >> rw[pushret_def])

val pushret_next_label = store_thm("pushret_next_label",
  ``∀t s. (pushret t s).next_label = s.next_label``,
  Cases >> rw[pushret_def])
val _ = export_rewrites["pushret_next_label"]

val zero_exists_lemma = store_thm("zero_exists_lemma", ``(∃m. n = m + n) ∧ (∃m. n = n + m)``, rw[]>>qexists_tac`0`>>rw[])

val compile_append_out = store_thm("compile_append_out",
  ``(∀env t sz cs exp.
      ∃bc. ((compile env t sz cs exp).out = bc ++ cs.out) ∧
           cs.next_label ≤ (compile env t sz cs exp).next_label ∧
           ALL_DISTINCT (FILTER is_Label bc) ∧
           EVERY (between cs.next_label (compile env t sz cs exp).next_label) (MAP dest_Label (FILTER is_Label bc))) ∧
    (∀env t sz exp n cs xs.
      ∃bc. ((compile_bindings env t sz exp n cs xs).out = bc ++ cs.out) ∧
           cs.next_label ≤ (compile_bindings env t sz exp n cs xs).next_label ∧
           ALL_DISTINCT (FILTER is_Label bc) ∧
           EVERY (between cs.next_label (compile_bindings env t sz exp n cs xs).next_label) (MAP dest_Label (FILTER is_Label bc))) ∧
    (∀env sz cs exps.
      ∃bc. ((compile_nts env sz cs exps).out = bc ++ cs.out) ∧
           cs.next_label ≤ (compile_nts env sz cs exps).next_label ∧
           ALL_DISTINCT (FILTER is_Label bc) ∧
           EVERY (between cs.next_label (compile_nts env sz cs exps).next_label) (MAP dest_Label (FILTER is_Label bc)))``,
  ho_match_mp_tac compile_ind >>
  strip_tac >- (
    simp[compile_def] >> rw[] >> rw[] ) >>
  strip_tac >- (
    simp[compile_def] >> rw[] >>
    SIMPLE_QUANT_ABBREV_TAC[select_fun_constant``pushret``2"s"] >>
    qspecl_then[`t`,`s`]mp_tac(pushret_append_out) >> rw[] >> fs[Abbr`s`] >>
    simp[] >>
    fsrw_tac[ARITH_ss,ETA_ss,DNF_ss][FILTER_APPEND,ALL_DISTINCT_APPEND,MEM_FILTER,EVERY_MEM,MEM_MAP,is_Label_rwt,between_def] >>
    qpat_assum`∀j k. t = TCTail j k ⇒ X`kall_tac >>
    rw[] >> fs[] >> spose_not_then strip_assume_tac >> res_tac >> fsrw_tac[ARITH_ss][] >>
    `FILTER is_Label bc'' = []` by (simp[FILTER_EQ_NIL,EVERY_MEM,is_Label_rwt] >> metis_tac[]) >>
    fs[]) >>
  strip_tac >- (
    rw[compile_def] >>
    SIMPLE_QUANT_ABBREV_TAC[select_fun_constant``pushret``2"s"] >>
    qspecl_then[`t`,`s`]mp_tac(pushret_append_out) >> rw[] >> fs[Abbr`s`] >>
    fs[FILTER_APPEND,GSYM FILTER_EQ_NIL,combinTheory.o_DEF] >>
    rw[] >> fs[] >> rw[zero_exists_lemma]) >>
  strip_tac >- (
    rw[compile_def] >>
    SIMPLE_QUANT_ABBREV_TAC[select_fun_constant``pushret``2"s"] >>
    qspecl_then[`t`,`s`]mp_tac(pushret_append_out) >> rw[] >> fs[Abbr`s`] >>
    fs[FILTER_APPEND,GSYM FILTER_EQ_NIL,combinTheory.o_DEF] >>
    rw[] >> fs[] >> rw[zero_exists_lemma]) >>
  strip_tac >- (
    rw[compile_def] >>
    SIMPLE_QUANT_ABBREV_TAC[select_fun_constant``pushret``2"s"] >>
    qspecl_then[`t`,`s`]mp_tac(pushret_append_out) >> rw[] >> fs[Abbr`s`] >>
    fs[FILTER_APPEND,GSYM FILTER_EQ_NIL,combinTheory.o_DEF] >>
    rw[] >> fs[] >> rw[zero_exists_lemma]) >>
  strip_tac >- (
    rw[compile_def] >>
    Q.PAT_ABBREV_TAC`ell:ctbind = X` >>
    qspecl_then[`sz`,`cs`,`ell`]mp_tac compile_varref_append_out >>
    SIMPLE_QUANT_ABBREV_TAC[select_fun_constant``pushret``2"s"] >>
    qspecl_then[`t`,`s`]mp_tac(pushret_append_out) >> rw[] >> fs[Abbr`s`] >>
    rw[] >> fs[GSYM FILTER_EQ_NIL,combinTheory.o_DEF] >>
    fs[FILTER_APPEND] >> rw[zero_exists_lemma]) >>
  strip_tac >- (
    rw[compile_def,LET_THM,UNCURRY] >>
    SIMPLE_QUANT_ABBREV_TAC[select_fun_constant``pushret``2"s"] >>
    qspecl_then[`t`,`s`]mp_tac(pushret_append_out) >> rw[] >> fs[Abbr`s`] >>
    fs[FILTER_APPEND,GSYM FILTER_EQ_NIL,combinTheory.o_DEF] >>
    rw[] >> fs[zero_exists_lemma] ) >>
  strip_tac >- (
    rw[compile_def] >>
    SIMPLE_QUANT_ABBREV_TAC[select_fun_constant``pushret``2"s"] >>
    qspecl_then[`t`,`s`]mp_tac(pushret_append_out) >> rw[] >> fs[Abbr`s`] >>
    fs[FILTER_APPEND,GSYM FILTER_EQ_NIL,combinTheory.o_DEF] >>
    rw[] >> fs[zero_exists_lemma]) >>
  strip_tac >- (
    rw[compile_def] >>
    SIMPLE_QUANT_ABBREV_TAC[select_fun_constant``pushret``2"s"] >>
    qspecl_then[`t`,`s`]mp_tac(pushret_append_out) >> rw[] >> fs[Abbr`s`] >>
    fs[FILTER_APPEND,GSYM FILTER_EQ_NIL,combinTheory.o_DEF] >>
    rw[] >> fs[zero_exists_lemma]) >>
  strip_tac >- (
    rw[compile_def,LET_THM] >>
    fsrw_tac[ARITH_ss,ETA_ss,DNF_ss][FILTER_APPEND,ALL_DISTINCT_APPEND,MEM_FILTER,EVERY_MEM,MEM_MAP,is_Label_rwt,between_def] >>
    rw[] >> fs[] >> spose_not_then strip_assume_tac >> res_tac >> DECIDE_TAC ) >>
  strip_tac >- (
    simp[compile_def,LET_THM] >>
    rpt strip_tac >> fs[] >>
    Q.ISPECL_THEN[`env`,`sz`,`cs`,`defs`]mp_tac compile_closures_thm >>
    simp[] >> strip_tac >> fs[] >>
    pop_assum kall_tac >>
    simp[FILTER_APPEND,ALL_DISTINCT_APPEND,GSYM FILTER_EQ_NIL,combinTheory.o_DEF,ALL_DISTINCT_REVERSE,FILTER_REVERSE,MAP_REVERSE,EVERY_REVERSE] >>
    fs[GSYM FILTER_EQ_NIL,combinTheory.o_DEF] >>
    rw[] >> fs[]) >>
  strip_tac >- (
    rw[compile_def] >>
    Q.ISPECL_THEN[`env`,`sz`,`cs`,`[cb]`]mp_tac compile_closures_thm >>
    simp[] >> strip_tac >>
    SIMPLE_QUANT_ABBREV_TAC[select_fun_constant``pushret``2"s"] >>
    qspecl_then[`t`,`s`]mp_tac(pushret_append_out) >> rw[] >> fs[Abbr`s`] >>
    fs[LET_THM,GSYM FILTER_EQ_NIL,combinTheory.o_DEF,FILTER_APPEND,ALL_DISTINCT_REVERSE,FILTER_REVERSE] >> rw[] >> fs[zero_exists_lemma]) >>
  strip_tac >- (
    rw[compile_def,LET_THM,UNCURRY] >>
    BasicProvers.EVERY_CASE_TAC >> rw[] >>
    srw_tac[ARITH_ss][] >>
    qexists_tac`0`>>rw[]) >>
  strip_tac >- (
    rw[compile_def,LET_THM] >> fs[] >>
    SIMPLE_QUANT_ABBREV_TAC[select_fun_constant``pushret``2"s"] >>
    qspecl_then[`t`,`s`]mp_tac(pushret_append_out) >> rw[] >> fs[Abbr`s`] >>
    fs[FILTER_APPEND,GSYM FILTER_EQ_NIL,combinTheory.o_DEF] >> rw[] >> fs[zero_exists_lemma]) >>
  strip_tac >- (
    rw[compile_def,LET_THM] >> fs[] >>
    SIMPLE_QUANT_ABBREV_TAC[select_fun_constant``pushret``2"s"] >>
    qspecl_then[`t`,`s`]mp_tac(pushret_append_out) >> rw[] >> fs[Abbr`s`] >>
    fs[FILTER_APPEND,GSYM FILTER_EQ_NIL,combinTheory.o_DEF] >>
    fsrw_tac[DNF_ss][FILTER_APPEND,ALL_DISTINCT_APPEND,MEM_FILTER,is_Label_rwt,EVERY_MEM,between_def,MEM_MAP] >>
    rw[] >> fs[zero_exists_lemma]) >>
  strip_tac >- (
    rw[compile_def,LET_THM] >> fs[] >>
    SIMPLE_QUANT_ABBREV_TAC[select_fun_constant``pushret``2"s"] >>
    qspecl_then[`t`,`s`]mp_tac(pushret_append_out) >> rw[] >> fs[Abbr`s`] >>
    fs[FILTER_APPEND,GSYM FILTER_EQ_NIL,combinTheory.o_DEF] >>
    fsrw_tac[DNF_ss][FILTER_APPEND,ALL_DISTINCT_APPEND,MEM_FILTER,is_Label_rwt,EVERY_MEM,between_def,MEM_MAP] >>
    rw[] >> fs[zero_exists_lemma]) >>
  strip_tac >- (
    gen_tac >> Cases >> simp[compile_def] >> rw[] >> fs[] >>
    fsrw_tac[DNF_ss][FILTER_APPEND,ALL_DISTINCT_APPEND,MEM_FILTER,is_Label_rwt,EVERY_MEM,MEM_MAP,between_def] >>
    rw[] >> spose_not_then strip_assume_tac >> res_tac >> DECIDE_TAC) >>
  strip_tac >- (
    rw[compile_def,LET_THM] >>
    BasicProvers.EVERY_CASE_TAC >> rw[] >>
    fs[] >> rw[] >> fs[] >> qexists_tac`n+m`>>simp[]) >>
  strip_tac >- rw[compile_def] >>
  strip_tac >- rw[compile_def] >>
  rw[compile_def] >> fs[] >>
  fsrw_tac[DNF_ss][FILTER_APPEND,ALL_DISTINCT_APPEND,MEM_FILTER,is_Label_rwt,EVERY_MEM,between_def,MEM_MAP] >>
  rw[] >> spose_not_then strip_assume_tac >> res_tac >> DECIDE_TAC)

val Cenv_bs_imp_incsz = store_thm("Cenv_bs_imp_incsz",
  ``∀rd s env renv rsz bs bs'.
    Cenv_bs rd s env renv rsz bs ∧
    (∃v p e. (bs' = bs with <| stack := v::bs.stack; pc := p; handler := e |>))
    ⇒
    Cenv_bs rd s env renv (rsz+1) bs'``,
  rw[Cenv_bs_def,s_refs_def,good_rd_def] >> rw[] >> fs[] >>
  match_mp_tac(GEN_ALL(MP_CANON EVERY2_mono)) >>
  HINT_EXISTS_TAC >> simp[] >>
  rpt gen_tac >>
  BasicProvers.CASE_TAC >>
  imp_res_tac lookup_ct_imp_incsz >>
  simp[])

val Cenv_bs_imp_decsz = store_thm("Cenv_bs_imp_decsz",
  ``∀rd s env renv rsz bs bs'.
    Cenv_bs rd s env renv (rsz+1) bs ∧
      (CTLet (rsz+1) ∉ set renv) ∧
      (∃v p e. bs = bs' with <| stack := v::bs'.stack; pc := p; handler := e |>) ⇒
    Cenv_bs rd s env renv rsz bs'``,
  rw[Cenv_bs_def,fmap_rel_def,s_refs_def,FDOM_DRESTRICT,good_rd_def] >> fs[] >>
  fs[EVERY2_EVERY,EVERY_MEM,FORALL_PROD] >>
  rpt strip_tac >> res_tac >> pop_assum mp_tac >>
  BasicProvers.CASE_TAC >>
  pop_assum mp_tac >>
  rw[lookup_ct_incsz] >>
  rfs[MEM_ZIP,MEM_EL] >>
  metis_tac[])

val Cenv_bs_CTLet_bound = store_thm("Cenv_bs_CTLet_bound",
  ``Cenv_bs rd s env renv rsz bs ∧ MEM (CTLet n) renv ⇒ n ≤ rsz``,
  rw[Cenv_bs_def,EVERY2_EVERY,EVERY_MEM,FORALL_PROD] >>
  rfs[MEM_ZIP,MEM_EL] >> fsrw_tac[DNF_ss][] >>
  qmatch_assum_rename_tac `z < LENGTH renv`[]>>
  first_x_assum (qspec_then `z` mp_tac) >>
  qpat_assum`CTLet n = X`(assume_tac o SYM) >>
  simp[el_check_def] >>
  srw_tac[ARITH_ss][])

val Cenv_bs_pops = store_thm("Cenv_bs_pops",
  ``∀vs rd s env renv rsz bs bs'. Cenv_bs rd s env renv (rsz + LENGTH vs) bs ∧
    (∀n. MEM (CTLet n) renv ⇒ n ≤ rsz) ∧
    (∃p e. bs = bs' with <| stack := vs ++ bs'.stack; pc := p; handler := e|>)
    ⇒ Cenv_bs rd s env renv rsz bs'``,
  Induct >> rw[] >- ( fs[Cenv_bs_def,s_refs_def,good_rd_def] >> fs[]) >>
  first_x_assum match_mp_tac >>
  simp[bc_state_component_equality] >>
  qexists_tac`bs' with stack := vs ++ bs'.stack` >> rw[] >>
  match_mp_tac Cenv_bs_imp_decsz >>
  qmatch_assum_abbrev_tac`Cenv_bs rd s env renv x y` >>
  qexists_tac`y` >>
  unabbrev_all_tac >>
  fsrw_tac[ARITH_ss][ADD1,bc_state_component_equality] >>
  spose_not_then strip_assume_tac >>
  res_tac >> fsrw_tac[ARITH_ss][] )

val Cenv_bs_with_pc = store_thm("Cenv_bs_with_pc",
  ``Cenv_bs rd s env env0 sz0 (bs with pc := p) = Cenv_bs rd s env env0 sz0 bs``,
  rw[Cenv_bs_def,s_refs_with_pc])

val Cv_bv_l2a_mono = store_thm("Cv_bv_l2a_mono",
  ``∀pp.
    (∀Cv bv. Cv_bv pp Cv bv ⇒ ∀pp' l2a.
     (∀x y. ((SND pp) x = SOME y) ⇒ (l2a x = SOME y))
     ∧ (pp' = (FST pp, l2a))
     ⇒ Cv_bv pp' Cv bv) ∧
    (∀benv fs env defs.
     benv_bvs pp benv fs env defs ⇒ ∀pp' l2a.
     (∀x y. ((SND pp) x = SOME y) ⇒ (l2a x = SOME y))
     ∧ (pp' = (FST pp, l2a))
     ⇒ benv_bvs pp' benv fs env defs)``,
  gen_tac >>
  PairCases_on `pp` >> simp[] >>
  ho_match_mp_tac Cv_bv_ind >>
  strip_tac >- rw[Once Cv_bv_cases] >>
  strip_tac >- rw[Once Cv_bv_cases] >>
  strip_tac >- rw[Once Cv_bv_cases] >>
  strip_tac >- rw[Once Cv_bv_cases] >>
  strip_tac >- (
    rw[] >>
    rw[Once Cv_bv_cases] >>
    fsrw_tac[DNF_ss][EVERY2_EVERY,EVERY_MEM,FORALL_PROD] ) >>
  strip_tac >- (
    simp[] >> rpt gen_tac >> strip_tac >> strip_tac >>
    simp[Once Cv_bv_cases] >>
    strip_tac >>
    map_every qexists_tac[`fs`,`l`] >> simp[] >>
    fs[el_check_def] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  rw[Once Cv_bv_cases] >>
  fs[])

val Cv_bv_l2a_mono_mp = MP_CANON (GEN_ALL (CONJUNCT1 (SPEC_ALL Cv_bv_l2a_mono)))

val s_refs_append_code = store_thm("s_refs_append_code",
  ``∀rd s bs bs' ls.
     s_refs rd s bs ∧ (bs' = (bs with code := bs.code ++ ls))
    ⇒ s_refs rd s bs'``,
  rw[s_refs_def,fmap_rel_def,good_rd_def,FEVERY_DEF,UNCURRY] >>
  fs[EVERY2_EVERY,EVERY_MEM,FORALL_PROD] >> rpt strip_tac >>
  res_tac >>
  match_mp_tac Cv_bv_l2a_mono_mp >>
  qexists_tac `mk_pp rd bs` >>
  rw[] >> metis_tac[bc_find_loc_aux_append_code])

val Cenv_bs_append_code = store_thm("Cenv_bs_append_code",
  ``∀rd s env env0 sz0 bs bs' ls.
    Cenv_bs rd s env env0 sz0 bs ∧ (bs' = (bs with code := bs.code ++ ls)) ⇒
    Cenv_bs rd s env env0 sz0 bs'``,
  reverse(rw[Cenv_bs_def]) >- PROVE_TAC[s_refs_append_code] >>
  fs[Cenv_bs_def,EVERY2_EVERY,EVERY_MEM,FORALL_PROD,s_refs_def] >> rw[] >>
  res_tac >>
  BasicProvers.CASE_TAC >> fs[] >>
  match_mp_tac Cv_bv_l2a_mono_mp >>
  qexists_tac `mk_pp rd bs` >>
  rw[] >> metis_tac[bc_find_loc_aux_append_code])

val Cenv_bs_FUPDATE = store_thm("Cenv_bs_FUPDATE",
  ``∀rd s env env0 sz0 bs v bv bs'.
    Cenv_bs rd s env env0 sz0 bs ∧
    Cv_bv (mk_pp rd bs') v bv ∧
    (bs' = bs with stack := bv::bs.stack)
    ⇒
    Cenv_bs rd s (v::env) ((CTLet (sz0 + 1))::env0) (sz0 + 1) bs'``,
  rw[Cenv_bs_def,s_refs_def] >> fs[el_check_def] >- (
    fs[EVERY2_EVERY,EVERY_MEM,FORALL_PROD] >>
    rpt strip_tac >> res_tac >>
    pop_assum mp_tac >> BasicProvers.CASE_TAC >>
    imp_res_tac lookup_ct_imp_incsz >>
    simp[] ) >>
  fs[good_rd_def])

val Cenv_bs_FUPDATE_LIST = store_thm("Cenv_bs_FUPDATE_LIST",
  ``∀vs rd s env cenv sz bs bs bvs bs' env' cenv' sz'.
  Cenv_bs rd s env cenv sz bs ∧
  (bs' = bs with stack := bvs ++ bs.stack) ∧
  EVERY2 (Cv_bv (mk_pp rd bs')) vs bvs ∧
  (env' = vs++env) ∧
  (cenv' = (REVERSE(GENLIST(λm. CTLet(sz+m+1))(LENGTH vs)))++cenv) ∧
  (sz' = sz + LENGTH vs)
  ⇒
  Cenv_bs rd s env' cenv' sz' bs'``,
  Induct >- (
    simp[LENGTH_NIL,FUPDATE_LIST_THM] ) >>
  rw[] >>
  rw[GENLIST,REVERSE_SNOC] >> simp[ADD1] >>
  REWRITE_TAC[ADD_ASSOC] >>
  match_mp_tac Cenv_bs_FUPDATE >>
  qexists_tac`bs with stack := ys ++ bs.stack` >>
  simp[bc_state_component_equality] >>
  conj_tac >- (
    first_x_assum match_mp_tac >>
    simp[] >>
    qexists_tac`bs` >> simp[] >>
    qexists_tac`ys` >> simp[] >>
    match_mp_tac (MP_CANON (GEN_ALL EVERY2_mono)) >>
    HINT_EXISTS_TAC >>
    simp[] ) >>
  match_mp_tac Cv_bv_l2a_mono_mp >>
  HINT_EXISTS_TAC >>
  simp[])

val Cenv_bs_DOMSUB = store_thm("Cenv_bs_DOMSUB",
  ``∀rd s env renv rsz bs.
    Cenv_bs rd s env renv rsz bs ∧ (env ≠ []) ∧ (renv ≠ []) ⇒
    Cenv_bs rd s (TL env) (TL renv) rsz bs``,
  ntac 2 gen_tac >> Cases >> simp[] >> Cases >> simp[] >>
  rw[Cenv_bs_def,EVERY2_EVERY])

val Cenv_bs_change_store = store_thm("Cenv_bs_change_store",
  ``∀rd s env renv rsz bs rd' s' bs' rfs'.
    Cenv_bs rd s env renv rsz bs ∧
    s_refs rd' s' bs' ∧
    (bs' = bs with refs := rfs') ∧
    DRESTRICT bs.refs (COMPL (set rd.sm)) ⊑ DRESTRICT rfs' (COMPL (set rd'.sm)) ∧
    rd.sm ≼ rd'.sm ∧ rd.cls ⊑ rd'.cls
    ⇒
    Cenv_bs rd' s' env renv rsz bs'``,
  rw[Cenv_bs_def,EVERY2_EVERY,EVERY_MEM,FORALL_PROD] >>
  res_tac >> pop_assum mp_tac >> BasicProvers.CASE_TAC >> strip_tac >>
  qho_match_abbrev_tac`case X of NONE => F | SOME Y => Z Y` >>
  qmatch_assum_abbrev_tac`X' = SOME x` >>
  `X = X'` by (
    unabbrev_all_tac >>
    match_mp_tac lookup_ct_change_refs >>
    rpt gen_tac >> strip_tac >>
    fs[s_refs_def,good_rd_def,FEVERY_DEF,UNCURRY,el_check_def] >>
    fs[SUBMAP_DEF,FDOM_DRESTRICT,FLOOKUP_DEF,DRESTRICT_DEF] >>
    metis_tac[] ) >>
  simp[Abbr`Z`] >>
  match_mp_tac (MP_CANON (GEN_ALL (CONJUNCT1 (SPEC_ALL Cv_bv_SUBMAP)))) >>
  HINT_EXISTS_TAC >>
  simp[] >>
  fs[s_refs_def,good_rd_def,FEVERY_DEF,UNCURRY] >>
  fs[SUBMAP_DEF,SUBSET_DEF,DRESTRICT_DEF,IN_FRANGE] )

val retbc_thm = store_thm("retbc_thm",
  ``∀bs bc0 bc1 bv vs benv ret args x st bs'.
    (bs.stack = bv::vs++benv::CodePtr ret::args++x::st) ∧
    (bs.code = bc0 ++ retbc (LENGTH args) (LENGTH vs) ++ bc1) ∧
    (bs.pc = next_addr bs.inst_length bc0) ∧
    (bs' = bs with <| stack := bv::st; pc := ret |>)
    ⇒ bc_next^* bs bs'``,
  rw[] >>
  qspecl_then[`bc0`,`bs`]mp_tac bc_fetch_next_addr >> simp[] >>
  rw[Once RTC_CASES1] >> disj2_tac >>
  rw[bc_eval1_thm] >>
  rw[bc_eval1_def] >>
  rw[bc_eval_stack_def] >>
  srw_tac[ARITH_ss][] >>
  rw[bump_pc_def] >>
  lrw[DROP_APPEND1,DROP_APPEND2] >>
  qmatch_abbrev_tac`bc_next^* bs1 bs2` >>
  qspecl_then[`bc0++(TAKE 1 (retbc (LENGTH args) (LENGTH vs)))`,`bs1`]mp_tac bc_fetch_next_addr >>
  simp[Abbr`bs1`,FILTER_APPEND,SUM_APPEND] >>
  rw[Once RTC_CASES1] >> disj2_tac >>
  rw[bc_eval1_thm] >>
  rw[bc_eval1_def] >>
  rw[bc_eval_stack_def] >>
  srw_tac[ARITH_ss][] >>
  rw[bump_pc_def] >>
  qmatch_abbrev_tac`bc_next^* bs1 bs2` >>
  qspecl_then[`bc0++(TAKE 2 (retbc (LENGTH args) (LENGTH vs)))`,`bs1`]mp_tac bc_fetch_next_addr >>
  simp[Abbr`bs1`,FILTER_APPEND,SUM_APPEND] >>
  rw[Once RTC_CASES1] >> disj2_tac >>
  rw[bc_eval1_thm] >>
  rw[bc_eval1_def] >>
  simp_tac std_ss [bc_eval_stack_def] >>
  srw_tac[ARITH_ss][ADD1] >>
  rw[bump_pc_def] >>
  lrw[TAKE_APPEND1] >>
  qmatch_abbrev_tac`bc_next^* bs1 bs2` >>
  qspecl_then[`bc0++(TAKE 3 (retbc (LENGTH args) (LENGTH vs)))`,`bs1`]mp_tac bc_fetch_next_addr >>
  simp[Abbr`bs1`,FILTER_APPEND,SUM_APPEND] >>
  rw[Once RTC_CASES1] >> disj2_tac >>
  rw[bc_eval1_thm] >>
  rw[bc_eval1_def] >>
  rw[bc_eval_stack_def] >>
  srw_tac[ARITH_ss][] >>
  rw[bump_pc_def] >>
  lrw[DROP_APPEND2,DROP_APPEND1] >>
  qmatch_abbrev_tac`bc_next^* bs1 bs2` >>
  qspecl_then[`bc0++(TAKE 4 (retbc (LENGTH args) (LENGTH vs)))`,`bs1`]mp_tac bc_fetch_next_addr >>
  simp[Abbr`bs1`,FILTER_APPEND,SUM_APPEND] >>
  rw[Once RTC_CASES1] >> disj2_tac >>
  rw[bc_eval1_thm] >>
  rw[bc_eval1_def])

val code = ``jmpbc (LENGTH (args1 :bc_value list)) (LENGTH (args : bc_value list)) (LENGTH (vs : bc_value list))``
val jmpbc_thm = store_thm("jmpbc_thm",
  ``∀bs bc0 bc1 bv vs benv ret args cl ct x y args1 st bs'.
    (bs.stack = args1 ++ (Block ct [CodePtr x;y])::vs++benv::ret::args++cl::st) ∧
    (bs.code = bc0 ++ jmpbc (LENGTH args1) (LENGTH args) (LENGTH vs) ++ bc1) ∧
    (bs.pc = next_addr bs.inst_length bc0) ∧
    (bs' = bs with <| stack := y::ret::args1++(Block ct [CodePtr x;y])::st; pc := x |>)
    ⇒ bc_next^* bs bs'``,
  rw[] >>
  qspecl_then[`bc0`,`bs`]mp_tac bc_fetch_next_addr >> simp[] >>
  rw[Once RTC_CASES1] >> disj2_tac >>
  rw[bc_eval1_thm] >>
  rw[bc_eval1_def] >>
  rw[bc_eval_stack_def] >>
  srw_tac[ARITH_ss][] >>
  rw[bump_pc_def] >>
  lrw[EL_APPEND2,EL_APPEND1] >>
  qmatch_abbrev_tac`bc_next^* bs1 bs2` >>
  qspecl_then[`bc0++(TAKE 1 ^code)`,`bs1`]mp_tac bc_fetch_next_addr >>
  simp[Abbr`bs1`,FILTER_APPEND,SUM_APPEND] >>
  rw[Once RTC_CASES1] >> disj2_tac >>
  rw[bc_eval1_thm] >>
  rw[bc_eval1_def] >>
  rw[bc_eval_stack_def] >>
  srw_tac[ARITH_ss][] >>
  rw[bump_pc_def] >>
  lrw[EL_APPEND1,EL_APPEND2,EL_CONS] >>
  srw_tac[ARITH_ss][GSYM ADD1] >>
  qmatch_abbrev_tac`bc_next^* bs1 bs2` >>
  qspecl_then[`bc0++(TAKE 2 ^code)`,`bs1`]mp_tac bc_fetch_next_addr >>
  simp[Abbr`bs1`,FILTER_APPEND,SUM_APPEND,ADD1] >>
  rw[Once RTC_CASES1] >> disj2_tac >>
  rw[bc_eval1_thm] >>
  rw[bc_eval1_def] >>
  simp_tac std_ss [bc_eval_stack_def] >>
  srw_tac[ARITH_ss][ADD1] >>
  rw[bump_pc_def] >>
  qmatch_abbrev_tac`bc_next^* bs1 bs2` >>
  qspecl_then[`bc0++(TAKE 3 ^code)`,`bs1`]mp_tac bc_fetch_next_addr >>
  simp[Abbr`bs1`,FILTER_APPEND,SUM_APPEND] >>
  rw[Once RTC_CASES1] >> disj2_tac >>
  rw[bc_eval1_thm] >>
  rw[bc_eval1_def] >>
  rw[bc_eval_stack_def] >>
  srw_tac[ARITH_ss][] >>
  rw[bump_pc_def] >>
  lrw[EL_APPEND1,EL_APPEND2,EL_CONS] >>
  REWRITE_TAC[TWO,ONE,Once ADD_SYM,prim_recTheory.PRE] >>
  REWRITE_TAC[Once ADD_SYM] >>
  REWRITE_TAC[GSYM ADD_SUC] >>
  srw_tac[ARITH_ss][] >>
  qmatch_abbrev_tac`bc_next^* bs1 bs2` >>
  qspecl_then[`bc0++(TAKE 4 ^code)`,`bs1`]mp_tac bc_fetch_next_addr >>
  simp[Abbr`bs1`,FILTER_APPEND,SUM_APPEND,ADD1] >>
  rw[Once RTC_CASES1] >> disj2_tac >>
  rw[bc_eval1_thm] >>
  rw[bc_eval1_def] >>
  rw[bc_eval_stack_def] >>
  rw[bump_pc_def] >>
  qmatch_abbrev_tac`bc_next^* bs1 bs2` >>
  qspecl_then[`bc0++(TAKE 5 ^code)`,`bs1`]mp_tac bc_fetch_next_addr >>
  simp[Abbr`bs1`,FILTER_APPEND,SUM_APPEND,ADD1] >>
  rw[Once RTC_CASES1] >> disj2_tac >>
  rw[bc_eval1_thm] >>
  rw[bc_eval1_def] >>
  simp[bc_eval_stack_def] >>
  lrw[TAKE_APPEND2,DROP_APPEND2,TAKE_APPEND1] >>
  rw[bump_pc_def] >>
  ntac 5 (pop_assum kall_tac) >>
  qmatch_abbrev_tac`bc_next^* bs1 bs2` >>
  qspecl_then[`bc0++(TAKE 6 ^code)`,`bs1`]mp_tac bc_fetch_next_addr >>
  simp[Abbr`bs1`,FILTER_APPEND,SUM_APPEND,ADD1] >>
  rw[Once RTC_CASES1] >> disj2_tac >>
  rw[bc_eval1_thm] >>
  rw[bc_eval1_def,Abbr`bs2`] >>
  REWRITE_TAC[GSYM CONS_APPEND,GSYM APPEND_ASSOC] >>
  rw[])

val code_for_push_def = Define`
  code_for_push rd bs bce bc0 code s s' env vs renv rsz =
    ∃bvs rf rd'.
    let bs' = bs with <| stack := (REVERSE bvs)++bs.stack; pc := next_addr bs.inst_length (bc0 ++ code); refs := rf |> in
    bc_next^* bs bs' ∧
    EVERY2 (Cv_bv (mk_pp rd' (bs' with code := bce))) vs bvs ∧
    Cenv_bs rd' s' env renv (rsz+(LENGTH vs)) (bs' with code := bce) ∧
    DRESTRICT bs.refs (COMPL (set rd.sm)) ⊑ DRESTRICT rf (COMPL (set rd'.sm)) ∧
    rd.sm ≼ rd'.sm ∧ rd.cls ⊑ rd'.cls`

val code_for_return_def = Define`
  code_for_return rd bs bce st ret sp v s s' =
    ∃bv rf rd'.
    let bs' = bs with <| stack := bv::st; pc := ret; refs := rf; handler := sp |> in
    bc_next^* bs bs' ∧
    Cv_bv (mk_pp rd' (bs' with code := bce)) v bv ∧
    s_refs rd' s' (bs' with code := bce) ∧
    DRESTRICT bs.refs (COMPL (set rd.sm)) ⊑ DRESTRICT rf (COMPL (set rd'.sm)) ∧
    rd.sm ≼ rd'.sm ∧ rd.cls ⊑ rd'.cls`

val code_for_push_return = store_thm("code_for_push_return",
  ``∀rd bs bce bc0 code s s' env v renv rsz bc1 args args1 bs' blvs benv st cl cl1 ret hdl.
    code_for_push rd (bs with code := bc0 ++ code) bce bc0 code s s' env [v] renv rsz ∧
    (bs.code = bc0 ++ code ++ retbc (LENGTH args) (LENGTH blvs) ++ bc1) ∧
    (bs.stack = blvs++benv::CodePtr ret::args++cl::st) ∧
    (bs.handler = hdl)
    ⇒
    code_for_return rd bs bce st ret hdl v s s'``,
    rw[code_for_push_def,code_for_return_def,LET_THM] >>
    qmatch_assum_rename_tac `Cv_bv pp v bv`["pp"] >>
    map_every qexists_tac [`bv`,`rf`,`rd'`] >>
    fs[Cenv_bs_def,s_refs_def,good_rd_def] >>
    qmatch_assum_abbrev_tac`bc_next^* bs0 bs1` >>
    qspecl_then[`bs0`,`bs1`,`retbc (LENGTH args) (LENGTH blvs) ++ bc1`]mp_tac (SIMP_RULE(srw_ss())[]RTC_bc_next_append_code) >>
    rw[] >>
    match_mp_tac (SIMP_RULE std_ss [transitive_def] RTC_TRANSITIVE) >>
    first_assum (exists_tac o rand o concl) >> fs[Abbr`bs0`] >>
    qpat_assum`bs.code = X`(assume_tac o SYM)>>fs[]>>
    match_mp_tac retbc_thm >>
    pop_assum(assume_tac o SYM) >>
    qexists_tac`bc0 ++ code` >> fs[Abbr`bs1`] >>
    qexists_tac`blvs`>>fs[]>>
    qexists_tac`args`>>fs[]>>
    simp[bc_state_component_equality])

val compile_labels_lemma = store_thm("compile_labels_lemma",
  ``∀env t sz cs exp bc0 cs1 cls1 code.
    (cs1 = compile env t sz cs exp) ∧
    (cs1.out = REVERSE code ++ cs.out) ∧
    (cls1 = bc0 ++ code) ∧
    ALL_DISTINCT (FILTER is_Label bc0) ∧
    EVERY (combin$C $< cs.next_label o dest_Label)
      (FILTER is_Label bc0)
    ⇒
    ALL_DISTINCT (FILTER is_Label cls1) ∧
    EVERY (combin$C $< cs1.next_label o dest_Label)
      (FILTER is_Label cls1)``,
  rpt gen_tac >> strip_tac >>
  qspecl_then[`env`,`t`,`sz`,`cs`,`exp`]mp_tac(CONJUNCT1 compile_append_out) >>
  disch_then(Q.X_CHOOSE_THEN`bc`strip_assume_tac) >>
  rpt BasicProvers.VAR_EQ_TAC >>
  fsrw_tac[DNF_ss][FILTER_APPEND,EVERY_MEM,MEM_FILTER,is_Label_rwt,
                   ALL_DISTINCT_APPEND,FILTER_REVERSE,ALL_DISTINCT_REVERSE,
                   MEM_MAP,between_def] >>
  qpat_assum`bc = REVERSE code`mp_tac >>
  Q.ISPECL_THEN[`bc`,`code`]SUBST1_TAC SWAP_REVERSE >>
  rw[FILTER_REVERSE,ALL_DISTINCT_REVERSE] >>
  spose_not_then strip_assume_tac >>
  res_tac >> DECIDE_TAC)

fun filter_asms P = POP_ASSUM_LIST (MAP_EVERY ASSUME_TAC o List.rev o List.filter P)

val Cv_bv_not_env = store_thm("Cv_bv_not_env",
  ``∀pp Cv bv. Cv_bv pp Cv bv ⇒ ∀vs. (bv = Block 0 vs) ⇒ (vs = [])``,
  gen_tac >> ho_match_mp_tac Cv_bv_only_ind >> simp[])

val compile_bindings_thm = store_thm("compile_bindings_thm",
  ``∀env t sz e n s m bc cc.
    ((compile_bindings env t sz e n s m).out = bc ++ s.out) ∧
    ((compile
       ((REVERSE(GENLIST(λi. CTLet (sz+n+1+i))m))++env)
       (case t of TCTail j k => TCTail j (k+(m+n)) | _ => t)
       (sz+(m+n))
       s e).out = cc++s.out) ⇒
    (bc = (case t of TCNonTail => [Stack(Pops (m + n))] | _ => [])++cc)``,
  Induct_on`m`>- (
    rw[compile_def,FUPDATE_LIST_THM]>>
    Cases_on`t`>>fs[]>>
    rw[]>>fs[]) >>
  rw[compile_def,GENLIST_CONS,combinTheory.o_DEF] >>
  qmatch_assum_abbrev_tac`(compile_bindings env0 t sz e n0 s m).out = bc ++ s.out` >>
  first_x_assum(qspecl_then[`env0`,`t`,`sz`,`e`,`n0`,`s`,`bc`,`cc`]mp_tac) >>
  simp[ADD1,Abbr`n0`] >>
  disch_then match_mp_tac >>
  unabbrev_all_tac >>
  pop_assum(SUBST1_TAC o SYM) >>
  simp[ADD1,FUPDATE_LIST_THM] >>
  rpt AP_TERM_TAC >> rpt AP_THM_TAC >>
  rpt AP_TERM_TAC >> rpt AP_THM_TAC >>
  rpt AP_TERM_TAC >> rpt AP_THM_TAC >>
  simp[FUN_EQ_THM] >>
  rpt AP_TERM_TAC >> rpt AP_THM_TAC >>
  rpt AP_TERM_TAC >> rpt AP_THM_TAC >>
  simp[FUN_EQ_THM])

val Cenv_bs_bind_fv = store_thm("Cenv_bs_bind_fv",
  ``∀cenv ccenv benv bve ret bvs a st fenv defs ix recs envs env pp rd bs s vs az e l e'.
    (cenv = MAP CTEnv ccenv) ∧
    (benv = Block 0 bve) ∧
    (bs.stack = benv::CodePtr ret::(REVERSE bvs)++(Block closure_tag [CodePtr a;benv])::st) ∧
    (env = REVERSE vs ++ [CRecClos fenv defs ix] ++ MAP (CRecClos fenv defs) recs ++ MAP (λn. EL n fenv) envs) ∧
    (bind_fv (az,e) (LENGTH defs) ix = (ccenv,(recs,envs),e')) ∧
    (pp = mk_pp rd bs) ∧
    benv_bvs pp bve (recs,envs) fenv defs ∧
    s_refs rd s bs ∧
    ix < LENGTH defs ∧
    (FST(EL ix defs) = SOME (l,ccenv,recs,envs)) ∧
    (bc_find_loc_aux bs.code bs.inst_length l 0 = SOME a) ∧
    EVERY2 (Cv_bv pp) vs bvs ∧ (az = LENGTH vs)
    ⇒ Cenv_bs rd s env cenv 0 bs``,
  rw[Cenv_bs_def] >>
  simp[EVERY2_EVERY] >>
  conj_asm1_tac >- (
    fsrw_tac[ARITH_ss][bind_fv_def,LET_THM] >>
    srw_tac[ARITH_ss][]) >>
  simp[EVERY_MEM,FORALL_PROD,MEM_ZIP,GSYM LEFT_FORALL_IMP_THM] >>
  gen_tac >> strip_tac >>
  simp[EL_MAP] >>
  simp[option_case_NONE_F] >>
  Cases_on`n< LENGTH vs` >- (
    fs[bind_fv_def,LET_THM] >> rw[] >>
    simp[EL_APPEND1,EL_REVERSE,PRE_SUB1,el_check_def,ADD1] >>
    fsrw_tac[ARITH_ss][EVERY2_EVERY] >>
    simp[EL_CONS,PRE_SUB1,EL_APPEND1,EL_REVERSE] >>
    fs[EVERY_MEM] >> rfs[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM] >>
    first_x_assum match_mp_tac >> simp[] ) >>
  Cases_on`n = LENGTH vs` >- (
    fs[bind_fv_def,LET_THM] >> rw[] >>
    REWRITE_TAC[GSYM APPEND_ASSOC] >>
    simp[EL_APPEND2,EL_APPEND1,el_check_def,ADD1,EL_CONS,PRE_SUB1] >>
    fsrw_tac[ARITH_ss][EVERY2_EVERY] >>
    REWRITE_TAC[GSYM APPEND_ASSOC] >>
    simp[EL_APPEND2] >>
    simp[Once Cv_bv_cases,el_check_def] >>
    qexists_tac`SND (EL ix defs)` >>
    Cases_on`EL ix defs`>>fs[] >>
    conj_tac >- simp[EVERY_FILTER,EVERY_GENLIST,EVERY_MAP] >>
    fs[Once Cv_bv_cases] >>
    simp[EVERY_MEM,MEM_EL] >>
    metis_tac[] ) >>
  fs[bind_fv_def,LET_THM] >> rw[] >>
  REWRITE_TAC[GSYM APPEND_ASSOC] >>
  simp[EL_APPEND2] >>
  Q.PAT_ABBREV_TAC`lrecs = LENGTH (FILTER X Y)` >>
  Q.PAT_ABBREV_TAC`recs:Cv list = MAP X (FILTER Y( GENLIST A Z))` >>
  `lrecs = LENGTH recs` by ( unabbrev_all_tac >> rw[]) >>
  Cases_on`n < LENGTH vs + 1 + LENGTH recs` >- (
    simp[EL_APPEND1,EL_MAP,el_check_def] >>
    rator_x_assum`benv_bvs`mp_tac >>
    simp[Once Cv_bv_cases] >> strip_tac >>
    qpat_assum`∀i. i < LENGTH recs ⇒ X`(qspec_then`n - (LENGTH vs + 1)` mp_tac) >>
    simp[] >> strip_tac >> simp[] >>
    fs[FLOOKUP_DEF,DRESTRICT_DEF] >>
    fs[s_refs_def,good_rd_def,FEVERY_DEF,UNCURRY] >>
    qpat_assum`∀x. x ∈ FDOM rd.cls ⇒ X`(qspec_then`p`mp_tac) >>
    simp[] >> strip_tac >>
    match_mp_tac (MP_CANON (CONJUNCT1 Cv_bv_syneq)) >>
    HINT_EXISTS_TAC >>
    simp[] >>
    qmatch_assum_abbrev_tac`syneq X Y` >>
    qmatch_abbrev_tac`syneq X Z` >>
    qsuff_tac`Y = Z`>-PROVE_TAC[syneq_refl] >>
    simp[Abbr`Y`,Abbr`Z`,Abbr`recs`] >>
    match_mp_tac (GSYM EL_MAP) >>
    fs[] >> DECIDE_TAC ) >>
  Q.PAT_ABBREV_TAC`lenvs = LENGTH (FILTER P (free_vars X))` >>
  Q.PAT_ABBREV_TAC`envs:num list = MAP X (FILTER Y Z)` >>
  `lenvs = LENGTH envs` by ( simp[Abbr`lenvs`,Abbr`envs`]) >>
  qunabbrev_tac`lrecs` >> fs[] >>
  qmatch_assum_abbrev_tac`n < LENGTH vs + 1 + lrecs + LENGTH envs` >>
  `lrecs = LENGTH recs` by simp[Abbr`lrecs`] >> fs[] >>
  simp[EL_APPEND2,EL_GENLIST,EL_MAP,el_check_def] >>
  rator_x_assum`benv_bvs`mp_tac >>
  simp[Once Cv_bv_cases] >> strip_tac >>
  qpat_assum`∀i. i < LENGTH envs ⇒ X`(qspec_then`n - (LENGTH recs + (LENGTH vs + 1))` mp_tac) >>
  simp[] >> strip_tac >> simp[] )

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

val Cenv_bs_with_irr = store_thm("Cenv_bs_with_irr",
  ``∀rd s env cenv sz bs bs'.
    Cenv_bs rd s env cenv sz bs ∧
    (bs'.stack = bs.stack) ∧ (bs'.refs = bs.refs) ∧
    (bs'.code = bs.code) ∧ (bs'.inst_length = bs.inst_length)
    ⇒
    Cenv_bs rd s env cenv sz bs'``,
  rw[Cenv_bs_def,s_refs_def,good_rd_def])

val s_refs_with_irr = store_thm("s_refs_with_irr",
  ``∀rd s bs bs'.
    s_refs rd s bs ∧ (bs'.refs = bs.refs) ∧ (bs'.inst_length = bs.inst_length) ∧ (bs'.code = bs.code)
    ⇒
    s_refs rd s bs'``,
  rw[s_refs_def,good_rd_def])

val code_for_return_append_code = store_thm("code_for_return_append_code",
  ``∀rd bs bce st hdl sp v s s' bs' bc1.
    code_for_return rd bs bce st hdl sp v s s' ∧
    (bs' = bs with code := bs.code ++ bc1)
    ⇒
    code_for_return rd bs' bce st hdl sp v s s'``,
  simp[code_for_return_def] >>
  rpt gen_tac >> strip_tac >>
  map_every qexists_tac[`bv`,`rf`,`rd'`] >> fs[] >>
  match_mp_tac RTC_bc_next_append_code >>
  qexists_tac`bs` >>
  HINT_EXISTS_TAC >>
  simp[bc_state_component_equality])

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
  ``∀a b c d x. a ++ [x] ++ b = c ++ [x] ++ d ∧ x ∉ set b ∧ x ∉ set a ⇒ a = c ∧ b = d``,
  rw[APPEND_EQ_APPEND_MID] >> fs[] >>
  fs[APPEND_EQ_SING])

val compile_val = store_thm("compile_val",
  ``(∀s env exp res. Cevaluate s env exp res ⇒
      ∀rd s' beh cs cenv sz bs bce bcr bc0 code bc1.
        BIGUNION (IMAGE all_Clocs (set env)) ⊆ count (LENGTH s) ∧
        BIGUNION (IMAGE all_Clocs (set s)) ⊆ count (LENGTH s) ∧
        (res = (s', beh)) ∧
        (bce ++ bcr = bc0 ++ code ++ bc1) ∧
        ALL_DISTINCT (FILTER is_Label bce) ∧
        all_vlabs_list s ∧ all_vlabs_list env ∧ all_labs exp ∧
        EVERY (code_env_cd bce) (free_labs (LENGTH env) exp) ∧
        (∀cd. cd ∈ vlabs_list s ⇒ code_env_cd bce cd) ∧
        (∀cd. cd ∈ vlabs_list env ⇒ code_env_cd bce cd) ∧
        (bs.pc = next_addr bs.inst_length bc0) ∧
        set (free_vars exp) ⊆ count (LENGTH cenv) ∧
        Cenv_bs rd s env cenv sz (bs with code := bce) ∧
        ALL_DISTINCT (FILTER is_Label bc0) ∧
        EVERY (combin$C $< cs.next_label o dest_Label) (FILTER is_Label bc0)
        ⇒
      (∀v.
         (beh = Cval v) ∧
         ((compile cenv TCNonTail sz cs exp).out = REVERSE code ++ cs.out)
           ⇒
         code_for_push rd (bs with code := bc0 ++ code) bce bc0 code s s' env [v] cenv sz) ∧
      (∀v az lz env0 defs vs klvs blvs benv ret args cl st.
         (beh = Cval v) ∧
         ((compile cenv (TCTail az lz) sz cs exp).out = REVERSE code ++ cs.out) ∧
         (az = LENGTH args) ∧ (lz = LENGTH klvs) ∧
         (env = klvs ++ REVERSE vs ++ env0) ∧
         EVERY2 (Cv_bv (mk_pp rd (bs with code := bce))) vs args ∧
         EVERY2 (Cv_bv (mk_pp rd (bs with code := bce))) klvs blvs ∧
         (bs.stack = blvs++benv::CodePtr ret::(REVERSE args)++cl::st)
           ⇒
         code_for_return rd (bs with code := bc0 ++ code) bce st ret bs.handler v s s') ∧
      (∀t v ig sp hdl st.
         (beh = Cexc (Craise v)) ∧
         ((compile cenv t sz cs exp).out = REVERSE code ++ cs.out) ∧
         (bs.stack = ig++(StackPtr sp)::CodePtr hdl::st) ∧
         (bs.handler = LENGTH st + 1)
           ⇒
         code_for_return rd (bs with code := bc0 ++ code) bce st hdl sp v s s')) ∧
    (∀s env exps ress. Cevaluate_list s env exps ress ⇒
      ∀rd s' beh cs cenv sz bs bce bcr bc0 code bc1.
        BIGUNION (IMAGE all_Clocs (set env)) ⊆ count (LENGTH s) ∧
        BIGUNION (IMAGE all_Clocs (set s)) ⊆ count (LENGTH s) ∧
        (ress = (s', beh)) ∧
        (bce ++ bcr = bc0 ++ code ++ bc1) ∧
        ALL_DISTINCT (FILTER is_Label bce) ∧
        all_vlabs_list s ∧ all_vlabs_list env ∧ all_labs_list exps ∧
        EVERY (code_env_cd bce) (free_labs_list (LENGTH env) exps) ∧
        (∀cd. cd ∈ vlabs_list s ⇒ code_env_cd bce cd) ∧
        (∀cd. cd ∈ vlabs_list env ⇒ code_env_cd bce cd) ∧
        (bs.pc = next_addr bs.inst_length bc0) ∧
        set (free_vars_list exps) ⊆ count (LENGTH cenv) ∧
        Cenv_bs rd s env cenv sz (bs with code := bce) ∧
        ALL_DISTINCT (FILTER is_Label bc0) ∧
        EVERY (combin$C $< cs.next_label o dest_Label) (FILTER is_Label bc0) ∧
        ((compile_nts cenv sz cs exps).out = REVERSE code ++ cs.out)
        ⇒
      (∀vs. (beh = Cval vs) ⇒
         code_for_push rd (bs with code := bc0 ++ code) bce bc0 code s s' env vs cenv sz) ∧
      (∀v ig sp hdl st.
        (beh = Cexc (Craise v)) ∧
        (bs.stack = ig++(StackPtr sp)::CodePtr hdl::st) ∧
        (bs.handler = LENGTH st + 1)
          ⇒
        code_for_return rd (bs with code := bc0 ++ code) bce st hdl sp v s s'))``,
  ho_match_mp_tac Cevaluate_strongind >>
  strip_tac >- (
    simp[compile_def] >>
    rpt gen_tac >> strip_tac >>
    rpt gen_tac >>
    qspecl_then[`cenv`,`TCNonTail`,`sz`,`cs`,`exp`]mp_tac(CONJUNCT1 compile_append_out)>>
    disch_then(Q.X_CHOOSE_THEN`cc`strip_assume_tac) >>
    simp[Once SWAP_REVERSE] >> strip_tac >>
    map_every qx_gen_tac[`ig`,`sp`,`hdl`,`st`] >> strip_tac >>
    first_x_assum(qspecl_then[`rd`,`cs`,`cenv`,`sz`,`bs`,`bce`,`bcr`,`bc0`,`REVERSE cc`,`[PopExc;Return]++bc1`]mp_tac) >>
    simp[] >>
    disch_then (mp_tac o CONJUNCT1) >>
    simp[code_for_push_def,code_for_return_def] >>
    simp_tac(srw_ss()++DNF_ss)[] >>
    map_every qx_gen_tac[`rf`,`rd'`,`ev`] >> strip_tac >>
    map_every qexists_tac[`ev`,`rf`,`rd'`] >>
    conj_tac >- (
      qmatch_assum_abbrev_tac`bc_next^* bs1 bs2` >>
      `bc_next^* (bs1 with code := bc0 ++ code) (bs2 with code := bc0 ++ code)` by (
        match_mp_tac RTC_bc_next_append_code >>
        map_every qexists_tac[`bs1`,`bs2`] >>
        simp[Abbr`bs1`,Abbr`bs2`,bc_state_component_equality]) >>
      match_mp_tac(SIMP_RULE std_ss [transitive_def] RTC_TRANSITIVE) >>
      rfs[Abbr`bs1`,Abbr`bs2`] >>
      HINT_EXISTS_TAC >> simp[] >>
      simp[RTC_eq_NRC] >>
      qexists_tac`SUC(SUC 0)` >>
      simp[NRC] >>
      qmatch_abbrev_tac`∃bs2. bc_next bs1 bs2 ∧ bc_next bs2 bs3` >>
      `bc_fetch bs1 = SOME PopExc` by (
        match_mp_tac bc_fetch_next_addr >>
        simp[Abbr`bs1`] >>
        qexists_tac`bc0++REVERSE cc`>>simp[] ) >>
      simp[bc_eval1_thm] >>
      simp[Once bc_eval1_def,Abbr`bs1`,EL_REVERSE,PRE_SUB1,EL_APPEND1,EL_APPEND2,bump_pc_def] >>
      simp[REVERSE_APPEND,TAKE_APPEND1,TAKE_APPEND2] >>
      qmatch_abbrev_tac`bc_eval1 bs2 = SOME bs3` >>
      `bc_fetch bs2 = SOME Return` by (
        match_mp_tac bc_fetch_next_addr >>
        simp[Abbr`bs2`] >>
        qexists_tac`bc0++REVERSE cc++[PopExc]`>>simp[SUM_APPEND,FILTER_APPEND] ) >>
      simp[bc_eval1_def,Abbr`bs2`] ) >>
    simp[] >>
    fs[Cenv_bs_def] >>
    fs[s_refs_def,good_rd_def] ) >>
  strip_tac >- (
    simp[compile_def] >>
    rpt gen_tac >> strip_tac >>
    rpt gen_tac >>
    qspecl_then[`cenv`,`TCNonTail`,`sz`,`cs`,`exp`]mp_tac(CONJUNCT1 compile_append_out)>>
    disch_then(Q.X_CHOOSE_THEN`cc`strip_assume_tac) >>
    simp[Once SWAP_REVERSE] >> strip_tac >>
    rw[] >>
    first_x_assum(qspecl_then[`rd`,`cs`,`cenv`,`sz`,`bs`,`bce`,`bcr`,`bc0`,`REVERSE cc`,`PopExc::Return::bc1`]mp_tac) >>
    simp[] >>
    disch_then(qspecl_then[`TCNonTail`,`ig`]mp_tac) >>
    rw[] >>
    match_mp_tac code_for_return_append_code >>
    qexists_tac`bs with code := bc0 ++ REVERSE cc` >>
    rw[bc_state_component_equality]) >>
  strip_tac >- (
    simp[compile_def] >>
    rpt gen_tac >> strip_tac >>
    rpt gen_tac >>
    Q.PAT_ABBREV_TAC`cs0 = compiler_result_out_fupd (K (PushExc::Y::Z)) U` >>
    qspecl_then[`cenv`,`TCNonTail`,`sz + 2`,`cs0`,`exp`](Q.X_CHOOSE_THEN`cc`strip_assume_tac)(CONJUNCT1 compile_append_out) >>
    simp[pushret_def] >>
    REWRITE_TAC[ONE] >>
    simp[compile_def] >>
    strip_tac >>
    conj_tac >- (
      Q.PAT_ABBREV_TAC`cs1 = compiler_result_out_fupd (K (Label X::Y::Z)) U` >>
      qspecl_then[`CTLet(sz+1)::cenv`,`TCNonTail`,`sz+1`,`cs1`,`e2`](Q.X_CHOOSE_THEN`cb`strip_assume_tac)(CONJUNCT1 compile_append_out) >>
      simp[Abbr`cs1`,Abbr`cs0`,Once SWAP_REVERSE] >>
      rpt gen_tac >> strip_tac >>
      Q.PAT_ABBREV_TAC`bss = bs with code := X` >>
      `bc_fetch bss = SOME (PushPtr (Lab cs.next_label))` by (
        match_mp_tac bc_fetch_next_addr >>
        qexists_tac`bc0`>>simp[Abbr`bss`] ) >>
      `bc_next bss (bump_pc bss with stack := CodePtr (next_addr bss.inst_length (TAKE (LENGTH bc0 + 2 + LENGTH cc + 4) bss.code))::bss.stack)` by (
        simp[bc_eval1_thm,bc_eval1_def,bump_pc_def] >>
        simp[bc_state_component_equality,bc_find_loc_def,Abbr`bss`] >>
        match_mp_tac bc_find_loc_aux_ALL_DISTINCT >>
        qexists_tac`LENGTH bc0 + LENGTH cc + 5` >>
        simp[TAKE_APPEND1,TAKE_APPEND2,EL_APPEND1,EL_APPEND2,EL_CONS,PRE_SUB1,FILTER_APPEND,SUM_APPEND] >>
        fs[FILTER_REVERSE,ALL_DISTINCT_APPEND,ALL_DISTINCT_REVERSE,GSYM FILTER_EQ_NIL,combinTheory.o_DEF] >>
        fsrw_tac[DNF_ss][EVERY_MEM,between_def,MEM_FILTER,MEM_MAP] >>
        fsrw_tac[DNF_ss][is_Label_rwt] >>
        rpt(first_x_assum(qspec_then`rd`kall_tac)) >>
        rpt(qpat_assum`X.out = Y`kall_tac) >>
        rw[] >> spose_not_then strip_assume_tac >> res_tac >> fsrw_tac[ARITH_ss][]) >>
      qmatch_assum_abbrev_tac`bc_next bss bs1` >>
      `bc_fetch bs1 = SOME PushExc` by (
        match_mp_tac bc_fetch_next_addr >>
        simp[Abbr`bs1`,bump_pc_def] >>
        qexists_tac`bc0 ++ [PushPtr (Lab cs.next_label)]` >>
        simp[FILTER_APPEND,SUM_APPEND,Abbr`bss`] ) >>
      `bc_next bs1 (bump_pc bs1 with <| stack := StackPtr bs.handler::bs1.stack; handler := LENGTH bs1.stack |>)` by (
        simp[bc_eval1_thm,bc_eval1_def,bump_pc_def] >>
        simp[bc_state_component_equality] >>
        simp[Abbr`bs1`,bump_pc_def,Abbr`bss`]) >>
      qmatch_assum_abbrev_tac`bc_next bs1 bs2` >>
      `bc_next^* bss bs2` by metis_tac[RTC_TRANSITIVE,transitive_def,RTC_SUBSET] >>
      pop_assum mp_tac >>
      simp[Abbr`bs2`,bump_pc_def,Abbr`bs1`,ADD1] >>
      rpt(qpat_assum`bc_next X Y`kall_tac) >>
      rpt(qpat_assum`bc_fetch X = Y`kall_tac) >>
      strip_tac >>
      qmatch_assum_abbrev_tac`bc_next^* bss bss0` >>
      qmatch_assum_abbrev_tac`(compile cenv TCNonTail (sz + 2) cs0 exp).out = cc ++ cs0.out` >>
      first_x_assum(qspecl_then[`rd`,`cs0`,`cenv`,`sz+2`,`bss0`,`bce`,`bcr`,`TAKE (LENGTH bc0+2) bss.code`,`REVERSE cc`
                               ,`DROP (LENGTH bc0+2+LENGTH cc) bss.code++bc1`]mp_tac) >>
      discharge_hyps >- (
        simp[Abbr`bss0`,Abbr`bss`] >>
        simp[SUM_APPEND,FILTER_APPEND,Abbr`cs0`,TAKE_APPEND1,TAKE_APPEND2,DROP_APPEND1,DROP_APPEND2,DROP_LENGTH_NIL_rwt] >>
        conj_tac >- (
          SUBST1_TAC(DECIDE``sz + 2 = (sz + 1) + 1``) >>
          qmatch_abbrev_tac`Cenv_bs rd s env cenv (sz + 1 + 1) bs0` >>
          match_mp_tac Cenv_bs_imp_incsz >>
          qexists_tac`bs0 with stack := TL bs0.stack` >>
          simp[Abbr`bs0`,bc_state_component_equality] >>
          qmatch_abbrev_tac`Cenv_bs rd s env cenv (sz + 1) bs0` >>
          match_mp_tac Cenv_bs_imp_incsz >>
          qexists_tac`bs0 with stack := TL bs0.stack` >>
          simp[Abbr`bs0`,bc_state_component_equality] >>
          match_mp_tac Cenv_bs_with_irr >>
          HINT_EXISTS_TAC >> simp[] ) >>
        fsrw_tac[DNF_ss,ARITH_ss][EVERY_MEM,MEM_FILTER,is_Label_rwt] >>
        rw[] >> res_tac >> simp[] ) >>
      disch_then(mp_tac o CONJUNCT1) >>
      simp[Abbr`bss0`,Abbr`bss`,TAKE_APPEND1,TAKE_APPEND2] >>
      simp[code_for_push_def] >>
      simp_tac(srw_ss()++DNF_ss)[] >>
      map_every qx_gen_tac[`rf`,`rd'`,`bv`] >>
      strip_tac >>
      map_every qexists_tac[`rf`,`rd'`,`bv`] >>
      conj_tac >- (
        qmatch_assum_abbrev_tac`bc_next^* bs2 bs3` >>
        qmatch_abbrev_tac`bc_next^* bss bs5` >>
        qmatch_assum_abbrev_tac`bc_next^* bss bss0` >>
        `(bs2 with code := bss0.code) = bss0` by (
          simp[bc_state_component_equality,Abbr`bs2`,Abbr`bss0`,Abbr`bss`,TAKE_APPEND1,TAKE_APPEND2] ) >>
        `bc_next^* bss0 (bs3 with code := bss0.code)` by (
          match_mp_tac RTC_bc_next_append_code >>
          map_every qexists_tac[`bs2`,`bs3`] >>
          rw[] >>
          simp[Abbr`bs2`,Abbr`bs3`,Abbr`bss0`,Abbr`bss`,bc_state_component_equality,TAKE_APPEND1,TAKE_APPEND2] ) >>
        match_mp_tac(SIMP_RULE std_ss [transitive_def] RTC_TRANSITIVE) >>
        qexists_tac`bss0` >> simp[] >>
        match_mp_tac(SIMP_RULE std_ss [transitive_def] RTC_TRANSITIVE) >>
        HINT_EXISTS_TAC >> simp[] >>
        simp[RTC_eq_NRC] >>
        qexists_tac`SUC(SUC(SUC 0))` >>
        simp[NRC] >>
        qho_match_abbrev_tac`∃bs1. bc_next bs0 bs1 ∧ P bs1` >>
        `bc_fetch bs0 = SOME PopExc` by (
          match_mp_tac bc_fetch_next_addr >>
          simp[Abbr`bs0`,Abbr`bs3`,Abbr`bss0`,Abbr`bss`] >>
          qexists_tac`bc0++[PushPtr(Lab cs.next_label);PushExc]++REVERSE cc` >>
          simp[] ) >>
        simp[bc_eval1_thm,bc_eval1_def,Abbr`bs0`,Abbr`bs3`,Abbr`bss0`,EL_APPEND1,EL_APPEND2,bump_pc_def] >>
        simp[Abbr`P`,Abbr`bss`] >>
        qho_match_abbrev_tac`∃bs1. bc_next bs0 bs1 ∧ P bs1` >>
        `bc_fetch bs0 = SOME (Stack (Pops 1))` by (
          match_mp_tac bc_fetch_next_addr >>
          simp[Abbr`bs0`] >>
          Q.PAT_ABBREV_TAC`ls:bc_inst list = X` >>
          qexists_tac`TAKE (LENGTH bc0 + 2 + LENGTH cc + 1) ls` >>
          simp[Abbr`ls`,SUM_APPEND,FILTER_APPEND,TAKE_APPEND2,TAKE_APPEND1] ) >>
        simp[bc_eval1_def,bc_eval1_thm,Abbr`bs0`,bc_eval_stack_def,bump_pc_def] >>
        simp[TAKE_APPEND1,TAKE_APPEND2,REVERSE_APPEND,Abbr`P`] >>
        qmatch_abbrev_tac`bc_next bs0 bs1` >>
        `bc_fetch bs0 = SOME (Jump (Lab (cs.next_label + 1)))` by (
          match_mp_tac bc_fetch_next_addr >>
          simp[Abbr`bs0`] >>
          Q.PAT_ABBREV_TAC`ls:bc_inst list = X` >>
          qexists_tac`TAKE (LENGTH bc0 + 2 + LENGTH cc + 2) ls` >>
          simp[Abbr`ls`,SUM_APPEND,FILTER_APPEND,TAKE_APPEND1,TAKE_APPEND2] ) >>
        simp[bc_eval1_thm,bc_eval1_def,bc_find_loc_def,Abbr`bs0`,Abbr`bs1`,Abbr`bs5`,bc_state_component_equality] >>
        match_mp_tac bc_find_loc_aux_ALL_DISTINCT >>
        Q.PAT_ABBREV_TAC`ls:bc_inst list = bc0++X` >>
        qexists_tac`LENGTH ls - 1` >>
        simp[Abbr`ls`,EL_APPEND1,EL_APPEND2,EL_CONS,PRE_SUB1,ADD1,TAKE_APPEND1,TAKE_APPEND2,TAKE_LENGTH_ID_rwt] >>
        simp[SUM_APPEND,FILTER_APPEND] >>
        rpt(qpat_assum`bc_fetch A = X`kall_tac) >>
        rpt(qpat_assum`bc_next^* A X`kall_tac) >>
        rpt(qpat_assum`Cenv_bs a b c d e f`kall_tac) >>
        rpt(qpat_assum`Cv_bv a b f`kall_tac) >>
        unabbrev_all_tac >>
        simp[ALL_DISTINCT_APPEND,FILTER_REVERSE,ALL_DISTINCT_REVERSE] >>
        fsrw_tac[DNF_ss][EVERY_MEM,MEM_FILTER,MEM_MAP,between_def] >>
        fsrw_tac[DNF_ss,ARITH_ss][is_Label_rwt] >>
        rw[] >> spose_not_then strip_assume_tac >> res_tac >> DECIDE_TAC ) >>
      qmatch_assum_abbrev_tac`Cenv_bs rd' s2 env cenv (sz + 3) bs0` >>
      `Cenv_bs rd' s2 env cenv sz (bs0 with stack := DROP 3 bs0.stack)` by (
        match_mp_tac Cenv_bs_pops >>
        qexists_tac`TAKE 3 bs0.stack` >>
        simp[Abbr`bs0`] >>
        HINT_EXISTS_TAC >>
        simp[bc_state_component_equality] >>
        metis_tac[Cenv_bs_CTLet_bound] ) >>
      fs[] >>
      match_mp_tac Cenv_bs_imp_incsz >>
      HINT_EXISTS_TAC >>
      simp[bc_state_component_equality,Abbr`bs0`] ) >>
    rpt gen_tac >>
    Q.PAT_ABBREV_TAC`cs1 = compiler_result_out_fupd (K (Label X::Y::Z)) U` >>
    Q.PAT_ABBREV_TAC`tt = TCTail X Y` >>
    qspecl_then[`CTLet(sz+1)::cenv`,`tt`,`sz+1`,`cs1`,`e2`](Q.X_CHOOSE_THEN`cb`strip_assume_tac)(CONJUNCT1 compile_append_out) >>
    simp[Abbr`cs1`,Abbr`cs0`,Once SWAP_REVERSE] >>
    strip_tac >>
    Q.PAT_ABBREV_TAC`bss = bs with code := X` >>
    `bc_fetch bss = SOME (PushPtr (Lab cs.next_label))` by (
      match_mp_tac bc_fetch_next_addr >>
      qexists_tac`bc0`>>simp[Abbr`bss`] ) >>
    `bc_next bss (bump_pc bss with stack := CodePtr (next_addr bss.inst_length (TAKE (LENGTH bc0 + 2 + LENGTH cc + 8) bss.code))::bss.stack)` by (
      simp[bc_eval1_thm,bc_eval1_def,bump_pc_def] >>
      simp[bc_state_component_equality,bc_find_loc_def,Abbr`bss`] >>
      match_mp_tac bc_find_loc_aux_ALL_DISTINCT >>
      qexists_tac`LENGTH bc0 + LENGTH cc + 10` >>
      simp[TAKE_APPEND1,TAKE_APPEND2,EL_APPEND1,EL_APPEND2,EL_CONS,PRE_SUB1,FILTER_APPEND,SUM_APPEND] >>
      fs[FILTER_REVERSE,ALL_DISTINCT_APPEND,ALL_DISTINCT_REVERSE,GSYM FILTER_EQ_NIL,combinTheory.o_DEF] >>
      fsrw_tac[DNF_ss][EVERY_MEM,between_def,MEM_FILTER,MEM_MAP] >>
      fsrw_tac[DNF_ss][is_Label_rwt] >>
      rpt(first_x_assum(qspec_then`rd`kall_tac)) >>
      rpt(qpat_assum`X.out = Y`kall_tac) >>
      rw[] >> spose_not_then strip_assume_tac >> res_tac >> fsrw_tac[ARITH_ss][]) >>
    qmatch_assum_abbrev_tac`bc_next bss bs1` >>
    `bc_fetch bs1 = SOME PushExc` by (
      match_mp_tac bc_fetch_next_addr >>
      simp[Abbr`bs1`,bump_pc_def] >>
      qexists_tac`bc0 ++ [PushPtr (Lab cs.next_label)]` >>
      simp[FILTER_APPEND,SUM_APPEND,Abbr`bss`] ) >>
    `bc_next bs1 (bump_pc bs1 with <| stack := StackPtr bs.handler::bs1.stack; handler := LENGTH bs1.stack |>)` by (
      simp[bc_eval1_thm,bc_eval1_def,bump_pc_def] >>
      simp[bc_state_component_equality] >>
      simp[Abbr`bs1`,bump_pc_def,Abbr`bss`]) >>
    qmatch_assum_abbrev_tac`bc_next bs1 bs2` >>
    `bc_next^* bss bs2` by metis_tac[RTC_TRANSITIVE,transitive_def,RTC_SUBSET] >>
    pop_assum mp_tac >>
    simp[Abbr`bs2`,bump_pc_def,Abbr`bs1`,ADD1] >>
    rpt(qpat_assum`bc_next X Y`kall_tac) >>
    rpt(qpat_assum`bc_fetch X = Y`kall_tac) >>
    strip_tac >>
    qmatch_assum_abbrev_tac`bc_next^* bss bss0` >>
    qmatch_assum_abbrev_tac`(compile cenv TCNonTail (sz + 2) cs0 exp).out = cc ++ cs0.out` >>
    first_x_assum(qspecl_then[`rd`,`cs0`,`cenv`,`sz+2`,`bss0`,`bce`,`bcr`,`TAKE (LENGTH bc0+2) bss.code`,`REVERSE cc`
                             ,`DROP (LENGTH bc0+2+LENGTH cc) bss.code ++ bc1`]mp_tac) >>
    discharge_hyps >- (
      simp[Abbr`bss0`,Abbr`bss`] >>
      simp[SUM_APPEND,FILTER_APPEND,Abbr`cs0`,TAKE_APPEND1,TAKE_APPEND2,DROP_APPEND1,DROP_APPEND2,DROP_LENGTH_NIL_rwt] >>
      conj_tac >- (
        SUBST1_TAC(DECIDE``sz + 2 = (sz + 1) + 1``) >>
        qmatch_abbrev_tac`Cenv_bs rd s eenv cenv (sz + 1 + 1) bs0` >>
        match_mp_tac Cenv_bs_imp_incsz >>
        qexists_tac`bs0 with stack := TL bs0.stack` >>
        simp[Abbr`bs0`,bc_state_component_equality] >>
        qmatch_abbrev_tac`Cenv_bs rd s eenv cenv (sz + 1) bs0` >>
        match_mp_tac Cenv_bs_imp_incsz >>
        qexists_tac`bs0 with stack := TL bs0.stack` >>
        simp[Abbr`bs0`,bc_state_component_equality] >>
        qpat_assum`bc_next^* X Y`kall_tac >>
        match_mp_tac Cenv_bs_with_irr >>
        qexists_tac`bs with code := bce` >>
        simp[] >> rw[]) >>
      fsrw_tac[DNF_ss,ARITH_ss][EVERY_MEM,MEM_FILTER,is_Label_rwt] >>
      rw[] >> res_tac >> simp[] ) >>
    disch_then(mp_tac o CONJUNCT1) >>
    simp[Abbr`bss0`,Abbr`bss`,TAKE_APPEND1,TAKE_APPEND2] >>
    simp[code_for_push_def,code_for_return_def] >>
    simp_tac(srw_ss()++DNF_ss)[] >>
    map_every qx_gen_tac[`rf`,`rd'`,`bv`] >>
    strip_tac >>
    map_every qexists_tac[`bv`,`rf`,`rd'`] >>
    conj_tac >- (
      qmatch_assum_abbrev_tac`bc_next^* bs2 bs3` >>
      qmatch_abbrev_tac`bc_next^* bss bs5` >>
      qmatch_assum_abbrev_tac`bc_next^* bss bss0` >>
      `(bs2 with code := bss0.code) = bss0` by (
        simp[bc_state_component_equality,Abbr`bs2`,Abbr`bss0`,Abbr`bss`,TAKE_APPEND1,TAKE_APPEND2] ) >>
      `bc_next^* bss0 (bs3 with code := bss0.code)` by (
        match_mp_tac RTC_bc_next_append_code >>
        map_every qexists_tac[`bs2`,`bs3`] >>
        rw[] >>
        simp[Abbr`bs2`,Abbr`bs3`,Abbr`bss0`,Abbr`bss`,bc_state_component_equality,TAKE_APPEND1,TAKE_APPEND2] ) >>
      match_mp_tac(SIMP_RULE std_ss [transitive_def] RTC_TRANSITIVE) >>
      qexists_tac`bss0` >> simp[] >>
      match_mp_tac(SIMP_RULE std_ss [transitive_def] RTC_TRANSITIVE) >>
      HINT_EXISTS_TAC >> simp[] >>
      match_mp_tac(SIMP_RULE std_ss [transitive_def] RTC_TRANSITIVE) >>
      qexists_tac`bs3 with <| pc := next_addr bs.inst_length (TAKE (LENGTH bc0 + LENGTH cc + 4) bss.code);
                              code := bss.code;
                              handler := bs.handler;
                              stack := bv::(DROP 3 bs3.stack)|>` >>
      reverse conj_tac >- (
        match_mp_tac retbc_thm >>
        simp[Abbr`bs3`,bc_state_component_equality,Abbr`bs5`,Abbr`bss`] >>
        simp[TAKE_APPEND1,TAKE_APPEND2] >>
        Q.PAT_ABBREV_TAC`bc00 = bc0 ++ X::Y::(Z++A)` >>
        qexists_tac`bc00` >>
        simp[Abbr`bc00`] >>
        qexists_tac`blvs` >>
        simp[] >> fs[EVERY2_EVERY] ) >>
      simp[RTC_eq_NRC] >>
      qexists_tac`SUC(SUC 0)` >>
      simp[NRC] >>
      qho_match_abbrev_tac`∃bs1. bc_next bs0 bs1 ∧ P bs1` >>
      `bc_fetch bs0 = SOME PopExc` by (
        match_mp_tac bc_fetch_next_addr >>
        simp[Abbr`bs0`,Abbr`bs3`,Abbr`bss0`,Abbr`bss`] >>
        qexists_tac`bc0++[PushPtr(Lab cs.next_label);PushExc]++REVERSE cc` >>
        simp[] ) >>
      simp[bc_eval1_thm,bc_eval1_def,Abbr`bs0`,Abbr`bs3`,Abbr`bss0`,EL_APPEND1,EL_APPEND2,bump_pc_def] >>
      simp[Abbr`P`,Abbr`bss`] >>
      qho_match_abbrev_tac`bc_next bs0 bs1` >>
      `bc_fetch bs0 = SOME (Stack (Pops 1))` by (
        match_mp_tac bc_fetch_next_addr >>
        simp[Abbr`bs0`] >>
        Q.PAT_ABBREV_TAC`ls:bc_inst list = X` >>
        qexists_tac`TAKE (LENGTH bc0 + 2 + LENGTH cc + 1) ls` >>
        simp[Abbr`ls`,SUM_APPEND,FILTER_APPEND,TAKE_APPEND2,TAKE_APPEND1] ) >>
      simp[bc_eval1_def,bc_eval1_thm,Abbr`bs0`,bc_eval_stack_def,bump_pc_def] >>
      simp[bc_state_component_equality,Abbr`bs1`,TAKE_APPEND1,TAKE_APPEND2] >>
      simp[SUM_APPEND,FILTER_APPEND] ) >>
    fs[] >>
    match_mp_tac s_refs_with_irr >>
    fs[Cenv_bs_def] >>
    HINT_EXISTS_TAC >>
    simp[] ) >>
  strip_tac >- (
    simp[compile_def] >>
    rpt gen_tac >> strip_tac >>
    rpt gen_tac >>
    Q.PAT_ABBREV_TAC`cs0 = compiler_result_out_fupd (K (PushExc::Y::Z)) U` >>
    qspecl_then[`cenv`,`TCNonTail`,`sz + 2`,`cs0`,`exp`](Q.X_CHOOSE_THEN`cc`strip_assume_tac)(CONJUNCT1 compile_append_out) >>
    simp[pushret_def] >>
    strip_tac >>
    reverse(Cases_on`ALL_DISTINCT (FILTER is_Label (bc0 ++ code)) ∧
                     ∃cc1 cc2. code = [PushPtr(Lab cs.next_label);PushExc]++REVERSE cc++PopExc::Stack(Pops 1)::cc1++Label cs.next_label::cc2`) >- (
      conj_tac >- (
        Q.PAT_ABBREV_TAC`cs1 = compiler_result_out_fupd (K (Label X::Y::Z)) U` >>
        qspecl_then[`cenv`,`TCNonTail`,`sz`,`exp'`,`0`,`cs1`,`1`](Q.X_CHOOSE_THEN`cb`strip_assume_tac)(CONJUNCT1 (CONJUNCT2 compile_append_out)) >>
        simp[Abbr`cs1`,Abbr`cs0`,Once SWAP_REVERSE] >>
        rw[] >> fs[] >> fs[MEM_SING_APPEND] >>
        qsuff_tac`F`>-rw[] >>
        qpat_assum`¬ALL_DISTINCT X`mp_tac >>
        simp[FILTER_APPEND,ALL_DISTINCT_APPEND,FILTER_REVERSE,ALL_DISTINCT_REVERSE] >>
        fsrw_tac[DNF_ss][EVERY_MEM,MEM_FILTER,MEM_MAP,between_def,is_Label_rwt] >>
        rpt (first_x_assum(qspec_then`rd`kall_tac)) >>
        rw[] >> spose_not_then strip_assume_tac >> res_tac >> DECIDE_TAC) >>
      conj_tac >- (
        rpt gen_tac >>
        Q.PAT_ABBREV_TAC`cs1 = compiler_result_out_fupd (K (Label X::Y::Z)) U` >>
        Q.PAT_ABBREV_TAC`tt:call_context = X` >>
        qspecl_then[`cenv`,`tt`,`sz`,`exp'`,`0`,`cs1`,`1`](Q.X_CHOOSE_THEN`cb`strip_assume_tac)(CONJUNCT1 (CONJUNCT2 compile_append_out)) >>
        simp[Abbr`cs1`,Abbr`cs0`,Once SWAP_REVERSE] >>
        rw[] >> fs[] >> fs[MEM_SING_APPEND] >>
        qsuff_tac`F`>-rw[] >>
        qpat_assum`¬ALL_DISTINCT X`mp_tac >>
        simp[FILTER_APPEND,ALL_DISTINCT_APPEND,FILTER_REVERSE,ALL_DISTINCT_REVERSE] >>
        fsrw_tac[DNF_ss][EVERY_MEM,MEM_FILTER,MEM_MAP,between_def,is_Label_rwt] >>
        rpt (first_x_assum(qspec_then`rd`kall_tac)) >>
        rw[] >> spose_not_then strip_assume_tac >> res_tac >> DECIDE_TAC) >>
      rpt gen_tac >>
      Q.PAT_ABBREV_TAC`cs1 = compiler_result_out_fupd (K (Label X::Y::Z)) U` >>
      qspecl_then[`cenv`,`t`,`sz`,`exp'`,`0`,`cs1`,`1`](Q.X_CHOOSE_THEN`cb`strip_assume_tac)(CONJUNCT1 (CONJUNCT2 compile_append_out)) >>
      simp[Abbr`cs1`,Abbr`cs0`] >>
      Q.PAT_ABBREV_TAC`cs1 = compiler_result_out_fupd (K X) U` >>
      qspecl_then[`t`,`cs1`](Q.X_CHOOSE_THEN`cp`strip_assume_tac)pushret_append_out >> pop_assum kall_tac >>
      simp[Abbr`cs1`,Once SWAP_REVERSE] >>
      rw[] >> fs[] >> fs[MEM_SING_APPEND] >>
      qsuff_tac`F`>-rw[] >>
      qpat_assum`¬ALL_DISTINCT X`mp_tac >>
      simp[FILTER_APPEND,ALL_DISTINCT_APPEND,FILTER_REVERSE,ALL_DISTINCT_REVERSE] >>
      fs[GSYM FILTER_EQ_NIL,combinTheory.o_DEF] >>
      fsrw_tac[DNF_ss][EVERY_MEM,MEM_FILTER,MEM_MAP,between_def,is_Label_rwt] >>
      rpt (first_x_assum(qspec_then`rd`kall_tac)) >>
      rw[] >> spose_not_then strip_assume_tac >> res_tac >> DECIDE_TAC) >>
    pop_assum strip_assume_tac >>
    qabbrev_tac`bss = bs with code := bc0 ++ code` >>
    `bc_fetch bss = SOME (PushPtr (Lab cs.next_label))` by (
      match_mp_tac bc_fetch_next_addr >>
      qexists_tac`bc0`>>simp[Abbr`bss`] ) >>
    `bc_next bss (bump_pc bss with stack := CodePtr (next_addr bss.inst_length (TAKE (LENGTH bc0 + 2 + LENGTH cc + 2 + LENGTH cc1) bss.code))::bss.stack)` by (
      simp[bc_eval1_thm,bc_eval1_def,bump_pc_def] >>
      simp[bc_state_component_equality,bc_find_loc_def,Abbr`bss`] >>
      match_mp_tac bc_find_loc_aux_ALL_DISTINCT >>
      qexists_tac`LENGTH bc0 + LENGTH cc + LENGTH cc1 + 4` >>
      simp[EL_APPEND1,EL_APPEND2,EL_CONS,PRE_SUB1,ADD1] >>
      qmatch_abbrev_tac`ALL_DISTINCT (FILTER is_Label xxx)` >>
      qsuff_tac`xxx = bc0 ++ code`>-PROVE_TAC[] >>
      simp[Abbr`xxx`]) >>
    qmatch_assum_abbrev_tac`bc_next bss bs1` >>
    `bc_fetch bs1 = SOME PushExc` by (
      match_mp_tac bc_fetch_next_addr >>
      simp[Abbr`bs1`,bump_pc_def] >>
      qexists_tac`bc0 ++ [PushPtr (Lab cs.next_label)]` >>
      simp[FILTER_APPEND,SUM_APPEND,Abbr`bss`] ) >>
    `bc_next bs1 (bump_pc bs1 with <| stack := StackPtr bs.handler::bs1.stack; handler := LENGTH bs1.stack |>)` by (
      simp[bc_eval1_thm,bc_eval1_def,bump_pc_def] >>
      simp[bc_state_component_equality] >>
      simp[Abbr`bs1`,bump_pc_def,Abbr`bss`]) >>
    qmatch_assum_abbrev_tac`bc_next bs1 bs2` >>
    `bc_next^* bss bs2` by metis_tac[RTC_TRANSITIVE,transitive_def,RTC_SUBSET] >>
    pop_assum mp_tac >>
    simp[Abbr`bs2`,bump_pc_def,Abbr`bs1`,ADD1] >>
    rpt(qpat_assum`bc_next X Y`kall_tac) >>
    rpt(qpat_assum`bc_fetch X = Y`kall_tac) >>
    Q.PAT_ABBREV_TAC`aa = next_addr bss.inst_length X` >>
    strip_tac >>
    qmatch_assum_abbrev_tac`bc_next^* bss bss0` >>
    last_x_assum(qspecl_then[`rd`,`cs0`,`cenv`,`sz+2`,`bss0`,`bce`,`bcr`,`bc0++(TAKE 2 code)`,`REVERSE cc`,`(DROP (2 + LENGTH cc) code) ++ bc1`]mp_tac) >>
    discharge_hyps >- (
      simp[Abbr`bss0`,Abbr`bss`,DROP_APPEND1,DROP_LENGTH_NIL_rwt] >>
      simp[SUM_APPEND,FILTER_APPEND,Abbr`cs0`] >>
      conj_tac >- (
        SUBST1_TAC(DECIDE``sz + 2 = (sz + 1) + 1``) >>
        qmatch_abbrev_tac`Cenv_bs rd s env cenv (sz + 1 + 1) bs0` >>
        match_mp_tac Cenv_bs_imp_incsz >>
        qexists_tac`bs0 with stack := TL bs0.stack` >>
        simp[Abbr`bs0`,bc_state_component_equality] >>
        qmatch_abbrev_tac`Cenv_bs rd s env cenv (sz + 1) bs0` >>
        match_mp_tac Cenv_bs_imp_incsz >>
        qexists_tac`bs0 with stack := TL bs0.stack` >>
        simp[Abbr`bs0`,bc_state_component_equality] >>
        match_mp_tac Cenv_bs_with_irr >>
        HINT_EXISTS_TAC >> simp[] ) >>
      fsrw_tac[DNF_ss,ARITH_ss][EVERY_MEM,MEM_FILTER,is_Label_rwt] >>
      rpt(qpat_assum`∀rd cs. P`kall_tac) >>
      rw[] >> res_tac >> simp[] ) >>
    disch_then(qspec_then`TCNonTail`mp_tac) >> simp[] >>
    disch_then(qspecl_then[`[]`,`bs.handler`,`aa`,`bs.stack`]mp_tac) >>
    discharge_hyps >- (
      simp[Abbr`bss0`,Abbr`bss`,TAKE_APPEND1,TAKE_APPEND2] ) >>
    disch_then(mp_tac o SIMP_RULE(srw_ss())[LET_THM,code_for_return_def]) >>
    disch_then(qx_choosel_then[`bv`,`rf`,`rd'`]strip_assume_tac) >>
    qmatch_assum_abbrev_tac`bc_next^* bs1 bs2` >>
    `bc_next^* (bs1 with code := bss.code) (bs2 with code := bss.code)` by (
      match_mp_tac RTC_bc_next_append_code >>
      map_every qexists_tac[`bs1`,`bs2`] >>
      simp[Abbr`bs1`,Abbr`bs2`,Abbr`bss0`,bc_state_component_equality,Abbr`bss`] ) >>
    `bs1 with code := bss.code = bss0` by (
      simp[Abbr`bs1`,Abbr`bss0`,Abbr`bss`,bc_state_component_equality] ) >>
    fs[] >>
    qpat_assum`bc_next^* bs1 bs2`kall_tac >>
    qunabbrev_tac`bs1` >> qunabbrev_tac`bs2` >>
    qmatch_assum_abbrev_tac`bc_next^* bss0 bs2` >>
    `bc_next^* bss bs2` by metis_tac[RTC_TRANSITIVE,transitive_def] >>
    qpat_assum`bc_next^* bss bss0`kall_tac >>
    qpat_assum`bc_next^* bss0 bs2`kall_tac >>
    qpat_assum`A = bss0`kall_tac >>
    `all_Clocs v ⊆ count (LENGTH s') ∧
     BIGUNION (IMAGE all_Clocs (set env)) ⊆ count (LENGTH s') ∧
     BIGUNION (IMAGE all_Clocs (set s')) ⊆ count (LENGTH s') ∧
     EVERY all_vlabs s' ∧ all_vlabs v ∧
     EVERY (code_env_cd bce) (free_labs (SUC (LENGTH env)) exp') ∧
     (∀cd. cd ∈ vlabs_list s' ⇒ code_env_cd bce cd) ∧
     (∀cd. cd ∈ vlabs v ∨ cd ∈ vlabs_list env ⇒ code_env_cd bce cd) ∧
     set (free_vars exp') ⊆ count (LENGTH (CTLet(sz+1)::cenv)) ∧
     Cenv_bs rd' s' (v::env) (CTLet(sz+1)::cenv) (sz+1) (bs2 with code := bce)` by (
      qspecl_then[`s`,`env`,`exp`,`s',Cexc(Craise v)`]mp_tac(CONJUNCT1 Cevaluate_store_SUBSET) >>
      qspecl_then[`s`,`env`,`exp`,`s',Cexc(Craise v)`]mp_tac(CONJUNCT1 Cevaluate_Clocs) >>
      qspecl_then[`s`,`env`,`exp`,`s',Cexc(Craise v)`]mp_tac(CONJUNCT1 Cevaluate_all_vlabs) >>
      qspecl_then[`s`,`env`,`exp`,`s',Cexc(Craise v)`]mp_tac(CONJUNCT1 Cevaluate_vlabs) >>
      simp[] >> ntac 4 strip_tac >>
      first_x_assum(qspec_then`rd`kall_tac) >>
      conj_tac >- (
        fsrw_tac[DNF_ss][SUBSET_DEF] >>
        rw[] >> res_tac >> fsrw_tac[ARITH_ss][] ) >>
      simp[ADD1] >>
      conj_tac >- (
        fsrw_tac[DNF_ss][SUBSET_DEF] >>
        metis_tac[EVERY_MEM] ) >>
      conj_tac >- (
        fsrw_tac[DNF_ss][SUBSET_DEF] >>
        metis_tac[EVERY_MEM] ) >>
      conj_tac >- (
        fsrw_tac[DNF_ss][SUBSET_DEF] >>
        rw[] >> res_tac >> fsrw_tac[ARITH_ss][] ) >>
      match_mp_tac Cenv_bs_FUPDATE >>
      qexists_tac`bs2 with <| stack := bs.stack; code := bce|>` >>
      simp[bc_state_component_equality,Abbr`bs2`] >>
      match_mp_tac Cenv_bs_change_store >>
      map_every qexists_tac [`rd`,`s`,`bs with <| pc := aa; code := bce|>`,`rf`] >>
      simp[Abbr`bss0`,Abbr`bss`,bc_state_component_equality] >>
      fs[s_refs_def,good_rd_def] >>
      match_mp_tac Cenv_bs_with_irr >>
      qexists_tac`bs with code := bce`>>simp[] ) >>
    fs[] >>
    conj_tac >- (
      REWRITE_TAC[ONE] >>
      simp[compile_def] >>
      Q.PAT_ABBREV_TAC`cs1 = compiler_result_out_fupd A B` >>
      Q.PAT_ABBREV_TAC`tt:call_context = A` >>
      qspecl_then[`CTLet(sz+1)::cenv`,`tt`,`sz+1`,`cs1`,`exp'`](Q.X_CHOOSE_THEN`cd`strip_assume_tac)(CONJUNCT1 compile_append_out) >>
      gen_tac >> simp[Abbr`cs1`,Abbr`cs0`] >>
      SUBST1_TAC(Q.prove(`REVERSE cc2 ++ [Label cs.next_label] ++ REVERSE cc1 = REVERSE(cc1++Label cs.next_label::cc2)`,lrw[])) >>
      REWRITE_TAC[Once SWAP_REVERSE] >>
      simp[] >> strip_tac >>
      qpat_assum`(A.out = cd ++ B)`mp_tac >>
      Q.PAT_ABBREV_TAC`cs1 = compiler_result_out_fupd A B` >> strip_tac >>
      `cc1 = [Jump (Lab (cs.next_label + 1))] ∧
       cc2 = REVERSE cd ++ [Stack (Pops 1); Label (cs.next_label + 1)]` by (
         match_mp_tac MEM_APPEND_lemma >>
         qexists_tac`Label cs.next_label` >>
         simp[] >>
         fsrw_tac[DNF_ss][FILTER_APPEND,ALL_DISTINCT_APPEND,MEM_FILTER] ) >>
      first_x_assum(qspecl_then[`rd'`,`cs1`,`CTLet (sz+1)::cenv`,`sz+1`,`bs2`,`bce`,`bcr`
                               ,`TAKE(LENGTH bc0+2+LENGTH cc+2+LENGTH cc1+1)bss.code`
                               ,`REVERSE cd`,`[Stack (Pops 1); Label (cs.next_label+1)]++bc1`]mp_tac) >>
      discharge_hyps >- (
        simp[Abbr`bss`,TAKE_APPEND1,TAKE_APPEND2,Abbr`bs2`,Abbr`bss0`,Abbr`aa`] >>
        conj_tac >- PROVE_TAC[] >>
        fs[SUM_APPEND,FILTER_APPEND,ALL_DISTINCT_APPEND,FILTER_REVERSE,EVERY_REVERSE] >>
        fsrw_tac[DNF_ss][MEM_FILTER,EVERY_MEM,is_Label_rwt,ALL_DISTINCT_REVERSE,MEM_MAP,between_def] >>
        fsrw_tac[ARITH_ss][Abbr`cs1`] >>
        rw[] >> spose_not_then strip_assume_tac >> res_tac >> fsrw_tac[ARITH_ss][] ) >>
      simp[] >>
      disch_then(mp_tac o CONJUNCT1) >>
      simp[code_for_push_def] >>
      simp_tac(srw_ss()++DNF_ss)[] >>
      map_every qx_gen_tac[`rf'`,`rd''`,`br`] >>
      strip_tac >>
      map_every qexists_tac[`rf'`,`rd''`,`br`] >>
      conj_tac >- (
        match_mp_tac(SIMP_RULE std_ss [transitive_def] RTC_TRANSITIVE) >>
        qexists_tac`bs2` >> simp[] >>
        qmatch_assum_abbrev_tac`bc_next^* bs3 bs4` >>
        `bc_next^* (bs3 with code := bc0 ++ code) (bs4 with code := bc0 ++ code)` by (
          match_mp_tac RTC_bc_next_append_code >>
          map_every qexists_tac[`bs3`,`bs4`] >>
          simp[Abbr`bs3`,Abbr`bs4`,bc_state_component_equality] >>
          simp[Abbr`bss`,TAKE_APPEND1,TAKE_APPEND2] ) >>
        `bs3 with code := bc0 ++ code = bs2` by (
          simp[Abbr`bs3`,bc_state_component_equality,Abbr`bs2`,Abbr`bss`] ) >>
        fs[] >>
        match_mp_tac(SIMP_RULE std_ss [transitive_def] RTC_TRANSITIVE) >>
        HINT_EXISTS_TAC >> simp[] >> ntac 2 (pop_assum kall_tac) >>
        fs[Abbr`bs3`,Abbr`bs4`] >>
        simp[Abbr`bs2`,Abbr`bss0`,Abbr`bss`] >>
        ntac 6 (pop_assum kall_tac) >> rw[] >>
        ntac 9 (pop_assum kall_tac) >>
        match_mp_tac RTC_SUBSET >>
        qmatch_abbrev_tac`bc_next bs1 bs2` >>
        `bc_fetch bs1 = SOME (Stack (Pops 1))` by (
          match_mp_tac bc_fetch_next_addr >>
          simp[Abbr`bs1`] >>
          CONV_TAC SWAP_EXISTS_CONV >>
          qexists_tac`Label (cs.next_label + 1)::[]` >>
          simp[TAKE_APPEND1,TAKE_APPEND2,SUM_APPEND,FILTER_APPEND] ) >>
        simp[bc_eval1_thm,bc_eval1_def,Abbr`bs1`,bump_pc_def,bc_eval_stack_def] >>
        simp[Abbr`bs2`,bc_state_component_equality] >>
        simp[SUM_APPEND,FILTER_APPEND,TAKE_APPEND1,TAKE_APPEND2] ) >>
      fs[Abbr`bs2`,Abbr`bss0`,Abbr`bss`] >>
      reverse conj_tac >- metis_tac[IS_PREFIX_TRANS,SUBMAP_TRANS] >>
      match_mp_tac Cenv_bs_imp_incsz >>
      qexists_tac`bs with <| refs := rf'; code := bce|>` >>
      simp[bc_state_component_equality] >>
      match_mp_tac Cenv_bs_pops >>
      qexists_tac`[br;bv]` >> simp[] >>
      qmatch_assum_abbrev_tac`Cenv_bs rd'' s'' (v::env) (CTLet(sz+1)::cenv) (sz+2) bs0` >>
      qexists_tac`bs0` >>
      simp[Abbr`bs0`,bc_state_component_equality] >>
      reverse conj_tac >- metis_tac[Cenv_bs_CTLet_bound] >>
      `env = TL (v::env) ∧ cenv = TL (CTLet (sz+1)::cenv)` by simp[] >>
      ntac 2 (pop_assum SUBST1_TAC) >>
      match_mp_tac Cenv_bs_DOMSUB >> simp[] >>
      match_mp_tac Cenv_bs_with_irr >>
      HINT_EXISTS_TAC >> simp[]) >>
    conj_tac >- (
      REWRITE_TAC[ONE] >>
      simp[compile_def] >>
      rpt gen_tac >>
      Q.PAT_ABBREV_TAC`cs1 = compiler_result_out_fupd A B` >>
      Q.PAT_ABBREV_TAC`tt:call_context = A` >>
      qspecl_then[`CTLet(sz+1)::cenv`,`tt`,`sz+1`,`cs1`,`exp'`](Q.X_CHOOSE_THEN`cd`strip_assume_tac)(CONJUNCT1 compile_append_out) >>
      simp[Abbr`cs1`,Abbr`cs0`] >>
      SUBST1_TAC(Q.prove(`REVERSE cc2 ++ [Label cs.next_label] ++ REVERSE cc1 = REVERSE(cc1++Label cs.next_label::cc2)`,lrw[])) >>
      REWRITE_TAC[Once SWAP_REVERSE] >>
      simp[] >> strip_tac >>
      qpat_assum`(A.out = cd ++ B)`mp_tac >>
      Q.PAT_ABBREV_TAC`cs1 = compiler_result_out_fupd A B` >> strip_tac >>
      qmatch_assum_abbrev_tac`cc1 ++ [lab] ++ cc2 = co` >>
      `cc1 = TAKE 6 co ∧
       cc2 = DROP 7 co` by (
         match_mp_tac MEM_APPEND_lemma >>
         qexists_tac`lab` >>
         simp[Abbr`co`] >>
         fsrw_tac[DNF_ss][FILTER_APPEND,ALL_DISTINCT_APPEND,MEM_FILTER,Abbr`lab`] ) >>
      first_x_assum(qspecl_then[`rd'`,`cs1`,`CTLet (sz+1)::cenv`,`sz+1`,`bs2`,`bce`,`bcr`
                               ,`TAKE(LENGTH bc0+2+LENGTH cc+2+LENGTH cc1+1)bss.code`
                               ,`REVERSE cd`,`[Label (cs.next_label+1)]++bc1`]mp_tac) >>
      discharge_hyps >- (
        simp[Abbr`bss`,TAKE_APPEND1,TAKE_APPEND2,Abbr`bs2`,Abbr`bss0`,Abbr`aa`,Abbr`co`] >>
        conj_tac >- PROVE_TAC[] >>
        fs[SUM_APPEND,FILTER_APPEND,ALL_DISTINCT_APPEND,FILTER_REVERSE,EVERY_REVERSE,Abbr`lab`] >>
        fsrw_tac[DNF_ss][MEM_FILTER,EVERY_MEM,is_Label_rwt,ALL_DISTINCT_REVERSE,MEM_MAP,between_def] >>
        fsrw_tac[ARITH_ss][Abbr`cs1`] >>
        rw[] >> spose_not_then strip_assume_tac >> res_tac >> fsrw_tac[ARITH_ss][] ) >>
      simp[] >>
      disch_then(qspecl_then[`env0`,`vs`,`v::klvs`,`bv::blvs`,`benv`,`ret`,`args`,`cl`,`st`]mp_tac o CONJUNCT2) >>
      fs[Abbr`tt`,ADD1,Abbr`bs2`] >>
      discharge_hyps >- (
        fs[Abbr`bss0`,Abbr`bss`] >>
        fs[EVERY2_EVERY,EVERY_MEM,FORALL_PROD] >>
        rw[] >>
        match_mp_tac(MP_CANON (GEN_ALL(CONJUNCT1(SPEC_ALL Cv_bv_SUBMAP)))) >>
        simp[] >>
        qexists_tac`rd` >>
        simp[DRESTRICT_SUBSET_SUBMAP] >>
        fs[Cenv_bs_def,s_refs_def,good_rd_def,FEVERY_DEF,SUBMAP_DEF,DRESTRICT_DEF,UNCURRY]) >>
      simp[code_for_return_def] >>
      simp_tac(srw_ss()++DNF_ss)[] >>
      map_every qx_gen_tac[`br`,`rf'`,`rd''`] >>
      strip_tac >>
      map_every qexists_tac[`br`,`rf'`,`rd''`] >>
      conj_tac >- (
        match_mp_tac(SIMP_RULE std_ss [transitive_def] RTC_TRANSITIVE) >>
        qmatch_assum_abbrev_tac`bc_next^* bss bs2` >>
        qexists_tac`bs2` >> simp[] >>
        qmatch_assum_abbrev_tac`bc_next^* bs3 bs4` >>
        `bc_next^* (bs3 with code := bc0 ++ code) (bs4 with code := bc0 ++ code)` by (
          match_mp_tac RTC_bc_next_append_code >>
          map_every qexists_tac[`bs3`,`bs4`] >>
          simp[Abbr`bs3`,Abbr`bs4`,bc_state_component_equality] >>
          simp[Abbr`bss`,TAKE_APPEND1,TAKE_APPEND2,Abbr`co`] ) >>
        `bs3 with code := bc0 ++ code = bs2` by (
          simp[Abbr`bs3`,bc_state_component_equality,Abbr`bs2`,Abbr`bss`] ) >>
        fs[] >>
        match_mp_tac(SIMP_RULE std_ss [transitive_def] RTC_TRANSITIVE) >>
        HINT_EXISTS_TAC >> simp[] >> ntac 2 (pop_assum kall_tac) >>
        fs[Abbr`bs3`,Abbr`bs4`] >>
        simp[Abbr`bs2`,Abbr`bss0`,Abbr`bss`] ) >>
      fs[Abbr`bss0`,Abbr`bss`] >>
      metis_tac[IS_PREFIX_TRANS,SUBMAP_TRANS]) >>
    rpt gen_tac >>
    Q.PAT_ABBREV_TAC`cs2 = compiler_result_out_fupd (K (Stack X::Y)) B` >>
    qspecl_then[`t`,`cs2`](Q.X_CHOOSE_THEN`cp`strip_assume_tac)pushret_append_out >> pop_assum kall_tac >>
    Q.PAT_ABBREV_TAC`cs1 = compiler_result_out_fupd X Y` >>
    qspecl_then[`cenv`,`t`,`sz`,`exp'`,`0`,`cs1`,`1`](Q.X_CHOOSE_THEN`cb`strip_assume_tac)(CONJUNCT1 (CONJUNCT2 compile_append_out)) >>
    simp[Abbr`cs2`,Abbr`cs1`,Abbr`cs0`] >>
    SUBST1_TAC(Q.prove(`REVERSE cc2 ++ [Label cs.next_label] ++ REVERSE cc1 = REVERSE(cc1++Label cs.next_label::cc2)`,lrw[])) >>
    REWRITE_TAC[Once SWAP_REVERSE] >>
    simp[] >> strip_tac >>
    qpat_assum`(A.out = cb ++ B)`mp_tac >>
    Q.PAT_ABBREV_TAC`cs1 = compiler_result_out_fupd A B` >> strip_tac >>
    `cc1 = REVERSE cp ++ [Jump (Lab (cs.next_label + 1))] ∧
     cc2 = REVERSE cb ++ [Label (cs.next_label + 1)]` by (
       match_mp_tac MEM_APPEND_lemma >>
       qexists_tac`Label (cs.next_label)` >>
       simp[] >>
       fsrw_tac[DNF_ss][FILTER_APPEND,ALL_DISTINCT_APPEND,MEM_FILTER] ) >>
    qabbrev_tac`tt = case t of TCNonTail => t | TCTail j k => TCTail j (k + 1)` >>
    qspecl_then[`CTLet(sz+1)::cenv`,`tt`,`sz+1`,`cs1`,`exp'`](Q.X_CHOOSE_THEN`cd`strip_assume_tac)(CONJUNCT1 compile_append_out) >>
    first_x_assum(qspecl_then[`rd'`,`cs1`,`CTLet (sz+1)::cenv`,`sz+1`,`bs2`,`bce`,`bcr`
                             ,`TAKE(LENGTH bc0+2+LENGTH cc+2+LENGTH cc1+1)bss.code`
                             ,`REVERSE cd`,`(DROP (LENGTH cd) cc2)++bc1`]mp_tac) >>
    discharge_hyps >- (
      simp[Abbr`bss`,TAKE_APPEND1,TAKE_APPEND2,Abbr`bs2`,Abbr`bss0`,Abbr`aa`] >>
      conj_tac >- (
        qpat_assum`X = cb ++ cs1.out`mp_tac >>
        REWRITE_TAC[ONE] >>
        Cases_on`t`>>simp[compile_def,Abbr`tt`] >>
        fs[] >> rw[] >> simp[DROP_APPEND1,DROP_APPEND2,DROP_LENGTH_NIL_rwt] ) >>
      conj_tac >- PROVE_TAC[] >>
      fs[SUM_APPEND,FILTER_APPEND,ALL_DISTINCT_APPEND,FILTER_REVERSE,EVERY_REVERSE] >>
      fsrw_tac[DNF_ss][MEM_FILTER,EVERY_MEM,is_Label_rwt,ALL_DISTINCT_REVERSE,MEM_MAP,between_def] >>
      fsrw_tac[ARITH_ss][Abbr`cs1`] >>
      rw[] >> spose_not_then strip_assume_tac >> res_tac >> fsrw_tac[ARITH_ss][] ) >>
    simp[] >>
    disch_then(qspecl_then[`tt`,`bv::ig`,`sp`,`hdl`,`st`]mp_tac) >>
    discharge_hyps >- simp[Abbr`bs2`] >>
    simp[code_for_return_def] >>
    simp_tac(srw_ss()++DNF_ss)[] >>
    map_every qx_gen_tac[`br`,`rf'`,`rd''`] >>
    strip_tac >>
    map_every qexists_tac[`br`,`rf'`,`rd''`] >>
    conj_tac >- (
      match_mp_tac(SIMP_RULE std_ss [transitive_def] RTC_TRANSITIVE) >>
      qmatch_assum_abbrev_tac`bc_next^* bss bs2` >>
      qexists_tac`bs2` >> simp[] >>
      qmatch_assum_abbrev_tac`bc_next^* bs3 bs4` >>
      qspecl_then[`cenv`,`t`,`sz`,`exp'`,`0`,`cs1`,`1`,`cb`,`cd`]mp_tac compile_bindings_thm >>
      simp[] >> strip_tac >>
      `bc_next^* (bs3 with code := bc0 ++ code) (bs4 with code := bc0 ++ code)` by (
        match_mp_tac RTC_bc_next_append_code >>
        map_every qexists_tac[`bs3`,`bs4`] >>
        simp[Abbr`bs3`,Abbr`bs4`,bc_state_component_equality] >>
        simp[Abbr`bss`,TAKE_APPEND1,TAKE_APPEND2] ) >>
      `bs3 with code := bc0 ++ code = bs2` by (
        simp[Abbr`bs3`,bc_state_component_equality,Abbr`bs2`,Abbr`bss`] ) >>
      fs[] >>
      match_mp_tac(SIMP_RULE std_ss [transitive_def] RTC_TRANSITIVE) >>
      HINT_EXISTS_TAC >> simp[] >> ntac 2 (pop_assum kall_tac) >>
      fs[Abbr`bs3`,Abbr`bs4`] >>
      simp[Abbr`bs2`,Abbr`bss0`,Abbr`bss`] ) >>
    fs[Abbr`bss0`,Abbr`bss`,Abbr`bs2`] >>
    metis_tac[IS_PREFIX_TRANS,SUBMAP_TRANS]) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    ntac 2 gen_tac >> qx_gen_tac`n` >> strip_tac >> simp[] >>
    rpt gen_tac >> strip_tac >> simp[compile_def,pushret_def] >>
    qpat_assum`bce ++ bcr = X`kall_tac>>
    qid_spec_tac`code` >> simp[FORALL_AND_THM] >>
    conj_asm1_tac >- (
      gen_tac >>
      fs[code_for_push_def,Cenv_bs_def,EVERY2_EVERY,EVERY_MEM,FORALL_PROD] >>
      fs[MEM_EL,GSYM LEFT_FORALL_IMP_THM] >> rfs[] >>
      pop_assum mp_tac >>
      first_assum(qspec_then `n` mp_tac o CONV_RULE (RESORT_FORALL_CONV List.rev)) >>
      REWRITE_TAC[Once option_case_NONE_F] >> simp[EL_ZIP] >>
      disch_then(Q.X_CHOOSE_THEN`x`strip_assume_tac) >>
      strip_tac >>
      imp_res_tac Cv_bv_not_env >> strip_tac >>
      map_every qexists_tac [`[x]`,`bs.refs`,`rd`] >> rw[s_refs_with_stack] >- (
        match_mp_tac compile_varref_thm >> fs[] >>
        simp[bc_state_component_equality] >>
        rfs[el_check_def] >>
        metis_tac[APPEND_NIL])
      >- (
        qmatch_assum_rename_tac `z < LENGTH cenv`[] >>
        qmatch_abbrev_tac`X` >>
        qpat_assum`∀x y z. X ⇒ Y`(qspec_then `z` mp_tac o CONV_RULE (RESORT_FORALL_CONV List.rev)) >>
        simp[option_case_NONE_F,EL_ZIP] >> rw[] >>
        qunabbrev_tac`X` >>
        imp_res_tac lookup_ct_imp_incsz >>
        rfs[EL_ZIP]) >>
      fs[s_refs_def,good_rd_def]) >>
    rw[] >> fs[] >>
    match_mp_tac code_for_push_return >>
    rfs[el_check_def] >>
    qspecl_then[`sz`,`cs`,`EL n cenv`]strip_assume_tac compile_varref_append_out >> fs[] >>
    first_x_assum(qspec_then`REVERSE bc`mp_tac) >> simp[] >>
    fs[Once SWAP_REVERSE] >> strip_tac >>
    qmatch_assum_abbrev_tac `code_for_push rd bss bce bc0 ccode s s renv v cenv rsz` >>
    map_every qexists_tac [`bc0`,`ccode`,`renv`,`cenv`,`rsz`] >>
    simp[] >>
    qexists_tac `REVERSE args` >> fsrw_tac[ARITH_ss][EVERY2_EVERY]) >>
  strip_tac >- (
    simp[] >>
    rpt gen_tac >> strip_tac >>
    qpat_assum`bce ++ bcr = X`kall_tac>>
    qid_spec_tac`code` >> simp[FORALL_AND_THM] >>
    conj_asm1_tac >- (
      gen_tac >>
      Cases_on`l`>>rw[compile_def,LET_THM,code_for_push_def,pushret_def]>>
      qpat_assum`X = REVERSE code`(assume_tac o SIMP_RULE std_ss [Once SWAP_REVERSE]) >> fs[] >>
      qmatch_assum_abbrev_tac `code = [x]` >>
      `bc_fetch (bs with code := bc0 ++ code) = SOME x` by (
        match_mp_tac bc_fetch_next_addr >>
        qexists_tac `bc0` >>
        rw[Abbr`x`]) >> (
      rw[Once Cv_bv_cases] >>
      map_every qexists_tac [`bs.refs`,`rd`] >> reverse (rw[]) >- (
        match_mp_tac Cenv_bs_imp_incsz >>
        qexists_tac`bs with code := bce` >>
        rw[bc_state_component_equality]  ) >>
      rw[RTC_eq_NRC] >>
      qexists_tac `SUC 0` >>
      rw[NRC] >>
      rw[bc_eval1_thm] >>
      rw[bc_eval1_def,Abbr`x`] >>
      rw[bc_eval_stack_def] >>
      srw_tac[ARITH_ss][bump_pc_def,FILTER_APPEND,SUM_APPEND,ADD1])) >>
    rpt gen_tac >> strip_tac >>
    qspecl_then[`cenv`,`TCNonTail`,`sz`,`cs`,`(CLit l)`]strip_assume_tac(CONJUNCT1 compile_append_out) >> fs[] >>
    fs[Once SWAP_REVERSE] >>
    `code = REVERSE bc ++ (retbc (LENGTH args) (LENGTH klvs))` by (
      Cases_on`l`>>fs[compile_def,pushret_def] >> rw[] >> fs[Once SWAP_REVERSE]) >>
    match_mp_tac code_for_push_return >> simp[] >>
    qmatch_assum_abbrev_tac`code_for_push rd bss bce bc0 ccode s s renv v cenv rsz` >>
    map_every qexists_tac [`bc0`,`ccode`,`renv`,`cenv`,`rsz`] >> rw[] >>
    qexists_tac`REVERSE args`>>fsrw_tac[ARITH_ss][EVERY2_EVERY]) >>
  strip_tac >- (
    fsrw_tac[ETA_ss][FOLDL_UNION_BIGUNION] >>
    rpt gen_tac >> strip_tac >>
    rpt gen_tac >> strip_tac >>
    simp[compile_def,LET_THM,pushret_def] >>
    fsrw_tac[ETA_ss][] >>
    qpat_assum`bce ++ bcr = X`mp_tac >> simp[IMP_CONJ_THM] >>
    map_every qid_spec_tac[`bc1`,`code`] >> simp[FORALL_AND_THM] >>
    conj_asm1_tac >- (
      ntac 2 gen_tac >>
      qspecl_then[`cenv`,`sz`,`cs`,`exps`](Q.X_CHOOSE_THEN`cx`strip_assume_tac)(CONJUNCT2 (CONJUNCT2 compile_append_out)) >>
      fs[] >> strip_tac >>
      disch_then(assume_tac o SIMP_RULE std_ss [Once SWAP_REVERSE]) >> fs[] >>
      qmatch_assum_abbrev_tac `code = ls0 ++ [x]` >>
      fsrw_tac[DNF_ss][] >>
      first_x_assum (qspecl_then[`rd`,`cs`,`cenv`,`sz`,`bs`,`bce`,`bcr`,`bc0`,`ls0`]mp_tac) >>
      simp[Abbr`ls0`] >>
      simp[code_for_push_def] >>
      disch_then(qx_choosel_then[`bvs`,`rf`,`rd'`]strip_assume_tac) >>
      srw_tac[DNF_ss][Once Cv_bv_cases] >>
      map_every qexists_tac[`rf`,`rd'`,`bvs`] >>
      simp[] >>
      conj_tac >- (
        qmatch_assum_abbrev_tac `bc_next^* bs0 bs05` >>
        qmatch_abbrev_tac`bc_next^* bs1 bs2` >>
        `bc_next^* bs1 (bs05 with code := bs1.code)` by (
          match_mp_tac RTC_bc_next_append_code >>
          map_every qexists_tac[`bs0`,`bs05`] >>
          simp[bc_state_component_equality,Abbr`bs1`,Abbr`bs0`,Abbr`bs05`] ) >>
        rw[Once RTC_CASES2] >> disj2_tac >>
        qexists_tac `bs05 with code := bs1.code` >>
        fs[Abbr`bs0`,Abbr`bs05`] >>
        qmatch_abbrev_tac`bc_next bs0 bs2` >>
        `bc_fetch bs0 = SOME x` by (
          match_mp_tac bc_fetch_next_addr >>
          simp[Abbr`bs0`,Abbr`x`] >>
          qexists_tac`bc0 ++ REVERSE cx` >> rw[Abbr`bs1`] ) >>
        rw[bc_eval1_thm] >>
        rw[bc_eval1_def,Abbr`x`,bump_pc_def] >>
        imp_res_tac Cevaluate_list_LENGTH >>
        fs[EVERY2_EVERY] >>
        srw_tac[ARITH_ss][bc_eval_stack_def,Abbr`bs0`] >>
        unabbrev_all_tac >>
        srw_tac[ARITH_ss][SUM_APPEND,FILTER_APPEND,ADD1] >>
        rw[bc_state_component_equality] >>
        metis_tac[TAKE_LENGTH_APPEND,REVERSE_REVERSE
                 ,DROP_LENGTH_APPEND,LENGTH_REVERSE]) >>
      qmatch_assum_abbrev_tac`Cenv_bs rd' s' denv cenv sz1 bs1` >>
      `Cenv_bs rd' s' denv cenv sz (bs1 with stack := bs.stack)` by (
        match_mp_tac Cenv_bs_pops >>
        map_every qexists_tac[`REVERSE bvs`,`bs1`] >>
        imp_res_tac Cevaluate_list_LENGTH >>
        fs[] >>
        simp[bc_state_component_equality,Abbr`bs1`] >>
        `LENGTH exps = LENGTH bvs` by fs[EVERY2_EVERY] >> fs[] >>
        PROVE_TAC[Cenv_bs_CTLet_bound,ADD_SYM] ) >>
      match_mp_tac Cenv_bs_imp_incsz >>
      qexists_tac `bs1 with stack := bs.stack` >>
      rw[bc_state_component_equality,Abbr`bs1`] ) >>
    rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
    match_mp_tac code_for_push_return >>
    first_x_assum(qspecl_then[`rd`]kall_tac) >>
    qspecl_then[`cenv`,`sz`,`cs`,`exps`]strip_assume_tac(CONJUNCT2(CONJUNCT2 compile_append_out)) >>
    fs[Once SWAP_REVERSE] >>
    qmatch_assum_abbrev_tac`code_for_push rd bss bce bc0 ccode s s' renv v cenv rsz` >>
    map_every qexists_tac[`bc0`,`ccode`,`renv`,`cenv`,`rsz`] >>
    simp[Abbr`ccode`] >>
    qexists_tac`REVERSE args`>>fsrw_tac[ARITH_ss][EVERY2_EVERY]) >>
  strip_tac >- (
    simp[] >>
    rpt gen_tac >> strip_tac >>
    rpt gen_tac >> strip_tac >>
    simp[compile_def,LET_THM,pushret_def] >>
    fsrw_tac[ETA_ss][] >>
    qspecl_then[`cenv`,`sz`,`cs`,`exps`](Q.X_CHOOSE_THEN`cx`strip_assume_tac)(CONJUNCT2 (CONJUNCT2 compile_append_out)) >>
    gen_tac >>
    Q.PAT_ABBREV_TAC`cs1 = compiler_result_out_fupd X Y` >>
    qspecl_then[`t`,`cs1`](Q.X_CHOOSE_THEN`cp`strip_assume_tac)pushret_append_out >> pop_assum kall_tac >>
    simp[Once SWAP_REVERSE,Abbr`cs1`] >> rw[] >>
    first_x_assum (qspecl_then[`rd`,`cs`,`cenv`,`sz`,`bs`,`bce`,`bcr`,`bc0`,`REVERSE cx`]mp_tac) >>
    simp[] >>
    disch_then(qspecl_then[`ig`,`sp`,`hdl`,`st`]mp_tac) >>
    simp[] >>
    strip_tac >>
    match_mp_tac code_for_return_append_code >>
    HINT_EXISTS_TAC >>
    simp[bc_state_component_equality] ) >>
  strip_tac >- (
    fs[] >> rpt gen_tac >> strip_tac >>
    rpt gen_tac >> strip_tac >>
    qpat_assum`bce ++ bcr = X`mp_tac >> simp[IMP_CONJ_THM] >>
    map_every qid_spec_tac[`bc1`,`code`] >> simp[FORALL_AND_THM] >>
    conj_asm1_tac >- (
      rw[compile_def,LET_THM,pushret_def] >> fs[REVERSE_APPEND] >>
      qspecl_then[`cenv`,`TCNonTail`,`sz`,`cs`,`exp`](Q.X_CHOOSE_THEN`cx`strip_assume_tac)(CONJUNCT1 compile_append_out) >> fs[] >>
      fs[Once SWAP_REVERSE] >>
      qmatch_assum_abbrev_tac `code = ls0 ++ [x]` >>
      first_x_assum(qspecl_then[`rd`,`cs`,`cenv`,`sz`,`bs`,`bce`,`bcr`,`bc0`,`ls0`,`x::bc1`]mp_tac) >>
      discharge_hyps >- (
        fsrw_tac[DNF_ss][] >> PROVE_TAC[] ) >>
      simp[code_for_push_def,Abbr`ls0`,Once SWAP_REVERSE] >>
      disch_then(qx_choosel_then[`bv`,`rfs`,`rd'`] mp_tac o CONJUNCT1) >>
      srw_tac[DNF_ss][Once Cv_bv_cases] >>
      srw_tac[DNF_ss][Once Cv_bv_cases] >>
      map_every qexists_tac[`rfs`,`rd'`] >>
      conj_tac >- (
        qmatch_assum_abbrev_tac `bc_next^* bss bs05` >>
        qmatch_abbrev_tac`bc_next^* bs1 bs2` >>
        `bc_next^* bs1 (bs05 with code := bs1.code)` by (
          match_mp_tac RTC_bc_next_append_code >>
          map_every qexists_tac[`bss`,`bs05`] >>
          simp[bc_state_component_equality,Abbr`bs1`,Abbr`bs05`,Abbr`bss`] ) >>
        rw[Once RTC_CASES2] >> disj2_tac >>
        qexists_tac `bs05 with code := bs1.code` >> rw[] >>
        `bc_fetch (bs05 with code := bs1.code) = SOME x` by (
          match_mp_tac bc_fetch_next_addr >>
          simp[Abbr`bs05`,Abbr`x`] >>
          qexists_tac `bc0 ++ REVERSE cx` >> rw[Abbr`bs1`] ) >>
        rw[bc_eval1_thm] >>
        rw[bc_eval1_def,Abbr`x`] >>
        rw[bump_pc_def] >>
        rw[bc_eval_stack_def,Abbr`bs05`] >>
        unabbrev_all_tac >>
        srw_tac[ARITH_ss][SUM_APPEND,FILTER_APPEND,ADD1] >>
        rw[bc_state_component_equality] >>
        AP_TERM_TAC >> rw[EQ_IMP_THM] ) >>
      reverse conj_tac >- fs[] >>
      qmatch_assum_abbrev_tac`Cenv_bs rd' s' ccenv csenv sz1 bs1` >>
      `Cenv_bs rd' s' ccenv csenv sz (bs1 with stack := bs.stack)` by (
        match_mp_tac Cenv_bs_imp_decsz >>
        qexists_tac `bs1` >>
        rw[bc_state_component_equality,Abbr`bs1`,Abbr`sz1`] >>
        spose_not_then strip_assume_tac >>
        imp_res_tac Cenv_bs_CTLet_bound >>
        DECIDE_TAC ) >>
      qunabbrev_tac`sz1` >>
      match_mp_tac Cenv_bs_imp_incsz >>
      qexists_tac`bs1 with stack := bs.stack` >>
      rw[bc_state_component_equality,Abbr`bs1`] ) >>
    first_x_assum(qspec_then`rd` kall_tac) >>
    fs[compile_def,LET_THM,pushret_def] >>
    rw[]>>fs[] >>
    match_mp_tac code_for_push_return >>
    qspecl_then[`cenv`,`TCNonTail`,`sz`,`cs`,`exp`]strip_assume_tac(CONJUNCT1 compile_append_out) >>
    fs[Once SWAP_REVERSE] >>
    qmatch_assum_abbrev_tac`code_for_push rd bss bce bc0 ccode s s' renv v cenv csz` >>
    map_every qexists_tac[`bc0`,`ccode`,`renv`,`cenv`,`csz`] >>
    rw[Abbr`ccode`] >>
    qexists_tac`REVERSE args`>>fs[EVERY2_EVERY]) >>
  strip_tac >- (
    simp[] >>
    rpt gen_tac >> strip_tac >>
    rpt gen_tac >> strip_tac >>
    simp[compile_def,LET_THM,pushret_def] >>
    fsrw_tac[ETA_ss][] >>
    qspecl_then[`cenv`,`TCNonTail`,`sz`,`cs`,`exp`](Q.X_CHOOSE_THEN`cx`strip_assume_tac)(CONJUNCT1 compile_append_out) >>
    gen_tac >>
    Q.PAT_ABBREV_TAC`cs1 = compiler_result_out_fupd X Y` >>
    qspecl_then[`t`,`cs1`](Q.X_CHOOSE_THEN`cp`strip_assume_tac)pushret_append_out >> pop_assum kall_tac >>
    simp[Once SWAP_REVERSE,Abbr`cs1`] >> rw[] >>
    first_x_assum (qspecl_then[`rd`,`cs`,`cenv`,`sz`,`bs`,`bce`,`bcr`,`bc0`,`REVERSE cx`]mp_tac) >>
    simp[] >>
    disch_then(qspecl_then[`TCNonTail`,`ig`,`sp`,`hdl`,`st`]mp_tac) >>
    simp[] >>
    strip_tac >>
    match_mp_tac code_for_return_append_code >>
    HINT_EXISTS_TAC >>
    simp[bc_state_component_equality] ) >>
  strip_tac >- (
    fs[] >> rpt gen_tac >> strip_tac >>
    rpt gen_tac >> strip_tac >>
    qpat_assum`bce ++ bcr = X`mp_tac >> simp[IMP_CONJ_THM] >>
    map_every qid_spec_tac[`bc1`,`code`] >> simp[FORALL_AND_THM] >>
    conj_asm1_tac >- (
      rw[compile_def,LET_THM,pushret_def] >> fs[REVERSE_APPEND] >>
      qspecl_then[`cenv`,`TCNonTail`,`sz`,`cs`,`exp`]strip_assume_tac(CONJUNCT1 compile_append_out) >>
      fs[Once SWAP_REVERSE] >>
      qmatch_assum_abbrev_tac `code = ls0 ++ [x]` >>
      first_x_assum(qspecl_then[`rd`,`cs`,`cenv`,`sz`,`bs`,`bce`,`bcr`,`bc0`,`ls0`]mp_tac) >>
      simp[code_for_push_def,Abbr`ls0`,Once SWAP_REVERSE] >>
      disch_then(qx_choosel_then[`bv`,`rfs`,`rd'`] mp_tac o CONJUNCT1) >>
      fs[(Q.SPECL[`CConv m vs`](CONJUNCT1 (SPEC_ALL Cv_bv_cases)))] >>
      srw_tac[DNF_ss][] >>
      fs[EVERY2_EVERY,EVERY_MEM,FORALL_PROD] >>
      map_every qexists_tac[`rfs`,`rd'`,`EL n bvs`] >>
      rev_full_simp_tac(srw_ss()++DNF_ss)[MEM_ZIP] >>
      conj_tac >- (
        qmatch_assum_abbrev_tac `bc_next^* bss bs05` >>
        qmatch_abbrev_tac`bc_next^* bs1 bs2` >>
        `bc_next^* bs1 (bs05 with code := bs1.code)` by (
          match_mp_tac RTC_bc_next_append_code >>
          map_every qexists_tac[`bss`,`bs05`] >>
          simp[bc_state_component_equality,Abbr`bs1`,Abbr`bs05`,Abbr`bss`] ) >>
        rw[Once RTC_CASES2] >> disj2_tac >>
        qexists_tac `bs05 with code := bs1.code` >> rw[] >>
        `bc_fetch (bs05 with code := bs1.code) = SOME x` by (
          match_mp_tac bc_fetch_next_addr >>
          simp[Abbr`bs05`,Abbr`x`] >>
          qexists_tac `bc0 ++ REVERSE bc` >> rw[Abbr`bs1`] ) >>
        rw[bc_eval1_thm] >>
        rw[bc_eval1_def,Abbr`x`] >>
        rw[bump_pc_def] >>
        rw[bc_eval_stack_def,Abbr`bs05`] >>
        unabbrev_all_tac >>
        srw_tac[ARITH_ss][SUM_APPEND,FILTER_APPEND,ADD1] ) >>
      qmatch_assum_abbrev_tac`Cenv_bs rd' s' ccenv csenv sz1 bs1` >>
      `Cenv_bs rd' s' ccenv csenv sz (bs1 with stack := bs.stack)` by (
        match_mp_tac Cenv_bs_imp_decsz >>
        qexists_tac `bs1` >>
        rw[bc_state_component_equality,Abbr`bs1`,Abbr`sz1`] >>
        spose_not_then strip_assume_tac >>
        imp_res_tac Cenv_bs_CTLet_bound >>
        DECIDE_TAC ) >>
      qunabbrev_tac`sz1` >>
      match_mp_tac Cenv_bs_imp_incsz >>
      qexists_tac`bs1 with stack := bs.stack` >>
      simp[bc_state_component_equality,Abbr`bs1`]) >>
    first_x_assum(qspec_then`rd` kall_tac) >>
    fs[compile_def,LET_THM,pushret_def] >>
    rw[]>>fs[] >>
    match_mp_tac code_for_push_return >>
    qspecl_then[`cenv`,`TCNonTail`,`sz`,`cs`,`exp`]strip_assume_tac(CONJUNCT1 compile_append_out) >>
    fs[Once SWAP_REVERSE] >>
    qmatch_assum_abbrev_tac`code_for_push rd bss bce bc0 ccode s s' ccenv v csenv csz` >>
    map_every qexists_tac[`bc0`,`ccode`,`ccenv`,`csenv`,`csz`] >>
    rw[Abbr`ccode`] >>
    qexists_tac`REVERSE args` >> fs[EVERY2_EVERY]) >>
  strip_tac >- (
    simp[] >>
    rpt gen_tac >> strip_tac >>
    rpt gen_tac >> strip_tac >>
    simp[compile_def,LET_THM,pushret_def] >>
    fsrw_tac[ETA_ss][] >>
    qspecl_then[`cenv`,`TCNonTail`,`sz`,`cs`,`exp`](Q.X_CHOOSE_THEN`cx`strip_assume_tac)(CONJUNCT1 compile_append_out) >>
    gen_tac >>
    Q.PAT_ABBREV_TAC`cs1 = compiler_result_out_fupd X Y` >>
    qspecl_then[`t`,`cs1`](Q.X_CHOOSE_THEN`cp`strip_assume_tac)pushret_append_out >> pop_assum kall_tac >>
    simp[Once SWAP_REVERSE,Abbr`cs1`] >> rw[] >>
    first_x_assum (qspecl_then[`rd`,`cs`,`cenv`,`sz`,`bs`,`bce`,`bcr`,`bc0`,`REVERSE cx`]mp_tac) >>
    simp[] >>
    disch_then(qspecl_then[`TCNonTail`,`ig`,`sp`,`hdl`,`st`]mp_tac) >>
    simp[] >>
    strip_tac >>
    match_mp_tac code_for_return_append_code >>
    HINT_EXISTS_TAC >>
    simp[bc_state_component_equality] ) >>

  strip_tac >- (
    simp[] >>
    rpt gen_tac >> strip_tac >>
    rpt gen_tac >> strip_tac >>
    simp[compile_def] >>
    REWRITE_TAC[ONE] >> REWRITE_TAC[compile_def] >> simp[compile_def] >>
    qspecl_then[`cenv`,`TCNonTail`,`sz`,`cs`,`exp`](Q.X_CHOOSE_THEN`cx`strip_assume_tac)(CONJUNCT1 compile_append_out) >> fs[] >>
    conj_tac >- (
      gen_tac >> strip_tac >>
      simp[GSYM FORALL_AND_THM] >> ntac 2 gen_tac >>
      reverse(Cases_on`∃bc10. code = REVERSE cx ++ bc10`) >- (
        fsrw_tac[DNF_ss][] >>
        conj_tac >> rpt gen_tac >>
        Q.PAT_ABBREV_TAC`tt = X:call_context` >>
        Q.PAT_ABBREV_TAC`ee = Y::cenv`>>
        Q.PAT_ABBREV_TAC`cs0 = compile cenv X Y Z A` >>
        qspecl_then[`ee`,`tt`,`sz + 1`,`cs0`,`exp'`](strip_assume_tac)(CONJUNCT1 compile_append_out) >> fs[] >>
        fs[Once SWAP_REVERSE] >> strip_tac >> fs[]) >> fs[] >>
      POP_ASSUM_LIST (MAP_EVERY ASSUME_TAC) >>
      first_x_assum(qspecl_then[`rd`,`cs`,`cenv`,`sz`,`bs`,`bce`,`bcr`,`bc0`]mp_tac) >>
      `LENGTH s ≤ LENGTH s' ∧
       LENGTH s' ≤ LENGTH s''` by PROVE_TAC[LESS_EQ_TRANS,Cevaluate_store_SUBSET,FST] >>
      discharge_hyps >- (
        fsrw_tac[DNF_ss][ALL_DISTINCT_APPEND] >> rfs[] >> PROVE_TAC[] ) >>
      fs[ALL_DISTINCT_APPEND] >> rfs[] >>
      fs[Once SWAP_REVERSE] >>
      disch_then (mp_tac o SIMP_RULE (srw_ss()++DNF_ss) [code_for_push_def,LET_THM] o CONJUNCT1) >>
      reverse(Cases_on`∃bc11. bs.code = bc0 ++ REVERSE cx ++ bc11`) >- (
        rw[] >> fs[] ) >> fs[] >>
      disch_then (qx_choosel_then[`rf`,`rd'`,`bv`]strip_assume_tac) >>
      qmatch_assum_abbrev_tac`bc_next^* bs bs1` >>
      conj_tac >- (
        Q.PAT_ABBREV_TAC`tt = X:call_context` >>
        Q.PAT_ABBREV_TAC`ee = Y::cenv`>>
        Q.PAT_ABBREV_TAC`cs0 = compile cenv X Y Z A` >>
        qspecl_then[`ee`,`tt`,`sz + 1`,`cs0`,`exp'`](strip_assume_tac)(CONJUNCT1 compile_append_out) >> fs[] >>
        fs[Abbr`tt`,Once SWAP_REVERSE] >>
        first_x_assum(qspecl_then[`rd'`,`cs0`,`ee`,`sz+1`,`bs1`,`bce`,`bcr`,`bc0 ++ REVERSE cx`]mp_tac) >>
        simp[Abbr`ee`] >>
        discharge_hyps >- (
          conj_tac >- (
            imp_res_tac Cevaluate_Clocs >> fs[] >>
            fsrw_tac[DNF_ss][SUBSET_DEF] >>
            metis_tac[LESS_LESS_EQ_TRANS]) >>
          conj_tac >- (
            imp_res_tac Cevaluate_Clocs >> fs[] ) >>
          fsrw_tac[DNF_ss][] >>
          simp[Abbr`cs0`,Abbr`bs1`,ADD1] >>
          qspecl_then[`s`,`env`,`exp`,`(s',Cval v)`]mp_tac(CONJUNCT1 Cevaluate_vlabs) >>
          simp[] >> strip_tac >>
          qspecl_then[`s`,`env`,`exp`,`(s',Cval v)`]mp_tac(CONJUNCT1 Cevaluate_all_vlabs) >>
          simp[] >> strip_tac >>
          conj_tac >- ( fsrw_tac[DNF_ss][SUBSET_DEF,EVERY_MEM] >> metis_tac[] ) >>
          conj_tac >- ( fsrw_tac[DNF_ss][SUBSET_DEF,EVERY_MEM] >> metis_tac[] ) >>
          conj_tac >- (
            fsrw_tac[DNF_ss][SUBSET_DEF] >>
            Cases>>fsrw_tac[ARITH_ss][]>>
            strip_tac>>res_tac>>fsrw_tac[ARITH_ss][]) >>
          conj_tac >- (
            match_mp_tac Cenv_bs_FUPDATE >>
            qexists_tac `bs with <|code := bce; pc := next_addr bs.inst_length (bc0 ++ REVERSE cx); refs := rf|>` >>
            simp[bc_state_component_equality] >>
            match_mp_tac Cenv_bs_imp_decsz >> rfs[] >>
            qmatch_assum_abbrev_tac`Cenv_bs rd' s' envv cenv szz bss` >>
            qexists_tac `bss` >>
            simp[bc_state_component_equality,Abbr`bss`,Abbr`szz`] >>
            spose_not_then strip_assume_tac >>
            imp_res_tac Cenv_bs_CTLet_bound >>
            DECIDE_TAC) >>
          match_mp_tac compile_labels_lemma >>
          map_every qexists_tac[`cenv`,`TCNonTail`,`sz`,`cs`,`exp`] >>
          simp[Once SWAP_REVERSE] ) >>
        disch_then(mp_tac o SIMP_RULE (srw_ss()++DNF_ss) [code_for_push_def,LET_THM,Once SWAP_REVERSE] o CONJUNCT1) >>
        ntac 2 strip_tac >> fs[] >> rfs[] >>
        qpat_assum`∀bc1. X`mp_tac >>
        `bs1.code = bs.code` by rw[Abbr`bs1`] >>
        simp[] >>
        disch_then(qx_choosel_then[`rf'`,`rd''`,`bv'`]strip_assume_tac) >>
        srw_tac[DNF_ss][code_for_push_def,LET_THM] >>
        map_every qexists_tac [`rf'`,`rd''`,`bv'`] >>
        qmatch_assum_abbrev_tac`bc_next^* bs1 bs2` >>
        conj_tac >- (
          match_mp_tac(SIMP_RULE std_ss [transitive_def] RTC_TRANSITIVE) >>
          qexists_tac`bs2` >>
          conj_tac >- metis_tac[RTC_TRANSITIVE,transitive_def] >>
          match_mp_tac RTC_SUBSET >>
          rw[bc_eval1_thm] >>
          `bc_fetch bs2 = SOME (Stack (Pops 1))` by (
            match_mp_tac bc_fetch_next_addr >>
            simp[Abbr`bs2`] >>
            qexists_tac`bc0 ++ REVERSE cx ++ REVERSE bc`>>rw[] ) >>
          rw[bc_eval1_def] >>
          rw[bump_pc_def] >>
          srw_tac[ARITH_ss][bc_eval_stack_def,Abbr`bs2`,Abbr`bs1`] >>
          rw[bc_state_component_equality] >>
          srw_tac[ARITH_ss][FILTER_APPEND,SUM_APPEND] ) >>
        conj_tac >- fs[Abbr`bs1`] >>
        conj_tac >- (
          qmatch_abbrev_tac`Cenv_bs rd'' s'' env cenv (sz + 1) bs4` >>
          match_mp_tac Cenv_bs_imp_incsz >>
          qmatch_assum_abbrev_tac`Cenv_bs rd'' s'' env3 renv1 rsz1 bs3` >>
          qexists_tac`bs4 with <| stack := bs.stack; pc := bs3.pc |>` >>
          reverse(rw[]) >- rw[bc_state_component_equality,Abbr`bs4`] >>
          qspecl_then[`rd''`,`s''`,`env3`,`renv1`,`rsz1`,`bs3`]mp_tac Cenv_bs_DOMSUB >>
          simp[Abbr`renv1`,Abbr`rsz1`,Abbr`env3`] >> strip_tac >>
          match_mp_tac Cenv_bs_imp_decsz >>
          qexists_tac`bs4 with stack := bv::bs.stack` >>
          reverse(rw[]) >-(rw[bc_state_component_equality,Abbr`bs4`])
          >- (
            imp_res_tac Cenv_bs_CTLet_bound >>
            pop_assum (qspec_then`sz +1`mp_tac) >>
            srw_tac[ARITH_ss][] ) >>
          match_mp_tac Cenv_bs_imp_decsz >>
          qexists_tac`bs4 with stack := bs3.stack` >>
          reverse(rw[]) >-(rw[bc_state_component_equality,Abbr`bs4`,Abbr`bs3`,Abbr`bs1`])
          >- (
            imp_res_tac Cenv_bs_CTLet_bound >>
            pop_assum (qspec_then`sz +2`mp_tac) >>
            srw_tac[ARITH_ss][] ) >>
          `bs4 with stack := bs3.stack = bs3 with pc := bs4.pc` by (
            rw[Abbr`bs4`,Abbr`bs3`,bc_state_component_equality,Abbr`bs1`] ) >>
          fs[Cenv_bs_with_pc] >> fsrw_tac[ARITH_ss][]) >>
        fs[Abbr`bs1`] >> metis_tac[SUBMAP_TRANS,IS_PREFIX_TRANS]) >>
      ntac 2 gen_tac >>
      Q.PAT_ABBREV_TAC`tt = X:call_context` >>
      Q.PAT_ABBREV_TAC`ee = Y::cenv`>>
      Q.PAT_ABBREV_TAC`cs0 = compile cenv X Y Z A` >>
      qspecl_then[`ee`,`tt`,`sz + 1`,`cs0`,`exp'`](Q.X_CHOOSE_THEN`cy`strip_assume_tac)(CONJUNCT1 compile_append_out) >> fs[] >>
      fs[Abbr`tt`,Once SWAP_REVERSE] >> strip_tac >>
      first_x_assum(qspecl_then[`rd'`,`cs0`,`ee`,`sz + 1`,`bs1`,`bce`,`bcr`,`bc0 ++ REVERSE cx`]mp_tac) >>
      simp[Abbr`ee`] >>
      discharge_hyps >- (
        conj_tac >- (
          imp_res_tac Cevaluate_Clocs >> fs[] >>
          fsrw_tac[DNF_ss][SUBSET_DEF] >>
          metis_tac[LESS_LESS_EQ_TRANS]) >>
        conj_tac >- (
          imp_res_tac Cevaluate_Clocs >> fs[] ) >>
        simp[Abbr`cs0`,Abbr`bs1`,ADD1] >>
        qspecl_then[`s`,`env`,`exp`,`(s',Cval v)`]mp_tac(CONJUNCT1 Cevaluate_vlabs) >>
        simp[] >> strip_tac >>
        qspecl_then[`s`,`env`,`exp`,`(s',Cval v)`]mp_tac(CONJUNCT1 Cevaluate_all_vlabs) >>
        simp[] >> strip_tac >>
        conj_tac >- ( fsrw_tac[DNF_ss][SUBSET_DEF,EVERY_MEM] >> metis_tac[] ) >>
        conj_tac >- ( fsrw_tac[DNF_ss][SUBSET_DEF,EVERY_MEM] >> metis_tac[] ) >>
        conj_tac >- (
          fsrw_tac[DNF_ss][SUBSET_DEF] >>
          Cases>>fsrw_tac[ARITH_ss][]>>
          strip_tac>>res_tac>>fsrw_tac[ARITH_ss][]) >>
        conj_tac >- (
          match_mp_tac Cenv_bs_FUPDATE >>
          qexists_tac `bs with <|code := bce; pc := next_addr bs.inst_length (bc0 ++ REVERSE cx); refs := rf|>` >>
          simp[bc_state_component_equality] >>
          match_mp_tac Cenv_bs_imp_decsz >> rfs[] >>
          qmatch_assum_abbrev_tac`Cenv_bs rd' s' envv cenv szz bss` >>
          qexists_tac `bss` >>
          simp[bc_state_component_equality,Abbr`bss`,Abbr`szz`] >>
          spose_not_then strip_assume_tac >>
          imp_res_tac Cenv_bs_CTLet_bound >>
          DECIDE_TAC) >>
        match_mp_tac compile_labels_lemma >>
        map_every qexists_tac[`cenv`,`TCNonTail`,`sz`,`cs`,`exp`] >>
        simp[Once SWAP_REVERSE] ) >>
      disch_then(mp_tac o SIMP_RULE (srw_ss()++DNF_ss) [] o CONJUNCT2) >>
      strip_tac >> rpt gen_tac >> strip_tac >>
      rw[] >> fs[] >> rfs[] >>
      qpat_assum`∀code bc1. X`(mp_tac o (CONV_RULE (RESORT_FORALL_CONV (op@ o partition (C mem ["args","klvs'"] o fst o dest_var))))) >>
      disch_then(qspecl_then[`v::klvs`,`args`]mp_tac) >> simp[ADD1] >>
      simp[Once SWAP_REVERSE] >>
      `bs1.code = bs.code` by rw[Abbr`bs1`] >>
      fsrw_tac[ARITH_ss][] >>
      disch_then(qspecl_then[`env0`,`vs`]mp_tac) >>
      simp[FUPDATE_LIST_THM] >>
      fsrw_tac[DNF_ss][] >>
      simp[Abbr`bs1`] >>
      disch_then(qspecl_then[`blvs`,`st`]mp_tac o (CONV_RULE (RESORT_FORALL_CONV List.rev))) >>
      simp[] >>
      discharge_hyps >- (
        fs[EVERY2_EVERY,EVERY_MEM,FORALL_PROD] >>
        rw[] >>
        match_mp_tac(MP_CANON (GEN_ALL(CONJUNCT1(SPEC_ALL Cv_bv_SUBMAP)))) >>
        simp[] >>
        qexists_tac`rd` >>
        simp[DRESTRICT_SUBSET_SUBMAP] >>
        fs[Cenv_bs_def,s_refs_def,good_rd_def,FEVERY_DEF,SUBMAP_DEF,DRESTRICT_DEF,UNCURRY]) >>
      simp[code_for_return_def] >>
      disch_then(qx_choosel_then[`bv2`,`rd2`,`rf2`]strip_assume_tac) >>
      map_every qexists_tac[`bv2`,`rd2`,`rf2`] >>
      simp[] >>
      conj_tac >- metis_tac[RTC_TRANSITIVE,transitive_def] >>
      metis_tac[SUBMAP_TRANS,IS_PREFIX_TRANS] ) >>
    cheat ) >>
  strip_tac >- cheat >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    rpt gen_tac >> strip_tac >>
    simp[compile_def,pushret_def] >>
    Q.ISPECL_THEN[`cenv`,`sz`,`cs`,`defs`]mp_tac compile_closures_thm >>
    simp[] >>
    disch_then(Q.X_CHOOSE_THEN`cc`mp_tac) >>
    strip_tac >>
    reverse(Cases_on`∃bc10. bs.code = bc0 ++ cc ++ bc10`) >- (
      qmatch_assum_abbrev_tac`X.out = REVERSE cc ++ cs.out` >>
      conj_tac >> gen_tac >> strip_tac >> TRY conj_tac >> rpt gen_tac >>
      Q.PAT_ABBREV_TAC`tt = Y:call_context`>>
      strip_tac >>
      qspecl_then[`cenv`,`tt`,`sz`,`exp`,`0`,`X`,`LENGTH defs`]mp_tac(CONJUNCT1 (CONJUNCT2 compile_append_out)) >>
      rw[Once SWAP_REVERSE_SYM] >> fs[] ) >>
    fs[] >>
    first_x_assum(qspecl_then[`bs`,`bc0`,`bc10`,`FDOM rd.cls`]mp_tac) >>
    simp[] >>
    discharge_hyps >- (
      qpat_assum`∀rd yy. Z`kall_tac >>
      fs[SUM_eq_0,MEM_MAP,GSYM LEFT_FORALL_IMP_THM,EVERY_MEM] >>
      conj_asm1_tac >- (
        fsrw_tac[DNF_ss][free_labs_defs_MAP,MEM_FLAT,MEM_GENLIST] >>
        rpt strip_tac >> res_tac >>
        PairCases_on`e` >>
        Cases_on`e0`>>fs[]) >>
      fsrw_tac[DNF_ss][MEM_FLAT,MEM_MAP] >>
      simp[GSYM FORALL_AND_THM,GSYM IMP_CONJ_THM] >>
      qx_gen_tac`def` >> strip_tac >>
      `IS_SOME (FST def)` by metis_tac[] >>
      `∃n. n < LENGTH defs ∧ (EL n defs = def)` by metis_tac[MEM_EL] >>
      `code_env_cd bce ((LENGTH env,LENGTH defs,n),(THE(FST def)),(SND def))` by (
        last_x_assum match_mp_tac >>
        simp[free_labs_defs_MAP,MEM_FLAT,MEM_GENLIST] >>
        simp_tac(srw_ss()++DNF_ss)[] >>
        qexists_tac`n` >>
        PairCases_on`def` >> Cases_on`def0` >> fs[] >>
        PairCases_on`x`>>simp[] ) >>
      PairCases_on`def`>>Cases_on`def0`>>fs[]>>PairCases_on`x`>>
      qpat_assum`X ++ A = Y ++ Z`(assume_tac o SYM) >>
      fs[code_env_cd_def,bc_find_loc_def] >>
      conj_tac >- (
        qmatch_abbrev_tac`IS_SOME X` >>
        Cases_on`X`>>rw[bc_find_loc_def]>>
        fs[markerTheory.Abbrev_def] >>
        imp_res_tac(GSYM bc_find_loc_aux_NONE)>>
        fs[]) >>
      fs[good_cd_def] >>
      `LENGTH cenv = LENGTH env` by fs[Cenv_bs_def,EVERY2_EVERY] >>
      fs[EVERY_MEM] >>
      qx_gen_tac`z` >>
      reverse conj_tac >- (
        fs[bind_fv_def,LET_THM,MEM_FILTER,MEM_GENLIST] ) >>
      rator_x_assum`Cenv_bs`mp_tac >>
      simp[Cenv_bs_def,EVERY2_EVERY,EVERY_MEM,FORALL_PROD,MEM_ZIP,GSYM LEFT_FORALL_IMP_THM] >>
      simp[option_case_NONE_F] >>
      metis_tac[optionTheory.IS_SOME_DEF] ) >>
    disch_then(Q.X_CHOOSE_THEN`rs`strip_assume_tac) >>
    qmatch_assum_abbrev_tac`bc_next^* bs bs1` >>
    qabbrev_tac`rd' = rd with cls := rd.cls |++ (GENLIST (λi. (EL i rs, (env, defs, i))) (LENGTH rs))` >>
    `rd.cls ⊑ rd'.cls` by (
      simp[Abbr`rd'`] >>
      simp[SUBMAP_DEF,FDOM_FUPDATE_LIST] >>
      rw[] >> match_mp_tac EQ_SYM >>
      match_mp_tac FUPDATE_LIST_APPLY_NOT_MEM >>
      simp[MAP_GENLIST,combinTheory.o_DEF,MEM_GENLIST] >>
      fs[Cenv_bs_def,s_refs_def,good_rd_def,FEVERY_DEF,UNCURRY] >>
      metis_tac[MEM_EL]) >>
    Q.PAT_ABBREV_TAC`ccs = compile_closures cenv sz cs defs` >>
    first_x_assum(qspecl_then[`rd'`,`ccs`,
      `REVERSE (GENLIST(λm. CTLet (sz+m+1))(LENGTH defs)) ++ cenv`,
      `sz+(LENGTH defs)`,
      `bs1`,`bce`,`bcr`,`bc0++cc`]mp_tac) >>
    discharge_hyps >- (
      simp[] >>
      conj_tac >- (
        fsrw_tac[DNF_ss][SUBSET_DEF,MEM_GENLIST] >>
        PROVE_TAC[] ) >>
      conj_tac >- simp[Abbr`bs1`] >>
      conj_tac >- simp[EVERY_GENLIST] >>
      conj_tac >- PROVE_TAC[ADD_SYM] >>
      conj_tac >- (
        fsrw_tac[DNF_ss][MEM_GENLIST,MEM_FLAT,MEM_MAP,vlabs_list_MAP] >>
        reverse conj_tac >- metis_tac[] >>
        conj_tac >- metis_tac[] >>
        fsrw_tac[DNF_ss][EVERY_MEM,MEM_FLAT,MEM_MAP] >>
        metis_tac[] ) >>
      conj_tac >- simp[Abbr`bs1`] >>
      conj_tac >- (
        fsrw_tac[DNF_ss][SUBSET_DEF,FOLDL_UNION_BIGUNION,LET_THM] >>
        rw[] >> res_tac >> fsrw_tac[ARITH_ss][]) >>
      conj_tac >- (
        match_mp_tac Cenv_bs_FUPDATE_LIST >>
        Q.PAT_ABBREV_TAC`vs = GENLIST (CRecClos env defs) Y` >>
        map_every qexists_tac[`vs`,`env`,`cenv`,`sz`] >>
        `LENGTH vs = LENGTH defs` by simp[Abbr`vs`] >>
        simp[] >>
        qexists_tac`bs1 with <| stack := bs.stack; code := bce |>` >>
        simp[bc_state_component_equality,Abbr`bs1`] >>
        reverse conj_asm2_tac >- (
          rator_x_assum`RTC`kall_tac >>
          simp[EVERY2_EVERY,EVERY_MEM,FORALL_PROD,MEM_ZIP,GSYM LEFT_FORALL_IMP_THM] >>
          qx_gen_tac`n`>>strip_tac >>
          simp[EL_MAP,Abbr`vs`] >>
          fsrw_tac[DNF_ss][EVERY_MEM,MEM_FLAT,MEM_MAP] >>
          qabbrev_tac`def = EL n defs` >>
          `MEM def defs` by metis_tac[MEM_EL] >>
          `code_env_cd bce ((LENGTH env,LENGTH defs,n),(THE(FST def)),(SND def))` by (
            last_x_assum match_mp_tac >>
            simp[free_labs_defs_MAP,MEM_FLAT,MEM_GENLIST] >>
            simp_tac(srw_ss()++DNF_ss)[] >>
            qexists_tac`n` >>
            qunabbrev_tac`def` >> qabbrev_tac`def = EL n defs` >>
            res_tac >>
            PairCases_on`def` >> Cases_on`def0` >> fs[] >>
            PairCases_on`x`>>simp[] ) >>
          res_tac >>
          PairCases_on`def`>>Cases_on`def0`>>fs[]>>PairCases_on`x`>>
          qpat_assum`X ++ A = Y ++ Z`(assume_tac o SYM) >>
          fs[code_env_cd_def,bc_find_loc_def,good_cd_def] >>
          simp[Once Cv_bv_cases,el_check_def] >>
          qpat_assum`X = bind_fv A B C` mp_tac >>
          simp[bind_fv_def] >>
          strip_tac >>
          conj_asm1_tac >- (
            rw[EVERY_FILTER,EVERY_GENLIST] ) >>
          conj_asm1_tac >- (
            qsuff_tac`MEM (Label x0) bce` >- (
              metis_tac[bc_find_loc_aux_append_code,bc_find_loc_aux_NONE,optionTheory.option_CASES,optionTheory.THE_DEF] ) >>
            rw[]) >>
          simp[Once Cv_bv_cases] >>
          conj_tac >- (
            gen_tac >> strip_tac >>
            Q.PAT_ABBREV_TAC`recs:num list = FILTER X Y` >>
            conj_asm1_tac >- (
              rw[] >> fs[EVERY_MEM,MEM_EL,GSYM LEFT_FORALL_IMP_THM] ) >>
            simp[EL_APPEND1,EL_MAP] >>
            map_every qexists_tac[`env`,`defs`,`EL i recs`] >>
            simp[FLOOKUP_DEF,Abbr`rd'`,FDOM_FUPDATE_LIST,MEM_MAP,MEM_GENLIST,EXISTS_PROD] >>
            conj_tac >- metis_tac[] >>
            qho_match_abbrev_tac`(fm |++ ls) ' k = X` >>
            qho_match_abbrev_tac`P ((fm |++ ls) ' k)` >>
            ho_match_mp_tac FUPDATE_LIST_ALL_DISTINCT_APPLY_MEM >>
            `MAP FST ls = rs` by (
              simp[LIST_EQ_REWRITE,Abbr`ls`,EL_MAP] ) >>
            simp[] >>
            simp[MEM_EL,Abbr`ls`,Abbr`P`] >>
            qexists_tac`EL i recs` >>
            simp[Abbr`k`] ) >>
          gen_tac >> strip_tac >>
          Q.PAT_ABBREV_TAC`envs:num list = MAP X Y` >>
          `i < LENGTH envs` by rw[Abbr`envs`] >>
          simp[EL_APPEND2,EL_MAP] >>
          conj_asm1_tac >- (
            fs[EVERY_MEM,MEM_EL,GSYM LEFT_FORALL_IMP_THM] ) >>
          rator_x_assum`Cenv_bs`mp_tac >>
          simp[Cenv_bs_def,EVERY2_EVERY,EVERY_MEM] >> strip_tac >>
          rfs[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM] >>
          qpat_assum`∀n. n < LENGTH cenv ⇒ P`(qspec_then`EL i envs`mp_tac) >>
          simp[option_case_NONE_F] >> rw[] >> simp[] >>
          match_mp_tac (GEN_ALL (MP_CANON (CONJUNCT1 (SPEC_ALL Cv_bv_SUBMAP)))) >>
          HINT_EXISTS_TAC >> simp[] >>
          simp[Abbr`rd'`] ) >>
        match_mp_tac Cenv_bs_change_store >>
        Q.PAT_ABBREV_TAC`pc = next_addr il X` >>
        map_every qexists_tac[`rd`,`s`,`bs with <| pc := pc ; code := bce|>`] >>
        simp[bc_state_component_equality,Abbr`rd'`,Cenv_bs_with_pc] >>
        fs[Cenv_bs_def,s_refs_def] >>
        reverse conj_tac >- (
          simp[SUBMAP_DEF,DRESTRICT_DEF,FDOM_FUPDATE_LIST] >>
          rw[] >>
          match_mp_tac EQ_SYM >>
          match_mp_tac FUPDATE_LIST_APPLY_NOT_MEM >>
          simp[MAP_ZIP] >>
          metis_tac[] ) >>
        fs[Cenv_bs_def,s_refs_def,fmap_rel_def,good_rd_def] >>
        conj_tac >- (
          fs[FEVERY_DEF,UNCURRY,FDOM_FUPDATE_LIST] >>
          simp[MAP_GENLIST,combinTheory.o_DEF,MAP_ZIP,MEM_GENLIST] >>
          qx_gen_tac`x` >>
          Q.ISPECL_THEN[`rs`,`x`](mp_tac o SYM)MEM_EL >>
          simp[] >> disch_then kall_tac >>
          Cases_on`MEM x rs` >> simp[] >- (
            fs[EVERY_MEM] >>
            conj_asm1_tac >- metis_tac[] >>
            Q.PAT_ABBREV_TAC`cls = ((rd.cls |++ ls) ' x)` >>
            `∃i. i < LENGTH rs ∧ (x = EL i rs)` by metis_tac[MEM_EL] >>
            `cls = (env,defs,i)` by (
              qunabbrev_tac`cls` >>
              qho_match_abbrev_tac`(fm |++ ls) ' x = y` >>
              qho_match_abbrev_tac`P ((fm |++ ls) ' x)` >>
              ho_match_mp_tac FUPDATE_LIST_ALL_DISTINCT_APPLY_MEM >>
              simp[Abbr`ls`,MAP_GENLIST,combinTheory.o_DEF,MEM_GENLIST] >>
              asm_simp_tac(srw_ss()++DNF_ss)[Abbr`P`,Abbr`y`] >> rfs[] >>
              qmatch_abbrev_tac`ALL_DISTINCT ls` >>
              `ls = rs` by (
                unabbrev_all_tac >>
                match_mp_tac GENLIST_EL >>
                simp[] ) >>
              simp[] ) >>
            simp[] >>
            qho_match_abbrev_tac`P ((bs.refs |++ ls) ' (EL i rs))` >>
            ho_match_mp_tac FUPDATE_LIST_ALL_DISTINCT_APPLY_MEM >>
            simp[Abbr`ls`,MAP_ZIP,MEM_ZIP] >>
            asm_simp_tac(srw_ss()++DNF_ss)[] >>
            qexists_tac`i` >>
            simp[Abbr`P`,EL_MAP] >>
            fs[EVERY2_EVERY,EVERY_MEM,FORALL_PROD] >> rfs[] >>
            first_x_assum match_mp_tac >>
            simp[Abbr`vs`,MEM_ZIP] >>
            qexists_tac`i` >>
            simp[EL_MAP] ) >>
          Q.PAT_ABBREV_TAC`bv = (bs.refs |++ ls) ' x` >>
          Q.PAT_ABBREV_TAC`dd = (rd.cls |++ ls) ' x` >>
          qsuff_tac`(bv = bs.refs ' x) ∧ (dd = rd.cls ' x)` >- (
            ntac 2 strip_tac >>
            match_mp_tac (MP_CANON (GEN_ALL (CONJUNCT1 (SPEC_ALL Cv_bv_SUBMAP)))) >> simp[] >>
            qexists_tac`rd` >> simp[] >> rfs[]) >>
          map_every qunabbrev_tac[`bv`,`dd`] >>
          conj_tac >> match_mp_tac FUPDATE_LIST_APPLY_NOT_MEM >>
          simp[MAP_ZIP,MAP_GENLIST,combinTheory.o_DEF] >>
          simp[MEM_GENLIST] >>
          fs[MEM_EL] >> metis_tac[] ) >>
        conj_tac >- (
          simp[EVERY_MEM,FDOM_FUPDATE_LIST,MAP_ZIP] >>
          fs[EVERY_MEM] ) >>
        fs[Cenv_bs_def,s_refs_def,EVERY2_EVERY,good_rd_def,EVERY_MEM,FORALL_PROD] >>
        rator_x_assum`RTC`kall_tac >>
        simp[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM] >>
        gen_tac >> strip_tac >> simp[EL_MAP] >>
        Q.PAT_ABBREV_TAC`bvs:bc_value list = MAP X Y` >>
        qsuff_tac`EL n rd.sm ∉ set (MAP FST (ZIP (rs,bvs)))` >- (
          strip_tac >>
          simp[FUPDATE_LIST_APPLY_NOT_MEM] >>
          match_mp_tac (MP_CANON (GEN_ALL (CONJUNCT1 (SPEC_ALL Cv_bv_SUBMAP)))) >> simp[] >>
          qexists_tac`rd` >> simp[] >>
          rfs[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM,EL_MAP] ) >>
        simp[MAP_ZIP,Abbr`bvs`] >>
        metis_tac[MEM_EL]) >>
      fs[GSYM FILTER_EQ_NIL,combinTheory.o_DEF] >>
      simp[ALL_DISTINCT_APPEND,FILTER_APPEND,Abbr`ccs`] ) >>
    simp[] >>
    strip_tac >>
    Cases_on`beh`>>fs[] >- (
      pop_assum kall_tac >>
      conj_tac >- (
        pop_assum kall_tac >>
        pop_assum mp_tac >>
        Q.PAT_ABBREV_TAC`cenv1 = ls ++ cenv` >>
        qspecl_then[`cenv1`,`TCNonTail`,`sz + LENGTH defs`,`ccs`,`exp`](Q.X_CHOOSE_THEN`ce`strip_assume_tac)(CONJUNCT1 compile_append_out) >>
        disch_then(qspec_then`REVERSE ce`mp_tac) >>
        qspecl_then[`cenv`,`TCNonTail`,`sz`,`exp`,`0`,`ccs`,`LENGTH defs`](Q.X_CHOOSE_THEN`cb`strip_assume_tac)(CONJUNCT1(CONJUNCT2 compile_append_out)) >>
        `bs1.code = bs.code` by rw[Abbr`bs1`] >>
        qspecl_then[`cenv`,`TCNonTail`,`sz`,`exp`,`0`,`ccs`,`LENGTH defs`]mp_tac compile_bindings_thm >>
        simp[Once SWAP_REVERSE] >>
        qpat_assum`X = ce ++ ccs.out`mp_tac >>
        simp[] >> strip_tac >> strip_tac >>
        strip_tac >> gen_tac >> strip_tac >>
        fs[] >>
        qpat_assum`code_for_push rd' bs1 bce X Y Z s' A B G D`mp_tac >>
        simp[code_for_push_def] >>
        asm_simp_tac(srw_ss()++DNF_ss)[] >>
        map_every qx_gen_tac[`rf1`,`rd1`,`bv1`] >>
        strip_tac >>
        map_every qexists_tac[`rf1`,`rd1`,`bv1`] >>
        conj_tac >- (
          qmatch_assum_abbrev_tac`bc_next^* bs1 bs2` >>
          qmatch_abbrev_tac`bc_next^* bs bs3` >>
          qsuff_tac `bc_next bs2 bs3` >- metis_tac[RTC_TRANSITIVE,transitive_def,RTC_SUBSET] >>
          simp[bc_eval1_thm] >>
          `bc_fetch bs2 = SOME (Stack (Pops (LENGTH defs)))` by (
            match_mp_tac bc_fetch_next_addr >>
            simp[Abbr`bs2`] >>
            qexists_tac`bc0 ++ cc ++ REVERSE ce` >>
            simp[] ) >>
          simp[bc_eval1_def] >>
          simp[bc_eval_stack_def,Abbr`bs2`,bump_pc_def] >>
          simp[Abbr`bs1`,Abbr`bs3`,bc_state_component_equality,SUM_APPEND,FILTER_APPEND] >>
          Q.PAT_ABBREV_TAC`f = (X:def->bc_value)` >>
          lrw[DROP_APPEND1,DROP_LENGTH_NIL_rwt] ) >>
        conj_tac >- fs[Abbr`bs1`] >>
        conj_asm2_tac >- (
          match_mp_tac Cenv_bs_imp_incsz >>
          qexists_tac`bs with <| code := bce ; refs := rf1 |>` >>
          simp[bc_state_component_equality] >>
          match_mp_tac Cenv_bs_change_store >>
          map_every qexists_tac[`rd`,`s`,`bs with code := bce`] >>
          simp[bc_state_component_equality] >>
          fs[Cenv_bs_def,s_refs_def,good_rd_def,Abbr`bs1`] ) >>
        fs[Abbr`rd'`] >>
        reverse conj_tac >- metis_tac[SUBMAP_TRANS] >>
        match_mp_tac SUBMAP_TRANS >>
        qexists_tac`DRESTRICT bs1.refs (COMPL (set rd.sm))` >>
        simp[] >>
        simp[SUBMAP_DEF,DRESTRICT_DEF] >>
        rw[] >- (
          simp[Abbr`bs1`] >>
          match_mp_tac EQ_SYM >>
          match_mp_tac FUPDATE_LIST_APPLY_NOT_MEM >>
          simp[MAP_ZIP] >>
          fs[Cenv_bs_def,s_refs_def,good_rd_def,FEVERY_DEF,UNCURRY] >>
          metis_tac[] ) >>
        pop_assum mp_tac >>
        simp[Abbr`bs1`,FDOM_FUPDATE_LIST] ) >>
      pop_assum mp_tac >>
      pop_assum kall_tac >>
      Q.PAT_ABBREV_TAC`cenv1 = ls ++ cenv` >>
      strip_tac >>
      rpt gen_tac >>
      pop_assum(mp_tac o Q.SPECL[`lz + LENGTH (defs:def list)`,`az`] o CONV_RULE (RESORT_FORALL_CONV List.rev)) >>
      qspecl_then[`cenv1`,`TCTail az (lz + LENGTH defs)`,`sz + LENGTH defs`,`ccs`,`exp`](Q.X_CHOOSE_THEN`ce`strip_assume_tac)(CONJUNCT1 compile_append_out) >>
      disch_then(qspec_then`REVERSE ce`mp_tac o CONV_RULE SWAP_FORALL_CONV) >>
      qspecl_then[`cenv`,`TCTail az lz`,`sz`,`exp`,`0`,`ccs`,`LENGTH defs`](Q.X_CHOOSE_THEN`cb`strip_assume_tac)(CONJUNCT1(CONJUNCT2 compile_append_out)) >>
      `bs1.code = bs.code` by rw[Abbr`bs1`] >>
      qspecl_then[`cenv`,`TCTail az lz`,`sz`,`exp`,`0`,`ccs`,`LENGTH defs`]mp_tac compile_bindings_thm >>
      simp[Once SWAP_REVERSE] >>
      qpat_assum`X = ce ++ ccs.out`mp_tac >>
      simp[] >> strip_tac >> strip_tac >>
      strip_tac >> strip_tac >>
      rfs[] >> fs[] >> rw[] >>
      fs[FOLDL_FUPDATE_LIST] >>
      first_x_assum(qspecl_then[`env0`,`vs`]mp_tac) >>
      Q.PAT_ABBREV_TAC`klvs2:Cv list = GENLIST X Y` >>
      qpat_assum`Abbrev(bs1 = X)`mp_tac >>
      Q.PAT_ABBREV_TAC`bvs:bc_value list = (MAP X defs)` >>
      strip_tac >>
      disch_then(qspecl_then[`klvs2++klvs`,`bvs++blvs`]mp_tac) >>
      simp[Abbr`bs1`] >>
      disch_then(qspec_then`args`mp_tac) >>
      simp[] >>
      discharge_hyps >- (
        conj_tac >- simp[Abbr`klvs2`] >>
        conj_tac >- (
          fs[EVERY2_EVERY,EVERY_MEM,FORALL_PROD] >>
          `rd'.sm = rd.sm` by rw[Abbr`rd'`] >>
          rw[] >>
          match_mp_tac (MP_CANON (GEN_ALL (CONJUNCT1 (SPEC_ALL Cv_bv_SUBMAP)))) >> simp[] >>
          qexists_tac`rd` >> simp[] ) >>
        fs[EVERY2_EVERY] >>
        conj_asm1_tac >- simp[Abbr`klvs2`,Abbr`bvs`] >>
        simp[GSYM ZIP_APPEND] >>
        conj_tac >- (
          rator_x_assum`RTC`kall_tac >>
          simp[EVERY_MEM,FORALL_PROD,MEM_ZIP] >>
          srw_tac[DNF_ss][EL_MAP,Abbr`klvs2`,EL_REVERSE,PRE_SUB1] >>
          fs[Abbr`bvs`,EL_MAP] >>
          qabbrev_tac`def = EL n defs` >>
          `MEM def defs` by metis_tac[MEM_EL] >>
          fs[EVERY_MEM] >>
          `code_env_cd bce ((LENGTH klvs + LENGTH vs + LENGTH env0,LENGTH defs,n),(THE(FST def)),(SND def))` by (
            last_x_assum match_mp_tac >>
            simp[free_labs_defs_MAP,MEM_FLAT,MEM_GENLIST] >>
            simp_tac(srw_ss()++DNF_ss)[] >>
            qexists_tac`n` >>
            qunabbrev_tac`def` >> qabbrev_tac`def = EL n defs` >>
            res_tac >>
            PairCases_on`def` >> Cases_on`def0` >> fs[] >>
            PairCases_on`x`>>simp[] ) >>
          res_tac >>
          PairCases_on`def`>>Cases_on`def0`>>fs[]>>PairCases_on`x`>>
          qpat_assum`X ++ A = Y ++ Z`(assume_tac o SYM) >>
          fs[code_env_cd_def,bc_find_loc_def,good_cd_def] >>
          simp[Once Cv_bv_cases,el_check_def] >>
          qpat_assum`X = bind_fv A B C`mp_tac >>
          simp[bind_fv_def] >>
          strip_tac >>
          conj_asm1_tac >- (
            rw[EVERY_FILTER,EVERY_GENLIST] ) >>
          conj_asm1_tac >- (
            rw[] >> fsrw_tac[ARITH_ss][EVERY2_EVERY] >> rfs[] >>
            fsrw_tac[ARITH_ss][] ) >>
          conj_asm1_tac >- (
            qsuff_tac`MEM (Label x0) bce` >- (
              metis_tac[bc_find_loc_aux_append_code,bc_find_loc_aux_NONE,optionTheory.option_CASES,optionTheory.THE_DEF] ) >>
            rw[]) >>
          simp[Once Cv_bv_cases] >>
          conj_tac >- (
            gen_tac >> strip_tac >>
            Q.PAT_ABBREV_TAC`recs:num list = FILTER X Y` >>
            conj_asm1_tac >- (
              rw[] >> fs[EVERY_MEM,MEM_EL,GSYM LEFT_FORALL_IMP_THM] ) >>
            simp[EL_APPEND1,EL_MAP] >>
            map_every qexists_tac[`klvs ++ REVERSE vs ++ env0`,`defs`,`EL i recs`] >>
            simp[FLOOKUP_DEF,Abbr`rd'`,FDOM_FUPDATE_LIST,MEM_MAP,MEM_GENLIST,EXISTS_PROD] >>
            conj_tac >- metis_tac[] >>
            qho_match_abbrev_tac`(fm |++ ls) ' k = X` >>
            qho_match_abbrev_tac`P ((fm |++ ls) ' k)` >>
            ho_match_mp_tac FUPDATE_LIST_ALL_DISTINCT_APPLY_MEM >>
            `MAP FST ls = rs` by (
              simp[LIST_EQ_REWRITE,Abbr`ls`,EL_MAP] ) >>
            simp[] >>
            simp[MEM_EL,Abbr`ls`,Abbr`P`] >>
            qexists_tac`EL i recs` >>
            simp[Abbr`k`] ) >>
          gen_tac >> strip_tac >>
          Q.PAT_ABBREV_TAC`envs:num list = MAP X Y` >>
          `i < LENGTH envs` by rw[Abbr`envs`] >>
          simp[EL_APPEND2,EL_MAP] >>
          conj_asm1_tac >- (
            fs[EVERY_MEM,MEM_EL,GSYM LEFT_FORALL_IMP_THM] ) >>
          rator_x_assum`Cenv_bs`mp_tac >>
          simp[Cenv_bs_def,EVERY2_EVERY,EVERY_MEM] >> strip_tac >>
          `LENGTH blvs = LENGTH klvs` by rw[] >> fsrw_tac[ARITH_ss][] >>
          `LENGTH args = LENGTH vs` by rw[] >> fsrw_tac[ARITH_ss][] >>
          rev_full_simp_tac(srw_ss()++ARITH_ss)[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM] >>
          qpat_assum`∀n. n < LENGTH cenv ⇒ P`(qspec_then`EL i envs`mp_tac) >>
          simp[option_case_NONE_F] >> rw[] >> simp[] >>
          match_mp_tac (GEN_ALL (MP_CANON (CONJUNCT1 (SPEC_ALL Cv_bv_SUBMAP)))) >>
          HINT_EXISTS_TAC >> simp[] >>
          simp[Abbr`rd'`] ) >>
        fs[EVERY_MEM,FORALL_PROD] >> rw[] >>
        match_mp_tac (MP_CANON (GEN_ALL (CONJUNCT1 (SPEC_ALL Cv_bv_SUBMAP)))) >> simp[] >>
        qexists_tac`rd` >> simp[] >>
        simp[Abbr`rd'`] ) >>
      simp[code_for_return_def] >>
      asm_simp_tac(srw_ss()++DNF_ss)[] >>
      map_every qx_gen_tac[`bv1`,`rf1`,`rd1`] >>
      strip_tac >>
      map_every qexists_tac[`bv1`,`rf1`,`rd1`] >>
      conj_tac >- metis_tac[RTC_TRANSITIVE,transitive_def] >>
      fs[] >>
      fs[Abbr`rd'`] >>
      reverse conj_tac >- metis_tac[SUBMAP_TRANS] >>
      qmatch_assum_abbrev_tac`DRESTRICT xx yy ⊑ DRESTRICT rf1 zz` >>
      match_mp_tac SUBMAP_TRANS >>
      qexists_tac`DRESTRICT xx yy` >>
      simp[] >>
      simp[SUBMAP_DEF,DRESTRICT_DEF,Abbr`yy`] >>
      rw[] >- (
        simp[Abbr`xx`] >>
        match_mp_tac EQ_SYM >>
        match_mp_tac FUPDATE_LIST_APPLY_NOT_MEM >>
        simp[MAP_ZIP] >>
        fs[Cenv_bs_def,s_refs_def,good_rd_def,FEVERY_DEF,UNCURRY,Abbr`klvs2`] >>
        simp[MAP_ZIP,TAKE_LENGTH_ID_rwt,Abbr`bvs`] >>
        metis_tac[] ) >>
      fs[Abbr`xx`,FDOM_FUPDATE_LIST]) >>
    qx_gen_tac`v` >> strip_tac >>fs[] >>
    CONV_TAC (RESORT_FORALL_CONV List.rev) >>
    qx_gen_tac`t` >>
    pop_assum kall_tac >>
    cheat
    (*
    pop_assum mp_tac >>
    Q.PAT_ABBREV_TAC`cenv1 = ls ++ cenv` >>
    strip_tac >>
    qspecl_then[`cenv`,`t`,`sz`,`exp`,`0`,`ccs`,`LENGTH defs`]mp_tac compile_bindings_thm >>
    simp[] >>
    Q.PAT_ABBREV_TAC`tt:call_context = call_context_CASE X Y Z` >>
    first_x_assum(mp_tac o Q.SPEC`tt` o CONV_RULE (RESORT_FORALL_CONV List.rev)) >>
    qspecl_then[`cenv1`,`tt`,`sz + LENGTH defs`,`ccs`,`exp`](Q.X_CHOOSE_THEN`ce`strip_assume_tac)(CONJUNCT1 compile_append_out) >>
    disch_then(qspec_then`REVERSE ce`mp_tac o CONV_RULE SWAP_FORALL_CONV) >>
    qspecl_then[`cenv`,`tt`,`sz`,`exp`,`0`,`ccs`,`LENGTH defs`](Q.X_CHOOSE_THEN`cb`strip_assume_tac)(CONJUNCT1(CONJUNCT2 compile_append_out)) >>
    `bs1.code = bs.code` by rw[Abbr`bs1`] >>
    asm_simp_tac std_ss [APPEND_ASSOC,REVERSE_REVERSE] >>
    asm_simp_tac std_ss [GSYM APPEND_ASSOC] >>
    asm_simp_tac std_ss [Once APPEND_11] >>
    asm_simp_tac std_ss [Once APPEND_11] >>
    *)) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    qpat_assum`X = (Y,beh)`(mp_tac o SYM) >>
    simp[] >> strip_tac >>
    PairCases_on`def`>>Cases_on`def0`>>fs[]>>
    PairCases_on`x`>>fs[]>>
    simp[compile_def,pushret_def] >>
    conj_asm1_tac >- (
      simp[code_for_push_def] >>
      Q.PAT_ABBREV_TAC`def = X:def` >>
      Q.ISPECL_THEN[`cenv`,`sz`,`cs`,`[def]`]mp_tac compile_closures_thm >>
      simp[] >> disch_then(Q.X_CHOOSE_THEN`cx`strip_assume_tac) >>
      simp[] >>
      fsrw_tac[DNF_ss][] >> rw[] >>
      first_x_assum(qspecl_then[`bs`,`bc0`,`bc1`,`FDOM rd.cls`]mp_tac) >>
      discharge_hyps >- (
        simp[Abbr`def`] >> fs[] >>
        qpat_assum`bce ++ bcr = X`(assume_tac o SYM) >>fs[]>>
        fs[code_env_cd_def,bc_find_loc_def] >>
        conj_tac >- (
          qmatch_abbrev_tac`IS_SOME X` >>
          Cases_on`X`>>rw[bc_find_loc_def]>>
          fs[markerTheory.Abbrev_def] >>
          imp_res_tac(GSYM bc_find_loc_aux_NONE)>>
          fs[]) >>
        fs[good_cd_def] >>
        `LENGTH cenv = LENGTH env` by fs[Cenv_bs_def,EVERY2_EVERY] >> fs[] >>
        reverse conj_tac >- (
          fs[bind_fv_def,LET_THM,MEM_FILTER,MEM_GENLIST] ) >>
        rator_x_assum`Cenv_bs`mp_tac >>
        simp[Cenv_bs_def,EVERY2_EVERY,EVERY_MEM,FORALL_PROD,MEM_ZIP,GSYM LEFT_FORALL_IMP_THM] >>
        simp[option_case_NONE_F] >>
        fs[EVERY_MEM] >>
        metis_tac[optionTheory.IS_SOME_DEF] ) >>
      disch_then(Q.X_CHOOSE_THEN`rs`strip_assume_tac) >>
      rfs[LENGTH_NIL,FUPDATE_LIST_THM,Abbr`def`] >> rw[] >>
      pop_assum mp_tac >>
      Q.PAT_ABBREV_TAC`bv = Block 3 X` >>
      strip_tac >>
      `∃r. rs = [r]` by (
        Cases_on`rs`>>fs[] >>
        Cases_on`t`>>fs[] ) >> fs[FUPDATE_LIST_THM] >>
      Q.PAT_ABBREV_TAC`def:def = X` >>
      map_every qexists_tac[`bs.refs |+ (r,bv)`,`rd with cls := rd.cls |+ (r,(env,[def],0))`,`bv`] >>
      simp[] >>
      `r ∉ FDOM rd.cls` by (
        fs[Cenv_bs_def,s_refs_def,FEVERY_DEF,good_rd_def,UNCURRY] >>
        metis_tac[] ) >>
      simp[] >>
      `r ∉ set rd.sm` by (
        fs[Cenv_bs_def,s_refs_def,good_rd_def,EVERY_MEM] >>
        metis_tac[] ) >>
      simp[FDOM_DRESTRICT] >>
      conj_asm1_tac >- (
        simp[Once Cv_bv_cases,el_check_def,Abbr`bv`,UNCURRY,FLOOKUP_DEF,Abbr`def`]>>
        `bs.code = bce ++ bcr` by metis_tac[] >>
        qpat_assum`bce ++ bcr = X`kall_tac >>
        qpat_assum`bc_next^* X Y`kall_tac >>
        qpat_assum`bs.code = bc0 ++ X ++ Y`kall_tac >>
        fs[good_cd_def,bc_find_loc_def,code_env_cd_def] >>
        conj_tac >- ( fs[bind_fv_def,LET_THM] ) >>
        conj_tac >- (
          qmatch_abbrev_tac`X = SOME (THE Y)` >>
          qsuff_tac`∃x. (Y = SOME x) ∧ (X = SOME x)`>-rw[] >>
          qsuff_tac`∃x. X = SOME x`>-metis_tac[bc_find_loc_aux_append_code] >>
          Cases_on`X`>>simp[]>>fs[markerTheory.Abbrev_def] >>
          qpat_assum`NONE = X`(assume_tac o SYM) >>
          imp_res_tac bc_find_loc_aux_NONE >>
          fs[]) >>
        simp[Once Cv_bv_cases] >>
        `x2 = []` by fs[bind_fv_def,LET_THM] >> simp[] >>
        gen_tac >> strip_tac >>
        fs[EVERY_MEM,MEM_EL,GSYM LEFT_FORALL_IMP_THM] >>
        fs[Cenv_bs_def,EVERY2_EVERY,EVERY_MEM] >>
        rfs[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM] >>
        qpat_assum`∀n. n < LENGTH cenv ⇒ P`(qspec_then`EL i x3`mp_tac) >>
        simp[option_case_NONE_F,EL_MAP] >> rw[] >>
        simp[] >>
        match_mp_tac (GEN_ALL (MP_CANON (CONJUNCT1 (SPEC_ALL Cv_bv_SUBMAP)))) >>
        HINT_EXISTS_TAC >> simp[]) >>
      match_mp_tac Cenv_bs_change_store >>
      qmatch_assum_abbrev_tac`bc_next^* bs bs1` >>
      map_every qexists_tac[`rd`,`s`,`bs1 with <| code := bce; refs := bs.refs|>`] >>
      simp[bc_state_component_equality,Abbr`bs1`,FDOM_DRESTRICT] >>
      conj_tac >- (
        match_mp_tac Cenv_bs_imp_incsz >>
        qexists_tac`bs with code := bce` >>
        simp[bc_state_component_equality] ) >>
      fs[Cenv_bs_def,s_refs_def,good_rd_def,FEVERY_DEF,EVERY_MEM,UNCURRY] >>
      conj_tac >- (
        qx_gen_tac`x` >>
        Cases_on`x=r`>>simp[] >>
        simp[FAPPLY_FUPDATE_THM] >>
        strip_tac >>
        match_mp_tac (GEN_ALL (MP_CANON (CONJUNCT1 (SPEC_ALL Cv_bv_SUBMAP)))) >>
        res_tac >>
        HINT_EXISTS_TAC >>
        simp[] ) >>
      fs[EVERY2_EVERY,EVERY_MEM,FORALL_PROD] >>
      rfs[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM] >>
      gen_tac >> strip_tac >>
      simp[EL_MAP,FAPPLY_FUPDATE_THM] >>
      rw[] >- metis_tac[MEM_EL] >>
      first_x_assum(qspec_then`n`mp_tac) >>
      simp[EL_MAP] >> strip_tac >>
      match_mp_tac (GEN_ALL (MP_CANON (CONJUNCT1 (SPEC_ALL Cv_bv_SUBMAP)))) >>
      HINT_EXISTS_TAC >>
      simp[] ) >>
    Q.PAT_ABBREV_TAC`def:def=X`>>
    Q.ISPECL_THEN[`cenv`,`sz`,`cs`,`[def]`]mp_tac compile_closures_thm >>
    simp[] >> disch_then strip_assume_tac >>
    pop_assum kall_tac >>
    fs[Once SWAP_REVERSE] >>
    rpt gen_tac >> strip_tac >> fs[] >> rw[] >>
    match_mp_tac code_for_push_return >>
    qmatch_assum_abbrev_tac`code_for_push rd bs bce bc0 code s s ee vv cenv sz` >>
    map_every qexists_tac [`bc0`,`code`,`ee`,`cenv`,`sz`] >>
    simp[] >>
    qexists_tac`REVERSE args`>>fs[EVERY2_EVERY]) >>

  strip_tac >- (
    simp[] >> ntac 5 gen_tac >> qx_gen_tac `fenv` >> rpt gen_tac >> strip_tac >>
    rpt gen_tac >>
    simp[compile_def,FOLDL_UNION_BIGUNION] >>
    simp_tac(srw_ss()++ETA_ss)[] >>
    strip_tac >> rfs[] >> fs[] >>
    BasicProvers.VAR_EQ_TAC >>
    qspecl_then[`cenv`,`TCNonTail`,`sz`,`cs`,`exp`](Q.X_CHOOSE_THEN`cx`strip_assume_tac)(CONJUNCT1 compile_append_out) >> fs[] >>
    simp[GSYM FORALL_AND_THM] >> ntac 2 gen_tac >>
    Q.PAT_ABBREV_TAC`cs0 = compile cenv X sz cs exp` >>
    qspecl_then[`cenv`,`sz+1`,`cs0`,`exps`](Q.X_CHOOSE_THEN`cxs`strip_assume_tac)(CONJUNCT2 (CONJUNCT2 compile_append_out)) >> fs[] >>
    reverse(Cases_on`∃bc10. code = REVERSE cx ++ REVERSE cxs ++ bc10`) >- (
      fsrw_tac[DNF_ss][] >>
      conj_tac >> rpt gen_tac >>
      rw[Once SWAP_REVERSE]) >> fs[] >>
    reverse(Cases_on`bs.code = bc0 ++ REVERSE cx ++ REVERSE cxs ++ bc10 ++ bc1`) >- fs[] >>
    fs[Once SWAP_REVERSE] >>
    last_x_assum(qspecl_then[`rd`,`cs`,`cenv`,`sz`,`bs`,`bce`,`bcr`,`bc0`]mp_tac) >>
    `LENGTH s ≤ LENGTH s' ∧ LENGTH s' ≤ LENGTH s'' ∧ LENGTH s'' ≤ LENGTH s'''` by PROVE_TAC[Cevaluate_store_SUBSET,FST] >>
    discharge_hyps >- (
      fsrw_tac[DNF_ss][ALL_DISTINCT_APPEND] >> PROVE_TAC[] ) >>
    fs[ALL_DISTINCT_APPEND] >>
    fs[Once SWAP_REVERSE] >>
    disch_then(mp_tac o SIMP_RULE(srw_ss()++DNF_ss)[code_for_push_def,LET_THM] o CONJUNCT1) >>
    disch_then(qx_choosel_then[`rf`,`rd'`,`bf`]strip_assume_tac) >>
    qmatch_assum_abbrev_tac`bc_next^* bs bs1` >>
    first_x_assum(qspecl_then[`rd'`,`cs0`,`cenv`,`sz+1`,`bs1`,`bce`,`bcr`,`bc0 ++ REVERSE cx`,`REVERSE cxs`]mp_tac) >>
    simp[Abbr`bs1`] >>
    discharge_hyps >- (
      simp[Abbr`cs0`] >>
      conj_tac >- PROVE_TAC[SUBSET_DEF,IN_COUNT,LESS_LESS_EQ_TRANS] >>
      conj_tac >- metis_tac[Cevaluate_Clocs,FST] >>
      fsrw_tac[DNF_ss][] >>
      qspecl_then[`s`,`env`,`exp`,`s',Cval(CRecClos fenv defs n)`]mp_tac(CONJUNCT1 Cevaluate_all_vlabs) >>
      simp[] >> strip_tac >>
      qspecl_then[`s`,`env`,`exp`,`s',Cval(CRecClos fenv defs n)`]mp_tac(CONJUNCT1 Cevaluate_vlabs) >>
      simp[] >> strip_tac >>
      conj_tac >- (  fsrw_tac[DNF_ss][SUBSET_DEF,EVERY_MEM] >> metis_tac[] ) >>
      match_mp_tac compile_labels_lemma >>
      map_every qexists_tac [`cenv`,`TCNonTail`,`sz`,`cs`,`exp`,`bc0`,`REVERSE cx`] >>
      rw[] ) >>
    disch_then(mp_tac o SIMP_RULE(srw_ss()++DNF_ss)[code_for_push_def,LET_THM]) >>
    disch_then(qx_choosel_then[`bvs`,`rfs`,`rd''`]strip_assume_tac) >>
    conj_tac >- (
      srw_tac[DNF_ss][code_for_push_def,LET_THM] >>
      qmatch_assum_abbrev_tac`Cv_bv (ps',l2a) cl bf` >>
      `Cv_bv (rd'', l2a) cl bf` by (
        match_mp_tac (MP_CANON (GEN_ALL (CONJUNCT1 (SPEC_ALL Cv_bv_SUBMAP)))) >> simp[] >>
        qexists_tac`rd'` >>
        rw[] >>
        fs[Cenv_bs_def,s_refs_def,good_rd_def,FEVERY_DEF,UNCURRY,SUBMAP_DEF,SUBSET_DEF]) >>
      pop_assum mp_tac >>
      simp[Abbr`cl`,Once Cv_bv_cases] >>
      disch_then(qx_choosel_then[`a`,`bve`,`cd`,`l`]strip_assume_tac) >>
      qho_match_abbrev_tac`∃rf sm bv. bc_next^* bs (bs2 rf bv) ∧ P rf sm bv` >>
      qmatch_assum_abbrev_tac`bc_next^* bs0 bs3` >>
      qmatch_assum_abbrev_tac`bc_next^* bs0 bs3` >>
      qsuff_tac `∃rf sm bv. bc_next^* bs3 (bs2 rf bv) ∧ P rf sm bv` >-
        metis_tac[RTC_TRANSITIVE,transitive_def] >>
      `bc_fetch bs3 = SOME (Stack (Load (LENGTH exps)))` by (
        match_mp_tac bc_fetch_next_addr >>
        rw[Abbr`bs3`,REVERSE_APPEND] >>
        qexists_tac`bc0 ++ REVERSE cx ++ REVERSE cxs` >>
        rw[] ) >>
      simp_tac(srw_ss()++DNF_ss)[Once RTC_CASES1] >> disj2_tac >>
      rw[bc_eval1_thm,bc_eval1_def,bc_eval_stack_def] >>
      `LENGTH exps = LENGTH bvs` by (fs[EVERY2_EVERY] >> metis_tac[Cevaluate_list_LENGTH] ) >>
      simp[Abbr`bs3`] >>
      lrw[EL_APPEND2] >>
      simp[bump_pc_with_stack] >> fs[bc_fetch_with_stack] >>
      simp[bump_pc_def] >>
      qpat_assum`bc_fetch X = Y` kall_tac >>
      qho_match_abbrev_tac`∃rf sm bv. bc_next^* bs1 (bs2 rf bv) ∧ P rf sm bv` >>
      `bc_fetch bs1 = SOME (Stack (El 1))` by (
        match_mp_tac bc_fetch_next_addr >>
        rw[Abbr`bs1`] >>
        Q.PAT_ABBREV_TAC`ls = bc0 ++ X ++ Y` >>
        qexists_tac`ls ++ [Stack (Load (LENGTH bvs))]` >>
        rw[Abbr`ls`,REVERSE_APPEND,FILTER_APPEND,SUM_APPEND,ADD1] ) >>
      simp_tac(srw_ss()++DNF_ss)[Once RTC_CASES1] >> disj2_tac >>
      rw[bc_eval1_thm,bc_eval1_def] >>
      simp[Abbr`bs1`,bc_eval_stack_def] >>
      fs[bump_pc_with_stack,bc_fetch_with_stack] >>
      simp[bump_pc_def] >>
      qpat_assum`bc_fetch X = Y` kall_tac >>
      qho_match_abbrev_tac`∃rf sm bv. bc_next^* bs1 (bs2 rf bv) ∧ P rf sm bv` >>
      `bc_fetch bs1 = SOME (Stack (Load (SUC(LENGTH bvs))))` by (
        match_mp_tac bc_fetch_next_addr >>
        rw[Abbr`bs1`] >>
        Q.PAT_ABBREV_TAC`ls = bc0 ++ X ++ Y` >>
        Q.PAT_ABBREV_TAC`l2:bc_inst list = X::Y` >>
        qexists_tac`ls ++ TAKE 2 l2` >>
        srw_tac[ARITH_ss][Abbr`ls`,Abbr`l2`,REVERSE_APPEND,FILTER_APPEND,SUM_APPEND,ADD1] ) >>
      simp_tac(srw_ss()++DNF_ss)[Once RTC_CASES1] >> disj2_tac >>
      rw[bc_eval1_thm,bc_eval1_def] >>
      simp[Abbr`bs1`,bc_eval_stack_def] >>
      lrw[EL_APPEND2,EL_APPEND1] >>
      fs[bc_fetch_with_stack,bump_pc_with_stack] >>
      rw[bump_pc_def] >>
      qpat_assum`bc_fetch X = Y` kall_tac >>
      qho_match_abbrev_tac`∃rf sm bv. bc_next^* bs1 (bs2 rf bv) ∧ P rf sm bv` >>
      `bc_fetch bs1 = SOME (Stack (El 0))` by (
        match_mp_tac bc_fetch_next_addr >>
        rw[Abbr`bs1`] >>
        Q.PAT_ABBREV_TAC`ls = bc0 ++ X ++ Y` >>
        Q.PAT_ABBREV_TAC`l2:bc_inst list = X::Y` >>
        qexists_tac`ls ++ TAKE 3 l2` >>
        srw_tac[ARITH_ss][Abbr`ls`,Abbr`l2`,REVERSE_APPEND,FILTER_APPEND,SUM_APPEND,ADD1] ) >>
      simp_tac(srw_ss()++DNF_ss)[Once RTC_CASES1] >> disj2_tac >>
      rw[bc_eval1_thm,bc_eval1_def] >>
      simp[Abbr`bs1`,bc_eval_stack_def] >>
      fs[bc_fetch_with_stack,bump_pc_with_stack] >>
      fsrw_tac[ARITH_ss][] >>
      rw[bump_pc_def] >>
      qho_match_abbrev_tac`∃rf sm bv. bc_next^* bs1 (bs2 rf bv) ∧ P rf sm bv` >>
      `bc_fetch bs1 = SOME CallPtr` by (
        match_mp_tac bc_fetch_next_addr >>
        rw[Abbr`bs1`] >>
        Q.PAT_ABBREV_TAC`ls = bc0 ++ X ++ Y` >>
        Q.PAT_ABBREV_TAC`l2:bc_inst list = X::Y` >>
        qexists_tac`ls ++ TAKE 4 l2` >>
        srw_tac[ARITH_ss][Abbr`ls`,Abbr`l2`,REVERSE_APPEND,FILTER_APPEND,SUM_APPEND,ADD1] ) >>
      simp_tac(srw_ss()++DNF_ss)[Once RTC_CASES1] >> disj2_tac >>
      rw[bc_eval1_thm,bc_eval1_def] >>
      simp[Abbr`bs1`] >>
      fs[bc_fetch_with_stack,bump_pc_with_stack] >>
      fsrw_tac[ARITH_ss][] >>
      rw[bump_pc_def] >>
      qpat_assum`bc_fetch X = Y` kall_tac >>
      qpat_assum`bc_fetch X = Y` kall_tac >>
      Q.PAT_ABBREV_TAC`ret = x + 1` >>
      qho_match_abbrev_tac`∃rf sm bv. bc_next^* bs1 (bs2 rf bv) ∧ P rf sm bv` >>
      fs[el_check_def] >>
      qmatch_assum_rename_tac`EL n defs = (SOME (z,ccenv,recs,envs),bve)`[]>>
      qmatch_assum_rename_tac`EL n defs = (SOME (l,ccenv,recs,envs),bve)`[]>>
      qmatch_assum_abbrev_tac`EL n defs = (SOME cc,bve)`>>
      `code_env_cd bce ((LENGTH fenv,LENGTH defs,n),cc,bve)` by (
        qspecl_then[`s`,`env`,`exp`,`s',Cval(CRecClos fenv defs n)`]mp_tac(CONJUNCT1 Cevaluate_vlabs) >>
        simp[] >> strip_tac >>
        fsrw_tac[DNF_ss][SUBSET_DEF,MEM_FLAT,MEM_MAP] >>
        pop_assum(qspec_then`(LENGTH fenv,LENGTH defs,n),cc,bve`mp_tac) >>
        discharge_hyps >- (
          PairCases_on`bve`>>
          simp[Abbr`cc`,free_labs_defs_MAP,MEM_FLAT,MEM_GENLIST] >>
          simp_tac(srw_ss()++DNF_ss)[] >>
          qexists_tac`n` >> simp[]) >>
        fs[EVERY_MEM] >>
        metis_tac[] ) >>
      pop_assum mp_tac >>
      qunabbrev_tac`cc` >>
      PairCases_on`bve` >>
      simp[code_env_cd_def] >>
      simp[GSYM AND_IMP_INTRO] >> strip_tac >>
      disch_then(qx_choosel_then[`csc`,`cb0`,`cc`,`cb1`] strip_assume_tac) >>
      pop_assum (assume_tac o SYM) >>
      first_x_assum (qspecl_then[`rd''`,`csc`,`MAP CTEnv ccenv`,`0`,`bs1`,`bce`,`bcr`,`cb0 ++ [Label l]`]mp_tac) >>
      simp[] >>
      discharge_hyps >- (
        fs[good_cd_def] >>
        conj_tac >- (
          qspecl_then[`s`,`env`,`exp`,`(s',Cval (CRecClos fenv defs n))`]mp_tac (CONJUNCT1 Cevaluate_Clocs) >>
          qspecl_then[`s'`,`env`,`exps`,`(s'',Cval vs)`]mp_tac (CONJUNCT2 Cevaluate_Clocs) >>
          simp[] >>
          rpt (qpat_assum `X ⊆ count (LENGTH s)`mp_tac) >>
          rpt(qpat_assum `LENGTH X ≤ LENGTH Y` mp_tac) >>
          qpat_assum `LENGTH fenv = X`mp_tac >>
          qpat_assum `EVERY Z envs` mp_tac >>
          rpt (pop_assum kall_tac) >>
          ntac 9 strip_tac  >>
          fsrw_tac[DNF_ss][SUBSET_DEF,MEM_MAP,EVERY_MEM] >>
          metis_tac[LESS_LESS_EQ_TRANS,MEM_EL] ) >>
        conj_tac >- (
          qspecl_then[`s`,`env`,`exp`,`(s',Cval (CRecClos fenv defs n))`]mp_tac (CONJUNCT1 Cevaluate_Clocs) >>
          qspecl_then[`s'`,`env`,`exps`,`(s'',Cval vs)`]mp_tac (CONJUNCT2 Cevaluate_Clocs) >>
          simp[] >> strip_tac >> strip_tac >>
          fsrw_tac[DNF_ss][] >>
          first_x_assum match_mp_tac >>
          metis_tac[SUBSET_DEF,IN_COUNT,LESS_LESS_EQ_TRANS] ) >>
        conj_tac >- simp[Abbr`bs1`] >>
        conj_tac >- (
          qspecl_then[`s'`,`env`,`exps`,`s'',Cval vs`]mp_tac(CONJUNCT2 Cevaluate_all_vlabs) >>
          qspecl_then[`s`,`env`,`exp`,`s',Cval (CRecClos fenv defs n)`]mp_tac(CONJUNCT1 Cevaluate_all_vlabs) >>
          simp[] ) >>
        conj_tac >- (
          simp[EVERY_REVERSE,EVERY_MAP] >>
          qspecl_then[`s`,`env`,`exp`,`s',Cval (CRecClos fenv defs n)`]mp_tac(CONJUNCT1 Cevaluate_all_vlabs) >>
          qspecl_then[`s'`,`env`,`exps`,`s'',Cval vs`]mp_tac(CONJUNCT2 Cevaluate_all_vlabs) >>
          simp[] >> fs[EVERY_MEM] >> metis_tac[MEM_EL] ) >>
        conj_tac >- (
          qspecl_then[`s`,`env`,`exp`,`s',Cval (CRecClos fenv defs n)`]mp_tac(CONJUNCT1 Cevaluate_all_vlabs) >>
          simp[] >> simp[EVERY_MEM] >> strip_tac >>
          `all_labs_def (EL n defs)` by metis_tac[MEM_EL] >>
          pop_assum mp_tac >> simp[] ) >>
        conj_tac >- (
          qspecl_then[`s`,`env`,`exp`,`s',Cval (CRecClos fenv defs n)`]mp_tac(CONJUNCT1 Cevaluate_vlabs) >>
          simp[] >> strip_tac >>
          qmatch_assum_abbrev_tac`set X ⊆ Y` >>
          simp[EVERY_MEM] >>
          qx_gen_tac`z` >> strip_tac >>
          qsuff_tac`z ∈ Y`>-metis_tac[IN_UNION,EVERY_MEM]>>
          qsuff_tac`MEM z X`>-metis_tac[SUBSET_DEF] >>
          simp[Abbr`X`,free_labs_defs_MAP,MEM_FLAT,MEM_GENLIST] >>
          simp_tac(srw_ss()++DNF_ss)[] >>
          qexists_tac`n` >> simp[] ) >>
        conj_tac >- (
          qspecl_then[`s`,`env`,`exp`,`s',Cval (CRecClos fenv defs n)`]mp_tac(CONJUNCT1 Cevaluate_vlabs) >>
          qspecl_then[`s'`,`env`,`exps`,`s'',Cval vs`]mp_tac(CONJUNCT2 Cevaluate_vlabs) >>
          simp[] >>
          fsrw_tac[DNF_ss][SUBSET_DEF,EVERY_MEM] >>
          metis_tac[] ) >>
        conj_tac >- (
          qspecl_then[`s`,`env`,`exp`,`s',Cval (CRecClos fenv defs n)`]mp_tac(CONJUNCT1 Cevaluate_vlabs) >>
          simp[] >> strip_tac >>
          simp[vlabs_list_MAP] >>
          fsrw_tac[DNF_ss][SUBSET_DEF,EVERY_MEM,MEM_MAP] >>
          fsrw_tac[DNF_ss][vlabs_list_MAP,MEM_MAP] >>
          reverse conj_tac >- metis_tac[MEM_EL] >>
          reverse conj_tac >- metis_tac[MEM_EL] >>
          reverse conj_tac >- metis_tac[MEM_EL] >>
          qspecl_then[`s'`,`env`,`exps`,`s'',Cval vs`]mp_tac(CONJUNCT2 Cevaluate_vlabs) >>
          simp[] >>
          fsrw_tac[DNF_ss][vlabs_list_MAP,MEM_MAP,SUBSET_DEF] >>
          metis_tac[MEM_EL] ) >>
        conj_asm1_tac >- (
          fs[Abbr`bs1`,Abbr`l2a`] >>
          qspecl_then[`bce`,`bs.inst_length`,`l`,`0`]mp_tac bc_find_loc_aux_ALL_DISTINCT >>
          simp[] >>
          disch_then(qspec_then`LENGTH cb0`mp_tac) >>
          srw_tac[ARITH_ss][] >>
          pop_assum mp_tac >>
          REWRITE_TAC[GSYM APPEND_ASSOC] >>
          rw[EL_LENGTH_APPEND,TAKE_LENGTH_APPEND] >>
          simp[FILTER_APPEND] ) >>
        conj_tac >- (
          match_mp_tac Cenv_bs_bind_fv >>
          qexists_tac`ccenv`>>simp[]>>
          simp[Abbr`bs1`]>>
          map_every qexists_tac[`bvs`,`a`,`bs.stack`] >> simp[] >>
          map_every qexists_tac[`fenv`,`defs`,`n`] >> simp[] >>
          qpat_assum`X = bind_fv A Z Y`(assume_tac o SYM) >>
          qexists_tac`e`>>simp[]>>
          fs[s_refs_def,Cenv_bs_def,good_rd_def] >>
          qspecl_then[`bce`,`bs.inst_length`,`l`,`0`]mp_tac bc_find_loc_aux_ALL_DISTINCT >>
          simp[] >>
          disch_then(qspec_then`LENGTH cb0`mp_tac) >>
          srw_tac[ARITH_ss][] >>
          pop_assum mp_tac >>
          REWRITE_TAC[GSYM APPEND_ASSOC] >>
          rw[EL_LENGTH_APPEND,TAKE_LENGTH_APPEND] >>
          simp[FILTER_APPEND] ) >>
        qpat_assum`X = bce`(assume_tac o SYM) >>
        fs[ALL_DISTINCT_APPEND,FILTER_APPEND] ) >>
      disch_then(qspecl_then[`0`,`bve0`]mp_tac o CONV_RULE (RESORT_FORALL_CONV List.rev) o CONJUNCT2) >>
      fs[] >> simp[] >> simp[Once SWAP_REVERSE] >>
      simp_tac (srw_ss()++DNF_ss) [] >>
      disch_then(mp_tac o CONV_RULE (RESORT_FORALL_CONV List.rev)) >>
      simp[LENGTH_NIL_SYM,FUPDATE_LIST_THM] >>
      simp_tac(srw_ss())[Abbr`bs1`]>>
      disch_then(qspecl_then[`bs.stack`,`Block 3 [CodePtr a; Block 0 cd]`,`bvs`,`vs`]mp_tac) >>
      `∃bc10. bs.code = cb0 ++ [Label l] ++ REVERSE cc ++ bc10` by (
        qpat_assum`bce ++ bcr = X`(assume_tac o SYM) >>
        qpat_assum`X = bce`(assume_tac o SYM) >>
        rw[] ) >> pop_assum SUBST1_TAC >> fs[] >>
      `LENGTH bvs = LENGTH vs` by fs[EVERY2_EVERY] >>
      simp[] >>
      simp[code_for_return_def] >>
      disch_then(qx_choosel_then[`bvr`,`rfr`,`smr`]strip_assume_tac) >>
      map_every qexists_tac [`rfr`,`smr`,`bvr`] >>
      simp[Abbr`bs2`] >>
      Q.PAT_ABBREV_TAC`ret' = next_addr X Y` >>
      `ret' = ret` by (
        map_every qunabbrev_tac[`ret`,`ret'`] >>
        srw_tac[ARITH_ss][FILTER_APPEND,SUM_APPEND,ADD1] ) >>
      rw[] >>
      simp[Abbr`P`] >>
      reverse conj_tac >- PROVE_TAC[SUBMAP_TRANS,IS_PREFIX_TRANS] >>
      match_mp_tac Cenv_bs_imp_incsz >>
      qunabbrev_tac`bs0` >>
      qmatch_assum_abbrev_tac`Cenv_bs rd s renv cenv sz bs0` >>
      qexists_tac`bs0 with refs := rfr` >>
      simp[Abbr`bs0`,bc_state_component_equality] >>
      match_mp_tac Cenv_bs_change_store >>
      qmatch_assum_abbrev_tac`Cenv_bs rd s renv cenv sz bs0` >>
      map_every qexists_tac[`rd`,`s`,`bs0`] >>
      simp[] >>
      fs[s_refs_def,Abbr`l2a`,good_rd_def] >>
      simp[Abbr`bs0`,bc_state_component_equality] >>
      conj_tac >- metis_tac[SUBMAP_TRANS] >>
      conj_tac >- metis_tac[IS_PREFIX_TRANS] >>
      fs[Cenv_bs_def,s_refs_def,good_rd_def] >>
      metis_tac[SUBMAP_TRANS]) >>
    asm_simp_tac(srw_ss()++DNF_ss)[] >>
    map_every qx_gen_tac[`env0`,`vs0`,`klvs`,`blvs`,`benv`,`ret`,`args0`,`cl0`,`st`] >>
    simp[Once SWAP_REVERSE] >> strip_tac >>
    qmatch_assum_abbrev_tac`Cv_bv (ps',l2a) cl bf` >>
    `Cv_bv (rd'', l2a) cl bf` by (
      match_mp_tac (MP_CANON (GEN_ALL (CONJUNCT1 (SPEC_ALL Cv_bv_SUBMAP)))) >> simp[] >>
      qexists_tac`rd'` >>
      rw[Abbr`ps'`] >>
      fs[Cenv_bs_def,s_refs_def,good_rd_def,FEVERY_DEF,UNCURRY,SUBMAP_DEF,SUBSET_DEF]) >>
    pop_assum mp_tac >>
    simp[Abbr`cl`,Once Cv_bv_cases] >>
    disch_then(qx_choosel_then[`a`,`bve`,`cd`,`l`]strip_assume_tac) >>
    strip_tac >>
    simp[code_for_return_def] >>
    qho_match_abbrev_tac`∃bv rf sm. bc_next^* bs (bs2 rf bv) ∧ P rf bv sm` >>
    qmatch_assum_abbrev_tac`bc_next^* bs bs05` >>
    qmatch_assum_abbrev_tac`bc_next^* bs05 bs3` >>
    qsuff_tac `∃rf bv sm. bc_next^* bs3 (bs2 rf bv) ∧ P rf bv sm` >-
      metis_tac[RTC_TRANSITIVE,transitive_def] >>
    qspec_then`bs3`mp_tac jmpbc_thm >>
    simp[Abbr`bs3`] >>
    disch_then(qspecl_then[`st`,`REVERSE bvs`]mp_tac o (CONV_RULE(RESORT_FORALL_CONV List.rev))) >> simp[] >>
    disch_then(qspec_then`REVERSE args0`mp_tac) >> simp[] >>
    disch_then(qspec_then`bc1`mp_tac) >> simp[] >>
    `(LENGTH exps = LENGTH bvs) ∧ (LENGTH klvs = LENGTH blvs)` by (
      fs[EVERY2_EVERY] >> imp_res_tac Cevaluate_list_LENGTH >> fs[] ) >>
    simp[] >>
    qmatch_abbrev_tac`bc_next^* bs1 bs3 ⇒ X` >> strip_tac >>
    qsuff_tac `∃rf bv sm. bc_next^* bs3 (bs2 rf bv) ∧ P rf bv sm` >- metis_tac[RTC_TRANSITIVE,transitive_def] >>
    map_every qunabbrev_tac[`X`,`bs3`,`bs1`] >>
    pop_assum kall_tac >>
    qho_match_abbrev_tac `∃rf bv sm. bc_next^* bs1 (bs2 rf bv) ∧ P rf bv sm` >>
    fs[el_check_def] >>
    qmatch_assum_rename_tac`EL n defs = (SOME (z,ccenv,recs,envs),bve)`[]>>
    qmatch_assum_rename_tac`EL n defs = (SOME (l,ccenv,recs,envs),bve)`[]>>
    qmatch_assum_abbrev_tac`EL n defs = (SOME cc,bve)`>>
    `code_env_cd bce ((LENGTH fenv,LENGTH defs,n),cc,bve)` by (
      qspecl_then[`s`,`env`,`exp`,`s',Cval(CRecClos fenv defs n)`]mp_tac(CONJUNCT1 Cevaluate_vlabs) >>
      simp[] >> strip_tac >>
      fsrw_tac[DNF_ss][SUBSET_DEF,MEM_FLAT,MEM_MAP] >>
      pop_assum(qspec_then`(LENGTH fenv,LENGTH defs,n),cc,bve`mp_tac) >>
      discharge_hyps >- (
        PairCases_on`bve`>>
        simp[Abbr`cc`,free_labs_defs_MAP,MEM_FLAT,MEM_GENLIST] >>
        simp_tac(srw_ss()++DNF_ss)[] >>
        qexists_tac`n` >> simp[]) >>
      fs[EVERY_MEM] >>
      metis_tac[ADD_SYM,ADD_ASSOC] ) >>
    pop_assum mp_tac >>
    qunabbrev_tac`cc` >>
    PairCases_on`bve` >>
    simp[code_env_cd_def] >>
    simp[GSYM AND_IMP_INTRO] >> strip_tac >>
    disch_then(qx_choosel_then[`csc`,`cb0`,`cc`,`cb1`] strip_assume_tac) >>
    pop_assum (assume_tac o SYM) >>
    first_x_assum (qspecl_then[`rd''`,`csc`,`MAP CTEnv ccenv`,`0`,`bs1`,`bce`,`bcr`,`cb0 ++ [Label l]`]mp_tac) >>
    simp[] >>
    discharge_hyps >- (
      fs[good_cd_def] >>
      conj_tac >- (
        qspecl_then[`s`,`env`,`exp`,`(s',Cval (CRecClos fenv defs n))`]mp_tac (CONJUNCT1 Cevaluate_Clocs) >>
        qspecl_then[`s'`,`env`,`exps`,`(s'',Cval vs)`]mp_tac (CONJUNCT2 Cevaluate_Clocs) >>
        simp[] >>
        rpt (qpat_assum `X ⊆ count (LENGTH s)`mp_tac) >>
        rpt(qpat_assum `LENGTH X ≤ LENGTH Y` mp_tac) >>
        fsrw_tac[DNF_ss][SUBSET_DEF,MEM_MAP,EVERY_MEM] >>
        metis_tac[LESS_LESS_EQ_TRANS,MEM_EL] ) >>
      conj_tac >- (
        qspecl_then[`s`,`env`,`exp`,`(s',Cval (CRecClos fenv defs n))`]mp_tac (CONJUNCT1 Cevaluate_Clocs) >>
        qspecl_then[`s'`,`env`,`exps`,`(s'',Cval vs)`]mp_tac (CONJUNCT2 Cevaluate_Clocs) >>
        simp[] >> strip_tac >> strip_tac >>
        fsrw_tac[DNF_ss][] >>
        first_x_assum match_mp_tac >>
        metis_tac[SUBSET_DEF,IN_COUNT,LESS_LESS_EQ_TRANS] ) >>
      conj_tac >- simp[Abbr`bs1`] >>
      conj_tac >- (
        qspecl_then[`s'`,`env`,`exps`,`s'',Cval vs`]mp_tac(CONJUNCT2 Cevaluate_all_vlabs) >>
        qspecl_then[`s`,`env`,`exp`,`s',Cval (CRecClos fenv defs n)`]mp_tac(CONJUNCT1 Cevaluate_all_vlabs) >>
        simp[] ) >>
      conj_tac >- (
        simp[EVERY_REVERSE,EVERY_MAP] >>
        qspecl_then[`s`,`env`,`exp`,`s',Cval (CRecClos fenv defs n)`]mp_tac(CONJUNCT1 Cevaluate_all_vlabs) >>
        qspecl_then[`s'`,`env`,`exps`,`s'',Cval vs`]mp_tac(CONJUNCT2 Cevaluate_all_vlabs) >>
        simp[] >> fs[EVERY_MEM] >> metis_tac[MEM_EL] ) >>
      conj_tac >- (
        qspecl_then[`s`,`env`,`exp`,`s',Cval (CRecClos fenv defs n)`]mp_tac(CONJUNCT1 Cevaluate_all_vlabs) >>
        simp[] >> simp[EVERY_MEM] >> strip_tac >>
        `all_labs_def (EL n defs)` by metis_tac[MEM_EL] >>
        pop_assum mp_tac >> simp[] ) >>
      conj_tac >- (
        qspecl_then[`s`,`env`,`exp`,`s',Cval (CRecClos fenv defs n)`]mp_tac(CONJUNCT1 Cevaluate_vlabs) >>
        simp[] >> strip_tac >>
        qmatch_assum_abbrev_tac`set X ⊆ Y` >>
        simp[EVERY_MEM] >>
        qx_gen_tac`z` >> strip_tac >>
        `LENGTH env0 + (LENGTH vs0 + LENGTH blvs) = LENGTH blvs + LENGTH vs0 + LENGTH env0` by simp[] >>
        qsuff_tac`z ∈ Y`>-metis_tac[IN_UNION,EVERY_MEM]>>
        qsuff_tac`MEM z X`>-metis_tac[SUBSET_DEF] >>
        simp[Abbr`X`,free_labs_defs_MAP,MEM_FLAT,MEM_GENLIST] >>
        simp_tac(srw_ss()++DNF_ss)[] >>
        qexists_tac`n` >> simp[] ) >>
      conj_tac >- (
        qspecl_then[`s`,`env`,`exp`,`s',Cval (CRecClos fenv defs n)`]mp_tac(CONJUNCT1 Cevaluate_vlabs) >>
        qspecl_then[`s'`,`env`,`exps`,`s'',Cval vs`]mp_tac(CONJUNCT2 Cevaluate_vlabs) >>
        simp[] >>
        fsrw_tac[DNF_ss,ARITH_ss][SUBSET_DEF,EVERY_MEM] >>
        metis_tac[] ) >>
      conj_tac >- (
        qspecl_then[`s`,`env`,`exp`,`s',Cval (CRecClos fenv defs n)`]mp_tac(CONJUNCT1 Cevaluate_vlabs) >>
        simp[] >> strip_tac >>
        simp[vlabs_list_MAP] >>
        fsrw_tac[ARITH_ss,DNF_ss][SUBSET_DEF,EVERY_MEM,MEM_MAP] >>
        fsrw_tac[DNF_ss][vlabs_list_MAP,MEM_MAP] >>
        reverse conj_tac >- metis_tac[MEM_EL] >>
        reverse conj_tac >- metis_tac[MEM_EL] >>
        reverse conj_tac >- metis_tac[MEM_EL] >>
        qspecl_then[`s'`,`env`,`exps`,`s'',Cval vs`]mp_tac(CONJUNCT2 Cevaluate_vlabs) >>
        simp[] >>
        fsrw_tac[DNF_ss][vlabs_list_MAP,MEM_MAP,SUBSET_DEF] >>
        metis_tac[MEM_EL] ) >>
      conj_asm1_tac >- (
        fs[Abbr`bs1`,Abbr`l2a`] >>
        qspecl_then[`bce`,`bs.inst_length`,`l`,`0`]mp_tac bc_find_loc_aux_ALL_DISTINCT >>
        simp[] >>
        disch_then(qspec_then`LENGTH cb0`mp_tac) >>
        srw_tac[ARITH_ss][] >>
        pop_assum mp_tac >>
        REWRITE_TAC[GSYM APPEND_ASSOC] >>
        rw[EL_LENGTH_APPEND,TAKE_LENGTH_APPEND] >>
        simp[FILTER_APPEND] ) >>
      conj_tac >- (
        match_mp_tac Cenv_bs_bind_fv >>
        qexists_tac`ccenv`>>simp[]>>
        simp[Abbr`bs1`]>>
        map_every qexists_tac[`bvs`,`a`,`st`] >> simp[] >>
        map_every qexists_tac[`fenv`,`defs`,`n`] >> simp[] >>
        qpat_assum`X = bind_fv A Z Y`(assume_tac o SYM) >>
        qexists_tac`e`>>simp[]>>
        fs[s_refs_def,Cenv_bs_def,good_rd_def] >>
        qspecl_then[`bce`,`bs.inst_length`,`l`,`0`]mp_tac bc_find_loc_aux_ALL_DISTINCT >>
        simp[] >>
        disch_then(qspec_then`LENGTH cb0`mp_tac) >>
        srw_tac[ARITH_ss][] >>
        pop_assum mp_tac >>
        REWRITE_TAC[GSYM APPEND_ASSOC] >>
        rw[EL_LENGTH_APPEND,TAKE_LENGTH_APPEND] >>
        simp[FILTER_APPEND] ) >>
      qpat_assum`X = bce`(assume_tac o SYM) >>
      fs[ALL_DISTINCT_APPEND,FILTER_APPEND] ) >>
    fs[] >>
    disch_then(qspecl_then[`0`,`bve0`]mp_tac o (CONV_RULE(RESORT_FORALL_CONV List.rev)) o CONJUNCT2) >>
    simp[Once SWAP_REVERSE] >>
    simp_tac (srw_ss()++DNF_ss) [] >>
    simp[Abbr`bs1`] >>
    disch_then(mp_tac o CONV_RULE (RESORT_FORALL_CONV List.rev)) >>
    simp[LENGTH_NIL_SYM,FUPDATE_LIST_THM] >>
    disch_then(qspecl_then[`st`,`Block 3 [CodePtr a; Block 0 cd]`,`bvs`,`vs`]mp_tac) >>
    qpat_assum`bs.code =X`(assume_tac o SYM) >> fsrw_tac[ARITH_ss][] >>
    `∃bc10. bs.code = cb0 ++ [Label l] ++ REVERSE cc ++ bc10` by (
      qpat_assum`bce ++ bcr = X`(assume_tac o SYM) >>
      qpat_assum`X = bce`(assume_tac o SYM) >>
      rw[] ) >> pop_assum SUBST1_TAC >> fs[] >>
    `LENGTH bvs = LENGTH vs` by fs[EVERY2_EVERY] >>
    simp[] >>
    simp[code_for_return_def] >>
    disch_then(qx_choosel_then[`bvr`,`rfr`,`smr`]strip_assume_tac) >>
    map_every qexists_tac [`rfr`,`bvr`,`smr`] >>
    simp[Abbr`bs2`,Abbr`P`] >>
    metis_tac[SUBMAP_TRANS,IS_PREFIX_TRANS]) >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    simp[compile_def,pushret_def] >>
    rpt gen_tac >> strip_tac >>
    qspecl_then[`cenv`,`TCNonTail`,`sz`,`cs`,`exp`]strip_assume_tac (CONJUNCT1 compile_append_out) >>
    simp[Once SWAP_REVERSE] >>
    simp[Once SWAP_REVERSE] >>
    reverse(Cases_on`∃bc10. bs.code = bc0 ++ REVERSE bc ++ (prim1_to_bc uop)::bc10`) >- (
      rw[] >> fs[] ) >>
    fs[] >>
    first_x_assum(qspecl_then[`rd`,`cs`,`cenv`,`sz`,`bs`,`bce`,`bcr`,`bc0`]mp_tac) >>
    simp[Once SWAP_REVERSE] >>
    disch_then(assume_tac o CONJUNCT1) >>
    conj_asm1_tac >- (
      pop_assum mp_tac >>
      simp[code_for_push_def] >>
      fsrw_tac[DNF_ss][] >>
      map_every qx_gen_tac[`rf`,`rd'`,`bv`] >>
      strip_tac >>
      qmatch_assum_abbrev_tac`bc_next^* bs bs1` >>
      qspecl_then[`rd'`,`uop`,`s'`,`v`,`s''`,`v'`,`bs1`,`bc0 ++ REVERSE bc`,`bc10`,`bce`,`bs.stack`,`bv`]
        mp_tac prim1_to_bc_thm >>
      simp[Abbr`bs1`] >>
      qmatch_abbrev_tac`(P ⇒ Q) ⇒ R` >>
      `P` by fs[Cenv_bs_def] >>
      simp[Abbr`Q`,Abbr`R`] >>
      disch_then(qx_choosel_then[`bvr`,`rfr`,`smr`]strip_assume_tac) >>
      map_every qexists_tac[`rfr`,`rd' with sm := smr`,`bvr`] >>
      simp[] >>
      qmatch_assum_abbrev_tac`bc_next^* bs bs1` >>
      qmatch_assum_abbrev_tac`bc_next bs1 bs2` >>
      conj_tac >- metis_tac[RTC_TRANSITIVE,transitive_def,RTC_SUBSET] >>
      reverse conj_tac >- metis_tac[SUBMAP_TRANS,IS_PREFIX_TRANS] >>
      match_mp_tac Cenv_bs_imp_incsz >>
      qexists_tac`bs with <| code := bce; refs := rfr|>`>>
      simp[bc_state_component_equality] >>
      match_mp_tac Cenv_bs_change_store >>
      map_every qexists_tac[`rd`,`s`,`bs with <| code := bce|>`]>>
      simp[bc_state_component_equality] >>
      fs[Cenv_bs_def,s_refs_def,good_rd_def,UNCURRY,FEVERY_DEF,SUBSET_DEF] >>
      metis_tac[SUBMAP_TRANS,IS_PREFIX_TRANS] ) >>
    srw_tac[DNF_ss][] >>
    match_mp_tac code_for_push_return >>
    qmatch_assum_abbrev_tac`code_for_push rd bs bce bc0 code s s'' env vv renv rsz` >>
    map_every qexists_tac [`bc0`,`code`,`env`,`renv`,`rsz`] >>
    simp[Abbr`code`] >>
    qexists_tac `REVERSE args` >>
    fs[EVERY2_EVERY] ) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    simp[] >>
    rpt gen_tac >> strip_tac >>
    rpt gen_tac >> strip_tac >>
    conj_asm1_tac >- (
      rw[compile_def,LET_THM,pushret_def] >>
      qspecl_then[`cenv`,`TCNonTail`,`sz`,`cs`,`e1`](Q.X_CHOOSE_THEN`cx`strip_assume_tac)(CONJUNCT1 compile_append_out) >>
      qmatch_assum_abbrev_tac`cs0.out = cx ++ cs.out` >>
      qspecl_then[`cenv`,`TCNonTail`,`sz+1`,`cs0`,`e2`](Q.X_CHOOSE_THEN`cy`strip_assume_tac)(CONJUNCT1 compile_append_out) >>
      fs[Once SWAP_REVERSE] >>
      first_x_assum (qspecl_then[`rd`,`cs`,`cenv`,`sz`,`bs`,`bce`,`bcr`,`bc0`]mp_tac) >>
      simp[Abbr`cs0`,compile_def,Once SWAP_REVERSE] >>
      simp[code_for_push_def] >>
      disch_then (qx_choosel_then [`bvs`,`rfs`,`sms`] strip_assume_tac) >>
      fs[EVERY2_EVERY] >>
      `∃bv0 bv1. bvs = [bv0;bv1]` by (
        Cases_on `bvs` >> fs[] >>
        Cases_on `t` >> fs[LENGTH_NIL] ) >> fs[] >> rw[] >>
      fsrw_tac[DNF_ss][] >>
      qmatch_assum_abbrev_tac `bc_next^* bs bs0` >>
      qmatch_assum_abbrev_tac `Cv_bv pp v1 bv0` >>
      qspecl_then[`p2`,`v1`,`v2`,`v`,`bs0`,`bc0 ++ REVERSE cx ++ REVERSE cy`,`bc1`,`bs.stack`,`bv0`,`bv1`,`pp`]mp_tac prim2_to_bc_thm >>
      fs[Abbr`bs0`] >>
      `FST pp = sms` by rw[Abbr`pp`] >> fs[] >>
      imp_res_tac (CONJUNCT2 Cevaluate_store_SUBSET) >>
      imp_res_tac (CONJUNCT2 Cevaluate_Clocs) >> fs[] >>
      `(LENGTH sms.sm = LENGTH s') ∧ ALL_DISTINCT sms.sm` by
        fs[Cenv_bs_def,s_refs_def,good_rd_def] >>
      simp[] >>
      disch_then (Q.X_CHOOSE_THEN`bv`strip_assume_tac) >>
      map_every qexists_tac [`rfs`,`sms`,`bv`] >> fs[] >>
      conj_tac >- (
        rw[Once RTC_CASES2] >> disj2_tac >>
        qmatch_assum_abbrev_tac `bc_next^* bs bs0` >>
        qexists_tac `bs0` >> rw[] >>
        qmatch_assum_abbrev_tac`bc_next bs0 bs11` >>
        qmatch_abbrev_tac `bc_next bs0 bs12` >>
        qsuff_tac `bs11 = bs12` >- metis_tac[bc_eval1_thm,optionTheory.SOME_11] >>
        rw[Abbr`bs11`,Abbr`bs12`] >>
        Q.PAT_ABBREV_TAC`x = Stack Y` >>
        qmatch_abbrev_tac `bump_pc bs2 = bs1` >>
        `bc_fetch bs2 = SOME x` by (
          match_mp_tac bc_fetch_next_addr >>
          simp[Abbr`bs2`] >>
          qexists_tac `bc0 ++ REVERSE cx ++ REVERSE cy` >>
          unabbrev_all_tac >> rw[] ) >>
        rw[bump_pc_def] >>
        unabbrev_all_tac >>
        srw_tac[ARITH_ss][SUM_APPEND,FILTER_APPEND,ADD1] >>
        rw[bc_state_component_equality]) >>
      match_mp_tac Cenv_bs_imp_incsz >>
      qmatch_assum_abbrev_tac `Cenv_bs sms s' renv cenv (sz + 2) bs0` >>
      qexists_tac`bs0 with <| stack := bs.stack |>` >>
      reverse(rw[])>-(rw[bc_state_component_equality,Abbr`bs0`])>>
      match_mp_tac Cenv_bs_pops >>
      map_every qexists_tac[`[bv1;bv0]`,`bs0`] >>
      simp[Abbr`bs0`,bc_state_component_equality] >>
      metis_tac[Cenv_bs_CTLet_bound] ) >>
    fs[Once compile_def,LET_THM,pushret_def] >>
    qspecl_then[`cenv`,`sz`,`cs`,`[e1;e2]`]strip_assume_tac(CONJUNCT2(CONJUNCT2 compile_append_out)) >>
    simp[Once SWAP_REVERSE] >> rw[] >>
    fs[Once SWAP_REVERSE] >>
    match_mp_tac code_for_push_return >>
    qmatch_assum_abbrev_tac`code_for_push sm bs bce bc0 ccode s s' ccenv rvs renv rsz` >>
    map_every qexists_tac[`bc0`,`ccode`,`ccenv`,`renv`,`rsz`] >>
    simp[Abbr`ccode`] >>
    qexists_tac`REVERSE args`>>fs[EVERY2_EVERY]) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    rpt gen_tac >> strip_tac >>
    conj_asm1_tac >- (
      rw[compile_def,LET_THM,pushret_def] >>
      qspecl_then[`cenv`,`TCNonTail`,`sz`,`cs`,`e1`](Q.X_CHOOSE_THEN`cx`strip_assume_tac)(CONJUNCT1 compile_append_out) >>
      qmatch_assum_abbrev_tac`cs0.out = cx ++ cs.out` >>
      qspecl_then[`cenv`,`TCNonTail`,`sz+1`,`cs0`,`e2`](Q.X_CHOOSE_THEN`cy`strip_assume_tac)(CONJUNCT1 compile_append_out) >>
      fs[Once SWAP_REVERSE] >>
      first_x_assum (qspecl_then[`rd`,`cs`,`cenv`,`sz`,`bs`,`bce`,`bcr`,`bc0`]mp_tac) >>
      simp[Abbr`cs0`,compile_def,Once SWAP_REVERSE] >>
      simp[code_for_push_def] >>
      disch_then (qx_choosel_then [`bvs`,`rfs`,`sms`] strip_assume_tac) >>
      fs[EVERY2_EVERY] >>
      `∃bv0 bv1. bvs = [bv0;bv1]` by (
        Cases_on `bvs` >> fs[] >>
        Cases_on `t` >> fs[LENGTH_NIL] ) >> fs[] >> rw[] >>
      fsrw_tac[DNF_ss][] >>
      qmatch_assum_abbrev_tac `bc_next^* bs bs0` >>
      Cases_on`v1`>>fs[]>>
      map_every qexists_tac[`rfs |+ (EL n sms.sm, bv1)`,`sms`,`Block unit_tag []`] >>
      Cases_on`n < LENGTH s'`>> fs[] >>
      conj_tac >- (
        match_mp_tac (SIMP_RULE std_ss [transitive_def] RTC_TRANSITIVE) >>
        qexists_tac`bs0` >>
        rw[RTC_eq_NRC] >>
        qexists_tac`SUC(SUC 0)` >>
        rw[NRC] >>
        `bc_fetch bs0 = SOME Update` by (
          match_mp_tac bc_fetch_next_addr >>
          qexists_tac`bc0 ++ REVERSE cx ++ REVERSE cy` >>
          simp[Abbr`bs0`] ) >>
        simp[Once bc_eval1_thm] >>
        simp[bc_eval1_def,Abbr`bs0`,el_check_def] >>
        qpat_assum`Cv_bv X Y bv0`mp_tac >>
        simp[Once Cv_bv_cases] >>
        disch_then strip_assume_tac >>
        simp[] >>
        conj_tac >- (
          fs[Cenv_bs_def,s_refs_def,EVERY_MEM,el_check_def] >>
          fs[EXTENSION] >> metis_tac[MEM_EL] ) >>
        fs[bump_pc_def] >>
        qpat_assum`X = SOME Update`kall_tac >>
        qmatch_abbrev_tac`bc_next bs0 bs1` >>
        `bc_fetch bs0 = SOME (Stack (Cons unit_tag 0))` by (
          match_mp_tac bc_fetch_next_addr >>
          qexists_tac`bc0 ++ REVERSE cx ++ REVERSE cy ++ [Update]` >>
          simp[Abbr`bs0`,SUM_APPEND,FILTER_APPEND] ) >>
        simp[bc_eval1_thm,bc_eval1_def,bc_eval_stack_def] >>
        simp[bump_pc_def,Abbr`bs0`,Abbr`bs1`,bc_state_component_equality] >>
        simp[SUM_APPEND,FILTER_APPEND] >>
        fs[FLOOKUP_DEF,el_check_def] ) >>
      qpat_assum`X = v`(assume_tac o SYM) >>
      qpat_assum`X = s'`(assume_tac o SYM) >>
      simp[Once Cv_bv_cases] >>
      conj_tac >- (
        match_mp_tac Cenv_bs_imp_incsz >>
        Q.PAT_ABBREV_TAC`rfs2 = rfs |+ X` >>
        qexists_tac`bs with <| code := bce; refs := rfs2|>` >>
        simp[bc_state_component_equality] >>
        match_mp_tac Cenv_bs_change_store >>
        map_every qexists_tac[`rd`,`s`,`bs with code := bce`] >>
        `LENGTH (LUPDATE v2 n s') = LENGTH s'` by (
          simp[LENGTH_LUPDATE]) >>
        simp[bc_state_component_equality] >>
        fs[Cenv_bs_def,s_refs_def,good_rd_def,FEVERY_DEF,UNCURRY] >>
        simp[Abbr`rfs2`] >>
        reverse conj_tac >- (
          simp[MEM_EL] >>
          srw_tac[SATISFY_ss][] >>
          metis_tac[] ) >>
        simp[EVERY2_EVERY] >>
        conj_tac >- (
          fs[FAPPLY_FUPDATE_THM] >> rw[] >>
          metis_tac[MEM_EL]) >>
        conj_asm1_tac >- (
          fs[EVERY_MEM] ) >>
        fs[EVERY_MEM,FORALL_PROD,EVERY2_EVERY] >>
        rfs[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM] >>
        gen_tac >> strip_tac >>
        simp[EL_LUPDATE] >>
        rfs[EL_MAP,FAPPLY_FUPDATE_THM] >>
        rw[] >>
        fs[EL_ALL_DISTINCT_EL_EQ] >>
        metis_tac[]) >>
      rw[] >>
      fs[Cenv_bs_def,s_refs_def,good_rd_def] >>
      metis_tac[MEM_EL]) >>
    fs[Once compile_def,LET_THM,pushret_def] >>
    qspecl_then[`cenv`,`sz`,`cs`,`[e1;e2]`]strip_assume_tac(CONJUNCT2(CONJUNCT2 compile_append_out)) >>
    simp[Once SWAP_REVERSE] >> rw[] >>
    fs[Once SWAP_REVERSE] >>
    match_mp_tac code_for_push_return >>
    qmatch_assum_abbrev_tac`code_for_push sm bs bce bc0 ccode s s'' ccenv rvs renv rsz` >>
    map_every qexists_tac[`bc0`,`ccode`,`ccenv`,`renv`,`rsz`] >>
    simp[Abbr`ccode`] >>
    qexists_tac`REVERSE args`>>fs[EVERY2_EVERY]) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    rpt gen_tac >> strip_tac >>
    fs[compile_def,LET_THM] >>
    Q.PAT_ABBREV_TAC`cs0 = compile cenv t sz cs exp` >>
    qabbrev_tac`nl = cs0.next_label` >>
    full_simp_tac std_ss [prove(``w::x::y::cs0.out=[w;x;y]++cs0.out``,rw[])] >>
    full_simp_tac std_ss [prove(``x::y::(cs0).out=[x;y]++(cs0).out``,rw[])] >>
    Q.PAT_ABBREV_TAC`lc3 = [Label x;y]` >>
    Q.PAT_ABBREV_TAC`lc2 = [Label x;y;z]` >>
    qunabbrev_tac`cs0` >>
    qspecl_then[`cenv`,`TCNonTail`,`sz`,`cs`,`exp`](Q.X_CHOOSE_THEN`be1`strip_assume_tac)(CONJUNCT1 compile_append_out) >>
    qmatch_assum_abbrev_tac`cs0.out = be1 ++ cs.out` >>
    simp_tac(srw_ss()++DNF_ss)[] >>
    simp[RIGHT_AND_FORALL_THM] >>
    CONV_TAC (RESORT_FORALL_CONV (op@ o partition (C mem ["args","klvs"] o fst o dest_var))) >>
    ntac 2 gen_tac >>
    Q.PAT_ABBREV_TAC`cs2 = compiler_result_out_fupd (K (lc2 ++ Y ++ X)) Z` >>
    Q.PAT_ABBREV_TAC`cs3 = compiler_result_out_fupd (K (lc3 ++ Y)) Z` >>
    Q.PAT_ABBREV_TAC`cs2k = compiler_result_out_fupd (K (lc2 ++ Y ++ X)) Z` >>
    Q.PAT_ABBREV_TAC`cs3k = compiler_result_out_fupd (K (X::Y)) Z` >>
    qspecl_then[`cenv`,`TCNonTail`,`sz`,`cs2`,`e2`](Q.X_CHOOSE_THEN`be2`strip_assume_tac)(CONJUNCT1 compile_append_out) >>
    qspecl_then[`cenv`,`TCNonTail`,`sz`,`cs3`,`e3`](Q.X_CHOOSE_THEN`be3`strip_assume_tac)(CONJUNCT1 compile_append_out) >>
    Q.PAT_ABBREV_TAC`tt = TCTail X Y` >>
    qspecl_then[`cenv`,`tt`,`sz`,`cs2k`,`e2`](Q.X_CHOOSE_THEN`be2k`strip_assume_tac)(CONJUNCT1 compile_append_out) >>
    qspecl_then[`cenv`,`tt`,`sz`,`cs3k`,`e3`](Q.X_CHOOSE_THEN`be3k`strip_assume_tac)(CONJUNCT1 compile_append_out) >>
    qabbrev_tac`tf = TCNonTail` >>
    `(compile cenv tf sz cs3 e3).out = be3 ++ lc3 ++ be2 ++ lc2 ++ be1 ++ cs.out` by (
      simp[Abbr`cs3`,Abbr`cs2`]) >>
    `(compile cenv tt sz cs3k e3).out = be3k ++ [Label (nl + 1)] ++ be2k ++ lc2 ++ be1 ++ cs.out` by (
      simp[Abbr`cs3k`,Abbr`cs2k`]) >>
    simp[] >>
    qabbrev_tac`nl1 = nl + 1` >>
    qabbrev_tac`nl2 = nl + 2` >>
    qabbrev_tac `il = bs.inst_length` >>
    `LENGTH s ≤ LENGTH s' ∧ LENGTH s' ≤ LENGTH s''` by metis_tac[SIMP_RULE(srw_ss())[FORALL_PROD]Cevaluate_store_SUBSET] >>
    rpt gen_tac >>
    simp_tac (srw_ss()) [Once SWAP_REVERSE] >>
    simp_tac (srw_ss()) [Once SWAP_REVERSE] >>
    reverse(Cases_on`∃bc10. bs.code = bc0 ++ REVERSE be1 ++ REVERSE lc2 ++ bc10`) >- (
      rw[] >> fs[]) >>
    rpt (qpat_assum `∀j k. X ⇒ Y` kall_tac) >> fs[] >>
    POP_ASSUM_LIST(MAP_EVERY ASSUME_TAC) >>
    first_x_assum(qspecl_then[`rd`,`cs`,`cenv`,`sz`,`bs`,`bce`,`bcr`,`bc0`]mp_tac) >>
    fs[ALL_DISTINCT_APPEND,Once SWAP_REVERSE] >>
    disch_then(CHOOSE_THEN strip_assume_tac o SIMP_RULE (srw_ss()) [code_for_push_def,LET_THM,Once Cv_bv_cases] o CONJUNCT1) >>
    qmatch_assum_abbrev_tac`bc_next^* bs bs1` >>
    conj_tac >- (
      rw[] >>
      Cases_on `b1` >> fs[] >- (
        first_x_assum(qspecl_then[`rd'`,`cs2`,`cenv`,`sz`,`bs1 with <| stack := bs.stack; pc := next_addr il (bc0 ++ REVERSE be1 ++ REVERSE lc2) |>`
                                 ,`bce`,`bcr`,`bc0 ++ REVERSE be1 ++ REVERSE lc2`]mp_tac) >>
        simp[Abbr`bs1`,Once SWAP_REVERSE] >>
        qmatch_abbrev_tac`(P ⇒ Q) ⇒ R` >>
        `P` by (
          map_every qunabbrev_tac [`P`,`Q`,`R`] >>
          conj_tac >- metis_tac[SUBSET_DEF,IN_COUNT,LESS_LESS_EQ_TRANS] >>
          conj_tac >- metis_tac[Cevaluate_Clocs,FST] >>
          qspecl_then[`s`,`env`,`exp`,`(s',Cval (CLitv (Bool T)))`]mp_tac(CONJUNCT1 Cevaluate_vlabs) >>
          simp[] >> strip_tac >>
          qspecl_then[`s`,`env`,`exp`,`(s',Cval (CLitv (Bool T)))`]mp_tac(CONJUNCT1 Cevaluate_all_vlabs) >>
          simp[] >> strip_tac >>
          conj_tac >- ( fsrw_tac[DNF_ss][SUBSET_DEF,EVERY_MEM] >> metis_tac[] ) >>
          conj_tac >- (
            fs[Abbr`cs2`,Abbr`cs0`] >>
            match_mp_tac Cenv_bs_imp_decsz >>
            qmatch_assum_abbrev_tac `Cenv_bs rd' s' renv cenv (sz + 1) bs1` >>
            qexists_tac`bs1` >>
            reverse(rw[])>-(rw[bc_state_component_equality,Abbr`bs1`])>>
            imp_res_tac Cenv_bs_CTLet_bound >>
            pop_assum(qspec_then`sz+1`mp_tac) >>
            srw_tac[ARITH_ss][] ) >>
          fsrw_tac[DNF_ss][FILTER_APPEND,ALL_DISTINCT_APPEND,MEM_FILTER,is_Label_rwt,EVERY_MEM,Abbr`cs2`
                          ,FILTER_REVERSE,ALL_DISTINCT_REVERSE,Abbr`lc2`,Abbr`nl`,between_def,MEM_MAP,Abbr`cs0`] >>
          rw[] >> spose_not_then strip_assume_tac >> res_tac >> DECIDE_TAC ) >>
        simp[] >>
        map_every qunabbrev_tac [`P`,`Q`,`R`] >>
        disch_then(mp_tac o CONJUNCT1) >>
        simp_tac(srw_ss()++DNF_ss)[code_for_push_def,LET_THM] >>
        map_every qx_gen_tac[`rfs2`,`sm2`,`b2`] >> strip_tac >>
        map_every qexists_tac[`rfs2`,`sm2`,`b2`] >>
        qmatch_assum_abbrev_tac`bc_next^* bs05 bs11` >>
        qmatch_assum_abbrev_tac`bc_next^* bs bs03` >>
        `bc_next^* bs03 bs05` by (
          rw[RTC_eq_NRC] >>
          qexists_tac `SUC 0` >>
          rw[] >>
          `bc_fetch bs03 = SOME (JumpIf (Lab nl))` by (
            match_mp_tac bc_fetch_next_addr >>
            simp[Abbr`bs03`,Abbr`lc2`] >>
            qexists_tac`bc0 ++ REVERSE be1` >>
            rw[]) >>
          rw[bc_eval1_thm] >>
          rw[bc_eval1_def,Abbr`bs03`,LET_THM] >>
          rw[Abbr`bs05`,bc_state_component_equality] >>
          rw[bc_find_loc_def] >>
          qmatch_abbrev_tac`bc_find_loc_aux ls il nl 0 = SOME (next_addr il ls0)` >>
          `∃ls1. ls = ls0 ++ ls1` by rw[Abbr`ls`,Abbr`ls0`] >>
          pop_assum SUBST1_TAC >> qunabbrev_tac`ls` >>
          match_mp_tac bc_find_loc_aux_append_code >>
          match_mp_tac bc_find_loc_aux_ALL_DISTINCT >>
          `ALL_DISTINCT (FILTER is_Label ls0)` by (
            fs[ALL_DISTINCT_APPEND,FILTER_APPEND] ) >>
          qexists_tac`LENGTH bc0 + LENGTH be1 + 2` >>
          fsrw_tac[ARITH_ss][Abbr`ls0`,Abbr`lc2`] >>
          conj_tac >- lrw[EL_DROP,EL_CONS,EL_APPEND2] >>
          lrw[TAKE_APPEND2,FILTER_APPEND] ) >>
        conj_tac >- (
          qmatch_abbrev_tac`bc_next^* bs bs13` >>
          `bc_fetch bs11 = SOME (Jump (Lab nl2))` by (
            match_mp_tac bc_fetch_next_addr >>
            simp[Abbr`bs11`,Abbr`lc3`] >>
            Q.PAT_ABBREV_TAC`ls = X ++ REVERSE be2` >>
            qexists_tac`ls` >>
            srw_tac[ARITH_ss][Abbr`nl2`,Abbr`nl1`] ) >>
          `bc_next bs11 bs13` by (
            rw[bc_eval1_thm] >>
            rw[bc_eval1_def,Abbr`bs13`,Abbr`bs11`] >>
            rw[bc_state_component_equality] >>
            rw[bc_find_loc_def] >>
            Q.PAT_ABBREV_TAC`ls = X ++ REVERSE be3` >>
            match_mp_tac bc_find_loc_aux_append_code >>
            match_mp_tac bc_find_loc_aux_ALL_DISTINCT >>
            qexists_tac`LENGTH ls` >>
            conj_tac >- (
              fsrw_tac[DNF_ss,ARITH_ss]
                [Abbr`ls`,FILTER_APPEND,ALL_DISTINCT_APPEND,FILTER_REVERSE,ALL_DISTINCT_REVERSE,MEM_FILTER,is_Label_rwt,EVERY_MEM
                ,Abbr`nl2`,Abbr`lc2`,Abbr`lc3`,Abbr`nl1`,Abbr`cs2`,MEM_MAP,between_def,Abbr`cs0`,Abbr`cs3`] >>
              rw[] >> spose_not_then strip_assume_tac >> res_tac >> DECIDE_TAC ) >>
            lrw[TAKE_APPEND2,EL_APPEND2,FILTER_APPEND] ) >>
          metis_tac[RTC_TRANSITIVE,transitive_def,RTC_SUBSET] ) >>
        simp[Abbr`il`] >>
        conj_tac >- fs[Cenv_bs_def,s_refs_def,good_rd_def] >>
        metis_tac[SUBMAP_TRANS,IS_PREFIX_TRANS] ) >>
      first_x_assum(qspecl_then[`rd'`,`cs3`,`cenv`,`sz`,`bs1 with <| stack := bs.stack;
                                pc := next_addr il (bc0 ++ REVERSE be1 ++ REVERSE lc2 ++ REVERSE be2 ++ REVERSE lc3) |>`
                               ,`bce`,`bcr`,`bc0 ++ REVERSE be1 ++ REVERSE lc2 ++ REVERSE be2 ++ REVERSE lc3`]mp_tac) >>
      simp[Abbr`bs1`,Once SWAP_REVERSE] >>
      qmatch_abbrev_tac`(P ⇒ Q) ⇒ R` >>
      `P` by (
        map_every qunabbrev_tac[`P`,`Q`,`R`] >>
        conj_tac >- metis_tac[SUBSET_DEF,IN_COUNT,LESS_LESS_EQ_TRANS] >>
        conj_tac >- metis_tac[Cevaluate_Clocs,FST] >>
        qspecl_then[`s`,`env`,`exp`,`(s',Cval (CLitv (Bool F)))`]mp_tac(CONJUNCT1 Cevaluate_vlabs) >>
        simp[] >> strip_tac >>
        qspecl_then[`s`,`env`,`exp`,`(s',Cval (CLitv (Bool F)))`]mp_tac(CONJUNCT1 Cevaluate_all_vlabs) >>
        simp[] >> strip_tac >>
        conj_tac >- ( fsrw_tac[DNF_ss][SUBSET_DEF,EVERY_MEM] >> metis_tac[] ) >>
        conj_tac >- (
          match_mp_tac Cenv_bs_imp_decsz >>
          qmatch_assum_abbrev_tac `Cenv_bs rd' s' renv cenv (sz + 1) bs1` >>
          qexists_tac`bs1` >>
          reverse(rw[])>-(rw[bc_state_component_equality,Abbr`bs1`])>>
          imp_res_tac Cenv_bs_CTLet_bound >>
          pop_assum(qspec_then`sz+1`mp_tac) >>
          srw_tac[ARITH_ss][]) >>
        simp[Abbr`cs3`] >>
        fsrw_tac[DNF_ss,ARITH_ss]
          [FILTER_APPEND,ALL_DISTINCT_APPEND,MEM_FILTER,is_Label_rwt,EVERY_MEM,Abbr`cs2`,Abbr`lc3`
          ,FILTER_REVERSE,ALL_DISTINCT_REVERSE,Abbr`lc2`,Abbr`nl`,between_def,MEM_MAP,Abbr`cs0`,Abbr`nl1`,Abbr`nl2`] >>
        rw[] >> spose_not_then strip_assume_tac >> res_tac >> DECIDE_TAC ) >>
      simp[] >>
      map_every qunabbrev_tac[`P`,`Q`,`R`] >>
      disch_then(mp_tac o CONJUNCT1) >>
      Q.PAT_ABBREV_TAC`ls = X++cs.out` >>
      `ls = be3 ++ cs3.out` by (
        rw[Abbr`ls`,Abbr`cs3`] >>
        qunabbrev_tac`cs2` >> simp[] ) >>
      simp[Once SWAP_REVERSE] >>
      simp_tac(srw_ss()++DNF_ss)[code_for_push_def,LET_THM] >>
      map_every qx_gen_tac[`rfs3`,`sm3`,`b3`] >> strip_tac >>
      map_every qexists_tac[`rfs3`,`sm3`,`b3`] >>
      qmatch_assum_abbrev_tac`bc_next^* bs bs03` >>
      qmatch_assum_abbrev_tac`bc_next^* bs05 bs07` >>
      `bc_next^* bs03 bs05` by (
        `bc_fetch bs03 = SOME (JumpIf (Lab nl))` by (
          match_mp_tac bc_fetch_next_addr >>
          rw[Abbr`bs03`,Abbr`lc2`] >>
          qexists_tac`bc0 ++ REVERSE be1` >>
          rw[]) >>
        rw[RTC_eq_NRC] >>
        qexists_tac`SUC (SUC 0)` >>
        rw[NRC] >>
        rw[bc_eval1_thm] >>
        rw[Once bc_eval1_def] >>
        rw[Abbr`bs03`,LET_THM] >>
        srw_tac[DNF_ss][] >>
        rw[bc_find_loc_def] >>
        rw[LEFT_EXISTS_AND_THM] >- (
          qmatch_abbrev_tac`∃n. X = SOME n` >>
          qsuff_tac `X ≠ NONE` >- (Cases_on`X` >> rw[]) >>
          qunabbrev_tac`X` >>
          match_mp_tac (CONTRAPOS (SPEC_ALL bc_find_loc_aux_NONE)) >>
          fsrw_tac[DNF_ss,ARITH_ss][EVERY_MEM,between_def,is_Label_rwt,MEM_FILTER,Abbr`lc2`,Abbr`nl2`]) >>
        qmatch_abbrev_tac`bc_eval1 (bump_pc bs03) = SOME bs06` >>
        `bc_fetch bs03 = SOME (JumpIf (Lab nl))` by (
          fs[bc_fetch_def,Abbr`bs03`] >> rfs[REVERSE_APPEND] ) >>
        rw[bump_pc_def] >>
        rw[Abbr`bs03`] >>
        qmatch_abbrev_tac`bc_eval1 bs03 = SOME bs06` >>
        `bc_fetch bs03 = SOME (Jump (Lab nl1))` by (
          match_mp_tac bc_fetch_next_addr >>
          rw[Abbr`bs03`,Abbr`lc2`] >>
          qexists_tac`bc0 ++ REVERSE be1 ++ [JumpIf (Lab nl)]` >>
          rw[REVERSE_APPEND,FILTER_APPEND,SUM_APPEND] >>
          srw_tac[ARITH_ss][] ) >>
        rw[bc_eval1_def] >>
        rw[Abbr`bs03`,Abbr`bs06`,Abbr`bs05`] >>
        rw[bc_state_component_equality] >>
        rw[bc_find_loc_def] >>
        match_mp_tac bc_find_loc_aux_append_code >>
        match_mp_tac bc_find_loc_aux_append_code >>
        match_mp_tac bc_find_loc_aux_append_code >>
        match_mp_tac bc_find_loc_aux_ALL_DISTINCT >>
        simp[Abbr`lc3`] >>
        Q.PAT_ABBREV_TAC`ls = X ++ REVERSE be2` >>
        qexists_tac`LENGTH ls + 1` >>
        lrw[Abbr`ls`,EL_APPEND2] >>
        lrw[TAKE_APPEND2,FILTER_APPEND] ) >>
      conj_tac >- (
        qmatch_abbrev_tac`bc_next^* bs bs08` >>
        `bs08 = bs07` by (
          rw[Abbr`bs08`,Abbr`bs07`] >>
          rw[bc_state_component_equality] >>
          rw[FILTER_APPEND] ) >>
        metis_tac[RTC_TRANSITIVE,transitive_def] ) >>
      simp[Abbr`il`] >>
      conj_tac >- fs[Cenv_bs_def,s_refs_def,good_rd_def] >>
      metis_tac[SUBMAP_TRANS,IS_PREFIX_TRANS] ) >>
    rpt strip_tac >>
    Cases_on `b1` >> fs[] >- (
      first_x_assum(qspecl_then[`rd'`,`cs2k`,`cenv`,`sz`,`bs1 with <| stack := bs.stack; pc := next_addr il (bc0 ++ REVERSE be1 ++ REVERSE lc2) |>`
                               ,`bce`,`bcr`,`bc0 ++ REVERSE be1 ++ REVERSE lc2`]mp_tac) >>
      simp[Abbr`bs1`] >>
      qmatch_abbrev_tac`(P ⇒ Q) ⇒ R` >>
      `P` by (
        map_every qunabbrev_tac [`P`,`Q`,`R`] >>
        conj_tac >- metis_tac[SUBSET_DEF,LESS_LESS_EQ_TRANS,IN_COUNT] >>
        conj_tac >- (
          qmatch_assum_abbrev_tac`Cevaluate s ee exp (s',vv)` >>
          qspecl_then[`s`,`ee`,`exp`,`(s',vv)`]mp_tac(CONJUNCT1 Cevaluate_Clocs)>>
          simp[Abbr`ee`] ) >>
        qspecl_then[`s`,`env`,`exp`,`(s',Cval (CLitv (Bool T)))`]mp_tac(CONJUNCT1 Cevaluate_vlabs) >>
        simp[] >> strip_tac >>
        qspecl_then[`s`,`env`,`exp`,`(s',Cval (CLitv (Bool T)))`]mp_tac(CONJUNCT1 Cevaluate_all_vlabs) >>
        simp[] >> strip_tac >>
        conj_tac >- ( fsrw_tac[DNF_ss,ARITH_ss][SUBSET_DEF,EVERY_MEM] >> metis_tac[] ) >>
        conj_tac >- (
          fs[Abbr`cs2k`,Abbr`cs0`] >>
          match_mp_tac Cenv_bs_imp_decsz >>
          qmatch_assum_abbrev_tac `Cenv_bs rd' s' renv cenv (sz + 1) bs1` >>
          qexists_tac`bs1` >>
          reverse(rw[])>-(rw[bc_state_component_equality,Abbr`bs1`])>>
          imp_res_tac Cenv_bs_CTLet_bound >>
          pop_assum(qspec_then`sz+1`mp_tac) >>
          srw_tac[ARITH_ss][] ) >>
        fsrw_tac[DNF_ss][FILTER_APPEND,ALL_DISTINCT_APPEND,MEM_FILTER,is_Label_rwt,EVERY_MEM,Abbr`cs2k`,Abbr`nl2`
                        ,FILTER_REVERSE,ALL_DISTINCT_REVERSE,Abbr`lc2`,Abbr`nl`,between_def,MEM_MAP,Abbr`cs0`] >>
        rw[] >> spose_not_then strip_assume_tac >> res_tac >> DECIDE_TAC ) >>
      simp[] >>
      map_every qunabbrev_tac [`P`,`Q`,`R`] >>
      disch_then(mp_tac o CONJUNCT2) >>
      simp_tac(srw_ss()++DNF_ss)[] >>
      disch_then(mp_tac o CONV_RULE (RESORT_FORALL_CONV (op@ o partition (C mem ["args'","klvs'"] o fst o dest_var)))) >>
      disch_then(qspecl_then[`klvs`,`args`]mp_tac) >>
      fs[Abbr`tf`,Once SWAP_REVERSE] >>
      `bc10 = REVERSE be2k ++ Label nl1::(REVERSE be3k ++ bc1)` by (
        rw[] >> fs[] ) >>
      simp[] >>
      disch_then(qspecl_then[`env0`,`vs`,`blvs`,`benv`,`ret`,`cl`,`st`]mp_tac) >>
      simp[] >>
      qmatch_abbrev_tac`(P ⇒ Q) ⇒ R` >>
      `P` by (
        map_every qunabbrev_tac [`P`,`Q`,`R`] >>
        conj_tac >> (
        qmatch_abbrev_tac`EVERY2 Q l1 l2` >>
        ho_match_mp_tac (MP_CANON (GEN_ALL EVERY2_mono)) >>
        qmatch_assum_abbrev_tac`EVERY2 P l1 l2` >>
        qexists_tac`P`>>rw[Abbr`P`,Abbr`Q`] >>
        match_mp_tac (GEN_ALL (MP_CANON (CONJUNCT1 (SPEC_ALL Cv_bv_SUBMAP)))) >>
        simp[] >>
        qexists_tac`rd` >>
        simp[] >>
        fs[SUBMAP_DEF,DRESTRICT_DEF,s_refs_def,good_rd_def,Cenv_bs_def,UNCURRY,FEVERY_DEF] )) >>
      simp[] >>
      map_every qunabbrev_tac [`P`,`Q`,`R`] >>
      simp[code_for_return_def] >>
      simp_tac(srw_ss()++DNF_ss)[] >>
      map_every qx_gen_tac[`bv2`,`rf2`,`sm2`] >>
      strip_tac >>
      map_every qexists_tac[`bv2`,`rf2`,`sm2`] >>
      simp[] >>
      reverse conj_tac >- metis_tac[SUBMAP_TRANS,IS_PREFIX_TRANS] >>
      qmatch_assum_abbrev_tac`bc_next^* bs bs1` >>
      qmatch_assum_abbrev_tac`bc_next^* bs2 bs3` >>
      qsuff_tac`bc_next bs1 bs2` >- metis_tac[RTC_TRANSITIVE,transitive_def,RTC_SUBSET] >>
      rw[bc_eval1_thm] >>
      `bc_fetch bs1 = SOME (JumpIf (Lab nl))` by (
         match_mp_tac bc_fetch_next_addr >>
         simp[Abbr`bs1`,Abbr`lc2`] >>
         qexists_tac`bc0 ++ REVERSE be1` >>
         rw[]) >>
      rw[bc_eval1_def,Abbr`bs1`,LET_THM] >>
      rw[Abbr`bs2`,bc_state_component_equality] >>
      rw[bc_find_loc_def] >>
      qmatch_abbrev_tac`bc_find_loc_aux ls il nl 0 = SOME (next_addr il ls0)` >>
      `∃ls1. ls = ls0 ++ ls1` by rw[Abbr`ls`,Abbr`ls0`] >>
      pop_assum SUBST1_TAC >> qunabbrev_tac`ls` >>
      match_mp_tac bc_find_loc_aux_append_code >>
      match_mp_tac bc_find_loc_aux_ALL_DISTINCT >>
      `ALL_DISTINCT (FILTER is_Label ls0)` by (
        fs[ALL_DISTINCT_APPEND,FILTER_APPEND] ) >>
      qexists_tac`LENGTH bc0 + LENGTH be1 + 2` >>
      fsrw_tac[ARITH_ss][Abbr`ls0`,Abbr`lc2`] >>
      conj_tac >- lrw[EL_DROP,EL_CONS,EL_APPEND2] >>
      lrw[TAKE_APPEND2,FILTER_APPEND] ) >>
    first_x_assum(qspecl_then[`rd'`,`cs3k`,`cenv`,`sz`,`bs1 with <| stack := bs.stack;
                              pc := next_addr il (bc0 ++ REVERSE be1 ++ REVERSE lc2 ++ REVERSE be2k ++ [Label nl1]) |>`
                             ,`bce`,`bcr`,`bc0 ++ REVERSE be1 ++ REVERSE lc2 ++ REVERSE be2k ++ [Label nl1]`]mp_tac) >>
    simp[Abbr`bs1`,Once SWAP_REVERSE] >>
    qmatch_abbrev_tac`(P ⇒ Q) ⇒ R` >>
    `P` by (
      map_every qunabbrev_tac[`P`,`Q`,`R`] >>
      conj_tac >- metis_tac[SUBSET_DEF,IN_COUNT,LESS_LESS_EQ_TRANS] >>
      conj_tac >- (
        qmatch_assum_abbrev_tac`Cevaluate s ee exp (s',vv)` >>
        qspecl_then[`s`,`ee`,`exp`,`(s',vv)`]mp_tac(CONJUNCT1 Cevaluate_Clocs)>>
        simp[Abbr`ee`] ) >>
      qspecl_then[`s`,`env`,`exp`,`(s',Cval (CLitv (Bool F)))`]mp_tac(CONJUNCT1 Cevaluate_vlabs) >>
      simp[] >> strip_tac >>
      qspecl_then[`s`,`env`,`exp`,`(s',Cval (CLitv (Bool F)))`]mp_tac(CONJUNCT1 Cevaluate_all_vlabs) >>
      simp[] >> strip_tac >>
      conj_tac >- ( fsrw_tac[DNF_ss,ARITH_ss][SUBSET_DEF,EVERY_MEM] >> metis_tac[] ) >>
      conj_tac >- (
        match_mp_tac Cenv_bs_imp_decsz >>
        qmatch_assum_abbrev_tac `Cenv_bs rd' s' renv cenv (sz + 1) bs1` >>
        qexists_tac`bs1` >>
        reverse(rw[])>-(rw[bc_state_component_equality,Abbr`bs1`])>>
        imp_res_tac Cenv_bs_CTLet_bound >>
        pop_assum(qspec_then`sz+1`mp_tac) >>
        srw_tac[ARITH_ss][]) >>
      simp[Abbr`cs3k`] >>
      fsrw_tac[DNF_ss,ARITH_ss]
        [FILTER_APPEND,ALL_DISTINCT_APPEND,MEM_FILTER,is_Label_rwt,EVERY_MEM,Abbr`cs2k`,Abbr`lc3`,Abbr`tt`,Abbr`tf`
        ,FILTER_REVERSE,ALL_DISTINCT_REVERSE,Abbr`lc2`,Abbr`nl`,between_def,MEM_MAP,Abbr`cs0`,Abbr`nl1`,Abbr`nl2`] >>
      rw[] >> spose_not_then strip_assume_tac >> res_tac >> DECIDE_TAC ) >>
    simp[] >>
    map_every qunabbrev_tac[`P`,`Q`,`R`] >>
    disch_then(mp_tac o CONJUNCT2) >>
    simp_tac(srw_ss()++DNF_ss)[Abbr`tt`] >>
    disch_then(mp_tac o CONV_RULE (RESORT_FORALL_CONV (op@ o partition (C mem ["args'","klvs'"] o fst o dest_var)))) >>
    disch_then(qspecl_then[`klvs`,`args`]mp_tac) >>
    simp[] >>
    `bc10 = REVERSE be2k ++ Label nl1::(REVERSE be3k ++ bc1)` by (
      rw[] >> fs[] ) >>
    simp[Abbr`cs3k`] >>
    disch_then(qspec_then`REVERSE be3k`mp_tac) >>
    simp[Abbr`cs2k`] >>
    disch_then(qspecl_then[`env0`,`vs`,`blvs`,`benv`,`ret`,`cl`,`st`]mp_tac) >>
    simp[] >>
    qmatch_abbrev_tac`(P ⇒ Q) ⇒ R` >>
    `P` by (
      map_every qunabbrev_tac [`P`,`Q`,`R`] >>
      conj_tac >> (
      qmatch_abbrev_tac`EVERY2 Q l1 l2` >>
      ho_match_mp_tac (MP_CANON (GEN_ALL EVERY2_mono)) >>
      qmatch_assum_abbrev_tac`EVERY2 P l1 l2` >>
      qexists_tac`P`>>rw[Abbr`P`,Abbr`Q`] >>
      match_mp_tac (GEN_ALL (MP_CANON (CONJUNCT1 (SPEC_ALL Cv_bv_SUBMAP)))) >>
      simp[] >>
      qexists_tac`rd` >>
      simp[] >>
      fs[SUBMAP_DEF,DRESTRICT_DEF,good_rd_def,s_refs_def,Cenv_bs_def,UNCURRY,FEVERY_DEF] )) >>
    simp[] >>
    map_every qunabbrev_tac [`P`,`Q`,`R`] >>
    simp[code_for_return_def] >>
    simp_tac(srw_ss()++DNF_ss)[] >>
    map_every qx_gen_tac[`bv2`,`rf2`,`sm2`] >>
    strip_tac >>
    map_every qexists_tac[`bv2`,`rf2`,`sm2`] >>
    simp[] >>
    reverse conj_tac >- metis_tac[SUBMAP_TRANS,IS_PREFIX_TRANS] >>
    qmatch_assum_abbrev_tac`bc_next^* bs bs1` >>
    qmatch_assum_abbrev_tac`bc_next^* bs2 bs3` >>
    qsuff_tac`bc_next^* bs1 bs2` >- metis_tac[RTC_TRANSITIVE,transitive_def] >>
    rw[RTC_eq_NRC] >>
    qexists_tac`SUC(SUC 0)` >>
    rw[NRC] >>
    rw[bc_eval1_thm] >>
    `bc_fetch bs1 = SOME (JumpIf (Lab nl))` by (
       match_mp_tac bc_fetch_next_addr >>
       simp[Abbr`bs1`,Abbr`lc2`] >>
       qexists_tac`bc0 ++ REVERSE be1` >>
       rw[]) >>
    rw[Once bc_eval1_def] >>
    rw[Abbr`bs1`,LET_THM] >>
    srw_tac[DNF_ss][] >>
    simp[LEFT_EXISTS_AND_THM] >>
    conj_tac >- (
      qmatch_abbrev_tac`∃n. X = SOME n` >>
      qsuff_tac`~(X = NONE)` >- ( Cases_on`X`>>rw[]) >>
      qunabbrev_tac`X` >>
      simp[bc_find_loc_def] >>
      spose_not_then strip_assume_tac >>
      imp_res_tac bc_find_loc_aux_NONE >>
      fs[] >> rfs[Abbr`lc2`] ) >>
    qmatch_abbrev_tac`bc_eval1 (bump_pc bs1) = SOME bs2` >>
    `bc_fetch bs1 = SOME (JumpIf (Lab nl))` by (
      match_mp_tac bc_fetch_next_addr >>
      simp[Abbr`bs1`,Abbr`lc2`] >>
      qexists_tac`bc0 ++ REVERSE be1` >>
      rw[] ) >>
    rw[bump_pc_def,Abbr`bs1`] >>
    qmatch_abbrev_tac`bc_eval1 bs1 = SOME bs2` >>
    `bc_fetch bs1 = SOME (Jump (Lab nl1))` by (
      match_mp_tac bc_fetch_next_addr >>
      simp[Abbr`bs1`,Abbr`lc2`] >>
      qexists_tac`bc0 ++ REVERSE be1 ++ [JumpIf (Lab nl)]` >>
      srw_tac[ARITH_ss][FILTER_APPEND,SUM_APPEND] ) >>
    rw[bc_eval1_def] >>
    rw[Abbr`bs2`,Abbr`bs1`,bc_state_component_equality] >>
    rw[bc_find_loc_def] >>
    qmatch_abbrev_tac`bc_find_loc_aux ls il nl1 0 = SOME (next_addr il ls2)` >>
    `∃ls1. ls = ls2 ++ ls1` by (
      rw[Abbr`ls2`,Abbr`ls`] ) >>
    pop_assum SUBST1_TAC >>
    match_mp_tac bc_find_loc_aux_append_code >>
    match_mp_tac bc_find_loc_aux_ALL_DISTINCT >>
    `ALL_DISTINCT (FILTER is_Label ls2)` by (
      fs[ALL_DISTINCT_APPEND,FILTER_APPEND] ) >>
    qunabbrev_tac`ls2` >>
    Q.PAT_ABBREV_TAC`ls2 = X ++ REVERSE be2k` >>
    qexists_tac`LENGTH ls2` >>
    lrw[EL_APPEND2,TAKE_APPEND2,FILTER_APPEND] ) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    simp[] >>
    simp[code_for_push_def,compile_def] >>
    rw[Once SWAP_REVERSE] >>
    map_every qexists_tac[`bs.refs`,`rd`] >>
    rw[RTC_eq_NRC] >>
    TRY (qexists_tac`0` >>rw[]) >>
    TRY (qmatch_abbrev_tac `Cenv_bs rd A B C D E` >>
         qmatch_assum_abbrev_tac `Cenv_bs rd A B C D E'` >>
         qsuff_tac`E = E'`>-rw[] >>
         unabbrev_all_tac) >>
    rw[bc_state_component_equality]) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    rpt gen_tac >> strip_tac >>
    simp[compile_def] >> strip_tac >>
    qspecl_then[`cenv`,`TCNonTail`,`sz`,`cs`,`exp`]mp_tac(CONJUNCT1 compile_append_out) >>
    disch_then(Q.X_CHOOSE_THEN`be`strip_assume_tac) >>
    qmatch_assum_abbrev_tac`cs0.out = be ++ cs.out` >>
    qspecl_then[`cenv`,`sz+1`,`cs0`,`exps`]mp_tac(CONJUNCT2(CONJUNCT2 compile_append_out)) >>
    disch_then(Q.X_CHOOSE_THEN`bes`strip_assume_tac) >>
    POP_ASSUM_LIST(MAP_EVERY ASSUME_TAC) >>
    first_x_assum(qspecl_then[`rd`,`s'`,`v`,`cs`,`cenv`,`sz`,`bs`,`bce`,`bcr`,`bc0`]mp_tac) >>
    `LENGTH s ≤ LENGTH s' ∧ LENGTH s' ≤ LENGTH s''` by metis_tac[Cevaluate_store_SUBSET,FST] >>
    simp[] >>
    fs[ALL_DISTINCT_APPEND] >>
    fs[Once SWAP_REVERSE] >>
    rfs[Abbr`cs0`] >>
    fs[REVERSE_APPEND] >>
    disch_then(mp_tac o CONJUNCT1) >>
    `code = REVERSE be ++ REVERSE bes` by (
      PROVE_TAC[SWAP_REVERSE,REVERSE_APPEND] ) >>
    fs[] >>
    simp[code_for_push_def] >>
    fsrw_tac[DNF_ss][] >>
    map_every qx_gen_tac[`rfs`,`rd'`,`bv`] >>
    strip_tac >>
    qmatch_assum_abbrev_tac`bc_next^* bs bs1` >>
    qmatch_assum_abbrev_tac`cs0.out = be ++ cs.out` >>
    first_x_assum(qspecl_then[`rd'`,`cs0`,`cenv`,`sz+1`,`bs1`,`bce`,`bcr`,`bc0 ++ REVERSE be`,`REVERSE bes`]mp_tac) >>
    simp[Abbr`bs1`] >>
    qmatch_abbrev_tac `(P ⇒ Q) ⇒ R` >>
    `P` by (
      map_every qunabbrev_tac[`P`,`Q`,`R`] >>
      conj_tac >- PROVE_TAC[SUBSET_DEF,IN_COUNT,LESS_LESS_EQ_TRANS] >>
      conj_tac >- PROVE_TAC[Cevaluate_Clocs,FST] >>
      qspecl_then[`s`,`env`,`exp`,`(s',Cval v)`]mp_tac(CONJUNCT1 Cevaluate_vlabs) >>
      simp[] >> strip_tac >>
      qspecl_then[`s`,`env`,`exp`,`(s',Cval v)`]mp_tac(CONJUNCT1 Cevaluate_all_vlabs) >>
      simp[] >> strip_tac >>
      conj_tac >- ( fsrw_tac[DNF_ss][SUBSET_DEF,EVERY_MEM] >> metis_tac[] ) >>
      match_mp_tac compile_labels_lemma >> fs[Abbr`cs0`] >>
      map_every qexists_tac[`cenv`,`TCNonTail`,`sz`,`cs`,`exp`,`bc0`] >>
      simp[]) >>
    map_every qunabbrev_tac[`P`,`Q`,`R`] >> fs[] >>
    simp[code_for_push_def] >>
    fsrw_tac[DNF_ss][] >>
    map_every qx_gen_tac[`bvs`,`rf`,`rd''`] >>
    strip_tac >>
    map_every qexists_tac[`bv::bvs`,`rf`,`rd''`] >>
    qmatch_assum_abbrev_tac`bc_next^* bs bs1` >>
    qmatch_assum_abbrev_tac`bc_next^* bs1 bs2` >>
    conj_tac >- (
      qmatch_abbrev_tac `bc_next^* bs bs3` >>
      qsuff_tac `bs2 = bs3` >- metis_tac[RTC_TRANSITIVE,transitive_def] >>
      rw[Abbr`bs2`,Abbr`bs3`,bc_state_component_equality,REVERSE_APPEND] ) >>
    qpat_assum`X = vs'`(assume_tac o SYM) >>
    fsrw_tac[ARITH_ss][EVERY2_EVERY,ADD1] >> rfs[] >>
    conj_tac >- (
      match_mp_tac (MP_CANON (GEN_ALL (CONJUNCT1 (SPEC_ALL Cv_bv_SUBMAP)))) >> simp[] >>
      qexists_tac `rd'` >>
      simp[] >>
      fs[SUBMAP_DEF,DRESTRICT_DEF,Cenv_bs_def,s_refs_def,good_rd_def,UNCURRY,FEVERY_DEF] ) >>
    conj_tac >- (
      qmatch_abbrev_tac `Cenv_bs rd'' s2 renv env0 sz0 bsx` >>
      qmatch_assum_abbrev_tac `Cenv_bs rd'' s2 renv env0 sz0 bsy` >>
      `bsx = bsy` by (
        rw[Abbr`bsx`,Abbr`bsy`,bc_state_component_equality,REVERSE_APPEND] ) >>
      rw[] ) >>
    metis_tac[SUBMAP_TRANS,IS_PREFIX_TRANS]) >>
  strip_tac >- rw[] >>
  rw[] )

val label_closures_thm = store_thm("label_closures_thm",
  ``(∀ez j e. (no_labs e) ∧ set (free_vars e) ⊆ count ez ⇒
     let (e',j') = label_closures ez j e in
     (j' = j + (LENGTH (free_labs ez e'))) ∧
     (MAP (FST o FST o SND) (free_labs ez e') = (GENLIST ($+ j) (LENGTH (free_labs ez e')))) ∧
     set (free_vars e') ⊆ set (free_vars e) ∧
     all_labs e' ∧ EVERY good_cd (free_labs ez e') ∧
     syneq_exp ez ez $= e e') ∧
    (∀ez j es.
     (no_labs_list es) ∧ set (free_vars_list es) ⊆ count ez ⇒
     let (es',j') = label_closures_list ez j es in
     (j' = j + LENGTH (free_labs_list ez es')) ∧
     (MAP (FST o FST o SND) (free_labs_list ez es') = (GENLIST ($+ j) (LENGTH (free_labs_list ez es')))) ∧
     set (free_vars_list es') ⊆ set (free_vars_list es) ∧
     all_labs_list es' ∧ EVERY good_cd (free_labs_list ez es') ∧
     EVERY2 (syneq_exp ez ez $=) es es') ∧
    (∀ez j nz k defs ds0 ls0.
     (no_labs_defs (ls0 ++ MAP ($, NONE) defs)) ∧
     set (free_vars_defs nz (MAP ($, NONE) defs)) ⊆ count ez ∧
     (LENGTH ds0 = k) ∧ (LENGTH defs = nz - k) ∧ k ≤ nz ∧ (LENGTH ls0 = k) ∧
     syneq_defs ez ez $= (ls0 ++ MAP ($, NONE) defs) (ds0 ++ MAP ($, NONE) defs) (λv1 v2. v1 < nz ∧ (v2 = v1))
     ⇒
     let (defs',j') = label_closures_defs ez j nz k defs in
     (j' = j + LENGTH (free_labs_defs ez nz k defs')) ∧
     (MAP (FST o FST o SND) (free_labs_defs ez nz k defs') = GENLIST ($+ j) (LENGTH (free_labs_defs ez nz k defs'))) ∧
     set (free_vars_defs nz defs') ⊆ set (free_vars_defs nz (MAP ($, NONE) defs)) ∧
     (LENGTH defs' = LENGTH defs) ∧
     all_labs_defs defs' ∧
     EVERY good_cd (free_labs_defs ez nz k defs') ∧
     syneq_defs ez ez $= (ls0 ++ (MAP ($, NONE) defs)) (ds0 ++ defs') (λv1 v2. v1 < nz ∧ (v2 = v1)))``,
  ho_match_mp_tac label_closures_ind >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >> strip_tac >>
    fs[LET_THM,UNCURRY] >>
    simp[Once syneq_exp_cases] ) >>
  strip_tac >- (
    ntac 2 gen_tac >>
    map_every qx_gen_tac[`e1`,`e2`] >>
    rpt strip_tac >> fs[] >>
    `set (free_vars e2) ⊆ count (ez + 1)` by (
      fsrw_tac[DNF_ss,ARITH_ss][SUBSET_DEF,PRE_SUB1] >>
      Cases>>fsrw_tac[ARITH_ss][] ) >> fs[] >>
    qabbrev_tac`p = label_closures ez j e1` >> PairCases_on`p`>>fs[LET_THM] >>
    qabbrev_tac`q = label_closures (ez+1) (j + LENGTH (free_labs ez p0)) e2` >> PairCases_on`q`>>fs[] >>
    simp[LIST_EQ_REWRITE] >>
    conj_tac >- (
      gen_tac >>
      Cases_on`x<LENGTH (free_labs ez p0)`>>
      lrw[EL_APPEND1,EL_APPEND2] ) >>
    rfs[] >>
    conj_tac >- (
      fsrw_tac[DNF_ss,ARITH_ss][SUBSET_DEF,PRE_SUB1] >>
      Cases >> rw[ADD1] >>
      res_tac >>
      disj2_tac >> HINT_EXISTS_TAC >>
      fsrw_tac[ARITH_ss][] ) >>
    simp[Once syneq_exp_cases] >>
    match_mp_tac (MP_CANON (CONJUNCT1 syneq_exp_mono_V)) >>
    HINT_EXISTS_TAC >>
    simp[]) >>
  strip_tac >- (rw[] >> rw[syneq_exp_refl]) >>
  strip_tac >- (rw[] >> rw[syneq_exp_refl]) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >> strip_tac >>
    fs[LET_THM,UNCURRY] >>
    simp[Once syneq_exp_cases] ) >>
  strip_tac >- (
    rw[] >> fs[LET_THM] >>
    rw[Once syneq_exp_cases] >> rfs[]) >>
  strip_tac >- (
    rw[] >> fs[LET_THM] >>
    rw[Once syneq_exp_cases] >> rfs[]) >>
  strip_tac >- (
    ntac 2 gen_tac >>
    map_every qx_gen_tac[`e1`,`e2`] >>
    rpt strip_tac >> fs[] >>
    `set (free_vars e2) ⊆ count (ez + 1)` by (
      fsrw_tac[DNF_ss,ARITH_ss][SUBSET_DEF,PRE_SUB1] >>
      Cases>>fsrw_tac[ARITH_ss][] ) >> fs[] >>
    qabbrev_tac`p = label_closures ez j e1` >> PairCases_on`p`>>fs[LET_THM] >>
    qabbrev_tac`q = label_closures (ez+1) (j + LENGTH (free_labs ez p0)) e2` >> PairCases_on`q`>>fs[] >>
    simp[LIST_EQ_REWRITE] >>
    conj_tac >- (
      gen_tac >>
      Cases_on`x<LENGTH (free_labs ez p0)`>>
      lrw[EL_APPEND1,EL_APPEND2] ) >>
    rfs[] >>
    conj_tac >- (
      fsrw_tac[DNF_ss,ARITH_ss][SUBSET_DEF,PRE_SUB1] >>
      Cases >> rw[ADD1] >>
      res_tac >>
      disj2_tac >> HINT_EXISTS_TAC >>
      fsrw_tac[ARITH_ss][] ) >>
    simp[Once syneq_exp_cases] >>
    match_mp_tac (MP_CANON (CONJUNCT1 syneq_exp_mono_V)) >>
    HINT_EXISTS_TAC >>
    simp[]) >>
  strip_tac >- (
    rpt strip_tac >>
    simp[] >>
    `FILTER (IS_NONE o FST) defs = defs` by (
      simp[FILTER_EQ_ID] >>
      fs[FLAT_EQ_NIL,EVERY_MAP] >>
      fs[EVERY_MEM,FORALL_PROD] >>
      qx_gen_tac`z` >> rpt strip_tac >>
      res_tac >> Cases_on`z`>>fs[] ) >>
    full_simp_tac std_ss [LET_THM] >>
    full_simp_tac std_ss [FILTER_EQ_ID,LENGTH_MAP] >>
    qabbrev_tac`p = label_closures_defs ez j (LENGTH defs) 0 (MAP SND defs)` >>
    PairCases_on`p`>>
    `no_labs e`by fs[] >>
    `set (free_vars e) ⊆ count (ez + LENGTH defs)` by (
      qpat_assum`set (free_vars X) ⊆ Y`mp_tac >>
      rpt (pop_assum kall_tac) >>
      fsrw_tac[DNF_ss,ARITH_ss][SUBSET_DEF,LET_THM] >>
      srw_tac[ARITH_ss][ADD1] >>
      res_tac >> fsrw_tac[ARITH_ss][] ) >>
    full_simp_tac std_ss [] >>
    qabbrev_tac`q = label_closures (ez + LENGTH defs) p1 e` >>
    PairCases_on`q` >>
    full_simp_tac std_ss [] >>
    `MAP ($, NONE) (MAP SND defs) = defs` by (
      fs[EVERY_MEM] >>
      lrw[MAP_MAP_o] >>
      CONV_TAC(RAND_CONV(REWRITE_CONV[Once (CONJUNCT2 (GSYM MAP_ID)),SimpRHS])) >>
      lrw[MAP_EQ_f,FORALL_PROD] >> res_tac >> fs[]) >>
    full_simp_tac std_ss [] >>
    first_x_assum(qspecl_then[`[]`,`[]`]mp_tac) >>
    simp[syneq_defs_refl,EVERY_MAP] >>
    fs[LET_THM] >>
    strip_tac >>
    fsrw_tac[ETA_ss][] >>
    rfs[] >> simp[] >>
    conj_tac >- (
      lrw[LIST_EQ_REWRITE] >>
      Cases_on`x < LENGTH (free_labs_defs ez (LENGTH defs) 0 p0)` >>
      lrw[EL_APPEND1,EL_APPEND2] ) >>
    conj_tac >- (
      fsrw_tac[DNF_ss][SUBSET_DEF,MEM_MAP,free_vars_defs_MAP] >>
      gen_tac >> strip_tac >>
      disj2_tac >>
      qexists_tac`m` >>
      simp[] ) >>
    simp[Once syneq_exp_cases] >>
    HINT_EXISTS_TAC >> simp[] >>
    match_mp_tac (MP_CANON (CONJUNCT1 syneq_exp_mono_V)) >>
    HINT_EXISTS_TAC >>
    simp[]) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >> strip_tac >>
    first_x_assum(qspecl_then[`[]`,`[]`]mp_tac) >>
    simp[] >>
    discharge_hyps >- (
      simp[syneq_defs_refl] >>
      PairCases_on`def`>>fs[]) >>
    qabbrev_tac`p = label_closures_defs ez j 1 0 [def]` >>
    PairCases_on`p` >>
    full_simp_tac std_ss [] >>
    strip_tac >>
    Cases_on`p0`>>fs[]>>
    Cases_on`t`>>fs[]>>
    PairCases_on`h`>>PairCases_on`def`>>fs[]>>
    simp[Once syneq_exp_cases] >> fs[] >>
    HINT_EXISTS_TAC >>
    simp[] ) >>
  strip_tac >- (
    rw[] >> PairCases_on`x`>>fs[]>>
    PairCases_on`y`>>fs[]) >>
  strip_tac >- (
    ntac 2 gen_tac >>
    map_every qx_gen_tac[`e`,`es`] >>
    rpt strip_tac >>
    qabbrev_tac`p = label_closures ez j e` >> PairCases_on`p`>>fs[LET_THM] >>
    qabbrev_tac`q = label_closures_list ez (j + LENGTH (free_labs ez p0)) es` >> PairCases_on`q`>>fs[] >>
    fs[] >>
    simp[LIST_EQ_REWRITE] >>
    conj_tac >- (
      gen_tac >>
      Cases_on`x<LENGTH (free_labs ez p0)`>>
      lrw[EL_APPEND1,EL_APPEND2] ) >>
    rfs[] >>
    conj_tac >- (
      fsrw_tac[DNF_ss][SUBSET_DEF] ) >>
    simp[Once syneq_exp_cases]) >>
  strip_tac >- (
    rw[] >> fs[LET_THM] >> rfs[] >>
    simp[Once syneq_exp_cases] ) >>
  strip_tac >- (
    ntac 2 gen_tac >>
    map_every qx_gen_tac[`p2`,`e1`,`e2`] >>
    rpt strip_tac >> fs[] >>
    qabbrev_tac`p = label_closures ez j e1` >> PairCases_on`p`>>fs[LET_THM] >>
    qabbrev_tac`q = label_closures ez (j + LENGTH (free_labs ez p0)) e2` >> PairCases_on`q`>>fs[] >>
    simp[LIST_EQ_REWRITE] >>
    conj_tac >- (
      gen_tac >> strip_tac >>
      Cases_on`x < LENGTH (free_labs ez p0)`>>
      lrw[EL_APPEND1,EL_APPEND2]) >>
    conj_tac >- (
      rfs[] >>
      fsrw_tac[DNF_ss][SUBSET_DEF] ) >>
    simp[Once syneq_exp_cases]) >>
  strip_tac >- (
    ntac 2 gen_tac >>
    map_every qx_gen_tac[`e1`,`e2`] >>
    rpt strip_tac >> fs[] >>
    qabbrev_tac`p = label_closures ez j e1` >> PairCases_on`p`>>fs[LET_THM] >>
    qabbrev_tac`q = label_closures ez (j + LENGTH (free_labs ez p0)) e2` >> PairCases_on`q`>>fs[] >>
    simp[LIST_EQ_REWRITE] >>
    conj_tac >- (
      gen_tac >> strip_tac >>
      Cases_on`x < LENGTH (free_labs ez p0)`>>
      lrw[EL_APPEND1,EL_APPEND2]) >>
    conj_tac >- (
      rfs[] >>
      fsrw_tac[DNF_ss][SUBSET_DEF] ) >>
    simp[Once syneq_exp_cases]) >>
  strip_tac >- (
    ntac 2 gen_tac >>
    map_every qx_gen_tac[`e1`,`e2`,`e3`] >>
    rpt strip_tac >> fs[] >>
    qabbrev_tac`p = label_closures ez j e1` >> PairCases_on`p`>>fs[LET_THM] >>
    qabbrev_tac`q = label_closures ez (j + LENGTH (free_labs ez p0)) e2` >> PairCases_on`q`>>fs[] >>
    qabbrev_tac`r = label_closures ez (j + LENGTH (free_labs ez p0) + LENGTH (free_labs ez q0)) e3` >> PairCases_on`r`>>fs[] >>
    simp[LIST_EQ_REWRITE] >>
    conj_tac >- (
      gen_tac >> strip_tac >>
      Cases_on`x < LENGTH (free_labs ez p0)`>>
      lrw[EL_APPEND1,EL_APPEND2] >>
      Cases_on`x < LENGTH (free_labs ez p0) + LENGTH (free_labs ez q0)` >>
      lrw[EL_APPEND1,EL_APPEND2] ) >>
    conj_tac >- (
      rfs[] >>
      fsrw_tac[DNF_ss,ARITH_ss][SUBSET_DEF,MEM_GENLIST] ) >>
    simp[Once syneq_exp_cases]) >>
  strip_tac >- simp[] >>
  strip_tac >- (
    rpt strip_tac >>
    fs[] >>
    qabbrev_tac`p = label_closures ez j e` >>
    PairCases_on`p`>>fs[LET_THM] >>
    qabbrev_tac`q = label_closures_list ez (j + LENGTH (free_labs ez p0)) es` >>
    PairCases_on`q`>>fs[] >> simp[] >> rfs[] >>
    conj_tac >- (
      lrw[LIST_EQ_REWRITE] >>
      Cases_on`x < LENGTH (free_labs ez p0)`>>
      lrw[EL_APPEND1,EL_APPEND2] ) >>
    conj_tac >- (
      fsrw_tac[DNF_ss][SUBSET_DEF] ) >>
    fsrw_tac[DNF_ss][SUBSET_DEF] ) >>
  strip_tac >- (
    simp[] >> rw[FUNION_FEMPTY_2] >>
    fs[LENGTH_NIL]) >>
  rpt gen_tac >> rpt strip_tac >>
  full_simp_tac (std_ss++ARITH_ss) [] >>
  last_x_assum mp_tac >>
  last_x_assum mp_tac >>
  simp[] >> ntac 2 strip_tac >>
  Q.PAT_ABBREV_TAC`r = bind_fv X Y Z` >>
  PairCases_on`r`>>fs[] >>
  Q.PAT_ABBREV_TAC`ezz:num = az + (X + (Y + 1))` >>
  qabbrev_tac`p = label_closures ezz (j+1) r3` >>
  PairCases_on`p` >> full_simp_tac std_ss [] >>
  qabbrev_tac`q = label_closures_defs ez p1 nz (k+1) defs` >>
  PairCases_on`q` >> full_simp_tac std_ss [] >>
  `no_labs r3` by (
    fs[bind_fv_def,LET_THM,markerTheory.Abbrev_def] ) >>
  `set (free_vars r3) ⊆ count ezz` by (
    fs[bind_fv_def,LET_THM,markerTheory.Abbrev_def] >>
    first_x_assum(qspec_then`[]`kall_tac) >>
    qpat_assum`P⇒Q`kall_tac >>
    fsrw_tac[DNF_ss][SUBSET_DEF] >>
    srw_tac[ARITH_ss][] >- (
      qho_match_abbrev_tac`(the n (find_index x ls n)) < y` >>
      qho_match_abbrev_tac`P (the n (find_index x ls n))` >>
      ho_match_mp_tac the_find_index_suff >>
      simp[Abbr`P`,Abbr`x`,Abbr`ls`,MEM_FILTER,ADD1,MEM_GENLIST,Abbr`n`,Abbr`y`] >>
      rw[] >>
      qmatch_abbrev_tac`m < A + B` >>
      Cases_on`m=A`>>fsrw_tac[ARITH_ss][]>>
      Cases_on`B=0`>>fsrw_tac[ARITH_ss][]>>
      fs[LENGTH_NIL_SYM,FILTER_EQ_NIL,EVERY_MEM,QSORT_MEM,markerTheory.Abbrev_def] >>
      res_tac >> fsrw_tac[ARITH_ss][]) >>
    qho_match_abbrev_tac`(the 0 (find_index x ls n)) < y` >>
    qho_match_abbrev_tac`P (the 0 (find_index x ls n))` >>
    ho_match_mp_tac the_find_index_suff >>
    `n ≤ nz` by (
      unabbrev_all_tac >>
      simp[GSYM ADD1] >>
      simp[GSYM LESS_EQ] >>
      qmatch_abbrev_tac`LENGTH (FILTER P ls) < nz` >>
      `nz = LENGTH ls` by rw[Abbr`ls`] >> pop_assum SUBST1_TAC >>
      match_mp_tac LENGTH_FILTER_LESS >>
      simp[Abbr`P`,Abbr`ls`,EXISTS_MEM,MEM_GENLIST] >>
      qexists_tac`LENGTH ls0` >>
      simp[] ) >>
    reverse conj_tac >- (
      unabbrev_all_tac >>
      simp[MEM_MAP,MEM_FILTER,sortingTheory.QSORT_MEM] >>
      qexists_tac`v` >> simp[] ) >>
    simp[Abbr`P`,Abbr`y`] >>
    qx_gen_tac`m`>>strip_tac >>
    qmatch_abbrev_tac`m + n < l1 + l2` >>
    `l2 = LENGTH ls + 1` by rw[Abbr`l2`,Abbr`ls`] >> rw[] >>
    qsuff_tac`n ≤ l1 + 1` >- DECIDE_TAC >>
    simp[Abbr`n`]) >>
  full_simp_tac std_ss [LET_THM] >>
  Q.PAT_ABBREV_TAC`cd:def = (SOME X,az,p0)` >>
  last_x_assum(qspecl_then[`ds0++[cd]`,`ls0++[(NONE,az,b)]`]mp_tac) >>
  discharge_hyps >- (
    simp[] >>
    rator_x_assum`syneq_defs`mp_tac >>
    simp[Once syneq_exp_cases] >>
    simp[EVERY_MAP] >> strip_tac >>
    simp[Once syneq_exp_cases,EVERY_MAP] >>
    qx_gen_tac`v` >> strip_tac >>
    first_x_assum(qspec_then`v`mp_tac) >> simp[] >>
    REWRITE_TAC[GSYM APPEND_ASSOC] >>
    Cases_on`v < k`>>simp[EL_APPEND1,EL_APPEND2,ADD1,EL_MAP] >- (
      strip_tac >>
      ntac 2 (first_x_assum (mp_tac o SYM)) >>
      ntac 2 strip_tac >>
      fsrw_tac[ARITH_ss][ADD1] ) >>
    Cases_on`v=k` >- (
      simp[Abbr`cd`] >> strip_tac >>
      simp[syneq_cb_aux_def] >>
      fsrw_tac[ARITH_ss][ADD1] >>
      simp[syneq_cb_aux_def] >>
      conj_asm1_tac >- (
        fs[bind_fv_def,LET_THM,markerTheory.Abbrev_def] >>
        simp[EVERY_MEM,MEM_MAP,MEM_FILTER,QSORT_MEM,MEM_FILTER,MEM_GENLIST] >>
        simp[GSYM LEFT_FORALL_IMP_THM] >>
        qpat_assum`Y ⊆ count ez` mp_tac >>
        qpat_assum`Y ⊆ count ez` mp_tac >>
        simp[SUBSET_DEF,GSYM LEFT_FORALL_IMP_THM] >>
        srw_tac[DNF_ss,ARITH_ss][NOT_LESS] >>
        metis_tac[] ) >>
      qmatch_abbrev_tac`syneq_exp z1 ezz V b p0` >>
      qsuff_tac`syneq_exp z1 ezz V b r3` >- (
        strip_tac >>
        `V = $= O V` by metis_tac[Id_O] >> pop_assum SUBST1_TAC >>
        match_mp_tac (MP_CANON (CONJUNCT1 syneq_exp_trans)) >>
        PROVE_TAC[] ) >>
      qpat_assum`Abbrev(X = bind_fv A Y Z)`mp_tac >>
      simp[bind_fv_def,markerTheory.Abbrev_def] >> rw[] >>
      match_mp_tac mkshift_thm >>
      simp[Abbr`z1`,Abbr`ezz`] >>
      conj_tac >- simp[Abbr`V`,syneq_cb_V_def] >>
      reverse conj_tac >- (
        qpat_assum`Y ⊆ count ez`mp_tac >>
        qpat_assum`Y ⊆ count ez`mp_tac >>
        simp[SUBSET_DEF,GSYM LEFT_FORALL_IMP_THM] >>
        srw_tac[DNF_ss,ARITH_ss][NOT_LESS] >>
        Cases_on`az + nz ≤ x`>>simp[]) >>
      gen_tac >> strip_tac >>
      reverse conj_tac >- (
        rw[] >- (
          qho_match_abbrev_tac`the 0 (find_index a w c) < X` >>
          qunabbrev_tac`X` >>
          qho_match_abbrev_tac`P (the c (find_index a w c))` >>
          match_mp_tac the_find_index_suff >>
          reverse conj_tac >- (
            unabbrev_all_tac >>
            fs[SUBSET_DEF] >>
            simp[MEM_FILTER,MEM_GENLIST] ) >>
          simp[Abbr`w`,Abbr`c`,Abbr`P`]) >>
        qho_match_abbrev_tac`the 0 (find_index a w c) < X` >>
        qunabbrev_tac`X` >>
        qho_match_abbrev_tac`P (the 0 (find_index a w c))` >>
        match_mp_tac the_find_index_suff >>
        reverse conj_tac >- (
          unabbrev_all_tac >>
          simp[MEM_MAP,MEM_FILTER,QSORT_MEM] >>
          qexists_tac`x`>>simp[]) >>
        simp[Abbr`w`,Abbr`c`,Abbr`P`]) >>
      Q.PAT_ABBREV_TAC`envs:num list = MAP X (FILTER Y Z)` >>
      `¬(x < az + nz) ⇒ MEM (x-(az+nz)) envs` by (
        simp[Abbr`envs`,MEM_MAP,MEM_FILTER,QSORT_MEM] >>
        strip_tac >>
        qexists_tac`x` >> simp[] ) >>
      Q.PAT_ABBREV_TAC`recs = LENGTH ls0::X` >>
      `x < az + nz ⇒ MEM (x - az) recs` by (
        simp[Abbr`recs`,MEM_FILTER,MEM_GENLIST] ) >>
      simp[Abbr`V`] >>
      reverse(rw[]) >- (
        fs[] >>
        simp[syneq_cb_V_def] >>
        Q.PAT_ABBREV_TAC`rz = LENGTH (FILTER X Y) + 1` >>
        Q.ISPECL_THEN[`envs`,`x-(az+nz)`,`rz`]mp_tac find_index_MEM >>
        simp[] >> disch_then strip_assume_tac >> simp[] >>
        simp[Abbr`rz`] ) >>
      simp[syneq_cb_V_def] >> fs[] >>
      Q.ISPECL_THEN[`recs`,`x-az`,`0:num`]mp_tac find_index_MEM >>
      simp[] >> disch_then strip_assume_tac >> simp[] >>
      Cases_on`i=0` >- (
        simp[] >> fs[Abbr`recs`]) >>
      simp[] >>
      qpat_assum`EL X Y = x - def0`mp_tac >>
      simp[Abbr`recs`,EL_CONS,PRE_SUB1] >>
      fsrw_tac[ARITH_ss][]) >>
    lrw[EL_CONS] >>
    ntac 2 (qpat_assum`X = Y`(mp_tac o SYM)) >>
    simp[PRE_SUB1,EL_MAP] >>
    Q.PAT_ABBREV_TAC`p = EL X defs` >>
    PairCases_on`p` >>
    simp[syneq_cb_aux_def] >>
    ntac 2 strip_tac >>
    fsrw_tac[ARITH_ss][] >> rw[] >> fs[] >>
    fsrw_tac[ARITH_ss][ADD1] >>
    `LENGTH defs + (LENGTH ls0 + 1) = nz` by simp[] >>
    pop_assum SUBST1_TAC >>
    match_mp_tac (MP_CANON(CONJUNCT1 syneq_exp_mono_V)) >>
    HINT_EXISTS_TAC >>
    simp[]) >>
  simp[] >> strip_tac >>
  simp[Abbr`cd`,ADD1]>>
  conj_tac >- (
    fsrw_tac[ARITH_ss][] >>
    lrw[LIST_EQ_REWRITE,EL_CONS,ADD1] >>
    Cases_on`x=0` >> lrw[EL_CONS,PRE_SUB1] >>
    Cases_on`x < LENGTH (free_labs ezz p0)` >>
    lrw[EL_APPEND1,EL_APPEND2] >>
    Cases_on `x-1 < LENGTH (free_labs ezz p0)` >>
    lrw[EL_APPEND1,EL_APPEND2]) >>
  conj_tac >- (
    rev_full_simp_tac std_ss [] >>
    fsrw_tac[DNF_ss][SUBSET_DEF] ) >>
  reverse conj_tac >-
    metis_tac[CONS_APPEND,APPEND_ASSOC] >>
  simp[good_cd_def] >>
  conj_tac >- (
    fs[bind_fv_def,LET_THM,markerTheory.Abbrev_def] >>
    simp[EVERY_MAP,EVERY_FILTER] >>
    simp[EVERY_MEM,QSORT_MEM] >>
    qpat_assum`Y ⊆ count ez` mp_tac >>
    qpat_assum`Y ⊆ count ez` mp_tac >>
    srw_tac[DNF_ss][SUBSET_DEF] >>
    res_tac >> fsrw_tac[ARITH_ss][] ) >>
  conj_tac >- (
    fs[bind_fv_def,LET_THM,markerTheory.Abbrev_def] >>
    qpat_assum`set (free_vars p0) ⊆ X`mp_tac >>
    simp[SUBSET_DEF] >> strip_tac >>
    gen_tac >> strip_tac >>
    first_x_assum(qspec_then`x`mp_tac) >>
    simp[] >> strip_tac >>
    Cases_on`v<az`>>fsrw_tac[ARITH_ss][]>>
    Cases_on`v<az+nz`>>fsrw_tac[ARITH_ss][]>- (
      qho_match_abbrev_tac`the 0 (find_index a ls n) < X` >>
      qho_match_abbrev_tac`P (the n (find_index a ls n))` >>
      match_mp_tac the_find_index_suff >>
      simp[Abbr`ls`,Abbr`P`,Abbr`X`,MEM_FILTER,MEM_GENLIST,Abbr`n`,Abbr`a`,MEM_MAP,QSORT_MEM] ) >>
    rw[] >>
    qho_match_abbrev_tac`the 0 (find_index a ls n) < X` >>
    qho_match_abbrev_tac`P (the 0 (find_index a ls n))` >>
    match_mp_tac the_find_index_suff >>
    simp[Abbr`ls`,Abbr`P`,Abbr`X`,MEM_FILTER,MEM_GENLIST,Abbr`n`,Abbr`a`,MEM_MAP,QSORT_MEM] >>
    HINT_EXISTS_TAC >> simp[] ) >>
  map_every qexists_tac[`b`,`r3`] >>
  simp[])

val _ = export_theory ()
