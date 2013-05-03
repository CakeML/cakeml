open HolKernel bossLib boolLib boolSimps listTheory rich_listTheory pred_setTheory relationTheory arithmeticTheory whileTheory pairTheory quantHeuristicsLib lcsymtacs
open miniMLExtraTheory miscTheory intLangTheory expToCexpTheory compileTerminationTheory compileCorrectnessTheory bytecodeTerminationTheory bytecodeExtraTheory bytecodeEvalTheory pmatchTheory  labelClosuresTheory
open miscLib MiniMLTerminationTheory finite_mapTheory sortingTheory SatisfySimps
val _ = new_theory"repl"

val good_contab_def = Define`
  good_contab (m,w,n) =
    fmap_linv m w`

val env_rs_def = Define`
  env_rs env rs rd s bs =
    (rs.rbvars = MAP FST env) ∧
    let Cenv = env_to_Cenv (cmap rs.contab) env in
    Cenv_bs rd s Cenv rs.renv rs.rsz bs`

val transitive_LESS = store_thm("transitive_LESS",
  ``transitive ($< : (num->num->bool))``,
  rw[transitive_def] >> PROVE_TAC[LESS_TRANS])
val _ = export_rewrites["transitive_LESS"]

val FOLDL_cce_aux_thm = store_thm("FOLDL_cce_aux_thm",
  ``∀c s. let s' = FOLDL cce_aux s c in
     ALL_DISTINCT (MAP (FST o FST) c) ∧
     EVERY (combin$C $< s.next_label) (MAP (FST o FST) c)
      ⇒
     ∃code.
     (s'.out = REVERSE code ++ s.out) ∧
     (s.next_label ≤ s'.next_label) ∧
     ALL_DISTINCT (FILTER is_Label code) ∧
     EVERY (λn. MEM n (MAP (FST o FST) c) ∨ between s.next_label s'.next_label n)
       (MAP dest_Label (FILTER is_Label code)) ∧
     ∃cs.
     ∀i. i < LENGTH c ⇒ let ((l,ccenv,ce),(az,body)) = EL i c in
         s.next_label ≤ (cs i).next_label ∧
         (∀j. j < i ⇒ (cs j).next_label ≤ (cs i).next_label) ∧
         ∃cc. ((compile (MAP CTEnv ccenv) (TCTail az 0) 0 (cs i) body).out = cc ++ (cs i).out) ∧
              l < (cs i).next_label ∧
              ∃bc0 bc1. (code = bc0 ++ Label l::REVERSE cc ++ bc1) ∧
                        EVERY (combin$C $< (cs i).next_label o dest_Label)
                          (FILTER is_Label bc0)``,
   Induct >- ( simp[Once SWAP_REVERSE] ) >>
   simp[] >>
   qx_gen_tac`p`>> PairCases_on`p` >>
   rpt gen_tac >>
   simp[cce_aux_def] >>
   strip_tac >>
   Q.PAT_ABBREV_TAC`s0 = s with out := X::y` >>
   qspecl_then[`MAP CTEnv p1`,`TCTail p3 0`,`0`,`s0`,`p4`]
     strip_assume_tac(CONJUNCT1 compile_append_out) >>
   Q.PAT_ABBREV_TAC`s1 = compile X Y Z A B` >>
   first_x_assum(qspecl_then[`s1`]mp_tac) >>
   simp[] >>
   discharge_hyps >- (
     fsrw_tac[ARITH_ss][EVERY_MEM,Abbr`s0`] >>
     rw[] >> res_tac >> DECIDE_TAC ) >>
   disch_then(Q.X_CHOOSE_THEN`c0`strip_assume_tac) >>
   simp[Abbr`s0`] >>
   simp[Once SWAP_REVERSE] >>
   fs[] >> simp[] >>
   simp[FILTER_APPEND,FILTER_REVERSE,MEM_FILTER,ALL_DISTINCT_REVERSE,ALL_DISTINCT_APPEND] >>
   conj_tac >- (
     rfs[FILTER_APPEND] >>
     fs[EVERY_MAP,EVERY_FILTER,EVERY_REVERSE,between_def] >>
     fsrw_tac[DNF_ss,ARITH_ss][EVERY_MEM,MEM_MAP] >>
     rw[] >> spose_not_then strip_assume_tac >> res_tac >> fsrw_tac[ARITH_ss][]
       >- metis_tac[] >>
     res_tac >> fsrw_tac[ARITH_ss][] ) >>
   conj_tac >- (
     fs[EVERY_MAP,EVERY_REVERSE,EVERY_FILTER,is_Label_rwt,GSYM LEFT_FORALL_IMP_THM] >>
     fsrw_tac[DNF_ss][EVERY_MEM,between_def] >>
     rw[] >> spose_not_then strip_assume_tac >> res_tac >>
     fsrw_tac[ARITH_ss][] ) >>
   qexists_tac`λi. if i = 0 then (s with out := Label p0::s.out) else cs (i-1)` >>
   Cases >> simp[] >- (
     map_every qexists_tac[`[]`,`c0`] >> simp[] ) >>
   strip_tac >>
   first_x_assum(qspec_then`n`mp_tac) >>
   simp[UNCURRY] >> strip_tac >>
   simp[] >>
   conj_asm1_tac >- ( Cases >> simp[] ) >>
   qexists_tac`Label p0::(REVERSE bc ++ bc0)` >>
   simp[FILTER_APPEND,FILTER_REVERSE,EVERY_REVERSE,EVERY_FILTER,is_Label_rwt,GSYM LEFT_FORALL_IMP_THM] >>
   qpat_assum`EVERY X (FILTER is_Label bc0)`mp_tac >>
   qpat_assum`EVERY X (MAP Y (FILTER is_Label bc))`mp_tac >>
   simp[EVERY_FILTER,EVERY_MAP,is_Label_rwt,GSYM LEFT_FORALL_IMP_THM,between_def] >>
   asm_simp_tac(srw_ss()++ARITH_ss++DNF_ss)[EVERY_MEM] >>
   rw[] >> res_tac >> DECIDE_TAC)

val MAP_SND_free_labs_any_ez = store_thm("MAP_SND_free_labs_any_ez",
  ``(∀ez e ez'. MAP SND (free_labs ez e) = MAP SND (free_labs ez' e)) ∧
    (∀ez es ez'. MAP SND (free_labs_list ez es) = MAP SND (free_labs_list ez' es)) ∧
    (∀ez nz ix defs ez'. MAP SND (free_labs_defs ez nz ix defs) = MAP SND (free_labs_defs ez' nz ix defs)) ∧
    (∀ez nz ix def ez'. MAP SND (free_labs_def ez nz ix def) = MAP SND (free_labs_def ez' nz ix def))``,
  ho_match_mp_tac free_labs_ind >> rw[] >> metis_tac[])

val compile_code_env_thm = store_thm("compile_code_env_thm",
  ``∀ez s e. let s' = compile_code_env s e in
      ALL_DISTINCT (MAP (FST o FST o SND) (free_labs ez e)) ∧
      EVERY (combin$C $< s.next_label) (MAP (FST o FST o SND) (free_labs ez e)) ∧
      EVERY good_cd (free_labs ez e)
      ⇒
      ∃code.
      (s'.out = REVERSE code ++ s.out) ∧
      (s.next_label < s'.next_label) ∧
      ALL_DISTINCT (FILTER is_Label code) ∧
      EVERY (λn. MEM n (MAP (FST o FST o SND) (free_labs ez e)) ∨ between s.next_label s'.next_label n)
        (MAP dest_Label (FILTER is_Label code)) ∧
      ∀bs bc0 bc1.
        (bs.code = bc0 ++ code ++ bc1) ∧
        (bs.pc = next_addr bs.inst_length bc0) ∧
        ALL_DISTINCT (FILTER is_Label bc0) ∧
        (∀l1 l2. MEM l1 (MAP dest_Label (FILTER is_Label bc0)) ∧ ((l2 = s.next_label) ∨ MEM l2 (MAP (FST o FST o SND) (free_labs ez e))) ⇒ l1 < l2)
        ⇒
        EVERY (code_env_cd (bc0++code)) (free_labs ez e) ∧
        bc_next bs (bs with pc := next_addr bs.inst_length (bc0++code))``,
  rw[compile_code_env_def] >> rw[] >>
  `MAP SND (free_labs 0 e) = MAP SND (free_labs ez e)` by metis_tac[MAP_SND_free_labs_any_ez] >>
  fs[] >>
  Q.ISPECL_THEN[`MAP SND (free_labs ez e)`,`s''`]mp_tac FOLDL_cce_aux_thm >>
  simp[Abbr`s''`] >>
  discharge_hyps >- (
    fsrw_tac[ARITH_ss][EVERY_MEM,MAP_MAP_o] >>
    rw[] >> res_tac >> DECIDE_TAC ) >>
  disch_then(Q.X_CHOOSE_THEN`c0`strip_assume_tac) >>
  simp[Once SWAP_REVERSE,Abbr`s''''`] >>
  conj_tac >- (
    simp[ALL_DISTINCT_APPEND,FILTER_APPEND,MEM_FILTER,Abbr`l`] >>
    fs[EVERY_MAP,EVERY_FILTER] >> fs[EVERY_MEM] >>
    spose_not_then strip_assume_tac >> res_tac >>
    fsrw_tac[ARITH_ss][between_def,MEM_MAP,MAP_MAP_o] >>
    res_tac >> rw[] >> DECIDE_TAC ) >>
  conj_tac >- (
    fs[EVERY_MAP,EVERY_FILTER,is_Label_rwt,GSYM LEFT_FORALL_IMP_THM,between_def,Abbr`l`] >>
    reverse conj_tac >- (disj2_tac >> DECIDE_TAC) >>
    fsrw_tac[DNF_ss][EVERY_MEM,MEM_MAP,FORALL_PROD,EXISTS_PROD] >>
    rw[] >> res_tac >>
    TRY(metis_tac[]) >>
    disj2_tac >> DECIDE_TAC ) >>
  rpt gen_tac >>
  strip_tac >>
  conj_tac >- (
    fs[EVERY_MEM] >>
    qx_gen_tac`z` >>
    PairCases_on`z` >> strip_tac >>
    simp[code_env_cd_def] >>
    qmatch_assum_abbrev_tac`MEM cd (free_labs ez e)` >>
    `∃i. i < LENGTH (free_labs ez e) ∧ (EL i (free_labs ez e) = cd)` by metis_tac[MEM_EL] >>
    qpat_assum`∀i. P ⇒ Q`(qspec_then`i`mp_tac) >>
    simp[EL_MAP] >>
    simp[Abbr`cd`] >> strip_tac >>
    qexists_tac`cs i`>>simp[] >>
    qexists_tac`bc0++Jump (Lab l)::bc0'` >>
    simp[] >>
    fs[EVERY_MEM,MEM_MAP,FILTER_APPEND] >>
    fsrw_tac[DNF_ss][] >- (
      rpt strip_tac >> res_tac >> DECIDE_TAC) >>
    rpt strip_tac >> res_tac >> DECIDE_TAC) >>
  `bc_fetch bs = SOME (Jump (Lab l))` by (
    match_mp_tac bc_fetch_next_addr >>
    qexists_tac`bc0` >> simp[] ) >>
  simp[bc_eval1_thm,bc_eval1_def,bc_state_component_equality,bc_find_loc_def] >>
  match_mp_tac bc_find_loc_aux_append_code >>
  match_mp_tac bc_find_loc_aux_ALL_DISTINCT >>
  qexists_tac`LENGTH bc0 + 1 + LENGTH c0` >>
  simp[EL_APPEND2,TAKE_APPEND2,FILTER_APPEND,SUM_APPEND,ALL_DISTINCT_APPEND,MEM_FILTER] >>
  fs[Abbr`l`,EVERY_MAP,EVERY_FILTER,between_def] >>
  fsrw_tac[DNF_ss][EVERY_MEM,is_Label_rwt,MEM_MAP,EXISTS_PROD,FORALL_PROD,MEM_FILTER] >>
  rw[] >> spose_not_then strip_assume_tac >> res_tac >> fsrw_tac[ARITH_ss][] >>
  res_tac >> fsrw_tac[ARITH_ss][])

val repl_exp_val = store_thm("repl_exp_val",
  ``∀cenv s env exp s' v rd rs rs' bc0 bc bs bs'.
      evaluate cenv s env exp (s', Rval v) ∧
      EVERY closed s ∧
      EVERY closed (MAP (FST o SND) env) ∧
      FV exp ⊆ set (MAP FST env) ∧
      closed_under_cenv cenv env s ∧
      (∀v. v ∈ env_range env ∨ MEM v s ⇒ all_locs v ⊆ count (LENGTH s)) ∧
      LENGTH s' ≤ LENGTH rd.sm ∧
      good_cenv cenv ∧
      good_cmap cenv (cmap rs.contab) ∧
      set (MAP FST cenv) ⊆ FDOM (cmap rs.contab) ∧
      good_contab rs.contab ∧
      env_rs env rs rd (MAP (v_to_Cv (cmap rs.contab)) s) (bs with code := bc0) ∧
      (repl_exp rs exp = (rs',bc)) ∧
      (bs.code = bc0 ++ bc) ∧
      (bs.pc = next_addr bs.inst_length bc0) ∧
      ALL_DISTINCT (FILTER is_Label bc0) ∧
      EVERY (combin$C $< rs.rnext_label o dest_Label) (FILTER is_Label bc0)
      ⇒
      ∃bv rf rd'.
      let bs' = bs with <|pc := next_addr bs.inst_length (bc0 ++ bc);
                          stack := bv :: bs.stack; refs := rf|> in
      bc_next^* bs bs' ∧
      (v_to_ov rd'.sm v = bv_to_ov (FST(SND(rs'.contab))) bv) ∧
      env_rs env rs' rd' (MAP (v_to_Cv (cmap rs'.contab)) s') bs'``,
  rpt gen_tac >>
  simp[repl_exp_def,compile_Cexp_def,GSYM LEFT_FORALL_IMP_THM] >>
  Q.PAT_ABBREV_TAC`Ce0 = exp_to_Cexp X exp` >>
  Q.PAT_ABBREV_TAC`p = label_closures Y X Ce0` >>
  PairCases_on`p`>>simp[]>> strip_tac >>
  qspecl_then[`cenv`,`s`,`env`,`exp`,`(s',Rval v)`] mp_tac (CONJUNCT1 exp_to_Cexp_thm1) >>
  simp[] >>
  disch_then (qspec_then `cmap rs.contab` mp_tac) >>
  fs[env_rs_def] >>
  simp[FORALL_PROD,GSYM LEFT_FORALL_IMP_THM] >>
  simp_tac(srw_ss()++DNF_ss)[] >>
  map_every qx_gen_tac [`Cs'0`,`Cv0`] >> strip_tac >>
  qspecl_then[`LENGTH env`,`rs.rnext_label`,`Ce0`]mp_tac(CONJUNCT1 label_closures_thm) >>
  discharge_hyps >- (
    simp[Abbr`Ce0`] >>
    match_mp_tac free_vars_exp_to_Cexp_matchable >>
    simp[] ) >>
  simp[] >> strip_tac >>
  qpat_assum`X = bc`mp_tac >>
  Q.PAT_ABBREV_TAC`cce = compile_code_env X Y` >>
  qpat_assum`Abbrev(cce = X)`mp_tac >>
  Q.PAT_ABBREV_TAC`s0 = X with out := []` >>
  strip_tac >>
  qspecl_then[`LENGTH env`,`s0`,`p0`]mp_tac compile_code_env_thm >>
  simp[] >>
  discharge_hyps >- (
    simp[ALL_DISTINCT_GENLIST,EVERY_GENLIST,Abbr`s0`] ) >>
  disch_then(Q.X_CHOOSE_THEN`c0`strip_assume_tac) >>
  Q.PAT_ABBREV_TAC`tf = X:call_context` >>
  qmatch_assum_rename_tac`free_vars Ce ⊆ free_vars Ce0`[] >>
  qspecl_then[`rs.renv`,`tf`,`rs.rsz`,`cce`,`Ce`](Q.X_CHOOSE_THEN`bc1`strip_assume_tac)(CONJUNCT1 compile_append_out) >>
  fs[Abbr`tf`] >>
  simp[REVERSE_APPEND] >> rw[] >>
  first_x_assum(qspecl_then[`bs`,`bc0`]mp_tac) >>
  simp[Abbr`s0`] >>
  discharge_hyps >- (
    simp[MEM_MAP,MEM_GENLIST,MEM_FILTER,GSYM LEFT_FORALL_IMP_THM,is_Label_rwt] >>
    fs[EVERY_FILTER,is_Label_rwt,EVERY_MEM] >>
    fsrw_tac[DNF_ss,ARITH_ss][] >>
    rw[] >> res_tac >> DECIDE_TAC ) >>
  strip_tac >>
  qmatch_assum_abbrev_tac`bc_next bs bs1` >>
  qmatch_assum_abbrev_tac`Cevaluate Cs Cenv Ce0 (Cs'0,Rval Cv0)` >>
  qspecl_then[`Cs`,`Cenv`,`Ce0`,`Cs'0,Rval Cv0`]mp_tac(CONJUNCT1 Cevaluate_syneq) >> simp[] >>
  disch_then(qspecl_then[`$=`,`Cs`,`Cenv`,`Ce`]mp_tac) >>
  `LENGTH Cenv = LENGTH env` by rw[Abbr`Cenv`,env_to_Cenv_MAP] >>
  simp[EXISTS_PROD] >>
  simp_tac(srw_ss()++DNF_ss)[] >>
  map_every qx_gen_tac[`Cs'`,`Cv`] >> strip_tac >>
  qspecl_then[`Cs`,`Cenv`,`Ce`,`(Cs',Rval Cv)`]mp_tac(CONJUNCT1 compile_val) >> simp[] >>
  disch_then(qspecl_then[`rd`,`cce`,`rs.renv`,`rs.rsz`,`bs1`,`bc0 ++ REVERSE (cce).out`,`REVERSE bc1`,`bc0 ++ REVERSE (cce).out`]mp_tac) >>
  `EVERY (code_env_cd (bc0 ++ REVERSE (cce).out)) (free_labs (LENGTH env) Ce)` by ( fs[Abbr`cce`] ) >>

  (* need to change Cs and Cenv into syneq things that satisfy all_vlabs and code_env_cd for bc0 -
    hopefully this can be proven to be always possible ?
    or env_rs should guarantee it ?  *)

  discharge_hyps >- (
    simp[Abbr`Cenv`,Abbr`Cs`,env_to_Cenv_MAP,LIST_TO_SET_MAP,GSYM IMAGE_COMPOSE,combinTheory.o_DEF,all_Clocs_v_to_Cv,Abbr`bs1`] >>
    conj_tac >- ( fsrw_tac[DNF_ss][SUBSET_DEF] >> PROVE_TAC[] ) >>
    conj_tac >- ( fsrw_tac[DNF_ss][SUBSET_DEF] >> PROVE_TAC[] ) >>
    conj_tac >- (
      simp[FILTER_APPEND,ALL_DISTINCT_APPEND] >>
      fs[EVERY_MAP,MEM_FILTER,EVERY_FILTER,is_Label_rwt,GSYM LEFT_FORALL_IMP_THM,between_def] >>
      rw[] >> fs[EVERY_MEM] >> spose_not_then strip_assume_tac >>
      res_tac >> fs[MEM_GENLIST] >> DECIDE_TAC ) >>
    conj_tac >- simp[EVERY_MAP]

    conj_tac >- (
      match_mp_tac SUBSET_TRANS >>
      HINT_EXISTS_TAC >>
      simp[Abbr`Ce0`] >>
      match_mp_tac free_vars_exp_to_Cexp_matchable >>
      simp[] >>
      fs[Cenv_bs_def,EVERY2_EVERY] ) >>
    conj_tac >- (
      fs[env_to_Cenv_MAP,combinTheory.o_DEF] >>
      match_mp_tac Cenv_bs_append_code >>
      qmatch_assum_abbrev_tac`bc_next bs bs1` >>
      qexists_tac`bs1 with code := bc0 ++ code` >>
      simp[bc_state_component_equality,Abbr`bs1`] >>
      match_mp_tac Cenv_bs_append_code >>
      Q.PAT_ABBREV_TAC`pc = SUM (MAP X Y)` >>
      qexists_tac`bs with <| pc := pc ; code := bc0 |>` >>
      simp[bc_state_component_equality,Cenv_bs_with_pc] >>
      match_mp_tac Cenv_bs_c_SUBMAP >>
      HINT_EXISTS_TAC >>
      simp[Abbr`Cc`,SUBMAP_FUNION] ) >>
    fsrw_tac[DNF_ss,ARITH_ss][EVERY_MEM,between_def,MEM_MAP,FILTER_APPEND,ALL_DISTINCT_APPEND,MEM_FILTER,is_Label_rwt,MEM_GENLIST] >>
    rw[] >> spose_not_then strip_assume_tac >> res_tac >> fsrw_tac[ARITH_ss][] ) >>
  disch_then(qspecl_then[`REVERSE bc`]mp_tac o CONJUNCT1) >>
  qmatch_assum_abbrev_tac`X.out = bc ++ (SND cce).out` >>
  Q.PAT_ABBREV_TAC`Y = compile Cc A B C D E` >>
  `Y = X` by (
    map_every qunabbrev_tac[`X`,`Y`] >>
    match_mp_tac (CONJUNCT1 compile_c_SUBMAP) >>
    rfs[] >>
    simp[Abbr`Cc`] >>
    match_mp_tac SUBMAP_FUNION >>
    simp[DISJOINT_DEF,EXTENSION] >>
    fs[SUBSET_DEF,MEM_GENLIST] >>
    disj2_tac >> spose_not_then strip_assume_tac >>
    res_tac >> fsrw_tac[ARITH_ss][] ) >>
  simp[Abbr`bs1`] >>
  simp_tac(srw_ss()++DNF_ss)[code_for_push_def,LET_THM] >>
  map_every qx_gen_tac[`rf`,`rd'`,`bv`] >> strip_tac >>
  map_every qexists_tac[`bv`,`rf`,`rd'`,`Cc`] >>
  conj_tac >- metis_tac[RTC_TRANSITIVE,transitive_def,RTC_SUBSET] >>
  conj_tac >- (
    match_mp_tac EQ_TRANS >>
    qexists_tac`Cv_to_ov (FST (SND rs.contab)) rd'.sm Cv` >>
    conj_tac >- (
      match_mp_tac EQ_SYM >>
      match_mp_tac EQ_TRANS >>
      qexists_tac`Cv_to_ov (FST (SND rs.contab)) rd'.sm (v_to_Cv (cmap rs.contab) v)` >>
      conj_tac >- (
        match_mp_tac EQ_SYM >>
        match_mp_tac EQ_TRANS >>
        qexists_tac`Cv_to_ov (FST (SND rs.contab)) rd'.sm Cv0` >>
        conj_tac >- (
          match_mp_tac (CONJUNCT1 syneq_ov) >>
          HINT_EXISTS_TAC >> simp[] ) >>
        match_mp_tac (CONJUNCT1 syneq_ov) >>
        HINT_EXISTS_TAC >> simp[] ) >>
      match_mp_tac (CONJUNCT1 v_to_Cv_ov) >>
      qabbrev_tac`ct=rs.contab` >>
      PairCases_on`ct` >> fs[good_contab_def] >>
      qspecl_then[`cenv`,`s`,`env`,`exp`,`s',Rval v`]mp_tac (CONJUNCT1 evaluate_all_cns) >>
      fs[good_cmap_def,closed_under_cenv_def] >>
      fs[SUBSET_DEF,MEM_MAP,EXISTS_PROD] >>
      metis_tac[]) >>
    match_mp_tac (MP_CANON Cv_bv_ov) >>
    HINT_EXISTS_TAC >> simp[] ) >>
  conj_tac >- (
    match_mp_tac code_env_code_append >>
    rfs[Abbr`cce`] >>
    simp[FILTER_APPEND,ALL_DISTINCT_APPEND,FILTER_REVERSE,ALL_DISTINCT_REVERSE] >>
    simp[MEM_FILTER,is_Label_rwt,GSYM LEFT_FORALL_IMP_THM] >>
    fsrw_tac[DNF_ss][EVERY_MAP,EVERY_FILTER,is_Label_rwt,MEM_GENLIST,between_def] >>
    fsrw_tac[DNF_ss][EVERY_MEM] >>
    rw[] >> spose_not_then strip_assume_tac >> res_tac >> fsrw_tac[ARITH_ss][] ) >>
  conj_tac >- (
    rfs[Abbr`Cc`] >>
    fsrw_tac[DNF_ss][SUBSET_DEF,MEM_GENLIST] >>
    rw[] >> res_tac >> DECIDE_TAC ) >>

  Cenv_bs_change_store
  match_mp_tac Cenv_bs_with_pc >>

  fs[Cenv_bs_def] >>
  conj_tac >- (
    fsrw_tac[DNF_ss][EVERY2_EVERY,EVERY_MEM,FORALL_PROD,option_case_NONE_F] >>
    rw[] >> res_tac >> HINT_EXISTS_TAC >>
    rw[] >> match_mp_tac (GEN_ALL (MP_CANON (CONJUNCT1 (SPEC_ALL Cv_bv_l2a_mono)))) >>
    qmatch_assum_abbrev_tac`Cv_bv pp x bv'` >>
    qexists_tac`pp` >> simp[Abbr`pp`] >>
    metis_tac[bc_find_loc_aux_append_code] ) >>
  fs[s_refs_def,good_rd_def]
    HINT_EXISTS_TAC
  DB.find"Cenv_bs"
  Cenv_bs

(* must read an expression followed by all space until the start of another
   expression (or end of string) *)
val parse_def = Define`
  (parse : string -> (t exp # string) option) s = ARB`

val _ = Hol_datatype`
  swhile_result = Terminate of 'a | Diverge`

val _ = Hol_datatype`
  swhile_step_result = Success of 'a | Fail of 'b`

val SWHILE_def = Define`
  SWHILE f x = case OWHILE (ISL o f) (OUTL o f) x of NONE => Diverge | SOME y => Terminate (OUTR (f y))`

val SWHILE_thm = store_thm("SWHILE_thm",
  ``SWHILE f x = case f x of INL x => SWHILE f x | INR y => Terminate y``,
  rw[SWHILE_def] >> Cases_on `f x` >> rw[Once OWHILE_THM])

val intersperse_def = Define`
  (intersperse _ [] = []) ∧
  (intersperse _ [x] = [x]) ∧
  (intersperse a (x::xs) = x::a::intersperse a xs)`

val ov_to_string_def = tDefine "ov_to_string"`
  (ov_to_string (OLit (IntLit i)) = if i < 0 then "-"++(num_to_dec_string (Num (-i)))
                                             else num_to_dec_string (Num i)) ∧
  (ov_to_string (OLit (Bool T)) = "true") ∧
  (ov_to_string (OLit (Bool F)) = "false") ∧
  (ov_to_string (OConv cn vs) = cn++"("++CONCAT(intersperse "," (MAP ov_to_string vs))++")") ∧
  (ov_to_string OFn = "fn")`
  (WF_REL_TAC`measure ov_size` >>
   gen_tac >> Induct >> rw[CompileTheory.ov_size_def] >>
   res_tac >> srw_tac[ARITH_ss][])

(*
``ov_to_string (OConv "Cons" [OLit(IntLit (-3));OConv "Nil"[]]) = X ``
rw[ov_to_string_def,intersperse_def,
   ASCIInumbersTheory.num_to_dec_string_def,
   ASCIInumbersTheory.n2s_def,
   ASCIInumbersTheory.HEX_def,
   Once numposrepTheory.n2l_def ]
*)

val init_bc_state_def =  Define`
  init_bc_state = <|
    stack := [];
    code := [];
    pc := 0;
    refs := FEMPTY;
    handler := 0;
    inst_length := ARB |>`

val repl_def = Define`
  repl s = SWHILE
   (λ(rs,bs,inp:string,out:string).
     if inp = "" then INR (Success out) else
     case parse inp of NONE => INR (Fail "parse error") |
     SOME (exp,inp) =>
       (* typecheck? *)
       let (rs',bc) = repl_exp rs exp in
       let bs' = bs with <|code := bs.code ++ bc;
                           pc := next_addr bs.inst_length bs.code|> in
       case SWHILE (λbs.
         if bs.pc = next_addr bs.inst_length (bs.code ++ bc) then INR (Success bs)
         else case bc_eval1 bs of NONE => INR (Fail "runtime error") | SOME bs => INL bs)
         bs'
       of | Diverge => INR (Fail "divergence")
          | Terminate (Fail s) => INR (Fail s)
          | Terminate (Success bs'') =>
       (* let vals = extract_bindings rs' bs'' in *)
       let v = HD bs''.stack in
       INL (rs',bs'',inp,(out ++ "\n" ++ (ov_to_string (bv_to_ov (FST (SND rs'.contab)) v)))))
  (init_repl_state,init_bc_state,s,"")`

val _ = export_theory()
