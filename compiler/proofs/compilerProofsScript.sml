open HolKernel bossLib boolLib boolSimps listTheory rich_listTheory pred_setTheory relationTheory arithmeticTheory whileTheory pairTheory quantHeuristicsLib lcsymtacs sortingTheory finite_mapTheory alistTheory
open SatisfySimps miscLib BigStepTheory terminationTheory semanticsExtraTheory miscTheory ToBytecodeTheory CompilerTheory compilerTerminationTheory intLangExtraTheory pmatchTheory toIntLangProofsTheory toBytecodeProofsTheory bytecodeTerminationTheory bytecodeExtraTheory bytecodeEvalTheory
val _ = new_theory"compilerProofs"

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
    simp[ALL_DISTINCT_APPEND,FILTER_APPEND,MEM_FILTER] >>
    fs[EVERY_MAP,EVERY_FILTER] >> fs[EVERY_MEM] >>
    spose_not_then strip_assume_tac >> res_tac >>
    fsrw_tac[ARITH_ss][between_def,MEM_MAP,MAP_MAP_o] >>
    res_tac >> rw[] >> DECIDE_TAC ) >>
  conj_tac >- (
    fs[EVERY_MAP,EVERY_FILTER,is_Label_rwt,GSYM LEFT_FORALL_IMP_THM,between_def] >>
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
    qexists_tac`bc0++Jump (Lab s.next_label)::bc0'` >>
    simp[] >>
    fs[EVERY_MEM,MEM_MAP,FILTER_APPEND] >>
    fsrw_tac[DNF_ss][] >- (
      rpt strip_tac >> res_tac >> DECIDE_TAC) >>
    rpt strip_tac >> res_tac >> DECIDE_TAC) >>
  `bc_fetch bs = SOME (Jump (Lab s.next_label))` by (
    match_mp_tac bc_fetch_next_addr >>
    qexists_tac`bc0` >> simp[] ) >>
  simp[bc_eval1_thm,bc_eval1_def,bc_state_component_equality,bc_find_loc_def] >>
  match_mp_tac bc_find_loc_aux_append_code >>
  match_mp_tac bc_find_loc_aux_ALL_DISTINCT >>
  qexists_tac`LENGTH bc0 + 1 + LENGTH c0` >>
  simp[EL_APPEND2,TAKE_APPEND2,FILTER_APPEND,SUM_APPEND,ALL_DISTINCT_APPEND,MEM_FILTER] >>
  fs[EVERY_MAP,EVERY_FILTER,between_def] >>
  fsrw_tac[DNF_ss][EVERY_MEM,is_Label_rwt,MEM_MAP,EXISTS_PROD,FORALL_PROD,MEM_FILTER] >>
  rw[] >> spose_not_then strip_assume_tac >> res_tac >> fsrw_tac[ARITH_ss][] >>
  res_tac >> fsrw_tac[ARITH_ss][])

val code_env_cd_append = store_thm("code_env_cd_append",
  ``∀code cd code'. code_env_cd code cd ∧ ALL_DISTINCT (FILTER is_Label (code ++ code')) ⇒ code_env_cd (code ++ code') cd``,
  rw[] >> PairCases_on`cd` >>
  fs[code_env_cd_def] >>
  HINT_EXISTS_TAC>>simp[]>>
  HINT_EXISTS_TAC>>simp[])

val good_contab_def = Define`
  good_contab ((m,w,n):contab) ⇔
    ALL_DISTINCT (MAP SND w) ∧
    EVERY (combin$C $< n) (MAP FST w) ∧
    set (MAP SND w) ⊆ (IMAGE id_to_string (FDOM m)) ∧
    cmap_linv m w`

val env_rs_def = Define`
  env_rs cenv env rs rd s bs ⇔
    good_contab rs.contab ∧
    good_cmap cenv (cmap rs.contab) ∧
    (({Short ""} ∪ set (MAP FST cenv)) = FDOM (cmap rs.contab)) ∧
    Short "" ∉ set (MAP FST cenv) ∧
    (∀id. (FLOOKUP (cmap rs.contab) id = SOME ((cmap rs.contab) ' (Short ""))) ⇒ (id = Short "")) ∧
    (set rs.rbvars = set (MAP FST env)) ∧
    ALL_DISTINCT rs.rbvars ∧
    let Cs0 = MAP (v_to_Cv (cmap rs.contab)) s in
    let Cenv0 = env_to_Cenv (cmap rs.contab) (MAP (λv. (v,THE (ALOOKUP env v))) rs.rbvars) in
    let rsz = LENGTH rs.rbvars in
    ∃Cenv Cs.
    LIST_REL syneq Cs0 Cs ∧ LIST_REL syneq Cenv0 Cenv ∧
    (BIGUNION (IMAGE all_Clocs (set Cs)) ⊆ count (LENGTH Cs)) ∧
    (BIGUNION (IMAGE all_Clocs (set Cenv)) ⊆ count (LENGTH Cs)) ∧
    EVERY all_vlabs Cs ∧ EVERY all_vlabs Cenv ∧
    (∀cd. cd ∈ vlabs_list Cs ⇒ code_env_cd bs.code cd) ∧
    (∀cd. cd ∈ vlabs_list Cenv ⇒ code_env_cd bs.code cd) ∧
    Cenv_bs rd Cs Cenv (GENLIST (λi. CTLet (rsz - i)) rsz) rsz bs`

val compile_shadows_thm = store_thm("compile_shadows_thm",
  ``∀vs bvs cs i. let cs' = compile_shadows bvs cs i vs in
      ∃code.
        (cs'.out = REVERSE code ++ cs.out) ∧
        (cs'.next_label = cs.next_label) ∧
        EVERY ($~ o is_Label) code ∧
        ∀bs bc0 u ws st.
          (bs.code = bc0 ++ code) ∧
          (bs.pc = next_addr bs.inst_length bc0) ∧
          (bs.stack = Block u ws::st) ∧
          (LENGTH vs + i ≤ LENGTH ws) ∧
          (LENGTH bvs ≤ LENGTH st) ∧
          set vs ⊆ set bvs ∧
          ALL_DISTINCT vs ∧ ALL_DISTINCT bvs
          ⇒
          let bs' =
          bs with <| pc := next_addr bs.inst_length (bc0 ++ code)
                   ; stack := Block u ws::
                     GENLIST (λx. if x < LENGTH bvs ∧ EL x bvs ∈ set vs then EL (THE (find_index (EL x bvs) vs i)) ws else EL x st)
                     (LENGTH st)
                   |> in
          bc_next^* bs bs'``,
  Induct >- (
    simp[compile_shadows_def,Once SWAP_REVERSE] >> rw[] >>
    simp[Once RTC_CASES1] >> disj1_tac >>
    simp[bc_state_component_equality] >>
    match_mp_tac EQ_SYM >>
    match_mp_tac GENLIST_EL >>
    simp[]) >>
  qx_gen_tac`v` >>
  simp[compile_shadows_def] >> rw[] >>
  Q.PAT_ABBREV_TAC`cs0 = cs with out := X` >>
  first_x_assum(qspecl_then[`bvs`,`cs0`,`i+1`]mp_tac) >>
  simp[] >>
  disch_then(Q.X_CHOOSE_THEN`c0`strip_assume_tac) >>
  simp[Abbr`cs0`,Once SWAP_REVERSE] >>
  rw[] >>
  simp[Once RTC_CASES1] >> disj2_tac >>
  `bc_fetch bs = SOME (Stack (Load 0))` by (
    match_mp_tac bc_fetch_next_addr >>
    qexists_tac`bc0`>>simp[] ) >>
  simp[bc_eval1_thm,bc_eval1_def] >>
  simp[bc_eval_stack_def,bump_pc_def] >>
  qpat_assum`bc_fetch X = Y`kall_tac >>
  qmatch_abbrev_tac`bc_next^* bs1 bs'` >>
  simp[Once RTC_CASES1] >> disj2_tac >>
  `bc_fetch bs1 = SOME (Stack (El i))` by (
    match_mp_tac bc_fetch_next_addr >>
    qexists_tac`TAKE (LENGTH bc0 + 1) bs.code` >>
    simp[Abbr`bs1`,TAKE_APPEND1,TAKE_APPEND2,FILTER_APPEND,SUM_APPEND]) >>
  simp[bc_eval1_thm,bc_eval1_def] >>
  simp[bc_eval_stack_def,bump_pc_def,Abbr`bs1`] >>
  qpat_assum`bc_fetch X = Y`kall_tac >>
  qmatch_abbrev_tac`bc_next^* bs1 bs'` >>
  simp[Once RTC_CASES1] >> disj2_tac >>
  `bc_fetch bs1 = SOME (Stack (Store (the 0 (find_index v bvs 1))))` by (
    match_mp_tac bc_fetch_next_addr >>
    qexists_tac`TAKE (LENGTH bc0 + 2) bs.code` >>
    simp[Abbr`bs1`,TAKE_APPEND1,TAKE_APPEND2,FILTER_APPEND,SUM_APPEND]) >>
  simp[bc_eval1_thm,bc_eval1_def] >>
  simp[bc_eval_stack_def,bump_pc_def,Abbr`bs1`] >>
  qpat_assum`bc_fetch X = Y`kall_tac >>
  qspecl_then[`bvs`,`v`,`1`]mp_tac find_index_MEM >>
  simp[] >> disch_then(Q.X_CHOOSE_THEN`m`strip_assume_tac) >>
  simp[] >>
  last_x_assum kall_tac >>
  last_x_assum kall_tac >>
  qmatch_abbrev_tac`bc_next^* bs1 bs'` >>
  first_x_assum(qspecl_then[`bs1`,`TAKE (LENGTH bc0 + 3) bs.code`]mp_tac) >>
  simp[Abbr`bs1`,TAKE_APPEND1,TAKE_APPEND2,SUM_APPEND,FILTER_APPEND,ADD1] >>
  qmatch_abbrev_tac`bc_next^* bs1 bs2 ⇒ bc_next^* bs1 bs'` >>
  `bs2 = bs'` by (
    simp[Abbr`bs2`,Abbr`bs'`,bc_state_component_equality,SUM_APPEND,FILTER_APPEND] >>
    simp[LIST_EQ_REWRITE] >> gen_tac >> strip_tac >>
    Cases_on`x < LENGTH bvs` >> simp[] >- (
      Cases_on`EL x bvs = v` >> simp[] >- (
        simp[CompilerLibTheory.find_index_def] >>
        `x = m` by metis_tac[EL_ALL_DISTINCT_EL_EQ] >>
        simp[EL_APPEND1,EL_APPEND2] ) >>
      Cases_on`MEM (EL x bvs) vs` >> simp[] >- (
        simp[CompilerLibTheory.find_index_def] ) >>
      Cases_on`x<m`>> simp[EL_APPEND1,EL_APPEND2,EL_TAKE] >>
      Cases_on`m<x`>> simp[EL_APPEND1,EL_APPEND2,EL_TAKE,EL_DROP] >>
      `x=m`by simp[] >>
      metis_tac[EL_ALL_DISTINCT_EL_EQ] ) >>
    `m < x` by simp[] >>
    simp[EL_APPEND2,EL_DROP] ) >>
  simp[])

val compile_news_thm = store_thm("compile_news_thm",
  ``∀vs cs i. let cs' = compile_news cs i vs in
      ∃code.
        (cs'.out = REVERSE code ++ cs.out) ∧
        (cs'.next_label = cs.next_label) ∧
        EVERY ($~ o is_Label) code ∧
        ∀bs bc0 u ws st.
          (bs.code = bc0 ++ code) ∧
          (bs.pc = next_addr bs.inst_length bc0) ∧
          (bs.stack = Block u ws::st) ∧
          (LENGTH ws = LENGTH vs + i)
          ⇒
          let bs' =
          bs with <| pc := next_addr bs.inst_length (bc0 ++ code)
                   ; stack := Block u ws::(REVERSE (DROP i ws))++st
                   |> in
          bc_next^* bs bs'``,
  Induct >- (
    simp[compile_news_def,Once SWAP_REVERSE] >> rw[] >>
    simp[Once RTC_CASES1] >> disj1_tac >>
    simp[bc_state_component_equality,DROP_LENGTH_NIL]) >>
  qx_gen_tac`v` >>
  simp[compile_news_def] >> rw[] >>
  Q.PAT_ABBREV_TAC`cs0 = cs with out := X` >>
  first_x_assum(qspecl_then[`cs0`,`i+1`]mp_tac) >>
  simp[] >>
  disch_then(Q.X_CHOOSE_THEN`c0`strip_assume_tac) >>
  simp[Abbr`cs0`,Once SWAP_REVERSE] >>
  rw[] >>
  simp[Once RTC_CASES1] >> disj2_tac >>
  `bc_fetch bs = SOME (Stack (Load 0))` by (
    match_mp_tac bc_fetch_next_addr >>
    qexists_tac`bc0`>>simp[] ) >>
  simp[bc_eval1_thm,bc_eval1_def] >>
  simp[bc_eval_stack_def,bump_pc_def] >>
  qpat_assum`bc_fetch X = Y`kall_tac >>
  qmatch_abbrev_tac`bc_next^* bs1 bs'` >>
  simp[Once RTC_CASES1] >> disj2_tac >>
  `bc_fetch bs1 = SOME (Stack (Load 0))` by (
    match_mp_tac bc_fetch_next_addr >>
    qexists_tac`TAKE (LENGTH bc0 + 1) bs.code` >>
    simp[Abbr`bs1`,TAKE_APPEND1,TAKE_APPEND2,FILTER_APPEND,SUM_APPEND]) >>
  simp[bc_eval1_thm,bc_eval1_def] >>
  simp[bc_eval_stack_def,bump_pc_def,Abbr`bs1`] >>
  qpat_assum`bc_fetch X = Y`kall_tac >>
  qmatch_abbrev_tac`bc_next^* bs1 bs'` >>
  simp[Once RTC_CASES1] >> disj2_tac >>
  `bc_fetch bs1 = SOME (Stack (El i))` by (
    match_mp_tac bc_fetch_next_addr >>
    qexists_tac`TAKE (LENGTH bc0 + 2) bs.code` >>
    simp[Abbr`bs1`,TAKE_APPEND1,TAKE_APPEND2,FILTER_APPEND,SUM_APPEND]) >>
  simp[bc_eval1_thm,bc_eval1_def] >>
  simp[bc_eval_stack_def,bump_pc_def,Abbr`bs1`] >>
  qpat_assum`bc_fetch X = Y`kall_tac >>
  qmatch_abbrev_tac`bc_next^* bs1 bs'` >>
  simp[Once RTC_CASES1] >> disj2_tac >>
  `bc_fetch bs1 = SOME (Stack (Store 1))` by (
    match_mp_tac bc_fetch_next_addr >>
    qexists_tac`TAKE (LENGTH bc0 + 3) bs.code` >>
    simp[Abbr`bs1`,TAKE_APPEND1,TAKE_APPEND2,FILTER_APPEND,SUM_APPEND]) >>
  simp[bc_eval1_thm,bc_eval1_def] >>
  simp[bc_eval_stack_def,bump_pc_def,Abbr`bs1`] >>
  qpat_assum`bc_fetch X = Y`kall_tac >>
  qmatch_abbrev_tac`bc_next^* bs1 bs'` >>
  first_x_assum(qspecl_then[`bs1`,`TAKE (LENGTH bc0 + 4) bs.code`]mp_tac) >>
  simp[Abbr`bs1`,SUM_APPEND,FILTER_APPEND,TAKE_APPEND1,TAKE_APPEND2] >>
  qmatch_abbrev_tac`bc_next^* bs1 bs2 ⇒ bc_next^* bs1 bs'` >>
  `bs2 = bs'` by (
    simp[Abbr`bs2`,Abbr`bs'`,bc_state_component_equality,SUM_APPEND,FILTER_APPEND] >>
    simp[LIST_EQ_REWRITE] >> gen_tac >> strip_tac >>
    Cases_on`x<LENGTH vs`>>simp[EL_REVERSE,EL_APPEND1,EL_APPEND2,EL_DROP,PRE_SUB1,ADD1] >>
    `x = LENGTH vs` by simp[] >>
    simp[] ) >>
  simp[])

(* TODO: move *)
val closed_under_menv_def = Define`
  closed_under_menv menv env s ⇔
    EVERY (closed menv) s ∧
    EVERY (closed menv) (MAP SND env) ∧
    EVERY (EVERY (closed menv) o MAP SND) (MAP SND menv)`

fun filter_asms P = POP_ASSUM_LIST (MAP_EVERY ASSUME_TAC o filter (P o concl))
fun contains tms tm = can (find_term (C mem tms)) tm

(* TODO move *)
val Cenv_bs_pc_handler = store_thm("Cenv_bs_pc_handler",
  ``∀rd s env env0 sz0 bs' bs p h. Cenv_bs rd s env env0 sz0 bs' ∧ (bs = bs' with <| pc := p; handler := h |>) ⇒ Cenv_bs rd s env env0 sz0 bs``,
  rw[Cenv_bs_with_pc] >> fs[Cenv_bs_def,s_refs_def,good_rd_def])

val err_to_Cerr = Define`
  (err_to_Cerr (Rraise Bind_error) = Craise CBind_excv) ∧
  (err_to_Cerr (Rraise Div_error) = Craise CDiv_excv) ∧
  (err_to_Cerr (Rraise (Int_error n)) = Craise (CLitv (IntLit n))) ∧
  (err_to_Cerr (Rtype_error) = Ctype_error)`
val _ = export_rewrites["err_to_Cerr_def"]

val err_bv_def = Define`
  (err_bv Div_error bv ⇔ bv = Block (block_tag+div_exc_cn) []) ∧
  (err_bv Bind_error bv ⇔ bv = Block (block_tag+bind_exc_cn) []) ∧
  (err_bv (Int_error n) bv ⇔ bv = Number n)`

val Cmap_result_Rerr = store_thm("Cmap_result_Rerr",
 ``Cmap_result f (Rerr err) = Cexc (err_to_Cerr err)``,
 Cases_on`err`>>simp[]>>Cases_on`e`>>simp[])

val compile_fake_exp_val = store_thm("compile_fake_exp_val",
  ``∀rs vars expf menv tup cenv s env exp s' beh rs' bc rd vv0 vv1 bc0 bs.
      evaluate menv ((Short "",tup)::cenv) s env exp (s', beh) ∧
      is_null menv ∧
      FV exp ⊆ set (MAP (Short o FST) env) ∪ menv_dom menv ∧
      closed_under_menv menv env s ∧
      closed_under_cenv cenv menv env s ∧
      (∀v. v ∈ env_range env ∨ MEM v s ⇒ all_locs v ⊆ count (LENGTH s)) ∧
      env_rs cenv env rs rd s (bs with code := bc0) ∧
      ALL_DISTINCT vars ∧
      (PARTITION (λv. MEM v rs.rbvars) vars = (vv0,vv1)) ∧
      (compile_fake_exp rs vars expf = (rs',bc ++ [Stop])) ∧
      (exp = expf (Con (Short "") (MAP (Var o Short) (vv0++vv1)))) ∧
      (bs.code = bc0 ++ bc ++ [Stop]) ∧
      (bs.pc = next_addr bs.inst_length bc0) ∧
      ALL_DISTINCT (FILTER is_Label bc0) ∧
      EVERY (combin$C $< rs.rnext_label o dest_Label) (FILTER is_Label bc0)
      ⇒
      (∀vs. (beh = Rval (Conv (Short "") vs)) ∧ (LENGTH vars = LENGTH vs) ⇒
        ∃st rf rd'.
        let env' = ZIP(vv0++vv1,vs) ++ env in
        let bs' = bs with <|pc := next_addr bs.inst_length (bc0 ++ bc); stack := (Number i0)::st; refs := rf|> in
        bc_next^* bs bs' ∧
        env_rs cenv env' rs' rd' s' (bs' with stack := st)) ∧
      (∀err. (beh = Rerr (Rraise err)) ⇒
        ∃bv rf rd'.
        let bs' = bs with <|pc := next_addr bs.inst_length (bc0 ++ bc); stack := (Number i1)::bv::bs.stack; refs := rf|> in
        bc_next^* bs bs' ∧
        err_bv err bv ∧
        env_rs cenv env rs' rd' s' (bs' with stack := bs.stack))``,
  rpt gen_tac >>
  simp[compile_fake_exp_def,compile_Cexp_def,GSYM LEFT_FORALL_IMP_THM] >>
  simp[GSYM AND_IMP_INTRO] >>
  Q.PAT_ABBREV_TAC`Ce0 = exp_to_Cexp X (expf Y)` >>
  Q.PAT_ABBREV_TAC`p = label_closures Y X Ce0` >>
  PairCases_on`p`>>simp[]>> ntac 15 strip_tac >>
  qpat_assum`Abbrev(Ce0 = X)`mp_tac >>
  Q.PAT_ABBREV_TAC`exp' = expf X` >>
  `exp' = exp` by (
    rw[Abbr`exp'`] >>
    rpt AP_TERM_TAC >>
    REWRITE_TAC[GSYM MAP_APPEND] >>
    simp[MAP_EQ_f] ) >>
  qpat_assum`exp = X`kall_tac >>
  qpat_assum`Abbrev(exp' = X)`kall_tac >>
  pop_assum SUBST1_TAC >>
  strip_tac >>
  qmatch_abbrev_tac`G` >>
  fs[env_rs_def,LET_THM] >>
  qmatch_assum_abbrev_tac`LIST_REL syneq (env_to_Cenv cm env1) Cenv` >>
  `∃s1 beh1. evaluate menv ((Short"",tup)::cenv) s env1 exp (s1,beh1) ∧
            LIST_REL syneq (MAP (v_to_Cv cm) s') (MAP (v_to_Cv cm) s1) ∧
            (∀vs. (beh = Rval (Conv (Short "") vs)) ⇒
                ∃vs1. (beh1 = Rval (Conv (Short "") vs1)) ∧
                LIST_REL syneq (MAP (v_to_Cv cm) vs) (MAP (v_to_Cv cm) vs1)) ∧
            (∀err. (beh = Rerr err) ⇒ beh1 = beh)` by (
    qspecl_then[`menv`,`(Short "",tup)::cenv`,`s`,`env`,`exp`,`(s',beh)`]mp_tac(CONJUNCT1 evaluate_enveq) >>
    simp[] >>
    disch_then(qspecl_then[`s`,`env1`]mp_tac) >>
    discharge_hyps >- (
      simp[Abbr`env1`] >>
      simp[ALIST_REL_def,optionTheory.OPTREL_def] >>
      qx_gen_tac`k` >>
      Cases_on`ALOOKUP env k` >> simp[] >- (
        imp_res_tac ALOOKUP_FAILS >>
        simp[ALOOKUP_NONE,MEM_MAP,FORALL_PROD] >>
        metis_tac[] ) >>
      qexists_tac`THE (ALOOKUP env k)` >>
      simp[] >>
      match_mp_tac ALOOKUP_ALL_DISTINCT_MEM >>
      simp[MAP_MAP_o,combinTheory.o_DEF] >>
      simp[MEM_MAP] >>
      imp_res_tac ALOOKUP_MEM >>
      simp[EXISTS_PROD] >> metis_tac[] ) >>
    disch_then(Q.X_CHOOSE_THEN`res1`strip_assume_tac) >>
    fs[closed_under_menv_def] >>
    qspecl_then[`menv`,`(Short "",tup)::cenv`,`s`,`env`,`exp`,`(s',beh)`]mp_tac(CONJUNCT1 evaluate_closed) >>
    simp[] >> strip_tac >>
    qspecl_then[`menv`,`(Short "",tup)::cenv`,`s`,`env1`,`exp`,`res1`]mp_tac(CONJUNCT1 evaluate_closed) >>
    simp[] >>
    discharge_hyps >- (
      simp[Abbr`env1`,EVERY_MAP,MAP_MAP_o,combinTheory.o_DEF] >>
      fsrw_tac[DNF_ss][SUBSET_DEF,EVERY_MEM,MEM_MAP,MEM_FLAT] >>
      qx_gen_tac`z` >> strip_tac >>
      qsuff_tac`∃y. MEM y env ∧ (THE (ALOOKUP env (FST z)) = SND y)` >- metis_tac[] >>
      Cases_on`ALOOKUP env (FST z)` >- (
        imp_res_tac ALOOKUP_FAILS >>
        Cases_on`z`>>fs[] ) >>
      imp_res_tac ALOOKUP_MEM >>
      simp[EXISTS_PROD] >> metis_tac[] ) >>
    strip_tac >>
    PairCases_on`res1` >>
    map_every qexists_tac[`res10`,`res11`] >>
    simp[] >>
    conj_tac >- (
      simp[EVERY2_MAP] >>
      fsrw_tac[DNF_ss][EVERY2_EVERY,EVERY_MEM,FORALL_PROD] >>
      rfs[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM] >>
      rpt strip_tac >>
      match_mp_tac (MP_CANON enveq_v_to_Cv) >>
      metis_tac[MEM_EL] ) >>
    Cases_on`beh`>>fs[]>>
    qx_gen_tac`vs1` >> strip_tac >>
    rator_x_assum`enveq` mp_tac >> simp[Once enveq_cases] >>
    strip_tac >>
    qexists_tac`vs2` >> fs[] >>
    simp[EVERY2_MAP] >>
    fs[EVERY2_EVERY,EVERY_MEM,FORALL_PROD] >>
    rfs[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM] >>
    rpt strip_tac >>
    match_mp_tac (MP_CANON enveq_v_to_Cv) >>
    fs[EVERY_MEM] >> metis_tac[MEM_EL]) >>
  Cases_on`beh1 = Rerr Rtype_error`>>fs[]>-(
    Cases_on`beh`>>fs[markerTheory.Abbrev_def]>>rw[] ) >>
  qspecl_then[`menv`,`(Short"",tup)::cenv`,`s`,`env1`,`exp`,`(s1,beh1)`] mp_tac (CONJUNCT1 exp_to_Cexp_thm1) >>
  simp[] >>
  discharge_hyps >- (
    fs[closed_under_menv_def] >>
    simp[Abbr`env1`] >>
    fsrw_tac[DNF_ss][SUBSET_DEF,MEM_MAP] >>
    fsrw_tac[DNF_ss][EVERY_MEM,MEM_MAP,closed_under_cenv_def,FORALL_PROD,EXISTS_PROD] >>
    qmatch_abbrev_tac`a ∧ b ∧ c ∧ d` >>
    qsuff_tac`(b ∧ d) ∧ (a ∧ c)`>-rw[] >>
    conj_tac >- (
      simp[Abbr`b`,Abbr`d`,GSYM FORALL_AND_THM] >>
      fsrw_tac[DNF_ss][MEM_FLAT,MEM_MAP,FORALL_PROD,SUBSET_DEF,EXISTS_PROD] >>
      metis_tac[] ) >>
    simp[Abbr`a`,Abbr`c`] >>
    simp[GSYM FORALL_AND_THM,GSYM IMP_CONJ_THM] >>
    map_every qx_gen_tac[`k`,`v`] >> strip_tac >>
    Cases_on`ALOOKUP env k` >- (
      imp_res_tac ALOOKUP_NONE >>
      fs[MEM_MAP,FORALL_PROD] ) >>
    imp_res_tac ALOOKUP_MEM >>
    simp[] >>
    metis_tac[SUBSET_DEF,IN_INSERT] ) >>
  disch_then (qspec_then `cm` mp_tac) >>
  discharge_hyps >- (
    fs[good_cmap_def,FAPPLY_FUPDATE_THM,Abbr`cm`] >>
    rw[] >>
    fs[SET_EQ_SUBSET,SUBSET_DEF,MEM_MAP,GSYM LEFT_FORALL_IMP_THM] >>
    qmatch_assum_rename_tac`MEM pp cenv`[] >>
    first_x_assum(qspec_then`FST pp`mp_tac) >>
    REWRITE_TAC[FLOOKUP_DEF] >>
    simp_tac std_ss [] >>
    discharge_hyps >- metis_tac[] >>
    metis_tac[]) >>
  `MAP FST env1 = rs.rbvars` by (
    simp[Abbr`env1`,MAP_MAP_o,combinTheory.o_DEF] ) >>
  disch_then(qx_choosel_then[`Cs'0`,`Cv0`]strip_assume_tac o SIMP_RULE(srw_ss())[EXISTS_PROD]) >>
  qspecl_then[`LENGTH rs.rbvars`,`rs.rnext_label`,`Ce0`]mp_tac(CONJUNCT1 label_closures_thm) >>
  discharge_hyps >- (
    simp[Abbr`Ce0`] >>
    match_mp_tac free_vars_exp_to_Cexp_matchable >>
    simp[] >>
    fsrw_tac[DNF_ss][SUBSET_DEF,MEM_FLAT,is_null_def,MEM_MAP] >>
    rw[] >> rfs[] >> res_tac >> fs[] >> metis_tac[]) >>
  simp[] >> strip_tac >>
  qpat_assum`X = bc`mp_tac >>
  Q.PAT_ABBREV_TAC`cce = compile_code_env X Y` >>
  qpat_assum`Abbrev(cce = X)`mp_tac >>
  Q.PAT_ABBREV_TAC`s0 = X with out := Y` >>
  strip_tac >>
  qspecl_then[`LENGTH rs.rbvars`,`s0`,`p0`]mp_tac compile_code_env_thm >>
  simp[] >>
  discharge_hyps >- (
    simp[ALL_DISTINCT_GENLIST,EVERY_GENLIST,Abbr`s0`] ) >>
  disch_then(Q.X_CHOOSE_THEN`c0`strip_assume_tac) >>
  qmatch_assum_rename_tac`set (free_vars Ce) ⊆ set (free_vars Ce0)`[] >>
  Q.PAT_ABBREV_TAC`renv:ctenv = GENLIST X (LENGTH rs.rbvars)` >>
  qspecl_then[`renv`,`TCNonTail`,`LENGTH rs.rbvars + 2`,`cce`,`Ce`](Q.X_CHOOSE_THEN`bc1`strip_assume_tac)(CONJUNCT1 compile_append_out) >>
  Q.PAT_ABBREV_TAC`cmp = compile renv X Y Z A with out := U` >>
  qspecl_then[`vv0`,`rs.rbvars`,`cmp`,`0`]mp_tac (INST_TYPE[alpha|->``:string``]compile_shadows_thm) >>
  simp[] >> disch_then(Q.X_CHOOSE_THEN`c1`strip_assume_tac) >>
  Q.PAT_ABBREV_TAC`csd = compile_shadows X Y Z A` >>
  Q.ISPECL_THEN[`vv1`,`csd`,`LENGTH vv0`]mp_tac compile_news_thm >>
  simp[] >> disch_then(Q.X_CHOOSE_THEN`c2`strip_assume_tac) >>
  simp[] >> rw[Abbr`s0`] >>
  fs[Abbr`cmp`] >>
  qunabbrev_tac`G` >>
  Q.PAT_ABBREV_TAC`l1 = LENGTH X + rs.rnext_label` >>
  qmatch_abbrev_tac`G` >>
  `bc_fetch bs = SOME (PushPtr (Lab l1))` by (
    match_mp_tac bc_fetch_next_addr >>
    qexists_tac`bc0` >> simp[] ) >>
  `ALL_DISTINCT (FILTER is_Label bs.code)` by (
    simp[FILTER_APPEND,SUM_APPEND,ADD1,FILTER_REVERSE,SUM_REVERSE,MAP_REVERSE] >>
    fs[GSYM FILTER_EQ_NIL,combinTheory.o_DEF] >>
    simp[ALL_DISTINCT_APPEND,ALL_DISTINCT_REVERSE,MEM_FILTER] >>
    fsrw_tac[DNF_ss][EVERY_MEM,between_def,FILTER_EQ_NIL,MEM_MAP,MEM_FILTER] >>
    fs[is_Label_rwt] >>
    fsrw_tac[DNF_ss][MEM_GENLIST,Abbr`l1`] >>
    rw[] >> spose_not_then strip_assume_tac >> res_tac >> DECIDE_TAC ) >>
  `bc_find_loc bs (Lab l1) = SOME (next_addr bs.inst_length (DROP 3 (REVERSE bs.code)))` by (
    simp[bc_find_loc_def] >>
    match_mp_tac bc_find_loc_aux_ALL_DISTINCT >>
    qexists_tac`LENGTH bs.code - 4` >>
    simp[TAKE_APPEND1,TAKE_APPEND2,REVERSE_APPEND,EL_APPEND1,EL_APPEND2] >>
    simp[ADD1,FILTER_REVERSE,SUM_REVERSE] >>
    simp[FILTER_APPEND,SUM_APPEND,ADD1,FILTER_REVERSE,SUM_REVERSE,MAP_REVERSE] >>
    rfs[ALL_DISTINCT_APPEND,FILTER_APPEND,FILTER_REVERSE,ALL_DISTINCT_REVERSE] >>
    metis_tac[] ) >>
  `bc_next bs (bump_pc bs with stack := CodePtr (THE (bc_find_loc bs (Lab l1)))::bs.stack)` by (
    simp[bc_eval1_thm,bc_eval1_def] ) >>
  qmatch_assum_abbrev_tac`bc_next bs bs1` >>
  `bc_fetch bs1 = SOME PushExc` by (
    match_mp_tac bc_fetch_next_addr >>
    qexists_tac`bc0 ++ [PushPtr (Lab l1)]` >>
    simp[Abbr`bs1`,bump_pc_def,FILTER_APPEND,SUM_APPEND] ) >>
  `bc_next bs1 (bump_pc bs1 with <| stack := StackPtr (bs1.handler)::bs1.stack ; handler := LENGTH bs1.stack|>)` by (
    simp[bc_eval1_def,bc_eval1_thm] ) >>
  qmatch_assum_abbrev_tac`bc_next bs1 bs2` >>
  `bc_next^* bs bs2` by metis_tac[RTC_TRANSITIVE,transitive_def,RTC_SUBSET] >>
  qpat_assum`bc_next bs bs1`kall_tac >>
  qpat_assum`bc_next bs1 bs2`kall_tac >>
  qpat_assum`Abbrev(bs2 = X)`mp_tac >>
  qpat_assum`bs.code = X`(assume_tac o SYM) >>
  simp[bump_pc_def,Abbr`bs1`] >>
  strip_tac >>
  qpat_assum`bc_fetch X = Y`kall_tac >>
  qpat_assum`bc_fetch X = Y`kall_tac >>
  qpat_assum`Abbrev(bs2 = X)`mp_tac >>
  Q.PAT_ABBREV_TAC`l1a = next_addr Y (DROP 3 X)` >>
  strip_tac >>
  last_x_assum(qspecl_then[`bs2`,`bc0 ++ [PushPtr(Lab l1);PushExc]`]mp_tac) >>
  qpat_assum`X = bs.code`(assume_tac o SYM) >>
  simp[Abbr`bs2`] >>
  discharge_hyps >- (
    simp[FILTER_APPEND,SUM_APPEND] >>
    simp[MEM_MAP,MEM_GENLIST,MEM_FILTER,GSYM LEFT_FORALL_IMP_THM,is_Label_rwt] >>
    fs[EVERY_FILTER,is_Label_rwt,EVERY_MEM] >>
    fsrw_tac[DNF_ss,ARITH_ss][Abbr`l1`] >>
    rw[] >> res_tac >> DECIDE_TAC ) >>
  strip_tac >>
  qmatch_assum_abbrev_tac`bc_next bs2 bs1` >>
  rfs[] >>
  qmatch_assum_abbrev_tac`Cevaluate Cs0 Cenv0 Ce0 (Cs'0,Cv0)` >>
  qspecl_then[`Cs0`,`Cenv0`,`Ce0`,`Cs'0,Cv0`]mp_tac(CONJUNCT1 Cevaluate_syneq) >> simp[] >>
  disch_then(qspecl_then[`$=`,`Cs`,`Cenv`,`Ce`]mp_tac) >>
  `LENGTH Cenv0 = LENGTH rs.rbvars` by rw[Abbr`Cenv0`,env_to_Cenv_MAP,Abbr`env1`] >>
  `LENGTH Cenv = LENGTH rs.rbvars` by fs[EVERY2_EVERY,Abbr`env1`] >>
  simp[EXISTS_PROD] >>
  discharge_hyps >- (
    qpat_assum`LIST_REL syneq Cenv0 Cenv`mp_tac >>
    ntac 2 (pop_assum mp_tac) >>
    rpt (pop_assum kall_tac) >>
    simp[EVERY2_EVERY,EVERY_MEM,FORALL_PROD] >>
    simp[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM] ) >>
  disch_then(qx_choosel_then[`Cs'`,`Cv`]strip_assume_tac) >>
  qspecl_then[`Cs`,`Cenv`,`Ce`,`(Cs',Cv)`]mp_tac(CONJUNCT1 compile_val) >> simp[] >>
  disch_then(qspecl_then[`rd`,`cce`,`renv`,`LENGTH rs.rbvars + 2`,`bs1`
    ,`bc0 ++ [PushPtr(Lab l1);PushExc]++c0`,`DROP (LENGTH bc0 + 2 + LENGTH c0) bs.code`
    ,`bc0 ++ [PushPtr(Lab l1);PushExc]++c0`,`REVERSE bc1`]mp_tac) >>
  simp[DROP_APPEND1,DROP_APPEND2,DROP_LENGTH_NIL_rwt] >>
  discharge_hyps >- (
    simp[Abbr`bs1`,DROP_APPEND1,DROP_APPEND2,DROP_LENGTH_NIL] >>
    conj_asm1_tac >- (
      simp[FILTER_APPEND,ALL_DISTINCT_APPEND] >>
      fsrw_tac[DNF_ss][EVERY_MEM,MEM_FILTER,is_Label_rwt,MEM_MAP,MEM_GENLIST,between_def,Abbr`l1`] >>
      rw[] >> spose_not_then strip_assume_tac >> res_tac >> DECIDE_TAC ) >>
    conj_tac >- PROVE_TAC[code_env_cd_append,APPEND_ASSOC] >>
    conj_tac >- PROVE_TAC[code_env_cd_append,APPEND_ASSOC] >>
    conj_tac >- (
      match_mp_tac SUBSET_TRANS >>
      HINT_EXISTS_TAC >>
      simp[Abbr`Ce0`] >>
      match_mp_tac free_vars_exp_to_Cexp_matchable >>
      simp[] >>
      fs[Cenv_bs_def,EVERY2_EVERY] >>
      fsrw_tac[DNF_ss][SUBSET_DEF,is_null_def,MEM_MAP,MEM_FLAT] >>
      rw[] >> rfs[] >> res_tac >> fs[] >> metis_tac[]) >>
    conj_tac >- (
      SUBST1_TAC(DECIDE``2:num = 1 + 1``) >>
      REWRITE_TAC[ADD_ASSOC] >>
      Q.PAT_ABBREV_TAC`bs1:bc_state = X` >>
      match_mp_tac Cenv_bs_imp_incsz >>
      qexists_tac`bs1 with stack := TL bs1.stack` >>
      simp[Abbr`bs1`,bc_state_component_equality] >>
      Q.PAT_ABBREV_TAC`bs1:bc_state = X` >>
      match_mp_tac Cenv_bs_imp_incsz >>
      qexists_tac`bs1 with stack := TL bs1.stack` >>
      simp[Abbr`bs1`,bc_state_component_equality] >>
      Q.PAT_ABBREV_TAC`bs1:bc_state = X` >>
      match_mp_tac Cenv_bs_append_code >>
      qexists_tac`bs1 with code := bc0` >>
      simp[bc_state_component_equality,Abbr`bs1`] >>
      match_mp_tac Cenv_bs_pc_handler >>
      qexists_tac`bs with code := bc0` >>
      simp[bc_state_component_equality]) >>
    qpat_assum`ALL_DISTINCT X`mp_tac >>
    qpat_assum`ALL_DISTINCT X`kall_tac >>
    strip_tac >>
    fsrw_tac[DNF_ss,ARITH_ss][EVERY_MEM,between_def,MEM_MAP,FILTER_APPEND,ALL_DISTINCT_APPEND,MEM_FILTER,is_Label_rwt,MEM_GENLIST,Abbr`l1`] >>
    rw[] >> spose_not_then strip_assume_tac >> res_tac >> fsrw_tac[ARITH_ss][] ) >>
  Cases_on`beh`>>fs[Abbr`G`]>- (
    disch_then(strip_assume_tac o CONJUNCT1) >>
    gen_tac >> ntac 2 strip_tac >> fs[] >>
    `∃u Cvs. (Cv = Cval(CConv u Cvs)) ∧ EVERY2 syneq (MAP (v_to_Cv cm) vs1) Cvs` by (
      qpat_assum`X Y Cv0`mp_tac >>
      simp[v_to_Cv_def,Once IntLangTheory.syneq_cases] >>
      simp_tac(srw_ss()++DNF_ss)[] >>
      simp[Abbr`cm`,vs_to_Cvs_MAP] >>
      gen_tac >> strip_tac >>
      qpat_assum`X Y Cv`mp_tac >>
      simp[Once IntLangTheory.syneq_cases] >>
      simp_tac(srw_ss()++DNF_ss)[] >>
      metis_tac[EVERY2_syneq_trans] ) >>
    qpat_assum`∀x. Y`mp_tac >>
    simp[Abbr`bs1`] >>
    simp_tac(srw_ss()++DNF_ss)[code_for_push_def,LET_THM] >>
    map_every qx_gen_tac[`rf`,`rd'`,`bv`] >> strip_tac >>
    qunabbrev_tac`bs2` >>
    qmatch_assum_abbrev_tac`bc_next^* bs1 bs2` >>
    rator_x_assum`Cv_bv`mp_tac >>
    simp[Once Cv_bv_cases] >>
    disch_then(Q.X_CHOOSE_THEN`bvs`strip_assume_tac) >>
    `bc_fetch bs2 = SOME PopExc` by (
      match_mp_tac bc_fetch_next_addr >>
      qexists_tac`TAKE (LENGTH bc0 + 2 + LENGTH c0 + LENGTH bc1) bs.code` >>
      simp[Abbr`bs2`,TAKE_APPEND1,TAKE_APPEND2,TAKE_LENGTH_ID_rwt] ) >>
    `bc_next bs2 (bump_pc bs2 with <| handler := bs.handler; stack := bv::CodePtr l1a::bs.stack |>)` by (
      simp[bc_eval1_def,bc_eval1_thm,bump_pc_def] >>
      simp[Abbr`bs2`,EL_APPEND1,ADD1,EL_APPEND2] >>
      simp[bc_state_component_equality,TAKE_APPEND1,TAKE_APPEND2] ) >>
    qmatch_assum_abbrev_tac`bc_next bs2 bs2'` >>
    `bc_fetch bs2' = SOME (Stack (Pops 1))` by (
      match_mp_tac bc_fetch_next_addr >>
      simp[Abbr`bs2'`,bump_pc_def,Abbr`bs2`] >>
      qexists_tac`TAKE (LENGTH bc0 + 2 + LENGTH c0 + LENGTH bc1 + 1) bs.code` >>
      simp[TAKE_APPEND1,TAKE_APPEND2] >>
      simp[SUM_APPEND,FILTER_APPEND] ) >>
    `bc_next bs2' (bump_pc bs2' with <| stack := bv::bs.stack |>)` by (
      simp[bc_eval1_thm,bc_eval1_def] >>
      simp[bc_eval_stack_def,Abbr`bs2'`,bump_pc_def,Abbr`bs2`] ) >>
    qmatch_assum_abbrev_tac`bc_next bs2' bs2''` >>
    `bc_next^* bs1 bs2''` by metis_tac[RTC_TRANSITIVE,transitive_def,RTC_SUBSET] >>
    qpat_assum`bc_next bs2 X`kall_tac >>
    qpat_assum`bc_next bs2' X`kall_tac >>
    qpat_assum`Abbrev(bs2''=X)`mp_tac >>
    simp[Abbr`bs2'`,bump_pc_def,Abbr`bs2`] >>
    strip_tac >>
    qpat_assum`bc_fetch X = Y`kall_tac >>
    qpat_assum`bc_fetch X = Y`kall_tac >>
    qmatch_assum_rename_tac`Abbrev(bs2 = X)`["X"] >>
    last_x_assum(qspecl_then[`bs2 with code := TAKE (LENGTH bc0 + LENGTH bc1 + LENGTH c0 + 4 + LENGTH c1) bs.code`
                            ,`TAKE (LENGTH bc0 + LENGTH bc1 + LENGTH c0 + 4) bs.code`,`4+u`,`bvs`,`bs.stack`]mp_tac) >>
    `LENGTH rs.rbvars ≤ LENGTH bs.stack` by (
      qpat_assum`Cenv_bs rd Cs Cenv renv (LENGTH rs.rbvars)X `mp_tac >>
      simp[Cenv_bs_def,EVERY2_EVERY,Abbr`renv`,EVERY_MEM,FORALL_PROD,MEM_ZIP,GSYM LEFT_FORALL_IMP_THM,CompilerLibTheory.el_check_def]>>
      strip_tac >>
      spose_not_then strip_assume_tac >>
      first_x_assum(qspec_then`LENGTH bs.stack`mp_tac) >>
      simp[] ) >>
    `LENGTH vs = LENGTH vv0 + LENGTH vv1` by
      metis_tac[PART_LENGTH,PARTITION_DEF,LENGTH_NIL,ADD_0,ADD_SYM] >>
    `∀x. MEM x (vars ++ ([] ++ [])) ⇔ MEM x (vv0 ++ vv1)` by
      metis_tac[PART_MEM,PARTITION_DEF] >>
    `(∀x. MEM x vv0 ⇒ (λv. MEM v rs.rbvars) x) ∧
     (∀x. MEM x vv1 ⇒ ¬ (λv. MEM v rs.rbvars) x)` by (
      qpat_assum`PARTITION X Y = Z`(assume_tac o SYM) >>
      fs[PARTITION_DEF] >>
      imp_res_tac PARTs_HAVE_PROP >>
      fs[]) >>
    `PERM vars (vv0 ++ vv1)` by metis_tac[PERM_PARTITION] >>
    `ALL_DISTINCT (vv0 ++ vv1)` by (
      metis_tac[ALL_DISTINCT_PERM] ) >>
    fs[] >>
    discharge_hyps >- (
      simp[Abbr`bs2`,TAKE_APPEND1,TAKE_APPEND2,SUM_APPEND,FILTER_APPEND] >>
      rfs[] >>
      conj_tac >- (
        rw[] >> fs[EVERY2_EVERY] >>
        qpat_assum`syneq Cv0 X`mp_tac >>
        qpat_assum`syneq X Cv0`mp_tac >>
        simp[v_to_Cv_def]) >>
      simp[SUBSET_DEF] >>
      metis_tac[ALL_DISTINCT_PERM,PARTITION_DEF,PERM_PARTITION,ALL_DISTINCT_APPEND] ) >>
    strip_tac >>
    qmatch_assum_abbrev_tac`bc_next^* bs2' bs3'` >>
    `bc_next^* (bs2' with code := bs2'.code ++ c1 ++ c2) (bs3' with code := bs3'.code ++ c1 ++ c2)` by (
      match_mp_tac RTC_bc_next_append_code >>
      map_every qexists_tac[`bs2'`,`bs3'`] >>
      simp[Abbr`bs2'`,Abbr`bs3'`,bc_state_component_equality] ) >>
    first_x_assum(qspecl_then[`bs3' with code := bs3'.code ++ c2`,`bs3'.code`,`4+u`,`bvs`]mp_tac) >>
    simp[Abbr`bs3'`] >>
    discharge_hyps >- ( fs[EVERY2_EVERY] ) >>
    strip_tac >>
    qmatch_assum_abbrev_tac`bc_next^* bs4 bs5` >>
    map_every qexists_tac[`TL bs5.stack`,`rf`,`rd'`
      ,`REVERSE (DROP (LENGTH vv0) Cvs) ++
        GENLIST (λx. if x < LENGTH rs.rbvars ∧ MEM (EL x rs.rbvars) vv0 then EL (THE (find_index (EL x rs.rbvars) vv0 0)) Cvs else EL x Cenv) (LENGTH Cenv)`
      ,`Cs'`] >>
    conj_tac >- (
      match_mp_tac (SIMP_RULE std_ss [transitive_def]RTC_TRANSITIVE) >>
      qmatch_assum_abbrev_tac`bc_next^* bs bs0` >>
      qmatch_assum_abbrev_tac`bc_next bs0' bs1` >>
      `bs0' = bs0` by (
        simp[Abbr`bs0`,Abbr`bs0'`,bc_state_component_equality] >>
        simp[SUM_APPEND,FILTER_APPEND] ) >>
      qexists_tac`bs2` >>
      conj_tac >- metis_tac[RTC_TRANSITIVE,transitive_def,RTC_SUBSET] >>
      qmatch_assum_abbrev_tac`bc_next^* bs2' bs3'` >>
      `bc_next^* (bs2' with code := bs.code) (bs3' with code := bs.code)` by (
        match_mp_tac RTC_bc_next_append_code >>
        map_every qexists_tac[`bs2'`,`bs3'`] >>
        simp[bc_state_component_equality,Abbr`bs2'`,Abbr`bs3'`] >>
        simp[TAKE_APPEND1,TAKE_APPEND2]) >>
      `bc_next^* (bs4 with code := bs.code) (bs5 with code := bs.code)` by (
        match_mp_tac RTC_bc_next_append_code >>
        map_every qexists_tac[`bs4`,`bs5`] >>
        simp[bc_state_component_equality,Abbr`bs4`,Abbr`bs5`] >>
        simp[TAKE_APPEND1,TAKE_APPEND2]) >>
      `bs4 with code := bs.code = bs3' with code := bs.code` by (
        simp[Abbr`bs4`,Abbr`bs3'`,bc_state_component_equality,Abbr`bs2'`] ) >>
      `bs2 = bs2' with code := bs.code` by (
        simp[Abbr`bs2'`,bc_state_component_equality,Abbr`bs2`] ) >>
      `bc_next^* bs2 (bs5 with code := bs.code)` by metis_tac[RTC_TRANSITIVE,transitive_def] >>
      match_mp_tac (SIMP_RULE std_ss [transitive_def]RTC_TRANSITIVE) >>
      qexists_tac`bs5 with code := bs.code` >> simp[] >>
      simp[RTC_eq_NRC] >>
      qexists_tac`SUC(SUC(SUC 0))` >>
      simp[NRC] >>
      simp[Abbr`bs5`,Abbr`bs2'`,Abbr`bs2`] >>
      ntac 13 (pop_assum kall_tac) >>
      Q.PAT_ABBREV_TAC`st:bc_value list = X ++ Y` >>
      simp[bc_eval1_thm] >>
      simp[TAKE_APPEND1,TAKE_APPEND2,REVERSE_APPEND] >>
      Q.PAT_ABBREV_TAC`cd = X ++ c2` >>
      qho_match_abbrev_tac`∃z. bc_eval1 bs6 = SOME z ∧ P z` >>
      `bc_fetch bs6 = SOME (Stack Pop)` by (
        match_mp_tac bc_fetch_next_addr >>
        qexists_tac`cd`>>simp[Abbr`bs6`] ) >>
      simp[bc_eval1_def,bump_pc_def] >>
      simp[Abbr`bs6`,bc_eval_stack_def] >>
      simp[Abbr`P`] >>
      qho_match_abbrev_tac`∃z. bc_eval1 bs6 = SOME z ∧ P z` >>
      `bc_fetch bs6 = SOME (Stack (PushInt i0))` by (
        match_mp_tac bc_fetch_next_addr >>
        qexists_tac`cd++[Stack Pop]`>>
        simp[Abbr`bs6`,SUM_APPEND,FILTER_APPEND] ) >>
      simp[bc_eval1_def,bump_pc_def] >>
      simp[Abbr`bs6`,bc_eval_stack_def] >>
      simp[Abbr`P`] >>
      Q.PAT_ABBREV_TAC`l2 = Lab X.next_label` >>
      qho_match_abbrev_tac`bc_eval1 bs6 = SOME z` >>
      `bc_fetch bs6 = SOME (Jump l2)` by (
        match_mp_tac bc_fetch_next_addr >>
        qexists_tac`cd++[Stack Pop;Stack (PushInt i0)]`>>
        simp[Abbr`bs6`,SUM_APPEND,FILTER_APPEND] ) >>
      `bc_find_loc bs6 l2 = SOME (next_addr bs.inst_length (TAKE (LENGTH bs.code - 1) bs.code))` by (
        simp[Abbr`l2`,bc_find_loc_def] >>
        match_mp_tac bc_find_loc_aux_ALL_DISTINCT >>
        qexists_tac`LENGTH bs.code - 2` >>
        simp[Abbr`bs6`,EL_APPEND1,EL_APPEND2] >>
        simp[SUM_APPEND,FILTER_APPEND,TAKE_APPEND1,TAKE_APPEND2] ) >>
      simp[bc_eval1_def] >>
      simp[Abbr`z`,Abbr`bs6`,bc_state_component_equality,SUM_APPEND,FILTER_APPEND,Abbr`cd`,TAKE_APPEND1,TAKE_APPEND2] ) >>
    simp[Abbr`bs5`] >>
    ntac 5 (pop_assum kall_tac) >>
    conj_tac >- ( fs[MAP_ZIP] >> fs[EXTENSION] >> metis_tac[] ) >>
    conj_tac >- (
      simp[ALL_DISTINCT_APPEND,ALL_DISTINCT_REVERSE] >>
      qpat_assum`set rs.rbvars = X`(SUBST1_TAC o SYM) >>
      metis_tac[ALL_DISTINCT_PERM,ALL_DISTINCT_APPEND] ) >>
    conj_tac >- metis_tac[EVERY2_syneq_trans] >>
    conj_tac >- (
      qunabbrev_tac`l1` >>
      match_mp_tac EVERY2_APPEND_suff >>
      conj_tac >- (
        simp[MAP_REVERSE,env_to_Cenv_MAP] >>
        match_mp_tac EVERY2_REVERSE >>
        match_mp_tac EVERY2_syneq_trans >>
        qexists_tac`DROP (LENGTH vv0) (MAP (v_to_Cv cm) vs)` >>
        reverse conj_tac >- (
          match_mp_tac EVERY2_DROP >>
          simp[] >>
          metis_tac[EVERY2_syneq_trans]) >>
        simp[MAP_MAP_o,combinTheory.o_DEF] >>
        qmatch_abbrev_tac`LIST_REL R l1 l2` >>
        qsuff_tac`l1 = l2`>-metis_tac[EVERY2_syneq_refl] >>
        simp[Abbr`l1`,Abbr`l2`,LIST_EQ_REWRITE] >>
        fs[EVERY2_EVERY] >>
        rw[EL_MAP] >>
        simp[EL_DROP,EL_MAP] >>
        qunabbrev_tac`R` >>
        ntac 2 (pop_assum mp_tac) >>
        `LENGTH vs = LENGTH (vv0 ++ vv1)` by metis_tac[PERM_LENGTH] >>
        pop_assum mp_tac >>
        rpt (pop_assum kall_tac) >>
        rw[] >>
        Q.PAT_ABBREV_TAC`al = ZIP (vv0++vv1,vs)` >>
        `ALL_DISTINCT (MAP FST al)` by (
          simp[Abbr`al`,MAP_ZIP] ) >>
        `MEM (EL x vv1, EL (x + LENGTH vv0) vs) al` by (
          simp[Abbr`al`,MEM_ZIP] >>
          qexists_tac`x + LENGTH vv0` >>
          simp[EL_APPEND2] ) >>
        imp_res_tac ALOOKUP_ALL_DISTINCT_MEM >>
        simp[ALOOKUP_APPEND] ) >>
      map_every qunabbrev_tac[`Cenv0`,`env1`] >>
      qpat_assum`EVERY2 syneq X Cenv`mp_tac >>
      simp[EVERY2_EVERY,env_to_Cenv_MAP,EVERY_MEM,FORALL_PROD] >>
      simp[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM] >>
      strip_tac >> qx_gen_tac`n` >> strip_tac >>
      first_x_assum(qspec_then`n`mp_tac) >>
      simp[EL_MAP] >> strip_tac >> rw[] >- (
        simp[ALOOKUP_APPEND] >>
        Q.ISPECL_THEN[`vv0`,`EL n rs.rbvars`,`0:num`]mp_tac find_index_MEM >>
        simp[] >> disch_then(Q.X_CHOOSE_THEN`i`strip_assume_tac) >>
        `MEM (EL n rs.rbvars, EL i vs) (ZIP (vv0 ++ vv1,vs))` by (
          simp[MEM_ZIP] >>
          qexists_tac`i` >>
          simp[EL_APPEND1] ) >>
        `ALL_DISTINCT (MAP FST (ZIP (vv0 ++ vv1,vs)))` by (
          simp[MAP_ZIP] >>
          metis_tac[PERM_PARTITION,ALL_DISTINCT_PERM] ) >>
        imp_res_tac ALOOKUP_ALL_DISTINCT_MEM >>
        simp[] >>
        qpat_assum`LIST_REL syneq X Cvs`mp_tac >>
        qpat_assum`LIST_REL syneq X (MAP Y vs1)`mp_tac >>
        simp[EVERY2_EVERY,EVERY_MEM,FORALL_PROD] >>
        ntac 2 strip_tac >> ntac 2 (qpat_assum `∀x y. Z`mp_tac) >>
        simp[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM] >>
        ntac 2 strip_tac >> ntac 2 (first_x_assum(qspec_then`i`mp_tac)) >>
        simp[EL_MAP] >>
        metis_tac[syneq_trans] ) >>
      `EL n rs.rbvars ∉ set (MAP FST (ZIP (vv0++vv1,vs)))` by (
        simp[MAP_ZIP] >>
        qpat_assum`PARTITION X Y = Z`(mp_tac o SYM) >>
        qpat_assum`set rs.rbvars = X`kall_tac >>
        rw[PARTITION_DEF] >>
        imp_res_tac PARTs_HAVE_PROP >> fs[] >>
        METIS_TAC[MEM_EL] ) >>
      fs[GSYM ALOOKUP_NONE] >>
      simp[ALOOKUP_APPEND] ) >>
    qspecl_then[`Cs`,`Cenv`,`Ce`,`Cs',Cval (CConv u Cvs)`]mp_tac(CONJUNCT1 Cevaluate_Clocs) >>
    simp[] >> strip_tac >>
    conj_tac >- (
      `LENGTH Cvs = LENGTH vs` by fs[EVERY2_EVERY] >>
      `LENGTH vv0 ≤ LENGTH Cvs` by simp[] >>
      fsrw_tac[DNF_ss][SUBSET_DEF] >>
      conj_tac >- ( rw[] >> imp_res_tac MEM_DROP >> metis_tac[] ) >>
      simp[MEM_GENLIST] >>
      qspecl_then[`Cs`,`Cenv`,`Ce`,`Cs',Cval (CConv u Cvs)`]mp_tac(CONJUNCT1 Cevaluate_store_SUBSET) >>
      simp[] >> strip_tac >>
      rw[] >> fs[] >>
      ntac 2 (pop_assum mp_tac) >> rw[] >- (
        qmatch_assum_rename_tac`MEM (EL z rs.rbvars) vv0`[] >>
        Q.ISPECL_THEN[`vv0`,`EL z rs.rbvars`,`0:num`]mp_tac find_index_MEM >> rw[] >>
        fs[] >>
        `i < LENGTH Cvs` by simp[] >>
        metis_tac[MEM_EL] ) >>
      qmatch_assum_rename_tac`x ∈ all_Clocs (EL z Cenv)`[] >>
      `z < LENGTH Cenv` by simp[] >>
      metis_tac[MEM_EL,LESS_LESS_EQ_TRANS] ) >>
    qspecl_then[`Cs`,`Cenv`,`Ce`,`Cs',Cval (CConv u Cvs)`]mp_tac(CONJUNCT1 Cevaluate_all_vlabs) >>
    simp[] >> strip_tac >>
    conj_tac >- (
      simp[EVERY_REVERSE,EVERY_GENLIST] >>
      conj_tac >- (
        match_mp_tac (MP_CANON EVERY_DROP) >>
        fs[EVERY2_EVERY] >> simp[] ) >>
      rw[] >- (
        qmatch_assum_rename_tac`MEM (EL z rs.rbvars) vv0`[] >>
        Q.ISPECL_THEN[`vv0`,`EL z rs.rbvars`,`0:num`]mp_tac find_index_MEM >> rw[] >>
        fs[EVERY2_EVERY] >>
        `i < LENGTH Cvs` by simp[] >>
        fs[EVERY_MEM] >>
        metis_tac[MEM_EL] ) >>
      `x < LENGTH Cenv` by simp[] >>
      fs[EVERY_MEM] >>
      metis_tac[MEM_EL] ) >>
    qspecl_then[`Cs`,`Cenv`,`Ce`,`Cs',Cval (CConv u Cvs)`]mp_tac(CONJUNCT1 Cevaluate_vlabs) >>
    simp[SUBSET_DEF,FORALL_PROD] >> strip_tac >>
    simp[REVERSE_APPEND] >>
    SUBST1_TAC(prove(``bc0 ++ PushPtr (Lab l1)::PushExc::(c0 ++ REVERSE bc1) = bc0 ++ [PushPtr (Lab l1);PushExc] ++ c0 ++ REVERSE bc1``,simp[])) >>
    Q.PAT_ABBREV_TAC`cd:bc_inst list = X++Y` >>
    qmatch_assum_abbrev_tac`ALL_DISTINCT (FILTER is_Label cd)` >>
    conj_tac >- (
      fs[FORALL_PROD,EVERY_MEM] >>
      metis_tac[code_env_cd_append,APPEND_ASSOC] ) >>
    conj_tac >- (
      fs[GSYM FORALL_PROD] >>
      qx_gen_tac`p` >> strip_tac >>
      qsuff_tac `p ∈ vlabs_list Cvs ∨ p ∈ vlabs_list Cenv` >- (
        fs[EVERY_MEM] >>
        metis_tac[code_env_cd_append,APPEND_ASSOC] ) >>
      fs[vlabs_list_APPEND,vlabs_list_REVERSE] >- (
        disj1_tac >>
        `LENGTH vv0 ≤ LENGTH Cvs` by (
          fs[EVERY2_EVERY] >> simp[] ) >>
        rfs[vlabs_list_MAP] >>
        metis_tac[MEM_DROP] ) >>
      fs[vlabs_list_MAP,MEM_GENLIST] >>
      pop_assum mp_tac >> rw[] >- (
        qmatch_assum_rename_tac`MEM z vv0`[] >>
        Q.ISPECL_THEN[`vv0`,`z`,`0:num`]mp_tac find_index_MEM >>
        rw[] >> fs[] >>
        `i < LENGTH Cvs` by (
          fs[EVERY2_EVERY] >> simp[] ) >>
        metis_tac[MEM_EL] ) >>
      qmatch_assum_rename_tac`p ∈ vlabs (EL i Cenv)`[] >>
      `i < LENGTH Cenv` by ( fs[EVERY2_EVERY] >> simp[]) >>
      metis_tac[MEM_EL] ) >>
    map_every qunabbrev_tac[`cd`] >>
    ntac 4 (pop_assum kall_tac) >>
    Q.PAT_ABBREV_TAC`bsc:bc_state = X` >>
    match_mp_tac Cenv_bs_append_code >>
    qexists_tac`bsc with code := bc0 ++ [PushPtr(Lab l1); PushExc] ++ c0` >>
    simp[bc_state_component_equality,Abbr`bsc`] >>
    qmatch_abbrev_tac`Cenv_bs rd' Cs' X Y Z bsc` >>
    qsuff_tac`Cenv_bs rd' Cs' X Y Z (bsc with pc := next_addr bs.inst_length (bc0 ++ [PushPtr(Lab l1);PushExc] ++ c0 ++ REVERSE bc1))`
      >- simp[Cenv_bs_with_pc] >>
    fs[Cenv_bs_def] >>
    reverse conj_tac >- (
      fs[s_refs_def,good_rd_def,Abbr`bsc`] ) >>
    simp[Abbr`X`,Abbr`Y`,Abbr`Z`,Abbr`bsc`] >>
    fs[option_case_NONE_F] >>
    fs[EVERY2_EVERY] >>
    conj_tac >- DECIDE_TAC >>
    fs[EVERY_MEM,FORALL_PROD] >>
    `LENGTH (DROP (LENGTH vv0) Cvs) = LENGTH vv1` by simp[] >>
    rfs[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM] >>
    qx_gen_tac`n`>>strip_tac >>
    simp[CompilerLibTheory.el_check_def] >>
    Cases_on`n < LENGTH vv1`>>simp[EL_APPEND1,EL_APPEND2] >- (
      simp[EL_REVERSE,PRE_SUB1,EL_DROP] ) >>
    rw[] >- (
      first_x_assum match_mp_tac >>
      Q.ISPECL_THEN[`vv0`,`EL (n-LENGTH vv1) rs.rbvars`,`0:num`]mp_tac find_index_MEM >>
      rw[] >> rw[] >> simp[] ) >>
    qpat_assum`∀n. n < LENGTH rs.rbvars ⇒ X`(qspec_then`n - LENGTH vv1`mp_tac) >>
    simp[Abbr`renv`,CompilerLibTheory.el_check_def] >>
    simp[EL_CONS,PRE_SUB1]) >>
  rfs[Cmap_result_Rerr] >>
  BasicProvers.VAR_EQ_TAC >>
  fs[] >>
  disch_then(qspec_then`TCNonTail`mp_tac) >>
  simp[Abbr`bs1`] >>
  strip_tac >> gen_tac >> strip_tac >>
  BasicProvers.VAR_EQ_TAC >>
  BasicProvers.VAR_EQ_TAC >>
  `∃v. e'' = Craise v` by (
    Cases_on`e''`>>fs[]>>
    Cases_on`err`>>fs[] ) >>
  fs[] >>
  first_x_assum(qspec_then`[]`mp_tac) >>
  simp[ADD1] >>
  simp[code_for_return_def] >>
  disch_then(qx_choosel_then[`bv`,`rf`,`rd'`]strip_assume_tac) >>
  map_every qexists_tac[`bv`,`rf`,`rd'`] >>
  simp[CONJ_ASSOC] >>
  reverse conj_tac >- (

    cheat ) >>
  cheat)

(* TODO: move?*)
val FV_dec_def = Define`
  (FV_dec (Dlet p e) = FV (Mat e [(p,Lit ARB)])) ∧
  (FV_dec (Dletrec defs) = FV (Letrec defs (Lit ARB))) ∧
  (FV_dec (Dtype _) = {})`
val _ = export_rewrites["FV_dec_def"]

val pmatch_extend_cenv = store_thm("pmatch_extend_cenv",
  ``(∀(cenv:envC) s p v env id x. id ∉ set (MAP FST cenv) ∧ pmatch cenv s p v env ≠ Match_type_error
    ⇒ pmatch ((id,x)::cenv) s p v env = pmatch cenv s p v env) ∧
    (∀(cenv:envC) s ps vs env id x. id ∉ set (MAP FST cenv) ∧ pmatch_list cenv s ps vs env ≠ Match_type_error
    ⇒ pmatch_list ((id,x)::cenv) s ps vs env = pmatch_list cenv s ps vs env)``,
  ho_match_mp_tac pmatch_ind >>
  rw[pmatch_def] >> rw[] >>
  BasicProvers.CASE_TAC >> rw[] >> rpt (pop_assum mp_tac) >>
  TRY (BasicProvers.CASE_TAC >> rw[] >> rpt (pop_assum mp_tac)) >>
  TRY (BasicProvers.CASE_TAC >> rw[] >> rpt (pop_assum mp_tac)) >>
  TRY (BasicProvers.CASE_TAC) >> rw[] >>
  TRY (
    TRY (BasicProvers.CASE_TAC) >> rw[] >>
    imp_res_tac ALOOKUP_MEM >>
    fsrw_tac[DNF_ss][MEM_MAP,FORALL_PROD] >>
    metis_tac[]))

val evaluate_extend_cenv = store_thm("evaluate_extend_cenv",
  ``(∀menv (cenv:envC) s env exp res. evaluate menv cenv s env exp res ⇒
      ∀id x. (SND res ≠ Rerr Rtype_error) ∧ id ∉ set (MAP FST cenv) ⇒ evaluate menv ((id,x)::cenv) s env exp res) ∧
    (∀menv (cenv:envC) s env es res. evaluate_list menv cenv s env es res ⇒
      ∀id x. (SND res ≠ Rerr Rtype_error) ∧ id ∉ set (MAP FST cenv) ⇒ evaluate_list menv ((id,x)::cenv) s env es res) ∧
    (∀menv (cenv:envC) s env v pes res. evaluate_match menv cenv s env v pes res ⇒
      ∀id x. (SND res ≠ Rerr Rtype_error) ∧ id ∉ set (MAP FST cenv) ⇒ evaluate_match menv ((id,x)::cenv) s env v pes res)``,
  ho_match_mp_tac evaluate_strongind >>
  rw[FORALL_PROD,EXISTS_PROD] >>
  rw[Once evaluate_cases] >>
  fsrw_tac[DNF_ss][EXISTS_PROD,FORALL_PROD,MEM_MAP] >>
  TRY(metis_tac[])>>
  TRY(
    fs[SemanticPrimitivesTheory.do_con_check_def] >> rw[] >>
    Cases_on`ALOOKUP cenv cn`>>fs[] >>
    imp_res_tac ALOOKUP_MEM >>
    PairCases_on`x`>>fs[] >> metis_tac[]) >>
  Q.ISPECL_THEN[`cenv`,`s`,`p`,`v`,`env`,`id`]mp_tac(CONJUNCT1 pmatch_extend_cenv) >>
  simp[MEM_MAP,FORALL_PROD])

val evaluate_list_MAP_Var = store_thm("evaluate_list_MAP_Var",
  ``∀vs menv cenv s env. set vs ⊆ set (MAP FST env) ⇒ evaluate_list menv cenv s env (MAP (Var o Short) vs) (s,Rval (MAP (THE o ALOOKUP env) vs))``,
  Induct >> simp[Once evaluate_cases] >>
  rw[] >> rw[Once evaluate_cases,SemanticPrimitivesTheory.lookup_var_id_def] >>
  Cases_on`ALOOKUP env h`>>simp[] >>
  imp_res_tac ALOOKUP_FAILS >>
  fsrw_tac[DNF_ss][MEM_MAP,EXISTS_PROD])

val env_rs_ALOOKUP_same = store_thm("env_rs_ALOOKUP_same",
  ``∀cenv env rs rd s bs env'.
    env_rs cenv env rs rd s bs ∧ (ALOOKUP env' = ALOOKUP env) ⇒
    env_rs cenv env' rs rd s bs``,
  simp[env_rs_def] >> rw[] >>
  REWRITE_TAC[GSYM FDOM_alist_to_fmap] >>
  pop_assum mp_tac >>
  REWRITE_TAC[CONJUNCT1(GSYM ALOOKUP_EQ_FLOOKUP)] >>
  REWRITE_TAC[EXTENSION] >>
  REWRITE_TAC[FUN_EQ_THM] >>
  REWRITE_TAC[FLOOKUP_DEF] >>
  metis_tac[optionTheory.NOT_SOME_NONE])

val ALOOKUP_APPEND_same = store_thm("ALOOKUP_APPEND_same",
  ``∀l1 l2 l. (ALOOKUP l1 = ALOOKUP l2) ==> ALOOKUP (l1 ++ l) = ALOOKUP (l2 ++ l)``,
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
    `∃m. m < LENGTH l2 ∧ x = EL m l2` by metis_tac[MEM_EL] >>
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

val number_constructors_thm = store_thm("number_constructors_thm",
  ``∀cs ct. number_constructors cs ct = (FST ct |++ GENLIST (λi. (Short (FST (EL i cs)), (SND(SND ct))+i)) (LENGTH cs)
                                        ,REVERSE (GENLIST (λi. ((SND(SND ct))+i,FST(EL i cs))) (LENGTH cs)) ++ (FST(SND ct))
                                        ,(SND(SND ct)) + LENGTH cs)``,
  Induct >- simp[number_constructors_def,FUPDATE_LIST_THM] >>
  qx_gen_tac`p` >> PairCases_on`p` >>
  qx_gen_tac`q` >> PairCases_on`q` >>
  simp[number_constructors_def] >>
  conj_tac >- (
    simp[GENLIST_CONS,FUPDATE_LIST_THM] >>
    AP_TERM_TAC >>
    simp[LIST_EQ_REWRITE] ) >>
  simp[GENLIST_CONS] >>
  simp[LIST_EQ_REWRITE])

val number_constructors_append = store_thm("number_constructors_append",
  ``∀l1 l2 ct. number_constructors (l1 ++ l2) ct = number_constructors l2 (number_constructors l1 ct)``,
  Induct >> simp[number_constructors_def] >>
  qx_gen_tac`p` >> PairCases_on`p` >>
  gen_tac >> qx_gen_tac`q` >> PairCases_on`q` >>
  simp[number_constructors_def])

val FOLDL_number_constructors_thm = store_thm("FOLDL_number_constructors_thm",
  ``∀tds ct. FOLDL (λct p. case p of (x,y,cs) => number_constructors cs ct) ct tds =
    number_constructors (FLAT (MAP (SND o SND) tds)) ct``,
  Induct >- (simp[number_constructors_thm,FUPDATE_LIST_THM]) >>
  simp[] >>
  qx_gen_tac`p` >> PairCases_on`p` >>
  simp[] >>
  simp[number_constructors_append])

val check_dup_ctors_ALL_DISTINCT = store_thm("check_dup_ctors_ALL_DISTINCT",
  ``check_dup_ctors menv cenv tds ⇒ ALL_DISTINCT (MAP FST (FLAT (MAP (SND o SND) tds)))``,
  simp[SemanticPrimitivesTheory.check_dup_ctors_def] >>
  rw[] >>
  qmatch_assum_abbrev_tac`ALL_DISTINCT l1` >>
  qmatch_abbrev_tac`ALL_DISTINCT l2` >>
  qsuff_tac`l1 = l2`>- PROVE_TAC[] >>
  unabbrev_all_tac >>
  rpt (pop_assum kall_tac) >>
  Induct_on`tds` >> simp[FORALL_PROD] >>
  Induct >> simp[FORALL_PROD])

val check_dup_ctors_NOT_MEM = store_thm("check_dup_ctors_NOT_MEM",
  ``check_dup_ctors mn cenv tds ∧ MEM e (MAP FST (FLAT (MAP (SND o SND) tds))) ⇒ ¬MEM (mk_id mn e) (MAP FST cenv)``,
  simp[SemanticPrimitivesTheory.check_dup_ctors_def] >>
  strip_tac >>
  qpat_assum`ALL_DISTINCT X`kall_tac >>
  Induct_on`tds` >> simp[] >>
  fs[FORALL_PROD,res_quanTheory.RES_FORALL] >>
  rw[] >- (
    fsrw_tac[DNF_ss][MEM_MAP] >>
    qmatch_assum_rename_tac`MEM a b`[] >>
    PairCases_on`a`>>fs[] >>
    res_tac >>
    imp_res_tac ALOOKUP_FAILS >>
    simp[FORALL_PROD] >>
    metis_tac[] ) >>
  first_x_assum (match_mp_tac o MP_CANON) >>
  simp[] >> metis_tac[])

val compile_dec_val = store_thm("compile_dec_val",
  ``∀mn menv cenv s env dec res. evaluate_dec mn menv cenv s env dec res ⇒
     ∀rs rs' rd bc bs bc0.
      (mn = NONE) ∧ is_null menv ∧
      EVERY (closed menv) s ∧
      EVERY (closed menv) (MAP SND env) ∧
      EVERY (EVERY (closed menv) o MAP SND) (MAP SND menv) ∧
      FV_dec dec ⊆ set (MAP (Short o FST) env) ∪ menv_dom menv ∧
      (∀ts. (dec = Dtype ts) ⇒ "" ∉ set (MAP FST (FLAT (MAP (SND o SND) ts)))) ∧
      (∀mn n. MEM (Long mn n) (MAP FST cenv) ⇒ MEM mn (MAP FST menv)) ∧
      closed_under_cenv cenv menv env s ∧
      closed_under_menv menv env s ∧
      (∀v. v ∈ env_range env ∨ MEM v s ⇒ all_locs v ⊆ count (LENGTH s)) ∧
      env_rs cenv env rs rd s (bs with code := bc0) ∧
      (compile_dec rs dec = (rs',bc ++ [Stop])) ∧
      (bs.code = bc0 ++ bc ++ [Stop]) ∧
      (bs.pc = next_addr bs.inst_length bc0) ∧
      ALL_DISTINCT (FILTER is_Label bc0) ∧
      EVERY (combin$C $< rs.rnext_label o dest_Label) (FILTER is_Label bc0)
      ⇒
      case res of (s',Rval(cenv',env')) =>
        ∃st rf rd'.
        let bs' = bs with <|pc := next_addr bs.inst_length (bc0 ++ bc); stack := (Number i0)::st; refs := rf|> in
        bc_next^* bs bs' ∧
        env_rs (cenv'++cenv) (env'++env) rs' rd' s' (bs' with stack := st)
      | (s',Rerr(Rraise err)) =>
        ∃bv rf rd'.
        let bs' = bs with <|pc := next_addr bs.inst_length (bc0 ++ bc); stack := (Number i1)::bv::bs.stack; refs := rf|> in
        bc_next^*bs bs' ∧
        err_bv err bv ∧
        env_rs cenv env rs' rd' s' (bs' with stack := bs.stack)
      | (s',Rerr Rtype_error) => T``,
  ho_match_mp_tac evaluate_dec_ind >>
  strip_tac >- (
    rpt gen_tac >>
    simp[compile_dec_def] >>
    strip_tac >> rpt gen_tac >> strip_tac >>
    qabbrev_tac`vv = PARTITION (λv. MEM v rs.rbvars) (pat_bindings p [])` >>
    PairCases_on`vv` >>
    qabbrev_tac`exp = Con (Short "") (MAP (Var o Short) (vv0 ++ vv1))` >>
    `Short "" ∉ set (MAP FST cenv)` by ( fs[env_rs_def]) >>
    `evaluate menv ((Short "",(LENGTH vv0 + LENGTH vv1,ARB))::cenv) s env (Mat e [(p,exp)])
        (s2,Rval (Conv (Short "") (MAP (THE o (ALOOKUP (env' ++ env))) (vv0 ++ vv1))))` by (
      simp[Once evaluate_cases] >>
      map_every qexists_tac[`v`,`s2`] >>
      conj_tac >- (
        match_mp_tac(MP_CANON (CONJUNCT1 evaluate_extend_cenv)) >> simp[] ) >>
      simp[Once evaluate_cases] >>
      disj1_tac >>
      imp_res_tac pmatch_extend_cenv >>
      first_x_assum(qspecl_then[`v`,`s2`,`p`,`emp`]mp_tac) >>
      simp[] >>
      fs[LibTheory.emp_def] >> strip_tac >>
      simp[Once pmatch_nil] >>
      simp[Once evaluate_cases,Abbr`exp`] >>
      simp[SemanticPrimitivesTheory.do_con_check_def] >>
      REWRITE_TAC[GSYM MAP_APPEND] >>
      match_mp_tac evaluate_list_MAP_Var >>
      qspecl_then[`cenv`,`s2`,`p`,`v`,`[]`,`env'`,`menv`]mp_tac(CONJUNCT1 pmatch_closed) >>
      qspecl_then[`menv`,`cenv`,`s`,`env`,`e`,`(s2,Rval v)`]mp_tac(CONJUNCT1 evaluate_closed) >>
      simp[] >>
      fs[PARTITION_DEF,markerTheory.Abbrev_def] >>
      imp_res_tac PART_MEM >>
      fsrw_tac[DNF_ss][SUBSET_DEF] ) >>
    qmatch_assum_abbrev_tac`evaluate menv ((Short "",tup)::cenv) s env Mexp (s2,Rval (Conv (Short "") vs))` >>
    qspecl_then[`rs`,`pat_bindings p []`,`λb. Mat e [(p,b)]`,`menv`,`tup`,`cenv`,`s`,`env`]mp_tac compile_fake_exp_val >>
    simp[] >>
    REWRITE_TAC[GSYM MAP_APPEND] >>
    disch_then(qspecl_then[`s2`,`Rval (Conv (Short "") vs)`,`rd`,`bc0`,`bs`]mp_tac) >>
    simp[AND_IMP_INTRO] >>
    discharge_hyps >- (
      fs[PARTITION_DEF,markerTheory.Abbrev_def,FV_list_MAP] >>
      imp_res_tac PART_MEM >>
      imp_res_tac PART_LENGTH >>
      reverse conj_tac >- (fs[] >> metis_tac[]) >>
      fsrw_tac[DNF_ss][SUBSET_DEF,MEM_MAP,MEM_FLAT,EXISTS_PROD] >>
      metis_tac[] ) >>
    disch_then(qx_choosel_then[`st`,`rf`,`rd'`]strip_assume_tac) >>
    map_every qexists_tac[`st`,`rf`,`rd'`] >>
    rw[LibTheory.emp_def] >>
    match_mp_tac env_rs_ALOOKUP_same >>
    HINT_EXISTS_TAC >>
    simp[FUN_EQ_THM,ALOOKUP_APPEND] >>
    rw[] >>
    BasicProvers.CASE_TAC >- (
      BasicProvers.CASE_TAC >>
      imp_res_tac ALOOKUP_FAILS >>
      imp_res_tac ALOOKUP_MEM >>
      fs[Abbr`vs`] >>
      fs[PARTITION_DEF,markerTheory.Abbrev_def] >>
      imp_res_tac PERM_PART >>
      qspecl_then[`cenv`,`s2`,`p`,`v`,`[]`,`env'`,`menv`]mp_tac(CONJUNCT1 pmatch_closed) >>
      qspecl_then[`menv`,`cenv`,`s`,`env`,`e`,`(s2,Rval v)`]mp_tac(CONJUNCT1 evaluate_closed) >>
      fs[LibTheory.emp_def] >> rw[] >>
      `¬MEM x (MAP FST env')` by (rw[MEM_MAP,EXISTS_PROD] >> metis_tac[]) >>
      `¬MEM x (vv0 ++ vv1)` by metis_tac[MEM_PERM] >>
      rfs[MEM_ZIP] >>
      metis_tac[MEM_EL,MEM_APPEND,LENGTH_APPEND] ) >>
    BasicProvers.CASE_TAC >- (
      imp_res_tac ALOOKUP_FAILS >>
      imp_res_tac ALOOKUP_MEM >>
      fs[Abbr`vs`] >>
      fs[PARTITION_DEF,markerTheory.Abbrev_def] >>
      imp_res_tac PERM_PART >>
      qspecl_then[`cenv`,`s2`,`p`,`v`,`[]`,`env'`,`menv`]mp_tac(CONJUNCT1 pmatch_closed) >>
      qspecl_then[`menv`,`cenv`,`s`,`env`,`e`,`(s2,Rval v)`]mp_tac(CONJUNCT1 evaluate_closed) >>
      fs[LibTheory.emp_def] >> rw[] >>
      `MEM x (MAP FST env')` by (rw[MEM_MAP,EXISTS_PROD] >> metis_tac[]) >>
      `MEM x (vv0 ++ vv1)` by metis_tac[MEM_PERM] >>
      rfs[MEM_ZIP] >>
      metis_tac[MEM_EL,MEM_APPEND,LENGTH_APPEND] ) >>
    qspecl_then[`cenv`,`s2`,`p`,`v`,`[]`,`env'`,`menv`]mp_tac(CONJUNCT1 pmatch_closed) >>
    qspecl_then[`menv`,`cenv`,`s`,`env`,`e`,`(s2,Rval v)`]mp_tac(CONJUNCT1 evaluate_closed) >>
    fs[LibTheory.emp_def] >> rw[] >>
    imp_res_tac ALOOKUP_MEM >>
    fs[Abbr`vs`] >>
    qsuff_tac`MEM (x,x'') env'` >- (
      metis_tac[ALOOKUP_ALL_DISTINCT_MEM,pairTheory.PAIR_EQ,optionTheory.SOME_11] ) >>
    rfs[MEM_ZIP] >>
    REWRITE_TAC[GSYM MAP_APPEND] >>
    simp[EL_MAP,ALOOKUP_APPEND] >>
    fs[] >> rfs[] ) >>
  strip_tac >- (
    rpt gen_tac >>
    simp[compile_dec_def] >>
    strip_tac >> rpt gen_tac >> strip_tac >>
    qabbrev_tac`vv = PARTITION (λv. MEM v rs.rbvars) (pat_bindings p [])` >>
    PairCases_on`vv` >>
    qabbrev_tac`exp = Con (Short "") (MAP (Var o Short) (vv0 ++ vv1))` >>
    `Short "" ∉ set (MAP FST cenv)` by ( fs[env_rs_def]) >>
    `evaluate menv ((Short "",(LENGTH vv0 + LENGTH vv1,ARB))::cenv) s env (Mat e [(p,exp)])
        (s2,Rerr (Rraise Bind_error))` by (
      simp[Once evaluate_cases] >>
      disj1_tac >>
      map_every qexists_tac[`v`,`s2`] >>
      conj_tac >- (
        match_mp_tac(MP_CANON (CONJUNCT1 evaluate_extend_cenv)) >> simp[] ) >>
      simp[Once evaluate_cases] >>
      disj2_tac >>
      simp[Once evaluate_cases] >>
      imp_res_tac pmatch_extend_cenv >>
      first_x_assum(qspecl_then[`v`,`s2`,`p`,`emp`]mp_tac) >>
      simp[] >>
      fs[LibTheory.emp_def] >> strip_tac >>
      simp[Once pmatch_nil]) >>
    qmatch_assum_abbrev_tac`evaluate menv ((Short "",tup)::cenv) s env Mexp (s2,Rerr (Rraise Bind_error))` >>
    qspecl_then[`rs`,`pat_bindings p []`,`λb. Mat e [(p,b)]`,`menv`,`tup`,`cenv`,`s`,`env`]mp_tac compile_fake_exp_val >>
    simp[] >>
    REWRITE_TAC[GSYM MAP_APPEND] >>
    disch_then(qspecl_then[`s2`,`Rerr (Rraise Bind_error)`,`rd`,`bc0`,`bs`]mp_tac) >>
    simp[AND_IMP_INTRO] >>
    discharge_hyps >- (
      fs[PARTITION_DEF,markerTheory.Abbrev_def,FV_list_MAP] >>
      imp_res_tac PART_MEM >>
      imp_res_tac PART_LENGTH >>
      reverse conj_tac >- (fs[] >> metis_tac[]) >>
      fsrw_tac[DNF_ss][SUBSET_DEF,MEM_MAP,MEM_FLAT,EXISTS_PROD] >>
      metis_tac[] ) >>
    simp[err_bv_def] ) >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- (
    cheat ) >>
  strip_tac >- (
    rpt gen_tac >>
    simp[compile_dec_def,FST_triple] >>
    strip_tac >> rpt gen_tac >> strip_tac >>
    qabbrev_tac`vv = PARTITION (λv. MEM v rs.rbvars) (MAP FST funs)` >>
    PairCases_on`vv` >>
    qabbrev_tac`exp = Con (Short "") (MAP (Var o Short) (vv0 ++ vv1))` >>
    `Short "" ∉ set (MAP FST cenv)` by ( fs[env_rs_def]) >>
    qmatch_assum_abbrev_tac`compile_fake_exp rs X Y = Z` >>
    `X = MAP FST funs` by (
      rw[Once LIST_EQ_REWRITE,Abbr`X`,EL_MAP] >>
      BasicProvers.CASE_TAC ) >>
    map_every qunabbrev_tac[`Y`,`Z`] >>
    BasicProvers.VAR_EQ_TAC >> pop_assum kall_tac >>
    `evaluate menv ((Short "",(LENGTH vv0 + LENGTH vv1,ARB))::cenv) s env (Letrec funs exp)
        (s,Rval (Conv (Short "") (MAP (THE o (ALOOKUP (build_rec_env funs env env))) (vv0 ++ vv1))))` by (
      simp[Once evaluate_cases,FST_triple] >>
      simp[Once evaluate_cases,Abbr`exp`] >>
      simp[SemanticPrimitivesTheory.do_con_check_def] >>
      REWRITE_TAC[GSYM MAP_APPEND] >>
      match_mp_tac evaluate_list_MAP_Var >>
      simp[build_rec_env_dom] >>
      fs[PARTITION_DEF,markerTheory.Abbrev_def] >>
      imp_res_tac PART_MEM >>
      fsrw_tac[DNF_ss][SUBSET_DEF] ) >>
    qmatch_assum_abbrev_tac`evaluate menv ((Short "",tup)::cenv) s env Mexp (s,Rval (Conv (Short "") vs))` >>
    qspecl_then[`rs`,`MAP FST funs`,`λb. Letrec funs b`,`menv`,`tup`,`cenv`,`s`,`env`]mp_tac compile_fake_exp_val >>
    simp[] >>
    REWRITE_TAC[GSYM MAP_APPEND] >>
    disch_then(qspecl_then[`s`,`Rval (Conv (Short "") vs)`,`rd`,`bc0`,`bs`]mp_tac) >>
    simp[AND_IMP_INTRO] >>
    discharge_hyps >- (
      fs[PARTITION_DEF,markerTheory.Abbrev_def,FV_list_MAP] >>
      imp_res_tac PART_MEM >>
      imp_res_tac PART_LENGTH >>
      reverse conj_tac >- (fs[] >> metis_tac[]) >>
      fsrw_tac[DNF_ss][SUBSET_DEF,MEM_MAP,MEM_FLAT,EXISTS_PROD] >>
      metis_tac[] ) >>
    disch_then(qx_choosel_then[`st`,`rf`,`rd'`]strip_assume_tac) >>
    map_every qexists_tac[`st`,`rf`,`rd'`] >>
    rw[LibTheory.emp_def] >>
    match_mp_tac env_rs_ALOOKUP_same >>
    HINT_EXISTS_TAC >> simp[] >>
    match_mp_tac ALOOKUP_APPEND_same >>
    match_mp_tac ALOOKUP_ALL_DISTINCT_PERM_same >>
    conj_asm1_tac >- simp[build_rec_env_MAP] >>
    conj_asm1_tac >- (
      fs[PARTITION_DEF,markerTheory.Abbrev_def] >>
      simp[build_rec_env_MAP,MAP_ZIP] >>
      imp_res_tac PERM_PART >> fs[] ) >>
    qunabbrev_tac`vs` >>
    simp_tac std_ss [build_rec_env_MAP,APPEND_NIL] >>
    match_mp_tac ALL_DISTINCT_PERM_ALOOKUP_ZIP >>
    simp[MAP_MAP_o,combinTheory.o_DEF,UNCURRY] >>
    fsrw_tac[ETA_ss][] >>
    rfs[MAP_ZIP] ) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    simp[compile_dec_def] >>
    rpt gen_tac >> strip_tac >>
    rpt gen_tac >> strip_tac >>
    map_every qexists_tac[`bs.stack`,`bs.refs`,`rd`] >>
    conj_tac >- (
      simp[RTC_eq_NRC] >>
      qexists_tac`SUC 0` >> simp[] >>
      rw[bc_eval1_thm] >>
      `bc_fetch bs = SOME (Stack (PushInt i0))` by (
        match_mp_tac bc_fetch_next_addr >>
        qexists_tac`bc0`>>simp[] ) >>
      rw[bc_eval1_def,bump_pc_def,bc_eval_stack_def] >>
      simp[bc_state_component_equality,SUM_APPEND,FILTER_APPEND] ) >>
    fs[FOLDL_number_constructors_thm,SemanticPrimitivesTheory.build_tdefs_def,LibTheory.emp_def,AstTheory.mk_id_def] >>
    fs[env_rs_def] >>
    conj_tac >- (
      fs[number_constructors_thm] >>
      qabbrev_tac`p = rs.contab` >>
      PairCases_on`p` >>
      fs[good_contab_def] >>
      fs[good_cmap_def,cmap_linv_def] >>
      conj_asm1_tac >- (
        simp[MAP_REVERSE,ALL_DISTINCT_REVERSE,ALL_DISTINCT_APPEND,MAP_GENLIST,ALL_DISTINCT_GENLIST] >>
        simp[MEM_GENLIST,MEM_MAP,FORALL_PROD] >>
        imp_res_tac check_dup_ctors_ALL_DISTINCT >>
        fs[EL_ALL_DISTINCT_EL_EQ,EL_MAP] >>
        conj_tac >- metis_tac[] >>
        qsuff_tac`∀e. MEM e (MAP FST (FLAT (MAP (SND o SND) tds))) ⇒ ¬MEM e (MAP SND p1)` >- (
          simp[MEM_MAP] >>
          simp[MEM_EL,EL_MAP,GSYM LEFT_FORALL_IMP_THM] >>
          simp[FORALL_PROD] ) >>
        imp_res_tac check_dup_ctors_NOT_MEM >>
        rpt strip_tac >>
        fs[EXTENSION] >>
        fs[SUBSET_DEF] >>
        res_tac >>
        res_tac >- (
          rw[] >>
          fsrw_tac[DNF_ss][MEM_MAP,FORALL_PROD,EXISTS_PROD,MEM_FLAT,PrinterTheory.id_to_string_def] ) >>
        rw[] >>
        qmatch_assum_rename_tac`MEM z (MAP FST cenv)`[] >> fs[] >>
        Cases_on`z`>>fs[PrinterTheory.id_to_string_def,AstTheory.mk_id_def] >>
        res_tac >> fs[is_null_def] >> rw[] >> fs[] ) >>
      cheat ) >>
    cheat) >>
  strip_tac >- rw[])

val _ = export_theory()
