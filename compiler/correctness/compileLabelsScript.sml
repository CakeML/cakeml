open HolKernel bossLib boolLib boolSimps listTheory rich_listTheory alistTheory finite_mapTheory lcsymtacs
open miscTheory bytecodeTerminationTheory compileTerminationTheory bytecodeEvalTheory bytecodeExtraTheory
val _ = intLib.deprecate_int()
val _ = new_theory"compileLabels"

val el_of_addr_def = Define`
  (el_of_addr il n [] = NONE) ∧
  (el_of_addr il n (x::xs) =
   if is_Label x then OPTION_BIND (el_of_addr il n xs) (λm. SOME (m + 1)) else
     if n = 0 then SOME (0:num) else
       if n < il x + 1 then NONE else
         OPTION_BIND (el_of_addr il (n - (il x + 1)) xs) (λm. SOME (m + 1)))`
val _ = export_rewrites["el_of_addr_def"]

val el_of_addr_LESS_LENGTH = store_thm("el_of_addr_LESS_LENGTH",
  ``∀il ls n m. (el_of_addr il n ls = SOME m) ⇒ m < LENGTH ls``,
  gen_tac >> Induct >> srw_tac[ARITH_ss][] >>
  res_tac >> fsrw_tac[ARITH_ss][])

val bc_fetch_aux_el_of_addr = store_thm("bc_fetch_aux_el_of_addr",
  ``∀c il pc. bc_fetch_aux c il pc = OPTION_BIND (el_of_addr il pc c) (λn. SOME (EL n c))``,
  Induct >> rw[] >>
  Q.PAT_ABBREV_TAC`opt = el_of_addr il pcX c` >>
  Cases_on `opt` >> fs[] >>
  rw[GSYM arithmeticTheory.ADD1])

val replace_lab_def = Define`
  (replace_lab m (Jump (Lab l)) = Jump (Addr (FAPPLY m l))) ∧
  (replace_lab m (JumpIf (Lab l)) = JumpIf (Addr (m ' l))) ∧
  (replace_lab m (Call (Lab l)) = Call (Addr (m ' l))) ∧
  (replace_lab m (PushPtr (Lab l)) = PushPtr (Addr (m ' l))) ∧
  (replace_lab m i = i)`
val _ = export_rewrites["replace_lab_def"]

val is_Label_replace_lab = store_thm("is_Label_replace_lab",
  ``∀x. is_Label (replace_lab m x) = is_Label x``,
  Cases >> rw[] >> Cases_on `l` >> rw[])
val _ = export_rewrites["is_Label_replace_lab"]

val good_il_def = Define`
  good_il il ⇔
  (∀x. il (Jump x) = il (Jump ARB)) ∧
  (∀x. il (JumpIf x) = il (JumpIf ARB)) ∧
  (∀x. il (Call x) = il (Call ARB)) ∧
  (∀x. il (PushPtr x) = il (PushPtr ARB))`

val il_replace_lab = store_thm("il_replace_lab",
  ``good_il il ⇒ ∀m x. (il (replace_lab m x) = il x)``,
  rw[good_il_def] >>
  Cases_on `x` >> rw[] >>
  Cases_on `l` >> rw[])

val calculate_labels_thm = store_thm("calculate_labels_thm",
  ``∀il m n bc lbc m' n' bc'.
      (calculate_labels il m n bc lbc = (m',n',bc')) ∧ ALL_DISTINCT (FILTER is_Label lbc) ⇒
      (bc' = (REVERSE (FILTER ($~ o is_Label) lbc) ++ bc)) ∧
      (let ls = MAP dest_Label (FILTER is_Label lbc) in
        (m' = m |++ ZIP (ls, MAP (THE o combin$C (bc_find_loc_aux lbc il) n) ls))) ∧
      (n' = n + SUM (MAP (SUC o il) (FILTER ($~ o is_Label) lbc)))``,
  ho_match_mp_tac calculate_labels_ind >>
  strip_tac >- (
    rw[calculate_labels_def,LET_THM,FUPDATE_LIST_THM] ) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    simp_tac(std_ss)[Once calculate_labels_def] >>
    rpt gen_tac >> strip_tac >>
    `ALL_DISTINCT (FILTER is_Label lbc)` by (
      pop_assum mp_tac >>
      rpt (pop_assum kall_tac) >>
      rw[] ) >>
    res_tac >>
    full_simp_tac(std_ss)[LET_THM] >>
    rpt BasicProvers.VAR_EQ_TAC >>
    pop_assum kall_tac >> pop_assum mp_tac >>
    rpt (pop_assum kall_tac) >>
    rw[FUPDATE_LIST_THM,bc_find_loc_aux_def] >>
    AP_TERM_TAC >> AP_TERM_TAC >> AP_TERM_TAC >>
    rw[MAP_EQ_f,MEM_MAP,MEM_FILTER] >>
    AP_TERM_TAC >>
    rw[bc_find_loc_aux_def] >>
    fs[MEM_FILTER] >>
    Cases_on `y` >> fs[]) >>
  REPEAT (
    strip_tac >- (
      rpt gen_tac >> strip_tac >>
      simp_tac(std_ss)[Once calculate_labels_def] >>
      rpt gen_tac >> strip_tac >>
      `ALL_DISTINCT (FILTER is_Label lbc)` by (
        pop_assum mp_tac >>
        rpt (pop_assum kall_tac) >>
        rw[] ) >>
      res_tac >>
      full_simp_tac(std_ss)[LET_THM] >>
      rpt BasicProvers.VAR_EQ_TAC >>
      rpt (pop_assum kall_tac) >>
      srw_tac[ARITH_ss][] >>
      AP_TERM_TAC >> AP_TERM_TAC >> AP_TERM_TAC >>
      rw[MAP_EQ_f,MEM_MAP,MEM_FILTER] >>
      AP_TERM_TAC >>
      rw[bc_find_loc_aux_def] )))

val replace_labels_thm = store_thm("replace_labels_thm",
  ``∀m a ls. (replace_labels m a ls = (REVERSE (MAP (replace_lab m) ls)) ++ a)``,
  ho_match_mp_tac replace_labels_ind >> rw[replace_labels_def])

val tac = (
    rw[LET_THM] >>
    match_mp_tac bc_eval1_SOME >>
    Q.PAT_ABBREV_TAC`f = replace_lab X` >>
    qspecl_then[`f`,`s1`] mp_tac bc_fetch_MAP >>
    qunabbrev_tac`f` >> rw[il_replace_lab] >>
    rw[bc_eval1_def] >>
    fs[bc_eval_stack_thm] >>
    fs[bump_pc_def] )

val tac2 = (
    rw[LET_THM] >>
    match_mp_tac bc_eval1_SOME >>
    Q.PAT_ABBREV_TAC`f = replace_lab X` >>
    qspecl_then[`f`,`s1`] mp_tac bc_fetch_MAP >>
    qunabbrev_tac`f` >>
    Cases_on `l` >> rw[il_replace_lab] >>
    srw_tac[DNF_ss][bc_eval1_def,LET_THM] >>
    fs[bc_eval_stack_thm,bc_find_loc_def] >>
    fs[FLOOKUP_DEF] >>
    rw[bump_pc_with_stack] >>
    rw[bump_pc_def] >>
    fs[good_il_def] >>
    metis_tac[optionTheory.SOME_11,optionTheory.NOT_SOME_NONE])

val bc_next_MAP_replace_lab = store_thm("bc_next_MAP_replace_lab",
  ``∀s1 s2. bc_next s1 s2 ⇒
      ∀m. good_il s1.inst_length ∧
      (∀l. FLOOKUP m l = bc_find_loc s1 (Lab l)) ⇒
    let c = MAP (replace_lab m) s1.code in
    bc_next (s1 with <| code := c |>) (s2 with <| code := c |>)``,
  ho_match_mp_tac bc_next_ind >>
  strip_tac >- tac >>
  strip_tac >- tac2 >>
  strip_tac >- tac2 >>
  strip_tac >- tac2 >>
  strip_tac >- tac >>
  strip_tac >- tac >>
  strip_tac >- tac2 >>
  strip_tac >- tac >>
  strip_tac >- tac >>
  strip_tac >- (
    rw[LET_THM] >>
    match_mp_tac bc_eval1_SOME >>
    Q.PAT_ABBREV_TAC`f = replace_lab X` >>
    qspecl_then[`f`,`s1`] mp_tac bc_fetch_MAP >>
    qunabbrev_tac`f` >> rw[il_replace_lab] >>
    srw_tac[ARITH_ss][bc_eval1_def] >>
    lrw[REVERSE_APPEND,EL_APPEND2,TAKE_APPEND2]) >>
  strip_tac >- tac >>
  strip_tac >- tac >>
  strip_tac >- tac )

val bc_fetch_MEM = store_thm("bc_fetch_MEM",
  ``(bc_fetch s1 = SOME i) ⇒ (MEM i s1.code)``,
  rw[bc_fetch_def] >>
  fs[bc_fetch_aux_el_of_addr] >>
  rw[MEM_EL] >>
  imp_res_tac el_of_addr_LESS_LENGTH >>
  metis_tac[])

val addrs_only_def = Define`
  (addrs_only (Jump (Lab _)) = F) ∧
  (addrs_only (JumpIf (Lab _)) = F) ∧
  (addrs_only (Call (Lab _)) = F) ∧
  (addrs_only (PushPtr (Lab _)) = F) ∧
  (addrs_only _ = T)`
val _ = export_rewrites["addrs_only_def"]

val addrs_only_replace_lab = store_thm("addrs_only_replace_lab",
  ``addrs_only (replace_lab m x)``,
  Cases_on `x` >> rw[] >> Cases_on `l` >> rw[])
val _ = export_rewrites["addrs_only_replace_lab"]

val bc_fetch_aux_FILTER_labels = store_thm("bc_fetch_aux_FILTER_labels",
  ``∀il ls n. bc_fetch_aux (FILTER ($~ o is_Label) ls) il n = bc_fetch_aux ls il n``,
  gen_tac >> Induct >> rw[])
val _ = export_rewrites["bc_fetch_aux_FILTER_labels"]

val bc_fetch_FILTER_labels = store_thm("bc_fetch_FILTER_labels",
  ``bc_fetch (s with code := FILTER ($~ o is_Label) s.code) = bc_fetch s``,
  rw[bc_fetch_def])
val _ = export_rewrites["bc_fetch_FILTER_labels"]

val bc_next_FILTER_labels = store_thm("bc_next_FILTER_labels",
  ``∀s1 s2. bc_next s1 s2 ⇒ EVERY addrs_only s1.code ⇒
      let c = FILTER ($~ o is_Label) s1.code in
      bc_next (s1 with <| code := c |>) (s2 with <| code := c |>)``,
  ho_match_mp_tac bc_next_ind >>
  rw[LET_THM] >>
  rw[bc_eval1_thm] >>
  srw_tac[DNF_ss][bc_eval1_def,LET_THM] >>
  fs[bc_eval_stack_thm] >>
  rw[bump_pc_def] >>
  imp_res_tac bc_fetch_MEM >>
  fs[EVERY_MEM] >>
  res_tac >>
  TRY (Cases_on `l`) >> fs[bc_find_loc_def] >>
  rw[bc_fetch_with_stack] >>
  srw_tac[ARITH_ss][] >>
  lrw[TAKE_APPEND2,REVERSE_APPEND,EL_APPEND2])

val bc_next_compile_labels = store_thm("bc_next_compile_labels",
  ``∀s1 s2. bc_next s1 s2 ⇒
      (good_il s1.inst_length ∧
       ALL_DISTINCT (FILTER is_Label s1.code)) ⇒
      let c = compile_labels s1.inst_length s1.code in
      bc_next (s1 with <| code := c |>) (s2 with <| code := c |>)``,
  rw[compile_labels_def,replace_labels_thm] >>
  imp_res_tac calculate_labels_thm >>
  rpt BasicProvers.VAR_EQ_TAC >>
  qunabbrev_tac`c` >>
  rw[MAP_REVERSE] >>
  `∀x. ($~ o is_Label) (replace_lab m x) = ($~ o is_Label) x` by rw[] >>
  rw[MAP_FILTER] >>
  qmatch_abbrev_tac `bc_next (s1 with code := FILTER P ls) (s2 with code := FILTER P ls)` >>
  `EVERY addrs_only ls` by (
    qunabbrev_tac`ls` >>
    rw[EVERY_MAP] ) >>
  `bc_next (s1 with code := ls) (s2 with code := ls)` by (
    qunabbrev_tac`ls` >>
    match_mp_tac (MP_CANON(SIMP_RULE(srw_ss())[LET_THM]bc_next_MAP_replace_lab)) >>
    rw[bc_find_loc_def] >>
    fs[LET_THM] >>
    qmatch_abbrev_tac `FLOOKUP (fm |++ ls) l = X` >>
    Cases_on `X` >- (
      `ALOOKUP (REVERSE ls) l = NONE` by (
        qunabbrev_tac`ls` >>
        rw[ALOOKUP_FAILS,ZIP_MAP] >>
        rw[MAP_MAP_o,combinTheory.o_DEF] >>
        `¬MEM (Label l) s1.code` by metis_tac[bc_find_loc_aux_NONE] >>
        `¬MEM (Label l) (FILTER is_Label s1.code)` by rw[MEM_FILTER] >>
        rw[MEM_MAP] >>
        Cases_on `x` >> rw[MEM_FILTER] >>
        PROVE_TAC[] ) >>
      imp_res_tac FLOOKUP_FUPDATE_LIST_ALOOKUP_NONE >>
      fs[Abbr`fm`] ) >>
    `ALOOKUP (REVERSE ls) l = SOME x` by (
      match_mp_tac ALOOKUP_ALL_DISTINCT_MEM >>
      qunabbrev_tac`ls` >>
      rw[REVERSE_ZIP,MAP_ZIP,ALL_DISTINCT_REVERSE] >- (
        match_mp_tac ALL_DISTINCT_MAP_INJ >> fs[] >>
        qx_gen_tac `a` >> qx_gen_tac `b` >>
        Cases_on `a` >> Cases_on `b` >> rw[MEM_FILTER] ) >>
      `MEM (Label l) s1.code` by
        metis_tac[bc_find_loc_aux_MEM,optionTheory.NOT_SOME_NONE] >>
      `MEM (Label l) (FILTER is_Label s1.code)` by rw[MEM_FILTER] >>
      pop_assum (strip_assume_tac o SIMP_RULE (srw_ss()) [MEM_EL]) >>
      rw[MEM_ZIP] >>
      qexists_tac `n` >>
      pop_assum (assume_tac o SYM) >>
      rw[EL_MAP] ) >>
    imp_res_tac FLOOKUP_FUPDATE_LIST_ALOOKUP_SOME >>
    fs[] ) >>
  qunabbrev_tac`P` >>
  `ls = (s1 with code := ls).code` by rw[] >>
  pop_assum SUBST1_TAC >>
  (bc_next_FILTER_labels
   |> SIMP_RULE std_ss [LET_THM]
   |> Q.SPECL[`s1 with code := ls`,`s2 with code := ls`]
   |> SIMP_RULE (srw_ss()) []
   |> MP_CANON |> match_mp_tac ) >>
  fs[])

val _ = export_theory()
