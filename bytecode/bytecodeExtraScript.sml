open HolKernel bossLib boolLib boolSimps listTheory relationTheory arithmeticTheory lcsymtacs
open miscTheory bytecodeTheory bytecodeTerminationTheory bytecodeEvalTheory rich_listTheory
val _ = numLib.prefer_num()
val _ = new_theory"bytecodeExtra"

val real_inst_length_def = zDefine `
  real_inst_length bc =
   case bc of
     Stack Pop => 0
   | Stack (Pops v25) => if v25 <= 268435455 then 4 else 1
   | Stack (PushInt v28) =>
       if v28 <= 268435455 then if v28 < 0 then 1 else 4 else 1
   | Stack (Cons v29 v30) =>
       if v29 < 4096 /\ v30 < 32768 then
         if v30 = 0 then 4 else if v30 < 32768 then 34 else 1
       else 1
   | Stack (Load v31) => if v31 <= 268435455 then 4 else 1
   | Stack (Store v32) => if v32 <= 268435455 then 4 else 1
   | Stack El => 6
   | Stack (TagEq v35) => if v35 <= 268435455 then 28 else 1
   | Stack IsBlock => 25
   | Stack Equal => 5
   | Stack Add => 3
   | Stack Sub => 3
   | Stack Mult => 8
   | Stack Div => 20
   | Stack Mod => 23
   | Stack Less => 24
   | Label l => 0
   | Jump _ => 2
   | JumpIf _ => 5
   | Call _ => 2
   | CallPtr => 3
   | PushPtr _ => 7
   | Return => 0
   | PushExc => 3
   | PopExc => 5
   | Ref => 23
   | Deref => 1
   | Update => 3
   | Stop b => 9
   | Tick => 1
   | Print => 5
   | PrintC v13 => 33:num
   | _ => 1`;

val thms = ([],``!bc. x = real_inst_length bc``)
  |> (Cases THEN TRY (Cases_on `b`)) |> fst |> map (rand o snd)
  |> map (REWRITE_CONV [real_inst_length_def] THENC EVAL)
val _ = save_thm("real_inst_length_compute", LIST_CONJ thms)
val _ = computeLib.add_persistent_funs ["real_inst_length_compute"]
(*
val names = let val r = ref 0 in map (fn th =>
  let val name = ("real_inst_length_"^Int.toString(!r)) in
     (save_thm(name,th);r := (!r)+1;name) end) thms end
val _ =  computeLib.add_persistent_funs names
*)

val bc_num_def = Define `
  bc_num s =
     case s of
       Stack Pop => (0:num,0:num,0:num)
     | Stack (Pops n) => (1,n,0)
     | Stack (PushInt i) => (3,Num (ABS i),if i < 0 then 1 else 0)
     | Stack (Cons n m) => (4,n,m)
     | Stack (Load n) => (5,n,0)
     | Stack (Store n) => (6,n,0)
     | Stack El => (50,0,0)
     | Stack (Cons2 n) => (51,n,0)
     | Stack (TagEq n) => (9,n,0)
     | Stack LengthBlock => (48,0,0)
     | Stack IsBlock => (10,0,0)
     | Stack Equal => (11,0,0)
     | Stack Add => (12,0,0)
     | Stack Sub => (13,0,0)
     | Stack Mult => (14,0,0)
     | Stack Div => (15,0,0)
     | Stack Mod => (16,0,0)
     | Stack Less => (17,0,0)
     | Label n => (20,n,0)
     | Jump (Addr n) => (21,n,0)
     | JumpIf (Addr n) => (22,n,0)
     | Call (Addr n) => (23,n,0)
     | PushPtr (Addr n) => (24,n,0)
     | Jump (Lab n) => (41,n,0)
     | JumpIf (Lab n) => (42,n,0)
     | Call (Lab n) => (43,n,0)
     | PushPtr (Lab n) => (44,n,0)
     | CallPtr => (26,0,0)
     | Return => (27,0,0)
     | PushExc => (28,0,0)
     | PopExc => (29,0,0)
     | Ref => (30,0,0)
     | RefByte => (45,0,0)
     | Deref => (31,0,0)
     | DerefByte => (46,0,0)
     | Update => (32,0,0)
     | UpdateByte => (47,0,0)
     | Length => (39,0,0)
     | LengthByte => (49,0,0)
     | Tick => (34,0,0)
     | Print => (35,0,0)
     | PrintWord8 => (40,0,0)
     | PrintC c => (36,ORD c,0)
     | Galloc n => (2,n,0)
     | Gread n => (7,n,0)
     | Gupdate n => (19,n,0)
     | Stop F => (37,0,0)
     | Stop T => (38,0,0)`;

val num_bc_def = Define `
  num_bc (n:num,x1:num,x2:num) =
    if n = 0 then Stack Pop
    else if n = 1 then Stack (Pops x1)
    else if n = 2 then Galloc x1
    else if n = 3 then Stack (PushInt (if x2 = 0 then &x1 else 0 - &x1))
    else if n = 4 then Stack (Cons x1 x2)
    else if n = 5 then Stack (Load x1)
    else if n = 6 then Stack (Store x1)
    else if n = 7 then Gread x1
    else if n = 9 then Stack (TagEq x1)
    else if n = 48 then Stack LengthBlock
    else if n = 50 then Stack El
    else if n = 51 then Stack (Cons2 x1)
    else if n = 10 then Stack IsBlock
    else if n = 11 then Stack Equal
    else if n = 12 then Stack Add
    else if n = 13 then Stack Sub
    else if n = 14 then Stack Mult
    else if n = 15 then Stack Div
    else if n = 16 then Stack Mod
    else if n = 17 then Stack Less
    else if n = 19 then Gupdate x1
    else if n = 20 then Label x1
    else if n = 21 then Jump (Addr x1)
    else if n = 22 then JumpIf (Addr x1)
    else if n = 23 then Call (Addr x1)
    else if n = 24 then PushPtr (Addr x1)
    else if n = 41 then Jump (Lab x1)
    else if n = 42 then JumpIf (Lab x1)
    else if n = 43 then Call (Lab x1)
    else if n = 44 then PushPtr (Lab x1)
    else if n = 26 then CallPtr
    else if n = 27 then Return
    else if n = 28 then PushExc
    else if n = 29 then PopExc
    else if n = 30 then Ref
    else if n = 45 then RefByte
    else if n = 31 then Deref
    else if n = 46 then DerefByte
    else if n = 32 then Update
    else if n = 47 then UpdateByte
    else if n = 39 then Length
    else if n = 49 then LengthByte
    else if n = 37 then Stop F
    else if n = 38 then Stop T
    else if n = 34 then Tick
    else if n = 35 then Print
    else if n = 40 then PrintWord8
    else if n = 36 then PrintC (CHR (if x1 < 256 then x1 else 0))
    else Label 0`;

val num_bc_bc_num = store_thm("num_bc_bc_num",
  ``!x. num_bc (bc_num x) = x``,
  Cases THEN TRY (Cases_on `b`) THEN TRY (Cases_on `l`) THEN EVAL_TAC
  THEN SIMP_TAC std_ss [stringTheory.ORD_BOUND]
  THEN Cases_on `i < 0` THEN FULL_SIMP_TAC std_ss []
  THEN intLib.COOPER_TAC);

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

val with_same_handler = store_thm("with_same_handler",
  ``(x with handler := x.handler) = x``,
  rw[bc_state_component_equality])
val _ = export_rewrites["with_same_handler"]

val bc_fetch_with_stack = store_thm("bc_fetch_with_stack",
  ``bc_fetch (s with stack := st) = bc_fetch s``,
  rw[bc_fetch_def])

val bc_fetch_with_refs = store_thm("bc_fetch_with_refs",
  ``bc_fetch (s with refs := st) = bc_fetch s``,
  rw[bc_fetch_def])

val bump_pc_with_stack = store_thm("bump_pc_with_stack",
  ``bump_pc (s with stack := st) = (bump_pc s) with stack := st``,
  rw[bump_pc_def,bc_fetch_with_stack] >>
  BasicProvers.EVERY_CASE_TAC)

val bump_pc_inst_length = store_thm("bump_pc_inst_length",
  ``(bump_pc s).inst_length = s.inst_length``,
  rw[bump_pc_def] >> BasicProvers.CASE_TAC >> rw[])
val _ = export_rewrites["bump_pc_inst_length"]

val bc_fetch_aux_MAP = store_thm("bc_fetch_aux_MAP",
  ``!il f. (∀x. il (f x) = il x) ∧ (∀x. is_Label (f x) = is_Label x) ⇒
      ∀ls n. (bc_fetch_aux (MAP f ls) il n = OPTION_MAP f (bc_fetch_aux ls il n))``,
  ntac 2 gen_tac >> strip_tac >>
  Induct >> rw[bc_fetch_aux_def])

val bc_fetch_MAP = store_thm("bc_fetch_MAP",
  ``∀f s. (∀x. s.inst_length (f x) = s.inst_length x) ∧ (∀x. is_Label (f x) = is_Label x) ⇒
    (bc_fetch (s with <| code := MAP f s.code |>) = OPTION_MAP f (bc_fetch s))``,
  rw[bc_fetch_def,bc_fetch_aux_MAP])

val bc_find_loc_aux_NONE = store_thm("bc_find_loc_aux_NONE",
  ``∀il l ls n. (bc_find_loc_aux ls il l n = NONE) ⇒ ¬MEM (Label l) ls``,
  ntac 2 gen_tac >>
  Induct >> rw[bc_find_loc_aux_def] >>
  res_tac >> fs[])

val bc_find_loc_aux_MEM = store_thm("bc_find_loc_aux_MEM",
  ``∀il l ls n. (bc_find_loc_aux ls il l n ≠ NONE) ⇒ MEM (Label l) ls``,
  ntac 2 gen_tac >>
  Induct >> rw[bc_find_loc_aux_def] >>
  res_tac)

val dest_Label_def = Define`(dest_Label (Label n) = n)`
val _ = export_rewrites["dest_Label_def"]

val is_Label_rwt = store_thm("is_Label_rwt",
  ``∀i. is_Label i = ∃l. i = Label l``,
  Cases >> rw[])

val addr_of_el_def = Define`
  (addr_of_el il n [] = NONE) ∧
  (addr_of_el il n (x::xs) =
   if n = 0 then if is_Label x then NONE else SOME 0 else
     OPTION_BIND (addr_of_el il (n - 1) xs) (λm. SOME (m + (if is_Label x then 0 else il x + 1))))`
val _ = export_rewrites["addr_of_el_def"]

val bc_fetch_aux_addr_of_el = store_thm("bc_fetch_aux_addr_of_el",
  ``∀c il pc n. (addr_of_el il n c = SOME pc) ⇒ (bc_fetch_aux c il pc = SOME (EL n c))``,
  Induct >> rw[] >>
  Cases_on `n` >> fs[] >>
  spose_not_then strip_assume_tac >>
  DECIDE_TAC)

val bc_fetch_aux_not_label = store_thm("bc_fetch_aux_not_label",
  ``∀c il pc i. (bc_fetch_aux c il pc = SOME i) ⇒ ¬is_Label i``,
  Induct >> rw[] >> fs[] >> PROVE_TAC[])

val labels_only_def = Define`
  (labels_only (Jump (Addr _)) = F) ∧
  (labels_only (JumpIf (Addr _)) = F) ∧
  (labels_only (Call (Addr _)) = F) ∧
  (labels_only (PushPtr (Addr _)) = F) ∧
  (labels_only _ = T)`
val _ = export_rewrites["labels_only_def"]

val bc_fetch_next_addr = store_thm("bc_fetch_next_addr",
  ``∀bc0 bs x bc.
    (bs.code = bc0 ++ (x::bc)) ∧ (¬is_Label x) ∧
    (bs.pc = next_addr bs.inst_length bc0)
    ⇒
    (bc_fetch bs = SOME x)``,
  Induct >- rw[bc_fetch_def] >>
  rw[bc_fetch_def] >>
  fsrw_tac[ARITH_ss][bc_fetch_def,ADD1] >>
  first_x_assum (qspec_then `bs with <| code := TL bs.code ; pc := next_addr bs.inst_length bc0 |>` mp_tac) >>
  rw[])

val bc_find_loc_aux_thm = store_thm("bc_find_loc_aux_thm",
  ``∀il ls l n.
     bc_find_loc_aux ls il l n =
     if MEM (Label l) ls then
     SOME (n + SUM (MAP (SUC o il) (FILTER ($~ o is_Label) (TAKE (LEAST m. m < LENGTH ls ∧ (EL m ls = Label l)) ls))))
     else NONE``,
  gen_tac >> Induct >- rw[bc_find_loc_aux_def] >>
  simp[bc_find_loc_aux_def] >>
  qx_gen_tac `h` >> qx_gen_tac `l` >>
  Cases_on `h = Label l` >> fs[] >- (
    qx_gen_tac `n` >>
    qmatch_abbrev_tac `n = n + m` >>
    qsuff_tac `m = 0` >- rw[] >>
    unabbrev_all_tac >>
    numLib.LEAST_ELIM_TAC >>
    conj_tac >- (
      qexists_tac `0` >> rw[] ) >>
    gen_tac >>
    strip_tac >>
    first_x_assum (qspec_then `0` mp_tac) >>
    srw_tac[ARITH_ss][] ) >>
  Cases_on `MEM (Label l) ls` >> fs[] >>
  Q.PAT_ABBREV_TAC`l0 = $LEAST X` >>
  Q.PAT_ABBREV_TAC`l1 = $LEAST X` >>
  `(SUC l0) = l1` by (
    unabbrev_all_tac >>
    qmatch_abbrev_tac `SUC ($LEAST P) = X` >>
    `∃n. P n` by (
      fs[MEM_EL,Abbr`P`] >>
      PROVE_TAC[] ) >>
    rw[UNDISCH(Q.SPEC`n`SUC_LEAST)] >>
    unabbrev_all_tac >>
    AP_TERM_TAC >>
    rw[FUN_EQ_THM] >>
    Cases_on `m` >> rw[] ) >>
  srw_tac[ARITH_ss][])

val bc_find_loc_aux_ALL_DISTINCT = store_thm("bc_find_loc_aux_ALL_DISTINCT",
  ``∀ls il l n z k. ALL_DISTINCT (FILTER is_Label ls) ∧ (k < LENGTH ls) ∧ (EL k ls = Label l) ∧
    (z = n + next_addr il (TAKE k ls)) ⇒
    (bc_find_loc_aux ls il l n = SOME z)``,
  rw[bc_find_loc_aux_thm] >- (
   rw[MEM_EL] >> PROVE_TAC[] ) >>
  numLib.LEAST_ELIM_TAC >>
  conj_tac >- PROVE_TAC[] >>
  qx_gen_tac `j` >> rw[] >>
  qsuff_tac `k = j` >> rw[] >>
  match_mp_tac (Q.ISPEC`is_Label`ALL_DISTINCT_FILTER_EL_IMP) >>
  qexists_tac `ls` >> rw[])

val bc_fetch_aux_append_code = store_thm("bc_fetch_aux_append_code",
  ``∀il ls n l2 i. (bc_fetch_aux ls il n = SOME i) ⇒ (bc_fetch_aux (ls ++ l2) il n = SOME i)``,
    gen_tac >> Induct >> rw[bc_fetch_aux_def] )

val bc_fetch_append_code = store_thm("bc_fetch_append_code",
  ``(bc_fetch bs = SOME i) ⇒ (bc_fetch (bs with code := bs.code ++ c) = SOME i)``,
  rw[bc_fetch_def] >>
  imp_res_tac bc_fetch_aux_append_code >>
  rw[] )

val bc_find_loc_aux_append_code = store_thm("bc_find_loc_aux_append_code",
  ``∀il ls n l2 l i. (bc_find_loc_aux ls il n l = SOME i) ⇒ (bc_find_loc_aux (ls ++ l2) il n l = SOME i)``,
  gen_tac >> Induct >> rw[bc_find_loc_aux_def] )

val bc_find_loc_append_code = store_thm("bc_find_loc_append_code",
  ``(bc_find_loc bs l = SOME n) ⇒ (bc_find_loc (bs with code := bs.code ++ c) l = SOME n)``,
  Cases_on `l` >> rw[bc_find_loc_def] >>
  imp_res_tac bc_find_loc_aux_append_code >>
  rw[] )

val bc_next_append_code = store_thm("bc_next_append_code",
  ``∀bs1 bs2. bc_next bs1 bs2 ⇒ ∀c0 c. (bs1.code = c0) ⇒ bc_next (bs1 with code := c0 ++ c) (bs2 with code := c0 ++ c)``,
  ho_match_mp_tac bc_next_ind >> rw[] >>
  rw[bc_eval1_thm] >>
  imp_res_tac bc_fetch_append_code >>
  imp_res_tac bc_find_loc_append_code >>
  rw[bc_eval1_def,LET_THM,wordsTheory.w2n_lt,
     SIMP_RULE std_ss [combinTheory.K_DEF] REPLICATE_GENLIST] >>
  simp[REVERSE_APPEND,EL_APPEND2,TAKE_APPEND2] >>
  rw[bump_pc_with_stack] >>
  rw[bump_pc_def] >>
  rw[bc_state_component_equality] >>
  fs[bc_eval_stack_thm] >>
  rw[stringTheory.IMPLODE_EXPLODE_I] >>
  TRY (BasicProvers.CASE_TAC >> rw[bc_state_component_equality,PRE_SUB1]) >>
  wordsLib.WORD_DECIDE_TAC);

val bc_next_preserves_code = store_thm("bc_next_preserves_code",
  ``∀bs1 bs2. bc_next bs1 bs2 ⇒ (bs2.code = bs1.code)``,
  ho_match_mp_tac bc_next_ind >>
  rw[bump_pc_def] >>
  BasicProvers.EVERY_CASE_TAC >> rw[])

val bc_next_preserves_inst_length = store_thm("bc_next_preserves_inst_length",
  ``∀bs1 bs2. bc_next bs1 bs2 ⇒ (bs2.inst_length = bs1.inst_length)``,
  ho_match_mp_tac bc_next_ind >>
  rw[bump_pc_def] >>
  BasicProvers.EVERY_CASE_TAC >> rw[])

val RTC_bc_next_preserves = store_thm("RTC_bc_next_preserves",
  ``∀bs1 bs2. bc_next^* bs1 bs2 ⇒ (bs2.code = bs1.code) ∧ (bs2.inst_length = bs1.inst_length)``,
  assume_tac(Q.ISPECL[`bc_next`,`λs. (s.code,s.inst_length)`](Q.GENL[`f`,`R`]RTC_lifts_equalities)) >>
  fs[] >> metis_tac[bc_next_preserves_code,bc_next_preserves_inst_length])

val RTC_bc_next_append_code = store_thm("RTC_bc_next_append_code",
  ``∀bs1 bs2 bs1c bs2c c. RTC bc_next bs1 bs2 ∧
    (bs1c = bs1 with code := bs1.code ++ c) ∧
    (bs2c = bs2 with code := bs2.code ++ c)
    ⇒ RTC bc_next bs1c bs2c``,
  rw[] >> (
     RTC_lifts_monotonicities
  |> Q.GEN`R` |> Q.ISPEC `bc_next`
  |> Q.GEN`f` |> Q.SPEC `λbs. bs with code := bs.code ++ c`
  |> strip_assume_tac) >> fs[] >> pop_assum (match_mp_tac o MP_CANON) >>
  rw[] >>
  imp_res_tac bc_next_append_code >> fs[] >>
  metis_tac[bc_next_preserves_code])

val bc_next_clock_less = store_thm("bc_next_clock_less",
  ``∀bs1 bs2. bc_next bs1 bs2 ⇒ OPTREL $>= bs1.clock bs2.clock``,
  ho_match_mp_tac bc_next_ind >>
  simp[bump_pc_def] >>
  conj_tac >- ( rw[] >> BasicProvers.CASE_TAC >> rw[] ) >>
  rw[] >>
  Cases_on`bs1.clock`>>fs[]>>
  simp[optionTheory.OPTREL_def])

val RTC_bc_next_clock_less = store_thm("RTC_bc_next_clock_less",
  ``∀bs1 bs2. RTC bc_next bs1 bs2 ⇒
    OPTREL $>= bs1.clock bs2.clock``,
  rw[] >> (
     RTC_lifts_reflexive_transitive_relations
  |> Q.GEN`R` |> Q.ISPEC `bc_next`
  |> Q.GEN`Q` |> Q.ISPEC `OPTREL $>=`
  |> Q.GEN`f` |> Q.ISPEC `bc_state_clock`
  |> strip_assume_tac) >> fs[] >> pop_assum (match_mp_tac o MP_CANON) >>
  rw[reflexive_def,transitive_def] >- (
    match_mp_tac bc_next_clock_less >> rw[] ) >>
  fs[optionTheory.OPTREL_def] >> rw[] >> simp[])

val bc_fetch_aux_end_NONE = store_thm("bc_fetch_aux_end_NONE",
  ``∀ls il n. next_addr il ls ≤ n ⇒ bc_fetch_aux ls il n = NONE``,
  Induct >> simp[] >> rw[] >> fs[arithmeticTheory.ADD1] >>
  first_x_assum match_mp_tac >> simp[])

val bc_next_output_IS_PREFIX = store_thm("bc_next_output_IS_PREFIX",
  ``∀s1 s2. bc_next s1 s2 ⇒ IS_PREFIX s2.output s1.output``,
  ho_match_mp_tac bc_next_ind >> simp[] >> simp[bump_pc_def] >> rw[IS_PREFIX_SNOC] >>
  BasicProvers.CASE_TAC >> rw[])

val RTC_bc_next_output_IS_PREFIX = store_thm("RTC_bc_next_output_IS_PREFIX",
  ``∀bs1 bs2. RTC bc_next bs1 bs2 ⇒
    IS_PREFIX bs2.output bs1.output``,
  rw[] >> (
     RTC_lifts_reflexive_transitive_relations
  |> Q.GEN`R` |> Q.ISPEC `bc_next`
  |> Q.GEN`Q` |> Q.ISPEC `combin$C IS_PREFIX`
  |> Q.GEN`f` |> Q.ISPEC `bc_state_output`
  |> strip_assume_tac) >> fs[] >> pop_assum (match_mp_tac o MP_CANON) >>
  rw[reflexive_def,transitive_def] >- (
    match_mp_tac bc_next_output_IS_PREFIX >> rw[] ) >>
  metis_tac[IS_PREFIX_TRANS])

val RTC_bc_next_output_squeeze = store_thm("RTC_bc_next_output_squeeze",
  ``RTC bc_next x y /\ RTC bc_next y z /\ (z.output = x.output) ==>
    (y.output = x.output)``,
  REPEAT STRIP_TAC \\ IMP_RES_TAC RTC_bc_next_output_IS_PREFIX
  \\ METIS_TAC [rich_listTheory.IS_PREFIX_ANTISYM]);

val bvs_to_chars_thm = store_thm("bvs_to_chars_thm",
  ``∀bvs ac. bvs_to_chars bvs ac =
      if EVERY is_Number bvs then
         SOME(REVERSE ac ++ MAP (CHR o Num o ABS o dest_Number) bvs)
      else NONE``,
  Induct >> simp[bvs_to_chars_def] >>
  Cases >> rw[bvs_to_chars_def])

val between_labels_def = Define`
  between_labels bc l1 l2 ⇔
  ALL_DISTINCT (FILTER is_Label bc) ∧
  EVERY (between l1 l2) (MAP dest_Label (FILTER is_Label bc)) ∧
  l1 ≤ l2`

val good_labels_def = Define`
  good_labels nl code ⇔
    ALL_DISTINCT (FILTER is_Label code) ∧
    EVERY (combin$C $< nl o dest_Label) (FILTER is_Label code)`

val code_executes_ok_def = Define `
  code_executes_ok s1 ⇔
      (* termination *)
      (?s2 b. bc_next^* s1 s2 /\ bc_fetch s2 = SOME (Stop b)) \/
      (* or divergence with no output *)
      !n. ?s2. NRC bc_next n s1 s2 /\ (s2.output = s1.output)`;

val gvrel_def = Define`
  gvrel gv1 gv2 ⇔ LENGTH gv1 ≤ LENGTH gv2 ∧
    (∀n x. n < LENGTH gv1 ∧ (EL n gv1 = SOME x) ⇒ (EL n gv2 = SOME x))`

val gvrel_refl = store_thm("gvrel_refl",
  ``gvrel g g``, rw[gvrel_def])
val _ = export_rewrites["gvrel_refl"]

val gvrel_trans = store_thm("gvrel_trans",
  ``gvrel gv1 gv2 ∧ gvrel gv2 gv3 ⇒ gvrel gv1 gv3``,
  rw[gvrel_def] >> fsrw_tac[ARITH_ss][])

val bc_next_gvrel = store_thm("bc_next_gvrel",
  ``∀bs1 bs2. bc_next bs1 bs2 ⇒ gvrel bs1.globals bs2.globals``,
  ho_match_mp_tac bytecodeTheory.bc_next_ind >>
  simp[bytecodeTheory.bump_pc_def] >>
  rw[] >- ( BasicProvers.CASE_TAC >> simp[] ) >>
  simp[gvrel_def] >> rw[EL_LUPDATE] >>
  simp[rich_listTheory.EL_APPEND1])

val RTC_bc_next_gvrel = store_thm("RTC_bc_next_gvrel",
  ``∀bs1 bs2. RTC bc_next bs1 bs2 ⇒
    gvrel bs1.globals bs2.globals``,
  ho_match_mp_tac relationTheory.RTC_lifts_reflexive_transitive_relations >>
  rw[relationTheory.reflexive_def,relationTheory.transitive_def,bc_next_gvrel] >>
  metis_tac[gvrel_trans])

val same_length_gvrel_same = store_thm("same_length_gvrel_same",
  ``∀l1 l2. LENGTH l1 = LENGTH l2 ∧ EVERY IS_SOME l1 ∧ gvrel l1 l2 ⇒ l1 = l2``,
  rw[gvrel_def,LIST_EQ_REWRITE,EVERY_MEM,MEM_EL,PULL_EXISTS,IS_SOME_EXISTS] >>
  metis_tac[])

val _ = export_theory()
