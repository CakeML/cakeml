open HolKernel boolLib bossLib Parse lcsymtacs
open SemanticPrimitivesTheory bytecodeTerminationTheory arithmeticTheory listTheory finite_mapTheory integerTheory whileTheory relationTheory
val _ = new_theory "bytecodeEval";

val isNumber_def = Define`
  (isNumber (Number _) = T) ∧
  (isNumber _ = F)`
val _ = export_rewrites["isNumber_def"]

val isNumber_exists_thm = store_thm(
"isNumber_exists_thm",
``∀x. isNumber x = ∃n. x = Number n``,
Cases >> rw[]);

val bc_eval_stack_def = Define`
  (bc_eval_stack Pop (x::xs) = SOME xs)
∧ (bc_eval_stack (Pops k) (x::xs) =
   if k ≤ LENGTH xs then SOME (x::(DROP k xs)) else NONE)
∧ (bc_eval_stack (Shift j k) xs =
   if j+k ≤ LENGTH xs then SOME (TAKE j xs++DROP (j+k) xs) else NONE)
∧ (bc_eval_stack (PushInt n) xs =
   SOME (Number n::xs))
∧ (bc_eval_stack (Cons tag k) xs =
   if k ≤ LENGTH xs then SOME (Block tag (REVERSE (TAKE k xs))::(DROP k xs)) else NONE)
∧ (bc_eval_stack (Load k) xs =
   if k < LENGTH xs then SOME (EL k xs::xs) else NONE)
∧ (bc_eval_stack (Store k) (y::xs) =
   if k < LENGTH xs ∧ 0 < LENGTH xs
   then SOME (TAKE k xs ++ y :: (DROP (k+1) xs)) else NONE)
∧ (bc_eval_stack (LoadRev k) xs =
   if k < LENGTH xs then SOME (EL k (REVERSE xs)::xs) else NONE)
∧ (bc_eval_stack (El k) ((Block tag ys)::xs) =
   if k < LENGTH ys then SOME (EL k ys::xs) else NONE)
∧ (bc_eval_stack (TagEq t) ((Block tag ys)::xs) =
   SOME (bool_to_val (tag = t)::xs))
∧ (bc_eval_stack Equal (x2::x1::xs) =
   SOME (bool_to_val (x1 = x2)::xs))
∧ (bc_eval_stack Less (Number n :: Number m :: xs) =
   SOME (bool_to_val (m < n)::xs))
∧ (bc_eval_stack Add (Number n :: Number m :: xs) =
   SOME (Number (m + n)::xs))
∧ (bc_eval_stack Sub (Number n :: Number m :: xs) =
   SOME (Number (m - n)::xs))
∧ (bc_eval_stack Mult (Number n :: Number m :: xs) =
   SOME (Number (m * n)::xs))
∧ (bc_eval_stack Div (Number n :: Number m :: xs) =
   if n = 0 then NONE else
   SOME (Number (m / n)::xs))
∧ (bc_eval_stack Mod (Number n :: Number m :: xs) =
   if n = 0 then NONE else
   SOME (Number (m % n)::xs))
∧ (bc_eval_stack _ _ = NONE)`

val bc_eval_stack_thm1 = prove(
``∀op xs ys. bc_stack_op op xs ys ⇒ (bc_eval_stack op xs = SOME ys)``,
ho_match_mp_tac bc_stack_op_ind >>
rw[bc_eval_stack_def, isNumber_exists_thm,
   rich_listTheory.FIRSTN_LENGTH_APPEND,
   rich_listTheory.BUTFIRSTN_LENGTH_APPEND] >>
srw_tac[ARITH_ss][GSYM arithmeticTheory.ADD1] >- (
  PROVE_TAC [ADD_COMM, APPEND_ASSOC,
    arithmeticTheory.LESS_EQ_ADD, LENGTH_APPEND,
    rich_listTheory.BUTFIRSTN_BUTFIRSTN,
    rich_listTheory.BUTFIRSTN_LENGTH_APPEND]
) >>
Induct_on `ys` >>
rw[rich_listTheory.BUTFIRSTN])

val bc_eval_stack_thm2 = prove(
``∀op xs ys. (bc_eval_stack op xs = SOME ys) ⇒ bc_stack_op op xs ys``,
Cases >> Cases >>
TRY (
  qmatch_rename_tac `∀ys. (bc_eval_stack (Shift j k) [] = SOME ys) ⇒
    bc_stack_op (Shift j k) [] ys` [] >>
  simp_tac bool_ss [bc_eval_stack_def] >>
  rw[] >> rw[bc_stack_op_cases] ) >>
TRY (
  qmatch_rename_tac `∀ys. (bc_eval_stack (Shift j k) (h::t) = SOME ys) ⇒
    bc_stack_op (Shift j k) (h::t) ys` [] >>
  rw[bc_eval_stack_def,bc_stack_op_cases,LENGTH_NIL_SYM] >> fs[] >- (
    qexists_tac `h::(TAKE (k - 1) t)` >>
    srw_tac[ARITH_ss][ADD1] ) >>
  map_every qexists_tac [`h::(TAKE (j-1) t)`,`TAKE k (DROP (j-1) t)`,`DROP (j+k-1) t`] >>
  Cases_on `k=0` >> srw_tac[ARITH_ss][] >>
  Q.ISPECL_THEN [`TAKE (j-1) t`,`DROP (j-1) t`,`j + k - 1`] (mp_tac o GSYM)
    (Q.GEN `l1` (Q.GEN `l2` TAKE_APPEND2)) >>
  srw_tac[ARITH_ss][]) >>
fs[bc_eval_stack_def,bc_stack_op_cases,isNumber_exists_thm] >> rw[]
>- (
  qmatch_assum_rename_tac `n ≤ LENGTH t` [] >>
  qexists_tac `TAKE n t` >> rw[])
>- (
  qmatch_rename_tac
    `∃(ys:bc_value list).
      (n = LENGTH ys) ∧
      (h::t = ys ++ DROP (n - 1) t) ∧
      (REVERSE (TAKE (n - 1) t) ++ [h] = REVERSE ys)` [] >>
  qexists_tac `TAKE n (h::t)` >> rw[] )
>- (
  qmatch_assum_rename_tac `n < LENGTH t` [] >>
  map_every qexists_tac [`TAKE n t`,`EL n t`,`DROP (n+1) t`] >>
  imp_res_tac arithmeticTheory.LESS_IMP_LESS_OR_EQ >>
  rw[] >>
  qpat_assum `n < LENGTH t` mp_tac >>
  rpt (pop_assum (K ALL_TAC)) >>
  qid_spec_tac `n` >>
  Induct_on `t` >> fs[] >>
  rw[] >> fs[DROP_def] >>
  first_x_assum (qspec_then `n-1` mp_tac) >>
  srw_tac[ARITH_ss][] >>
  Cases_on `n` >> fs[] )
>- (
  qmatch_assum_rename_tac `bc_eval_stack (El n) (h::t) = SOME ys` [] >>
  Cases_on `h` >> fs[bc_eval_stack_def] )
>- (
  qmatch_assum_rename_tac `bc_eval_stack (TagEq n) (h::t) = SOME ys` [] >>
  Cases_on `h` >> fs[bc_eval_stack_def] )
>- (
  qmatch_assum_rename_tac `bc_eval_stack Equal (h::t) = SOME ys` [] >>
  Cases_on `h` >> Cases_on `t` >> fs[bc_eval_stack_def] )
>- (
  qmatch_assum_rename_tac `bc_eval_stack Add (h::t) = SOME ys` [] >>
  Cases_on `h` >> Cases_on `HD t` >> Cases_on `t` >> fs[bc_eval_stack_def] )
>- (
  qmatch_assum_rename_tac `bc_eval_stack Sub (h::t) = SOME ys` [] >>
  Cases_on `h` >> Cases_on `HD t` >> Cases_on `t` >> fs[bc_eval_stack_def] )
>- (
  qmatch_assum_rename_tac `bc_eval_stack Mult (h::t) = SOME ys` [] >>
  Cases_on `h` >> Cases_on `HD t` >> Cases_on `t` >> fs[bc_eval_stack_def] )
>- (
  qmatch_assum_rename_tac `bc_eval_stack Div (h::t) = SOME ys` [] >>
  Cases_on `h` >> Cases_on `HD t` >> Cases_on `t` >> fs[bc_eval_stack_def] )
>- (
  qmatch_assum_rename_tac `bc_eval_stack Mod (h::t) = SOME ys` [] >>
  Cases_on `h` >> Cases_on `HD t` >> Cases_on `t` >> fs[bc_eval_stack_def] )
>- (
  qmatch_assum_rename_tac `bc_eval_stack Less (h::t) = SOME ys` [] >>
  Cases_on `h` >> Cases_on `HD t` >> Cases_on `t` >> fs[bc_eval_stack_def] )
)

val bc_eval_stack_thm = store_thm(
"bc_eval_stack_thm",
``∀op xs ys. bc_stack_op op xs ys = (bc_eval_stack op xs = SOME ys)``,
rpt gen_tac >> EQ_TAC >| map (ACCEPT_TAC o SPEC_ALL)
[bc_eval_stack_thm1, bc_eval_stack_thm2])

val bc_eval_stack_NONE = store_thm(
"bc_eval_stack_NONE",
``∀op xs. (bc_eval_stack op xs = NONE) = (∀ys. ¬bc_stack_op op xs ys)``,
PROVE_TAC[bc_eval_stack_thm,
optionTheory.option_CASES,
optionTheory.NOT_SOME_NONE])

val bc_eval1_def = Define`
  bc_eval1 s = OPTION_BIND (bc_fetch s)
  (λx. case (x, s.stack) of
  | (Stack b, _) =>
    OPTION_BIND (bc_eval_stack b s.stack)
      (λys. SOME (bump_pc s with stack := ys))
  | (Jump l, _) =>
    OPTION_BIND (bc_find_loc s l)
      (λn. SOME (s with pc := n))
  | (JumpIf l, (Block b [])::xs) =>
    OPTION_BIND (bc_find_loc s l)
      (λn. let s' = s with stack := xs in
        if b = 0 then SOME (bump_pc s') else
        if b = 1 then SOME (s' with pc := n) else
        NONE)
  | (Call l, x::xs) =>
      OPTION_BIND (bc_find_loc s l)
      (λn. SOME (s with <| pc := n; stack := x :: CodePtr ((bump_pc s).pc) :: xs |>))
  | (CallPtr, CodePtr ptr::x::xs) =>
      SOME (s with <| pc := ptr; stack := x :: CodePtr ((bump_pc s).pc) :: xs |>)
  | (JumpPtr, CodePtr ptr::xs) =>
     SOME (s with <| pc := ptr; stack := xs |>)
  | (PushPtr l, xs) =>
      OPTION_BIND (bc_find_loc s l)
        (λn. SOME (bump_pc s with <| stack := CodePtr n::xs |>))
  | (Return, x :: CodePtr n :: xs) =>
     SOME (s with <| pc := n; stack := x::xs |>)
  | (PushExc, xs) =>
     SOME (bump_pc s with <| handler := LENGTH xs; stack := StackPtr s.handler::xs|>)
  | (PopExc, x::xs) =>
    if s.handler < LENGTH xs then
      case EL s.handler (REVERSE xs) of
      | (StackPtr sp) => SOME (bump_pc s with <| handler := sp; stack := x::(REVERSE (TAKE s.handler (REVERSE xs))) |>)
      | _ => NONE
    else NONE
  | (Ref, x::xs) =>
     let ptr = LEAST n. n ∉ (FDOM s.refs) in
     SOME (bump_pc s with <| stack := (RefPtr ptr)::xs;
                             refs := s.refs |+ (ptr,x) |>)
  | (Deref, (RefPtr ptr)::xs) =>
      if (ptr IN FDOM s.refs) then
        SOME (bump_pc s with <| stack := (s.refs ' ptr)::xs |>)
      else NONE
  | (Update, x::(RefPtr ptr)::xs) =>
      if (ptr IN FDOM s.refs) then
        SOME (bump_pc s with <| stack := xs ;
                                refs := s.refs |+ (ptr,x) |>)
      else NONE
  | (Tick, _) =>
    (case s.clock of
     | NONE => SOME (bump_pc s)
     | SOME n => if n > 0 then SOME (bump_pc s with <| clock := SOME (n-1) |>) else NONE)
  | (Print, x::xs) =>
    SOME (bump_pc s with <| stack := xs; output := STRCAT(IMPLODE(REVERSE(EXPLODE(ov_to_string(bv_to_ov s.cons_names x))))) s.output |>)
  | (PrintE, Number i::xs) =>
    SOME (bump_pc s with <| stack := xs; output := STRCAT(IMPLODE(REVERSE(EXPLODE(CONCAT["raise <";int_to_string i;">"])))) s.output |>)
  | (PrintE, Block n []::xs) =>
    if n = 5 ∧ n = 5 then
    SOME (bump_pc s with <| stack := xs; output := STRCAT(IMPLODE(REVERSE(EXPLODE("raise <Bind>")))) s.output |>)
    else if n = 6 then
    SOME (bump_pc s with <| stack := xs; output := STRCAT(IMPLODE(REVERSE(EXPLODE("raise <Div>")))) s.output |>)
    else NONE
  | (PrintC c,_) =>
    SOME (bump_pc s with <| output := STRING c s.output |>)
  | _ => NONE)`

val bc_eval1_SOME = store_thm(
"bc_eval1_SOME",
``∀s1 s2. (bc_eval1 s1 = SOME s2) ⇒ bc_next s1 s2``,
rw[bc_eval1_def] >>
qmatch_assum_rename_tac `bc_fetch s1 = SOME inst` [] >>
Cases_on `inst` >> fs[GSYM bc_eval_stack_thm]
>- rw[bc_next_rules]
>- rw[bc_next_rules]
>- (
  Cases_on `s1.stack` >> fs[LET_THM] >>
  Cases_on `h` >> fs[LET_THM] >>
  qpat_assum `X = SOME s2` mp_tac >>
  BasicProvers.EVERY_CASE_TAC >> rw[] >>
  rw[bc_next_cases] >>
  ((qexists_tac `T` >> rw[] >> NO_TAC) ORELSE
   (qexists_tac `F` >> rw[] >> NO_TAC)))
>- (
  Cases_on `s1.stack` >> fs[LET_THM] >>
  rw[bc_next_cases] )
>- (
  Cases_on `s1.stack` >> fs[LET_THM] >>
  qmatch_assum_rename_tac `s1.stack = h::t` [] >>
  Cases_on `h` >> fs[] >>
  rw[bc_next_cases] )
>- (
  Cases_on `s1.stack` >> fs[LET_THM] >>
  qmatch_assum_rename_tac `s1.stack = h::t` [] >>
  Cases_on `h` >> Cases_on `t` >> fs[] >>
  rw[bc_next_cases] )
>- ( rw[bc_next_rules] )
>- (
  Cases_on `s1.stack` >> fs[LET_THM] >>
  qmatch_assum_rename_tac `s1.stack = h::t` [] >>
  Cases_on `t` >> fs [] >>
  qmatch_assum_rename_tac `s1.stack = x::y::t` [] >>
  Cases_on `y` >> fs [] >>
  rw[bc_next_cases] )
>- ( rw[bc_next_cases] )
>- (
  Cases_on `s1.stack` >> fs[LET_THM] >>
  qmatch_assum_rename_tac`s1.stack = x::xs`[] >>
  Cases_on `s1.handler < LENGTH xs` >> fs[LET_THM] >>
  Cases_on `EL s1.handler (REVERSE xs)` >> fs[LET_THM] >>
  rw[bc_next_cases,BytecodeTheory.bc_state_component_equality] >>
  qpat_assum`X = x::xs`kall_tac >>
  qpat_assum`X = SOME PopExc`kall_tac >>
  qmatch_assum_rename_tac`m < LENGTH xs`[] >>
  Induct_on`xs`>>fs[] >>
  fs[ADD1] >> rpt gen_tac >> strip_tac >>
  Cases_on`m < LENGTH xs` >- (
    lrw[rich_listTheory.EL_APPEND1,rich_listTheory.TAKE_APPEND1] >>
    fs[] >> qexists_tac`h::l1` >> lrw[] ) >>
  `m = LENGTH xs` by DECIDE_TAC >>
  lrw[rich_listTheory.EL_APPEND2,rich_listTheory.TAKE_APPEND2])
>- (
  Cases_on `s1.stack` >> fs[LET_THM] >>
  rw[bc_next_cases] )
>- (
  Cases_on `s1.stack` >> fs[LET_THM] >>
  qmatch_assum_rename_tac `s1.stack = h::t` [] >>
  Cases_on `h` >> fs[] >>
  rw[bc_next_cases] )
>- (
  Cases_on `s1.stack` >> fs[LET_THM] >>
  qmatch_assum_rename_tac `s1.stack = h::t` [] >>
  Cases_on `t` >> fs [] >>
  qmatch_assum_rename_tac `s1.stack = x::y::t` [] >>
  Cases_on `y` >> fs [] >>
  rw[bc_next_cases] )
>- (
  pop_assum mp_tac >>
  BasicProvers.EVERY_CASE_TAC >>
  rw[bc_next_cases,PRE_SUB1] >>
  rw[BytecodeTheory.bc_state_component_equality,bump_pc_def])
>- (
  Cases_on `s1.stack` >> fs[LET_THM] >>
  rw[bc_next_cases] )
>- (
  Cases_on`s1.stack`>>fs[]>>
  Cases_on`h`>>fs[]>-(
    rw[bc_next_cases] ) >>
  rw[bc_next_cases]>>
  Cases_on`l`>>fs[]>>
  Cases_on`n=5`>>fs[])
>- ( rw[bc_next_cases] ))

val bc_next_bc_eval1 = store_thm(
"bc_next_bc_eval1",
``∀s1 s2. bc_next s1 s2 ⇒ (bc_eval1 s1 = SOME s2)``,
ho_match_mp_tac bc_next_ind >>
rw[bc_eval1_def] >>
fs[bc_eval_stack_thm] >>
unabbrev_all_tac >> rw[] >>
fsrw_tac[ARITH_ss][] >>
lrw[REVERSE_APPEND,rich_listTheory.EL_APPEND2,rich_listTheory.TAKE_APPEND1] >>
TRY(
  pop_assum (assume_tac o SYM) >>
  lrw[rich_listTheory.TAKE_REVERSE,rich_listTheory.LASTN_LENGTH_ID]) >>
BasicProvers.EVERY_CASE_TAC >> fs[PRE_SUB1] >>
rw[BytecodeTheory.bc_state_component_equality,bump_pc_def])

val bc_eval1_thm = store_thm("bc_eval1_thm",
  ``!s1 s2. bc_next s1 s2 = (bc_eval1 s1 = SOME s2)``,
rw[] >> EQ_TAC >> rw[bc_eval1_SOME,bc_next_bc_eval1])

val bc_eval_def = Define`bc_eval = OWHILE (IS_SOME o bc_eval1) (THE o bc_eval1)`

val bc_eval_compute = store_thm("bc_eval_compute",
  ``∀s. bc_eval s = case bc_eval1 s of NONE => SOME s | SOME s => bc_eval s``,
  rw[bc_eval_def] >>
  rw[Once OWHILE_THM] >>
  BasicProvers.CASE_TAC >> fs[])

val bc_eval_SOME_RTC_bc_next = store_thm("bc_eval_SOME_RTC_bc_next",
  ``∀s1 s2. bc_eval s1 = SOME s2 ⇒ bc_next^* s1 s2 ∧ ∀s3. ¬bc_next s2 s3``,
  simp[bc_eval_def] >>
  ho_match_mp_tac OWHILE_IND >>
  simp[bc_eval1_thm] >>
  rw[] >> Cases_on`bc_eval1 s1`>>fs[] >>
  metis_tac[bc_eval1_thm,RTC_CASES1])

val RTC_bc_next_bc_eval = store_thm("RTC_bc_next_bc_eval",
  ``∀s1 s2. bc_next^* s1 s2 ⇒ (∀s3. ¬bc_next s2 s3) ⇒ bc_eval s1 = SOME s2``,
  ho_match_mp_tac RTC_INDUCT >>
  rw[] >- (
    simp[bc_eval_def] >>
    simp[Once OWHILE_THM] >>
    rw[] >> fs[bc_eval1_thm] >>
    Cases_on`bc_eval1 s1`>>fs[]) >>
  fs[bc_eval_def] >>
  simp[Once OWHILE_THM] >>
  rw[] >>
  Cases_on`bc_eval1 s1`>>fs[bc_eval1_thm])

val _ = export_theory();
