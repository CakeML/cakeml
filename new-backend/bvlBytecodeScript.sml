open HolKernel boolLib boolSimps bossLib lcsymtacs
open pairTheory listTheory rich_listTheory relationTheory quantHeuristicsLib quantHeuristicsLibAbbrev arithmeticTheory
open miscLib miscTheory bytecodeTheory bytecodeExtraTheory bytecodeEvalTheory bvlTheory
val _ = new_theory"bvlBytecode"

val _ = Datatype`
  bvl_bc_state = <|
    next_label : num;
    out : bc_inst list |>`

val bvl_bc_state_component_equality = theorem"bvl_bc_state_component_equality"

val emit_def = Define`
  emit = FOLDL (λs i. s with <| out := i :: s.out |>)`

val get_label_def = Define`
  get_label s = (s with <| next_label := s.next_label + 1 |>, s.next_label)`

val _ = Datatype`
  bvl_bc_tail = TCNonTail | TCTail num num`

val stackshiftaux_def = Define`
  stackshiftaux (n:num) i j =
    if n = 0 then []
    else (Load i)::(Store j)::(stackshiftaux (n-1) (i+1) (j+1))`

val stackshift_def = Define`
  stackshift j k =
    if k = 0 then []
    else if j = 0 then [Pops (k-1); Pop]
    else if j = 1 then [Pops k]
    else if j ≤ k then (GENLIST (K (Store (k-1))) j)++(stackshift 0 (k-j))
    else (stackshiftaux k (j-k) j)++(stackshift (j-k) k)`

val stackshiftaux_ind = theorem"stackshiftaux_ind"

val stackshiftaux_thm = store_thm("stackshiftaux_thm",
  ``∀n i j bs bc0 bc1 xs ys z0 zs st.
      let code = MAP Stack (stackshiftaux n i j) in
      bs.code = bc0 ++ code ++ bc1 ∧
      bs.pc = next_addr bs.inst_length bc0 ∧
      bs.stack = xs++ys++z0++zs++st ∧
      LENGTH xs = i ∧
      LENGTH ys = n ∧
      LENGTH zs = n ∧
      j = i + n + LENGTH z0
      ⇒
      bc_next^* bs (bs with <|stack := xs++ys++z0++ys++st; pc := next_addr bs.inst_length (bc0++code)|>)``,
  ho_match_mp_tac stackshiftaux_ind >>
  rpt gen_tac >> strip_tac >>
  simp[Once stackshiftaux_def] >>
  Cases_on`n=0`>>simp[LENGTH_NIL]>-(
    rw[] >> simp[Once RTC_CASES1] >> disj1_tac >>
    simp[bc_state_component_equality] ) >>
  rw[] >> fs[] >>
  `bc_fetch bs = SOME (Stack(Load (LENGTH xs)))` by (
    match_mp_tac bc_fetch_next_addr >>
    qexists_tac`bc0` >>
    simp[] ) >>
  simp[Once RTC_CASES1] >> disj2_tac >>
  simp[bc_eval1_thm] >>
  simp[bc_eval1_def,bc_eval_stack_def,bump_pc_def,EL_APPEND1,EL_APPEND2] >>
  Cases_on`zs`>>fs[]>>
  Cases_on`ys`>>fs[]>>
  qmatch_abbrev_tac`bc_next^* bs1 bs2` >>
  `bc_fetch bs1 = SOME (Stack (Store (LENGTH xs + LENGTH z0 + LENGTH t + 1)))` by (
    match_mp_tac bc_fetch_next_addr >>
    qmatch_assum_abbrev_tac`bc_fetch bs = SOME i` >>
    qexists_tac`bc0++[i]` >>
    simp[Abbr`bs1`,SUM_APPEND,FILTER_APPEND,Abbr`i`] ) >>
  simp[Once RTC_CASES1] >> disj2_tac >>
  simp[bc_eval1_thm] >>
  simp[bc_eval1_def,bc_eval_stack_def,bump_pc_def,Abbr`bs1`] >>
  simp[TAKE_APPEND1,TAKE_APPEND2,DROP_APPEND1,DROP_APPEND2] >>
  qmatch_abbrev_tac`bc_next^* bs1 bs2` >>
  qmatch_assum_abbrev_tac`bc_fetch bs = SOME i1` >>
  qmatch_assum_abbrev_tac`bc_fetch bs0 = SOME i2` >>
  first_x_assum(qspecl_then[`bs1`,`bc0++[i1;i2]`]mp_tac) >>
  simp[Abbr`bs1`,Abbr`i2`] >>
  disch_then(qspecl_then[`xs++[h']`,`t'`,`z0++[h']`]mp_tac) >>
  simp[SUM_APPEND,FILTER_APPEND,Abbr`i1`] >>
  disch_then(qspec_then`t`mp_tac) >>
  simp[ADD1] >>
  qmatch_abbrev_tac`bc_next^* bs3' bs2' ⇒ bc_next^* bs3 bs2` >>
  `bs3 = bs3'` by (
    simp[Abbr`bs3`,Abbr`bs3'`,bc_state_component_equality] ) >>
  `bs2 = bs2'` by (
    simp[Abbr`bs2`,Abbr`bs2'`,bc_state_component_equality] >>
    simp[SUM_APPEND,FILTER_APPEND,ADD1] ) >>
  rw[] )

val GENLIST_Store_thm = store_thm("GENLIST_Store_thm",
  ``∀n k bs bc0 bc1 xs ys zs.
    let code = MAP Stack (GENLIST (K (Store k)) n) in
    bs.code = bc0 ++ code ++ bc1 ∧
    bs.pc = next_addr bs.inst_length bc0 ∧
    bs.stack = xs ++ ys ++ zs ∧
    LENGTH xs = n ∧
    LENGTH ys = SUC k ∧
    n ≤ SUC k
    ⇒
    bc_next^* bs (bs with <| stack := TAKE (SUC k - n) ys ++ xs ++ zs; pc := next_addr bs.inst_length (bc0++code) |>)``,
  Induct >- (
    simp[LENGTH_NIL,TAKE_LENGTH_ID_rwt] >>
    rw[Once RTC_CASES1] >> disj1_tac >>
    simp[bc_state_component_equality] ) >>
  simp[GENLIST_CONS] >> rw[] >>
  Q.PAT_ABBREV_TAC`f:num->bc_stack_op = K (Store k)` >>
  `f o SUC = f` by simp[Abbr`f`,FUN_EQ_THM] >> fs[] >>
  `bc_fetch bs = SOME (Stack (Store k))` by (
    match_mp_tac bc_fetch_next_addr >>
    qexists_tac`bc0` >> simp[] ) >>
  simp[Once RTC_CASES1] >> disj2_tac >>
  Cases_on`xs`>>fs[]>>
  simp[bc_eval1_thm,bc_eval1_def,bc_eval_stack_def,bump_pc_def] >>
  simp[TAKE_APPEND1,TAKE_APPEND2,DROP_APPEND2,DROP_APPEND1] >>
  qmatch_abbrev_tac`bc_next^* bs1 bs2` >>
  first_x_assum(qspecl_then[`k`,`bs1`,`bc0++[Stack(Store k)]`]mp_tac) >>
  simp[Abbr`bs1`,SUM_APPEND,FILTER_APPEND] >>
  disch_then(qspecl_then[`t`]mp_tac) >> simp[] >>
  disch_then(mp_tac o CONV_RULE SWAP_FORALL_CONV) >>
  disch_then(qspecl_then[`zs`]mp_tac) >> simp[] >>
  simp[TAKE_APPEND1,TAKE_APPEND2,DROP_APPEND2,DROP_APPEND1] >>
  qmatch_abbrev_tac`bc_next^* bs3' bs2' ⇒ bc_next^* bs3 bs2` >>
  `bs3 = bs3'` by (
    simp[Abbr`bs3`,Abbr`bs3'`,bc_state_component_equality] ) >>
  `bs2 = bs2'` by (
    simp[Abbr`bs2`,Abbr`bs2'`,bc_state_component_equality] >>
    simp[SUM_APPEND,FILTER_APPEND,ADD1] ) >>
  rw[] )

val stackshift_ind = theorem"stackshift_ind"

val stackshift_thm = store_thm("stackshift_thm",
  ``∀j k bs bc0 bc1 xs ys st.
      let code = MAP Stack (stackshift j k) in
      bs.code = bc0 ++ code ++ bc1 ∧
      bs.pc = next_addr bs.inst_length bc0 ∧
      bs.stack = xs++ys++st ∧
      LENGTH xs = j ∧
      LENGTH ys = k
      ⇒
      bc_next^* bs (bs with <|stack := xs++st; pc := next_addr bs.inst_length (bc0++code)|>)``,
  ho_match_mp_tac stackshift_ind >>
  rpt gen_tac >> strip_tac >>
  simp[Once stackshift_def] >>
  rpt gen_tac >>
  Cases_on`k=0`>>simp[] >- (
    rw[LENGTH_NIL] >>
    simp[Once RTC_CASES1] >> disj1_tac >>
    simp[bc_state_component_equality] ) >>
  Cases_on`j=0`>>simp[] >- (
    rw[LENGTH_NIL] >>
    Cases_on`ys`>>fs[] >>
    `bc_fetch bs = SOME (Stack (Pops (LENGTH t)))` by (
      match_mp_tac bc_fetch_next_addr >>
      qexists_tac`bc0` >>
      simp[] ) >>
    simp[Once RTC_CASES1] >> disj2_tac >>
    simp[bc_eval1_thm,bc_eval1_def,bc_eval_stack_def,bump_pc_def,DROP_APPEND2] >>
    qmatch_abbrev_tac`bc_next^* bs1 bs2` >>
    `bc_fetch bs1 = SOME (Stack Pop)` by (
      match_mp_tac bc_fetch_next_addr >>
      CONV_TAC SWAP_EXISTS_CONV >>
      qexists_tac`bc1` >>
      simp[Abbr`bs1`,SUM_APPEND,FILTER_APPEND] ) >>
    simp[Once RTC_CASES1] >> disj2_tac >>
    simp[bc_eval1_thm,bc_eval1_def,bc_eval_stack_def,bump_pc_def,Abbr`bs1`] >>
    simp[Once RTC_CASES1] >> disj1_tac >>
    simp[Abbr`bs2`,bc_state_component_equality,SUM_APPEND,FILTER_APPEND] ) >>
  Cases_on`j=1`>>simp[] >- (
    rw[] >>
    Cases_on`xs`>>fs[LENGTH_NIL] >>
    Cases_on`ys`>>fs[] >>
    qmatch_assum_abbrev_tac`bs.code = bc0 ++ [xi] ++ bc1` >>
    `bc_fetch bs = SOME xi` by (
      match_mp_tac bc_fetch_next_addr >>
      qexists_tac`bc0` >> simp[Abbr`xi`] ) >>
    match_mp_tac RTC_SUBSET >>
    simp[bc_eval1_thm,bc_eval1_def,bc_eval_stack_def,bump_pc_def,Abbr`xi`] >>
    simp[bc_state_component_equality,SUM_APPEND,FILTER_APPEND,DROP_APPEND1,DROP_LENGTH_NIL_rwt] ) >>
  fs[] >>
  Cases_on`j ≤ k` >> fsrw_tac[ARITH_ss][] >- (
    rw[] >>
    qmatch_assum_abbrev_tac`bs.code = bc0 ++ MAP Stack (GENLIST (K(Store k)) n) ++ bc10 ++ bc1` >>
    qspecl_then[`n`,`k`,`bs`,`bc0`,`bc10++bc1`]mp_tac GENLIST_Store_thm >>
    simp[Abbr`bc10`] >>
    disch_then(qspecl_then[`xs`,`ys`]mp_tac) >>
    simp[Abbr`n`,Abbr`k`] >>
    qmatch_abbrev_tac`bc_next^* bs bs1 ⇒ bc_next^* bs bs2` >>
    strip_tac >>
    qsuff_tac`bc_next^* bs1 bs2` >- metis_tac[RTC_TRANSITIVE,transitive_def] >>
    first_x_assum(qspecl_then[`bs1`](mp_tac o CONV_RULE SWAP_FORALL_CONV)) >>
    disch_then(qspecl_then[`bc1`]mp_tac) >> simp[Abbr`bs1`,ADD1,LENGTH_NIL] >>
    disch_then(mp_tac o CONV_RULE SWAP_FORALL_CONV) >>
    disch_then(qspecl_then[`xs++st`]mp_tac) >> simp[] ) >>
  rw[] >>
  qmatch_assum_abbrev_tac`bs.code = bc0 ++ MAP Stack (stackshiftaux n i j) ++ MAP Stack (stackshift i n) ++ bc1` >>
  qunabbrev_tac`i` >> qabbrev_tac`i = j-n` >>
  qspecl_then[`n`,`i`,`j`,`bs`,`bc0`]mp_tac stackshiftaux_thm >>
  simp[] >>
  disch_then(qspecl_then[`TAKE i xs`,`DROP i xs`,`[]`]mp_tac) >> simp[] >>
  simp[Abbr`i`,Abbr`j`,Abbr`n`] >>
  disch_then(qspecl_then[`ys`]mp_tac) >> simp[] >>
  qmatch_abbrev_tac`bc_next^* bs bs1 ⇒ bc_next^* bs bs2` >>
  strip_tac >>
  qsuff_tac`bc_next^* bs1 bs2` >- metis_tac[RTC_TRANSITIVE,transitive_def] >>
  first_x_assum(qspecl_then[`bs1`](mp_tac o CONV_RULE SWAP_FORALL_CONV)) >>
  disch_then(qspecl_then[`bc1`]mp_tac) >> simp[Abbr`bs1`] >>
  disch_then(qspecl_then[`TAKE (LENGTH xs - LENGTH ys) xs`,`DROP (LENGTH xs - LENGTH ys) xs`]mp_tac) >> simp[])

val pushret_def = Define`
  (pushret TCNonTail s = s) ∧
  (pushret (TCTail j k) s =
    if j = 0 then
      emit s [Stack (Pops k); Return]
    else
      emit s [
      (* v::|k|++ret++|j| *)
        Stack (Pops k);
      (* v::ret::|j| *)
        Stack (Load 1);
      (* ret::v::ret::|j| *)
        Stack (Store (j+1));
      (* v::ret::|j-1|::ret *)
        Stack (Pops j);
      (* v::ret *)
        Return])`

val bvl_bc_def = C (tDefine "bvl_bc")
  (WF_REL_TAC`measure (bvl_exp1_size o SND o SND o SND o SND)`)`
  (bvl_bc cenv t sz s [] = s) ∧
  (bvl_bc cenv t sz s (e1::e2::es) =
    let s = bvl_bc cenv TCNonTail sz s [e1] in
    bvl_bc cenv t (sz+1) s (e2::es)) ∧
  (bvl_bc cenv t sz s [Var n] =
     if n < LENGTH cenv then
       pushret t (emit s [Stack(Load(sz-(EL n cenv)))])
     else s) ∧
  (bvl_bc cenv t sz s [If e1 e2 e3] =
    let (s,l1) = get_label s in
    let (s,l2) = get_label s in
    let s = bvl_bc cenv TCNonTail sz s [e1] in
    let s = emit s [JumpIf (Lab l1)] in
    let s = bvl_bc cenv t sz s [e3] in
    let s = emit s [Jump (Lab l2);Label l1] in
    let s = bvl_bc cenv t sz s [e2] in
            emit s [Label l2]) ∧
  (bvl_bc cenv t sz s [Let es e] =
    let s = bvl_bc cenv TCNonTail sz s es in
    let n = LENGTH es in
    let s =
      bvl_bc ((GENLIST (λi. sz+i+1) n)++cenv)
             (case t of TCTail j k => TCTail j (k+n) | _ => t)
             (sz+n) s [e] in
    emit s (case t of TCNonTail => [Stack(Pops n)] | _ => [])) ∧
  (bvl_bc cenv t sz s [Raise e] =
    let s = bvl_bc cenv TCNonTail sz s [e] in
            emit s [PopExc; Return]) ∧
  (bvl_bc cenv t sz s [Handle e1 e2] =
    let (s,l0) = get_label s in
    let (s,l1) = get_label s in
    let s = emit s [PushPtr (Lab l0); PushExc] in
    let s = bvl_bc cenv TCNonTail (sz+2) s [e1] in
    let s = pushret t (emit s [PopExc; Stack (Pops 1)]) in
    let s = emit s [Jump (Lab l1); Label l0] in
    let s = bvl_bc ((sz+1)::cenv) t (sz+1) s [e2] in
            emit s [Label l1]) ∧
  (bvl_bc cenv t sz s [Tick e] =
    let s = emit s [Tick] in
            bvl_bc cenv t sz s [e]) ∧
  (bvl_bc cenv t sz s [Call dest es] =
    let s = bvl_bc cenv TCNonTail sz s es in
    let s = emit s [Tick] in
    let n = LENGTH es in
    case t of
    | TCNonTail =>
        (case dest of
           (* ptr::args *)
         | NONE => emit s [Stack(Load 0); CallPtr]
           (* args *)
         | SOME p => emit s [Stack(PushInt 0); Call (Lab p)])
    | TCTail j k =>
      (* args++|k|++ret::|j| *)
        (case dest of
         | NONE =>
           (* ptr::args++|k|++ret::|j| *)
             let s = emit s [Stack(Load 0);Stack(Load (1+1+n+k));Stack(Store 1);Stack(PushInt 0)] in
           (*      ptr::ptr::args++|k|++ret::|j| *)
           (* ret::ptr::ptr::args++|k|++ret::|j| *)
           (*      ptr::ret::args++|k|++ret::|j| *)
           (*  ig::ptr::ret::args++|k|++ret::|j| *)
             let s = emit s (MAP Stack (stackshift (1+1+1+n) (k+1+j))) in
           (* ig::ptr::ret::args *)
                     emit s [Return]
         | SOME p =>
           (* args++|k|++ret::|j| *)
             let s = emit s [Stack(Load(n+k));Stack(PushInt 0)] in
           (*     ret::args++|k|++ret::|j| *)
           (* ig::ret::args++|k|++ret::|j| *)
             let s = emit s (MAP Stack (stackshift (1+1+n) (k+1+j))) in
           (* ig::ret::args *)
                     emit s [Jump (Lab p)])) ∧
  (bvl_bc cenv t sz s [Op op es] =
    let s = bvl_bc cenv TCNonTail sz s es in
    let s = emit s (case op of
    | Global n => [Gread n]
    | AllocGlobal => [Galloc 1]
    | SetGlobal n => [Gupdate n]
    | Cons n => [Stack(PushInt (&(LENGTH es))); Stack (Cons n)]
    | El n => [Stack (PushInt (&n)); Stack El]
    | El2 => [Stack El]
    | LengthBlock => [Stack LengthBlock]
    | Length => [Length]
    | LengthByte => [LengthByte]
    | RefByte => [RefByte]
    | Ref2 => [Ref]
    | DerefByte => [DerefByte]
    | UpdateByte => [UpdateByte]
    | FromList n => [] (* TODO *)
    | ToList => [] (* TODO *)
    | Const i => [Stack (PushInt i)]
    | TagEq n => [Stack (TagEq n)]
    | IsBlock => [Stack IsBlock]
    | Equal => [Stack Equal]
    | Ref => [] (* TODO *)
    | Deref => [Deref]
    | Update => [Update]
    | Label n => [PushPtr (Lab n)]
    | Print => [Print]
    | PrintC c => [PrintC c]
    | Add => [Stack Add]
    | Sub => [Stack Sub]
    | Mult => [Stack Mult]
    | Div => [Stack Div]
    | Mod => [Stack Mod]
    | Less => [Stack Less])
    in pushret t s)`

val bvl_bc_ind = theorem"bvl_bc_ind"

(*
stack = a,b,x5,x4,x3,c,x7,x6,d
sz = 9
env = [x3,x4,x5,x6,x7]
cenv = [5,6,7,2,3]

add another junk:
stack = z,a,b,x5,x4,x3,c,x7,x6,d
sz = 10
env = [x3,x4,x5,x6,x7]
cenv = [5,6,7,2,3]

add another let:
stack = x2,x1,x0,z,a,b,x5,x4,x3,c,x7,x6,d
sz = 13
env = [x0,x1,x2,x3,x4,x5,x6,x7]
cenv = [11,12,13,5,6,7,2,3]
*)

val pushret_append_out = store_thm("pushret_append_out",
  ``∀t s. ((pushret t s).next_label = s.next_label) ∧
          ∃bc. ((pushret t s).out = bc ++ s.out) ∧
               (FILTER is_Label bc = [])``,
  Cases >> rw[pushret_def,emit_def])

val FOLDL_emit_append_out = prove(
  ``∀ls s. emit s ls = s with out := REVERSE ls ++ s.out``,
  Induct >> simp[bvl_bc_state_component_equality,emit_def] >> fs[emit_def])
  |> SIMP_RULE (srw_ss())[]

val bvl_bc_append_out = store_thm("bvl_bc_append_out",
  ``(∀cenv t sz s e.
       ∃bc. ((bvl_bc cenv t sz s e).out = bc ++ s.out) ∧
            ALL_DISTINCT (FILTER is_Label bc) ∧
            s.next_label ≤ (bvl_bc cenv t sz s e).next_label ∧
            EVERY (between s.next_label (bvl_bc cenv t sz s e).next_label)
              (MAP dest_Label (FILTER is_Label bc)))``,
  ho_match_mp_tac bvl_bc_ind >>
  strip_tac >- simp[bvl_bc_def] >>
  strip_tac >- (
    simp[bvl_bc_def] >> rw[] >>
    fs[FILTER_APPEND,ALL_DISTINCT_APPEND,EVERY_MAP,MEM_FILTER,EVERY_FILTER,
       is_Label_rwt,PULL_EXISTS] >>
    fs[EVERY_MEM,between_def] >> rw[] >> res_tac >> fsrw_tac[ARITH_ss][] >>
    strip_tac >> res_tac >> fsrw_tac[ARITH_ss][] ) >>
  strip_tac >- (
    simp[bvl_bc_def] >> rw[] >>
    SIMPLE_QUANT_ABBREV_TAC[select_fun_constant``pushret``2"s0"] >>
    qspecl_then[`t`,`s0`]mp_tac(pushret_append_out) >> rw[] >> fs[Abbr`s0`] >>
    fs[emit_def,FILTER_APPEND] ) >>
  strip_tac >- (
    simp[bvl_bc_def,get_label_def] >> rw[] >>
    fs[FILTER_APPEND,ALL_DISTINCT_APPEND,EVERY_MAP,MEM_FILTER,EVERY_FILTER,
       emit_def,is_Label_rwt,PULL_EXISTS] >>
    fs[EVERY_MEM,between_def] >> rw[] >> res_tac >> fsrw_tac[ARITH_ss][] >>
    spose_not_then strip_assume_tac >> rw[] >> res_tac >> fsrw_tac[ARITH_ss][]) >>
  strip_tac >- (
    simp[bvl_bc_def,emit_def] >> rw[] >>
    Cases_on`t`>>fs[]>>
    fs[FILTER_APPEND,ALL_DISTINCT_APPEND,EVERY_MAP,MEM_FILTER,EVERY_FILTER,
       emit_def,is_Label_rwt,PULL_EXISTS] >>
    fs[EVERY_MEM,between_def] >> rw[] >> res_tac >> fsrw_tac[ARITH_ss][] >>
    spose_not_then strip_assume_tac >> rw[] >> res_tac >> fsrw_tac[ARITH_ss][]) >>
  strip_tac >- (
    simp[bvl_bc_def,emit_def] >> rw[] >>
    fs[FILTER_APPEND,ALL_DISTINCT_APPEND,EVERY_MAP,MEM_FILTER,EVERY_FILTER,
       emit_def,is_Label_rwt,PULL_EXISTS]) >>
  strip_tac >- (
    simp[bvl_bc_def,get_label_def,emit_def] >> rw[] >>
    SIMPLE_QUANT_ABBREV_TAC[select_fun_constant``pushret``2"s0"] >>
    qspecl_then[`t`,`s0`]mp_tac(pushret_append_out) >> rw[] >> fs[Abbr`s0`] >>
    fs[FILTER_APPEND,ALL_DISTINCT_APPEND,EVERY_MAP,MEM_FILTER,EVERY_FILTER,
       is_Label_rwt,PULL_EXISTS] >>
    fs[EVERY_MEM,between_def] >> rw[] >> res_tac >> fsrw_tac[ARITH_ss][] >>
    spose_not_then strip_assume_tac >> rw[] >> res_tac >> fsrw_tac[ARITH_ss][] >>
    fs[FILTER_EQ_NIL,EVERY_MEM,is_Label_rwt] >> res_tac >> fs[]) >>
  strip_tac >- (
    simp[bvl_bc_def,emit_def] >> rw[] >>
    fs[FILTER_APPEND,ALL_DISTINCT_APPEND,EVERY_MAP,MEM_FILTER,EVERY_FILTER,
       emit_def,is_Label_rwt,PULL_EXISTS]) >>
  strip_tac >- (
    simp[bvl_bc_def,emit_def,FOLDL_emit_append_out] >> rw[] >>
    Cases_on`t`>>Cases_on`dest`>>fs[]>>
    fs[FILTER_APPEND,ALL_DISTINCT_APPEND,EVERY_MAP,MEM_FILTER,EVERY_FILTER,
       FILTER_REVERSE,EVERY_REVERSE,ALL_DISTINCT_REVERSE,is_Label_rwt,PULL_EXISTS] >>
    fs[MEM_MAP] >>
    qmatch_abbrev_tac`ALL_DISTINCT ls` >>
    qsuff_tac`ls=[]`>>rw[Abbr`ls`]>>
    rw[FILTER_EQ_NIL,EVERY_MAP]) >>
  strip_tac >- (
    simp[bvl_bc_def] >> rw[] >>
    Cases_on`op`>>fs[emit_def] >>
    SIMPLE_QUANT_ABBREV_TAC[select_fun_constant``pushret``2"s0"] >>
    qspecl_then[`t`,`s0`]mp_tac(pushret_append_out) >> rw[] >> fs[Abbr`s0`] >>
    fs[FILTER_APPEND,ALL_DISTINCT_APPEND,EVERY_MAP,MEM_FILTER,EVERY_FILTER,
       is_Label_rwt,PULL_EXISTS] >>
    fs[EVERY_MEM,between_def] >> rw[] >> res_tac >> fsrw_tac[ARITH_ss][] >>
    spose_not_then strip_assume_tac >> rw[] >> res_tac >> fsrw_tac[ARITH_ss][] >>
    fs[FILTER_EQ_NIL,EVERY_MEM,is_Label_rwt] >> res_tac >> fs[]))

val good_code_env_def = Define`
  good_code_env cmap ls ⇔
    ∀ptr exp arity. (lookup ptr cmap = SOME (arity,exp)) ⇒
      ∃cs l0 cc l1.
        ((bvl_bc (GENLIST (λn. arity-n) arity) (TCTail arity 1) (arity+2) cs [exp]).out = cc ++ cs.out) ∧
        EVERY (combin$C $< cs.next_label o dest_Label) (FILTER is_Label l0) ∧ ptr < cs.next_label ∧
        (ls = l0 ++ [Label ptr] ++ REVERSE cc ++ l1)`

val good_env_def = Define`
  good_env sz st env cenv ⇔
      sz ≤ LENGTH st ∧
      LIST_REL (λv n. n ≤ sz ∧ (sz-n) < LENGTH st ∧ (EL (sz-n) st = v)) env cenv`

val good_env_cons = store_thm("good_env_cons",
  ``good_env sz st env cenv ⇒
    good_env (sz+1) (h::st) env cenv``,
  rw[good_env_def,LIST_REL_EL_EQN] >> rfs[] >> res_tac >>
  simp[EL_CONS,PRE_SUB1])

val pushret_correct = store_thm("pushret_correct",
  ``∀t s bs prc igc code bc0 bc1 bs1 v ret rst.
      ((pushret t s).out = REVERSE prc ++ s.out) ∧
      (s.out = REVERSE code ++ igc) ∧
      (bs.code = bc0 ++ code ++ prc ++ bc1) ∧
      (bs.pc = next_addr bs.inst_length bc0) ∧
      (bc_next^* bs bs1) ∧
      (bs1.stack = v::bs.stack) ∧
      (bs1.pc = next_addr bs.inst_length (bc0++code)) ∧
      (case t of TCTail j k =>
         ∃ig args. bs.stack = ig ++ [CodePtr ret] ++ args ++ rst ∧
                   LENGTH ig = k ∧ LENGTH args = j
       | TCNonTail => T)
      ⇒
      ∃bs2.
        bc_next^* bs bs2 ∧
        case t of TCNonTail => bs2 = bs1
        | TCTail j k =>
            bs2 = bs1 with <| stack := v::rst; pc := ret |>``,
  Cases >> rw[pushret_def,emit_def] >>
  fs[Once (GSYM SWAP_REVERSE)] >> rw[] >>
  simp[Once RTC_CASES_RTC_TWICE] >>
  first_assum(match_exists_tac o concl) >>
  simp[] >>
  qmatch_assum_abbrev_tac`bs.code = bc0 ++ code ++ ls ++ bc1` >>
  imp_res_tac RTC_bc_next_preserves >>
  qmatch_abbrev_tac`bc_next^* bs0 bs2` >>
  srw_tac[DNF_ss][Once RTC_CASES1] >> disj2_tac >>
  `bc_fetch bs0 = SOME(EL 0 ls)` by (
    match_mp_tac bc_fetch_next_addr >>
    qexists_tac`bc0++code++(TAKE 0 ls)` >>
    simp[Abbr`bs0`,Abbr`ls`] ) >>
  simp[bc_eval1_thm,bc_eval1_def,Abbr`ls`,bc_eval_stack_def,bump_pc_def,Abbr`bs0`] >>
  simp[DROP_APPEND1,DROP_LENGTH_NIL] >>
  pop_assum kall_tac >>
  qmatch_assum_abbrev_tac`bs.code = bc0 ++ code ++ ls ++ bc1` >>
  qmatch_abbrev_tac`bc_next^* bs0 bs2` >>
  srw_tac[DNF_ss][Once RTC_CASES1] >> disj2_tac >>
  `bc_fetch bs0 = SOME(EL 1 ls)` by (
    match_mp_tac bc_fetch_next_addr >>
    qexists_tac`bc0++code++(TAKE 1 ls)` >>
    simp[Abbr`bs0`,Abbr`ls`] >>
    simp[FILTER_APPEND,SUM_APPEND]) >>
  simp[bc_eval1_thm,bc_eval1_def,Abbr`ls`,bc_eval_stack_def,bump_pc_def,Abbr`bs0`] >>
  pop_assum kall_tac >>
  qmatch_assum_abbrev_tac`bs.code = bc0 ++ code ++ ls ++ bc1` >>
  qmatch_abbrev_tac`bc_next^* bs0 bs2` >>
  srw_tac[DNF_ss][Once RTC_CASES1] >- (
    disj1_tac >> unabbrev_all_tac >> fs[LENGTH_NIL] ) >>
  disj2_tac >>
  `bc_fetch bs0 = SOME(EL 2 ls)` by (
    match_mp_tac bc_fetch_next_addr >>
    qexists_tac`bc0++code++(TAKE 2 ls)` >>
    simp[Abbr`bs0`,Abbr`ls`] >>
    simp[FILTER_APPEND,SUM_APPEND]) >>
  simp[bc_eval1_thm,bc_eval1_def,Abbr`ls`,bc_eval_stack_def,bump_pc_def,Abbr`bs0`] >>
  pop_assum kall_tac >>
  qmatch_assum_abbrev_tac`bs.code = bc0 ++ code ++ ls ++ bc1` >>
  qmatch_abbrev_tac`bc_next^* bs0 bs2` >>
  srw_tac[DNF_ss][Once RTC_CASES1] >> disj2_tac >>
  `bc_fetch bs0 = SOME(EL 3 ls)` by (
    match_mp_tac bc_fetch_next_addr >>
    qexists_tac`bc0++code++(TAKE 3 ls)` >>
    simp[Abbr`bs0`,Abbr`ls`] >>
    simp[FILTER_APPEND,SUM_APPEND]) >>
  simp[bc_eval1_thm,bc_eval1_def,Abbr`ls`,bc_eval_stack_def,bump_pc_def,Abbr`bs0`] >>
  simp[TAKE_APPEND1,DROP_APPEND1,DROP_LENGTH_NIL_rwt] >>
  pop_assum kall_tac >>
  qmatch_assum_abbrev_tac`bs.code = bc0 ++ code ++ ls ++ bc1` >>
  qmatch_abbrev_tac`bc_next^* bs0 bs2` >>
  srw_tac[DNF_ss][Once RTC_CASES1] >> disj2_tac >>
  `bc_fetch bs0 = SOME(EL 4 ls)` by (
    match_mp_tac bc_fetch_next_addr >>
    qexists_tac`bc0++code++(TAKE 4 ls)` >>
    simp[Abbr`bs0`,Abbr`ls`] >>
    simp[FILTER_APPEND,SUM_APPEND]) >>
  simp[bc_eval1_thm,bc_eval1_def,Abbr`ls`,bc_eval_stack_def,bump_pc_def,Abbr`bs0`])

val bvl_bc_correct = store_thm("bvl_bc_correct",
  ``∀exps env s res s' bs1 bc0 code bc1 cenv t sz cs stw ret sp hdl rst.
      (bEval (exps,env,s) = (res,s')) ∧ res ≠ Error ∧
      (good_env sz bs1.stack env cenv) ∧
      (good_code_env s.code bs1.code) ∧
      ((bvl_bc cenv t sz cs exps).out = REVERSE code ++ cs.out) ∧
      (bs1.code = bc0 ++ code ++ bc1) ∧
      (bs1.pc = next_addr bs1.inst_length bc0) ∧
      (bs1.output = s.output) ∧ (bs1.clock = SOME s.clock) ∧
      (bs1.globals = s.globals) ∧ (bs1.refs = s.refs) ∧
      (case t of
       | TCTail j k =>
           (LENGTH exps = 1) ∧
           (∃ig args. (bs1.stack = ig++(CodePtr ret::args)++rst) ∧ (LENGTH ig = k) ∧ (LENGTH args = j))
       | TCNonTail => T) ∧
      (case res of Exception _ =>
        ∃ig. (bs1.stack = ig ++ [StackPtr sp; CodePtr hdl] ++ rst) ∧
             (LENGTH rst + 1 = bs1.handler)
       | _ => T)
      ⇒
      ∃bs2.
        bc_next^* bs1 bs2 ∧
        case res of
        | TimeOut =>
            (bc_fetch bs2 = SOME Tick) ∧
            (bs2.output = s'.output) ∧ (bs2.clock = SOME 0) ∧
            (bs2.globals = s'.globals) ∧ (bs2.refs = s'.refs)
        | Exception v =>
            (bs2 = bs1 with <|stack := v::rst; pc := hdl; handler := sp;
                              output := s'.output; clock := SOME s'.clock;
                              globals := s'.globals; refs := s'.refs|>)
        | Result vs =>
          (case t of
            | TCNonTail =>
              (bs2 = bs1 with <|
                stack := (REVERSE vs)++bs1.stack;
                pc := next_addr bs2.inst_length (bc0++code);
                output := s'.output; clock := SOME s'.clock;
                globals := s'.globals; refs := s'.refs|>)
            | TCTail _ _ =>
              (bs2 = bs1 with <|
                stack := (HD vs)::rst; pc := ret;
                output := s'.output; clock := SOME s'.clock;
                globals := s'.globals; refs := s'.refs|>))``,
  recInduct bEval_ind >>
  strip_tac >- (
    simp[bEval_def,bvl_bc_def] >>
    simp[Once SWAP_REVERSE] >>
    Cases_on`t`>>rw[] >>
    qexists_tac`bs1`>>rw[bc_state_component_equality] ) >>
  strip_tac >- (
    simp[bEval_def,bvl_bc_def] >>
    rw[] >> Cases_on`t`>>fs[] >>
    `∃res0 s0. bEval ([x],env,s) = (res0,s0)` by metis_tac[pair_CASES] >>
    `∃res1 s1. bEval (y::xs,env,s0) = (res1,s1)` by metis_tac[pair_CASES] >>
    qspecl_then[`cenv`,`TCNonTail`,`sz`,`cs`,`[x]`]strip_assume_tac bvl_bc_append_out >>
    qspecl_then[`cenv`,`TCNonTail`,`sz+1`,`bvl_bc cenv TCNonTail sz cs [x]`,`y::xs`]strip_assume_tac bvl_bc_append_out >>
    Cases_on`res0`>>fs[] >- (
      first_x_assum(qspecl_then[`bs1`,`bc0`,`REVERSE bc`,`REVERSE bc'++bc1`,`cenv`,`TCNonTail`,`sz`,`cs`]mp_tac) >>
      simp[] >> fs[Once SWAP_REVERSE] >> strip_tac >>
      first_x_assum(qspecl_then[`bs2`,`bc0++REVERSE bc`,`REVERSE bc'`,`bc1`,`cenv`,`TCNonTail`,`sz+1`
                               ,`bvl_bc cenv TCNonTail sz cs [x]`]mp_tac) >>
      imp_res_tac bEval_IMP_LENGTH >>
      Cases_on`a`>>fs[LENGTH_NIL] >>
      imp_res_tac bEval_code >> simp[] >>
      Cases_on`res1`>>fs[] >- (
        rpt BasicProvers.VAR_EQ_TAC >>
        discharge_hyps >- (
          qpat_assum`bs2 = X`SUBST1_TAC >>
          imp_res_tac RTC_bc_next_preserves >> simp[] >>
          match_mp_tac good_env_cons >> rw[] ) >>
        strip_tac >> simp[] >>
        qexists_tac`bs2'` >>
        conj_tac >- metis_tac[RTC_TRANSITIVE,transitive_def] >>
        first_x_assum(CHANGED_TAC o SUBST1_TAC) >>
        simp[bc_state_component_equality] >>
        first_x_assum(CHANGED_TAC o SUBST1_TAC) >>
        imp_res_tac RTC_bc_next_preserves >>
        simp[bc_state_component_equality] ) >>
      rpt BasicProvers.VAR_EQ_TAC >> fs[] >- (
        disch_then(qspecl_then[`sp`,`hdl`,`rst`]mp_tac) >>
        discharge_hyps >- (
          qpat_assum`bs2 = X`SUBST1_TAC >>
          imp_res_tac RTC_bc_next_preserves >> simp[] >>
          match_mp_tac good_env_cons >> fs[] ) >>
        strip_tac >>
        match_mp_tac(SIMP_RULE std_ss [transitive_def] RTC_TRANSITIVE) >>
        first_assum(match_exists_tac o concl) >> simp[] >>
        qmatch_abbrev_tac`bc_next^* bs2 bs3` >>
        qmatch_assum_abbrev_tac`bc_next^* bs2 bs3'` >>
        `bs3 = bs3'` by (
          unabbrev_all_tac >> simp[bc_state_component_equality] >>
          imp_res_tac RTC_bc_next_preserves >> simp[] ) >>
        rw[] ) >>
      discharge_hyps >- (
        qpat_assum`bs2 = X`SUBST1_TAC >>
        imp_res_tac RTC_bc_next_preserves >> simp[] >>
        match_mp_tac good_env_cons >> fs[] ) >>
      strip_tac >>
      qexists_tac`bs2'` >> simp[] >>
      metis_tac[transitive_def,RTC_TRANSITIVE] ) >>
    rpt BasicProvers.VAR_EQ_TAC >> fs[] >>
    first_x_assum(qspecl_then[`bs1`,`bc0`,`REVERSE bc`,`REVERSE bc'++bc1`,`cenv`,`TCNonTail`,`sz`,`cs`]mp_tac) >>
    simp[] >> fs[Once SWAP_REVERSE]) >>
  strip_tac >- (
    simp[bEval_def,bvl_bc_def] >>
    reverse(rw[]) >> fs[] >- (
      fs[good_env_def,LIST_REL_EL_EQN] ) >>
    qmatch_assum_abbrev_tac`(pushret t s0).out = X` >>
    qspecl_then[`t`,`s0`]mp_tac pushret_append_out >>
    simp[Abbr`s0`,Abbr`X`,emit_def] >>
    Q.PAT_ABBREV_TAC`i = Stack X` >> rw[] >>
    fs[Once SWAP_REVERSE_SYM] >>
    `bc_fetch bs1 = SOME i` by (
      match_mp_tac bc_fetch_next_addr >>
      simp[] >>
      qexists_tac`bc0`>>simp[Abbr`i`] ) >>
    mp_tac(Q.REFL `bc_eval1 bs1`) >>
    CONV_TAC(LAND_CONV(RAND_CONV(SIMP_CONV(srw_ss())[bc_eval1_def]))) >>
    simp[Abbr`i`,bc_eval_stack_def,bump_pc_def] >>
    fs[good_env_def,LIST_REL_EL_EQN] >>
    first_x_assum(qspec_then`n`mp_tac) >> simp[] >> strip_tac >>
    simp[GSYM bc_eval1_thm] >> strip_tac >>
    qmatch_assum_abbrev_tac`(pushret t s0).out = X` >>
    qspecl_then[`t`,`s0`,`bs1`]mp_tac pushret_correct >>
    simp[Abbr`s0`,Abbr`X`,emit_def,Once SWAP_REVERSE] >>
    disch_then(qspec_then`cs.out`mp_tac) >> simp[Once SWAP_REVERSE] >>
    disch_then(qspec_then`bc0`mp_tac) >> simp[] >>
    first_x_assum(strip_assume_tac o MATCH_MP RTC_SUBSET) >>
    simp[GSYM AND_IMP_INTRO] >>
    disch_then(fn th => first_x_assum (mp_tac o MATCH_MP th)) >>
    simp[FILTER_APPEND,SUM_APPEND] >>
    disch_then(fn th => first_x_assum (strip_assume_tac o MATCH_MP th)) >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    Cases_on`t`>>fs[bc_state_component_equality,pushret_def,emit_def] >>
    simp[FILTER_APPEND,SUM_APPEND,FILTER_REVERSE,SUM_REVERSE,MAP_REVERSE,ADD1] >>
    rw[] ) >>
  strip_tac >- cheat >> (* If *)
  strip_tac >- (
    simp[bEval_def,bvl_bc_def] >> rw[] >>
    `∃res0 s0. bEval (xs,env,s) = (res0,s0)` by metis_tac[pair_CASES] >>
    qspecl_then[`cenv`,`TCNonTail`,`sz`,`cs`,`xs`]strip_assume_tac bvl_bc_append_out >>
    qmatch_assum_abbrev_tac`(emit (bvl_bc cenv1 t1 sz1 s1 [x2]) l1).out = REVERSE code ++ cs.out` >>
    qspecl_then[`cenv1`,`t1`,`sz1`,`s1`,`[x2]`]strip_assume_tac bvl_bc_append_out >>
    fs[FOLDL_emit_append_out] >>
    fs[Once (GSYM SWAP_REVERSE)] >>
    imp_res_tac bEval_code >>
    Cases_on`res0`>>fs[] >- (
      first_x_assum(qspecl_then[`bs1`,`bc0`,`REVERSE bc`,`REVERSE bc' ++ l1 ++ bc1`,`cenv`,`TCNonTail`,`sz`,`cs`]mp_tac) >>
      simp[] >> strip_tac >>
      imp_res_tac RTC_bc_next_preserves >>
      imp_res_tac bEval_IMP_LENGTH >>
      first_x_assum(qspecl_then[`bs2`,`bc0++REVERSE bc`,`REVERSE bc'`,`l1++bc1`,`cenv1`,`t1`,`sz1`,`s1`]mp_tac) >>
      qpat_assum`bs2 = X`(fn th => SUBST1_TAC th >> assume_tac th) >> simp[] >>
      disch_then(qspecl_then[`ret`,`sp`,`hdl`,`rst`]mp_tac) >>
      discharge_hyps >- (
        conj_tac >- (
          fs[good_env_def,LIST_REL_EL_EQN,Abbr`cenv1`,Abbr`sz1`] >> simp[] >>
          gen_tac >> strip_tac >>
          Cases_on`n < LENGTH a` >- (
            simp[EL_APPEND1,EL_REVERSE,PRE_SUB1] ) >>
          first_x_assum(qspec_then`n-LENGTH a`mp_tac) >>
          simp[EL_APPEND2] ) >>
        conj_tac >- (
          qunabbrev_tac`t1` >>
          Cases_on`t`>>fs[] >>
          qexists_tac`REVERSE a ++ ig`>>simp[] ) >>
        Cases_on`res`>>fs[] ) >>
      strip_tac >>
      Cases_on`res`>>fs[] >- (
        Cases_on`t`>>fs[Abbr`t1`] >- (
          mp_tac(Q.REFL `bc_eval1 bs2'`) >>
          `bc_fetch bs2' = SOME (Stack(Pops (LENGTH a)))` by (
            match_mp_tac bc_fetch_next_addr >>
            pop_assum SUBST1_TAC >> simp[] >>
            imp_res_tac RTC_bc_next_preserves >> simp[] >>
            CONV_TAC(SWAP_EXISTS_CONV) >>
            qexists_tac`bc1`>>simp[] ) >>
          CONV_TAC(LAND_CONV(RAND_CONV(SIMP_CONV(srw_ss())[bc_eval1_def]))) >>
          simp[bump_pc_def] >>
          imp_res_tac bEval_IMP_LENGTH >>
          Cases_on`a'`>>fs[LENGTH_NIL] >>
          qpat_assum`bs2' = X`(fn th => SUBST1_TAC th >> assume_tac th) >>
          simp[bc_eval_stack_def,DROP_APPEND1,DROP_LENGTH_NIL_rwt] >>
          simp[GSYM bc_eval1_thm] >> disch_then(strip_assume_tac o MATCH_MP RTC_SUBSET) >>
          srw_tac[DNF_ss][Once RTC_CASES_RTC_TWICE] >>
          first_assum(match_exists_tac o concl) >> simp[] >>
          qpat_assum`bs2 = X`(fn th => SUBST1_TAC th >> assume_tac th) >>
          imp_res_tac RTC_bc_next_preserves >> fs[] >>
          srw_tac[DNF_ss][Once RTC_CASES_RTC_TWICE] >>
          first_assum(match_exists_tac o concl) >> simp[] >>
          first_assum(match_exists_tac o concl) >> simp[] >>
          simp[bc_state_component_equality,FILTER_APPEND,SUM_APPEND,FILTER_REVERSE,SUM_REVERSE,Abbr`l1`] ) >>
        imp_res_tac bEval_IMP_LENGTH >>
        Cases_on`a'`>>fs[LENGTH_NIL] >>
        srw_tac[DNF_ss][Once RTC_CASES_RTC_TWICE] >>
        first_assum(match_exists_tac o concl) >> simp[] >>
        qpat_assum`bs2 = X`(fn th => SUBST1_TAC th >> assume_tac th) >>
        imp_res_tac RTC_bc_next_preserves >> fs[] >>
        rfs[] ) >>
      imp_res_tac RTC_bc_next_preserves >> fs[] >>
      rpt BasicProvers.VAR_EQ_TAC >>
      srw_tac[DNF_ss][Once RTC_CASES_RTC_TWICE] >>
      first_assum(match_exists_tac o concl) >> simp[] >>
      rfs[] >>
      first_assum(match_exists_tac o concl) >> simp[]) >>
    rpt BasicProvers.VAR_EQ_TAC >> fs[] >>
    first_x_assum match_mp_tac >> simp[] >>
    qexists_tac`bc0`>>simp[] >>
    qexists_tac`REVERSE bc` >> simp[] >>
    map_every qexists_tac[`cenv`,`TCNonTail`,`sz`,`cs`] >> simp[] >>
    fs[] ) >>
  strip_tac >- (
    simp[bEval_def,bvl_bc_def] >> rw[] >>
    `∃res0 s0. bEval ([x1],env,s) = (res0,s0)` by metis_tac[pair_CASES] >>
    qspecl_then[`cenv`,`TCNonTail`,`sz`,`cs`,`[x1]`]strip_assume_tac bvl_bc_append_out >>
    fs[FOLDL_emit_append_out] >>
    fs[Once (GSYM SWAP_REVERSE)] >>
    imp_res_tac bEval_code >>
    first_x_assum(qspecl_then[`bs1`,`bc0`,`REVERSE bc`,`[PopExc; Return] ++ bc1`,`cenv`,`TCNonTail`,`sz`,`cs`]mp_tac) >>
    simp[] >>
    Cases_on`res0`>>fs[]>>rpt BasicProvers.VAR_EQ_TAC >> fs[] >>
    imp_res_tac bEval_IMP_LENGTH >>
    Cases_on`a`>>fs[LENGTH_NIL] >>
    strip_tac >>
    simp[Once RTC_CASES_RTC_TWICE] >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    imp_res_tac RTC_bc_next_preserves >>
    srw_tac[DNF_ss][Once RTC_CASES1] >> disj2_tac >>
    `bc_fetch bs2 = SOME PopExc` by (
      match_mp_tac bc_fetch_next_addr >> simp[] >>
      qexists_tac`bc0++REVERSE bc`>>simp[] >>
      qpat_assum`bs2 = X`SUBST1_TAC >> simp[] ) >>
    qpat_assum`X = bs1.handler`(assume_tac o SYM) >>
    simp[bc_eval1_thm,bc_eval1_def,bump_pc_def] >>
    qpat_assum`bs2 = X`(fn th => SUBST1_TAC th >> assume_tac th) >>
    simp[EL_REVERSE,EL_APPEND1,EL_APPEND2,PRE_SUB1,TAKE_REVERSE,
         LASTN_APPEND1,LASTN_APPEND2,LASTN_CONS,LASTN_1] >>
    qmatch_abbrev_tac`bc_next^* bs3 bs4` >>
    `bc_fetch bs3 = SOME Return` by (
      match_mp_tac bc_fetch_next_addr >>
      simp[Abbr`bs3`] >>
      qexists_tac`bc0 ++ REVERSE bc ++ [PopExc]` >>
      simp[SUM_APPEND,FILTER_APPEND] ) >>
    match_mp_tac RTC_SUBSET >>
    simp[bc_eval1_thm,bc_eval1_def] >>
    simp[Abbr`bs3`] ) >>
  strip_tac >- (
    simp[bEval_def,bvl_bc_def] >> rw[] >>
    (* Handle *)
    cheat) >>
  strip_tac >- cheat >> (* Op *)
  strip_tac >- (
    simp[bEval_def,bvl_bc_def] >> rw[] >- (
      qexists_tac`bs1` >> simp[] >>
      qspecl_then[`cenv`,`t`,`sz`,`emit cs [Tick]`,`[x]`]strip_assume_tac bvl_bc_append_out >>
      fs[emit_def] >>
      match_mp_tac bc_fetch_next_addr >>
      simp[] >> qexists_tac`bc0`>>simp[] >>
      fs[Once (GSYM SWAP_REVERSE)] ) >>
    qspecl_then[`cenv`,`t`,`sz`,`emit cs [Tick]`,`[x]`]strip_assume_tac bvl_bc_append_out >> fs[] >>
    fs[Once(GSYM SWAP_REVERSE),emit_def] >>
    mp_tac(Q.REFL `bc_eval1 bs1`) >>
    `bc_fetch bs1 = SOME Tick` by (
      match_mp_tac bc_fetch_next_addr >> simp[] >>
      qexists_tac`bc0` >> simp[] ) >>
    CONV_TAC(LAND_CONV(RAND_CONV(SIMP_CONV(srw_ss())[bc_eval1_def]))) >>
    simp[bump_pc_def] >>
    simp[GSYM bc_eval1_thm] >>
    disch_then(strip_assume_tac o MATCH_MP RTC_SUBSET) >>
    srw_tac[DNF_ss][Once RTC_CASES_RTC_TWICE] >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    qmatch_assum_abbrev_tac`bc_next^* bs1 bs2` >>
    imp_res_tac RTC_bc_next_preserves >>
    first_x_assum(qspecl_then[`bs2`,`bc0++[Tick]`,`REVERSE bc`]mp_tac) >> simp[] >>
    simp[Abbr`bs2`,dec_clock_def,SUM_APPEND,FILTER_APPEND] >>
    simp[GSYM AND_IMP_INTRO] >>
    disch_then(fn th => first_assum(mp_tac o MATCH_MP th)) >>
    disch_then(qspecl_then[`t`,`cs with out := Tick::cs.out`]mp_tac) >>
    simp[] ) >>
  simp[bEval_def,bvl_bc_def] >> rw[] >>
  `∃res0 s0. bEval (xs,env,s1) = (res0,s0)` by metis_tac[pair_CASES] >>
  qspecl_then[`cenv`,`TCNonTail`,`sz`,`cs`,`xs`]strip_assume_tac bvl_bc_append_out >>
  cheat (* Call *))

val _ = export_theory()
