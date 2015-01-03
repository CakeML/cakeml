open HolKernel boolLib bossLib lcsymtacs
open listTheory rich_listTheory quantHeuristicsLib quantHeuristicsLibAbbrev arithmeticTheory
open miscTheory bytecodeTheory bytecodeExtraTheory bvlTheory
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
      bvl_bc ((GENLIST (λk. sz+k-n) n)++cenv)
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

val good_code_env_def = Define`
  good_code_env cmap ls ⇔
    ∀ptr exp arity. (lookup ptr cmap = SOME (arity,exp)) ⇒
      ∃cs l0 cc l1.
        ((bvl_bc (GENLIST (λn. arity-n) arity) (TCTail arity 1) (arity+2) cs exp).out = cc ++ cs.out) ∧
        EVERY (combin$C $< cs.next_label o dest_Label) (FILTER is_Label l0) ∧ ptr < cs.next_label ∧
        (ls = l0 ++ [Label ptr] ++ REVERSE cc ++ l1)`

val good_env_def = Define`
  good_env sz st =
      LIST_REL (λv n. n ≤ sz ∧ (sz-n) < LENGTH st ∧ (EL (sz-n) st = v))`

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

(*
val bvl_bc_correct = store_thm("bvl_bc_correct",
  ``∀exps env s res s' bs1 bc0 code bc1 cenv t sz cs stw ret sp hdl rst.
      (bEval (exps,env,s) = (res,s')) ∧ res ≠ Error ∧
      (good_env sz bs1.stack env cenv) ∧
      (good_code_env s.code bs1.code) ∧
      ((bvl_bc cenv t sz cs exps).out = REVERSE code ++ cs.out) ∧
      (bs1.code = bc0 ++ code ++ bc1) ∧
      (bs1.pc = next_addr bs1.inst_length bc0) ∧
      (bs1.clock = SOME s.clock) ∧ (bs1.globals = s.globals) ∧ (bs1.refs = s.refs) ∧
      (case t of
       | TCTail j k => (∃ig args. (bs.stack = ig++(RetPtr ret::args)++rst) ∧ (LENGTH ig = k) ∧ (LENGTH args = j))
       | TCNonTail => T) ∧
      (case res of Exception _ =>
        ∃ig. (bs1.stack = ig ++ [StackPtr sp; CodePtr hdl] ++ rst) ∧
             (LENGTH rst = bs1.handler)
       | _ => T)
      ⇒
      ∃bs2.
        bc_next^* bs1 bs2 ∧
        (bs2.clock = SOME s'.clock) ∧ (bs2.globals = s'.globals) ∧ (bs2.refs = s'.refs) ∧
        case res of
        | TimeOut =>
            (bs2.clock = SOME 0) ∧ (bc_fetch bs2 = SOME Tick) ∧ (bs2.output = bs1.output)
        | Exception v =>
            (bs2 = bs1 with <|stack := v::rst; pc := hdl; handler := sp|>)
        | Result v =>
          (case t of
            | TCNonTail =>
              (bs2 = bs1 with <|
                stack := v::bs1.stack;
                pc := next_addr bs2.inst_length (bc0++code)|>)
            | TCTail _ _ =>
              (bs2 = bs1 with <| stack := v::rst; pc := ret |>))``,
  bEval_ind
*)

val _ = export_theory()
