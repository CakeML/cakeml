open HolKernel boolLib bossLib lcsymtacs
open bytecodeTheory bvlTheory
val _ = new_theory"bvlBytecode"

val _ = Datatype`
  bvl_bc_state = <|
    next_label : num;
    out : bc_inst list |>`

val emit_def = Define`
  emit = FOLDL (λs i. s with <| out := i :: s.out |>)`

val get_label_def = Define`
  get_label s = (s with <| next_label := s.next_label + 1 |>, s.next_label)`

val _ = Datatype`
  bvl_bc_tail = TCNonTail | TCTail num num`

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

val bvl_bc_def = tDefine "bvl_bc"`
  (bvl_bc cenv t sz s (Var n) =
     if n < LENGTH cenv then
       pushret t (emit s [Stack(Load(sz-(EL n cenv)))])
     else s) ∧
  (bvl_bc cenv t sz s (If e1 e2 e3) =
    let (s,l1) = get_label s in
    let (s,l2) = get_label s in
    let s = bvl_bc cenv TCNonTail sz s e1 in
    let s = emit s [JumpIf (Lab l1)] in
    let s = bvl_bc cenv t sz s e3 in
    let s = emit s [Jump (Lab l2);Label l1] in
    let s = bvl_bc cenv t sz s e2 in
            emit s [Label l2]) ∧
  (bvl_bc cenv t sz s (Let es e) =
    bvl_bc_bindings cenv sz s es t 0 e) ∧
  (bvl_bc cenv t sz s (Raise e) =
    let s = bvl_bc cenv TCNonTail sz s e in
            emit s [PopExc; Return]) ∧
  (bvl_bc cenv t sz s (Handle e1 e2) =
    let (s,l0) = get_label s in
    let (s,l1) = get_label s in
    let s = emit s [PushPtr (Lab l0); PushExc] in
    let s = bvl_bc cenv TCNonTail (sz+2) s e1 in
    let s = pushret t (emit s [PopExc; Stack (Pops 1)]) in
    let s = emit s [Jump (Lab l1); Label l0] in
    let s = bvl_bc ((sz+1)::cenv) t (sz+1) s e2 in
            emit s [Label l1]) ∧
  (bvl_bc cenv t sz s (Tick e) =
    let s = emit s [Tick] in
            bvl_bc cenv t sz s e) ∧
  (bvl_bc cenv t sz s (Call dest es) =
    let s = bvl_bc_list cenv sz s es in
    let s = emit s [Tick] in
    case dest of
    | NONE => emit s [Stack(Load 0); CallPtr]
    | SOME p => emit s [Stack(PushInt 0); Call (Lab p)]) ∧
  (bvl_bc cenv t sz s (Op op es) =
    let s = bvl_bc_list cenv sz s es in
            pushret t s (* TODO *)) ∧
  (bvl_bc_list cenv sz s [] = s) ∧
  (bvl_bc_list cenv sz s (e::es) =
    let s = bvl_bc cenv TCNonTail sz s e in
      bvl_bc_list cenv (sz+1) s es) ∧
  (bvl_bc_bindings cenv sz s [] t n b =
     case t of
     | TCNonTail => emit (bvl_bc cenv t sz s b) [Stack (Pops n)]
     | TCTail j k => bvl_bc cenv (TCTail j (k+n)) sz s b) ∧
  (bvl_bc_bindings cenv sz s (e::es) t n b =
     let s = bvl_bc cenv TCNonTail sz s e in
       bvl_bc_bindings ((sz+1)::cenv) (sz+1) s es t (n+1) b)`
  (WF_REL_TAC`inv_image ($< LEX $<)
      (λx. case x of INL (_,_,_,_,e) => (bvl_exp_size e,2:num)
                   | INR (INL (_,_,_,es)) => (bvl_exp1_size es,1)
                   | INR (INR (_,_,_,es,_,_,b)) => (bvl_exp1_size (b::es),0))`)

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

(*
val bvl_bc_correct = store_thm("bvl_bc_correct",
  ``∀exps env s res s' bs1 bc0 code bc1 cenv t sz cs stw ret sp hdl rst.
      (bEval (exps,env,s) = (res,s')) ∧ res ≠ Error ∧
      (good_env sz bs1.stack env cenv) ∧
      (good_code_env s.code bs1.code) ∧

      ((bvl_bc cenv t sz cs exp).out = REVERSE code ++ cs.out) ∧
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
