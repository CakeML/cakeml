(*
  WASM semantics
  incomplete and possibly incorrect
  NOT YET TESTED AGAINST THE OFFICIAL WASM SPECIFICATION
*)

open preamble

val _ = new_theory "wasmSem";

Datatype:
  value_type = I32 | I64 | F32 | F64
End

Type func_type = “:value_type list # value_type list”


Datatype:
  value = VALUE num
End

Definition nonzero_def:
  nonzero (VALUE n) = (n≠0)
End

Definition nat_value_def:
  nat_value (VALUE n) = n
End


Datatype:
  regular_inst =
    const value

End

Datatype:
  inst =
    Regular regular_inst
  | Seq inst inst
  | Block func_type inst
  | Loop func_type inst
  | Br num
  | If func_type inst inst
  | BrIf num
  | Call num

  | Local_get num
  | Local_set num
  | Local_tee num
  | Global_get num
  | Global_set num
End

Definition inst_size'_def:
  inst_size' (Regular _) = 1 ∧
  inst_size' (Seq i1 i2) = SUC (inst_size' i1 + inst_size' i2) ∧
  inst_size' (Block _ b) = SUC (inst_size' b) ∧
  inst_size' (Loop _ b) = SUC (inst_size' b) ∧
  inst_size' (Br _) = 1 ∧
  inst_size' (If _ i1 i2) = SUC (inst_size' i1 + inst_size' i2) ∧
  inst_size' (BrIf _) = 1 ∧
  inst_size' (Call _) = 1 ∧
  inst_size' (Local_get _) = 1 ∧
  inst_size' (Local_set _) = 1 ∧
  inst_size' (Local_tee _) = 1 ∧
  inst_size' (Global_get _) = 1 ∧
  inst_size' (Global_set _) = 1
End

Triviality inst_size'_nonzero:
  0 < inst_size' i
Proof
  Induct_on‘i’>>rw[inst_size'_def]
QED

Datatype:
  result = RNormal | RBreak num | RTrap | RTimeout
End

Datatype:
  func =
  <|
    type: func_type;
    locals: value_type list;
    body: inst
  |>
End

Datatype:
  state =
  <|
    clock: num;
    stack: value list;
    locals: value list;
    globals: value list;
    funcs: func list
  |>
End

Definition pop_def:
  pop s = (HD s.stack, (s with stack := TL s.stack))
End

Definition pop_n_def:
  (pop_n 0 s = ([], s)) ∧
  (pop_n (SUC n) s =
    let (first, s1) = pop s in
    let (rest, s') = pop_n n s1 in
    (first::rest, s')
  )
End

Theorem pop_clock:
  (x, s') = pop s ⇒ s'.clock = s.clock
Proof rw[pop_def]
QED

Theorem pop_n_clock:
  (xx, s') = pop_n n s ⇒ s'.clock = s.clock
Proof
  qid_spec_tac‘s’>>qid_spec_tac‘s'’>>qid_spec_tac‘xx’
  >>Induct_on‘n’
  >>rw[pop_n_def,pop_def]
  >>(pairarg_tac>>fs[])
  >>‘s''.clock = (s with stack:=TL s.stack).clock’ by metis_tac[]
  >>rw(#rewrs(TypeBase.simpls_of“:state”))
QED

Definition push_def:
  push x s = s with locals updated_by CONS x
End

Theorem push_clock:
  push x s = s' ⇒ s'.clock = s.clock
Proof rw[push_def]>>rw(#rewrs(TypeBase.simpls_of“:state”))
QED

Definition fix_clock_def:
  fix_clock s (res,s1) = (res,s1 with clock := MIN s.clock s1.clock)
End

Triviality fix_clock_def':
  fix_clock s x =
  case x of (res,s1) =>
  (res,s1 with clock := MIN s.clock s1.clock)
Proof
  Cases_on‘x’
  >>rw[fix_clock_def]
QED

Triviality fix_clock_IMP:
  fix_clock s x = (res,s1) ==> s1.clock <= s.clock
Proof
  Cases_on `x` \\ fs [fix_clock_def] \\ rw [] \\ fs []
QED

Definition exec_R_def:
  exec_R = (inv_image (measure I LEX measure inst_size') (\(i,s). (s.clock,i)))
End

Theorem exec_R_WF:
  WF exec_R
Proof
  rw[exec_R_def]
  >>irule WF_inv_image
  >>irule WF_LEX
  >>rw[]
QED

Definition exec_def:
  (exec (Seq i1 i2) s =
    let (res, s) = fix_clock s (exec i1 s) in
    case res of
      RNormal => exec i2 s
    | _ => (res, s)
  ) ∧

  (exec (Block ft b) s =
    let stack0 = s.stack in
    let (res, s) = exec b (s with stack:=[]) in
    case res of
      RBreak 0 =>
      let args = FST (pop_n (LENGTH (SND ft)) s) in
      (RNormal, (s with stack := REV args stack0))

    | RBreak (SUC l) => (RBreak l, s)
    | _ => (res, s)
  ) ∧

  (exec (Loop ft b) s =
    let stack0 = s.stack in
    let (res, s) = fix_clock s (exec b s) in
    case res of
      RBreak 0 =>
      (case s.clock of
        0 => (RTimeout, s)
      | SUC c =>
        let args = FST (pop_n (LENGTH (SND ft)) s) in
        exec (Loop ft b) (s with <|clock := c; stack := REV args s.stack|>)
      )
    | RBreak (SUC l) => (RBreak l, s)
    | _ => (res, s)
  ) ∧

  (exec (Br n) s = (RBreak n, s)) ∧
  (exec (Regular r) s = (RNormal, s)) ∧

  (exec (If bt i1 i2) s =
    let (c,s) = pop s in
    if nonzero c
    then exec (Block bt i1) s
    else exec (Block bt i2) s
  ) ∧

  (exec (BrIf l) s =
    let (c,s) = pop s in
    if nonzero c
    then (RBreak l, s)
    else (RNormal, s)
  ) ∧

  (exec (Call fi) s =
    case s.clock of
      0 => (RTimeout, s)
    | SUC c =>
      let f = EL fi s.funcs in
      let np = LENGTH (FST f.type) in
      let nr = LENGTH (SND f.type) in
      let (args, s) = pop_n np s in
      let init_locals = args ++ REPLICATE (LENGTH f.locals) ARB in
      let (res, s1) = fix_clock s (exec (Block ([], SND f.type) f.body) (s with <|clock:=c; stack:=[]; locals:=init_locals|>)) in
      case res of
      | RNormal =>
        let (args, _) = pop_n nr s1 in
        (RNormal, s with stack updated_by REV args)
      | _ => (res, s1)
  ) ∧

  (exec (Local_get i) s =
    (RNormal, push (EL i s.locals) s)
  ) ∧

  (exec (Local_set i) s =
    let (x,s) = pop s in
    (RNormal, s with locals updated_by LUPDATE x i)
  ) ∧

  (exec (Local_tee i) s =
    let x = HD s.locals in
    (RNormal, s with locals updated_by LUPDATE x i)
  ) ∧

  (exec (Global_get i) s =
    (RNormal, push (EL i s.globals) s)
  ) ∧

  (exec (Global_set i) s =
    let (x,s) = pop s in
    (RNormal, s with globals updated_by LUPDATE x i)
  )

Termination
  WF_REL_TAC ‘(inv_image (measure I LEX measure inst_size') (\(i,s). (s.clock,i)))’
  >>rw[pop_def,inst_size'_def,inst_size'_nonzero]
  >>imp_res_tac(GSYM fix_clock_IMP)
  >>rpt(dxrule pop_n_clock)
  >>decide_tac
End

val ace = gvs[AllCaseEqs()];
val pa = rpt(pairarg_tac>>fs[]);

Theorem exec_clock:
  ∀inst s s' res'. exec inst s = (res',s') ⇒ s'.clock ≤ s.clock
Proof
  recInduct exec_ind
  >>rw[]
  >>TRY(
    rename1‘Loop’ ORELSE rename1‘If’ ORELSE rename1‘Call’
    >>pop_assum mp_tac
    >>simp[Once exec_def]
    >>TOP_CASE_TAC
    >>pa>>rw[]
    >>imp_res_tac(fix_clock_IMP)
    >>imp_res_tac(GSYM pop_clock)
    >>imp_res_tac(GSYM pop_n_clock)
    >>ace
  )
  >>fs[exec_def,push_def]
  >>pa
  >>imp_res_tac(fix_clock_IMP)
  >>imp_res_tac(GSYM pop_clock)
  >>ace
QED

Theorem fix_clock_exec:
  fix_clock s (exec i s) = exec i s
Proof
  Cases_on‘exec i s’>>fs[fix_clock_def]
  >>imp_res_tac exec_clock
  >>fs[MIN_DEF,DB.theorem"state_component_equality"]
QED

Theorem exec_def[compute,allow_rebind] =
  REWRITE_RULE [fix_clock_exec] exec_def;

Theorem exec_ind[allow_rebind] =
  REWRITE_RULE [fix_clock_exec] exec_ind;

val _ = export_theory();
