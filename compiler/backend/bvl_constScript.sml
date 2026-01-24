(*
   This is a BVL transformation that propagates simple and
   cheap-to-compute context-free expression from Let bindings. It also
   performs some simple constant folding with SmartOp (below).

   The most significant impact of this optimisation is that it removes
   each Var in a Let, i.e. Let [...; Var ...; ...] ..., and replaces
   them with constants Let [...; Op (IntOp (Const _)) []; ...] .... and
   replaces all occurrences of the bound var with a lookup to the
   original variable.

   bvi_let is a simpler version of this optimisation.
*)
Theory bvl_const
Ancestors
  bvl
Libs
  preamble

val _ = patternMatchesSyntax.temp_enable_pmatch();

Definition dest_simple_def[simp]:
  (dest_simple (bvl$Op (IntOp (Const i)) xs) = if NULL xs then SOME i else NONE) /\
  (dest_simple _ = NONE)
End

Theorem dest_simple_pmatch:
    ∀op. dest_simple op =
    pmatch op of
      bvl$Op (IntOp (Const i)) [] => SOME i
    | _ => NONE
Proof
  rpt strip_tac
  >> rpt(CONV_TAC(RAND_CONV patternMatchesLib.PMATCH_ELIM_CONV) >> every_case_tac)
  >> fs[dest_simple_def]
QED

Definition case_op_const_def:
    case_op_const exp =
        case exp of
        | (Op op [x1; Op (IntOp (Const n2)) l]) => if NULL l then SOME (op, x1, n2) else NONE
        | _ => NONE
End

Theorem case_op_const_pmatch:
    ∀exp. case_op_const exp =
    pmatch exp of
      | (Op op [x1; Op (IntOp (Const n2)) []]) => SOME (op, x1, n2)
      | _ => NONE
Proof
  rpt strip_tac
  >> rpt(CONV_TAC(RAND_CONV patternMatchesLib.PMATCH_ELIM_CONV) >> every_case_tac)
  >> fs[case_op_const_def]
QED

Definition SmartOp_flip_def:
    SmartOp_flip op x1 x2 =
      case (dest_simple x1) of
      | (SOME i) =>
          if MEM op [IntOp Add; IntOp Mult] then (op, x2, x1)
          else if op = IntOp Sub then (IntOp Add, x2, Op (IntOp (Const (-i))) [])
          else (op, x1, x2)
      | _ => (op, x1, x2)
End

Theorem SmartOp_flip_pmatch:
  !op x1 x2. SmartOp_flip op x1 x2 =
    pmatch (dest_simple x1) of
    | (SOME i) =>
        if MEM op [IntOp Add; IntOp Mult] then (op, x2, x1)
        else if op = IntOp Sub then (IntOp Add, x2, Op (IntOp (Const (-i))) [])
        else (op, x1, x2)
    | _ => (op, x1, x2)
Proof
  rpt strip_tac
  >> rpt(CONV_TAC(RAND_CONV patternMatchesLib.PMATCH_ELIM_CONV) >> every_case_tac)
  >> fs[SmartOp_flip_def]
QED

local val SmartOp2_quotation = `
  SmartOp2 (op, x1:bvl$exp, x2:bvl$exp) =
    let mk_add_const x1 c2 =
      if c2 = 0 then x1
      else Op (IntOp Add) [x1; Op (IntOp (Const c2)) []]
    in
    let mk_add x1 x2 =
      let default = Op (IntOp Add) [x1; x2] in
        case (dest_simple x2) of
        | (SOME n2) => (
            case (case_op_const x1) of
            | SOME (op, x11, n12) =>
                if op = IntOp Add then mk_add_const x11 (n2+n12)
                else if op = IntOp Sub then Op (IntOp Sub) [x11; Op (IntOp (Const (n2+n12))) []]
                else default
            | _ =>
                case (dest_simple x1) of
                | SOME n1 => Op (IntOp (Const (n2+n1))) []
                | _ => mk_add_const x1 n2
        )
        | _ =>
            case (case_op_const x1, case_op_const x2) of
            | (SOME (op1, x11, n12), SOME (op2, x21, n22)) =>
                if op1 = IntOp Add /\ op2 = IntOp Add then
                  mk_add_const (Op (IntOp Add) [x11; x21]) (n22+n12)
                else if op1 = IntOp Add /\ op2 = IntOp Sub then
                  Op (IntOp Sub) [Op (IntOp Sub) [x11; x21]; Op (IntOp (Const (n22+n12))) []]
                else if op1 = IntOp Sub /\ op2 = IntOp Add then
                  mk_add_const (Op (IntOp Sub) [x11; x21]) (n22+n12)
                else default
            | _ => default
    in
    let mk_sub x1 x2 =
      let default = Op (IntOp Sub) [x1; x2] in
        case (dest_simple x2) of
        | (SOME n2) => (
            case (case_op_const x1) of
            | SOME (op, x11, n12) =>
                if op = IntOp Add then Op (IntOp Sub) [x11; Op (IntOp (Const (n2-n12))) []]
                else if op = IntOp Sub then mk_add_const x11 (n2-n12)
                else default
            | _ =>
                case (dest_simple x1) of
                | SOME n1 => Op (IntOp (Const (n2-n1))) []
                | _ => default
        )
        | _ =>
            case (case_op_const x1, case_op_const x2) of
            | (SOME (op1, x11, n12), SOME (op2, x21, n22)) =>
                if op1 = IntOp Add /\ op2 = IntOp Add then
                  Op (IntOp Add) [Op (IntOp Sub) [x11; x21]; Op (IntOp (Const (n22-n12))) []]
                else if op1 = IntOp Add /\ op2 = IntOp Sub then
                  Op (IntOp Sub) [Op (IntOp Add) [x11; x21]; Op (IntOp (Const (n22-n12))) []]
                else if op1 = IntOp Sub /\ op2 = IntOp Add then
                  mk_add_const (Op (IntOp Add) [x11; x21]) (n22-n12)
                else default
            | _ => default
    in
    let mk_mul x1 x2 =
      let default = Op (IntOp Mult) [x1; x2] in
        case (dest_simple x2) of
        | (SOME n2) => (
            case (case_op_const x1) of
            | SOME (op, x11, n12) =>
                if op = IntOp Mult then Op (IntOp Mult) [x11; Op (IntOp (Const (n2*n12))) []]
                else default
            | _ =>
                case (dest_simple x1) of
                | SOME n1 => Op (IntOp (Const (n2*n1))) []
                | _ =>
                    if n2 = 1 then x1
                    else if n2 = -1 then mk_sub x1 (Op (IntOp (Const 0)) [])
                    else default
        )
        | _ =>
            case (case_op_const x1, case_op_const x2) of
            | (SOME (op1, x11, n12), SOME (op2, x21, n22)) =>
                if op1 = IntOp Mult /\ op2 = IntOp Mult then
                  Op (IntOp Mult) [Op (IntOp (Const (n22*n12))) []; Op (IntOp Mult) [x11; x21]]
                else default
            | _ => default
    in
    let default = Op op [x1;x2] in
    if op = IntOp Add then
      mk_add x1 x2
    else if op = IntOp Sub then
      mk_sub x1 x2
    else if op = IntOp Mult then
      mk_mul x1 x2
    else if MEM op [IntOp Div; IntOp Mod; IntOp Less; IntOp LessEq; IntOp Greater; IntOp GreaterEq] then
      case (dest_simple x1, dest_simple x2) of
      | (SOME x1, SOME (x2:int)) =>
          (case op of
           | IntOp Div => if x1 = 0 then default else Op (IntOp (Const (x2 / x1))) []
           | IntOp Mod => if x1 = 0 then default else Op (IntOp (Const (x2 % x1))) []
           | IntOp Less => Bool (x2 < x1)
           | IntOp LessEq => Bool (x2 <= x1)
           | IntOp Greater => Bool (x2 > x1)
           | IntOp GreaterEq => Bool (x2 >= x1)
           | _ => default)
      | _ => default
    else if op = BlockOp Equal then
      case (dest_simple x1, dest_simple x2) of
      | (SOME i, SOME j) => Bool (j = i)
      | (SOME i, _) => Op (BlockOp (EqualConst (Int i))) [x2]
      | (_, SOME i) => Op (BlockOp (EqualConst (Int i))) [x1]
      | _ => default
    else if op = MemOp El then
      case dest_simple x1 of
      | SOME i => if i < 0 then default else Op (BlockOp (ElemAt (Num i))) [x2]
      | _ => default
    else default`
in
val SmartOp2_def = Define SmartOp2_quotation

val tm = (SmartOp2_quotation |>
   map (fn QUOTE s => Portable.replace_string {from="case",to="case"} s |> QUOTE
       | aq => aq)) |> Term

Theorem SmartOp2_pmatch:
  ^tm
Proof
  CONV_TAC (DEPTH_CONV patternMatchesLib.PMATCH_ELIM_CONV) >>
  simp [SmartOp2_def]
QED
end


Definition dest_EqualInt_def:
  dest_EqualInt (BlockOp (EqualConst (Int i))) = SOME i ∧
  dest_EqualInt _ = NONE
End

Theorem dest_EqualInt_pmatch:
  dest_EqualInt x = pmatch x of BlockOp (EqualConst (Int i)) => SOME i | _ => NONE
Proof
  CONV_TAC(RAND_CONV patternMatchesLib.PMATCH_ELIM_CONV)
  \\ Cases_on ‘x’ \\ EVAL_TAC
  \\ Cases_on ‘b’ \\ EVAL_TAC
  \\ rename [‘EqualConst cc’] \\ Cases_on ‘cc’ \\ EVAL_TAC
QED

Definition SmartOp1_def:
  SmartOp1 op x =
    case dest_EqualInt op of
    | NONE => Op op [x]
    | SOME i =>
      case dest_simple x of
      | NONE => Op op [x]
      | SOME j => Bool (j = i)
End


Definition SmartOp_def:
  SmartOp op xs =
    case xs of
    | [x1; x2] => SmartOp2 (SmartOp_flip op x1 x2)
    | [x] => SmartOp1 op x
    | _ => Op op xs
End

Theorem SmartOp_pmatch:
      !op xs. SmartOp op xs =
      pmatch xs of
      | [x1;x2] => SmartOp2 (SmartOp_flip op x1 x2)
      | [x] => SmartOp1 op x
      | _ => Op op xs
Proof
  rpt strip_tac
  >> rpt(CONV_TAC(RAND_CONV patternMatchesLib.PMATCH_ELIM_CONV) >> every_case_tac)
  >> fs[SmartOp_def]
QED

Definition extract_def:
  (extract ((Var n):bvl$exp) ys = SOME ((Var (n + LENGTH ys + 1)):bvl$exp)) /\
  (extract (Op (IntOp (Const i)) xs) ys = SOME (Op (IntOp (Const i)) [])) /\
  (extract (Op (BlockOp (Cons t)) xs) ys =
    if NULL xs then SOME (Op (BlockOp (Cons t)) []) else NONE) /\
  (extract _ _ = NONE)
End

Theorem extract_pmatch:
    ∀op ys. extract op ys =
    pmatch op of
      (Var n):bvl$exp => SOME ((Var (n + LENGTH ys + 1)):bvl$exp)
    | Op (IntOp (Const i)) xs => SOME (Op (IntOp (Const i)) [])
    | Op (BlockOp (Cons t)) [] => SOME (Op (BlockOp (Cons t)) [])
    | _ => NONE
Proof
  rpt strip_tac
  >> rpt(CONV_TAC(RAND_CONV patternMatchesLib.PMATCH_ELIM_CONV) >> every_case_tac)
  >> fs[extract_def]
QED

Definition extract_list_def:
  (extract_list [] = []) /\
  (extract_list (x::xs) = extract x xs :: extract_list xs)
End

Definition delete_var_def:
  (delete_var ((Var n):bvl$exp) = Op (IntOp (Const 0)) []) /\
  (delete_var x = x)
End

Theorem delete_var_pmatch:
  !op.
  delete_var op =
    pmatch op of
      Var n => Op (IntOp (Const 0)) []
    | x => x
Proof
  rpt strip_tac
  >> rpt(CONV_TAC(RAND_CONV patternMatchesLib.PMATCH_ELIM_CONV) >> every_case_tac)
  >> fs[delete_var_def]
QED

Definition compile_def:
  (compile env [] = []) /\
  (compile env (x::y::xs) = compile env [x] ++ compile env (y::xs)) /\
  (compile env [Var v] =
     case LLOOKUP env v of
     | NONE => [Var v]
     | SOME NONE => [Var v]
     | SOME (SOME (Var i)) => [Var (v + i)]
     | SOME (SOME x) => [x]) /\
  (compile env [If x1 x2 x3] =
     let y1 = HD (compile env [x1]) in
     let y2 = HD (compile env [x2]) in
     let y3 = HD (compile env [x3]) in
       if y1 = Bool T then [y2] else
       if y1 = Bool F then [y3] else
         [If y1 y2 y3]) /\
  (compile env [Let xs x2] =
     let ys = compile env xs in
       [Let (MAP delete_var ys)
            (HD (compile (extract_list ys ++ env) [x2]))]) /\
  (compile env [Handle x1 x2] =
     [Handle (HD (compile env [x1])) (HD (compile (NONE::env) [x2]))]) /\
  (compile env [Raise x1] =
     [Raise (HD (compile env [x1]))]) /\
  (compile env [Op op xs] = [SmartOp op (compile env xs)]) /\
  (compile env [Tick x] = [Tick (HD (compile env [x]))]) /\
  (compile env [Force loc v] =
     case LLOOKUP env v of
     | NONE => [Force loc v]
     | SOME NONE => [Force loc v]
     | SOME (SOME (Var i)) => [Force loc (v + i)]
     | SOME (SOME x) => [Force loc v]) /\
  (compile env [Call t dest xs] = [Call t dest (compile env xs)])
End

Definition compile_sing_def:
  (compile_sing env (Var v) =
     case LLOOKUP env v of
     | NONE => Var v
     | SOME NONE => Var v
     | SOME (SOME (Var i)) => Var (v + i)
     | SOME (SOME x) => x) /\
  (compile_sing env (If x1 x2 x3) =
     let y1 = compile_sing env x1 in
     let y2 = compile_sing env x2 in
     let y3 = compile_sing env x3 in
       if y1 = Bool T then y2 else
       if y1 = Bool F then y3 else
         If y1 y2 y3) /\
  (compile_sing env (Let xs x2) =
     let ys = compile_list env xs in
       Let (MAP delete_var ys)
           (compile_sing (extract_list ys ++ env) x2)) /\
  (compile_sing env (Handle x1 x2) =
     Handle (compile_sing env x1) (compile_sing (NONE::env) x2)) /\
  (compile_sing env (Raise x1) =
     Raise (compile_sing env x1)) /\
  (compile_sing env (Op op xs) = SmartOp op (compile_list env xs)) /\
  (compile_sing env (Tick x) = Tick (compile_sing env x)) /\
  (compile_sing env (Force loc v) =
     case LLOOKUP env v of
     | NONE => Force loc v
     | SOME NONE => Force loc v
     | SOME (SOME (Var i)) => Force loc (v + i)
     | SOME (SOME x) => Force loc v) ∧
  (compile_sing env (Call t dest xs) = Call t dest (compile_list env xs)) ∧

  (compile_list env [] = []) /\
  (compile_list env (x::xs) = compile_sing env x :: compile_list env xs)
End

Theorem compile_eq:
  (∀e env. compile env [e] = [compile_sing env e]) ∧
  (∀es env. compile env es = compile_list env es)
Proof
  Induct >> rw[compile_def, compile_sing_def] >>
  rpt (TOP_CASE_TAC >> gvs[]) >>
  Cases_on `es` >> simp[compile_def, compile_sing_def]
QED

Theorem compile_length[simp]:
   !n xs. LENGTH (compile n xs) = LENGTH xs
Proof
  HO_MATCH_MP_TAC compile_ind \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC (srw_ss()) [compile_def,ADD1,LET_DEF]
  \\ every_case_tac \\ SRW_TAC [] [] \\ DECIDE_TAC
QED

Theorem compile_HD_SING:
   [HD (compile n [x])] = compile n [x]
Proof
  MP_TAC (Q.SPECL [`n`,`[x]`] compile_length)
  \\ Cases_on `compile n [x]` \\ fs [LENGTH_NIL]
QED

Definition compile_exp_def:
  compile_exp x =
    case compile [] [x] of (y::_) => y | _ => Var 0 (* impossible *)
End

Theorem compile_exp_eq = compile_exp_def |> SRULE [compile_eq];

