(*
  WASM syntax and semantics
  incomplete and possibly incorrect
  NOT YET TESTED AGAINST THE OFFICIAL WASM SPECIFICATION
*)
open preamble;

val _ = new_theory "wasmSem";

(* Syntax *)

Datatype:
  t = T_i32 | T_i64 (* | T_f32 | T_f64 and vector types *)
End

(* memory operations other than 64 bits *)
Datatype:
  tp_num = Tp_i8 | Tp_i16 | Tp_i32
End

Datatype:
  stackop = StackTODO
End

Datatype:
  tb = Tbf num (* | Tbv (t option) *)
End

Datatype:
  tf = FunctionTypeTemp
End

Datatype:
  unop = UnOpTemp
End

Datatype:
  binop = BinOpTemp
End

Datatype:
  testop = TestOpTemp
End

Datatype:
  relop = RelOpTemp
End

Datatype:
  cvtop = CvtOpTemp
End

Datatype:
  stack_instr =
  | I32Const word32
  | I64Const word64
  | Unop t unop
  | Binop t binop
  | Testop t testop
  | Relop t testop
  (* | Cvtop *)
End

Datatype:
  instr =
  | Unreachable
  | Nop
  | Drop
  | Select
  | Block tb (instr list)
  | Loop tb (instr list)
  | If tb (instr list) (instr list)
  | Br num
  | BrIf num
  | BrTable (num list) num
  | Return
  | Call num
  | CallIndirect num tf (* TODO: first num is tableid *)
  | LocalGet num
  | LocalSet num
  | LocalTee num
  | GlobalGet num
  | GlobalSet num
  | Load t ((tp_num # bool) option) word32 (* TODO: alignment *)
  | Store t tp_num word32 (* TODO: alignment *)
  | Instr stack_instr
  | ReturnCall num (* TODO: tail call *)
  | ReturnCallIndirect num tf (* TODO: input/output params, names *)
End

(* Semantics *)
Datatype:
  value = I32 word32 | I64 word64
End

Datatype:
  state =
  <|
    clock: num;
    stack: value list;
    locals: value list;
    globals: value list;
    memory: word8 list;
    types: (t list # t list) list;
    (* TODO: funcs: func list *)
  |>
End

Datatype:
  result =
    RNormal
  | RBreak num
  | RTrap
  | RInvalid (* failures from "Assert: due to validation ..." *)
  | RTimeout
End

(* Returns the function type for tb *)
Definition tb_tf_def:
  tb_tf types (Tbf n) = oEL n types
End

Definition exec_def:
  (exec Unreachable s = (RTrap,s)) ∧
  (exec Nop s = (RNormal,s)) ∧
  (exec Drop s =
    case s.stack of [] => (RInvalid, s) | (_::ss) =>
      (RNormal, s with stack := ss)) ∧
  (exec Select s = ARB) ∧
  (exec (Block tb b) s =
    case tb_tf s.types tb of NONE => (RInvalid,s) | SOME (mts,nts) =>
    let m = LENGTH mts in
    let n = LENGTH nts in
    if LENGTH s.stack < m then (RInvalid,s) else
    let stack0 = s.stack in
    let (res, s) = exec_list b (s with stack:=TAKE m stack0) in
    case res of
      RBreak 0 =>
      if LENGTH s.stack < n then (RInvalid,s) else
      (RNormal, (s with stack := (TAKE n s.stack) ++ (DROP m stack0)))
    | RBreak (SUC l) => (RBreak l, s)
    | RNormal =>
      if LENGTH s.stack ≠ n then (RInvalid,s) else
      (RNormal, (s with stack := s.stack ++ (DROP m stack0)))
    | _ => (res, s)
  ) ∧
  (exec (Loop tb b) s = ARB) ∧
  (exec (If tb bl br) s = ARB) ∧
  (exec (Br n) s = (RBreak n, s)) ∧
  (exec (BrIf n) s = ARB) ∧
  (exec (BrTable table n) s = ARB) ∧
  (exec Return s = ARB) ∧
  (exec (Call n) s = ARB) ∧
  (exec (CallIndirect n tf) s = ARB) ∧
  (exec (LocalGet n) s = ARB) ∧
  (exec (LocalSet n) s = ARB) ∧
  (exec (LocalTee n) s = ARB) ∧
  (exec (GlobalGet n) s = ARB) ∧
  (exec (GlobalSet n) s = ARB) ∧
  (exec (Load _ _ _) s = ARB) ∧
  (exec (Store _ _ _) s = ARB) ∧
  (exec (Instr _) s = ARB) ∧
  (exec (ReturnCall n) s = ARB) ∧
  (exec (ReturnCallIndirect n tf) s = ARB) ∧
  (exec_list [] s = (RNormal, s)) ∧
  (exec_list (b::bs) s =
    let (res,s) = exec b s in
    case res of
      RNormal => exec_list bs s
    | _ => (res,s))
End

val _ = export_theory();
