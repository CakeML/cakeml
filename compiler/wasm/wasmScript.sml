(*
  WASM syntax and semantics
  incomplete and possibly incorrect
  NOT YET TESTED AGAINST THE OFFICIAL WASM SPECIFICATION
*)
open preamble;

val _ = new_theory "wasmSem";

(* Syntax *)

Datatype:
  memopsz = W8 | W32 | W64
End

(* bool means signed/unsigned *)
Datatype:
  memopty = Load bool | Store
End

Datatype:
  stackop = StackTODO
End

Datatype:
  inst =
    LocalGet num
  | LocalSet num
  | LocalTee num
  | GlobalGet num
  | GlobalSet num
  | I32Const word32
  | I64Const word64
  | Memory memopty memopsz word32 (* TODO: align? *)
  | Regular stackop
  | Block (inst list) (* TODO: input/output params, names *)
  | Loop (inst list) (* TODO: input/output params, names *)
  | If (inst list) (inst list) (* TODO: input/output params, names *)
  | Br num
  | BrIf num
  | BrTable (num list) num
  | Call num
  | CallIndirect (* TODO: input/output params, names *)
  | ReturnCall num (* TODO: tail call *)
  | ReturnCallIndirect (* TODO: input/output params, names *)
  | Return
  | Unreachable
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
    (* TODO: funcs: func list *)
  |>
End

val _ = export_theory();
