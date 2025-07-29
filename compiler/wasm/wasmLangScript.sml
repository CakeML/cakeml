(*
  CakeML Wasm 1.0 (+ tail calls) AST

  The AST here has
  + control flow instructions
  + int numeric instructions (ie, those not involving floats)
  + int memory operations    (not involving floats/vecs)
*)

open preamble;

val _ = new_theory "wasmLang";

(* Note :
  Most datatypes closely follow the wasm abstractions. ie,
  The HOL Datatype: <ABC> is named to wasm's <ABC> type.
  We attempt to note where our encoding differs from wasm specs.
*)

(***********************)
(*                     *)
(*     Basic Types     *)
(*                     *)
(***********************)

Datatype: bvtype (* bit vector type (Does anyone have a better name? *)
  = Int

End

Datatype: width
  = W32
  | W64
End

Datatype: sign
  = Signed
  | Unsigned
End

Datatype: numtype (* we do not enumerate num types directly because bytypes and widths are useful to have *)
  = NT bvtype width
End

Datatype: valtype
  = Tnum numtype
End

(* Note :
  ops/instructions data constructors have their return types
  -- when not present in the data constructor name --
  as the last argument/s.

  The other arguments distinguish variants of the same function.

  Example:
  Clz W32  represents the wasm instruction  i32.clz  -- "W32" specified the return type i32.
  Clz W64  represents  i64.clz  instead.
  We don't need to encode the "int" part of i32/i64
  because there is no float version of the clz instruction.

  More examples
  i32.add :=: Add Int   W32
  f64.add :=: Add Float W64

  i64_trunc_f32_s :=: Trunc_f  W32    Signed  W64
  i32_trunc_f64_u :=: Trunc_f  W64  Unsigned  W32
*)

(********************************)
(*                              *)
(*     Numeric Instructions     *)
(*                              *)
(********************************)

Datatype: unary_op

  (* int ops *)
  = (* inn *) Clz        width
  | (* inn *) Ctz        width
  | (* inn *) Popcnt     width
  | (* inn *) Extend8s   width
  | (* inn *) Extend16s  width
  | (* i64 *) Extend32s
  | (* i64 *) ExtendI32_ sign
End

Datatype: binary_op

  (* ops for both int and float *)
  = (* all *) Add bvtype width
  | (* all *) Sub bvtype width
  | (* all *) Mul bvtype width

  (* int *)
  | (* inn *) Div_ sign  width
  | (* inn *) Rem_ sign  width
  | (* inn *) And        width
  | (* inn *) Or         width
  | (* inn *) Xor        width
  | (* inn *) Shl        width
  | (* inn *) Shr_ sign  width
  | (* inn *) Rotl       width
  | (* inn *) Rotr       width
End

Datatype: compare_op

  (* both *)
  = (* all *) Eq bvtype width
  | (* all *) Ne bvtype width

  (* int *)
  | (* inn *) Lt_ sign width
  | (* inn *) Gt_ sign width
  | (* inn *) Le_ sign width
  | (* inn *) Ge_ sign width
End

(* Datatype: test_op (* for future test instructions? *)
  = (* inn *) Eqz width
End *)

Datatype: convert_op
  = (* i32 *) WrapI64
End

Datatype: num_instr
  = N_const32 bvtype word32
  | N_const64 bvtype word64
  | N_unary     unary_op
  | N_binary   binary_op
  | N_compare compare_op
  | N_eqz     width (* eqz is the only test op *)
  (* | N_test       test_op *)
  | N_convert convert_op
End

Datatype: ishap2
  = I8x16
  | I16x8
End

(*******************************)
(*                             *)
(*     Memory Instructions     *)
(*                             *)
(*******************************)

(* NB:
  We abuse abstraction by (re)use the ishape (ishap2/ishap3) datatype from vectors
  to specify narrowness for loads.

  eg,
  We can load 8/16 bits from memory into a 32 bit value : i32.load8_s / i32.load16_s
  The CWasm AST uses it's encoding for vec shapes (i8x16) to represent "8" etc
*)

Datatype: mem_instr

  = Load            bvtype width (word32 # word32)
  | LoadNarrow ishap2 sign width (word32 # word32)
  | LoadNarrow32      sign       (word32 # word32)

  | Store       bvtype width (word32 # word32)
  | StoreNarrow ishap2 width (word32 # word32)
  | StoreNarrow32            (word32 # word32)
End



(*************************************)
(*                                   *)
(*     Control Flow Instructions     *)
(*                                   *)
(*************************************)

  (******************************)
  (*   Misc Notations/"types"   *)
  (******************************)

Type t = “:numtype”
Type tf = “:t list # t list”;

(* memory operations other than 64 bits *)
Datatype:
  tp_num = Tp_i8 | Tp_i16 | Tp_i32
End

Datatype:
  tb = Tbf num (* | Tbv (t option) *)
End

Datatype: instr

  (* control instructions *)
  = Unreachable
  | Nop

  | Block tb (instr list)
  | Loop  tb (instr list)
  | If    tb (instr list) (instr list)

  | Br                 num
  | BrIf               num
  | BrTable (num list) num

  | Return
  | ReturnCall         num                  (* TODO: tail call *)
  | ReturnCallIndirect num tf               (* TODO: input/output params, names *)
  | Call               num
  | CallIndirect       num tf               (* TODO: first num is tableid *)

  (* parametric instructions *)
  | Drop
  | Select

  (* variable instructions *)
  | LocalGet  num
  | LocalSet  num
  | LocalTee  num
  | GlobalGet num
  | GlobalSet num

  (* memory instructions *)
  | OLoad  t ((tp_num # bool) option) word32 (* TODO: alignment *)
  | OStore t tp_num word32                   (* TODO: alignment *)

  | Memory  mem_instr
  | Numeric num_instr

End

val _ = export_theory();
