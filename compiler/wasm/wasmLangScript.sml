(*
  CakeML Wasm 1.0 (+ tail calls) AST

  The AST here has
  + control flow instructions
  + numeric instructions not involving floats
*)
open preamble;

val _ = new_theory "wasmLang";

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

(* Doing it this way allows us to -- for exmaple -- later limit things
to just ints, which we couldn't do if iNN and fNN were all in the same datatype *)
Datatype: numtype
  = NT bvtype width
End

Overload i32 = “NT Int   W32”
Overload i64 = “NT Int   W64”

Datatype: valtype
  = Tnum numtype
  | Tvec
  | TFunRef
  | TExtRef
End

(********************************)
(*                              *)
(*     Numeric Instructions     *)
(*                              *)
(********************************)

Datatype: unary_op

  (* int *)
  = (* inn *) Clz         width
  | (* inn *) Ctz         width
  | (* inn *) Popcnt      width
  | (* inn *) Extend8_s   width
  | (* inn *) Extend16_s  width
  | (* i64 *) Extend32_s
  | (* i64 *) Extend_i32_ sign

End

Datatype: binary_op

  (* both int and/or float -- given by {bvtype} *)
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
  = (* all *) Eq  bvtype width
  | (* all *) Ne  bvtype width

  (* int *)
  | (* inn *) Lt_ sign width
  | (* inn *) Gt_ sign width
  | (* inn *) Le_ sign width
  | (* inn *) Ge_ sign width

End

(* Datatype: test_op
  = (* inn *) Eqz width
End *)

Datatype: convert_op
  = (* i32 *) Wrap_i64
End

Datatype: num_instr
  = N_const32 bvtype word32
  | N_const64 bvtype word64
  | N_unary     unary_op
  | N_binary   binary_op
  | N_compare compare_op
  | N_eqz     width (* this is the only test op *)
  (* | N_test       test_op *)
  | N_convert convert_op
End

Datatype: ishap2
  = I8x16
  | I16x8
End

Datatype: ishap3
  = Is2 ishap2
  | I32x4
End

Datatype: ishape
  = Is3 ishap3
  | I64x2
End

(*******************************)
(*                             *)
(*     Memory Instructions     *)
(*                             *)
(*******************************)

Datatype: mem_instr

  = Load            bvtype width (word32 # word32)
  | LoadNarrow ishap2 sign width (word32 # word32)
  | LoadNarrow32      sign       (word32 # word32)

  | Store       bvtype width (word32 # word32)
  | StoreNarrow ishap2 width (word32 # word32)
  | StoreNarrow32            (word32 # word32)

  (* vec *)
  | Load128               (word32 # word32)
  | LoadHalf  ishap3 sign (word32 # word32)
  | LoadZero  width       (word32 # word32)
  | LoadSplat ishape      (word32 # word32)
  | LoadLane  ishape      (word32 # word32) word8

  | Store128         (word32 # word32)
  | StoreLane ishape (word32 # word32) word8

  | Size
  | Grow
  | Fill
  | Copy
  | Init num
  | Drop num

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

  | Br   num
  | BrIf num
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
  | LocalGet     num
  | LocalSet     num
  | LocalTee     num
  | GlobalGet    num
  | GlobalSet    num

  (* memory instructions *)
  | OLoad  t ((tp_num # bool) option) word32 (* TODO: alignment *)
  | OStore t tp_num word32                   (* TODO: alignment *)

  | Memory  mem_instr
  | Numeric num_instr

End

val _ = export_theory();
