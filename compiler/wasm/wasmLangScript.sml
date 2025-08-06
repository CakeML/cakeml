(*
  CWasm AST modelling Wasm 1.0 (+ tail calls)
  Present here are
    + control flow instructions
    + int numeric instructions (ie, those not involving floats)
    + int memory operations    (not involving floats/vecs)
  Imprecisions:
    HOL lists encode Wasm vectors; latter has max length of 2^32
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

Datatype: valtype
  = Tnum bvtype width
End

Type addrtype = “:width”

Datatype: limits
  = Lunb word64
  | Lwmx word64 word64
End

Type mem = “:word8 list”
Type memtyp = “:(addrtype # limits)”

Type resulttype = “:valtype list”
Type functype = “:resulttype list # resulttype list”

(* Note on style :
  instructions data constructors have their return types
  -- when present in the encoding; they are elided when unnecessary (due to being unique/variant-less) --
  as the last argument/s.

  The other arguments distinguish variants of the same function.

  Example:
    Clz W32  represents (the wasm instruction)  i32.clz  -- "W32" specified the return type i32.
  & Clz W64  represents                         i64.clz
  We don't encode the "int" part of i32/i64 because there is no float version of clz.

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

  (***************************************)
  (*   Misc vec notations/"types"/tags   *)
  (***************************************)

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

(* NB:
  We abuse abstraction by (re)using the ishape (ishap2/ishap3) datatype from vectors
  to specify narrowness for loads.

  eg,
  Wasm instructions allow loading 8/16 bits from memory into a 32 bit value : i32.load8_s / i32.load16_s
  The CWasm AST uses it's encoding for vec shapes (i8x16) to represent "8" etc
*)

Datatype: load_instr

  (* int/float *)
  = Load            bvtype width word32 word32
  | LoadNarrow ishap2 sign width word32 word32
  | LoadNarrow32      sign       word32 word32
End

Datatype: store_instr

  (* int/float *)
  = Store       bvtype width word32 word32
  | StoreNarrow ishap2 width word32 word32
  | StoreNarrow32            word32 word32
End

Type index = “:word32”


(******************************)
(*                            *)
(*     Other instructions     *)
(*                            *)
(******************************)

Datatype: para_instr (* parametric *)
  = Drop
  | Select
End

Datatype: var_instr
  = LocalGet  index
  | LocalSet  index
  | LocalTee  index
  | GlobalGet index
  | GlobalSet index
End


(*************************************)
(*                                   *)
(*     Control Flow Instructions     *)
(*                                   *)
(*************************************)

  (******************************)
  (*   Misc Notations/"types"   *)
  (******************************)

(* Type t = “:valtype”
Type functype = “:t list # t list” *)
(* Datatype: functype
  =
  |
End *)


(* QQ these represent block types? *)
(* Datatype:
  tb = Tbf num (* | Tbv (t option) *)
End *)

(* Datatype: ctrlFlow_instr
  | CtrlFlow  ctrlFlow_instr
End *)

Datatype: blocktype
  = BlkNil
  | BlkVal valtype
End

(* TODO switch out nums in AST to index *)

Datatype: instr

  (* control instructions *)
  = Unreachable
  | Nop

  | Block blocktype (instr list)
  | Loop  blocktype (instr list)
  | If    blocktype (instr list) (instr list)

  | Br                   index
  | BrIf                 index
  | BrTable (index list) index

  | Return
  | ReturnCall         index            (* TODO: tail call *)
  | ReturnCallIndirect index functype   (* TODO: input/output params, names *)
  | Call               index
  | CallIndirect       index functype   (* TODO: first num is tableid *)

  | Variable   var_instr
  | Parametric para_instr
  | Numeric    num_instr
  | MemRead    load_instr
  | MemWrite   store_instr

End

Datatype: global
  = Gconst valtype
  | Gmut   valtype
End

(* we could also do global much more simply *)
(* Type global = “:bool # valtype” *)

Datatype: func =
  <|
    name       : string     ;
    type       : functype   ;
    body       : instr list ;
    localTypes : valtype list
  |>
End

(* MM: HOL doesn't have a utf8 library *)
Datatype: module =
  <|
  funcs   : func list   ;
  (* tables  : table list  ; *)
  mems    : mem list    ;
  globals : global list ;
  (* elems   : elem list   ; *)
  (* datas   : data list   ; *)
  start   : index       ;
  (* imports : import list ; *)
  (* exports : export list ; *)
  |>
End

val _ = export_theory();
