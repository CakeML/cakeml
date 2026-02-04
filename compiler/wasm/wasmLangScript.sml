(*
  CWasm AST modelling Wasm 1.0 (+ tail calls)
  Imprecisions:
    HOL lists encode Wasm vectors; latter has max length of 2^32
*)

Theory    wasmLang
Ancestors words arithmetic list mlstring
Libs      wordsLib dep_rewrite

(* Note :
  Most datatypes closely follow the wasm abstractions. ie,
  The HOL Datatype: <ABC> is named for wasm's <ABC> type.
  We attempt to note where our encoding differs from wasm specs.
*)

(************************************)
(*                                  *)
(*     Basic Types + ancillaries    *)
(*                                  *)
(************************************)

Type index = “:word32”

(* CWasm's bvtype + width ~= Wasm numerical types *)
Datatype: bvtype (* bit vector type (Does anyone have a better name? *)
  = Int
End

Datatype: width
  = W32
  | W64
End

Datatype: valtype
  = Tnum bvtype width
End

Type resulttype = “:valtype option”

Type functype = “:valtype list # valtype list”

Datatype: limits
  = Lunb word32
  | Lwmx word32 word32
End

Type memtype = “:limits”

Datatype: globaltype
  = Gconst valtype
  | Gmut   valtype
End
(* Type globaltype = “:bool # valtype” *)

(************************)
(*                      *)
(*     Instructions     *)
(*                      *)
(************************)

(* Note on style :
  To start with an example: the CWasm instruction   "Clz W32"   represents the wasm instruction   "i32.clz".
  The "W32" specifies the return type i32. A bvtype (Int or Float) is unnesscessary as clz is an Int-only instruction.

  In general, a CWasm instruction's (data constructor's) last argument indicates it's return type.
  However, where there is enough information
   have their return types
  -- when present in the encoding; they are elided when unnecessary (due to being unique/variant-less) --
  as the last argument/s.

*)

(****************)
(*   Numerics   *)
(****************)

Datatype: sign  (* ancillary type *)
  = Signed
  | Unsigned
End

Datatype: unary_op
  (* int ops *)
  = (* inn *) Clz        width
  | (* inn *) Ctz        width
  | (* inn *) Popcnt     width
  | (* inn *) Extend8s   width  (* from Wasm 1+ε *)
  | (* inn *) Extend16s  width  (* from Wasm 1+ε *)
  | (* i64 *) Extend32s         (* from Wasm 1+ε *)
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


(*********************************)
(*   Vectors - ancillary types   *)
(*********************************)

Datatype: ishap2
  = I8x16
  | I16x8
End


(*******************)
(*   Parametrics   *)
(*******************)

Datatype: para_instr
  = Drop
  | Select
End


(*****************)
(*   Variables   *)
(*****************)

Datatype: var_instr
  = LocalGet  index
  | LocalSet  index
  | LocalTee  index
  | GlobalGet index
  | GlobalSet index
End


(**************)
(*   Memory   *)
(**************)

(* NB:
  We abuse abstraction by (re)using the ishap2 datatype from vectors
  to specify narrowness for loads.

  eg,
  Wasm instructions allow loading 8/16 bits from memory into a 32 bit value : i32.load8_s / i32.load16_s
  The CWasm AST uses it's encoding for vec shapes (I8x16) to represent "8" etc
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


(************************************************)
(*   Control Flows + top level instr Datatype   *)
(************************************************)

(*  Note: Since branches (control flow instructions) can contain
    lists of instrutions, we don't factor CF instructions out of
    the top level *)

(* CF ancillaries *)
Datatype: blocktype
  = BlkNil
  | BlkVal valtype
End

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
  | ReturnCall         index
  | ReturnCallIndirect index functype
  | Call               index
  | CallIndirect       index functype

  | Numeric    num_instr
  | Parametric para_instr
  | Variable   var_instr
  | MemRead    load_instr
  | MemWrite   store_instr

End



(*************************)
(*                       *)
(*     CWasm Modules     *)
(*                       *)
(*************************)

(*  Note: CWasm modules are sound wrt to the Wasm
    spec, but have been simplified. ie, Every CWasm
    module can be represented as a Wasm module, but
    the converse may not be true *)

Type expr          = “:instr list”
Type constant_expr = “:instr list”

Datatype: global =
  <| gtype : globaltype
   ; ginit : expr
   |>
End

Datatype: data =
  <| data   : index
   ; offset : constant_expr
   ; dinit  : word8 list
   |>
End

Datatype: func =
  <| ftype  : index
   ; locals : valtype list
   ; body   : expr
   |>
End

Datatype: module =
  <| types   : functype list
   (* TODO: add imports and exports
   ; import_funcs : (index_into_types # (mlstring # mlstring)) list
   ; export_mems : (index_into_mems # mlstring) list
   *)
   ; funcs   : func     list
   ; mems    : memtype  list
   ; globals : global   list
   ; datas   : data     list
   |>
End

Datatype: names =
  <| mname  : mlstring
   ; fnames : (index # mlstring) list
   ; lnames : (index # ((index # mlstring) list)) list
   |>
End

Definition blank_mod_def:
  blank_mod = module [] [] [] [] []
End

Definition blank_names_def:
  blank_names : names =
  <| mname  := «»
   ; fnames := []
   ; lnames := []
   |>
End

(*******************)
(*                 *)
(*     Modules     *)
(*                 *)
(*******************)

Datatype: moduleWasm =
  <| types   : functype list
   ; funcs   : func     list
   ; mems    : memtype  list
   ; globals : global   list
   ; datas   : data     list
   ; start   : index
   |>
End

(******************************************************************************)
(*                                                                            *)
(*  Ready-to-use Wasm instructions                                            *)
(*                                                                            *)
(******************************************************************************)

Definition I64_EQ_def:
  I64_EQ = Numeric (N_compare (Eq Int W64))
End
Definition I32_EQ_def:
  I32_EQ = Numeric (N_compare (Eq Int W32))
End

Definition I64_NE_def:
  I64_NE = Numeric (N_compare (Ne Int W64))
End
Definition I32_NE_def:
  I32_NE = Numeric (N_compare (Ne Int W32))
End

Definition I64_LT_U_def:
  I64_LT_U = Numeric (N_compare (Lt_ Unsigned W64))
End
Definition I32_LT_U_def:
  I32_LT_U = Numeric (N_compare (Lt_ Unsigned W32))
End

Definition I64_GT_U_def:
  I64_GT_U = Numeric (N_compare (Gt_ Unsigned W64))
End
Definition I32_GT_U_def:
  I32_GT_U = Numeric (N_compare (Gt_ Unsigned W32))
End

Definition I64_LE_U_def:
  I64_LE_U = Numeric (N_compare (Le_ Unsigned W64))
End
Definition I32_LE_U_def:
  I32_LE_U = Numeric (N_compare (Le_ Unsigned W32))
End

Definition I64_GE_U_def:
  I64_GE_U = Numeric (N_compare (Ge_ Unsigned W64))
End
Definition I32_GE_U_def:
  I32_GE_U = Numeric (N_compare (Ge_ Unsigned W32))
End

Definition I64_LT_S_def:
  I64_LT_S = Numeric (N_compare (Lt_ Signed W64))
End
Definition I32_LT_S_def:
  I32_LT_S = Numeric (N_compare (Lt_ Signed W32))
End

Definition I64_GT_S_def:
  I64_GT_S = Numeric (N_compare (Gt_ Signed W64))
End
Definition I32_GT_S_def:
  I32_GT_S = Numeric (N_compare (Gt_ Signed W32))
End

Definition I64_LE_S_def:
  I64_LE_S = Numeric (N_compare (Le_ Signed W64))
End
Definition I32_LE_S_def:
  I32_LE_S = Numeric (N_compare (Le_ Signed W32))
End

Definition I64_GE_S_def:
  I64_GE_S = Numeric (N_compare (Ge_ Signed W64))
End
Definition I32_GE_S_def:
  I32_GE_S = Numeric (N_compare (Ge_ Signed W32))
End

Definition I64_EQZ_def:
  I64_EQZ = Numeric (N_eqz W64)
End
Definition I32_EQZ_def:
  I32_EQZ = Numeric (N_eqz W32)
End

Definition I64_CONST_def:
  I64_CONST w = Numeric (N_const64 Int w)
End
Definition I32_CONST_def:
  I32_CONST w = Numeric (N_const32 Int w)
End

Definition I64_ADD_def:
  I64_ADD = Numeric (N_binary (Add Int W64))
End
Definition I32_ADD_def:
  I32_ADD = Numeric (N_binary (Add Int W32))
End

Definition I64_SUB_def:
  I64_SUB = Numeric (N_binary (Sub Int W64))
End
Definition I32_SUB_def:
  I32_SUB = Numeric (N_binary (Sub Int W32))
End

Definition I64_MUL_def:
  I64_MUL = Numeric (N_binary (Mul Int W64))
End
Definition I32_MUL_def:
  I32_MUL = Numeric (N_binary (Mul Int W32))
End

Definition I64_AND_def:
  I64_AND = Numeric (N_binary (And W64))
End
Definition I32_AND_def:
  I32_AND = Numeric (N_binary (And W32))
End

Definition I64_OR_def:
  I64_OR = Numeric (N_binary (Or W64))
End
Definition I32_OR_def:
  I32_OR = Numeric (N_binary (Or W32))
End

Definition I64_XOR_def:
  I64_XOR = Numeric (N_binary (Xor W64))
End
Definition I32_XOR_def:
  I32_XOR = Numeric (N_binary (Xor W32))
End

Definition I64_SHL_def:
  I64_SHL = Numeric (N_binary (Shl W64))
End
Definition I32_SHL_def:
  I32_SHL = Numeric (N_binary (Shl W32))
End

Definition I64_SHR_S_def:
  I64_SHR_S = Numeric (N_binary (Shr_ Signed W64))
End
Definition I32_SHR_S_def:
  I32_SHR_S = Numeric (N_binary (Shr_ Signed W32))
End

Definition I64_SHR_U_def:
  I64_SHR_U = Numeric (N_binary (Shr_ Unsigned W64))
End
Definition I32_SHR_U_def:
  I32_SHR_U = Numeric (N_binary (Shr_ Unsigned W32))
End

Definition I64_ROTR_def:
  I64_ROTR = Numeric (N_binary (Rotr W64))
End
Definition I32_ROTR_def:
  I32_ROTR = Numeric (N_binary (Rotr W32))
End

Definition I64_DIV_S_def:
  I64_DIV_S = Numeric (N_binary (Div_ Signed W64))
End
Definition I32_DIV_S_def:
  I32_DIV_S = Numeric (N_binary (Div_ Signed W32))
End

Definition I64_DIV_U_def:
  I64_DIV_U = Numeric (N_binary (Div_ Unsigned W64))
End
Definition I32_DIV_U_def:
  I32_DIV_U = Numeric (N_binary (Div_ Unsigned W32))
End

Definition I32_WRAP_I64_def:
  I32_WRAP_I64 = Numeric (N_convert WrapI64)
End

Definition GLOBAL_GET_def:
  GLOBAL_GET i = Variable (GlobalGet (n2w i))
End

Definition GLOBAL_SET_def:
  GLOBAL_SET i = Variable (GlobalSet (n2w i))
End

Definition LOCAL_GET_def:
  LOCAL_GET i = Variable (LocalGet (n2w i))
End

Definition LOCAL_SET_def:
  LOCAL_SET i = Variable (LocalSet (n2w i))
End

Definition LOCAL_TEE_def:
  LOCAL_TEE i = Variable (LocalTee (n2w i))
End

Definition RETURN_def:
  RETURN = wasmLang$Return
End

Definition CALL_def:
  CALL i = wasmLang$Call (n2w i)
End

Definition CALL_INDIRECT_def:
  CALL_INDIRECT ft = CallIndirect 0w ft
End

Definition RETURN_CALL_def:
  RETURN_CALL i = ReturnCall (n2w i)
End

Definition RETURN_CALL_INDIRECT_def:
  RETURN_CALL_INDIRECT ft = ReturnCallIndirect 0w ft
End

Definition SELECT_def:
  SELECT = Parametric Select
End

Definition I64_EXTEND32_U_def:
  I64_EXTEND32_U = Numeric (N_unary (ExtendI32_ Unsigned))
End

Definition I64_LOAD_def:
  I64_LOAD ofs = MemRead (Load Int W64 ofs 8w)
End

Definition I64_LOAD8_S_def:
  I64_LOAD8_S ofs = MemRead (LoadNarrow I8x16 Signed W32 ofs 1w)
End

Definition I64_LOAD8_U_def:
  I64_LOAD8_U ofs = MemRead (LoadNarrow I8x16 Unsigned W32 ofs 1w)
End

Definition I64_LOAD16_S_def:
  I64_LOAD16_S ofs = MemRead (LoadNarrow I16x8 Signed W32 ofs 2w)
End

Definition I64_LOAD16_U_def:
  I64_LOAD16_U ofs = MemRead (LoadNarrow I16x8 Unsigned W32 ofs 2w)
End

Definition I64_LOAD32_S_def:
  I64_LOAD32_S ofs = MemRead (LoadNarrow32 Signed ofs 4w)
End

Definition I64_LOAD32_U_def:
  I64_LOAD32_U ofs = MemRead (LoadNarrow32 Unsigned ofs 4w)
End

Definition I64_STORE_def:
  I64_STORE ofs = MemWrite (Store Int W64 ofs 8w)
End

Definition I64_STORE8_def:
  I64_STORE8 ofs = MemWrite (StoreNarrow I8x16 W32 ofs 1w)
End

Definition I64_STORE16_def:
  I64_STORE16 ofs = MemWrite (StoreNarrow I16x8 W32 ofs 2w)
End

Definition I64_STORE32_def:
  I64_STORE32 ofs = MemWrite (StoreNarrow32 ofs 4w)
End

Definition i32_def:
  i32 = Tnum Int W32
End

Definition i64_def:
  i64 = Tnum Int W64
End
