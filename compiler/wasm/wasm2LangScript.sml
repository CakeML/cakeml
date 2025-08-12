(*
  CWasm AST modelling Wasm 2.0 (+ tail calls)
  Present here are
    + control flow instructions
    + all numeric (stack) instructions
    + all vector (stack) instructions
    + all (incl num&vec) memory operations -- factored into their own datatype
  Imprecisions:
    HOL lists encode Wasm vectors; latter has max length of 2^32
*)
open preamble;

val _ = set_grammar_ancestry ["words", "arithmetic", "list"];

val _ = new_theory "wasm2Lang";

(* Note :
  Most datatypes closely follow the wasm abstractions. ie,
  The HOL Datatype: <ABC> is named to wasm's <ABC> type.
  We attempt to note where our encoding differs from wasm specs.
*)

(************************************)
(*                                  *)
(*     Basic Types + ancillaries    *)
(*                                  *)
(************************************)

Datatype: bvtype (* bit vector type (Does anyone have a better name? *)
  = Int
  | Float
End

Datatype: width
  = W32
  | W64
End

Type index = “:word32”

Datatype: reftype
  = Fun
  | Ext
End

Datatype: valtype
  = Tnum bvtype width
  | Tvec
  | Tref reftype
End

Type resulttype = “:valtype list”

Type functype = “:resulttype # resulttype”

Datatype: limits
  = Lunb word64
  | Lwmx word64 word64
End

Type mem = “:word8 list”
(* Type addrtype = “:width” *)
Type memtype = “:(width # limits)”

Type tabletype = “:limits # reftype”

Datatype: globaltype
  = Gconst valtype
  | Gmut   valtype
End
(* Type globaltype = “:bool # valtype” *)

Datatype: externtype
  = ExFun functype
  | ExTbl tabletype
  | ExMem memtype
  | ExGbl globaltype
End

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

(************************)
(*                      *)
(*     Instructions     *)
(*                      *)
(************************)

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
  | (* inn *) Extend8s   width
  | (* inn *) Extend16s  width
  | (* i64 *) Extend32s
  | (* i64 *) ExtendI32_ sign

  (* float ops *)
  | (* fnn *) Abs     width
  | (* fnn *) Neg     width
  | (* fnn *) Ceil    width
  | (* fnn *) Floor   width
  | (* fnn *) Trunc   width
  | (* fnn *) Nearest width
  | (* fnn *) Sqrt    width
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

  (* float *)
  | (* fnn *) Div        width
  | (* fnn *) Min        width
  | (* fnn *) Max        width
  | (* fnn *) Copysign   width
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

  (* float *)
  | (* fnn *) Lt width
  | (* fnn *) Gt width
  | (* fnn *) Le width
  | (* fnn *) Ge width
End

(* Datatype: test_op (* for future test instructions? *)
  = (* inn *) Eqz width
End *)

Datatype: convert_op
  = (* i32 *) WrapI64
  | (* inn *) Trunc_f       width sign width
  | (* inn *) Trunc_sat_f   width sign width
  | (* f32 *) Demote
  | (* f64 *) Promote
  | (* fnn *) Convert       width sign width
  | (* inn *) Reinterpret_f width
  | (* fnn *) Reinterpret_i width
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
Type laneidx = “:word8”
Type word128 = “:128 word”

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

Datatype: fshape
  = F32x4
  | F64x2
End

Datatype: shape
  = IShp ishape
  | FShp fshape
End

Datatype: half
  = Low
  | High
End

(***************)
(*   Vectors   *)
(***************)

Datatype: vec_unary_op

  (* vec *)
  = (* v128 *) Vnot
  (* misc *)
  | (* iall *) Vbitmask ishape

  (* int *)
  | (* 8x16 *) Vpopcnt

  (* int & float *)
  | (*  all *) Vabs shape
  | (*  all *) Vneg shape

  (* float *)
  | (* fall *) Vsqrt    fshape
  | (* fall *) Vceil    fshape
  | (* fall *) Vfloor   fshape
  | (* fall *) Vtrunc   fshape
  | (* fall *) Vnearest fshape
End

Datatype: vec_binary_op

  (* vec *)
  = (* v128 *) Vand
  | (* v128 *) VandNot
  | (* v128 *) Vor
  | (* v128 *) Vxor
  (* misc *)
  | (* v128 *) Vswizzle
  | (* v128 *) Vnarrow sign ishap2
  | (* i2x4 *) Vdot

  (* both *)
  | (*  all *) Vadd shape
  | (*  all *) Vsub shape

  (* int *)
  | (* 16x8 *) VmulQ15
  | (* 16x8 *) VmulI16
  | (* 32x4 *) VmulI32
  | (* 64x2 *) VmulI64
  | (* IS3  *) Vmin_     sign ishap3
  | (* IS3  *) Vmax_     sign ishap3
  | (* IS2  *) Vadd_sat_ sign ishap2
  | (* IS2  *) Vsub_sat_ sign ishap2
  | (* IS2  *) Vavgr_u        ishap2

  (* float *)
  | (* fall *) VmulF fshape
  | (* fall *) Vdiv  fshape
  | (* fall *) Vmin  fshape
  | (* fall *) Vmax  fshape
  | (* fall *) Vpmin fshape
  | (* fall *) Vpmax fshape
End

Datatype: vec_ternary_op
  = VbitSelect
End

Datatype: vec_compare_op

  = (*  all *) Veq shape
  | (*  all *) Vne shape

  | (* IS3  *) Vlt_ sign ishap3
  | (* IS3  *) Vgt_ sign ishap3
  | (* IS3  *) Vle_ sign ishap3
  | (* IS3  *) Vge_ sign ishap3
  | (* 64x2 *) Vlt_s
  | (* 64x2 *) Vgt_s
  | (* 64x2 *) Vle_s
  | (* 64x2 *) Vge_s

  | (* fall *) Vlt fshape
  | (* fall *) Vgt fshape
  | (* fall *) Vle fshape
  | (* fall *) Vge fshape
End

Datatype: vec_test_op
  (* vec *)
  = (* v128 *) VanyTrue

  (* int *)
  | (* iall *) VallTrue ishape
End

Datatype: vec_shift_op

  (* int *)
  = (* v128 *) Vshl       ishape
  | (* v128 *) Vshr_ sign ishape
End

Datatype: vec_convert_op

  = (* il3  *) Vextend     half   ishap3 sign
  | (* il3  *) VextMul     half   ishap3 sign
  | (* il3  *) VextAdd            ishap2 sign
  | (* i2x4 *) VtruncSat          sign
  | (* i2x4 *) VtruncSat0         sign
  | (* fall *) Vconvert    half   sign
  | (* f2x4 *) Vdemote
  | (* f4x2 *) Vpromote
End

(* Datatype: vec_splat_op
  = Vsplat shape
End *)

Datatype: vec_lane_op
  = Vextract_    sign ishap2
  | VextractI32x4
  | VextractI64x2
  | VextractF    fshape
  | Vreplace      shape
  | Vshuffle laneidx laneidx laneidx laneidx
             laneidx laneidx laneidx laneidx
             laneidx laneidx laneidx laneidx
             laneidx laneidx laneidx (* last laneidx from V_lane *)
End

Datatype: vec_instr
  = V_const    word128
  | V_unary    vec_unary_op
  | V_binary   vec_binary_op
  | V_ternary  vec_ternary_op
  | V_compare  vec_compare_op
  | V_test     vec_test_op
  | V_shift    vec_shift_op
  | V_convert  vec_convert_op
  | V_splat    shape
  (* | V_splat    vec_splat_op *)
  | V_lane     vec_lane_op laneidx
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
(*   Tables   *)
(**************)

Datatype: table_instr
  = TableSet  index
  | TableGet  index
  | TableSize index
  | TableGrow index
  | TableFill index
  | TableCopy index index
  | TableInit index index
  | Elemdrop  index
End


(**************)
(*   Memory   *)
(**************)

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

  (* vec *)
  | Load128               word32 word32
  | LoadHalf  ishap3 sign word32 word32
  | LoadZero  width       word32 word32
  | LoadSplat ishape      word32 word32
  | LoadLane  ishape      word32 word32 word8
End

Datatype: store_instr

  (* int/float *)
  = Store       bvtype width word32 word32
  | StoreNarrow ishap2 width word32 word32
  | StoreNarrow32            word32 word32

  (* vec *)
  | Store128         word32 word32
  | StoreLane ishape word32 word32 word8
End

Datatype: mem_others
  = MemorySize
  | MemoryGrow
  | MemoryFill
  | MemoryCopy
  | MemoryInit index
  | DataDrop   index
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
  | BlkIdx index
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
  | Vector     vec_instr
  | Parametric para_instr
  | Variable   var_instr
  | Table      table_instr
  | MemRead    load_instr
  | MemWrite   store_instr
  | MemOthers  mem_others

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

Datatype: func =
  <| name   : string
   ; type   : functype
   ; locals : valtype list
   ; body   : expr
   |>
End

Datatype: global =
  <| type: globaltype
   ; init: expr
   |>
End

Datatype: data =
  <| data   : index
   ; offset : constant_expr
   ; init   : word8 list
   |>
End

Datatype: datamode
  = Dpassive
  | Dactive index constant_expr
End

Datatype: data2 =
  <| init : word8 list
   ; mode : datamode
   |>
End

Datatype: module =
  <| funcs   : func    list
   ; mems    : memtype
   ; globals : global  list
   ; datas   : data
   |>
End



(*******************)
(*                 *)
(*     Modules     *)
(*                 *)
(*******************)

Datatype: moduleWasm =
  <|
    funcs   : func    list ;
    (* tables  : table   list ; *)
    mems    : memtype list ;
    globals : global  list ;
    (* elems   : elem    list ; *)
    datas   : data    list ;
    start   : index        ;
    (* imports : import  list ; *)
    (* exports : export  list ; *)
  |>
End


val _ = export_theory();

(*
2.3 Types
    2.3.1 Number Types
    2.3.2 Vector Types
    2.3.3 Reference Types
    2.3.4 Value Types
    2.3.5 Result Types
    2.3.6 Function Types
    2.3.7 Limits
    2.3.8 Memory Types
    2.3.9 Table Types
    2.3.10 Global Types
    2.3.11 External Types

2.4 Instructions
    2.4.1 Numeric Instructions
    2.4.2 Vector Instructions
    2.4.3 Reference Instructions
    2.4.4 Parametric Instructions
    2.4.5 Variable Instructions
    2.4.6 Table Instructions
    2.4.7 Memory Instructions
    2.4.8 Control Instructions
    2.4.9 Expressions

2.5 Modules
*)

  (* wasm 3 *)
  (* | MemorySize index       *)
  (* | MemoryGrow index       *)
  (* | MemoryFill index       *)
  (* | MemoryCopy index       *)
  (* | MemoryInit index index *)
  (* | DataDrop   index index *)
