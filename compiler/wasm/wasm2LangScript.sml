(*
  CakeML Wasm 2.0 (+ tail calls) AST

  The AST here has
  + control flow instructions
  + all numeric (stack) instructions
  + all vector (stack) instructions
  + all memory operations -- factored into their own datatype
*)
open preamble;

val _ = new_theory "wasm2Lang";

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
  | Float
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
  | Tvec
  | TFunRef
  | TExtRef
End

Type addrtype = “:width”

Datatype: limits
  = Lunb word64
  | Lwmx word64 word64
End

Type memtyp = “:(addrtype # limits)”

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


(*******************************)
(*                             *)
(*     Vector Instructions     *)
(*                             *)
(*******************************)

  (***************************************)
  (*   Misc vec notations/"types"/tags   *)
  (***************************************)

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

  (*************************)
  (*   Vector Operations   *)
  (*************************)

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
  = Size
  | Grow
  | Fill
  | Copy
  | Init num
  | DDrop num
End
  (* wasm 3 *)
  (* | Size num *)
  (* | Grow num *)
  (* | Fill num *)
  (* | Copy num *)
  (* | Init num num *)
  (* | Drop num num *)


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
(* QQ this is a table id? *)

(* memory operations other than 64 bits *)
Datatype:
  tp_num = Tp_i8 | Tp_i16 | Tp_i32
End

(* QQ these represent block types? *)
Datatype:
  tb = Tbf num (* | Tbv (t option) *)
End

(* Datatype: ctrlFlow_instr
  | CtrlFlow  ctrlFlow_instr
End *)

Datatype: blocktype
  = BlkNil
  | BlkVal valtype
  | BlkIdx num
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

  | Numeric  num_instr
  | Vector   vec_instr
  | MemRead  load_instr
  | MemWrite store_instr
  | Memory   mem_others

End

(* Datatype: module
  =
End *)

val _ = export_theory();
