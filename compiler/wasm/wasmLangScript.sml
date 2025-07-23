(*
  WebAssembly (Wasm) syntax
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

(* Doing it this way allows us to -- for exmaple -- later limit things
to just ints, which we couldn't do if iNN and fNN were all in the same datatype *)
Datatype: numtype
  = NT bvtype width
End

Overload i32 = “NT Int   W32”
Overload i64 = “NT Int   W64”
Overload f32 = “NT Float W32”
Overload f64 = “NT Float W64”

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

  (* float *)
  | (* fnn *) Abs     width
  | (* fnn *) Neg     width
  | (* fnn *) Sqrt    width
  | (* fnn *) Ceil    width
  | (* fnn *) Floor   width
  | (* fnn *) Trunc   width
  | (* fnn *) Nearest width
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

  (* float *)
  | (* fnn *) Div        width
  | (* fnn *) Min        width
  | (* fnn *) Max        width
  | (* fnn *) Copysign   width

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

  (* float *)
  | (* fnn *) Lt width
  | (* fnn *) Gt width
  | (* fnn *) Le width
  | (* fnn *) Ge width

End

(* let's leave it like this for the abstraction + future exstensibility despite it being a singleton  *)
Datatype: test_op
  = (* inn *) Eqz width
  (* | *)
End

Datatype: convert_op
  = (* i32 *) Wrap_i64
  | (* inn *) Trunc_f       width sign width
  | (* inn *) Trunc_sat_f   width sign width
  | (* f32 *) Demote
  | (* f64 *) Promote
  | (* fnn *) Convert       width sign width
  | (* inn *) Reinterpret_f width
  | (* fnn *) Reinterpret_i width
End

Datatype: num_instr
  = (* if3 *) N_const32 bvtype word32
  | (* if6 *) N_const64 bvtype word64
  | (* all *) N_unary     unary_op
  | (* all *) N_binary   binary_op
  | (* all *) N_compare compare_op
  | (* inn *) N_test       test_op
  | (* all *) N_convert convert_op
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
  | (*  all *) Vmul shape (* i16x8 is really "q15mulr_sat_s" *)

  (* int *)
  | (* IS3  *) Vmin_     sign ishap3
  | (* IS3  *) Vmax_     sign ishap3
  | (* IS2  *) Vadd_sat_ sign ishap2
  | (* IS2  *) Vsub_sat_ sign ishap2
  | (* IS2  *) Vavgr_u        ishap2

  (* float *)
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

(* This wasn't worth encoding -- no need for an "empty" constructor *)
(* Datatype: vec_splat_op (* consume a value of numeric type and produce a v128 result of a specified shape *)
  = (*  all *) Vsplat shape
End *)

Datatype: vec_lane_op
  = VextractLane_    sign ishap2
  | VextractLane32_4
  | VextractLane64_2
  | VextractLanef    fshape
  | VreplaceLane     shape
  | (* v128 *) Vshuffle
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
  | V_splat    shape   (* vec_splat_op *)
  | V_lane     vec_lane_op

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

(* Datatype: ctrlFlow_instr
  | CtrlFlow  ctrlFlow_instr
End *)

Datatype: instr
  = Unreachable
  | Nop

  | Drop
  | Select
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

  | Load  t ((tp_num # bool) option) word32 (* TODO: alignment *)
  | Store t tp_num word32                   (* TODO: alignment *)

  | LocalGet     num
  | LocalSet     num
  | LocalTee     num
  | GlobalGet    num
  | GlobalSet    num

  | Instr     num_instr
  | Vec       vec_instr

End

val _ = export_theory();
