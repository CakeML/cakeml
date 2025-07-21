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
  (* | Float *)
End

Datatype: width
  = w32
  | w64
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

Overload i32 = “NT Int   w32”
Overload i64 = “NT Int   w64”

(* Overload f32 = “NT Float w32”
Overload f64 = “NT Float w64” *)



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

  (* float
  | (* fnn *) Abs     width
  | (* fnn *) Neg     width
  | (* fnn *) Sqrt    width
  | (* fnn *) Ceil    width
  | (* fnn *) Floor   width
  | (* fnn *) Trunc   width
  | (* fnn *) Nearest width
  *)
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

  (* float
  | (* fnn *) Div        width
  | (* fnn *) Min        width
  | (* fnn *) Max        width
  | (* fnn *) Copysign   width
  *)
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

  (* float
  | (* fnn *) Lt       width
  | (* fnn *) Gt       width
  | (* fnn *) Le       width
  | (* fnn *) Ge       width
  *)
End

(* let's leave it like this for the abstraction + future exstensibility despite it being a singleton  *)
Datatype: test_op
  = (* inn *) Eqz width
  (* | *)
End

Datatype: convert_op
  = (* i32 *) Wrap_i64 sign
  | (* inn *) Trunc_f width sign
  | (* inn *) Trunc_sat_f width sign
  | (* f32 *) Demote
  | (* f64 *) Promote
  | (* fnn *) Convert width sign
  | (* inn *) Reinterpret_f width width
  | (* fnn *) Reinterpret_i width width
End

Datatype: num_instr
  = (* if3 *) N_const32 bvtype word32
  | (* if6 *) N_const64 bvtype word64
  | (* all *) N_unary     unary_op
  | (* all *) N_binary   binary_op
  | (* inn *) N_test       test_op
  | (* all *) N_compare compare_op
  | (* all *) N_convert convert_op
End



(*******************************)
(*                             *)
(*     Vector Instructions     *)
(*                             *)
(*******************************)

Type word128 = “:128 word”

(********************)
(*   vec "types"    *)
(********************)

Datatype: is2
  = I8x16
  | I16x8
End

Datatype: is3
  = Is2 is2
  | I32x4
End

Datatype: ishape
  = Is3 is3
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

(**************************)
(*   Vector Operations    *)
(**************************)

Datatype: vec_unary_op

  = (* v128 *) Vnot

  | (* 8x16 *) Vpopcnt

  | (*  all *) Vabs shape
  | (*  all *) Vneg shape

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

  (* both *)
  | (*  all *) Vadd shape
  | (*  all *) Vsub shape
  | (*  all *) Vmul shape (* i16x8 is really "q15mulr_sat_s" *)

  (* int *)
  | (* IS3  *) Vmin_     sign is3
  | (* IS3  *) Vmax_     sign is3
  | (* IS2  *) Vadd_sat_ sign is2
  | (* IS2  *) Vsub_sat_ sign is2
  | (* IS2  *) Vavgr_u        is2

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

  | (* IS3  *) Vlt_ sign is3
  | (* IS3  *) Vgt_ sign is3
  | (* IS3  *) Vle_ sign is3
  | (* IS3  *) Vge_ sign is3
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
  (* TODO *)
  (* =
  |  *)
End

Datatype: vec_lane_op
  (* TODO *)
  (* =
  |  *)
End

Datatype: vec_splat_op (* consume a values of numeric type and produce a v128 result of a specified shape *)
  (* TODO *)
  = Vsplat shape
  |
End

Datatype: vec_ _op
End

Datatype: vec_ _op
End

(* Datatype:
End *)

Datatype: vec_instr
  = V_const    word128
  | V_unary    vec_unary_op
  | V_binary   vec_binary_op
  | V_ternary  vec_ternary_op
  | V_compare  vec_compare_op
  | V_test     vec_test_op
  | V_convert  vec_convert_op
End


(*

vvunop ::= not
viunop ::= abs | neg
vfunop ::= abs | neg | sqrt | ceil | floor | trunc | nearest

vvbinop ::= and | andnot | or | xor
vibinop ::= add | sub
vfbinop ::= add | sub | mul | div | min | max | pmin | pmax
viminmaxop ::= min_sx | max_sx
visatbinop ::= add_sat_sx | sub_sat_sx

virelop ::= eq | ne | lt_sx | gt_sx | le_sx | ge_sx
vfrelop ::= eq | ne | lt | gt | le | ge

vvtestop ::= any_true
vitestop ::= all_true


vvternop ::= bitselect
vishiftop ::= shl | shr_sx



vec_instr ::= . . .
== const =============================================
DONE
== unary =============================================
DONE
== binary =============================================
DONE
== ternary ================================================
DONE
== compare ================================================
DONE
== test ===================================================
DONE
== shift ==================================================
| ishape.vishiftop
== convert ================================================
| i16x8.extend_half _i8x16_sx
| i16x8.extmul_half _i8x16_sx
| i16x8.extadd_pairwise_i8x16_sx
| i32x4.extend_half _i16x8_sx
| i32x4.extmul_half _i16x8_sx
| i64x2.extend_half _i32x4_sx
| i64x2.extmul_half _i32x4_sx

| i32x4.trunc_sat_f32x4_sx
| i32x4.trunc_sat_f64x2_sx _zero

| f32x4.convert_i32x4_sx
| f32x4.demote_f64x2_zero
| f64x2.convert_low_i32x4_sx
| f64x2.promote_low_f32x4
== lane ==================================================
| i8x16.extract_lane_sx laneidx
| i16x8.extract_lane_sx laneidx
| i32x4.extract_lane laneidx
| i64x2.extract_lane laneidx
| fshape.extract_lane laneidx
| shape.replace_lane laneidx
== splat ==================================================
| shape.splat


?


| i8x16.shuffle laneidx 16
| i8x16.swizzle
| i8x16.narrow_i16x8_sx
| i16x8.narrow_i32x4_sx
| i32x4.dot_i16x8_s
| i32x4.extadd_pairwise_i16x8_sx
| ishape.bitmask


*)










Type t = “:numtype”

(* memory operations other than 64 bits *)
Datatype:
  tp_num = Tp_i8 | Tp_i16 | Tp_i32
End

Datatype:
  tb = Tbf num (* | Tbv (t option) *)
End

Type tf = “:t list # t list”;

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
  | ReturnCall num (* TODO: tail call *)
  | ReturnCallIndirect num tf (* TODO: input/output params, names *)
  | Instr num_instr
  (* | Vec   vec_instr *)

End


(*********************)
(*                   *)
(*     Notations     *)
(*                   *)
(*********************)
(* This was done manually & therefore is error prone *)


Overload i32_const = “N_const32 Int”
Overload i64_const = “N_const64 Int”

(* Overload f32_const = “N_const32 Float”
Overload f64_const = “N_const64 Float” *)

(***************)
(*   Unaries   *)
(***************)

(* ints *)
Overload i32_clz    = “N_unary (Clz    w32)”
Overload i32_ctz    = “N_unary (Ctz    w32)”
Overload i32_popcnt = “N_unary (Popcnt w32)”

Overload i64_clz    = “N_unary (Clz    w64)”
Overload i64_ctz    = “N_unary (Ctz    w64)”
Overload i64_popcnt = “N_unary (Popcnt w64)”

(* extends *)
Overload i32_Extend8_s    = “N_unary (Extend8_s  w32)”
Overload i32_Extend16_s   = “N_unary (Extend16_s w32)”

Overload i64_Extend8_s    = “N_unary (Extend8_s  w64)”
Overload i64_Extend16_s   = “N_unary (Extend16_s w64)”

Overload i64_Extend32_s   = “N_unary  Extend32_s”
Overload i64_Extend_i32_u = “N_unary (Extend_i32_ Unsgnd)”
Overload i64_Extend_i32_s = “N_unary (Extend_i32_ Signed)”

(* floats *)
(* Overload f32_abs     = “N_unary (Abs     w32)”
Overload f32_neg     = “N_unary (Neg     w32)”
Overload f32_sqrt    = “N_unary (Sqrt    w32)”
Overload f32_ceil    = “N_unary (Ceil    w32)”
Overload f32_floor   = “N_unary (Floor   w32)”
Overload f32_trunc   = “N_unary (Trunc   w32)”
Overload f32_nearest = “N_unary (Nearest w32)”

Overload f64_abs     = “N_unary (Abs     w64)”
Overload f64_neg     = “N_unary (Neg     w64)”
Overload f64_sqrt    = “N_unary (Sqrt    w64)”
Overload f64_ceil    = “N_unary (Ceil    w64)”
Overload f64_floor   = “N_unary (Floor   w64)”
Overload f64_trunc   = “N_unary (Trunc   w64)”
Overload f64_nearest = “N_unary (Nearest w64)” *)

(****************)
(*   Binaries   *)
(****************)

(* ints *)
Overload i32_add = “N_binary (Add Int w32)”
Overload i32_sub = “N_binary (Sub Int w32)”
Overload i32_mul = “N_binary (Mul Int w32)”

Overload i64_add = “N_binary (Add Int w64)”
Overload i64_sub = “N_binary (Sub Int w64)”
Overload i64_mul = “N_binary (Mul Int w64)”

Overload i32_div_u  = “N_binary (Div_ Unsgnd w32)”
Overload i32_div_s  = “N_binary (Div_ Signed w32)”
Overload i32_rem_u  = “N_binary (Rem_ Unsgnd w32)”
Overload i32_rem_s  = “N_binary (Rem_ Signed w32)”
Overload i32_and    = “N_binary (And         w32)”
Overload i32_or     = “N_binary (Or          w32)”
Overload i32_xor    = “N_binary (Xor         w32)”
Overload i32_shl    = “N_binary (Shl         w32)”
Overload i32_shr_u  = “N_binary (Shr_ Unsgnd w32)”
Overload i32_shr_s  = “N_binary (Shr_ Signed w32)”
Overload i32_rotl   = “N_binary (Rotl        w32)”
Overload i32_rotr   = “N_binary (Rotr        w32)”

Overload i64_div_u  = “N_binary (Div_ Unsgnd w64)”
Overload i64_div_s  = “N_binary (Div_ Signed w64)”
Overload i64_rem_u  = “N_binary (Rem_ Unsgnd w64)”
Overload i64_rem_s  = “N_binary (Rem_ Signed w64)”
Overload i64_and    = “N_binary (And         w64)”
Overload i64_or     = “N_binary (Or          w64)”
Overload i64_xor    = “N_binary (Xor         w64)”
Overload i64_shl    = “N_binary (Shl         w64)”
Overload i64_shr_u  = “N_binary (Shr_ Unsgnd w64)”
Overload i64_shr_s  = “N_binary (Shr_ Signed w64)”
Overload i64_rotl   = “N_binary (Rotl        w64)”
Overload i64_rotr   = “N_binary (Rotr        w64)”

(* floats *)
(* Overload f32_add = “N_binary (Add Float w32)”
Overload f32_sub = “N_binary (Sub Float w32)”
Overload f32_mul = “N_binary (Mul Float w32)”

Overload f64_add = “N_binary (Add Float w64)”
Overload f64_sub = “N_binary (Sub Float w64)”
Overload f64_mul = “N_binary (Mul Float w64)”


Overload f32_div      = “N_binary (Div      w32)”
Overload f32_min      = “N_binary (Min      w32)”
Overload f32_max      = “N_binary (Max      w32)”
Overload f32_copysign = “N_binary (Copysign w32)”

Overload f64_div      = “N_binary (Div      w64)”
Overload f64_min      = “N_binary (Min      w64)”
Overload f64_max      = “N_binary (Max      w64)”
Overload f64_copysign = “N_binary (Copysign w64)” *)


(*************)
(*   Tests   *)
(*************)

Overload i32_eqz = “N_Test (Eqz w32)”
Overload i64_eqz = “N_Test (Eqz w64)”


(*******************)
(*   Comparisons   *)
(*******************)

(* ints *)
Overload i32_eq    = “N_compare (Eq  Int    w32)”
Overload i32_ne    = “N_compare (Ne  Int    w32)”
Overload i32_lt_u  = “N_compare (Lt_ Unsgnd w32)”
Overload i32_lt_s  = “N_compare (Lt_ Signed w32)”
Overload i32_gt_u  = “N_compare (Gt_ Unsgnd w32)”
Overload i32_gt_s  = “N_compare (Gt_ Signed w32)”
Overload i32_le_u  = “N_compare (Le_ Unsgnd w32)”
Overload i32_le_s  = “N_compare (Le_ Signed w32)”
Overload i32_ge_u  = “N_compare (Ge_ Unsgnd w32)”
Overload i32_ge_s  = “N_compare (Ge_ Signed w32)”

Overload i64_eq    = “N_compare (Eq  Int    w64)”
Overload i64_ne    = “N_compare (Ne  Int    w64)”
Overload i64_lt_u  = “N_compare (Lt_ Unsgnd w64)”
Overload i64_lt_s  = “N_compare (Lt_ Signed w64)”
Overload i64_gt_u  = “N_compare (Gt_ Unsgnd w64)”
Overload i64_gt_s  = “N_compare (Gt_ Signed w64)”
Overload i64_le_u  = “N_compare (Le_ Unsgnd w64)”
Overload i64_le_s  = “N_compare (Le_ Signed w64)”
Overload i64_ge_u  = “N_compare (Ge_ Unsgnd w64)”
Overload i64_ge_s  = “N_compare (Ge_ Signed w64)”

(* floats *)
(* Overload f32_eq = “N_compare (Eq Float w32)”
Overload f32_ne = “N_compare (Ne Float w32)”

Overload f64_eq = “N_compare (Eq Float w64)”
Overload f64_ne = “N_compare (Ne Float w64)”

Overload f32_lt = “N_compare (Lt w32)”
Overload f32_gt = “N_compare (Gt w32)”
Overload f32_le = “N_compare (Le w32)”
Overload f32_ge = “N_compare (Ge w32)”

Overload f64_lt = “N_compare (Lt w64)”
Overload f64_gt = “N_compare (Gt w64)”
Overload f64_le = “N_compare (Le w64)”
Overload f64_ge = “N_compare (Ge w64)” *)

val _ = export_theory();

