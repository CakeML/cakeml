(*
  Notations for cake's Wasm AST
*)
open preamble;
open wasmLangTheory;

val _ = new_theory "wasmNotations";

(*********************)
(*                   *)
(*     Notations     *)
(*                   *)
(*********************)
  (* NB: This was done manually & is therefore error prone *)
  (* Rationale:
      1) These notations serve as a sanity check as
        a) they have to be type checked before they can be overloaded
        b) the (overloaded? what is the HOL jargon for this?) notation is easier to compare against the text spec than the AST is

      2) Obviously it's nicer to write with the notations than the HOL object level AST

      NB: don't forget that we still have to pattern match against the AST -- no using notations there *)


(****************)
(*   Numerics   *)
(****************)

  (****************)
  (*   N Consts   *)
  (****************)

      (* these are incomplete instructions, they are of type word32/64 -> num_instr*)
Overload i32_const = “N_const32 Int”
Overload i64_const = “N_const64 Int”
Overload f32_const = “N_const32 Float”
Overload f64_const = “N_const64 Float”

  (*****************)
  (*   N Unaries   *)
  (*****************)

    (* ints *)
Overload i32_clz    = “N_unary (Clz    W32)”
Overload i32_ctz    = “N_unary (Ctz    W32)”
Overload i32_popcnt = “N_unary (Popcnt W32)”

Overload i64_clz    = “N_unary (Clz    W64)”
Overload i64_ctz    = “N_unary (Ctz    W64)”
Overload i64_popcnt = “N_unary (Popcnt W64)”

    (* extends *)
Overload i32_extend8_s    = “N_unary (Extend8_s  W32)”
Overload i32_extend16_s   = “N_unary (Extend16_s W32)”

Overload i64_extend8_s    = “N_unary (Extend8_s  W64)”
Overload i64_extend16_s   = “N_unary (Extend16_s W64)”

Overload i64_extend32_s   = “N_unary  Extend32_s”
Overload i64_extend_i32_u = “N_unary (Extend_i32_ Unsigned)”
Overload i64_extend_i32_s = “N_unary (Extend_i32_   Signed)”

    (* floats *)
Overload f32_abs     = “N_unary (Abs     W32)”
Overload f32_neg     = “N_unary (Neg     W32)”
Overload f32_sqrt    = “N_unary (Sqrt    W32)”
Overload f32_ceil    = “N_unary (Ceil    W32)”
Overload f32_floor   = “N_unary (Floor   W32)”
Overload f32_trunc   = “N_unary (Trunc   W32)”
Overload f32_nearest = “N_unary (Nearest W32)”

Overload f64_abs     = “N_unary (Abs     W64)”
Overload f64_neg     = “N_unary (Neg     W64)”
Overload f64_sqrt    = “N_unary (Sqrt    W64)”
Overload f64_ceil    = “N_unary (Ceil    W64)”
Overload f64_floor   = “N_unary (Floor   W64)”
Overload f64_trunc   = “N_unary (Trunc   W64)”
Overload f64_nearest = “N_unary (Nearest W64)”

  (******************)
  (*   N Binaries   *)
  (******************)

    (* ints *)
Overload i32_add = “N_binary (Add Int W32)”
Overload i32_sub = “N_binary (Sub Int W32)”
Overload i32_mul = “N_binary (Mul Int W32)”

Overload i64_add = “N_binary (Add Int W64)”
Overload i64_sub = “N_binary (Sub Int W64)”
Overload i64_mul = “N_binary (Mul Int W64)”

Overload i32_div_u  = “N_binary (Div_ Unsigned W32)”
Overload i32_div_s  = “N_binary (Div_   Signed W32)”
Overload i32_rem_u  = “N_binary (Rem_ Unsigned W32)”
Overload i32_rem_s  = “N_binary (Rem_   Signed W32)”
Overload i32_and    = “N_binary (And           W32)”
Overload i32_or     = “N_binary (Or            W32)”
Overload i32_xor    = “N_binary (Xor           W32)”
Overload i32_shl    = “N_binary (Shl           W32)”
Overload i32_shr_u  = “N_binary (Shr_ Unsigned W32)”
Overload i32_shr_s  = “N_binary (Shr_   Signed W32)”
Overload i32_rotl   = “N_binary (Rotl          W32)”
Overload i32_rotr   = “N_binary (Rotr          W32)”

Overload i64_div_u  = “N_binary (Div_ Unsigned W64)”
Overload i64_div_s  = “N_binary (Div_   Signed W64)”
Overload i64_rem_u  = “N_binary (Rem_ Unsigned W64)”
Overload i64_rem_s  = “N_binary (Rem_   Signed W64)”
Overload i64_and    = “N_binary (And           W64)”
Overload i64_or     = “N_binary (Or            W64)”
Overload i64_xor    = “N_binary (Xor           W64)”
Overload i64_shl    = “N_binary (Shl           W64)”
Overload i64_shr_u  = “N_binary (Shr_ Unsigned W64)”
Overload i64_shr_s  = “N_binary (Shr_   Signed W64)”
Overload i64_rotl   = “N_binary (Rotl          W64)”
Overload i64_rotr   = “N_binary (Rotr          W64)”

    (* floats *)
Overload f32_add = “N_binary (Add Float W32)”
Overload f32_sub = “N_binary (Sub Float W32)”
Overload f32_mul = “N_binary (Mul Float W32)”

Overload f64_add = “N_binary (Add Float W64)”
Overload f64_sub = “N_binary (Sub Float W64)”
Overload f64_mul = “N_binary (Mul Float W64)”


Overload f32_div      = “N_binary (Div      W32)”
Overload f32_min      = “N_binary (Min      W32)”
Overload f32_max      = “N_binary (Max      W32)”
Overload f32_copysign = “N_binary (Copysign W32)”

Overload f64_div      = “N_binary (Div      W64)”
Overload f64_min      = “N_binary (Min      W64)”
Overload f64_max      = “N_binary (Max      W64)”
Overload f64_copysign = “N_binary (Copysign W64)”


  (*********************)
  (*   N Comparisons   *)
  (*********************)

    (* ints *)
Overload i32_eq    = “N_compare (Eq Int W32)”
Overload i64_eq    = “N_compare (Eq Int W64)”

Overload i32_ne    = “N_compare (Ne Int W32)”
Overload i64_ne    = “N_compare (Ne Int W64)”

Overload i32_lt_s  = “N_compare (Lt_   Signed W32)”
Overload i32_lt_u  = “N_compare (Lt_ Unsigned W32)”
Overload i64_lt_s  = “N_compare (Lt_   Signed W64)”
Overload i64_lt_u  = “N_compare (Lt_ Unsigned W64)”

Overload i32_gt_s  = “N_compare (Gt_   Signed W32)”
Overload i32_gt_u  = “N_compare (Gt_ Unsigned W32)”
Overload i64_gt_s  = “N_compare (Gt_   Signed W64)”
Overload i64_gt_u  = “N_compare (Gt_ Unsigned W64)”

Overload i32_le_s  = “N_compare (Le_   Signed W32)”
Overload i32_le_u  = “N_compare (Le_ Unsigned W32)”
Overload i64_le_s  = “N_compare (Le_   Signed W64)”
Overload i64_le_u  = “N_compare (Le_ Unsigned W64)”

Overload i32_ge_s  = “N_compare (Ge_   Signed W32)”
Overload i32_ge_u  = “N_compare (Ge_ Unsigned W32)”
Overload i64_ge_s  = “N_compare (Ge_   Signed W64)”
Overload i64_ge_u  = “N_compare (Ge_ Unsigned W64)”

    (* floats *)
Overload f32_eq = “N_compare (Eq Float W32)”
Overload f32_ne = “N_compare (Ne Float W32)”

Overload f64_eq = “N_compare (Eq Float W64)”
Overload f64_ne = “N_compare (Ne Float W64)”

Overload f32_lt = “N_compare (Lt W32)”
Overload f32_gt = “N_compare (Gt W32)”
Overload f32_le = “N_compare (Le W32)”
Overload f32_ge = “N_compare (Ge W32)”

Overload f64_lt = “N_compare (Lt W64)”
Overload f64_gt = “N_compare (Gt W64)”
Overload f64_le = “N_compare (Le W64)”
Overload f64_ge = “N_compare (Ge W64)”


  (***************)
  (*   N Tests   *)
  (***************)

Overload i32_eqz = “N_test (Eqz W32)”
Overload i64_eqz = “N_test (Eqz W64)”


  (*********************)
  (*   N Conversions   *)
  (*********************)

Overload i32_wrap_i64        = “N_convert Wrap_i64”

Overload i32_trunc_f32_s     = “N_convert (Trunc_f W32   Signed W32)”
Overload i32_trunc_f32_u     = “N_convert (Trunc_f W32 Unsigned W32)”
Overload i32_trunc_f64_s     = “N_convert (Trunc_f W64   Signed W32)”
Overload i32_trunc_f64_u     = “N_convert (Trunc_f W64 Unsigned W32)”
Overload i64_trunc_f32_s     = “N_convert (Trunc_f W32   Signed W64)”
Overload i64_trunc_f32_u     = “N_convert (Trunc_f W32 Unsigned W64)”
Overload i64_trunc_f64_s     = “N_convert (Trunc_f W64   Signed W64)”
Overload i64_trunc_f64_u     = “N_convert (Trunc_f W64 Unsigned W64)”

Overload i32_trunc_sat_f32_s = “N_convert (Trunc_sat_f W32   Signed W32)”
Overload i32_trunc_sat_f32_u = “N_convert (Trunc_sat_f W32 Unsigned W32)”
Overload i32_trunc_sat_f64_s = “N_convert (Trunc_sat_f W64   Signed W32)”
Overload i32_trunc_sat_f64_u = “N_convert (Trunc_sat_f W64 Unsigned W32)”
Overload i64_trunc_sat_f32_s = “N_convert (Trunc_sat_f W32   Signed W64)”
Overload i64_trunc_sat_f32_u = “N_convert (Trunc_sat_f W32 Unsigned W64)”
Overload i64_trunc_sat_f64_s = “N_convert (Trunc_sat_f W64   Signed W64)”
Overload i64_trunc_sat_f64_u = “N_convert (Trunc_sat_f W64 Unsigned W64)”

Overload f32_demote_f64      = “N_convert  Demote ”

Overload f64_promote_f32     = “N_convert  Promote”

Overload f32_convert_i32_s   = “N_convert (Convert W32   Signed W32)”
Overload f32_convert_i64_s   = “N_convert (Convert W64   Signed W32)”
Overload f32_convert_i32_u   = “N_convert (Convert W32 Unsigned W32)”
Overload f32_convert_i64_u   = “N_convert (Convert W64 Unsigned W32)”
Overload f64_convert_i32_s   = “N_convert (Convert W32   Signed W64)”
Overload f64_convert_i64_s   = “N_convert (Convert W64   Signed W64)”
Overload f64_convert_i32_u   = “N_convert (Convert W32 Unsigned W64)”
Overload f64_convert_i64_u   = “N_convert (Convert W64 Unsigned W64)”

Overload i32_reinterpret_f32 = “N_convert (Reinterpret_f W32)”
Overload i64_reinterpret_f64 = “N_convert (Reinterpret_f W64)”

Overload f32_reinterpret_i32 = “N_convert (Reinterpret_i W32)”
Overload f64_reinterpret_i64 = “N_convert (Reinterpret_i W64)”
(***************)
(*   Vectors   *)
(***************)

Overload t8x16 = “Is2 I8x16” (* : ishap3 *)
Overload t16x8 = “Is2 I16x8” (* : ishap3 *)

Overload e8x16 = “Is3 (Is2 I8x16)” (* : ishape *)
Overload e16x8 = “Is3 (Is2 I16x8)” (* : ishape *)
Overload e32x4 = “Is3 I32x4”       (* : ishape *)

Overload i8x16 = “IShp (Is3 (Is2 I8x16))” (* : shape *)
Overload i16x8 = “IShp (Is3 (Is2 I16x8))” (* : shape *)
Overload i32x4 = “IShp (Is3 I32x4)”       (* : shape *)
Overload i64x2 = “IShp I64x2”             (* : shape *)
Overload f32x4 = “FShp F32x4”             (* : shape *)
Overload f64x2 = “FShp F64x2”             (* : shape *)

  (****************)
  (*   V Consts   *)
  (****************)

Overload v128_const = “V_const”

  (*****************)
  (*   V Unaries   *)
  (*****************)

Overload v128_const    = “V_unary  Vnot”

Overload i8x16_bitmask = “V_unary (Vbitmask e8x16)”
Overload i16x8_bitmask = “V_unary (Vbitmask e16x8)”
Overload i32x4_bitmask = “V_unary (Vbitmask e32x4)”
Overload i64x2_bitmask = “V_unary (Vbitmask I64x2)”

Overload i8x16_popcnt  = “V_unary  Vpopcnt”

Overload i8x16_abs = “V_unary (Vabs i8x16)”
Overload i16x8_abs = “V_unary (Vabs i16x8)”
Overload i32x4_abs = “V_unary (Vabs i32x4)”
Overload i64x2_abs = “V_unary (Vabs i64x2)”
Overload f32x4_abs = “V_unary (Vabs f32x4)”
Overload f64x2_abs = “V_unary (Vabs f64x2)”

Overload i8x16_neg = “V_unary (Vneg i8x16)”
Overload i16x8_neg = “V_unary (Vneg i16x8)”
Overload i32x4_neg = “V_unary (Vneg i32x4)”
Overload i64x2_neg = “V_unary (Vneg i64x2)”
Overload f32x4_neg = “V_unary (Vneg f32x4)”
Overload f64x2_neg = “V_unary (Vneg f64x2)”

Overload f32x4_sqrt    = “V_unary (Vsqrt    F32x4)”
Overload f64x2_sqrt    = “V_unary (Vsqrt    F64x2)”

Overload f32x4_ceil    = “V_unary (Vceil    F32x4)”
Overload f64x2_ceil    = “V_unary (Vceil    F64x2)”

Overload f32x4_floor   = “V_unary (Vfloor   F32x4)”
Overload f64x2_floor   = “V_unary (Vfloor   F64x2)”

Overload f32x4_trunc   = “V_unary (Vtrunc   F32x4)”
Overload f64x2_trunc   = “V_unary (Vtrunc   F64x2)”

Overload f32x4_nearest = “V_unary (Vnearest F32x4)”
Overload f64x2_nearest = “V_unary (Vnearest F64x2)”


  (******************)
  (*   V Binaries   *)
  (******************)

Overload v128_and    = “V_binary Vand”
Overload v128_andNot = “V_binary VandNot”
Overload v128_or     = “V_binary Vor”
Overload v128_xor    = “V_binary Vxor”

Overload v128_swizzle = “V_binary Vswizzle”

Overload i8x16_narrow_i16x8_s = “V_binary (Vnarrow   Signed I8x16)”
Overload i8x16_narrow_i16x8_u = “V_binary (Vnarrow Unsigned I8x16)”
Overload i16x8_narrow_i32x4_s = “V_binary (Vnarrow   Signed I16x8)”
Overload i16x8_narrow_i32x4_u = “V_binary (Vnarrow Unsigned I16x8)”

Overload v128_dot = “V_binary Vdot”

Overload i8x16_add = “V_binary (Vadd i8x16)”
Overload i16x8_add = “V_binary (Vadd i16x8)”
Overload i32x4_add = “V_binary (Vadd i32x4)”
Overload i64x2_add = “V_binary (Vadd i64x2)”
Overload f32x4_add = “V_binary (Vadd f32x4)”
Overload f64x2_add = “V_binary (Vadd f64x2)”

Overload i8x16_sub = “V_binary (Vsub i8x16)”
Overload i16x8_sub = “V_binary (Vsub i16x8)”
Overload i32x4_sub = “V_binary (Vsub i32x4)”
Overload i64x2_sub = “V_binary (Vsub i64x2)”
Overload f32x4_sub = “V_binary (Vsub f32x4)”
Overload f64x2_sub = “V_binary (Vsub f64x2)”

Overload i8x16_mul = “V_binary (Vmul i8x16)”
Overload i16x8_mul = “V_binary (Vmul i16x8)”
Overload i32x4_mul = “V_binary (Vmul i32x4)”
Overload i64x2_mul = “V_binary (Vmul i64x2)”
Overload f32x4_mul = “V_binary (Vmul f32x4)”
Overload f64x2_mul = “V_binary (Vmul f64x2)”

Overload i8x16_min_s = “V_binary (Vmin_   Signed t8x16)”
Overload i8x16_min_u = “V_binary (Vmin_ Unsigned t8x16)”
Overload i16x8_min_s = “V_binary (Vmin_   Signed t16x8)”
Overload i16x8_min_u = “V_binary (Vmin_ Unsigned t16x8)”
Overload i32x4_min_s = “V_binary (Vmin_   Signed I32x4)”
Overload i32x4_min_u = “V_binary (Vmin_ Unsigned I32x4)”

Overload i8x16_max_s = “V_binary (Vmax_   Signed (Is2 I8x16))”
Overload i8x16_max_u = “V_binary (Vmax_ Unsigned (Is2 I8x16))”
Overload i16x8_max_s = “V_binary (Vmax_   Signed (Is2 I16x8))”
Overload i16x8_max_u = “V_binary (Vmax_ Unsigned (Is2 I16x8))”
Overload i32x4_max_s = “V_binary (Vmax_   Signed I32x4)”
Overload i32x4_max_u = “V_binary (Vmax_ Unsigned I32x4)”

Overload i8x16_add_sat_s = “V_binary (Vadd_sat_   Signed I8x16)”
Overload i8x16_add_sat_u = “V_binary (Vadd_sat_ Unsigned I8x16)”
Overload i16x8_add_sat_s = “V_binary (Vadd_sat_   Signed I16x8)”
Overload i16x8_add_sat_u = “V_binary (Vadd_sat_ Unsigned I16x8)”

Overload i8x16_sub_sat_s = “V_binary (Vsub_sat_   Signed I8x16)”
Overload i8x16_sub_sat_u = “V_binary (Vsub_sat_ Unsigned I8x16)”
Overload i16x8_sub_sat_s = “V_binary (Vsub_sat_   Signed I16x8)”
Overload i16x8_sub_sat_u = “V_binary (Vsub_sat_ Unsigned I16x8)”

Overload i8x16_avgr_u = “V_binary (Vavgr_u I8x16)”
Overload i16x8_avgr_u = “V_binary (Vavgr_u I16x8)”

Overload f32x4_div  = “V_binary (Vdiv  F32x4)”
Overload f64x2_div  = “V_binary (Vdiv  F64x2)”

Overload f32x4_min  = “V_binary (Vmin  F32x4)”
Overload f64x2_min  = “V_binary (Vmin  F64x2)”

Overload f32x4_max  = “V_binary (Vmax  F32x4)”
Overload f64x2_max  = “V_binary (Vmax  F64x2)”

Overload f32x4_pmin = “V_binary (Vpmin F32x4)”
Overload f64x2_pmin = “V_binary (Vpmin F64x2)”

Overload f32x4_pmax = “V_binary (Vpmax F32x4)”
Overload f64x2_pmax = “V_binary (Vpmax F64x2)”

  (*******************)
  (*   V Ternaries   *)
  (*******************)

Overload v128_const = “V_ternary VbitSelect”

  (*********************)
  (*   V Comparisons   *)
  (*********************)

Overload i8x16_eq = “V_compare (Veq i8x16)”
Overload i16x8_eq = “V_compare (Veq i16x8)”
Overload i32x4_eq = “V_compare (Veq i32x4)”
Overload i64x2_eq = “V_compare (Veq i64x2)”
Overload f32x4_eq = “V_compare (Veq f32x4)”
Overload f64x2_eq = “V_compare (Veq f64x2)”

Overload i8x16_ne = “V_compare (Vne i8x16)”
Overload i16x8_ne = “V_compare (Vne i16x8)”
Overload i32x4_ne = “V_compare (Vne i32x4)”
Overload i64x2_ne = “V_compare (Vne i64x2)”
Overload f32x4_ne = “V_compare (Vne f32x4)”
Overload f64x2_ne = “V_compare (Vne f64x2)”

Overload i8x16_lt_s = “V_compare (Vlt_   Signed t8x16)”
Overload i8x16_lt_u = “V_compare (Vlt_ Unsigned t8x16)”
Overload i16x8_lt_s = “V_compare (Vlt_   Signed t16x8)”
Overload i16x8_lt_u = “V_compare (Vlt_ Unsigned t16x8)”
Overload i32x4_lt_s = “V_compare (Vlt_   Signed I32x4)”
Overload i32x4_lt_u = “V_compare (Vlt_ Unsigned I32x4)”

Overload i8x16_gt_s = “V_compare (Vgt_   Signed t8x16)”
Overload i8x16_gt_u = “V_compare (Vgt_ Unsigned t8x16)”
Overload i16x8_gt_s = “V_compare (Vgt_   Signed t16x8)”
Overload i16x8_gt_u = “V_compare (Vgt_ Unsigned t16x8)”
Overload i32x4_gt_s = “V_compare (Vgt_   Signed I32x4)”
Overload i32x4_gt_u = “V_compare (Vgt_ Unsigned I32x4)”

Overload i8x16_le_s = “V_compare (Vle_   Signed tI8x16)”
Overload i8x16_le_u = “V_compare (Vle_ Unsigned tI8x16)”
Overload i16x8_le_s = “V_compare (Vle_   Signed tI16x8)”
Overload i16x8_le_u = “V_compare (Vle_ Unsigned tI16x8)”
Overload i32x4_le_s = “V_compare (Vle_   Signed I32x4)”
Overload i32x4_le_u = “V_compare (Vle_ Unsigned I32x4)”

Overload i8x16_ge_s = “V_compare (Vge_   Signed t8x16)”
Overload i8x16_ge_u = “V_compare (Vge_ Unsigned t8x16)”
Overload i16x8_ge_s = “V_compare (Vge_   Signed t16x8)”
Overload i16x8_ge_u = “V_compare (Vge_ Unsigned t16x8)”
Overload i32x4_ge_s = “V_compare (Vge_   Signed I32x4)”
Overload i32x4_ge_u = “V_compare (Vge_ Unsigned I32x4)”

Overload i64x2_lt_s = “V_compare Vlt_s”
Overload i64x2_gt_s = “V_compare Vgt_s”
Overload i64x2_le_s = “V_compare Vle_s”
Overload i64x2_ge_s = “V_compare Vge_s”

Overload f32x4_lt = “V_compare (Vlt F32x4)”
Overload f64x2_lt = “V_compare (Vlt F64x2)”

Overload f32x4_gt = “V_compare (Vgt F32x4)”
Overload f64x2_gt = “V_compare (Vgt F64x2)”

Overload f32x4_le = “V_compare (Vle F32x4)”
Overload f64x2_le = “V_compare (Vle F64x2)”

Overload f32x4_ge = “V_compare (Vge F32x4)”
Overload f64x2_ge = “V_compare (Vge F64x2)”


  (***************)
  (*   V Tests   *)
  (***************)

Overload v128_any_true = “V_test VanyTrue”

Overload i8x16_all_true = “V_test (VallTrue e8x16)”
Overload i16x8_all_true = “V_test (VallTrue e16x8)”
Overload i32x4_all_true = “V_test (VallTrue e32x4)”
Overload i64x2_all_true = “V_test (VallTrue I64x2)”


  (****************)
  (*   V Shifts   *)
  (****************)

Overload i8x16_shl = “V_shift (Vshl e8x16)”
Overload i16x8_shl = “V_shift (Vshl e16x8)”
Overload i32x4_shl = “V_shift (Vshl e32x4)”
Overload i64x2_shl = “V_shift (Vshl I64x2)”

Overload i8x16_shr_s = “V_shift (Vshr_   Signed e8x16)”
Overload i8x16_shr_u = “V_shift (Vshr_ Unsigned e8x16)”
Overload i16x8_shr_s = “V_shift (Vshr_   Signed e16x8)”
Overload i16x8_shr_u = “V_shift (Vshr_ Unsigned e16x8)”
Overload i32x4_shr_s = “V_shift (Vshr_   Signed e32x4)”
Overload i32x4_shr_u = “V_shift (Vshr_ Unsigned e32x4)”
Overload i64x2_shr_s = “V_shift (Vshr_   Signed I64x2)”
Overload i64x2_shr_u = “V_shift (Vshr_ Unsigned I64x2)”


  (*********************)
  (*   V Conversions   *)
  (*********************)

Overload i16x8_extend_high_i8x16_s = “V_convert (Vextend  High  t8x16    Signed)”
Overload i16x8_extend_low_i8x16_s  = “V_convert (Vextend   Low  t8x16    Signed)”
Overload i16x8_extend_high_i8x16_u = “V_convert (Vextend  High  t8x16  Unsigned)”
Overload i16x8_extend_low_i8x16_u  = “V_convert (Vextend   Low  t8x16  Unsigned)”
Overload i32x4_extend_high_i16x8_s = “V_convert (Vextend  High  t16x8    Signed)”
Overload i32x4_extend_low_i16x8_s  = “V_convert (Vextend   Low  t16x8    Signed)”
Overload i32x4_extend_high_i16x8_u = “V_convert (Vextend  High  t16x8  Unsigned)”
Overload i32x4_extend_low_i16x8_u  = “V_convert (Vextend   Low  t16x8  Unsigned)”
Overload i64x2_extend_high_i32x4_s = “V_convert (Vextend  High  I32x4    Signed)”
Overload i64x2_extend_low_i32x4_s  = “V_convert (Vextend   Low  I32x4    Signed)”
Overload i64x2_extend_high_i32x4_u = “V_convert (Vextend  High  I32x4  Unsigned)”
Overload i64x2_extend_low_i32x4_u  = “V_convert (Vextend   Low  I32x4  Unsigned)”

Overload i16x8_extmul_high_i8x16_s = “V_convert (VextMul  High  t8x16    Signed)”
Overload i16x8_extmul_low_i8x16_s  = “V_convert (VextMul   Low  t8x16    Signed)”
Overload i16x8_extmul_high_i8x16_u = “V_convert (VextMul  High  t8x16  Unsigned)”
Overload i16x8_extmul_low_i8x16_u  = “V_convert (VextMul   Low  t8x16  Unsigned)”
Overload i32x4_extmul_high_i16x8_s = “V_convert (VextMul  High  t16x8    Signed)”
Overload i32x4_extmul_low_i16x8_s  = “V_convert (VextMul   Low  t16x8    Signed)”
Overload i32x4_extmul_high_i16x8_u = “V_convert (VextMul  High  t16x8  Unsigned)”
Overload i32x4_extmul_low_i16x8_u  = “V_convert (VextMul   Low  t16x8  Unsigned)”
Overload i64x2_extmul_high_i32x4_s = “V_convert (VextMul  High  I32x4    Signed)”
Overload i64x2_extmul_low_i32x4_s  = “V_convert (VextMul   Low  I32x4    Signed)”
Overload i64x2_extmul_high_i32x4_u = “V_convert (VextMul  High  I32x4  Unsigned)”
Overload i64x2_extmul_low_i32x4_u  = “V_convert (VextMul   Low  I32x4  Unsigned)”

Overload i16x8_extadd_pairwise_i8x16_s = “V_convert (VextAdd I8x16   Signed)”
Overload i16x8_extadd_pairwise_i8x16_u = “V_convert (VextAdd I8x16 Unsigned)”
Overload i32x4_extadd_pairwise_i16x8_s = “V_convert (VextAdd I16x8   Signed)”
Overload i32x4_extadd_pairwise_i16x8_u = “V_convert (VextAdd I16x8 Unsigned)”

Overload i32x4_trunc_sat_f32x4_s = “V_convert (VtruncSat   Signed)”
Overload i32x4_trunc_sat_f32x4_u = “V_convert (VtruncSat Unsigned)”

Overload  i32x4_trunc_sat_f64x2_s_zero = “V_convert (VtruncSat0   Signed)”
Overload  i32x4_trunc_sat_f64x2_u_zero = “V_convert (VtruncSat0 Unsigned)”

Overload f32x4_convert_i32x4_s     = “V_convert (Vconvert High   Signed)”
Overload f32x4_convert_i32x4_u     = “V_convert (Vconvert High Unsigned)”
Overload f64x2_convert_low_i32x4_s = “V_convert (Vconvert  Low   Signed)”
Overload f64x2_convert_low_i32x4_u = “V_convert (Vconvert  Low Unsigned)”

Overload f32x4_demote_f64x2_zero = “V_convert Vdemote”

Overload f64x2_promote_low_f32x4 = “V_convert Vpromote”


  (****************)
  (*   V Splats   *)
  (****************)

Overload i8x16_splat = “V_splat i8x16”
Overload i16x8_splat = “V_splat i16x8”
Overload i32x4_splat = “V_splat i32x4”
Overload I64x2_splat = “V_splat i64x2”
Overload f32x4_splat = “V_splat f32x4”
Overload f64x2_splat = “V_splat f64x2”


  (***************)
  (*   V Lanes   *)
  (***************)

Overload i8x16_extractLane_s = “V_lane (Vextract_   Signed I8x16)”
Overload i8x16_extractLane_u = “V_lane (Vextract_ Unsigned I8x16)”
Overload i16x8_extractLane_s = “V_lane (Vextract_   Signed I16x8)”
Overload i16x8_extractLane_u = “V_lane (Vextract_ Unsigned I16x8)”

Overload i32x4_extractLane   = “V_lane  VextractI32x4”
Overload i64x2_extractLane   = “V_lane  VextractI64x2”

Overload f32x4_extractLane   = “V_lane (VextractF F32x4)”
Overload f64x2_extractLane   = “V_lane (VextractF F64x2)”

Overload i8x16_replaceLane = “V_lane (Vreplace i8x16)”
Overload i16x8_replaceLane = “V_lane (Vreplace i16x8)”
Overload i32x4_replaceLane = “V_lane (Vreplace i32x4)”
Overload i64x2_replaceLane = “V_lane (Vreplace i64x2)”
Overload f32x4_replaceLane = “V_lane (Vreplace f32x4)”
Overload f64x2_replaceLane = “V_lane (Vreplace f64x2)”

Overload v128_shuffle = “V_lane Vshuffle”

val _ = export_theory();
