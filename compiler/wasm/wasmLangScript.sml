(*
  WebAssembly (Wasm) syntax
*)
open preamble;

val _ = new_theory "wasmLang";

Datatype: bvtype (* bit vector type (Does anyone have a better name? *)
  = Int
  | Float
End

Datatype: width
  = w32
  | w64
End

(* Doing it this way allows us to -- for exmaple -- later limit things
to just "Int", which we couldn't do if iNN and fNN were all in the same datatype *)
Datatype: numtype
  = NT bvtype width
End

Overload i32 = ``NT Int   w32``
Overload i64 = ``NT Int   w64``
Overload f32 = ``NT Float w32``
Overload f64 = ``NT Float w64``

Datatype: sign
  = Signed
  | Unsgnd
End

(********************************************************)
(*   unary (+ binary,test,comparison&conversion) ops.   *)
(********************************************************)

(* Ctrl-f "Notations" to see some examples *)

Datatype: uop

  (* int ops *)
  = (* inn *) Clz         width
  | (* inn *) Ctz         width
  | (* inn *) Popcnt      width
  | (* inn *) Extend8_s   width
  | (* inn *) Extend16_s  width
  | (* i64 *) Extend32_s
  | (* i64 *) Extend_i32_ sign

  (* float ops
  | (* fnn *) Abs     width
  | (* fnn *) Neg     width
  | (* fnn *) Sqrt    width
  | (* fnn *) Ceil    width
  | (* fnn *) Floor   width
  | (* fnn *) Trunc   width
  | (* fnn *) Nearest width
  *)
End

Datatype: bop

  (* both int and/or float -- given by {bvtype} *)
  = (* all *) Add bvtype width
  | (* all *) Sub bvtype width
  | (* all *) Mul bvtype width

  (* int *)
  | (* inn *) Div_ sign   width
  | (* inn *) Rem_ sign   width
  | (* inn *) And         width
  | (* inn *) Or          width
  | (* inn *) Xor         width
  | (* inn *) Shl         width
  | (* inn *) Shr_ sign   width
  | (* inn *) Rotl        width
  | (* inn *) Rotr        width

  (* float *)
  (*
  | (* fnn *) Div         width
  | (* fnn *) Min         width
  | (* fnn *) Max         width
  | (* fnn *) Copysign    width
  *)
End

Datatype: cmpop

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
Datatype: testop
  = (* inn *) Eqz width
  (* | *)

End

Datatype: cvtop (* cvt := convert *)
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
  = (* all *) I32Const word32
  | (* all *) I64Const word64
  | (* all *) Uny    uop
  | (* all *) Bny    bop
  | (* inn *) Tst testop
  | (* all *) Cmp  cmpop
  | (* all *) Cvt  cvtop
End

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
  | Instr num_instr
  | ReturnCall num (* TODO: tail call *)
  | ReturnCallIndirect num tf (* TODO: input/output params, names *)
End


(*********************)
(*                   *)
(*     Notations     *)
(*                   *)
(*********************)
(* This was done manually & therefore is error prone *)


(***************)
(*   Unaries   *)
(***************)

(* ints *)
Overload i32_clz    = “Uny (Clz    w32)”
Overload i32_ctz    = “Uny (Ctz    w32)”
Overload i32_popcnt = “Uny (Popcnt w32)”

Overload i64_clz    = “Uny (Clz    w64)”
Overload i64_ctz    = “Uny (Ctz    w64)”
Overload i64_popcnt = “Uny (Popcnt w64)”

(* extends *)
Overload i32_Extend8_s    = “Uny (Extend8_s  w32)”
Overload i32_Extend16_s   = “Uny (Extend16_s w32)”

Overload i64_Extend8_s    = “Uny (Extend8_s  w64)”
Overload i64_Extend16_s   = “Uny (Extend16_s w64)”

Overload i64_Extend32_s   = “Uny  Extend32_s”
Overload i64_Extend_i32_u = “Uny (Extend_i32_ Unsgnd)”
Overload i64_Extend_i32_s = “Uny (Extend_i32_ Signed)”

(* floats *)
Overload f32_abs     = “Uny (Abs     w32)”
Overload f32_neg     = “Uny (Neg     w32)”
Overload f32_sqrt    = “Uny (Sqrt    w32)”
Overload f32_ceil    = “Uny (Ceil    w32)”
Overload f32_floor   = “Uny (Floor   w32)”
Overload f32_trunc   = “Uny (Trunc   w32)”
Overload f32_nearest = “Uny (Nearest w32)”

Overload f64_abs     = “Uny (Abs     w64)”
Overload f64_neg     = “Uny (Neg     w64)”
Overload f64_sqrt    = “Uny (Sqrt    w64)”
Overload f64_ceil    = “Uny (Ceil    w64)”
Overload f64_floor   = “Uny (Floor   w64)”
Overload f64_trunc   = “Uny (Trunc   w64)”
Overload f64_nearest = “Uny (Nearest w64)”

(****************)
(*   Binaries   *)
(****************)

(* ints *)
Overload i32_add = “Bny (Add Int w32)”
Overload i32_sub = “Bny (Sub Int w32)”
Overload i32_mul = “Bny (Mul Int w32)”

Overload i64_add = “Bny (Add Int w64)”
Overload i64_sub = “Bny (Sub Int w64)”
Overload i64_mul = “Bny (Mul Int w64)”

Overload i32_div_u  = “Bny (Div_ Unsgnd w32)”
Overload i32_div_s  = “Bny (Div_ Signed w32)”
Overload i32_rem_u  = “Bny (Rem_ Unsgnd w32)”
Overload i32_rem_s  = “Bny (Rem_ Signed w32)”
Overload i32_and    = “Bny (And         w32)”
Overload i32_or     = “Bny (Or          w32)”
Overload i32_xor    = “Bny (Xor         w32)”
Overload i32_shl    = “Bny (Shl         w32)”
Overload i32_shr_u  = “Bny (Shr_ Unsgnd w32)”
Overload i32_shr_s  = “Bny (Shr_ Signed w32)”
Overload i32_rotl   = “Bny (Rotl        w32)”
Overload i32_rotr   = “Bny (Rotr        w32)”

Overload i64_div_u  = “Bny (Div_ Unsgnd w64)”
Overload i64_div_s  = “Bny (Div_ Signed w64)”
Overload i64_rem_u  = “Bny (Rem_ Unsgnd w64)”
Overload i64_rem_s  = “Bny (Rem_ Signed w64)”
Overload i64_and    = “Bny (And         w64)”
Overload i64_or     = “Bny (Or          w64)”
Overload i64_xor    = “Bny (Xor         w64)”
Overload i64_shl    = “Bny (Shl         w64)”
Overload i64_shr_u  = “Bny (Shr_ Unsgnd w64)”
Overload i64_shr_s  = “Bny (Shr_ Signed w64)”
Overload i64_rotl   = “Bny (Rotl        w64)”
Overload i64_rotr   = “Bny (Rotr        w64)”

(* floats *)
Overload f32_add = “Bny (Add Float w32)”
Overload f32_sub = “Bny (Sub Float w32)”
Overload f32_mul = “Bny (Mul Float w32)”

Overload f64_add = “Bny (Add Float w64)”
Overload f64_sub = “Bny (Sub Float w64)”
Overload f64_mul = “Bny (Mul Float w64)”

Overload f32_div      = “Bny (Div      Float w32)”
Overload f32_min      = “Bny (Min      Float w32)”
Overload f32_max      = “Bny (Max      Float w32)”
Overload f32_copysign = “Bny (Copysign Float w32)”

Overload f64_div      = “Bny (Div      Float w64)”
Overload f64_min      = “Bny (Min      Float w64)”
Overload f64_max      = “Bny (Max      Float w64)”
Overload f64_copysign = “Bny (Copysign Float w64)”

(*******************)
(*   Comparisons   *)
(*******************)

(* ints *)
Overload i32_eq    = “Cmp (Eq  Int    w32)”
Overload i32_ne    = “Cmp (Ne  Int    w32)”
Overload i32_lt_u  = “Cmp (Lt_ Unsgnd w32)”
Overload i32_lt_s  = “Cmp (Lt_ Signed w32)”
Overload i32_gt_u  = “Cmp (Gt_ Unsgnd w32)”
Overload i32_gt_s  = “Cmp (Gt_ Signed w32)”
Overload i32_le_u  = “Cmp (Le_ Unsgnd w32)”
Overload i32_le_s  = “Cmp (Le_ Signed w32)”
Overload i32_ge_u  = “Cmp (Ge_ Unsgnd w32)”
Overload i32_ge_s  = “Cmp (Ge_ Signed w32)”

Overload i64_eq    = “Cmp (Eq  Int w64)”
Overload i64_ne    = “Cmp (Ne  Int w64)”
Overload i64_lt_u  = “Cmp (Lt_ Unsgnd w64)”
Overload i64_lt_s  = “Cmp (Lt_ Signed w64)”
Overload i64_gt_u  = “Cmp (Gt_ Unsgnd w64)”
Overload i64_gt_s  = “Cmp (Gt_ Signed w64)”
Overload i64_le_u  = “Cmp (Le_ Unsgnd w64)”
Overload i64_le_s  = “Cmp (Le_ Signed w64)”
Overload i64_ge_u  = “Cmp (Ge_ Unsgnd w64)”
Overload i64_ge_s  = “Cmp (Ge_ Signed w64)”

(* floats *)
Overload f32_eq = “Cmp (Eq Float w32)”
Overload f32_ne = “Cmp (Ne Float w32)”

Overload f64_eq = “Cmp (Eq Float w64)”
Overload f64_ne = “Cmp (Ne Float w64)”

Overload f32_lt = “Cmp (Lt w32)”
Overload f32_gt = “Cmp (Gt w32)”
Overload f32_le = “Cmp (Le w32)”
Overload f32_ge = “Cmp (Ge w32)”

Overload f64_lt = “Cmp (Lt w64)”
Overload f64_gt = “Cmp (Gt w64)”
Overload f64_le = “Cmp (Le w64)”
Overload f64_ge = “Cmp (Ge w64)”

val _ = export_theory();
