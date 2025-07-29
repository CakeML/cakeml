(*
  Notations for cake's Wasm 1.0 AST
*)
open preamble;
open wasmLangTheory;

val _ = new_theory "wasm_notations";

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
Overload i32_extend8_s    = “N_unary (Extend8s  W32)”
Overload i32_extend16_s   = “N_unary (Extend16s W32)”

Overload i64_extend8_s    = “N_unary (Extend8s  W64)”
Overload i64_extend16_s   = “N_unary (Extend16s W64)”
Overload i64_extend32_s   = “N_unary  Extend32s”
Overload i64_extend_i32_s = “N_unary (ExtendI32_   Signed)”
Overload i64_extend_i32_u = “N_unary (ExtendI32_ Unsigned)”


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


  (***************)
  (*   N Tests   *)
  (***************)

Overload i32_eqz = “N_eqz W32”
Overload i64_eqz = “N_eqz W64”

  (*********************)
  (*   N Conversions   *)
  (*********************)

Overload i32_wrap_i64        = “N_convert Wrap_i64”

val _ = export_theory();
