(*
  Mechanism for adding runtime type checking annotations, used in the Candle
  prover soundness proofs.
 *)

structure runtime_checkLib :> runtime_checkLib = struct

open HolKernel boolLib bossLib BasicProvers mlstringTheory runtime_checkTheory;

(* Runtime checks are inserted as assert_shape, which the translator turns
   into an Assert expression (see ml_translatorLib) that consumes no clock. *)

fun shape_of_type ty =
  if ty = “:mlstring” then “PrimA StrT” else
  if ty = “:type” then “ConsA (Short «Tyvar»)” else
  if ty = “:term” then “ConsA (Short «Const»)” else
  if ty = “:thm” then “ConsA (Short «Sequent»)” else
  case total listSyntax.dest_list_type ty of
    SOME ety => mk_comb (“ListA”, shape_of_type ety)
  | NONE =>
    case total pairSyntax.dest_prod ty of
      SOME (a, b) =>
        mk_comb (“TupleA”,
                 listSyntax.mk_list ([shape_of_type a, shape_of_type b],
                                     “:shape_assert”))
    | NONE => failwith ("shape_of_type: " ^ type_to_string ty)

fun assert_check [] def = SPEC_ALL def
  | assert_check (v::vs) def =
    let
      val def = assert_check vs def
      val tm = Parse.parse_in_context (free_vars (concl def)) v
      val sa = shape_of_type (type_of tm)
      val chk = “ml_translator$assert_shape ^sa ^tm”
    in MATCH_MP pure_seq_intro def |> ISPEC chk end

end

