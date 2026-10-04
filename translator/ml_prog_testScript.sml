(*
  Tests for constructing declarations from oracle-independent expressions.
*)
Theory ml_prog_test
Ancestors
  ml_prog evaluateProps ast semanticPrimitives namespace
Libs
  preamble ml_progLib

val arithmetic =
  add_dec
    “Dlet NoLocs (Pvar «answer»)
       (App (Arith Add IntT) [Lit (IntLit 40); Lit (IntLit 2)])”
    I init_state;

Theorem arithmetic_value =
  EVAL “nsLookup ^(get_env arithmetic).v (Short «answer») =
        SOME (Litv (IntLit 42))” |> EQT_ELIM;

val tuple =
  add_dec
    “Dlet NoLocs (Pvar «pair»)
       (Con NONE [Ident (Short «answer»); Lit (IntLit 7)])”
    I arithmetic;

Theorem constructor_value =
  EVAL “nsLookup ^(get_env tuple).v (Short «pair») =
        SOME (Conv NONE [Litv (IntLit 42); Litv (IntLit 7)])” |> EQT_ELIM;

val allocated =
  add_dec
    “Dlet NoLocs (Pvar «cell») (App Opref [Lit (IntLit 9)])”
    I tuple;

Theorem allocated_value =
  EVAL “nsLookup ^(get_env allocated).v (Short «cell») = SOME (Loc T 0)”
  |> EQT_ELIM;

Theorem allocated_refs =
  EVAL “^(get_state allocated).refs = [Refv (Litv (IntLit 9))]” |> EQT_ELIM;

Theorem allocated_oracle =
  EVAL “^(get_state allocated).ptr_eq_oracle =
        ^(get_state init_state).ptr_eq_oracle” |> EQT_ELIM;

val nested = open_module "Nested" allocated;
val nested = add_dec
  “Dlet NoLocs (Pvar «next»)
     (Let (SOME «x») (Lit (IntLit 1))
       (App (Arith Add IntT) [Ident (Short «answer»); Ident (Short «x»)]))”
  I nested;
val nested = close_module NONE nested;

Theorem module_value =
  EVAL “nsLookup ^(get_env nested).v (Long «Nested» (Short «next»)) =
        SOME (Litv (IntLit 43))” |> EQT_ELIM;

Theorem declarations = get_Decls_thm nested;

fun rejects reason exp =
  let
    val dec = “Dlet NoLocs (Pvar «rejected») ^exp”
    val rejected = (add_dec dec I allocated; false)
      handle HOL_ERR e => String.isSubstring reason (message_of e)
  in
    if rejected then () else failwith "add_dec accepted an unsafe expression"
  end;

val _ = List.app (rejects "does not pass no_ptr_eq")
  [“App PtrEq [Lit (IntLit 0); Lit (IntLit 0)]”,
   “If (Con (SOME (Short «True»)) []) (Lit (IntLit 1))
       (App PtrEq [Lit (IntLit 0); Lit (IntLit 0)])”,
   “App Opapp [Fun «x» (Ident (Short «x»)); Lit (IntLit 1)]”,
   “App Eval []”,
   “App (ThunkOp ForceThunk) []”];

val _ = rejects "did not evaluate to a value" “App (Arith Add IntT) []”;
