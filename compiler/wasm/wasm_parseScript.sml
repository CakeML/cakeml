(*
  WASM parser -- supports part of WASM text format
*)
open preamble;
open dafny_sexpTheory;
open wasmTheory;
open mlintTheory mlstringTheory;

val _ = new_theory "wasm_parse";

Definition parse_sexp_def:
  parse_sexp input =
    do
      toks <- lex input;
      parse toks
    od
End

Definition dest_Expr_def:
  dest_Expr (Expr xs) = SOME xs ∧
  dest_Expr _ = NONE
End

Definition get_Expr_def:
  get_Expr (Expr xs) = return xs ∧
  get_Expr _ = fail "expected Expr"
End

Definition dest_Atom_def:
  dest_Atom (Atom n) = SOME n ∧
  dest_Atom _ = NONE
End

Definition dest_named_def:
  dest_named n s =
    case dest_Expr s of
    | SOME (x::xs) => (if x = Atom n then SOME xs else NONE)
    | _ => NONE
End

Definition dest_t_def:
  dest_t (Atom n) = (if n = "i32" then SOME T_i32 else
                     if n = "i64" then SOME T_i64 else NONE) ∧
  dest_t _ = NONE
End

Definition list_dest_t_def:
  list_dest_t [] = SOME [] ∧
  list_dest_t (x::xs) =
    case dest_t x of NONE => NONE| SOME t =>
    case list_dest_t xs of NONE => NONE| SOME ts =>
      SOME (t::ts)
End

Definition dest_param_def:
  dest_param x = dest_named "param" x
End

Definition dest_params_def:
  dest_params [] = NONE ∧
  dest_params (x::xs) =
    case dest_param x of | NONE => NONE | SOME p =>
    case list_dest_t p of NONE => NONE | SOME ts =>
      SOME (ts,xs)
End

Definition dest_result_def:
  dest_result x = dest_named "result" x
End

Definition dest_results_def:
  dest_results [] = NONE ∧
  dest_results (x::xs) =
    case dest_result x of | NONE => NONE | SOME p =>
    case list_dest_t p of NONE => NONE | SOME ts =>
      SOME (ts,xs)
End

Definition dest_num_def:
  dest_num (Atom x::xs) = (case mlint$fromNatString (implode x) of
                           | NONE => NONE
                           | SOME n => SOME (n,xs)) ∧
  dest_num _ = NONE
End

Definition dest_local_get_def:
  dest_local_get x =
    case dest_named "local.get" x of NONE => NONE | SOME rest =>
    case dest_num rest of NONE => NONE | SOME (n,rest) =>
      SOME (LocalGet n)
End

Definition dest_stack_op_def:
  dest_stack_op x =
    case dest_named "i32.add" x of SOME rest => SOME (Instr $ Binop T_i32 Add) | NONE =>
    case dest_named "i64.add" x of SOME rest => SOME (Instr $ Binop T_i64 Add) | NONE =>
      NONE
End

Definition dest_instr_def:
  dest_instr x =
    case dest_local_get x of SOME i => SOME i | NONE =>
    case dest_stack_op x of SOME i => SOME i | NONE =>
      NONE
End

Definition read_instrs_def:
  read_instrs [] = return [] ∧
  read_instrs (x::xs) =
    case dest_instr x of
    | NONE => fail (case x of Expr (Atom n :: _) => ("can't read instruction " ++ n)
                           | _ => "instruction parsing failed")
    | SOME i => do is <- read_instrs xs ; return (i :: is) od
End

Definition read_func_def:
  read_func input =
    case dest_Expr input of | NONE => fail "must be Expr" | SOME rest =>
    case rest of [] => fail "must be nonempty" | (y::rest) =>
    if y ≠ Atom "func" then fail "must begin with func" else
    case rest of [] => fail "must be nonempty" | (y::rest) =>
    case dest_Atom y of NONE => fail "bad func name" | SOME fname =>
    case dest_params rest of NONE => fail "params" | SOME (ps,rest) =>
    case dest_results rest of NONE => fail "return" | SOME (rs,rest) =>
      do is <- read_instrs rest ;
         return (fname,ps,rs,is)
      od
End

Definition parse_wasm_def:
  parse_wasm input =
    do res <- parse_sexp input ; read_func res od
End

(* --------- tests below this line --------- *)

fun as_hol_term_string q =
  case q of
    [QUOTE s] => String.tokens (fn c => c = #"\n") s |> tl
                   |> String.concatWith "\n" |> stringSyntax.fromMLstring
  | _ => fail ();

Quote tm = as_hol_term_string:
  (func $add (param i32 i32) (result i32)
    (local.get 0)
    (local.get 1)
    (i32.add))
End

val res = EVAL “parse_wasm ^tm”

val _ = export_theory();
