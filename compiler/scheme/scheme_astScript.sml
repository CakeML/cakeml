(*
  AST of Scheme
*)
open preamble;
open mlstringTheory;

val _ = new_theory "scheme_ast";

(* This needs completing: Var, Lit, ... *)
Datatype:
  prim = SAdd | SMul
End

Datatype:
  val = Prim prim | SNum num | Wrong string
End

Datatype:
  exp = Print mlstring | Apply exp (exp list) | Val val
End

Definition exp_size_def:
  exp_size (Val _) = 0 ∧
  exp_size (Print _) = 0 ∧
  exp_size (Apply fn args) = 1
End

val _ = export_theory();
