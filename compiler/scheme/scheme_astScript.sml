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
  val = Prim prim | SNum num | Wrong string | SBool bool
End

Datatype:
  exp = Print mlstring
      | Apply exp (exp list)
      | Val val
      | Cond exp exp exp
      | Ident mlstring
      | SLet ((mlstring # exp) list) exp
End

val _ = export_theory();
