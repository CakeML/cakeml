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
      | SList (val list)
      | Proc ((mlstring # val) list) (mlstring list) (mlstring option) exp
;
  exp = Print mlstring
      | Apply exp (exp list)
      | Val val
      | Cond exp exp exp
      | Ident mlstring
      | SLet ((mlstring # exp) list) exp
      | Lambda (mlstring list) (mlstring option) exp
      | Exception mlstring
End

val _ = export_theory();
