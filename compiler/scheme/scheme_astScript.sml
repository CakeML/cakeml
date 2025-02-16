(*
  AST of Scheme
*)
open preamble;
open mlstringTheory;

val _ = new_theory "scheme_ast";

Type senv = “:(mlstring |-> num)”

(* This needs completing: Var, Lit, ... *)
Datatype:
  prim = SAdd | SMul
End

Datatype:
  val = Prim prim | SNum num | Wrong string | SBool bool
      | SList (val list)
      | Proc senv (mlstring list) (mlstring option) exp
;
  exp = Print mlstring
      | Apply exp (exp list)
      | Val ((*exp*) val)
      | Cond exp exp exp
      | Ident mlstring
      | Lambda (mlstring list) (mlstring option) exp
      | Exception mlstring
      | Begin exp (exp list)
      | Set mlstring exp
      | Letrec ((mlstring # exp) list) exp
End

val _ = export_theory();
