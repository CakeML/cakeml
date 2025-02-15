(*
  AST of Scheme
*)
open preamble;
open mlstringTheory;

val _ = new_theory "scheme_ast";

(* This needs completing: Var, Lit, ... *)
Datatype:
  prim = SAdd | SMul | CallCC
End

Datatype:
  val = Prim prim | SNum num | Wrong string | SBool bool
      | SList (val list)
      (*| Proc ((mlstring # val) list) (mlstring list) (mlstring option) 'a*)
      | Throw (cont list)
;
  (*Contexts for small-step operational semantics*)
  cont = ApplyK (( val # val list) option) (exp list)
       | CondK exp exp
       | LetK ((mlstring # val) list) mlstring ((mlstring # exp) list) exp
       | InLetK ((mlstring # val) list)
       | BeginK (exp list)
;
  exp = Print mlstring
      | Apply exp (exp list)
      | Val val
      | Cond exp exp exp
      | Ident mlstring
      | SLet ((mlstring # exp) list) exp
      | Lambda (mlstring list) (mlstring option) exp
      | Exception mlstring
      | Begin exp (exp list)
End

val _ = export_theory();
