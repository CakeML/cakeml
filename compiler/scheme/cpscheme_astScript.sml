(*
  AST of CPScheme
*)
open preamble;
open mlstringTheory;
open scheme_astTheory;

val _ = new_theory "cpscheme_ast";

Datatype:
  cexp = CVal ((*cexp*) val)             (*λk.k val*)
       | CException mlstring  (**)
       | Call cexp (cexp cont)       (*λk.cexp (cont o k)*)
       (*| CLambda (mlstring list) (mlstring option) cexp*)
End

val _ = export_theory();