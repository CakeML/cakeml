(*
  Defines a simple S-expression type.
*)

open preamble
open mlstringTheory

val _ = new_theory "dafny_sexp";

Datatype:
  sexp = Atom mlstring | Expr (sexp list)
End

val _ = export_theory ();
