(*
  Basic properties of the AST.
  TODO: delete this theory (it has no content)
*)

open preamble;
open astTheory astSyntax;

val _ = new_theory "astProps";

(*
val _ = export_rewrites ["ast.Tstring_def",
                         "ast.Tint_def",
                         "ast.Tref_def",
                         "ast.Tfn_def",
                         "ast.Tword8_def",
                         "ast.Tword8array_def",
                         "ast.Texn_def"];
                         *)

val _ = export_theory ();
