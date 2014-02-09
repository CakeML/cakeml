(* Basic properties of the AST *)

open preamble;
open astTheory;

val _ = new_theory "astProps";

val _ = export_rewrites ["ast.Tstring_def",
                         "ast.Tint_def",
                         "ast.Tunit_def",
                         "ast.Tbool_def",
                         "ast.Tref_def",
                         "ast.Tfn_def",
                         "ast.Texn_def"];

val _ = export_theory ();
