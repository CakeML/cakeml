(*
  Generates an s-expression from the OCaml parser things that
  can be fed into the CakeML compiler binary.
 *)

open preamble astToSexprLib camlProgTheory;
open fromSexpTheory; (* this should be pulled in by the Lib, but isn't *)

val _ = new_theory "caml_sexpr";

val filename = "caml-sexpr";

val _ = ((write_ast_to_file filename) o rhs o concl) caml_parse_prog_def;

val _ = export_theory ();

