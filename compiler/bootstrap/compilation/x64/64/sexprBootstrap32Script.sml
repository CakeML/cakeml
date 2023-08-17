(*
  Produces an sexp print-out of the bootstrap translated compiler
  definition for the 32-bit version of the compiler.
*)
open preamble compiler32ProgTheory astToSexprLib

val _ = new_theory"sexprBootstrap32";

val filename = "cake-sexpr-32"

val _ = ((write_ast_to_file filename) o rhs o concl) compiler32_prog_def;

val _ = export_theory();
