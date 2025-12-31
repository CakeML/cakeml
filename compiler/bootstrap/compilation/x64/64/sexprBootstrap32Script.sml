(*
  Produces an sexp print-out of the bootstrap translated compiler
  definition for the 32-bit version of the compiler.
*)
Theory sexprBootstrap32
Ancestors
  compiler32Prog
Libs
  preamble astToSexprLib

val filename = "cake-sexpr-32"

val _ = ((write_ast_to_file filename) o rhs o concl) compiler32_prog_def;

