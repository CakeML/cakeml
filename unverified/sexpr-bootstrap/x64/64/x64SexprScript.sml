(*
  Produces an sexp print-out of the bootstrap translated compiler
  definition for the 64-bit version of the compiler.
*)
Theory x64Sexpr
Ancestors
  compiler64Prog
Libs
  preamble mlstringSyntax astToSexprLib

val filename = "cake-sexpr-x64-64"

val _ = ((write_ast_to_file filename) o rhs o concl) compiler64_prog_def;

