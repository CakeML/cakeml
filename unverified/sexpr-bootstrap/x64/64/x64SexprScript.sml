(*
  Produces an sexp print-out of the bootstrap translated compiler
  definition for the 64-bit version of the compiler.
*)
Theory x64Sexpr
Ancestors
  compiler64Prog
Libs
  preamble mlstringSyntax astSyntax astToSexprLib

val filename = "cake-sexpr-64"

val _ = compiler64_prog_def
          |> CONV_RULE (RAND_CONV EVAL)
          |> concl
          |> rhs
          |> write_ast_to_file filename;
