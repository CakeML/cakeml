(*
  Produces an sexp print-out of the bootstrap translated compiler
  definition for the 32-bit version of the compiler.
*)
Theory sexprBootstrap32
Ancestors
  compiler32Prog
Libs
  preamble mlstringSyntax astSyntax astToSexprLib

val filename = "cake-sexpr-32"

val _ = compiler32_prog_def
          |> CONV_RULE (RAND_CONV EVAL)
          |> concl
          |> rhs
          |> write_ast_to_file filename;
