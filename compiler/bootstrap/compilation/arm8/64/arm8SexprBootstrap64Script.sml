(*
  S-expression release artifact for the native ARM8 compiler.
*)
Theory arm8SexprBootstrap64
Ancestors
  compiler64Arm8Prog
Libs
  preamble mlstringSyntax astSyntax astToSexprLib

val _ = compiler64_arm8_prog_def
          |> CONV_RULE (RAND_CONV EVAL)
          |> concl
          |> rhs
          |> write_ast_to_file "cake-sexpr-64";
