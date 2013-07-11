open HolKernel bossLib boolLib ml_repl_stepTheory
val _ = new_theory"oneshot"
val oneshot_decs_def = Define`oneshot_decs =
  ml_repl_step_decls++
    [Dlet (Pvar"it") (App Opapp (Var(Short"parse_elaborate_infertype_compile"))
                                (Var(Short"input")))]`
val _ = export_theory()

