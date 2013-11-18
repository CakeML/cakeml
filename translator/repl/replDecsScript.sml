open HolKernel bossLib boolLib ml_repl_stepTheory
val _ = new_theory"replDecs"

val repl_decs_def = Define`repl_decs =
  ml_repl_step_decls++
    [Dlet (Pvar"input" ) (Uapp Opref (Con (SOME(Short"None"))[]))
    ;Dlet (Pvar"output") (Uapp Opref (Lit(IntLit 0)))
    ;Dlet (Pvar"call_repl_step") (Fun "unit" (* (Mat (Var(Short"unit")) [Plit Unit, *)
       (App Opassign (Var(Short"output")) (App Opapp (Var(Short"repl_step")) (Uapp Opderef (Var(Short"input")))))(*])*))
    ]`

val _ = export_theory()

