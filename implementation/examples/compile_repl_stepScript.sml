open preamble repl_computeLib ml_repl_stepTheory
val _ = new_theory"compile_repl_step"

val compile_decs = Define`
  compile_decs cs [] acc = acc ∧
  compile_decs cs (d::ds) acc =
  let (cs,code) = compile_dec cs d in
  compile_decs cs ds (code::acc)`

val _ = computeLib.add_funs[ml_repl_step_decls]

val _ = save_thm("result",time EVAL ``FLAT (REVERSE (compile_decs init_compiler_state ml_repl_step_decls []))``)

val _ = export_theory()
