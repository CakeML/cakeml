open HolKernel boolLib bossLib compile_repl_decsTheory compute_bytecodeLib
val _ = new_theory"removeLabelsReplDecs"

val repl_decs_code_def = zDefine
  `repl_decs_code = code_labels real_inst_length (SND(SND(compile_repl_decs)))`

val cs = wordsLib.words_compset()
val () = add_labels_compset cs
(* TODO: this won't work because we're missing the VfromList code.
         we need to remove labels for all the code that will be installed in
         the REPL on setup, not just the code in compile_repl_decs.
  val () = add_code_labels_ok_thm
val eval = computeLib.CBV_CONV cs
val repl_decs_code_eq = save_thm("repl_decs_code_eq",
  time (REWR_CONV repl_decs_code_def THENC PURE_ONCE_REWRITE_CONV[compile_repl_decs_eq] THENC eval)
  ``repl_decs_code``)
*)

val compile_call_repl_step_labels = store_thm("compile_call_repl_step_labels",
  ``FILTER is_Label compile_call_repl_step = []``,
  REWRITE_TAC[compile_call_repl_step_eq] THEN EVAL_TAC)

val _ = export_theory()
