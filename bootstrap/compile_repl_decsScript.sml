open HolKernel boolLib bossLib evaluate_repl_decsTheory flookupLib compute_compilerLib compute_free_varsLib
val _ = new_theory"compile_repl_decs"

val _ = Globals.max_print_depth := 20

val cs = the_compiler_compset false;
val () = computeLib.scrub_const cs finite_mapSyntax.flookup_t;
val () = computeLib.add_conv (finite_mapSyntax.flookup_t,2,FLOOKUP_DEFN_CONV) cs;
(* TODO: this should go into a separate compset *)
val () = computeLib.add_datatype_info cs (valOf(TypeBase.fetch``:comp_environment``))
val eval = computeLib.CBV_CONV cs

val compile_repl_decs_eq = save_thm("compile_repl_decs_eq",
  time (REWR_CONV compile_repl_decs_def
        THENC PURE_ONCE_REWRITE_CONV[ml_repl_moduleTheory.ml_repl_module_decls,initCompEnvTheory.prim_env_eq]
        THENC eval)
  ``compile_repl_decs``)

val repl_decs_code_def = zDefine
  `repl_decs_code = code_labels real_inst_length (SND(SND(compile_repl_decs)))`

val repl_decs_code_eq = save_thm("repl_decs_code_eq",
  time (REWR_CONV repl_decs_code_def THENC PURE_ONCE_REWRITE_CONV[compile_repl_decs_eq] THENC eval)
  ``repl_decs_code``)

val _ = computeLib.add_thms [compilerTheory.compile_special_def] cs
val eval_special = computeLib.CBV_CONV cs
val compile_call_repl_step_eq = save_thm("compile_call_repl_step_eq",
  time (REWR_CONV compile_call_repl_step_def THENC
        PURE_ONCE_REWRITE_CONV[compile_repl_decs_eq] THENC
        eval_special)
  ``compile_call_repl_step``)

val compile_call_repl_step_labels = store_thm("compile_call_repl_step_labels",
  ``FILTER is_Label compile_call_repl_step = []``,
  REWRITE_TAC[compile_call_repl_step_eq] THEN EVAL_TAC)

val eval_fvs = computeLib.CBV_CONV (the_free_vars_compset())
val FV_decs_ml_repl_module_decls = save_thm("FV_decs_ml_repl_module_decls",
  time (PURE_ONCE_REWRITE_CONV[ml_repl_moduleTheory.ml_repl_module_decls] THENC eval_fvs)
  ``FV_decs ml_repl_module_decls``)

val _ = Feedback.set_trace "TheoryPP.include_docs" 0
val _ = export_theory()
