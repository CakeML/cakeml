open HolKernel boolLib bossLib cakeml_computeLib ml_repl_moduleTheory compile_primitivesTheory flookupLib
val _ = new_theory"compile_repl_decs"

val compile_repl_decs_def = zDefine`
  compile_repl_decs = compile_top NONE (FST compile_primitives) (Tmod "REPL" NONE ml_repl_module_decls)`

val _ = Globals.max_print_depth := 20

val cs = cakeml_compset();
(*TODO: add FUNION_FUPDATE_1 to finite_map compset*)
val _ = computeLib.add_thms [finite_mapTheory.FUNION_FUPDATE_1,compile_primitives_eq] cs
val _ = computeLib.scrub_const cs finite_mapSyntax.flookup_t;
val _ = computeLib.add_conv (finite_mapSyntax.flookup_t,2,FLOOKUP_DEFN_CONV) cs;
val eval = computeLib.CBV_CONV cs

val compile_repl_decs_eq = save_thm("compile_repl_decs_eq",
  time (REWR_CONV compile_repl_decs_def THENC PURE_ONCE_REWRITE_CONV[ml_repl_module_decls] THENC eval)
  ``compile_repl_decs``)

val repl_decs_code_def = zDefine
  `repl_decs_code = code_labels real_inst_length (SND(SND(compile_repl_decs)))`

val repl_decs_code_eq = save_thm("repl_decs_code_eq",
  time (REWR_CONV repl_decs_code_def THENC PURE_ONCE_REWRITE_CONV[compile_repl_decs_eq] THENC eval)
  ``repl_decs_code``)

val call_dec = ``Tdec (Dlet (Plit Unit) (App Opapp (Var(Long"REPL""call_repl_step")) (Lit Unit)))``

val compile_call_repl_step_def = zDefine`
  compile_call_repl_step = compile_special (FST compile_repl_decs) ^call_dec`


val _ = computeLib.add_thms [compilerProofTheory.compile_special_def,
                             compilerProofTheory.prompt_to_i3_special_def] cs
val eval_special = computeLib.CBV_CONV cs
val compile_call_repl_step_eq = save_thm("compile_call_repl_step_eq",
  time (REWR_CONV compile_call_repl_step_def THENC
        PURE_ONCE_REWRITE_CONV[compile_repl_decs_eq] THENC
        eval_special)
  ``compile_call_repl_step``)

val compile_call_repl_step_labels = store_thm("compile_call_repl_step_labels",
  ``FILTER is_Label compile_call_repl_step = []``,
  REWRITE_TAC[compile_call_repl_step_eq] THEN EVAL_TAC)

val _ = Feedback.set_trace "TheoryPP.include_docs" 0
val _ = export_theory()
