open HolKernel boolLib bossLib compileReplTheory closedReplTheory initCompEnvTheory compute_bytecodeLib
open miscLib lcsymtacs
val _ = new_theory"removeLabelsRepl"

val _ = Globals.max_print_depth := 20

val bootstrap_code_def = zDefine
  `bootstrap_code = code_labels real_inst_length
    (initial_bc_state.code++REVERSE(SND(THE prim_env)++SND(SND(compile_repl_module))))`

val initial_bc_state_code_eq = EVAL``initial_bc_state.code``

val cs = listLib.list_compset()
val () = pairLib.add_pair_compset cs
val () = optionLib.OPTION_rws cs
val () = computeLib.add_datatype_info cs (valOf(TypeBase.fetch``:comp_environment``))
val () = computeLib.add_thms [prim_env_eq,compile_repl_module_eq] cs
val labelled_bootstrap_code_eq =
  (PURE_ONCE_REWRITE_CONV[initial_bc_state_code_eq] THENC
   computeLib.CBV_CONV cs)
  ``initial_bc_state.code++REVERSE(SND(THE prim_env)++SND(SND(compile_repl_module)))``

val bootstrap_code_labels_ok0 = prove(
  ``code_labels_ok ^(rand(rhs(concl bootstrap_code_def)))``,
  match_mp_tac compilerTerminationTheory.code_labels_ok_append_local >>
  conj_tac >- simp[initCompEnvTheory.initial_bc_state_def,
                   compilerTerminationTheory.code_labels_ok_microcode] >>
  reverse conj_tac >- (
    simp[compilerTerminationTheory.contains_primitives_def,
         initCompEnvTheory.initial_bc_state_def] >>
    qexists_tac`[]`>>simp[]>> EVAL_TAC) >>
  simp[compilerTerminationTheory.local_labels_reverse,
       compilerTerminationTheory.local_labels_append] >>
  match_mp_tac bytecodeLabelsTheory.code_labels_ok_append >>
  reverse conj_tac >- (
    simp[evaluateReplTheory.compile_repl_module_def] >>
    match_mp_tac (
      compilerProofTheory.compile_top_labels
      |> SPEC_ALL |> UNDISCH_ALL  |> CONJUNCT2 |> CONJUNCT2
      |> DISCH_ALL |> GEN_ALL) >>
    simp[evalPropsTheory.FV_top_def,
         FV_decs_replModule_decls]) >>
    REWRITE_TAC[initCompEnvTheory.prim_env_eq] >>
    EVAL_TAC >> simp[])

val bootstrap_code_labels_ok =
  bootstrap_code_labels_ok0
  |> CONV_RULE(RAND_CONV(REWR_CONV labelled_bootstrap_code_eq))

val cs = wordsLib.words_compset()
val () = add_labels_compset cs
val () = add_code_labels_ok_thm bootstrap_code_labels_ok
val eval = computeLib.CBV_CONV cs
val bootstrap_code_eq = save_thm("bootstrap_code_eq",
  time (REWR_CONV bootstrap_code_def THENC
        RAND_CONV(REWR_CONV labelled_bootstrap_code_eq) THENC
        eval)
  ``bootstrap_code``)

val compile_call_repl_step_labels = store_thm("compile_call_repl_step_labels",
  ``FILTER is_Label compile_call_repl_step = []``,
  REWRITE_TAC[compile_call_repl_step_eq] THEN EVAL_TAC)

val _ = export_theory()
