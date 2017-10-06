open preamble
     semanticsPropsTheory backendProofTheory x64_configProofTheory
     grepProgTheory grepCompileTheory

val _ = new_theory"grepProof";

val grep_io_events_def = new_specification("grep_io_events_def",["grep_io_events"],
  grep_semantics |> Q.GENL[`inp`,`cls`,`files`]
  |> SIMP_RULE bool_ss [SKOLEM_THM,GSYM RIGHT_EXISTS_IMP_THM]);

val (grep_sem,grep_output) = grep_io_events_def |> SPEC_ALL |> UNDISCH |> CONJ_PAIR
val (grep_not_fail,grep_sem_sing) = MATCH_MP semantics_prog_Terminate_not_Fail grep_sem |> CONJ_PAIR

val compile_correct_applied =
  MATCH_MP compile_correct grep_compiled
  |> SIMP_RULE(srw_ss())[LET_THM,ml_progTheory.init_state_env_thm,GSYM AND_IMP_INTRO]
  |> C MATCH_MP grep_not_fail
  |> C MATCH_MP x64_backend_config_ok
  |> REWRITE_RULE[grep_sem_sing]

val grep_compiled_thm =
  CONJ compile_correct_applied grep_output
  |> DISCH_ALL
  |> curry save_thm "grep_compiled_thm";

val _ = export_theory();
