open preamble
     semanticsPropsTheory backendProofTheory configProofTheory
     echoProgTheory echoCompileTheory

val _ = new_theory"echoProof";

val echo_io_events_def = new_specification("echo_io_events_def",["echo_io_events"],
  echo_semantics |> Q.GENL(List.rev[`inp`,`cls`,`files`])
  |> SIMP_RULE bool_ss [SKOLEM_THM,GSYM RIGHT_EXISTS_IMP_THM]);

val (echo_sem,echo_output) = echo_io_events_def |> SPEC_ALL |> UNDISCH |> CONJ_PAIR
val (echo_not_fail,echo_sem_sing) = MATCH_MP semantics_prog_Terminate_not_Fail echo_sem |> CONJ_PAIR

val compile_correct_applied =
  MATCH_MP compile_correct echo_compiled
  |> SIMP_RULE(srw_ss())[LET_THM,ml_progTheory.init_state_env_thm,GSYM AND_IMP_INTRO]
  |> C MATCH_MP x64_conf_ok
  |> C MATCH_MP echo_not_fail
  |> REWRITE_RULE[echo_sem_sing]

val echo_compiled_thm =
  CONJ compile_correct_applied echo_output
  |> DISCH_ALL
  |> curry save_thm "echo_compiled_thm";

val _ = export_theory();
