(*
  Compose the echo semantics theorem and the compiler correctness
  theorem with the compiler evaluation theorem to produce end-to-end
  correctness theorem that reaches final machine code.
*)
open preamble
     semanticsPropsTheory backendProofTheory x64_configProofTheory
     echoProgTheory echoCompileTheory

val _ = new_theory"echoProof";

val echo_io_events_def = new_specification("echo_io_events_def",["echo_io_events"],
  echo_semantics
  |> Q.GENL[`cl`,`fs`]
  |> SIMP_RULE bool_ss [SKOLEM_THM,GSYM RIGHT_EXISTS_IMP_THM]);

val (echo_sem,echo_output) = echo_io_events_def |> SPEC_ALL |> UNDISCH |> CONJ_PAIR
val (echo_not_fail,echo_sem_sing) = MATCH_MP semantics_prog_Terminate_not_Fail echo_sem |> CONJ_PAIR

val compile_correct_applied =
  MATCH_MP compile_correct echo_compiled
  |> SIMP_RULE(srw_ss())[LET_THM,ml_progTheory.init_state_env_thm,GSYM AND_IMP_INTRO]
  |> C MATCH_MP echo_not_fail
  |> C MATCH_MP x64_backend_config_ok
  |> REWRITE_RULE[echo_sem_sing,AND_IMP_INTRO]
  |> REWRITE_RULE[Once (GSYM AND_IMP_INTRO)]
  |> C MATCH_MP (CONJ(UNDISCH x64_machine_config_ok)(UNDISCH x64_init_ok))
  |> DISCH(#1(dest_imp(concl x64_init_ok)))
  |> REWRITE_RULE[AND_IMP_INTRO]

val echo_compiled_thm =
  CONJ compile_correct_applied echo_output
  |> DISCH_ALL
  |> check_thm
  |> curry save_thm "echo_compiled_thm";

val _ = export_theory();
