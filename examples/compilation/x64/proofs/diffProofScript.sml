(*
  Compose the diff semantics theorem and the compiler correctness
  theorem with the compiler evaluation theorem to produce end-to-end
  correctness theorem that reaches final machine code.
*)
open preamble
     semanticsPropsTheory backendProofTheory x64_configProofTheory
     diffProgTheory diffCompileTheory

val _ = new_theory"diffProof";

val diff_io_events_def = new_specification("diff_io_events_def",["diff_io_events"],
  diff_semantics |> Q.GENL[`cl`,`fs`]
  |> SIMP_RULE bool_ss [SKOLEM_THM,Once(GSYM RIGHT_EXISTS_IMP_THM)]);

val (diff_sem,diff_output) = diff_io_events_def |> SPEC_ALL |> UNDISCH |> CONJ_PAIR
val (diff_not_fail,diff_sem_sing) = diff_sem
  |> SRULE [diff_compiled,ml_progTheory.prog_syntax_ok_semantics]
  |> MATCH_MP semantics_prog_Terminate_not_Fail |> CONJ_PAIR

val compile_correct_applied =
  MATCH_MP compile_correct (cj 1 diff_compiled)
  |> SIMP_RULE(srw_ss())[LET_THM,ml_progTheory.init_state_env_thm,GSYM AND_IMP_INTRO]
  |> C MATCH_MP diff_not_fail
  |> C MATCH_MP x64_backend_config_ok
  |> REWRITE_RULE[diff_sem_sing,AND_IMP_INTRO]
  |> REWRITE_RULE[Once (GSYM AND_IMP_INTRO)]
  |> C MATCH_MP (CONJ(UNDISCH x64_machine_config_ok)(UNDISCH x64_init_ok))
  |> DISCH(#1(dest_imp(concl x64_init_ok)))
  |> REWRITE_RULE[AND_IMP_INTRO]

Theorem diff_compiled_thm =
  CONJ compile_correct_applied diff_output
  |> DISCH_ALL
  |> check_thm

val _ = export_theory();
