open preamble
     semanticsPropsTheory backendProofTheory x64_configProofTheory
     sortProgTheory sortCompileTheory

val _ = new_theory"sortProof";

val sort_io_events_def = new_specification("sort_io_events_def",
  ["sort_io_events","sort_error","sort_output"],
  sort_semantics |> Q.GENL(List.rev[`inp`,`cls`,`files`])
  |> SIMP_RULE bool_ss [SKOLEM_THM,GSYM RIGHT_EXISTS_IMP_THM]);

val (sort_pred,th) = sort_io_events_def |> SPEC_ALL |> UNDISCH |> CONJ_PAIR
val (sort_sem,sort_output) = th |> CONJ_PAIR
val (sort_not_fail,sort_sem_sing) = MATCH_MP semantics_prog_Terminate_not_Fail sort_sem |> CONJ_PAIR

val compile_correct_applied =
  MATCH_MP compile_correct sort_compiled
  |> SIMP_RULE(srw_ss())[LET_THM,ml_progTheory.init_state_env_thm,GSYM AND_IMP_INTRO]
  |> C MATCH_MP x64_conf_ok
  |> C MATCH_MP sort_not_fail
  |> REWRITE_RULE[sort_sem_sing]

val sort_compiled_thm =
  LIST_CONJ [compile_correct_applied,sort_output,sort_pred]
  |> DISCH_ALL
  |> curry save_thm "sort_compiled_thm";

val _ = export_theory();
