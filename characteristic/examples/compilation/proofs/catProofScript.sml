open preamble
     semanticsPropsTheory backendProofTheory configProofTheory
     catProgTheory catCompileTheory

val _ = new_theory"catProof";

val cat_io_events_def = new_specification("cat_io_events_def",["cat_io_events"],
  cat_semantics_thm |> Q.GENL(List.rev[`inp`,`cls`,`files`])
  |> SIMP_RULE bool_ss [SKOLEM_THM,GSYM RIGHT_EXISTS_IMP_THM]);

val (cat_sem,cat_output) = cat_io_events_def |> SPEC_ALL |> UNDISCH |> CONJ_PAIR
val (cat_not_fail,cat_sem_sing) = MATCH_MP semantics_prog_Terminate_not_Fail cat_sem |> CONJ_PAIR

val compile_correct_applied =
  MATCH_MP compile_correct cat_compiled
  |> SIMP_RULE(srw_ss())[LET_THM,ml_progTheory.init_state_env_thm,GSYM AND_IMP_INTRO]
  |> C MATCH_MP x64_conf_ok
  |> C MATCH_MP cat_not_fail
  |> REWRITE_RULE[cat_sem_sing]

val cat_compiled_thm =
  CONJ compile_correct_applied cat_output
  |> DISCH_ALL
  |> curry save_thm "cat_compiled_thm";

val _ = export_theory();
