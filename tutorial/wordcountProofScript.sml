open preamble
     semanticsPropsTheory backendProofTheory x64_configProofTheory
     wordcountProgTheory wordcountCompileTheory

val _ = new_theory"wordcountProof";

val wordcount_io_events_def = new_specification("wordcount_io_events_def",["wordcount_io_events"],
  wordcount_semantics |> Q.GENL(List.rev[`inp`,`cls`,`files`]) |> SIMP_RULE bool_ss [SKOLEM_THM]);

val (wordcount_sem,wordcount_output) = wordcount_io_events_def |> SPEC_ALL |> CONJ_PAIR
val (wordcount_not_fail,wordcount_sem_sing) = MATCH_MP semantics_prog_Terminate_not_Fail wordcount_sem |> CONJ_PAIR

val compile_correct_applied =
  MATCH_MP compile_correct wordcount_compiled
  |> SIMP_RULE(srw_ss())[LET_THM,ml_progTheory.init_state_env_thm,GSYM AND_IMP_INTRO]
  |> C MATCH_MP x64_conf_ok
  |> C MATCH_MP wordcount_not_fail
  |> REWRITE_RULE[wordcount_sem_sing]

val wordcount_compiled_thm =
  CONJ compile_correct_applied wordcount_output
  |> curry save_thm "wordcount_compiled_thm";

val _ = export_theory();
