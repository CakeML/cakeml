open preamble
     semanticsPropsTheory backendProofTheory x64_configProofTheory
     iocatProgTheory iocatCompileTheory

val _ = new_theory"iocatProof";

val cat_io_events_def =
  new_specification("cat_io_events_def",["cat_io_events","cat_numchars"],
  cat_semantics_thm |> Q.GENL[`fs`,`cls`,`out`]
  |> SIMP_RULE bool_ss [SKOLEM_THM,GSYM RIGHT_EXISTS_IMP_THM]);

val (cat_streams,th) = cat_io_events_def |> SPEC_ALL |> UNDISCH_ALL |> CONJ_PAIR
val (cat_sem,cat_output) = th |> CONJ_PAIR
val (cat_not_fail,cat_sem_sing) = MATCH_MP semantics_prog_Terminate_not_Fail cat_sem |> CONJ_PAIR

val compile_correct_applied =
  MATCH_MP compile_correct iocat_compiled
  |> SIMP_RULE(srw_ss())[LET_THM,ml_progTheory.init_state_env_thm,GSYM AND_IMP_INTRO]
  |> C MATCH_MP cat_not_fail
  |> C MATCH_MP x64_backend_config_ok
  |> REWRITE_RULE[cat_sem_sing]

val cat_compiled_thm =
  CONJ compile_correct_applied cat_output
  |> DISCH_ALL
  |> curry save_thm "cat_compiled_thm";

val _ = export_theory();
