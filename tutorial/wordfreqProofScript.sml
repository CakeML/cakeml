open preamble
     semanticsPropsTheory backendProofTheory x64_configProofTheory
     wordfreqProgTheory wordfreqCompileTheory

val _ = new_theory"wordfreqProof";

val wordfreq_io_events_def = new_specification("wordfreq_io_events_def",["wordfreq_io_events"],
  wordfreq_semantics |> Q.GENL[`fs`,`pname`,`fname`(*,`contents`*)]
  |> SIMP_RULE bool_ss [SKOLEM_THM,Once(GSYM RIGHT_EXISTS_IMP_THM),RIGHT_EXISTS_AND_THM]);

val (wordfreq_sem,wordfreq_output) = wordfreq_io_events_def |> SPEC_ALL |> UNDISCH |> CONJ_PAIR
val (wordfreq_not_fail,wordfreq_sem_sing) = MATCH_MP semantics_prog_Terminate_not_Fail wordfreq_sem |> CONJ_PAIR

val compile_correct_applied =
  MATCH_MP compile_correct wordfreq_compiled
  |> SIMP_RULE(srw_ss())[LET_THM,ml_progTheory.init_state_env_thm,GSYM AND_IMP_INTRO]
  |> C MATCH_MP wordfreq_not_fail
  |> C MATCH_MP x64_backend_config_ok
  |> REWRITE_RULE[wordfreq_sem_sing,AND_IMP_INTRO]
  |> REWRITE_RULE[Once (GSYM AND_IMP_INTRO)]
  |> C MATCH_MP (CONJ(UNDISCH x64_machine_config_ok)(UNDISCH x64_init_ok))
  |> DISCH(#1(dest_imp(concl x64_init_ok)))
  |> REWRITE_RULE[AND_IMP_INTRO]

val wordfreq_compiled_thm =
  CONJ compile_correct_applied wordfreq_output
  |> SIMP_RULE std_ss [AND_IMP_INTRO,GSYM CONJ_ASSOC]
  |> DISCH_ALL
  |> curry save_thm "wordfreq_compiled_thm";

val _ = export_theory();
