open preamble
     semanticsPropsTheory backendProofTheory x64_configProofTheory
     catProgTheory catCompileTheory

val _ = new_theory"catProof";

val cat_io_events_def = new_specification("cat_io_events_def",["cat_io_events"],
  cat_semantics_thm |> Q.GENL[`cl`,`fs`]
  |> SIMP_RULE bool_ss [SKOLEM_THM,Once(GSYM RIGHT_EXISTS_IMP_THM)]);

val (cat_sem,cat_output) = cat_io_events_def |> SPEC_ALL |> UNDISCH_ALL |> CONJ_PAIR
val (cat_not_fail,cat_sem_sing) = MATCH_MP semantics_prog_Terminate_not_Fail cat_sem |> CONJ_PAIR

val compile_correct_applied =
  MATCH_MP compile_correct cat_compiled
  |> SIMP_RULE(srw_ss())[LET_THM,ml_progTheory.init_state_env_thm,GSYM AND_IMP_INTRO]
  |> C MATCH_MP cat_not_fail
  |> C MATCH_MP x64_backend_config_ok
  |> REWRITE_RULE[cat_sem_sing,AND_IMP_INTRO]
  |> REWRITE_RULE[Once (GSYM AND_IMP_INTRO)]
  |> C MATCH_MP (CONJ(UNDISCH x64_machine_config_ok)(UNDISCH x64_init_ok))
  |> DISCH(#1(dest_imp(concl x64_init_ok)))
  |> REWRITE_RULE[AND_IMP_INTRO]

val cat_compiled_thm =
  CONJ compile_correct_applied cat_output
  |> DISCH_ALL
  |> check_thm
  |> curry save_thm "cat_compiled_thm";

val _ = export_theory();
