open preamble
     semanticsPropsTheory backendProofTheory x64_configProofTheory
     helloErrProgTheory helloErrCompileTheory

val _ = new_theory"helloErrProof";

val helloErr_io_events_def =
  new_specification("helloErr_io_events_def",["helloErr_io_events"],
  helloErr_semantics |> Q.GENL[`cl`,`fs`]
  |> SIMP_RULE bool_ss [SKOLEM_THM,Once(GSYM RIGHT_EXISTS_IMP_THM)]);

val (helloErr_sem,helloErr_output) = helloErr_io_events_def |> SPEC_ALL |> UNDISCH |> CONJ_PAIR
val (helloErr_not_fail,helloErr_sem_sing) = MATCH_MP
        semantics_prog_Terminate_not_Fail helloErr_sem |> CONJ_PAIR

val compile_correct_applied =
  MATCH_MP compile_correct helloErr_compiled
  |> SIMP_RULE(srw_ss())[LET_THM,ml_progTheory.init_state_env_thm,GSYM AND_IMP_INTRO]
  |> C MATCH_MP helloErr_not_fail
  |> C MATCH_MP x64_backend_config_ok
  |> REWRITE_RULE[helloErr_sem_sing,AND_IMP_INTRO]
  |> REWRITE_RULE[Once (GSYM AND_IMP_INTRO)]
  |> C MATCH_MP (CONJ(UNDISCH x64_machine_config_ok)(UNDISCH x64_init_ok))
  |> DISCH(#1(dest_imp(concl x64_init_ok)))
  |> REWRITE_RULE[AND_IMP_INTRO]

val helloErr_compiled_thm =
  CONJ compile_correct_applied helloErr_output
  |> DISCH_ALL
  |> curry save_thm "hello_compiled_thm";

val _ = export_theory();
