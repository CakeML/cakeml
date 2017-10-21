open preamble
     semanticsPropsTheory backendProofTheory x64_configProofTheory
     helloErrProgTheory helloErrCompileTheory

val _ = new_theory"helloErrProof";

val helloErr_io_events_def =
  new_specification("helloErr_io_events_def",["helloErr_io_events","hello_numchars"],
  helloErr_semantics
  |> SIMP_RULE (bool_ss++listLib.LIST_ss++ARITH_ss) [AND_IMP_INTRO,GSYM CONJ_ASSOC]
  |> Q.GENL[`cls`,`fs`,`err`]
  |> SIMP_RULE bool_ss [SKOLEM_THM,GSYM RIGHT_EXISTS_IMP_THM]);

val (helloErr_streams,th) = helloErr_io_events_def |> SPEC_ALL |> UNDISCH |> CONJ_PAIR
val (helloErr_sem,helloErr_output) = th |> CONJ_PAIR
val (helloErr_not_fail,helloErr_sem_sing) = MATCH_MP
        semantics_prog_Terminate_not_Fail helloErr_sem |> CONJ_PAIR

val compile_correct_applied =
  MATCH_MP compile_correct helloErr_compiled
  |> SIMP_RULE(srw_ss())[LET_THM,ml_progTheory.init_state_env_thm,GSYM AND_IMP_INTRO]
  |> C MATCH_MP helloErr_not_fail
  |> C MATCH_MP x64_backend_config_ok
  |> REWRITE_RULE[helloErr_sem_sing]

val helloErr_compiled_thm =
  CONJ compile_correct_applied helloErr_output
  |> DISCH_ALL
  |> curry save_thm "hello_compiled_thm";

val _ = export_theory();
