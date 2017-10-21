open preamble
     semanticsPropsTheory backendProofTheory x64_configProofTheory
     echoProgTheory echoCompileTheory

val _ = new_theory"echoProof";

val STD_streams_imp_stdout = Q.store_thm("STD_streams_imp_stdout",
  `STD_streams fs ⇒
   stdout fs (THE(ALOOKUP fs.files (IOStream(strlit"stdout"))))`,
  EVAL_TAC \\ rw[] \\ rw[]);
(* -- *)

val _ = clear_overloads_on"STRCAT";

val echo_io_events_def = new_specification("echo_io_events_def",["echo_io_events","echo_numchars"],
  echo_semantics
  |> SIMP_RULE (bool_ss++listLib.LIST_ss++ARITH_ss) [AND_IMP_INTRO,GSYM CONJ_ASSOC]
  |> Q.GENL[`cls`,`fs`,`output`]
  |> SIMP_RULE bool_ss [SKOLEM_THM,GSYM RIGHT_EXISTS_IMP_THM]);

val (echo_streams,th) = echo_io_events_def |> SPEC_ALL |> UNDISCH |> CONJ_PAIR
val (echo_sem,echo_output) = th |> CONJ_PAIR
val (echo_not_fail,echo_sem_sing) = MATCH_MP semantics_prog_Terminate_not_Fail echo_sem |> CONJ_PAIR

val compile_correct_applied =
  MATCH_MP compile_correct echo_compiled
  |> SIMP_RULE(srw_ss())[LET_THM,ml_progTheory.init_state_env_thm,GSYM AND_IMP_INTRO]
  |> C MATCH_MP echo_not_fail
  |> C MATCH_MP x64_backend_config_ok
  |> REWRITE_RULE[echo_sem_sing]

val echo_compiled_thm =
  CONJ compile_correct_applied echo_output (*CONJ echo_output echo_streams -- do we need this?*)
  |> DISCH_ALL
  |> curry save_thm "echo_compiled_thm";

val _ = export_theory();
