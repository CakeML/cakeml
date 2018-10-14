open preamble
     semanticsPropsTheory backendProofTheory x64_configProofTheory
     readerProgTheory readerCompileTheory

val _ = new_theory "readerProgProof";

val reader_io_events_def = new_specification (
  "reader_io_events_def", ["reader_io_events"],
  semantics_reader_prog
  |> Q.GENL[`cl`,`fs`]
  |> SIMP_RULE bool_ss [SKOLEM_THM,GSYM RIGHT_EXISTS_IMP_THM]);

val (reader_sem, reader_output) =
  reader_io_events_def |> SPEC_ALL |> UNDISCH |> CONJ_PAIR

val (reader_not_fail, reader_sem_sing) =
  MATCH_MP semantics_prog_Terminate_not_Fail reader_sem |> CONJ_PAIR

val compile_correct_applied =
  MATCH_MP compile_correct reader_compiled
  |> SIMP_RULE (srw_ss()) [LET_THM, ml_progTheory.init_state_env_thm,
                           GSYM AND_IMP_INTRO]
  |> C MATCH_MP reader_not_fail
  |> C MATCH_MP x64_backend_config_ok
  |> REWRITE_RULE [reader_sem_sing,AND_IMP_INTRO]
  |> REWRITE_RULE [Once (GSYM AND_IMP_INTRO)]
  |> C MATCH_MP (CONJ (UNDISCH x64_machine_config_ok) (UNDISCH x64_init_ok))
  |> DISCH (#1 (dest_imp (concl x64_init_ok)))
  |> REWRITE_RULE [AND_IMP_INTRO]

val reader_compiled_thm =
  CONJ compile_correct_applied reader_output
  |> DISCH_ALL
  |> check_thm
  |> curry save_thm "reader_compiled_thm";

val _ = export_theory ();

