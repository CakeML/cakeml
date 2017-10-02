open preamble
     semanticsPropsTheory backendProofTheory x64_configProofTheory
     patchProgTheory patchCompileTheory

val _ = new_theory"patchProof";

val patch_io_events_def = new_specification("patch_io_events_def",["patch_io_events"],
  patch_semantics |> Q.GENL[`inp`,`cls`,`files`]
  |> SIMP_RULE bool_ss [SKOLEM_THM,GSYM RIGHT_EXISTS_IMP_THM]);

val (patch_sem,patch_output) = patch_io_events_def |> SPEC_ALL |> UNDISCH |> CONJ_PAIR
val (patch_not_fail,patch_sem_sing) = MATCH_MP semantics_prog_Terminate_not_Fail patch_sem |> CONJ_PAIR

val compile_correct_applied =
  MATCH_MP compile_correct patch_compiled
  |> SIMP_RULE(srw_ss())[LET_THM,ml_progTheory.init_state_env_thm,GSYM AND_IMP_INTRO]
  |> C MATCH_MP patch_not_fail
  |> C MATCH_MP x64_backend_config_ok
  |> REWRITE_RULE[patch_sem_sing]

val patch_compiled_thm =
  CONJ compile_correct_applied patch_output
  |> DISCH_ALL
  |> curry save_thm "patch_compiled_thm";

val _ = export_theory();
