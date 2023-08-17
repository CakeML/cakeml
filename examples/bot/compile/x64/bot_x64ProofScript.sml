(*
  x64 proof
*)

open preamble
     semanticsPropsTheory backendProofTheory x64_configProofTheory
     botProgTheory bot_x64CompileTheory

val _ = new_theory"bot_x64Proof";

val bot_io_events_def = new_specification("bot_io_events_def",["bot_io_events"],
  bot_semantics_thm |> Q.GENL[`w`,`st`]
  |> SIMP_RULE bool_ss [SKOLEM_THM,Once(GSYM RIGHT_EXISTS_IMP_THM),RIGHT_EXISTS_AND_THM]);

val (bot_sem,bot_output) = bot_io_events_def |> SPEC_ALL |> UNDISCH_ALL |> CONJ_PAIR
val (bot_not_fail,bot_sem_sing) = MATCH_MP semantics_prog_Terminate_not_Fail bot_sem |> CONJ_PAIR

val compile_correct_applied =
  MATCH_MP compile_correct bot_x64
  |> SIMP_RULE(srw_ss())[LET_THM,ml_progTheory.init_state_env_thm,GSYM AND_IMP_INTRO]
  |> C MATCH_MP bot_not_fail
  |> C MATCH_MP x64_backend_config_ok
  |> REWRITE_RULE[bot_sem_sing,AND_IMP_INTRO]
  |> REWRITE_RULE[Once (GSYM AND_IMP_INTRO)]
  |> C MATCH_MP (CONJ(UNDISCH x64_machine_config_ok)(UNDISCH x64_init_ok))
  |> DISCH(#1(dest_imp(concl x64_init_ok)))
  |> REWRITE_RULE[AND_IMP_INTRO]

val bot_compiled_thm =
  CONJ compile_correct_applied bot_output
  |> DISCH_ALL
  |> curry save_thm "bot_compiled_thm";

val _ = export_theory();
