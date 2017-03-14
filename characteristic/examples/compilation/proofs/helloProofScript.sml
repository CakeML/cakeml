open preamble
     semanticsPropsTheory backendProofTheory configProofTheory
     helloProgTheory helloCompileTheory

val _ = new_theory"helloProof";

val _ = Globals.max_print_depth := 20;

val hello_io_events_def = new_specification("hello_io_events_def",["hello_io_events"],
  hello_semantics |> Q.GENL(List.rev[`inp`,`cls`,`files`]) |> SIMP_RULE bool_ss [SKOLEM_THM]);

val (hello_sem,hello_output) = hello_io_events_def |> SPEC_ALL |> CONJ_PAIR
val (hello_not_fail,hello_sem_sing) = MATCH_MP semantics_prog_Terminate_not_Fail hello_sem |> CONJ_PAIR

val compile_correct_applied =
  MATCH_MP compile_correct hello_compiled
  |> SIMP_RULE(srw_ss())[LET_THM,ml_progTheory.init_state_env_thm,GSYM AND_IMP_INTRO]
  |> C MATCH_MP x64_conf_ok
  |> C MATCH_MP hello_not_fail
  |> REWRITE_RULE[hello_sem_sing]

val hello_compiled_thm =
  CONJ compile_correct_applied hello_output
  |> curry save_thm "hello_compiled_thm";

val _ = export_theory();
