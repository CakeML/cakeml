open preamble
     semanticsPropsTheory backendProofTheory x64_configProofTheory
     helloProgTheory helloCompileTheory

val _ = new_theory"helloProof";

(* TODO: move *)
(* the spec theorems should have been simplified earlier.. *)
val with_same_numchars = Q.store_thm("with_same_numchars",
  `x with numchars := x.numchars = x`,
  rw[fsFFITheory.IO_fs_component_equality])
(* -- *)

val hello_io_events_def = new_specification("hello_io_events_def",["hello_io_events","hello_numchars"],
  hello_semantics
  |> Q.GEN`ll` |> Q.SPEC`fs.numchars`
  |> SIMP_RULE (bool_ss++listLib.LIST_ss++ARITH_ss) [with_same_numchars,AND_IMP_INTRO,GSYM CONJ_ASSOC]
  |> Q.GENL[`cls`,`fs`,`output`]
  |> SIMP_RULE bool_ss [SKOLEM_THM,GSYM RIGHT_EXISTS_IMP_THM]);

val (hello_streams,th) = hello_io_events_def |> SPEC_ALL |> UNDISCH |> CONJ_PAIR
val (hello_sem,hello_output) = th |> CONJ_PAIR
val (hello_not_fail,hello_sem_sing) = MATCH_MP semantics_prog_Terminate_not_Fail hello_sem |> CONJ_PAIR

val compile_correct_applied =
  MATCH_MP compile_correct hello_compiled
  |> SIMP_RULE(srw_ss())[LET_THM,ml_progTheory.init_state_env_thm,GSYM AND_IMP_INTRO]
  |> C MATCH_MP hello_not_fail
  |> C MATCH_MP x64_backend_config_ok
  |> REWRITE_RULE[hello_sem_sing]

val hello_compiled_thm =
  CONJ compile_correct_applied hello_output
  |> DISCH_ALL
  |> curry save_thm "hello_compiled_thm";

val _ = export_theory();
