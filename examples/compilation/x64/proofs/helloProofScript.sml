(*
  Compose the hello semantics theorem and the compiler correctness
  theorem with the compiler evaluation theorem to produce end-to-end
  correctness theorem that reaches final machine code.
*)
Theory helloProof
Ancestors
  semanticsProps backendProof x64_configProof helloProg
  helloCompile
Libs
  preamble

Theorem semantics_dec_list_eq[local]:
  ml_prog$prog_syntax_ok prog ⇒
  semantics_dec_list st init_env prog = semantics_prog st init_env prog
Proof
  rw [FUN_EQ_THM, evaluate_decTheory.semantics_dec_list_def,
      semanticsTheory.semantics_prog_def]
  \\ simp [ml_progTheory.prog_syntax_ok_semantics]
QED

(* Each pointer oracle has its own terminating trace. *)
Theorem sem_satisfies_terminate_determ[local]:
  cfMain$sem_satisfies (semantics_prog st env prog)
    (λbehavior. ∃io. behavior = Terminate Success io ∧ P io) ⇒
  ¬semantics_prog st env prog Fail ∧
  ∀po. ∃io.
    semantics_determ (st with ptr_eq_oracle := po) env prog =
      {Terminate Success io} ∧ P io
Proof
  rw [cfMainTheory.sem_satisfies_def, IN_DEF]
  >- (strip_tac \\ res_tac \\ fs [])
  \\ qspecl_then [‘st with ptr_eq_oracle := po’, ‘env’, ‘prog’]
       (qx_choose_then ‘behavior’ assume_tac) semantics_determ_total
  \\ ‘semantics_prog st env prog behavior’ by
    (simp [semanticsTheory.semantics_prog_def] \\ metis_tac [])
  \\ res_tac \\ gvs []
  \\ imp_res_tac semantics_determ_Terminate_not_Fail
  \\ metis_tac []
QED

val (hello_not_fail,hello_determ) = hello_semantics
  |> UNDISCH
  |> SRULE [hello_compiled,semantics_dec_list_eq]
  |> HO_MATCH_MP sem_satisfies_terminate_determ
  |> CONJ_PAIR

val hello_io_events_def =
  new_specification("hello_io_events_def",["hello_io_events"],
  hello_determ |> DISCH_ALL |> Q.GENL[`ext`,`cl`,`fs`]
  |> SIMP_RULE bool_ss [SKOLEM_THM,Once(GSYM RIGHT_EXISTS_IMP_THM)]);

val (hello_sem_sing,hello_output) =
  hello_io_events_def |> SPEC_ALL |> UNDISCH |> SPEC_ALL |> CONJ_PAIR

val compile_correct_applied =
  MATCH_MP compile_correct (cj 1 hello_compiled)
  |> SIMP_RULE(srw_ss())[LET_THM,ml_progTheory.init_state_env_thm,GSYM AND_IMP_INTRO]
  |> C MATCH_MP hello_not_fail
  |> C MATCH_MP x64_backend_config_ok
  |> REWRITE_RULE[hello_sem_sing,AND_IMP_INTRO]
  |> REWRITE_RULE[Once (GSYM AND_IMP_INTRO)]
  |> C MATCH_MP (CONJ(UNDISCH x64_machine_config_ok)(UNDISCH x64_init_ok))
  |> DISCH(#1(dest_imp(concl x64_init_ok)))
  |> REWRITE_RULE[AND_IMP_INTRO]

Theorem hello_compiled_thm =
  CONJ compile_correct_applied (hello_output |> Q.GEN ‘po’)
  |> DISCH_ALL
  |> check_thm
