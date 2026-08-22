(*
  Compose the semantics theorem and the compiler correctness
  theorem with the compiler evaluation theorem to produce end-to-end
  correctness theorem that reaches final machine code.
*)
Theory lrupProof
Ancestors
  semanticsProps backendProof x64_configProof TextIOProof
  lrup_cnf lrup lrup_arrayFullProg lrupCompile
Libs
  preamble

val cake_lrup_io_events_def = new_specification("cake_lrup_io_events_def",["cake_lrup_io_events"],
  check_unsat_semantics |> Q.GENL[`ext`,`cl`,`fs`]
  |> SIMP_RULE bool_ss [SKOLEM_THM,Once(GSYM RIGHT_EXISTS_IMP_THM)]);

val (cake_lrup_sem,cake_lrup_output) = cake_lrup_io_events_def |> SPEC_ALL |> UNDISCH |> SIMP_RULE std_ss [GSYM PULL_EXISTS]|> CONJ_PAIR
val (cake_lrup_not_fail,cake_lrup_sem_sing) = cake_lrup_sem
  |> SRULE [lrup_array_compiled,ml_progTheory.prog_syntax_ok_semantics]
  |> MATCH_MP semantics_prog_Terminate_not_Fail |> CONJ_PAIR

val compile_correct_applied =
  MATCH_MP compile_correct (cj 1 lrup_array_compiled)
  |> SIMP_RULE(srw_ss())[LET_THM,ml_progTheory.init_state_env_thm,GSYM AND_IMP_INTRO]
  |> C MATCH_MP cake_lrup_not_fail
  |> C MATCH_MP x64_backend_config_ok
  |> REWRITE_RULE[cake_lrup_sem_sing,AND_IMP_INTRO]
  |> REWRITE_RULE[Once (GSYM AND_IMP_INTRO)]
  |> C MATCH_MP (CONJ(UNDISCH x64_machine_config_ok)(UNDISCH x64_init_ok))
  |> DISCH(#1(dest_imp(concl x64_init_ok)))
  |> REWRITE_RULE[AND_IMP_INTRO]

Theorem cake_lrup_compiled_thm =
  CONJ compile_correct_applied cake_lrup_output
  |> DISCH_ALL
  |> check_thm

(* Prettifying the standard parts of all the theorems *)
Definition installed_x64_def:
  installed_x64 ((code, data, cfg) :
      (word8 list # word64 list # backend$config))
    mc ms
  <=>
    ?cbspace data_sp.
      is_x64_machine_config mc /\
      installed
        code cbspace
        data data_sp
        cfg.lab_conf.ffi_names
        (heap_regs x64_backend_config.stack_conf.reg_names) mc
        cfg.lab_conf.shmem_extra ms
End

Definition cake_lrup_code_def:
  cake_lrup_code = (code, data, info)
End

(* A standard run of cake_lrup satisfying all the default assumptions *)
Definition cake_lrup_run_def:
  cake_lrup_run cl fs mc ms ⇔
  wfcl cl ∧ wfFS fs ∧ STD_streams fs ∧ hasFreeFD fs ∧
  installed_x64 cake_lrup_code mc ms
End

Theorem machine_code_sound:
  cake_lrup_run cl fs mc ms ⇒
  machine_sem mc (basis_ffi ext cl fs) ms ⊆
    extend_with_resource_limit
      {Terminate Success (cake_lrup_io_events ext cl fs)} ∧
  ∃out err.
    extract_fs ext (cl,fs) (cake_lrup_io_events ext cl fs) =
      SOME (add_stdout (add_stderr fs err) out) ∧
  if LENGTH cl = 2 then
    (case get_cnf fs (EL 1 cl) of
      NONE => out = «»
    | SOME fml => out = concat (print_cnf fml))
  else if LENGTH cl = 3 then
    (out ≠ «» ⇒
      out = «s VERIFIED UNSAT\n» ∧
      ∃fml. get_cnf fs (EL 1 cl) = SOME fml ∧ sols fml = {})
  else out = «»
Proof
  strip_tac>>
  fs[installed_x64_def,cake_lrup_code_def,cake_lrup_run_def]>>
  drule_at (Pos last) cake_lrup_compiled_thm>>
  simp[AND_IMP_INTRO]>>
  disch_then drule>>
  disch_then (qspecl_then [`ms`,`mc`,`ext`,`data_sp`,`cbspace`] mp_tac)>>
  simp[]>>strip_tac>>
  qexists_tac`out`>>qexists_tac`err`>>
  gvs[check_unsat_sem_def,check_unsat_1_sem_def,check_unsat_2_sem_def]
QED
