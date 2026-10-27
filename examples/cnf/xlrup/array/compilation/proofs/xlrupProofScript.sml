(*
  Compose the semantics theorem and the compiler correctness
  theorem with the compiler evaluation theorem to produce end-to-end
  correctness theorem that reaches final machine code.
*)
Theory xlrupProof
Ancestors
  semanticsProps backendProof x64_configProof TextIOProof
  xlrup_cnf xlrup xlrup_arrayFullProg xlrupCompile
Libs
  preamble

val cake_xlrup_terminate = UNDISCH_ALL check_unsat_semantics
  |> SIMP_RULE bool_ss [RIGHT_EXISTS_AND_THM]
  |> HO_MATCH_MP ml_progTheory.sem_satisfies_IMP_Terminate
  |> SRULE [xlrup_array_compiled];

Theorem cake_xlrup_compiled_thm =
  MATCH_MP compile_correct (cj 1 xlrup_array_compiled)
  |> SIMP_RULE(srw_ss())[LET_THM,ml_progTheory.init_state_env_thm,GSYM AND_IMP_INTRO]
  |> C MATCH_MP (cj 1 cake_xlrup_terminate)
  |> C MATCH_MP x64_backend_config_ok
  |> Q.GEN ‘mc’ |> ISPEC (x64_init_ok |> concl |> rand |> rand) |> UNDISCH_ALL
  |> MATCH_MP (cj 2 cake_xlrup_terminate)
  |> REWRITE_RULE [targetPropsTheory.machine_sem_sing] |> DISCH_ALL
  |> CONJ (UNDISCH is_x64_machine_config_IMP)
  |> SRULE [SF CONJ_ss] |> CONJUNCT2 |> DISCH_ALL
  |> REWRITE_RULE [AND_IMP_INTRO, GSYM CONJ_ASSOC]
  |> check_thm

(* Prettifying the standard parts of all the theorems *)
Definition installed_x64_def:
  installed_x64 ((code, data, cfg) :
      (word8 list # num list # backend$config))
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

Definition cake_xlrup_code_def:
  cake_xlrup_code = (code, data, info)
End

(* A standard run of cake_xlrup satisfying all the default assumptions *)
Definition cake_xlrup_run_def:
  cake_xlrup_run cl fs mc ms ⇔
  wfcl cl ∧ wfFS fs ∧ STD_streams fs ∧ hasFreeFD fs ∧
  (reads_stdin cl ⇒ stdin_content fs ≠ NONE) ∧
  installed_x64 cake_xlrup_code mc ms
End

Theorem machine_code_sound:
  cake_xlrup_run cl fs mc ms ⇒
  ∃io.
  machine_sem mc (basis_ffi ext cl fs) ms ⊆
    extend_with_resource_limit {Terminate Success io} ∧
  ∃k out err.
    extract_fs ext (cl,fs) io =
      SOME (add_stdout (add_stderr (forwardFD fs 0 k) err) out) ∧
  case split_flags (T,F) (TL cl) of
    (SOME (b,T), [f1]) =>
      (case get_cnf_ext fs f1 of
        NONE => out = «»
      | SOME fml => out = concat (print_cnf_ext fml))
  | (SOME (b,F), [f1]) =>
      (out ≠ «» ⇒
        out = «s VERIFIED UNSAT\n» ∧
        ∃fml. get_cnf_ext fs f1 = SOME fml ∧ sols fml = {})
  | (SOME (b,F), [f1; f2]) =>
      (out ≠ «» ⇒
        out = «s VERIFIED UNSAT\n» ∧
        ∃fml. get_cnf_ext fs f1 = SOME fml ∧ sols fml = {})
  | _ => out = «»
Proof
  strip_tac>>
  fs[installed_x64_def,cake_xlrup_code_def,cake_xlrup_run_def]>>
  drule_at (Pos last) cake_xlrup_compiled_thm>>
  simp[AND_IMP_INTRO]>>
  disch_then drule>>
  disch_then (qspecl_then [`ms`,`ext`,`data_sp`,`cl`,`cbspace`] mp_tac)>>
  simp[]>>strip_tac>>
  qexists_tac`io_events`>>simp[]>>
  qexistsl_tac[`k`,`out`,`err`]>>
  gvs[check_unsat_sem_def,check_unsat_1_sem_def,check_unsat_2_sem_def]
QED
