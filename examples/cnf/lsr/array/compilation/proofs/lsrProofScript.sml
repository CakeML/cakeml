(*
  Compose the semantics theorem and the compiler correctness
  theorem with the compiler evaluation theorem to produce end-to-end
  correctness theorem that reaches final machine code.
*)
Theory lsrProof
Ancestors
  semanticsProps backendProof x64_configProof TextIOProof
  x64_config dimacs lsr lsr_arrayFullProg lsrCompile
Libs
  preamble

val cake_lsr_terminate = UNDISCH_ALL check_unsat_semantics
  |> SIMP_RULE bool_ss [RIGHT_EXISTS_AND_THM]
  |> HO_MATCH_MP ml_progTheory.sem_satisfies_IMP_Terminate
  |> SRULE [lsr_array_compiled];

(* The configuration differs from x64_backend_config only in max_app, which
  backend_config_ok and mc_init_ok constrain only to be positive *)
Theorem x64_backend_config_ok':
  backend_config_ok x64_config x64_config'
Proof
  assume_tac x64_backend_config_ok>>
  fs[backend_config_ok_def,x64_config'_def]>>
  EVAL_TAC
QED

Theorem x64_init_ok':
  is_x64_machine_config mc ⇒
  mc_init_ok x64_config x64_config' mc
Proof
  strip_tac>>
  drule x64_init_ok>>
  simp[mc_init_ok_def,x64_config'_def]
QED

Theorem x64_config'_stack_conf:
  x64_config'.stack_conf = x64_backend_config.stack_conf
Proof
  simp[x64_config'_def]
QED

Theorem cake_lsr_compiled_thm =
  MATCH_MP compile_correct (cj 1 lsr_array_compiled)
  |> SIMP_RULE(srw_ss())[LET_THM,ml_progTheory.init_state_env_thm,GSYM AND_IMP_INTRO]
  |> C MATCH_MP (cj 1 cake_lsr_terminate)
  |> C MATCH_MP x64_backend_config_ok'
  |> REWRITE_RULE[x64_config'_stack_conf]
  |> Q.GEN ‘mc’ |> ISPEC (x64_init_ok' |> concl |> rand |> rand) |> UNDISCH_ALL
  |> MATCH_MP (cj 2 cake_lsr_terminate)
  |> REWRITE_RULE [targetPropsTheory.machine_sem_sing] |> DISCH_ALL
  |> CONJ (CONJ (UNDISCH x64_machine_config_ok) (UNDISCH x64_init_ok'))
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

Definition cake_lsr_code_def:
  cake_lsr_code = (code, data, info)
End

(* A standard run of cake_lsr satisfying all the default assumptions *)
Definition cake_lsr_run_def:
  cake_lsr_run cl fs mc ms ⇔
  wfcl cl ∧ wfFS fs ∧ STD_streams fs ∧ hasFreeFD fs ∧
  installed_x64 cake_lsr_code mc ms
End

Theorem machine_code_sound:
  cake_lsr_run cl fs mc ms ⇒
  ∃io.
  machine_sem mc (basis_ffi ext cl fs) ms ⊆
    extend_with_resource_limit {Terminate Success io} ∧
  ∃out err.
    extract_fs ext (cl,fs) io =
      SOME (add_stdout (add_stderr fs err) out) ∧
  if LENGTH cl = 2 then
    (case get_cnf fs (EL 1 cl) of
      NONE => out = «»
    | SOME fml => out = concat (print_cnf (max_cnf fml) fml))
  else if LENGTH cl = 3 then
    (out ≠ «» ⇒
      out = «s VERIFIED UNSAT\n» ∧
      ∃fml. get_cnf fs (EL 1 cl) = SOME fml ∧ unsatisfiable_cnf (set fml))
  else out = «»
Proof
  strip_tac>>
  fs[installed_x64_def,cake_lsr_code_def,cake_lsr_run_def]>>
  drule_all cake_lsr_compiled_thm>>
  disch_then (qspec_then `ext` strip_assume_tac)>>
  goal_assum drule>>
  qpat_x_assum `result = _` SUBST_ALL_TAC>>
  qexists_tac`out`>>qexists_tac`err`>>
  gvs[check_unsat_sem_def,check_unsat_1_sem_def,check_unsat_2_sem_def]
QED
