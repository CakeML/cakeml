(*
  Compose the semantics theorem and the compiler correctness
  theorem with the compiler evaluation theorem to produce end-to-end
  correctness theorem that reaches final machine code.
*)
Theory lpr_arrayPackingProof
Ancestors
  semanticsProps backendProof x64_configProof TextIOProof satSem
  lpr lpr_list lpr_arrayPackingProg lpr_parsing
  lpr_arrayPackingCompile lpr_composeProg lpr_list packing
Libs
  preamble

val main_terminate = UNDISCH_ALL main_semantics
  |> SIMP_RULE bool_ss [RIGHT_EXISTS_AND_THM]
  |> HO_MATCH_MP ml_progTheory.sem_satisfies_IMP_Terminate
  |> SRULE [lpr_packing_compiled];

Theorem main_compiled_thm =
  MATCH_MP compile_correct (cj 1 lpr_packing_compiled)
  |> SIMP_RULE(srw_ss())[LET_THM,ml_progTheory.init_state_env_thm,GSYM AND_IMP_INTRO]
  |> C MATCH_MP (cj 1 main_terminate)
  |> C MATCH_MP x64_backend_config_ok
  |> Q.GEN ‘mc’ |> ISPEC (x64_init_ok |> concl |> rand |> rand) |> UNDISCH_ALL
  |> MATCH_MP (cj 2 main_terminate)
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

Definition main_code_def:
  main_code = (code, data, info)
End

(* A standard run of packing satisfying all the default assumptions *)
Definition packing_run_def:
  packing_run cl fs mc ms ⇔
  wfcl cl ∧ wfFS fs ∧ STD_streams fs ∧ hasFreeFD fs ∧
  installed_x64 main_code mc ms
End

Theorem parse_numbers_imp:
  parse_numbers rs ks cs = SOME (r,k,c) ⇒
  c ≥ 1 ∧ c ≤ k
Proof
  rw[parse_numbers_def]>>
  every_case_tac>>fs[]
QED

Theorem machine_code_sound:
  packing_run cl fs mc ms ⇒
  ∃io.
  machine_sem mc (basis_ffi ext cl fs) ms ⊆
    extend_with_resource_limit {Terminate Success io} ∧
  ∃out err.
    extract_fs ext (cl,fs) io =
      SOME (add_stdout (add_stderr fs err) out) ∧
  if LENGTH cl = 4 then
    case parse_numbers (EL 1 cl) (EL 2 cl) (EL 3 cl) of
      SOME (r,k,c) =>
        ∃fml.
          out = concat (print_dimacs fml) ∧
          (unsatisfiable (interp fml) ⇒
            ∀f. ¬ is_plane_packing_col f k)
    | NONE => out = «»
  else out = «»
Proof
  strip_tac>>
  fs[installed_x64_def,main_code_def,packing_run_def]>>
  drule_all main_compiled_thm>>
  disch_then (qspec_then `ext` strip_assume_tac)>>
  goal_assum drule>>
  qpat_x_assum `result = _` SUBST_ALL_TAC>>
  fs[main_sem_def]>>
  Cases_on`cl`>>fs[]
  >- (
    (* 0 arg *)
    fs[CommandLineProofTheory.wfcl_def])>>
  TOP_CASE_TAC>>fs[]
  >- metis_tac[STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil]>>
  TOP_CASE_TAC>>fs[]
  >- metis_tac[STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil]>>
  TOP_CASE_TAC>>fs[]
  >- metis_tac[STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil]>>
  reverse (TOP_CASE_TAC>>fs[])
  >- metis_tac[STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil]>>
  simp[check_unsat_3_sem_def]>>
  TOP_CASE_TAC>>fs[]
  >- metis_tac[STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil]>>
  PairCases_on`x`>>simp[]>>
  qmatch_goalsub_abbrev_tac`add_stdout fs ls`>>
  qexists_tac`ls`>>qexists_tac`«»`>>
  `add_stderr fs «» = fs` by
    (match_mp_tac (GEN_ALL add_stdo_nil)>>
    metis_tac[STD_streams_stderr])>>
  simp[Abbr`ls`]>>
  drule parse_numbers_imp>>
  strip_tac>>
  metis_tac[unsat_is_plane_packing]
QED
