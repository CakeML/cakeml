(*
  Compose the semantics theorem and the compiler correctness
  theorem with the compiler evaluation theorem to produce end-to-end
  correctness theorem that reaches final machine code.
*)
Theory colourProof
Ancestors
  semanticsProps backendProof x64_configProof TextIOProof
  colourProg colour colourCompile
Libs
  preamble

val cake_pb_colour_terminate = UNDISCH_ALL main_semantics
  |> SIMP_RULE bool_ss [RIGHT_EXISTS_AND_THM]
  |> HO_MATCH_MP ml_progTheory.sem_satisfies_IMP_Terminate
  |> SRULE [colour_compiled];

Theorem cake_pb_colour_compiled_thm =
  MATCH_MP compile_correct (cj 1 colour_compiled)
  |> SIMP_RULE(srw_ss())[LET_THM,ml_progTheory.init_state_env_thm,GSYM AND_IMP_INTRO]
  |> C MATCH_MP (cj 1 cake_pb_colour_terminate)
  |> C MATCH_MP x64_backend_config_ok
  |> Q.GEN ‘mc’ |> ISPEC (x64_init_ok |> concl |> rand |> rand) |> UNDISCH_ALL
  |> MATCH_MP (cj 2 cake_pb_colour_terminate)
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

Definition cake_pb_colour_code_def:
  cake_pb_colour_code = (code, data, info)
End

(* A standard run of cake_pb_colour
  satisfying all the default assumptions *)
Definition cake_pb_colour_run_def:
  cake_pb_colour_run cl fs mc ms ⇔
  wfcl cl ∧ wfFS fs ∧ STD_streams fs ∧ hasFreeFD fs ∧
  installed_x64 cake_pb_colour_code mc ms
End

Theorem machine_code_sound:
  cake_pb_colour_run cl fs mc ms ⇒
  ∃io.
  machine_sem mc (basis_ffi ext cl fs) ms ⊆
    extend_with_resource_limit {Terminate Success io} ∧
  ∃out err.
    extract_fs ext (cl,fs) io =
      SOME (add_stdout (add_stderr fs err) out) ∧
    (out ≠ «» ⇒
      ∃g.
        get_graph_dimacs fs (EL 1 cl) = SOME g ∧
        (
          (LENGTH cl = 2 ∧
            out = concat (print_annot_prob (mk_prob (full_encode (FST g) g)))) ∨
          (LENGTH cl = 5 ∧
            ∃k f.
              get_col fs (EL 4 cl) = SOME (k,f) ∧
              is_k_colour k f g ∧
              (out = colour_eq_str (min_colour g) ∨
              ∃l.
                out = colour_bound_str l k ∧
                (∀k' f'. is_k_colour k' f' g ⇒ l ≤ k')))
        )
    )
Proof
  strip_tac>>
  fs[installed_x64_def,cake_pb_colour_code_def,cake_pb_colour_run_def]>>
  drule_all cake_pb_colour_compiled_thm>>
  disch_then (qspec_then `ext` strip_assume_tac)>>
  goal_assum drule>>
  qpat_x_assum `result = _` SUBST_ALL_TAC>>
  fs[main_sem_def]>>
  pop_assum mp_tac>>
  rpt (IF_CASES_TAC)>>
  strip_tac
  >- (
    qexists_tac`out`>>qexists_tac`err`>>simp[]>>
    fs[check_unsat_1_sem_def]>>
    every_case_tac>>gvs[])
  >- (
    qexists_tac`out`>>qexists_tac`err`>>simp[]>>
    fs[check_unsat_4_sem_def]>>
    strip_tac>>
    gvs[]>>
    qpat_x_assum`colour_sem _ _ _ _` mp_tac>>
    simp[colour_sem_def,print_colour_str_def]>>
    rw[]>>
    metis_tac[])>>
  metis_tac[]
QED

val chk = machine_code_sound |> check_thm;
