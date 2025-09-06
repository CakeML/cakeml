(*
  Compose the semantics theorem and the compiler correctness
  theorem with the compiler evaluation theorem to produce end-to-end
  correctness theorem that reaches final machine code.
*)
Theory subgraph_isoProof
Ancestors
  semanticsProps backendProof x64_configProof TextIOProof
  subgraph_isoProg subgraph_isoCompile
Libs
  preamble

val cake_pb_iso_io_events_def = new_specification("cake_pb_iso_io_events_def",["cake_pb_iso_io_events"],
  main_semantics |> Q.GENL[`cl`,`fs`]
  |> SIMP_RULE bool_ss [SKOLEM_THM,Once(GSYM RIGHT_EXISTS_IMP_THM)]);

val (cake_pb_iso_sem,cake_pb_iso_output) = cake_pb_iso_io_events_def |> SPEC_ALL |> UNDISCH |> SIMP_RULE std_ss [GSYM PULL_EXISTS]|> CONJ_PAIR
val (cake_pb_iso_not_fail,cake_pb_iso_sem_sing) = cake_pb_iso_sem
  |> SRULE [subgraph_iso_compiled,ml_progTheory.prog_syntax_ok_semantics]
  |> MATCH_MP semantics_prog_Terminate_not_Fail |> CONJ_PAIR

val compile_correct_applied =
  MATCH_MP compile_correct (cj 1 subgraph_iso_compiled)
  |> SIMP_RULE(srw_ss())[LET_THM,ml_progTheory.init_state_env_thm,GSYM AND_IMP_INTRO]
  |> C MATCH_MP cake_pb_iso_not_fail
  |> C MATCH_MP x64_backend_config_ok
  |> REWRITE_RULE[cake_pb_iso_sem_sing,AND_IMP_INTRO]
  |> REWRITE_RULE[Once (GSYM AND_IMP_INTRO)]
  |> C MATCH_MP (CONJ(UNDISCH x64_machine_config_ok)(UNDISCH x64_init_ok))
  |> DISCH(#1(dest_imp(concl x64_init_ok)))
  |> REWRITE_RULE[AND_IMP_INTRO]

Theorem cake_pb_iso_compiled_thm =
  CONJ compile_correct_applied cake_pb_iso_output
  |> DISCH_ALL
  (* |> check_thm *)

(* Prettifying the standard parts of all the theorems *)
Definition installed_x64_def:
  installed_x64 ((code, data, cfg) :
      (word8 list # word64 list # 64 backend$config))
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

Definition cake_pb_iso_code_def:
  cake_pb_iso_code = (code, data, info)
End

(* A standard run of cake_pb_subgraph_iso
  satisfying all the default assumptions *)
Definition cake_pb_iso_run_def:
  cake_pb_iso_run cl fs mc ms ⇔
  wfcl cl ∧ wfFS fs ∧ STD_streams fs ∧ hasFreeFD fs ∧
  installed_x64 cake_pb_iso_code mc ms
End

Theorem machine_code_sound:
  cake_pb_iso_run cl fs mc ms ⇒
  machine_sem mc (basis_ffi cl fs) ms ⊆
    extend_with_resource_limit
      {Terminate Success (cake_pb_iso_io_events cl fs)} ∧
  ∃out err.
    extract_fs fs (cake_pb_iso_io_events cl fs) =
      SOME (add_stdout (add_stderr fs err) out) ∧
    (out ≠ strlit"" ⇒
      ∃gp gt.
        get_graph_lad fs (EL 1 cl) = SOME gp ∧
        get_graph_lad fs (EL 2 cl) = SOME gt ∧
        (
          (LENGTH cl = 3 ∧
            out = concat (print_prob (mk_prob (full_encode gp gt)))) ∨
          (LENGTH cl = 4 ∧
            (
              (out = «s VERIFIED NOT SUBGRAPH ISOMORPHIC\n» ∧
                ¬ has_subgraph_iso gp gt) ∨
              (out = «s VERIFIED SUBGRAPH ISOMORPHIC\n» ∧
                has_subgraph_iso gp gt)
            ))
        )
    )
Proof
  strip_tac>>
  fs[installed_x64_def,cake_pb_iso_code_def,cake_pb_iso_run_def]>>
  drule cake_pb_iso_compiled_thm>>
  simp[AND_IMP_INTRO]>>
  disch_then drule>>
  disch_then (qspecl_then [`ms`,`mc`,`data_sp`,`cbspace`] mp_tac)>>
  simp[]>> strip_tac>>
  fs[main_sem_def]>>
  every_case_tac>>fs[]
  >- (
    qexists_tac`out`>>qexists_tac`err`>>simp[]>>
    fs[check_unsat_3_sem_def]>>
    strip_tac>>
    gvs[]>>
    EVAL_TAC)
  >- (
    qexists_tac`out`>>qexists_tac`err`>>simp[]>>
    fs[check_unsat_2_sem_def]>>
    strip_tac>>
    every_case_tac>>fs[])>>
  metis_tac[]
QED

val chk = machine_code_sound |> check_thm;

