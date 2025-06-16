(*
  Compose the semantics theorem and the compiler correctness
  theorem with the compiler evaluation theorem to produce end-to-end
  correctness theorem that reaches final machine code.
*)
open preamble
     semanticsPropsTheory backendProofTheory x64_configProofTheory
     TextIOProofTheory
     cliqueProgTheory
     cliqueTheory cliqueCompileTheory;

val _ = new_theory"cliqueProof";

val cake_pb_clique_io_events_def = new_specification("cake_pb_clique_io_events_def",["cake_pb_clique_io_events"],
  main_semantics |> Q.GENL[`cl`,`fs`]
  |> SIMP_RULE bool_ss [SKOLEM_THM,Once(GSYM RIGHT_EXISTS_IMP_THM)]);

val (cake_pb_clique_sem,cake_pb_clique_output) = cake_pb_clique_io_events_def |> SPEC_ALL |> UNDISCH |> SIMP_RULE std_ss [GSYM PULL_EXISTS]|> CONJ_PAIR
val (cake_pb_clique_not_fail,cake_pb_clique_sem_sing) = cake_pb_clique_sem
  |> SRULE [clique_compiled,ml_progTheory.prog_syntax_ok_semantics]
  |> MATCH_MP semantics_prog_Terminate_not_Fail |> CONJ_PAIR

val compile_correct_applied =
  MATCH_MP compile_correct (cj 1 clique_compiled)
  |> SIMP_RULE(srw_ss())[LET_THM,ml_progTheory.init_state_env_thm,GSYM AND_IMP_INTRO]
  |> C MATCH_MP cake_pb_clique_not_fail
  |> C MATCH_MP x64_backend_config_ok
  |> REWRITE_RULE[cake_pb_clique_sem_sing,AND_IMP_INTRO]
  |> REWRITE_RULE[Once (GSYM AND_IMP_INTRO)]
  |> C MATCH_MP (CONJ(UNDISCH x64_machine_config_ok)(UNDISCH x64_init_ok))
  |> DISCH(#1(dest_imp(concl x64_init_ok)))
  |> REWRITE_RULE[AND_IMP_INTRO]

Theorem cake_pb_clique_compiled_thm =
  CONJ compile_correct_applied cake_pb_clique_output
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

Definition cake_pb_clique_code_def:
  cake_pb_clique_code = (code, data, info)
End

(* A standard run of cake_pb_clique
  satisfying all the default assumptions *)
Definition cake_pb_clique_run_def:
  cake_pb_clique_run cl fs mc ms ⇔
  wfcl cl ∧ wfFS fs ∧ STD_streams fs ∧ hasFreeFD fs ∧
  installed_x64 cake_pb_clique_code mc ms
End

Theorem machine_code_sound:
  cake_pb_clique_run cl fs mc ms ⇒
  machine_sem mc (basis_ffi cl fs) ms ⊆
    extend_with_resource_limit
      {Terminate Success (cake_pb_clique_io_events cl fs)} ∧
  ∃out err.
    extract_fs fs (cake_pb_clique_io_events cl fs) =
      SOME (add_stdout (add_stderr fs err) out) ∧
    (out ≠ strlit"" ⇒
      ∃g.
        get_graph_dimacs fs (EL 1 cl) = SOME g ∧
        (
          (LENGTH cl = 2 ∧
            out = concat (print_annot_prob (mk_prob (full_encode g)))) ∨
          (LENGTH cl = 3 ∧
            (
              out = clique_eq_str (max_clique_size g) ∨
              ∃l u.
                out = clique_bound_str l u ∧
                (∀vs. is_clique vs g ⇒ CARD vs ≤ u) ∧
                (∃vs. is_clique vs g ∧ l ≤ CARD vs)
            ))
        )
    )
Proof
  strip_tac>>
  fs[installed_x64_def,cake_pb_clique_code_def,cake_pb_clique_run_def]>>
  drule cake_pb_clique_compiled_thm>>
  simp[AND_IMP_INTRO]>>
  disch_then drule>>
  disch_then (qspecl_then [`ms`,`mc`,`data_sp`,`cbspace`] mp_tac)>>
  simp[]>> strip_tac>>
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
    fs[check_unsat_2_sem_def]>>
    strip_tac>>
    gvs[]>>
    Cases_on`bounds`>>
    qpat_x_assum`clique_sem _ _` mp_tac>>
    simp[clique_sem_def,print_clique_str_def]>>
    rw[]>>
    metis_tac[])>>
  metis_tac[]
QED

val chk = machine_code_sound |> check_thm;

val _ = export_theory();
