(*
  Compose the hello semantics theorem and the compiler correctness
  theorem with the compiler evaluation theorem to produce end-to-end
  correctness theorem that reaches final machine code.
*)
open preamble
     semanticsPropsTheory backendProofTheory ag32_configProofTheory
     ag32_memoryTheory ag32_memoryProofTheory ag32_ffi_codeProofTheory
     ag32_machine_configTheory ag32_basis_ffiProofTheory
     helloProgTheory helloCompileTheory;

val _ = new_theory"helloProof";

val hello_io_events_def =
  new_specification("hello_io_events_def",["hello_io_events"],
  hello_semantics |> Q.GENL[`cl`,`fs`]
  |> SIMP_RULE std_ss [GSYM RIGHT_EXISTS_IMP_THM]
  |> SIMP_RULE std_ss [SKOLEM_THM]);

val (hello_sem,hello_output) = hello_io_events_def |> SPEC_ALL |> UNDISCH |> CONJ_PAIR
val (hello_not_fail,hello_sem_sing) = MATCH_MP semantics_prog_Terminate_not_Fail hello_sem |> CONJ_PAIR

val ffi_names =
  ``config.ffi_names``
  |> (REWRITE_CONV[helloCompileTheory.config_def] THENC EVAL)

val LENGTH_code =
  ``LENGTH code``
  |> (REWRITE_CONV[helloCompileTheory.code_def] THENC listLib.LENGTH_CONV)

val LENGTH_data =
  ``LENGTH data``
  |> (REWRITE_CONV[helloCompileTheory.data_def] THENC listLib.LENGTH_CONV)

val _ = overload_on("hello_machine_config",
    ``ag32_machine_config (THE config.ffi_names) (LENGTH code) (LENGTH data)``);

Theorem target_state_rel_hello_start_asm_state:
   SUM (MAP strlen cl) + LENGTH cl ≤ cline_size ∧
   LENGTH inp ≤ stdin_size ∧
   is_ag32_init_state (init_memory code data (THE config.ffi_names) (cl,inp)) ms ⇒
   ∃n. target_state_rel ag32_target (init_asm_state code data (THE config.ffi_names) (cl,inp)) (FUNPOW Next n ms) ∧
       ((FUNPOW Next n ms).io_events = ms.io_events) ∧
       (∀x. x ∉ (ag32_startup_addresses) ⇒
         ((FUNPOW Next n ms).MEM x = ms.MEM x))
Proof
  strip_tac
  \\ drule (GEN_ALL init_asm_state_RTC_asm_step)
  \\ disch_then drule
  \\ simp_tac std_ss []
  \\ disch_then(qspecl_then[`code`,`data`,`THE config.ffi_names`]mp_tac)
  \\ impl_tac >- ( EVAL_TAC>> fs[ffi_names,LENGTH_data,LENGTH_code])
  \\ strip_tac
  \\ drule (GEN_ALL target_state_rel_ag32_init)
  \\ rveq
  \\ qmatch_goalsub_abbrev_tac`_ ∉ md`
  \\ disch_then(qspec_then`md`assume_tac)
  \\ drule (GEN_ALL RTC_asm_step_ag32_target_state_rel_io_events)
  \\ simp[EVAL``(ag32_init_asm_state m md).mem_domain``]
QED

val hello_startup_clock_def =
  new_specification("hello_startup_clock_def",["hello_startup_clock"],
  GEN_ALL (Q.SPEC`ms0`(Q.GEN`ms`target_state_rel_hello_start_asm_state))
  |> SIMP_RULE bool_ss [GSYM RIGHT_EXISTS_IMP_THM,SKOLEM_THM]);

val compile_correct_applied =
  MATCH_MP compile_correct hello_compiled
  |> SIMP_RULE(srw_ss())[LET_THM,ml_progTheory.init_state_env_thm,GSYM AND_IMP_INTRO]
  |> C MATCH_MP hello_not_fail
  |> C MATCH_MP ag32_backend_config_ok
  |> REWRITE_RULE[hello_sem_sing,AND_IMP_INTRO]
  |> REWRITE_RULE[Once (GSYM AND_IMP_INTRO)]
  |> C MATCH_MP (CONJ(UNDISCH ag32_machine_config_ok)(UNDISCH ag32_init_ok))
  |> DISCH(#1(dest_imp(concl ag32_init_ok)))
  |> C MATCH_MP is_ag32_machine_config_ag32_machine_config
  |> Q.GEN`cbspace` |> Q.SPEC`0`
  |> Q.GEN`data_sp` |> Q.SPEC`0`

Theorem hello_installed:
   SUM (MAP strlen cl) + LENGTH cl ≤ cline_size ∧
   LENGTH inp ≤ stdin_size ∧
   is_ag32_init_state (init_memory code data (THE config.ffi_names) (cl,inp)) ms0 ⇒
   installed code 0 data 0 config.ffi_names (basis_ffi cl fs)
     (heap_regs ag32_backend_config.stack_conf.reg_names)
     (hello_machine_config) (FUNPOW Next (hello_startup_clock ms0 inp cl) ms0)
Proof
  rewrite_tac[ffi_names, THE_DEF]
  \\ strip_tac
  \\ irule ag32_installed
  \\ drule hello_startup_clock_def
  \\ disch_then drule
  \\ rewrite_tac[ffi_names, THE_DEF]
  \\ disch_then drule
  \\ strip_tac
  \\ simp[]
  \\ conj_tac >- (simp[LENGTH_code] \\ EVAL_TAC)
  \\ conj_tac >- (simp[LENGTH_code, LENGTH_data] \\ EVAL_TAC)
  \\ conj_tac >- (EVAL_TAC)
  \\ asm_exists_tac
  \\ simp[]
  \\ fs[ffi_names]
QED

val hello_machine_sem =
  compile_correct_applied
  |> C MATCH_MP (UNDISCH hello_installed)
  |> DISCH_ALL
  |> curry save_thm "hello_machine_sem";

Theorem hello_extract_writes_stdout:
   wfcl cl ⇒
   (extract_writes 1 (MAP get_output_io_event (hello_io_events cl (stdin_fs inp))) =
    "Hello World!\n")
Proof
  strip_tac
  \\ drule(GEN_ALL(DISCH_ALL hello_output))
  \\ disch_then(qspec_then`stdin_fs inp`mp_tac)
  \\ simp[wfFS_stdin_fs, STD_streams_stdin_fs]
  \\ simp[TextIOProofTheory.add_stdo_def]
  \\ SELECT_ELIM_TAC
  \\ simp[TextIOProofTheory.stdo_def]
  \\ conj_tac
  >- (
    simp[stdin_fs_def]
    \\ qexists_tac`implode""`
    \\ simp[] )
  \\ simp[Once stdin_fs_def, AFUPDKEY_def]
  \\ Cases \\ simp[] \\ strip_tac \\ rveq
  \\ pop_assum mp_tac
  \\ simp[TextIOProofTheory.up_stdo_def]
  \\ simp[fsFFITheory.fsupdate_def]
  \\ simp[stdin_fs_def]
  \\ rw[]
  \\ drule (GEN_ALL extract_fs_extract_writes)
  \\ simp[AFUPDKEY_ALOOKUP]
  \\ disch_then match_mp_tac
  \\ rw[fsFFIPropsTheory.inFS_fname_def]
  >- (fs[CaseEq"option",CaseEq"bool"] \\ rveq \\ fs[] \\
      Cases_on`v` >> qmatch_goalsub_abbrev_tac`(q,r)` >>
      Cases_on`r` >> rfs[] >> Cases_on`q = File fnm` >> rw[])
  >- (
    pop_assum mp_tac
    \\ rw[] \\ fs[] \\ rw[]
    \\ pop_assum mp_tac \\ rw[])
  >- rw[]
QED

Theorem hello_ag32_next:
   SUM (MAP strlen cl) + LENGTH cl ≤ cline_size ∧ wfcl cl ∧
   LENGTH inp ≤ stdin_size ∧
   is_ag32_init_state (init_memory code data (THE config.ffi_names) (cl,inp)) ms0
  ⇒
   ∃k1. ∀k. k1 ≤ k ⇒
     let ms = FUNPOW Next k ms0 in
     let outs = MAP (get_ag32_io_event) ms.io_events in
       (ms.PC = (hello_machine_config).halt_pc) ∧
       (get_mem_word ms.MEM ms.PC = Encode (Jump (fAdd,0w,Imm 0w))) ∧
       outs ≼ MAP get_output_io_event (hello_io_events cl (stdin_fs inp)) ∧
       ((ms.R (n2w (hello_machine_config).ptr_reg) = 0w) ⇒
        (outs = MAP get_output_io_event (hello_io_events cl (stdin_fs inp))))
Proof
  strip_tac
  \\ drule (GEN_ALL hello_machine_sem)
  \\ disch_then drule
  \\ disch_then drule
  \\ disch_then(qspec_then`stdin_fs inp`mp_tac)
  \\ impl_tac >- fs[STD_streams_stdin_fs, wfFS_stdin_fs]
  \\ strip_tac
  \\ irule ag32_next
  \\ conj_tac >- simp[ffi_names]
  \\ conj_tac >- (simp[ffi_names, LENGTH_code, LENGTH_data] \\ EVAL_TAC)
  \\ conj_tac >- (simp[ffi_names] \\ EVAL_TAC)
  \\ goal_assum(first_assum o mp_then Any mp_tac)
  \\ goal_assum(first_assum o mp_then Any mp_tac)
  \\ goal_assum(first_assum o mp_then Any mp_tac)
  \\ goal_assum(first_assum o mp_then Any mp_tac)
  \\ goal_assum(first_assum o mp_then Any mp_tac)
  \\ drule hello_startup_clock_def
  \\ disch_then drule
  \\ disch_then drule
  \\ strip_tac
  \\ goal_assum(first_assum o mp_then Any mp_tac)
  \\ goal_assum(first_assum o mp_then Any mp_tac)
  \\ metis_tac[]
QED

val _ = export_theory();
