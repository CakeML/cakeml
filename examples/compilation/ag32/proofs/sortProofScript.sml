(*
  Compose the sort semantics theorem and the compiler correctness
  theorem with the compiler evaluation theorem to produce end-to-end
  correctness theorem that reaches final machine code.
*)
open preamble
     semanticsPropsTheory backendProofTheory ag32_configProofTheory
     ag32_memoryTheory ag32_memoryProofTheory ag32_ffi_codeProofTheory
     ag32_machine_configTheory ag32_basis_ffiProofTheory
     sortProgTheory sortCompileTheory;

val _ = new_theory"sortProof";

Theorem sort_stdin_semantics:
  ∃io_events.
    semantics_prog (init_state (basis_ffi [strlit"sort"] (stdin_fs input))) init_env
      sort_prog (Terminate Success io_events) ∧
    (∃output. PERM output (lines_of (implode input)) ∧ SORTED mlstring_le output ∧
     (extract_fs (stdin_fs input) io_events =
      SOME (add_stdout (fastForwardFD (stdin_fs input) 0) (concat output))))
Proof
  qspecl_then[`stdin_fs input`,`[strlit"sort"]`]mp_tac (GEN_ALL sort_semantics)
  \\ `stdin (stdin_fs input) input 0` by EVAL_TAC
  \\ drule TextIOProofTheory.stdin_get_file_content
  \\ rw[wfFS_stdin_fs, STD_streams_stdin_fs, CommandLineProofTheory.wfcl_def, clFFITheory.validArg_def]
  \\ asm_exists_tac \\ rw[]
  \\ fs[valid_sort_result_def, fsFFIPropsTheory.all_lines_def]
  \\ rfs[TextIOProofTheory.stdin_def]
  \\ asm_exists_tac \\ simp[]
QED

val sort_io_events_def =
  new_specification("sort_io_events_def",["sort_io_events"],
  sort_stdin_semantics |> Q.GENL[`input`]
  |> SIMP_RULE std_ss [GSYM RIGHT_EXISTS_IMP_THM]
  |> SIMP_RULE std_ss [SKOLEM_THM]);

val (sort_sem,sort_output) = sort_io_events_def |> SPEC_ALL |> CONJ_PAIR
val (sort_not_fail,sort_sem_sing) = MATCH_MP semantics_prog_Terminate_not_Fail sort_sem |> CONJ_PAIR

val ffinames_to_string_list_def = backendTheory.ffinames_to_string_list_def;

Theorem extcalls_ffi_names:
  extcalls info.lab_conf.ffi_names = ffis
Proof
  rewrite_tac [sort_compiled]
  \\ qspec_tac (‘info.lab_conf.ffi_names’,‘xs’) \\ Cases
  \\ gvs [extcalls_def,ffinames_to_string_list_def,miscTheory.the_def]
  \\ Induct_on ‘x’
  \\ gvs [extcalls_def,ffinames_to_string_list_def,miscTheory.the_def]
  \\ Cases \\ gvs [extcalls_def,ffinames_to_string_list_def,miscTheory.the_def]
QED

val ffis = ffis_def |> CONV_RULE (RAND_CONV EVAL);
val ffi_names = extcalls_ffi_names |> SRULE [ffis]

val LENGTH_code = “LENGTH code” |> SCONV [sort_compiled];
val LENGTH_data = “LENGTH data” |> SCONV [sort_compiled];
val shmem = “info.lab_conf.shmem_extra” |> SCONV [sort_compiled];

Overload sort_machine_config =
  “ag32_machine_config (extcalls info.lab_conf.ffi_names) (LENGTH code) (LENGTH data)”

Theorem target_state_rel_sort_start_asm_state:
   SUM (MAP strlen cl) + LENGTH cl ≤ cline_size ∧
   LENGTH inp ≤ stdin_size ∧
   is_ag32_init_state (init_memory code data (extcalls info.lab_conf.ffi_names) (cl,inp)) ms ⇒
   ∃n. target_state_rel ag32_target (init_asm_state code data (extcalls info.lab_conf.ffi_names) (cl,inp)) (FUNPOW Next n ms) ∧
       ((FUNPOW Next n ms).io_events = ms.io_events) ∧
       (∀x. x ∉ (ag32_startup_addresses) ⇒
         ((FUNPOW Next n ms).MEM x = ms.MEM x))
Proof
  strip_tac
  \\ drule (GEN_ALL init_asm_state_RTC_asm_step)
  \\ disch_then drule
  \\ simp_tac std_ss []
  \\ disch_then(qspecl_then[`code`,`data`,`extcalls info.lab_conf.ffi_names`]mp_tac)
  \\ impl_tac >- ( EVAL_TAC>> fs[ffi_names,LENGTH_data,LENGTH_code,extcalls_def])
  \\ strip_tac
  \\ drule (GEN_ALL target_state_rel_ag32_init)
  \\ rveq
  \\ qmatch_goalsub_abbrev_tac`_ ∉ md`
  \\ disch_then(qspec_then`md`assume_tac)
  \\ drule (GEN_ALL RTC_asm_step_ag32_target_state_rel_io_events)
  \\ simp[EVAL``(ag32_init_asm_state m md).mem_domain``]
QED

val sort_startup_clock_def =
  new_specification("sort_startup_clock_def",["sort_startup_clock"],
  GEN_ALL (Q.SPEC`ms0`(Q.GEN`ms`target_state_rel_sort_start_asm_state))
  |> SIMP_RULE bool_ss [GSYM RIGHT_EXISTS_IMP_THM,SKOLEM_THM]);

val compile_correct_applied =
  MATCH_MP compile_correct (cj 1 sort_compiled)
  |> SIMP_RULE(srw_ss())[LET_THM,ml_progTheory.init_state_env_thm,
                         GSYM AND_IMP_INTRO]
  |> C MATCH_MP sort_not_fail
  |> C MATCH_MP ag32_backend_config_ok
  |> REWRITE_RULE[sort_sem_sing,AND_IMP_INTRO]
  |> REWRITE_RULE[Once (GSYM AND_IMP_INTRO)]
  |> C MATCH_MP (CONJ(UNDISCH ag32_machine_config_ok)(UNDISCH ag32_init_ok))
  |> DISCH(#1(dest_imp(concl ag32_init_ok)))
  |> C MATCH_MP is_ag32_machine_config_ag32_machine_config
  |> Q.GEN`cbspace` |> Q.SPEC`0`
  |> Q.GEN`data_sp` |> Q.SPEC`0`

Theorem sort_installed:
   SUM (MAP strlen cl) + LENGTH cl ≤ cline_size ∧
   LENGTH inp ≤ stdin_size ∧
   is_ag32_init_state (init_memory code data (extcalls info.lab_conf.ffi_names) (cl,inp)) ms0 ⇒
   installed code 0 data 0 info.lab_conf.ffi_names
     (heap_regs ag32_backend_config.stack_conf.reg_names)
     (sort_machine_config) info.lab_conf.shmem_extra
     (FUNPOW Next (sort_startup_clock ms0 inp cl) ms0)
Proof
  rewrite_tac[ffi_names, extcalls_def, shmem]
  \\ strip_tac
  \\ qmatch_asmsub_abbrev_tac ‘init_memory _ _ ff’
  \\ qmatch_goalsub_abbrev_tac ‘installed _ _ _ _ dd’
  \\ ‘dd = SOME (MAP ExtCall ff)’ by
   (unabbrev_all_tac
    \\ assume_tac (cj 1 sort_compiled)
    \\ drule ag32_configProofTheory.compile_imp_ffi_names
    \\ gvs [sort_compiled]
    \\ gvs [GSYM sort_compiled,ffis]
    \\ simp [backendTheory.set_oracle_def,
             ag32_configTheory.ag32_backend_config_def])
  \\ asm_rewrite_tac []
  \\ irule ag32_installed
  \\ drule sort_startup_clock_def
  \\ disch_then drule
  \\ rewrite_tac[ffi_names, extcalls_def]
  \\ unabbrev_all_tac
  \\ disch_then drule
  \\ strip_tac
  \\ simp[]
  \\ conj_tac >- (simp[LENGTH_code] \\ EVAL_TAC)
  \\ conj_tac >- (simp[LENGTH_code, LENGTH_data] \\ EVAL_TAC)
  \\ conj_tac >- (EVAL_TAC)
  \\ rpt $ goal_assum $ drule_at Any
  \\ simp[]
QED

Theorem sort_machine_sem =
  compile_correct_applied
  |> C MATCH_MP (
      sort_installed
       |> Q.GEN `cl`
       |> Q.SPEC `[strlit"sort"]`
       |> SIMP_RULE(srw_ss())[cline_size_def]
       |> UNDISCH)
  |> DISCH_ALL

(* TODO: theorems currently in ag32Bootstrap can make this shorter *)
Theorem sort_extract_writes_stdout:
   ∃output. PERM output (lines_of (implode input)) ∧ SORTED mlstring_le output ∧
   (extract_writes 1 (MAP get_output_io_event (sort_io_events input)) =
    explode (concat output))
Proof
  qspec_then`input`strip_assume_tac(GEN_ALL(DISCH_ALL sort_output))
  \\ asm_exists_tac
  \\ pop_assum mp_tac
  \\ DEP_REWRITE_TAC[TextIOProofTheory.add_stdout_fastForwardFD]
  \\ simp[STD_streams_stdin_fs]
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
  \\ simp[fsFFITheory.fsupdate_def, fsFFIPropsTheory.fastForwardFD_def]
  \\ simp[stdin_fs_def, AFUPDKEY_ALOOKUP, miscTheory.the_def]
  \\ rw[]
  \\ drule (GEN_ALL extract_fs_extract_writes)
  \\ simp[AFUPDKEY_ALOOKUP]
  \\ disch_then match_mp_tac
  \\ rw[fsFFIPropsTheory.inFS_fname_def]
  >- (fs[CaseEq"option",CaseEq"bool"] \\ rveq \\ fs[] \\
      Cases_on`v` >> qmatch_goalsub_abbrev_tac`(q,r)` >>
      Cases_on`r` >> rfs[] >> Cases_on`q = File fnm` >> rw[] \\
      DISJ1_TAC \\ Cases_on`v'` >>
      Cases_on`r` >> rfs[] >> Cases_on`q = File fnm` >> rw[])
  >- (
    pop_assum mp_tac
    \\ rw[] \\ fs[] \\ rw[]
    \\ pop_assum mp_tac \\ rw[])
  >- rw[OPTREL_def]
QED

Theorem sort_ag32_next:
   LENGTH inp ≤ stdin_size ∧
   is_ag32_init_state (init_memory code data (extcalls info.lab_conf.ffi_names) ([strlit"sort"],inp)) ms0
  ⇒
   ∃k1. ∀k. k1 ≤ k ⇒
     let ms = FUNPOW Next k ms0 in
     let outs = MAP (get_ag32_io_event) ms.io_events in
       (ms.PC = (sort_machine_config).halt_pc) ∧
       (get_mem_word ms.MEM ms.PC = Encode (Jump (fAdd,0w,Imm 0w))) ∧
       outs ≼ MAP get_output_io_event (sort_io_events inp) ∧
       ((ms.R (n2w (sort_machine_config).ptr_reg) = 0w) ⇒
        (outs = MAP get_output_io_event (sort_io_events inp)))
Proof
  strip_tac
  \\ drule (GEN_ALL sort_machine_sem)
  \\ disch_then drule
  \\ strip_tac
  \\ irule ag32_next
  \\ conj_tac >- simp[ffi_names,extcalls_def]
  \\ conj_tac >- (simp[ffi_names,extcalls_def, LENGTH_code, LENGTH_data] \\ EVAL_TAC)
  \\ conj_tac >- (simp[ffi_names,extcalls_def] \\ EVAL_TAC)
  \\ rpt $ goal_assum $ drule_at Any
  \\ drule_at Any sort_startup_clock_def
  \\ simp[]
  \\ impl_tac >- EVAL_TAC
  \\ strip_tac
  \\ rpt $ goal_assum $ drule_at Any
  \\ qmatch_goalsub_abbrev_tac`FUNPOW Next clk`
  \\ qexists_tac`clk` \\ simp[]
  \\ EVAL_TAC
QED

val _ = export_theory();
