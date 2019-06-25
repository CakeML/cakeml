(*
  End-to-end correctness theorem for the OpenTheory article
  checker. The theorem reaches the next-state function of the
  verified hardware platform called Silver.
*)
open preamble
     semanticsPropsTheory backendProofTheory ag32_configProofTheory
     ag32_memoryTheory ag32_memoryProofTheory ag32_ffi_codeProofTheory
     ag32_machine_configTheory ag32_basis_ffiProofTheory
     readerProgTheory readerCompileTheory
     holSoundnessTheory

val _ = new_theory "readerProgProof";

val reader_io_events_def =
  new_specification ("reader_io_events_def", ["reader_io_events"],
  reader_semantics |> Q.GENL [`cl`,`fs`]
  |> SIMP_RULE std_ss [GSYM RIGHT_EXISTS_IMP_THM]
  |> SIMP_RULE std_ss [SKOLEM_THM]);

val (reader_sem,reader_output) = reader_io_events_def |> SPEC_ALL |> UNDISCH |> CONJ_PAIR
val (reader_not_fail,reader_sem_sing) = MATCH_MP semantics_prog_Terminate_not_Fail reader_sem |> CONJ_PAIR

val ffi_names =
  ``config.ffi_names``
  |> (REWRITE_CONV[readerCompileTheory.config_def] THENC EVAL)

val LENGTH_code =
  ``LENGTH code``
  |> (REWRITE_CONV[readerCompileTheory.code_def] THENC listLib.LENGTH_CONV)

val LENGTH_data =
  ``LENGTH data``
  |> (REWRITE_CONV[readerCompileTheory.data_def] THENC listLib.LENGTH_CONV)

val _ = overload_on("reader_machine_config",
    ``ag32_machine_config (THE config.ffi_names) (LENGTH code) (LENGTH data)``);

Theorem target_state_rel_reader_start_asm_state:
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

val reader_startup_clock_def =
  new_specification("reader_startup_clock_def",["reader_startup_clock"],
  GEN_ALL (Q.SPEC`ms0`(Q.GEN`ms`target_state_rel_reader_start_asm_state))
  |> SIMP_RULE bool_ss [GSYM RIGHT_EXISTS_IMP_THM,SKOLEM_THM]);

val compile_correct_applied =
  MATCH_MP compile_correct reader_compiled
  |> SIMP_RULE(srw_ss())[LET_THM,ml_progTheory.init_state_env_thm,GSYM AND_IMP_INTRO]
  |> C MATCH_MP reader_not_fail
  |> C MATCH_MP ag32_backend_config_ok
  |> REWRITE_RULE[reader_sem_sing,AND_IMP_INTRO]
  |> REWRITE_RULE[Once (GSYM AND_IMP_INTRO)]
  |> C MATCH_MP (CONJ(UNDISCH ag32_machine_config_ok)(UNDISCH ag32_init_ok))
  |> DISCH(#1(dest_imp(concl ag32_init_ok)))
  |> C MATCH_MP is_ag32_machine_config_ag32_machine_config
  |> Q.GEN`cbspace` |> Q.SPEC`0`
  |> Q.GEN`data_sp` |> Q.SPEC`0`

Theorem reader_installed:
   SUM (MAP strlen cl) + LENGTH cl ≤ cline_size ∧
   LENGTH inp ≤ stdin_size ∧
   is_ag32_init_state (init_memory code data (THE config.ffi_names) (cl,inp)) ms0 ⇒
   installed code 0 data 0 config.ffi_names (basis_ffi cl fs)
     (heap_regs ag32_backend_config.stack_conf.reg_names)
     (reader_machine_config) (FUNPOW Next (reader_startup_clock ms0 inp cl) ms0)
Proof
  rewrite_tac[ffi_names, THE_DEF]
  \\ strip_tac
  \\ irule ag32_installed
  \\ drule reader_startup_clock_def
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

val reader_machine_sem =
  compile_correct_applied
  |> C MATCH_MP (UNDISCH reader_installed)
  |> DISCH_ALL
  |> curry save_thm "reader_machine_sem";

val _ = Parse.hide "mem";
val mem = ``mem:'U->'U-> bool``;
val _ = temp_overload_on ("reader", ``\inp r. readLines inp init_state r``);

val all_lines_stdin_fs = Q.prove (
  `all_lines (stdin_fs inp) (UStream (strlit"stdin"))
   =
   lines_of (implode inp)`,
  EVAL_TAC);

Theorem reader_extract_writes:
   wfcl cl /\
   (LENGTH cl = 1)
   ==>
   let events = MAP get_output_io_event (reader_io_events cl (stdin_fs inp)) in
   let out = extract_writes 1 events in
   let err = extract_writes 2 events in
   let refs = SND (init_reader () init_refs) in
     case reader (lines_of (implode inp)) refs of
       (Failure (Fail e), refs) => (out = "") /\ (err = explode e)
     | (Success (s, _), refs) =>
         (is_set_theory ^mem ==>
           (!asl c.
              MEM (Sequent asl c) s.thms
              ==>
              (thyof refs.the_context, asl) |= c)) /\
         refs.the_context extends init_ctxt /\
         (out = explode (msg_success s refs.the_context)) /\ (err = "")
     | _ => F
Proof
  strip_tac \\ fs []
  \\ mp_tac (GEN_ALL (DISCH_ALL reader_output))
  \\ disch_then (qspecl_then [`stdin_fs inp`, `cl`] mp_tac)
  \\ fs [wfFS_stdin_fs, STD_streams_stdin_fs, LENGTH_EQ_NUM_compute]
  \\ impl_tac
  >- (qexists_tac `inp` \\ EVAL_TAC)
  \\ strip_tac
  \\ Cases_on `init_reader () init_refs`
  \\ imp_res_tac readerProofTheory.init_reader_success \\ rw []
  \\ fs [GSYM all_lines_stdin_fs]
  \\ PURE_TOP_CASE_TAC \\ fs []
  \\ reverse PURE_TOP_CASE_TAC \\ fs []
  >-
   (PURE_CASE_TAC \\ fs [] \\ rw []
    \\ irule extract_fs_extract_writes
    \\ goal_assum (first_assum o mp_then Any mp_tac)
    \\ simp [RIGHT_EXISTS_AND_THM]
    \\ simp [readerProofTheory.reader_main_def,
             readerProofTheory.read_stdin_def]
    \\ (conj_tac >- simp [fsFFIPropsTheory.inFS_fname_def, stdin_fs_def])
    \\ simp [fsFFIPropsTheory.inFS_fname_def]
    \\ simp [TextIOProofTheory.add_stdo_def]
    \\ SELECT_ELIM_TAC
    \\ simp [TextIOProofTheory.stdo_def]
    \\ simp [stdin_fs_def]
    \\ simp [fsFFIPropsTheory.fastForwardFD_def]
    \\ simp [libTheory.the_def]
    \\ simp [AFUPDKEY_ALOOKUP]
    \\ (conj_tac >- (qexists_tac `implode ""` \\ fs []))
    \\ Cases
    \\ strip_tac \\ fs [] \\ rveq
    \\ simp [TextIOProofTheory.up_stdo_def, fsFFITheory.fsupdate_def]
    \\ simp [AFUPDKEY_ALOOKUP]
    \\ simp [fsFFIPropsTheory.inFS_fname_def]
    \\ rw [OPTREL_def]
    \\ CCONTR_TAC \\ fs [] \\ rw [])
  \\ PURE_CASE_TAC \\ fs []
  \\ once_rewrite_tac [CONJ_ASSOC]
  \\ conj_tac
  >-
   (rw []
    \\ imp_res_tac readerProofTheory.init_reader_ok
    \\ `READER_STATE defs init_state`
      by fs [readerProofTheory.READER_STATE_init_state]
    \\ drule readerProofTheory.readLines_thm
    \\ rpt (disch_then drule) \\ rw []
    \\ fs [holKernelProofTheory.CONTEXT_def, holKernelProofTheory.STATE_def]
    \\ fs [EQ_SYM_EQ] \\ rw []
    \\ fs [readerProofTheory.READER_STATE_def, EVERY_MEM]
    \\ irule proves_sound \\ fs []
    \\ first_x_assum (assume_tac o REWRITE_RULE [holKernelProofTheory.THM_def] o
                      Q.GENL [`a`,`b`] o Q.SPEC `Sequent a b`)
    \\ fs [])
  \\ rw []
  \\ irule extract_fs_extract_writes
  \\ goal_assum (first_assum o mp_then Any mp_tac)
  \\ simp [RIGHT_EXISTS_AND_THM]
  \\ simp [readerProofTheory.reader_main_def,
           readerProofTheory.read_stdin_def]
  \\ (conj_tac >- simp [fsFFIPropsTheory.inFS_fname_def, stdin_fs_def])
  \\ (conj_tac >- simp [fsFFIPropsTheory.inFS_fname_def, stdin_fs_def])
  \\ simp [fsFFIPropsTheory.inFS_fname_def]
  \\ simp [TextIOProofTheory.add_stdo_def]
  \\ SELECT_ELIM_TAC
  \\ simp [TextIOProofTheory.stdo_def]
  \\ simp [stdin_fs_def]
  \\ simp [fsFFIPropsTheory.fastForwardFD_def]
  \\ simp [libTheory.the_def]
  \\ simp [AFUPDKEY_ALOOKUP]
  \\ (conj_tac >- (qexists_tac `implode ""` \\ fs []))
  \\ Cases
  \\ strip_tac \\ fs [] \\ rveq
  \\ simp [TextIOProofTheory.up_stdo_def, fsFFITheory.fsupdate_def]
  \\ simp [AFUPDKEY_ALOOKUP]
  \\ simp [fsFFIPropsTheory.inFS_fname_def]
  \\ rw [OPTREL_def]
  \\ CCONTR_TAC \\ fs [] \\ rw []
QED

Theorem reader_ag32_next:
   SUM (MAP strlen cl) + LENGTH cl <= cline_size /\
   LENGTH inp <= stdin_size /\
   wfcl cl /\
   (LENGTH cl = 1) /\
   is_ag32_init_state (init_memory code data (THE config.ffi_names) (cl,inp)) ms0
   ==>
   ?k1. !k. k1 <= k ==>
     let ms = FUNPOW Next k ms0 in
     let outs = MAP (get_ag32_io_event) ms.io_events in
       (ms.PC = (reader_machine_config).halt_pc) /\
       (get_mem_word ms.MEM ms.PC = Encode (Jump (fAdd,0w,Imm 0w))) /\
       outs ≼ MAP get_output_io_event (reader_io_events cl (stdin_fs inp)) /\
       ((ms.R (n2w (reader_machine_config).ptr_reg) = 0w) ==>
        (outs = MAP get_output_io_event (reader_io_events cl (stdin_fs inp))))
Proof
  strip_tac
  \\ mp_tac (GEN_ALL reader_machine_sem)
  \\ disch_then (mp_tac o CONV_RULE (RESORT_FORALL_CONV rev))
  \\ disch_then (qspec_then `cl` mp_tac)
  \\ disch_then (qspecl_then [`stdin_fs inp`, `inp`, `ms0`] mp_tac)
  \\ impl_tac
  >-
   (
    fs [STD_streams_stdin_fs, wfFS_stdin_fs, LENGTH_EQ_NUM_compute]
    \\ qexists_tac `inp`
    \\ simp [stdin_fs_def, TextIOProofTheory.stdin_def])
  \\ strip_tac
  \\ irule ag32_next
  \\ conj_tac >- simp [ffi_names]
  \\ conj_tac >- (simp [ffi_names, LENGTH_code, LENGTH_data] \\ EVAL_TAC)
  \\ conj_tac >- (simp [ffi_names] \\ EVAL_TAC)
  \\ goal_assum (first_assum o mp_then Any mp_tac)
  \\ goal_assum (first_assum o mp_then Any mp_tac)
  \\ goal_assum (first_assum o mp_then Any mp_tac)
  \\ goal_assum (first_assum o mp_then Any mp_tac)
  \\ drule reader_startup_clock_def
  \\ rpt (disch_then drule)
  \\ strip_tac
  \\ goal_assum (first_assum o mp_then Any mp_tac)
  \\ goal_assum (first_assum o mp_then Any mp_tac)
  \\ metis_tac []
QED

val _ = export_theory();
