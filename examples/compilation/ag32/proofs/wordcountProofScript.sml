open preamble
     semanticsPropsTheory backendProofTheory ag32_configProofTheory
     ag32_memoryTheory ag32_memoryProofTheory ag32_ffi_codeProofTheory
     ag32_machine_configTheory ag32_basis_ffiProofTheory
     wordcountProgTheory wordcountCompileTheory;

val _ = new_theory"wordcountProof";

val is_ag32_init_state_def = ag32_targetTheory.is_ag32_init_state_def;

(* TODO: move *)
val int_toString_num = Q.store_thm("int_toString_num",
  `mlint$toString (&n) = mlnum$toString n`,
  rw[mlintTheory.toString_thm, mlnumTheory.toString_thm]);
(* -- *)

val wordcount_stdin_semantics = Q.prove(
  `∃io_events.
     semantics_prog (init_state (basis_ffi [strlit"wordcount"] (stdin_fs input))) init_env
       wordcount_prog (Terminate Success io_events) ∧
     (extract_fs (stdin_fs input) io_events =
      SOME (add_stdout (fastForwardFD (stdin_fs input) 0)
             (concat
               [mlint$toString (&LENGTH (TOKENS isSpace input)); strlit " ";
                mlint$toString (&LENGTH (splitlines input)); strlit "\n"])))`,
  match_mp_tac (GEN_ALL wordcount_semantics)
  \\ simp[wordcount_precond_def, CommandLineProofTheory.wfcl_def, clFFITheory.validArg_def]
  \\ simp[wfFS_stdin_fs, STD_streams_stdin_fs]
  \\ simp[stdin_fs_def])
  |> SIMP_RULE std_ss[int_toString_num]
  |> curry save_thm "wordcount_stdin_semantics";

val wordcount_io_events_def =
  new_specification("wordcount_io_events_def",["wordcount_io_events"],
  wordcount_stdin_semantics
  |> Q.GENL[`input`]
  |> SIMP_RULE std_ss [GSYM RIGHT_EXISTS_IMP_THM]
  |> SIMP_RULE std_ss [SKOLEM_THM]);

val (wordcount_sem,wordcount_output) = wordcount_io_events_def |> SPEC_ALL |> CONJ_PAIR
val (wordcount_not_fail,wordcount_sem_sing) = MATCH_MP semantics_prog_Terminate_not_Fail wordcount_sem |> CONJ_PAIR

val ffi_names =
  ``config.ffi_names``
  |> (REWRITE_CONV[wordcountCompileTheory.config_def] THENC EVAL)

val LENGTH_code =
  ``LENGTH code``
  |> (REWRITE_CONV[wordcountCompileTheory.code_def] THENC listLib.LENGTH_CONV)

val LENGTH_data =
  ``LENGTH data``
  |> (REWRITE_CONV[wordcountCompileTheory.data_def] THENC listLib.LENGTH_CONV)

val wordcount_startup_asm_code_def = Define`
  wordcount_startup_asm_code = (
      startup_asm_code
        (LENGTH (THE config.ffi_names))
        (n2w (LENGTH code))
        (n2w (4 * LENGTH data)))`;

val wordcount_startup_code_def = Define`
  wordcount_startup_code =
    FLAT (MAP ag32_enc wordcount_startup_asm_code)`;

val wordcount_init_memory_words_def = zDefine `
  wordcount_init_memory_words =
    init_memory_words code data (THE config.ffi_names)`;

val wordcount_init_memory_def = Define`
  wordcount_init_memory = init_memory code data (THE config.ffi_names)`;

val wordcount_machine_config_def = Define`
  wordcount_machine_config =
    ag32_machine_config (THE config.ffi_names) (LENGTH code) (LENGTH data)`;

val wordcount_startup_asm_code_eq =
  wordcount_startup_asm_code_def
  |> CONV_RULE(RAND_CONV EVAL)
  |> SIMP_RULE(srw_ss())[LENGTH_code,LENGTH_data,ffi_names]

val wordcount_startup_code_eq =
  wordcount_startup_code_def
  |> REWRITE_RULE[wordcount_startup_asm_code_eq]
  |> CONV_RULE(RAND_CONV (RAND_CONV ag32_targetLib.ag32_encode_conv))
  |> CONV_RULE(RAND_CONV listLib.FLAT_CONV)

val words_of_bytes_wordcount_startup_code_eq =
  ``words_of_bytes F wordcount_startup_code :word32 list``
  |> REWRITE_CONV[wordcount_startup_code_eq]
  |> CONV_RULE(RAND_CONV EVAL)

val LENGTH_words_of_bytes_wordcount_startup_code =
  ``LENGTH (words_of_bytes F wordcount_startup_code : word32 list)``
  |> REWRITE_CONV[words_of_bytes_wordcount_startup_code_eq]
  |> CONV_RULE(RAND_CONV listLib.LENGTH_CONV)

val LENGTH_wordcount_startup_code =
  ``LENGTH wordcount_startup_code``
  |> (RAND_CONV(REWR_CONV wordcount_startup_code_eq)
  THENC listLib.LENGTH_CONV)

val wordcount_init_memory_words_eq = save_thm (
  "wordcount_init_memory_words_eq",
  ``wordcount_init_memory_words``
  |> REWRITE_CONV [wordcount_init_memory_words_def]
  |> SIMP_RULE std_ss [init_memory_words_def, FUN_EQ_THM]
  |> Q.SPECL [`cl`,`sti`]
  |> SIMP_RULE std_ss [LET_THM]
  |> REWRITE_RULE [SPEC_ALL startup_code_def]
  |> REWRITE_RULE [GSYM wordcount_startup_asm_code_def]
  |> REWRITE_RULE [GSYM wordcount_startup_code_def]);

val wordcount_init_memory_eq = Q.store_thm("wordcount_init_memory_eq",
  `wordcount_init_memory (cl, sti) (k:word32) =
   get_byte k
     (EL (w2n (byte_align k) DIV 4) (wordcount_init_memory_words cl sti)) F`,
  fs [wordcount_init_memory_def,
      wordcount_init_memory_words_def,init_memory_def]);

val wordcount_machine_config_halt_pc =
  ``(wordcount_machine_config).halt_pc``
  |> EVAL |> SIMP_RULE(srw_ss())[ffi_names]

val wordcount_start_asm_state_def = Define`
  wordcount_start_asm_state =
    init_asm_state code data (THE config.ffi_names)`;

val _ = temp_overload_on("wordcount_asm_state0",
  ``(ag32_init_asm_state
      (wordcount_init_memory (cl,inp))
      (ag32_startup_addresses))``);

val wordcount_start_asm_state_RTC_asm_step = Q.store_thm("wordcount_start_asm_state_RTC_asm_step",
  `SUM (MAP strlen cl) + LENGTH cl ≤ cline_size ∧
   LENGTH inp ≤ stdin_size
  ⇒
   (λx y. ∃i. asm_step ag32_config x i y)^* wordcount_asm_state0 (wordcount_start_asm_state (cl,inp)) ∧
   let ffi_names = THE config.ffi_names in
   let num_ffis = LENGTH ffi_names in
   let hs = n2w heap_start_offset in
   let ds = n2w (code_start_offset num_ffis + LENGTH code) in
   ((wordcount_start_asm_state (cl,inp)).pc = n2w (code_start_offset num_ffis)) ∧
   (read_bytearray (wordcount_start_asm_state (cl,inp)).pc (LENGTH code)
      (λa. if a ∈ wordcount_machine_config.prog_addresses then SOME ((wordcount_start_asm_state (cl,inp)).mem a) else NONE)
      = SOME code) ∧
    ((wordcount_start_asm_state (cl,inp)).regs 2 = hs) ∧
    ((wordcount_start_asm_state (cl,inp)).regs 4 = hs + n2w heap_size) ∧
    (word_of_bytes F 0w (GENLIST ((wordcount_start_asm_state (cl,inp)).mem o ((+)(hs + 0w * 4w)) o n2w) 4)
     = ds) ∧
    (word_of_bytes F 0w (GENLIST ((wordcount_start_asm_state (cl,inp)).mem o ((+)(hs + 1w * 4w)) o n2w) 4)
     = ds + n2w (4 * LENGTH data)) ∧
    (word_of_bytes F 0w (GENLIST ((wordcount_start_asm_state (cl,inp)).mem o ((+)(hs + 2w * 4w)) o n2w) 4)
     = ds + n2w (4 * LENGTH data)) ∧
    (word_of_bytes F 0w (GENLIST ((wordcount_start_asm_state (cl,inp)).mem o ((+)(hs + 3w * 4w)) o n2w) 4)
     = ds) ∧
    (word_of_bytes F 0w (GENLIST ((wordcount_start_asm_state (cl,inp)).mem o ((+)(hs + 4w * 4w)) o n2w) 4)
     = ds) ∧
    (∀k. k < 4 * LENGTH data + 4 ⇒
      ((wordcount_start_asm_state (cl,inp)).mem (ds + n2w k) =
       wordcount_init_memory (cl,inp) (ds + n2w k)))`,
  strip_tac>>
  drule (GEN_ALL init_asm_state_RTC_asm_step)>>
  disch_then drule>>
  disch_then(qspecl_then [`wordcount_machine_config`,`wordcount_init_memory`,`wordcount_start_asm_state (cl,inp)`,`wordcount_asm_state0`,`code`,`data`,`THE config.ffi_names`] mp_tac)>>
  impl_tac >-(
    EVAL_TAC>>
    fs[ffi_names,LENGTH_data,LENGTH_code])>>
  simp[]);

val target_state_rel_wordcount_start_asm_state = Q.store_thm("target_state_rel_wordcount_start_asm_state",
  `SUM (MAP strlen cl) + LENGTH cl ≤ cline_size ∧
   LENGTH inp ≤ stdin_size ∧
   is_ag32_init_state (wordcount_init_memory (cl,inp)) ms ⇒
   ∃n. target_state_rel ag32_target (wordcount_start_asm_state (cl,inp)) (FUNPOW Next n ms) ∧
       ((FUNPOW Next n ms).io_events = ms.io_events) ∧
       (∀x. x ∉ (ag32_startup_addresses) ⇒
         ((FUNPOW Next n ms).MEM x = ms.MEM x))`,
  strip_tac
  \\ imp_res_tac wordcount_start_asm_state_RTC_asm_step
  \\ drule (GEN_ALL target_state_rel_ag32_init)
  \\ rveq
  \\ qmatch_goalsub_abbrev_tac`_ ∉ md`
  \\ disch_then(qspec_then`md`assume_tac)
  \\ drule (GEN_ALL RTC_asm_step_ag32_target_state_rel_io_events)
  \\ simp[EVAL``(ag32_init_asm_state m md).mem_domain``]);

val wordcount_startup_clock_def =
  new_specification("wordcount_startup_clock_def",["wordcount_startup_clock"],
  GEN_ALL (Q.SPEC`ms0`(Q.GEN`ms`target_state_rel_wordcount_start_asm_state))
  |> SIMP_RULE bool_ss [GSYM RIGHT_EXISTS_IMP_THM,SKOLEM_THM]);

val wordcount_good_init_state = Q.store_thm("wordcount_good_init_state",
  `SUM (MAP strlen cl) + LENGTH cl ≤ cline_size ∧
   LENGTH inp ≤ stdin_size ∧
   is_ag32_init_state (wordcount_init_memory (cl,inp)) ms0 ⇒
   ∃io_regs cc_regs.
   good_init_state wordcount_machine_config (FUNPOW Next (wordcount_startup_clock ms0 inp cl) ms0)
     (basis_ffi cl fs) wordcountCompile$code 0
     ((wordcount_start_asm_state (cl,inp)) with mem_domain := wordcount_machine_config.prog_addresses)
     (λk. Word
       (word_of_bytes F 0w (GENLIST (λi. (wordcount_start_asm_state (cl,inp)).mem (k + n2w i)) 4)))
       ({w | (wordcount_start_asm_state (cl,inp)).regs 2 <=+ w ∧
             w <+ (wordcount_start_asm_state (cl,inp)).regs 4}
        ∪ {w | n2w (code_start_offset (LENGTH (THE config.ffi_names)) + LENGTH wordcountCompile$code) <=+ w ∧
               w <+ n2w(code_start_offset (LENGTH (THE config.ffi_names)) + LENGTH wordcountCompile$code + 4 * LENGTH wordcountCompile$data) })
     io_regs
     cc_regs`,
  strip_tac
  \\ rewrite_tac[wordcount_machine_config_def, wordcount_start_asm_state_def]
  \\ match_mp_tac ag32_good_init_state
  \\ simp[]
  \\ conj_tac >- (simp[ffi_names] \\ EVAL_TAC)
  \\ conj_tac >- (simp[ffi_names])
  \\ conj_tac >- (simp[ffi_names, LENGTH_data, LENGTH_code] \\ EVAL_TAC)
  \\ conj_tac >- (simp[ LENGTH_code] \\ EVAL_TAC)
  \\ conj_tac >- (fs[wordcount_init_memory_def])
  \\ drule wordcount_startup_clock_def
  \\ disch_then drule
  \\ disch_then drule \\ rw[]
  \\ fs[wordcount_start_asm_state_def]);

val is_ag32_machine_config_wordcount_machine_config = Q.store_thm("is_ag32_machine_config_wordcount_machine_config",
  `is_ag32_machine_config wordcount_machine_config`,
  rw[wordcount_machine_config_def, is_ag32_machine_config_ag32_machine_config]);

val compile_correct_applied =
  MATCH_MP compile_correct wordcount_compiled
  |> SIMP_RULE(srw_ss())[LET_THM,ml_progTheory.init_state_env_thm,GSYM AND_IMP_INTRO]
  |> C MATCH_MP wordcount_not_fail
  |> C MATCH_MP ag32_backend_config_ok
  |> REWRITE_RULE[wordcount_sem_sing,AND_IMP_INTRO]
  |> REWRITE_RULE[Once (GSYM AND_IMP_INTRO)]
  |> C MATCH_MP (CONJ(UNDISCH ag32_machine_config_ok)(UNDISCH ag32_init_ok))
  |> DISCH(#1(dest_imp(concl ag32_init_ok)))
  |> C MATCH_MP is_ag32_machine_config_wordcount_machine_config
  |> Q.GEN`cbspace` |> Q.SPEC`0`
  |> Q.GEN`data_sp` |> Q.SPEC`0`

val wordcount_installed = Q.store_thm("wordcount_installed",
  `SUM (MAP strlen cl) + LENGTH cl ≤ cline_size ∧
   LENGTH inp ≤ stdin_size ∧
   is_ag32_init_state (wordcount_init_memory (cl,inp)) ms0 ⇒
   installed code 0 data 0 config.ffi_names (basis_ffi cl fs)
     (heap_regs ag32_backend_config.stack_conf.reg_names)
     (wordcount_machine_config) (FUNPOW Next (wordcount_startup_clock ms0 inp cl) ms0)`,
  rewrite_tac[wordcount_machine_config_def, wordcount_init_memory_def, ffi_names, THE_DEF]
  \\ strip_tac
  \\ irule ag32_installed
  \\ drule wordcount_startup_clock_def
  \\ disch_then drule
  \\ rewrite_tac[wordcount_init_memory_def, ffi_names, THE_DEF]
  \\ disch_then drule
  \\ strip_tac
  \\ simp[]
  \\ conj_tac >- (simp[LENGTH_code] \\ EVAL_TAC)
  \\ conj_tac >- (simp[LENGTH_code, LENGTH_data] \\ EVAL_TAC)
  \\ conj_tac >- (EVAL_TAC)
  \\ asm_exists_tac
  \\ simp[]
  \\ fs[wordcount_start_asm_state_def, ffi_names]);

val wordcount_machine_sem =
  compile_correct_applied
  |> C MATCH_MP (
       wordcount_installed
       |> Q.GENL[`cl`,`fs`]
       |> Q.SPECL[`[strlit"wordcount"]`,`stdin_fs inp`]
       |> SIMP_RULE(srw_ss())[cline_size_def]
       |> UNDISCH)
  |> DISCH_ALL
  |> curry save_thm "wordcount_machine_sem";

val wordcount_halted = Q.store_thm("wordcount_halted",
  `∀ms.
    SUM (MAP strlen cl) + LENGTH cl ≤ cline_size ∧
    LENGTH inp ≤ stdin_size ∧
    (mc = wordcount_machine_config) ∧
    (ms.PC = mc.halt_pc) ∧
    (∀x. mc.halt_pc <=+ x ∧ x <+ mc.halt_pc + 16w ⇒
         (mc.target.get_byte ms x = (wordcount_init_memory (cl,inp)) x)) ⇒
    ∀k. ((FUNPOW Next k ms).io_events = ms.io_events) ∧
        ((FUNPOW Next k ms).PC = ms.PC) ∧
        ((FUNPOW Next k ms).MEM = ms.MEM) ∧
        (∀w. w ≠ 0w ⇒ ((FUNPOW Next k ms).R w = ms.R w))`,
  rewrite_tac[wordcount_init_memory_def]
  \\ gen_tac \\ strip_tac
  \\ irule ag32_halted
  \\ asm_exists_tac
  \\ fs[ffi_names, FFI_codes_def, wordcount_machine_config_def]);

val wordcount_interference_implemented = Q.store_thm("wordcount_interference_implemented",
  `SUM (MAP strlen cl) + LENGTH cl ≤ cline_size ∧
   LENGTH inp ≤ stdin_size ∧
   is_ag32_init_state (wordcount_init_memory (cl,inp)) ms0 ∧
   Abbrev(ms = FUNPOW Next (wordcount_startup_clock ms0 inp cl) ms0)
  ⇒
   interference_implemented
    (wordcount_machine_config)
    (ag32_ffi_rel)
    (ag32_ffi_mem_domain) ms`,
  rewrite_tac[wordcount_machine_config_def, wordcount_init_memory_def]
  \\ strip_tac
  \\ irule ag32_interference_implemented
  \\ conj_tac >- simp[ffi_names]
  \\ conj_tac >- (simp[ffi_names, LENGTH_code, LENGTH_data] \\ EVAL_TAC)
  \\ conj_tac >- (simp[ffi_names] \\ EVAL_TAC)
  \\ goal_assum(first_assum o mp_then Any mp_tac)
  \\ goal_assum(first_assum o mp_then Any mp_tac)
  \\ goal_assum(first_assum o mp_then Any mp_tac)
  \\ goal_assum(first_assum o mp_then Any mp_tac)
  \\ drule wordcount_startup_clock_def
  \\ disch_then drule
  \\ rewrite_tac[wordcount_init_memory_def]
  \\ disch_then drule
  \\ simp[]);

val wordcount_extract_writes_stdout = Q.store_thm("wordcount_extract_writes_stdout",
  `(extract_writes 1 (MAP get_output_io_event (wordcount_io_events input)) =
    explode (
      concat [toString (LENGTH (TOKENS isSpace input)); strlit" ";
              toString (LENGTH (splitlines input)); strlit "\n"]))`,
  qspec_then`input`mp_tac(GEN_ALL(DISCH_ALL wordcount_output))
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
  \\ simp[Once stdin_fs_def, ALIST_FUPDKEY_def]
  \\ Cases \\ simp[] \\ strip_tac \\ rveq
  \\ pop_assum mp_tac
  \\ simp[TextIOProofTheory.up_stdo_def]
  \\ simp[fsFFITheory.fsupdate_def, fsFFIPropsTheory.fastForwardFD_def]
  \\ simp[stdin_fs_def, ALIST_FUPDKEY_ALOOKUP, libTheory.the_def]
  \\ rw[]
  \\ drule (GEN_ALL extract_fs_extract_writes)
  \\ simp[ALIST_FUPDKEY_ALOOKUP]
  \\ disch_then match_mp_tac
  \\ rw[fsFFIPropsTheory.inFS_fname_def]
  >- (fs[CaseEq"option",CaseEq"bool"] \\ rveq \\ fs[])
  >- (
    pop_assum mp_tac
    \\ rw[] \\ fs[] \\ rw[]
    \\ pop_assum mp_tac \\ rw[])
  >- rw[OPTREL_def]);

val wordcount_ag32_next = Q.store_thm("wordcount_ag32_next",
  `LENGTH inp ≤ stdin_size ∧
   is_ag32_init_state (wordcount_init_memory ([strlit"wordcount"],inp)) ms0
  ⇒
   ∃k1. ∀k. k1 ≤ k ⇒
     let ms = FUNPOW Next k ms0 in
     let outs = MAP (get_ag32_io_event) ms.io_events in
       (ms.PC = (wordcount_machine_config).halt_pc) ∧
       outs ≼ MAP get_output_io_event (wordcount_io_events inp) ∧
       ((ms.R (n2w (wordcount_machine_config).ptr_reg) = 0w) ⇒
        (outs = MAP get_output_io_event (wordcount_io_events inp)))`,
  rw[]
  \\ mp_tac (GEN_ALL wordcount_machine_sem)
  \\ disch_then(first_assum o mp_then Any mp_tac) \\ fs[]
  \\ strip_tac
  \\ fs[extend_with_resource_limit_def]
  \\ qmatch_asmsub_abbrev_tac`machine_sem mc st ms`
  \\ `∃b. machine_sem mc st ms b` by metis_tac[targetPropsTheory.machine_sem_total]
  \\ fs[SUBSET_DEF, IN_DEF]
  \\ first_x_assum drule
  \\ disch_then(assume_tac o ONCE_REWRITE_RULE[GSYM markerTheory.Abbrev_def])
  \\ `∃x y. b = Terminate x y` by fs[markerTheory.Abbrev_def] \\ rveq
  \\ first_x_assum(mp_then Any mp_tac (GEN_ALL machine_sem_Terminate_FUNPOW_next))
  \\ qspec_then`[strlit"wordcount"]`mp_tac(Q.GEN`cl` wordcount_interference_implemented)
  \\ impl_tac >- ( fs[] \\ fs[markerTheory.Abbrev_def, cline_size_def] )
  \\ strip_tac \\ rfs[]
  \\ disch_then drule
  \\ impl_tac >- (
    simp[ag32_ffi_rel_def,Abbr`st`]
    \\ conj_tac
    >- (
      EVAL_TAC
      \\ simp[Abbr`ms`]
      \\ qspec_then`[strlit"wordcount"]`mp_tac(CONV_RULE(RESORT_FORALL_CONV List.rev)wordcount_startup_clock_def)
      \\ simp[cline_size_def]
      \\ rpt(disch_then drule)
      \\ fs[is_ag32_init_state_def])
    \\ simp[basis_ffiTheory.basis_ffi_def]
    \\ simp[ag32_fs_ok_stdin_fs]
    \\ simp[Abbr`ms`]
    \\ qspec_then`[strlit"wordcount"]`mp_tac(CONV_RULE(RESORT_FORALL_CONV List.rev)wordcount_startup_clock_def)
    \\ simp[cline_size_def]
    \\ rpt(disch_then drule)
    \\ strip_tac
    (* TODO: could these be pulled out as lemmas? *)
    \\ conj_tac
    >- (
      simp[ag32_stdin_implemented_def]
      \\ simp[stdin_fs_def]
      \\ qmatch_goalsub_abbrev_tac`get_mem_word m1`
      \\ qmatch_asmsub_abbrev_tac`m1 _ = m2 _`
      \\ DEP_ONCE_REWRITE_TAC[get_mem_word_change_mem]
      \\ conj_tac
      >- (
        rw[]
        \\ first_x_assum irule
        \\ EVAL_TAC
        \\ simp[word_lo_n2w, word_ls_n2w] )
      \\ conj_tac
      >- (
        fs[is_ag32_init_state_def]
        \\ qmatch_goalsub_abbrev_tac`get_mem_word m`
        \\ qspecl_then[`stdin_offset DIV 4`,`0`]mp_tac (Q.GENL[`off`,`k`,`ls`,`ll`,`lr`]get_mem_word_get_byte)
        \\ simp[EVAL``stdin_offset``]
        \\ disch_then(qspec_then`[0w]`mp_tac) \\ simp[]
        \\ disch_then irule
        \\ simp[Abbr`m`, wordcount_init_memory_eq]
        \\ simp[wordcount_init_memory_words_eq]
        \\ rewrite_tac[GSYM APPEND_ASSOC]
        \\ qmatch_goalsub_abbrev_tac`([0w] ++ lr)`
        \\ rewrite_tac[APPEND_ASSOC]
        \\ qmatch_goalsub_abbrev_tac`ll ++ [0w] ++ lr`
        \\ map_every qexists_tac[`ll`,`lr`]
        \\ simp[]
        \\ simp[Abbr`ll`, LENGTH_words_of_bytes_wordcount_startup_code, LENGTH_wordcount_startup_code]
        \\ simp[LENGTH_words_of_bytes, bitstringTheory.length_pad_right, LENGTH_code,
                bytes_in_word_def, LENGTH_FLAT, MAP_MAP_o, o_DEF, ADD1, SUM_MAP_PLUS,
                Q.ISPEC`λx. 1n`SUM_MAP_K |> SIMP_RULE(srw_ss())[]]
        \\ qmatch_goalsub_abbrev_tac`_ + (cz DIV 4 + _)`
        \\ `cz = cline_size` by (rw[Abbr`cz`,cline_size_def])
        \\ qpat_x_assum`Abbrev(cz = _)`kall_tac
        \\ simp[] \\ EVAL_TAC )
      \\ DEP_ONCE_REWRITE_TAC[get_mem_word_change_mem]
      \\ conj_tac
      >- (
        rw[]
        \\ first_x_assum irule
        \\ EVAL_TAC
        \\ simp[word_lo_n2w, word_ls_n2w] )
      \\ conj_tac
      >- (
        fs[is_ag32_init_state_def]
        \\ qmatch_goalsub_abbrev_tac`get_mem_word m`
        \\ qspecl_then[`(stdin_offset + 4) DIV 4`,`0`]mp_tac (Q.GENL[`off`,`k`,`ls`,`ll`,`lr`]get_mem_word_get_byte)
        \\ simp[EVAL``stdin_offset``]
        \\ disch_then(qspec_then`[n2w(LENGTH inp)]`mp_tac) \\ simp[]
        \\ disch_then irule
        \\ simp[Abbr`m`, wordcount_init_memory_eq]
        \\ simp[wordcount_init_memory_words_eq]
        \\ rewrite_tac[GSYM APPEND_ASSOC]
        \\ qmatch_goalsub_abbrev_tac`([n2w(LENGTH inp)] ++ lr)`
        \\ rewrite_tac[APPEND_ASSOC]
        \\ qmatch_goalsub_abbrev_tac`ll ++ [n2w(LENGTH inp)] ++ lr`
        \\ map_every qexists_tac[`ll`,`lr`]
        \\ simp[]
        \\ simp[Abbr`ll`, LENGTH_words_of_bytes_wordcount_startup_code, LENGTH_wordcount_startup_code]
        \\ simp[LENGTH_words_of_bytes, bitstringTheory.length_pad_right, LENGTH_code,
                bytes_in_word_def, LENGTH_FLAT, MAP_MAP_o, o_DEF, ADD1, SUM_MAP_PLUS,
                Q.ISPEC`λx. 1n`SUM_MAP_K |> SIMP_RULE(srw_ss())[]]
        \\ qmatch_goalsub_abbrev_tac`_ + (cz DIV 4 + _)`
        \\ `cz = cline_size` by (rw[Abbr`cz`,cline_size_def])
        \\ qpat_x_assum`Abbrev(cz = _)`kall_tac
        \\ simp[] \\ EVAL_TAC )
      \\ irule asmPropsTheory.bytes_in_memory_change_mem
      \\ qexists_tac`m2`
      \\ conj_tac
      >- (
        rw[]
        \\ irule EQ_SYM
        \\ first_x_assum irule
        \\ EVAL_TAC
        \\ fs[EVAL``stdin_size``]
        \\ fs[word_ls_n2w, word_lo_n2w] )
      \\ fs[is_ag32_init_state_def]
      \\ simp[wordcount_init_memory_eq]
      \\ irule asmPropsTheory.read_bytearray_IMP_bytes_in_memory
      \\ qexists_tac`SOME o m2`
      \\ qexists_tac`LENGTH inp`
      \\ simp[]
      \\ irule data_to_word_assignProofTheory.IMP_read_bytearray_GENLIST
      \\ simp[]
      \\ simp[wordcount_init_memory_eq]
      \\ `byte_aligned ((n2w (stdin_offset + 8)):word32)` by EVAL_TAC
      \\ pop_assum mp_tac
      \\ simp[alignmentTheory.byte_aligned_def, alignmentTheory.byte_align_def]
      \\ strip_tac
      \\ drule (GEN_ALL align_add_aligned_gen)
      \\ simp[]
      \\ disch_then kall_tac
      \\ rw[]
      \\ DEP_REWRITE_TAC[w2n_add]
      \\ conj_tac
      >- (
        conj_tac >- EVAL_TAC
        \\ simp[word_msb_align]
        \\ simp[word_msb_n2w]
        \\ match_mp_tac bitTheory.NOT_BIT_GT_TWOEXP
        \\ fs[EVAL``stdin_size``] )
      \\ simp[alignmentTheory.align_w2n]
      \\ fs[EVAL``stdin_size``, EVAL``stdin_offset``]
      \\ DEP_REWRITE_TAC[ADD_DIV_RWT] \\ simp[]
      \\ rewrite_tac[wordcount_init_memory_words_eq]
      \\ rewrite_tac[GSYM APPEND_ASSOC] \\ DEP_ONCE_REWRITE_TAC[EL_APPEND2]
      \\ simp[LENGTH_words_of_bytes_wordcount_startup_code]
      \\ rewrite_tac[GSYM APPEND_ASSOC] \\ DEP_ONCE_REWRITE_TAC[EL_APPEND2]
      \\ simp[LENGTH_wordcount_startup_code, startup_code_size_def]
      \\ simp[EL_CONS, PRE_SUB1]
      \\ rewrite_tac[GSYM APPEND_ASSOC] \\ DEP_ONCE_REWRITE_TAC[EL_APPEND2]
      \\ simp[LENGTH_words_of_bytes, bitstringTheory.length_pad_right, LENGTH_FLAT, bytes_in_word_def, MAP_MAP_o, o_DEF, ADD1, SUM_MAP_PLUS]
      \\ simp[Q.ISPEC`λx. 1n`SUM_MAP_K |> SIMP_RULE(srw_ss())[]]
      \\ qmatch_goalsub_abbrev_tac`MIN 1 (cz MOD _)` \\ `cz = cline_size` by ( simp[Abbr`cz`,cline_size_def] )
      \\ qpat_x_assum`Abbrev(cz = _)`kall_tac \\ pop_assum SUBST_ALL_TAC
      \\ simp[cline_size_def]
      \\ simp[EL_CONS, PRE_SUB1]
      \\ rewrite_tac[GSYM APPEND_ASSOC]
      \\ DEP_REWRITE_TAC[EL_APPEND1]
      \\ simp[LENGTH_words_of_bytes, bitstringTheory.length_pad_right, LENGTH_FLAT, bytes_in_word_def, MAP_MAP_o, o_DEF, ADD1, SUM_MAP_PLUS]
      \\ qmatch_goalsub_abbrev_tac`MIN 1 (cz MOD _)` \\ `cz = stdin_size` by ( simp[Abbr`cz`,EVAL``stdin_size``] )
      \\ qpat_x_assum`Abbrev(cz = _)`kall_tac \\ pop_assum SUBST_ALL_TAC
      \\ fs[EVAL``stdin_size``]
      \\ simp[DIV_LT_X]
      \\ qmatch_goalsub_abbrev_tac`a MOD _`
      \\ `a < dimword(:32)` by (
        simp[Abbr`a`]
        \\ irule IMP_MULT_DIV_LESS
        \\ simp[] )
      \\ fs[]
      \\ conj_tac
      >- (
        simp[Abbr`a`]
        \\ irule IMP_MULT_DIV_LESS
        \\ simp[] )
      \\ `2300w:word32 = byte_align 2300w` by EVAL_TAC
      \\ pop_assum SUBST1_TAC
      \\ DEP_REWRITE_TAC[data_to_word_memoryProofTheory.get_byte_byte_align]
      \\ conj_tac >- EVAL_TAC
      \\ `a = w2n (byte_align (n2w i) : word32)`
      by (
        simp[Abbr`a`]
        \\ simp[alignmentTheory.byte_align_def]
        \\ simp[alignmentTheory.align_w2n] )
      \\ qpat_x_assum`Abbrev(a = _)`kall_tac
      \\ simp[]
      \\ `4 = w2n (bytes_in_word:word32)` by EVAL_TAC
      \\ pop_assum SUBST1_TAC
      \\ DEP_REWRITE_TAC[get_byte_EL_words_of_bytes]
      \\ simp[bitstringTheory.length_pad_right]
      \\ EVAL_TAC
      \\ simp[EL_APPEND1])
    \\ simp[ag32_cline_implemented_def]
    \\ fs[CommandLineProofTheory.wfcl_def]
    \\ qmatch_goalsub_abbrev_tac`get_mem_word m1`
    \\ qmatch_asmsub_abbrev_tac`m1 _ = m2 _`
    \\ conj_tac
    >- (
      DEP_ONCE_REWRITE_TAC[get_mem_word_change_mem]
      \\ conj_tac
      >- (
        rw[]
        \\ first_x_assum irule
        \\ EVAL_TAC
        \\ simp[word_lo_n2w, word_ls_n2w] )
      \\ fs[is_ag32_init_state_def]
      \\ qmatch_goalsub_abbrev_tac`get_mem_word m`
      \\ qspecl_then[`startup_code_size DIV 4`,`0`]mp_tac (Q.GENL[`off`,`k`,`ls`,`ll`,`lr`]get_mem_word_get_byte)
      \\ simp[EVAL``startup_code_size``]
      \\ disch_then(qspec_then`[n2w(1)]`mp_tac) \\ simp[]
      \\ disch_then irule
      \\ simp[Abbr`m`, wordcount_init_memory_eq]
      \\ simp[wordcount_init_memory_words_eq]
      \\ rewrite_tac[GSYM APPEND_ASSOC]
      \\ qmatch_goalsub_abbrev_tac`([n2w (1)] ++ lr)`
      \\ rewrite_tac[APPEND_ASSOC]
      \\ qmatch_goalsub_abbrev_tac`ll ++ [n2w (1)] ++ lr`
      \\ map_every qexists_tac[`ll`,`lr`]
      \\ simp[]
      \\ simp[Abbr`ll`, LENGTH_words_of_bytes_wordcount_startup_code, LENGTH_wordcount_startup_code]
      \\ EVAL_TAC )
    \\ conj_tac >- EVAL_TAC
    \\ conj_tac >- EVAL_TAC
    \\ irule asmPropsTheory.bytes_in_memory_change_mem
    \\ qexists_tac`m2`
    \\ conj_tac
    >- (
      rw[]
      \\ irule EQ_SYM
      \\ first_x_assum irule
      \\ EVAL_TAC
      \\ fs[EVAL``startup_code_size``,EVAL``cline_size``]
      \\ fs[word_ls_n2w, word_lo_n2w] )
    \\ fs[is_ag32_init_state_def]
    \\ irule asmPropsTheory.read_bytearray_IMP_bytes_in_memory
    \\ qexists_tac`SOME o m2`
    \\ simp[]
    \\ irule data_to_word_assignProofTheory.IMP_read_bytearray_GENLIST
    \\ simp[]
    \\ simp[wordcount_init_memory_eq]
    \\ `byte_aligned ((n2w (startup_code_size + 4)):word32)` by EVAL_TAC
    \\ pop_assum mp_tac
    \\ simp[alignmentTheory.byte_aligned_def, alignmentTheory.byte_align_def]
    \\ strip_tac
    \\ drule (GEN_ALL align_add_aligned_gen)
    \\ simp[]
    \\ disch_then kall_tac
    \\ rw[]
    \\ DEP_REWRITE_TAC[w2n_add]
    \\ conj_tac
    >- (
      conj_tac >- EVAL_TAC
      \\ simp[word_msb_align]
      \\ simp[word_msb_n2w]
      \\ match_mp_tac bitTheory.NOT_BIT_GT_TWOEXP
      \\ fs[EVAL``cline_size``] )
    \\ simp[alignmentTheory.align_w2n]
    \\ fs[EVAL``cline_size``,EVAL``startup_code_size``]
    \\ DEP_REWRITE_TAC[ADD_DIV_RWT] \\ simp[]
    \\ rewrite_tac[wordcount_init_memory_words_eq]
    \\ rewrite_tac[GSYM APPEND_ASSOC] \\ DEP_ONCE_REWRITE_TAC[EL_APPEND2]
    \\ simp[LENGTH_words_of_bytes_wordcount_startup_code]
    \\ rewrite_tac[GSYM APPEND_ASSOC] \\ DEP_ONCE_REWRITE_TAC[EL_APPEND2]
    \\ simp[LENGTH_wordcount_startup_code, startup_code_size_def]
    \\ simp[EL_CONS, PRE_SUB1]
    \\ rewrite_tac[GSYM APPEND_ASSOC] \\ DEP_ONCE_REWRITE_TAC[EL_APPEND1]
    \\ simp[LENGTH_words_of_bytes, bitstringTheory.length_pad_right]
    \\ fs[EVAL``cline_size``]
    \\ simp[DIV_LT_X]
    \\ qmatch_goalsub_abbrev_tac`a MOD _`
    \\ `a < dimword(:32)` by (
      simp[Abbr`a`]
      \\ irule IMP_MULT_DIV_LESS
      \\ simp[] )
    \\ fs[]
    \\ conj_tac
    >- (
      simp[Abbr`a`, bytes_in_word_def]
      \\ fs[DIV_LT_X])
    \\ `244w:word32 = byte_align 244w` by EVAL_TAC
    \\ pop_assum SUBST1_TAC
    \\ DEP_REWRITE_TAC[data_to_word_memoryProofTheory.get_byte_byte_align]
    \\ conj_tac >- EVAL_TAC
    \\ `a = w2n (byte_align (n2w i) : word32)`
    by (
      simp[Abbr`a`]
      \\ simp[alignmentTheory.byte_align_def]
      \\ simp[alignmentTheory.align_w2n] )
    \\ qpat_x_assum`Abbrev(a = _)`kall_tac
    \\ simp[]
    \\ `4 = w2n (bytes_in_word:word32)` by EVAL_TAC
    \\ pop_assum SUBST1_TAC
    \\ DEP_REWRITE_TAC[get_byte_EL_words_of_bytes]
    \\ simp[bitstringTheory.length_pad_right]
    \\ EVAL_TAC
    \\ qpat_x_assum`i < _`mp_tac
    \\ simp[NUMERAL_LESS_THM]
    \\ strip_tac \\ rveq \\ EVAL_TAC)
  \\ strip_tac
  \\ qspec_then`[strlit"wordcount"]`mp_tac (Q.GENL[`cl`,`mc`] wordcount_halted)
  \\ simp[cline_size_def]
  \\ disch_then(qspec_then`FUNPOW Next k ms`mp_tac)
  \\ impl_tac
  >- (
    conj_tac >- (
      fs[Abbr`mc`]
      \\ fs[EVAL``(wordcount_machine_config).target.get_pc``]
      \\ fs[Abbr`ms`, FUNPOW_ADD]
      \\ fs[EVAL``(wordcount_machine_config).target.next``]
      \\ first_x_assum irule
      \\ fs[markerTheory.Abbrev_def] )
    \\ fs[Abbr`mc`]
    \\ fs[EVAL``(wordcount_machine_config).target.next``]
    \\ fs[Abbr`ms`, FUNPOW_ADD]
    \\ qspec_then`[strlit"wordcount"]`mp_tac(CONV_RULE(RESORT_FORALL_CONV List.rev)wordcount_startup_clock_def)
    \\ disch_then(first_assum o mp_then Any mp_tac)
    \\ impl_tac >- fs[cline_size_def]
    \\ strip_tac
    \\ fs[EVAL``(wordcount_machine_config).target.get_byte``]
    \\ fs[ag32_targetTheory.is_ag32_init_state_def] \\ rfs[]
    \\ rw[]
    \\ qmatch_goalsub_rename_tac`_ = _ a`
    \\ `a ∉ ag32_startup_addresses`
    by (
      EVAL_TAC
      \\ ntac 2 (pop_assum mp_tac)
      \\ EVAL_TAC
      \\ simp[ffi_names]
      \\ Cases_on`a` \\ Cases_on`ms0.PC`
      \\ simp[word_add_n2w]
      \\ simp[word_ls_n2w, word_lo_n2w])
    \\ first_x_assum drule
    \\ disch_then(assume_tac o SYM) \\ simp[]
    \\ first_x_assum irule
    \\ Cases_on`a`
    \\ fs[word_add_n2w, wordcount_machine_config_halt_pc]
    \\ simp[wordcount_machine_config_def, ag32_machine_config_def, ffi_names, ag32_prog_addresses_def, LENGTH_code, LENGTH_data]
    \\ EVAL_TAC
    \\ fs[word_lo_n2w, word_ls_n2w, memory_size_def] \\ rfs[])
  \\ strip_tac
  \\ qexists_tac`k + wordcount_startup_clock ms0 inp [strlit"wordcount"]`
  \\ qx_gen_tac`k2` \\ strip_tac
  \\ first_x_assum(qspec_then`k2-k-(wordcount_startup_clock ms0 inp [strlit"wordcount"])`mp_tac)
  \\ fs[GSYM FUNPOW_ADD, Abbr`ms`]
  \\ strip_tac
  \\ fs[EVAL``(wordcount_machine_config).target.next``,Abbr`mc`,FUNPOW_ADD]
  \\ fs[EVAL``(wordcount_machine_config).target.get_reg``]
  \\ fs[EVAL``(wordcount_machine_config).target.get_pc``]
  \\ fs[EVAL``(wordcount_machine_config).ptr_reg``]
  \\ fs[ag32_ffi_rel_def]
  \\ conj_tac
  >- ( fs[IS_PREFIX_APPEND] \\ fs[markerTheory.Abbrev_def] )
  \\ strip_tac \\ fs[]
  \\ Cases_on`x` \\ fs[]
  \\ fs[markerTheory.Abbrev_def]);

val _ = export_theory();
