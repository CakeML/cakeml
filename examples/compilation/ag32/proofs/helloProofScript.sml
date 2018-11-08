open preamble
     semanticsPropsTheory backendProofTheory ag32_configProofTheory
     ag32_memoryTheory ag32_memoryProofTheory ag32_ffi_codeProofTheory
     ag32_machine_configTheory ag32_basis_ffiProofTheory
     helloProgTheory helloCompileTheory;

val _ = new_theory"helloProof";

val is_ag32_init_state_def = ag32_targetTheory.is_ag32_init_state_def;

val hello_io_events_def =
  new_specification("hello_io_events_def",["hello_io_events"],
  hello_semantics |> Q.GENL[`cl`,`fs`]
  |> SIMP_RULE std_ss [GSYM RIGHT_EXISTS_IMP_THM]
  |> SIMP_RULE std_ss [SKOLEM_THM]);

val (hello_sem,hello_output) = hello_io_events_def |> SPEC_ALL |> UNDISCH |> CONJ_PAIR
val (hello_not_fail,hello_sem_sing) = MATCH_MP semantics_prog_Terminate_not_Fail hello_sem |> CONJ_PAIR

(*

structure helloCompileTheory = struct
  val config_def = zDefine`config : 32 lab_to_target$config = <| ffi_names := SOME ["write"] |>`;
  val code_def = zDefine`code = [72w; 57w; 242w; 15w; 131w; 11w; 0w; 0w] : word8 list`;
  val data_def = zDefine`data = [4w; 24w; 31w; 12w; 15w; 3w; 62w; 63w; 127w] : word32 list`;
end
val hello_compiled = mk_thm([],``compile (ag32_backend_config with word_to_word_conf := <|reg_alg := 2; col_oracle := ARB|>)
  hello_prog = SOME(code,data,config)``);

*)

val ffi_names =
  ``config.ffi_names``
  |> (REWRITE_CONV[helloCompileTheory.config_def] THENC EVAL)

val LENGTH_code =
  ``LENGTH code``
  |> (REWRITE_CONV[helloCompileTheory.code_def] THENC listLib.LENGTH_CONV)

val LENGTH_data =
  ``LENGTH data``
  |> (REWRITE_CONV[helloCompileTheory.data_def] THENC listLib.LENGTH_CONV)

val hello_startup_asm_code_def = Define`
  hello_startup_asm_code = (
      startup_asm_code
        (LENGTH (THE config.ffi_names))
        (n2w (LENGTH code))
        (n2w (4 * LENGTH data)))`;

val hello_startup_code_def = Define`
    hello_startup_code =
    FLAT (MAP ag32_enc hello_startup_asm_code)`;

val hello_init_memory_words_def = zDefine`
  hello_init_memory_words =
    init_memory_words code data (THE config.ffi_names)`

val hello_init_memory_def = Define`
  hello_init_memory = init_memory code data (THE config.ffi_names)`

val hello_machine_config_def = Define`
  hello_machine_config =
    ag32_machine_config (THE config.ffi_names) (LENGTH code) (LENGTH data)`;

val hello_startup_asm_code_eq =
  hello_startup_asm_code_def
  |> CONV_RULE(RAND_CONV EVAL)
  |> SIMP_RULE(srw_ss())[LENGTH_code,LENGTH_data,ffi_names]

val hello_startup_code_eq =
  hello_startup_code_def
  |> REWRITE_RULE[hello_startup_asm_code_eq]
  |> CONV_RULE(RAND_CONV (RAND_CONV ag32_targetLib.ag32_encode_conv))
  |> CONV_RULE(RAND_CONV listLib.FLAT_CONV)

val words_of_bytes_hello_startup_code_eq =
  ``words_of_bytes F hello_startup_code :word32 list``
  |> REWRITE_CONV[hello_startup_code_eq]
  |> CONV_RULE(RAND_CONV EVAL)

val LENGTH_words_of_bytes_hello_startup_code =
  ``LENGTH (words_of_bytes F hello_startup_code : word32 list)``
  |> REWRITE_CONV[words_of_bytes_hello_startup_code_eq]
  |> CONV_RULE(RAND_CONV listLib.LENGTH_CONV)

val LENGTH_hello_startup_code =
  ``LENGTH hello_startup_code``
  |> (RAND_CONV(REWR_CONV hello_startup_code_eq)
  THENC listLib.LENGTH_CONV)

val hello_init_memory_words_eq = Q.store_thm("hello_init_memory_words_eq",`
  hello_init_memory_words cl sti =
    words_of_bytes F hello_startup_code ++
    REPLICATE ((startup_code_size - LENGTH hello_startup_code) DIV 4) 0w ++
    [n2w (LENGTH cl)] ++
    words_of_bytes F (PAD_RIGHT 0w cline_size (FLAT (MAP (SNOC 0w) (MAP (MAP (n2w o ORD) o explode) cl)))) ++
    [0w] ++
    [n2w (LENGTH sti)] ++
    words_of_bytes F (PAD_RIGHT 0w stdin_size (MAP (n2w o ORD) sti)) ++
    REPLICATE ((8 + 4 + output_buffer_size + 4) DIV 4) 0w ++
    ag32_ffi_code ++
    REPLICATE (heap_size DIV 4) 0w ++
    ag32_ffi_jumps (THE config.ffi_names) ++
    words_of_bytes F code ++
    data (* ++ padding of 0w out to memory_size: not included here *)
    `,
  fs[hello_init_memory_words_def,init_memory_words_def,hello_startup_code_def,hello_startup_asm_code_def,startup_code_def]);

val hello_init_memory_eq = Q.store_thm("hello_init_memory_eq",`
  hello_init_memory (cl, sti) (k:word32) =
  get_byte k (EL (w2n (byte_align k) DIV 4) (hello_init_memory_words cl sti)) F`,
  fs[hello_init_memory_def,hello_init_memory_words_def,init_memory_def]);

val LENGTH_hello_init_memory_words = Q.store_thm("LENGTH_hello_init_memory_words",
  `SUM (MAP strlen cl) + LENGTH cl ≤ cline_size ∧ LENGTH inp ≤ stdin_size ⇒
   (LENGTH (hello_init_memory_words cl inp) = 27572274)`, (* adjust as necessary *)
  simp[hello_init_memory_words_def,LENGTH_init_memory_words]>>
  simp[LENGTH_code,LENGTH_data,ffi_names,LENGTH_ag32_ffi_jumps]);

val hello_machine_config_halt_pc =
  ``hello_machine_config.halt_pc``
  |> EVAL |> SIMP_RULE(srw_ss())[ffi_names]

val hello_machine_config_ccache_pc =
  ``hello_machine_config.ccache_pc``
  |> EVAL |> SIMP_RULE(srw_ss())[ffi_names]

val hello_init_memory_halt = Q.store_thm("hello_init_memory_halt",
  `(pc = hello_machine_config.halt_pc) ∧
   SUM (MAP strlen cl) + LENGTH cl ≤ cline_size ∧ LENGTH inp ≤ stdin_size
  ⇒
  (get_mem_word (hello_init_memory (cl,inp)) pc =
    Encode (Jump (fAdd, 0w, Imm 0w)))`,
  simp[hello_machine_config_def,hello_init_memory_def]>>
  strip_tac>>
  match_mp_tac init_memory_halt>>
  simp[ffi_names,ag32_machine_config_def,FFI_codes_def]);

val hello_init_memory_ccache = Q.store_thm("hello_init_memory_ccache",
  `(pc = hello_machine_config.ccache_pc) ∧
   SUM (MAP strlen cl) + LENGTH cl ≤ cline_size ∧ LENGTH inp ≤ stdin_size
  ⇒
   (get_mem_word (hello_init_memory (cl,inp)) pc =
    Encode (Jump (fSnd, 0w, Reg 0w)))`,
  simp[hello_machine_config_def,hello_init_memory_def]>>
  strip_tac>>
  match_mp_tac init_memory_ccache>>
  simp[ffi_names,ag32_machine_config_def,FFI_codes_def]);

val hello_start_asm_state_def = Define`
  hello_start_asm_state =
    init_asm_state code data (THE config.ffi_names)`;

val _ = temp_overload_on("hello_asm_state0",
  ``(ag32_init_asm_state
      (hello_init_memory (cl,inp))
      (ag32_startup_addresses))``);

val hello_start_asm_state_RTC_asm_step = Q.store_thm("hello_start_asm_state_RTC_asm_step",
  `SUM (MAP strlen cl) + LENGTH cl ≤ cline_size ∧
   LENGTH inp ≤ stdin_size
  ⇒
   (λx y. ∃i. asm_step ag32_config x i y)^* hello_asm_state0 (hello_start_asm_state (cl,inp)) ∧
   let ffi_names = THE config.ffi_names in
   let num_ffis = LENGTH ffi_names in
   let hs = n2w heap_start_offset in
   let ds = n2w (code_start_offset num_ffis + LENGTH code) in
   ((hello_start_asm_state (cl,inp)).pc = n2w (code_start_offset num_ffis)) ∧
   (read_bytearray (hello_start_asm_state (cl,inp)).pc (LENGTH code)
      (λa. if a ∈ hello_machine_config.prog_addresses then SOME ((hello_start_asm_state (cl,inp)).mem a) else NONE)
      = SOME code) ∧
    ((hello_start_asm_state (cl,inp)).regs 2 = hs) ∧
    ((hello_start_asm_state (cl,inp)).regs 4 = hs + n2w heap_size) ∧
    (word_of_bytes F 0w (GENLIST ((hello_start_asm_state (cl,inp)).mem o ((+)(hs + 0w * 4w)) o n2w) 4)
     = ds) ∧
    (word_of_bytes F 0w (GENLIST ((hello_start_asm_state (cl,inp)).mem o ((+)(hs + 1w * 4w)) o n2w) 4)
     = ds + n2w (4 * LENGTH data)) ∧
    (word_of_bytes F 0w (GENLIST ((hello_start_asm_state (cl,inp)).mem o ((+)(hs + 2w * 4w)) o n2w) 4)
     = ds + n2w (4 * LENGTH data)) ∧
    (word_of_bytes F 0w (GENLIST ((hello_start_asm_state (cl,inp)).mem o ((+)(hs + 3w * 4w)) o n2w) 4)
     = ds) ∧
    (word_of_bytes F 0w (GENLIST ((hello_start_asm_state (cl,inp)).mem o ((+)(hs + 4w * 4w)) o n2w) 4)
     = ds) ∧
    (∀k. k < 4 * LENGTH data + 4 ⇒
      ((hello_start_asm_state (cl,inp)).mem (ds + n2w k) =
       hello_init_memory (cl,inp) (ds + n2w k)))`,
  strip_tac>>
  drule (GEN_ALL init_asm_state_RTC_asm_step)>>
  disch_then drule>>
  disch_then(qspecl_then [`hello_machine_config`,`hello_init_memory`,`hello_start_asm_state (cl,inp)`,`hello_asm_state0`,`code`,`data`,`THE config.ffi_names`] mp_tac)>>
  impl_tac >-(
    EVAL_TAC>>
    fs[ffi_names,LENGTH_data,LENGTH_code])>>
  simp[]);

val target_state_rel_hello_start_asm_state = Q.store_thm("target_state_rel_hello_start_asm_state",
  `SUM (MAP strlen cl) + LENGTH cl ≤ cline_size ∧
   LENGTH inp ≤ stdin_size ∧
   is_ag32_init_state (hello_init_memory (cl,inp)) ms ⇒
   ∃n. target_state_rel ag32_target (hello_start_asm_state (cl,inp)) (FUNPOW Next n ms) ∧
       ((FUNPOW Next n ms).io_events = ms.io_events) ∧
       (∀x. x ∉ (ag32_startup_addresses) ⇒
         ((FUNPOW Next n ms).MEM x = ms.MEM x))`,
  strip_tac
  \\ imp_res_tac hello_start_asm_state_RTC_asm_step
  \\ drule (GEN_ALL target_state_rel_ag32_init)
  \\ rveq
  \\ qmatch_goalsub_abbrev_tac`_ ∉ md`
  \\ disch_then(qspec_then`md`assume_tac)
  \\ drule (GEN_ALL RTC_asm_step_ag32_target_state_rel_io_events)
  \\ simp[EVAL``(ag32_init_asm_state m md).mem_domain``]);

val target_state_rel_init_asm_state = Q.store_thm("target_state_rel_init_asm_state",
  `SUM (MAP strlen cl) + LENGTH cl ≤ cline_size ∧
   LENGTH inp ≤ stdin_size ∧
   LENGTH ffi_names ≤ LENGTH FFI_codes ∧
   code_start_offset (LENGTH ffi_names) + LENGTH code + 4 * LENGTH data < memory_size ∧
   is_ag32_init_state (init_memory code data ffi_names (cl,inp)) ms ⇒
   ∃n. target_state_rel ag32_target (init_asm_state code data ffi_names (cl,inp)) (FUNPOW Next n ms) ∧
       ((FUNPOW Next n ms).io_events = ms.io_events) ∧
       (∀x. x ∉ (ag32_startup_addresses) ⇒
         ((FUNPOW Next n ms).MEM x = ms.MEM x))`,
  strip_tac
  \\ drule (GEN_ALL init_asm_state_RTC_asm_step)
  \\ disch_then drule
  \\ disch_then drule
  \\ disch_then drule
  \\ strip_tac
  \\ drule (GEN_ALL target_state_rel_ag32_init)
  \\ fs[]
  \\ rveq
  \\ qmatch_goalsub_abbrev_tac`_ ∉ md`
  \\ disch_then(qspec_then`md`assume_tac)
  \\ drule (GEN_ALL RTC_asm_step_ag32_target_state_rel_io_events)
  \\ simp[EVAL``(ag32_init_asm_state m md).mem_domain``]);

val hello_startup_clock_def =
  new_specification("hello_startup_clock_def",["hello_startup_clock"],
  GEN_ALL (Q.SPEC`ms0`(Q.GEN`ms`target_state_rel_hello_start_asm_state))
  |> SIMP_RULE bool_ss [GSYM RIGHT_EXISTS_IMP_THM,SKOLEM_THM]);

(*
val ag32_good_init_state = Q.store_thm("ag32_good_init_state",
  `SUM (MAP strlen cl) + LENGTH cl ≤ cline_size ∧
   LENGTH inp ≤ stdin_size ∧
   LENGTH ffi_names ≤ LENGTH FFI_codes ∧
   code_start_offset (LENGTH ffi_names) + LENGTH code + 4 * LENGTH data < memory_size ∧
   is_ag32_init_state (init_memory code data ffi_names (cl,inp)) ms0 ∧
   target_state_rel ag32_target (init_asm_state code data ffi_names (cl,inp))
     (FUNPOW Next startup_clock ms0) ∧
   (∀x. x ∉ ag32_startup_addresses ⇒
      ((FUNPOW Next startup_clock ms0).MEM x = ms0.MEM x))
   ⇒
   ∃io_regs cc_regs.
   good_init_state (ag32_machine_config ffi_names (LENGTH code) (LENGTH data))
     (FUNPOW Next startup_clock ms0)
     (basis_ffi cl fs) code 0
     ((init_asm_state code data ffi_names (cl,inp)) with
       mem_domain := (ag32_machine_config ffi_names (LENGTH code) (LENGTH data)).prog_addresses)
     (λk. Word
       (word_of_bytes F 0w (GENLIST (λi. (init_asm_state code data ffi_names (cl,inp)).mem (k + n2w i)) 4)))
       ({w | (init_asm_state code data ffi_names (cl,inp)).regs 2 <=+ w ∧
             w <+ (init_asm_state code data ffi_names (cl,inp)).regs 4}
        ∪ {w | n2w (code_start_offset (LENGTH ffi_names) + LENGTH code) <=+ w ∧
               w <+ n2w(code_start_offset (LENGTH ffi_names) + LENGTH code + 4 * LENGTH data) })
     io_regs
     cc_regs`,
  strip_tac
  \\ simp[lab_to_targetProofTheory.good_init_state_def,RIGHT_EXISTS_AND_THM]
  \\ drule (GEN_ALL init_asm_state_RTC_asm_step)
  \\ disch_then drule
  \\ disch_then drule
  \\ disch_then drule
  \\ strip_tac \\ fs[]
  \\ conj_tac >- (
    fs[ag32_machine_config_def]
    \\ fs[asmPropsTheory.target_state_rel_def]
    \\ fs[EVAL``ag32_target.get_byte``]
    \\ qx_gen_tac`a` \\ strip_tac
    \\ drule asmPropsTheory.RTC_asm_step_consts
    \\ strip_tac \\ fs[]
    \\ `(ag32_init_asm_state (init_memory code data ffi_names (cl,inp)) ag32_startup_addresses).mem_domain = ag32_startup_addresses` by (
      fs[ag32_init_asm_state_def] )
    \\ fs[]
    \\ Cases_on`a ∈ ag32_startup_addresses` \\ fs[]
    \\ drule asmPropsTheory.RTC_asm_step_outside_mem_domain
    \\ simp[]
    \\ fs[is_ag32_init_state_def]
    \\ simp[ag32_init_asm_state_def])
  \\ conj_tac
  >- (
    Q.ISPEC_THEN `ag32_machine_config ffi_names (LENGTH code) (LENGTH data) with prog_addresses := ag32_startup_addresses`
      drule (Q.GEN`mc` RTC_asm_step_target_configured)
    \\ simp[lab_to_targetProofTheory.target_configured_def]
    \\ impl_tac >- EVAL_TAC
    \\ strip_tac \\ fs[])
  \\ conj_tac >- (
    fs[asmPropsTheory.target_state_rel_def, ag32_machine_config_def] )
  \\ qabbrev_tac`num_ffis = LENGTH ffi_names`
  \\ `n2w (code_start_offset num_ffis) && 3w = 0w:word32` by (
    EVAL_TAC
    \\ fs[alignmentTheory.aligned_bitwise_and, alignmentTheory.byte_aligned_def, Abbr`num_ffis`, FFI_codes_def]
    \\ qpat_x_assum`_ ≤ _`mp_tac
    \\ simp[LESS_OR_EQ]
    \\ CONV_TAC(LAND_CONV(SIMP_CONV(srw_ss())[NUMERAL_LESS_THM]))
    \\ rpt(pop_assum kall_tac)
    \\ strip_tac \\ simp[])
  \\ `n2w (code_start_offset num_ffis) && 1w = 0w:word32` by (
    EVAL_TAC
    \\ fs[alignmentTheory.aligned_bitwise_and, alignmentTheory.byte_aligned_def, Abbr`num_ffis`, FFI_codes_def]
    \\ qpat_x_assum`_ ≤ _`mp_tac
    \\ simp[LESS_OR_EQ]
    \\ CONV_TAC(LAND_CONV(SIMP_CONV(srw_ss())[NUMERAL_LESS_THM]))
    \\ rpt(pop_assum kall_tac)
    \\ strip_tac \\ simp[])
  \\ conj_tac >- (
    rewrite_tac[lab_to_targetProofTheory.start_pc_ok_def]
    \\ conj_tac >- ( EVAL_TAC \\ simp[] \\ fs[FFI_codes_def, word_lo_n2w, word_ls_n2w])
    \\ conj_tac >- ( EVAL_TAC \\ simp[] \\ fs[FFI_codes_def, word_lo_n2w, word_ls_n2w])
    \\ simp[lab_to_targetTheory.ffi_offset_def]
    \\ conj_tac >- (EVAL_TAC \\ fs[FFI_codes_def])
    \\ conj_tac >- (EVAL_TAC \\ fs[FFI_codes_def])
    \\ conj_tac >- fs[]
    \\ simp[ag32_machine_config_def]
    \\ simp[ag32_prog_addresses_def]
    \\ fs[EVAL``code_start_offset _``, word_add_n2w,
          EVAL``ffi_jumps_offset``, lab_to_targetTheory.ffi_offset_def,
          EVAL``heap_start_offset``, EVAL``heap_size``]
    \\ qpat_x_assum`_ ≤ _`mp_tac
    \\ simp[FFI_codes_def, LESS_OR_EQ]
    \\ CONV_TAC(LAND_CONV(SIMP_CONV(srw_ss())[NUMERAL_LESS_THM]))
    \\ strip_tac \\ rveq \\ simp[word_ls_n2w, word_lo_n2w]
    \\ TRY( gen_tac \\ CONV_TAC(LAND_CONV(SIMP_CONV(srw_ss())[NUMERAL_LESS_THM])) \\ strip_tac \\ rveq)
    \\ EVAL_TAC)
  \\ conj_tac >- (
    imp_res_tac asmPropsTheory.RTC_asm_step_consts
    \\ qpat_x_assum`_ && 3w = _`mp_tac \\ fs[]
    \\ simp[ag32_init_asm_state_def] )
  \\ conj_tac >- (
    rw[asmPropsTheory.interference_ok_def]
    \\ simp[EVAL``(ag32_machine_config _ _ _).target``]
    \\ simp[EVAL``(ag32_machine_config _ _ _).next_interfer``] )
  \\ simp[LEFT_EXISTS_AND_THM]

  \\ conj_tac >- (
    simp[lab_to_targetProofTheory.ffi_interfer_ok_def]
    \\ simp[hello_machine_config_def, ag32_machine_config_def]
    \\ simp[lab_to_targetTheory.ffi_offset_def,LENGTH_data,heap_size_def,Abbr`num_ffis`,ffi_names]
    \\ simp[EVAL``ag32_target.config``,labSemTheory.get_reg_value_def]
    \\ simp[ag32_ffi_interfer_def]
    \\ simp[LENGTH_ag32_ffi_code,LENGTH_code]
    \\ qmatch_goalsub_abbrev_tac`0w =+ v0`
    \\ qexists_tac`λk s n. if n = 0 then SOME v0 else if n < 9 then SOME 0w else NONE`
    \\ rpt gen_tac
    \\ srw_tac[ETA_ss][]
    \\ fs[asmPropsTheory.target_state_rel_def]
    \\ fs[ag32_targetTheory.ag32_target_def]
    \\ fs[ag32_targetTheory.ag32_ok_def]
    \\ fs[ag32_targetTheory.ag32_config_def]
    \\ conj_tac
    >- (
      rw[]
      \\ fs[ffiTheory.call_FFI_def]
      \\ `st.oracle = (basis_ffi cl fs).oracle` by metis_tac[evaluatePropsTheory.RTC_call_FFI_rel_consts]
      \\ fs[basis_ffiTheory.basis_ffi_def]
      \\ fs[SIMP_CONV(srw_ss())[basis_ffiTheory.basis_ffi_oracle_def]``basis_ffi_oracle "write"``]
      \\ fs[CaseEq"option",CaseEq"bool",CaseEq"oracle_result"]
      \\ pairarg_tac \\ fs[]
      \\ fs[CaseEq"option",CaseEq"bool",CaseEq"oracle_result",CaseEq"ffi_result"]
      \\ rveq \\ fs[]
      \\ simp[ag32_ffi_mem_update_def]
      \\ qmatch_goalsub_abbrev_tac`asm_write_bytearray p new_bytes m2`
      \\ `asm_write_bytearray p new_bytes m2 a = asm_write_bytearray p new_bytes t1.mem a`
      by (
        irule mem_eq_imp_asm_write_bytearray_eq
        \\ simp[Abbr`m2`, APPLY_UPDATE_THM] \\ rw[]
        \\ qpat_x_assum`_ ∈ _.mem_domain`mp_tac
        \\ qpat_x_assum`_ = _.mem_domain`(assume_tac o SYM)
        \\ simp[ag32_prog_addresses_def]
        \\ EVAL_TAC)
      \\ reverse IF_CASES_TAC
      >- (
        rw[APPLY_UPDATE_THM]
        \\ qpat_x_assum`_ ∈ _.mem_domain`mp_tac
        \\ qpat_x_assum`_ = _.mem_domain`(assume_tac o SYM)
        \\ simp[ag32_prog_addresses_def]
        \\ EVAL_TAC)
      \\ rw[]
      \\ fs[targetSemTheory.read_ffi_bytearrays_def]
      \\ fs[targetSemTheory.read_ffi_bytearray_def]
      \\ fs[fsFFITheory.ffi_write_def]
      \\ fs[CaseEq"list"] \\ rveq
      \\ qhdtm_x_assum`OPTION_CHOICE`mp_tac
      \\ rewrite_tac[OPTION_CHOICE_EQUALS_OPTION]
      \\ reverse strip_tac
      >- (
        pop_assum mp_tac \\ simp[LUPDATE_def]
        \\ strip_tac \\ rveq
        \\ qpat_x_assum`_ = 0w`mp_tac
        \\ simp[] )
      \\ fs[]
      \\ pairarg_tac \\ fs[] \\ rveq
      \\ rw[]
      \\ irule asm_write_bytearray_unchanged
      \\ fs[EVAL``output_offset``, output_buffer_size_def]
      \\ fs[LENGTH_TAKE_EQ, fsFFITheory.write_def]
      \\ pairarg_tac \\ fs[]
      \\ qpat_x_assum`_ ∈ _.mem_domain`mp_tac
      \\ qpat_x_assum`_ = _.mem_domain`(mp_tac o SYM)
      \\ simp[ag32_prog_addresses_def]
      \\ strip_tac
      \\ CONV_TAC(LAND_CONV EVAL)
      \\ Cases_on`a` \\ fs[word_ls_n2w, word_lo_n2w, word_add_n2w]
      \\ rw[MIN_DEF])
    \\ simp[APPLY_UPDATE_THM]
    \\ rpt strip_tac
    \\ rpt(IF_CASES_TAC \\ simp[labSemTheory.get_reg_value_def]))
  \\ conj_tac >- (
    rw[lab_to_targetProofTheory.ccache_interfer_ok_def,
       hello_machine_config_def, ag32_machine_config_def,
       lab_to_targetTheory.ffi_offset_def, ag32_ccache_interfer_def,
       LENGTH_data, heap_size_def, EVAL``ag32_target.config``]
    \\ qmatch_goalsub_abbrev_tac`0w =+ v0`
    \\ qexists_tac`λk n. if n = 0 then SOME v0 else NONE`
    \\ EVAL_TAC \\ rw[]
    \\ IF_CASES_TAC \\ simp[labSemTheory.get_reg_value_def] )
  \\ conj_asm1_tac >- (
    simp[targetSemTheory.code_loaded_def]
    \\ fs[asmPropsTheory.target_state_rel_def]
    \\ simp[SIMP_CONV (srw_ss()) [hello_machine_config_def,ag32_machine_config_def]``(hello_machine_config).target``]
    \\ rfs[]
    \\ first_x_assum(CONV_TAC o RAND_CONV o REWR_CONV o SYM)
    \\ AP_TERM_TAC
    \\ rw[FUN_EQ_THM]
    \\ rw[]
    \\ match_mp_tac EQ_SYM
    \\ fs[EVAL``ag32_target.get_byte``]
    \\ reverse(Cases_on`a ∈ ag32_startup_addresses`) \\ fs[]
    >- (
      drule asmPropsTheory.RTC_asm_step_outside_mem_domain
      \\ simp[ag32_init_asm_state_def]
      \\ fs[is_ag32_init_state_def] )
    \\ imp_res_tac asmPropsTheory.RTC_asm_step_consts \\ fs[]
    \\ fs[ag32_init_asm_state_def])
  \\ conj_tac >- (
    fs[bytes_in_mem_bytes_in_memory]
    \\ qpat_x_assum`_.pc = _`(assume_tac o SYM) \\ fs[]
    \\ irule read_bytearray_IMP_bytes_in_memory_WORD_LOWER
    \\ goal_assum(first_assum o mp_then Any mp_tac)
    \\ simp[]
    \\ imp_res_tac asmPropsTheory.RTC_asm_step_consts
    \\ qpat_x_assum`_ = _.pc`(assume_tac o SYM) \\ fs[]
    \\ EVAL_TAC
    \\ simp[LENGTH_data,LENGTH_code,Abbr`num_ffis`,ffi_names]
    \\ Cases \\ fs[word_lo_n2w, word_ls_n2w, word_add_n2w])
  \\ conj_tac >- (
    imp_res_tac asmPropsTheory.RTC_asm_step_consts
    \\ fs[LENGTH_data,heap_size_def]
    \\ EVAL_TAC
    \\ simp[SUBSET_DEF, LENGTH_code, LENGTH_data, Abbr`num_ffis`, ffi_names]
    \\ Cases
    \\ fs[word_lo_n2w, word_ls_n2w, word_add_n2w])
  \\ conj_tac >- (
    gen_tac
    \\ qmatch_goalsub_abbrev_tac`low <=+ byte_align a`
    \\ qmatch_goalsub_abbrev_tac`byte_align a <+ hi`
    \\ strip_tac
    >- (
      disj1_tac
      \\ irule (SIMP_RULE (srw_ss()) [] byte_align_IN_IMP_IN_range)
      \\ simp[Abbr`hi`,Abbr`low`]
      \\ fs[alignmentTheory.byte_aligned_def]
      \\ EVAL_TAC )
    \\ disj2_tac
    \\ irule (SIMP_RULE (srw_ss()) [] byte_align_IN_IMP_IN_range)
    \\ simp[heap_size_def,LENGTH_data,LENGTH_code]
    \\ fs[alignmentTheory.byte_aligned_def,Abbr`hi`,heap_size_def]
    \\ simp[Abbr`num_ffis`,ffi_names]
    \\ EVAL_TAC )
  \\ conj_tac >- (
    simp[EVAL``(hello_machine_config).target.config``]
    \\ Cases
    \\ qmatch_asmsub_rename_tac`i < dimword _`
    \\ `byte_align ((n2w i):word32) <=+ n2w i`
      by metis_tac[align_ls,alignmentTheory.byte_align_def]
    \\ pop_assum mp_tac
    \\ simp[alignmentTheory.byte_align_def, alignmentTheory.align_w2n]
    \\ simp[word_ls_n2w]
    \\ `4 * (i DIV 4) ≤ i` by (
      once_rewrite_tac[MULT_COMM]
      \\ simp[GSYM X_LE_DIV] )
    \\ fs[]
    \\ fs[LESS_EQ_EXISTS]
    \\ qmatch_asmsub_rename_tac`i = q + _`
    \\ `n2w i : word32 = n2w q + n2w (4 * (i DIV 4))` by metis_tac[word_add_n2w]
    \\ pop_assum(fn th => CONV_TAC(RAND_CONV(REWRITE_CONV[th])))
    \\ `n2w (4 * (i DIV 4)) : word32 = byte_align (n2w (4 * (i DIV 4)))`
    by (
      simp[alignmentTheory.byte_align_def]
      \\ simp[GSYM alignmentTheory.aligned_def]
      \\ simp[GSYM ALIGNED_eq_aligned,addressTheory.ALIGNED_n2w] )
    \\ pop_assum(CONV_TAC o PATH_CONV"rllrr" o REWR_CONV)
    \\ DEP_REWRITE_TAC[data_to_word_memoryProofTheory.get_byte_byte_align]
    \\ conj_tac >- EVAL_TAC
    \\ `q < 4`
    by (
      `q = i - 4 * (i DIV 4)` by fs[]
      \\ rw[]
      \\ qspec_then`4`mp_tac DIVISION
      \\ impl_tac >- rw[]
      \\ disch_then(qspec_then`i`mp_tac)
      \\ strip_tac
      \\ first_x_assum(CONV_TAC o LAND_CONV o REWR_CONV)
      \\ simp[] )
    \\ DEP_REWRITE_TAC[MP_CANON get_byte_word_of_bytes]
    \\ simp[word_add_n2w]
    \\ conj_tac >- EVAL_TAC
    \\ Cases_on`q` \\ fs[] >- metis_tac[]
    \\ qmatch_asmsub_rename_tac`SUC q < _`
    \\ Cases_on`q` \\ fs[] >- metis_tac[]
    \\ qmatch_asmsub_rename_tac`SUC (SUC q) < _`
    \\ Cases_on`q` \\ fs[] >- metis_tac[]
    \\ qmatch_asmsub_rename_tac`SUC (SUC (SUC q)) < _`
    \\ Cases_on`q` \\ fs[] >- metis_tac[] )
  \\ simp[LENGTH_code]);
*)

val hello_good_init_state = Q.store_thm("hello_good_init_state",
  `SUM (MAP strlen cl) + LENGTH cl ≤ cline_size ∧
   LENGTH inp ≤ stdin_size ∧
   is_ag32_init_state (hello_init_memory (cl,inp)) ms0 ⇒
   ∃io_regs cc_regs.
   good_init_state hello_machine_config (FUNPOW Next (hello_startup_clock ms0 inp cl) ms0)
     (basis_ffi cl fs) code 0
     ((hello_start_asm_state (cl,inp)) with mem_domain := hello_machine_config.prog_addresses)
     (λk. Word
       (word_of_bytes F 0w (GENLIST (λi. (hello_start_asm_state (cl,inp)).mem (k + n2w i)) 4)))
       ({w | (hello_start_asm_state (cl,inp)).regs 2 <=+ w ∧
             w <+ (hello_start_asm_state (cl,inp)).regs 4}
        ∪ {w | n2w (code_start_offset (LENGTH (THE config.ffi_names)) + LENGTH code) <=+ w ∧
               w <+ n2w(code_start_offset (LENGTH (THE config.ffi_names)) + LENGTH code + 4 * LENGTH data) })
     io_regs
     cc_regs`,
  strip_tac
  \\ drule hello_startup_clock_def \\ fs[]
  \\ disch_then drule \\ disch_then drule
  \\ strip_tac
  \\ simp[lab_to_targetProofTheory.good_init_state_def,RIGHT_EXISTS_AND_THM]
  \\ mp_tac hello_start_asm_state_RTC_asm_step
  \\ impl_tac >- fs[]
  \\ strip_tac
  \\ conj_tac >- (
    fs[hello_machine_config_def, ag32_machine_config_def]
    \\ fs[asmPropsTheory.target_state_rel_def]
    \\ fs[EVAL``ag32_target.get_byte``]
    \\ qx_gen_tac`a` \\ strip_tac
    \\ drule asmPropsTheory.RTC_asm_step_consts
    \\ strip_tac \\ fs[]
    \\ `hello_asm_state0.mem_domain = ag32_startup_addresses` by (
      fs[ag32_init_asm_state_def] )
    \\ fs[]
    \\ Cases_on`a ∈ ag32_startup_addresses` \\ fs[]
    \\ drule asmPropsTheory.RTC_asm_step_outside_mem_domain
    \\ simp[]
    \\ fs[is_ag32_init_state_def]
    \\ simp[ag32_init_asm_state_def])
  \\ conj_tac
  >- (
    Q.ISPEC_THEN `hello_machine_config with prog_addresses := ag32_startup_addresses`
      drule (Q.GEN`mc` RTC_asm_step_target_configured)
    \\ simp[lab_to_targetProofTheory.target_configured_def]
    \\ impl_tac >- EVAL_TAC
    \\ strip_tac \\ fs[])
  \\ conj_tac >- (
    fs[asmPropsTheory.target_state_rel_def, hello_machine_config_def, ag32_machine_config_def] )
  \\ qabbrev_tac`num_ffis = LENGTH (THE config.ffi_names)`
  \\ `n2w (code_start_offset num_ffis) && 3w = 0w:word32` by (
    EVAL_TAC
    \\ fs[alignmentTheory.aligned_bitwise_and, alignmentTheory.byte_aligned_def, Abbr`num_ffis`, ffi_names])
  \\ `n2w (code_start_offset num_ffis) && 1w = 0w:word32` by (
    EVAL_TAC
    \\ fs[alignmentTheory.aligned_bitwise_and, alignmentTheory.byte_aligned_def, Abbr`num_ffis`, ffi_names])
  \\ conj_tac >- (
    rewrite_tac[lab_to_targetProofTheory.start_pc_ok_def]
    \\ conj_tac >- ( EVAL_TAC \\ simp[LENGTH_code, LENGTH_data, ffi_names, Abbr`num_ffis`])
    \\ conj_tac >- ( EVAL_TAC \\ simp[LENGTH_code, LENGTH_data, ffi_names, Abbr`num_ffis`])
    \\ simp[lab_to_targetTheory.ffi_offset_def]
    \\ conj_tac >- (EVAL_TAC \\ simp[ffi_names,Abbr`num_ffis`])
    \\ conj_tac >- (EVAL_TAC \\ simp[ffi_names,Abbr`num_ffis`] )
    \\ conj_tac >- fs[]
    \\ rewrite_tac[EVAL``hello_machine_config.ffi_names``]
    \\ fs[ffi_names, Abbr`num_ffis`,lab_to_targetTheory.ffi_offset_def, EVAL``code_start_offset n``]
    \\ simp[hello_machine_config_def, ffi_names, ag32_machine_config_def]
    \\ EVAL_TAC \\ simp[LENGTH_data, LENGTH_code])
  \\ conj_tac >- (
    imp_res_tac asmPropsTheory.RTC_asm_step_consts
    \\ qpat_x_assum`_ && 3w = _`mp_tac \\ fs[]
    \\ simp[ag32_init_asm_state_def] )
  \\ conj_tac >- (
    rw[asmPropsTheory.interference_ok_def]
    \\ simp[EVAL``(hello_machine_config).target``]
    \\ simp[EVAL``(hello_machine_config).next_interfer``] )
  \\ simp[LEFT_EXISTS_AND_THM]
  \\ conj_tac >- (
    simp[lab_to_targetProofTheory.ffi_interfer_ok_def]
    \\ simp[hello_machine_config_def, ag32_machine_config_def]
    \\ simp[lab_to_targetTheory.ffi_offset_def,LENGTH_data,heap_size_def,Abbr`num_ffis`,ffi_names]
    \\ simp[EVAL``ag32_target.config``,labSemTheory.get_reg_value_def]
    \\ simp[ag32_ffi_interfer_def]
    \\ simp[LENGTH_ag32_ffi_code,LENGTH_code]
    \\ qmatch_goalsub_abbrev_tac`0w =+ v0`
    \\ qexists_tac`λk s n. if n = 0 then SOME v0 else if n < 9 then SOME 0w else NONE`
    \\ rpt gen_tac
    \\ srw_tac[ETA_ss][]
    \\ fs[asmPropsTheory.target_state_rel_def]
    \\ fs[ag32_targetTheory.ag32_target_def]
    \\ fs[ag32_targetTheory.ag32_ok_def]
    \\ fs[ag32_targetTheory.ag32_config_def]
    \\ conj_tac
    >- (
      rw[]
      \\ fs[ffiTheory.call_FFI_def]
      \\ `st.oracle = (basis_ffi cl fs).oracle` by metis_tac[evaluatePropsTheory.RTC_call_FFI_rel_consts]
      \\ fs[basis_ffiTheory.basis_ffi_def]
      \\ fs[SIMP_CONV(srw_ss())[basis_ffiTheory.basis_ffi_oracle_def]``basis_ffi_oracle "write"``]
      \\ fs[CaseEq"option",CaseEq"bool",CaseEq"oracle_result"]
      \\ pairarg_tac \\ fs[]
      \\ fs[CaseEq"option",CaseEq"bool",CaseEq"oracle_result",CaseEq"ffi_result"]
      \\ rveq \\ fs[]
      \\ simp[ag32_ffi_mem_update_def]
      \\ qmatch_goalsub_abbrev_tac`asm_write_bytearray p new_bytes m2`
      \\ `asm_write_bytearray p new_bytes m2 a = asm_write_bytearray p new_bytes t1.mem a`
      by (
        irule mem_eq_imp_asm_write_bytearray_eq
        \\ simp[Abbr`m2`, APPLY_UPDATE_THM] \\ rw[]
        \\ qpat_x_assum`_ ∈ _.mem_domain`mp_tac
        \\ qpat_x_assum`_ = _.mem_domain`(assume_tac o SYM)
        \\ simp[ag32_prog_addresses_def]
        \\ EVAL_TAC)
      \\ reverse IF_CASES_TAC
      >- (
        rw[APPLY_UPDATE_THM]
        \\ qpat_x_assum`_ ∈ _.mem_domain`mp_tac
        \\ qpat_x_assum`_ = _.mem_domain`(assume_tac o SYM)
        \\ simp[ag32_prog_addresses_def]
        \\ EVAL_TAC)
      \\ rw[]
      \\ fs[targetSemTheory.read_ffi_bytearrays_def]
      \\ fs[targetSemTheory.read_ffi_bytearray_def]
      \\ fs[fsFFITheory.ffi_write_def]
      \\ fs[CaseEq"list"] \\ rveq
      \\ qhdtm_x_assum`OPTION_CHOICE`mp_tac
      \\ rewrite_tac[OPTION_CHOICE_EQUALS_OPTION]
      \\ reverse strip_tac
      >- (
        pop_assum mp_tac \\ simp[LUPDATE_def]
        \\ strip_tac \\ rveq
        \\ qpat_x_assum`_ = 0w`mp_tac
        \\ simp[] )
      \\ fs[]
      \\ pairarg_tac \\ fs[] \\ rveq
      \\ rw[]
      \\ irule asm_write_bytearray_unchanged
      \\ fs[EVAL``output_offset``, output_buffer_size_def]
      \\ fs[LENGTH_TAKE_EQ, fsFFITheory.write_def]
      \\ pairarg_tac \\ fs[]
      \\ qpat_x_assum`_ ∈ _.mem_domain`mp_tac
      \\ qpat_x_assum`_ = _.mem_domain`(mp_tac o SYM)
      \\ simp[ag32_prog_addresses_def]
      \\ strip_tac
      \\ CONV_TAC(LAND_CONV EVAL)
      \\ Cases_on`a` \\ fs[word_ls_n2w, word_lo_n2w, word_add_n2w]
      \\ rw[MIN_DEF])
    \\ simp[APPLY_UPDATE_THM]
    \\ rpt strip_tac
    \\ rpt(IF_CASES_TAC \\ simp[labSemTheory.get_reg_value_def]))
  \\ conj_tac >- (
    rw[lab_to_targetProofTheory.ccache_interfer_ok_def,
       hello_machine_config_def, ag32_machine_config_def,
       lab_to_targetTheory.ffi_offset_def, ag32_ccache_interfer_def,
       LENGTH_data, heap_size_def, EVAL``ag32_target.config``]
    \\ qmatch_goalsub_abbrev_tac`0w =+ v0`
    \\ qexists_tac`λk n. if n = 0 then SOME v0 else NONE`
    \\ EVAL_TAC \\ rw[]
    \\ IF_CASES_TAC \\ simp[labSemTheory.get_reg_value_def] )
  \\ conj_asm1_tac >- (
    simp[targetSemTheory.code_loaded_def]
    \\ fs[asmPropsTheory.target_state_rel_def]
    \\ simp[SIMP_CONV (srw_ss()) [hello_machine_config_def,ag32_machine_config_def]``(hello_machine_config).target``]
    \\ rfs[]
    \\ first_x_assum(CONV_TAC o RAND_CONV o REWR_CONV o SYM)
    \\ AP_TERM_TAC
    \\ rw[FUN_EQ_THM]
    \\ rw[]
    \\ match_mp_tac EQ_SYM
    \\ fs[EVAL``ag32_target.get_byte``]
    \\ reverse(Cases_on`a ∈ ag32_startup_addresses`) \\ fs[]
    >- (
      drule asmPropsTheory.RTC_asm_step_outside_mem_domain
      \\ simp[ag32_init_asm_state_def]
      \\ fs[is_ag32_init_state_def] )
    \\ imp_res_tac asmPropsTheory.RTC_asm_step_consts \\ fs[]
    \\ fs[ag32_init_asm_state_def])
  \\ conj_tac >- (
    fs[bytes_in_mem_bytes_in_memory]
    \\ qpat_x_assum`_.pc = _`(assume_tac o SYM) \\ fs[]
    \\ irule read_bytearray_IMP_bytes_in_memory_WORD_LOWER
    \\ goal_assum(first_assum o mp_then Any mp_tac)
    \\ simp[]
    \\ imp_res_tac asmPropsTheory.RTC_asm_step_consts
    \\ qpat_x_assum`_ = _.pc`(assume_tac o SYM) \\ fs[]
    \\ EVAL_TAC
    \\ simp[LENGTH_data,LENGTH_code,Abbr`num_ffis`,ffi_names]
    \\ Cases \\ fs[word_lo_n2w, word_ls_n2w, word_add_n2w])
  \\ conj_tac >- (
    imp_res_tac asmPropsTheory.RTC_asm_step_consts
    \\ fs[LENGTH_data,heap_size_def]
    \\ EVAL_TAC
    \\ simp[SUBSET_DEF, LENGTH_code, LENGTH_data, Abbr`num_ffis`, ffi_names]
    \\ Cases
    \\ fs[word_lo_n2w, word_ls_n2w, word_add_n2w])
  \\ conj_tac >- (
    gen_tac
    \\ qmatch_goalsub_abbrev_tac`low <=+ byte_align a`
    \\ qmatch_goalsub_abbrev_tac`byte_align a <+ hi`
    \\ strip_tac
    >- (
      disj1_tac
      \\ irule (SIMP_RULE (srw_ss()) [] byte_align_IN_IMP_IN_range)
      \\ simp[Abbr`hi`,Abbr`low`]
      \\ fs[alignmentTheory.byte_aligned_def]
      \\ EVAL_TAC )
    \\ disj2_tac
    \\ irule (SIMP_RULE (srw_ss()) [] byte_align_IN_IMP_IN_range)
    \\ simp[heap_size_def,LENGTH_data,LENGTH_code]
    \\ fs[alignmentTheory.byte_aligned_def,Abbr`hi`,heap_size_def]
    \\ simp[Abbr`num_ffis`,ffi_names]
    \\ EVAL_TAC )
  \\ conj_tac >- (
    simp[EVAL``(hello_machine_config).target.config``]
    \\ Cases
    \\ qmatch_asmsub_rename_tac`i < dimword _`
    \\ `byte_align ((n2w i):word32) <=+ n2w i`
      by metis_tac[align_ls,alignmentTheory.byte_align_def]
    \\ pop_assum mp_tac
    \\ simp[alignmentTheory.byte_align_def, alignmentTheory.align_w2n]
    \\ simp[word_ls_n2w]
    \\ `4 * (i DIV 4) ≤ i` by (
      once_rewrite_tac[MULT_COMM]
      \\ simp[GSYM X_LE_DIV] )
    \\ fs[]
    \\ fs[LESS_EQ_EXISTS]
    \\ qmatch_asmsub_rename_tac`i = q + _`
    \\ `n2w i : word32 = n2w q + n2w (4 * (i DIV 4))` by metis_tac[word_add_n2w]
    \\ pop_assum(fn th => CONV_TAC(RAND_CONV(REWRITE_CONV[th])))
    \\ `n2w (4 * (i DIV 4)) : word32 = byte_align (n2w (4 * (i DIV 4)))`
    by (
      simp[alignmentTheory.byte_align_def]
      \\ simp[GSYM alignmentTheory.aligned_def]
      \\ simp[GSYM ALIGNED_eq_aligned,addressTheory.ALIGNED_n2w] )
    \\ pop_assum(CONV_TAC o PATH_CONV"rllrr" o REWR_CONV)
    \\ DEP_REWRITE_TAC[data_to_word_memoryProofTheory.get_byte_byte_align]
    \\ conj_tac >- EVAL_TAC
    \\ `q < 4`
    by (
      `q = i - 4 * (i DIV 4)` by fs[]
      \\ rw[]
      \\ qspec_then`4`mp_tac DIVISION
      \\ impl_tac >- rw[]
      \\ disch_then(qspec_then`i`mp_tac)
      \\ strip_tac
      \\ first_x_assum(CONV_TAC o LAND_CONV o REWR_CONV)
      \\ simp[] )
    \\ DEP_REWRITE_TAC[MP_CANON get_byte_word_of_bytes]
    \\ simp[word_add_n2w]
    \\ conj_tac >- EVAL_TAC
    \\ Cases_on`q` \\ fs[] >- metis_tac[]
    \\ qmatch_asmsub_rename_tac`SUC q < _`
    \\ Cases_on`q` \\ fs[] >- metis_tac[]
    \\ qmatch_asmsub_rename_tac`SUC (SUC q) < _`
    \\ Cases_on`q` \\ fs[] >- metis_tac[]
    \\ qmatch_asmsub_rename_tac`SUC (SUC (SUC q)) < _`
    \\ Cases_on`q` \\ fs[] >- metis_tac[] )
  \\ simp[LENGTH_code]);

val is_ag32_machine_config_hello_machine_config = Q.store_thm("is_ag32_machine_config_hello_machine_config",
  `is_ag32_machine_config hello_machine_config`,
  rw[hello_machine_config_def, is_ag32_machine_config_ag32_machine_config]);

val compile_correct_applied =
  MATCH_MP compile_correct hello_compiled
  |> SIMP_RULE(srw_ss())[LET_THM,ml_progTheory.init_state_env_thm,GSYM AND_IMP_INTRO]
  |> C MATCH_MP hello_not_fail
  |> C MATCH_MP ag32_backend_config_ok
  |> REWRITE_RULE[hello_sem_sing,AND_IMP_INTRO]
  |> REWRITE_RULE[Once (GSYM AND_IMP_INTRO)]
  |> C MATCH_MP (CONJ(UNDISCH ag32_machine_config_ok)(UNDISCH ag32_init_ok))
  |> DISCH(#1(dest_imp(concl ag32_init_ok)))
  |> C MATCH_MP is_ag32_machine_config_hello_machine_config
  |> Q.GEN`cbspace` |> Q.SPEC`0`
  |> Q.GEN`data_sp` |> Q.SPEC`0`

val hello_installed = Q.store_thm("hello_installed",
  `SUM (MAP strlen cl) + LENGTH cl ≤ cline_size ∧
   LENGTH inp ≤ stdin_size ∧
   is_ag32_init_state (hello_init_memory (cl,inp)) ms0 ⇒
   installed code 0 data 0 config.ffi_names (basis_ffi cl fs)
     (heap_regs ag32_backend_config.stack_conf.reg_names)
     (hello_machine_config) (FUNPOW Next (hello_startup_clock ms0 inp cl) ms0)`,
  disch_then assume_tac
  \\ CONV_TAC(PATH_CONV"llr"EVAL)
  \\ simp[backendProofTheory.installed_def]
  \\ simp[word_list_exists_def, set_sepTheory.SEP_CLAUSES, word_list_def]
  \\ simp[EVAL``(hello_machine_config).target.get_pc``]
  \\ strip_assume_tac(UNDISCH hello_good_init_state)
  \\ fs[]
  \\ mp_tac hello_start_asm_state_RTC_asm_step
  \\ impl_tac >- fs[]
  \\ strip_tac
  \\ qmatch_asmsub_abbrev_tac`good_init_state _ _ _ _ _ t`
  \\ qexists_tac`t` \\ simp[Abbr`t`]
  \\ asm_exists_tac \\ rfs[]
  \\ qhdtm_x_assum`good_init_state` mp_tac
  \\ rewrite_tac[lab_to_targetProofTheory.good_init_state_def]
  \\ disch_then(assume_tac o el 1 o CONJUNCTS)
  \\ conj_tac >- EVAL_TAC
  \\ conj_tac >- EVAL_TAC
  \\ conj_tac >- (simp[ffi_names, LENGTH_code] \\ EVAL_TAC)
  \\ conj_tac >- EVAL_TAC
  \\ conj_tac >- EVAL_TAC
  \\ conj_tac
  >- (
    simp[IN_DISJOINT]
    \\ EVAL_TAC
    \\ simp[LENGTH_code,LENGTH_data,ffi_names]
    \\ Cases
    \\ fs[word_add_n2w,word_ls_n2w,word_lo_n2w] )
  \\ conj_tac
  >- ( rw[LENGTH_data, bytes_in_word_def, LENGTH_code, ffi_names] )
  \\ conj_tac >- simp[bytes_in_word_def, GSYM word_add_n2w, word_mul_n2w]
  \\ conj_tac >- (
    fs[asmPropsTheory.target_state_rel_def,
       hello_machine_config_def, ag32_machine_config_def,
       ag32_targetTheory.ag32_target_def]
    \\ simp[bytes_in_word_def, GSYM word_add_n2w, GSYM word_mul_n2w] )
  \\ conj_tac >- (
    fs[asmPropsTheory.target_state_rel_def,
       hello_machine_config_def,
       ag32_machine_config_def,
       ag32_targetTheory.ag32_target_def]
    \\ simp[bytes_in_word_def, GSYM word_add_n2w, GSYM word_mul_n2w] )
  \\ conj_tac >- (
    irule IMP_word_list
    \\ fs[LENGTH_code, LENGTH_data, heap_size_def, bytes_in_word_def,
          memory_size_def, ffi_names, EVAL``code_start_offset n``]
    \\ fs[word_add_n2w]
    \\ simp[EXTENSION,FORALL_PROD,set_sepTheory.IN_fun2set]
    \\ reverse(rw[EQ_IMP_THM])
    \\ fs[word_mul_n2w, word_add_n2w, word_lo_n2w, word_ls_n2w]
    \\ simp[EL_MAP, LENGTH_data]
    >- (
      simp[IN_DEF,alignmentTheory.byte_aligned_def]
      \\ simp[GSYM word_add_n2w]
      \\ (alignmentTheory.aligned_add_sub_cor
          |> SPEC_ALL |> UNDISCH |> CONJUNCT1 |> DISCH_ALL
          |> irule)
      \\ reverse conj_tac >- EVAL_TAC
      \\ fs[alignmentTheory.byte_aligned_def]
      \\ simp[GSYM word_mul_n2w]
      \\ simp[GSYM ALIGNED_eq_aligned]
      \\ qspecl_then[`0w`,`n2w k`]mp_tac addressTheory.ALIGNED_MULT
      \\ simp[]
      \\ disch_then irule
      \\ EVAL_TAC )
    >- (
      first_assum(qspec_then`4 * k + 0`mp_tac)
      \\ first_assum(qspec_then`4 * k + 1`mp_tac)
      \\ first_assum(qspec_then`4 * k + 2`mp_tac)
      \\ first_x_assum(qspec_then`4 * k + 3`mp_tac)
      \\ simp[]
      \\ ntac 4 (disch_then kall_tac)
      \\ qmatch_goalsub_abbrev_tac`n + off`
      \\ qmatch_goalsub_abbrev_tac`word_of_bytes _ _ ls`
      \\ `ls = GENLIST (λi. hello_init_memory (cl,inp) (n2w (4 * (k + (off DIV 4)) + i))) 4`
      by ( simp[Abbr`ls`,Abbr`off`,LEFT_ADD_DISTRIB] )
      \\ qpat_x_assum`Abbrev(ls = _)`kall_tac
      \\ pop_assum SUBST_ALL_TAC
      \\ simp[Abbr`off`, GSYM word_add_n2w]
      \\ simp[hello_init_memory_eq]
      \\ rewrite_tac[GSYM WORD_ADD_ASSOC]
      \\ `∀(y:word32) x. get_byte (n2w (4 * x) + y) = get_byte y`
      by (
        rw[FUN_EQ_THM]
        \\ `byte_aligned ((n2w (4 * x)):word32)` by (
          fs[alignmentTheory.byte_aligned_def, GSYM ALIGNED_eq_aligned, addressTheory.ALIGNED_n2w] )
        \\ `n2w (4 * x) : word32 = byte_align (n2w (4 * x))`
        by ( fs[alignmentTheory.byte_aligned_def, alignmentTheory.byte_align_def, alignmentTheory.aligned_def] )
        \\ pop_assum SUBST1_TAC
        \\ match_mp_tac data_to_word_memoryProofTheory.get_byte_byte_align
        \\ EVAL_TAC )
      \\ simp[]
      \\ pop_assum(qspec_then`0w`mp_tac) \\ simp[]
      \\ disch_then kall_tac
      \\ `∀y x. byte_align (n2w (4 * x) + y) = n2w (4 * x) + byte_align y : word32`
      by (
        rw[]
        \\ `byte_aligned ((n2w (4 * x)):word32)` by (
          fs[alignmentTheory.byte_aligned_def, GSYM ALIGNED_eq_aligned, addressTheory.ALIGNED_n2w] )
        \\ fs[alignmentTheory.byte_aligned_def, alignmentTheory.byte_align_def]
        \\ ONCE_REWRITE_TAC[WORD_ADD_COMM]
        \\ DEP_REWRITE_TAC[align_add_aligned_gen]
        \\ simp[] )
      \\ simp[]
      \\ pop_assum(qspec_then`0w`mp_tac)
      \\ simp[]
      \\ disch_then kall_tac
      \\ simp[alignmentTheory.byte_align_def, alignmentTheory.align_def]
      \\ once_rewrite_tac[MULT_COMM]
      \\ simp[MULT_DIV]
      \\ qmatch_goalsub_abbrev_tac`get_byte _ mm`
      \\ pop_assum mp_tac
      \\ rewrite_tac[hello_init_memory_words_eq]
      \\ DEP_REWRITE_TAC[EL_APPEND2]
      \\ qmatch_goalsub_abbrev_tac`ll ≤ _`
      \\ pop_assum mp_tac
      \\ simp[LENGTH_words_of_bytes_hello_startup_code,LENGTH_ag32_ffi_code,heap_size_def,
              output_buffer_size_def,startup_code_size_def,LENGTH_hello_startup_code,
              LENGTH_ag32_ffi_jumps, ffi_names]
      \\ simp[LENGTH_words_of_bytes, bitstringTheory.length_pad_right, LENGTH_code,
              bytes_in_word_def, LENGTH_FLAT, MAP_MAP_o, o_DEF, ADD1, SUM_MAP_PLUS,
              Q.ISPEC`λx. 1n`SUM_MAP_K |> SIMP_RULE(srw_ss())[]]
      \\ qmatch_goalsub_abbrev_tac`sz DIV 4`
      \\ `sz = stdin_size` by (rw[Abbr`sz`])
      \\ qpat_x_assum`Abbrev(sz = _)`kall_tac
      \\ qmatch_goalsub_abbrev_tac`_ + (cz DIV 4 + _)`
      \\ `cz = cline_size` by (rw[Abbr`cz`])
      \\ qpat_x_assum`Abbrev(cz = _)`kall_tac
      \\ rveq
      \\ rw[stdin_size_def, cline_size_def]
      \\ simp[word_of_bytes_def]
      \\ simp[get_byte_def, byte_index_def,
              set_byte_def, word_slice_alt_def]
      \\ blastLib.BBLAST_TAC)
    \\ qmatch_asmsub_rename_tac`_ <=+ p`
    \\ Cases_on`p` \\ fs[word_ls_n2w,word_lo_n2w] \\ rfs[] \\ rw[]
    \\ qmatch_asmsub_rename_tac`_ <= q`
    \\ qmatch_asmsub_abbrev_tac`l ≤ q`
    \\ qpat_x_assum`l ≤ q`mp_tac
    \\ simp[LESS_EQ_EXISTS] \\ strip_tac
    \\ `∃d. p = 4 * d`
    by (
      fs[IN_DEF,alignmentTheory.byte_aligned_def,GSYM ALIGNED_eq_aligned,
         addressTheory.ALIGNED_n2w]
      \\ fs[MOD_EQ_0_DIVISOR] \\ rfs[]
      \\ fs[Abbr`l`] \\ rveq
      \\ qmatch_asmsub_abbrev_tac`p + m = 4 * d`
      \\ qexists_tac`(d - m DIV 4)`
      \\ simp[Abbr`m`])
    \\ qexists_tac`d`
    \\ simp[]
    \\ simp[Abbr`l`]
    (* TODO: all copied from previous subgoal -- try to pull out a lemma, or better subgoal *)
    \\ first_assum(qspec_then`4 * d + 0`mp_tac)
    \\ first_assum(qspec_then`4 * d + 1`mp_tac)
    \\ first_assum(qspec_then`4 * d + 2`mp_tac)
    \\ first_x_assum(qspec_then`4 * d + 3`mp_tac)
    \\ simp[word_add_n2w]
    \\ rpt(disch_then kall_tac)
    \\ `d < LENGTH data` by ( simp[LENGTH_data] ) \\ simp[EL_MAP]
    \\ qmatch_goalsub_abbrev_tac`n + off`
    \\ qmatch_goalsub_abbrev_tac`word_of_bytes _ _ ls`
    \\ `ls = GENLIST (λi. hello_init_memory (cl,inp) (n2w (4 * (d + (off DIV 4)) + i))) 4`
    by ( simp[Abbr`ls`,Abbr`off`,LEFT_ADD_DISTRIB] )
    \\ qpat_x_assum`Abbrev(ls = _)`kall_tac
    \\ pop_assum SUBST_ALL_TAC
    \\ simp[Abbr`off`, GSYM word_add_n2w]
    \\ simp[hello_init_memory_eq]
    \\ rewrite_tac[GSYM WORD_ADD_ASSOC]
    \\ `∀(y:word32) x. get_byte (n2w (4 * x) + y) = get_byte y`
    by (
      rw[FUN_EQ_THM]
      \\ `byte_aligned ((n2w (4 * x)):word32)` by (
        fs[alignmentTheory.byte_aligned_def, GSYM ALIGNED_eq_aligned, addressTheory.ALIGNED_n2w] )
      \\ `n2w (4 * x) : word32 = byte_align (n2w (4 * x))`
      by ( fs[alignmentTheory.byte_aligned_def, alignmentTheory.byte_align_def, alignmentTheory.aligned_def] )
      \\ pop_assum SUBST1_TAC
      \\ match_mp_tac data_to_word_memoryProofTheory.get_byte_byte_align
      \\ EVAL_TAC )
    \\ simp[]
    \\ pop_assum(qspec_then`0w`mp_tac) \\ simp[]
    \\ disch_then kall_tac
    \\ `∀y x. byte_align (n2w (4 * x) + y) = n2w (4 * x) + byte_align y : word32`
    by (
      rw[]
      \\ `byte_aligned ((n2w (4 * x)):word32)` by (
        fs[alignmentTheory.byte_aligned_def, GSYM ALIGNED_eq_aligned, addressTheory.ALIGNED_n2w] )
      \\ fs[alignmentTheory.byte_aligned_def, alignmentTheory.byte_align_def]
      \\ ONCE_REWRITE_TAC[WORD_ADD_COMM]
      \\ DEP_REWRITE_TAC[align_add_aligned_gen]
      \\ simp[] )
    \\ simp[]
    \\ pop_assum(qspec_then`0w`mp_tac)
    \\ simp[]
    \\ disch_then kall_tac
    \\ simp[alignmentTheory.byte_align_def, alignmentTheory.align_def]
    \\ once_rewrite_tac[MULT_COMM]
    \\ simp[MULT_DIV]
    \\ qmatch_goalsub_abbrev_tac`get_byte _ mm`
    \\ pop_assum mp_tac
    \\ rewrite_tac[hello_init_memory_words_eq]
    \\ DEP_REWRITE_TAC[EL_APPEND2]
    \\ qmatch_goalsub_abbrev_tac`ll ≤ _`
    \\ pop_assum mp_tac
    \\ simp[LENGTH_words_of_bytes_hello_startup_code,LENGTH_ag32_ffi_code,heap_size_def,
            output_buffer_size_def,startup_code_size_def,LENGTH_hello_startup_code,
            LENGTH_ag32_ffi_jumps, ffi_names]
    \\ simp[LENGTH_words_of_bytes, bitstringTheory.length_pad_right, LENGTH_code,
            bytes_in_word_def, LENGTH_FLAT, MAP_MAP_o, o_DEF, ADD1, SUM_MAP_PLUS,
            Q.ISPEC`λx. 1n`SUM_MAP_K |> SIMP_RULE(srw_ss())[]]
    \\ qmatch_goalsub_abbrev_tac`sz DIV 4`
    \\ `sz = stdin_size` by (rw[Abbr`sz`])
    \\ qpat_x_assum`Abbrev(sz = _)`kall_tac
    \\ qmatch_goalsub_abbrev_tac`_ + (cz DIV 4 + _)`
    \\ `cz = cline_size` by (rw[Abbr`cz`])
    \\ qpat_x_assum`Abbrev(cz = _)`kall_tac
    \\ rveq
    \\ rw[stdin_size_def, cline_size_def]
    \\ simp[word_of_bytes_def, Abbr`ll`]
    \\ fs[LENGTH_data, LEFT_ADD_DISTRIB, Abbr`n`]
    >- ( DEP_REWRITE_TAC[ADD_DIV_RWT] \\ simp[] )
    \\ pop_assum mp_tac
    \\ simp[]
    \\ DEP_REWRITE_TAC[ADD_DIV_RWT] \\ simp[]
    \\ once_rewrite_tac[MULT_COMM]
    \\ simp[MULT_DIV] \\ rw[]
    \\ simp[get_byte_def, byte_index_def,
            set_byte_def, word_slice_alt_def]
    \\ blastLib.BBLAST_TAC)
  \\ EVAL_TAC
  \\ rewrite_tac[ffi_names]
  \\ EVAL_TAC);

val hello_machine_sem =
  compile_correct_applied
  |> C MATCH_MP (UNDISCH hello_installed)
  |> DISCH_ALL
  |> curry save_thm "hello_machine_sem";

val hello_halted = Q.store_thm("hello_halted",
  `∀ms.
    SUM (MAP strlen cl) + LENGTH cl ≤ cline_size ∧
    LENGTH inp ≤ stdin_size ∧
    (mc = hello_machine_config) ∧
    (ms.PC = mc.halt_pc) ∧
    (∀x. mc.halt_pc <=+ x ∧ x <+ mc.halt_pc + 16w ⇒
         (mc.target.get_byte ms x = (hello_init_memory (cl,inp)) x)) ⇒
    ∀k. ((FUNPOW Next k ms).io_events = ms.io_events) ∧
        ((FUNPOW Next k ms).PC = ms.PC) ∧
        ((FUNPOW Next k ms).MEM = ms.MEM) ∧
        (∀w. w ≠ 0w ⇒ ((FUNPOW Next k ms).R w = ms.R w))`,
  gen_tac \\ strip_tac \\ rveq
  \\ Induct >- rw[]
  \\ simp[FUNPOW_SUC]
  \\ qmatch_goalsub_abbrev_tac`ms1.io_events`
  \\ pop_assum mp_tac
  \\ simp[ag32Theory.Next_def]
  \\ qmatch_goalsub_abbrev_tac`pc' + 2w`
  \\ qmatch_asmsub_abbrev_tac`_.PC = pc`
  \\ `aligned 2 pc`
  by (
    simp[Abbr`pc`]
    \\ simp[hello_machine_config_def, ag32_machine_config_def]
    \\ simp[LENGTH_data, heap_size_def, lab_to_targetTheory.ffi_offset_def, ffi_names]
    \\ EVAL_TAC )
  \\ `pc = pc'`
  by (
    pop_assum mp_tac
    \\ unabbrev_all_tac
    \\ simp[alignmentTheory.aligned_extract]
    \\ blastLib.BBLAST_TAC )
  \\ qpat_x_assum`Abbrev(pc' = _)` kall_tac
  \\ pop_assum (SUBST_ALL_TAC o SYM)
  \\ fs[Abbr`pc`]
  \\ first_assum(qspec_then`ms.PC`mp_tac)
  \\ impl_tac >- simp[hello_machine_config_halt_pc]
  \\ first_assum(qspec_then`ms.PC + 1w`mp_tac)
  \\ impl_tac >- simp[hello_machine_config_halt_pc]
  \\ first_assum(qspec_then`ms.PC + 2w`mp_tac)
  \\ impl_tac >- simp[hello_machine_config_halt_pc]
  \\ first_x_assum(qspec_then`ms.PC + 3w`mp_tac)
  \\ impl_tac >- simp[hello_machine_config_halt_pc]
  \\ simp[]
  \\ simp[EVAL``(hello_machine_config).target.get_byte``]
  \\ rpt (disch_then SUBST_ALL_TAC)
  \\ qmatch_goalsub_abbrev_tac`_ @@ hello_init_memory _ pc`
  \\ mp_tac hello_init_memory_halt
  \\ impl_tac >- simp[]
  \\ simp[get_mem_word_def]
  \\ disch_then kall_tac
  \\ simp[ag32_targetProofTheory.Decode_Encode]
  \\ simp[ag32Theory.Run_def, ag32Theory.dfn'Jump_def]
  \\ simp[ag32Theory.ALU_def, ag32Theory.ri2word_def]
  \\ strip_tac
  \\ simp[Abbr`ms1`, APPLY_UPDATE_THM]);

val hello_interference_implemented = Q.store_thm("hello_interference_implemented",
  `SUM (MAP strlen cl) + LENGTH cl ≤ cline_size ∧
   LENGTH inp ≤ stdin_size ∧
   is_ag32_init_state (hello_init_memory (cl,inp)) ms0 ∧
   Abbrev(ms = FUNPOW Next (hello_startup_clock ms0 inp cl) ms0)
  ⇒
   interference_implemented
    (hello_machine_config)
    (ag32_ffi_rel)
    (ag32_ffi_mem_domain) ms`,
  rw[interference_implemented_def]
  \\ simp[EVAL``(hello_machine_config).target.next``]
  \\ simp[EVAL``(hello_machine_config).target.get_byte``]
  \\ simp[EVAL``(hello_machine_config).target.get_pc``]
  \\ simp[EVAL``(hello_machine_config).target.get_reg``]
  \\ simp[EVAL``(hello_machine_config).ffi_entry_pcs``]
  \\ simp[ffi_names, REV_DEF]
  \\ simp[Once hello_machine_config_def, ag32_machine_config_def]
  \\ simp[Once hello_machine_config_def, ag32_machine_config_def]
  \\ simp[Once hello_machine_config_def, ag32_machine_config_def]
  \\ qx_gen_tac`k0`
  \\ strip_tac
  \\ conj_tac
  >- (
    qmatch_goalsub_abbrev_tac`_ ∧ encoded_bytes_in_mem _ pc m md ∧ _ ⇒ _`
    \\ strip_tac
    \\ qexists_tac`0`
    \\ simp[]
    \\ simp[ag32_ffi_rel_def, FUN_EQ_THM]
    \\ qmatch_goalsub_abbrev_tac`ms1.io_events`
    \\ `((Next ms1).io_events = ms1.io_events)` by (
      irule ag32_io_events_unchanged
      \\ simp[Abbr`ms1`]
      \\ `aligned 2 pc` by rfs[ag32_targetTheory.ag32_target_def, ag32_targetTheory.ag32_ok_def, EVAL``(hello_machine_config).target.state_ok``]
      \\ qmatch_goalsub_abbrev_tac`m (pc' + _)`
      \\ `pc' = pc`
      by (
        simp[Abbr`pc'`]
        \\ pop_assum mp_tac
        \\ simp[alignmentTheory.aligned_extract]
        \\ blastLib.BBLAST_TAC )
      \\ qpat_x_assum`Abbrev(pc' = _)`kall_tac
      \\ pop_assum SUBST_ALL_TAC
      \\ fs[targetSemTheory.encoded_bytes_in_mem_def]
      \\ fs[EVAL``(hello_machine_config).target.config.code_alignment``]
      \\ fs[EVAL``(hello_machine_config).target.config.encode``]
      \\ `4 ≤ LENGTH (DROP (4 * k) (ag32_enc i))` by (
        qspec_then`i`mp_tac(Q.GEN`istr`ag32_enc_lengths)
        \\ simp[]
        \\ strip_tac \\ fs[]
        \\ Cases_on`k` \\ fs[]
        \\ Cases_on`n` \\ fs[]
        \\ Cases_on`n'` \\ fs[]
        \\ Cases_on`n` \\ fs[] )
      \\ `∀j. j < 4 ⇒ (m (pc + n2w j) = EL j (DROP (4 * k) (ag32_enc i)))`
      by (
        qmatch_asmsub_abbrev_tac`bytes_in_memory pc bs`
        \\ rw[]
        \\ Q.ISPECL_THEN[`TAKE j bs`,`DROP j bs`,`pc`]mp_tac asmPropsTheory.bytes_in_memory_APPEND
        \\ simp[]
        \\ disch_then(drule o #1 o EQ_IMP_RULE o SPEC_ALL)
        \\ simp[]
        \\ Cases_on`DROP j bs` \\ fs[DROP_NIL]
        \\ simp[asmSemTheory.bytes_in_memory_def]
        \\ rw[]
        \\ `j < LENGTH bs` by fs[]
        \\ imp_res_tac DROP_EL_CONS
        \\ rfs[] )
      \\ simp[]
      \\ pop_assum(qspec_then`0`mp_tac) \\ simp[]
      \\ disch_then kall_tac
      \\ drule ag32_enc_not_Interrupt
      \\ simp[] )
    \\ rw[]
    \\ qmatch_goalsub_abbrev_tac`A ∧ B ∧ _ ⇔ _`
    \\ ntac 2 (pop_assum mp_tac)
    \\ Cases_on`A ∧ B` \\ fs[]
    \\ rw[markerTheory.Abbrev_def]
    \\ Cases_on`ag32_fs_ok (SND x.ffi_state)` \\ fs[]
    \\ fs[ag32_fs_ok_def]
    \\ first_assum(qspec_then`0`mp_tac)
    \\ last_assum(qspec_then`0`mp_tac)
    \\ simp_tac(srw_ss())[IS_SOME_EXISTS, EXISTS_PROD, PULL_EXISTS]
    \\ rw[ag32_stdin_implemented_def]
    \\ qmatch_goalsub_rename_tac`fnm = IOStream _`
    \\ Cases_on`fnm = IOStream (strlit"stdin")` \\ simp[]
    \\ Cases_on`ALOOKUP (SND x.ffi_state).files (IOStream(strlit"stdin"))` \\ simp[]
    \\ qmatch_goalsub_rename_tac`off ≤ LENGTH input`
    \\ Cases_on`off ≤ LENGTH input ∧ LENGTH input ≤ stdin_size` \\ fs[] \\ rveq
    \\ `∀i. i < 8 + LENGTH cnt ⇒ ((Next ms1).MEM (n2w (stdin_offset + i)) = m (n2w (stdin_offset + i)))`
    by (
      rw[]
      \\ first_x_assum irule
      \\ rw[Abbr`md`]
      \\ EVAL_TAC
      \\ simp[LENGTH_code, LENGTH_data, ffi_names, word_lo_n2w, word_ls_n2w]
      \\ fs[EVAL``stdin_size``] )
    \\ qspecl_then[`(Next ms1).MEM`,`m`,`n2w stdin_offset`]mp_tac(Q.GENL[`m1`,`m2`,`pc`]get_mem_word_change_mem)
    \\ impl_tac
    >- (
      rw[word_add_n2w]
      \\ first_x_assum (qspec_then`k`mp_tac)
      \\ simp[] )
    \\ rw[]
    \\ qspecl_then[`(Next ms1).MEM`,`m`,`n2w (stdin_offset + 4)`]mp_tac(Q.GENL[`m1`,`m2`,`pc`]get_mem_word_change_mem)
    \\ impl_tac
    >- (
      rw[word_add_n2w]
      \\ first_x_assum (qspec_then`k+4`mp_tac)
      \\ simp[] )
    \\ rw[]
    \\ rewrite_tac[GSYM CONJ_ASSOC]
    \\ AP_TERM_TAC
    \\ AP_TERM_TAC
    \\ AP_TERM_TAC
    \\ qmatch_goalsub_abbrev_tac`A ∧ _ ⇔ A' ∧ _`
    \\ `A = A'`
    by (
      simp[Abbr`A`,Abbr`A'`]
      \\ EQ_TAC \\ strip_tac
      \\ irule asmPropsTheory.bytes_in_memory_change_mem
      \\ goal_assum(first_assum o mp_then Any mp_tac)
      \\ rw[word_add_n2w]
      \\ first_x_assum(qspec_then`n + 8`mp_tac)
      \\ rw[])
    \\ simp[]
    \\ AP_TERM_TAC
    \\ ntac 3 (pop_assum kall_tac)
    \\ rw[ag32_cline_implemented_def]
    \\ qmatch_goalsub_abbrev_tac`ll ≤ _`
    \\ Cases_on`ll ≤ cline_size` \\ fs[]
    \\ qmatch_goalsub_abbrev_tac`cc ≠ []`
    \\ Cases_on`EVERY validArg cc ∧ cc ≠ []` \\ full_simp_tac std_ss []
    \\ qmatch_goalsub_abbrev_tac`bytes_in_memory a lc`
    \\ `∀i. i < 4 + LENGTH lc ⇒ ((Next ms1).MEM (n2w (startup_code_size + i)) = m (n2w (startup_code_size + i)))`
    by (
      rw[]
      \\ first_x_assum irule
      \\ rw[Abbr`md`]
      \\ EVAL_TAC
      \\ simp[LENGTH_code, LENGTH_data, ffi_names, word_lo_n2w, word_ls_n2w]
      \\ fs[EVAL``cline_size``,Abbr`lc`,LENGTH_FLAT,MAP_MAP_o,o_DEF,ADD1,SUM_MAP_PLUS,
            Q.ISPEC`λx. 1n`SUM_MAP_K |> SIMP_RULE(srw_ss())[], Abbr`ll`])
    \\ qspecl_then[`(Next ms1).MEM`,`m`,`n2w startup_code_size`]mp_tac(Q.GENL[`m1`,`m2`,`pc`]get_mem_word_change_mem)
    \\ impl_tac
    >- (
      rw[word_add_n2w]
      \\ first_x_assum (qspec_then`k`mp_tac)
      \\ simp[] )
    \\ rw[]
    \\ AP_TERM_TAC
    \\ EQ_TAC
    \\ strip_tac
    \\ irule asmPropsTheory.bytes_in_memory_change_mem
    \\ goal_assum(first_assum o mp_then Any mp_tac)
    \\ rw[word_add_n2w]
    \\ first_x_assum(qspec_then`n+4`mp_tac)
    \\ rw[Abbr`a`,word_add_n2w])
  \\ conj_tac
  >- (
    strip_tac
    \\ qexists_tac`1`
    \\ simp[ag32_ccache_interfer_def]
    \\ conj_asm1_tac
    >- (
      simp[ag32Theory.Next_def]
      \\ qmatch_goalsub_abbrev_tac`pc' + 2w`
      \\ qmatch_asmsub_abbrev_tac`_.PC = pc`
      \\ `aligned 2 pc`
      by (
        simp[Abbr`pc`, hello_machine_config_ccache_pc]
        \\ EVAL_TAC )
      \\ `pc = pc'`
      by (
        pop_assum mp_tac
        \\ unabbrev_all_tac
        \\ simp[alignmentTheory.aligned_extract]
        \\ blastLib.BBLAST_TAC )
      \\ qpat_x_assum`Abbrev(pc' = _)` kall_tac
      \\ pop_assum (SUBST_ALL_TAC o SYM)
      \\ first_assum(qspec_then`pc`mp_tac)
      \\ impl_tac >- ( simp[Abbr`pc`] \\ EVAL_TAC \\ simp[ffi_names, LENGTH_code, LENGTH_data])
      \\ first_assum(qspec_then`pc + 1w`mp_tac)
      \\ impl_tac >- ( simp[Abbr`pc`] \\ EVAL_TAC \\ simp[ffi_names, LENGTH_code, LENGTH_data])
      \\ first_assum(qspec_then`pc + 2w`mp_tac)
      \\ impl_tac >- ( simp[Abbr`pc`] \\ EVAL_TAC \\ simp[ffi_names, LENGTH_code, LENGTH_data])
      \\ first_assum(qspec_then`pc + 3w`mp_tac)
      \\ impl_tac >- ( simp[Abbr`pc`] \\ EVAL_TAC \\ simp[ffi_names, LENGTH_code, LENGTH_data])
      \\ simp[]
      \\ ntac 4 (disch_then kall_tac)
      \\ mp_tac hello_startup_clock_def
      \\ simp[]
      \\ disch_then drule
      \\ disch_then drule
      \\ disch_then drule
      \\ strip_tac
      \\ first_assum(qspec_then`pc`mp_tac)
      \\ impl_tac >- ( simp[Abbr`pc`] \\ EVAL_TAC \\ simp[ffi_names,LENGTH_code,LENGTH_data])
      \\ first_assum(qspec_then`pc + 1w`mp_tac)
      \\ impl_tac >- ( simp[Abbr`pc`] \\ EVAL_TAC \\ simp[ffi_names,LENGTH_code,LENGTH_data])
      \\ first_assum(qspec_then`pc + 2w`mp_tac)
      \\ impl_tac >- ( simp[Abbr`pc`] \\ EVAL_TAC \\ simp[ffi_names,LENGTH_code,LENGTH_data])
      \\ first_assum(qspec_then`pc + 3w`mp_tac)
      \\ impl_tac >- ( simp[Abbr`pc`] \\ EVAL_TAC \\ simp[ffi_names,LENGTH_code,LENGTH_data])
      \\ simp[]
      \\ ntac 4 (disch_then kall_tac)
      \\ fs[is_ag32_init_state_def]
      \\ simp[GSYM get_mem_word_def]
      \\ DEP_REWRITE_TAC[hello_init_memory_ccache]
      \\ conj_tac
      >- ( simp[Abbr`pc`,LENGTH_data] \\ EVAL_TAC )
      \\ simp[ag32_targetProofTheory.Decode_Encode]
      \\ simp[ag32Theory.Run_def]
      \\ simp[ag32Theory.dfn'Jump_def]
      \\ simp[ag32Theory.ALU_def]
      \\ simp[ag32Theory.ri2word_def]
      \\ rpt(AP_TERM_TAC ORELSE AP_THM_TAC)
      \\ simp[Abbr`pc`, hello_machine_config_ccache_pc,ffi_names]
      \\ EVAL_TAC)
    \\ pop_assum(SUBST_ALL_TAC o SYM)
    \\ conj_tac >- simp[ag32_ffi_rel_def,FUN_EQ_THM]
    \\ simp[] )
  \\ rpt gen_tac
  \\ strip_tac
  \\ fs[find_index_def] \\ rveq
  \\ simp[ffi_names]
  \\ fs[EVAL``(hello_machine_config).ffi_names``, ffi_names]
  \\ fs[ffiTheory.call_FFI_def,CaseEq"oracle_result",CaseEq"bool"]
  \\ rveq \\ rfs[basis_ffiTheory.basis_ffi_def]
  \\ `ffi.oracle = basis_ffi_oracle` by fs[ag32_ffi_rel_def] \\ fs[]
  \\ qhdtm_x_assum`basis_ffi_oracle`mp_tac
  \\ simp[Once basis_ffiTheory.basis_ffi_oracle_def]
  \\ pairarg_tac \\ rw[CaseEq"option",CaseEq"ffi_result"]
  \\ qmatch_goalsub_abbrev_tac`_ = FUNPOW Next _ ms1`
  \\ drule (GEN_ALL ag32_ffi_interfer_write)
  \\ fs[hello_machine_config_def]
  \\ disch_then drule
  \\ fs[GSYM hello_machine_config_def]
  \\ simp[ffiTheory.call_FFI_def, Once basis_ffiTheory.basis_ffi_oracle_def]
  \\ simp[ffi_names, INDEX_OF_def, INDEX_FIND_def]
  \\ reverse impl_tac
  THEN1
   (strip_tac
    \\ asm_exists_tac
    \\ simp[hello_machine_config_def,ag32_machine_config_def])
  \\ conj_tac
  >- (
    fs[targetSemTheory.read_ffi_bytearrays_def,
       targetSemTheory.read_ffi_bytearray_def,
       EVAL``(hello_machine_config).target.get_reg``,
       EVAL``(hello_machine_config).ptr2_reg``,
       EVAL``(hello_machine_config).len2_reg``]
    \\ drule (SIMP_RULE(srw_ss())[PULL_EXISTS, IS_SOME_EXISTS]read_bytearray_no_wrap)
    \\ simp[]
    \\ Cases_on`ms1.R 4w` \\ fs[]
    \\ imp_res_tac read_bytearray_LENGTH \\ fs[]
    \\ strip_tac
    \\ first_x_assum irule
    \\ Cases_on`ms1.R 3w` \\ fs[]
    \\ EVAL_TAC
    \\ simp[ffi_names, LENGTH_code, LENGTH_data]
    \\ qpat_x_assum`_ = ms1.PC`(assume_tac o SYM)
    \\ simp[]
    \\ Cases
    \\ simp[word_ls_n2w, word_lo_n2w] )
  \\ conj_tac >- EVAL_TAC
  \\ conj_tac >- ( simp[LENGTH_data, LENGTH_code] \\ EVAL_TAC )
  \\ conj_tac >- ( EVAL_TAC \\ simp[])
  \\ conj_tac >- (
    rw[]
    \\ first_assum(mp_then Any mp_tac (GEN_ALL get_mem_word_get_byte))
    \\ disch_then(qspec_then`ffi_jumps_offset DIV 4`mp_tac)
    \\ simp[LEFT_ADD_DISTRIB]
    \\ mp_tac(EVAL``4 * (ffi_jumps_offset DIV 4) = ffi_jumps_offset``)
    \\ simp[] \\ disch_then kall_tac
    \\ disch_then match_mp_tac
    \\ qexists_tac`DROP (ffi_jumps_offset DIV 4 + LENGTH (ag32_ffi_jumps (THE config.ffi_names)))
                        (hello_init_memory_words cl inp)`
    \\ qexists_tac`TAKE (ffi_jumps_offset DIV 4) (hello_init_memory_words cl inp)`
    \\ simp[ffi_names]
    \\ reverse conj_tac
    >- (
      simp[LENGTH_TAKE_EQ]
      \\ reverse conj_tac
      >- (
        pop_assum mp_tac
        \\ EVAL_TAC
        \\ fs[])
      \\ rw[]
      \\ pop_assum mp_tac
      \\ simp[]
      \\ CONV_TAC(LAND_CONV EVAL)
      \\ simp[LENGTH_hello_init_memory_words] )
    \\ simp[LENGTH_TAKE_EQ]
    \\ reverse IF_CASES_TAC
    >- (
      `F` suffices_by rw[]
      \\ pop_assum mp_tac
      \\ simp[LENGTH_hello_init_memory_words]
      \\ EVAL_TAC )
    \\ rw[]
    \\ qmatch_goalsub_abbrev_tac`EL _ mw`
    \\ `mw = hello_init_memory_words cl inp`
    by (
      simp[Abbr`mw`]
      \\ match_mp_tac TAKE_DROP_SUBLIST
      \\ simp[]
      \\ reverse conj_tac
      >- (
        simp[LENGTH_hello_init_memory_words]
        \\ EVAL_TAC )
      \\ simp[IS_PREFIX_APPEND]
      \\ simp[hello_init_memory_words_eq]
      \\ simp[ffi_names]
      \\ qmatch_goalsub_abbrev_tac`l1 ++ ag32_ffi_jumps _ ++ _ ++ _`
      \\ `ffi_jumps_offset DIV 4 = LENGTH l1`
      by (
        simp[Abbr`l1`, LENGTH_ag32_ffi_code, heap_size_def,
             output_buffer_size_def, LENGTH_hello_startup_code,
             startup_code_size_def,LENGTH_words_of_bytes_hello_startup_code]
        \\ CONV_TAC(LAND_CONV EVAL)
        \\ simp[LENGTH_words_of_bytes, bitstringTheory.length_pad_right, LENGTH_code,
                bytes_in_word_def, LENGTH_FLAT, MAP_MAP_o, o_DEF, ADD1, SUM_MAP_PLUS,
                Q.ISPEC`λx. 1n`SUM_MAP_K |> SIMP_RULE(srw_ss())[]]
        \\ qmatch_goalsub_abbrev_tac`sz DIV 4`
        \\ `sz = stdin_size` by (rw[Abbr`sz`])
        \\ qpat_x_assum`Abbrev(sz = _)`kall_tac
        \\ qmatch_goalsub_abbrev_tac`_ + (cz DIV 4 + _)`
        \\ `cz = cline_size` by (rw[Abbr`cz`])
        \\ qpat_x_assum`Abbrev(cz = _)`kall_tac
        \\ rveq
        \\ rw[stdin_size_def, cline_size_def])
      \\ rewrite_tac[GSYM APPEND_ASSOC]
      \\ asm_rewrite_tac[DROP_LENGTH_APPEND]
      \\ simp[])
    \\ qpat_x_assum`Abbrev(mw = _)`kall_tac
    \\ rw[]
    \\ simp[GSYM(SIMP_RULE(srw_ss())[]hello_init_memory_eq)]
    \\ mp_tac hello_startup_clock_def
    \\ simp[]
    \\ rpt(disch_then drule)
    \\ rw[]
    \\ fs[is_ag32_init_state_def]
    \\ rfs[]
    \\ `ms1.MEM x = ms.MEM x`
    by (
      first_x_assum irule
      \\ simp[hello_machine_config_def, ag32_machine_config_def]
      \\ conj_tac
      >- (
        EVAL_TAC
        \\ fs[EVAL``ffi_jumps_offset``, EVAL``ag32_ffi_jumps [_]``]
        \\ Cases_on`x` \\ fs[ word_add_n2w]
        \\ fs[word_ls_n2w, word_lo_n2w] \\ rfs[] )
      \\ simp[ffi_names, LENGTH_code, LENGTH_data]
      \\ qpat_x_assum`_ = ms1.PC`(assume_tac o SYM)
      \\ EVAL_TAC \\ simp[]
      \\ Cases_on`x` \\ fs[word_add_n2w]
      \\ fs[word_ls_n2w, word_lo_n2w] \\ rfs[]
      \\ fs[EVAL``ffi_jumps_offset``, EVAL``ag32_ffi_jumps [_]``]
      \\ rfs[])
    \\ rw[]
    \\ first_x_assum irule
    \\ EVAL_TAC
    \\ fs[EVAL``ffi_jumps_offset``, EVAL``ag32_ffi_jumps [_]``]
    \\ Cases_on`x` \\ Cases_on`ms0.PC` \\ fs[word_add_n2w]
    \\ fs[word_ls_n2w, word_lo_n2w] \\ rfs[])
  \\ rw[]
  \\ qmatch_goalsub_abbrev_tac`4 * k + off`
  \\ qspecl_then[`off DIV 4`,`ms1.MEM`,`MAP Encode ag32_ffi_write_code`]mp_tac
      (GEN_ALL get_mem_word_get_byte)
  \\ simp[EL_MAP,LEFT_ADD_DISTRIB]
  \\ `4 * (off DIV 4) = off` by (simp[Abbr`off`] \\ EVAL_TAC)
  \\ simp[]
  \\ disch_then match_mp_tac
  \\ pop_assum kall_tac
  \\ qexists_tac`DROP (off DIV 4 + LENGTH ag32_ffi_write_code) (hello_init_memory_words cl inp)`
  \\ qexists_tac`TAKE (off DIV 4) (hello_init_memory_words cl inp)`
  \\ reverse conj_tac
  >- (
    simp[LENGTH_TAKE_EQ, LENGTH_hello_init_memory_words]
    \\ simp[Abbr`off`]
    \\ pop_assum mp_tac
    \\ EVAL_TAC
    \\ fs[memory_size_def] )
  \\ simp[LENGTH_TAKE_EQ, LENGTH_hello_init_memory_words]
  \\ pop_assum mp_tac
  \\ CONV_TAC(LAND_CONV EVAL)
  \\ strip_tac \\ simp[Abbr`off`]
  \\ rw[]
  \\ qmatch_goalsub_abbrev_tac`EL _ mw`
  \\ `mw = hello_init_memory_words cl inp`
  by (
    simp[Abbr`mw`]
    \\ match_mp_tac TAKE_DROP_SUBLIST
    \\ simp[]
    \\ reverse conj_tac
    >- (
      simp[LENGTH_hello_init_memory_words]
      \\ EVAL_TAC )
    \\ simp[IS_PREFIX_APPEND]
    \\ simp[hello_init_memory_words_eq]
    \\ simp[ffi_names]
    \\ simp[ag32_ffi_code_def]
    \\ rewrite_tac[GSYM APPEND_ASSOC]
    \\ qmatch_goalsub_abbrev_tac`MAP Encode ag32_ffi_write_code ++ l2`
    \\ simp[]
    \\ qmatch_goalsub_abbrev_tac`l1 ++ MAP Encode ag32_ffi_write_code ++ l2`
    \\ qmatch_goalsub_abbrev_tac`DROP n`
    \\ `n = LENGTH l1`
    by (
      simp[Abbr`n`, Abbr`l1`, LENGTH_ag32_ffi_code, heap_size_def,
           output_buffer_size_def, LENGTH_hello_startup_code,
           startup_code_size_def,LENGTH_words_of_bytes_hello_startup_code]
      \\ CONV_TAC(PATH_CONV"rrr"EVAL)
      \\ simp[LENGTH_words_of_bytes, bitstringTheory.length_pad_right, LENGTH_code,
              bytes_in_word_def, LENGTH_FLAT, MAP_MAP_o, o_DEF, ADD1, SUM_MAP_PLUS,
              Q.ISPEC`λx. 1n`SUM_MAP_K |> SIMP_RULE(srw_ss())[]]
      \\ qmatch_goalsub_abbrev_tac`sz DIV 4`
      \\ `sz = stdin_size` by (rw[Abbr`sz`])
      \\ qpat_x_assum`Abbrev(sz = _)`kall_tac
      \\ qmatch_goalsub_abbrev_tac`_ + (cz DIV 4 + _)`
      \\ `cz = cline_size` by (rw[Abbr`cz`])
      \\ qpat_x_assum`Abbrev(cz = _)`kall_tac
      \\ rveq
      \\ rw[stdin_size_def, cline_size_def])
    \\ rewrite_tac[GSYM APPEND_ASSOC]
    \\ asm_rewrite_tac[DROP_LENGTH_APPEND]
    \\ simp[])
  \\ qpat_x_assum`Abbrev(mw = _)`kall_tac
  \\ rw[]
  \\ simp[GSYM(SIMP_RULE(srw_ss())[]hello_init_memory_eq)]
  \\ mp_tac hello_startup_clock_def
  \\ simp[]
  \\ rpt(disch_then drule)
  \\ rw[]
  \\ fs[is_ag32_init_state_def]
  \\ rfs[]
  \\ `ms1.MEM x = ms.MEM x`
  by (
    first_x_assum irule
    \\ simp[hello_machine_config_def, ag32_machine_config_def]
    \\ conj_tac
    >- (
      EVAL_TAC
      \\ fs[EVAL``LENGTH ag32_ffi_write_code``]
      \\ Cases_on`x` \\ fs[word_add_n2w]
      \\ fs[word_ls_n2w, word_lo_n2w] \\ rfs[] )
    \\ simp[ffi_names, LENGTH_code, LENGTH_data]
    \\ qpat_x_assum`_ = ms1.PC`(assume_tac o SYM)
    \\ EVAL_TAC \\ simp[]
    \\ Cases_on`x` \\ fs[word_add_n2w]
    \\ fs[word_ls_n2w, word_lo_n2w] \\ rfs[]
    \\ fs[EVAL``LENGTH ag32_ffi_write_code``]
    \\ rfs[])
  \\ rw[]
  \\ first_x_assum irule
  \\ EVAL_TAC
  \\ fs[EVAL``LENGTH ag32_ffi_write_code``]
  \\ Cases_on`x` \\ Cases_on`ms0.PC` \\ fs[word_add_n2w]
  \\ fs[word_ls_n2w, word_lo_n2w] \\ rfs[]);

val hello_extract_writes_stdout = Q.store_thm("hello_extract_writes_stdout",
  `wfcl cl ⇒
   (extract_writes 1 (MAP get_output_io_event (hello_io_events cl (stdin_fs inp))) =
    "Hello World!\n")`,
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
  \\ simp[Once stdin_fs_def, ALIST_FUPDKEY_def]
  \\ Cases \\ simp[] \\ strip_tac \\ rveq
  \\ pop_assum mp_tac
  \\ simp[TextIOProofTheory.up_stdo_def]
  \\ simp[fsFFITheory.fsupdate_def]
  \\ simp[stdin_fs_def]
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
  >- rw[]);

val hello_ag32_next = Q.store_thm("hello_ag32_next",
  `SUM (MAP strlen cl) + LENGTH cl ≤ cline_size ∧ wfcl cl ∧
   LENGTH inp ≤ stdin_size ∧
   is_ag32_init_state (hello_init_memory (cl,inp)) ms0
  ⇒
   ∃k1. ∀k. k1 ≤ k ⇒
     let ms = FUNPOW Next k ms0 in
     let outs = MAP (get_ag32_io_event) ms.io_events in
       (ms.PC = (hello_machine_config).halt_pc) ∧
       outs ≼ MAP get_output_io_event (hello_io_events cl (stdin_fs inp)) ∧
       ((ms.R (n2w (hello_machine_config).ptr_reg) = 0w) ⇒
        (outs = MAP get_output_io_event (hello_io_events cl (stdin_fs inp))))`,
  rw[]
  \\ mp_tac (GEN_ALL hello_machine_sem)
  \\ disch_then(first_assum o mp_then Any mp_tac) \\ fs[]
  \\ disch_then(qspec_then`stdin_fs inp`mp_tac)
  \\ simp[wfFS_stdin_fs, STD_streams_stdin_fs]
  \\ strip_tac
  \\ fs[extend_with_resource_limit_def]
  \\ qmatch_asmsub_abbrev_tac`machine_sem mc st ms`
  \\ `∃b. machine_sem mc st ms b` by metis_tac[targetPropsTheory.machine_sem_total]
  \\ fs[SUBSET_DEF, IN_DEF]
  \\ first_x_assum drule
  \\ disch_then(assume_tac o ONCE_REWRITE_RULE[GSYM markerTheory.Abbrev_def])
  \\ `∃x y. b = Terminate x y` by fs[markerTheory.Abbrev_def] \\ rveq
  \\ first_x_assum(mp_then Any mp_tac (GEN_ALL machine_sem_Terminate_FUNPOW_next))
  \\ mp_tac hello_interference_implemented
  \\ impl_tac >- ( fs[] \\ fs[markerTheory.Abbrev_def] )
  \\ strip_tac \\ rfs[]
  \\ disch_then drule
  \\ impl_tac >- (
    simp[ag32_ffi_rel_def,Abbr`st`]
    \\ conj_tac
    >- (
      EVAL_TAC
      \\ simp[Abbr`ms`]
      \\ mp_tac hello_startup_clock_def
      \\ simp[]
      \\ rpt(disch_then drule)
      \\ fs[is_ag32_init_state_def])
    \\ simp[basis_ffiTheory.basis_ffi_def]
    \\ simp[ag32_fs_ok_stdin_fs]
    \\ simp[Abbr`ms`]
    \\ mp_tac hello_startup_clock_def
    \\ simp[]
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
        \\ simp[Abbr`m`, hello_init_memory_eq]
        \\ simp[hello_init_memory_words_eq]
        \\ rewrite_tac[GSYM APPEND_ASSOC]
        \\ qmatch_goalsub_abbrev_tac`([0w] ++ lr)`
        \\ rewrite_tac[APPEND_ASSOC]
        \\ qmatch_goalsub_abbrev_tac`ll ++ [0w] ++ lr`
        \\ map_every qexists_tac[`ll`,`lr`]
        \\ simp[]
        \\ simp[Abbr`ll`, LENGTH_words_of_bytes_hello_startup_code, LENGTH_hello_startup_code]
        \\ simp[LENGTH_words_of_bytes, bitstringTheory.length_pad_right, LENGTH_code,
                bytes_in_word_def, LENGTH_FLAT, MAP_MAP_o, o_DEF, ADD1, SUM_MAP_PLUS,
                Q.ISPEC`λx. 1n`SUM_MAP_K |> SIMP_RULE(srw_ss())[]]
        \\ qmatch_goalsub_abbrev_tac`_ + (cz DIV 4 + _)`
        \\ `cz = cline_size` by (rw[Abbr`cz`])
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
        \\ simp[Abbr`m`, hello_init_memory_eq]
        \\ simp[hello_init_memory_words_eq]
        \\ rewrite_tac[GSYM APPEND_ASSOC]
        \\ qmatch_goalsub_abbrev_tac`([n2w(LENGTH inp)] ++ lr)`
        \\ rewrite_tac[APPEND_ASSOC]
        \\ qmatch_goalsub_abbrev_tac`ll ++ [n2w(LENGTH inp)] ++ lr`
        \\ map_every qexists_tac[`ll`,`lr`]
        \\ simp[]
        \\ simp[Abbr`ll`, LENGTH_words_of_bytes_hello_startup_code, LENGTH_hello_startup_code]
        \\ simp[LENGTH_words_of_bytes, bitstringTheory.length_pad_right, LENGTH_code,
                bytes_in_word_def, LENGTH_FLAT, MAP_MAP_o, o_DEF, ADD1, SUM_MAP_PLUS,
                Q.ISPEC`λx. 1n`SUM_MAP_K |> SIMP_RULE(srw_ss())[]]
        \\ qmatch_goalsub_abbrev_tac`_ + (cz DIV 4 + _)`
        \\ `cz = cline_size` by (rw[Abbr`cz`])
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
      \\ simp[hello_init_memory_eq]
      \\ irule asmPropsTheory.read_bytearray_IMP_bytes_in_memory
      \\ qexists_tac`SOME o m2`
      \\ qexists_tac`LENGTH inp`
      \\ simp[]
      \\ irule data_to_word_assignProofTheory.IMP_read_bytearray_GENLIST
      \\ simp[]
      \\ simp[hello_init_memory_eq]
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
      \\ rewrite_tac[hello_init_memory_words_eq]
      \\ rewrite_tac[GSYM APPEND_ASSOC] \\ DEP_ONCE_REWRITE_TAC[EL_APPEND2]
      \\ simp[LENGTH_words_of_bytes_hello_startup_code]
      \\ rewrite_tac[GSYM APPEND_ASSOC] \\ DEP_ONCE_REWRITE_TAC[EL_APPEND2]
      \\ simp[LENGTH_hello_startup_code, startup_code_size_def]
      \\ simp[EL_CONS, PRE_SUB1]
      \\ rewrite_tac[GSYM APPEND_ASSOC] \\ DEP_ONCE_REWRITE_TAC[EL_APPEND2]
      \\ simp[LENGTH_words_of_bytes, bitstringTheory.length_pad_right, LENGTH_FLAT, bytes_in_word_def, MAP_MAP_o, o_DEF, ADD1, SUM_MAP_PLUS]
      \\ simp[Q.ISPEC`λx. 1n`SUM_MAP_K |> SIMP_RULE(srw_ss())[]]
      \\ qmatch_goalsub_abbrev_tac`MIN 1 (cz MOD _)` \\ `cz = cline_size` by ( simp[Abbr`cz`] )
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
      \\ disch_then(qspec_then`[n2w(LENGTH cl)]`mp_tac) \\ simp[]
      \\ disch_then irule
      \\ simp[Abbr`m`, hello_init_memory_eq]
      \\ simp[hello_init_memory_words_eq]
      \\ rewrite_tac[GSYM APPEND_ASSOC]
      \\ qmatch_goalsub_abbrev_tac`([n2w (LENGTH cl)] ++ lr)`
      \\ rewrite_tac[APPEND_ASSOC]
      \\ qmatch_goalsub_abbrev_tac`ll ++ [n2w (LENGTH cl)] ++ lr`
      \\ map_every qexists_tac[`ll`,`lr`]
      \\ simp[]
      \\ simp[Abbr`ll`, LENGTH_words_of_bytes_hello_startup_code, LENGTH_hello_startup_code]
      \\ EVAL_TAC )
    \\ irule asmPropsTheory.bytes_in_memory_change_mem
    \\ qexists_tac`m2`
    \\ qmatch_goalsub_abbrev_tac`_ < lf`
    \\ `lf = LENGTH cl + SUM (MAP strlen cl)`
    by (
      simp[Abbr`lf`, LENGTH_FLAT, MAP_MAP_o, o_DEF, ADD1, SUM_MAP_PLUS]
      \\ simp[Q.ISPEC`λx. 1n`SUM_MAP_K |> SIMP_RULE(srw_ss())[]] )
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
    \\ qexists_tac`lf`
    \\ simp[]
    \\ irule data_to_word_assignProofTheory.IMP_read_bytearray_GENLIST
    \\ simp[]
    \\ simp[hello_init_memory_eq]
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
    \\ rewrite_tac[hello_init_memory_words_eq]
    \\ rewrite_tac[GSYM APPEND_ASSOC] \\ DEP_ONCE_REWRITE_TAC[EL_APPEND2]
    \\ simp[LENGTH_words_of_bytes_hello_startup_code]
    \\ rewrite_tac[GSYM APPEND_ASSOC] \\ DEP_ONCE_REWRITE_TAC[EL_APPEND2]
    \\ simp[LENGTH_hello_startup_code, startup_code_size_def]
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
      \\ qmatch_goalsub_abbrev_tac`_ < a + b`
      \\ `i DIV 4 < a` suffices_by simp[]
      \\ `a = 2048 DIV 4` by (
        rw[Abbr`a`]
        \\ fs[NOT_LESS]
        \\ `LENGTH cl + SUM (MAP strlen cl) = 2048` by simp[]
        \\ simp[] )
      \\ simp[DIV_LT_X])
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
    \\ simp[EL_APPEND1]
    \\ qpat_x_assum`_ ≤ 2048`mp_tac
    \\ EVAL_TAC \\ rw[])
  \\ strip_tac
  \\ mp_tac (GEN_ALL hello_halted)
  \\ simp[]
  \\ disch_then drule
  \\ disch_then drule
  \\ disch_then(qspec_then`FUNPOW Next k ms`mp_tac)
  \\ strip_tac
  \\ qexists_tac`k + hello_startup_clock ms0 inp cl`
  \\ qx_gen_tac`k2` \\ strip_tac
  \\ first_x_assum(qspec_then`k2-k-(hello_startup_clock ms0 inp cl)`mp_tac)
  \\ impl_tac
  >- (
    conj_tac
    >- (
      fs[Abbr`mc`]
      \\ fs[EVAL``(hello_machine_config).target.get_pc``]
      \\ fs[Abbr`ms`, FUNPOW_ADD]
      \\ fs[EVAL``(hello_machine_config).target.next``]
      \\ first_x_assum irule
      \\ fs[markerTheory.Abbrev_def] )
    \\ fs[Abbr`mc`]
    \\ fs[EVAL``(hello_machine_config).target.next``]
    \\ fs[Abbr`ms`, FUNPOW_ADD]
    \\ mp_tac hello_startup_clock_def
    \\ disch_then(qspec_then`ms0`mp_tac)
    \\ disch_then(first_assum o mp_then Any mp_tac)
    \\ impl_tac >- fs[]
    \\ strip_tac
    \\ fs[EVAL``(hello_machine_config).target.get_byte``]
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
    \\ fs[word_add_n2w, hello_machine_config_halt_pc]
    \\ simp[hello_machine_config_def, ag32_machine_config_def, ffi_names, ag32_prog_addresses_def, LENGTH_code, LENGTH_data]
    \\ EVAL_TAC
    \\ fs[word_lo_n2w, word_ls_n2w, memory_size_def] \\ rfs[])
  \\ fs[GSYM FUNPOW_ADD, Abbr`ms`]
  \\ strip_tac
  \\ fs[EVAL``(hello_machine_config).target.next``,Abbr`mc`,FUNPOW_ADD]
  \\ fs[EVAL``(hello_machine_config).target.get_reg``]
  \\ fs[EVAL``(hello_machine_config).target.get_pc``]
  \\ fs[EVAL``(hello_machine_config).ptr_reg``]
  \\ fs[ag32_ffi_rel_def]
  \\ conj_tac
  >- ( fs[IS_PREFIX_APPEND] \\ fs[markerTheory.Abbrev_def] )
  \\ strip_tac \\ fs[]
  \\ Cases_on`x` \\ fs[]
  \\ fs[markerTheory.Abbrev_def]);

val _ = export_theory();
