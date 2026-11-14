(*
  Part of the correctness proof for data_to_word: assign for MemOp
*)
Theory data_to_word_assign_memProof
Libs
  preamble helperLib blastLib
Ancestors
  wordSem
  backend_common (* for word_add_carry *)
  data_to_word_memoryProof data_to_word_gcProof dataSem
  wordSem[qualified] data_to_word int_bitwise dataProps
  wordProps While set_sep
  semanticsProps alignment backendProps word_bignum wordLang
  word_bignumProof gc_shared word_gcFunctions word_simpProof wordConvs
  data_to_word_assign_commonProof

val assign_thm_goal = concl assign_goal;

Theorem WordCopyAdd_thm:
  ∀count c copy_source copy_target (s:('a,'c,'ffi) wordSem$state) memory domain
    final_memory return_value ret_section ret_label.
    memcopy count copy_source copy_target memory domain = SOME final_memory ∧
    arch_width_bits c.arch_width = dimindex (:'a) ∧
    s.memory = memory ∧ s.mdomain = domain ∧
    (∃md. lookup WordCopyAdd_location s.code = SOME (5,WordCopyAdd_code c,md)) ∧
    count ≤ s.clock ∧ 2 * count < dimword (:'a) ∧
    get_var 0 s = SOME (Loc ret_section ret_label) ∧
    get_var 2 s = SOME (Word (n2w (2 * count))) ∧
    get_var 4 s = SOME (Word copy_source) ∧
    get_var 6 s = SOME (Word copy_target) ∧
    get_var 8 s = SOME return_value ⇒
    ∃maximum.
      evaluate (WordCopyAdd_code c,s) =
        (SOME (Result (Loc ret_section ret_label) [return_value]),
         s with <|clock := s.clock - count; memory := final_memory;
                  locals := LN; locals_size := SOME 0; stack_max := maximum|>) ∧
      backendProps$option_le maximum
        (OPTION_MAP2 MAX s.stack_max
          (OPTION_MAP2 $+ (stack_size s.stack)
            (lookup WordCopyAdd_location s.stack_size)))
Proof
  Induct
  >~ [`memcopy 0`] >- (
    rw [Once memcopy_def]
    >> simp [WordCopyAdd_code_def,Once wordSemTheory.evaluate_def,
             wordSemTheory.get_var_imm_def,wordSemTheory.word_cmp_def,
             integer_wordTheory.i2w_0]
    >> simp [Once wordSemTheory.evaluate_def,wordSemTheory.get_vars_def,
             wordSemTheory.flush_state_def]
    >> qexists_tac `s.stack_max`
    >> simp [wordSemTheory.state_component_equality,option_le_max_right])
  >~ [`memcopy (SUC remaining)`] >- (
    pop_assum (assume_named_tac "copy_ih")
    >> qx_genl_tac [`c`,`copy_source`,`copy_target`,`s`,`memory`,`copy_domain`,
                   `final_memory`,`return_value`,`ret_section`,`ret_label`]
    >> simp [Once memcopy_def]
    >> strip_tac
    >> gvs []
    >> `(n2w (2 * SUC remaining):'a word) ≠ 0w` by simp [n2w_11]
    >> once_rewrite_tac [WordCopyAdd_code_def]
    >> simp [Once wordSemTheory.evaluate_def,wordSemTheory.get_var_imm_def,
             wordSemTheory.word_cmp_def,integer_wordTheory.i2w_0]
    >> `s.clock ≠ 0` by decide_tac
    >> `(i2w (&arch_bytes c.arch_width):'a word) = bytes_in_word` by
      simp [integer_wordTheory.i2w_pos,arch_size,bytes_in_word_def]
    >> fs [list_Seq_def,wordSemTheory.evaluate_def,wordSemTheory.word_exp_def,
           wordSemTheory.get_var_def,wordSemTheory.set_var_def,lookup_insert,
           wordSemTheory.mem_load_def,wordSemTheory.mem_store_def,
           wordSemTheory.get_vars_def,wordSemTheory.the_words_def,
           wordSemTheory.word_op_def,wordSemTheory.find_code_def,
           wordSemTheory.bad_dest_args_def,wordSemTheory.add_ret_loc_def,
           wordSemTheory.call_env_def,wordSemTheory.dec_clock_def,fromList2_def,
           integer_wordTheory.i2w_pos,integer_wordTheory.i2w_0]
    >> fs [MULT_CLAUSES,GSYM word_add_n2w]
    >> qmatch_goalsub_abbrev_tac `(WordCopyAdd_code c,next_state)`
    >> LABEL_ASSUM "copy_ih" (qspecl_then
         [`c`,`copy_source + bytes_in_word`,`copy_target + bytes_in_word`,`next_state`,
          `(copy_target =+ s.memory copy_source) s.memory`,`s.mdomain`,`final_memory`,
          `return_value`,`ret_section`,`ret_label`] mp_tac)
    >> impl_tac
    >- (
      simp [Abbr `next_state`,wordSemTheory.get_var_def,lookup_insert]
      >> decide_tac)
    >> disch_then (qx_choose_then `maximum` strip_assume_tac)
    >> qexists_tac `maximum`
    >> fs [Abbr `next_state`,wordSemTheory.state_component_equality,
           option_le_max_right,ADD1])
QED

Theorem WordCopySub_thm:
  ∀count c copy_source copy_target (s:('a,'c,'ffi) wordSem$state) memory domain
    final_memory return_value ret_section ret_label.
    memcopy_bwd count copy_source copy_target memory domain = SOME final_memory ∧
    arch_width_bits c.arch_width = dimindex (:'a) ∧
    s.memory = memory ∧ s.mdomain = domain ∧
    (∃md. lookup WordCopySub_location s.code = SOME (5,WordCopySub_code c,md)) ∧
    count ≤ s.clock ∧ 2 * count < dimword (:'a) ∧
    get_var 0 s = SOME (Loc ret_section ret_label) ∧
    get_var 2 s = SOME (Word (n2w (2 * count))) ∧
    get_var 4 s = SOME (Word copy_source) ∧
    get_var 6 s = SOME (Word copy_target) ∧
    get_var 8 s = SOME return_value ⇒
    ∃maximum.
      evaluate (WordCopySub_code c,s) =
        (SOME (Result (Loc ret_section ret_label) [return_value]),
         s with <|clock := s.clock - count; memory := final_memory;
                  locals := LN; locals_size := SOME 0; stack_max := maximum|>) ∧
      backendProps$option_le maximum
        (OPTION_MAP2 MAX s.stack_max
          (OPTION_MAP2 $+ (stack_size s.stack)
            (lookup WordCopySub_location s.stack_size)))
Proof
  Induct
  >~ [`memcopy_bwd 0`] >- (
    rw [Once memcopy_bwd_def]
    >> simp [WordCopySub_code_def,Once wordSemTheory.evaluate_def,
             wordSemTheory.get_var_imm_def,wordSemTheory.word_cmp_def,
             integer_wordTheory.i2w_0]
    >> simp [Once wordSemTheory.evaluate_def,wordSemTheory.get_vars_def,
             wordSemTheory.flush_state_def]
    >> qexists_tac `s.stack_max`
    >> simp [wordSemTheory.state_component_equality,option_le_max_right])
  >~ [`memcopy_bwd (SUC remaining)`] >- (
    pop_assum (assume_named_tac "copy_ih")
    >> qx_genl_tac [`c`,`copy_source`,`copy_target`,`s`,`memory`,`copy_domain`,
                   `final_memory`,`return_value`,`ret_section`,`ret_label`]
    >> simp [Once memcopy_bwd_def]
    >> strip_tac
    >> gvs []
    >> `(n2w (2 * SUC remaining):'a word) ≠ 0w` by simp [n2w_11]
    >> once_rewrite_tac [WordCopySub_code_def]
    >> simp [Once wordSemTheory.evaluate_def,wordSemTheory.get_var_imm_def,
             wordSemTheory.word_cmp_def,integer_wordTheory.i2w_0]
    >> `s.clock ≠ 0` by decide_tac
    >> `(i2w (&arch_bytes c.arch_width):'a word) = bytes_in_word` by
      simp [integer_wordTheory.i2w_pos,arch_size,bytes_in_word_def]
    >> fs [list_Seq_def,wordSemTheory.evaluate_def,wordSemTheory.word_exp_def,
           wordSemTheory.get_var_def,wordSemTheory.set_var_def,lookup_insert,
           wordSemTheory.mem_load_def,wordSemTheory.mem_store_def,
           wordSemTheory.get_vars_def,wordSemTheory.the_words_def,
           wordSemTheory.word_op_def,wordSemTheory.find_code_def,
           wordSemTheory.bad_dest_args_def,wordSemTheory.add_ret_loc_def,
           wordSemTheory.call_env_def,wordSemTheory.dec_clock_def,fromList2_def,
           integer_wordTheory.i2w_pos,integer_wordTheory.i2w_0]
    >> fs [MULT_CLAUSES,GSYM word_add_n2w]
    >> qmatch_goalsub_abbrev_tac `(WordCopySub_code c,next_state)`
    >> LABEL_ASSUM "copy_ih" (qspecl_then
         [`c`,`copy_source - bytes_in_word`,`copy_target - bytes_in_word`,`next_state`,
          `(copy_target - bytes_in_word =+ s.memory (copy_source - bytes_in_word)) s.memory`,
          `s.mdomain`,`final_memory`,
          `return_value`,`ret_section`,`ret_label`] mp_tac)
    >> impl_tac
    >- simp [Abbr `next_state`,wordSemTheory.get_var_def,lookup_insert]
    >> disch_then (qx_choose_then `maximum` strip_assume_tac)
    >> qexists_tac `maximum`
    >> fs [Abbr `next_state`,wordSemTheory.state_component_equality,
           option_le_max_right,ADD1])
QED

Definition copy_loop_ticks_def:
  copy_loop_ticks (k:num) =
    if k < 6 then k + 1 else 1 + copy_loop_ticks (k-6)
End

Theorem copy_loop_ticks_small:
  k < 6 ⇒ copy_loop_ticks k = k + 1
Proof
  simp [Once copy_loop_ticks_def]
QED

Theorem copy_loop_ticks_large:
  6 ≤ k ⇒ copy_loop_ticks k = 1 + copy_loop_ticks (k-6)
Proof
  simp [Once copy_loop_ticks_def]
QED

Theorem WordCopyLoop_thm:
  ∀count c copy_source copy_target (s:('a,'c,'ffi) wordSem$state) memory domain
    final_memory return_value ret_section ret_label.
    memcopy6 count copy_source copy_target memory domain = SOME final_memory ∧
    arch_width_bits c.arch_width = dimindex (:'a) ∧
    s.memory = memory ∧ s.mdomain = domain ∧
    (∃md. lookup WordCopyLoop_location s.code = SOME (5,WordCopyLoop_code c,md)) ∧
    (∃md. lookup WordCopyAdd_location s.code = SOME (5,WordCopyAdd_code c,md)) ∧
    copy_loop_ticks count ≤ s.clock ∧ 2 * count < dimword (:'a) ∧
    get_var 0 s = SOME (Loc ret_section ret_label) ∧
    get_var 2 s = SOME (Word (n2w (2 * count))) ∧
    get_var 4 s = SOME (Word copy_source) ∧
    get_var 6 s = SOME (Word copy_target) ∧
    get_var 8 s = SOME return_value ⇒
    ∃maximum.
      evaluate (WordCopyLoop_code c,s) =
        (SOME (Result (Loc ret_section ret_label) [return_value]),
         s with <|clock := s.clock - copy_loop_ticks count; memory := final_memory;
                  locals := LN; locals_size := SOME 0; stack_max := maximum|>) ∧
      backendProps$option_le maximum
        (OPTION_MAP2 MAX s.stack_max
          (OPTION_MAP2 MAX
            (OPTION_MAP2 $+ (stack_size s.stack)
              (lookup WordCopyLoop_location s.stack_size))
            (OPTION_MAP2 $+ (stack_size s.stack)
              (lookup WordCopyAdd_location s.stack_size))))
Proof
  qx_gen_tac `copy_count`
  >> completeInduct_on `copy_count`
  >> pop_assum (assume_named_tac "copy_ih")
  >> Cases_on `copy_count < 6`
  >~ [`copy_count < 6 (* a *)`] >- (
    qx_genl_tac [`c`,`copy_source`,`copy_target`,`s`,`memory`,`copy_domain`,
                 `final_memory`,`return_value`,`ret_section`,`ret_label`]
    >> simp [Once memcopy6_def,Once copy_loop_ticks_def]
    >> strip_tac
    >> gvs []
    >> `12 < dimword (:'a)` by (
      Cases_on `c.arch_width`
      >> gvs [asmTheory.arch_width_bits_def,dimword_def])
    >> `s.clock ≠ 0` by decide_tac
    >> once_rewrite_tac [WordCopyLoop_code_def]
    >> fs [wordSemTheory.evaluate_def,wordSemTheory.get_var_imm_def,
           wordSemTheory.word_cmp_def,WORD_LO,integer_wordTheory.i2w_pos,
           wordSemTheory.get_vars_def,wordSemTheory.get_var_def,
           wordSemTheory.find_code_def,wordSemTheory.add_ret_loc_def,
           wordSemTheory.bad_dest_args_def,wordSemTheory.call_env_def,
           wordSemTheory.dec_clock_def,fromList2_def]
    >> qmatch_goalsub_abbrev_tac `(WordCopyAdd_code c,next_state)`
    >> qspecl_then
         [`copy_count`,`c`,`copy_source`,`copy_target`,`next_state`,`s.memory`,`s.mdomain`,
          `final_memory`,`return_value`,`ret_section`,`ret_label`]
         mp_tac WordCopyAdd_thm
    >> impl_tac
    >- (
      simp [Abbr `next_state`,wordSemTheory.get_var_def,lookup_insert]
      >> decide_tac)
    >> disch_then (qx_choose_then `maximum` strip_assume_tac)
    >> qexists_tac `maximum`
    >> simp [Once copy_loop_ticks_def]
    >> fs [Abbr `next_state`,wordSemTheory.state_component_equality,
           option_le_max_right])
  >~ [`¬(copy_count < 6) (* a *)`] >- (
    qx_genl_tac [`c`,`copy_source`,`copy_target`,`s`,`memory`,`copy_domain`,
                 `final_memory`,`return_value`,`ret_section`,`ret_label`]
    >> simp [Once memcopy6_def,Once copy_loop_ticks_def]
    >> strip_tac
    >> gvs []
    >> fs [EVAL ``GENLIST I 6``]
    >> `∀i. (i2w (&(i * arch_bytes c.arch_width)):'a word) =
               n2w i * bytes_in_word` by
      simp [integer_wordTheory.i2w_pos,arch_size,bytes_in_word_def,word_mul_n2w]
    >> `12 < dimword (:'a)` by decide_tac
    >> `s.clock ≠ 0` by decide_tac
    >> once_rewrite_tac [WordCopyLoop_code_def]
    >> simp [Once wordSemTheory.evaluate_def,wordSemTheory.get_var_imm_def,
             wordSemTheory.word_cmp_def,WORD_LO,integer_wordTheory.i2w_pos]
    >> `(i2w (&arch_bytes c.arch_width):'a word) = bytes_in_word` by
      simp [integer_wordTheory.i2w_pos,arch_size,bytes_in_word_def]
    >> fs [list_Seq_def,wordSemTheory.evaluate_def,wordSemTheory.word_exp_def,
           wordSemTheory.get_var_def,wordSemTheory.set_var_def,lookup_insert,
           wordSemTheory.mem_load_def,wordSemTheory.mem_store_def,
           wordSemTheory.get_vars_def,wordSemTheory.the_words_def,
           wordSemTheory.word_op_def,wordSemTheory.find_code_def,
           wordSemTheory.bad_dest_args_def,wordSemTheory.add_ret_loc_def,
           wordSemTheory.call_env_def,wordSemTheory.dec_clock_def,fromList2_def,
           integer_wordTheory.i2w_pos,integer_wordTheory.i2w_0]
    >> `2 * copy_count = 2 * (copy_count - 6) + 12` by decide_tac
    >> fs [GSYM word_add_n2w]
    >> qmatch_goalsub_abbrev_tac `(WordCopyLoop_code c,next_state)`
    >> LABEL_ASSUM "copy_ih" (qspec_then `copy_count - 6` mp_tac)
    >> impl_tac >- decide_tac
    >> disch_then (qspecl_then
         [`c`,`copy_source + 6w * bytes_in_word`,`copy_target + 6w * bytes_in_word`,
          `next_state`,`copy_word_chunk 6 copy_source copy_target s.memory`,`s.mdomain`,
          `final_memory`,`return_value`,`ret_section`,`ret_label`] mp_tac)
    >> impl_tac
    >- (
      fs [Abbr `next_state`,copy_word_chunk_def,EVAL ``GENLIST I 6``,FOLDL,
          wordSemTheory.get_var_def,lookup_insert]
      >> decide_tac)
    >> disch_then (qx_choose_then `maximum` strip_assume_tac)
    >> qexists_tac `maximum`
    >> simp [copy_loop_ticks_large]
    >> fs [Abbr `next_state`,wordSemTheory.state_component_equality,
           option_le_max_right])
QED

Theorem copy_byte_length:
  arch_width_bits aw = dimindex (:'a) ⇒
  (n2w (2 * k):'a word) ≪ (arch_shift aw - 1) = n2w k * bytes_in_word
Proof
  Cases_on `aw`
  >> rw [asmTheory.arch_width_bits_def,asmTheory.arch_shift_def]
  >> pop_assum (assume_tac o SYM)
  >> simp [bytes_in_word_def,word_mul_n2w,word_lsl_n2w]
QED

Definition word_copy_plan_def:
  word_copy_plan count (copy_source:'a word) copy_target memory domain =
    let size = n2w count * bytes_in_word in
      if count = 0 then (0,SOME memory)
      else if copy_target - copy_source <+ size then
        (count + 1,memcopy_bwd count (copy_source + size) (copy_target + size) memory domain)
      else if copy_source - copy_target <+ size then
        (count + 1,memcopy count copy_source copy_target memory domain)
      else (copy_loop_ticks count + 1,memcopy6 count copy_source copy_target memory domain)
End

Theorem WordCopy_thm:
  ∀count c copy_source copy_target (s:('a,'c,'ffi) wordSem$state) memory domain
    final_memory ticks return_value ret_section ret_label.
    word_copy_plan count copy_source copy_target memory domain = (ticks,SOME final_memory) ∧
    arch_width_bits c.arch_width = dimindex (:'a) ∧
    s.memory = memory ∧ s.mdomain = domain ∧
    (∃md. lookup WordCopyAdd_location s.code = SOME (5,WordCopyAdd_code c,md)) ∧
    (∃md. lookup WordCopySub_location s.code = SOME (5,WordCopySub_code c,md)) ∧
    (∃md. lookup WordCopyLoop_location s.code = SOME (5,WordCopyLoop_code c,md)) ∧
    ticks ≤ s.clock ∧ 2 * count < dimword (:'a) ∧
    get_var 0 s = SOME (Loc ret_section ret_label) ∧
    get_var 2 s = SOME (Word (n2w (2 * count))) ∧
    get_var 4 s = SOME (Word copy_source) ∧
    get_var 6 s = SOME (Word copy_target) ∧
    get_var 8 s = SOME return_value ⇒
    ∃maximum.
      evaluate (WordCopy_code c,s) =
        (SOME (Result (Loc ret_section ret_label) [return_value]),
         s with <|clock := s.clock - ticks; memory := final_memory;
                  locals := LN; locals_size := SOME 0; stack_max := maximum|>) ∧
      backendProps$option_le maximum
        (OPTION_MAP2 MAX s.stack_max
          (OPTION_MAP2 MAX
            (OPTION_MAP2 $+ (stack_size s.stack)
              (lookup WordCopySub_location s.stack_size))
            (OPTION_MAP2 MAX
              (OPTION_MAP2 $+ (stack_size s.stack)
                (lookup WordCopyLoop_location s.stack_size))
              (OPTION_MAP2 $+ (stack_size s.stack)
                (lookup WordCopyAdd_location s.stack_size)))))
Proof
  qx_genl_tac [`copy_count`,`c`,`copy_source`,`copy_target`,`s`,`memory`,`copy_domain`,
               `final_memory`,`ticks`,`return_value`,`ret_section`,`ret_label`]
  >> strip_tac
  >> Cases_on `copy_count = 0`
  >~ [`copy_count = 0 (* a *)`] >- (
    gvs [word_copy_plan_def]
    >> simp [WordCopy_code_def,Once wordSemTheory.evaluate_def,
             wordSemTheory.get_var_imm_def,wordSemTheory.word_cmp_def,
             integer_wordTheory.i2w_0]
    >> simp [Once wordSemTheory.evaluate_def,wordSemTheory.get_vars_def,
             wordSemTheory.flush_state_def]
    >> qexists_tac `s.stack_max`
    >> simp [wordSemTheory.state_component_equality,option_le_max_right])
  >> Cases_on `copy_target - copy_source <+ n2w copy_count * bytes_in_word`
  >~ [`copy_target - copy_source <+ n2w copy_count * bytes_in_word (* a *)`]
    >- (
      gvs [word_copy_plan_def]
      >> `s.clock ≠ 0` by decide_tac
      >> `(n2w (2 * copy_count):'a word) ≠ 0w` by simp [n2w_11]
      >> `arch_shift c.arch_width - 1 < dimindex (:'a) ∧
          arch_shift c.arch_width - 1 < dimword (:'a)` by (
        Cases_on `c.arch_width`
        >> gvs [asmTheory.arch_width_bits_def,asmTheory.arch_shift_def,dimword_def])
      >> drule copy_byte_length
      >> disch_then (qspec_then `copy_count` assume_tac)
      >> once_rewrite_tac [WordCopy_code_def]
      >> fs [list_Seq_def,wordSemTheory.evaluate_def,wordSemTheory.word_exp_def,
             wordSemTheory.get_var_def,wordSemTheory.set_var_def,lookup_insert,
             wordSemTheory.get_var_imm_def,wordSemTheory.word_cmp_def,
             wordSemTheory.word_sh_def,wordSemTheory.get_vars_def,
             wordSemTheory.the_words_def,wordSemTheory.word_op_def,
             wordSemTheory.find_code_def,wordSemTheory.bad_dest_args_def,
             wordSemTheory.add_ret_loc_def,wordSemTheory.call_env_def,
             wordSemTheory.dec_clock_def,fromList2_def,
             integer_wordTheory.i2w_pos,integer_wordTheory.i2w_0]
      >> qmatch_goalsub_abbrev_tac `(WordCopySub_code c,next_state)`
      >> qspecl_then
           [`copy_count`,`c`,`copy_source + n2w copy_count * bytes_in_word`,
            `copy_target + n2w copy_count * bytes_in_word`,`next_state`,`s.memory`,
            `s.mdomain`,`final_memory`,`return_value`,`ret_section`,`ret_label`]
           mp_tac WordCopySub_thm
      >> impl_tac
      >- (
        simp [Abbr `next_state`,wordSemTheory.get_var_def,lookup_insert]
        >> decide_tac)
      >> disch_then (qx_choose_then `maximum` strip_assume_tac)
      >> qexists_tac `maximum`
      >> fs [Abbr `next_state`,wordSemTheory.state_component_equality,
             wordSemTheory.bad_fun_return_def,option_le_max_right])
  >> Cases_on `copy_source - copy_target <+ n2w copy_count * bytes_in_word`
  >~ [`copy_source - copy_target <+ n2w copy_count * bytes_in_word (* a *)`]
    >- (
      gvs [word_copy_plan_def]
      >> `s.clock ≠ 0` by decide_tac
      >> `(n2w (2 * copy_count):'a word) ≠ 0w` by simp [n2w_11]
      >> `arch_shift c.arch_width - 1 < dimindex (:'a) ∧
          arch_shift c.arch_width - 1 < dimword (:'a)` by (
        Cases_on `c.arch_width`
        >> gvs [asmTheory.arch_width_bits_def,asmTheory.arch_shift_def,dimword_def])
      >> drule copy_byte_length
      >> disch_then (qspec_then `copy_count` assume_tac)
      >> once_rewrite_tac [WordCopy_code_def]
      >> fs [list_Seq_def,wordSemTheory.evaluate_def,wordSemTheory.word_exp_def,
             wordSemTheory.get_var_def,wordSemTheory.set_var_def,lookup_insert,
             wordSemTheory.get_var_imm_def,wordSemTheory.word_cmp_def,
             wordSemTheory.word_sh_def,wordSemTheory.get_vars_def,
             wordSemTheory.the_words_def,wordSemTheory.word_op_def,
             wordSemTheory.find_code_def,wordSemTheory.bad_dest_args_def,
             wordSemTheory.add_ret_loc_def,wordSemTheory.call_env_def,
             wordSemTheory.dec_clock_def,fromList2_def,
             integer_wordTheory.i2w_pos,integer_wordTheory.i2w_0]
      >> qmatch_goalsub_abbrev_tac `(WordCopyAdd_code c,next_state)`
      >> qspecl_then
           [`copy_count`,`c`,`copy_source`,
            `copy_target`,`next_state`,`s.memory`,
            `s.mdomain`,`final_memory`,`return_value`,`ret_section`,`ret_label`]
           mp_tac WordCopyAdd_thm
      >> impl_tac
      >- (
        simp [Abbr `next_state`,wordSemTheory.get_var_def,lookup_insert]
        >> decide_tac)
      >> disch_then (qx_choose_then `maximum` strip_assume_tac)
      >> qexists_tac `maximum`
      >> fs [Abbr `next_state`,wordSemTheory.state_component_equality,
             wordSemTheory.bad_fun_return_def,option_le_max_right])
  >> gvs [word_copy_plan_def]
  >> `s.clock ≠ 0` by decide_tac
  >> `(n2w (2 * copy_count):'a word) ≠ 0w` by simp [n2w_11]
  >> `arch_shift c.arch_width - 1 < dimindex (:'a) ∧
      arch_shift c.arch_width - 1 < dimword (:'a)` by (
    Cases_on `c.arch_width`
    >> gvs [asmTheory.arch_width_bits_def,asmTheory.arch_shift_def,dimword_def])
  >> drule copy_byte_length
  >> disch_then (qspec_then `copy_count` assume_tac)
  >> once_rewrite_tac [WordCopy_code_def]
  >> fs [list_Seq_def,wordSemTheory.evaluate_def,wordSemTheory.word_exp_def,
         wordSemTheory.get_var_def,wordSemTheory.set_var_def,lookup_insert,
         wordSemTheory.get_var_imm_def,wordSemTheory.word_cmp_def,
         wordSemTheory.word_sh_def,wordSemTheory.get_vars_def,
         wordSemTheory.the_words_def,wordSemTheory.word_op_def,
         wordSemTheory.find_code_def,wordSemTheory.bad_dest_args_def,
         wordSemTheory.add_ret_loc_def,wordSemTheory.call_env_def,
         wordSemTheory.dec_clock_def,fromList2_def,
         integer_wordTheory.i2w_pos,integer_wordTheory.i2w_0]
  >> qmatch_goalsub_abbrev_tac `(WordCopyLoop_code c,next_state)`
  >> qspecl_then
       [`copy_count`,`c`,`copy_source`,
        `copy_target`,`next_state`,`s.memory`,
        `s.mdomain`,`final_memory`,`return_value`,`ret_section`,`ret_label`]
       mp_tac WordCopyLoop_thm
  >> impl_tac
  >- (
    simp [Abbr `next_state`,wordSemTheory.get_var_def,lookup_insert]
    >> decide_tac)
  >> disch_then (qx_choose_then `maximum` strip_assume_tac)
  >> qexists_tac `maximum`
  >> fs [Abbr `next_state`,wordSemTheory.state_component_equality,
         wordSemTheory.bad_fun_return_def,option_le_max_right]
QED

Theorem word_copy_plan_store_list:
  ∀copy_count copy_source copy_target copy_memory copy_domain.
    0 < dimindex (:'a) DIV 8 ∧
    2 * (copy_count * (dimindex (:'a) DIV 8)) < dimword (:'a) ∧
    (∀i. i < copy_count ⇒
       copy_source + n2w i * bytes_in_word ∈ copy_domain ∧
       copy_target + n2w i * bytes_in_word ∈ copy_domain) ⇒
    SND (word_copy_plan copy_count (copy_source:'a word) copy_target
      copy_memory copy_domain) =
    store_list copy_target
      (GENLIST (λi. copy_memory (copy_source + n2w i * bytes_in_word)) copy_count)
      copy_memory copy_domain
Proof
  qx_genl_tac [`copy_count`,`copy_source`,`copy_target`,`copy_memory`,`copy_domain`]
  >> disch_then (CONJUNCTS_THEN2 assume_tac
       (CONJUNCTS_THEN2 assume_tac (assume_named_tac "copy_ranges_mapped")))
  >> `copy_count * (dimindex (:'a) DIV 8) < dimword (:'a)` by decide_tac
  >> Cases_on `copy_count = 0`
  >~ [`copy_count = 0 (* a *)`] >- simp [word_copy_plan_def,store_list_def]
  >> Cases_on `copy_target - copy_source <+ n2w copy_count * bytes_in_word`
  >~ [`copy_target - copy_source <+ n2w copy_count * bytes_in_word (* a *)`] >- (
    asm_simp_tac std_ss [word_copy_plan_def,LET_THM]
    >> irule memcopy_bwd_store_list
    >> rpt conj_tac
    >~ [`∀i. i < copy_count ⇒
           copy_source + n2w i * bytes_in_word ∈ copy_domain ∧
           copy_target + n2w i * bytes_in_word ∈ copy_domain (* g *)`]
      >- LABEL_ASSUM "copy_ranges_mapped" ACCEPT_TAC
    >~ [`∀i j. i < j ∧ j < copy_count ⇒
           copy_target + n2w j * bytes_in_word ≠
             copy_source + n2w i * bytes_in_word (* g *)`]
      >- (
        rpt gen_tac >> strip_tac
        >> irule copy_word_backward_safe
        >> asm_simp_tac std_ss []
        >> qexists_tac `copy_count`
        >> asm_simp_tac std_ss [])
    >> rpt gen_tac >> strip_tac
    >> drule_all copy_word_addresses_distinct
    >> asm_simp_tac std_ss [])
  >> Cases_on `copy_source - copy_target <+ n2w copy_count * bytes_in_word`
  >~ [`copy_source - copy_target <+ n2w copy_count * bytes_in_word (* a *)`] >- (
    asm_simp_tac std_ss [word_copy_plan_def,LET_THM]
    >> irule memcopy_store_list
    >> rpt conj_tac
    >~ [`∀i. i < copy_count ⇒
           copy_source + n2w i * bytes_in_word ∈ copy_domain (* g *)`]
    >- (
      qx_gen_tac `copy_index` >> strip_tac
      >> LABEL_ASSUM "copy_ranges_mapped" (qspec_then `copy_index` mp_tac)
      >> asm_simp_tac std_ss [])
    >> rpt gen_tac >> strip_tac
    >> irule copy_word_forward_safe
    >> asm_simp_tac std_ss []
    >> qexists_tac `copy_count`
    >> asm_simp_tac std_ss [])
  >> asm_simp_tac std_ss [word_copy_plan_def,LET_THM]
  >> irule memcopy6_store_list
  >> rpt conj_tac
  >~ [`∀i. i < copy_count ⇒
         copy_source + n2w i * bytes_in_word ∈ copy_domain ∧
         copy_target + n2w i * bytes_in_word ∈ copy_domain (* g *)`]
    >- LABEL_ASSUM "copy_ranges_mapped" ACCEPT_TAC
  >> rpt gen_tac >> strip_tac
  >> irule copy_word_ranges_disjoint
  >> asm_simp_tac std_ss []
  >> qexists_tac `copy_count`
  >> asm_simp_tac std_ss []
QED

Theorem copy_loop_ticks_bound:
  ∀copy_count. copy_loop_ticks copy_count ≤ copy_count + 1
Proof
  qx_gen_tac `copy_count`
  >> completeInduct_on `copy_count`
  >> pop_assum (assume_named_tac "copy_clock_ih")
  >> Cases_on `copy_count < 6`
  >~ [`copy_count < 6 (* a *)`] >- simp [copy_loop_ticks_small]
  >> `6 ≤ copy_count` by decide_tac
  >> `copy_count - 6 < copy_count` by decide_tac
  >> `copy_loop_ticks (copy_count - 6) ≤ copy_count - 6 + 1` by (
    LABEL_ASSUM "copy_clock_ih" (qspec_then `copy_count - 6` mp_tac)
    >> simp [])
  >> simp [copy_loop_ticks_large]
  >> decide_tac
QED

Theorem word_copy_plan_ticks_bound:
  ∀copy_count copy_source copy_target copy_memory copy_domain.
    FST (word_copy_plan copy_count copy_source copy_target copy_memory copy_domain) ≤
      copy_count + 2
Proof
  qx_genl_tac [`copy_count`,`copy_source`,`copy_target`,`copy_memory`,`copy_domain`]
  >> rw [word_copy_plan_def,LET_THM]
  >> mp_tac (Q.SPEC `copy_count` copy_loop_ticks_bound)
  >> decide_tac
QED

val _ = augment_srw_ss [rewrites [CONJUNCT2 data_to_wordTheory.arch_size]];

val _ = temp_delsimps ["NORMEQ_CONV"]
val _ = temp_delsimps ["lift_disj_eq", "lift_imp_disj"]
val _ = temp_delsimps ["DIV_NUMERAL_THM"]
val _ = temp_delsimps ["fromAList_def", "domain_union",
                       "domain_inter", "domain_difference",
                       "domain_map", "sptree.map_def", "sptree.lookup_rwts",
                       "sptree.insert_notEmpty", "sptree.isEmpty_union"]
val _ = diminish_srw_ss ["ABBREV"]

Theorem evaluate_Seq_step[local]:
  ∀code_first code_rest (t:('a,'c,'ffi) wordSem$state).
    evaluate (Seq code_first code_rest,t) =
    (λ(res,s1). if res = NONE then evaluate (code_rest,s1) else (res,s1))
      (evaluate (code_first,t))
Proof
  rpt gen_tac \\ simp_tac std_ss [Once wordSemTheory.evaluate_def,LET_THM]
QED

Theorem w2w_byte_eq[local]:
  good_dimindex (:'a) ⇒
  ((w2w (x:word8):'a word) = w2w y ⇔ x = y)
Proof
  Cases_on ‘x’ \\ Cases_on ‘y’
  \\ gvs [good_dimindex_def,w2w_n2w,n2w_11,dimword_def]
  \\ rw [bitTheory.BITS_ZEROL] \\ gvs []
QED

Theorem word_has_zero_byte_32[local]:
  ∀w:word32.
    (w - 0x01010101w) && ¬w && 0x80808080w ≠ 0w ⇔
    ∃i. i < 4 ∧ (w2w (w ⋙ (8 * i)):word8) = 0w
Proof
  gen_tac
  \\ simp [DECIDE “i < 4 ⇔ i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3”]
  \\ simp [RIGHT_AND_OVER_OR,EXISTS_OR_THM]
  \\ blastLib.BBLAST_TAC
  \\ tautLib.TAUT_TAC
QED

Theorem word_has_zero_byte_64[local]:
  ∀w:word64.
    (w - 0x0101010101010101w) && ¬w && 0x8080808080808080w ≠ 0w ⇔
    ∃i. i < 8 ∧ (w2w (w ⋙ (8 * i)):word8) = 0w
Proof
  gen_tac
  \\ simp [DECIDE “i < 8 ⇔ i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7”]
  \\ simp [RIGHT_AND_OVER_OR,EXISTS_OR_THM]
  \\ blastLib.BBLAST_TAC
  \\ tautLib.TAUT_TAC
QED

Theorem word_has_zero_byte[local]:
  good_dimindex (:'a) ⇒
  (((w:'a word) - word_of_byte 1w) && ¬w && word_of_byte 128w ≠ 0w ⇔
   ∃i. i < dimindex (:'a) DIV 8 ∧ (w2w (w ⋙ (8 * i)):word8) = 0w)
Proof
  strip_tac
  \\ Cases_on ‘dimindex (:'a) = 32’
  >- (
    qspec_then ‘w2w w:word32’ mp_tac word_has_zero_byte_32
    \\ Cases_on ‘w’
    \\ gvs [word_of_byte_def,word_sub_def,word_add_n2w,word_2comp_n2w,
            word_1comp_n2w,word_and_n2w,word_or_n2w,word_lsl_n2w,
            word_lsr_n2w,word_bits_n2w,w2w_n2w,w2n_n2w,n2w_11,dimword_def]
    \\ rewrite_tac [GSYM (w2n_n2w |> INST_TYPE [alpha |-> “:32”]
                         |> REWRITE_RULE [dimword_def,dimindex_32] |> numLib.REDUCE_RULE)]
    \\ rewrite_tac [GSYM (word_and_n2w |> INST_TYPE [alpha |-> “:32”]
                                       |> REWRITE_RULE [dimindex_32]),
                    GSYM (word_add_n2w |> INST_TYPE [alpha |-> “:32”])]
    \\ once_rewrite_tac [GSYM (n2w_mod |> INST_TYPE [alpha |-> “:32”])]
    \\ simp_tac arith_ss [dimword_def,dimindex_32]
    \\ simp [WORD_AND_ASSOC,WORD_AND_COMM]
  )
  \\ ‘dimindex (:'a) = 64’ by gvs [good_dimindex_def]
  \\ qspec_then ‘w2w w:word64’ mp_tac word_has_zero_byte_64
  \\ Cases_on ‘w’
  \\ gvs [word_of_byte_def,word_sub_def,word_add_n2w,word_2comp_n2w,
          word_1comp_n2w,word_and_n2w,word_or_n2w,word_lsl_n2w,
          word_lsr_n2w,word_bits_n2w,w2w_n2w,w2n_n2w,n2w_11,dimword_def]
  \\ rewrite_tac [GSYM (w2n_n2w |> INST_TYPE [alpha |-> “:64”]
                       |> REWRITE_RULE [dimword_def,dimindex_64] |> numLib.REDUCE_RULE)]
  \\ rewrite_tac [GSYM (word_and_n2w |> INST_TYPE [alpha |-> “:64”]
                                     |> REWRITE_RULE [dimindex_64]),
                  GSYM (word_add_n2w |> INST_TYPE [alpha |-> “:64”])]
  \\ once_rewrite_tac [GSYM (n2w_mod |> INST_TYPE [alpha |-> “:64”])]
  \\ simp_tac arith_ss [dimword_def,dimindex_64]
  \\ simp [WORD_AND_ASSOC,WORD_AND_COMM]
QED

Theorem get_byte_word_of_byte[local]:
  ∀(a:'a word) (b:word8) be.
    good_dimindex (:'a) ⇒ get_byte a (word_of_byte (w2w b)) be = b
Proof
  rw [good_dimindex_def]
  \\ ‘∃k. byte_index a be = 8 * k ∧ k < dimindex (:'a) DIV 8’ by (
    fs [byte_index_def] \\ rw [])
  \\ gvs [get_byte_def,word_of_byte_def,
          DECIDE “k < 4 ⇔ k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3”,
          DECIDE “k < 8 ⇔ k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨
                          k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7”]
  \\ srw_tac [wordsLib.WORD_BIT_EQ_ss] []
QED

Theorem word_has_zero_get_byte[local]:
  ∀(w:'a word) be.
    good_dimindex (:'a) ⇒
    ((w - word_of_byte 1w) && ¬w && word_of_byte 128w ≠ 0w ⇔
     ∃i. i < dimindex (:'a) DIV 8 ∧ get_byte (n2w i) w be = 0w)
Proof
  rpt gen_tac \\ strip_tac
  \\ simp [word_has_zero_byte]
  \\ fs [good_dimindex_def]
  \\ simp [DECIDE “i < 4 ⇔ i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3”,
           DECIDE “i < 8 ⇔ i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨
                           i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7”,
           RIGHT_AND_OVER_OR,EXISTS_OR_THM]
  \\ Cases_on ‘be’
  \\ simp [get_byte_def,byte_index_def,dimword_def,AC DISJ_COMM DISJ_ASSOC]
QED

Theorem get_byte_xor[local]:
  ∀(a:'a word) w v be.
    get_byte a (w ?? v) be = get_byte a w be ?? get_byte a v be
Proof
  simp [get_byte_def,GSYM LSR_BITWISE,GSYM WORD_w2w_OVER_BITWISE]
QED

Theorem word_eq_broadcast[local]:
  ∀(w:'a word) (b:word8) be.
    good_dimindex (:'a) ⇒
    (w = word_of_byte (w2w b) ⇔
     ∀i. i < dimindex (:'a) DIV 8 ⇒ get_byte (n2w i) w be = b)
Proof
  rpt gen_tac \\ strip_tac \\ eq_tac
  >- (rw [] \\ simp [get_byte_word_of_byte])
  \\ strip_tac
  \\ irule word_eq_of_get_byte
  \\ conj_tac
  >- (qexists_tac ‘be’ \\ simp [get_byte_word_of_byte])
  \\ gvs [good_dimindex_def,dividesTheory.divides_def]
QED

Theorem ScanByte_word_test[local]:
  ∀(w:'a word) (needle:word8) neq be.
    good_dimindex (:'a) ⇒
    let v = w ?? word_of_byte (w2w needle) in
      ((if neq then v ≠ 0w else
          (v - word_of_byte 1w) && ¬v && word_of_byte 128w ≠ 0w) ⇔
       ∃i. i < dimindex (:'a) DIV 8 ∧
           ((get_byte (n2w i) w be = needle) ⇔ ¬neq))
Proof
  rpt gen_tac \\ strip_tac \\ Cases_on ‘neq’
  >- (
    simp [LET_THM,addressTheory.WORD_EQ_XOR_ZERO]
    \\ qspecl_then [‘w’,‘needle’,‘be’] mp_tac word_eq_broadcast
    \\ simp [])
  \\ qspecl_then [‘w ?? word_of_byte (w2w needle)’,‘be’]
    mp_tac word_has_zero_get_byte
  \\ simp [LET_THM,get_byte_xor,get_byte_word_of_byte,
           addressTheory.WORD_EQ_XOR_ZERO]
  \\ simp [EQ_SYM_EQ]
QED

Theorem ScanByte_aligned_offset[local]:
  ∀(pointer:'a word) i.
    good_dimindex (:'a) ∧ byte_aligned pointer ∧ i < dimindex (:'a) DIV 8 ⇒
    byte_align (pointer + n2w i) = pointer
Proof
  rpt gen_tac \\ strip_tac
  \\ fs [byte_align_def,byte_aligned_def]
  \\ irule align_add_aligned \\ simp []
  \\ gvs [good_dimindex_def,dimword_def]
QED

Theorem ScanByte_load_word[local]:
  ∀m dm be (pointer:'a word) bs.
    good_dimindex (:'a) ∧ byte_aligned pointer ∧
    dimindex (:'a) DIV 8 ≤ LENGTH bs ∧
    (∀i. i < LENGTH bs ⇒
      mem_load_byte_aux m dm be (pointer + n2w i) = SOME (EL i bs)) ⇒
    ∃w. m pointer = Word w ∧ pointer ∈ dm ∧
        ∀i. i < dimindex (:'a) DIV 8 ⇒ get_byte (n2w i) w be = EL i bs
Proof
  rpt gen_tac \\ strip_tac
  \\ ‘0 < LENGTH bs’ by gvs [good_dimindex_def]
  \\ ‘mem_load_byte_aux m dm be pointer = SOME (EL 0 bs)’ by (
    qpat_x_assum ‘∀i. i < LENGTH bs ⇒ _’ (qspec_then ‘0’ mp_tac)
    \\ simp [])
  \\ ‘byte_align pointer = pointer’ by gvs [GSYM byte_align_aligned]
  \\ namedCases_on ‘m pointer’ ["raw","ret1 ret2"]
  \\ gvs [wordSemTheory.mem_load_byte_aux_def]
  \\ qx_gen_tac ‘i’ \\ strip_tac
  \\ ‘get_byte (pointer + n2w i) raw be = get_byte (n2w i) raw be’ by (
    irule get_byte_eq \\ simp [ScanByte_aligned_offset])
  \\ qpat_x_assum ‘∀i. i < LENGTH bs ⇒ _’ (qspec_then ‘i’ mp_tac)
  \\ simp [ScanByte_aligned_offset]
QED

Theorem ScanByte_constants[local]:
  ∀c. arch_width_bits c.arch_width = dimindex (:'a) ⇒
    arch_bytes c.arch_width = dimindex (:'a) DIV 8 ∧
    i2w (if arch_bytes c.arch_width = 4 then 0x01010101 else 0x0101010101010101) =
      (word_of_byte 1w:'a word) ∧
    i2w (128 * (if arch_bytes c.arch_width = 4 then 0x01010101 else 0x0101010101010101)) =
      (word_of_byte 128w:'a word)
Proof
  gen_tac \\ Cases_on ‘c.arch_width’
  \\ simp [asmTheory.arch_width_bits_def,asmTheory.arch_bytes_def]
  \\ disch_then (assume_tac o SYM)
  \\ simp [word_of_byte_def,integer_wordTheory.i2w_def,word_lsl_n2w,
           WORD_LITERAL_OR,dimword_def]
QED

Theorem cut_state_ScanByte[local]:
  ∀(t:('a,'c,'ffi) wordSem$state) ret needle addr count index.
  wordSem$get_vars [0;2;4;6;8] (t:('a,'c,'ffi) wordSem$state) =
    SOME [ret;needle;addr;count;index] ⇒
  cut_state (fromAList [(0,());(2,());(4,());(6,());(8,())],LN) t =
    SOME (t with locals :=
      fromAList [(0,ret);(2,needle);(4,addr);(6,count);(8,index)])
Proof
  qx_genl_tac [‘t’,‘ret’,‘needle’,‘pointer’,‘remaining’,‘result_index’]
  \\ strip_tac
  \\ gvs [wordSemTheory.get_vars_def,wordSemTheory.get_var_def,AllCaseEqs()]
  \\ ‘domain (fromAList [(0,());(2,());(4,());(6,());(8,())]) SUBSET
      domain t.locals’
  by (
    simp [domain_fromAList,SUBSET_DEF]
    \\ rw [domain_lookup] \\ simp [])
  \\ simp [wordSemTheory.cut_state_def,wordSemTheory.cut_env_def,
           wordSemTheory.cut_envs_def,wordSemTheory.cut_names_def]
  \\ simp [spt_eq_thm,wf_fromAList,lookup_inter_alt,domain_fromAList,
           lookup_fromAList]
  \\ gen_tac \\ rw [] \\ simp []
QED

Theorem cut_state_ScanByte_word[local]:
  ∀(t:('a,'c,'ffi) wordSem$state) ret needle addr count index broadcast.
    wordSem$get_vars [0;2;4;6;8;10] t =
      SOME [ret;needle;addr;count;index;broadcast] ⇒
    cut_state (insert 10 () (fromAList [(0,());(2,());(4,());(6,());(8,())]),LN) t =
      SOME (t with locals := fromAList
        [(0,ret);(2,needle);(4,addr);(6,count);(8,index);(10,broadcast)])
Proof
  qx_genl_tac [‘t’,‘ret’,‘needle’,‘pointer’,‘remaining’,‘result_index’,‘broadcast’]
  \\ strip_tac
  \\ gvs [wordSemTheory.get_vars_def,wordSemTheory.get_var_def,AllCaseEqs()]
  \\ ‘domain (insert 10 () (fromAList [(0,());(2,());(4,());(6,());(8,())])) SUBSET
      domain t.locals’
  by (
    simp [domain_insert,domain_fromAList,SUBSET_DEF]
    \\ rw [domain_lookup] \\ simp [])
  \\ simp [wordSemTheory.cut_state_def,wordSemTheory.cut_env_def,
           wordSemTheory.cut_envs_def,wordSemTheory.cut_names_def]
  \\ simp [spt_eq_thm,wf_fromAList,lookup_inter_alt,domain_fromAList,
           lookup_fromAList,domain_insert,lookup_insert,domain_lookup]
  \\ gen_tac \\ rw [] \\ simp [] \\ gvs []
QED

Theorem evaluate_ScanByte_tail[local]:
  ∀bs neq needle addr index (t:('a,'c,'ffi) wordSem$state) ret1 ret2.
    good_dimindex (:'a) ∧ LENGTH bs < dimword (:'a) ∧
    LENGTH bs < t.clock ∧
    (∀i. i < LENGTH bs ⇒
      mem_load_byte_aux t.memory t.mdomain t.be (addr + n2w i) =
      SOME (EL i bs)) ∧
    get_var 0 t = SOME (Loc ret1 ret2) ∧
    get_var 2 t = SOME (Word (w2w needle)) ∧
    get_var 4 t = SOME (Word addr) ∧
    get_var 6 t = SOME (Word (n2w (LENGTH bs))) ∧
    get_var 8 t = SOME (Word index) ⇒
    ∃ck.
      evaluate
        (Loop (fromAList [(0,());(2,());(4,());(6,());(8,())])
          (If Equal 6 (Imm 0) (Return 0 [8]) (ScanByte_step neq))
          (fromAList [(0,());(2,());(4,());(6,());(8,())]),t) =
      (SOME (Result (Loc ret1 ret2)
        [Word (index + 2w * n2w
          (LENGTH (FST (SPLITP (λw. (w = needle) ⇔ ¬neq) bs))))]),
       t with <| clock := ck; locals := LN; locals_size := SOME 0 |>)
Proof
  Induct
  >- (
    qx_genl_tac [‘neq’,‘needle’,‘pointer’,‘index’,‘t’,‘ret1’,‘ret2’]
    \\ strip_tac
    \\ ‘get_vars [0;2;4;6;8] t =
        SOME [Loc ret1 ret2; Word (w2w needle); Word pointer; Word 0w; Word index]’
      by gvs [wordSemTheory.get_vars_def]
    \\ drule cut_state_ScanByte \\ strip_tac
    \\ once_rewrite_tac [wordSemTheory.evaluate_def]
    \\ simp [eq_eval,lookup_fromAList,SPLITP,integer_wordTheory.i2w_def,
             wordSemTheory.flush_state_def]
    \\ qexists_tac ‘t.clock’ \\ simp [])
  \\ qx_genl_tac [‘head’,‘neq’,‘needle’,‘pointer’,‘index’,‘t’,‘ret1’,‘ret2’]
  \\ strip_tac
  \\ ‘mem_load_byte_aux t.memory t.mdomain t.be pointer = SOME head’ by (
    qpat_x_assum ‘∀i. i < LENGTH (head::bs) ⇒ _’ (qspec_then ‘0’ mp_tac)
    \\ simp [])
  \\ ‘(n2w (LENGTH (head::bs)):'a word) ≠ 0w’ by simp [n2w_11]
  \\ ‘((w2w head:'a word) = w2w needle) ⇔ head = needle’ by (
    irule w2w_byte_eq \\ asm_rewrite_tac [])
  \\ ‘get_vars [0;2;4;6;8] t =
      SOME [Loc ret1 ret2; Word (w2w needle); Word pointer;
            Word (n2w (LENGTH (head::bs))); Word index]’
    by simp [wordSemTheory.get_vars_def]
  \\ drule cut_state_ScanByte \\ strip_tac
  \\ fs [LENGTH]
  \\ once_rewrite_tac [wordSemTheory.evaluate_def]
  \\ Cases_on ‘neq’ \\ Cases_on ‘head = needle’
  \\ simp [ScanByte_step_def,list_Seq_def,eq_eval,lookup_fromAList,
           wordSemTheory.inst_def,integer_wordTheory.i2w_def,SPLITP,
           wordSemTheory.flush_state_def,wordSemTheory.state_component_equality]
  >- (
    rewrite_tac [GSYM (ScanByte_step_def |> SPEC T |> REWRITE_RULE [list_Seq_def]),
                 STOP_def]
    \\ qmatch_goalsub_abbrev_tac ‘evaluate (_,next_state)’
    \\ qpat_x_assum ‘∀neq needle pointer index t ret1 ret2. _’
      (qspecl_then [‘T’,‘needle’,‘pointer + 1w’,‘index + 2w’,‘next_state’,
                    ‘ret1’,‘ret2’] mp_tac)
    \\ impl_tac
    >- (
      simp [Abbr‘next_state’,wordSemTheory.get_var_def,lookup_insert,
            lookup_fromAList,n2w_SUC]
      \\ qx_gen_tac ‘offset’ \\ strip_tac
      \\ qpat_x_assum ‘∀i. i < SUC (LENGTH bs) ⇒ _’
        (qspec_then ‘SUC offset’ mp_tac)
      \\ simp [n2w_SUC,WORD_ADD_ASSOC])
    \\ simp [n2w_SUC,WORD_LEFT_ADD_DISTRIB,WORD_ADD_ASSOC,Abbr‘next_state’])
  \\ rewrite_tac [GSYM (ScanByte_step_def |> SPEC F |> REWRITE_RULE [list_Seq_def]),
               STOP_def]
  \\ qmatch_goalsub_abbrev_tac ‘evaluate (_,next_state)’
  \\ qpat_x_assum ‘∀neq needle pointer index t ret1 ret2. _’
    (qspecl_then [‘F’,‘needle’,‘pointer + 1w’,‘index + 2w’,‘next_state’,
                  ‘ret1’,‘ret2’] mp_tac)
  \\ impl_tac
  >- (
    simp [Abbr‘next_state’,wordSemTheory.get_var_def,lookup_insert,
          lookup_fromAList,n2w_SUC]
    \\ qx_gen_tac ‘offset’ \\ strip_tac
    \\ qpat_x_assum ‘∀i. i < SUC (LENGTH bs) ⇒ _’
      (qspec_then ‘SUC offset’ mp_tac)
    \\ simp [n2w_SUC,WORD_ADD_ASSOC])
  \\ simp [n2w_SUC,WORD_LEFT_ADD_DISTRIB,WORD_ADD_ASSOC,Abbr‘next_state’]
QED

Theorem evaluate_ScanByte_word_body[local]:
  ∀c neq (raw:'a word) (needle:word8) pointer index len
    (t:('a,'c,'ffi) wordSem$state).
    good_dimindex (:'a) ∧ arch_width_bits c.arch_width = dimindex (:'a) ∧
    dimindex (:'a) DIV 8 ≤ len ∧ len < dimword (:'a) ∧
    t.memory pointer = Word raw ∧ pointer ∈ t.mdomain ∧
    get_var 4 t = SOME (Word pointer) ∧
    get_var 6 t = SOME (Word (n2w len)) ∧
    get_var 8 t = SOME (Word index) ∧
    get_var 10 t = SOME (Word (word_of_byte (w2w needle))) ⇒
    let v = raw ?? word_of_byte (w2w needle) in
    let u = if neq then set_var 1 (Word v) t else
      set_var 3 (Word ((v - word_of_byte 1w) && ¬v)) (set_var 1 (Word v) t) in
      evaluate (ScanByte_word_body c neq,t) =
      if ∃i. i < dimindex (:'a) DIV 8 ∧
              ((get_byte (n2w i) raw t.be = needle) ⇔ ¬neq)
      then (SOME (Break 0),u)
      else (NONE,set_var 8 (Word (index + 2w * n2w (dimindex (:'a) DIV 8)))
        (set_var 6 (Word (n2w len - n2w (dimindex (:'a) DIV 8)))
          (set_var 4 (Word (pointer + n2w (dimindex (:'a) DIV 8))) u)))
Proof
  rpt gen_tac \\ strip_tac
  \\ drule ScanByte_constants \\ strip_tac \\ fs []
  \\ ‘dimindex (:'a) DIV 8 < dimword (:'a)’ by gvs [good_dimindex_def,dimword_def]
  \\ qspecl_then [‘raw’,‘needle’,‘neq’,‘t.be’] mp_tac ScanByte_word_test
  \\ asm_rewrite_tac []
  \\ simp_tac std_ss [LET_THM]
  \\ disch_then (assume_tac o GSYM)
  \\ Cases_on ‘neq’
  >- (
    fs []
    \\ simp [ScanByte_word_body_def,list_Seq_def,eq_eval,WORD_LO,
             integer_wordTheory.i2w_def]
    \\ Cases_on ‘raw ?? word_of_byte (w2w needle) = 0w’
    \\ fs [wordSemTheory.get_var_def]
    \\ simp [word_mul_n2w]
    \\ simp [eq_eval,word_mul_n2w,integer_wordTheory.i2w_def]
    \\ rewrite_tac [GSYM WORD_NEG_MUL])
  \\ gvs [wordSemTheory.get_var_def]
  \\ simp [ScanByte_word_body_def,list_Seq_def,eq_eval,WORD_LO,
           integer_wordTheory.i2w_def]
  \\ IF_CASES_TAC
  \\ simp [eq_eval,word_mul_n2w,integer_wordTheory.i2w_def]
  \\ rewrite_tac [GSYM WORD_NEG_MUL]
QED

Theorem SPLITP_skip_length[local]:
  ∀P k xs.
    k ≤ LENGTH xs ∧ (∀i. i < k ⇒ ¬P (EL i xs)) ⇒
    LENGTH (FST (SPLITP P xs)) =
      k + LENGTH (FST (SPLITP P (DROP k xs)))
Proof
  rpt gen_tac \\ strip_tac
  \\ ‘¬EXISTS P (TAKE k xs)’ by
    simp [EXISTS_NOT_EVERY,EVERY_EL,EL_TAKE,LENGTH_TAKE]
  \\ qspecl_then [‘TAKE k xs’,‘DROP k xs’] mp_tac SPLITP_APPEND
  \\ simp [TAKE_DROP,LENGTH_TAKE]
QED

Theorem evaluate_ScanByte_bulk[local]:
  ∀bs c neq needle addr index (t:('a,'c,'ffi) wordSem$state) ret1 ret2.
    good_dimindex (:'a) ∧ arch_width_bits c.arch_width = dimindex (:'a) ∧
    byte_aligned addr ∧ LENGTH bs < dimword (:'a) ∧ LENGTH bs < t.clock ∧
    (∀i. i < LENGTH bs ⇒
      mem_load_byte_aux t.memory t.mdomain t.be (addr + n2w i) = SOME (EL i bs)) ∧
    get_var 0 t = SOME (Loc ret1 ret2) ∧
    get_var 2 t = SOME (Word (w2w needle)) ∧
    get_var 4 t = SOME (Word addr) ∧
    get_var 6 t = SOME (Word (n2w (LENGTH bs))) ∧
    get_var 8 t = SOME (Word index) ∧
    get_var 10 t = SOME (Word (word_of_byte (w2w needle))) ⇒
    ∃ck.
      evaluate (ScanByte_bulk c neq,t) =
      (SOME (Result (Loc ret1 ret2)
        [Word (index + 2w * n2w
          (LENGTH (FST (SPLITP (λw. (w = needle) ⇔ ¬neq) bs))))]),
       t with <| clock := ck; locals := LN; locals_size := SOME 0 |>)
Proof
  gen_tac \\ completeInduct_on ‘LENGTH bs’
  \\ qx_gen_tac ‘bs’ \\ strip_tac \\ gvs []
  \\ qx_genl_tac [‘c’,‘neq’,‘needle’,‘pointer’,‘index’,‘t’,‘ret1’,‘ret2’]
  \\ strip_tac
  \\ ‘get_vars [0;2;4;6;8;10] t =
      SOME [Loc ret1 ret2; Word (w2w needle); Word pointer;
            Word (n2w (LENGTH bs)); Word index;
            Word (word_of_byte (w2w needle))]’
    by simp [wordSemTheory.get_vars_def]
  \\ drule cut_state_ScanByte_word \\ strip_tac
  \\ drule ScanByte_constants \\ strip_tac
  \\ Cases_on ‘LENGTH bs < dimindex (:'a) DIV 8’
  >- (
    ‘dimindex (:'a) DIV 8 < dimword (:'a)’ by gvs [good_dimindex_def,dimword_def]
    \\ simp_tac std_ss [ScanByte_bulk_def,LET_THM]
    \\ qmatch_goalsub_abbrev_tac ‘Seq bulk_loop tail_loop’
    \\ once_rewrite_tac [wordSemTheory.evaluate_def]
    \\ simp_tac std_ss [Abbr‘bulk_loop’]
    \\ once_rewrite_tac [wordSemTheory.evaluate_def]
    \\ simp [ScanByte_word_body_def,eq_eval,lookup_fromAList,integer_wordTheory.i2w_def,WORD_LO]
    \\ qmatch_goalsub_abbrev_tac ‘cut_state _ word_state’
    \\ ‘get_vars [0;2;4;6;8] word_state =
        SOME [Loc ret1 ret2; Word (w2w needle); Word pointer;
              Word (n2w (LENGTH bs)); Word index]’ by
      simp [Abbr‘word_state’,wordSemTheory.get_vars_def,wordSemTheory.get_var_def,
            lookup_fromAList]
    \\ drule cut_state_ScanByte \\ strip_tac
    \\ simp []
    \\ simp_tac std_ss [Abbr‘tail_loop’,ScanByte_tail_code_def,LET_THM]
    \\ qmatch_goalsub_abbrev_tac ‘evaluate (_,tail_state)’
    \\ qspecl_then [‘bs’,‘neq’,‘needle’,‘pointer’,‘index’,‘tail_state’,‘ret1’,‘ret2’]
      mp_tac evaluate_ScanByte_tail
    \\ impl_tac
    >- (
      simp [Abbr‘tail_state’,Abbr‘word_state’,wordSemTheory.get_var_def,
            lookup_fromAList])
    \\ simp [Abbr‘tail_state’,Abbr‘word_state’])
  \\ ‘dimindex (:'a) DIV 8 ≤ LENGTH bs’ by decide_tac
  \\ drule_all ScanByte_load_word
  \\ disch_then (qx_choose_then ‘raw’ strip_assume_tac)
  \\ simp_tac std_ss [ScanByte_bulk_def,LET_THM]
  \\ qmatch_goalsub_abbrev_tac ‘Seq bulk_loop tail_loop’
  \\ once_rewrite_tac [wordSemTheory.evaluate_def]
  \\ simp_tac std_ss [Abbr‘bulk_loop’]
  \\ once_rewrite_tac [wordSemTheory.evaluate_def]
  \\ simp []
  \\ qmatch_goalsub_abbrev_tac ‘evaluate (ScanByte_word_body c neq,word_state)’
  \\ qspecl_then [‘c’,‘neq’,‘raw’,‘needle’,‘pointer’,‘index’,‘LENGTH bs’,‘word_state’]
    mp_tac evaluate_ScanByte_word_body
  \\ impl_tac
  >- (
    simp [Abbr‘word_state’,wordSemTheory.get_var_def,lookup_fromAList])
  \\ simp_tac std_ss [LET_THM] \\ strip_tac
  \\ qabbrev_tac ‘tested_state =
      if neq then set_var 1 (Word (raw ?? word_of_byte (w2w needle))) word_state
      else set_var 3
        (Word (((raw ?? word_of_byte (w2w needle)) - word_of_byte 1w) &&
               ¬(raw ?? word_of_byte (w2w needle))))
        (set_var 1 (Word (raw ?? word_of_byte (w2w needle))) word_state)’
  \\ ‘word_state.be = t.be’ by simp [Abbr‘word_state’]
  \\ ‘tested_state.clock = t.clock’ by (
    Cases_on ‘neq’ \\ simp [Abbr‘tested_state’,Abbr‘word_state’,wordSemTheory.set_var_def])
  \\ ‘t.clock ≠ 0’ by decide_tac
  \\ Cases_on ‘∃i. i < dimindex (:'a) DIV 8 ∧
      ((get_byte (n2w i) raw t.be = needle) ⇔ ¬neq)’
  \\ asm_simp_tac std_ss [wordSemTheory.cont_loop_def,wordSemTheory.exit_loop_def,
                          wordSemTheory.set_var_def]
  >- (
    ‘get_vars [0;2;4;6;8] tested_state =
        SOME [Loc ret1 ret2; Word (w2w needle); Word pointer;
              Word (n2w (LENGTH bs)); Word index]’
    by (
      Cases_on ‘neq’
      \\ simp [Abbr‘tested_state’,Abbr‘word_state’,eq_eval,lookup_fromAList])
    \\ drule cut_state_ScanByte \\ strip_tac
    \\ simp []
    \\ simp_tac std_ss [Abbr‘tail_loop’,ScanByte_tail_code_def,LET_THM]
    \\ qmatch_goalsub_abbrev_tac ‘evaluate (_,tail_state)’
    \\ qspecl_then [‘bs’,‘neq’,‘needle’,‘pointer’,‘index’,‘tail_state’,‘ret1’,‘ret2’]
      mp_tac evaluate_ScanByte_tail
    \\ impl_tac
    >- (
      Cases_on ‘neq’
      \\ simp [Abbr‘tail_state’,Abbr‘tested_state’,Abbr‘word_state’,
               wordSemTheory.set_var_def,wordSemTheory.get_var_def,lookup_fromAList])
    \\ Cases_on ‘neq’
    \\ simp [Abbr‘tail_state’,Abbr‘tested_state’,Abbr‘word_state’,wordSemTheory.set_var_def])
  \\ simp []
  \\ rewrite_tac [STOP_def]
  \\ simp_tac std_ss [Abbr‘tail_loop’]
  \\ rewrite_tac [GSYM evaluate_Seq_step,
      GSYM (ScanByte_bulk_def |> SIMP_RULE std_ss [LET_THM])]
  \\ qmatch_goalsub_abbrev_tac ‘evaluate (_,next_state)’
  \\ ‘0 < dimindex (:'a) DIV 8’ by gvs [good_dimindex_def]
  \\ ‘LENGTH (DROP (dimindex (:'a) DIV 8) bs) < LENGTH bs’ by (
    simp [LENGTH_DROP] \\ decide_tac)
  \\ qpat_x_assum ‘∀m. m < LENGTH bs ⇒ ∀shorter. m = LENGTH shorter ⇒ _’
    (qspec_then ‘LENGTH (DROP (dimindex (:'a) DIV 8) bs)’ mp_tac)
  \\ asm_rewrite_tac []
  \\ disch_then (qspec_then ‘DROP (dimindex (:'a) DIV 8) bs’ mp_tac)
  \\ simp_tac std_ss []
  \\ disch_then (qspecl_then
    [‘c’,‘neq’,‘needle’,‘pointer + n2w (dimindex (:'a) DIV 8)’,
     ‘index + 2w * n2w (dimindex (:'a) DIV 8)’,‘next_state’,‘ret1’,‘ret2’] mp_tac)
  \\ impl_tac
  >- (
    ‘byte_aligned (pointer + n2w (dimindex (:'a) DIV 8))’ by (
      irule byte_aligned_add
      \\ simp [REWRITE_RULE [bytes_in_word_def] byte_aligned_bytes_in_word])
    \\ Cases_on ‘neq’
    \\ simp [Abbr‘next_state’,Abbr‘tested_state’,Abbr‘word_state’,
             wordSemTheory.set_var_def,wordSemTheory.dec_clock_def,
             wordSemTheory.get_var_def,lookup_insert,lookup_fromAList,LENGTH_DROP,n2w_sub]
    \\ qx_gen_tac ‘offset’ \\ strip_tac
    \\ qpat_x_assum ‘∀i. i < LENGTH bs ⇒ mem_load_byte_aux _ _ _ _ = _’
      (qspec_then ‘offset + dimindex (:'a) DIV 8’ mp_tac)
    \\ simp [EL_DROP,GSYM word_add_n2w,WORD_ADD_ASSOC])
  \\ ‘∀i. i < dimindex (:'a) DIV 8 ⇒ ¬((EL i bs = needle) ⇔ ¬neq)’
    by (
      qx_gen_tac ‘offset’ \\ strip_tac
      \\ ‘get_byte (n2w offset) raw t.be = EL offset bs’ by simp []
      \\ metis_tac [])
  \\ ‘LENGTH (FST (SPLITP (λw. (w = needle) ⇔ ¬neq) bs)) =
      dimindex (:'a) DIV 8 + LENGTH (FST
        (SPLITP (λw. (w = needle) ⇔ ¬neq) (DROP (dimindex (:'a) DIV 8) bs)))’
  by (
    irule SPLITP_skip_length \\ simp [])
  \\ simp [GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB,WORD_ADD_ASSOC]
  \\ Cases_on ‘neq’
  \\ simp [Abbr‘next_state’,Abbr‘tested_state’,Abbr‘word_state’,
           wordSemTheory.set_var_def,wordSemTheory.dec_clock_def]
QED

Theorem ScanByte_alignment_test[local]:
  ∀c (pointer:'a word).
    arch_width_bits c.arch_width = dimindex (:'a) ⇒
    (pointer && i2w (&arch_bytes c.arch_width - 1) = 0w ⇔ byte_aligned pointer)
Proof
  rpt gen_tac \\ Cases_on ‘c.arch_width’
  \\ simp [asmTheory.arch_width_bits_def,asmTheory.arch_bytes_def]
  \\ disch_then (assume_tac o SYM)
  \\ simp [byte_aligned_def,aligned_bitwise_and,integer_wordTheory.i2w_def]
QED

Theorem ScanByte_broadcast[local]:
  ∀c (w:'a word).
    arch_width_bits c.arch_width = dimindex (:'a) ⇒
    let p = w ‖ (w ≪ 8) in
    let q = p ‖ (p ≪ 16) in
      (if arch_bytes c.arch_width = 4 then q else q ‖ (q ≪ 32)) = word_of_byte w
Proof
  rpt gen_tac \\ Cases_on ‘c.arch_width’
  \\ simp [asmTheory.arch_width_bits_def,asmTheory.arch_bytes_def]
  \\ disch_then (assume_tac o SYM)
  \\ simp [word_of_byte_def,WORD_OR_COMM]
QED

Theorem ScanByte_code_cases[local]:
  ∀c neq. (if neq then ScanNeq_code c else ScanEq_code c) = ScanByte_code c neq
Proof
  rpt gen_tac \\ Cases_on ‘neq’ \\ simp [ScanNeq_code_def,ScanEq_code_def]
QED

Theorem evaluate_ScanByte_step[local]:
  ∀neq (head:word8) needle pointer remaining index
    (t:('a,'c,'ffi) wordSem$state) ret1 ret2.
    good_dimindex (:'a) ∧
    mem_load_byte_aux t.memory t.mdomain t.be pointer = SOME head ∧
    get_var 0 t = SOME (Loc ret1 ret2) ∧
    get_var 2 t = SOME (Word (w2w needle)) ∧
    get_var 4 t = SOME (Word pointer) ∧
    get_var 6 t = SOME (Word remaining) ∧
    get_var 8 t = SOME (Word index) ⇒
    evaluate (ScanByte_step neq,t) =
      if (head = needle) ⇔ ¬neq then
        (SOME (Result (Loc ret1 ret2) [Word index]),
         t with <| locals := LN; locals_size := SOME 0 |>)
      else
        (NONE,set_var 8 (Word (index + 2w))
          (set_var 6 (Word (remaining - 1w))
            (set_var 4 (Word (pointer + 1w))
              (set_var 1 (Word (w2w head)) t))))
Proof
  rpt gen_tac \\ strip_tac
  \\ ‘((w2w head:'a word) = w2w needle) ⇔ head = needle’ by (
    irule w2w_byte_eq \\ asm_rewrite_tac [])
  \\ Cases_on ‘neq’ \\ Cases_on ‘head = needle’
  \\ gvs [ScanByte_step_def,list_Seq_def,eq_eval,wordSemTheory.inst_def,
           integer_wordTheory.i2w_def,wordSemTheory.flush_state_def]
QED

Theorem evaluate_ScanByte_broadcast[local]:
  ∀c (w:'a word) (t:('a,'c,'ffi) wordSem$state) next.
    arch_width_bits c.arch_width = dimindex (:'a) ∧
    get_var 2 t = SOME (Word w) ⇒
    evaluate
      (list_Seq
        [Assign 10 (Op Or [Var 2; ShiftN Lsl (Var 2) 8]);
         Assign 10 (Op Or [Var 10; ShiftN Lsl (Var 10) 16]);
         (if arch_bytes c.arch_width = 4 then Skip else
            Assign 10 (Op Or [Var 10; ShiftN Lsl (Var 10) 32]));
         next],t) =
    evaluate (next,set_var 10 (Word (word_of_byte w)) t)
Proof
  rpt gen_tac \\ strip_tac
  \\ qspecl_then [‘c’,‘w’] mp_tac ScanByte_broadcast
  \\ asm_rewrite_tac [] \\ simp_tac std_ss [LET_THM] \\ strip_tac
  \\ qpat_x_assum ‘arch_width_bits _ = _’ (assume_tac o SYM)
  \\ Cases_on ‘c.arch_width’
  \\ gvs [asmTheory.arch_width_bits_def,asmTheory.arch_bytes_def,wordSemTheory.get_var_def]
  \\ simp [list_Seq_def,eq_eval,wordSemTheory.word_sh_def,insert_shadow]
  \\ simp [eq_eval,wordSemTheory.word_sh_def,integer_wordTheory.i2w_def,
           dimword_def,insert_shadow]
QED

Theorem evaluate_ScanByte:
  ∀bs c neq needle addr index (t:('a,'c,'ffi) wordSem$state) ret1 ret2.
    good_dimindex (:'a) ∧ arch_width_bits c.arch_width = dimindex (:'a) ∧ LENGTH bs < dimword (:'a) ∧
    LENGTH bs < t.clock ∧
    (∀i. i < LENGTH bs ⇒
      mem_load_byte_aux t.memory t.mdomain t.be (addr + n2w i) =
      SOME (EL i bs)) ∧
    (∃md. lookup (if neq then ScanNeq_location else ScanEq_location) t.code =
      SOME (5,if neq then ScanNeq_code c else ScanEq_code c,md)) ∧
    get_var 0 t = SOME (Loc ret1 ret2) ∧
    get_var 2 t = SOME (Word (w2w needle)) ∧
    get_var 4 t = SOME (Word addr) ∧
    get_var 6 t = SOME (Word (n2w (LENGTH bs))) ∧
    get_var 8 t = SOME (Word index) ⇒
    ∃ck max_stack.
      evaluate ((if neq then ScanNeq_code c else ScanEq_code c),t) =
      (SOME (Result (Loc ret1 ret2)
        [Word (index + 2w * n2w
          (LENGTH (FST (SPLITP (λw. (w = needle) ⇔ ¬neq) bs))))]),
       t with <| clock := ck; stack_max := max_stack;
                 locals := LN; locals_size := SOME 0 |>) ∧
      (max_stack ≠ t.stack_max ⇒
       max_stack = OPTION_MAP2 MAX t.stack_max
         (OPTION_MAP2 $+ (stack_size t.stack)
           (lookup (if neq then ScanNeq_location else ScanEq_location)
                   t.stack_size)))
Proof
  rewrite_tac [ScanByte_code_cases]
  \\ Induct
  >- (
    qx_genl_tac [‘c’,‘neq’,‘needle’,‘pointer’,‘index’,‘t’,‘ret1’,‘ret2’]
    \\ strip_tac
    \\ ‘get_vars [0;2;4;6;8] t =
        SOME [Loc ret1 ret2; Word (w2w needle); Word pointer; Word 0w; Word index]’
      by gvs [wordSemTheory.get_vars_def]
    \\ drule cut_state_ScanByte \\ strip_tac
    \\ qexists_tac ‘t.clock’ \\ qexists_tac ‘t.stack_max’
    \\ simp [ScanByte_code_def,list_Seq_def,eq_eval,lookup_fromAList,SPLITP,
             integer_wordTheory.i2w_def,wordSemTheory.flush_state_def])
  \\ qx_genl_tac [‘head’,‘c’,‘neq’,‘needle’,‘pointer’,‘index’,‘t’,‘ret1’,‘ret2’]
  \\ strip_tac
  \\ ‘mem_load_byte_aux t.memory t.mdomain t.be pointer = SOME head’ by (
    qpat_x_assum ‘∀i. i < LENGTH (head::bs) ⇒ _’ (qspec_then ‘0’ mp_tac)
    \\ simp [])
  \\ ‘(n2w (LENGTH (head::bs)):'a word) ≠ 0w’ by simp [n2w_11]
  \\ ‘get_vars [0;2;4;6;8] t =
      SOME [Loc ret1 ret2; Word (w2w needle); Word pointer;
            Word (n2w (LENGTH (head::bs))); Word index]’
    by simp [wordSemTheory.get_vars_def]
  \\ drule cut_state_ScanByte \\ strip_tac
  \\ qspecl_then [‘c’,‘pointer’] mp_tac ScanByte_alignment_test
  \\ asm_rewrite_tac [] \\ strip_tac
  \\ fs [LENGTH]
  \\ simp_tac std_ss [ScanByte_code_def,list_Seq_def,LET_THM]
  \\ qmatch_goalsub_abbrev_tac ‘Seq prefix_loop rest’
  \\ once_rewrite_tac [wordSemTheory.evaluate_def]
  \\ simp_tac std_ss [Abbr‘prefix_loop’]
  \\ once_rewrite_tac [wordSemTheory.evaluate_def]
  \\ simp [eq_eval,lookup_fromAList,integer_wordTheory.i2w_0]
  \\ Cases_on ‘byte_aligned pointer’ \\ simp []
  >- (
    qmatch_goalsub_abbrev_tac ‘cut_state _ prefix_state’
    \\ ‘get_vars [0;2;4;6;8] prefix_state =
        SOME [Loc ret1 ret2; Word (w2w needle); Word pointer;
              Word (n2w (SUC (LENGTH bs))); Word index]’ by
      simp [Abbr‘prefix_state’,wordSemTheory.get_vars_def,wordSemTheory.get_var_def,
            lookup_fromAList]
    \\ drule cut_state_ScanByte \\ strip_tac \\ simp []
    \\ qmatch_goalsub_abbrev_tac ‘evaluate (_,ready_state)’
    \\ ‘get_var 6 ready_state = SOME (Word (n2w (SUC (LENGTH bs))))’ by
      simp [Abbr‘ready_state’,wordSemTheory.get_var_def,lookup_fromAList]
    \\ drule ScanByte_constants \\ disch_then (assume_tac o CONJUNCT1)
    \\ ‘dimindex (:'a) DIV 8 < dimword (:'a)’ by gvs [good_dimindex_def,dimword_def]
    \\ simp_tac std_ss [Abbr‘rest’]
    \\ once_rewrite_tac [wordSemTheory.evaluate_def]
    \\ Cases_on ‘SUC (LENGTH bs) < dimindex (:'a) DIV 8’
    \\ simp [wordSemTheory.get_var_imm_def,asmTheory.word_cmp_def,
             integer_wordTheory.i2w_def,WORD_LO]
    >- (
      simp_tac std_ss [ScanByte_tail_code_def,LET_THM]
      \\ qspecl_then [‘head::bs’,‘neq’,‘needle’,‘pointer’,‘index’,‘ready_state’,‘ret1’,‘ret2’]
        mp_tac evaluate_ScanByte_tail
      \\ impl_tac
      >- (
        simp [Abbr‘ready_state’,Abbr‘prefix_state’,wordSemTheory.get_var_def,
              lookup_fromAList,LENGTH])
      \\ disch_then (qx_choose_then ‘result_clock’ assume_tac)
      \\ qexists_tac ‘result_clock’ \\ qexists_tac ‘t.stack_max’
      \\ asm_rewrite_tac []
      \\ simp [Abbr‘ready_state’,Abbr‘prefix_state’]
      \\ simp [wordSemTheory.state_component_equality])
    \\ qspecl_then [‘c’,‘w2w needle:'a word’,‘ready_state’,‘ScanByte_bulk c neq’]
      mp_tac (REWRITE_RULE [list_Seq_def] evaluate_ScanByte_broadcast)
    \\ impl_tac
    >- (
      simp [Abbr‘ready_state’,wordSemTheory.get_var_def,lookup_fromAList])
    \\ strip_tac \\ gvs []
    \\ qmatch_goalsub_abbrev_tac ‘evaluate (ScanByte_bulk c neq,bulk_state)’
    \\ qspecl_then [‘head::bs’,‘c’,‘neq’,‘needle’,‘pointer’,‘index’,‘bulk_state’,‘ret1’,‘ret2’]
      mp_tac evaluate_ScanByte_bulk
    \\ impl_tac
    >- (
      simp [Abbr‘bulk_state’,Abbr‘ready_state’,Abbr‘prefix_state’,
            wordSemTheory.set_var_def,wordSemTheory.get_var_def,lookup_insert,
            lookup_fromAList,LENGTH])
    \\ disch_then (qx_choose_then ‘result_clock’ assume_tac)
    \\ qexists_tac ‘result_clock’ \\ qexists_tac ‘t.stack_max’
    \\ asm_rewrite_tac []
    \\ simp [Abbr‘bulk_state’,Abbr‘ready_state’,Abbr‘prefix_state’,
             wordSemTheory.set_var_def,wordSemTheory.state_component_equality])
  \\ qmatch_goalsub_abbrev_tac ‘evaluate (ScanByte_step neq,prefix_state)’
  \\ qspecl_then
    [‘neq’,‘head’,‘needle’,‘pointer’,‘n2w (SUC (LENGTH bs)):'a word’,
     ‘index’,‘prefix_state’,‘ret1’,‘ret2’] mp_tac evaluate_ScanByte_step
  \\ impl_tac
  >- (
    simp [Abbr‘prefix_state’,wordSemTheory.get_var_def,lookup_fromAList])
  \\ strip_tac
  \\ ‘prefix_state.clock = t.clock’ by simp [Abbr‘prefix_state’]
  \\ ‘t.clock ≠ 0’ by decide_tac
  \\ Cases_on ‘(head = needle) ⇔ ¬neq’
  \\ asm_simp_tac std_ss [wordSemTheory.cont_loop_def,wordSemTheory.exit_loop_def,
                          wordSemTheory.set_var_def]
  >- (
    qexists_tac ‘t.clock’ \\ qexists_tac ‘t.stack_max’
    \\ simp [SPLITP,Abbr‘prefix_state’,wordSemTheory.state_component_equality])
  \\ simp [SPLITP]
  \\ rewrite_tac [STOP_def]
  \\ simp_tac std_ss [Abbr‘rest’]
  \\ rewrite_tac [GSYM evaluate_Seq_step,
      GSYM (ScanByte_code_def |> SIMP_RULE std_ss [LET_THM,list_Seq_def])]
  \\ qmatch_goalsub_abbrev_tac ‘evaluate (_,next_state)’
  \\ qpat_x_assum ‘∀c neq needle addr index t ret1 ret2. _’
    (qspecl_then [‘c’,‘neq’,‘needle’,‘pointer + 1w’,‘index + 2w’,‘next_state’,
                  ‘ret1’,‘ret2’] mp_tac)
  \\ impl_tac
  >- (
    simp [Abbr‘next_state’,Abbr‘prefix_state’,wordSemTheory.get_var_def,
          lookup_insert,lookup_fromAList,n2w_SUC]
    \\ qx_gen_tac ‘offset’ \\ strip_tac
    \\ qpat_x_assum ‘∀i. i < SUC (LENGTH bs) ⇒ mem_load_byte_aux _ _ _ _ = _’
      (qspec_then ‘SUC offset’ mp_tac)
    \\ simp [n2w_SUC,WORD_ADD_ASSOC])
  \\ simp [n2w_SUC,WORD_LEFT_ADD_DISTRIB,WORD_ADD_ASSOC,
        Abbr‘next_state’,Abbr‘prefix_state’]
QED

Theorem evaluate_ByteCopyWords:
  ∀c s a b k.
    get_var 4 s = SOME (Word a) /\
    get_var 6 s = SOME (Word b) /\
    k = n2w (arch_bytes c.arch_width) /\
    a IN s.mdomain /\ a + k IN s.mdomain /\ a + 2w * k IN s.mdomain /\
    b IN s.mdomain /\ b + k IN s.mdomain /\ b + 2w * k IN s.mdomain ==>
    evaluate (ByteCopyWords_code c,s) =
      (NONE,
       (set_var 5 (s.memory (a + 2w * k))
         (set_var 3 (s.memory (a + k))
           (set_var 1 (s.memory a) s))) with memory :=
         (b + 2w * k =+ s.memory (a + 2w * k))
           ((b + k =+ s.memory (a + k))
             ((b =+ s.memory a) s.memory)))
Proof
  rpt gen_tac
  \\ rw []
  \\ fs [ByteCopyWords_code_def,list_Seq_def,
          wordSemTheory.evaluate_def,wordSemTheory.word_exp_def,
          wordSemTheory.get_var_def,wordSemTheory.set_var_def,
          wordSemTheory.mem_load_def,wordSemTheory.mem_store_def,
          wordSemTheory.the_words_def,wordSemTheory.word_op_def,
          wordSemTheory.fix_clock_def,lookup_insert,
          integer_wordTheory.i2w_pos,GSYM word_mul_n2w]
QED

Theorem evaluate_ByteCopyShiftWords:
  ∀c s a b carry sh back k w1 w2 w3.
    get_var 4 (s:('a,'c,'ffi) wordSem$state) = SOME (Word a) /\
    get_var 6 s = SOME (Word b) /\
    get_var 10 s = SOME (Word carry) /\
    get_var 12 s = SOME (Word sh) /\
    get_var 14 s = SOME (Word back) /\
    w2n sh < dimindex (:'a) /\ w2n back < dimindex (:'a) /\
    k = n2w (arch_bytes c.arch_width) /\
    s.memory a = Word w1 /\ s.memory (a + k) = Word w2 /\
    s.memory (a + 2w * k) = Word w3 /\
    a IN s.mdomain /\ a + k IN s.mdomain /\ a + 2w * k IN s.mdomain /\
    b IN s.mdomain /\ b + k IN s.mdomain /\ b + 2w * k IN s.mdomain ==>
    let push = (\w. if c.be then w >>> w2n sh else w << w2n sh);
        pull = (\w. if c.be then w << w2n back else w >>> w2n back);
        out1 = carry || push w1;
        out2 = pull w1 || push w2;
        out3 = pull w2 || push w3
    in
      evaluate (ByteCopyShiftWords_code c,s) =
        (NONE,
         (set_var 10 (Word (pull w3))
           (set_var 7 (Word out3)
             (set_var 5 (Word w3)
               (set_var 3 (Word w2) (set_var 1 (Word w1) s)))))
         with memory :=
           (b + 2w * k =+ Word out3)
             ((b + k =+ Word out2) ((b =+ Word out1) s.memory)))
Proof
  rpt gen_tac
  \\ Cases_on `c.be`
  \\ rw []
  \\ fs [ByteCopyShiftWords_code_def,list_Seq_def,
          wordSemTheory.evaluate_def,wordSemTheory.word_exp_def,
          wordSemTheory.get_var_def,wordSemTheory.set_var_def,
          wordSemTheory.mem_load_def,wordSemTheory.mem_store_def,
          wordSemTheory.the_words_def,wordSemTheory.word_op_def,
          wordSemTheory.fix_clock_def,wordSemTheory.word_sh_def,
          lookup_insert,insert_shadow,
          integer_wordTheory.i2w_pos,GSYM word_mul_n2w]
QED

Theorem byte_copy_flush_zero:
  byte_copy_flush be 0 carry b m = m
Proof
  simp [byte_copy_flush_def]
QED

Theorem evaluate_ByteCopyFlush:
  ∀c d s b carry old.
    good_dimindex (:'a) /\ d < dimindex (:'a) DIV 8 /\
    get_var 6 (s:('a,'c,'ffi) wordSem$state) = SOME (Word b) /\
    get_var 10 s = SOME (Word carry) /\
    get_var 12 s = SOME (Word (n2w (8 * d))) /\
    (d <> 0 ==> b IN s.mdomain /\ s.memory b = Word old) ==>
    let push = if (c:data_to_word$config).be then Lsr else Lsl;
        out = carry || (old && (if c.be then -1w >>> (8 * d) else -1w << (8 * d)))
    in
      evaluate
        (If Equal 12 (Imm 0) Skip
          (list_Seq [
            Assign 1 (Op Or [Var 10; Op And [Load (Var 6);
                              Shift push (Const (-1)) (Var 12)]]);
            Store (Var 6) 1;
            Assign 6 (Op Add [Var 6; ShiftN Lsr (Var 12) 3])]),s) =
      (NONE, if d = 0 then s else
         set_var 6 (Word (b + n2w d)) (set_var 1 (Word out)
           (s with memory := (b =+ Word out) s.memory)))
Proof
  rpt gen_tac
  \\ Cases_on `c.be`
  \\ rw []
  \\ gvs [miscTheory.good_dimindex_def,
          DECIDE ``d < 4 <=> d = 0 \/ d = 1 \/ d = 2 \/ d = 3``,
          DECIDE ``d < 8 <=> d = 0 \/ d = 1 \/ d = 2 \/ d = 3 \/
                               d = 4 \/ d = 5 \/ d = 6 \/ d = 7``]
  \\ fs [list_Seq_def,wordSemTheory.evaluate_def,
          wordSemTheory.get_var_imm_def,asmTheory.word_cmp_def,
          wordSemTheory.word_exp_def,wordSemTheory.word_op_def,
          wordSemTheory.word_sh_def,wordSemTheory.the_words_def,
          wordSemTheory.get_var_def,wordSemTheory.set_var_def,
          wordSemTheory.mem_load_def,wordSemTheory.mem_store_def,
          wordSemTheory.fix_clock_def,lookup_insert,dimword_def,
          integer_wordTheory.i2w_pos,integer_wordTheory.i2w_minus_1,
          word_lsr_n2w,word_bits_n2w,bitTheory.BITS_THM]
QED

val _ = augment_srw_ss [rewrites [integer_wordTheory.i2w_pos,
                                  integer_wordTheory.i2w_w2i, i2w_neg, i2w_sub1,
    data_to_word_memoryProofTheory.compiler_all_ones_i2w,
  data_to_wordTheory.get_lowerbits_def,data_to_wordTheory.make_ptr_def,
  data_to_wordTheory.make_cons_ptr_def]]

val _ = numLib.prefer_num ();

fun drule0 th =
  first_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO] th))

val _ = hide "next";
val _ = hide "el";
val shift_def = backend_commonTheory.word_shift_def
val Smallnum_def = LIST_CONJ [data_to_word_memoryProofTheory.Smallnum_def,
                             data_to_wordTheory.Smallnum_def];
val get_lowerbits_def = data_to_word_memoryProofTheory.get_lowerbits_def;
val make_ptr_def = data_to_word_memoryProofTheory.make_ptr_def;
val make_cons_ptr_def = data_to_word_memoryProofTheory.make_cons_ptr_def;
val isWord_def = wordSemTheory.isWord_def
val theWord_def = wordSemTheory.theWord_def

Overload lookup[local] = “sptree$lookup”;

val assign_def =
  data_to_wordTheory.assign_def
  |> REWRITE_RULE [arg1_def, arg2_def, arg3_def, arg4_def, all_assign_defs];

val clean_tac = rpt var_eq_tac \\ rpt (qpat_x_assum `T` kall_tac);
fun rpt_drule0 th = drule0 (th |> GEN_ALL) \\ rpt (disch_then drule0 \\ fs []);

val state_rel_def = data_to_word_gcProofTheory.state_rel_def;
val code_rel_def = data_to_word_gcProofTheory.code_rel_def;

val do_app = LIST_CONJ [do_app_def,do_app_aux_def,do_space_def,
  data_spaceTheory.op_space_req_def,
  dataLangTheory.op_space_reset_def,
  do_stack_def,stack_consumed_def];

val eval_tac = fs [wordSemTheory.evaluate_def,
  wordSemTheory.word_exp_def, wordSemTheory.set_var_def, set_var_def,
  wordSemTheory.get_store_def,
  wordSemTheory.get_var_def,
  wordSemTheory.the_words_def, wordSemTheory.mem_load_def,
  wordSemTheory.word_op_def, wordSemTheory.word_sh_def];

Theorem get_real_offset_lemma:
   get_var v t = SOME (Word i_w) /\
    good_dimindex (:'a) /\
    arch_width_bits c.arch_width = dimindex (:'a) /\
    get_real_offset i_w = SOME y ==>
    word_exp t (real_offset c v) = SOME (Word (y:'a word))
Proof
  fs [get_real_offset_def,shift_def,data_to_wordTheory.arch_size] \\ every_case_tac \\ fs []
  \\ fs [wordSemTheory.get_var_def,real_offset_def,shift_def,data_to_wordTheory.arch_size] \\ eval_tac \\ fs []
  \\ fs [good_dimindex_def,dimword_def,bytes_in_word_def] \\ rw []
    \\ fs [wordSemTheory.get_var_def,real_offset_def,shift_def,data_to_wordTheory.arch_size]
QED

Theorem get_real_byte_offset_lemma:
   get_var v t = SOME (Word (w:α word)) ∧ good_dimindex (:α) ∧
   arch_width_bits c.arch_width = dimindex (:α) ⇒
   word_exp t (real_byte_offset c v) = SOME (Word (w >>> 1))
Proof
  rw[real_byte_offset_def,data_to_wordTheory.arch_size,wordSemTheory.get_var_def,bytes_in_word_def]
  \\ eval_tac \\ fs[good_dimindex_def,dimword_def]
QED

Theorem reorder_lemma:
  memory_rel c be ts x.refs x.space t.store t.memory t.mdomain (x1::x2::x3::xs) ==>
  memory_rel c be ts x.refs x.space t.store t.memory t.mdomain (x3::x1::x2::xs)
Proof
  match_mp_tac memory_rel_rearrange \\ fs [] \\ rw [] \\ fs []
QED

Theorem lookup_loc_lemma:
   env_to_list y2 permute = (l',permute') ∧
   cut_envs (adjust_sets keep_names) locals = SOME (y1,y2) ∧
   lookup 0 (union y2 y1) = SOME (Loc l1 l2) ⇒
   ALOOKUP l' 0 = NONE ∧ lookup 0 y1 = SOME (Loc l1 l2)
Proof
  strip_tac
  \\ imp_res_tac wordPropsTheory.env_to_list_lookup_equiv
  \\ gvs []
  \\ reverse conj_asm1_tac
  >- gvs [lookup_union]
  \\ gvs [adjust_sets_def,wordSemTheory.cut_envs_def]
  \\ gvs [AllCaseEqs(),wordSemTheory.cut_names_def]
  \\ gvs [lookup_inter_alt,data_to_word_gcProofTheory.NOT_0_domain]
QED

Theorem header_sum_reassoc[local]:
  (a:num) * p + (b * p + k) = (a + b) * p + k
Proof
  rewrite_tac [RIGHT_ADD_DISTRIB,ADD_ASSOC]
QED

val _ = augment_srw_ss [rewrites [arch_bytes_word]];
val eval_tac = imp_res_tac state_rel_arch_width
  \\ imp_res_tac memory_rel_arch_width \\ eval_tac
  \\ fs [GSYM word_mul_n2w];

Theorem set_vars_sing:
   set_vars [n] [w] t = set_var n w t
Proof
  EVAL_TAC
QED

Theorem TWO_MUL_LSL:
   n2w (2 * i) << k = n2w i << (k + 1)
Proof
  fs [WORD_MUL_LSL,EXP_ADD,word_mul_n2w]
QED

Theorem word_exp_SmallLsr:
  n < dimindex(:'a) ⇒
   word_exp s (SmallLsr e n) =
      case word_exp s e of
        | SOME (Word w) => SOME (Word ((w:'a word) >>> n))
        | res => (if n = 0 then res else NONE)
Proof
  rw [SmallLsr_def] \\ assume_tac DIMINDEX_GT_0
  \\ TRY (`F` by decide_tac \\ NO_TAC)
  THEN1
   (full_simp_tac std_ss [GSYM NOT_LESS]
    \\ Cases_on `word_exp s e` \\ fs []
    \\ Cases_on `x` \\ fs [])
  \\ fs [word_exp_rw] \\ every_case_tac \\ fs []
  \\ ‘n < dimword (:α)’ by simp[dimindex_lt_dimword] \\ fs []
QED

Theorem evaluate_MakeBytes:
   arch_width_bits c.arch_width = dimindex(:'a) /\ good_dimindex (:'a) ==>
    evaluate (MakeBytes c n,s) =
      case get_var n s of
      | SOME (Word w) => (NONE,set_var n (Word (word_of_byte ((w:'a word) >>> 1))) s)
      | _ => (SOME Error,s)
Proof
  fs [MakeBytes_def,list_Seq_def,wordSemTheory.evaluate_def,word_exp_rw,
      wordSemTheory.get_var_def] \\ strip_tac
  \\ Cases_on `lookup n s.locals` \\ fs []
  \\ Cases_on `x` \\ fs [] \\ IF_CASES_TAC
  \\ fs [EVAL ``good_dimindex (:'a)``]
  \\ fs [wordSemTheory.set_var_def,
         wordSemTheory.get_var_def,lookup_insert,word_of_byte_def,
         insert_shadow,wordSemTheory.evaluate_def,word_exp_rw,dimword_def]
QED

Theorem w2w_shift_shift:
   good_dimindex (:'a) ==> ((w2w (w:word8) ≪ 1 ⋙ 1) : 'a word) = w2w w
Proof
  fs [good_dimindex_def,fcpTheory.CART_EQ,
      word_lsl_def,word_lsr_def,fcpTheory.FCP_BETA,w2w]
  \\ rw [] \\ fs [] \\ EQ_TAC \\ rw [] \\ rfs [fcpTheory.FCP_BETA,w2w]
QED

fun sort_tac n =
  CONV_TAC(PATH_CONV(String.concat(List.tabulate(n,(K "lr"))))(REWR_CONV set_byte_sort)) \\
  simp[good_dimindex_def]

Theorem evaluate_WriteLastBytes:
   arch_width_bits c.arch_width = dimindex(:'a) ∧ good_dimindex(:'a) ∧ w2n n < dimindex(:'a) DIV 8 ∧
   get_vars [av;bv;nv] (s:('a,'c,'ffi)wordSem$state) = SOME [Word (a:'a word); Word b; Word n] ∧
   byte_aligned a ∧ a ∈ s.mdomain ∧ s.memory a = Word w
  ⇒
   evaluate (WriteLastBytes c av bv nv,s) =
     (NONE, s with memory := (a =+ Word (last_bytes (w2n n) (w2w b) 0w w s.be)) s.memory)
Proof
  rw[good_dimindex_def]
  \\ fs[get_vars_SOME_IFF]
  \\ simp[WriteLastBytes_def]
  \\ simp[WriteLastByte_aux_def]
  \\ map_every (let
      val th = CONV_RULE(RESORT_FORALL_CONV(sort_vars["p","b"])) align_add_aligned
      val th = Q.SPEC`LOG2 (dimindex(:'a) DIV 8)`th
      val th2 = set_byte_change_a |> Q.GEN`b` |> Q.SPEC`w2w b` |> Q.GENL[`be`,`a`,`a'`,`w`]
      in (fn n =>
       let val nw = Int.toString n ^ "w" in
         qspecl_then([[QUOTE nw],`a`])mp_tac th \\
         qspecl_then([`s.be`,[QUOTE (nw^"+ byte_align a")], [QUOTE nw]])mp_tac th2
       end) end)
       (List.tabulate(8,I))
  \\ simp_tac std_ss [GSYM byte_align_def,GSYM byte_aligned_def]
  \\ fs[w2n_add_byte_align_lemma,good_dimindex_def]
  \\ fs[dimword_def]
  \\ rpt strip_tac
  \\ fs[wordSemTheory.evaluate_def,wordSemTheory.inst_def,
        wordSemTheory.get_var_imm_def,
        word_exp_rw, wordSemTheory.get_var_def,
        asmTheory.word_cmp_def,last_bytes_simp,
        wordSemTheory.mem_store_byte_aux_def,
        APPLY_UPDATE_THM]
  \\ rw[wordSemTheory.state_component_equality,
        FUN_EQ_THM,APPLY_UPDATE_THM,
        dimword_def, last_bytes_simp]
  \\ rw[] \\ rw[] \\ rfs[dimword_def]
  >- ( simp[Once set_byte_sort,good_dimindex_def] )
  >- ( map_every sort_tac [1,2,1])
  >- ( Cases_on`n` \\ fs[dimword_def] \\ rfs[] )
  >- ( simp[Once set_byte_sort,good_dimindex_def] )
  >- ( map_every sort_tac [1,2,1] )
  >- ( map_every sort_tac [1,2,3,2,1,2] )
  >- ( map_every sort_tac [1,2,3,4,3,2,1,2,3,2] )
  >- ( map_every sort_tac [1,2,3,4,5,4,3,2,1,2,3,4,3,2,3] )
  >- ( map_every sort_tac [1,2,3,4,5,6,5,4,3,2,1,2,3,4,5,4,3,2,3,4,5,4,3,4,3,4,5] )
  >- ( Cases_on`n` \\ fs[dimword_def] \\ rfs[] )
QED

Theorem byte_aligned_bytes_in_word:
   good_dimindex (:'a) ==>
    byte_aligned (w * bytes_in_word) /\
    byte_aligned (bytes_in_word * w:'a word)
Proof
  fs [byte_aligned_def,good_dimindex_def] \\ rw []
  \\ fs [bytes_in_word_def]
  \\ `aligned 2 (0w + w * n2w (2 ** 2)) /\
      aligned 3 (0w + w * n2w (2 ** 3))` by
    (Cases_on `w` \\ rewrite_tac [word_mul_n2w,aligned_add_pow,aligned_0])
  \\ fs []
QED

Theorem ADD4DIV4[local] =
  ADD_DIV_ADD_DIV |> Q.SPEC `4` |> SIMP_RULE std_ss []
  |> Q.SPEC `1` |> SIMP_RULE std_ss[]
  |> Q.SPEC `i` |> PURE_ONCE_REWRITE_RULE [ADD_SYM];

Theorem ADD8DIV8[local] =
  ADD_DIV_ADD_DIV |> Q.SPEC `8` |> SIMP_RULE std_ss []
  |> Q.SPEC `1` |> SIMP_RULE std_ss[]
  |> Q.SPEC `i` |> PURE_ONCE_REWRITE_RULE [ADD_SYM];

Theorem RefByte_thm:
   state_rel c l1 l2 s (t:('a,'c,'ffi) wordSem$state) NONE locs /\
    get_vars [0;1;2] s.locals = SOME (vals ++ [Number &(if fl then 0 else 8)]) /\
    t.clock = MustTerminate_limit (:'a) - 1 /\
    pop_env s = SOME s1 /\ is_env(HD s.stack) /\
    s.locals_size = lookup RefByte_location s.stack_frame_sizes /\
    do_app (MemOp (RefByte fl)) vals s1 = Rval (v,s2) ==>
    ?q r new_c.
      evaluate (RefByte_code c,t) = (q,r) /\
      if q = SOME NotEnoughSpace then
        r.ffi = t.ffi ∧
        option_le r.stack_max s2.stack_max /\
        (c.gc_kind <> None ∧ no_thunks_in_refs s.refs ==>
         case vals of
              (Number i::_) =>
              (i < 0 \/
              ~small_num s.limits.arch_64_bit i \/
              ~(Num i DIV (arch_size s.limits DIV 8) < dimword (:α) DIV arch_size s.limits) \/
              ~(Num i DIV (arch_size s.limits DIV 8) + 1 < (2 ** c.len_size)) \/
              s1.limits.heap_limit <
              size_of_heap s1 + Num i DIV (arch_size s.limits DIV 8) + 2)
         )
      else
        ?rv. q = SOME (Result (Loc l1 l2) [rv]) /\
             state_rel c r1 r2 (s2 with <| locals := LN;
                                           locals_size := SOME 0;
                                           clock := new_c;
                                           stack := s.stack |>)
                r (SOME [(v,rv)]) locs
Proof
  qpat_abbrev_tac`tag = if fl then _ else _`
  \\ fs [RefByte_code_def,GSYM dimword_def]
  \\ fs [do_app_def,do_space_def,EVAL ``op_space_reset (MemOp (RefByte fl))``,do_app_aux_def]
  \\ Cases_on `vals` \\ fs []
  \\ Cases_on `t'` \\ fs []
  \\ Cases_on `h` \\ fs []
  \\ Cases_on `t''` \\ fs []
  \\ Cases_on `h'` \\ fs []
  \\ IF_CASES_TAC \\ fs [] \\ rw []
  \\ imp_res_tac state_rel_arch_width
  \\ `arch_bytes c.arch_width = dimindex(:α) DIV 8` by
       (Cases_on `c.arch_width` \\ gvs[asmTheory.arch_bytes_def,asmTheory.arch_width_bits_def]
        \\ qpat_x_assum `_ = dimindex(:α)` (assume_tac o SYM) \\ fs[])
  \\ fs[GSYM dimword_def]
  \\ `good_dimindex (:'a)` by fs [state_rel_def]
  \\ drule0 NONNEG_INT \\ strip_tac \\ rveq \\ fs []
  \\ rename1 `get_vars [0; 1; 2] s.locals = SOME [Number (&i); Number (&w2n w); Number &tag]`
  \\ once_rewrite_tac [list_Seq_def]
  \\ fs [wordSemTheory.evaluate_def,word_exp_rw,GSYM bytes_in_word_def]
  \\ rpt_drule0 state_rel_get_vars_IMP \\ strip_tac \\ fs [LENGTH_EQ_NUM_compute]
  \\ rveq \\ fs [adjust_var_def,get_vars_SOME_IFF]
  \\ fs [get_vars_SOME_IFF_data]
  \\ drule0 (Q.GEN`a1`(Q.SPEC `0` state_rel_get_var_Number_IMP_alt)) \\ fs []
  \\ strip_tac \\ rveq
  \\ rpt_drule0 evaluate_BignumHalt2
  \\ reverse (Cases_on `small_int (dimindex (:α)) (&i)` \\ fs [] \\ strip_tac \\ fs [])
  >-
    (conj_tac >-
       (fs[do_stack_def,stack_consumed_def,state_rel_def,pop_env_def,CaseEq"option",
           CaseEq"list",CaseEq"stack"]>>rveq>>
        match_mp_tac option_le_trans>>asm_exists_tac>>fs[]>>
        match_mp_tac option_le_trans>>asm_exists_tac>>fs[]>>
        simp[option_le_max_right]) >>
     strip_tac >> spose_not_then strip_assume_tac >>
     fs[small_int_def,state_rel_def,good_dimindex_def,limits_inv_def,arch_size_def,dimword_def,
        pop_env_def,CaseEq"option",CaseEq"list",CaseEq"stack"] >>
     rveq >> rfs[] >> fs[DIV_LT_X])
  \\ ntac 3 (pop_assum kall_tac)
  \\ once_rewrite_tac [list_Seq_def]
  \\ fs [wordSemTheory.evaluate_def,word_exp_rw,GSYM bytes_in_word_def]
  \\ rpt_drule0 state_rel_get_vars_IMP \\ strip_tac \\ fs [LENGTH_EQ_2]
  \\ rveq \\ fs [adjust_var_def,get_vars_SOME_IFF]
  \\ fs [wordSemTheory.get_var_def]
  \\ `w' = n2w (2 * i) /\ 2 * i < dimword (:'a)` by
   (fs [state_rel_thm]
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ qpat_x_assum `get_var 0 s.locals = SOME (Number (&i))` assume_tac
    \\ rpt_drule0 memory_rel_get_var_IMP \\ fs [adjust_var_def]
    \\ fs [wordSemTheory.get_var_def]
    \\ strip_tac \\ imp_res_tac memory_rel_Number_IMP
    \\ fs [Smallnum_def] \\ fs [small_int_def,GSYM dimword_def] \\ fs [X_LT_DIV] \\ NO_TAC)
  \\ rveq
  \\ `shift (dimindex (:'a)) - 1 < dimindex (:'a)` by
       (assume_tac DIMINDEX_GT_0 \\ rw [shift_def] \\ fs [good_dimindex_def])
  \\ fs [word_exp_SmallLsr]
  \\ `2 < dimword (:'a)` by
       (assume_tac dimindex_lt_dimword \\
        fs [good_dimindex_def] \\ decide_tac)
  \\ `shift (dimindex (:'a)) < dimword (:'a)` by
       (assume_tac dimindex_lt_dimword \\
        rw [shift_def] \\ fs [good_dimindex_def] \\ decide_tac)
  \\ `shift_length c − shift (dimindex (:'a)) < dimword (:'a)` by
       (assume_tac dimindex_lt_dimword \\
        `shift_length c < dimindex (:'a)` suffices_by decide_tac \\
        fs [state_rel_def])
  \\ `dimindex (:'a) − shift (dimindex (:'a)) − c.len_size < dimword (:'a)` by
       (assume_tac dimindex_lt_dimword \\ decide_tac)
  \\ fs [word_exp_rw,GSYM bytes_in_word_def]
  \\ IF_CASES_TAC
  THEN1 (fs [good_dimindex_def] \\ NO_TAC) \\ fs []
  \\ pop_assum kall_tac
  \\ `n2w (2 * i) ⋙ 1 = (n2w i):'a word` by
   (rewrite_tac [GSYM w2n_11,w2n_lsr]
    \\ fs [ONCE_REWRITE_RULE [MULT_COMM] MULT_DIV] \\ NO_TAC) \\ fs []
  \\ qabbrev_tac `wA = ((bytes_in_word + n2w i)
        ⋙ (shift (dimindex (:α)) − 1)):'a word`
  \\ once_rewrite_tac [list_Seq_def]
  \\ fs [wordSemTheory.evaluate_def,word_exp_rw,GSYM bytes_in_word_def]
  \\ `state_rel c l1 l2 s (set_var 1 (Word wA) t) NONE locs` by
        fs [wordSemTheory.set_var_def,state_rel_insert_1]
  \\ rpt_drule0 AllocVar_thm
  \\ `?x. dataSem$cut_env (fromList [();();()]) s.locals = SOME x` by
    (fs [EVAL ``sptree$fromList [(); (); ()]``,cut_env_def,domain_lookup,
         get_var_def,get_vars_SOME_IFF_data] \\ NO_TAC)
  \\ disch_then drule0
  \\ fs [wordSemTheory.get_vars_def,wordSemTheory.get_var_def]
  \\ qabbrev_tac `limit = MIN (2 ** c.len_size) (dimword (:α) DIV 16)`
  \\ fs [get_var_set_var_thm]
  \\ Cases_on `evaluate
       (AllocVar c limit (fromList [(); (); ()]),set_var 1 (Word wA) t)` \\ fs []
  \\ disch_then drule0
  \\ impl_tac THEN1 (unabbrev_all_tac \\ fs []
                     \\ fs [state_rel_def,EVAL ``good_dimindex (:'a)``,dimword_def])
  \\ strip_tac \\ fs [set_vars_sing]
  \\ reverse IF_CASES_TAC \\ fs []
  >- (fs[do_stack_def,option_le_max_right,pop_env_def,CaseEq"list",CaseEq"stack"] >>
      rveq >> fs[] >> rfs[is_env_def] >>
      strip_tac >>
      spose_not_then strip_assume_tac >>
      `w2n wA DIV 2 < limit`
        by(fs[Abbr`wA`,Abbr`limit`,state_rel_def,limits_inv_def,good_dimindex_def] >>
           rfs[dimword_def] >>
           fs[] >>
           `~word_msb(bytes_in_word:'a word)`
             by(fs[word_msb_def,bytes_in_word_def] >>
                wordsLib.WORD_EVAL_TAC >> rw[]) >>
           `~word_msb(n2w i)`
             by(fs[word_msb_def,bytes_in_word_def] >>
                wordsLib.WORD_EVAL_TAC >> rw[] >>
                match_mp_tac bitTheory.NOT_BIT_GT_TWOEXP >>
                fs[]) >>
           simp[w2n_add,dimword_def,w2n_lsr,shift_def] >>
           simp[bytes_in_word_def,dimword_def,DIV_DIV_DIV_MULT] >>
           simp[ADD4DIV4,ADD8DIV8] >>
           rfs[arch_size_def,limits_inv_def] >>
           rewrite_tac [arithmeticTheory.EXP] >>
           strip_assume_tac (Q.SPEC `i` (MATCH_MP DIVISION (DECIDE ``0 < 4n``))) >>
           strip_assume_tac (Q.SPEC `i` (MATCH_MP DIVISION (DECIDE ``0 < 8n``))) >>
           strip_assume_tac (Q.SPEC `i + 8` (MATCH_MP DIVISION (DECIDE ``0 < 4n``))) >>
           strip_assume_tac (Q.SPEC `i + 4` (MATCH_MP DIVISION (DECIDE ``0 < 2n``))) >>
           decide_tac) >>
      fs[space_consumed_def] >>
      `size_of_heap (cut_locals (fromList [(); (); ()]) s) =
       size_of_heap
             (s with <|locals := e; locals_size := ss; stack := xs|>)`
        by(fs[cut_locals_def,cut_env_def,size_of_heap_def,
              stack_to_vs_def,extract_stack_def
             ] >> rveq >>
           fs[fromList_def] >>
           rfs[] >>
           `inter s.locals (fromList [();();()]) =
            inter (insert 2 (THE(lookup 2 s.locals))
                   (insert 1 (THE(lookup 1 s.locals))
                    (insert 0 (THE(lookup 0 s.locals)) LN)))
                   (fromList [();();()])`
            by(fs[dataSemTheory.get_var_def] >>
               rw[inter_eq,lookup_inter,lookup_insert,lookup_fromList] >>
               fs[] >>
               fs[lookup_def] >> TOP_CASE_TAC >> rw[]) >>
           pop_assum(SUBST_ALL_TAC o SIMP_RULE list_ss [fromList_def]) >>
           rpt(CHANGED_TAC(simp[Once insert_def])) >>
           simp[inter_def,mk_BS_def,toList_def] >>
           fs[toList_def,toListA_def,dataSemTheory.get_var_def] >>
           `small_num s.limits.arch_64_bit (&tag)` by rw[small_num_def,Abbr `tag`] >>
           `small_num s.limits.arch_64_bit (&w2n w)`
             by(fs[small_num_def,small_int_def] >> rw[] >>
                match_mp_tac LESS_TRANS >>
                qexists_tac `dimword(:8)` >>
                (conj_tac >- MATCH_ACCEPT_TAC w2n_lt) >>
                rw[]) >>
           simp[size_of_Number_head]) >>
      fs[] >>
      fs[Abbr`wA`,Abbr`limit`,state_rel_def,good_dimindex_def] >>
      rfs[dimword_def] >>
      fs[] >>
      `~word_msb(bytes_in_word:'a word)`
        by(fs[word_msb_def,bytes_in_word_def] >>
           wordsLib.WORD_EVAL_TAC >> rw[]) >>
      `~word_msb(n2w i)`
        by(fs[word_msb_def,bytes_in_word_def] >>
           wordsLib.WORD_EVAL_TAC >> rw[] >>
           match_mp_tac bitTheory.NOT_BIT_GT_TWOEXP >>
           fs[]) >>
      fs[w2n_add,dimword_def,w2n_lsr,arch_size_def,limits_inv_def,shift_def] >>
      rfs[bytes_in_word_def,dimword_def,DIV_DIV_DIV_MULT] >>
      fs[ADD4DIV4,ADD8DIV8] >>
      fs[NOT_LESS] >>
      drule_then drule LESS_EQ_LESS_TRANS >>
      rpt(pop_assum kall_tac) >> rw[] >>
      rw[DIV_LT_X] >> intLib.COOPER_TAC)
  \\ rveq \\ fs []
  \\ fs [dataSemTheory.call_env_def,push_env_def,
         dataSemTheory.set_var_def,wordSemTheory.set_var_def]
  \\ qabbrev_tac `new = LEAST ptr. ptr ∉ domain s.refs`
  \\ `new ∉ domain s.refs` by metis_tac [LEAST_NOTIN_spt_DOMAIN]
  \\ fs [] \\ once_rewrite_tac [list_Seq_def]
  \\ fs [] \\ once_rewrite_tac [list_Seq_def]
  \\ fs [] \\ once_rewrite_tac [list_Seq_def]
  \\ once_rewrite_tac [wordSemTheory.evaluate_def]
  \\ simp [Once wordSemTheory.evaluate_def]
  \\ fs [word_exp_rw,GSYM bytes_in_word_def]
  \\ `lookup 2 r.locals = SOME (Word (n2w (2 * i)))` by
   (qabbrev_tac `s9 = s with <|locals := x; space := w2n wA DIV 2 + 1|>`
    \\ fs [state_rel_def,get_vars_SOME_IFF_data]
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,get_var_def]
    \\ rpt_drule0 word_ml_inv_get_var_IMP
    \\ fs [get_var_def,wordSemTheory.get_var_def,adjust_var_def]
    \\ `lookup 0 s9.locals = SOME (Number (&i))` by
     (unabbrev_all_tac \\ fs [cut_env_def] \\ rveq
      \\ fs [lookup_inter_alt] \\ EVAL_TAC)
    \\ rpt (disch_then drule0) \\ fs []
    \\ `IS_SOME (lookup 0 s9.locals)` by fs []
    \\ res_tac \\ Cases_on `lookup 2 r.locals` \\ fs []
    \\ fs [word_ml_inv_def] \\ rw []
    \\ fs [abs_ml_inv_def,bc_stack_ref_inv_def,v_inv_def] \\ rfs []
    \\ rw [] \\ fs [word_addr_def,Smallnum_def]
    \\ fs [small_int_def,X_LT_DIV]
    \\ match_mp_tac minus_2_word_and_id
    \\ fs [word_index,word_mul_n2w,bitTheory.BIT0_ODD,ODD_MULT] \\ NO_TAC)
  \\ `~(2 ≥ dimindex (:α))` by (fs [good_dimindex_def] \\ NO_TAC)
  \\ `shift (dimindex (:α)) ≠ 0 /\ ~(shift (dimindex (:α)) ≥ dimindex (:α))` by
        (rw [shift_def] \\ fs [good_dimindex_def] \\ NO_TAC)
  \\ simp []
  \\ simp [Once wordSemTheory.evaluate_def]
  \\ simp [Once wordSemTheory.evaluate_def]
  \\ simp [Once wordSemTheory.evaluate_def]
  \\ simp [Once wordSemTheory.evaluate_def]
  \\ fs [word_exp_rw,GSYM bytes_in_word_def]
  \\ `(?free. FLOOKUP r.store NextFree = SOME (Word free)) /\
      (?eoh1. FLOOKUP r.store EndOfHeap = SOME (Word eoh1)) /\
      (?cur1. FLOOKUP r.store CurrHeap = SOME (Word cur1))` by
        (fs [state_rel_thm,memory_rel_def,heap_in_memory_store_def] \\ NO_TAC)
  \\ fs []
  \\ `lookup 4 r.locals = SOME (Word (w2w w << 1))` by
   (qabbrev_tac `s9 = s with <|locals := x; space := w2n wA DIV 2 + 1|>`
    \\ fs [state_rel_def,get_vars_SOME_IFF_data]
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,get_var_def]
    \\ rpt_drule0 word_ml_inv_get_var_IMP
    \\ fs [get_var_def,wordSemTheory.get_var_def,adjust_var_def]
    \\ `lookup 1 s9.locals = SOME (Number (&w2n w))` by
     (unabbrev_all_tac \\ fs [cut_env_def] \\ rveq
      \\ fs [lookup_inter_alt] \\ EVAL_TAC)
    \\ rpt (disch_then drule0) \\ fs []
    \\ `IS_SOME (lookup 1 s9.locals)` by fs []
    \\ res_tac \\ Cases_on `lookup 4 r.locals` \\ fs []
    \\ fs [word_ml_inv_def] \\ rw []
    \\ fs [abs_ml_inv_def,bc_stack_ref_inv_def,v_inv_def] \\ rfs []
    \\ rw [] \\ fs [word_addr_def,Smallnum_def]
    \\ fs [word_mul_n2w,w2w_def,WORD_MUL_LSL]
    \\ fs [small_int_def,X_LT_DIV]
    \\ match_mp_tac minus_2_word_and_id
    \\ fs [word_index,word_mul_n2w,bitTheory.BIT0_ODD,ODD_MULT] \\ NO_TAC)
  \\ `lookup 6 r.locals = SOME (Word (n2w (2 * tag)))` by
   (qabbrev_tac `s9 = s with <|locals := x; space := w2n wA DIV 2 + 1|>`
    \\ fs [state_rel_def,get_vars_SOME_IFF_data]
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,get_var_def]
    \\ rpt_drule0 word_ml_inv_get_var_IMP
    \\ fs [get_var_def,wordSemTheory.get_var_def,adjust_var_def]
    \\ `lookup 2 s9.locals = SOME (Number &tag)` by
     (unabbrev_all_tac \\ fs [cut_env_def] \\ rveq
      \\ fs [lookup_inter_alt] \\ EVAL_TAC)
    \\ rpt (disch_then drule0) \\ fs []
    \\ `IS_SOME (lookup 2 s9.locals)` by fs []
    \\ res_tac \\ Cases_on `lookup 6 r.locals` \\ fs []
    \\ fs [word_ml_inv_def] \\ rw []
    \\ fs [abs_ml_inv_def,bc_stack_ref_inv_def,v_inv_def] \\ rfs []
    \\ `small_int (dimindex (:'a)) (&tag)`
    by (
      rw[small_int_def,Abbr`tag`]
      \\ fs[good_dimindex_def,dimword_def] )
    \\ fs[word_addr_def,Smallnum_def]
    \\ match_mp_tac minus_2_word_and_id
    \\ simp[word_index,bitTheory.BIT0_ODD,ODD_MULT]
    \\ NO_TAC)
  \\ fs [wordSemTheory.set_var_def,lookup_insert]
  \\ fs [] \\ once_rewrite_tac [list_Seq_def]
  \\ fs [wordSemTheory.evaluate_def,word_exp_rw,GSYM bytes_in_word_def,wordSemTheory.set_var_def]
  \\ once_rewrite_tac [list_Seq_def]
  \\ fs [wordSemTheory.evaluate_def,word_exp_rw,GSYM bytes_in_word_def,wordSemTheory.set_var_def,
         wordSemTheory.set_store_def]
  \\ once_rewrite_tac [list_Seq_def]
  \\ fs [wordSemTheory.evaluate_def,word_exp_rw,GSYM bytes_in_word_def,wordSemTheory.set_var_def,
         wordSemTheory.set_store_def,FLOOKUP_UPDATE]
  \\ IF_CASES_TAC
  THEN1 (fs [shift_def,shift_length_def,state_rel_def,
                 EVAL ``good_dimindex (:'a)``] \\ fs [])
  \\ pop_assum kall_tac \\ fs []
  \\ qabbrev_tac `var5 = (bytes_in_word + n2w i:'a word) ⋙ shift (dimindex (:α))`
  \\ once_rewrite_tac [list_Seq_def]
  \\ fs [wordSemTheory.evaluate_def,word_exp_rw,GSYM bytes_in_word_def,wordSemTheory.set_var_def,
         wordSemTheory.set_store_def]
  \\ once_rewrite_tac [list_Seq_def]
  \\ fs [wordSemTheory.evaluate_def,word_exp_rw,GSYM bytes_in_word_def,wordSemTheory.set_var_def,
         wordSemTheory.set_store_def]
  \\ fs [evaluate_MakeBytes,word_exp_rw,GSYM bytes_in_word_def,wordSemTheory.set_var_def,
         lookup_insert,wordSemTheory.get_var_def,w2w_shift_shift]
  \\ qpat_assum `state_rel c l1 l2 _ _ _ _` mp_tac
  \\ simp_tac std_ss [Once state_rel_thm] \\ strip_tac \\ fs []
  \\ `w2n wA DIV 2 = byte_len (dimindex (:'a)) i` by
   (unabbrev_all_tac \\ fs [byte_len_def,bytes_in_word_def,w2n_lsr,shift_def,
      good_dimindex_def,word_add_n2w,dimword_def] \\ rfs []
    \\ fs [GSYM word_add_n2w] \\ fs [word_add_n2w,dimword_def]
    \\ fs [ADD_DIV_EQ,DIV_DIV_DIV_MULT] \\ NO_TAC)
  \\ fs [wordSemTheory.set_var_def,lookup_insert]
  \\ rpt_drule0 memory_rel_RefByte_alt
  \\ disch_then (qspecl_then [`w`,`i`,`fl`] mp_tac) \\ fs []
  \\ impl_tac THEN1
   (unabbrev_all_tac \\ fs []
    \\ fs [good_dimindex_def,dimword_def] \\ rfs [])
  \\ strip_tac \\ fs [FLOOKUP_DEF] \\ rveq \\ clean_tac
  \\ `var5 = n2w (byte_len (dimindex (:α)) i)` by
   (unabbrev_all_tac
    \\ rewrite_tac [GSYM w2n_11,w2n_lsr,byte_len_def]
    \\ fs [bytes_in_word_def,shift_def,good_dimindex_def]
    \\ fs [word_add_n2w,ADD_DIV_EQ]
    THEN1
     (sg `i + 4 < dimword (:'a)`
      \\ sg `i + 4 DIV 4 < dimword (:'a)` \\ fs []
      \\ rfs [dimword_def] \\ fs [DIV_LT_X])
    THEN1
     (sg `i + 8 < dimword (:'a)`
      \\ sg `i + 8 DIV 8 < dimword (:'a)` \\ fs []
      \\ rfs [dimword_def] \\ fs [DIV_LT_X]))
  \\ fs [] \\ rveq
  \\ once_rewrite_tac [list_Seq_def]
  \\ fs [wordSemTheory.evaluate_def,word_exp_rw,GSYM bytes_in_word_def,wordSemTheory.set_var_def,
         wordSemTheory.set_store_def,wordSemTheory.get_var_def,lookup_insert,
         wordSemTheory.mem_store_def,store_list_def]
  \\ once_rewrite_tac [list_Seq_def]
  \\ simp[Once wordSemTheory.evaluate_def,
          wordSemTheory.get_var_def,lookup_insert,
          wordSemTheory.get_var_imm_def,
          asmTheory.word_cmp_def]
  \\ rfs [shift_lsl,GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
  \\ qpat_abbrev_tac `ppp = Word (_ || _:'a word)`
  \\ sg `ppp = Word (n2w (make_byte_header c fl i))`
  >- (`arch_width_bits c.arch_width = dimindex (:α) /\
   c.len_size + 9 < dimindex (:α)` by
    fs [memory_rel_def,heap_in_memory_store_def]
  \\ unabbrev_all_tac \\ fs [make_byte_header_def,bytes_in_word_def]
  \\ Cases_on `c.arch_width`
  \\ Cases_on `fl`
  \\ qpat_x_assum `arch_width_bits _ = dimindex (:α)` mp_tac
  \\ qpat_x_assum `c.len_size + 9 < dimindex (:α)` mp_tac
  \\ rpt (pop_assum kall_tac)
  \\ simp[asmTheory.arch_width_bits_def]
  \\ strip_tac
  \\ disch_then (fn th => (SUBST_ALL_TAC (GSYM th) \\ assume_tac th))
  \\ simp[shift_def,GSYM word_add_n2w,WORD_MUL_LSL]
  \\ simp[word_mul_n2w,word_add_n2w,RIGHT_ADD_DISTRIB]
  \\ once_rewrite_tac [GSYM RIGHT_ADD_DISTRIB]
  \\ once_rewrite_tac [header_sum_reassoc]
  \\ irule multiplied_header_or \\ fs [])
  \\ rveq \\ pop_assum kall_tac
  \\ fs [wordSemTheory.evaluate_def,word_exp_rw,GSYM bytes_in_word_def,
         wordSemTheory.get_var_def,lookup_insert,
         wordSemTheory.mem_store_def,store_list_def]
  \\ once_rewrite_tac[list_Seq_def]
  \\ simp[wordSemTheory.evaluate_def,word_exp_rw,GSYM bytes_in_word_def]
  \\ simp[wordSemTheory.set_var_def]
  \\ once_rewrite_tac[list_Seq_def]
  \\ simp[wordSemTheory.evaluate_def,word_exp_rw,GSYM bytes_in_word_def,
          asmTheory.word_cmp_def,wordSemTheory.get_var_def]
  \\ `(bytes_in_word:'a word) + -1w = n2w (2 ** shift (dimindex (:'a)) - 1)`
  by ( fs[bytes_in_word_def,good_dimindex_def,shift_def] )
  \\ simp[WORD_AND_EXP_SUB1]
  \\ `i MOD 2 ** (shift (dimindex (:'a))) < dimword(:'a)`
  by (
    match_mp_tac LESS_LESS_EQ_TRANS
    \\ qexists_tac`2 ** shift (dimindex (:'a))`
    \\ simp[]
    \\ fs[good_dimindex_def,dimword_def,shift_def] )
  \\ simp[]
  \\ `2 ** shift (dimindex (:'a)) = dimindex(:'a) DIV 8`
    by ( fs[good_dimindex_def,dimword_def,shift_def] )
  \\ simp[]
  \\ simp[(* CONJUNCT2 (CONJUNCT2 list_Seq_def), *)
          wordSemTheory.evaluate_def,word_exp_rw,GSYM bytes_in_word_def,
          wordSemTheory.set_var_def,
          wordSemTheory.mem_store_def,
          wordSemTheory.get_var_def,lookup_insert]
  \\ reverse IF_CASES_TAC
  >- (
    `F` suffices_by rw[]
    \\ pop_assum mp_tac \\ simp []
    \\ imp_res_tac store_list_domain
    \\ fs[LENGTH_REPLICATE]
    \\ first_x_assum(qspec_then`byte_len (dimindex (:'a)) i-1`mp_tac)
    \\ simp[]
    \\ fs[WORD_MUL_LSL,word_mul_n2w]
    \\ Cases_on`byte_len (dimindex (:'a)) i = 0` \\ fs[]
    \\ Cases_on`byte_len (dimindex (:'a)) i` \\ fs[ADD1,GSYM word_add_n2w]
    \\ simp[WORD_MULT_CLAUSES,WORD_LEFT_ADD_DISTRIB]
    \\ NO_TAC)
  \\ fs[]
  \\ simp[CONJUNCT2 (CONJUNCT2 list_Seq_def),
          wordSemTheory.evaluate_def,word_exp_rw,GSYM bytes_in_word_def,
          wordSemTheory.set_var_def,
          wordSemTheory.mem_store_def,
          wordSemTheory.get_var_def,lookup_insert]
  \\ pairarg_tac \\ fs[]
  \\ pairarg_tac \\ fs[]
  \\ pop_assum mp_tac
  \\ pop_assum mp_tac
  \\ assume_tac(GEN_ALL evaluate_WriteLastBytes)
  \\ SEP_I_TAC "evaluate"
  \\ pop_assum mp_tac
  \\ simp[wordSemTheory.get_vars_def,wordSemTheory.get_var_def,lookup_insert,APPLY_UPDATE_THM]
  \\ impl_tac
  >- (
    TRY (conj_tac >- fs[good_dimindex_def])
    \\ fs[memory_rel_def,heap_in_memory_store_def,FLOOKUP_UPDATE]
    \\ fs[FLOOKUP_DEF]
    \\ qpat_x_assum `free' + bytes_in_word + _ = _` mp_tac
    \\ simp_tac std_ss [WORD_ADD_EQ_SUB]
    \\ simp[aligned_add_sub] \\ rpt strip_tac \\ rveq
    \\ fs [byte_aligned_def]
    \\ rewrite_tac [GSYM WORD_ADD_ASSOC]
    \\ (alignmentTheory.aligned_add_sub_cor
          |> SPEC_ALL |> UNDISCH_ALL |> CONJUNCT1 |> DISCH_ALL |> match_mp_tac)
    \\ fs []
    \\ (alignmentTheory.aligned_add_sub_cor
          |> SPEC_ALL |> UNDISCH_ALL |> CONJUNCT1 |> DISCH_ALL |> match_mp_tac)
    \\ fs [GSYM byte_aligned_def]
    \\ fs [byte_aligned_bytes_in_word])
  \\ simp[] \\ disch_then kall_tac
  \\ strip_tac \\ fs[] \\ clean_tac \\ fs[]
  \\ fs [lookup_insert]
  \\ strip_tac \\ rveq \\ fs []
  \\ pop_assum mp_tac \\ simp[list_Seq_def]
  \\ strip_tac \\ clean_tac \\ fs[]
  \\ `(?md. lookup Replicate_location r.code = SOME (5,Replicate_code c,md))` by
         (imp_res_tac lookup_RefByte_location \\ fs [] \\ NO_TAC) \\ rfs []
  \\ qmatch_asmsub_abbrev_tac`LUPDATE lw (len-1) ls`
  \\ qmatch_assum_abbrev_tac`Abbrev(ls = REPLICATE len rw)`
  \\ `0 < len` by ( Cases_on`len` \\ fs[byte_len_def,markerTheory.Abbrev_def] )
  \\ `ls = REPLICATE (len-1) rw ++ [rw] ++ []`
  by (
    simp[Abbr`ls`,LIST_EQ_REWRITE,EL_REPLICATE,LENGTH_REPLICATE]
    \\ qx_gen_tac`z` \\ strip_tac
    \\ Cases_on`z = len-1` \\ simp[EL_APPEND1,EL_APPEND2,EL_REPLICATE,LENGTH_REPLICATE] )
  \\ `LUPDATE lw (len-1) ls = REPLICATE (len-1) rw ++ [lw] ++ []` by metis_tac[lupdate_append2,LENGTH_REPLICATE]
  \\ pop_assum SUBST_ALL_TAC
  \\ pop_assum kall_tac \\ fs[]
  \\ imp_res_tac store_list_append_imp
  \\ assume_tac (GEN_ALL Replicate_code_thm)
  \\ SEP_I_TAC "evaluate"
  \\ pop_assum mp_tac \\ fs[wordSemTheory.get_var_def,lookup_insert]
  \\ simp[UPDATE_EQ]
  \\ qmatch_goalsub_abbrev_tac`(a' =+ v)`
  \\ qhdtm_x_assum`store_list`mp_tac
  \\ drule0 (Q.GEN`a'`store_list_update_m_outside)
  \\ disch_then(qspec_then`a'`mp_tac)
  \\ impl_tac
  >- (
    simp[Abbr`a'`,LENGTH_REPLICATE]
    \\ rewrite_tac[GSYM WORD_ADD_ASSOC]
    \\ simp[WORD_EQ_ADD_LCANCEL]
    \\ CONV_TAC(PATH_CONV"brrlrr"(REWR_CONV WORD_MULT_COMM))
    \\ rewrite_tac[GSYM WORD_MULT_ASSOC]
    \\ `len < dimword (:α) DIV 16` by
          (unabbrev_all_tac \\ fs [])
    \\ qpat_x_assum `good_dimindex (:'a)` mp_tac
    \\ pop_assum mp_tac
    \\ rpt (pop_assum kall_tac)
    \\ fs [good_dimindex_def] \\ rw [] \\ fs [bytes_in_word_def]
    \\ fs [word_add_n2w,word_mul_n2w,dimword_def])
  \\ ntac 2 strip_tac \\ rfs []
  \\ disch_then drule0 \\ simp []
  \\ disch_then drule0
  \\ impl_tac THEN1 (
    simp[Abbr`len`,WORD_MUL_LSL,word_mul_n2w,LEFT_SUB_DISTRIB,n2w_sub]
    \\ fs [good_dimindex_def,dimword_def,state_rel_thm] \\ rfs []
    \\ unabbrev_all_tac \\ fs []
    \\ `byte_len (dimindex (:α)) i -1 < dimword (:'a)` by (fs [dimword_def])
    \\ imp_res_tac IMP_LESS_MustTerminate_limit \\ fs[] \\ rfs[])
  \\ strip_tac \\ fs []
  \\ qpat_x_assum`evaluate _ = (SOME _,_)` mp_tac
  \\ simp [WORD_MUL_LSL,n2w_sub,GSYM word_mul_n2w,WORD_LEFT_ADD_DISTRIB]
  \\ strip_tac
  \\ simp [state_rel_thm]
  \\ fs []
  \\ fs [lookup_def]
  \\ qhdtm_x_assum `memory_rel` mp_tac
  \\ fs [EVAL ``join_env LN []``,code_oracle_rel_def,FLOOKUP_UPDATE]
  \\ fs[store_list_def]
  \\ fs[Abbr`a'`,Abbr`v`,LENGTH_REPLICATE]
  \\ clean_tac
  \\ fs[make_ptr_def,WORD_MUL_LSL]
  \\ strip_tac
  \\ fs[CaseEq"list",pop_env_def,CaseEq"stack",is_env_def] >> rveq >> fs[] >> rfs[]
  \\ conj_asm1_tac >- (
     drule wordPropsTheory.evaluate_stack_max_le
     \\ fs [wordSemTheory.state_fn_updates]
     \\ drule  option_le_add_indv
     \\ metis_tac [option_le_trans])
  \\ conj_tac >- (
     drule wordPropsTheory.evaluate_stack_max_le
     \\ fs [wordSemTheory.state_fn_updates]
     \\ strip_tac
     \\ imp_res_tac stack_rel_IMP_size_of_stack
     \\ drule_then match_mp_tac option_le_trans
     \\ fs[do_stack_def,CaseEq"list",pop_env_def,CaseEq"stack",stack_consumed_def,stack_rel_simp] >> rveq >> fs[]
     \\ imp_res_tac stack_rel_simp
     \\ rw[size_of_stack_eq,option_le_max_right,option_le_max,option_map2_max_add,AC option_add_comm option_add_assoc,option_le_eq_eqns,option_map2_max_add,stack_size_eq]
    )
  \\ conj_tac >- fs [limits_inv_def, FLOOKUP_DEF,FAPPLY_FUPDATE_THM]
  \\ pop_assum kall_tac
  \\ pop_assum mp_tac
  \\ qmatch_abbrev_tac`P xx yy zz ⇒ P x' yy z'`
  \\ `xx = x'`
  by (
    simp[Abbr`xx`,Abbr`x'`,FUN_EQ_THM,APPLY_UPDATE_THM,Abbr`lw`]
    \\ simp[n2w_sub,WORD_LEFT_ADD_DISTRIB] \\ rw[]
    \\ simp[w2w_word_of_byte_w2w] )
  \\ rveq \\ qunabbrev_tac `P`
  \\ match_mp_tac memory_rel_rearrange
  \\ unabbrev_all_tac
  \\ imp_res_tac stack_rel_simp
  \\ fs[]
  \\ fs[FAPPLY_FUPDATE_THM]
  \\ rw [] \\ fs []
QED

val get_var_get_real_addr_lemma =
    GEN_ALL(CONV_RULE(LAND_CONV(move_conj_left(
                                   same_const``wordSem$get_var`` o #1 o
                                   strip_comb o lhs)))
                     get_real_addr_lemma)

val mk_wf_inter = MATCH_MP wf_mk_id (SPEC_ALL wf_inter) |> GEN_ALL;
(* cut_env is idempotent: cutting the same names twice gives the same result. *)

Theorem cut_env_idempotent:
  dataSem$cut_env ns s_locals = SOME env ==>
  dataSem$cut_env ns env = SOME env
Proof
  rw [dataSemTheory.cut_env_def, AllCaseEqs()]
  \\ simp [sptreeTheory.domain_inter, pred_setTheory.SUBSET_INTER]
  \\ simp [sptreeTheory.spt_eq_thm, sptreeTheory.wf_inter,
           sptreeTheory.lookup_inter, AllCaseEqs()]
  \\ rw []
  \\ Cases_on ‘lookup x s_locals’ \\ Cases_on ‘lookup x ns’ \\ simp []
QED

(* The three heap-store FLOOKUPs follow directly from state_rel.
   Reusable in any op that needs to inspect t.store.{NextFree,CurrHeap,HeapLength}. *)

Theorem state_rel_FLOOKUP_heap:
  state_rel c l1 l2 s t NONE locs ==>
  ?nf cu hl.
    FLOOKUP t.store NextFree = SOME (Word nf) /\
    FLOOKUP t.store CurrHeap = SOME (Word cu) /\
    FLOOKUP t.store HeapLength = SOME (Word hl)
Proof
  rw [state_rel_thm, data_to_word_memoryProofTheory.memory_rel_def,
      data_to_word_memoryProofTheory.heap_in_memory_store_def]
  \\ metis_tac []
QED

(* Evaluating a SilentFFI block (the c.call_empty_ffi=T form emitted by
   op_requires_names ops, with var slot 3): if the word state's locals can be
   cut by the same names, the FFI call has empty payload and reduces to a
   locals-updated state. Reusable in any op whose generated code begins or
   resumes with `SilentFFI c 3 (adjust_sets <names>)`. *)

Theorem evaluate_SilentFFI_3:
  c.call_empty_ffi /\
  state_rel c l1 l2 s t NONE locs /\
  wordSem$cut_env (adjust_sets ns) t.locals = SOME env ==>
  wordSem$evaluate (SilentFFI c 3 (adjust_sets ns), t) =
    (NONE, t with <|locals := env; fp_regs := FEMPTY;
                    memory := t.memory; ffi := t.ffi|>)
Proof
  strip_tac
  \\ imp_res_tac state_rel_FLOOKUP_heap
  \\ fs [data_to_wordTheory.SilentFFI_def, wordSemTheory.evaluate_def,
         eq_eval,
         wordSemTheory.word_exp_def,
         wordSemTheory.set_var_def, wordSemTheory.get_var_def,
         lookup_insert, data_to_wordTheory.list_Seq_def,
         wordSemTheory.the_words_def, wordSemTheory.word_op_def,
         wordSemTheory.get_store_def,
         EVAL ``read_bytearray (a:'a word) 0 m``, ffiTheory.call_FFI_def,
         EVAL ``write_bytearray (a:'a word) [] m dm b``,
         data_to_word_gcProofTheory.cut_env_adjust_sets_insert_ODD]
QED

(* size_of_heap monotonicity helpers *)

val _=augment_srw_ss[rewrites[i2w_int_or,i2w_mod_pow2,compiler_ptr_bits_i2w]];

Theorem assign_MutCons:
  (∃t k. op = MemOp (MutCons t k)) ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ imp_res_tac state_rel_small_shift_length \\ drule0 (evaluate_GiveUp2 |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ rpt_drule0 state_rel_cut_IMP
  \\ qpat_x_assum `state_rel c l1 l2 s t NONE locs` kall_tac \\ strip_tac
  \\ gvs [dataLangTheory.op_requires_names_def,
          dataLangTheory.op_space_reset_def,
          dataSemTheory.cut_state_opt_def]
  \\ fs [assign_def]
  \\ reverse (Cases_on `c.gc_kind`) \\ fs []
  >- ((* Generational: the code gives up, and MutCons is not safe for space *)
      gvs [do_app,allowed_op_def,AllCaseEqs()])
  \\ Cases_on `args = []` \\ fs []
  \\ TRY ((* MutCons always has a hole, so it cannot have zero arguments *)
          gvs [do_app,allowed_op_def,AllCaseEqs()]
          \\ imp_res_tac get_vars_IMP_LENGTH \\ gvs [] \\ NO_TAC)
  \\ CASE_TAC \\ fs []
  \\ TRY ((* no header: giving up is sound, MutCons is never safe for space *)
          gvs [do_app,allowed_op_def,AllCaseEqs()] \\ NO_TAC)
  \\ fs [do_app,allowed_op_def] \\ every_case_tac \\ fs []
  \\ imp_res_tac get_vars_IMP_LENGTH \\ fs [] \\ clean_tac
  \\ fs [consume_space_def] \\ clean_tac
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ `shift_length c - shift (dimindex (:'a)) < dimword (:'a)` by
       (fs [state_rel_thm] \\ assume_tac dimindex_lt_dimword \\ decide_tac)
  \\ simp [state_rel_thm] \\ eval_tac
  \\ fs [state_rel_thm,option_le_max_right] \\ eval_tac
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ drule0 (memory_rel_get_vars_IMP |> GEN_ALL)
  \\ disch_then drule0 \\ fs [NOT_LESS,DECIDE ``n + 1 <= m <=> n < m:num``]
  \\ strip_tac
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ qabbrev_tac `new = LEAST ptr. ptr ∉ domain s.refs`
  \\ `new ∉ domain s.refs` by metis_tac [LEAST_NOTIN_spt_DOMAIN]
  \\ `vals <> [] /\ (LENGTH vals = LENGTH ws)` by
       (Cases_on `args` \\ Cases_on `vals` \\ fs [])
  \\ `k < LENGTH vals` by fs []
  \\ `!gs. c.gc_kind <> Generational gs` by fs []
  \\ rpt_drule0 memory_rel_MutCons
  \\ disch_then (qspecl_then [`new`,`k`] mp_tac)
  \\ impl_tac >- fs []
  \\ strip_tac
  \\ fs [list_Seq_def] \\ eval_tac
  \\ fs [wordSemTheory.set_store_def]
  \\ qpat_abbrev_tac `t5 = t with <| locals := _ |>`
  \\ pairarg_tac \\ fs []
  \\ `t.memory = t5.memory /\ t.mdomain = t5.mdomain` by
       (unabbrev_all_tac \\ fs []) \\ fs []
  \\ ntac 2 (pop_assum kall_tac)
  \\ drule0 evaluate_StoreEach
  \\ disch_then (qspecl_then [`3::MAP adjust_var args`,`1`,`c`] mp_tac)
  (* both non-generational gc kinds are still in play, so the side conditions
     of evaluate_StoreEach have to be discharged on each of them *)
  \\ impl_tac
  \\ TRY (fs [wordSemTheory.get_vars_def,Abbr`t5`,wordSemTheory.get_var_def,
               lookup_insert,get_vars_with_store,get_vars_adjust_var]
           \\ `(t with locals := t.locals) = t` by
                 fs [wordSemTheory.state_component_equality] \\ fs [] \\ NO_TAC)
  \\ clean_tac \\ fs [] \\ UNABBREV_ALL_TAC
  \\ fs [lookup_insert,FAPPLY_FUPDATE_THM,adjust_var_11,FLOOKUP_UPDATE,
         code_oracle_rel_def,FLOOKUP_UPDATE]
  \\ rw [] \\ fs [] \\ rw [] \\ fs []
  \\ fs [inter_insert_ODD_adjust_set,option_le_max_right]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ match_mp_tac memory_rel_insert \\ fs []
  \\ fs [make_cons_ptr_def,get_lowerbits_def]
QED

Theorem assign_UpdateCons:
  op = MemOp UpdateCons ==> ^assign_thm_goal
Proof
  strip_tac
  \\ rpt strip_tac
  \\ gvs [dataLangTheory.op_requires_names_def,
          dataLangTheory.op_space_reset_def,
          dataSemTheory.cut_state_opt_def]
  \\ drule0 (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ imp_res_tac get_vars_IMP_LENGTH \\ fs []
  \\ fs [do_app,allowed_op_def] \\ every_case_tac \\ fs [] \\ clean_tac
  \\ fs [integerTheory.NUM_OF_INT,LENGTH_EQ_3] \\ clean_tac
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ fs [bvlSemTheory.Unit_def] \\ rveq
  \\ fs [GSYM bvlSemTheory.Unit_def] \\ rveq
  \\ fs [assign_def] \\ eval_tac \\ fs [state_rel_thm]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ drule0 (memory_rel_get_vars_IMP |> GEN_ALL)
  \\ disch_then drule0 \\ fs []
  \\ imp_res_tac get_vars_3_IMP \\ fs []
  \\ fs [integerTheory.NUM_OF_INT,LENGTH_EQ_3] \\ clean_tac
  \\ imp_res_tac get_vars_3_IMP \\ fs [] \\ strip_tac
  \\ drule0 reorder_lemma \\ strip_tac
  \\ drule0 (memory_rel_UpdateCons |> GEN_ALL) \\ fs []
  \\ strip_tac \\ clean_tac
  \\ `word_exp t (real_offset c (adjust_var a2)) = SOME (Word y)` by
        (match_mp_tac (GEN_ALL get_real_offset_lemma)
         \\ fs [wordSemTheory.get_var_def] \\ NO_TAC)
  \\ `word_exp t (real_addr c (adjust_var a1)) = SOME (Word x)` by
        (match_mp_tac (GEN_ALL get_real_addr_lemma)
         \\ fs [wordSemTheory.get_var_def] \\ NO_TAC)
  \\ fs [] \\ eval_tac \\ fs [EVAL ``word_exp s1 Unit``]
  \\ fs [wordSemTheory.mem_store_def]
  \\ fs [lookup_insert,adjust_var_11]
  \\ rw [] \\ fs [option_le_max_right]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ match_mp_tac memory_rel_insert \\ fs []
  \\ match_mp_tac memory_rel_Unit \\ fs []
  \\ first_x_assum (fn th => mp_tac th THEN match_mp_tac memory_rel_rearrange)
  \\ rw [] \\ fs []
QED

Theorem assign_FinaliseCons:
  op = MemOp FinaliseCons ==> ^assign_thm_goal
Proof
  strip_tac
  \\ rpt strip_tac
  \\ gvs [dataLangTheory.op_requires_names_def,
          dataLangTheory.op_space_reset_def,
          dataSemTheory.cut_state_opt_def]
  \\ drule0 (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ imp_res_tac get_vars_IMP_LENGTH \\ fs []
  \\ fs [do_app,allowed_op_def] \\ every_case_tac \\ fs [] \\ clean_tac
  \\ fs [LENGTH_EQ_1] \\ clean_tac
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ fs [LENGTH_EQ_1] \\ clean_tac
  \\ imp_res_tac get_vars_1_IMP
  \\ fs [assign_def] \\ eval_tac \\ fs [state_rel_thm]
  \\ imp_res_tac state_rel_IMP_tstamps
  \\ Cases_on `s.tstamps` \\ fs []
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ drule0 (memory_rel_get_vars_IMP |> GEN_ALL)
  \\ disch_then drule0 \\ fs [] \\ strip_tac
  (* the whole content of the step is this one memory_rel theorem *)
  \\ drule_all memory_rel_FinaliseCons \\ strip_tac
  \\ fs [lookup_insert,adjust_var_11]
  \\ rw [] \\ fs [option_le_max_right]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ match_mp_tac memory_rel_insert \\ fs []
QED

Theorem LENGTH_EQ_5:
   (LENGTH xs = 5 <=> ?a1 a2 a3 a4 a5. xs = [a1;a2;a3;a4;a5]) /\
    (5 = LENGTH xs <=> ?a1 a2 a3 a4 a5. xs = [a1;a2;a3;a4;a5])
Proof
  Cases_on `xs` \\ fs []
  \\ rpt (Cases_on `t` \\ fs [] ORELSE Cases_on `t'` \\ fs [])
QED

Theorem memory_rel_get_num:
   memory_rel c be ts refs sp st m dm vars /\
    n < dimword (:'a) DIV 8 /\ good_dimindex (:'a) /\
    MEM (Number (&n),a:'a word_loc) vars ==>
    ?w. a = Word w /\ w >>> 1 = n2w n
Proof
  rw []
  \\ `memory_rel c be ts refs sp st m dm [Number (&n),a]` by
   (first_x_assum (fn th => mp_tac th THEN match_mp_tac memory_rel_rearrange)
    \\ fs [])
  \\ `small_int (dimindex (:α)) (&n)` by
       (fs [good_dimindex_def,dimword_def,small_int_def] \\ fs [])
  \\ imp_res_tac memory_rel_Number_IMP
  \\ fs [Smallnum_def] \\ rewrite_tac [GSYM w2n_11,w2n_lsr]
  \\ fs [good_dimindex_def,dimword_def]
  \\ `2 * n < dimword (:'a)` by fs [dimword_def]
  \\ fs [dimword_def]
  \\ match_mp_tac (MULT_DIV |> ONCE_REWRITE_RULE [MULT_COMM]) \\ fs []
QED

Theorem get_var_to_word_exp:
   get_var r s = SOME (Word w) ⇒
  word_exp s (Op Add [Var r;Const 0] ) = SOME (Word (w+0w)) ∧
  word_exp s (Op Add [Var r;Const 1] ) = SOME (Word (w+1w)) ∧
  word_exp s (Op Add [Var r;Const 2] ) = SOME (Word (w+2w)) ∧
  word_exp s (Op Add [Var r;Const 3] ) = SOME (Word (w+3w))
Proof
  EVAL_TAC>>rw[]
QED

Theorem word_exp_set[local]:
  (word_exp s (Op Add [Var n; Const c]) =
  case get_var n s of
    SOME (Word w) => SOME (Word (w+i2w c))
  | _ => NONE) ∧
  (word_exp s (Op Sub [Var n; Const c]) =
  case get_var n s of
    SOME (Word w) => SOME (Word (w-i2w c))
  | _ => NONE)
Proof
  EVAL_TAC>>rw[]>>
  every_case_tac>>rw[]>>
  fs[]
QED

Theorem good_dimindex_w2w_byte[local]:
  good_dimindex (:'a) ⇒
  w2w (w2w (w:word8):'a word) = w
Proof
  rw[good_dimindex_def]>>
  simp[w2w_w2w]>>
  match_mp_tac WORD_ALL_BITS>>fs[]
QED

Theorem set_var_consts[local]:
  (set_var r v s).memory = s.memory ∧
  (set_var r v s).mdomain = s.mdomain ∧
  (set_var r v s).be = s.be ∧
  (set_var r v s).code = s.code
Proof
  fs[wordSemTheory.set_var_def]
QED

Theorem get_var_consts[local]:
  get_var r (s with memory:=m) = get_var r s
Proof
  EVAL_TAC>>rw[]
QED

Theorem CopyByteAdd_thm:
   !be n a1 a2 m dm ret_val l1 l2 (s:('a,'c,'ffi) wordSem$state) m1.
      word_copy_fwd be n a1 a2 m dm = SOME m1 /\
      s.memory = m /\ s.mdomain = dm /\
      s.be = be ∧
      good_dimindex(:'a) ∧
      (?md. lookup ByteCopyAdd_location s.code = SOME (5,ByteCopyAdd_code,md)) /\
      w2n n DIV 4 <= s.clock /\
      get_var 0 s = SOME (Loc l1 l2) /\
      get_var 2 s = SOME (Word n) /\
      get_var 4 s = SOME (Word (a1:'a word)) /\
      get_var 6 s = SOME (Word a2) /\
      get_var 8 s = SOME ret_val ==>
      evaluate (ByteCopyAdd_code,s) =
        (SOME (Result (Loc l1 l2) [ret_val]),
         s with <| clock := s.clock - w2n n DIV 4 ;
                   memory := m1 ; locals := LN; locals_size := SOME 0;
                   stack_max :=
                   if n <₊ 4w then
                     s.stack_max
                   else
                     OPTION_MAP2 MAX s.stack_max
                       (OPTION_MAP2 $+ (stack_size s.stack)
                       (lookup ByteCopyAdd_location s.stack_size))|>)
Proof
  ho_match_mp_tac word_copy_fwd_ind >>
  rw[]>>
  qpat_x_assum`A=SOME m1` mp_tac>>
  simp[Once word_copy_fwd_def]>>
  rpt (IF_CASES_TAC)>>rw[]
  >-
    (fs[ByteCopyAdd_code_def,wordSemTheory.evaluate_def,wordSemTheory.get_var_imm_def,
        wordSemTheory.get_var_def,asmTheory.word_cmp_def,wordSemTheory.get_vars_def]>>
     EVAL_TAC>>fs[wordSemTheory.state_component_equality])
  >-
    (imp_res_tac get_var_to_word_exp>>
    fs[ByteCopyAdd_code_def,wordSemTheory.evaluate_def,wordSemTheory.get_var_imm_def,asmTheory.word_cmp_def,list_Seq_def,wordSemTheory.inst_def,wordSemTheory.get_vars_def]>>
    simp[word_exp_set,get_var_set_var_thm,set_var_consts]>>
    simp[good_dimindex_w2w_byte]>>
    simp[get_var_set_var_thm,get_var_consts]>>
    EVAL_TAC>>fs[wordSemTheory.state_component_equality]>>
    fs[WORD_LO]>>
    `w2n n DIV 4 = 0` by
      (match_mp_tac LESS_DIV_EQ_ZERO>>fs[])>>
    fs[])
  >-
    (FULL_CASE_TAC>>fs[]
    >-
      (imp_res_tac get_var_to_word_exp>>
      fs[ByteCopyAdd_code_def,wordSemTheory.evaluate_def,wordSemTheory.get_var_imm_def,asmTheory.word_cmp_def,list_Seq_def,wordSemTheory.inst_def,wordSemTheory.get_vars_def]>>
      simp[word_exp_set,get_var_set_var_thm,set_var_consts]>>
      simp[good_dimindex_w2w_byte]>>
      simp[get_var_set_var_thm,get_var_consts,set_var_consts]>>
      simp[good_dimindex_w2w_byte]>>
      simp[get_var_set_var_thm,get_var_consts,set_var_consts]>>
      EVAL_TAC>>fs[wordSemTheory.state_component_equality]>>
      fs[WORD_LO]>>
      `w2n n DIV 4 = 0` by
        (match_mp_tac LESS_DIV_EQ_ZERO>>fs[])>>
      fs[])
    >>
      (imp_res_tac get_var_to_word_exp>>
      fs[ByteCopyAdd_code_def,wordSemTheory.evaluate_def,wordSemTheory.get_var_imm_def,asmTheory.word_cmp_def,list_Seq_def,wordSemTheory.inst_def,wordSemTheory.get_vars_def]>>
      simp[word_exp_set,get_var_set_var_thm,set_var_consts]>>
      simp[good_dimindex_w2w_byte]>>
      simp[get_var_set_var_thm,get_var_consts,set_var_consts]>>
      simp[good_dimindex_w2w_byte]>>
      simp[get_var_set_var_thm,get_var_consts,set_var_consts]>>
      simp[good_dimindex_w2w_byte]>>
      simp[get_var_set_var_thm,get_var_consts,set_var_consts]>>
      EVAL_TAC>>fs[wordSemTheory.state_component_equality]>>
      fs[WORD_LO]>>
      `w2n n DIV 4 = 0` by
        (match_mp_tac LESS_DIV_EQ_ZERO>>fs[])>>
      fs[]))
  >>
    (imp_res_tac get_var_to_word_exp>>
    simp[ByteCopyAdd_code_def,wordSemTheory.evaluate_def,wordSemTheory.get_var_imm_def,asmTheory.word_cmp_def,list_Seq_def,wordSemTheory.inst_def,wordSemTheory.get_vars_def]>>
    simp[word_exp_set,get_var_set_var_thm,set_var_consts]>>
    simp[good_dimindex_w2w_byte]>>
    simp[get_var_set_var_thm,get_var_consts,set_var_consts]>>
    simp[good_dimindex_w2w_byte]>>
    simp[get_var_set_var_thm,get_var_consts,set_var_consts]>>
    simp[good_dimindex_w2w_byte]>>
    simp[get_var_set_var_thm,get_var_consts,set_var_consts]>>
    simp[good_dimindex_w2w_byte]>>
    simp[get_var_set_var_thm,get_var_consts,set_var_consts,wordSemTheory.get_vars_def]>>
    simp[wordSemTheory.bad_dest_args_def,wordSemTheory.find_code_def,wordSemTheory.add_ret_loc_def]>>
    `w2n n DIV 4 = (w2n (n+ -4w) DIV 4) +1` by
      (fs[WORD_NOT_LOWER]>>
      FULL_SIMP_TAC (std_ss) [WORD_SUB_INTRO,word_sub_w2n]>>
      simp[DIV_SUB]>>
      fs[WORD_LS]>>
      `0 < 4 ∧ 4 * 1 ≤ w2n n` by fs[]>>
      imp_res_tac DIV_SUB>>
      fs[]>>
      `0 < w2n n DIV 4` by
        (match_mp_tac bitTheory.DIV_GT0>>
        fs[])>>
      fs[])>>
    simp[]>>
    qmatch_goalsub_abbrev_tac`evaluate (_,s')`>>
    first_x_assum drule0 >>
    simp[]>>
    disch_then (qspecl_then [`ret_val`,`l1`,`l2`,`s'`] mp_tac)>>
    impl_tac>-
      (unabbrev_all_tac>>simp[wordSemTheory.call_env_def,wordSemTheory.dec_clock_def]>>
      simp[wordSemTheory.get_var_def,lookup_fromList2,lookup_fromList,set_var_consts])>>
    rw[]>>
    unabbrev_all_tac>>simp[wordSemTheory.call_env_def,wordSemTheory.dec_clock_def]>>
    simp[wordSemTheory.state_component_equality,wordSemTheory.set_var_def])
QED

Theorem CopyByteSub_thm:
   !be n a1 a2 m dm ret_val l1 l2 (s:('a,'c,'ffi) wordSem$state) m1.
      word_copy_bwd be n a1 a2 m dm = SOME m1 /\
      s.memory = m /\ s.mdomain = dm /\
      s.be = be ∧
      good_dimindex(:'a) ∧
      (?md. lookup ByteCopySub_location s.code = SOME (5,ByteCopySub_code,md)) /\
      w2n n DIV 4 <= s.clock /\
      get_var 0 s = SOME (Loc l1 l2) /\
      get_var 2 s = SOME (Word n) /\
      get_var 4 s = SOME (Word (a1:'a word)) /\
      get_var 6 s = SOME (Word a2) /\
      get_var 8 s = SOME ret_val ==>
      evaluate (ByteCopySub_code,s) =
        (SOME (Result (Loc l1 l2) [ret_val]),
         s with <| clock := s.clock - w2n n DIV 4 ;
                   memory := m1 ; locals := LN; locals_size := SOME 0;
                   stack_max :=
                   if n <₊ 4w then
                     s.stack_max
                   else
                     OPTION_MAP2 MAX s.stack_max
                       (OPTION_MAP2 $+ (stack_size s.stack)
                       (lookup ByteCopySub_location s.stack_size))|>)
Proof
  ho_match_mp_tac word_copy_bwd_ind >>
  rw[]>>
  qpat_x_assum`A=SOME m1` mp_tac>>
  simp[Once word_copy_bwd_def]>>
  rpt (IF_CASES_TAC)>>rw[]
  >-
    (fs[ByteCopySub_code_def,wordSemTheory.evaluate_def,wordSemTheory.get_var_imm_def,
        wordSemTheory.get_vars_def]>>
    EVAL_TAC>>fs[wordSemTheory.state_component_equality])
  >-
    (imp_res_tac get_var_to_word_exp>>
    fs[ByteCopySub_code_def,wordSemTheory.evaluate_def,wordSemTheory.get_var_imm_def,asmTheory.word_cmp_def,list_Seq_def,wordSemTheory.inst_def,wordSemTheory.get_vars_def]>>
    simp[word_exp_set,get_var_set_var_thm,set_var_consts]>>
    simp[good_dimindex_w2w_byte]>>
    simp[get_var_set_var_thm,get_var_consts]>>
    EVAL_TAC>>fs[wordSemTheory.state_component_equality]>>
    fs[WORD_LO]>>
    `w2n n DIV 4 = 0` by
      (match_mp_tac LESS_DIV_EQ_ZERO>>fs[])>>
    fs[])
  >-
    (FULL_CASE_TAC>>fs[]
    >-
      (imp_res_tac get_var_to_word_exp>>
      fs[ByteCopySub_code_def,wordSemTheory.evaluate_def,wordSemTheory.get_var_imm_def,asmTheory.word_cmp_def,list_Seq_def,wordSemTheory.inst_def,wordSemTheory.get_vars_def]>>
      simp[word_exp_set,get_var_set_var_thm,set_var_consts]>>
      simp[good_dimindex_w2w_byte]>>
      simp[get_var_set_var_thm,get_var_consts,set_var_consts]>>
      simp[good_dimindex_w2w_byte]>>
      simp[get_var_set_var_thm,get_var_consts,set_var_consts]>>
      EVAL_TAC>>fs[wordSemTheory.state_component_equality]>>
      fs[WORD_LO]>>
      `w2n n DIV 4 = 0` by
        (match_mp_tac LESS_DIV_EQ_ZERO>>fs[])>>
      fs[])
    >>
      (imp_res_tac get_var_to_word_exp>>
      fs[ByteCopySub_code_def,wordSemTheory.evaluate_def,wordSemTheory.get_var_imm_def,asmTheory.word_cmp_def,list_Seq_def,wordSemTheory.inst_def,wordSemTheory.get_vars_def]>>
      simp[word_exp_set,get_var_set_var_thm,set_var_consts]>>
      simp[good_dimindex_w2w_byte]>>
      simp[get_var_set_var_thm,get_var_consts,set_var_consts]>>
      simp[good_dimindex_w2w_byte]>>
      simp[get_var_set_var_thm,get_var_consts,set_var_consts]>>
      simp[good_dimindex_w2w_byte]>>
      simp[get_var_set_var_thm,get_var_consts,set_var_consts]>>
      EVAL_TAC>>fs[wordSemTheory.state_component_equality]>>
      fs[WORD_LO]>>
      `w2n n DIV 4 = 0` by
        (match_mp_tac LESS_DIV_EQ_ZERO>>fs[])>>
      fs[]))
  >>
    (imp_res_tac get_var_to_word_exp>>
    simp[ByteCopySub_code_def,wordSemTheory.evaluate_def,wordSemTheory.get_var_imm_def,asmTheory.word_cmp_def,list_Seq_def,wordSemTheory.inst_def]>>
    simp[word_exp_set,get_var_set_var_thm,set_var_consts]>>
    simp[good_dimindex_w2w_byte]>>
    simp[get_var_set_var_thm,get_var_consts,set_var_consts]>>
    simp[good_dimindex_w2w_byte]>>
    simp[get_var_set_var_thm,get_var_consts,set_var_consts]>>
    simp[good_dimindex_w2w_byte]>>
    simp[get_var_set_var_thm,get_var_consts,set_var_consts]>>
    simp[good_dimindex_w2w_byte]>>
    simp[get_var_set_var_thm,get_var_consts,set_var_consts,wordSemTheory.get_vars_def]>>
    simp[wordSemTheory.bad_dest_args_def,wordSemTheory.find_code_def,wordSemTheory.add_ret_loc_def]>>
    `w2n n DIV 4 = (w2n (n+ -4w) DIV 4) +1` by
      (fs[WORD_NOT_LOWER]>>
      FULL_SIMP_TAC (std_ss) [WORD_SUB_INTRO,word_sub_w2n]>>
      simp[DIV_SUB]>>
      fs[WORD_LS]>>
      `0 < 4 ∧ 4 * 1 ≤ w2n n` by fs[]>>
      imp_res_tac DIV_SUB>>
      fs[]>>
      `0 < w2n n DIV 4` by
        (match_mp_tac bitTheory.DIV_GT0>>
        fs[])>>
      fs[])>>
    simp[]>>
    qmatch_goalsub_abbrev_tac`evaluate (_,s')`>>
    first_x_assum drule0 >>
    simp[]>>
    disch_then (qspecl_then [`ret_val`,`l1`,`l2`,`s'`] mp_tac)>>
    impl_tac>-
      (unabbrev_all_tac>>simp[wordSemTheory.call_env_def,wordSemTheory.dec_clock_def]>>
      simp[wordSemTheory.get_var_def,lookup_fromList2,lookup_fromList,set_var_consts])>>
    rw[]>>
    unabbrev_all_tac>>simp[wordSemTheory.call_env_def,wordSemTheory.dec_clock_def]>>
    simp[wordSemTheory.state_component_equality,wordSemTheory.set_var_def])
QED

Theorem CopyByteAdd_call:
  ∀s n a b ret_val l1 l2 final.
    good_dimindex (:'a) /\
    wordSem$get_vars [0;2;4;6;8] (s:('a,'c,'ffi) wordSem$state) =
      SOME [Loc l1 l2;Word n;Word a;Word b;ret_val] /\
    (?md. lookup ByteCopyAdd_location s.code = SOME (5,ByteCopyAdd_code,md)) /\
    w2n n DIV 4 < s.clock /\
    word_copy_fwd s.be n a b s.memory s.mdomain = SOME final ==>
    evaluate (Call NONE (SOME ByteCopyAdd_location) [0;2;4;6;8] NONE,s) =
      (SOME (Result (Loc l1 l2) [ret_val]),
       s with <| clock := s.clock - (w2n n DIV 4 + 1); memory := final;
                 locals := LN; locals_size := SOME 0;
                 stack_max := OPTION_MAP2 MAX s.stack_max
                   (OPTION_MAP2 $+ (stack_size s.stack)
                     (lookup ByteCopyAdd_location s.stack_size)) |>)
Proof
  rpt gen_tac
  \\ strip_tac
  \\ `s.clock <> 0` by decide_tac
  \\ simp [Once wordSemTheory.evaluate_def,wordSemTheory.bad_dest_args_def,
           wordSemTheory.find_code_def,wordSemTheory.add_ret_loc_def]
  \\ qmatch_goalsub_abbrev_tac `evaluate (ByteCopyAdd_code,callee)`
  \\ qspecl_then [`s.be`,`n`,`a`,`b`,`s.memory`,`s.mdomain`,
                   `ret_val`,`l1`,`l2`,`callee`,`final`] mp_tac CopyByteAdd_thm
  \\ impl_tac >- (
    fs [Abbr `callee`,wordSemTheory.call_env_def,wordSemTheory.dec_clock_def,
        wordSemTheory.get_var_def,lookup_fromList2,lookup_fromList]
    \\ decide_tac)
  \\ disch_then SUBST1_TAC
  \\ simp [Abbr `callee`,wordSemTheory.call_env_def,wordSemTheory.dec_clock_def,
           wordSemTheory.state_component_equality]
QED

Theorem byte_copy_memory_rel_source[local]:
  ∀k n b actual model a d.
    0 < k /\ byte_copy_memory_rel k (n DIV (3 * k)) (b:'a word) actual model /\
    (!i j. (i + 1) * k <= n /\ j * k < n + d ==>
      a + n2w (i * k) <> b + n2w (j * k)) ==>
    !i. (i + 1) * k <= n ==>
      actual (a + n2w (i * k)) = model (a + n2w (i * k))
Proof
  rpt gen_tac
  \\ strip_tac
  \\ `0 < 3 * k` by decide_tac
  \\ `n DIV (3 * k) * (3 * k) <= n` by (
    qpat_x_assum `0 < 3 * k`
      (ACCEPT_TAC o SIMP_RULE std_ss [LESS_EQ_REFL] o
       MATCH_MP (Q.SPECL [`n DIV (3 * k)`,`n`,`3 * k`] X_LE_DIV)))
  \\ qx_gen_tac `src_index` \\ strip_tac
  \\ qpat_x_assum `byte_copy_memory_rel _ _ _ _ _`
       (irule o REWRITE_RULE [byte_copy_memory_rel_def])
  \\ qx_gen_tac `dst_index` \\ strip_tac
  \\ `dst_index * k < (3 * (n DIV (3 * k))) * k`
  by (
    irule (iffRL LT_MULT_RCANCEL)
    \\ conj_tac \\ first_assum ACCEPT_TAC)
  \\ qpat_x_assum `!i j. _` irule
  \\ ASM_REWRITE_TAC []
  \\ `(3 * (n DIV (3 * k))) * k = (n DIV (3 * k)) * (3 * k)` by
       CONV_TAC (AC_CONV (MULT_ASSOC,MULT_COMM))
  \\ qpat_x_assum `(3 * (n DIV (3 * k))) * k = _`
       (RULE_ASSUM_TAC o REWRITE_RULE o single)
  \\ irule LESS_LESS_EQ_TRANS
  \\ qexists_tac `n`
  \\ ASM_REWRITE_TAC [LESS_EQ_ADD]
  \\ irule LESS_LESS_EQ_TRANS
  \\ qexists_tac `(n DIV (3 * k)) * (3 * k)`
  \\ ASM_REWRITE_TAC []
QED

Definition byte_copy_loop_inv_def:
  byte_copy_loop_inv k n d (a:'a word) b (m:'a word -> 'a word_loc) dm <=>
    (!i. i * k < n ==>
      a + n2w (i * k) IN dm /\ isWord (m (a + n2w (i * k)))) /\
    (!j. j * k < n + d ==>
      b + n2w (j * k) IN dm /\ isWord (m (b + n2w (j * k)))) /\
    (!i j. (i + 1) * k <= n /\ j * k < n + d ==>
      a + n2w (i * k) <> b + n2w (j * k))
End

Theorem byte_copy_loop_inv_step[local]:
  0 < k /\ 3 * k <= n /\ byte_copy_loop_inv k n d a b m dm ==>
  byte_copy_loop_inv k (n - 3 * k) d (a + n2w (3 * k)) (b + n2w (3 * k))
    ((b + n2w (2 * k) =+ Word out3)
      ((b + n2w k =+ Word out2) ((b =+ Word out1) m))) dm
Proof
  strip_tac
  \\ qpat_x_assum `byte_copy_loop_inv _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [byte_copy_loop_inv_def])
  \\ PURE_REWRITE_TAC [byte_copy_loop_inv_def]
  \\ conj_tac
  >- (
    qx_gen_tac `src_index` \\ strip_tac
    \\ `(src_index + 3) * k < n` by (
      REWRITE_TAC [RIGHT_ADD_DISTRIB]
      \\ decide_tac)
    \\ qpat_x_assum `!i. i * k < n ==> _`
         (qspec_then `src_index + 3` mp_tac)
    \\ impl_tac >- ASM_REWRITE_TAC []
    \\ rw [RIGHT_ADD_DISTRIB,addressTheory.word_arith_lemma1,APPLY_UPDATE_THM,isWord_def]
    \\ rpt IF_CASES_TAC \\ fs [isWord_def])
  \\ conj_tac
  >- (
    qx_gen_tac `dst_index` \\ strip_tac
    \\ `(dst_index + 3) * k < n + d` by (
      REWRITE_TAC [RIGHT_ADD_DISTRIB]
      \\ decide_tac)
    \\ qpat_x_assum `!j. j * k < n + d ==> _`
         (qspec_then `dst_index + 3` mp_tac)
    \\ impl_tac >- ASM_REWRITE_TAC []
    \\ rw [RIGHT_ADD_DISTRIB,addressTheory.word_arith_lemma1,APPLY_UPDATE_THM,isWord_def]
    \\ rpt IF_CASES_TAC \\ fs [isWord_def])
  \\ qx_gen_tac `src_index` \\ qx_gen_tac `dst_index` \\ strip_tac
  \\ `(src_index + 3 + 1) * k <= n /\ (dst_index + 3) * k < n + d`
  by (
    fs [RIGHT_ADD_DISTRIB]
    \\ decide_tac)
  \\ qpat_x_assum `!i j. _`
       (qspecl_then [`src_index + 3`,`dst_index + 3`] mp_tac)
  \\ impl_tac >- ASM_REWRITE_TAC []
  \\ simp [RIGHT_ADD_DISTRIB,addressTheory.word_arith_lemma1]
QED

Theorem evaluate_ByteCopyLoop_next:
  get_vars [0;2;4;6;8;10;12;14] s =
    SOME [Loc l1 l2;Word (n2w n);Word a;Word b;ret_val;carry;sh;back] /\
  3 * k <= n /\ s.clock <> 0 /\
  lookup ByteCopyLoop_location s.code = SOME (8,ByteCopyLoop_code c,md) /\
  evaluate (ByteCopyLoop_code c,
    call_env [Loc l1 l2;Word (n2w (n - 3 * k));Word (a + n2w (3 * k));
              Word (b + n2w (3 * k));ret_val;carry;sh;back]
      (lookup ByteCopyLoop_location s.stack_size) (dec_clock s)) =
    (SOME (Result (Loc l1 l2) [ret_val]),out) ==>
  evaluate (list_Seq [
    Assign 2 (Op Sub [Var 2;Const (&(3 * k))]);
    Assign 4 (Op Add [Var 4;Const (&(3 * k))]);
    Assign 6 (Op Add [Var 6;Const (&(3 * k))]);
    Call NONE (SOME ByteCopyLoop_location) [0;2;4;6;8;10;12;14] NONE],s) =
    (SOME (Result (Loc l1 l2) [ret_val]),out)
Proof
  strip_tac
  \\ fs [wordSemTheory.get_vars_def,AllCaseEqs()]
  \\ `~(n < 3 * k)` by decide_tac
  \\ `(n2w n + -1w * n2w (3 * k):'a word) = n2w (n - 3 * k)` by (
    PURE_REWRITE_TAC [GSYM WORD_NEG_MUL,GSYM word_sub_def]
    \\ qpat_assum `~(n < 3 * k)` mp_tac
    \\ SIMP_TAC std_ss [addressTheory.word_arith_lemma2])
  \\ fs [wordSemTheory.get_var_def]
  \\ fs [list_Seq_def,wordSemTheory.evaluate_def,wordSemTheory.word_exp_def,
          wordSemTheory.word_op_def,wordSemTheory.set_var_def,
          wordSemTheory.get_var_def,lookup_insert,wordSemTheory.get_vars_def,
          wordSemTheory.fix_clock_def,wordSemTheory.bad_dest_args_def,
          wordSemTheory.find_code_def,wordSemTheory.add_ret_loc_def,
          wordSemTheory.call_env_def,wordSemTheory.dec_clock_def,
          integer_wordTheory.i2w_pos,wordSemTheory.the_words_def,
          wordSemTheory.bad_fun_return_def]
QED

Definition byte_copy_range_inv_def:
  byte_copy_range_inv n (a:'a word) b (m:'a word -> 'a word_loc) dm <=>
    (!i. i < n ==>
      byte_align (a + n2w i) IN dm /\ isWord (m (byte_align (a + n2w i))) /\
      byte_align (b + n2w i) IN dm /\ isWord (m (byte_align (b + n2w i)))) /\
    (!i j. i < n /\ j < n ==> a + n2w i <> b + n2w j)
End

Theorem byte_copy_range_inv_store[local]:
  ∀n a b m dm i be value.
    good_dimindex (:'a) /\ byte_copy_range_inv n (a:'a word) b m dm /\ i < n ==>
    ?updated.
      mem_store_byte_aux m dm be (b + n2w i) value = SOME updated /\
      byte_copy_range_inv n a b updated dm /\
      (!j. j < n ==> mem_load_byte_aux updated dm be (a + n2w j) =
                     mem_load_byte_aux m dm be (a + n2w j))
Proof
  rpt gen_tac
  \\ strip_tac
  \\ qpat_x_assum `byte_copy_range_inv _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [byte_copy_range_inv_def])
  \\ qpat_assum `!j. j < n ==> _` (qspec_then `i` mp_tac)
  \\ impl_tac >- qpat_assum `i < n` ACCEPT_TAC
  \\ disch_then (strip_assume_tac)
  \\ fs [isWord_exists]
  \\ qmatch_asmsub_rename_tac `m (byte_align (b + n2w i)) = Word old_word`
  \\ qabbrev_tac `updated =
       (byte_align (b + n2w i) =+
         Word (set_byte (b + n2w i) value old_word be)) m`
  \\ `mem_store_byte_aux m dm be (b + n2w i) value = SOME updated` by (
    simp [wordSemTheory.mem_store_byte_aux_def,Abbr `updated`])
  \\ qexists_tac `updated`
  \\ simp []
  \\ conj_tac >- (
    PURE_REWRITE_TAC [byte_copy_range_inv_def]
    \\ conj_tac >- (
      qx_gen_tac `j` \\ strip_tac
      \\ qpat_assum `!j. j < n ==> _` (qspec_then `j` mp_tac)
      \\ impl_tac >- qpat_assum `j < n` ACCEPT_TAC
      \\ disch_then (strip_assume_tac)
      \\ rw [Abbr `updated`,APPLY_UPDATE_THM]
      \\ fs [isWord_def])
    \\ first_assum ACCEPT_TAC)
  \\ qx_gen_tac `j` \\ strip_tac
  \\ qspecl_then [`a + n2w j`,`b + n2w i`,`m`,`dm`,`be`,`value`,`updated`]
       match_mp_tac
       mem_load_byte_aux_store_other
  \\ simp []
QED

Theorem byte_copy_range_inv_load[local]:
  ∀n a b m dm i be.
    byte_copy_range_inv n (a:'a word) b m dm /\ i < n ==>
    ?value. mem_load_byte_aux m dm be (a + n2w i) = SOME value
Proof
  rpt gen_tac
  \\ strip_tac
  \\ fs [byte_copy_range_inv_def]
  \\ qpat_assum `!j. j < n ==> _` (qspec_then `i` mp_tac)
  \\ impl_tac >- qpat_assum `i < n` ACCEPT_TAC
  \\ disch_then (strip_assume_tac)
  \\ fs [isWord_exists,wordSemTheory.mem_load_byte_aux_def]
QED

Theorem byte_copy_range_inv_suffix[local]:
  ∀n a b m dm skip_bytes.
    byte_copy_range_inv n (a:'a word) b m dm /\ skip_bytes <= n ==>
    byte_copy_range_inv (n - skip_bytes) (a + n2w skip_bytes) (b + n2w skip_bytes) m dm
Proof
  rpt gen_tac
  \\ strip_tac
  \\ qpat_x_assum `byte_copy_range_inv _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [byte_copy_range_inv_def])
  \\ PURE_REWRITE_TAC [byte_copy_range_inv_def]
  \\ conj_tac >- (
    qx_gen_tac `i` \\ strip_tac
    \\ `skip_bytes + i < n` by decide_tac
    \\ qpat_assum `!j. j < n ==> _` (qspec_then `skip_bytes + i` mp_tac)
    \\ simp [addressTheory.word_arith_lemma1])
  \\ map_every qx_gen_tac [`i`,`j`] \\ strip_tac
  \\ `skip_bytes + i < n /\ skip_bytes + j < n` by decide_tac
  \\ qpat_assum `!i j. _` (qspecl_then [`skip_bytes + i`,`skip_bytes + j`] mp_tac)
  \\ simp [addressTheory.word_arith_lemma1]
QED

Definition byte_copy_seq_def:
  (byte_copy_seq be 0 (a:'a word) b m dm = SOME m) /\
  (byte_copy_seq be (SUC n) a b m dm =
    OPTION_BIND (mem_load_byte_aux m dm be a) (\value.
      OPTION_BIND (mem_store_byte_aux m dm be b value) (\updated.
        byte_copy_seq be n (a + 1w) (b + 1w) updated dm)))
End

Theorem byte_copy_seq_unfold[local]:
  byte_copy_seq be n a b m dm =
    if n = 0 then SOME m else
      OPTION_BIND (mem_load_byte_aux m dm be a) (\value.
        OPTION_BIND (mem_store_byte_aux m dm be b value) (\updated.
          byte_copy_seq be (n - 1) (a + 1w) (b + 1w) updated dm))
Proof
  Cases_on `n` \\ simp [byte_copy_seq_def]
QED

Theorem word_copy_fwd_byte_copy_seq[local]:
  !n be (a:'a word) b m dm.
    good_dimindex (:'a) /\ n < dimword (:'a) /\
    byte_copy_range_inv n a b m dm ==>
    word_copy_fwd be (n2w n) a b m dm = byte_copy_seq be n a b m dm
Proof
  completeInduct_on `n`
  \\ map_every qx_gen_tac [`be`,`a`,`b`,`m`,`dm`]
  \\ strip_tac
  \\ `4 < dimword (:'a)` by fs [good_dimindex_def,dimword_def]
  \\ Cases_on `n = 0`
  >- (
    simp [Once word_copy_fwd_def,Once byte_copy_seq_unfold,byte_copy_seq_def,WORD_LO])
  \\ `0 < n` by decide_tac
  \\ qspecl_then [`n`,`a`,`b`,`m`,`dm`,`0`,`be`] mp_tac
       byte_copy_range_inv_load
  \\ impl_tac >- simp []
  \\ SIMP_TAC std_ss [WORD_ADD_0]
  \\ disch_then (qx_choose_then `first_byte` strip_assume_tac)
  \\ qspecl_then [`n`,`a`,`b`,`m`,`dm`,`0`,`be`,`first_byte`] mp_tac
       byte_copy_range_inv_store
  \\ impl_tac >- simp []
  \\ SIMP_TAC std_ss [WORD_ADD_0]
  \\ disch_then (qx_choose_then `memory1` strip_assume_tac)
  \\ Cases_on `n = 1`
  >- (
    simp [Once word_copy_fwd_def,Once byte_copy_seq_unfold,byte_copy_seq_def,WORD_LO])
  \\ `1 < n` by decide_tac
  \\ qspecl_then [`n`,`a`,`b`,`m`,`dm`,`1`,`be`] mp_tac
       byte_copy_range_inv_load
  \\ impl_tac >- simp []
  \\ disch_then (qx_choose_then `second_byte` strip_assume_tac)
  \\ qspecl_then [`n`,`a`,`b`,`memory1`,`dm`,`1`,`be`,`second_byte`] mp_tac
       byte_copy_range_inv_store
  \\ impl_tac >- simp []
  \\ disch_then (qx_choose_then `memory2` strip_assume_tac)
  \\ Cases_on `n = 2`
  >- (
    simp [Once word_copy_fwd_def,Once byte_copy_seq_unfold,WORD_LO]
    \\ simp [Once byte_copy_seq_unfold,byte_copy_seq_def])
  \\ `2 < n` by decide_tac
  \\ qspecl_then [`n`,`a`,`b`,`m`,`dm`,`2`,`be`] mp_tac
       byte_copy_range_inv_load
  \\ impl_tac >- simp []
  \\ disch_then (qx_choose_then `third_byte` strip_assume_tac)
  \\ qspecl_then [`n`,`a`,`b`,`memory2`,`dm`,`2`,`be`,`third_byte`] mp_tac
       byte_copy_range_inv_store
  \\ impl_tac >- simp []
  \\ disch_then (qx_choose_then `memory3` strip_assume_tac)
  \\ Cases_on `n = 3`
  >- (
    simp [Once word_copy_fwd_def,Once byte_copy_seq_unfold,WORD_LO]
    \\ simp [Once byte_copy_seq_unfold,addressTheory.word_arith_lemma1]
    \\ simp [Once byte_copy_seq_unfold,byte_copy_seq_def])
  \\ `3 < n /\ 4 <= n /\ n - 4 < n /\ n - 4 < dimword (:'a)` by decide_tac
  \\ qspecl_then [`n`,`a`,`b`,`m`,`dm`,`3`,`be`] mp_tac
       byte_copy_range_inv_load
  \\ impl_tac >- simp []
  \\ disch_then (qx_choose_then `fourth_byte` strip_assume_tac)
  \\ qspecl_then [`n`,`a`,`b`,`memory3`,`dm`,`3`,`be`,`fourth_byte`] mp_tac
       byte_copy_range_inv_store
  \\ impl_tac >- simp []
  \\ disch_then (qx_choose_then `memory4` strip_assume_tac)
  \\ qspecl_then [`n`,`a`,`b`,`memory4`,`dm`,`4`] mp_tac
       byte_copy_range_inv_suffix
  \\ impl_tac >- simp []
  \\ disch_tac
  \\ qpat_x_assum `!smaller. smaller < n ==> !be a b memory dm. _` (qspec_then `n - 4` mp_tac)
  \\ impl_tac >- first_assum ACCEPT_TAC
  \\ disch_then (qspecl_then [`be`,`a + 4w`,`b + 4w`,`memory4`,`dm`] mp_tac)
  \\ impl_tac >- simp []
  \\ disch_tac
  \\ `byte_copy_seq be n a b m dm =
       byte_copy_seq be (n - 4) (a + 4w) (b + 4w) memory4 dm` by (
    `n = SUC (SUC (SUC (SUC (n - 4))))` by decide_tac
    \\ pop_assum (CONV_TAC o LAND_CONV o ONCE_REWRITE_CONV o single)
    \\ simp [byte_copy_seq_def,addressTheory.word_arith_lemma1])
  \\ `(n2w n - 4w:'a word) = n2w (n - 4)` by (
    qpat_assum `4 <= n` (mp_tac o MATCH_MP (DECIDE ``!n. 4 <= n ==> ~(n < 4)``))
    \\ SIMP_TAC std_ss [addressTheory.word_arith_lemma2])
  \\ `~(dimword (:'a) <= 4) /\ ~(n < 4)` by decide_tac
  \\ once_rewrite_tac [word_copy_fwd_def]
  \\ asm_simp_tac std_ss [WORD_LO,w2n_n2w,LESS_MOD]
QED

Theorem word_copy_fwd_step_byte[local]:
  ∀n a b m dm be value updated.
    good_dimindex (:'a) /\ 0 < n /\ n < dimword (:'a) /\
    byte_copy_range_inv n (a:'a word) b m dm /\
    mem_load_byte_aux m dm be a = SOME value /\
    mem_store_byte_aux m dm be b value = SOME updated ==>
    byte_copy_range_inv (n - 1) (a + 1w) (b + 1w) updated dm /\
    word_copy_fwd be (n2w n) a b m dm =
      word_copy_fwd be (n2w (n - 1)) (a + 1w) (b + 1w) updated dm
Proof
  rpt gen_tac
  \\ strip_tac
  \\ qspecl_then [`n`,`a`,`b`,`m`,`dm`,`0`,`be`,`value`] mp_tac
       byte_copy_range_inv_store
  \\ impl_tac >- simp []
  \\ SIMP_TAC std_ss [WORD_ADD_0]
  \\ disch_then (qx_choose_then `memory` strip_assume_tac)
  \\ gvs []
  \\ qmatch_asmsub_rename_tac `mem_store_byte_aux m dm be b value = SOME updated`
  \\ qspecl_then [`n`,`a`,`b`,`updated`,`dm`,`1`] mp_tac
       byte_copy_range_inv_suffix
  \\ simp []
  \\ strip_tac
  \\ `n - 1 < dimword (:'a)` by decide_tac
  \\ qspecl_then [`n`,`be`,`a`,`b`,`m`,`dm`] mp_tac word_copy_fwd_byte_copy_seq
  \\ impl_tac >- simp []
  \\ disch_tac
  \\ qspecl_then [`n - 1`,`be`,`a + 1w`,`b + 1w`,`updated`,`dm`]
       mp_tac word_copy_fwd_byte_copy_seq
  \\ impl_tac >- simp []
  \\ disch_tac
  \\ qpat_assum `word_copy_fwd be (n2w n) a b m dm = _`
       (PURE_ONCE_REWRITE_TAC o single)
  \\ CONV_TAC (LAND_CONV (REWR_CONV byte_copy_seq_unfold))
  \\ simp []
QED

Theorem byte_align_add_words[local]:
  ∀k a.
    good_dimindex (:'a) /\ k = dimindex (:'a) DIV 8 /\ byte_aligned (a:'a word) ==>
    !i. byte_align (a + n2w (i * k)) = a + n2w (i * k)
Proof
  rpt gen_tac
  \\ strip_tac \\ gen_tac
  \\ `0 < k` by fs [good_dimindex_def]
  \\ qspecl_then [`a`,`i * k`] mp_tac byte_align_add_offset
  \\ impl_tac >- simp []
  \\ qpat_x_assum `k = dimindex (:'a) DIV 8` (PURE_REWRITE_TAC o single o GSYM)
  \\ simp [MULT_DIV]
QED

Theorem byte_copy_range_inv_loop[local]:
  ∀k n d a b m dm.
    good_dimindex (:'a) /\ k = dimindex (:'a) DIV 8 /\ 0 < n /\ d < k /\
    byte_aligned (a:'a word) /\ byte_aligned b /\
    byte_copy_range_inv n a (b + n2w d) m dm ==>
    byte_copy_loop_inv k n d a b m dm
Proof
  rpt gen_tac
  \\ strip_tac
  \\ `0 < k` by fs [good_dimindex_def]
  \\ qspecl_then [`k`,`a`] mp_tac byte_align_add_words
  \\ impl_tac >- simp []
  \\ disch_tac
  \\ qspecl_then [`k`,`b`] mp_tac byte_align_add_words
  \\ impl_tac >- simp []
  \\ disch_tac
  \\ `byte_align (b + n2w d) = b` by (
    irule byte_align_add_byte \\ fs [])
  \\ qpat_x_assum `k = dimindex (:'a) DIV 8` kall_tac
  \\ qpat_x_assum `byte_copy_range_inv _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [byte_copy_range_inv_def])
  \\ PURE_REWRITE_TAC [byte_copy_loop_inv_def]
  \\ conj_tac >- (
    qx_gen_tac `i` \\ strip_tac
    \\ qpat_assum `!i. i < n ==> _` (qspec_then `i * k` mp_tac)
    \\ impl_tac >- qpat_assum `i * k < n` ACCEPT_TAC
    \\ disch_then (strip_assume_tac)
    \\ qpat_assum `!index. byte_align (a + n2w (index * k)) = _`
         (qspec_then `i` SUBST_ALL_TAC)
    \\ fs [])
  \\ conj_tac >- (
    qx_gen_tac `j` \\ strip_tac
    \\ Cases_on `j = 0`
    >- (
      qpat_assum `!i. i < n ==> _` (qspec_then `0` mp_tac)
      \\ impl_tac >- qpat_assum `0 < n` ACCEPT_TAC
      \\ disch_then (strip_assume_tac o SIMP_RULE std_ss [WORD_ADD_0])
      \\ qpat_x_assum `byte_align (b + n2w d) = b` SUBST_ALL_TAC
      \\ fs [])
    \\ `k <= j * k` by (Cases_on `j` \\ fs [MULT_CLAUSES])
    \\ `d <= j * k /\ j * k - d < n /\ d + (j * k - d) = j * k` by decide_tac
    \\ qpat_assum `!i. i < n ==> _` (qspec_then `j * k - d` mp_tac)
    \\ impl_tac >- qpat_assum `j * k - d < n` ACCEPT_TAC
    \\ disch_then (strip_assume_tac)
    \\ qpat_assum `!index. byte_align (b + n2w (index * k)) = _`
         (qspec_then `j` assume_tac)
    \\ gvs [addressTheory.word_arith_lemma1])
  \\ map_every qx_gen_tac [`i`,`j`] \\ strip_tac
  \\ `i * k < n /\ i * k + d < n` by (
    fs [RIGHT_ADD_DISTRIB] \\ decide_tac)
  \\ Cases_on `j = 0`
  >- (
    strip_tac
    \\ qpat_assum `!i j. i < n /\ j < n ==> _`
         (qspecl_then [`i * k + d`,`0`] mp_tac)
    \\ impl_tac >- (conj_tac \\ first_assum ACCEPT_TAC)
    \\ gvs [addressTheory.word_arith_lemma1])
  \\ `k <= j * k` by (Cases_on `j` \\ fs [MULT_CLAUSES])
  \\ `j * k - d < n /\ d + (j * k - d) = j * k` by decide_tac
  \\ strip_tac
  \\ qpat_assum `!i j. i < n /\ j < n ==> _`
       (qspecl_then [`i * k`,`j * k - d`] mp_tac)
  \\ impl_tac >- (conj_tac \\ first_assum ACCEPT_TAC)
  \\ gvs [addressTheory.word_arith_lemma1]
QED

Theorem byte_copy_initial_carry[local]:
  ∀k d m b old be.
    good_dimindex (:'a) /\ k = dimindex (:'a) DIV 8 /\ d < k /\
    (m:'a word -> 'a word_loc) b = Word old ==>
    let hi = if be then old >>> (8 * (k - d)) else old << (8 * (k - d));
        carry = if d = 0 then 0w else old &&
          (if be then -1w << (8 * (k - d)) else -1w >>> (8 * (k - d)))
    in
      (if d = 0 then 0w else
         if be then hi << (8 * (k - d)) else hi >>> (8 * (k - d))) = carry /\
      byte_copy_flush be d carry b m = m
Proof
  rpt gen_tac
  \\ strip_tac
  \\ Cases_on `be`
  \\ gvs [good_dimindex_def,LET_THM,byte_copy_flush_def]
  \\ gvs [DECIDE ``d < 4 <=> d = 0 \/ d = 1 \/ d = 2 \/ d = 3``,
          DECIDE ``d < 8 <=> d = 0 \/ d = 1 \/ d = 2 \/ d = 3 \/
                               d = 4 \/ d = 5 \/ d = 6 \/ d = 7``]
  \\ rw [FUN_EQ_THM,APPLY_UPDATE_THM]
  \\ rpt IF_CASES_TAC
  \\ gvs [theWord_def]
  \\ srw_tac [wordsLib.WORD_BIT_EQ_ss] [WORD_NEG_1_T]
QED

Theorem byte_copy_align_address[local]:
  ∀k d b.
    good_dimindex (:'a) /\ k = dimindex (:'a) DIV 8 /\ d = w2n (b:'a word) MOD k ==>
    b && n2w (k - 1) = n2w d /\
    b && -n2w k = byte_align b /\
    b = byte_align b + n2w d /\
    (d = 0 <=> byte_aligned b) /\ d < k /\
    8 * d < dimindex (:'a) /\ 8 * d < dimword (:'a) /\
    8 * (k - d) = dimindex (:'a) - 8 * d
Proof
  rpt gen_tac
  \\ strip_tac
  \\ `0 < k` by fs [good_dimindex_def]
  \\ `d < k` by fs []
  \\ `w2n b DIV k * k + w2n b MOD k = w2n b` by metis_tac [DIVISION]
  \\ conj_tac >- (
    qspecl_then [`LOG2 k`,`w2n b`] mp_tac WORD_AND_EXP_SUB1
    \\ gvs [good_dimindex_def])
  \\ conj_tac >- (
    gvs [good_dimindex_def,byte_align_def,align_bitwise_and]
    \\ SIMP_TAC std_ss [GSYM WORD_NEG_1,WORD_MUL_LSL,GSYM WORD_NEG_RMUL,
                        WORD_MULT_CLAUSES,EXP,WORD_AND_COMM])
  \\ conj_tac >- (
    gvs [good_dimindex_def,byte_align_def,align_w2n,addressTheory.word_arith_lemma1])
  \\ conj_tac >- (
    gvs [good_dimindex_def,byte_aligned_def,aligned_w2n])
  \\ qpat_x_assum `d < k` mp_tac
  \\ qpat_x_assum `good_dimindex (:'a)` mp_tac
  \\ qpat_x_assum `k = dimindex (:'a) DIV 8` mp_tac
  \\ rpt (pop_assum kall_tac)
  \\ ntac 3 strip_tac
  \\ gvs [good_dimindex_def,dimword_def]
  \\ decide_tac
QED

Theorem evaluate_ByteCopyAlign_start:
  ∀c k d b s l1 l2 n a ret_val old md out.
    good_dimindex (:'a) /\
    dimindex (:'a) = arch_width_bits (c:data_to_word$config).arch_width /\
    k = arch_bytes c.arch_width /\ d = w2n (b:'a word) MOD k /\
    get_vars [0;2;4;6;8] s = SOME [Loc l1 l2;Word n;Word a;Word b;ret_val] /\
    (d <> 0 ==> byte_align b IN s.mdomain /\ s.memory (byte_align b) = Word old) /\
    s.clock <> 0 /\
    lookup ByteCopyLoop_location s.code = SOME (8,ByteCopyLoop_code c,md) ==>
    let carry = if d = 0 then 0w else old &&
          (if c.be then -1w << (8 * (k - d)) else -1w >>> (8 * (k - d)));
        back = if d = 0 then 0 else 8 * (k - d);
        callee = call_env
          [Loc l1 l2;Word n;Word a;Word (byte_align b);ret_val;
           Word carry;Word (n2w (8 * d));Word (n2w back)]
          (lookup ByteCopyLoop_location s.stack_size) (dec_clock s)
    in
      evaluate (ByteCopyLoop_code c,callee) =
        (SOME (Result (Loc l1 l2) [ret_val]),out) ==>
      evaluate (list_Seq [
        Assign 12 (ShiftN Lsl (Op And [Var 6;Const (&(arch_bytes c.arch_width) - 1)]) 3);
        Assign 14 (Op Sub [Const (&(arch_width_bits c.arch_width));Var 12]);
        If Equal 12 (Imm 0)
          (list_Seq [Assign 10 (Const 0);Assign 14 (Const 0)])
          (list_Seq [
            Assign 6 (Op And [Var 6;Const (-&(arch_bytes c.arch_width))]);
            Assign 10 (Op And [Load (Var 6);
              Shift (if c.be then Lsl else Lsr) (Const (-1)) (Var 14)])]);
        Call NONE (SOME ByteCopyLoop_location) [0;2;4;6;8;10;12;14] NONE],s) =
        (SOME (Result (Loc l1 l2) [ret_val]),out)
Proof
  rpt gen_tac
  \\ strip_tac
  \\ `k = dimindex (:'a) DIV 8` by gvs [arch_size]
  \\ qpat_x_assum `dimindex (:'a) = _` (ASSUME_NAMED_TAC "width")
  \\ qspecl_then [`k`,`d`,`b`] mp_tac
       byte_copy_align_address
  \\ impl_tac >- (rpt conj_tac \\ first_assum ACCEPT_TAC)
  \\ strip_tac
  \\ qpat_x_assum `b = byte_align b + n2w d` (ASSUME_NAMED_TAC "address")
  \\ qpat_x_assum `d = w2n b MOD k` kall_tac
  \\ SIMP_TAC std_ss [LET_THM]
  \\ strip_tac
  \\ qpat_x_assum `d = 0 <=> byte_aligned b` kall_tac
  \\ `0 < k /\ 3 < dimindex (:'a) /\ dimindex (:'a) < dimword (:'a) /\
       3 < dimword (:'a) /\ (i2w (&k - 1):'a word) = n2w (k - 1)` by (
    qpat_assum `k = dimindex (:'a) DIV 8` SUBST1_TAC
    \\ qpat_assum `good_dimindex (:'a)`
         (strip_assume_tac o REWRITE_RULE [good_dimindex_def])
    \\ simp [dimword_def,integer_wordTheory.i2w_pos])
  \\ `8 * (k - d) < dimword (:'a)` by decide_tac
  \\ `(i2w (-&k):'a word) = -n2w k` by (
    SIMP_TAC std_ss [GSYM integer_wordTheory.MULT_MINUS_ONE,
                    integer_wordTheory.i2w_pos,GSYM WORD_NEG_MUL])
  \\ `((n2w d:'a word) << 3) = n2w (8 * d)` by (
    qpat_assum `3 < dimindex (:'a)`
      (mp_tac o MATCH_MP (DECIDE ``!n. 3 < n ==> ~(n - 1 < 3)``))
    \\ SIMP_TAC (srw_ss()) [word_lsl_n2w,MULT_COMM])
  \\ `(n2w (dimindex (:'a)) - n2w (8 * d):'a word) = n2w (8 * (k - d))` by (
    qpat_assum `8 * (k - d) = dimindex (:'a) - 8 * d` (PURE_REWRITE_TAC o single)
    \\ qpat_assum `8 * d < dimindex (:'a)`
      (mp_tac o MATCH_MP (DECIDE ``!a b. b < a ==> ~(a < b)``))
    \\ SIMP_TAC std_ss [addressTheory.word_arith_lemma2])
  \\ `(n2w (dimindex (:'a)) + -1w * n2w (8 * d):'a word) =
       n2w (8 * (k - d))` by (
    PURE_REWRITE_TAC [GSYM WORD_NEG_MUL,GSYM word_sub_def]
    \\ first_assum ACCEPT_TAC)
  \\ `((n2w (8 * d):'a word) = 0w <=> d = 0)` by (
    qpat_assum `8 * d < dimword (:'a)` mp_tac
    \\ SIMP_TAC (srw_ss()) [n2w_11,LESS_MOD])
  \\ `(d <> 0 ==> 8 * (k - d) < dimindex (:'a))` by decide_tac
  \\ `(d = 0 ==> byte_align b = b)` by (
    strip_tac
    \\ LABEL_ASSUM "address" mp_tac
    \\ qpat_assum `d = 0` SUBST1_TAC
    \\ REWRITE_TAC [WORD_ADD_0]
    \\ disch_then (ACCEPT_TAC o GSYM))
  \\ qpat_x_assum `k = arch_bytes c.arch_width` (SUBST_ALL_TAC o SYM)
  \\ LABEL_X_ASSUM "width" (SUBST_ALL_TAC o SYM)
  \\ qpat_x_assum `k = dimindex (:'a) DIV 8` kall_tac
  \\ qpat_x_assum `8 * (k - d) = dimindex (:'a) - 8 * d` kall_tac
  \\ fs [wordSemTheory.get_vars_def,AllCaseEqs()]
  \\ qpat_assum `3 < dimindex (:'a)`
       (ASSUME_TAC o REWRITE_RULE [GSYM NOT_LESS_EQUAL])
  \\ qpat_assum `d <> 0 ==> 8 * (k - d) < dimindex (:'a)`
       (ASSUME_TAC o REWRITE_RULE [GSYM NOT_LESS_EQUAL])
  \\ Cases_on `d = 0`
  >- (
    qpat_x_assum `d = 0` SUBST_ALL_TAC
    \\ fs [list_Seq_def,wordSemTheory.evaluate_def,
            wordSemTheory.get_var_def,wordSemTheory.get_vars_def,
            wordSemTheory.get_var_imm_def,wordSemTheory.word_cmp_def,
            wordSemTheory.word_exp_def,wordSemTheory.word_op_def,
            wordSemTheory.word_sh_def,wordSemTheory.the_words_def,
            wordSemTheory.set_var_def,wordSemTheory.fix_clock_def,lookup_insert,
            wordSemTheory.bad_dest_args_def,wordSemTheory.find_code_def,
            wordSemTheory.add_ret_loc_def,wordSemTheory.call_env_def,
            wordSemTheory.dec_clock_def,wordSemTheory.bad_fun_return_def,
            integer_wordTheory.i2w_pos,integer_wordTheory.i2w_minus_1,
            w2n_n2w,LESS_MOD,WORD_AND_COMM])
  \\ Cases_on `c.be`
  >- (
    qpat_x_assum `evaluate (ByteCopyLoop_code c,_) = _` mp_tac
    \\ asm_simp_tac (srw_ss()) [wordSemTheory.call_env_def,wordSemTheory.dec_clock_def]
    \\ strip_tac
    \\ RULE_ASSUM_TAC (SIMP_RULE std_ss [wordSemTheory.get_var_def])
    \\ asm_simp_tac (srw_ss())
         [LET_THM,GREATER_EQ,list_Seq_def,wordSemTheory.evaluate_def,
          wordSemTheory.get_var_def,wordSemTheory.get_vars_def,
          wordSemTheory.get_var_imm_def,wordSemTheory.word_cmp_def,
          wordSemTheory.word_exp_def,wordSemTheory.word_op_def,
          wordSemTheory.word_sh_def,wordSemTheory.the_words_def,
          wordSemTheory.set_var_def,wordSemTheory.mem_load_def,
          wordSemTheory.fix_clock_def,lookup_insert,
          wordSemTheory.bad_dest_args_def,wordSemTheory.find_code_def,
          wordSemTheory.add_ret_loc_def,wordSemTheory.call_env_def,
          wordSemTheory.dec_clock_def,wordSemTheory.bad_fun_return_def,
          integer_wordTheory.i2w_pos,integer_wordTheory.i2w_minus_1,
          w2n_n2w,LESS_MOD])
  \\ qpat_x_assum `evaluate (ByteCopyLoop_code c,_) = _` mp_tac
  \\ asm_simp_tac (srw_ss()) [wordSemTheory.call_env_def,wordSemTheory.dec_clock_def]
  \\ strip_tac
  \\ RULE_ASSUM_TAC (SIMP_RULE std_ss [wordSemTheory.get_var_def])
  \\ asm_simp_tac (srw_ss())
       [LET_THM,GREATER_EQ,list_Seq_def,wordSemTheory.evaluate_def,
        wordSemTheory.get_var_def,wordSemTheory.get_vars_def,
        wordSemTheory.get_var_imm_def,wordSemTheory.word_cmp_def,
        wordSemTheory.word_exp_def,wordSemTheory.word_op_def,
        wordSemTheory.word_sh_def,wordSemTheory.the_words_def,
        wordSemTheory.set_var_def,wordSemTheory.mem_load_def,
        wordSemTheory.fix_clock_def,lookup_insert,
        wordSemTheory.bad_dest_args_def,wordSemTheory.find_code_def,
        wordSemTheory.add_ret_loc_def,wordSemTheory.call_env_def,
        wordSemTheory.dec_clock_def,wordSemTheory.bad_fun_return_def,
        integer_wordTheory.i2w_pos,integer_wordTheory.i2w_minus_1,
        w2n_n2w,LESS_MOD]
QED

Theorem byte_copy_memory_rel_update[local]:
  byte_copy_memory_rel k blocks (base:'a word) actual model ==>
  byte_copy_memory_rel k blocks base ((p =+ value) actual) ((p =+ value) model)
Proof
  rw [byte_copy_memory_rel_def,APPLY_UPDATE_THM]
  \\ rpt IF_CASES_TAC \\ fs []
QED

Theorem byte_copy_aligned_test[local]:
  ∀k a.
    good_dimindex (:'a) /\ k = dimindex (:'a) DIV 8 ==>
    ((a:'a word) && n2w (k - 1) = 0w <=> byte_aligned a)
Proof
  rpt gen_tac
  \\ strip_tac
  \\ qspecl_then [`LOG2 k`,`w2n a`] mp_tac WORD_AND_EXP_SUB1
  \\ gvs [good_dimindex_def,byte_aligned_def,aligned_w2n,
          dimword_def,n2w_11,MOD_MOD_LESS_EQ]
QED

Theorem evaluate_ByteCopyAlign_byte:
  ∀s n a b ret_val l1 l2 value updated c md out.
    good_dimindex (:'a) /\ 0 < n /\
    get_vars [0;2;4;6;8] s =
      SOME [Loc l1 l2;Word (n2w n);Word (a:'a word);Word b;ret_val] /\
    mem_load_byte_aux s.memory s.mdomain s.be a = SOME value /\
    mem_store_byte_aux s.memory s.mdomain s.be b value = SOME updated /\
    s.clock <> 0 /\
    lookup ByteCopyAlign_location s.code = SOME (5,ByteCopyAlign_code c,md) /\
    evaluate (ByteCopyAlign_code c,
      call_env [Loc l1 l2;Word (n2w (n - 1));Word (a + 1w);Word (b + 1w);ret_val]
        (lookup ByteCopyAlign_location s.stack_size)
        (s with <|clock := s.clock - 1;memory := updated|>)) =
      (SOME (Result (Loc l1 l2) [ret_val]),out) ==>
    evaluate (list_Seq [
      Inst (Mem Load8 1 (Addr 4 0));
      Inst (Mem Store8 1 (Addr 6 0));
      Assign 2 (Op Sub [Var 2;Const 1]);
      Assign 4 (Op Add [Var 4;Const 1]);
      Assign 6 (Op Add [Var 6;Const 1]);
      Call NONE (SOME ByteCopyAlign_location) [0;2;4;6;8] NONE],s) =
      (SOME (Result (Loc l1 l2) [ret_val]),out)
Proof
  rpt gen_tac
  \\ strip_tac
  \\ fs [wordSemTheory.get_vars_def,AllCaseEqs()]
  \\ `~(n < 1)` by decide_tac
  \\ `(n2w n + -1w:'a word) = n2w (n - 1)` by (
    PURE_REWRITE_TAC [GSYM word_sub_def]
    \\ qpat_assum `~(n < 1)` mp_tac
    \\ SIMP_TAC std_ss [addressTheory.word_arith_lemma2])
  \\ qpat_x_assum `evaluate (ByteCopyAlign_code c,_) = _`
       (ASSUME_TAC o SIMP_RULE (srw_ss())
          [wordSemTheory.call_env_def,wordSemTheory.dec_clock_def])
  \\ RULE_ASSUM_TAC (SIMP_RULE std_ss [wordSemTheory.get_var_def])
  \\ asm_simp_tac (srw_ss())
       [LET_THM,list_Seq_def,wordSemTheory.evaluate_def,wordSemTheory.inst_def,
        wordSemTheory.word_exp_def,wordSemTheory.word_op_def,
        wordSemTheory.the_words_def,wordSemTheory.get_var_def,
        wordSemTheory.get_vars_def,wordSemTheory.set_var_def,
        wordSemTheory.fix_clock_def,lookup_insert,
        wordSemTheory.bad_dest_args_def,wordSemTheory.find_code_def,
        wordSemTheory.add_ret_loc_def,wordSemTheory.call_env_def,
        wordSemTheory.dec_clock_def,wordSemTheory.bad_fun_return_def,
        integer_wordTheory.i2w_pos,good_dimindex_w2w_byte]
QED

Definition byte_copy_align_inv_def:
  byte_copy_align_inv k n prefix_bytes (a:'a word) b actual model dm <=>
    prefix_bytes < k /\ byte_aligned (a + n2w prefix_bytes) /\
    (!i. i < prefix_bytes ==> ~byte_aligned (a + n2w i)) /\
    byte_copy_range_inv n a b model dm /\
    (!i. i < n ==> actual (byte_align (a + n2w i)) = model (byte_align (a + n2w i))) /\
    (!i. i <= prefix_bytes ==>
      actual (byte_align (b + n2w i)) = model (byte_align (b + n2w i))) /\
    byte_copy_memory_rel k ((n - prefix_bytes) DIV (3 * k))
      (byte_align (b + n2w prefix_bytes)) actual model
End

Theorem byte_copy_align_step[local]:
  ∀k n prefix_bytes a b actual model dm be final.
    good_dimindex (:'a) /\ n < dimword (:'a) /\
    0 < prefix_bytes /\ prefix_bytes <= n /\
    byte_copy_align_inv k n prefix_bytes (a:'a word) b actual model dm /\
    word_copy_fwd be (n2w n) a b model dm = SOME final ==>
    ?value actual_after model_after.
      mem_load_byte_aux actual dm be a = SOME value /\
      mem_store_byte_aux actual dm be b value = SOME actual_after /\
      byte_copy_align_inv k (n - 1) (prefix_bytes - 1)
        (a + 1w) (b + 1w) actual_after model_after dm /\
      word_copy_fwd be (n2w (n - 1)) (a + 1w) (b + 1w) model_after dm = SOME final
Proof
  rpt gen_tac
  \\ strip_tac
  \\ qpat_x_assum `byte_copy_align_inv _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [byte_copy_align_inv_def])
  \\ `0 < n /\ prefix_bytes - 1 < k /\
       n - 1 - (prefix_bytes - 1) = n - prefix_bytes /\
       1 + (prefix_bytes - 1) = prefix_bytes` by (
    qpat_x_assum `0 < prefix_bytes` mp_tac
    \\ qpat_x_assum `prefix_bytes <= n` mp_tac
    \\ qpat_x_assum `prefix_bytes < k` mp_tac
    \\ rpt (pop_assum kall_tac)
    \\ decide_tac)
  \\ qspecl_then [`n`,`a`,`b`,`model`,`dm`,`0`,`be`] mp_tac
       byte_copy_range_inv_load
  \\ impl_tac >- (conj_tac \\ first_assum ACCEPT_TAC)
  \\ SIMP_TAC std_ss [WORD_ADD_0]
  \\ disch_then (qx_choose_then `value` assume_tac)
  \\ `actual (byte_align a) = model (byte_align a)` by (
    qpat_assum `!i. i < n ==> actual (byte_align (a + n2w i)) = _`
      (qspec_then `0` mp_tac)
    \\ qpat_assum `0 < n` mp_tac
    \\ SIMP_TAC std_ss [WORD_ADD_0])
  \\ `actual (byte_align b) = model (byte_align b)` by (
    qpat_assum `!i. i <= prefix_bytes ==> _` (qspec_then `0` mp_tac)
    \\ SIMP_TAC std_ss [WORD_ADD_0,ZERO_LESS_EQ])
  \\ `?old. model (byte_align b) = Word old /\ byte_align b IN dm` by (
    qpat_assum `byte_copy_range_inv _ _ _ _ _`
         (strip_assume_tac o REWRITE_RULE [byte_copy_range_inv_def])
    \\ qpat_assum `!i. i < n ==> _ /\ _ /\ _ /\ _` (qspec_then `0` mp_tac)
    \\ qpat_assum `0 < n` mp_tac
    \\ SIMP_TAC std_ss [WORD_ADD_0]
    \\ rpt strip_tac
    \\ fs [isWord_exists])
  \\ qmatch_asmsub_rename_tac `model (byte_align b) = Word old_word`
  \\ qabbrev_tac `actual_after =
       (byte_align b =+ Word (set_byte b value old_word be)) actual`
  \\ qabbrev_tac `model_after =
       (byte_align b =+ Word (set_byte b value old_word be)) model`
  \\ `mem_load_byte_aux actual dm be a = SOME value` by (
    fs [wordSemTheory.mem_load_byte_aux_def])
  \\ `mem_store_byte_aux actual dm be b value = SOME actual_after` by (
    simp [wordSemTheory.mem_store_byte_aux_def,Abbr `actual_after`])
  \\ `mem_store_byte_aux model dm be b value = SOME model_after` by (
    simp [wordSemTheory.mem_store_byte_aux_def,Abbr `model_after`])
  \\ qspecl_then [`n`,`a`,`b`,`model`,`dm`,`be`,`value`,`model_after`] mp_tac
       word_copy_fwd_step_byte
  \\ impl_tac >- (rpt conj_tac \\ first_assum ACCEPT_TAC)
  \\ strip_tac
  \\ qpat_x_assum `word_copy_fwd be (n2w n) a b model dm = word_copy_fwd _ _ _ _ _ _`
       mp_tac
  \\ qpat_x_assum `word_copy_fwd be (n2w n) a b model dm = SOME final` SUBST1_TAC
  \\ disch_then (ASSUME_TAC o SYM)
  \\ qexistsl_tac [`value`,`actual_after`,`model_after`]
  \\ simp [byte_copy_align_inv_def,Abbr `actual_after`,Abbr `model_after`,
           addressTheory.word_arith_lemma1,byte_copy_memory_rel_update,APPLY_UPDATE_THM]
QED

Theorem CopyByteLoop_thm:
  !n c k d a b hi ret_val l1 l2 (s:('a,'c,'ffi) wordSem$state) model final smx.
    good_dimindex (:'a) /\ dimindex (:'a) = arch_width_bits c.arch_width /\
    k = dimindex (:'a) DIV 8 /\ c.be = s.be /\
    n < dimword (:'a) /\ d < k /\
    byte_aligned a /\ byte_aligned b /\
    byte_copy_loop_inv k n d a b model s.mdomain /\
    byte_copy_memory_rel k (n DIV (3 * k)) b s.memory model /\
    (?md. lookup ByteCopyLoop_location s.code = SOME (8,ByteCopyLoop_code c,md)) /\
    (?md. lookup ByteCopyAdd_location s.code = SOME (5,ByteCopyAdd_code,md)) /\
    option_le s.stack_max smx /\
    option_le (OPTION_MAP2 $+ (stack_size s.stack)
      (lookup ByteCopyLoop_location s.stack_size)) smx /\
    option_le (OPTION_MAP2 $+ (stack_size s.stack)
      (lookup ByteCopyAdd_location s.stack_size)) smx /\
    n + 1 <= s.clock /\
    get_var 0 s = SOME (Loc l1 l2) /\
    get_var 2 s = SOME (Word (n2w n)) /\
    get_var 4 s = SOME (Word a) /\
    get_var 6 s = SOME (Word b) /\
    get_var 8 s = SOME ret_val /\
    get_var 10 s = SOME (Word (if d = 0 then 0w else
      if c.be then hi << (8 * (k - d)) else hi >>> (8 * (k - d)))) /\
    get_var 12 s = SOME (Word (n2w (8 * d))) /\
    get_var 14 s = SOME (Word (n2w (if d = 0 then 0 else 8 * (k - d)))) /\
    word_copy_fwd s.be (n2w n) a (b + n2w d)
      (byte_copy_flush s.be d
        (if d = 0 then 0w else
          if c.be then hi << (8 * (k - d)) else hi >>> (8 * (k - d))) b model)
      s.mdomain = SOME final ==>
    ?remaining_clock used_stack.
      remaining_clock <= s.clock /\ option_le used_stack smx /\
      evaluate (ByteCopyLoop_code c,s) =
        (SOME (Result (Loc l1 l2) [ret_val]),
         s with <| clock := remaining_clock; memory := final;
                   locals := LN; locals_size := SOME 0; stack_max := used_stack |>)
Proof
  completeInduct_on `n`
  \\ map_every qx_gen_tac
       [`c`,`k`,`d`,`a`,`b`,`hi`,`ret_val`,`l1`,`l2`,`s`,`model`,`final`,`smx`]
  \\ strip_tac
  \\ qmatch_asmsub_rename_tac
       `lookup ByteCopyLoop_location s.code = SOME (8,ByteCopyLoop_code c,loop_md)`
  \\ qmatch_asmsub_rename_tac
       `lookup ByteCopyAdd_location s.code = SOME (5,ByteCopyAdd_code,add_md)`
  \\ qpat_x_assum `!m. m < n ==> _` (ASSUME_NAMED_TAC "IH")
  \\ `0 < k /\ d < dimindex (:'a) DIV 8 /\ arch_bytes c.arch_width = k /\
      3 * k < dimword (:'a) /\ (3 * k) MOD 4 = 0 /\
      8 * d < dimindex (:'a) /\ 8 * d < dimword (:'a) /\
      (if d = 0 then 0 else 8 * (k - d)) < dimindex (:'a) /\
      (if d = 0 then 0 else 8 * (k - d)) < dimword (:'a)` by (
    gvs [good_dimindex_def,arch_size,dimword_def]
    \\ Cases_on `d = 0` \\ fs [] \\ decide_tac)
  \\ qpat_x_assum `k = dimindex (:'a) DIV 8` (ASSUME_NAMED_TAC "k_def")
  \\ qpat_x_assum `dimindex (:'a) = _` (ASSUME_NAMED_TAC "width")
  \\ Cases_on `n < 3 * k`
  >- (
    `n DIV (3 * k) = 0` by (irule LESS_DIV_EQ_ZERO \\ ASM_REWRITE_TAC [])
    \\ `s.memory = model` by fs [byte_copy_memory_rel_zero]
    \\ qpat_x_assum `s.memory = model` (SUBST_ALL_TAC o GSYM)
    \\ `d <> 0 ==> b IN s.mdomain /\
         s.memory b = Word (theWord (s.memory b))`
    by (
      strip_tac
      \\ `0 < n + d` by decide_tac
      \\ qpat_assum `byte_copy_loop_inv _ _ _ _ _ _ _`
           (strip_assume_tac o REWRITE_RULE [byte_copy_loop_inv_def])
      \\ qpat_x_assum `!j. j * k < n + d ==> _` (qspec_then `0` mp_tac)
      \\ simp [isWord_exists]
      \\ strip_tac
      \\ fs [theWord_def])
    \\ qmatch_asmsub_abbrev_tac `get_var 10 s = SOME (Word carry)`
    \\ qspecl_then [`c`,`d`,`s`,`b`,`carry`,`theWord (s.memory b)`] mp_tac
         evaluate_ByteCopyFlush
    \\ impl_tac >- gvs []
    \\ SIMP_TAC std_ss [LET_THM]
    \\ disch_tac
    \\ qmatch_asmsub_abbrev_tac `evaluate (_,s) = (NONE,after_flush)`
    \\ `after_flush.memory = byte_copy_flush s.be d carry b s.memory`
    by (
      Cases_on `d = 0`
      \\ fs [Abbr `after_flush`,byte_copy_flush_def,wordSemTheory.set_var_def])
    \\ `after_flush.clock = s.clock /\ after_flush.termdep = s.termdep`
    by (
      Cases_on `d = 0`
      \\ fs [Abbr `after_flush`,wordSemTheory.set_var_def])
    \\ `n DIV 4 < s.clock` by (
      `n DIV 4 <= n` by simp [DIV_LESS_EQ]
      \\ decide_tac)
    \\ qspecl_then [`after_flush`,`n2w n`,`a`,`b + n2w d`,
                     `ret_val`,`l1`,`l2`,`final`] mp_tac
         CopyByteAdd_call
    \\ impl_tac >- (
      Cases_on `d = 0`
      \\ gvs [Abbr `after_flush`,Abbr `carry`,wordSemTheory.get_vars_def,
              wordSemTheory.get_var_def,wordSemTheory.set_var_def,
              lookup_insert,byte_copy_flush_def])
    \\ disch_tac
    \\ qexistsl_tac [`s.clock - (n DIV 4 + 1)`,
         `OPTION_MAP2 MAX s.stack_max
           (OPTION_MAP2 $+ (stack_size s.stack)
             (lookup ByteCopyAdd_location s.stack_size))`]
    \\ simp [option_le_max]
    \\ qpat_x_assum `c.be = s.be` kall_tac
    \\ once_rewrite_tac [ByteCopyLoop_code_def]
    \\ SIMP_TAC std_ss [LET_THM,Once wordSemTheory.evaluate_def]
    \\ simp [wordSemTheory.get_var_imm_def,wordSemTheory.word_cmp_def,
             integer_wordTheory.i2w_pos,WORD_LO]
    \\ once_rewrite_tac [list_Seq_def]
    \\ SIMP_TAC std_ss [Once wordSemTheory.evaluate_def]
    \\ simp [wordSemTheory.fix_clock_def]
    \\ once_rewrite_tac [list_Seq_def]
    \\ simp []
    \\ Cases_on `d = 0`
    \\ fs [Abbr `after_flush`,wordSemTheory.set_var_def,
            wordSemTheory.state_component_equality])
  \\ `0 < 3 * k /\ 3 * k <= n /\ n - 3 * k < n` by decide_tac
  \\ `n DIV (3 * k) = SUC ((n - 3 * k) DIV (3 * k))` by (
    `1 <= n DIV (3 * k)` by (
      qspecl_then [`1`,`n`,`3 * k`] mp_tac X_LE_DIV
      \\ simp [])
    \\ `(n - 3 * k) DIV (3 * k) = n DIV (3 * k) - 1` by (
      irule (DIV_SUB |> Q.INST [`q` |-> `1`] |> SIMP_RULE std_ss [MULT_CLAUSES])
      \\ decide_tac)
    \\ pop_assum SUBST1_TAC
    \\ decide_tac)
  \\ `?w1 w2 w3.
       model a = Word w1 /\ model (a + n2w k) = Word w2 /\
       model (a + n2w (2 * k)) = Word w3 /\
       s.memory a = Word w1 /\ s.memory (a + n2w k) = Word w2 /\
       s.memory (a + n2w (2 * k)) = Word w3 /\
       a IN s.mdomain /\ a + n2w k IN s.mdomain /\
       a + n2w (2 * k) IN s.mdomain` by (
    `0 < n /\ k < n /\ 2 * k < n /\ k <= n /\ 2 * k <= n` by decide_tac
    \\ qpat_assum `byte_copy_loop_inv _ _ _ _ _ _ _`
         (strip_assume_tac o REWRITE_RULE [byte_copy_loop_inv_def])
    \\ qspecl_then [`k`,`n`,`b`,`s.memory`,`model`,`a`,`d`] mp_tac
         byte_copy_memory_rel_source
    \\ impl_tac >- (rpt conj_tac \\ first_assum ACCEPT_TAC)
    \\ disch_then (assume_named_tac "same_words")
    \\ LABEL_ASSUM "same_words" (qspec_then `0` mp_tac)
    \\ LABEL_ASSUM "same_words" (qspec_then `1` mp_tac)
    \\ LABEL_X_ASSUM "same_words" (qspec_then `2` mp_tac)
    \\ qpat_assum `!i. i * k < n ==> _` (qspec_then `0` mp_tac)
    \\ qpat_assum `!i. i * k < n ==> _` (qspec_then `1` mp_tac)
    \\ qpat_x_assum `!i. i * k < n ==> _` (qspec_then `2` mp_tac)
    \\ simp [isWord_exists]
    \\ rpt strip_tac
    \\ fs [])
  \\ qmatch_asmsub_rename_tac `model a = Word first_word`
  \\ qmatch_asmsub_rename_tac `model (a + n2w k) = Word second_word`
  \\ qmatch_asmsub_rename_tac `model (a + n2w (2 * k)) = Word third_word`
  \\ `?old0 old1 old2.
       model b = Word old0 /\ model (b + n2w k) = Word old1 /\
       model (b + n2w (2 * k)) = Word old2 /\
       b IN s.mdomain /\ b + n2w k IN s.mdomain /\
       b + n2w (2 * k) IN s.mdomain` by (
    `0 < n + d /\ k < n + d /\ 2 * k < n + d` by decide_tac
    \\ qpat_assum `byte_copy_loop_inv _ _ _ _ _ _ _`
         (strip_assume_tac o REWRITE_RULE [byte_copy_loop_inv_def])
    \\ qpat_assum `!j. j * k < n + d ==> _` (qspec_then `0` mp_tac)
    \\ qpat_assum `!j. j * k < n + d ==> _` (qspec_then `1` mp_tac)
    \\ qpat_x_assum `!j. j * k < n + d ==> _` (qspec_then `2` mp_tac)
    \\ simp [isWord_exists]
    \\ rpt strip_tac
    \\ fs [])
  \\ qmatch_asmsub_rename_tac `model b = Word old_first`
  \\ qmatch_asmsub_rename_tac `model (b + n2w k) = Word old_second`
  \\ qmatch_asmsub_rename_tac `model (b + n2w (2 * k)) = Word old_third`
  \\ `DISJOINT (set [a;a + n2w k;a + n2w (2 * k)])
               (set [b;b + n2w k;b + n2w (2 * k)])` by (
    `k <= n /\ 2 * k <= n /\ 0 < n + d /\ k < n + d /\ 2 * k < n + d` by decide_tac
    \\ qpat_assum `byte_copy_loop_inv _ _ _ _ _ _ _`
         (strip_assume_tac o REWRITE_RULE [byte_copy_loop_inv_def])
    \\ qpat_assum `!i j. _` (qspecl_then [`0`,`0`] mp_tac)
    \\ qpat_assum `!i j. _` (qspecl_then [`0`,`1`] mp_tac)
    \\ qpat_assum `!i j. _` (qspecl_then [`0`,`2`] mp_tac)
    \\ qpat_assum `!i j. _` (qspecl_then [`1`,`0`] mp_tac)
    \\ qpat_assum `!i j. _` (qspecl_then [`1`,`1`] mp_tac)
    \\ qpat_assum `!i j. _` (qspecl_then [`1`,`2`] mp_tac)
    \\ qpat_assum `!i j. _` (qspecl_then [`2`,`0`] mp_tac)
    \\ qpat_assum `!i j. _` (qspecl_then [`2`,`1`] mp_tac)
    \\ qpat_x_assum `!i j. _` (qspecl_then [`2`,`2`] mp_tac)
    \\ simp [])
  \\ `!base:'a word. ALL_DISTINCT [base;base + n2w k;base + n2w (2 * k)]` by (
    `ALL_DISTINCT [(0w:'a word);n2w k;n2w (2 * k)]` by
      (LABEL_ASSUM "k_def" mp_tac
       \\ gvs [good_dimindex_def,ALL_DISTINCT,n2w_11,dimword_def])
    \\ qx_gen_tac `base`
    \\ qspecl_then [`[(0w:'a word);n2w k;n2w (2 * k)]`,`\p. base + p`]
         mp_tac ALL_DISTINCT_MAP_INJ
    \\ pop_assum mp_tac
    \\ SIMP_TAC std_ss [MAP,WORD_ADD_0,WORD_EQ_ADD_LCANCEL])
  \\ `ALL_DISTINCT [a;a + n2w k;a + n2w (2 * k);
                     b;b + n2w k;b + n2w (2 * k)]` by (
    qspecl_then [`[a;a + n2w k;a + n2w (2 * k)]`,
                 `[b;b + n2w k;b + n2w (2 * k)]`] mp_tac ALL_DISTINCT_APPEND'
    \\ qpat_x_assum `DISJOINT _ _` mp_tac
    \\ qpat_x_assum `!base:'a word. ALL_DISTINCT _` mp_tac
    \\ SIMP_TAC std_ss [APPEND])
  \\ `!out1 out2 out3.
       byte_copy_loop_inv k (n - 3 * k) d
         (a + n2w (3 * k)) (b + n2w (3 * k))
         ((b + n2w (2 * k) =+ Word out3)
           ((b + n2w k =+ Word out2) ((b =+ Word out1) model))) s.mdomain` by (
    rpt gen_tac
    \\ irule byte_copy_loop_inv_step
    \\ rpt conj_tac \\ first_assum ACCEPT_TAC)
  \\ `!out1 out2 out3.
       byte_copy_memory_rel k ((n - 3 * k) DIV (3 * k)) (b + n2w (3 * k))
         ((b + n2w (2 * k) =+ Word out3)
           ((b + n2w k =+ Word out2) ((b =+ Word out1) s.memory)))
         ((b + n2w (2 * k) =+ Word out3)
           ((b + n2w k =+ Word out2) ((b =+ Word out1) model)))` by (
    rpt gen_tac
    \\ irule byte_copy_memory_rel_step
    \\ qpat_x_assum `n DIV (3 * k) = SUC ((n - 3 * k) DIV (3 * k))`
         (PURE_REWRITE_TAC o single o GSYM)
    \\ first_assum ACCEPT_TAC)
  \\ `byte_aligned (n2w (3 * k):'a word)` by (
    `(n2w (3 * k):'a word) = 3w * bytes_in_word` by
      (LABEL_ASSUM "k_def" mp_tac
       \\ simp [bytes_in_word_def,word_mul_n2w])
    \\ pop_assum SUBST1_TAC
    \\ simp [byte_align_mult_bytes_in_word])
  \\ `byte_aligned (a + n2w (3 * k)) /\ byte_aligned (b + n2w (3 * k))`
  by (
    rpt conj_tac
    \\ irule byte_aligned_add
    \\ conj_tac \\ first_assum ACCEPT_TAC)
  \\ LABEL_X_ASSUM "IH" (qspec_then `n - 3 * k` mp_tac)
  \\ impl_tac >- first_assum ACCEPT_TAC
  \\ disch_then (ASSUME_NAMED_TAC "IH")
  \\ Cases_on `d = 0`
  >- (
    qpat_x_assum `d = 0` SUBST_ALL_TAC
    \\ LABEL_X_ASSUM "IH" mp_tac
    \\ RULE_ASSUM_TAC (SIMP_RULE std_ss
         [COND_CLAUSES,MULT_CLAUSES,ADD_CLAUSES,WORD_ADD_0,byte_copy_flush_zero])
    \\ disch_then (ASSUME_NAMED_TAC "IH")
    \\ qspecl_then [`k`,`a`,`b`,`model`,`s.mdomain`,`s.be`,
                     `first_word`,`second_word`,`third_word`,
                     `old_first`,`old_second`,`old_third`] mp_tac
         word_copy_fwd_three_words
    \\ impl_tac >- (
      LABEL_ASSUM "k_def" assume_tac
      \\ SIMP_TAC std_ss [EVERY_DEF]
      \\ rpt conj_tac \\ first_assum ACCEPT_TAC)
    \\ disch_tac
    \\ qmatch_asmsub_abbrev_tac
         `word_copy_fwd s.be (n2w (3 * k)) a b model s.mdomain = SOME model_after`
    \\ `3 * k + (n - 3 * k) = n` by (
      once_rewrite_tac [ADD_COMM]
      \\ irule SUB_ADD
      \\ first_assum ACCEPT_TAC)
    \\ qspecl_then [`3 * k`,`n - 3 * k`,`a`,`b`,`model`,`s.mdomain`,`s.be`]
         mp_tac word_copy_fwd_add
    \\ impl_tac >- (
      qpat_x_assum `3 * k + (n - 3 * k) = n` (PURE_REWRITE_TAC o single)
      \\ rpt conj_tac \\ first_assum ACCEPT_TAC)
    \\ qpat_x_assum `3 * k + (n - 3 * k) = n` SUBST1_TAC
    \\ qpat_x_assum `word_copy_fwd s.be (n2w n) a b model s.mdomain = SOME final`
         SUBST1_TAC
    \\ qpat_x_assum `word_copy_fwd s.be (n2w (3 * k)) a b model s.mdomain = SOME model_after`
         SUBST1_TAC
    \\ SIMP_TAC std_ss []
    \\ disch_then (ASSUME_TAC o GSYM)
    \\ qspecl_then [`c`,`s`,`a`,`b`,`(n2w k:'a word)`] mp_tac
         evaluate_ByteCopyWords
    \\ impl_tac >- (
      qpat_x_assum `arch_bytes c.arch_width = k` SUBST1_TAC
      \\ SIMP_TAC std_ss [word_mul_n2w]
      \\ rpt conj_tac \\ first_assum ACCEPT_TAC)
    \\ qpat_assum `s.memory a = Word first_word` mp_tac
    \\ qpat_assum `s.memory (a + n2w k) = Word second_word` mp_tac
    \\ qpat_assum `s.memory (a + n2w (2 * k)) = Word third_word` mp_tac
    \\ SIMP_TAC std_ss [word_mul_n2w]
    \\ ntac 3 (disch_then kall_tac)
    \\ disch_tac
    \\ qmatch_asmsub_abbrev_tac `evaluate (ByteCopyWords_code c,s) = (NONE,after_words)`
    \\ `byte_copy_loop_inv k (n - 3 * k) 0
           (a + n2w (3 * k)) (b + n2w (3 * k)) model_after s.mdomain`
    by (
      qpat_x_assum `!out1 out2 out3. byte_copy_loop_inv _ _ _ _ _ _ _`
           (qspecl_then [`first_word`,`second_word`,`third_word`] mp_tac)
      \\ simp [Abbr `model_after`])
    \\ `byte_copy_memory_rel k ((n - 3 * k) DIV (3 * k)) (b + n2w (3 * k))
           after_words.memory model_after`
    by (
      qpat_x_assum `!out1 out2 out3. byte_copy_memory_rel _ _ _ _ _`
           (qspecl_then [`first_word`,`second_word`,`third_word`] mp_tac)
      \\ simp [Abbr `after_words`,Abbr `model_after`,wordSemTheory.set_var_def])
    \\ `n - 3 * k < dimword (:'a) /\ n - 3 * k + 1 <= s.clock - 1` by simp []
    \\ qabbrev_tac `callee = wordSem$call_env
         [Loc l1 l2;Word (n2w (n - 3 * k));Word (a + n2w (3 * k));
          Word (b + n2w (3 * k));ret_val;Word 0w;Word 0w;Word 0w]
         (lookup ByteCopyLoop_location s.stack_size)
         (s with <|clock := s.clock - 1; memory := after_words.memory|>)`
    \\ LABEL_X_ASSUM "IH"
         (qspecl_then [`c`,`k`,`0`,`a + n2w (3 * k)`,`b + n2w (3 * k)`,
                        `(0w:'a word)`,`ret_val`,`l1`,`l2`,`callee`,`model_after`,
                        `final`,`smx`] mp_tac)
    \\ impl_tac >- (
      LABEL_ASSUM "k_def" assume_tac
      \\ LABEL_ASSUM "width" assume_tac
      \\ gvs [Abbr `callee`,wordSemTheory.call_env_def,wordSemTheory.get_var_def,
           lookup_fromList2,lookup_fromList,option_le_max,byte_copy_flush_zero])
    \\ disch_then (qx_choosel_then [`remaining_clock`,`used_stack`] strip_assume_tac)
    \\ `callee.clock <= s.clock` by (
      simp [Abbr `callee`,wordSemTheory.call_env_def])
    \\ qexistsl_tac [`remaining_clock`,`used_stack`]
    \\ conj_tac >- (
      irule LESS_EQ_TRANS
      \\ qexists_tac `callee.clock`
      \\ conj_tac \\ first_assum ACCEPT_TAC)
    \\ conj_tac >- first_assum ACCEPT_TAC
    \\ qpat_x_assum `c.be = s.be` kall_tac
    \\ once_rewrite_tac [ByteCopyLoop_code_def]
    \\ SIMP_TAC std_ss [LET_THM,Once wordSemTheory.evaluate_def]
    \\ simp [wordSemTheory.get_var_imm_def,wordSemTheory.word_cmp_def,
             integer_wordTheory.i2w_pos,WORD_LO]
    \\ once_rewrite_tac [list_Seq_def]
    \\ SIMP_TAC std_ss [Once wordSemTheory.evaluate_def]
    \\ simp [Once wordSemTheory.evaluate_def,wordSemTheory.get_var_imm_def,
             wordSemTheory.word_cmp_def]
    \\ irule evaluate_ByteCopyLoop_next
    \\ conj_tac >- (
      simp [Abbr `after_words`,wordSemTheory.set_var_def]
      \\ qpat_assum `n + 1 <= s.clock`
        (ACCEPT_TAC o MATCH_MP (DECIDE ``!n clock. n + 1 <= clock ==> clock <> 0``)))
    \\ qexistsl_tac [`a`,`b`,`Word 0w`,`c`,`Word 0w`,`loop_md`,`n`,`Word 0w`]
    \\ fs [Abbr `callee`,Abbr `after_words`,wordSemTheory.call_env_def,
            wordSemTheory.dec_clock_def,wordSemTheory.set_var_def,
            wordSemTheory.get_vars_def,wordSemTheory.get_var_def,lookup_insert])
  \\ LABEL_X_ASSUM "IH" mp_tac
  \\ qpat_assum `d <> 0` mp_tac
  \\ qpat_x_assum `d <> 0` (RULE_ASSUM_TAC o SIMP_RULE std_ss o single)
  \\ disch_tac
  \\ disch_then (ASSUME_NAMED_TAC "IH")
  \\ `0 < d /\ 3 * k < n + d` by simp []
  \\ `?old3. model (b + n2w (3 * k)) = Word old3 /\
                 b + n2w (3 * k) IN s.mdomain` by (
    qpat_assum `byte_copy_loop_inv _ _ _ _ _ _ _`
      (strip_assume_tac o REWRITE_RULE [byte_copy_loop_inv_def])
    \\ qpat_x_assum `!j. j * k < n + d ==> _` (qspec_then `3` mp_tac)
    \\ qpat_assum `3 * k < n + d` mp_tac
    \\ SIMP_TAC std_ss [isWord_exists]
    \\ metis_tac [])
  \\ qmatch_asmsub_rename_tac `model (b + n2w (3 * k)) = Word old_last`
  \\ `a <> b + n2w (3 * k) /\
       a + n2w k <> b + n2w (3 * k) /\
       a + n2w (2 * k) <> b + n2w (3 * k)` by (
    `k <= n /\ 2 * k <= n` by simp []
    \\ qpat_assum `byte_copy_loop_inv _ _ _ _ _ _ _`
      (strip_assume_tac o REWRITE_RULE [byte_copy_loop_inv_def])
    \\ qpat_assum `!i j. _` (qspecl_then [`0`,`3`] mp_tac)
    \\ qpat_assum `!i j. _` (qspecl_then [`1`,`3`] mp_tac)
    \\ qpat_x_assum `!i j. _` (qspecl_then [`2`,`3`] mp_tac)
    \\ simp [])
  \\ `ALL_DISTINCT [a;a + n2w k;a + n2w (2 * k);
                     b;b + n2w k;b + n2w (2 * k);b + n2w (3 * k)]` by (
    LABEL_ASSUM "k_def" mp_tac
    \\ gvs [good_dimindex_def,ALL_DISTINCT,n2w_11,dimword_def,
           addressTheory.WORD_EQ_ADD_CANCEL])
  \\ qabbrev_tac `push = \w:'a word. if c.be then w >>> (8 * d) else w << (8 * d)`
  \\ qabbrev_tac `pull = \w:'a word.
       if c.be then w << (8 * (k - d)) else w >>> (8 * (k - d))`
  \\ qabbrev_tac `model_after =
       (b + n2w (2 * k) =+ Word (pull second_word || push third_word))
         ((b + n2w k =+ Word (pull first_word || push second_word))
           ((b =+ Word (pull hi || push first_word)) model))`
  \\ qspecl_then [`k`,`d`,`a`,`b`,`model`,`s.mdomain`,`c.be`,
                   `first_word`,`second_word`,`third_word`,
                   `old_first`,`old_second`,`old_third`,`old_last`,`hi`] mp_tac
       word_copy_fwd_shift_three_words
  \\ impl_tac >- (
    LABEL_ASSUM "k_def" assume_tac
    \\ SIMP_TAC std_ss [EVERY_DEF]
    \\ rpt conj_tac \\ first_assum ACCEPT_TAC)
  \\ disch_tac
  \\ `word_copy_fwd c.be (n2w (3 * k)) a (b + n2w d)
         (byte_copy_flush c.be d (pull hi) b model) s.mdomain =
       SOME (byte_copy_flush c.be d (pull third_word)
         (b + n2w (3 * k)) model_after)` by (
    pop_assum mp_tac
    \\ qpat_assum `ALL_DISTINCT [a;_;_;b;_;_;_]`
         (mp_tac o SIMP_RULE std_ss [ALL_DISTINCT,MEM])
    \\ qpat_assum `model b = Word old_first` mp_tac
    \\ qpat_assum `model (b + n2w (3 * k)) = Word old_last` mp_tac
    \\ qpat_assum `d <> 0` mp_tac
    \\ SIMP_TAC (srw_ss())
         [LET_THM,Abbr `push`,Abbr `pull`,Abbr `model_after`,
          byte_copy_flush_def,APPLY_UPDATE_THM,theWord_def])
  \\ `3 * k + (n - 3 * k) = n` by (
    once_rewrite_tac [ADD_COMM]
    \\ irule SUB_ADD
    \\ first_assum ACCEPT_TAC)
  \\ qspecl_then [`3 * k`,`n - 3 * k`,`a`,`b + n2w d`,
                   `byte_copy_flush c.be d (pull hi) b model`,`s.mdomain`,`c.be`]
       mp_tac word_copy_fwd_add
  \\ impl_tac >- (
    qpat_assum `3 * k + (n - 3 * k) = n` (PURE_REWRITE_TAC o single)
    \\ rpt conj_tac \\ first_assum ACCEPT_TAC)
  \\ qpat_x_assum `word_copy_fwd s.be (n2w n) a (b + n2w d) _ _ = SOME final`
       (fn complete =>
    qpat_x_assum `word_copy_fwd c.be (n2w (3 * k)) _ _ _ _ = SOME _` (fn block =>
      qpat_assum `c.be = s.be` (fn endian =>
        qpat_assum `Abbrev (pull = _)` (fn pull_def =>
          qpat_x_assum `3 * k + (n - 3 * k) = n` (fn total =>
            SIMP_TAC std_ss [total,REWRITE_RULE [markerTheory.Abbrev_def] pull_def,
              SIMP_RULE std_ss [REWRITE_RULE [markerTheory.Abbrev_def] pull_def] block,
              SIMP_RULE std_ss [GSYM endian] complete])))))
  \\ disch_then (ASSUME_TAC o GSYM)
  \\ qspecl_then [`c`,`s`,`a`,`b`,`pull hi`,`(n2w (8 * d):'a word)`,
                   `(n2w (8 * (k - d)):'a word)`,`(n2w k:'a word)`,
                   `first_word`,`second_word`,`third_word`] mp_tac
       evaluate_ByteCopyShiftWords
  \\ impl_tac >- (
    qpat_assum `arch_bytes c.arch_width = k` SUBST1_TAC
    \\ qpat_assum `8 * d < dimword (:'a)` mp_tac
    \\ qpat_assum `8 * (k - d) < dimword (:'a)` mp_tac
    \\ SIMP_TAC std_ss [word_mul_n2w,Abbr `pull`,w2n_n2w,LESS_MOD]
    \\ ntac 2 (disch_then kall_tac)
    \\ rpt conj_tac \\ first_assum ACCEPT_TAC)
  \\ qpat_assum `8 * d < dimword (:'a)` mp_tac
  \\ qpat_assum `8 * (k - d) < dimword (:'a)` mp_tac
  \\ SIMP_TAC std_ss [LET_THM,w2n_n2w,LESS_MOD,word_mul_n2w]
  \\ ntac 2 (disch_then kall_tac)
  \\ disch_tac
  \\ qmatch_asmsub_abbrev_tac `evaluate (ByteCopyShiftWords_code c,s) = (NONE,after_words)`
  \\ `byte_copy_loop_inv k (n - 3 * k) d
         (a + n2w (3 * k)) (b + n2w (3 * k)) model_after s.mdomain` by (
    qpat_x_assum `!out1 out2 out3. byte_copy_loop_inv _ _ _ _ _ _ _`
         (qspecl_then [`pull hi || push first_word`,
                      `pull first_word || push second_word`,
                      `pull second_word || push third_word`] mp_tac)
    \\ simp [Abbr `model_after`])
  \\ `byte_copy_memory_rel k ((n - 3 * k) DIV (3 * k)) (b + n2w (3 * k))
         after_words.memory model_after` by (
    qpat_x_assum `!out1 out2 out3. byte_copy_memory_rel _ _ _ _ _`
         (qspecl_then [`pull hi || push first_word`,
                      `pull first_word || push second_word`,
                      `pull second_word || push third_word`] mp_tac)
    \\ simp [Abbr `after_words`,Abbr `model_after`,Abbr `pull`,Abbr `push`,
             wordSemTheory.set_var_def])
  \\ `n - 3 * k < dimword (:'a) /\ n - 3 * k + 1 <= s.clock - 1` by simp []
  \\ `b + n2w d + n2w (3 * k) = b + n2w (3 * k) + n2w d` by (
    CONV_TAC (AC_CONV (WORD_ADD_ASSOC,WORD_ADD_COMM)))
  \\ qpat_x_assum `word_copy_fwd c.be (n2w (n - 3 * k)) _ _ _ _ = SOME final` mp_tac
  \\ qpat_x_assum `b + n2w d + n2w (3 * k) = _` (ONCE_REWRITE_TAC o single)
  \\ disch_tac
  \\ qabbrev_tac `callee = wordSem$call_env
       [Loc l1 l2;Word (n2w (n - 3 * k));Word (a + n2w (3 * k));
        Word (b + n2w (3 * k));ret_val;Word (pull third_word);
        Word (n2w (8 * d));Word (n2w (8 * (k - d)))]
       (lookup ByteCopyLoop_location s.stack_size)
       (s with <|clock := s.clock - 1; memory := after_words.memory|>)`
  \\ LABEL_X_ASSUM "IH"
       (qspecl_then [`c`,`k`,`d`,`a + n2w (3 * k)`,`b + n2w (3 * k)`,
                      `third_word`,`ret_val`,`l1`,`l2`,`callee`,`model_after`,
                      `final`,`smx`] mp_tac)
  \\ impl_tac >- (
    LABEL_ASSUM "k_def" assume_tac
    \\ LABEL_ASSUM "width" assume_tac
    \\ gvs [Abbr `callee`,Abbr `pull`,wordSemTheory.call_env_def,
         wordSemTheory.get_var_def,lookup_fromList2,lookup_fromList,option_le_max])
  \\ disch_then (qx_choosel_then [`remaining_clock`,`used_stack`] strip_assume_tac)
  \\ `callee.clock <= s.clock` by (
    simp [Abbr `callee`,wordSemTheory.call_env_def])
  \\ qexistsl_tac [`remaining_clock`,`used_stack`]
  \\ conj_tac >- (
    irule LESS_EQ_TRANS
    \\ qexists_tac `callee.clock`
    \\ conj_tac \\ first_assum ACCEPT_TAC)
  \\ conj_tac >- first_assum ACCEPT_TAC
  \\ `(n2w (8 * d):'a word) <> 0w` by (
    qpat_assum `8 * d < dimword (:'a)` mp_tac
    \\ qpat_assum `d <> 0` mp_tac
    \\ SIMP_TAC (srw_ss()) [n2w_11,LESS_MOD])
  \\ qpat_x_assum `c.be = s.be` kall_tac
  \\ once_rewrite_tac [ByteCopyLoop_code_def]
  \\ SIMP_TAC std_ss [LET_THM,Once wordSemTheory.evaluate_def]
  \\ simp [wordSemTheory.get_var_imm_def,wordSemTheory.word_cmp_def,
           integer_wordTheory.i2w_pos,WORD_LO]
  \\ once_rewrite_tac [list_Seq_def]
  \\ SIMP_TAC std_ss [Once wordSemTheory.evaluate_def]
  \\ simp [Once wordSemTheory.evaluate_def,wordSemTheory.get_var_imm_def,
           wordSemTheory.word_cmp_def]
  \\ irule evaluate_ByteCopyLoop_next
  \\ conj_tac >- (
    simp [Abbr `after_words`,wordSemTheory.set_var_def]
    \\ qpat_assum `n + 1 <= s.clock`
      (ACCEPT_TAC o MATCH_MP (DECIDE ``!n clock. n + 1 <= clock ==> clock <> 0``)))
  \\ qexistsl_tac [`a`,`b`,`Word (n2w (8 * (k - d)))`,`c`,
                   `Word (pull third_word)`,`loop_md`,`n`,`Word (n2w (8 * d))`]
  \\ fs [Abbr `callee`,Abbr `after_words`,Abbr `pull`,Abbr `push`,
          wordSemTheory.call_env_def,
          wordSemTheory.dec_clock_def,wordSemTheory.set_var_def,
          wordSemTheory.get_vars_def,wordSemTheory.get_var_def,lookup_insert]
QED

Theorem CopyByteAlign_thm:
  !n (c:data_to_word$config) k prefix_bytes (a:'a word) b ret_val l1 l2 s model final smx.
    good_dimindex (:'a) /\ dimindex (:'a) = arch_width_bits c.arch_width /\
    k = dimindex (:'a) DIV 8 /\ c.be = s.be /\ n < dimword (:'a) /\
    byte_copy_align_inv k n prefix_bytes a b s.memory model s.mdomain /\
    (?md. lookup ByteCopyAlign_location s.code = SOME (5,ByteCopyAlign_code c,md)) /\
    (?md. lookup ByteCopyLoop_location s.code = SOME (8,ByteCopyLoop_code c,md)) /\
    (?md. lookup ByteCopyAdd_location s.code = SOME (5,ByteCopyAdd_code,md)) /\
    option_le s.stack_max smx /\
    option_le (OPTION_MAP2 $+ (stack_size s.stack)
      (lookup ByteCopyAlign_location s.stack_size)) smx /\
    option_le (OPTION_MAP2 $+ (stack_size s.stack)
      (lookup ByteCopyLoop_location s.stack_size)) smx /\
    option_le (OPTION_MAP2 $+ (stack_size s.stack)
      (lookup ByteCopyAdd_location s.stack_size)) smx /\
    n + 2 <= s.clock /\
    get_vars [0;2;4;6;8] s =
      SOME [Loc l1 l2;Word (n2w n);Word a;Word b;ret_val] /\
    word_copy_fwd s.be (n2w n) a b model s.mdomain = SOME final ==>
    ?remaining_clock used_stack.
      remaining_clock <= s.clock /\ option_le used_stack smx /\
      evaluate (ByteCopyAlign_code c,s) =
        (SOME (Result (Loc l1 l2) [ret_val]),
         s with <|clock := remaining_clock;memory := final;locals := LN;
                  locals_size := SOME 0;stack_max := used_stack|>)
Proof
  completeInduct_on `n`
  \\ map_every qx_gen_tac
       [`c`,`k`,`prefix_bytes`,`a`,`b`,`ret_val`,`l1`,`l2`,`s`,`model`,`final`,`smx`]
  \\ strip_tac
  \\ qmatch_asmsub_rename_tac
       `lookup ByteCopyAlign_location s.code = SOME (5,ByteCopyAlign_code c,align_md)`
  \\ qmatch_asmsub_rename_tac
       `lookup ByteCopyLoop_location s.code = SOME (8,ByteCopyLoop_code c,loop_md)`
  \\ qmatch_asmsub_rename_tac
       `lookup ByteCopyAdd_location s.code = SOME (5,ByteCopyAdd_code,add_md)`
  \\ qpat_x_assum `!smaller. smaller < n ==> _` (ASSUME_NAMED_TAC "IH")
  \\ qpat_assum `byte_copy_align_inv _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [byte_copy_align_inv_def])
  \\ `0 < k /\ arch_bytes c.arch_width = k /\ 3 * k < dimword (:'a) /\
      (i2w (&k - 1):'a word) = n2w (k - 1)` by
       gvs [good_dimindex_def,arch_size,dimword_def,integer_wordTheory.i2w_pos]
  \\ qpat_x_assum `dimindex (:'a) = _` (ASSUME_NAMED_TAC "width")
  \\ `get_var 0 s = SOME (Loc l1 l2) /\ get_var 2 s = SOME (Word (n2w n)) /\
       get_var 4 s = SOME (Word a) /\ get_var 6 s = SOME (Word b) /\
       get_var 8 s = SOME ret_val` by (
    qpat_x_assum `get_vars [0;2;4;6;8] s = _` mp_tac
    \\ simp [wordSemTheory.get_vars_def,AllCaseEqs()])
  \\ Cases_on `n < 3 * k`
  >- (
    qpat_x_assum `k = dimindex (:'a) DIV 8` kall_tac
    \\ qpat_x_assum `c.be = s.be` kall_tac
    \\ `(n - prefix_bytes) DIV (3 * k) = 0` by (
      irule LESS_DIV_EQ_ZERO
      \\ irule LESS_EQ_LESS_TRANS
      \\ qexists_tac `n`
      \\ simp [])
    \\ `s.memory = model` by fs [byte_copy_memory_rel_zero]
    \\ qpat_x_assum `s.memory = model` (SUBST_ALL_TAC o GSYM)
    \\ `n DIV 4 < s.clock` by (
      `n DIV 4 <= n` by simp [DIV_LESS_EQ]
      \\ decide_tac)
    \\ qspecl_then [`s`,`n2w n`,`a`,`b`,`ret_val`,`l1`,`l2`,`final`] mp_tac
         CopyByteAdd_call
    \\ impl_tac >- simp [w2n_n2w,LESS_MOD]
    \\ qpat_assum `n < dimword (:'a)` mp_tac
    \\ SIMP_TAC std_ss [w2n_n2w,LESS_MOD]
    \\ disch_then kall_tac
    \\ disch_tac
    \\ qexistsl_tac [`s.clock - (n DIV 4 + 1)`,
         `OPTION_MAP2 MAX s.stack_max
           (OPTION_MAP2 $+ (stack_size s.stack)
             (lookup ByteCopyAdd_location s.stack_size))`]
    \\ simp [option_le_max]
    \\ once_rewrite_tac [ByteCopyAlign_code_def]
    \\ SIMP_TAC std_ss [LET_THM,Once wordSemTheory.evaluate_def]
    \\ simp [wordSemTheory.get_var_imm_def,wordSemTheory.word_cmp_def,
             integer_wordTheory.i2w_pos,WORD_LO])
  \\ `3 * k <= n` by (
    qpat_assum `~(n < 3 * k)` (ACCEPT_TAC o REWRITE_RULE [NOT_LESS]))
  \\ Cases_on `prefix_bytes = 0`
  >- (
    qpat_x_assum `prefix_bytes = 0` SUBST_ALL_TAC
    \\ `0 < n` by simp []
    \\ `byte_aligned a` by fs []
    \\ `byte_aligned (byte_align b)` by (
      simp [byte_aligned_def,byte_align_def,aligned_align])
    \\ `s.memory (byte_align b) = model (byte_align b)` by (
      qpat_assum `!i. i <= 0 ==> _`
        (ACCEPT_TAC o SIMP_RULE std_ss [WORD_ADD_0,ZERO_LESS_EQ] o Q.SPEC `0`))
    \\ `byte_copy_memory_rel k (n DIV (3 * k)) (byte_align b) s.memory model` by (
      qpat_assum `byte_copy_memory_rel _ _ _ _ _`
           (ACCEPT_TAC o SIMP_RULE std_ss [SUB_0,WORD_ADD_0]))
    \\ `?old. model (byte_align b) = Word old /\ byte_align b IN s.mdomain` by (
      qpat_assum `byte_copy_range_inv _ _ _ _ _`
           (strip_assume_tac o REWRITE_RULE [byte_copy_range_inv_def])
      \\ qpat_assum `!i. i < n ==> _ /\ _ /\ _ /\ _` (qspec_then `0` mp_tac)
      \\ impl_tac >- qpat_assum `0 < n` ACCEPT_TAC
      \\ disch_then (strip_assume_tac o SIMP_RULE std_ss [WORD_ADD_0])
      \\ fs [isWord_exists])
    \\ qmatch_asmsub_rename_tac `model (byte_align b) = Word old_word`
    \\ qabbrev_tac `d = w2n b MOD k`
    \\ qspecl_then [`k`,`d`,`b`] mp_tac byte_copy_align_address
    \\ impl_tac >- simp [Abbr `d`]
    \\ strip_tac
    \\ qpat_x_assum `d = 0 <=> byte_aligned b` kall_tac
    \\ qspecl_then [`k`,`n`,`d`,`a`,`byte_align b`,`model`,`s.mdomain`] mp_tac
         byte_copy_range_inv_loop
    \\ impl_tac >- (
      qpat_assum `b = byte_align b + n2w d` (PURE_ONCE_REWRITE_TAC o single o GSYM)
      \\ rpt conj_tac \\ first_assum ACCEPT_TAC)
    \\ disch_tac
    \\ qspecl_then [`k`,`d`,`model`,`byte_align b`,`old_word`,`c.be`] mp_tac
         byte_copy_initial_carry
    \\ impl_tac >- (rpt conj_tac \\ first_assum ACCEPT_TAC)
    \\ SIMP_TAC std_ss [LET_THM]
    \\ strip_tac
    \\ qabbrev_tac `hi = if c.be then old_word >>> (8 * (k - d))
                           else old_word << (8 * (k - d))`
    \\ qabbrev_tac `carry = if d = 0 then 0w else old_word &&
         (if c.be then -1w << (8 * (k - d)) else -1w >>> (8 * (k - d)))`
    \\ `(if d = 0 then 0w else
           if c.be then hi << (8 * (k - d)) else hi >>> (8 * (k - d))) = carry`
    by (
      qpat_assum `(if d = 0 then 0w else if c.be then _ else _) = carry` mp_tac
      \\ SIMP_TAC std_ss [Abbr `hi`])
    \\ `n + 1 <= s.clock - 1 /\ s.clock <> 0` by simp []
    \\ qabbrev_tac `callee = call_env
         [Loc l1 l2;Word (n2w n);Word a;Word (byte_align b);ret_val;
          Word carry;Word (n2w (8 * d));Word (n2w (if d = 0 then 0 else 8 * (k - d)))]
         (lookup ByteCopyLoop_location s.stack_size) (dec_clock s)`
    \\ qspecl_then [`n`,`c`,`k`,`d`,`a`,`byte_align b`,`hi`,`ret_val`,`l1`,`l2`,
                     `callee`,`model`,`final`,`smx`] mp_tac CopyByteLoop_thm
    \\ impl_tac >- (
      qpat_assum `b = byte_align b + n2w d` (PURE_ONCE_REWRITE_TAC o single o GSYM)
      \\ LABEL_ASSUM "width" assume_tac
      \\ gvs [Abbr `callee`,wordSemTheory.call_env_def,wordSemTheory.dec_clock_def,
             wordSemTheory.get_var_def,lookup_fromList2,lookup_fromList,option_le_max])
    \\ disch_then (qx_choosel_then [`remaining_clock`,`used_stack`] strip_assume_tac)
    \\ `callee.clock <= s.clock` by (
      simp [Abbr `callee`,wordSemTheory.call_env_def,wordSemTheory.dec_clock_def])
    \\ `callee with <|clock := remaining_clock;memory := final;locals := LN;
                      locals_size := SOME 0;stack_max := used_stack|> =
         s with <|clock := remaining_clock;memory := final;locals := LN;
                  locals_size := SOME 0;stack_max := used_stack|>` by (
      simp [Abbr `callee`,wordSemTheory.call_env_def,wordSemTheory.dec_clock_def,
            wordSemTheory.state_component_equality])
    \\ qspecl_then [`c`,`k`,`d`,`b`,`s`,`l1`,`l2`,`(n2w n:'a word)`,`a`,`ret_val`,
                     `old_word`,`loop_md`,
                     `s with <|clock := remaining_clock;memory := final;locals := LN;
                               locals_size := SOME 0;stack_max := used_stack|>`] mp_tac
         evaluate_ByteCopyAlign_start
    \\ impl_tac >- (
      LABEL_ASSUM "width" assume_tac
      \\ gvs [Abbr `d`])
    \\ SIMP_TAC std_ss [LET_THM]
    \\ impl_tac >- (
      gvs [Abbr `callee`,Abbr `carry`,wordSemTheory.call_env_def,wordSemTheory.dec_clock_def])
    \\ disch_tac
    \\ `a && n2w (k - 1) = 0w` by (
      qspecl_then [`k`,`a`] mp_tac byte_copy_aligned_test
      \\ impl_tac >- (conj_tac \\ first_assum ACCEPT_TAC)
      \\ simp [])
    \\ qexistsl_tac [`remaining_clock`,`used_stack`]
    \\ conj_tac >- (
      irule LESS_EQ_TRANS \\ qexists_tac `callee.clock`
      \\ conj_tac \\ first_assum ACCEPT_TAC)
    \\ conj_tac >- first_assum ACCEPT_TAC
    \\ qpat_x_assum `k = dimindex (:'a) DIV 8` kall_tac
    \\ qpat_x_assum `c.be = s.be` kall_tac
    \\ qpat_x_assum `(i2w (&k - 1):'a word) = n2w (k - 1)`
         (ASSUME_TAC o SIMP_RULE (srw_ss()) [])
    \\ once_rewrite_tac [ByteCopyAlign_code_def]
    \\ SIMP_TAC std_ss [LET_THM,Once wordSemTheory.evaluate_def]
    \\ simp [wordSemTheory.get_var_imm_def,wordSemTheory.word_cmp_def,
             integer_wordTheory.i2w_pos,WORD_LO]
    \\ SIMP_TAC std_ss [Once wordSemTheory.evaluate_def]
    \\ simp [wordSemTheory.get_var_imm_def,wordSemTheory.word_cmp_def]
    \\ qpat_x_assum `evaluate (list_Seq _,s) = _` mp_tac
    \\ simp [])
  \\ `0 < n /\ 0 < prefix_bytes /\ prefix_bytes <= n /\ n - 1 < n /\
   n - 1 < dimword (:'a) /\ n - 1 + 2 <= s.clock - 1 /\ s.clock <> 0` by simp []
  \\ qspecl_then [`k`,`n`,`prefix_bytes`,`a`,`b`,`s.memory`,`model`,
                   `s.mdomain`,`s.be`,`final`] mp_tac
       byte_copy_align_step
  \\ impl_tac >- (rpt conj_tac \\ first_assum ACCEPT_TAC)
  \\ disch_then (qx_choosel_then [`value`,`actual_after`,`model_after`] strip_assume_tac)
  \\ qabbrev_tac `callee = call_env
       [Loc l1 l2;Word (n2w (n - 1));Word (a + 1w);Word (b + 1w);ret_val]
       (lookup ByteCopyAlign_location s.stack_size)
       (s with <|clock := s.clock - 1;memory := actual_after|>)`
  \\ LABEL_X_ASSUM "IH" (qspec_then `n - 1` mp_tac)
  \\ impl_tac >- first_assum ACCEPT_TAC
  \\ disch_then (qspecl_then [`c`,`k`,`prefix_bytes - 1`,`a + 1w`,`b + 1w`,
                              `ret_val`,`l1`,`l2`,`callee`,`model_after`,`final`,`smx`] mp_tac)
  \\ impl_tac >- (
    LABEL_ASSUM "width" assume_tac
    \\ gvs [Abbr `callee`,wordSemTheory.call_env_def,wordSemTheory.get_vars_def,
         wordSemTheory.get_var_def,lookup_fromList2,lookup_fromList,option_le_max])
  \\ disch_then (qx_choosel_then [`remaining_clock`,`used_stack`] strip_assume_tac)
  \\ `callee.clock <= s.clock` by simp [Abbr `callee`,wordSemTheory.call_env_def]
  \\ `callee with <|clock := remaining_clock;memory := final;locals := LN;
                    locals_size := SOME 0;stack_max := used_stack|> =
       s with <|clock := remaining_clock;memory := final;locals := LN;
                locals_size := SOME 0;stack_max := used_stack|>` by (
    simp [Abbr `callee`,wordSemTheory.call_env_def,wordSemTheory.state_component_equality])
  \\ qspecl_then [`s`,`n`,`a`,`b`,`ret_val`,`l1`,`l2`,`value`,`actual_after`,
                   `c`,`align_md`,
                   `s with <|clock := remaining_clock;memory := final;locals := LN;
                             locals_size := SOME 0;stack_max := used_stack|>`] mp_tac
       evaluate_ByteCopyAlign_byte
  \\ impl_tac >- (
    gvs [Abbr `callee`,wordSemTheory.call_env_def])
  \\ disch_tac
  \\ `~byte_aligned a` by (
    qpat_assum `!i. i < prefix_bytes ==> ~byte_aligned (a + n2w i)` (qspec_then `0` mp_tac)
    \\ impl_tac >- qpat_assum `0 < prefix_bytes` ACCEPT_TAC
    \\ disch_then (ACCEPT_TAC o SIMP_RULE std_ss [WORD_ADD_0]))
  \\ `~(a && n2w (k - 1) = 0w)` by (
    qspecl_then [`k`,`a`] mp_tac byte_copy_aligned_test
    \\ impl_tac >- (conj_tac \\ first_assum ACCEPT_TAC)
    \\ simp [])
  \\ qexistsl_tac [`remaining_clock`,`used_stack`]
  \\ conj_tac >- (
    irule LESS_EQ_TRANS \\ qexists_tac `callee.clock`
    \\ conj_tac \\ first_assum ACCEPT_TAC)
  \\ conj_tac >- first_assum ACCEPT_TAC
  \\ qpat_x_assum `k = dimindex (:'a) DIV 8` kall_tac
  \\ qpat_x_assum `c.be = s.be` kall_tac
  \\ qpat_x_assum `(i2w (&k - 1):'a word) = n2w (k - 1)`
       (ASSUME_TAC o SIMP_RULE (srw_ss()) [])
  \\ once_rewrite_tac [ByteCopyAlign_code_def]
  \\ SIMP_TAC std_ss [LET_THM,Once wordSemTheory.evaluate_def]
  \\ simp [wordSemTheory.get_var_imm_def,wordSemTheory.word_cmp_def,
           integer_wordTheory.i2w_pos,WORD_LO]
  \\ SIMP_TAC std_ss [Once wordSemTheory.evaluate_def]
  \\ simp [wordSemTheory.get_var_imm_def,wordSemTheory.word_cmp_def]
QED

Theorem byte_copy_ranges_disjoint[local]:
  ∀n b a.
    n < dimword (:'a) /\ n <= w2n ((b:'a word) - a) /\
    n <= w2n (a - b) ==>
    !i j. i < n /\ j < n ==> a + n2w i <> b + n2w j
Proof
  rpt gen_tac
  \\ rpt strip_tac
  \\ `b - a = n2w i - n2w j /\ a - b = n2w j - n2w i` by (
    qpat_assum `a + n2w i = b + n2w j` mp_tac
    \\ PURE_REWRITE_TAC [WORD_EQ_SUB_LADD,GSYM WORD_ADD_SUB_SYM,WORD_EQ_SUB_RADD]
    \\ simp [WORD_ADD_COMM])
  \\ Cases_on `j <= i`
  >- (
    `i - j < dimword (:'a)` by decide_tac
    \\ `w2n (b - a) = i - j` by simp [GSYM n2w_sub,w2n_n2w,LESS_MOD]
    \\ decide_tac)
  \\ `i <= j /\ j - i < dimword (:'a)` by decide_tac
  \\ `w2n (a - b) = j - i` by simp [GSYM n2w_sub,w2n_n2w,LESS_MOD]
  \\ decide_tac
QED

Theorem byte_copy_align_prefix[local]:
  ∀k a.
    good_dimindex (:'a) /\ k = dimindex (:'a) DIV 8 ==>
    ?prefix_bytes. prefix_bytes < k /\
      byte_aligned ((a:'a word) + n2w prefix_bytes) /\
      !i. i < prefix_bytes ==> ~byte_aligned (a + n2w i)
Proof
  rpt gen_tac
  \\ strip_tac
  \\ `?r. r < k /\ byte_aligned (a + n2w r)` by (
    `0 < k` by fs [good_dimindex_def]
    \\ `w2n a MOD k < k` by simp []
    \\ Cases_on `w2n a MOD k = 0`
    >- (
      qexists_tac `0`
      \\ gvs [good_dimindex_def,byte_aligned_def,aligned_w2n])
    \\ `w2n a + (k - w2n a MOD k) = (w2n a DIV k + 1) * k` by (
      drule_then (qspec_then `w2n a` strip_assume_tac) DIVISION
      \\ PURE_REWRITE_TAC [RIGHT_ADD_DISTRIB,MULT_CLAUSES]
      \\ decide_tac)
    \\ `a + n2w (k - w2n a MOD k) = n2w ((w2n a DIV k + 1) * k)` by (
      qpat_assum `w2n a + _ = _` (PURE_REWRITE_TAC o single o GSYM)
      \\ PURE_REWRITE_TAC [GSYM word_add_n2w,n2w_w2n]
      \\ REFL_TAC)
    \\ qexists_tac `k - w2n a MOD k`
    \\ conj_tac >- decide_tac
    \\ asm_rewrite_tac []
    \\ gvs [good_dimindex_def,byte_aligned_def]
    \\ irule MOD_0_aligned
    \\ simp [])
  \\ qmatch_asmsub_rename_tac `byte_aligned (a + n2w some_prefix)`
  \\ qspec_then `\i. i < k /\ byte_aligned (a + n2w i)` mp_tac WOP
  \\ SIMP_TAC std_ss []
  \\ impl_tac >- (qexists_tac `some_prefix` \\ simp [])
  \\ disch_then (qx_choose_then `prefix_bytes` strip_assume_tac)
  \\ qexists_tac `prefix_bytes`
  \\ simp []
  \\ metis_tac [LESS_TRANS]
QED

Theorem byte_copy_align_initial[local]:
  ∀k n a b m dm.
    good_dimindex (:'a) /\ k = dimindex (:'a) DIV 8 /\
    byte_copy_range_inv n (a:'a word) b m dm ==>
    ?prefix_bytes. byte_copy_align_inv k n prefix_bytes a b m m dm
Proof
  rpt gen_tac
  \\ strip_tac
  \\ qspecl_then [`k`,`a`] mp_tac byte_copy_align_prefix
  \\ impl_tac >- (conj_tac \\ first_assum ACCEPT_TAC)
  \\ disch_then (qx_choose_then `prefix_bytes` strip_assume_tac)
  \\ qexists_tac `prefix_bytes`
  \\ simp [byte_copy_align_inv_def,byte_copy_memory_rel_refl]
QED

Theorem byte_copy_range_inv_from_loads[local]:
  ∀n b a m dm be.
    n < dimword (:'a) /\ n <= w2n ((b:'a word) - a) /\ n <= w2n (a - b) /\
    (!i. i < n ==>
      IS_SOME (mem_load_byte_aux m dm be (a + n2w i)) /\
      IS_SOME (mem_load_byte_aux m dm be (b + n2w i))) ==>
    byte_copy_range_inv n a b m dm
Proof
  rpt gen_tac
  \\ strip_tac
  \\ PURE_REWRITE_TAC [byte_copy_range_inv_def]
  \\ conj_tac
  >- (
    qx_gen_tac `i` \\ disch_tac
    \\ qpat_x_assum `!j. j < n ==> _` (qspec_then `i` mp_tac)
    \\ simp []
    \\ namedCases_on `m (byte_align (a + n2w i))` ["source_word","source_l1 source_l2"]
    \\ namedCases_on `m (byte_align (b + n2w i))` ["target_word","target_l1 target_l2"]
    \\ gvs [wordSemTheory.mem_load_byte_aux_def,isWord_def,AllCaseEqs()]
    \\ Cases_on `byte_align (a + n2w i) IN dm`
    \\ Cases_on `byte_align (b + n2w i) IN dm`
    \\ simp [])
  \\ qspecl_then [`n`,`b`,`a`] mp_tac byte_copy_ranges_disjoint
  \\ impl_tac >- (rpt conj_tac \\ first_assum ACCEPT_TAC)
  \\ simp []
QED

Theorem byte_copy_update_suffix[local]:
  !offset ys value tail.
    offset < LENGTH ys ==>
    TAKE (offset + 1) (LUPDATE value offset ys) ++ tail ++
      DROP (offset + 1 + LENGTH tail) (LUPDATE value offset ys) =
    TAKE offset ys ++ value::tail ++ DROP (offset + SUC (LENGTH tail)) ys
Proof
  Induct \\ Cases_on `ys` \\ fs [LUPDATE_def,ADD1]
QED

Theorem byte_copy_seq_memory_rel[local]:
  ∀be ts sp st dm flag p w vars array_flag target_base.
    !bytes refs offset ys (m:'a word -> 'a word_loc) a.
      good_dimindex (:'a) /\
      memory_rel c be ts refs sp st m dm ((RefPtr flag p,Word (w:'a word))::vars) /\
      lookup p refs = SOME (ByteArray array_flag ys) /\
      get_real_addr c st w = SOME target_base /\ offset + LENGTH bytes <= LENGTH ys /\
      byte_copy_range_inv (LENGTH bytes) a (target_base + bytes_in_word + n2w offset) m dm /\
      (!i. i < LENGTH bytes ==>
        mem_load_byte_aux m dm be (a + n2w i) = SOME (EL i bytes)) ==>
      ?final.
        byte_copy_seq be (LENGTH bytes) a (target_base + bytes_in_word + n2w offset) m dm =
          SOME final /\
        memory_rel c be ts
          (insert p (ByteArray array_flag
            (TAKE offset ys ++ bytes ++ DROP (offset + LENGTH bytes) ys)) refs)
          sp st final dm ((RefPtr flag p,Word w)::vars)
Proof
  ntac 11 gen_tac
  \\ Induct_on `bytes`
  >- (
    rpt strip_tac
    \\ qexists_tac `m`
    \\ simp [byte_copy_seq_def,TAKE_DROP,insert_unchanged])
  \\ qx_gen_tac `value`
  \\ map_every qx_gen_tac [`refs`,`offset`,`ys`,`m`,`a`]
  \\ strip_tac
  \\ `offset < LENGTH ys /\ offset + 1 + LENGTH bytes <= LENGTH ys` by (
    qpat_assum `offset + LENGTH (value::bytes) <= LENGTH ys` mp_tac
    \\ PURE_REWRITE_TAC [LENGTH]
    \\ decide_tac)
  \\ qpat_assum `!i. i < LENGTH (value::bytes) ==> _`
       (ASSUME_TAC o SIMP_RULE (srw_ss()) [] o Q.SPEC `0`)
  \\ rpt_drule0 memory_rel_ByteArray_IMP_store
  \\ disch_then (qspecl_then [`offset`,`value`] mp_tac)
  \\ impl_tac >- decide_tac
  \\ disch_then (qx_choose_then `updated` strip_assume_tac)
  \\ qspecl_then [`SUC (LENGTH bytes)`,`a`,
       `target_base + bytes_in_word + n2w offset`,`m`,`dm`,`0`,`be`,`value`] mp_tac
       byte_copy_range_inv_store
  \\ impl_tac >- simp []
  \\ SIMP_TAC std_ss [WORD_ADD_0]
  \\ disch_then (qx_choose_then `stored` strip_assume_tac)
  \\ gvs []
  \\ qspecl_then [`SUC (LENGTH bytes)`,`a`,
       `target_base + bytes_in_word + n2w offset`,`stored`,`dm`,`1`] mp_tac
       byte_copy_range_inv_suffix
  \\ simp []
  \\ disch_tac
  \\ qpat_x_assum `!refs offset ys m a. _`
       (qspecl_then [`insert p (ByteArray array_flag (LUPDATE value offset ys)) refs`,
                     `offset + 1`,`LUPDATE value offset ys`,`stored`,`a + 1w`] mp_tac)
  \\ impl_tac >- (
    simp [lookup_insert,LENGTH_LUPDATE,GSYM word_add_n2w,WORD_ADD_ASSOC]
    \\ qx_gen_tac `i` \\ strip_tac
    \\ qpat_assum `!j. j < SUC (LENGTH bytes) ==> mem_load_byte_aux stored _ _ _ = _`
         (qspec_then `SUC i` mp_tac)
    \\ simp [ADD1,addressTheory.word_arith_lemma1]
    \\ simp [GSYM ADD1])
  \\ disch_then (qx_choose_then `final` strip_assume_tac)
  \\ `offset < LENGTH ys` by decide_tac
  \\ qspecl_then [`offset`,`ys`,`value`,`bytes`] mp_tac byte_copy_update_suffix
  \\ impl_tac >- first_assum ACCEPT_TAC
  \\ disch_tac
  \\ qexists_tac `final`
  \\ conj_tac >- (
    qpat_x_assum `byte_copy_seq be (LENGTH bytes) _ _ _ _ = SOME final` mp_tac
    \\ simp [byte_copy_seq_def,GSYM word_add_n2w,WORD_ADD_ASSOC])
  \\ qpat_assum `memory_rel _ _ _ (insert p _ (insert p _ refs)) _ _ final _ _` mp_tac
  \\ qpat_assum `TAKE (offset + 1) _ ++ bytes ++ _ = _` (REWRITE_TAC o single)
  \\ REWRITE_TAC [insert_shadow]
QED

Theorem CopyByteAlign_call:
  !n args (c:data_to_word$config) k prefix_bytes (a:'a word) b ret_val l1 l2 s model final smx.
    good_dimindex (:'a) /\ dimindex (:'a) = arch_width_bits c.arch_width /\
    k = dimindex (:'a) DIV 8 /\ c.be = s.be /\ n < dimword (:'a) /\
    byte_copy_align_inv k n prefix_bytes a b s.memory model s.mdomain /\
    (?md. lookup ByteCopyAlign_location s.code = SOME (5,ByteCopyAlign_code c,md)) /\
    (?md. lookup ByteCopyLoop_location s.code = SOME (8,ByteCopyLoop_code c,md)) /\
    (?md. lookup ByteCopyAdd_location s.code = SOME (5,ByteCopyAdd_code,md)) /\
    option_le s.stack_max smx /\
    option_le (OPTION_MAP2 $+ (stack_size s.stack)
      (lookup ByteCopyAlign_location s.stack_size)) smx /\
    option_le (OPTION_MAP2 $+ (stack_size s.stack)
      (lookup ByteCopyLoop_location s.stack_size)) smx /\
    option_le (OPTION_MAP2 $+ (stack_size s.stack)
      (lookup ByteCopyAdd_location s.stack_size)) smx /\
    n + 3 <= s.clock /\
    get_vars args s =
      SOME [Loc l1 l2;Word (n2w n);Word a;Word b;ret_val] /\
    word_copy_fwd s.be (n2w n) a b model s.mdomain = SOME final ==>
    ?remaining_clock used_stack.
      remaining_clock <= s.clock /\ option_le used_stack smx /\
      evaluate (Call NONE (SOME ByteCopyAlign_location) args NONE,s) =
        (SOME (Result (Loc l1 l2) [ret_val]),
         s with <|clock := remaining_clock;memory := final;locals := LN;
                  locals_size := SOME 0;stack_max := used_stack|>)
Proof
  map_every qx_gen_tac
    [`n`,`args`,`c`,`k`,`prefix_bytes`,`a`,`b`,`ret_val`,`l1`,`l2`,`s`,`model`,`final`,`smx`]
  \\ strip_tac
  \\ qmatch_asmsub_rename_tac
       `lookup ByteCopyAlign_location s.code = SOME (5,ByteCopyAlign_code c,align_md)`
  \\ qmatch_asmsub_rename_tac
       `lookup ByteCopyLoop_location s.code = SOME (8,ByteCopyLoop_code c,loop_md)`
  \\ qmatch_asmsub_rename_tac
       `lookup ByteCopyAdd_location s.code = SOME (5,ByteCopyAdd_code,add_md)`
  \\ `LENGTH args = 5` by (
    imp_res_tac get_vars_IMP_LENGTH_word \\ fs [])
  \\ `s.clock <> 0 /\ n + 2 <= s.clock - 1` by decide_tac
  \\ simp [Once wordSemTheory.evaluate_def,wordSemTheory.bad_dest_args_def,
           wordSemTheory.find_code_def,wordSemTheory.add_ret_loc_def]
  \\ qmatch_goalsub_abbrev_tac `evaluate (ByteCopyAlign_code c,callee)`
  \\ qspecl_then [`n`,`c`,`k`,`prefix_bytes`,`a`,`b`,`ret_val`,`l1`,`l2`,
                   `callee`,`model`,`final`,`smx`] mp_tac CopyByteAlign_thm
  \\ impl_tac >- (
    gvs [Abbr `callee`,wordSemTheory.call_env_def,wordSemTheory.dec_clock_def,
         wordSemTheory.get_vars_def,wordSemTheory.get_var_def,
         lookup_fromList2,lookup_fromList,option_le_max])
  \\ disch_then (qx_choosel_then [`remaining_clock`,`used_stack`] strip_assume_tac)
  \\ `callee.clock <= s.clock` by (
    simp [Abbr `callee`,wordSemTheory.call_env_def,wordSemTheory.dec_clock_def])
  \\ qexistsl_tac [`remaining_clock`,`used_stack`]
  \\ conj_tac >- (
    irule LESS_EQ_TRANS \\ qexists_tac `callee.clock`
    \\ conj_tac \\ first_assum ACCEPT_TAC)
  \\ asm_simp_tac std_ss [wordSemTheory.bad_fun_return_def]
  \\ simp [Abbr `callee`,wordSemTheory.call_env_def,wordSemTheory.dec_clock_def,
           wordSemTheory.state_component_equality]
QED

Theorem push_env_store:
   (push_env x y s).store = s.store /\
    (push_env x y s).memory = s.memory /\
    (push_env x y s).mdomain = s.mdomain /\
    (push_env x y s).code = s.code /\
    (push_env x y s).be = s.be
Proof
  Cases_on `y`
  \\ fs [wordSemTheory.push_env_def]
  \\ TRY pairarg_tac \\ fs []
  \\ PairCases_on `x'` \\ fs [wordSemTheory.push_env_def]
  \\ TRY pairarg_tac \\ fs []
QED

Theorem not_less_zero_int_eq[local]:
    ~(i < 0:int) <=> ?n. i = &n
Proof
  Cases_on `i` \\ fs []
QED

val _ = augment_srw_ss [rewrites [arch_width_eq32, arch_bytes_scaled_word]];

Theorem IN_adjust_var_lemma:
  cut_env kept_names s_locals = SOME x ∧
  cut_envs (adjust_sets kept_names) t_locals = SOME (y1,y2) ∧
  n ∈ domain x ⇒
  adjust_var n ∈ domain y2
Proof
  rw []
  \\ gvs [wordSemTheory.cut_envs_def,AllCaseEqs(),adjust_sets_def,
          wordSemTheory.cut_names_def,lookup_inter_alt,
          dataSemTheory.cut_env_def]
  \\ gvs [domain_union,domain_inter,adjust_var_IN_adjust_set]
  \\ gvs [SUBSET_DEF]
  \\ first_x_assum irule
  \\ simp [adjust_var_IN_adjust_set]
QED

Theorem Smallnum_lsr_1[local]:
  good_dimindex (:'a) ∧ small_int (dimindex (:'a)) (&n) ⇒
  (Smallnum (&n):'a word) ⋙ 1 = n2w n
Proof
  strip_tac
  \\ gvs [Smallnum_def]
  \\ rewrite_tac [GSYM w2n_11,w2n_lsr]
  \\ gvs [small_int_def,good_dimindex_def,dimword_def]
  \\ once_rewrite_tac [MULT_COMM]
  \\ simp [MULT_DIV]
QED

Theorem assign_ScanByte:
  (∃neq. op = MemOp (ScanByte neq)) ⇒ ^assign_thm_goal
Proof
  rpt strip_tac \\ imp_res_tac state_rel_arch_width
  \\ drule0 (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ ‘t.termdep ≠ 0’ by fs []
  \\ ‘names_opt ≠ NONE’ by gvs [dataLangTheory.op_requires_names_def]
  \\ gvs [GSYM IS_SOME_EQ_NOT_NONE,IS_SOME_EXISTS]
  \\ rename [‘cut_state_opt (SOME kept_names) s’]
  \\ drule_all state_rel_cut_state_opt_SOME \\ strip_tac
  \\ qpat_x_assum ‘_ (t with locals := _) NONE locs’
       (ASSUME_NAMED_TAC "with_locals")
  \\ qpat_x_assum ‘_ s t NONE locs’ (ASSUME_NAMED_TAC "old")
  \\ fs [do_app,dataSemTheory.allowed_op_def] \\ clean_tac
  \\ imp_res_tac get_vars_IMP_LENGTH
  \\ gvs [AllCaseEqs(),LENGTH_EQ_NUM_compute]
  \\ qmatch_asmsub_rename_tac
       ‘get_vars [start_arg;end_arg;byte_arg;array_arg] s.locals =
        SOME [Number start_index;Number end_index;Number byte;RefPtr block pointer]’
  \\ qmatch_asmsub_rename_tac ‘lookup pointer x.refs = SOME (ByteArray immutable bytes)’
  \\ ‘x.refs = s.refs’ by (
    qpat_x_assum ‘cut_state_opt _ _ = SOME x’ mp_tac
    \\ simp [dataSemTheory.cut_state_opt_def,dataSemTheory.cut_state_def,AllCaseEqs()]
    \\ rw [] \\ simp [])
  \\ fs []
  \\ LABEL_ASSUM "old" (assume_tac o REWRITE_RULE [state_rel_thm])
  \\ full_simp_tac std_ss [APPEND,GSYM APPEND_ASSOC]
  \\ rpt_drule0 memory_rel_get_vars_IMP \\ strip_tac
  \\ ‘good_dimindex (:'a) ∧ shift_length c < dimindex (:'a)’ by fs [state_rel_thm]
  \\ ntac 3 (drule memory_rel_tl \\ strip_tac)
  \\ drule_all memory_rel_ByteArray_IMP \\ strip_tac
  \\ qmatch_asmsub_rename_tac ‘get_real_addr c t.store array_word = SOME base’
  \\ ‘small_int (dimindex (:'a)) start_index ∧
      small_int (dimindex (:'a)) end_index ∧
      small_int (dimindex (:'a)) byte’ by (
    gvs [good_dimindex_def,small_int_def,dimword_def] \\ intLib.COOPER_TAC)
  \\ qpat_x_assum ‘memory_rel _ _ _ _ _ _ _ _ ((Number start_index,_)::_)’
       (mp_then (Pos last) mp_tac memory_rel_Number_IMP)
  \\ asm_rewrite_tac [] \\ disch_tac
  \\ qpat_x_assum ‘memory_rel _ _ _ _ _ _ _ _ ((Number end_index,_)::_)’
       (mp_then (Pos last) mp_tac memory_rel_Number_IMP)
  \\ asm_rewrite_tac [] \\ disch_tac
  \\ qpat_x_assum ‘memory_rel _ _ _ _ _ _ _ _ ((Number byte,_)::_)’
       (mp_then (Pos last) mp_tac memory_rel_Number_IMP)
  \\ asm_rewrite_tac [] \\ disch_tac
  \\ gvs []
  \\ ‘∃start stop raw_byte.
        start_index = &start ∧ end_index = &stop ∧ byte = &raw_byte’ by
       intLib.COOPER_TAC
  \\ gvs []
  \\ ‘((Smallnum (&start):'a word) <+ Smallnum (&stop)) ⇔ start < stop’ by
       gvs [Smallnum_def,INT_EQ_NUM_LEMMA,dimword_def,good_dimindex_def,WORD_LO]
  \\ gvs [wordSemTheory.get_vars_def,wordSemTheory.get_var_def,CaseEq "option"]
  \\ ‘x.stack = s.stack ∧ x.locals_size = s.locals_size ∧
      x.stack_frame_sizes = s.stack_frame_sizes’ by (
    qpat_x_assum ‘cut_state_opt _ _ = SOME x’ mp_tac
    \\ simp [dataSemTheory.cut_state_opt_def,dataSemTheory.cut_state_def,AllCaseEqs()]
    \\ rw [] \\ simp [])
  \\ Cases_on ‘stop ≤ start’
  >- (
    simp [assign_def,arg4_def,assign_ScanByte_def,eq_eval]
    \\ fs [state_rel_thm,dataSemTheory.set_var_def,lookup_insert]
    \\ conj_tac
    >- (
      qx_gen_tac ‘local_index’ \\ Cases_on ‘local_index = dest’
      \\ simp [adjust_var_11])
    \\ conj_tac >- simp [option_le_max_right]
    \\ rewrite_tac [GSYM APPEND_ASSOC,APPEND]
    \\ irule memory_rel_insert \\ rewrite_tac [APPEND]
    \\ irule IMP_memory_rel_Number
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
  )
  \\ fs []
  \\ ‘small_int (dimindex (:'a)) (&(stop - start))’ by (
    gvs [small_int_def,good_dimindex_def,dimword_def] \\ intLib.COOPER_TAC)
  \\ ‘&stop - &start:int = &(stop - start)’ by intLib.COOPER_TAC
  \\ ‘(Smallnum (&stop) - Smallnum (&start):'a word) =
      Smallnum (&(stop - start))’ by simp [small_int_Smallnum_sub]
  \\ ‘LENGTH bytes < dimword (:'a)’ by gvs [good_dimindex_def,dimword_def]
  \\ qabbrev_tac ‘slice = DROP start (TAKE stop bytes)’
  \\ ‘LENGTH slice = stop - start’ by simp [Abbr‘slice’,LENGTH_DROP,LENGTH_TAKE_EQ]
  \\ drule_all word_exp_real_addr \\ strip_tac
  \\ simp [assign_def,arg4_def,assign_ScanByte_def,eq_eval]
  \\ ‘1 < dimindex (:'a)’ by fs [good_dimindex_def]
  \\ ‘(n2w (arch_bytes c.arch_width):'a word) = bytes_in_word’ by
       simp [data_to_wordTheory.arch_size,bytes_in_word_def]
  \\ ntac 5 (
    once_rewrite_tac [list_Seq_def]
    \\ simp [eq_eval,wordSemTheory.word_sh_def,Smallnum_lsr_1])
  \\ rewrite_tac [GSYM WORD_NEG_MUL,WORD_SUB]
  \\ simp [Smallnum_lsr_1,insert_shadow]
  \\ ‘(w2w (n2w raw_byte:word8):'a word) = n2w raw_byte’ by
       simp [w2w_n2w,bitTheory.BITS_ZEROL]
  \\ ‘∃md. lookup (if neq then ScanNeq_location else ScanEq_location) t.code =
      SOME (5,if neq then ScanNeq_code c else ScanEq_code c,md)’ by (
    Cases_on ‘neq’ \\ fs [code_rel_def,stubs_md_def,stubs_def,MAP_MAP_o,o_DEF])
  \\ drule cut_env_IMP_cut_envs
  \\ disch_then (qx_choosel_then [‘fixed’,‘live’] strip_assume_tac)
  \\ namedCases_on ‘env_to_list live t.permute’ ["saved_locals next_permute"]
  \\ simp [list_Seq_def,eq_eval,get_names_def,insert_shadow,
           cut_envs_adjust_sets_insert_ODD,domain_adjust_sets,wordSemTheory.push_env_def]
  \\ qmatch_goalsub_abbrev_tac
       ‘evaluate ((if neq then ScanNeq_code c else ScanEq_code c),call_state)’
  \\ qspecl_then [‘slice’,‘c’,‘neq’,‘n2w raw_byte:word8’,
                   ‘base + bytes_in_word + n2w start’,‘Smallnum (&start):'a word’,
                   ‘call_state’,‘n’,‘l’] mp_tac evaluate_ScanByte
  \\ impl_tac
  >- (
    ‘LENGTH slice < dimword (:'a)’ by (fs [] \\ decide_tac)
    \\ simp [Abbr‘call_state’,wordSemTheory.get_var_def,lookup_insert]
    \\ conj_tac
    >- (
      drule dimword_LESS_MustTerminate_limit
      \\ strip_tac \\ decide_tac
    )
    \\ qx_gen_tac ‘offset’ \\ strip_tac
    \\ ‘offset + start < stop ∧ offset + start < LENGTH bytes’ by decide_tac
    \\ qpat_x_assum ‘∀i. i < LENGTH bytes ⇒ mem_load_byte_aux _ _ _ _ = _’
         (qspec_then ‘offset + start’ mp_tac)
    \\ simp [Abbr‘slice’,EL_DROP,EL_TAKE,WORD_ADD_ASSOC,word_add_n2w]
    \\ rewrite_tac [GSYM word_add_n2w,WORD_ADD_ASSOC]
  )
  \\ strip_tac \\ simp []
  \\ simp [Abbr‘call_state’,wordSemTheory.pop_env_def]
  \\ drule env_to_list_domain \\ strip_tac
  \\ simp [domain_union,domain_fromAList_toAList,UNION_COMM,
           wordSemTheory.set_vars_def,alist_insert_def]
  \\ gvs [OPTION_MAP2_MAX_CANCEL]
  \\ ‘wf fixed ∧ wf live’ by
       gvs [wordSemTheory.cut_envs_def,wordSemTheory.cut_names_def,AllCaseEqs(),wf_inter]
  \\ drule env_to_list_lookup_equiv \\ strip_tac
  \\ ‘fromAList saved_locals = live’ by
       simp [spt_eq_thm,wf_fromAList,lookup_fromAList]
  \\ gvs [fromAList_toAList]
  \\ qabbrev_tac
       ‘scanned = LENGTH (FST (SPLITP (λw:word8. (w = n2w raw_byte) ⇔ ¬neq) slice))’
  \\ ‘scanned ≤ LENGTH slice’ by (
    qspecl_then [‘λw:word8. (w = n2w raw_byte) ⇔ ¬neq’,‘slice’]
      mp_tac (GEN_ALL SPLITP_LENGTH)
    \\ simp [Abbr‘scanned’] \\ decide_tac)
  \\ ‘start + scanned ≤ stop’ by (fs [] \\ decide_tac)
  \\ ‘small_int (dimindex (:'a)) (&(start + scanned))’ by (
    gvs [small_int_def,good_dimindex_def,dimword_def] \\ intLib.COOPER_TAC)
  \\ ‘Smallnum (&start) + 2w * n2w scanned = (Smallnum (&(start + scanned)):'a word)’ by
       simp [Smallnum_def,word_mul_n2w,word_add_n2w,LEFT_ADD_DISTRIB]
  \\ simp []
  \\ LABEL_ASSUM "with_locals" (assume_tac o REWRITE_RULE [state_rel_thm])
  \\ fs [state_rel_thm,dataSemTheory.set_var_def,lookup_insert,stack_size_eq]
  \\ conj_tac
  >- (
    qx_gen_tac ‘local_index’ \\ Cases_on ‘local_index = dest’
    \\ simp [adjust_var_11])
  \\ conj_tac
  >- simp [option_le_max_right,option_add_comm]
  \\ ‘stack_size t.stack = size_of_stack s.stack’ by (
    irule stack_rel_IMP_size_of_stack \\ first_assum (irule_at Any))
  \\ conj_tac
  >- simp [option_le_max,option_le_max_right,option_add_comm,option_le_add]
  \\ simp [inter_insert_ODD_adjust_set]
  \\ rewrite_tac [GSYM APPEND_ASSOC,APPEND]
  \\ irule memory_rel_insert \\ rewrite_tac [APPEND]
  \\ irule IMP_memory_rel_Number
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
  \\ qpat_x_assum ‘x.refs = s.refs’ (fn th => rewrite_tac [GSYM th])
  \\ qpat_x_assum ‘x.stack = s.stack’ (fn th => rewrite_tac [GSYM th])
  \\ first_assum ACCEPT_TAC
QED

Theorem evaluate_ByteCopyDispatch[local]:
  ∀s b a n fast slow.
    get_var 3 s = SOME (Word ((b:'a word) - a)) /\
    get_var 5 s = SOME (Word (a - b)) /\
    get_var 6 s = SOME (Word n) ==>
    evaluate (If NotLower 3 (Reg 6) (If NotLower 5 (Reg 6) fast slow) slow,s) =
      if n <=+ b - a /\ n <=+ a - b then evaluate (fast,s) else evaluate (slow,s)
Proof
  rpt gen_tac
  \\ strip_tac
  \\ Cases_on `n <=+ b - a`
  \\ Cases_on `n <=+ a - b`
  \\ fs [wordSemTheory.evaluate_def,wordSemTheory.get_var_imm_def,
           asmTheory.word_cmp_def,WORD_NOT_LOWER]
QED

Theorem do_app_aux_CopyWord_F[local]:
  do_app_aux (MemOp (CopyWord F)) vs s = Rval (v,s2) ⇔
  ∃copy_source copy_source_values copy_source_offset copy_length
     copy_target_flag copy_target_location copy_target_values copy_target_offset
     copy_result_values.
    vs = [copy_source; Number copy_source_offset; Number copy_length;
          RefPtr copy_target_flag copy_target_location; Number copy_target_offset] ∧
    word_copy_source s.refs copy_source copy_source_values ∧
    lookup copy_target_location s.refs = SOME (ValueArray copy_target_values) ∧
    copy_array (copy_source_values,copy_source_offset) copy_length
      (SOME (copy_target_values,copy_target_offset)) = SOME copy_result_values ∧
    v = Unit ∧
    s2 = s with refs := insert copy_target_location
                          (ValueArray copy_result_values) s.refs
Proof
  simp [do_app_aux_def,AllCaseEqs(),word_copy_source_def,PULL_EXISTS]
  >> eq_tac >> rw [] >> gvs []
QED

Theorem do_app_aux_CopyWord_T[local]:
  do_app_aux (MemOp (CopyWord T)) vs (s:('a,'b) dataSem$state) = Rval (v,s2) ⇔
  ∃copy_source copy_source_values copy_source_offset copy_length
     copy_result_values.
    vs = [copy_source; Number copy_source_offset; Number copy_length] ∧
    word_copy_source s.refs copy_source copy_source_values ∧
    copy_array (copy_source_values,copy_source_offset) copy_length NONE =
      SOME copy_result_values ∧
    (copy_result_values = [] ∧ v = Block 0 0 [] ∧ s2 = s ∨
     copy_result_values ≠ [] ∧
     with_fresh_ts s 1 (λts next. Rval (Block ts 0 copy_result_values,next)) =
       (Rval (v,s2) :(v # ('a,'b) dataSem$state, v) semanticPrimitives$result))
Proof
  simp [do_app_aux_def,AllCaseEqs(),word_copy_source_def,PULL_EXISTS]
  >> eq_tac >> rw [] >> gvs []
QED

Theorem assign_CopyWord:
  op = MemOp (CopyWord F) ⇒ ^assign_thm_goal
Proof
  rpt strip_tac
  >> gvs [dataLangTheory.op_requires_names_def]
  >> namedCases_on `names_opt` ["","copy_kept_names"]
  >> gvs []
  >> drule_all state_rel_cut_state_opt_SOME
  >> disch_then (qx_choosel_then [`copy_kept_locals`,`copy_argument_words`]
       strip_assume_tac)
  >> qpat_x_assum `state_rel c l1 l2 s t NONE locs`
       (assume_named_tac "copy_before")
  >> qpat_x_assum `state_rel c l1 l2 x (t with locals := copy_kept_locals) NONE locs`
       (assume_named_tac "copy_after_cut")
  >> drule do_app_stack_max
  >> disch_then (assume_named_tac "copy_stack_grows")
  >> qpat_x_assum `do_app (MemOp (CopyWord F)) vals x = Rval (v,s2)`
       (assume_named_tac "copy_primitive")
  >> LABEL_ASSUM "copy_primitive" assume_tac
  >> fs [do_app_def,do_app_aux_CopyWord_F,do_space_def,
         data_spaceTheory.op_space_req_def,dataLangTheory.op_space_reset_def,
         do_stack_def,stack_consumed_def,dataSemTheory.allowed_op_def]
  >> gvs [AllCaseEqs()]
  >> qpat_x_assum `LENGTH args = 5` (mp_tac o REWRITE_RULE [LENGTH_EQ_5])
  >> disch_then (qx_choosel_then
       [`copy_source_var`,`copy_source_offset_var`,`copy_length_var`,
        `copy_target_var`,`copy_target_offset_var`] assume_tac)
  >> qpat_x_assum `LENGTH copy_argument_words = 5`
       (mp_tac o REWRITE_RULE [LENGTH_EQ_5])
  >> disch_then (qx_choosel_then
       [`copy_source_rep`,`copy_source_offset_rep`,`copy_length_rep`,
        `copy_target_rep`,`copy_target_offset_rep`] assume_tac)
  >> gvs []
  >> LABEL_ASSUM "copy_before" (assume_tac o REWRITE_RULE [state_rel_thm])
  >> full_simp_tac std_ss [APPEND,GSYM APPEND_ASSOC]
  >> drule_all (memory_rel_get_vars_IMP
       |> Q.INST [`n` |-> `[copy_source_var; copy_source_offset_var; copy_length_var;
                            copy_target_var; copy_target_offset_var]`]
       |> SIMP_RULE (srw_ss()) [MAP])
  >> disch_then (assume_named_tac "copy_arguments_related")
  >> `x.refs = s.refs` by (
    drule cut_state_opt_SOME_eq
    >> strip_tac >> gvs [])
  >> qabbrev_tac `copy_frame =
       join_env s.locals (toAList (inter t.locals (adjust_set s.locals))) ++
       (the_global s.global,t.store ' Globals)::flat s.stack t.stack`
  >> `memory_rel c t.be (THE s.tstamps) s.refs s.space t.store t.memory t.mdomain
        ((copy_source,copy_source_rep)::
         (RefPtr copy_target_flag copy_target_location,copy_target_rep)::copy_frame)` by (
    LABEL_ASSUM "copy_arguments_related" mp_tac
    >> match_mp_tac memory_rel_rearrange
    >> rw [ZIP,MEM_APPEND,Abbr `copy_frame`] >> gvs [])
  >> `word_copy_source s.refs copy_source copy_source_values` by fs []
  >> drule_all memory_rel_copy_source_IMP
  >> disch_then (qx_choose_then `copy_source_pointer` strip_assume_tac)
  >> `lookup copy_target_location s.refs = SOME (ValueArray copy_target_values)`
       by fs []
  >> `memory_rel c t.be (THE s.tstamps) s.refs s.space t.store t.memory t.mdomain
        ((RefPtr copy_target_flag copy_target_location,copy_target_rep)::copy_frame)` by (
    LABEL_ASSUM "copy_arguments_related" mp_tac
    >> match_mp_tac memory_rel_rearrange
    >> rw [ZIP,MEM_APPEND,Abbr `copy_frame`] >> gvs [])
  >> drule_all memory_rel_ValueArray_IMP
  >> disch_then (qx_choosel_then
       [`copy_target_pointer`,`copy_target_address`,`copy_target_header`]
       strip_assume_tac)
  >> `LENGTH copy_target_values < dimword (:'a) DIV 16` by (
    fs [good_dimindex_def,dimword_def] >> rfs [])
  >> `∃copy_source_index copy_count copy_target_index.
        copy_source_offset = &copy_source_index ∧ copy_length = &copy_count ∧
        copy_target_offset = &copy_target_index ∧
        copy_source_index + copy_count ≤ LENGTH copy_source_values ∧
        copy_target_index + copy_count ≤ LENGTH copy_target_values` by (
    fs [semanticPrimitivesTheory.copy_array_def,not_less_zero_int_eq]
    >> rveq
    >> fs [NOT_LESS,integerTheory.INT_ADD,integerTheory.INT_ABS_NUM])
  >> gvs []
  >> `copy_source_index < dimword (:'a) DIV 16 ∧
      copy_count < dimword (:'a) DIV 16 ∧
      copy_target_index < dimword (:'a) DIV 16` by decide_tac
  >> `small_int (dimindex (:'a)) (&copy_source_index) ∧
      small_int (dimindex (:'a)) (&copy_count) ∧
      small_int (dimindex (:'a)) (&copy_target_index)` by (
    fs [good_dimindex_def,dimword_def,small_int_def]
    >> rfs [] >> decide_tac)
  >> `2 * copy_source_index < dimword (:'a) ∧
      2 * copy_target_index < dimword (:'a) ∧
      2 * copy_count < dimword (:'a) ∧ 0 < dimindex (:'a) DIV 8 ∧
      2 * (copy_count * (dimindex (:'a) DIV 8)) < dimword (:'a)` by (
    fs [good_dimindex_def,dimword_def]
    >> rfs [] >> decide_tac)
  >> `memory_rel c t.be (THE s.tstamps) s.refs s.space t.store t.memory t.mdomain
        [(Number (&copy_source_index),copy_source_offset_rep);
         (Number (&copy_count),copy_length_rep);
         (Number (&copy_target_index),copy_target_offset_rep)]` by (
    LABEL_ASSUM "copy_arguments_related" mp_tac
    >> match_mp_tac memory_rel_rearrange
    >> rw [ZIP,MEM_APPEND] >> gvs [])
  >> ntac 2 (imp_res_tac memory_rel_tl)
  >> imp_res_tac memory_rel_Number_IMP
  >> gvs [Smallnum_def]
  >> `∃copy_source_address.
        get_real_addr c t.store copy_source_pointer = SOME copy_source_address` by (
    fs [get_real_addr_def,AllCaseEqs()])
  >> `memory_rel c t.be (THE s.tstamps) s.refs s.space t.store t.memory t.mdomain
        (eq_explode (copy_source_address + bytes_in_word) t.memory t.mdomain
           (TAKE (LENGTH copy_source_values) copy_source_values) ++
         (copy_source,
          Word copy_source_pointer)::
         (RefPtr copy_target_flag copy_target_location,Word copy_target_pointer)::
         copy_frame) ∧
      eq_assum (copy_source_address + bytes_in_word) t.memory t.mdomain
        (TAKE (LENGTH copy_source_values) copy_source_values)` by (
    irule memory_rel_copy_source_fields
    >> asm_simp_tac std_ss [])
  >> fs []
  >> `memory_rel c t.be (THE s.tstamps) s.refs s.space t.store t.memory t.mdomain
        (ZIP (TAKE copy_count (DROP copy_source_index copy_source_values),
          GENLIST (λi. t.memory (copy_source_address + bytes_in_word +
            n2w copy_source_index * bytes_in_word + n2w i * bytes_in_word))
            copy_count) ++
         (copy_source,
          Word copy_source_pointer)::
         (RefPtr copy_target_flag copy_target_location,Word copy_target_pointer)::
         copy_frame) ∧
      ∀i. i < copy_count ⇒
        copy_source_address + bytes_in_word + n2w copy_source_index * bytes_in_word +
          n2w i * bytes_in_word ∈ t.mdomain` by (
    irule memory_rel_fields_slice
    >> asm_simp_tac std_ss [ADD_COMM])
  >> `LENGTH (TAKE copy_count (DROP copy_source_index copy_source_values)) =
        copy_count` by (
    simp [LENGTH_TAKE,LENGTH_DROP]
    >> decide_tac)
  >> `∀i. i < copy_count ⇒
        copy_target_address + bytes_in_word + n2w copy_target_index * bytes_in_word +
          n2w i * bytes_in_word ∈ t.mdomain` by (
    qx_gen_tac `copy_index`
    >> strip_tac
    >> `copy_target_index + copy_index < LENGTH copy_target_values` by decide_tac
    >> drule_all (memory_rel_Deref'
         |> Q.INST [`index` |-> `copy_target_index + copy_index`])
    >> strip_tac
    >> gvs [GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB,WORD_ADD_ASSOC])
  >> qabbrev_tac `copy_source_start =
       copy_source_address + bytes_in_word + n2w copy_source_index * bytes_in_word`
  >> qabbrev_tac `copy_target_start =
       copy_target_address + bytes_in_word + n2w copy_target_index * bytes_in_word`
  >> qabbrev_tac `copy_words =
       GENLIST (λi. t.memory (copy_source_start + n2w i * bytes_in_word)) copy_count`
  >> `store_list copy_target_start copy_words t.memory t.mdomain =
        SOME (copy_word_chunk copy_count copy_source_start copy_target_start t.memory)` by (
    asm_simp_tac std_ss [Abbr `copy_words`]
    >> irule copy_word_chunk_store_list
    >> simp [])
  >> `SND (word_copy_plan copy_count copy_source_start copy_target_start
        t.memory t.mdomain) =
        SOME (copy_word_chunk copy_count copy_source_start copy_target_start t.memory)` by (
    qspecl_then [`copy_count`,`copy_source_start`,`copy_target_start`,
      `t.memory`,`t.mdomain`] mp_tac word_copy_plan_store_list
    >> impl_tac >- asm_simp_tac std_ss []
    >> fs [Abbr `copy_words`])
  >> `memory_rel c t.be (THE s.tstamps) s.refs s.space t.store t.memory t.mdomain
        (ZIP (TAKE copy_count (DROP copy_source_index copy_source_values),copy_words) ++
         (RefPtr copy_target_flag copy_target_location,Word copy_target_pointer)::
         (copy_source,
          Word copy_source_pointer)::copy_frame)` by (
    qpat_x_assum `memory_rel _ _ _ _ _ _ _ _ (ZIP _ ++ _)` mp_tac
    >> match_mp_tac memory_rel_rearrange
    >> rw [MEM_APPEND] >> gvs [])
  >> `memory_rel c t.be (THE s.tstamps)
        (insert copy_target_location
          (ValueArray (TAKE copy_target_index copy_target_values ++
            TAKE copy_count (DROP copy_source_index copy_source_values) ++
            DROP (copy_target_index +
              LENGTH (TAKE copy_count (DROP copy_source_index copy_source_values)))
              copy_target_values)) s.refs)
        s.space t.store
        (copy_word_chunk copy_count copy_source_start copy_target_start t.memory)
        t.mdomain
        ((RefPtr copy_target_flag copy_target_location,Word copy_target_pointer)::
         (copy_source,
          Word copy_source_pointer)::copy_frame)` by (
    irule memory_rel_store_array_slice
    >> asm_simp_tac std_ss [ADD_COMM]
    >> qexistsl_tac [`t.memory`,`copy_words`]
    >> asm_simp_tac std_ss []
    >> simp [Abbr `copy_words`])
  >> `copy_result_values = TAKE copy_target_index copy_target_values ++
        TAKE copy_count (DROP copy_source_index copy_source_values) ++
        DROP (copy_target_index + copy_count) copy_target_values` by (
    fs [semanticPrimitivesTheory.copy_array_def,integerTheory.INT_ADD,
        integerTheory.INT_ABS_NUM])
  >> `arch_width_bits c.arch_width = dimindex (:'a)` by (
    drule state_rel_arch_width >> simp [])
  >> `get_var (adjust_var copy_source_var) t = SOME (Word copy_source_pointer) ∧
      get_var (adjust_var copy_source_offset_var) t =
        SOME (Word (n2w (2 * copy_source_index))) ∧
      get_var (adjust_var copy_length_var) t = SOME (Word (n2w (2 * copy_count))) ∧
      get_var (adjust_var copy_target_var) t = SOME (Word copy_target_pointer) ∧
      get_var (adjust_var copy_target_offset_var) t =
        SOME (Word (n2w (2 * copy_target_index)))` by (
    qpat_x_assum `get_vars _ t = SOME _` mp_tac
    >> simp [wordSemTheory.get_vars_def,AllCaseEqs()])
  >> `word_exp t (real_addr c (adjust_var copy_source_var)) =
        SOME (Word copy_source_address)` by (
    irule get_real_addr_lemma >> simp [])
  >> `word_exp t (real_addr c (adjust_var copy_target_var)) =
        SOME (Word copy_target_address)` by (
    irule get_real_addr_lemma >> simp [])
  >> `get_real_offset (n2w (2 * copy_source_index):'a word) =
        SOME (bytes_in_word + n2w copy_source_index * bytes_in_word) ∧
      get_real_offset (n2w (2 * copy_target_index):'a word) =
        SOME (bytes_in_word + n2w copy_target_index * bytes_in_word)` by (
    fs [good_dimindex_def,get_real_offset_def,bytes_in_word_def,
        word_lsl_n2w,word_mul_n2w]
    >> simp [MULT_ASSOC,WORD_ADD_COMM])
  >> `word_exp t (real_offset c (adjust_var copy_source_offset_var)) =
        SOME (Word (bytes_in_word + n2w copy_source_index * bytes_in_word))` by (
    irule get_real_offset_lemma >> simp [])
  >> `word_exp t (real_offset c (adjust_var copy_target_offset_var)) =
        SOME (Word (bytes_in_word + n2w copy_target_index * bytes_in_word))` by (
    irule get_real_offset_lemma >> simp [])
  >> `∀copy_temp.
        word_exp (t with locals := insert 1 (Word copy_temp) t.locals)
          (real_addr c (adjust_var copy_target_var)) =
        SOME (Word copy_target_address)` by (
    irule word_exp_real_addr >> fs [wordSemTheory.get_var_def])
  >> `word_exp (t with locals := insert 1 (Word copy_source_start) t.locals)
        (real_offset c (adjust_var copy_target_offset_var)) =
        SOME (Word (bytes_in_word + n2w copy_target_index * bytes_in_word))` by (
    irule get_real_offset_lemma
    >> fs [wordSemTheory.get_var_def,lookup_insert])
  >> `word_exp t (Op Add [real_addr c (adjust_var copy_source_var);
        real_offset c (adjust_var copy_source_offset_var)]) =
        SOME (Word copy_source_start)` by (
    simp [wordSemTheory.word_exp_def,wordSemTheory.word_op_def,
          wordSemTheory.the_words_def,Abbr `copy_source_start`,WORD_ADD_ASSOC])
  >> `word_exp (t with locals := insert 1 (Word copy_source_start) t.locals)
        (Op Add [real_addr c (adjust_var copy_target_var);
          real_offset c (adjust_var copy_target_offset_var)]) =
        SOME (Word copy_target_start)` by (
    simp [wordSemTheory.word_exp_def,wordSemTheory.word_op_def,
          wordSemTheory.the_words_def,Abbr `copy_target_start`,WORD_ADD_ASSOC])
  >> `∃copy_md copy_add_md copy_sub_md copy_loop_md.
        lookup WordCopy_location t.code = SOME (5,WordCopy_code c,copy_md) ∧
        lookup WordCopyAdd_location t.code = SOME (5,WordCopyAdd_code c,copy_add_md) ∧
        lookup WordCopySub_location t.code = SOME (5,WordCopySub_code c,copy_sub_md) ∧
        lookup WordCopyLoop_location t.code = SOME (5,WordCopyLoop_code c,copy_loop_md)` by (
    fs [data_to_word_gcProofTheory.code_rel_def,stubs_md_def,stubs_def,MAP_MAP_o,o_DEF])
  >> simp [assign_def,assign_CopyWord_def,list_Seq_def,eq_eval,
           data_to_wordTheory.Unit_def,GSYM WORD_ADD_ASSOC]
  >> drule cut_env_IMP_cut_envs
  >> disch_then (qx_choosel_then [`copy_saved_return`,`copy_saved_locals`] strip_assume_tac)
  >> fs [get_names_def,wordSemTheory.get_var_def]
  >> simp [domain_adjust_sets,cut_envs_adjust_sets_insert_ODD]
  >> qmatch_goalsub_abbrev_tac `evaluate (WordCopy_code c,copy_call_state)`
  >> `word_copy_plan copy_count copy_source_start copy_target_start t.memory t.mdomain =
        (FST (word_copy_plan copy_count copy_source_start copy_target_start
          t.memory t.mdomain),
         SOME (copy_word_chunk copy_count copy_source_start copy_target_start t.memory))` by (
    Cases_on `word_copy_plan copy_count copy_source_start copy_target_start
      t.memory t.mdomain` >> fs [])
  >> `copy_count + 2 < dimword (:'a)` by (
    fs [good_dimindex_def,dimword_def] >> rfs [] >> decide_tac)
  >> `FST (word_copy_plan copy_count copy_source_start copy_target_start
        t.memory t.mdomain) < dimword (:'a)` by (
    qspecl_then [`copy_count`,`copy_source_start`,`copy_target_start`,
      `t.memory`,`t.mdomain`] mp_tac word_copy_plan_ticks_bound
    >> decide_tac)
  >> `FST (word_copy_plan copy_count copy_source_start copy_target_start
        t.memory t.mdomain) ≤ MustTerminate_limit (:'a) - 1` by (
    drule IMP_LESS_MustTerminate_limit >> decide_tac)
  >> qpat_x_assum `word_copy_plan _ _ _ _ _ = _`
       (assume_named_tac "copy_plan")
  >> qspecl_then [`copy_count`,`c`,`copy_source_start`,`copy_target_start`,
       `copy_call_state`,`t.memory`,`t.mdomain`,
       `copy_word_chunk copy_count copy_source_start copy_target_start t.memory`,
       `FST (word_copy_plan copy_count copy_source_start copy_target_start t.memory t.mdomain)`,
       `Word (0w:'a word)`,`n`,`l`] mp_tac WordCopy_thm
  >> impl_tac
  >- (
    simp [Abbr `copy_call_state`,wordSemTheory.get_var_def,lookup_insert]
    >> LABEL_ASSUM "copy_plan" ACCEPT_TAC)
  >> disch_then (qx_choose_then `copy_maximum` strip_assume_tac)
  >> namedCases_on `env_to_list copy_saved_locals t.permute`
    ["copy_saved_values copy_next_permute"]
  >> `wf copy_saved_return ∧ wf copy_saved_locals` by (
    gvs [wordSemTheory.cut_envs_def,wordSemTheory.cut_names_def,
         AllCaseEqs(),wf_inter])
  >> drule env_to_list_lookup_equiv >> strip_tac
  >> `fromAList copy_saved_values = copy_saved_locals` by (
    simp [spt_eq_thm,wf_fromAList,lookup_fromAList])
  >> fs [Abbr `copy_call_state`,wordSemTheory.pop_env_def,wordSemTheory.push_env_def,
         wordSemTheory.set_vars_def,alist_insert_def,fromAList_toAList,domain_union,
         AC UNION_COMM UNION_ASSOC]
  >> rfs [wordSemTheory.pop_env_def,wordSemTheory.set_vars_def,alist_insert_def,
          fromAList_toAList,domain_union]
  >> `x.stack = s.stack ∧ x.stack_max = s.stack_max ∧
      x.locals_size = s.locals_size ∧ x.stack_frame_sizes = s.stack_frame_sizes ∧
      x.tstamps = s.tstamps ∧ x.space = s.space ∧ x.global = s.global` by (
    drule cut_state_opt_SOME_eq >> strip_tac >> gvs [])
  >> LABEL_ASSUM "copy_after_cut" (assume_tac o REWRITE_RULE [state_rel_thm])
  >> fs [state_rel_thm,dataSemTheory.set_var_def,lookup_insert,adjust_var_11]
  >> drule evaluate_stack_max_le
  >> simp [option_le_max,stack_size_eq,option_add_comm]
  >> strip_tac
  >> rfs []
  >> conj_tac
  >- (
    qx_gen_tac `copy_local`
    >> Cases_on `copy_local = dest` >> simp [])
  >> `stack_size t.stack = size_of_stack s.stack` by (
    irule stack_rel_IMP_size_of_stack >> first_assum (irule_at Any))
  >> conj_tac
  >- (
    qmatch_asmsub_abbrev_tac `option_le copy_maximum copy_stack_bound`
    >> irule option_le_trans
    >> qexists_tac `copy_stack_bound`
    >> conj_tac >- simp []
    >> simp [Abbr `copy_stack_bound`,stack_size_eq,option_map2_max_add,
             option_le_max,option_le_max_right,option_le_add,option_add_comm]
    >> disj2_tac >> disj1_tac
    >> irule (ONCE_REWRITE_RULE [option_add_comm] option_le_add))
  >> full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
  >> irule memory_rel_insert
  >> rewrite_tac [APPEND]
  >> irule memory_rel_Unit
  >> asm_simp_tac std_ss []
  >> qpat_x_assum `memory_rel _ _ _ (insert _ _ _) _ _ _ _ (_::_)`
       (mp_tac o MATCH_MP memory_rel_tl o MATCH_MP memory_rel_tl)
  >> match_mp_tac memory_rel_rearrange
  >> rw [Abbr `copy_frame`,MEM_APPEND]
  >> gvs []
  >> `∀copy_index copy_value.
        lookup copy_index x.locals = SOME copy_value ⇒
        lookup copy_index s.locals = SOME copy_value` by (
    drule cut_state_opt_SOME_eq >> strip_tac >> gvs []
    >> rw [lookup_inter_alt,AllCaseEqs()] >> gvs [])
  >> disj1_tac
  >> fs [join_env_def,MEM_MAP,MEM_FILTER,EXISTS_PROD,MEM_toAList,
         lookup_inter_alt,AllCaseEqs()]
  >> qmatch_goalsub_rename_tac `THE (lookup ((copy_word_index - 2) DIV 2) x.locals)`
  >> `∃copy_data_value.
        lookup ((copy_word_index - 2) DIV 2) x.locals = SOME copy_data_value` by (
    fs [domain_lookup,lookup_adjust_set,GSYM EVEN_ODD,IS_SOME_EXISTS])
  >> qpat_x_assum `∀i v. lookup i x.locals = SOME v ⇒ _`
       (qspecl_then [`(copy_word_index - 2) DIV 2`,`copy_data_value`] mp_tac)
  >> asm_simp_tac std_ss []
  >> strip_tac
  >> drule_all cut_env_IMP_lookup >> strip_tac
  >> qexists_tac `copy_word_index`
  >> fs [lookup_adjust_set,domain_lookup,GSYM EVEN_ODD]
QED

Theorem copy_word_header[local]:
  arch_width_bits c.arch_width = dimindex (:'a) ∧
  c.len_size ≠ 0 ∧ c.len_size + 9 < dimindex (:'a) ⇒
  (3w || (n2w (2 * copy_count):'a word) <<
    (arch_width_bits c.arch_width - c.len_size - 1)) =
  n2w (make_header c 0 copy_count)
Proof
  strip_tac
  >> `dimindex (:'a) - c.len_size - 1 + 1 = dimindex (:'a) - c.len_size` by
       decide_tac
  >> `dimindex (:'a) - c.len_size < dimindex (:'a)` by decide_tac
  >> `2 ** 2 ≤ 2 ** (dimindex (:'a) - c.len_size)` by (
    irule bitTheory.TWOEXP_MONO2 >> decide_tac)
  >> asm_rewrite_tac [make_header_def,LET_THM,MULT_CLAUSES,ADD_CLAUSES,TWO_MUL_LSL]
  >> once_rewrite_tac [WORD_OR_COMM]
  >> BETA_TAC
  >> irule shifted_header_or
  >> simp []
QED

Theorem assign_CopyWord_new:
  op = MemOp (CopyWord T) ⇒ ^assign_thm_goal
Proof
  rpt strip_tac
  >> gvs [dataLangTheory.op_requires_names_def]
  >> namedCases_on `names_opt` ["","copy_kept_names"]
  >> gvs []
  >> drule_all state_rel_cut_state_opt_SOME
  >> disch_then (qx_choosel_then [`copy_kept_locals`,`copy_argument_words`]
       strip_assume_tac)
  >> qpat_x_assum `state_rel c l1 l2 s t NONE locs`
       (assume_named_tac "copy_before")
  >> qpat_x_assum `state_rel c l1 l2 x (t with locals := copy_kept_locals) NONE locs`
       (assume_named_tac "copy_after_cut")
  >> `IS_SOME x.tstamps` by fs [state_rel_thm]
  >> namedCases_on `x.tstamps` ["","copy_new_timestamp"]
  >> fs []
  >> drule do_app_stack_max
  >> disch_then (assume_named_tac "copy_stack_grows")
  >> qpat_x_assum `do_app (MemOp (CopyWord T)) vals x = Rval (v,s2)`
       (assume_named_tac "copy_primitive")
  >> LABEL_ASSUM "copy_primitive" assume_tac
  >> fs [do_app_def,do_app_aux_CopyWord_T,do_space_def,
         data_spaceTheory.op_space_req_def,dataLangTheory.op_space_reset_def,
         do_stack_def,stack_consumed_def,dataSemTheory.allowed_op_def,
         dataSemTheory.with_fresh_ts_def]
  >> gvs [AllCaseEqs()]
  >~ [`get_vars _ s.locals = SOME
         [copy_source; Number copy_source_offset; Number copy_length] (* a *)`,
       `copy_array (copy_source_values,copy_source_offset) copy_length NONE = SOME []
          (* a *)`] >- (
    `∃copy_source_index copy_count.
       copy_source_offset = &copy_source_index ∧ copy_length = &copy_count ∧
       copy_source_index + copy_count ≤ LENGTH copy_source_values` by (
      fs [semanticPrimitivesTheory.copy_array_def,not_less_zero_int_eq]
      >> rveq
      >> fs [NOT_LESS,integerTheory.INT_ADD,integerTheory.INT_ABS_NUM])
    >> gvs []
    >> `copy_count = 0` by (
      fs [semanticPrimitivesTheory.copy_array_def,integerTheory.INT_ADD,
          integerTheory.INT_ABS_NUM]
      >> qpat_x_assum `TAKE _ _ = []` (mp_tac o AP_TERM ``LENGTH:dataSem$v list -> num``)
      >> simp [LENGTH_TAKE,LENGTH_DROP]
      >> decide_tac)
    >> gvs []
    >> qpat_x_assum `LENGTH args = 3` (mp_tac o REWRITE_RULE [LENGTH_EQ_3])
    >> disch_then (qx_choosel_then
         [`copy_source_var`,`copy_source_offset_var`,`copy_length_var`] assume_tac)
    >> gvs []
    >> `dataSem$get_var copy_length_var s.locals = SOME (Number (&0))` by (
      qpat_x_assum `get_vars _ s.locals = SOME _` mp_tac
      >> simp [dataSemTheory.get_vars_def,AllCaseEqs()])
    >> `small_int (dimindex (:'a)) (&0)` by (
      fs [state_rel_thm,good_dimindex_def,small_int_def])
    >> LABEL_ASSUM "copy_before" assume_tac
    >> drule_all state_rel_get_var_Number_IMP >> strip_tac
    >> `arch_width_bits c.arch_width = dimindex (:'a)` by (
      drule state_rel_arch_width >> simp [])
    >> `good_dimindex (:'a)` by fs [state_rel_thm]
    >> `encode_header c 0 0 = SOME 3` by (
      fs [encode_header_def,make_header_def,good_dimindex_def] >> rfs [])
    >> fs [Smallnum_def,wordSemTheory.get_var_def]
    >> simp [assign_def,assign_CopyWord_def,eq_eval]
    >> fs [state_rel_thm,dataSemTheory.set_var_def,lookup_insert,adjust_var_11,
           option_le_max_right]
    >> rfs []
    >> conj_tac
    >- (
      qx_gen_tac `copy_local`
      >> Cases_on `copy_local = dest` >> simp [])
    >> conj_tac
    >- (
      qpat_x_assum `option_le (OPTION_MAP2 $+ (stack_size t.stack) t.locals_size)
        t.stack_max` mp_tac
      >> simp [])
    >> irule memory_rel_zero_space
    >> qexists_tac `x.space`
    >> full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
    >> irule memory_rel_insert
    >> rewrite_tac [APPEND]
    >> rewrite_tac [GSYM (SIMP_RULE std_ss [tuple_tag_def] dataSemTheory.Unit_def)]
    >> irule memory_rel_Unit
    >> asm_simp_tac std_ss [])
  >> qpat_x_assum `LENGTH args = 3` (mp_tac o REWRITE_RULE [LENGTH_EQ_3])
  >> disch_then (qx_choosel_then
       [`copy_source_var`,`copy_source_offset_var`,`copy_length_var`] assume_tac)
  >> qpat_x_assum `LENGTH copy_argument_words = 3`
       (mp_tac o REWRITE_RULE [LENGTH_EQ_3])
  >> disch_then (qx_choosel_then
       [`copy_source_rep`,`copy_source_offset_rep`,`copy_length_rep`] assume_tac)
  >> gvs []
  >> `∃copy_source_index copy_count.
        copy_source_offset = &copy_source_index ∧ copy_length = &copy_count ∧
        copy_source_index + copy_count ≤ LENGTH copy_source_values` by (
    fs [semanticPrimitivesTheory.copy_array_def,not_less_zero_int_eq]
    >> rveq
    >> fs [NOT_LESS,integerTheory.INT_ADD,integerTheory.INT_ABS_NUM])
  >> gvs []
  >> `copy_count ≠ 0` by (
    CCONTR_TAC
    >> fs [semanticPrimitivesTheory.copy_array_def,integerTheory.INT_ADD,
           integerTheory.INT_ABS_NUM])
  >> LABEL_ASSUM "copy_before" (assume_tac o REWRITE_RULE [state_rel_thm])
  >> full_simp_tac std_ss [APPEND,GSYM APPEND_ASSOC]
  >> drule_all (memory_rel_get_vars_IMP
       |> Q.INST [`n` |-> `[copy_source_var; copy_source_offset_var; copy_length_var]`]
       |> SIMP_RULE (srw_ss()) [MAP])
  >> disch_then (assume_named_tac "copy_arguments_related")
  >> `x.refs = s.refs` by (
    drule cut_state_opt_SOME_eq >> strip_tac >> gvs [])
  >> qabbrev_tac `copy_frame =
       join_env s.locals (toAList (inter t.locals (adjust_set s.locals))) ++
       (the_global s.global,t.store ' Globals)::flat s.stack t.stack`
  >> `memory_rel c t.be (THE s.tstamps) s.refs s.space t.store t.memory t.mdomain
        ((copy_source,copy_source_rep)::copy_frame)` by (
    LABEL_ASSUM "copy_arguments_related" mp_tac
    >> match_mp_tac memory_rel_rearrange
    >> rw [ZIP,MEM_APPEND,Abbr `copy_frame`] >> gvs [])
  >> `copy_source_values ≠ []` by (CCONTR_TAC >> fs [])
  >> `word_copy_source s.refs copy_source copy_source_values` by fs []
  >> drule_all memory_rel_copy_source_IMP
  >> disch_then (qx_choose_then `copy_source_pointer` strip_assume_tac)
  >> qpat_x_assum `_ ≠ [] ⇒ _`
       (drule_then (qx_choose_then `copy_source_address` assume_tac))
  >> `copy_source_index < dimword (:'a) DIV 16 ∧
      copy_count < dimword (:'a) DIV 16` by decide_tac
  >> `small_int (dimindex (:'a)) (&copy_source_index) ∧
      small_int (dimindex (:'a)) (&copy_count)` by (
    fs [good_dimindex_def,dimword_def,small_int_def] >> rfs [] >> decide_tac)
  >> `2 * copy_source_index < dimword (:'a) ∧
      2 * copy_count < dimword (:'a)` by (
    fs [good_dimindex_def,dimword_def] >> rfs [] >> decide_tac)
  >> `memory_rel c t.be (THE s.tstamps) s.refs s.space t.store t.memory t.mdomain
        [(Number (&copy_source_index),copy_source_offset_rep);
         (Number (&copy_count),copy_length_rep)]` by (
    LABEL_ASSUM "copy_arguments_related" mp_tac
    >> match_mp_tac memory_rel_rearrange
    >> rw [ZIP,MEM_APPEND] >> gvs [])
  >> imp_res_tac memory_rel_tl
  >> imp_res_tac memory_rel_Number_IMP
  >> gvs [Smallnum_def]
  >> `arch_width_bits c.arch_width = dimindex (:'a)` by (
    drule state_rel_arch_width >> simp [])
  >> `encode_header c 0 0 = SOME 3` by (
    fs [encode_header_def,make_header_def,good_dimindex_def] >> rfs [])
  >> `get_var (adjust_var copy_length_var) t = SOME (Word (n2w (2 * copy_count)))` by (
    qpat_x_assum `get_vars _ t = SOME _` mp_tac
    >> simp [wordSemTheory.get_vars_def,AllCaseEqs()])
  >> `¬word_bit 0 (n2w (2 * copy_count):'a word)` by (
    simp [word_bit_def,word_index,bitTheory.BIT0_ODD,ODD_MULT])
  >> drule_all evaluate_BignumHalt2 >> simp [] >> strip_tac
  >> `(n2w (2 * copy_count):'a word) ≠ 0w` by (
    simp [GSYM w2n_11])
  >> fs [wordSemTheory.get_var_def]
  >> simp [assign_def,assign_CopyWord_def,list_Seq_def,eq_eval,GSYM dimword_def]
  >> qpat_x_assum `¬word_bit 0 (n2w (2 * copy_count):'a word)`
       (assume_tac o SIMP_RULE std_ss [word_bit_def])
  >> simp [get_names_def]
  >> qmatch_goalsub_abbrev_tac `evaluate (AllocVar c copy_limit copy_alloc_names,copy_alloc_start)`
  >> `state_rel c l1 l2 s copy_alloc_start NONE locs` by (
    LABEL_ASSUM "copy_before" mp_tac
    >> simp [Abbr `copy_alloc_start`,state_rel_insert_1])
  >> `get_var 1 copy_alloc_start = SOME (Word (n2w (2 * copy_count)))` by (
    simp [Abbr `copy_alloc_start`,wordSemTheory.get_var_def,lookup_insert])
  >> `copy_limit < dimword (:'a) DIV 8` by (
    fs [Abbr `copy_limit`,good_dimindex_def,dimword_def] >> rfs [])
  >> `domain copy_kept_names ⊆ domain s.locals` by (
    fs [dataSemTheory.cut_state_opt_def,dataSemTheory.cut_state_def,
        dataSemTheory.cut_env_def,AllCaseEqs()])
  >> `set [copy_source_var;copy_source_offset_var;copy_length_var] ⊆ domain s.locals` by (
    rw [SUBSET_DEF] >> metis_tac [get_vars_IMP_domain,MEM])
  >> `∃copy_alloc_locals.
        dataSem$cut_env copy_alloc_names s.locals = SOME copy_alloc_locals` by (
    fs [dataSemTheory.cut_env_def,Abbr `copy_alloc_names`,domain_insert,SUBSET_DEF]
    >> rw [] >> fs [])
  >> namedCases_on `evaluate (AllocVar c copy_limit copy_alloc_names,copy_alloc_start)`
       ["copy_alloc_result copy_alloc_state"]
  >> qspecl_then [`c`,`l1`,`l2`,`s`,`copy_alloc_start`,`locs`,
       `[copy_source_var;copy_source_offset_var;copy_length_var]`,`copy_kept_names`,
       `copy_alloc_locals`,
       `[copy_source;
         Number (&copy_source_index);Number (&copy_count)]`,
       `copy_count`,`copy_limit`,`copy_alloc_result`,`copy_alloc_state`]
       mp_tac AllocVar_thm_nary
  >> impl_tac
  >- fs [Abbr `copy_alloc_names`,list_insert_def]
  >> disch_then (CONJUNCTS_THEN2
       (assume_named_tac "copy_alloc_failure")
       (assume_named_tac "copy_alloc_success"))
  >> Cases_on `copy_alloc_result = SOME NotEnoughSpace`
  >~ [`copy_alloc_result = SOME NotEnoughSpace (* a *)`]
    >- (
      LABEL_ASSUM "copy_alloc_failure" mp_tac
      >> asm_simp_tac std_ss []
      >> disch_then (CONJUNCTS_THEN2 assume_tac
           (CONJUNCTS_THEN2 assume_tac (assume_named_tac "copy_heap_failure")))
      >> `x.stack_max = s.stack_max ∧ x.limits = s.limits ∧
          cut_locals copy_kept_names s = x` by (
        fs [dataSemTheory.cut_state_opt_def,dataSemTheory.cut_state_def,
            cut_locals_def,AllCaseEqs()]
        >> rveq >> simp [])
      >> simp []
      >> conj_tac >- simp [option_le_max_right]
      >> strip_tac >> disj1_tac
      >> spose_not_then strip_assume_tac
      >> fs []
      >> `copy_count < copy_limit` by (
        fs [Abbr `copy_limit`,limits_inv_def] >> rfs [])
      >> LABEL_ASSUM "copy_heap_failure" mp_tac
      >> asm_simp_tac std_ss []
      >> fs [space_consumed_def]
      >> decide_tac)
  >> LABEL_ASSUM "copy_alloc_success" mp_tac
  >> asm_simp_tac std_ss [] >> strip_tac
  >> gvs []
  >> `dataSem$get_vars [copy_source_var;copy_source_offset_var;copy_length_var]
      copy_alloc_locals = SOME [copy_source;
        Number (&copy_source_index);Number (&copy_count)]` by (
    gvs [dataSemTheory.cut_env_def,Abbr `copy_alloc_names`,
         dataSemTheory.get_vars_def,dataSemTheory.get_var_def,
         lookup_inter_alt,AllCaseEqs()])
  >> qpat_x_assum `state_rel c l1 l2
       (s with <|locals := copy_alloc_locals; space := copy_count + 1|>)
       copy_alloc_state NONE locs` (assume_named_tac "copy_allocated_state")
  >> LABEL_ASSUM "copy_allocated_state"
       (mp_then (Pos hd) mp_tac state_rel_get_vars_IMP)
  >> disch_then (qspecl_then
       [`[copy_source_var;copy_source_offset_var;copy_length_var]`,
        `[copy_source;
          Number (&copy_source_index);Number (&copy_count)]`] mp_tac)
  >> impl_tac >- simp []
  >> disch_then (qx_choose_then `copy_alloc_words` strip_assume_tac)
  >> fs []
  >> qpat_x_assum `3 = LENGTH copy_alloc_words`
       (mp_tac o REWRITE_RULE [LENGTH_EQ_3] o GSYM)
  >> disch_then (qx_choosel_then
       [`copy_alloc_source_rep`,`copy_alloc_offset_rep`,`copy_alloc_length_rep`] assume_tac)
  >> gvs []
  >> LABEL_ASSUM "copy_allocated_state" (assume_tac o REWRITE_RULE [state_rel_thm])
  >> fs []
  >> full_simp_tac std_ss [APPEND,GSYM APPEND_ASSOC]
  >> drule_all (memory_rel_get_vars_IMP_lemma
       |> Q.INST [`n` |-> `[copy_source_var;copy_source_offset_var;copy_length_var]`]
       |> SIMP_RULE (srw_ss()) [MAP])
  >> disch_then (assume_named_tac "copy_alloc_arguments_related")
  >> qabbrev_tac `copy_alloc_frame =
       join_env copy_alloc_locals
         (toAList (inter copy_alloc_state.locals (adjust_set copy_alloc_locals))) ++
       (the_global s.global,copy_alloc_state.store ' Globals)::
       flat s.stack copy_alloc_state.stack`
  >> `memory_rel c copy_alloc_state.be (THE s.tstamps) s.refs (copy_count + 1)
        copy_alloc_state.store copy_alloc_state.memory copy_alloc_state.mdomain
        ((copy_source,copy_alloc_source_rep)::
         copy_alloc_frame)` by (
    LABEL_ASSUM "copy_alloc_arguments_related" mp_tac
    >> match_mp_tac memory_rel_rearrange
    >> rw [ZIP,MEM_APPEND,Abbr `copy_alloc_frame`] >> gvs [])
  >> drule_all memory_rel_copy_source_IMP
  >> disch_then (qx_choose_then `copy_alloc_source_pointer` strip_assume_tac)
  >> qpat_x_assum `_ ≠ [] ⇒ _`
       (drule_then (qx_choose_then `copy_alloc_source_address` assume_tac))
  >> `memory_rel c copy_alloc_state.be (THE s.tstamps) s.refs (copy_count + 1)
        copy_alloc_state.store copy_alloc_state.memory copy_alloc_state.mdomain
        [(Number (&copy_source_index),copy_alloc_offset_rep);
         (Number (&copy_count),copy_alloc_length_rep)]` by (
    LABEL_ASSUM "copy_alloc_arguments_related" mp_tac
    >> match_mp_tac memory_rel_rearrange
    >> rw [ZIP,MEM_APPEND] >> gvs [])
  >> imp_res_tac memory_rel_tl
  >> imp_res_tac memory_rel_Number_IMP
  >> qpat_x_assum `copy_alloc_offset_rep = Word (Smallnum (&copy_source_index))`
    (assume_tac o SIMP_RULE (srw_ss()) [Smallnum_def])
  >> qpat_x_assum `copy_alloc_length_rep = Word (Smallnum (&copy_count))`
       (assume_tac o SIMP_RULE (srw_ss()) [Smallnum_def])
  >> rveq
  >> `get_var (adjust_var copy_source_var) copy_alloc_state =
        SOME (Word copy_alloc_source_pointer) ∧
      get_var (adjust_var copy_source_offset_var) copy_alloc_state =
        SOME (Word (n2w (2 * copy_source_index))) ∧
      get_var (adjust_var copy_length_var) copy_alloc_state =
        SOME (Word (n2w (2 * copy_count)))` by (
    qpat_x_assum `get_vars _ copy_alloc_state = SOME _` mp_tac
    >> simp [wordSemTheory.get_vars_def,AllCaseEqs()])
  >> `∃copy_header. encode_header c 0 copy_count = SOME copy_header` by (
    qpat_x_assum `copy_count < copy_limit` mp_tac
    >> qunabbrev_tac `copy_limit`
    >> qpat_x_assum `arch_width_bits c.arch_width = dimindex (:'a)` mp_tac
    >> qpat_x_assum `good_dimindex (:'a)` mp_tac
    >> rpt (pop_assum kall_tac)
    >> rw [good_dimindex_def,dimword_def]
    >> qpat_x_assum `dimindex (:'a) = _` SUBST_ALL_TAC
    >> fs [encode_header_def])
  >> `c.len_size ≠ 0 ∧ c.len_size + 9 < dimindex (:'a)` by (
    drule memory_rel_len_size >> simp [])
  >> qpat_assum `memory_rel c copy_alloc_state.be (THE s.tstamps) s.refs
       (copy_count + 1) copy_alloc_state.store copy_alloc_state.memory
       copy_alloc_state.mdomain
       ((copy_source,Word copy_alloc_source_pointer)::
        copy_alloc_frame)`
       (mp_tac o MATCH_MP (memory_rel_write
         |> Q.INST [`w` |-> `Word (n2w copy_header:'a word)`]))
  >> disch_then (qx_choose_then `copy_free`
       (CONJUNCTS_THEN2 assume_tac
         (qspec_then `0` (strip_assume_tac o SIMP_RULE (srw_ss()) [LET_THM,DECIDE ``0 < n + 1``]))))
  >> qabbrev_tac `copy_header_memory =
       (copy_free =+ Word (n2w copy_header)) copy_alloc_state.memory`
  >> `memory_rel c copy_alloc_state.be (THE s.tstamps) s.refs (copy_count + 1)
        copy_alloc_state.store copy_header_memory copy_alloc_state.mdomain
        ((copy_source,Word copy_alloc_source_pointer)::
         copy_alloc_frame)` by simp [Abbr `copy_header_memory`]
  >> `memory_rel c copy_alloc_state.be (THE s.tstamps) s.refs (copy_count + 1)
        copy_alloc_state.store copy_header_memory copy_alloc_state.mdomain
        (eq_explode (copy_alloc_source_address + bytes_in_word)
           copy_header_memory copy_alloc_state.mdomain
           (TAKE (LENGTH copy_source_values) copy_source_values) ++
         (copy_source,
          Word copy_alloc_source_pointer)::copy_alloc_frame) ∧
      eq_assum (copy_alloc_source_address + bytes_in_word) copy_header_memory
        copy_alloc_state.mdomain
        (TAKE (LENGTH copy_source_values) copy_source_values)` by (
    irule memory_rel_copy_source_fields
    >> asm_simp_tac std_ss [])
  >> qpat_x_assum `memory_rel _ _ _ _ _ _ copy_header_memory _ (eq_explode _ _ _ _ ++ _)`
       (assume_tac o SIMP_RULE (srw_ss()) [])
  >> qpat_x_assum `eq_assum _ copy_header_memory _ _`
       (assume_tac o SIMP_RULE (srw_ss()) [])
  >> `memory_rel c copy_alloc_state.be (THE s.tstamps) s.refs (copy_count + 1)
        copy_alloc_state.store copy_header_memory copy_alloc_state.mdomain
        (ZIP (TAKE copy_count (DROP copy_source_index copy_source_values),
          GENLIST (λi. copy_header_memory (copy_alloc_source_address + bytes_in_word +
            n2w copy_source_index * bytes_in_word + n2w i * bytes_in_word))
            copy_count) ++
         (copy_source,
          Word copy_alloc_source_pointer)::copy_alloc_frame) ∧
      ∀i. i < copy_count ⇒
        copy_alloc_source_address + bytes_in_word + n2w copy_source_index * bytes_in_word +
          n2w i * bytes_in_word ∈ copy_alloc_state.mdomain` by (
    irule memory_rel_fields_slice
    >> asm_simp_tac std_ss [ADD_COMM])
  >> `copy_result_values = TAKE copy_count (DROP copy_source_index copy_source_values)` by (
    fs [semanticPrimitivesTheory.copy_array_def,integerTheory.INT_ADD,integerTheory.INT_ABS_NUM])
  >> `LENGTH copy_result_values = copy_count` by (
    simp [LENGTH_TAKE,LENGTH_DROP]
    >> decide_tac)
  >> qabbrev_tac `copy_source_start =
       copy_alloc_source_address + bytes_in_word + n2w copy_source_index * bytes_in_word`
  >> qabbrev_tac `copy_words =
       GENLIST (λi. copy_header_memory (copy_source_start + n2w i * bytes_in_word))
         copy_count`
  >> qspecl_then
       [`copy_words`,
        `(copy_source,
          Word copy_alloc_source_pointer)::copy_alloc_frame`,
        `copy_result_values`,`THE s.tstamps`,`0`,`copy_alloc_state.store`,
        `copy_count + 1`,`s.refs`,`copy_header_memory`,`copy_header`,
        `copy_alloc_state.mdomain`,`c`,`copy_alloc_state.be`]
       mp_tac (GEN_ALL memory_rel_Cons1)
  >> impl_tac
  >- (
    simp [Abbr `copy_words`,Abbr `copy_source_start`]
    >> fs [])
  >> disch_then (qx_choosel_then
       [`copy_result_free`,`copy_current_heap`,`copy_final_memory`]
         (strip_assume_tac o SIMP_RULE std_ss [LET_THM]))
  >> `copy_result_free = copy_free` by fs []
  >> qpat_x_assum `copy_result_free = copy_free` SUBST_ALL_TAC
  >> `LENGTH copy_words = copy_count` by simp [Abbr `copy_words`]
  >> qabbrev_tac `copy_target_start = copy_free + bytes_in_word`
  >> `store_list copy_target_start copy_words copy_header_memory
        copy_alloc_state.mdomain = SOME copy_final_memory` by (
    qpat_x_assum `store_list copy_free (_::_) _ _ = SOME copy_final_memory` mp_tac
    >> simp [store_list_def,Abbr `copy_header_memory`,Abbr `copy_target_start`])
  >> `∀i. i < copy_count ⇒
        copy_target_start + n2w i * bytes_in_word ∈ copy_alloc_state.mdomain` by (
    qpat_assum `store_list copy_target_start _ _ _ = SOME copy_final_memory`
      (mp_tac o MATCH_MP store_list_domain)
    >> simp [])
  >> `SND (word_copy_plan copy_count copy_source_start copy_target_start
        copy_header_memory copy_alloc_state.mdomain) = SOME copy_final_memory` by (
    `0 < dimindex (:'a) DIV 8 ∧
     2 * (copy_count * (dimindex (:'a) DIV 8)) < dimword (:'a)` by (
      qpat_x_assum `copy_count + copy_source_index ≤ LENGTH copy_source_values` mp_tac
      >> qpat_x_assum `LENGTH copy_source_values < dimword (:'a) DIV 16` mp_tac
      >> qpat_x_assum `good_dimindex (:'a)` mp_tac
      >> rpt (pop_assum kall_tac)
      >> rw [good_dimindex_def,dimword_def]
      >> qpat_x_assum `dimindex (:'a) = _` (fs o single)
      >> decide_tac)
    >> qspecl_then [`copy_count`,`copy_source_start`,`copy_target_start`,
         `copy_header_memory`,`copy_alloc_state.mdomain`] mp_tac word_copy_plan_store_list
    >> impl_tac >- asm_simp_tac std_ss []
    >> fs [Abbr `copy_words`])
  >> `copy_header = make_header c 0 copy_count` by fs [encode_header_def]
  >> `3w || (n2w (2 * copy_count):'a word) <<
        (dimindex (:'a) - (c.len_size + 1)) = n2w copy_header` by (
    qspecl_then [`copy_count`,`c`] mp_tac (GEN_ALL copy_word_header)
    >> asm_simp_tac std_ss [SUB_PLUS])
  >> `(n2w (2 * copy_count):'a word) >>> 1 = n2w copy_count` by (
    rewrite_tac [GSYM w2n_11,w2n_lsr]
    >> fs [ONCE_REWRITE_RULE [MULT_COMM] MULT_DIV])
  >> `1 < dimindex (:'a) ∧
      dimindex (:'a) - (c.len_size + 1) < dimindex (:'a) ∧
      dimindex (:'a) - (c.len_size + 1) < dimword (:'a)` by (
    assume_tac dimindex_lt_dimword
    >> fs [good_dimindex_def] >> decide_tac)
  >> qpat_x_assum `get_var (adjust_var copy_source_var) copy_alloc_state = SOME _`
       (assume_tac o REWRITE_RULE [wordSemTheory.get_var_def])
  >> qpat_x_assum `get_var (adjust_var copy_source_offset_var) copy_alloc_state = SOME _`
       (assume_tac o REWRITE_RULE [wordSemTheory.get_var_def])
  >> qpat_x_assum `get_var (adjust_var copy_length_var) copy_alloc_state = SOME _`
       (assume_tac o REWRITE_RULE [wordSemTheory.get_var_def])
  >> qpat_x_assum `Word (n2w (2 * copy_count)) = Word (Smallnum (&copy_count))` kall_tac
  >> qpat_x_assum `Word (n2w (2 * copy_source_index)) =
       Word (Smallnum (&copy_source_index))` kall_tac
  >> `(n2w (2 * copy_count):'a word) <<
        (dimindex (:'a) - (c.len_size + 1)) || 3w = n2w copy_header` by (
    once_rewrite_tac [WORD_OR_COMM]
    >> qpat_assum `3w || _ = n2w copy_header` ACCEPT_TAC)
  >> simp [wordSemTheory.get_store_def,wordSemTheory.word_sh_def,
           wordSemTheory.mem_store_def,lookup_insert]
  >> qmatch_goalsub_abbrev_tac
       `evaluate (Make_ptr_bits_code c 9 7 3,copy_pointer_state)`
  >> `c.tag_bits < dimindex (:'a) ∧ c.len_bits < dimindex (:'a) ∧
      c.len_bits + 1 < dimindex (:'a) ∧
      shift_length c < dimindex (:'a) + shift (dimindex (:'a))` by (
    fs [shift_length_def] >> decide_tac)
  >> `copy_count < dimword (:'a)` by decide_tac
  >> `evaluate (Make_ptr_bits_code c 9 7 3,copy_pointer_state) =
        (NONE,set_var 3
          (make_cons_ptr c (copy_free - copy_current_heap) 0 copy_count)
          copy_pointer_state)` by (
    qspecl_then [`9`,`0`,`copy_pointer_state`,`7`,`copy_count`,`copy_free`,
      `3`,`copy_current_heap`,`c`] mp_tac (GEN_ALL Make_ptr_bits_thm)
    >> impl_tac >- simp [Abbr `copy_pointer_state`,lookup_insert]
    >> simp [])
  >> `shift (dimindex (:'a)) < dimindex (:'a) ∧
      shift (dimindex (:'a)) < dimword (:'a)` by (
    assume_tac dimindex_lt_dimword
    >> rw [shift_def] >> fs [good_dimindex_def] >> decide_tac)
  >> simp [Abbr `copy_pointer_state`,wordSemTheory.set_var_def,
           wordSemTheory.set_store_def,lookup_insert,wordSemTheory.word_sh_def,shift_lsl]
  >> qmatch_goalsub_abbrev_tac
       `word_exp copy_source_state (real_addr c (adjust_var copy_source_var))`
  >> `get_real_addr c copy_source_state.store copy_alloc_source_pointer =
        SOME copy_alloc_source_address` by (
    qpat_x_assum `get_real_addr c copy_alloc_state.store copy_alloc_source_pointer =
      SOME copy_alloc_source_address` mp_tac
    >> simp [Abbr `copy_source_state`,get_real_addr_def,FLOOKUP_UPDATE])
  >> `get_var (adjust_var copy_source_var) copy_source_state =
      SOME (Word copy_alloc_source_pointer) ∧
   get_var (adjust_var copy_source_offset_var) copy_source_state =
      SOME (Word (n2w (2 * copy_source_index))) ∧
   get_var (adjust_var copy_length_var) copy_source_state =
      SOME (Word (n2w (2 * copy_count)))` by (
    simp [Abbr `copy_source_state`,wordSemTheory.get_var_def,lookup_insert])
  >> `word_exp copy_source_state (real_addr c (adjust_var copy_source_var)) =
        SOME (Word copy_alloc_source_address)` by (
    irule get_real_addr_lemma >> simp [])
  >> `get_real_offset (n2w (2 * copy_source_index):'a word) =
        SOME (bytes_in_word + n2w copy_source_index * bytes_in_word)` by (
    fs [good_dimindex_def,get_real_offset_def,bytes_in_word_def,
        word_lsl_n2w,word_mul_n2w]
    >> simp [MULT_ASSOC,WORD_ADD_COMM])
  >> `word_exp copy_source_state (real_offset c (adjust_var copy_source_offset_var)) =
        SOME (Word (bytes_in_word + n2w copy_source_index * bytes_in_word))` by (
    irule get_real_offset_lemma >> simp [])
  >> asm_simp_tac std_ss []
  >> simp []
  >> qpat_x_assum `copy_result_values = TAKE copy_count _`
       (assume_named_tac "copy_values_slice")
  >> qpat_x_assum `LENGTH copy_result_values = copy_count`
       (assume_named_tac "copy_values_length")
  >> `copy_alloc_state.termdep = t.termdep` by (
    qpat_assum `evaluate (AllocVar _ _ _,copy_alloc_start) = (NONE,copy_alloc_state)`
      (mp_tac o MATCH_MP wordSemTheory.evaluate_clock)
    >> simp [Abbr `copy_alloc_start`])
  >> `dataSem$cut_env copy_kept_names s.locals = SOME x.locals` by (
    qpat_x_assum `cut_state_opt (SOME copy_kept_names) s = SOME x` mp_tac
    >> rpt (pop_assum kall_tac)
    >> simp [dataSemTheory.cut_state_opt_def,dataSemTheory.cut_state_def,AllCaseEqs()]
    >> strip_tac >> gvs [])
  >> `dataSem$cut_env copy_kept_names copy_alloc_locals = SOME x.locals` by (
    irule cut_env_cut_env_list_insert
    >> qexistsl_tac
         [`s.locals`,`[copy_source_var;copy_source_offset_var;copy_length_var]`]
    >> simp [list_insert_def,Abbr `copy_alloc_names`])
  >> `cut_state_opt (SOME copy_kept_names)
        (s with <|locals := copy_alloc_locals;space := copy_count + 1|>) =
        SOME (x with space := copy_count + 1)` by (
    qpat_x_assum `cut_state_opt (SOME copy_kept_names) s = SOME x` mp_tac
    >> qpat_x_assum `dataSem$cut_env copy_kept_names copy_alloc_locals = SOME x.locals` mp_tac
    >> rpt (pop_assum kall_tac)
    >> simp [dataSemTheory.cut_state_opt_def,dataSemTheory.cut_state_def,AllCaseEqs()]
    >> rpt strip_tac >> gvs [])
  >> LABEL_ASSUM "copy_allocated_state"
    (mp_then (Pos hd) mp_tac state_rel_cut_state_opt_SOME)
  >> disch_then (qspecl_then
       [`x with space := copy_count + 1`,
        `[copy_source;
          Number (&copy_source_index);Number (&copy_count)]`,
        `copy_kept_names`,
        `[copy_source_var;copy_source_offset_var;copy_length_var]`] mp_tac)
  >> impl_tac >- simp []
  >> disch_then (qx_choosel_then
       [`copy_after_alloc_locals`,`copy_after_alloc_words`] strip_assume_tac)
  >> qpat_x_assum `state_rel c l1 l2 (x with space := copy_count + 1)
       (copy_alloc_state with locals := copy_after_alloc_locals) NONE locs`
       (assume_named_tac "copy_after_alloc_cut")
  >> `∃copy_md copy_add_md copy_sub_md copy_loop_md.
        lookup WordCopy_location copy_alloc_state.code = SOME (5,WordCopy_code c,copy_md) ∧
        lookup WordCopyAdd_location copy_alloc_state.code = SOME (5,WordCopyAdd_code c,copy_add_md) ∧
        lookup WordCopySub_location copy_alloc_state.code = SOME (5,WordCopySub_code c,copy_sub_md) ∧
        lookup WordCopyLoop_location copy_alloc_state.code = SOME (5,WordCopyLoop_code c,copy_loop_md)` by (
    qpat_x_assum `code_rel c s.code copy_alloc_state.code` mp_tac
    >> simp [data_to_word_gcProofTheory.code_rel_def,stubs_md_def,stubs_def,MAP_MAP_o,o_DEF])
  >> qpat_assum `cut_env (adjust_sets copy_kept_names) copy_alloc_state.locals =
       SOME copy_after_alloc_locals` (mp_tac o MATCH_MP cut_env_IMP_cut_envs)
  >> disch_then (qx_choosel_then
       [`copy_saved_return`,`copy_saved_locals`] strip_assume_tac)
  >> simp [lookup_insert,domain_adjust_sets,cut_envs_adjust_sets_insert_ODD]
  >> qpat_assum `copy_alloc_state.code = copy_alloc_start.code` mp_tac
  >> qpat_x_assum `copy_alloc_state.code = copy_alloc_start.code`
       (RULE_ASSUM_TAC o REWRITE_RULE o single)
  >> disch_tac
  >> simp []
  >> qmatch_goalsub_abbrev_tac `evaluate (WordCopy_code c,copy_call_state)`
  >> `word_copy_plan copy_count copy_source_start copy_target_start
        copy_header_memory copy_alloc_state.mdomain =
        (FST (word_copy_plan copy_count copy_source_start copy_target_start
          copy_header_memory copy_alloc_state.mdomain),SOME copy_final_memory)` by (
    qpat_x_assum `SND (word_copy_plan copy_count copy_source_start copy_target_start
      copy_header_memory copy_alloc_state.mdomain) = SOME copy_final_memory` mp_tac
    >> rpt (pop_assum kall_tac)
    >> Cases_on `word_copy_plan copy_count copy_source_start copy_target_start
      copy_header_memory copy_alloc_state.mdomain` >> simp [])
  >> `copy_count + 2 < dimword (:'a)` by (
    qpat_x_assum `copy_count + copy_source_index ≤ LENGTH copy_source_values` mp_tac
    >> qpat_x_assum `LENGTH copy_source_values < dimword (:'a) DIV 16` mp_tac
    >> qpat_x_assum `good_dimindex (:'a)` mp_tac
    >> rpt (pop_assum kall_tac)
    >> rw [good_dimindex_def,dimword_def]
    >> qpat_x_assum `dimindex (:'a) = _` (fs o single)
    >> decide_tac)
  >> `FST (word_copy_plan copy_count copy_source_start copy_target_start
        copy_header_memory copy_alloc_state.mdomain) < dimword (:'a)` by (
    qpat_x_assum `copy_count + 2 < dimword (:'a)` mp_tac
    >> rpt (pop_assum kall_tac)
    >> qspecl_then [`copy_count`,`copy_source_start`,`copy_target_start`,
         `copy_header_memory`,`copy_alloc_state.mdomain`] mp_tac word_copy_plan_ticks_bound
    >> decide_tac)
  >> `FST (word_copy_plan copy_count copy_source_start copy_target_start
        copy_header_memory copy_alloc_state.mdomain) ≤ MustTerminate_limit (:'a) - 1` by (
    qpat_x_assum `FST (word_copy_plan copy_count copy_source_start copy_target_start
      copy_header_memory copy_alloc_state.mdomain) < dimword (:'a)`
      (mp_tac o MATCH_MP IMP_LESS_MustTerminate_limit)
    >> rpt (pop_assum kall_tac)
    >> decide_tac)
  >> qpat_x_assum `word_copy_plan _ _ _ _ _ = _`
       (assume_named_tac "copy_plan")
  >> qspecl_then [`copy_count`,`c`,`copy_source_start`,`copy_target_start`,
       `copy_call_state`,`copy_header_memory`,`copy_alloc_state.mdomain`,
       `copy_final_memory`,
       `FST (word_copy_plan copy_count copy_source_start copy_target_start
         copy_header_memory copy_alloc_state.mdomain)`,
       `make_cons_ptr c (copy_free - copy_current_heap) 0 copy_count`,`n`,`l`]
       mp_tac WordCopy_thm
  >> impl_tac
  >- (
    conj_tac >- LABEL_ASSUM "copy_plan" ACCEPT_TAC
    >> simp [Abbr `copy_call_state`,Abbr `copy_header_memory`,Abbr `copy_source_start`,
             wordSemTheory.get_var_def,lookup_insert]
    >> qpat_x_assum `FST (word_copy_plan _ _ _ _ _) ≤ MustTerminate_limit (:'a) - 1` mp_tac
    >> qpat_x_assum `copy_header = make_header c 0 copy_count` mp_tac
    >> rpt (pop_assum kall_tac)
    >> simp [WORD_MULT_COMM])
  >> disch_then (qx_choose_then `copy_maximum` strip_assume_tac)
  >> qpat_x_assum `LENGTH copy_words = copy_count`
       (assume_named_tac "copy_words_length")
  >> namedCases_on `env_to_list copy_saved_locals copy_alloc_state.permute`
       ["copy_saved_values copy_next_permute"]
  >> `wf copy_saved_return ∧ wf copy_saved_locals` by (
    qpat_x_assum `cut_envs (adjust_sets copy_kept_names) copy_alloc_state.locals =
      SOME (copy_saved_return,copy_saved_locals)` mp_tac
    >> rpt (pop_assum kall_tac)
    >> gvs [wordSemTheory.cut_envs_def,wordSemTheory.cut_names_def,AllCaseEqs(),wf_inter]
    >> strip_tac >> gvs [])
  >> drule env_to_list_lookup_equiv >> strip_tac
  >> `fromAList copy_saved_values = copy_saved_locals` by (
    simp [spt_eq_thm,wf_fromAList,lookup_fromAList])
  >> simp [Abbr `copy_call_state`,wordSemTheory.pop_env_def,wordSemTheory.push_env_def,
        wordSemTheory.set_vars_def,alist_insert_def,fromAList_toAList,domain_union,
        AC UNION_COMM UNION_ASSOC]
  >> `x.stack = s.stack ∧ x.stack_max = s.stack_max ∧
      x.locals_size = s.locals_size ∧ x.stack_frame_sizes = s.stack_frame_sizes ∧
      x.tstamps = s.tstamps ∧ x.global = s.global ∧ x.clock = s.clock` by (
    qpat_x_assum `cut_state_opt (SOME copy_kept_names) s = SOME x`
      (mp_tac o MATCH_MP cut_state_opt_SOME_eq)
    >> rpt (pop_assum kall_tac)
    >> strip_tac >> gvs [])
  >> LABEL_ASSUM "copy_after_alloc_cut"
       (strip_assume_tac o SIMP_RULE (srw_ss()) [state_rel_thm])
  >> simp [state_rel_thm,dataSemTheory.set_var_def,lookup_insert,adjust_var_11]
  >> qpat_assum `copy_alloc_state.code = copy_alloc_start.code`
       (RULE_ASSUM_TAC o REWRITE_RULE o single)
  >> qpat_assum `copy_alloc_state.compile_oracle = copy_alloc_start.compile_oracle`
       (RULE_ASSUM_TAC o REWRITE_RULE o single)
  >> qpat_assum `copy_alloc_state.code_buffer = copy_alloc_start.code_buffer`
       (RULE_ASSUM_TAC o REWRITE_RULE o single)
  >> qpat_assum `copy_alloc_state.data_buffer = copy_alloc_start.data_buffer`
       (RULE_ASSUM_TAC o REWRITE_RULE o single)
  >> qpat_assum `copy_after_alloc_locals = union copy_saved_locals copy_saved_return`
       (RULE_ASSUM_TAC o REWRITE_RULE o single)
  >> simp [FLOOKUP_UPDATE]
  >> conj_tac
  >- (
    qx_gen_tac `copy_local`
    >> Cases_on `copy_local = dest` >> simp [])
  >> conj_tac
  >- (
    qpat_assum `evaluate (WordCopy_code c,_) = _`
      (mp_tac o MATCH_MP evaluate_stack_max_le)
    >> simp [option_le_max,stack_size_eq,option_add_comm]
    >> strip_tac
    >> qpat_x_assum `option_le (push_env _ _ _).stack_max copy_maximum` mp_tac
    >> simp [wordSemTheory.push_env_def,option_le_max]
    >> strip_tac
    >> irule option_le_trans
    >> qexists_tac `copy_alloc_state.stack_max`
    >> simp []
    >> qpat_x_assum `option_le (OPTION_MAP2 $+ (stack_size copy_alloc_state.stack) _)
         copy_alloc_state.stack_max` mp_tac
    >> simp [option_add_comm])
  >> conj_tac
  >- (
    qpat_x_assum `option_le copy_maximum _` mp_tac
    >> simp [wordSemTheory.push_env_def,stack_size_eq,option_add_comm]
    >> strip_tac
    >> `stack_size copy_alloc_state.stack = size_of_stack s.stack` by (
      irule stack_rel_IMP_size_of_stack
      >> qpat_assum `LIST_REL stack_rel s.stack copy_alloc_state.stack` ACCEPT_TAC)
    >> qmatch_asmsub_abbrev_tac `option_le copy_maximum copy_stack_bound`
    >> irule option_le_trans
    >> qexists_tac `copy_stack_bound`
    >> conj_tac >- simp []
    >> simp [Abbr `copy_stack_bound`,option_map2_max_add,option_le_max,
             option_le_max_right,option_le_add,option_add_comm]
    >> disj2_tac >> disj1_tac
    >> irule (ONCE_REWRITE_RULE [option_add_comm] option_le_add))
  >> `s.tstamps = SOME copy_new_timestamp` by (
    qpat_x_assum `x.tstamps = SOME copy_new_timestamp` mp_tac
    >> simp [])
  >> `copy_free + bytes_in_word * n2w (copy_count + 1) =
        copy_target_start + bytes_in_word * n2w copy_count` by (
    qunabbrev_tac `copy_target_start`
    >> rpt (pop_assum kall_tac)
    >> once_rewrite_tac [GSYM word_add_n2w]
    >> rewrite_tac [WORD_LEFT_ADD_DISTRIB,WORD_MULT_CLAUSES]
    >> simp_tac std_ss [AC WORD_ADD_ASSOC WORD_ADD_COMM])
  >> `memory_rel c copy_alloc_state.be (copy_new_timestamp + 1) s.refs 0
        (copy_alloc_state.store |+ (NextFree,
          Word (copy_target_start + bytes_in_word * n2w copy_count)))
        copy_final_memory copy_alloc_state.mdomain
        ((Block copy_new_timestamp 0
            (TAKE copy_count (DROP copy_source_index copy_source_values)),
          make_cons_ptr c (copy_free - copy_current_heap) 0 copy_count)::
         (copy_source,
          Word copy_alloc_source_pointer)::copy_alloc_frame)` by (
    qpat_x_assum `memory_rel _ _ _ _ _ _ copy_final_memory _ ((Block _ _ _,_)::_)` mp_tac
    >> LABEL_ASSUM "copy_words_length" mp_tac
    >> LABEL_ASSUM "copy_values_slice" mp_tac
    >> qpat_x_assum `s.tstamps = SOME copy_new_timestamp` mp_tac
    >> qpat_x_assum `copy_free + bytes_in_word * n2w (copy_count + 1) = _` mp_tac
    >> rpt (pop_assum kall_tac)
    >> simp [])
  >> qpat_x_assum `memory_rel _ _ _ _ 0 _ copy_final_memory _ ((Block _ _ _,_)::_)`
       (assume_named_tac "copy_result_heap")
  >> `∀copy_index copy_value.
        lookup copy_index x.locals = SOME copy_value ⇒
        lookup copy_index copy_alloc_locals = SOME copy_value` by (
    qpat_x_assum `dataSem$cut_env copy_kept_names copy_alloc_locals = SOME x.locals` mp_tac
    >> rpt (pop_assum kall_tac)
    >> simp [dataSemTheory.cut_env_def,AllCaseEqs()]
    >> strip_tac
    >> qpat_x_assum `inter copy_alloc_locals copy_kept_names = x.locals`
         (rewrite_tac o single o GSYM)
    >> rw [lookup_inter_alt,AllCaseEqs()] >> gvs [])
  >> pop_assum (assume_named_tac "copy_data_submap")
  >> `∀copy_index copy_value.
        lookup copy_index (union copy_saved_locals copy_saved_return) = SOME copy_value ⇒
        lookup copy_index copy_alloc_state.locals = SOME copy_value` by (
    qpat_x_assum `cut_env (adjust_sets copy_kept_names) copy_alloc_state.locals =
      SOME (union copy_saved_locals copy_saved_return)` mp_tac
    >> rpt (pop_assum kall_tac)
    >> strip_tac
    >> qx_genl_tac [`copy_index`,`copy_value`] >> strip_tac
    >> drule_all cut_env_IMP_lookup >> simp [])
  >> pop_assum (assume_named_tac "copy_word_submap")
  >> simp [FAPPLY_FUPDATE_THM]
  >> asm_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
  >> irule memory_rel_insert
  >> rewrite_tac [APPEND]
  >> LABEL_ASSUM "copy_result_heap" mp_tac
  >> match_mp_tac memory_rel_rearrange
  >> LABEL_ASSUM "copy_data_submap" mp_tac
  >> LABEL_ASSUM "copy_word_submap" mp_tac
  >> qunabbrev_tac `copy_alloc_frame`
  >> rpt (pop_assum kall_tac)
  >> rpt strip_tac
  >> rw [MEM_APPEND] >> gvs []
  >> disj2_tac >> disj2_tac >> disj1_tac
  >> drule_all join_env_submap_MEM >> simp []
QED

Theorem assign_CopyByte:
  (∃new_flag. op = MemOp (CopyByte new_flag) /\ ¬ new_flag) ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ drule0 (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ ‘names_opt ≠ NONE’ by
       (qpat_x_assum ‘op_requires_names _ ⇎ _’ mp_tac \\ simp [dataLangTheory.op_requires_names_def])
  \\ gvs [GSYM IS_SOME_EQ_NOT_NONE,IS_SOME_EXISTS]
  \\ rename [‘cut_state_opt (SOME kept_names) s’]
  \\ drule_all state_rel_cut_state_opt_SOME \\ strip_tac
  \\ qpat_x_assum ‘_ (t with locals := y) NONE locs’ $ ASSUME_NAMED_TAC "with_locals"
  \\ qpat_x_assum `_  s t NONE locs`$ ASSUME_NAMED_TAC "old"
  \\ fs[do_app,dataSemTheory.allowed_op_def] \\ clean_tac
  \\ imp_res_tac get_vars_IMP_LENGTH
  \\ gvs [AllCaseEqs()]
  \\ gvs [LENGTH_EQ_NUM_compute,LENGTH_EQ_5]
  \\ qmatch_asmsub_rename_tac
       ‘get_vars [e1; e2; e3; e4; e5] s.locals =
          SOME [RefPtr src_b src; Number srcoff; Number le;
                RefPtr dst_b dst; Number dstoff]’
  \\ qmatch_asmsub_rename_tac ‘lookup src x.refs = SOME (ByteArray xs_fl xs)’
  \\ qmatch_asmsub_rename_tac ‘lookup dst x.refs = SOME (ByteArray ys_fl ys)’
  \\ qmatch_asmsub_rename_tac ‘copy_array (xs,srcoff) le (SOME (ys,dstoff)) = SOME ys1’
  \\ ‘x.refs = s.refs’ by
       (qpat_x_assum ‘cut_state_opt _ _ = SOME x’ mp_tac
        \\ simp [dataSemTheory.cut_state_opt_def, dataSemTheory.cut_state_def, AllCaseEqs()]
        \\ rw [] \\ simp [])
  \\ fs []
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ LABEL_ASSUM "old" (assume_tac o REWRITE_RULE [state_rel_thm])
  \\ full_simp_tac std_ss [APPEND, GSYM APPEND_ASSOC]
  \\ rpt_drule0 memory_rel_get_vars_IMP \\ strip_tac
  \\ ‘good_dimindex (:'a) ∧ shift_length c < dimindex (:α)’ by fs [state_rel_thm]
  (* offset bounds *)
  \\ `?xp yp len_n.
        srcoff = &xp /\ xp < dimword (:'a) DIV 8 /\
        dstoff = &yp /\ yp < dimword (:'a) DIV 8 /\
        le = &len_n /\ len_n < dimword (:'a) DIV 8` by
   (fs [semanticPrimitivesTheory.copy_array_def,not_less_zero_int_eq]
    \\ rveq \\ fs [NOT_LESS,integerTheory.INT_ADD,integerTheory.INT_ABS_NUM]
    \\ rpt_drule0 memory_rel_ByteArray_IMP
    \\ ntac 3 (drule0 memory_rel_tl \\ pop_assum kall_tac \\ strip_tac)
    \\ rpt_drule0 memory_rel_ByteArray_IMP
    \\ fs [good_dimindex_def,dimword_def]
    \\ rpt strip_tac \\ fs [])
  \\ rveq \\ fs []
  \\ `∃w. a3 = Word w ∧ w ⋙ 1 = n2w len_n` by
        (rpt_drule0 memory_rel_get_num \\ metis_tac [])
  \\ rveq \\ fs [] \\ ntac 2 (pop_assum mp_tac)
  \\ `∃w. a5 = Word w ∧ w ⋙ 1 = n2w yp` by
        (rpt_drule0 memory_rel_get_num \\ metis_tac [])
  \\ rveq \\ fs [] \\ ntac 2 (pop_assum mp_tac)
  \\ `∃w. a2 = Word w ∧ w ⋙ 1 = n2w xp` by
        (rpt_drule0 memory_rel_get_num \\ metis_tac [])
  \\ rveq \\ fs [] \\ rpt strip_tac
  (* simulation of generated code: outer Call to ByteCopy_location *)
  \\ simp [assign_def,assign_CopyByte_def]
  \\ ‘(?md. lookup ByteCopy_location t.code = SOME (6,ByteCopy_code c,md))’ by
       fs [data_to_word_gcProofTheory.code_rel_def,
           stubs_md_def,stubs_def,MAP_MAP_o,o_DEF]
  \\ qmatch_asmsub_rename_tac
       ‘get_vars [adjust_var e1; adjust_var e2; adjust_var e3; adjust_var e4;
                  adjust_var e5] t = SOME [a1; Word sw; Word lw; a4; Word ow]’
  \\ ‘lookup (adjust_var e1) t.locals = SOME a1 ∧
      lookup (adjust_var e2) t.locals = SOME (Word sw) ∧
      lookup (adjust_var e3) t.locals = SOME (Word lw) ∧
      lookup (adjust_var e4) t.locals = SOME a4 ∧
      lookup (adjust_var e5) t.locals = SOME (Word ow)’ by
       (qpat_x_assum ‘get_vars _ t = _’ mp_tac
        \\ simp [wordSemTheory.get_vars_def, wordSemTheory.get_var_def, AllCaseEqs()])
  \\ drule cut_env_IMP_cut_envs \\ strip_tac \\ fs [get_names_def]
  \\ fs [wordSemTheory.evaluate_def, wordSemTheory.add_ret_loc_def,
         wordSemTheory.bad_dest_args_def, wordSemTheory.find_code_def,
         wordSemTheory.get_vars_def, wordSemTheory.get_var_def]
  \\ simp [domain_adjust_sets,cut_envs_adjust_sets_insert_ODD]
  \\ Cases_on ‘env_to_list y2 t.permute’
  \\ simp [wordSemTheory.push_env_def,wordSemTheory.call_env_def,fromList2_def,
           wordSemTheory.dec_clock_def]
  \\ fs [ByteCopy_code_def]
  \\ once_rewrite_tac [list_Seq_def] \\ eval_tac
  \\ simp [Once word_exp_ShiftVar_bits] \\ fs [eq_eval]
  \\ once_rewrite_tac [list_Seq_def] \\ eval_tac
  \\ simp [Once word_exp_ShiftVar_bits] \\ fs [eq_eval]
  \\ once_rewrite_tac [list_Seq_def] \\ eval_tac
  \\ simp [Once word_exp_ShiftVar_bits] \\ fs [eq_eval]
  \\ once_rewrite_tac [list_Seq_def] \\ fs [data_to_wordTheory.Unit_def] \\ eval_tac
  \\ `?wa1 addr1. a1 = Word wa1 /\ get_real_addr c t.store wa1 = SOME addr1`
          by (rpt_drule0 memory_rel_ByteArray_IMP \\ strip_tac \\ fs [])
  \\ `?wa2 addr2. a4 = Word wa2 /\ get_real_addr c t.store wa2 = SOME addr2`
          by (ntac 3 (drule0 memory_rel_tl \\ strip_tac)
              \\ rpt_drule0 memory_rel_ByteArray_IMP \\ strip_tac \\ fs [])
  \\ rveq \\ fs []
  \\ qmatch_goalsub_abbrev_tac `wordSem$evaluate (_,t7)`
  \\ `get_var 2 t7 = SOME (Word wa1)` by
      (unabbrev_all_tac \\ fs [wordSemTheory.get_var_def,lookup_insert])
  \\ once_rewrite_tac [list_Seq_def] \\ eval_tac
  \\ `t7.store = t.store` by (unabbrev_all_tac \\ fs [push_env_store])
  \\ full_simp_tac std_ss [GSYM wordSemTheory.get_var_def]
  \\ rpt_drule0 get_var_get_real_addr_lemma
  \\ disch_then kall_tac
  \\ qunabbrev_tac `t7` \\ fs [eq_eval]
  \\ qmatch_goalsub_abbrev_tac `wordSem$evaluate (_,t7)`
  \\ `get_var 8 t7 = SOME (Word wa2)` by
      (unabbrev_all_tac \\ fs [wordSemTheory.get_var_def,lookup_insert])
  \\ once_rewrite_tac [list_Seq_def] \\ eval_tac
  \\ `t7.store = t.store` by (unabbrev_all_tac \\ fs [push_env_store])
  \\ full_simp_tac std_ss [GSYM wordSemTheory.get_var_def]
  \\ rpt_drule0 get_var_get_real_addr_lemma
  \\ disch_then kall_tac
  \\ qunabbrev_tac `t7` \\ fs [eq_eval]
  \\ pop_assum kall_tac \\ clean_tac
  \\ qpat_x_assum `lookup ByteCopy_location t.code = _` kall_tac
  \\ once_rewrite_tac [list_Seq_def] \\ eval_tac \\ fs [eq_eval]
  \\ once_rewrite_tac [list_Seq_def] \\ eval_tac \\ fs [eq_eval]
  \\ once_rewrite_tac [list_Seq_def]
  \\ qmatch_goalsub_abbrev_tac `wordSem$evaluate (_,byte_copy_entry)`
  \\ qspecl_then [`byte_copy_entry`,`addr2 + bytes_in_word + n2w yp`,
       `addr1 + bytes_in_word + n2w xp`,`n2w len_n`,
       `Call NONE (SOME ByteCopyAlign_location) [0;6;2;8;1] NONE`,
       `If Lower 4 (Reg 10)
         (list_Seq [Assign 3 (Op Sub [Var 6;Const 1]);
                    Assign 2 (Op Add [Var 2;Var 3]);
                    Assign 8 (Op Add [Var 8;Var 3]);
                    Call NONE (SOME ByteCopySub_location) [0;6;2;8;1] NONE])
         (Call NONE (SOME ByteCopyAdd_location) [0;6;2;8;1] NONE)`] mp_tac
       evaluate_ByteCopyDispatch
  \\ impl_tac >- (
    simp [Abbr `byte_copy_entry`,wordSemTheory.get_var_def,lookup_insert])
  \\ disch_then SUBST1_TAC
  \\ Cases_on `(n2w len_n:'a word) <=+
       (addr2 + bytes_in_word + n2w yp) - (addr1 + bytes_in_word + n2w xp) /\
       (n2w len_n:'a word) <=+
       (addr1 + bytes_in_word + n2w xp) - (addr2 + bytes_in_word + n2w yp)`
  \\ asm_simp_tac std_ss []
  >- (
    qmatch_asmsub_rename_tac `cut_state_opt (SOME kept_names) s = SOME cut_source`
    \\ qmatch_asmsub_rename_tac `cut_envs (adjust_sets kept_names) t.locals = SOME (non_gc_env,gc_env)`
    \\ qmatch_asmsub_rename_tac `env_to_list gc_env t.permute = (saved_env,next_permute)`
    \\ qmatch_asmsub_rename_tac `insert 0 (Loc return_label1 return_label2) LN`
    \\ `xp + len_n <= LENGTH xs /\ yp + len_n <= LENGTH ys /\
     ys1 = TAKE yp ys ++ TAKE len_n (DROP xp xs) ++ DROP (yp + len_n) ys` by (
      gvs [semanticPrimitivesTheory.copy_array_def,integerTheory.INT_ADD,
           integerTheory.INT_ABS_NUM])
    \\ `len_n < dimword (:'a)` by (
      irule LESS_LESS_EQ_TRANS \\ qexists_tac `dimword (:'a) DIV 8`
      \\ conj_tac >- first_assum ACCEPT_TAC
      \\ simp [DIV_LESS_EQ])
    \\ `len_n <= w2n ((addr2 + bytes_in_word + n2w yp) -
                          (addr1 + bytes_in_word + n2w xp)) /\
         len_n <= w2n ((addr1 + bytes_in_word + n2w xp) -
                          (addr2 + bytes_in_word + n2w yp))` by (
      gvs [WORD_LS,w2n_n2w,LESS_MOD])
    \\ rpt_drule0 memory_rel_ByteArray_IMP
    \\ strip_tac
    \\ gvs []
    \\ `memory_rel c t.be (THE s.tstamps) s.refs s.space t.store t.memory t.mdomain
         ((RefPtr dst_b dst,Word wa2)::
           (join_env s.locals (toAList (inter t.locals (adjust_set s.locals))) ++
            [(the_global s.global,t.store ' Globals)] ++ flat s.stack t.stack))` by (
      qpat_assum `memory_rel _ _ _ _ _ _ _ _ (_::(Number (&xp),Word sw)::_)` mp_tac
      \\ match_mp_tac memory_rel_rearrange
      \\ fs [] \\ rw [] \\ fs [])
    \\ qpat_x_assum `memory_rel _ _ _ _ _ _ _ _ (_::(Number (&xp),Word sw)::_ )` kall_tac
    \\ qpat_x_assum `!i w. i < LENGTH xs ==> memory_rel _ _ _ _ _ _ _ _ _` kall_tac
    \\ qpat_x_assum `if dimindex (:'a) = 32 then _ else _` kall_tac
    \\ rpt_drule0 memory_rel_ByteArray_IMP
    \\ strip_tac
    \\ gvs []
    \\ qpat_x_assum `!i w. i < LENGTH ys ==> memory_rel _ _ _ _ _ _ _ _ _` kall_tac
    \\ qpat_x_assum `if dimindex (:'a) = 32 then _ else _` kall_tac
    \\ qspecl_then [`len_n`,`addr2 + bytes_in_word + n2w yp`,
         `addr1 + bytes_in_word + n2w xp`,`t.memory`,`t.mdomain`,`t.be`] mp_tac
         byte_copy_range_inv_from_loads
    \\ impl_tac >- (
      simp []
      \\ qx_gen_tac `i` \\ strip_tac
      \\ `xp + i < LENGTH xs /\ yp + i < LENGTH ys` by decide_tac
      \\ simp [addressTheory.word_arith_lemma1])
    \\ disch_tac
    \\ qabbrev_tac `copied_bytes = TAKE len_n (DROP xp xs)`
    \\ `len_n <= LENGTH xs - xp` by decide_tac
    \\ `LENGTH copied_bytes = len_n` by (
      simp [Abbr `copied_bytes`,LENGTH_TAKE_EQ])
    \\ qspecl_then [`t.be`,`THE s.tstamps`,`s.space`,`t.store`,`t.mdomain`,
         `dst_b`,`dst`,`wa2`,
         `join_env s.locals (toAList (inter t.locals (adjust_set s.locals))) ++
          [(the_global s.global,t.store ' Globals)] ++ flat s.stack t.stack`,
         `ys_fl`,`addr2`,`copied_bytes`,`s.refs`,`yp`,`ys`,`t.memory`,
         `addr1 + bytes_in_word + n2w xp`] mp_tac
         byte_copy_seq_memory_rel
    \\ impl_tac >- (
      simp []
      \\ qx_gen_tac `i` \\ strip_tac
      \\ `xp + i < LENGTH xs` by decide_tac
      \\ simp [Abbr `copied_bytes`,EL_TAKE,EL_DROP,addressTheory.word_arith_lemma1])
    \\ simp []
    \\ disch_then (qx_choose_then `final_memory` strip_assume_tac)
    \\ `word_copy_fwd t.be (n2w len_n) (addr1 + bytes_in_word + n2w xp)
         (addr2 + bytes_in_word + n2w yp) t.memory t.mdomain = SOME final_memory` by (
      qspecl_then [`len_n`,`t.be`,`addr1 + bytes_in_word + n2w xp`,
           `addr2 + bytes_in_word + n2w yp`,`t.memory`,`t.mdomain`] mp_tac
           word_copy_fwd_byte_copy_seq
      \\ impl_tac >- (rpt conj_tac \\ first_assum ACCEPT_TAC)
      \\ simp [])
    \\ qspecl_then [`dimindex (:'a) DIV 8`,`len_n`,
         `addr1 + bytes_in_word + n2w xp`,`addr2 + bytes_in_word + n2w yp`,
         `t.memory`,`t.mdomain`] mp_tac
         byte_copy_align_initial
    \\ impl_tac >- simp []
    \\ disch_then (qx_choose_then `prefix_bytes` strip_assume_tac)
    \\ `c.be = t.be` by (imp_res_tac memory_rel_be \\ fs [])
    \\ `(?md. lookup ByteCopyAlign_location t.code = SOME (5,ByteCopyAlign_code c,md)) /\
         (?md. lookup ByteCopyLoop_location t.code = SOME (8,ByteCopyLoop_code c,md)) /\
         (?md. lookup ByteCopyAdd_location t.code = SOME (5,ByteCopyAdd_code,md))` by (
      fs [data_to_word_gcProofTheory.code_rel_def,stubs_md_def,stubs_def,MAP_MAP_o,o_DEF])
    \\ `4 <= dimword (:'a)` by fs [good_dimindex_def,dimword_def]
    \\ `len_n + 3 <= byte_copy_entry.clock` by (
      simp [Abbr `byte_copy_entry`,wordSemTheory.MustTerminate_limit_def]
      \\ decide_tac)
    \\ `cut_source.stack = s.stack /\ cut_source.stack_max = s.stack_max /\
         cut_source.locals_size = s.locals_size /\
         cut_source.stack_frame_sizes = s.stack_frame_sizes` by (
      qpat_x_assum `cut_state_opt _ _ = SOME cut_source` mp_tac
      \\ simp [dataSemTheory.cut_state_opt_def,dataSemTheory.cut_state_def,AllCaseEqs()]
      \\ rw [] \\ simp [])
    \\ `stack_size t.stack = size_of_stack s.stack` by (
      irule stack_rel_IMP_size_of_stack \\ first_assum (irule_at Any))
    \\ qabbrev_tac `copy_bound = OPTION_MAP2 MAX cut_source.stack_max
         (OPTION_MAP2 $+
           (OPTION_MAP2 MAX (lookup ByteCopy_location cut_source.stack_frame_sizes)
             (OPTION_MAP2 MAX (lookup ByteCopyAlign_location cut_source.stack_frame_sizes)
               (OPTION_MAP2 MAX (lookup ByteCopyLoop_location cut_source.stack_frame_sizes)
                 (OPTION_MAP2 MAX (lookup ByteCopyAdd_location cut_source.stack_frame_sizes)
                   (lookup ByteCopySub_location cut_source.stack_frame_sizes)))))
           (OPTION_MAP2 $+ (size_of_stack cut_source.stack) cut_source.locals_size))`
    \\ `option_le byte_copy_entry.stack_max copy_bound /\
         option_le (OPTION_MAP2 $+ (stack_size byte_copy_entry.stack)
           (lookup ByteCopyAlign_location byte_copy_entry.stack_size)) copy_bound /\
         option_le (OPTION_MAP2 $+ (stack_size byte_copy_entry.stack)
           (lookup ByteCopyLoop_location byte_copy_entry.stack_size)) copy_bound /\
         option_le (OPTION_MAP2 $+ (stack_size byte_copy_entry.stack)
           (lookup ByteCopyAdd_location byte_copy_entry.stack_size)) copy_bound` by (
      simp [Abbr `byte_copy_entry`,Abbr `copy_bound`,stack_size_eq]
      \\ PURE_REWRITE_TAC [option_le_max]
      \\ simp [option_map2_max_add,option_le_max_right,option_add_comm,option_le_add,
               ONCE_REWRITE_RULE [option_add_comm] option_le_add])
    \\ qspecl_then [`len_n`,`[0;6;2;8;1]`,`c`,`dimindex (:'a) DIV 8`,`prefix_bytes`,
         `addr1 + bytes_in_word + n2w xp`,`addr2 + bytes_in_word + n2w yp`,
         `Word 0w`,`return_label1`,`return_label2`,`byte_copy_entry`,`t.memory`,
         `final_memory`,`copy_bound`] mp_tac CopyByteAlign_call
    \\ impl_tac >- (
      gvs [Abbr `byte_copy_entry`,wordSemTheory.get_vars_def,
           wordSemTheory.get_var_def,lookup_insert])
    \\ disch_then (qx_choosel_then [`remaining_clock`,`used_stack`] strip_assume_tac)
    \\ `domain (fromAList saved_env) = domain gc_env` by (
      imp_res_tac env_to_list_domain \\ asm_simp_tac std_ss [])
    \\ simp []
    \\ simp [Abbr `byte_copy_entry`,wordSemTheory.pop_env_def,
             wordSemTheory.set_vars_def,alist_insert_def,domain_union,
             domain_fromAList_toAList,AC UNION_COMM UNION_ASSOC]
    \\ `option_le t.stack_max used_stack` by (
      qpat_assum `wordSem$evaluate _ = _` (mp_tac o MATCH_MP evaluate_stack_max_le)
      \\ simp [option_le_max])
    \\ `cut_source.tstamps = s.tstamps /\ cut_source.space = s.space /\
         cut_source.global = s.global` by (
      qpat_x_assum `cut_state_opt _ _ = SOME cut_source` mp_tac
      \\ simp [dataSemTheory.cut_state_opt_def,dataSemTheory.cut_state_def,AllCaseEqs()]
      \\ rw [] \\ simp [])
    \\ fs [state_rel_thm,lookup_insert,lookup_fromAList,adjust_var_11]
    \\ drule0 env_to_list_lookup_equiv \\ fs [] \\ strip_tac
    \\ conj_tac >- (
      drule_all cut_envs_lookup_0
      \\ simp [lookup_union,lookup_fromAList,ALOOKUP_toAList])
    \\ conj_tac >- (
      qx_gen_tac `local_name`
      \\ Cases_on `local_name = dest` \\ simp []
      \\ LABEL_ASSUM "with_locals" (strip_assume_tac o REWRITE_RULE [state_rel_thm])
      \\ fs [lookup_union,lookup_fromAList,ALOOKUP_toAList])
    \\ conj_tac >- (
      irule option_le_trans \\ qexists_tac `t.stack_max`
      \\ conj_tac \\ first_assum ACCEPT_TAC)
    \\ rewrite_tac [GSYM APPEND_ASSOC]
    \\ irule memory_rel_insert \\ rewrite_tac [APPEND]
    \\ irule memory_rel_Unit \\ asm_rewrite_tac []
    \\ qpat_assum `memory_rel _ _ _ _ _ _ final_memory _ ((RefPtr dst_b dst,Word wa2)::_)`
         (mp_tac o REWRITE_RULE [GSYM APPEND_ASSOC])
    \\ match_mp_tac memory_rel_rearrange
    \\ `dataSem$cut_env kept_names s.locals = SOME cut_source.locals` by (
      qpat_x_assum `cut_state_opt _ _ = SOME cut_source` mp_tac
      \\ simp [dataSemTheory.cut_state_opt_def,dataSemTheory.cut_state_def,AllCaseEqs()]
      \\ rw [] \\ simp [])
    \\ simp [SF DNF_ss]
    \\ fs [join_env_def,inter_union_distrib]
    \\ drule_all cut_envs_inter \\ strip_tac \\ simp []
    \\ `cut_source.locals = inter s.locals kept_names` by (
      imp_res_tac cut_state_opt_SOME_eq
      \\ asm_rewrite_tac [] \\ simp [mk_wf_inter])
    \\ `gc_env = inter t.locals (adjust_set kept_names)` by (
      qpat_x_assum `cut_envs _ _ = SOME (non_gc_env,gc_env)` mp_tac
      \\ simp [wordSemTheory.cut_envs_def,wordSemTheory.cut_names_def,
               adjust_sets_def,AllCaseEqs()]
      \\ rw [] \\ simp [])
    \\ `inter (fromAList saved_env) (adjust_set cut_source.locals) =
         inter t.locals (adjust_set cut_source.locals)` by (
      simp [spt_eq_thm,lookup_inter_alt,lookup_fromAList,adjust_set_inter,domain_inter])
    \\ qpat_x_assum `inter (fromAList saved_env) _ = _` (PURE_ONCE_REWRITE_TAC o single)
    \\ qpat_assum `cut_source.locals = inter s.locals kept_names` (PURE_REWRITE_TAC o single)
    \\ rpt strip_tac \\ disj2_tac \\ disj1_tac
    \\ gvs [MEM_MAP,MEM_FILTER,EXISTS_PROD,MEM_toAList,lookup_inter,AllCaseEqs()]
    \\ qmatch_asmsub_rename_tac
         `lookup register_name (adjust_set (inter s.locals kept_names)) = SOME ()`
    \\ qexists_tac `register_name`
    \\ simp []
    \\ qpat_x_assum `lookup register_name (adjust_set (inter s.locals kept_names)) = SOME ()`
         mp_tac
    \\ rpt (pop_assum kall_tac)
    \\ simp [lookup_adjust_set,domain_inter,domain_lookup,AllCaseEqs()]
    \\ rpt strip_tac
    \\ gvs [lookup_inter,lookup_adjust_set,domain_lookup,AllCaseEqs()])
  \\ qpat_x_assum `~((n2w len_n:'a word) <=+ _ /\ (n2w len_n:'a word) <=+ _)` kall_tac
  \\ qunabbrev_tac `byte_copy_entry`
  \\ Cases_on ‘src = dst’ \\ rveq
  >-
   (‘wa2 = wa1’ by
     (drule0 memory_rel_swap \\ strip_tac
      \\ drule0 memory_rel_tl \\ strip_tac
      \\ drule0 memory_rel_swap \\ strip_tac
      \\ drule0 memory_rel_tl \\ strip_tac
      \\ drule memory_rel_RefPtr_EQ_IMP \\ gvs [])
    \\ fs [] \\ rveq
    \\ ‘memory_rel c t.be (THE s.tstamps) s.refs s.space t.store t.memory t.mdomain
         ((RefPtr dst_b dst,Word wa1)::
            (join_env s.locals (toAList (inter t.locals (adjust_set s.locals))) ++
             [(the_global s.global,t.store ' Globals)] ++ flat s.stack t.stack))’ by
     (first_x_assum (fn th => mp_tac th THEN match_mp_tac memory_rel_rearrange)
      \\ fs [] \\ rw [] \\ fs [])
    \\ rpt_drule0 word_copy_array_alias_thm \\ strip_tac
    \\ qpat_x_assum ‘_ = SOME m1’ mp_tac
    \\ fs [word_copy_array_def,GSYM WORD_NOT_LOWER]
    \\ IF_CASES_TAC \\ fs [] \\ strip_tac
    >- (
  once_rewrite_tac [wordSemTheory.evaluate_def]
  \\ simp [wordSemTheory.get_var_def,wordSemTheory.get_var_imm_def,
           lookup_insert,asmTheory.word_cmp_def]
  \\ ‘(?md. lookup ByteCopyAdd_location t.code = SOME (5,ByteCopyAdd_code,md))’ by
       fs [data_to_word_gcProofTheory.code_rel_def,
           stubs_md_def,stubs_def,MAP_MAP_o,o_DEF]
  \\ fs [wordSemTheory.bad_dest_args_def,wordSemTheory.find_code_def,
         eq_eval,push_env_code]
  \\ assume_tac CopyByteAdd_thm \\ SEP_I_TAC "evaluate"
  \\ pop_assum drule0 \\ fs [eq_eval]
  \\ impl_tac
  >- (‘2 ≤ dimword (:'a)’ by (fs [good_dimindex_def] \\ fs [dimword_def])
      \\ match_mp_tac LESS_EQ_TRANS \\ qexists_tac ‘dimword (:'a)’ \\ conj_tac
      >- (irule LESS_EQ_TRANS \\ qexists_tac ‘len_n MOD dimword (:'a)’
          \\ conj_tac
          >- simp [DIV_LESS_EQ]
          >- (irule LESS_IMP_LESS_OR_EQ \\ simp [MOD_LESS]))
      >- fs [wordSemTheory.MustTerminate_limit_def])
  \\ fs [] \\ disch_then kall_tac
  \\ fs [wordSemTheory.pop_env_def,wordSemTheory.push_env_def,
         wordSemTheory.set_vars_def,alist_insert_def]
  \\ fs [domain_union,domain_fromAList_toAList]
  \\ ‘domain (fromAList q) = domain y2’ by
    (imp_res_tac env_to_list_domain \\ asm_simp_tac std_ss [])
  \\ asm_simp_tac std_ss [AC UNION_COMM UNION_ASSOC]
  \\ fs [state_rel_thm,lookup_insert,lookup_fromAList,adjust_var_11]
  \\ drule0 env_to_list_lookup_equiv \\ fs [] \\ strip_tac
  \\ ‘x.stack = s.stack ∧ x.stack_max = s.stack_max ∧ x.locals_size = s.locals_size ∧
      x.stack_frame_sizes = s.stack_frame_sizes’ by
       (qpat_x_assum ‘cut_state_opt _ _ = SOME x’ mp_tac
        \\ simp [dataSemTheory.cut_state_opt_def, dataSemTheory.cut_state_def, AllCaseEqs()]
        \\ rw [] \\ simp [])
  \\ ‘stack_size t.stack = size_of_stack s.stack’ by
       (irule stack_rel_IMP_size_of_stack \\ first_assum (irule_at Any))
  \\ conj_tac >-
   (drule_all cut_envs_lookup_0 \\ simp [lookup_union,lookup_fromAList,ALOOKUP_toAList])
  \\ conj_tac >-
   (gen_tac \\ IF_CASES_TAC \\ asm_simp_tac std_ss [adjust_var_11]
    \\ ‘dataSem$cut_env kept_names s.locals = SOME x.locals’ by
         (qpat_x_assum ‘cut_state_opt _ _ = SOME x’ mp_tac
          \\ simp [dataSemTheory.cut_state_opt_def, dataSemTheory.cut_state_def, AllCaseEqs()]
          \\ rw [] \\ simp [])
    \\ full_simp_tac std_ss [IS_SOME_lookup,domain_union] \\ strip_tac
    \\ drule_all IN_adjust_var_lemma \\ simp [])
  \\ conj_tac >-
   (rewrite_tac [stack_size_eq, option_le_max_right]
    \\ disj1_tac \\ disj1_tac \\ disj2_tac
    \\ metis_tac [option_add_comm,option_le_refl])
  \\ conj_tac >-
   (rewrite_tac [stack_size_eq]
    \\ qpat_x_assum ‘x.stack = s.stack’ (rewrite_tac o single)
    \\ qpat_x_assum ‘stack_size t.stack = size_of_stack s.stack’ (rewrite_tac o single)
    \\ rewrite_tac [option_le_max] \\ rpt conj_tac
    >- (rewrite_tac [option_le_max_right] \\ disj1_tac
        \\ qpat_x_assum ‘x.stack_max = s.stack_max’ (rewrite_tac o single)
        \\ first_assum ACCEPT_TAC)
    >- (rewrite_tac [option_le_max_right] \\ disj2_tac
        \\ metis_tac [option_add_comm,option_le_add])
    >- (rewrite_tac [option_le_max_right] \\ disj2_tac
        \\ metis_tac [option_add_comm,option_add_assoc,option_le_eq_eqns,
                      option_le_max_right,option_le_refl])
    >- (rewrite_tac [option_le_max_right] \\ disj2_tac
        \\ metis_tac [option_add_comm,option_add_assoc,option_le_eq_eqns,
                      option_le_max_right,option_le_refl]))
  \\ ‘x.tstamps = s.tstamps ∧ x.space = s.space ∧ x.global = s.global’ by
       (qpat_x_assum ‘cut_state_opt _ _ = SOME x’ mp_tac
        \\ simp [dataSemTheory.cut_state_opt_def, dataSemTheory.cut_state_def, AllCaseEqs()]
        \\ rw [] \\ simp [])
  \\ asm_simp_tac std_ss []
  \\ once_rewrite_tac [insert_insert]
  \\ rewrite_tac [GSYM APPEND_ASSOC,APPEND]
  \\ irule memory_rel_insert \\ rewrite_tac [APPEND]
  \\ irule memory_rel_Unit \\ asm_rewrite_tac []
  \\ qpat_x_assum ‘_ t.mdomain _’ mp_tac
  \\ match_mp_tac memory_rel_rearrange
  \\ ‘cut_env kept_names s.locals = SOME x.locals’ by
       (qpat_x_assum ‘cut_state_opt _ _ = SOME x’ mp_tac
        \\ simp [dataSemTheory.cut_state_opt_def, dataSemTheory.cut_state_def, AllCaseEqs()]
        \\ rw [] \\ simp [])
  \\ simp [SF DNF_ss]
  \\ fs [join_env_def,inter_union_distrib]
  \\ drule_all cut_envs_inter \\ strip_tac \\ simp []
  \\ qsuff_tac ‘inter (fromAList q) (adjust_set x.locals) = inter t.locals (adjust_set x.locals)’
  >-
   (disch_then SUBST1_TAC
    \\ ‘x.locals = mk_wf (inter s.locals kept_names)’ by
         (imp_res_tac cut_state_opt_SOME_eq \\ asm_rewrite_tac [] \\ simp [])
    \\ rpt strip_tac \\ disj2_tac \\ disj1_tac \\ disj1_tac
    \\ gvs [MEM_MAP, MEM_FILTER, EXISTS_PROD, MEM_toAList, lookup_inter, AllCaseEqs()]
    \\ qexists_tac ‘p_1’
    \\ qpat_x_assum ‘lookup p_1 (adjust_set (inter s.locals kept_names)) = SOME ()’ mp_tac
    \\ simp [lookup_adjust_set, domain_inter, AllCaseEqs(), domain_lookup]
    \\ rw []
    \\ qpat_x_assum ‘lookup _ (inter s.locals kept_names) = SOME _’ mp_tac
    \\ simp [lookup_inter, AllCaseEqs()] \\ rw [] \\ simp [])
  \\ fs [spt_eq_thm,lookup_inter_alt]
  \\ rw [] \\ fs []
  \\ drule env_to_list_lookup_equiv
  \\ fs [lookup_insert,lookup_fromAList,adjust_var_11]
  \\ rpt strip_tac \\ fs []
  \\ fs [wordSemTheory.cut_envs_def,wordSemTheory.cut_env_def] \\ rveq
  \\ gvs [wordSemTheory.cut_names_def,AllCaseEqs()]
  \\ fs [lookup_inter_alt] \\ rw []
  \\ fs [IN_domain_adjust_set_inter]
  \\ gvs [adjust_sets_def]
  \\ qpat_x_assum ‘_ ∈ domain (adjust_set x.locals)’ mp_tac
  \\ qpat_x_assum ‘_ ∉ domain (adjust_set kept_names)’ mp_tac
  \\ ‘domain x.locals = domain s.locals ∩ domain kept_names’ by
       (imp_res_tac cut_state_opt_SOME_eq \\ asm_rewrite_tac []
        \\ simp [domain_mk_wf, domain_inter])
  \\ simp [domain_lookup, lookup_adjust_set, AllCaseEqs()]
  \\ rw [] \\ gvs [domain_lookup]
  \\ qpat_x_assum ‘lookup _ x.locals = SOME _’ mp_tac
  \\ qpat_x_assum ‘domain x.locals = _’ mp_tac
  \\ qpat_x_assum ‘lookup _ kept_names ≠ _’ mp_tac
  \\ rpt (pop_assum kall_tac)
  \\ simp [domain_lookup, EXTENSION, IN_INTER]
  \\ metis_tac [oneTheory.one])
    >- (
  once_rewrite_tac [wordSemTheory.evaluate_def]
  \\ simp [wordSemTheory.get_var_def,wordSemTheory.get_var_imm_def,
           lookup_insert,asmTheory.word_cmp_def]
  \\ rewrite_tac [list_Seq_def]
  \\ simp [eq_eval]
  \\ ‘(?md. lookup ByteCopySub_location t.code = SOME (5,ByteCopySub_code,md))’ by
       fs [data_to_word_gcProofTheory.code_rel_def,
           stubs_md_def,stubs_def,MAP_MAP_o,o_DEF]
  \\ fs [wordSemTheory.bad_dest_args_def,wordSemTheory.find_code_def,
         eq_eval,push_env_code]
  \\ assume_tac CopyByteSub_thm \\ SEP_I_TAC "evaluate"
  \\ pop_assum drule0 \\ fs [eq_eval]
  \\ impl_tac
  >- (‘2 ≤ dimword (:'a)’ by (fs [good_dimindex_def] \\ fs [dimword_def])
      \\ match_mp_tac LESS_EQ_TRANS \\ qexists_tac ‘dimword (:'a)’ \\ conj_tac
      >- (irule LESS_EQ_TRANS \\ qexists_tac ‘len_n MOD dimword (:'a)’
          \\ conj_tac
          >- simp [DIV_LESS_EQ]
          >- (irule LESS_IMP_LESS_OR_EQ \\ simp [MOD_LESS]))
      >- fs [wordSemTheory.MustTerminate_limit_def])
  \\ fs [] \\ disch_then kall_tac
  \\ fs [wordSemTheory.pop_env_def,wordSemTheory.push_env_def,
         wordSemTheory.set_vars_def,alist_insert_def]
  \\ fs [domain_union,domain_fromAList_toAList]
  \\ ‘domain (fromAList q) = domain y2’ by
    (imp_res_tac env_to_list_domain \\ asm_simp_tac std_ss [])
  \\ asm_simp_tac std_ss [AC UNION_COMM UNION_ASSOC]
  \\ fs [state_rel_thm,lookup_insert,lookup_fromAList,adjust_var_11]
  \\ drule0 env_to_list_lookup_equiv \\ fs [] \\ strip_tac
  \\ ‘x.stack = s.stack ∧ x.stack_max = s.stack_max ∧ x.locals_size = s.locals_size ∧
      x.stack_frame_sizes = s.stack_frame_sizes’ by
       (qpat_x_assum ‘cut_state_opt _ _ = SOME x’ mp_tac
        \\ simp [dataSemTheory.cut_state_opt_def, dataSemTheory.cut_state_def, AllCaseEqs()]
        \\ rw [] \\ simp [])
  \\ ‘stack_size t.stack = size_of_stack s.stack’ by
       (irule stack_rel_IMP_size_of_stack \\ first_assum (irule_at Any))
  \\ conj_tac >-
   (drule_all cut_envs_lookup_0 \\ simp [lookup_union,lookup_fromAList,ALOOKUP_toAList])
  \\ conj_tac >-
   (gen_tac \\ IF_CASES_TAC \\ asm_simp_tac std_ss [adjust_var_11]
    \\ ‘dataSem$cut_env kept_names s.locals = SOME x.locals’ by
         (qpat_x_assum ‘cut_state_opt _ _ = SOME x’ mp_tac
          \\ simp [dataSemTheory.cut_state_opt_def, dataSemTheory.cut_state_def, AllCaseEqs()]
          \\ rw [] \\ simp [])
    \\ full_simp_tac std_ss [IS_SOME_lookup,domain_union] \\ strip_tac
    \\ drule_all IN_adjust_var_lemma \\ simp [])
  \\ conj_tac >-
   (rewrite_tac [stack_size_eq, option_le_max_right]
    \\ disj1_tac \\ disj1_tac \\ disj2_tac
    \\ metis_tac [option_add_comm,option_le_refl])
  \\ conj_tac >-
   (rewrite_tac [stack_size_eq]
    \\ qpat_x_assum ‘x.stack = s.stack’ (rewrite_tac o single)
    \\ qpat_x_assum ‘stack_size t.stack = size_of_stack s.stack’ (rewrite_tac o single)
    \\ rewrite_tac [option_le_max] \\ rpt conj_tac
    >- (rewrite_tac [option_le_max_right] \\ disj1_tac
        \\ qpat_x_assum ‘x.stack_max = s.stack_max’ (rewrite_tac o single)
        \\ first_assum ACCEPT_TAC)
    >- (rewrite_tac [option_le_max_right] \\ disj2_tac
        \\ metis_tac [option_add_comm,option_le_add])
    >- (rewrite_tac [option_le_max_right] \\ disj2_tac
        \\ metis_tac [option_add_comm,option_add_assoc,option_le_eq_eqns,
                      option_le_max_right,option_le_refl])
    >- (rewrite_tac [option_le_max_right] \\ disj2_tac
        \\ metis_tac [option_add_comm,option_add_assoc,option_le_eq_eqns,
                      option_le_max_right,option_le_refl]))
  \\ ‘x.tstamps = s.tstamps ∧ x.space = s.space ∧ x.global = s.global’ by
       (qpat_x_assum ‘cut_state_opt _ _ = SOME x’ mp_tac
        \\ simp [dataSemTheory.cut_state_opt_def, dataSemTheory.cut_state_def, AllCaseEqs()]
        \\ rw [] \\ simp [])
  \\ asm_simp_tac std_ss []
  \\ once_rewrite_tac [insert_insert]
  \\ rewrite_tac [GSYM APPEND_ASSOC,APPEND]
  \\ irule memory_rel_insert \\ rewrite_tac [APPEND]
  \\ irule memory_rel_Unit \\ asm_rewrite_tac []
  \\ qpat_x_assum ‘_ t.mdomain _’ mp_tac
  \\ match_mp_tac memory_rel_rearrange
  \\ ‘cut_env kept_names s.locals = SOME x.locals’ by
       (qpat_x_assum ‘cut_state_opt _ _ = SOME x’ mp_tac
        \\ simp [dataSemTheory.cut_state_opt_def, dataSemTheory.cut_state_def, AllCaseEqs()]
        \\ rw [] \\ simp [])
  \\ simp [SF DNF_ss]
  \\ fs [join_env_def,inter_union_distrib]
  \\ drule_all cut_envs_inter \\ strip_tac \\ simp []
  \\ qsuff_tac ‘inter (fromAList q) (adjust_set x.locals) = inter t.locals (adjust_set x.locals)’
  >-
   (disch_then SUBST1_TAC
    \\ ‘x.locals = mk_wf (inter s.locals kept_names)’ by
         (imp_res_tac cut_state_opt_SOME_eq \\ asm_rewrite_tac [] \\ simp [])
    \\ rpt strip_tac \\ disj2_tac \\ disj1_tac \\ disj1_tac
    \\ gvs [MEM_MAP, MEM_FILTER, EXISTS_PROD, MEM_toAList, lookup_inter, AllCaseEqs()]
    \\ qexists_tac ‘p_1’
    \\ qpat_x_assum ‘lookup p_1 (adjust_set (inter s.locals kept_names)) = SOME ()’ mp_tac
    \\ simp [lookup_adjust_set, domain_inter, AllCaseEqs(), domain_lookup]
    \\ rw []
    \\ qpat_x_assum ‘lookup _ (inter s.locals kept_names) = SOME _’ mp_tac
    \\ simp [lookup_inter, AllCaseEqs()] \\ rw [] \\ simp [])
  \\ fs [spt_eq_thm,lookup_inter_alt]
  \\ rw [] \\ fs []
  \\ drule env_to_list_lookup_equiv
  \\ fs [lookup_insert,lookup_fromAList,adjust_var_11]
  \\ rpt strip_tac \\ fs []
  \\ fs [wordSemTheory.cut_envs_def,wordSemTheory.cut_env_def] \\ rveq
  \\ gvs [wordSemTheory.cut_names_def,AllCaseEqs()]
  \\ fs [lookup_inter_alt] \\ rw []
  \\ fs [IN_domain_adjust_set_inter]
  \\ gvs [adjust_sets_def]
  \\ qpat_x_assum ‘_ ∈ domain (adjust_set x.locals)’ mp_tac
  \\ qpat_x_assum ‘_ ∉ domain (adjust_set kept_names)’ mp_tac
  \\ ‘domain x.locals = domain s.locals ∩ domain kept_names’ by
       (imp_res_tac cut_state_opt_SOME_eq \\ asm_rewrite_tac []
        \\ simp [domain_mk_wf, domain_inter])
  \\ simp [domain_lookup, lookup_adjust_set, AllCaseEqs()]
  \\ rw [] \\ gvs [domain_lookup]
  \\ qpat_x_assum ‘lookup _ x.locals = SOME _’ mp_tac
  \\ qpat_x_assum ‘domain x.locals = _’ mp_tac
  \\ qpat_x_assum ‘lookup _ kept_names ≠ _’ mp_tac
  \\ rpt (pop_assum kall_tac)
  \\ simp [domain_lookup, EXTENSION, IN_INTER]
  \\ metis_tac [oneTheory.one]))
    \\ ‘memory_rel c t.be (THE s.tstamps) s.refs s.space t.store t.memory t.mdomain
          ((RefPtr src_b src,Word wa1)::(RefPtr dst_b dst,Word wa2)::
             (join_env s.locals (toAList (inter t.locals (adjust_set s.locals))) ++
              [(the_global s.global,t.store ' Globals)] ++ flat s.stack t.stack))’ by
        (first_x_assum (fn th => mp_tac th THEN match_mp_tac memory_rel_rearrange)
         \\ fs [] \\ rw [] \\ fs [])
    \\ rpt_drule0 word_copy_array_thm \\ strip_tac
    \\ qpat_x_assum ‘_ = SOME m1’ mp_tac
    \\ fs [word_copy_array_def,GSYM WORD_NOT_LOWER]
    \\ IF_CASES_TAC \\ fs [] \\ strip_tac
    >- (
  once_rewrite_tac [wordSemTheory.evaluate_def]
  \\ simp [wordSemTheory.get_var_def,wordSemTheory.get_var_imm_def,
           lookup_insert,asmTheory.word_cmp_def]
  \\ ‘(?md. lookup ByteCopyAdd_location t.code = SOME (5,ByteCopyAdd_code,md))’ by
       fs [data_to_word_gcProofTheory.code_rel_def,
           stubs_md_def,stubs_def,MAP_MAP_o,o_DEF]
  \\ fs [wordSemTheory.bad_dest_args_def,wordSemTheory.find_code_def,
         eq_eval,push_env_code]
  \\ assume_tac CopyByteAdd_thm \\ SEP_I_TAC "evaluate"
  \\ pop_assum drule0 \\ fs [eq_eval]
  \\ impl_tac
  >- (‘2 ≤ dimword (:'a)’ by (fs [good_dimindex_def] \\ fs [dimword_def])
      \\ match_mp_tac LESS_EQ_TRANS \\ qexists_tac ‘dimword (:'a)’ \\ conj_tac
      >- (irule LESS_EQ_TRANS \\ qexists_tac ‘len_n MOD dimword (:'a)’
          \\ conj_tac
          >- simp [DIV_LESS_EQ]
          >- (irule LESS_IMP_LESS_OR_EQ \\ simp [MOD_LESS]))
      >- fs [wordSemTheory.MustTerminate_limit_def])
  \\ fs [] \\ disch_then kall_tac
  \\ fs [wordSemTheory.pop_env_def,wordSemTheory.push_env_def,
         wordSemTheory.set_vars_def,alist_insert_def]
  \\ fs [domain_union,domain_fromAList_toAList]
  \\ ‘domain (fromAList q) = domain y2’ by
    (imp_res_tac env_to_list_domain \\ asm_simp_tac std_ss [])
  \\ asm_simp_tac std_ss [AC UNION_COMM UNION_ASSOC]
  \\ fs [state_rel_thm,lookup_insert,lookup_fromAList,adjust_var_11]
  \\ drule0 env_to_list_lookup_equiv \\ fs [] \\ strip_tac
  \\ ‘x.stack = s.stack ∧ x.stack_max = s.stack_max ∧ x.locals_size = s.locals_size ∧
      x.stack_frame_sizes = s.stack_frame_sizes’ by
       (qpat_x_assum ‘cut_state_opt _ _ = SOME x’ mp_tac
        \\ simp [dataSemTheory.cut_state_opt_def, dataSemTheory.cut_state_def, AllCaseEqs()]
        \\ rw [] \\ simp [])
  \\ ‘stack_size t.stack = size_of_stack s.stack’ by
       (irule stack_rel_IMP_size_of_stack \\ first_assum (irule_at Any))
  \\ conj_tac >-
   (drule_all cut_envs_lookup_0 \\ simp [lookup_union,lookup_fromAList,ALOOKUP_toAList])
  \\ conj_tac >-
   (gen_tac \\ IF_CASES_TAC \\ asm_simp_tac std_ss [adjust_var_11]
    \\ ‘dataSem$cut_env kept_names s.locals = SOME x.locals’ by
         (qpat_x_assum ‘cut_state_opt _ _ = SOME x’ mp_tac
          \\ simp [dataSemTheory.cut_state_opt_def, dataSemTheory.cut_state_def, AllCaseEqs()]
          \\ rw [] \\ simp [])
    \\ full_simp_tac std_ss [IS_SOME_lookup,domain_union] \\ strip_tac
    \\ drule_all IN_adjust_var_lemma \\ simp [])
  \\ conj_tac >-
   (rewrite_tac [stack_size_eq, option_le_max_right]
    \\ disj1_tac \\ disj1_tac \\ disj2_tac
    \\ metis_tac [option_add_comm,option_le_refl])
  \\ conj_tac >-
   (rewrite_tac [stack_size_eq]
    \\ qpat_x_assum ‘x.stack = s.stack’ (rewrite_tac o single)
    \\ qpat_x_assum ‘stack_size t.stack = size_of_stack s.stack’ (rewrite_tac o single)
    \\ rewrite_tac [option_le_max] \\ rpt conj_tac
    >- (rewrite_tac [option_le_max_right] \\ disj1_tac
        \\ qpat_x_assum ‘x.stack_max = s.stack_max’ (rewrite_tac o single)
        \\ first_assum ACCEPT_TAC)
    >- (rewrite_tac [option_le_max_right] \\ disj2_tac
        \\ metis_tac [option_add_comm,option_le_add])
    >- (rewrite_tac [option_le_max_right] \\ disj2_tac
        \\ metis_tac [option_add_comm,option_add_assoc,option_le_eq_eqns,
                      option_le_max_right,option_le_refl])
    >- (rewrite_tac [option_le_max_right] \\ disj2_tac
        \\ metis_tac [option_add_comm,option_add_assoc,option_le_eq_eqns,
                      option_le_max_right,option_le_refl]))
  \\ ‘x.tstamps = s.tstamps ∧ x.space = s.space ∧ x.global = s.global’ by
       (qpat_x_assum ‘cut_state_opt _ _ = SOME x’ mp_tac
        \\ simp [dataSemTheory.cut_state_opt_def, dataSemTheory.cut_state_def, AllCaseEqs()]
        \\ rw [] \\ simp [])
  \\ asm_simp_tac std_ss []
  \\ once_rewrite_tac [insert_insert]
  \\ rewrite_tac [GSYM APPEND_ASSOC,APPEND]
  \\ irule memory_rel_insert \\ rewrite_tac [APPEND]
  \\ irule memory_rel_Unit \\ asm_rewrite_tac []
  \\ qpat_x_assum ‘_ t.mdomain _’ mp_tac
  \\ match_mp_tac memory_rel_rearrange
  \\ ‘cut_env kept_names s.locals = SOME x.locals’ by
       (qpat_x_assum ‘cut_state_opt _ _ = SOME x’ mp_tac
        \\ simp [dataSemTheory.cut_state_opt_def, dataSemTheory.cut_state_def, AllCaseEqs()]
        \\ rw [] \\ simp [])
  \\ simp [SF DNF_ss]
  \\ fs [join_env_def,inter_union_distrib]
  \\ drule_all cut_envs_inter \\ strip_tac \\ simp []
  \\ qsuff_tac ‘inter (fromAList q) (adjust_set x.locals) = inter t.locals (adjust_set x.locals)’
  >-
   (disch_then SUBST1_TAC
    \\ ‘x.locals = mk_wf (inter s.locals kept_names)’ by
         (imp_res_tac cut_state_opt_SOME_eq \\ asm_rewrite_tac [] \\ simp [])
    \\ rpt strip_tac \\ disj2_tac \\ disj2_tac \\ disj1_tac \\ disj1_tac
    \\ gvs [MEM_MAP, MEM_FILTER, EXISTS_PROD, MEM_toAList, lookup_inter, AllCaseEqs()]
    \\ qexists_tac ‘p_1’
    \\ qpat_x_assum ‘lookup p_1 (adjust_set (inter s.locals kept_names)) = SOME ()’ mp_tac
    \\ simp [lookup_adjust_set, domain_inter, AllCaseEqs(), domain_lookup]
    \\ rw []
    \\ qpat_x_assum ‘lookup _ (inter s.locals kept_names) = SOME _’ mp_tac
    \\ simp [lookup_inter, AllCaseEqs()] \\ rw [] \\ simp [])
  \\ fs [spt_eq_thm,lookup_inter_alt]
  \\ rw [] \\ fs []
  \\ drule env_to_list_lookup_equiv
  \\ fs [lookup_insert,lookup_fromAList,adjust_var_11]
  \\ rpt strip_tac \\ fs []
  \\ fs [wordSemTheory.cut_envs_def,wordSemTheory.cut_env_def] \\ rveq
  \\ gvs [wordSemTheory.cut_names_def,AllCaseEqs()]
  \\ fs [lookup_inter_alt] \\ rw []
  \\ fs [IN_domain_adjust_set_inter]
  \\ gvs [adjust_sets_def]
  \\ qpat_x_assum ‘_ ∈ domain (adjust_set x.locals)’ mp_tac
  \\ qpat_x_assum ‘_ ∉ domain (adjust_set kept_names)’ mp_tac
  \\ ‘domain x.locals = domain s.locals ∩ domain kept_names’ by
       (imp_res_tac cut_state_opt_SOME_eq \\ asm_rewrite_tac []
        \\ simp [domain_mk_wf, domain_inter])
  \\ simp [domain_lookup, lookup_adjust_set, AllCaseEqs()]
  \\ rw [] \\ gvs [domain_lookup]
  \\ qpat_x_assum ‘lookup _ x.locals = SOME _’ mp_tac
  \\ qpat_x_assum ‘domain x.locals = _’ mp_tac
  \\ qpat_x_assum ‘lookup _ kept_names ≠ _’ mp_tac
  \\ rpt (pop_assum kall_tac)
  \\ simp [domain_lookup, EXTENSION, IN_INTER]
  \\ metis_tac [oneTheory.one])
    \\ once_rewrite_tac [wordSemTheory.evaluate_def]
    \\ simp [wordSemTheory.get_var_def,wordSemTheory.get_var_imm_def,
             lookup_insert,asmTheory.word_cmp_def]
    \\ rewrite_tac [list_Seq_def]
    \\ simp [eq_eval]
    \\ ‘(?md. lookup ByteCopySub_location t.code = SOME (5,ByteCopySub_code,md))’ by
         fs [data_to_word_gcProofTheory.code_rel_def,
           stubs_md_def,stubs_def,MAP_MAP_o,o_DEF]
    \\ fs [wordSemTheory.bad_dest_args_def,wordSemTheory.find_code_def,
           eq_eval,push_env_code]
    \\ assume_tac CopyByteSub_thm \\ SEP_I_TAC "evaluate"
    \\ pop_assum drule0 \\ fs [eq_eval]
    \\ impl_tac
    >- (‘2 ≤ dimword (:'a)’ by (fs [good_dimindex_def] \\ fs [dimword_def])
        \\ match_mp_tac LESS_EQ_TRANS \\ qexists_tac ‘dimword (:'a)’ \\ conj_tac
        >- (irule LESS_EQ_TRANS \\ qexists_tac ‘len_n MOD dimword (:'a)’
            \\ conj_tac
            >- simp [DIV_LESS_EQ]
            >- (irule LESS_IMP_LESS_OR_EQ \\ simp [MOD_LESS]))
        >- fs [wordSemTheory.MustTerminate_limit_def])
    \\ fs [] \\ disch_then kall_tac
    \\ fs [wordSemTheory.pop_env_def,wordSemTheory.push_env_def,
           wordSemTheory.set_vars_def,alist_insert_def]
    \\ fs [domain_union,domain_fromAList_toAList]
    \\ ‘domain (fromAList q) = domain y2’ by
      (imp_res_tac env_to_list_domain \\ asm_simp_tac std_ss [])
    \\ asm_simp_tac std_ss [AC UNION_COMM UNION_ASSOC]
    \\ fs [state_rel_thm,lookup_insert,lookup_fromAList,adjust_var_11]
    \\ drule0 env_to_list_lookup_equiv \\ fs [] \\ strip_tac
    \\ ‘x.stack = s.stack ∧ x.stack_max = s.stack_max ∧ x.locals_size = s.locals_size ∧
        x.stack_frame_sizes = s.stack_frame_sizes’ by
         (qpat_x_assum ‘cut_state_opt _ _ = SOME x’ mp_tac
          \\ simp [dataSemTheory.cut_state_opt_def, dataSemTheory.cut_state_def, AllCaseEqs()]
          \\ rw [] \\ simp [])
    \\ ‘stack_size t.stack = size_of_stack s.stack’ by
         (irule stack_rel_IMP_size_of_stack \\ first_assum (irule_at Any))
    \\ conj_tac >-
     (drule_all cut_envs_lookup_0 \\ simp [lookup_union,lookup_fromAList,ALOOKUP_toAList])
    \\ conj_tac >-
     (gen_tac \\ IF_CASES_TAC \\ asm_simp_tac std_ss [adjust_var_11]
      \\ ‘dataSem$cut_env kept_names s.locals = SOME x.locals’ by
           (qpat_x_assum ‘cut_state_opt _ _ = SOME x’ mp_tac
            \\ simp [dataSemTheory.cut_state_opt_def, dataSemTheory.cut_state_def, AllCaseEqs()]
            \\ rw [] \\ simp [])
      \\ full_simp_tac std_ss [IS_SOME_lookup,domain_union] \\ strip_tac
      \\ drule_all IN_adjust_var_lemma \\ simp [])
    \\ conj_tac >-
     (rewrite_tac [stack_size_eq, option_le_max_right]
      \\ disj1_tac \\ disj1_tac \\ disj2_tac
      \\ metis_tac [option_add_comm,option_le_refl])
    \\ conj_tac >-
     (rewrite_tac [stack_size_eq]
      \\ qpat_x_assum ‘x.stack = s.stack’ (rewrite_tac o single)
      \\ qpat_x_assum ‘stack_size t.stack = size_of_stack s.stack’ (rewrite_tac o single)
      \\ rewrite_tac [option_le_max] \\ rpt conj_tac
      >- (rewrite_tac [option_le_max_right] \\ disj1_tac
          \\ qpat_x_assum ‘x.stack_max = s.stack_max’ (rewrite_tac o single)
          \\ first_assum ACCEPT_TAC)
      >- (rewrite_tac [option_le_max_right] \\ disj2_tac
          \\ metis_tac [option_add_comm,option_le_add])
      >- (rewrite_tac [option_le_max_right] \\ disj2_tac
          \\ metis_tac [option_add_comm,option_add_assoc,option_le_eq_eqns,
                        option_le_max_right,option_le_refl])
      >- (rewrite_tac [option_le_max_right] \\ disj2_tac
          \\ metis_tac [option_add_comm,option_add_assoc,option_le_eq_eqns,
                        option_le_max_right,option_le_refl]))
    \\ ‘x.tstamps = s.tstamps ∧ x.space = s.space ∧ x.global = s.global’ by
         (qpat_x_assum ‘cut_state_opt _ _ = SOME x’ mp_tac
          \\ simp [dataSemTheory.cut_state_opt_def, dataSemTheory.cut_state_def, AllCaseEqs()]
          \\ rw [] \\ simp [])
    \\ asm_simp_tac std_ss []
    \\ once_rewrite_tac [insert_insert]
    \\ rewrite_tac [GSYM APPEND_ASSOC,APPEND]
    \\ irule memory_rel_insert \\ rewrite_tac [APPEND]
    \\ irule memory_rel_Unit \\ asm_rewrite_tac []
    \\ qpat_x_assum ‘_ t.mdomain _’ mp_tac
    \\ match_mp_tac memory_rel_rearrange
    \\ ‘cut_env kept_names s.locals = SOME x.locals’ by
         (qpat_x_assum ‘cut_state_opt _ _ = SOME x’ mp_tac
          \\ simp [dataSemTheory.cut_state_opt_def, dataSemTheory.cut_state_def, AllCaseEqs()]
          \\ rw [] \\ simp [])
    \\ simp [SF DNF_ss]
    \\ fs [join_env_def,inter_union_distrib]
    \\ drule_all cut_envs_inter \\ strip_tac \\ simp []
    \\ qsuff_tac ‘inter (fromAList q) (adjust_set x.locals) = inter t.locals (adjust_set x.locals)’
    >-
     (disch_then SUBST1_TAC
      \\ ‘x.locals = mk_wf (inter s.locals kept_names)’ by
           (imp_res_tac cut_state_opt_SOME_eq \\ asm_rewrite_tac [] \\ simp [])
      \\ rpt strip_tac \\ disj2_tac \\ disj2_tac \\ disj1_tac \\ disj1_tac
      \\ gvs [MEM_MAP, MEM_FILTER, EXISTS_PROD, MEM_toAList, lookup_inter, AllCaseEqs()]
      \\ qexists_tac ‘p_1’
      \\ qpat_x_assum ‘lookup p_1 (adjust_set (inter s.locals kept_names)) = SOME ()’ mp_tac
      \\ simp [lookup_adjust_set, domain_inter, AllCaseEqs(), domain_lookup]
      \\ rw []
      \\ qpat_x_assum ‘lookup _ (inter s.locals kept_names) = SOME _’ mp_tac
      \\ simp [lookup_inter, AllCaseEqs()] \\ rw [] \\ simp [])
    \\ fs [spt_eq_thm,lookup_inter_alt]
    \\ rw [] \\ fs []
    \\ drule env_to_list_lookup_equiv
    \\ fs [lookup_insert,lookup_fromAList,adjust_var_11]
    \\ rpt strip_tac \\ fs []
    \\ fs [wordSemTheory.cut_envs_def,wordSemTheory.cut_env_def] \\ rveq
    \\ gvs [wordSemTheory.cut_names_def,AllCaseEqs()]
    \\ fs [lookup_inter_alt] \\ rw []
    \\ fs [IN_domain_adjust_set_inter]
    \\ gvs [adjust_sets_def]
    \\ qpat_x_assum ‘_ ∈ domain (adjust_set x.locals)’ mp_tac
    \\ qpat_x_assum ‘_ ∉ domain (adjust_set kept_names)’ mp_tac
    \\ ‘domain x.locals = domain s.locals ∩ domain kept_names’ by
         (imp_res_tac cut_state_opt_SOME_eq \\ asm_rewrite_tac []
          \\ simp [domain_mk_wf, domain_inter])
    \\ simp [domain_lookup, lookup_adjust_set, AllCaseEqs()]
    \\ rw [] \\ gvs [domain_lookup]
    \\ qpat_x_assum ‘lookup _ x.locals = SOME _’ mp_tac
    \\ qpat_x_assum ‘domain x.locals = _’ mp_tac
    \\ qpat_x_assum ‘lookup _ kept_names ≠ _’ mp_tac
    \\ rpt (pop_assum kall_tac)
    \\ simp [domain_lookup, EXTENSION, IN_INTER]
    \\ metis_tac [oneTheory.one]
QED

Theorem byte_copy_alloc_source[local]:
  ∀k n prefix_bytes a b model dm actual.
    good_dimindex (:'a) /\ k = dimindex (:'a) DIV 8 /\
    byte_copy_range_inv n (a:'a word) b model dm /\
    byte_copy_memory_rel k ((n - prefix_bytes) DIV (3 * k)) b actual model ==>
    !i. i < n ==>
      actual (byte_align (a + n2w i)) = model (byte_align (a + n2w i))
Proof
  rpt gen_tac
  \\ strip_tac
  \\ `0 < k` by fs [good_dimindex_def]
  \\ `0 < 3 * k` by decide_tac
  \\ `((n - prefix_bytes) DIV (3 * k)) * (3 * k) <= n` by (
    qspec_then `3 * k` mp_tac DIVISION
    \\ simp []
    \\ disch_then (qspec_then `n - prefix_bytes` mp_tac)
    \\ decide_tac)
  \\ qx_gen_tac `src_index` \\ strip_tac
  \\ qpat_x_assum `byte_copy_memory_rel _ _ _ _ _`
       (irule o REWRITE_RULE [byte_copy_memory_rel_def])
  \\ qx_gen_tac `dst_index` \\ strip_tac
  \\ qspecl_then [`k`,`w2n (a + n2w src_index) MOD k`,`a + n2w src_index`]
       mp_tac byte_copy_align_address
  \\ impl_tac >- ASM_REWRITE_TAC []
  \\ strip_tac
  \\ strip_tac
  \\ qabbrev_tac `r = w2n (a + n2w src_index) MOD k`
  \\ `r < k` by simp [Abbr `r`]
  \\ `(dst_index + 1) * k <= (3 * ((n - prefix_bytes) DIV (3 * k))) * k`
       by (PURE_REWRITE_TAC [LE_MULT_RCANCEL] \\ decide_tac)
  \\ `dst_index * k + r < n` by (
    qpat_assum `(dst_index + 1) * k <= _` mp_tac
    \\ qpat_assum `((n - prefix_bytes) DIV (3 * k)) * (3 * k) <= n` mp_tac
    \\ qpat_assum `r < k` mp_tac
    \\ rpt (pop_assum kall_tac)
    \\ PURE_REWRITE_TAC [RIGHT_ADD_DISTRIB,MULT_CLAUSES,GSYM MULT_ASSOC]
    \\ decide_tac)
  \\ qpat_x_assum `byte_copy_range_inv _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [byte_copy_range_inv_def])
  \\ qpat_x_assum `!i j. _` (qspecl_then [`src_index`,`dst_index * k + r`] mp_tac)
  \\ simp [GSYM word_add_n2w,WORD_ADD_ASSOC]
  \\ qpat_x_assum `a + n2w src_index = byte_align _ + _` mp_tac
  \\ qpat_x_assum `byte_align (a + n2w src_index) = _` mp_tac
  \\ qpat_x_assum `k = _` mp_tac
  \\ rpt (pop_assum kall_tac)
  \\ metis_tac [WORD_ADD_ASSOC,WORD_ADD_COMM]
QED

Theorem byte_copy_alloc_middle[local]:
  ∀k prefix_bytes j n.
    0 < k /\ prefix_bytes < k /\ j + 4 < n DIV k + 1 ==>
    j < 3 * ((n - prefix_bytes) DIV (3 * k))
Proof
  rpt gen_tac
  \\ strip_tac
  \\ `0 < 3 * k` by decide_tac
  \\ qpat_assum `0 < k` (STRIP_ASSUME_TAC o Q.SPEC `n` o MATCH_MP DIVISION)
  \\ qpat_assum `0 < 3 * k`
       (STRIP_ASSUME_TAC o Q.SPEC `n - prefix_bytes` o MATCH_MP DIVISION)
  \\ `(j + 4) * k <= (n DIV k) * k` by (
    PURE_REWRITE_TAC [LE_MULT_RCANCEL]
    \\ decide_tac)
  \\ `j * k < (3 * ((n - prefix_bytes) DIV (3 * k))) * k` by (
    qpat_assum `(j + 4) * k <= _` mp_tac
    \\ qpat_assum `n = _` mp_tac
    \\ qpat_assum `n - prefix_bytes = _` mp_tac
    \\ qpat_assum `(n - prefix_bytes) MOD (3 * k) < _` mp_tac
    \\ qpat_assum `prefix_bytes < k` mp_tac
    \\ rpt (pop_assum kall_tac)
    \\ PURE_REWRITE_TAC [RIGHT_ADD_DISTRIB,GSYM MULT_ASSOC,MULT_CLAUSES]
    \\ decide_tac)
  \\ fs [LT_MULT_RCANCEL]
QED

Theorem byte_copy_alloc_memory[local]:
  ∀k prefix_bytes payload_words n b original dm model actual.
    good_dimindex (:'a) /\ k = dimindex (:'a) DIV 8 /\ prefix_bytes < k /\
    payload_words = n DIV k + 1 /\
    store_list (b:'a word) (REPLICATE payload_words (Word 0w)) original dm = SOME model /\
    (!p. (?j. j < payload_words /\ (j = 0 \/ payload_words <= j + 4) /\
              p = b + n2w (j * k)) ==> actual p = Word 0w) /\
    (!p. (!j. j < payload_words ==> p <> b + n2w (j * k)) ==>
         actual p = original p) ==>
    byte_copy_memory_rel k ((n - prefix_bytes) DIV (3 * k)) b actual model
Proof
  rpt gen_tac
  \\ strip_tac
  \\ drule store_list_replicate_memory
  \\ disch_tac
  \\ PURE_REWRITE_TAC [byte_copy_memory_rel_def]
  \\ qx_gen_tac `p` \\ strip_tac
  \\ qpat_assum `k = dimindex (:'a) DIV 8` (fn bytes =>
    qpat_x_assum `!p. model p = _`
      (assume_tac o REWRITE_RULE [bytes_in_word_def,word_mul_n2w,GSYM bytes]))
  \\ Cases_on `?j. j < payload_words /\ p = b + n2w (j * k)`
  >- (
    qpat_assum `?j. j < payload_words /\ _`
      (qx_choose_then `word_index` strip_assume_tac)
    \\ `0 < k` by fs [good_dimindex_def]
    \\ `~(word_index < 3 * ((n - prefix_bytes) DIV (3 * k)))` by (
      qpat_x_assum `!j. j < 3 * _ ==> _` (qspec_then `word_index` mp_tac)
      \\ simp [])
    \\ `payload_words <= word_index + 4` by (
      qspecl_then [`k`,`prefix_bytes`,`word_index`,`n`] mp_tac
        byte_copy_alloc_middle
      \\ ASM_REWRITE_TAC []
      \\ decide_tac)
    \\ `actual p = Word 0w` by (
      qpat_x_assum `!p. (?j. _ /\ _ /\ _) ==> actual p = _` irule
      \\ qexists_tac `word_index`
      \\ simp [])
    \\ simp [])
  \\ `!j. j < payload_words ==> p <> b + n2w (j * k)` by metis_tac []
  \\ simp []
QED

Theorem byte_copy_alloc_align_initial[local]:
  good_dimindex (:'a) /\ k = dimindex (:'a) DIV 8 /\ byte_aligned (b:'a word) /\
  byte_copy_range_inv n a b model dm /\ actual b = model b /\
  (!prefix_bytes. prefix_bytes < k ==>
    byte_copy_memory_rel k ((n - prefix_bytes) DIV (3 * k)) b actual model) ==>
  ?prefix_bytes. byte_copy_align_inv k n prefix_bytes a b actual model dm
Proof
  strip_tac
  \\ qspecl_then [`k`,`a`] mp_tac byte_copy_align_prefix
  \\ impl_tac >- ASM_REWRITE_TAC []
  \\ disch_then (qx_choose_then `prefix_bytes` strip_assume_tac)
  \\ `byte_copy_memory_rel k ((n - prefix_bytes) DIV (3 * k)) b actual model`
       by simp []
  \\ `!i. i <= prefix_bytes ==> byte_align (b + n2w i) = b` by (
    rpt strip_tac
    \\ irule byte_align_add_byte
    \\ fs [] \\ decide_tac)
  \\ qexists_tac `prefix_bytes`
  \\ simp [byte_copy_align_inv_def]
  \\ conj_tac
  >- (
    qspecl_then [`k`,`n`,`prefix_bytes`,`a`,`b`,`model`,`dm`,`actual`] mp_tac
      byte_copy_alloc_source
    \\ simp [])
  \\ gvs []
QED

Definition byte_copy_alloc_init_def:
  byte_copy_alloc_init k payload_words (base:'a word) m =
    let last = base + n2w ((payload_words - 1) * k) in
    let m = (last =+ Word 0w) m in
    let m = if payload_words < 2 then m else (last - n2w k =+ Word 0w) m in
    let m = if payload_words < 3 then m else (last - n2w (2 * k) =+ Word 0w) m in
    let m = if payload_words < 4 then m else (last - n2w (3 * k) =+ Word 0w) m in
      (base =+ Word 0w) m
End

Theorem byte_copy_alloc_edge_indices[local]:
  0 < payload_words ==>
  (j < payload_words /\ (j = 0 \/ payload_words <= j + 4) <=>
   j = 0 \/ j = payload_words - 1 \/
   (2 <= payload_words /\ j = payload_words - 2) \/
   (3 <= payload_words /\ j = payload_words - 3) \/
   (4 <= payload_words /\ j = payload_words - 4))
Proof
  strip_tac
  \\ decide_tac
QED

Theorem byte_copy_alloc_init_address[local]:
  j < payload_words ==>
  (base:'a word) + n2w ((payload_words - 1) * k) - n2w (j * k) =
    base + n2w ((payload_words - (j + 1)) * k)
Proof
  strip_tac
  \\ `j <= payload_words - 1` by decide_tac
  \\ `j * k <= (payload_words - 1) * k` by simp [LE_MULT_RCANCEL]
  \\ `payload_words - 1 - j = payload_words - (j + 1)` by decide_tac
  \\ simp [WORD_ADD_SUB_ASSOC,GSYM n2w_sub,GSYM RIGHT_SUB_DISTRIB]
QED

Theorem byte_copy_alloc_init_apply[local]:
  0 < payload_words ==>
  !p. byte_copy_alloc_init k payload_words (base:'a word) m p =
    if ?j. j < payload_words /\ (j = 0 \/ payload_words <= j + 4) /\
           p = base + n2w (j * k)
    then Word 0w else m p
Proof
  strip_tac \\ gen_tac
  \\ PURE_REWRITE_TAC [CONJ_ASSOC]
  \\ asm_simp_tac std_ss
       [byte_copy_alloc_edge_indices,RIGHT_AND_OVER_OR,EXISTS_OR_THM]
  \\ Cases_on `payload_words < 2`
  \\ Cases_on `payload_words < 3`
  \\ Cases_on `payload_words < 4`
  \\ gvs [DECIDE ``~(n < 2) <=> 1 < n``,
          DECIDE ``~(n < 3) <=> 2 < n``,
          DECIDE ``~(n < 4) <=> 3 < n``]
  \\ asm_simp_tac std_ss
       [byte_copy_alloc_init_def,LET_THM,COND_RATOR,APPLY_UPDATE_THM]
  \\ rpt IF_CASES_TAC
  \\ gvs [APPLY_UPDATE_THM,
    DECIDE ``~((n:num) < 2) <=> 1 < n``,
    DECIDE ``~((n:num) < 3) <=> 2 < n``,
    DECIDE ``~((n:num) < 4) <=> 3 < n``,
    DECIDE ``(2:num) < n ==> 1 < n``,
    DECIDE ``(3:num) < n ==> 1 < n /\ 2 < n``,
    SIMP_RULE (srw_ss() ++ ARITH_ss) []
      (Q.INST [`j` |-> `1`] byte_copy_alloc_init_address),
    SIMP_RULE (srw_ss() ++ ARITH_ss) [] byte_copy_alloc_init_address]
QED

Theorem byte_copy_alloc_ready[local]:
  good_dimindex (:'a) /\ k = dimindex (:'a) DIV 8 /\ byte_aligned (b:'a word) /\
  payload_words = n DIV k + 1 /\ byte_copy_range_inv n a b model dm /\
  store_list b (REPLICATE payload_words (Word 0w)) original dm = SOME model ==>
  ?prefix_bytes. byte_copy_align_inv k n prefix_bytes a b
    (byte_copy_alloc_init k payload_words b original) model dm
Proof
  strip_tac
  \\ `0 < payload_words` by decide_tac
  \\ `!p. byte_copy_alloc_init k payload_words b original p =
       if ?j. j < payload_words /\ (j = 0 \/ payload_words <= j + 4) /\
              p = b + n2w (j * k)
       then Word 0w else original p` by (
    match_mp_tac byte_copy_alloc_init_apply
    \\ ASM_REWRITE_TAC [])
  \\ drule store_list_replicate_memory \\ disch_tac
  \\ match_mp_tac byte_copy_alloc_align_initial
  \\ ASM_REWRITE_TAC []
  \\ conj_tac
  >- (
    CONV_TAC (ONCE_DEPTH_CONV (HO_REWR_CONV EXISTS_NUM))
    \\ simp [])
  \\ qx_gen_tac `prefix_bytes` \\ strip_tac
  \\ qspecl_then [`k`,`prefix_bytes`,`payload_words`,`n`,`b`,`original`,`dm`,`model`,
                    `byte_copy_alloc_init k payload_words b original`] mp_tac
       byte_copy_alloc_memory
  \\ impl_tac
  >- (
    simp []
    \\ rpt strip_tac
    \\ IF_CASES_TAC
    >- (
      qpat_x_assum `?j. _` (qx_choose_then `edge_index` strip_assume_tac)
      \\ qpat_x_assum `!j. j < n DIV (dimindex (:'a) DIV 8) + 1 ==> _`
           (qspec_then `edge_index` mp_tac)
      \\ simp [])
    \\ simp [])
  \\ simp []
QED

Theorem do_app_CopyByte_new_shape[local]:
  do_app (MemOp (CopyByte T)) vals s = Rval (v,s') ==>
  ?flag src offset len. vals = [RefPtr flag src;Number offset;Number len]
Proof
  strip_tac
  \\ fs [do_app_def,do_space_def,dataLangTheory.op_space_reset_def,
         do_app_aux_def,AllCaseEqs()]
QED

Theorem byte_copy_range_inv_from_arrays[local]:
  memory_rel c be ts refs sp st m dm
    ((RefPtr flag1 p1,Word (w1:'a word))::(RefPtr flag2 p2,Word w2)::vars) /\
  lookup p1 refs = SOME (ByteArray array_flag1 xs) /\
  lookup p2 refs = SOME (ByteArray array_flag2 ys) /\
  good_dimindex (:'a) /\ p1 <> p2 /\
  get_real_addr c st w1 = SOME a /\ get_real_addr c st w2 = SOME b /\
  offset + n <= LENGTH xs /\ n <= LENGTH ys ==>
  byte_copy_range_inv n (a + bytes_in_word + n2w offset) (b + bytes_in_word) m dm
Proof
  strip_tac
  \\ `!i. i < LENGTH xs ==>
       mem_load_byte_aux m dm be (a + bytes_in_word + n2w i) = SOME (EL i xs)` by (
    rpt strip_tac
    \\ drule_all_then ACCEPT_TAC memory_rel_ByteArray_loads)
  \\ `!i j. i < LENGTH xs /\ j < LENGTH ys ==>
       a + bytes_in_word + n2w i <> b + bytes_in_word + n2w j` by (
    qx_genl_tac [`i`,`j`] \\ strip_tac
    \\ drule_all_then ACCEPT_TAC memory_rel_byte_arrays_disjoint)
  \\ qpat_assum `memory_rel _ _ _ _ _ _ _ _ _`
       (assume_tac o MATCH_MP memory_rel_swap)
  \\ `!i. i < LENGTH ys ==>
       mem_load_byte_aux m dm be (b + bytes_in_word + n2w i) = SOME (EL i ys)` by (
    rpt strip_tac
    \\ drule_all_then ACCEPT_TAC memory_rel_ByteArray_loads)
  \\ PURE_REWRITE_TAC [byte_copy_range_inv_def,addressTheory.word_arith_lemma1]
  \\ conj_tac
  >- (
    qx_gen_tac `i` \\ strip_tac
    \\ qpat_x_assum `!i. i < LENGTH xs ==> _`
         (qspec_then `offset + i` mp_tac)
    \\ impl_tac >- decide_tac
    \\ disch_tac
    \\ qpat_x_assum `!i. i < LENGTH ys ==> _` (qspec_then `i` mp_tac)
    \\ impl_tac >- decide_tac
    \\ disch_tac
    \\ gvs [wordSemTheory.mem_load_byte_aux_def,isWord_def,AllCaseEqs()])
  \\ qx_genl_tac [`i`,`j`] \\ strip_tac
  \\ qpat_x_assum `!i j. i < LENGTH xs /\ j < LENGTH ys ==> _`
       (qspecl_then [`offset + i`,`j`] mp_tac)
  \\ impl_tac >- decide_tac
  \\ simp []
QED

Theorem evaluate_byte_copy_clear[local]:
  wordSem$get_var count_reg (s:('a,'c,'ffi) wordSem$state) = SOME (Word (n2w len)) /\
  wordSem$get_var zero_reg s = SOME (Word 0w) /\
  wordSem$word_exp s address_exp = SOME (Word p) /\
  len < dimword (:'a) /\ limit < dimword (:'a) /\
  (~(len < limit) ==> p IN s.mdomain) ==>
  wordSem$evaluate (If Lower count_reg (Imm (&limit)) Skip (Store address_exp zero_reg),s) =
  (NONE,s with memory := if len < limit then s.memory else (p =+ Word 0w) s.memory)
Proof
  strip_tac \\ Cases_on `len < limit`
  \\ simp [Once wordSemTheory.evaluate_def,word_exp_rw,asmTheory.word_cmp_def,WORD_LO]
  \\ simp [Once wordSemTheory.evaluate_def,word_exp_rw,wordSemTheory.mem_store_def]
QED

Theorem byte_copy_alloc_header[local]:
  arch_width_bits c.arch_width = dimindex (:'a) /\
  c.len_size + 9 < dimindex (:'a) ==>
  ((7w || (bytes_in_word + n2w len) <<
    (dimindex (:'a) - shift (dimindex (:'a)) - c.len_size)) : 'a word) =
  n2w (make_byte_header c T len)
Proof
  strip_tac
  \\ Cases_on `c.arch_width`
  \\ fs [make_byte_header_def,bytes_in_word_def,asmTheory.arch_width_bits_def,
         shift_def,WORD_MUL_LSL,word_add_n2w,word_mul_n2w]
  \\ qpat_assum `NUMERAL _ = dimindex (:'a)` (PURE_REWRITE_TAC o single o GSYM)
  \\ simp [GSYM RIGHT_ADD_DISTRIB]
  \\ irule multiplied_header_or
  \\ fs []
QED

Theorem evaluate_ByteCopyNewInit:
  ∀c len k payload_words s base.
    good_dimindex (:'a) /\ arch_width_bits c.arch_width = dimindex (:'a) /\
    c.len_size + 9 < dimindex (:'a) /\ len < dimword (:'a) DIV 8 /\
    k = dimindex (:'a) DIV 8 /\ payload_words = byte_len (dimindex (:'a)) len /\
    get_var 6 (s:('a,'c,'ffi) wordSem$state) = SOME (Word (n2w (2 * len))) /\
    FLOOKUP s.store NextFree = SOME (Word base) /\
    (!j. j <= payload_words ==> base + n2w j * bytes_in_word IN s.mdomain) ==>
    ?locals.
      evaluate (ByteCopyNewInit_code c,s) =
        (NONE,s with <|locals := locals;
           memory := byte_copy_alloc_init k payload_words (base + bytes_in_word)
             ((base =+ Word (n2w (make_byte_header c T len))) s.memory);
           store := s.store |+
             (NextFree,Word (base + bytes_in_word * n2w (payload_words + 1)))|>) /\
      lookup 9 locals = SOME (Word base) /\
      !v. v < 9 /\ EVEN v ==> lookup v locals = lookup v s.locals
Proof
  rpt gen_tac
  \\ strip_tac
  \\ qpat_x_assum `k = _` (assume_tac o ONCE_REWRITE_RULE [GSYM markerTheory.Abbrev_def])
  \\ qpat_x_assum `payload_words = _`
       (assume_tac o ONCE_REWRITE_RULE [GSYM markerTheory.Abbrev_def])
  \\ `0 < k /\ payload_words = len DIV k + 1` by (
    fs [Abbr `k`,Abbr `payload_words`,byte_len_def,good_dimindex_def] \\ fs [])
  \\ `0 < payload_words /\ payload_words < dimword (:'a)` by (
    `len DIV k <= len /\ dimword (:'a) DIV 8 < dimword (:'a)` by
      simp [DIV_LESS_EQ,DIV_LESS]
    \\ decide_tac)
  \\ qpat_x_assum `payload_words = len DIV k + 1` kall_tac
  \\ `arch_bytes c.arch_width = dimindex (:'a) DIV 8` by simp [arch_size]
  \\ `base IN s.mdomain` by
       qpat_assum `!j. j <= payload_words ==> _`
         (qspec_then `0` (ACCEPT_TAC o SIMP_RULE (srw_ss()) [WORD_MULT_CLAUSES]))
  \\ `2 * len < dimword (:'a) /\ len < dimword (:'a)` by (
    fs [X_LT_DIV] \\ decide_tac)
  \\ `(n2w (2 * len):'a word) >>> 1 = n2w len` by (
    rewrite_tac [GSYM w2n_11,w2n_lsr]
    \\ simp [ONCE_REWRITE_RULE [MULT_COMM] MULT_DIV])
  \\ `n2w k = (bytes_in_word:'a word)` by simp [Abbr `k`,bytes_in_word_def]
  \\ `(bytes_in_word + n2w len) >>> shift (dimindex (:'a)) =
        n2w payload_words : 'a word` by (
    qpat_assum `n2w k = _` (SUBST1_TAC o SYM)
    \\ simp_tac std_ss [word_add_n2w]
    \\ rewrite_tac [GSYM w2n_11,w2n_lsr]
    \\ qpat_assum `good_dimindex _` (strip_assume_tac o REWRITE_RULE [good_dimindex_def])
    \\ fs [Abbr `k`,Abbr `payload_words`,byte_len_def,shift_def,dimword_def,
           ADD4DIV4,ADD8DIV8])
  \\ `((7w || (bytes_in_word + n2w len) <<
        (dimindex (:'a) - shift (dimindex (:'a)) - c.len_size)) : 'a word) =
        n2w (make_byte_header c T len)` by
       (irule byte_copy_alloc_header \\ simp [])
  \\ `dimindex (:'a) - shift (dimindex (:'a)) - c.len_size < dimindex (:'a)` by
       fs [good_dimindex_def,shift_def]
  \\ `dimindex (:'a) - shift (dimindex (:'a)) - c.len_size < dimword (:'a)` by (
    match_mp_tac LESS_TRANS
    \\ qexists_tac `dimindex (:'a)`
    \\ simp [dimindex_lt_dimword] \\ decide_tac)
  \\ `shift (dimindex (:'a)) < dimindex (:'a) /\
        shift (dimindex (:'a)) < dimword (:'a)` by
       fs [good_dimindex_def,shift_def,dimword_def]
  \\ simp [ByteCopyNewInit_code_def]
  \\ once_rewrite_tac [list_Seq_def] \\ eval_tac
  \\ once_rewrite_tac [list_Seq_def] \\ eval_tac
  \\ simp [lookup_insert,GREATER_EQ]
  \\ once_rewrite_tac [list_Seq_def]
  \\ fs [wordSemTheory.evaluate_def,word_exp_rw,wordSemTheory.mem_store_def,
         wordSemTheory.set_var_def]
  \\ once_rewrite_tac [list_Seq_def]
  \\ fs [wordSemTheory.evaluate_def,word_exp_rw,wordSemTheory.set_var_def,
         GSYM word_mul_n2w,GREATER_EQ]
  \\ `n2w payload_words << shift (dimindex (:'a)) =
        (bytes_in_word:'a word) * n2w payload_words` by
       simp [shift_lsl,WORD_MULT_COMM]
  \\ `base + bytes_in_word * n2w payload_words IN s.mdomain` by (
    qpat_assum `!j. j <= payload_words ==> _` (qspec_then `payload_words` mp_tac)
    \\ simp [])
  \\ once_rewrite_tac [list_Seq_def]
  \\ fs [wordSemTheory.evaluate_def,word_exp_rw,wordSemTheory.set_var_def,GREATER_EQ]
  \\ once_rewrite_tac [list_Seq_def]
  \\ fs [wordSemTheory.evaluate_def,word_exp_rw,wordSemTheory.set_var_def]
  \\ once_rewrite_tac [list_Seq_def]
  \\ fs [wordSemTheory.evaluate_def,word_exp_rw,wordSemTheory.mem_store_def]
  \\ `!j. j <= payload_words ==>
        base + bytes_in_word * n2w payload_words - bytes_in_word * n2w j IN s.mdomain` by (
    qx_gen_tac `j` \\ strip_tac
    \\ qpat_x_assum `!j. j <= payload_words ==> _`
         (qspec_then `payload_words - j` mp_tac)
    \\ simp_tac std_ss [SUB_LESS_EQ]
    \\ asm_simp_tac std_ss [n2w_sub,WORD_LEFT_SUB_DISTRIB,GSYM WORD_ADD_SUB_ASSOC])
  \\ `4 < dimword (:'a)` by fs [good_dimindex_def,dimword_def]
  \\ `2 < dimword (:'a) /\ 3 < dimword (:'a)` by decide_tac
  \\ `!j. j < 4 ==> (~(payload_words < j + 1) ==>
        base + bytes_in_word * n2w payload_words - bytes_in_word * n2w j IN s.mdomain)` by (
    qx_gen_tac `j` \\ strip_tac \\ strip_tac
    \\ `j <= payload_words` by decide_tac
    \\ qpat_x_assum `!j. j <= payload_words ==> _` (qspec_then `j` mp_tac)
    \\ simp [])
  \\ qpat_assum `!j. j < 4 ==> _` (assume_tac o SIMP_RULE (srw_ss()) [] o Q.SPEC `1`)
  \\ qpat_assum `!j. j < 4 ==> _` (assume_tac o SIMP_RULE (srw_ss()) [] o Q.SPEC `2`)
  \\ qpat_assum `!j. j < 4 ==> _` (assume_tac o SIMP_RULE (srw_ss()) [] o Q.SPEC `3`)
  \\ once_rewrite_tac [list_Seq_def]
  \\ simp [Once wordSemTheory.evaluate_def]
  \\ qmatch_goalsub_abbrev_tac
       `wordSem$evaluate (If Lower 7 (Imm 2) Skip
          (Store (Op Sub [Var 11; Const (&k)]) 13),edge_state)`
  \\ `wordSem$evaluate (If Lower 7 (Imm 2) Skip
          (Store (Op Sub [Var 11; Const (&k)]) 13),edge_state) =
       (NONE,edge_state with memory := if payload_words < 2 then edge_state.memory else
         (base + bytes_in_word * n2w payload_words - bytes_in_word =+ Word 0w)
           edge_state.memory)` by (
    irule evaluate_byte_copy_clear
    \\ simp [Abbr `edge_state`,word_exp_rw,GSYM word_mul_n2w])
  \\ qpat_x_assum `wordSem$evaluate (If Lower 7 (Imm 2) Skip _,_) = _` SUBST1_TAC
  \\ simp [Abbr `edge_state`]
  \\ once_rewrite_tac [list_Seq_def]
  \\ simp [Once wordSemTheory.evaluate_def]
  \\ qmatch_goalsub_abbrev_tac
       `wordSem$evaluate (If Lower 7 (Imm 3) Skip
          (Store (Op Sub [Var 11; Const (&(2 * k))]) 13),edge_state_two)`
  \\ `wordSem$evaluate (If Lower 7 (Imm 3) Skip
          (Store (Op Sub [Var 11; Const (&(2 * k))]) 13),edge_state_two) =
       (NONE,edge_state_two with memory := if payload_words < 3 then edge_state_two.memory else
         (base + bytes_in_word * n2w payload_words - n2w (2 * k) =+ Word 0w)
           edge_state_two.memory)` by (
    irule evaluate_byte_copy_clear
    \\ simp [Abbr `edge_state_two`,word_exp_rw,GSYM word_mul_n2w])
  \\ qpat_x_assum `wordSem$evaluate (If Lower 7 (Imm 3) Skip _,_) = _` SUBST1_TAC
  \\ simp [Abbr `edge_state_two`]
  \\ once_rewrite_tac [list_Seq_def]
  \\ simp [Once wordSemTheory.evaluate_def]
  \\ qmatch_goalsub_abbrev_tac
       `wordSem$evaluate (If Lower 7 (Imm 4) Skip
          (Store (Op Sub [Var 11; Const (&(3 * k))]) 13),edge_state_three)`
  \\ `wordSem$evaluate (If Lower 7 (Imm 4) Skip
          (Store (Op Sub [Var 11; Const (&(3 * k))]) 13),edge_state_three) =
       (NONE,edge_state_three with memory := if payload_words < 4 then edge_state_three.memory else
         (base + bytes_in_word * n2w payload_words - n2w (3 * k) =+ Word 0w)
           edge_state_three.memory)` by (
    irule evaluate_byte_copy_clear
    \\ simp [Abbr `edge_state_three`,word_exp_rw,GSYM word_mul_n2w])
  \\ qpat_x_assum `wordSem$evaluate (If Lower 7 (Imm 4) Skip _,_) = _` SUBST1_TAC
  \\ simp [Abbr `edge_state_three`]
  \\ `base + bytes_in_word IN s.mdomain` by (
    qpat_x_assum `!j. j <= payload_words ==> base + bytes_in_word * n2w j IN s.mdomain`
      (qspec_then `1` mp_tac)
    \\ simp [])
  \\ once_rewrite_tac [list_Seq_def]
  \\ fs [wordSemTheory.evaluate_def,word_exp_rw,wordSemTheory.mem_store_def]
  \\ once_rewrite_tac [list_Seq_def]
  \\ fs [wordSemTheory.evaluate_def,word_exp_rw,wordSemTheory.set_store_def]
  \\ simp [wordSemTheory.state_component_equality,lookup_insert]
  \\ `base + bytes_in_word + n2w ((payload_words - 1) * k) =
        base + bytes_in_word * n2w payload_words` by (
    `1 <= payload_words` by simp []
    \\ asm_simp_tac std_ss
      [GSYM word_mul_n2w,n2w_sub,WORD_RIGHT_SUB_DISTRIB,WORD_MULT_CLAUSES,WORD_MULT_COMM]
    \\ CONV_TAC wordsLib.WORD_ARITH_CONV)
  \\ rpt conj_tac
  >- (
    simp_tac std_ss [GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB,WORD_MULT_CLAUSES]
    \\ CONV_TAC wordsLib.WORD_ARITH_CONV)
  >- (
    Cases_on `payload_words < 2`
    \\ Cases_on `payload_words < 3`
    \\ Cases_on `payload_words < 4`
    \\ fs [byte_copy_alloc_init_def,GSYM word_mul_n2w]
    \\ `1 <= payload_words` by decide_tac
    \\ asm_simp_tac std_ss [n2w_sub,WORD_LEFT_SUB_DISTRIB,WORD_MULT_CLAUSES]
    \\ CONV_TAC wordsLib.WORD_ARITH_CONV)
  \\ rw [] \\ fs []
QED

Theorem CopyByteNew_thm:
  state_rel c l1 l2 s (t:('a,'c,'ffi) wordSem$state) NONE locs /\
  dataSem$get_vars [0;1;2] s.locals = SOME vals /\
  t.clock = MustTerminate_limit (:'a) - 1 /\
  dataSem$pop_env s = SOME s1 /\ is_env (HD s.stack) /\
  s.locals_size = lookup ByteCopyNew_location s.stack_frame_sizes /\
  do_app (MemOp (CopyByte T)) vals s1 = Rval (v,s2) ==>
  ?q r new_clock.
    evaluate (ByteCopyNew_code c,t) = (q,r) /\
    (q = SOME NotEnoughSpace ==>
      r.ffi = t.ffi /\ option_le r.stack_max s2.stack_max /\
      (c.gc_kind <> None ==> ~s2.safe_for_space)) /\
    (q <> SOME NotEnoughSpace ==>
      ?rv. q = SOME (Result (Loc l1 l2) [rv]) /\
        state_rel c r1 r2
          (s2 with <|locals := LN; locals_size := SOME 0;
                     clock := new_clock; stack := s.stack|>)
          r (SOME [(v,rv)]) locs)
Proof
  strip_tac
  \\ drule do_app_CopyByte_new_shape
  \\ disch_then (qx_choosel_then [`source_flag`,`source_ref`,`source_offset`,`copy_length`]
       strip_assume_tac)
  \\ gvs []
  \\ fs [do_app,dataSemTheory.allowed_op_def,AllCaseEqs()]
  \\ qpat_x_assum `_ = ByteArray _ _` SUBST_ALL_TAC
  \\ qmatch_asmsub_rename_tac
       `lookup source_ref s1.refs = SOME (ByteArray source_array_flag source_bytes)`
  \\ qmatch_asmsub_rename_tac
       `copy_array (source_bytes,source_offset) copy_length NONE = SOME copied_bytes`
  \\ `good_dimindex (:'a)` by fs [state_rel_thm]
  \\ drule state_rel_arch_width \\ disch_tac
  \\ `s1.refs = s.refs` by (
    qpat_x_assum `pop_env s = SOME s1` mp_tac
    \\ simp [dataSemTheory.pop_env_def,AllCaseEqs()]
    \\ rpt strip_tac \\ gvs [])
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ fs [LENGTH_EQ_NUM_compute,adjust_var_def]
  \\ ntac 3 (qpat_x_assum `_ = _::_` SUBST_ALL_TAC)
  \\ qmatch_asmsub_rename_tac
       `wordSem$get_vars [2;4;6] t = SOME [source_value;offset_value;length_value]`
  \\ qpat_assum `state_rel c l1 l2 s t NONE locs`
       (mp_tac o REWRITE_RULE [state_rel_thm])
  \\ strip_tac
  \\ full_simp_tac std_ss [APPEND,GSYM APPEND_ASSOC]
  \\ rpt_drule0 memory_rel_get_vars_IMP \\ strip_tac
  \\ fs [adjust_var_def]
  \\ qpat_x_assum `!w. get_vars [2;4;6] t = SOME w ==> _`
       (qspec_then `[source_value;offset_value;length_value]` mp_tac)
  \\ impl_tac >- ASM_REWRITE_TAC []
  \\ strip_tac \\ fs [ZIP]
  \\ `?offset len.
        source_offset = &offset /\ copy_length = &len /\
        offset < dimword (:'a) DIV 8 /\ len < dimword (:'a) DIV 8` by (
    fs [semanticPrimitivesTheory.copy_array_def,not_less_zero_int_eq]
    \\ rveq \\ fs [NOT_LESS,integerTheory.INT_ADD,integerTheory.INT_ABS_NUM]
    \\ rpt_drule0 memory_rel_ByteArray_IMP
    \\ fs [good_dimindex_def,dimword_def]
    \\ rpt strip_tac \\ fs [])
  \\ qpat_x_assum `source_offset = &offset` SUBST_ALL_TAC
  \\ qpat_x_assum `copy_length = &len` SUBST_ALL_TAC
  \\ `offset_value = Word (n2w (2 * offset)) /\
      length_value = Word (n2w (2 * len))` by (
    conj_tac \\ irule memory_rel_get_small_num
    \\ simp []
    \\ goal_assum (drule_at Any)
    \\ simp [])
  \\ qpat_x_assum `offset_value = _` SUBST_ALL_TAC
  \\ qpat_x_assum `length_value = _` SUBST_ALL_TAC
  \\ fs [get_vars_SOME_IFF,get_vars_SOME_IFF_data]
  \\ `evaluate (BignumHalt 6,t) = (NONE,t)` by (
    simp [BignumHalt_def,wordSemTheory.evaluate_def,word_exp_rw,
          wordSemTheory.get_var_imm_def,asmTheory.word_cmp_def,
          SIMP_RULE (srw_ss()) [] word_and_one_eq_0_iff,
          word_index,bitTheory.BIT0_ODD,ODD_MULT])
  \\ simp [ByteCopyNew_code_def]
  \\ once_rewrite_tac [list_Seq_def]
  \\ simp [Once wordSemTheory.evaluate_def]
  \\ `arch_bytes c.arch_width = dimindex (:'a) DIV 8` by simp [arch_size]
  \\ `2 * len < dimword (:'a) /\ len < dimword (:'a)` by (
    fs [X_LT_DIV] \\ decide_tac)
  \\ `(n2w (2 * len):'a word) >>> 1 = n2w len` by (
    rewrite_tac [GSYM w2n_11,w2n_lsr]
    \\ simp [ONCE_REWRITE_RULE [MULT_COMM] MULT_DIV])
  \\ `shift (dimindex (:'a)) - 1 < dimindex (:'a)` by
       fs [good_dimindex_def,shift_def]
  \\ once_rewrite_tac [list_Seq_def]
  \\ fs [wordSemTheory.evaluate_def,word_exp_SmallLsr,word_exp_rw,
          GSYM bytes_in_word_def]
  \\ `~(1 >= dimindex (:'a))` by fs [good_dimindex_def]
  \\ fs []
  \\ qmatch_goalsub_abbrev_tac `set_var 1 (Word allocation_size) t`
  \\ `w2n allocation_size DIV 2 = byte_len (dimindex (:'a)) len` by (
    qunabbrev_tac `allocation_size`
    \\ fs [byte_len_def,bytes_in_word_def,w2n_lsr,shift_def,
           good_dimindex_def,word_add_n2w,dimword_def]
    \\ rfs []
    \\ fs [GSYM word_add_n2w]
    \\ fs [word_add_n2w,dimword_def]
    \\ fs [ADD_DIV_EQ,DIV_DIV_DIV_MULT])
  \\ `state_rel c l1 l2 s (set_var 1 (Word allocation_size) t) NONE locs` by
       simp [wordSemTheory.set_var_def,state_rel_insert_1]
  \\ `?retained_locals. dataSem$cut_env (fromList [();();()]) s.locals =
       SOME retained_locals` by
       fs [EVAL ``sptree$fromList [();();()]``,dataSemTheory.cut_env_def,
           domain_lookup,dataSemTheory.get_var_def,get_vars_SOME_IFF_data]
  \\ qmatch_goalsub_abbrev_tac
       `AllocVar c allocation_limit (fromList [();();()])`
  \\ `allocation_limit < dimword (:'a) DIV 8` by (
    rw [Abbr `allocation_limit`,MIN_DEF]
    \\ fs [good_dimindex_def,dimword_def]
    \\ decide_tac)
  \\ `get_var 1 (set_var 1 (Word allocation_size) t) = SOME (Word allocation_size)` by
       simp [get_var_set_var_thm]
  \\ namedCases_on
       `evaluate (AllocVar c allocation_limit (fromList [();();()]),
                  set_var 1 (Word allocation_size) t)`
       ["allocation_result allocation_state"]
  \\ drule_all_then strip_assume_tac AllocVar_thm
  \\ once_rewrite_tac [list_Seq_def]
  \\ simp [Once wordSemTheory.evaluate_def]
  \\ Cases_on `allocation_result = SOME NotEnoughSpace`
  \\ fs []
  >- (
    conj_tac
    >- (
      irule option_le_trans
      \\ qexists_tac `s.stack_max`
      \\ ASM_REWRITE_TAC []
      \\ qpat_assum `_ = s2` (PURE_REWRITE_TAC o single o GSYM)
      \\ drule dataPropsTheory.pop_env_const \\ strip_tac
      \\ simp [option_le_max_right])
    \\ rpt strip_tac
    \\ qpat_assum `_ = s2` (fn result =>
      qpat_x_assum `s2.safe_for_space`
        (strip_assume_tac o SIMP_RULE (srw_ss()) [GSYM result]))
    \\ `?caller_size caller_locals caller_stack.
          s.stack = Env caller_size caller_locals :: caller_stack /\
          s1 = s with <|locals := caller_locals; stack := caller_stack;
                        locals_size := caller_size|>` by (
      qpat_x_assum `pop_env s = SOME s1` mp_tac
      \\ simp [dataSemTheory.pop_env_def,AllCaseEqs()]
      \\ rpt strip_tac \\ gvs [is_env_def])
    \\ qpat_x_assum `s1 = _` SUBST_ALL_TAC
    \\ fs [space_consumed_def]
    \\ `w2n allocation_size DIV 2 < allocation_limit` by (
      qpat_assum `w2n allocation_size DIV 2 = byte_len (dimindex (:'a)) len`
        (PURE_REWRITE_TAC o single)
      \\ rw [Abbr `allocation_limit`,MIN_DEF]
      \\ fs [limits_inv_def,arch_size_def,good_dimindex_def,dimword_def,byte_len_def]
      \\ rfs []
      \\ decide_tac)
    \\ `small_num s.limits.arch_64_bit (&offset)` by (
      fs [small_num_def,limits_inv_def,good_dimindex_def,dimword_def]
      \\ rfs [])
    \\ `retained_locals =
          fromList [RefPtr source_flag source_ref;Number (&offset);Number (&len)]` by (
      qpat_x_assum `cut_env (fromList [();();()]) s.locals = SOME retained_locals` mp_tac
      \\ simp [dataSemTheory.cut_env_def,AllCaseEqs()]
      \\ strip_tac
      \\ qpat_x_assum `_ = retained_locals`
           (PURE_REWRITE_TAC o single o GSYM)
      \\ fs [dataSemTheory.get_var_def]
      \\ simp [spt_eq_thm,lookup_mk_wf,lookup_inter_alt,lookup_fromList,domain_fromList]
      \\ qx_gen_tac `register`
      \\ Cases_on `register < 3`
      >- (
        `register = 0 \/ register = 1 \/ register = 2` by decide_tac
        \\ gvs [])
      \\ simp [])
    \\ `toList retained_locals =
         [Number (&len);RefPtr source_flag source_ref;Number (&offset)]` by (
      qpat_assum `retained_locals = _` (PURE_REWRITE_TAC o single)
      \\ EVAL_TAC)
    \\ `size_of_heap (cut_locals (fromList [();();()]) s) =
         size_of_heap_args [RefPtr source_flag source_ref;Number (&offset);Number (&len)]
           (s with <|locals := caller_locals;stack := caller_stack;
                     locals_size := caller_size|>)` by (
      gvs []
      \\ simp [cut_locals_def,size_of_heap_def,size_of_heap_args_def,
            stack_to_vs_def,extract_stack_def,APPEND_ASSOC,size_of_Number_head]
      \\ once_rewrite_tac [size_of_cons]
      \\ simp [size_of_Number_head])
    \\ qpat_x_assum `w2n allocation_size DIV 2 < allocation_limit ==> _`
         (drule_then assume_tac)
    \\ gvs [limits_inv_def,arch_size_def,good_dimindex_def,dimword_def,byte_len_def]
    \\ decide_tac)
  \\ qmatch_asmsub_abbrev_tac
    `state_rel c l1 l2 allocated_source allocation_state NONE locs`
  \\ drule_then assume_tac cut_env_IMP_lookup_EQ
  \\ `dataSem$get_vars [0;1;2] allocated_source.locals =
       SOME [RefPtr source_flag source_ref;Number (&offset);Number (&len)]` by
       fs [Abbr `allocated_source`,get_vars_SOME_IFF_data,
           dataSemTheory.get_var_def,domain_fromList]
  \\ drule_all_then (qx_choose_then `allocated_values` strip_assume_tac)
       state_rel_get_vars_IMP
  \\ fs [LENGTH_EQ_NUM_compute,adjust_var_def]
  \\ ntac 3 (qpat_x_assum `_ = _::_` SUBST_ALL_TAC)
  \\ qmatch_asmsub_rename_tac
       `get_vars [2;4;6] allocation_state =
         SOME [allocated_source_value;allocated_offset_value;allocated_length_value]`
  \\ qpat_assum `state_rel c l1 l2 allocated_source allocation_state NONE locs`
       (mp_tac o REWRITE_RULE [state_rel_thm])
  \\ strip_tac
  \\ full_simp_tac std_ss [APPEND,GSYM APPEND_ASSOC]
  \\ rpt_drule0 memory_rel_get_vars_IMP \\ strip_tac
  \\ fs [adjust_var_def]
  \\ qpat_x_assum `!w. get_vars [2;4;6] allocation_state = SOME w ==> _`
       (qspec_then `[allocated_source_value;allocated_offset_value;allocated_length_value]` mp_tac)
  \\ impl_tac >- ASM_REWRITE_TAC []
  \\ strip_tac \\ fs [ZIP]
  \\ ntac 2 (qpat_x_assum `memory_rel _ _ _ _ _ _ t.memory _ _` kall_tac)
  \\ `allocated_offset_value = Word (n2w (2 * offset)) /\
      allocated_length_value = Word (n2w (2 * len))` by (
    conj_tac \\ irule memory_rel_get_small_num
    \\ simp [] \\ goal_assum (drule_at Any) \\ simp [])
  \\ qpat_x_assum `allocated_offset_value = _` SUBST_ALL_TAC
  \\ qpat_x_assum `allocated_length_value = _` SUBST_ALL_TAC
  \\ `byte_len (dimindex (:'a)) len < allocation_limit` by (
    qpat_assum `w2n allocation_size DIV 2 = byte_len (dimindex (:'a)) len`
      (PURE_REWRITE_TAC o single o GSYM)
    \\ ASM_REWRITE_TAC [])
  \\ `byte_len (dimindex (:'a)) len < 2 ** (dimindex (:'a) - 4) /\
      byte_len (dimindex (:'a)) len < 2 ** c.len_size` by (
    fs [Abbr `allocation_limit`,MIN_LT,good_dimindex_def,dimword_def,byte_len_def]
    \\ rfs [])
  \\ `byte_len (dimindex (:'a)) len < allocated_source.space` by
       simp [Abbr `allocated_source`]
  \\ `lookup source_ref allocated_source.refs =
       SOME (ByteArray source_array_flag source_bytes)` by
       simp [Abbr `allocated_source`]
  \\ qabbrev_tac `new_ref = LEAST ptr. ptr NOTIN domain s.refs`
  \\ `new_ref NOTIN domain allocated_source.refs` by
       simp [Abbr `new_ref`,Abbr `allocated_source`,LEAST_NOTIN_spt_DOMAIN]
  \\ drule memory_rel_copy_array_NONE
  \\ disch_then (qspecl_then
       [`copied_bytes`,`source_bytes`,`offset`,`new_ref`,`len`,`source_array_flag`,`T`]
       mp_tac)
  \\ impl_tac >- ASM_REWRITE_TAC []
  \\ disch_then
       (qx_choosel_then [`allocation_base`,`curr`,`source_header`,`target_header`,
                        `zero_model`,`copied_memory`,`source_word`,`target_word`]
         strip_assume_tac)
  \\ `0 < allocated_source.space` by simp [Abbr `allocated_source`]
  \\ `get_real_addr c allocation_state.store target_word = SOME allocation_base /\
         byte_aligned allocation_base` by (
    qpat_x_assum `memory_rel _ _ _ _ _ _ copied_memory _ _` kall_tac
    \\ drule_all_then ACCEPT_TAC memory_rel_next_free_addr)
  \\ `target_header = allocation_base` by (
    qpat_x_assum `get_real_addr c allocation_state.store target_word = SOME target_header`
      mp_tac
    \\ simp [])
  \\ qpat_x_assum `target_header = allocation_base` SUBST_ALL_TAC
  \\ qpat_x_assum `allocated_source_value = Word source_word` SUBST_ALL_TAC
  \\ fs [get_vars_SOME_IFF]
  \\ qpat_assum
       `memory_rel _ _ _ _ _ _ allocation_state.memory _ ((RefPtr _ _,_)::_)`
       (mp_then (Pos hd) (qspecl_then [`new_ref`,`len`,`T`] mp_tac)
         (memory_rel_RefByte_alt |> Q.INST [`w` |-> `(0w:word8)`] |>
          SIMP_RULE (srw_ss()) [w2w_def,w2n_n2w,word_of_byte_0,last_bytes_0,
                               LET_THM,LUPDATE_REPLICATE]))
  \\ impl_tac >- ASM_REWRITE_TAC []
  \\ disch_then
       (qx_choosel_then [`zero_base`,`zero_curr`,`initial_model`] strip_assume_tac)
  \\ `zero_base = allocation_base /\ zero_curr = curr /\ initial_model = zero_model`
       by gvs []
  \\ qpat_x_assum `zero_base = allocation_base` SUBST_ALL_TAC
  \\ qpat_x_assum `zero_curr = curr` SUBST_ALL_TAC
  \\ qpat_x_assum `initial_model = zero_model` SUBST_ALL_TAC
  \\ `make_ptr c (-1w * curr + allocation_base) 0w
        (byte_len (dimindex (:'a)) len) = Word target_word` by gvs []
  \\ qpat_assum `make_ptr c (-1w * curr + allocation_base) _ _ = Word target_word`
       (RULE_ASSUM_TAC o REWRITE_RULE o single)
  \\ qabbrev_tac `allocation_store = allocation_state.store |+
       (NextFree,Word (allocation_base +
          bytes_in_word * n2w (byte_len (dimindex (:'a)) len + 1)))`
  \\ `source_ref <> new_ref` by (
    spose_not_then SUBST_ALL_TAC \\ fs [domain_lookup])
  \\ `offset + len <= LENGTH source_bytes` by (
    qpat_x_assum `copy_array (source_bytes,&offset) (&len) NONE = SOME copied_bytes`
      mp_tac
    \\ simp [semanticPrimitivesTheory.copy_array_def,
             integerTheory.INT_ADD,integerTheory.INT_ABS_NUM,AllCaseEqs()])
  \\ `lookup source_ref
        (insert new_ref (ByteArray T (REPLICATE len 0w)) allocated_source.refs) =
       SOME (ByteArray source_array_flag source_bytes)` by simp [lookup_insert]
  \\ `lookup new_ref
        (insert new_ref (ByteArray T (REPLICATE len 0w)) allocated_source.refs) =
       SOME (ByteArray T (REPLICATE len 0w))` by simp [lookup_insert]
  \\ `get_real_addr c allocation_store source_word = SOME source_header /\
      get_real_addr c allocation_store target_word = SOME allocation_base` by
       fs [Abbr `allocation_store`,get_real_addr_def,FLOOKUP_UPDATE]
  \\ qpat_assum
       `memory_rel _ _ _ _ _ _ zero_model _
         ((RefPtr T new_ref,Word target_word)::(RefPtr source_flag source_ref,Word source_word)::_)`
       (assume_tac o MATCH_MP memory_rel_swap)
  \\ `byte_copy_range_inv len (source_header + bytes_in_word + n2w offset)
        (allocation_base + bytes_in_word) zero_model allocation_state.mdomain` by (
    qpat_x_assum
      `memory_rel _ _ _ _ _ _ zero_model _ ((RefPtr T new_ref,Word target_word)::_)` kall_tac
    \\ irule byte_copy_range_inv_from_arrays
    \\ simp [] \\ goal_assum (drule_at Any) \\ simp [])
  \\ qabbrev_tac `k = dimindex (:'a) DIV 8`
  \\ qabbrev_tac `payload_words = byte_len (dimindex (:'a)) len`
  \\ `0 < k /\ payload_words = len DIV k + 1` by (
    fs [Abbr `k`,Abbr `payload_words`,byte_len_def,good_dimindex_def]
    \\ fs [])
  \\ `byte_aligned (allocation_base + bytes_in_word)` by (
    irule byte_aligned_add
    \\ simp [data_to_word_memoryProofTheory.byte_aligned_bytes_in_word])
  \\ qpat_assum
       `store_list allocation_base (Word _::_) allocation_state.memory
          allocation_state.mdomain = SOME zero_model`
       (strip_assume_tac o
        SIMP_RULE (srw_ss()) [Once store_list_def,AllCaseEqs()])
  \\ qabbrev_tac `copy_initial_memory =
       byte_copy_alloc_init k payload_words (allocation_base + bytes_in_word)
         ((allocation_base =+ Word (n2w (make_byte_header c T len))) allocation_state.memory)`
  \\ `?prefix_bytes. byte_copy_align_inv k len prefix_bytes
        (source_header + bytes_in_word + n2w offset) (allocation_base + bytes_in_word)
        copy_initial_memory zero_model allocation_state.mdomain` by (
    simp [Abbr `copy_initial_memory`]
    \\ match_mp_tac byte_copy_alloc_ready
    \\ gvs [Abbr `k`])
  \\ `0 < payload_words` by decide_tac
  \\ qpat_x_assum `payload_words = len DIV k + 1` kall_tac
  \\ `c.len_size <> 0 /\ c.len_size + 9 < dimindex (:'a)` by
       drule_all_then ACCEPT_TAC memory_rel_len_size
  \\ `!j. j <= payload_words ==>
        allocation_base + n2w j * bytes_in_word IN allocation_state.mdomain` by (
    qpat_assum `store_list allocation_base (Word _::_) _ _ = SOME zero_model`
      (mp_tac o MATCH_MP store_list_domain)
    \\ simp [])
  \\ qspecl_then [`c`,`len`,`k`,`payload_words`,`allocation_state`,`allocation_base`]
       mp_tac evaluate_ByteCopyNewInit
  \\ impl_tac >- simp [Abbr `k`,Abbr `payload_words`]
  \\ disch_then (qx_choose_then `initialised_locals` strip_assume_tac)
  \\ once_rewrite_tac [list_Seq_def]
  \\ simp [Once wordSemTheory.evaluate_def]
  \\ qmatch_goalsub_abbrev_tac `wordSem$evaluate (_,initialised_state)`
  \\ `initialised_state.memory = copy_initial_memory /\
      initialised_state.store = allocation_store` by
       simp [Abbr `initialised_state`,Abbr `copy_initial_memory`,Abbr `allocation_store`]
  \\ `wordSem$get_var 0 initialised_state = SOME (Loc l1 l2) /\
        wordSem$get_var 2 initialised_state = SOME (Word source_word) /\
        wordSem$get_var 4 initialised_state = SOME (Word (n2w (2 * offset))) /\
        wordSem$get_var 6 initialised_state = SOME (Word (n2w (2 * len))) /\
        wordSem$get_var 9 initialised_state = SOME (Word allocation_base)` by
       fs [Abbr `initialised_state`,wordSemTheory.get_var_def]
  \\ `n2w k = (bytes_in_word:'a word)` by simp [Abbr `k`,bytes_in_word_def]
  \\ `shift (dimindex (:'a)) < dimindex (:'a) /\
        shift (dimindex (:'a)) < dimword (:'a)` by
       fs [good_dimindex_def,shift_def,dimword_def]
  \\ `FLOOKUP initialised_state.store CurrHeap = SOME (Word curr)` by
       simp [Abbr `allocation_store`,FLOOKUP_UPDATE]
  \\ `((1w || (allocation_base - curr) <<
         (shift_length c - shift (dimindex (:'a)))):'a word) = target_word` by (
    `allocation_base - curr = allocation_base + -1w * curr` by
         (CONV_TAC wordsLib.WORD_ARITH_CONV)
    \\ qpat_assum `allocation_base - curr = _`
         (PURE_REWRITE_TAC o single)
    \\ once_rewrite_tac [WORD_OR_COMM]
    \\ qpat_x_assum `make_ptr c _ _ _ = Word target_word`
         (mp_tac o REWRITE_RULE [make_ptr_def])
    \\ simp [])
  \\ `shift_length c - shift (dimindex (:'a)) < dimindex (:'a) /\
        shift_length c - shift (dimindex (:'a)) < dimword (:'a)` by (
    assume_tac (INST_TYPE [alpha |-> ``:'a``] dimindex_lt_dimword)
    \\ decide_tac)
  \\ once_rewrite_tac [list_Seq_def] \\ eval_tac
  \\ simp [lookup_insert,GREATER_EQ]
  \\ `2 * offset < dimword (:'a) /\ offset < dimword (:'a)` by (
    fs [X_LT_DIV] \\ decide_tac)
  \\ `(n2w (2 * offset):'a word) >>> 1 = n2w offset` by (
    rewrite_tac [GSYM w2n_11,w2n_lsr]
    \\ simp [ONCE_REWRITE_RULE [MULT_COMM] MULT_DIV])
  \\ qmatch_goalsub_abbrev_tac `wordSem$evaluate (_,address_state)`
  \\ `wordSem$get_var 0 address_state = SOME (Loc l1 l2) /\
        wordSem$get_var 4 address_state = SOME (Word (n2w (2 * offset))) /\
        wordSem$get_var 6 address_state = SOME (Word (n2w (2 * len))) /\
        wordSem$get_var 8 address_state = SOME (Word target_word) /\
        wordSem$get_var 9 address_state = SOME (Word allocation_base)` by
       simp [Abbr `address_state`,wordSemTheory.get_var_def,lookup_insert,GSYM word_mul_n2w]
  \\ `wordSem$word_exp address_state (real_addr c 2) = SOME (Word source_header)` by (
    match_mp_tac (GEN_ALL get_real_addr_lemma)
    \\ qexists_tac `source_word`
    \\ simp [Abbr `address_state`,wordSemTheory.get_var_def,lookup_insert])
  \\ once_rewrite_tac [list_Seq_def] \\ eval_tac
  \\ simp [lookup_insert,GREATER_EQ]
  \\ once_rewrite_tac [list_Seq_def] \\ eval_tac
  \\ simp [lookup_insert,GREATER_EQ]
  \\ once_rewrite_tac [list_Seq_def] \\ eval_tac
  \\ simp [lookup_insert,GREATER_EQ]
  \\ once_rewrite_tac [list_Seq_def]
  \\ qmatch_goalsub_abbrev_tac `wordSem$evaluate (_,copy_entry)`
  \\ `copy_entry.memory = copy_initial_memory /\ copy_entry.store = allocation_store /\
        copy_entry.mdomain = allocation_state.mdomain /\ copy_entry.code = allocation_state.code /\
        copy_entry.be = allocation_state.be /\ copy_entry.clock = allocation_state.clock /\
        copy_entry.stack = allocation_state.stack /\ copy_entry.stack_size = allocation_state.stack_size /\
        copy_entry.stack_max = allocation_state.stack_max` by
       simp [Abbr `copy_entry`,Abbr `address_state`,Abbr `initialised_state`]
  \\ `wordSem$get_vars [0;6;4;9;8] copy_entry =
       SOME [Loc l1 l2;Word (n2w len);Word (source_header + bytes_in_word + n2w offset);
             Word (allocation_base + bytes_in_word);Word target_word]` by
       simp [Abbr `copy_entry`,wordSemTheory.get_vars_def,wordSemTheory.get_var_def,lookup_insert]
  \\ `c.be = allocation_state.be` by drule_all_then ACCEPT_TAC memory_rel_be
  \\ `(?md. lookup ByteCopyAlign_location allocation_state.code = SOME (5,ByteCopyAlign_code c,md)) /\
       (?md. lookup ByteCopyLoop_location allocation_state.code = SOME (8,ByteCopyLoop_code c,md)) /\
       (?md. lookup ByteCopyAdd_location allocation_state.code = SOME (5,ByteCopyAdd_code,md))` by
       fs [data_to_word_gcProofTheory.code_rel_def,stubs_md_def,stubs_def,MAP_MAP_o,o_DEF]
  \\ `len + 3 <= copy_entry.clock` by (
    `4 < dimword (:'a)` by fs [good_dimindex_def,dimword_def]
    \\ simp [Abbr `allocated_source`,wordSemTheory.MustTerminate_limit_def])
  \\ `size_of_stack s.stack =
     OPTION_MAP2 $+ (size_of_stack s1.stack) s1.locals_size /\
   s1.stack_max = s.stack_max /\ s1.stack_frame_sizes = s.stack_frame_sizes` by (
    `?caller_size caller_locals caller_stack.
       s.stack = Env caller_size caller_locals :: caller_stack /\
       s1 = s with <|locals := caller_locals;stack := caller_stack;
                     locals_size := caller_size|>` by (
      qpat_x_assum `pop_env s = SOME s1` mp_tac
      \\ simp [dataSemTheory.pop_env_def,AllCaseEqs()]
      \\ rpt strip_tac \\ gvs [is_env_def])
    \\ gvs [dataSemTheory.size_of_stack_def,dataSemTheory.size_of_stack_frame_def,
             option_add_comm])
  \\ `stack_size allocation_state.stack = size_of_stack s.stack` by (
    qpat_assum `LIST_REL stack_rel allocated_source.stack allocation_state.stack`
      (mp_tac o MATCH_MP stack_rel_IMP_size_of_stack)
    \\ simp [Abbr `allocated_source`])
  \\ `s2.stack_max = OPTION_MAP2 MAX s.stack_max
       (OPTION_MAP2 $+
         (OPTION_MAP2 MAX (lookup ByteCopyNew_location s.stack_frame_sizes)
           (OPTION_MAP2 MAX (lookup ByteCopyAlign_location s.stack_frame_sizes)
             (OPTION_MAP2 MAX (lookup ByteCopyLoop_location s.stack_frame_sizes)
               (OPTION_MAP2 MAX (lookup ByteCopyAdd_location s.stack_frame_sizes) (SOME 0)))))
         (size_of_stack s.stack))` by (
    qpat_assum `_ = s2` (PURE_REWRITE_TAC o single o GSYM)
    \\ simp [])
  \\ `option_le copy_entry.stack_max s2.stack_max` by (
    irule option_le_trans \\ qexists_tac `s.stack_max`
    \\ conj_tac >- fs [Abbr `allocated_source`]
    \\ simp [option_le_max_right])
  \\ `option_le (OPTION_MAP2 $+ (stack_size copy_entry.stack)
         (lookup ByteCopyAlign_location copy_entry.stack_size)) s2.stack_max /\
       option_le (OPTION_MAP2 $+ (stack_size copy_entry.stack)
         (lookup ByteCopyLoop_location copy_entry.stack_size)) s2.stack_max /\
       option_le (OPTION_MAP2 $+ (stack_size copy_entry.stack)
         (lookup ByteCopyAdd_location copy_entry.stack_size)) s2.stack_max` by (
    fs [Abbr `allocated_source`]
    \\ PURE_REWRITE_TAC [option_le_max]
    \\ simp [option_map2_max_add,option_le_max_right,option_add_comm,option_le_add,
             ONCE_REWRITE_RULE [option_add_comm] option_le_add])
  \\ qspecl_then [`len`,`[0;6;4;9;8]`,`c`,`k`,`prefix_bytes`,
       `source_header + bytes_in_word + n2w offset`,`allocation_base + bytes_in_word`,
       `Word target_word`,`l1`,`l2`,`copy_entry`,`zero_model`,`copied_memory`,`s2.stack_max`]
       mp_tac CopyByteAlign_call
  \\ impl_tac >- gvs [Abbr `k`]
  \\ disch_then (qx_choosel_then [`remaining_clock`,`used_stack`] strip_assume_tac)
  \\ `option_le copy_entry.stack_max used_stack` by (
    qpat_assum `wordSem$evaluate (Call _ _ _ _,_) = _`
      (mp_tac o MATCH_MP wordPropsTheory.evaluate_stack_max_le)
    \\ simp [])
  \\ `option_le (stack_size allocation_state.stack) used_stack` by (
    qpat_assum `option_le (OPTION_MAP2 $+ (stack_size allocation_state.stack) _) _`
      (strip_assume_tac o MATCH_MP option_le_add_indv)
    \\ irule option_le_trans \\ qexists_tac `allocation_state.stack_max`
    \\ gvs [])
  \\ simp []
  \\ qexists_tac `remaining_clock`
  \\ `s2.ffi = s.ffi /\ s2.handler = s.handler /\ s2.code = s.code /\
        s2.compile = s.compile /\ s2.compile_oracle = s.compile_oracle /\
        s2.tstamps = s.tstamps /\ s2.global = s.global /\ s2.limits = s.limits /\
        s2.refs = insert new_ref (ByteArray T copied_bytes) s.refs /\ s2.space = 0 /\
        s2.stack_frame_sizes = s.stack_frame_sizes` by (
    `?caller_size caller_locals caller_stack.
       s.stack = Env caller_size caller_locals :: caller_stack /\
       s1 = s with <|locals := caller_locals;stack := caller_stack;
                     locals_size := caller_size|>` by (
      qpat_x_assum `pop_env s = SOME s1` mp_tac
      \\ simp [dataSemTheory.pop_env_def,AllCaseEqs()]
      \\ rpt strip_tac \\ gvs [is_env_def])
    \\ qpat_assum `_ = s2` (PURE_REWRITE_TAC o single o GSYM)
    \\ gvs [])
  \\ fs [state_rel_thm,Abbr `copy_entry`,Abbr `address_state`,Abbr `initialised_state`,
         Abbr `allocation_store`,Abbr `allocated_source`,FLOOKUP_UPDATE]
  \\ gvs [lookup_def,EVAL ``join_env LN []``,FAPPLY_FUPDATE_THM]
  \\ qpat_x_assum `memory_rel _ _ _ _ _ _ copied_memory _ _` mp_tac
  \\ match_mp_tac memory_rel_rearrange
  \\ simp [] \\ rpt strip_tac \\ fs []
QED

Theorem do_app_CopyByte_new_stack[local]:
  do_app (MemOp (CopyByte T)) vals s = Rval (v,s2) ==>
  s2.stack_max = OPTION_MAP2 MAX s.stack_max
    (OPTION_MAP2 $+
      (stack_consumed s.stack_frame_sizes s.limits (MemOp (CopyByte T)) vals)
      (OPTION_MAP2 $+ (size_of_stack s.stack) s.locals_size)) /\
  do_app (MemOp (CopyByte T)) vals (s with stack_max := s2.stack_max) = Rval (v,s2)
Proof
  strip_tac
  \\ drule do_app_CopyByte_new_shape
  \\ disch_then (qx_choosel_then [`flag`,`source_ref`,`offset`,`len`] strip_assume_tac)
  \\ gvs [do_app,dataSemTheory.allowed_op_def,AllCaseEqs()]
  \\ simp [dataSemTheory.state_component_equality,size_of_heap_args_def,
           space_consumed_def,stack_to_vs_def]
QED

Theorem state_rel_bound_stack_max[local]:
  state_rel c l1 l2 s (t:('a,'c,'ffi) wordSem$state) result locs /\
  option_le s.stack_max bound ==>
  state_rel c l1 l2 (s with <|stack_max := bound;safe_for_space := safe|>) t result locs
Proof
  rw [state_rel_thm]
  \\ irule option_le_trans \\ qexists_tac `s.stack_max` \\ simp []
QED

Theorem call_env_push_env_dec_clock_lift[local]:
  call_env (args:'a word_loc list) b (push_env (y1,y2) NONE
    (wordSem$dec_clock ((t:('a,'c,'ffi) wordSem$state) with <|clock := ck'; termdep := tp|>))) =
  (call_env args b (push_env (y1,y2) NONE t)) with
    <|clock := ck' - 1; termdep := tp|>
Proof
  simp [wordSemTheory.dec_clock_def, wordSemTheory.call_env_def,
        wordSemTheory.push_env_def]
  \\ pairarg_tac \\ fs []
  \\ simp [wordSemTheory.state_component_equality]
QED

Theorem assign_CopyByte_new:
  op = MemOp (CopyByte T) ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ gvs []
  \\ drule do_app_CopyByte_new_shape
  \\ disch_then
       (qx_choosel_then [`source_flag`,`source_ref`,`source_offset`,`copy_length`] strip_assume_tac)
  \\ gvs []
  \\ `names_opt <> NONE` by fs [dataLangTheory.op_requires_names_def]
  \\ namedCases_on `names_opt` ["","kept_names"] \\ gvs []
  \\ qmatch_asmsub_rename_tac `cut_state_opt (SOME kept_names) s = SOME caller_source`
  \\ drule_all state_rel_cut_state_opt_SOME
  \\ disch_then (qx_choosel_then [`saved_locals`,`word_args`] strip_assume_tac)
  \\ gvs [LENGTH_EQ_NUM_compute]
  \\ qmatch_asmsub_rename_tac
       `dataSem$get_vars [a1;a2;a3] s.locals =
          SOME [RefPtr source_flag source_ref;Number source_offset;Number copy_length]`
  \\ qmatch_asmsub_rename_tac
       `wordSem$get_vars [adjust_var a1;adjust_var a2;adjust_var a3] t =
          SOME [source_value;offset_value;length_value]`
  \\ `dataSem$cut_env kept_names s.locals = SOME caller_source.locals /\
        caller_source = s with locals := caller_source.locals` by (
    qpat_x_assum `cut_state_opt (SOME kept_names) s = SOME caller_source` mp_tac
    \\ simp [dataSemTheory.cut_state_opt_def,dataSemTheory.cut_state_def,AllCaseEqs()]
    \\ rpt strip_tac \\ gvs [])
  \\ drule cut_env_IMP_cut_envs
  \\ disch_then (qx_choosel_then [`saved_non_gc`,`saved_gc`] strip_assume_tac)
  \\ `t.termdep <> 0` by decide_tac
  \\ `t.stack_size = s.stack_frame_sizes` by fs [state_rel_thm]
  \\ `?md. lookup ByteCopyNew_location t.code = SOME (4,ByteCopyNew_code c,md)` by
       fs [state_rel_thm,data_to_word_gcProofTheory.code_rel_def,
           stubs_md_def,stubs_def,MAP_MAP_o,o_DEF]
  \\ qabbrev_tac `clocked_source = s with clock := MustTerminate_limit (:'a)`
  \\ qabbrev_tac `clocked_word = t with
       <|clock := MustTerminate_limit (:'a);termdep := t.termdep - 1|>`
  \\ `state_rel c l1 l2 clocked_source clocked_word NONE locs` by
       gvs [Abbr `clocked_source`,Abbr `clocked_word`,state_rel_thm]
  \\ qabbrev_tac `data_callee = dataSem$call_env
       [RefPtr source_flag source_ref;Number source_offset;Number copy_length]
       (lookup ByteCopyNew_location t.stack_size)
       (dataSem$push_env caller_source.locals F (dataSem$dec_clock clocked_source))`
  \\ qabbrev_tac `word_callee = wordSem$call_env
       [Loc n l;source_value;offset_value;length_value]
       (lookup ByteCopyNew_location t.stack_size)
       (wordSem$push_env (saved_non_gc,saved_gc) NONE (wordSem$dec_clock clocked_word))`
  \\ `state_rel c n l data_callee word_callee NONE ((l1,l2)::locs)` by (
    simp [Abbr `data_callee`,Abbr `word_callee`]
    \\ irule (state_rel_call_env_push_env |> Q.SPEC `NONE` |> SIMP_RULE std_ss []
         |> Q.INST [`r` |-> `kept_names`,`args` |-> `[a1;a2;a3]`])
    \\ conj_tac >- (
      qexistsl_tac [`a1`,`a2`,`a3`]
      \\ simp [Abbr `clocked_source`,Abbr `clocked_word`])
    \\ conj_tac >- (
      qexists_tac `kept_names`
      \\ simp [Abbr `clocked_source`,Abbr `clocked_word`])
    \\ simp [])
  \\ drule do_app_CopyByte_new_stack \\ strip_tac
  \\ drule cut_state_opt_SOME_eq \\ disch_tac
  \\ qpat_x_assum `caller_source = s with locals := caller_source.locals` kall_tac
  \\ `option_le data_callee.stack_max s2.stack_max` by (
    gvs [Abbr `data_callee`,Abbr `clocked_source`,dataSemTheory.call_env_def,
         dataSemTheory.push_env_def,dataSemTheory.dec_clock_def,
         dataSemTheory.size_of_stack_def,dataSemTheory.size_of_stack_frame_def]
    \\ PURE_REWRITE_TAC [option_le_max]
    \\ simp [option_map2_max_add,option_le_max_right,option_add_comm,option_le_add,
             ONCE_REWRITE_RULE [option_add_comm] option_le_add,stack_consumed_def])
  \\ qabbrev_tac `native_source = data_callee with
       <|stack_max := s2.stack_max;safe_for_space := caller_source.safe_for_space|>`
  \\ `state_rel c n l native_source word_callee NONE ((l1,l2)::locs)` by (
    simp [Abbr `native_source`]
    \\ irule state_rel_bound_stack_max \\ gvs [])
  \\ `word_callee.clock = MustTerminate_limit (:'a) - 1` by
       gvs [state_rel_thm,Abbr `native_source`,Abbr `data_callee`,Abbr `clocked_source`,
            dataSemTheory.call_env_def,dataSemTheory.push_env_def,dataSemTheory.dec_clock_def]
  \\ `dataSem$get_vars [0;1;2] native_source.locals =
       SOME [RefPtr source_flag source_ref;Number source_offset;Number copy_length]` by
       simp [Abbr `native_source`,Abbr `data_callee`,dataSemTheory.call_env_def,
             dataSemTheory.get_vars_def,dataSemTheory.get_var_def,lookup_fromList]
  \\ `is_env (HD native_source.stack)` by
       simp [Abbr `native_source`,Abbr `data_callee`,dataSemTheory.call_env_def,
             dataSemTheory.push_env_def,is_env_def]
  \\ `native_source.locals_size = lookup ByteCopyNew_location native_source.stack_frame_sizes` by
       simp [Abbr `native_source`,Abbr `data_callee`,Abbr `clocked_source`,
             dataSemTheory.call_env_def,dataSemTheory.push_env_def,dataSemTheory.dec_clock_def]
  \\ `dataSem$pop_env native_source = SOME (caller_source with
       <|stack_max := s2.stack_max;clock := MustTerminate_limit (:'a) - 1|>)` by
       gvs [Abbr `native_source`,Abbr `data_callee`,Abbr `clocked_source`,
            dataSemTheory.call_env_def,dataSemTheory.push_env_def,dataSemTheory.dec_clock_def,
            dataSemTheory.pop_env_def,dataSemTheory.state_component_equality]
  \\ `do_app (MemOp (CopyByte T))
       [RefPtr source_flag source_ref;Number source_offset;Number copy_length]
       (caller_source with <|stack_max := s2.stack_max;clock := MustTerminate_limit (:'a) - 1|>) =
       Rval (v,s2 with clock := MustTerminate_limit (:'a) - 1)` by (
    qpat_assum `do_app (MemOp (CopyByte T)) _ caller_source = Rval (v,s2)`
      (ACCEPT_TAC o SIMP_RULE (srw_ss()) [] o CONJUNCT2 o
       MATCH_MP do_app_CopyByte_new_stack o
       Q.INST [`ck` |-> `MustTerminate_limit (:'a) - 1`] o
       MATCH_MP dataPropsTheory.do_app_change_clock))
  \\ drule_all_then
       (qx_choosel_then [`native_result`,`native_state`,`native_clock`] strip_assume_tac)
       (CopyByteNew_thm |> Q.INST [`r1` |-> `l1`,`r2` |-> `l2`])
  \\ `word_callee.ffi = t.ffi` by
       gvs [state_rel_thm,Abbr `native_source`,Abbr `data_callee`,Abbr `clocked_source`,
            dataSemTheory.call_env_def,dataSemTheory.push_env_def,dataSemTheory.dec_clock_def]
  \\ `lookup 0 saved_non_gc = SOME (Loc l1 l2)` by (
    qunabbrev_tac `word_callee`
    \\ drule_all_then ACCEPT_TAC state_rel_push_env_loc)
  \\ `MustTerminate_limit (:'a) <> 0` by simp [wordSemTheory.MustTerminate_limit_def]
  \\ fs [assign_def,assign_CopyByte_def,wordSemTheory.evaluate_def,
         wordSemTheory.bad_dest_args_def,wordSemTheory.find_code_def,wordSemTheory.add_ret_loc_def,
         get_names_def,domain_adjust_sets,Abbr `word_callee`,Abbr `clocked_word`]
  \\ qpat_assum `t.stack_size = s.stack_frame_sizes`
       (RULE_ASSUM_TAC o REWRITE_RULE o single)
  \\ simp []
  \\ Cases_on `native_result = SOME NotEnoughSpace` \\ fs []
  >- gvs []
  \\ qmatch_asmsub_rename_tac
       `state_rel c n l _ native_state (SOME [(v,copy_result_word)]) ((l1,l2)::locs)`
  \\ qmatch_asmsub_abbrev_tac
       `state_rel c n l copy_return_source native_state
          (SOME [(v,copy_result_word)]) ((l1,l2)::locs)`
  \\ `s2.stack = s.stack /\ s2.locals = inter s.locals kept_names /\ s2.clock = t.clock` by (
    qpat_assum `do_app (MemOp (CopyByte T)) _
       (s with locals := inter s.locals kept_names) = Rval (v,s2)`
      (strip_assume_tac o MATCH_MP dataPropsTheory.do_app_const)
    \\ gvs [state_rel_thm])
  \\ `s2.locals_size = s.locals_size` by (
    qpat_x_assum `do_app (MemOp (CopyByte T)) _
       (s with locals := inter s.locals kept_names) = Rval (v,s2)` mp_tac
    \\ simp [do_app,dataSemTheory.allowed_op_def,AllCaseEqs()]
    \\ rpt strip_tac \\ gvs [])
  \\ `dataSem$pop_env copy_return_source = SOME (s2 with clock := native_clock)` by
       gvs [Abbr `copy_return_source`,Abbr `native_source`,Abbr `data_callee`,Abbr `clocked_source`,
            dataSemTheory.call_env_def,dataSemTheory.push_env_def,dataSemTheory.dec_clock_def,
            dataSemTheory.pop_env_def,dataSemTheory.state_component_equality]
  \\ qpat_assum `state_rel c n l copy_return_source native_state
       (SOME [(v,copy_result_word)]) ((l1,l2)::locs)`
       (fn relation => qpat_assum
         `dataSem$pop_env copy_return_source = SOME (s2 with clock := native_clock)`
         (fn popped => mp_tac (MATCH_MP
           (Q.INST [`q1` |-> `dest`] state_rel_pop_env_set_var_IMP) (CONJ relation popped))))
  \\ disch_then
       (qx_choosel_then [`restored_word`,`saved_label1`,`saved_label2`,`saved_locs`] strip_assume_tac)
  \\ gvs [set_vars_sing]
  \\ `domain restored_word.locals = domain saved_non_gc UNION domain saved_gc` by (
    qpat_assum `wordSem$evaluate (ByteCopyNew_code c,_) = _`
      (assume_tac o REWRITE_RULE [call_env_push_env_dec_clock_lift])
    \\ drule_all_then (ACCEPT_TAC o CONJUNCT1) evaluate_IMP_domain_union)
  \\ gvs [state_rel_thm,dataSemTheory.set_var_def,wordSemTheory.set_var_def]
QED

Theorem evaluate_StringCmpLoop:
  ∀a1 a2 r1 r2 len be ck dm m l1 l2 (t1:('a,'c,'ffi) wordSem$state) x1 x2.
    word_str_cmp_loop a1 a2 r1 r2 len dm m be ck = SOME (x1,x2) ∧
    t1.memory = m ∧ t1.mdomain = dm ∧ be = t1.be ∧
    ck < t1.clock ∧ good_dimindex (:'a) ∧
    arch_width_bits c.arch_width = dimindex (:'a) ∧
    (?md. lookup StringCmpLoop_location t1.code = SOME (6,StringCmpLoop_code c,md)) ∧
    get_var 0 t1 = SOME (Loc l1 l2) ∧
    get_var 2 t1 = SOME (Word a1) ∧
    get_var 4 t1 = SOME (Word a2) ∧
    get_var 6 t1 = SOME (Word len) ∧
    get_var 8 t1 = SOME (Word r1) ∧
    get_var 10 t1 = SOME (Word r2) ⇒
    ∃ck max_stack.
      evaluate (StringCmpLoop_code c,t1) =
      (SOME (Result (Loc l1 l2) [Word x1; Word x2]),
       t1 with <| clock := ck; stack_max := max_stack;
                  locals := LN; locals_size := SOME 0 |>) ∧
      (max_stack ≠ t1.stack_max ⇒
       max_stack = OPTION_MAP2 MAX t1.stack_max
                     (OPTION_MAP2 $+ (stack_size t1.stack)
                        (lookup StringCmpLoop_location t1.stack_size)))
Proof
  Induct_on ‘ck’ \\ gvs []
  \\ simp [Once word_str_cmp_loop_def]
  \\ rewrite_tac [StringCmpLoop_code_def]
  \\ rpt gen_tac
  \\ IF_CASES_TAC
  >-
   (strip_tac \\ gvs []
    \\ gvs [eq_eval,wordSemTheory.flush_state_def,
            wordSemTheory.state_component_equality])
  \\ simp [CaseEq"option"] \\ rpt strip_tac
  \\ simp [eq_eval]
  \\ fs [GSYM StringCmpLoop_code_def]
  \\ rewrite_tac [list_Seq_def]
  \\ simp [eq_eval,wordSemTheory.inst_def]
  \\ gvs [wordSemTheory.get_var_def,lookup_insert]
  \\ gvs [wordSemTheory.word_cmp_def,asmTheory.word_cmp_def]
  \\ simp [w2w_def]
  \\ ‘w2n b1 < dimword (:'a) ∧ w2n b2 < dimword (:'a)’ by
    (rw [] \\ irule LESS_TRANS
     \\ irule_at Any w2n_lt
     \\ gvs [good_dimindex_def,dimword_def])
  \\ gvs []
  \\ IF_CASES_TAC \\ gvs [lookup_insert]
  >- gvs [eq_eval,wordSemTheory.flush_state_def,
          wordSemTheory.state_component_equality,w2w_def]
  \\ qmatch_goalsub_abbrev_tac ‘evaluate (StringCmpLoop_code c, t2)’
  \\ ‘t1.mdomain = t2.mdomain ∧ t1.memory = t2.memory ∧ t1.be = t2.be’
        by (unabbrev_all_tac \\ gvs [])
  \\ gvs [] \\ last_x_assum drule
  \\ gvs [] \\ disch_then $ qspecl_then [‘l1’,‘l2’] mp_tac
  \\ impl_tac >- simp [Abbr‘t2’,lookup_insert]
  \\ strip_tac \\ gvs []
  \\ qunabbrev_tac ‘t2’
  \\ simp_tac (srw_ss()) [wordSemTheory.state_component_equality]
  \\ simp [] \\ fs []
QED

Theorem evaluate_AssignCmp:
  evaluate (AssignCmp dest cmp v1 v2,s) =
    case (get_var v1 s, get_var v2 s) of
    | (SOME (Word x1), SOME (Word x2)) =>
        (NONE, set_var dest (if num_cmp cmp (w2n x1) (w2n x2) then Word 2w else Word 0w) s)
    | _ => evaluate (AssignCmp dest cmp v1 v2,s)
Proof
  Cases_on ‘get_var v1 s’ \\ gvs [] \\ Cases_on ‘x’ \\ gvs []
  \\ Cases_on ‘get_var v2 s’ \\ gvs [] \\ Cases_on ‘x’ \\ gvs []
  \\ Cases_on ‘cmp’ \\ gvs [eq_eval,AssignCmp_def,SetBool_def]
  \\ gvs [WORD_LO] \\ rw [] \\ gvs []
QED

Theorem evaluate_StringCmpMin[local]:
  evaluate (Seq (Assign 9 (Var 5))
                (Seq (If Lower 7 (Reg 5) (Assign 9 (Var 7)) Skip) p),
            t1 with locals := l) =
  case (lookup 5 l, lookup 7 l) of
  | (SOME (Word w1), SOME (Word w2)) =>
      evaluate (p,t1 with locals := insert 9 (Word (n2w (MIN (w2n w1) (w2n w2)))) l)
  | _ =>
      evaluate (Seq (Assign 9 (Var 5))
                    (Seq (If Lower 7 (Reg 5) (Assign 9 (Var 7)) Skip) p),
                t1 with locals := l)
Proof
  Cases_on ‘lookup 5 l’ \\ gvs [] \\ Cases_on ‘x’ \\ gvs []
  \\ Cases_on ‘lookup 7 l’ \\ gvs [] \\ Cases_on ‘x’ \\ gvs []
  \\ gvs [eq_eval,WORD_LO,MIN_DEF]
  \\ simp [Once insert_insert]
  \\ Cases_on ‘w2n c = w2n c'’ >- fs [] \\ simp []
  \\ Cases_on ‘w2n c < w2n c'’ \\ simp []
  \\ ‘w2n c' < w2n c’ by decide_tac \\ gvs []
QED

Theorem assign_StringCmp:
  (∃b cmp. op = MemOp (StringCmp b cmp)) ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ imp_res_tac state_rel_arch_width \\ drule0 (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ ‘names_opt ≠ NONE’ by (qpat_x_assum ‘op_requires_names _ ⇎ _’ mp_tac \\ EVAL_TAC \\ simp [])
  \\ gvs [GSYM IS_SOME_EQ_NOT_NONE,IS_SOME_EXISTS]
  \\ rename [‘cut_state_opt (SOME kept_names) s’]
  \\ drule_all state_rel_cut_state_opt_SOME \\ strip_tac
  \\ qpat_x_assum ‘_ (t with locals := y) NONE locs’ $ ASSUME_NAMED_TAC "with_locals"
  \\ qpat_x_assum `_  s t NONE locs`$ ASSUME_NAMED_TAC "old"
  \\ fs[do_app,dataSemTheory.allowed_op_def] \\ clean_tac
  \\ imp_res_tac get_vars_IMP_LENGTH
  \\ gvs [AllCaseEqs()]
  \\ gvs [LENGTH_EQ_NUM_compute]
  \\ qmatch_asmsub_rename_tac ‘get_vars [a1; a2] s.locals = SOME [RefPtr s1_b s1; RefPtr s2_b s2]’
  \\ ‘x.refs = s.refs’ by
       (qpat_x_assum ‘cut_state_opt _ _ = SOME x’ mp_tac
        \\ simp [dataSemTheory.cut_state_opt_def, dataSemTheory.cut_state_def, AllCaseEqs()]
        \\ rw [] \\ simp [])
  \\ fs []
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ LABEL_ASSUM "old" (assume_tac o REWRITE_RULE [state_rel_thm])
  \\ full_simp_tac std_ss [APPEND, GSYM APPEND_ASSOC]
  \\ rpt_drule0 memory_rel_get_vars_IMP \\ strip_tac
  \\ ‘good_dimindex (:'a) ∧ shift_length c < dimindex (:α)’ by fs [state_rel_thm]
  \\ drule_all memory_rel_str_cmp
  \\ disch_then $ qspecl_then [‘cmp’,‘b’] strip_assume_tac \\ gvs []
  \\ Cases_on ‘b’ \\ gvs []
  >- (simp [assign_def, arg2_def, assign_StringCmp_def]
  \\ qpat_x_assum ‘word_str_cmp T _ _ t.mdomain t.memory t.be c = SOME (r1,r2)’ mp_tac
  \\ simp [word_str_cmp_def]
  \\ Cases_on ‘t.memory a1'’ \\ gvs [isWord_def,theWord_def]
  \\ Cases_on ‘t.memory a2'’ \\ gvs [isWord_def,theWord_def]
  \\ qabbrev_tac ‘sh_len = dimindex (:α) − (c.len_size + shift (dimindex (:α)))’
  \\ strip_tac \\ pop_assum mp_tac
  \\ simp [Once list_Seq_def, wordSemTheory.evaluate_def]
  \\ gvs [wordSemTheory.get_vars_def,CaseEq"option"]
  \\ qpat_x_assum ‘get_var (adjust_var a1) t = SOME _’ assume_tac
  \\ ‘shift_length c < dimindex (:α)’ by fs [state_rel_thm]
  \\ dxrule_then drule_all get_var_get_real_addr_lemma
  \\ full_simp_tac std_ss [wordSemTheory.get_var_def]
  \\ dxrule_then drule_all word_exp_real_addr
  \\ rpt strip_tac
  \\ simp [Once list_Seq_def, wordSemTheory.evaluate_def]
  \\ simp [wordSemTheory.set_var_def]
  \\ rpt $ qpat_x_assum ‘get_real_addr c t.store _ = SOME _’ kall_tac
  \\ ntac 2 $ once_rewrite_tac [list_Seq_def]
  \\ ‘sh_len < dimindex (:α)’ by (unabbrev_all_tac \\ gvs [good_dimindex_def,shift_def])
  \\ `sh_len < dimword (:'a)` by (assume_tac dimindex_lt_dimword \\ decide_tac)
  \\ simp [eq_eval,word_sh_def]
  \\ ‘(?md. lookup StringCmpLoop_location t.code = SOME (6, StringCmpLoop_code c,md))’ by
       (fs [state_rel_def,code_rel_def,stubs_md_def,stubs_def,MAP_MAP_o,o_DEF])
  \\ simp [Once list_Seq_def, eq_eval]
  \\ reverse IF_CASES_TAC \\ gvs []
  >- (* fast path: lengths differ, no Call, compare directly via AssignCmp *)
   (simp [list_Seq_def]
    \\ once_rewrite_tac [evaluate_AssignCmp]
    \\ simp [wordSemTheory.get_var_def,lookup_insert]
    \\ gvs [state_rel_thm,wordSemTheory.set_var_def,set_var_def,lookup_insert]
    \\ rw []
    >- (rewrite_tac [option_le_max_right] \\ disj1_tac \\ first_assum ACCEPT_TAC)
    \\ fs [inter_insert_ODD_adjust_set]
    \\ rewrite_tac [GSYM APPEND_ASSOC,APPEND]
    \\ irule memory_rel_insert \\ rewrite_tac [APPEND]
    \\ irule memory_rel_Boolv \\ simp []
    \\ ‘x.tstamps = s.tstamps ∧ x.space = s.space ∧ x.global = s.global ∧ x.stack = s.stack’ by
         (qpat_x_assum ‘cut_state_opt _ _ = SOME x’ mp_tac
          \\ simp [dataSemTheory.cut_state_opt_def, dataSemTheory.cut_state_def, AllCaseEqs()]
          \\ rw [] \\ simp [])
    \\ qpat_x_assum ‘x.tstamps = s.tstamps’ (fn th => rewrite_tac [th])
    \\ qpat_x_assum ‘x.space = s.space’ (fn th => rewrite_tac [th])
    \\ qpat_x_assum ‘x.global = s.global’ (fn th => rewrite_tac [th])
    \\ qpat_x_assum ‘x.stack = s.stack’ (fn th => rewrite_tac [th])
    \\ qpat_x_assum ‘memory_rel _ _ _ _ _ _ _ _ (join_env s.locals _ ++ _)’ mp_tac
    \\ match_mp_tac memory_rel_rearrange
    \\ ‘x.locals = mk_wf (inter s.locals kept_names)’ by
         (imp_res_tac cut_state_opt_SOME_eq \\ asm_rewrite_tac [] \\ simp [])
    \\ simp [SF DNF_ss]
    \\ rpt strip_tac \\ disj1_tac
    \\ gvs [join_env_def, MEM_MAP, MEM_FILTER, EXISTS_PROD, MEM_toAList, lookup_inter, AllCaseEqs()]
    \\ qexists_tac ‘p_1’
    \\ qpat_x_assum ‘lookup p_1 (adjust_set (inter s.locals kept_names)) = SOME ()’ mp_tac
    \\ simp [lookup_adjust_set, domain_inter, AllCaseEqs(), domain_lookup]
    \\ rw []
    \\ qpat_x_assum ‘lookup _ (inter s.locals kept_names) = SOME _’ mp_tac
    \\ simp [lookup_inter, AllCaseEqs()] \\ rw [] \\ simp [])
  (* slow path: StringCmpLoop Call *)
  \\ simp [list_Seq_def,eq_eval]
  \\ drule cut_env_IMP_cut_envs \\ strip_tac \\ fs [get_names_def]
  \\ simp [eq_eval,cut_envs_adjust_sets_insert_ODD,domain_adjust_sets]
  \\ Cases_on ‘env_to_list y2 t.permute’
  \\ simp [wordSemTheory.push_env_def]
  \\ qmatch_goalsub_abbrev_tac ‘evaluate (StringCmpLoop_code c,t1)’
  \\ rename [‘insert 0 (Loc rl1 rl2) LN’]
  \\ drule evaluate_StringCmpLoop
  \\ disch_then $ qspecl_then [‘c’,‘rl1’,‘rl2’,‘t1’] mp_tac
  \\ impl_tac
  >-
   (simp [Abbr‘t1’,wordSemTheory.get_var_def,lookup_insert]
    \\ rewrite_tac [wordSemTheory.MustTerminate_limit_def]
    \\ ‘dimword (:α) < 2 * dimword (:α) ∧ 10 < dimword (:α)’ by gvs [good_dimindex_def,dimword_def]
    \\ decide_tac)
  \\ strip_tac \\ simp []
  \\ simp [Abbr‘t1’,wordSemTheory.pop_env_def]
  \\ reverse $ IF_CASES_TAC
  >-
   (qsuff_tac ‘F’ >- rewrite_tac []
    \\ fs [domain_union,domain_fromAList_toAList]
    \\ pop_assum mp_tac \\ drule env_to_list_domain
    \\ simp_tac std_ss [AC UNION_COMM UNION_ASSOC])
  \\ simp [wordSemTheory.set_vars_def,alist_insert_def]
  \\ qpat_x_assum ‘evaluate (StringCmpLoop_code c,_) = _’ kall_tac
  \\ fs [] \\ rpt var_eq_tac
  \\ once_rewrite_tac [evaluate_AssignCmp]
  \\ simp [wordSemTheory.get_var_def,lookup_insert]
  \\ simp [list_Seq_def,eq_eval]
  (* final part: proving state_rel *)
  \\ qpat_x_assum ‘state_rel c l1 l2 x t NONE locs’ mp_tac
  \\ simp [state_rel_thm,dataSemTheory.set_var_def,lookup_insert]
  \\ strip_tac \\ pop_assum kall_tac
  \\ ‘x.stack = s.stack ∧ x.stack_max = s.stack_max ∧ x.locals_size = s.locals_size ∧
      x.stack_frame_sizes = s.stack_frame_sizes ∧ x.limits = s.limits ∧
      x.safe_for_space = s.safe_for_space ∧ x.tstamps = s.tstamps ∧
      x.space = s.space ∧ x.global = s.global’ by
       (qpat_x_assum ‘cut_state_opt _ _ = SOME x’ mp_tac
        \\ simp [dataSemTheory.cut_state_opt_def, dataSemTheory.cut_state_def, AllCaseEqs()]
        \\ rw [] \\ simp [])
  \\ conj_tac >-
   (drule_all cut_envs_lookup_0 \\ simp [lookup_union,lookup_fromAList,ALOOKUP_toAList])
  \\ conj_tac >-
   (gen_tac \\ IF_CASES_TAC \\ asm_simp_tac std_ss [adjust_var_11]
    \\ ‘dataSem$cut_env kept_names s.locals = SOME x.locals’ by
         (qpat_x_assum ‘cut_state_opt _ _ = SOME x’ mp_tac
          \\ simp [dataSemTheory.cut_state_opt_def, dataSemTheory.cut_state_def, AllCaseEqs()]
          \\ rw [] \\ simp [])
    \\ full_simp_tac std_ss [IS_SOME_lookup,domain_union] \\ strip_tac
    \\ drule_all IN_adjust_var_lemma \\ simp [])
  \\ qpat_x_assum ‘x.stack = s.stack’ (fn th => rewrite_tac [th])
  \\ qpat_x_assum ‘x.stack_max = s.stack_max’ (fn th => rewrite_tac [th])
  \\ qpat_x_assum ‘x.locals_size = s.locals_size’ (fn th => rewrite_tac [th])
  \\ qpat_x_assum ‘x.stack_frame_sizes = s.stack_frame_sizes’ (fn th => rewrite_tac [th])
  \\ ‘stack_size t.stack = size_of_stack s.stack’ by
       (irule stack_rel_IMP_size_of_stack \\ first_assum (irule_at Any))
  \\ pop_assum (fn th => rewrite_tac [GSYM th])
  \\ qpat_x_assum ‘t.stack_size = s.stack_frame_sizes’ (fn th => full_simp_tac std_ss [th])
  \\ qmatch_asmsub_abbrev_tac ‘max_stack ≠ BB ⇒ max_stack = OPTION_MAP2 MAX BB XX’
  \\ ‘max_stack = BB’ by
       (Cases_on ‘max_stack = BB’ >- asm_rewrite_tac []
        \\ first_x_assum drule \\ strip_tac
        \\ ‘OPTION_MAP2 MAX BB XX = BB’ by (qunabbrev_tac ‘BB’ \\ rewrite_tac [OPTION_MAP2_MAX_CANCEL])
        \\ fs [])
  \\ pop_assum (fn th => rewrite_tac [th])
  \\ conj_tac >-
   (qunabbrev_tac ‘BB’ \\ rewrite_tac [stack_size_eq]
    \\ simp [option_le_max_right,option_le_add,option_add_comm])
  \\ conj_tac >-
   (qunabbrev_tac ‘BB’ \\ qunabbrev_tac ‘XX’ \\ rewrite_tac [stack_size_eq]
    \\ ‘x.stack_frame_sizes = s.stack_frame_sizes’ by fs []
    \\ ‘x.locals_size = s.locals_size’ by fs []
    \\ ntac 2 (pop_assum (fn th => rewrite_tac [th]))
    \\ rewrite_tac [option_le_max,option_le_max_right]
    \\ rpt conj_tac
    >- (disj1_tac \\ first_assum ACCEPT_TAC)
    >- (disj2_tac \\ metis_tac [option_add_comm,option_le_add])
    >- (disj2_tac \\ metis_tac [option_add_comm,option_le_refl]))
  (* memory_rel *)
  \\ fs [inter_insert_ODD_adjust_set]
  \\ rewrite_tac [GSYM APPEND_ASSOC,APPEND]
  \\ irule memory_rel_insert \\ rewrite_tac [APPEND]
  \\ irule memory_rel_Boolv \\ simp []
  \\ qpat_x_assum ‘_ t.mdomain _’ mp_tac
  \\ match_mp_tac memory_rel_rearrange
  \\ ‘cut_env kept_names s.locals = SOME x.locals’ by
       (qpat_x_assum ‘cut_state_opt _ _ = SOME x’ mp_tac
        \\ simp [dataSemTheory.cut_state_opt_def, dataSemTheory.cut_state_def, AllCaseEqs()]
        \\ rw [] \\ simp [])
  \\ simp [SF DNF_ss]
  \\ fs [join_env_def,inter_union_distrib]
  \\ drule_all cut_envs_inter \\ strip_tac \\ simp []
  \\ qsuff_tac ‘inter (fromAList q) (adjust_set x.locals) = inter t.locals (adjust_set x.locals)’
  >-
   (disch_then (fn th => rewrite_tac [th])
    \\ ‘x.locals = mk_wf (inter s.locals kept_names)’ by
         (imp_res_tac cut_state_opt_SOME_eq \\ asm_rewrite_tac [] \\ simp [])
    \\ rpt strip_tac \\ disj2_tac \\ disj2_tac \\ disj1_tac
    \\ gvs [MEM_MAP, MEM_FILTER, EXISTS_PROD, MEM_toAList, lookup_inter, AllCaseEqs()]
    \\ qexists_tac ‘p_1’
    \\ qpat_x_assum ‘lookup p_1 (adjust_set (inter s.locals kept_names)) = SOME ()’ mp_tac
    \\ simp [lookup_adjust_set, domain_inter, AllCaseEqs(), domain_lookup]
    \\ rw []
    \\ qpat_x_assum ‘lookup _ (inter s.locals kept_names) = SOME _’ mp_tac
    \\ simp [lookup_inter, AllCaseEqs()] \\ rw [] \\ simp [])
  \\ fs [spt_eq_thm,lookup_inter_alt]
  \\ rw [] \\ fs []
  \\ drule env_to_list_lookup_equiv
  \\ fs [lookup_insert,lookup_fromAList,adjust_var_11]
  \\ rpt strip_tac \\ fs []
  \\ fs [wordSemTheory.cut_envs_def,wordSemTheory.cut_env_def] \\ rveq
  \\ gvs [wordSemTheory.cut_names_def,AllCaseEqs()]
  \\ fs [lookup_inter_alt] \\ rw []
  \\ fs [IN_domain_adjust_set_inter]
  \\ gvs [adjust_sets_def]
  \\ qpat_x_assum ‘_ ∈ domain (adjust_set x.locals)’ mp_tac
  \\ qpat_x_assum ‘_ ∉ domain (adjust_set kept_names)’ mp_tac
  \\ ‘domain x.locals = domain s.locals ∩ domain kept_names’ by
       (imp_res_tac cut_state_opt_SOME_eq \\ asm_rewrite_tac []
        \\ simp [domain_mk_wf, domain_inter])
  \\ simp [domain_lookup, lookup_adjust_set, AllCaseEqs()]
  \\ rw [] \\ gvs [domain_lookup]
  \\ qpat_x_assum ‘lookup _ x.locals = SOME _’ mp_tac
  \\ qpat_x_assum ‘domain x.locals = _’ mp_tac
  \\ qpat_x_assum ‘lookup _ kept_names ≠ _’ mp_tac
  \\ rpt (pop_assum kall_tac)
  \\ simp [domain_lookup, EXTENSION, IN_INTER]
  \\ metis_tac [oneTheory.one])
  \\ simp [assign_def, arg2_def, assign_StringCmp_def]
  \\ qpat_x_assum ‘word_str_cmp F _ _ t.mdomain t.memory t.be c = SOME (r1,r2)’ mp_tac
  \\ simp [word_str_cmp_def]
  \\ Cases_on ‘t.memory a1'’ \\ gvs [isWord_def,theWord_def]
  \\ Cases_on ‘t.memory a2'’ \\ gvs [isWord_def,theWord_def]
  \\ qabbrev_tac ‘sh_len = dimindex (:α) − (c.len_size + shift (dimindex (:α)))’
  \\ strip_tac \\ pop_assum mp_tac
  \\ simp [Once list_Seq_def, wordSemTheory.evaluate_def]
  \\ gvs [wordSemTheory.get_vars_def,CaseEq"option"]
  \\ qpat_x_assum ‘get_var (adjust_var a1) t = SOME _’ assume_tac
  \\ ‘shift_length c < dimindex (:α)’ by fs [state_rel_thm]
  \\ dxrule_then drule_all get_var_get_real_addr_lemma
  \\ full_simp_tac std_ss [wordSemTheory.get_var_def]
  \\ dxrule_then drule_all word_exp_real_addr
  \\ rpt strip_tac
  \\ simp [Once list_Seq_def, wordSemTheory.evaluate_def]
  \\ simp [wordSemTheory.set_var_def]
  \\ rpt $ qpat_x_assum ‘get_real_addr c t.store _ = SOME _’ kall_tac
  \\ ntac 2 $ once_rewrite_tac [list_Seq_def]
  \\ ‘sh_len < dimindex (:α)’ by (unabbrev_all_tac \\ gvs [good_dimindex_def,shift_def])
  \\ `sh_len < dimword (:'a)` by (assume_tac dimindex_lt_dimword \\ decide_tac)
  \\ simp [eq_eval,word_sh_def]
  \\ ‘(?md. lookup StringCmpLoop_location t.code = SOME (6, StringCmpLoop_code c,md))’ by
       (fs [state_rel_def,code_rel_def,stubs_md_def,stubs_def,MAP_MAP_o,o_DEF])
  \\ once_rewrite_tac [list_Seq_def] \\ simp [eq_eval]
  \\ once_rewrite_tac [list_Seq_def] \\ simp [eq_eval]
  \\ once_rewrite_tac [list_Seq_def] \\ simp [eq_eval]
  \\ once_rewrite_tac [list_Seq_def]
  \\ once_rewrite_tac [list_Seq_def]
  \\ once_rewrite_tac [evaluate_StringCmpMin]
  \\ simp [lookup_insert]
  (* call *)
  \\ simp [list_Seq_def,eq_eval]
  \\ drule cut_env_IMP_cut_envs \\ strip_tac \\ fs [get_names_def]
  \\ simp [eq_eval,cut_envs_adjust_sets_insert_ODD,domain_adjust_sets]
  \\ Cases_on ‘env_to_list y2 t.permute’
  \\ simp [wordSemTheory.push_env_def]
  \\ qmatch_goalsub_abbrev_tac ‘evaluate (StringCmpLoop_code c,t1)’
  \\ rename [‘insert 0 (Loc rl1 rl2) LN’]
  \\ drule evaluate_StringCmpLoop
  \\ disch_then $ qspecl_then [‘c’,‘rl1’,‘rl2’,‘t1’] mp_tac
  \\ impl_tac
  >-
   (simp [Abbr‘t1’,wordSemTheory.get_var_def,lookup_insert]
    \\ rewrite_tac [wordSemTheory.MustTerminate_limit_def]
    \\ ‘dimword (:α) < 2 * dimword (:α) ∧ 10 < dimword (:α)’ by gvs [good_dimindex_def,dimword_def]
    \\ decide_tac)
  \\ strip_tac \\ simp []
  \\ simp [Abbr‘t1’,wordSemTheory.pop_env_def]
  \\ reverse $ IF_CASES_TAC
  >-
   (qsuff_tac ‘F’ >- rewrite_tac []
    \\ fs [domain_union,domain_fromAList_toAList]
    \\ pop_assum mp_tac \\ drule env_to_list_domain
    \\ simp_tac std_ss [AC UNION_COMM UNION_ASSOC])
  \\ simp [wordSemTheory.set_vars_def,alist_insert_def]
  \\ qpat_x_assum ‘evaluate (StringCmpLoop_code c,_) = _’ kall_tac
  \\ fs [] \\ rpt var_eq_tac
  \\ once_rewrite_tac [evaluate_AssignCmp]
  \\ simp [wordSemTheory.get_var_def,lookup_insert]
  \\ simp [list_Seq_def,eq_eval]
  (* final part: proving state_rel *)
  \\ qpat_x_assum ‘state_rel c l1 l2 x t NONE locs’ mp_tac
  \\ simp [state_rel_thm,dataSemTheory.set_var_def,lookup_insert]
  \\ strip_tac \\ pop_assum kall_tac
  \\ ‘x.stack = s.stack ∧ x.stack_max = s.stack_max ∧ x.locals_size = s.locals_size ∧
      x.stack_frame_sizes = s.stack_frame_sizes ∧ x.limits = s.limits ∧
      x.safe_for_space = s.safe_for_space ∧ x.tstamps = s.tstamps ∧
      x.space = s.space ∧ x.global = s.global’ by
       (qpat_x_assum ‘cut_state_opt _ _ = SOME x’ mp_tac
        \\ simp [dataSemTheory.cut_state_opt_def, dataSemTheory.cut_state_def, AllCaseEqs()]
        \\ rw [] \\ simp [])
  \\ conj_tac >-
   (drule_all cut_envs_lookup_0 \\ simp [lookup_union,lookup_fromAList,ALOOKUP_toAList])
  \\ conj_tac >-
   (gen_tac \\ IF_CASES_TAC \\ asm_simp_tac std_ss [adjust_var_11]
    \\ ‘dataSem$cut_env kept_names s.locals = SOME x.locals’ by
         (qpat_x_assum ‘cut_state_opt _ _ = SOME x’ mp_tac
          \\ simp [dataSemTheory.cut_state_opt_def, dataSemTheory.cut_state_def, AllCaseEqs()]
          \\ rw [] \\ simp [])
    \\ full_simp_tac std_ss [IS_SOME_lookup,domain_union] \\ strip_tac
    \\ drule_all IN_adjust_var_lemma \\ simp [])
  \\ qpat_x_assum ‘x.stack = s.stack’ (fn th => rewrite_tac [th])
  \\ qpat_x_assum ‘x.stack_max = s.stack_max’ (fn th => rewrite_tac [th])
  \\ qpat_x_assum ‘x.locals_size = s.locals_size’ (fn th => rewrite_tac [th])
  \\ qpat_x_assum ‘x.stack_frame_sizes = s.stack_frame_sizes’ (fn th => rewrite_tac [th])
  \\ ‘stack_size t.stack = size_of_stack s.stack’ by
       (irule stack_rel_IMP_size_of_stack \\ first_assum (irule_at Any))
  \\ pop_assum (fn th => rewrite_tac [GSYM th])
  \\ qpat_x_assum ‘t.stack_size = s.stack_frame_sizes’ (fn th => full_simp_tac std_ss [th])
  \\ qmatch_asmsub_abbrev_tac ‘max_stack ≠ BB ⇒ max_stack = OPTION_MAP2 MAX BB XX’
  \\ ‘max_stack = BB’ by
       (Cases_on ‘max_stack = BB’ >- asm_rewrite_tac []
        \\ first_x_assum drule \\ strip_tac
        \\ ‘OPTION_MAP2 MAX BB XX = BB’ by (qunabbrev_tac ‘BB’ \\ rewrite_tac [OPTION_MAP2_MAX_CANCEL])
        \\ fs [])
  \\ pop_assum (fn th => rewrite_tac [th])
  \\ conj_tac >-
   (qunabbrev_tac ‘BB’ \\ rewrite_tac [stack_size_eq]
    \\ simp [option_le_max_right,option_le_add,option_add_comm])
  \\ conj_tac >-
   (qunabbrev_tac ‘BB’ \\ qunabbrev_tac ‘XX’ \\ rewrite_tac [stack_size_eq]
    \\ ‘x.stack_frame_sizes = s.stack_frame_sizes’ by fs []
    \\ ‘x.locals_size = s.locals_size’ by fs []
    \\ ntac 2 (pop_assum (fn th => rewrite_tac [th]))
    \\ rewrite_tac [option_le_max,option_le_max_right]
    \\ rpt conj_tac
    >- (disj1_tac \\ first_assum ACCEPT_TAC)
    >- (disj2_tac \\ metis_tac [option_add_comm,option_le_add])
    >- (disj2_tac \\ metis_tac [option_add_comm,option_le_refl]))
  (* memory_rel *)
  \\ fs [inter_insert_ODD_adjust_set]
  \\ rewrite_tac [GSYM APPEND_ASSOC,APPEND]
  \\ irule memory_rel_insert \\ rewrite_tac [APPEND]
  \\ irule memory_rel_Boolv \\ simp []
  \\ qpat_x_assum ‘_ t.mdomain _’ mp_tac
  \\ match_mp_tac memory_rel_rearrange
  \\ ‘cut_env kept_names s.locals = SOME x.locals’ by
       (qpat_x_assum ‘cut_state_opt _ _ = SOME x’ mp_tac
        \\ simp [dataSemTheory.cut_state_opt_def, dataSemTheory.cut_state_def, AllCaseEqs()]
        \\ rw [] \\ simp [])
  \\ simp [SF DNF_ss]
  \\ fs [join_env_def,inter_union_distrib]
  \\ drule_all cut_envs_inter \\ strip_tac \\ simp []
  \\ qsuff_tac ‘inter (fromAList q) (adjust_set x.locals) = inter t.locals (adjust_set x.locals)’
  >-
   (disch_then (fn th => rewrite_tac [th])
    \\ ‘x.locals = mk_wf (inter s.locals kept_names)’ by
         (imp_res_tac cut_state_opt_SOME_eq \\ asm_rewrite_tac [] \\ simp [])
    \\ rpt strip_tac \\ disj2_tac \\ disj2_tac \\ disj1_tac
    \\ gvs [MEM_MAP, MEM_FILTER, EXISTS_PROD, MEM_toAList, lookup_inter, AllCaseEqs()]
    \\ qexists_tac ‘p_1’
    \\ qpat_x_assum ‘lookup p_1 (adjust_set (inter s.locals kept_names)) = SOME ()’ mp_tac
    \\ simp [lookup_adjust_set, domain_inter, AllCaseEqs(), domain_lookup]
    \\ rw []
    \\ qpat_x_assum ‘lookup _ (inter s.locals kept_names) = SOME _’ mp_tac
    \\ simp [lookup_inter, AllCaseEqs()] \\ rw [] \\ simp [])
  \\ fs [spt_eq_thm,lookup_inter_alt]
  \\ rw [] \\ fs []
  \\ drule env_to_list_lookup_equiv
  \\ fs [lookup_insert,lookup_fromAList,adjust_var_11]
  \\ rpt strip_tac \\ fs []
  \\ fs [wordSemTheory.cut_envs_def,wordSemTheory.cut_env_def] \\ rveq
  \\ gvs [wordSemTheory.cut_names_def,AllCaseEqs()]
  \\ fs [lookup_inter_alt] \\ rw []
  \\ fs [IN_domain_adjust_set_inter]
  \\ gvs [adjust_sets_def]
  \\ qpat_x_assum ‘_ ∈ domain (adjust_set x.locals)’ mp_tac
  \\ qpat_x_assum ‘_ ∉ domain (adjust_set kept_names)’ mp_tac
  \\ ‘domain x.locals = domain s.locals ∩ domain kept_names’ by
       (imp_res_tac cut_state_opt_SOME_eq \\ asm_rewrite_tac []
        \\ simp [domain_mk_wf, domain_inter])
  \\ simp [domain_lookup, lookup_adjust_set, AllCaseEqs()]
  \\ rw [] \\ gvs [domain_lookup]
  \\ qpat_x_assum ‘lookup _ x.locals = SOME _’ mp_tac
  \\ qpat_x_assum ‘domain x.locals = _’ mp_tac
  \\ qpat_x_assum ‘lookup _ kept_names ≠ _’ mp_tac
  \\ rpt (pop_assum kall_tac)
  \\ simp [domain_lookup, EXTENSION, IN_INTER]
  \\ metis_tac [oneTheory.one]
QED

Theorem evaluate_XorLoop:
  ∀a1 a2 l dm m l1 l2 (t1:('a,'c,'ffi) wordSem$state) m1.
    word_xor_bytes a1 a2 l dm m = SOME m1 ∧ t1.memory = m ∧ t1.mdomain = dm ∧
    w2n l < t1.clock ∧ good_dimindex (:'a) ∧
    arch_width_bits c.arch_width = dimindex (:'a) ∧
    (?md. lookup XorLoop_location t1.code = SOME (4,XorLoop_code c,md)) ∧
    get_var 0 t1 = SOME (Loc l1 l2) ∧
    get_var 2 t1 = SOME (Word a2) ∧
    get_var 4 t1 = SOME (Word a1) ∧
    get_var 6 t1 = SOME (Word l) ⇒
    ∃ck max_stack.
      evaluate (XorLoop_code c,t1) =
      (SOME (Result (Loc l1 l2) [Word 0w]),
       t1 with <| memory := m1; clock := ck; stack_max := max_stack;
                  locals := LN; locals_size := SOME 0 |>) ∧
      (max_stack ≠ t1.stack_max ⇒
       max_stack = OPTION_MAP2 MAX t1.stack_max
                     (OPTION_MAP2 $+ (stack_size t1.stack)
                        (lookup XorLoop_location t1.stack_size)))
Proof
  ho_match_mp_tac word_xor_bytes_ind \\ rpt gen_tac \\ strip_tac
  \\ rpt gen_tac
  \\ once_rewrite_tac [word_xor_bytes_def]
  \\ simp [SF CONJ_ss,read_word_def]
  \\ rpt IF_CASES_TAC \\ simp []
  \\ rpt strip_tac
  \\ rpt var_eq_tac
  >~ [‘get_var 6 t1 = SOME (Word 0w)’] >-
   (fs [wordSemTheory.isWord_exists,theWord_def,wordSemTheory.get_var_def]
    \\ simp [XorLoop_code_def,eq_eval,wordSemTheory.flush_state_def,list_Seq_def]
    \\ simp [wordSemTheory.state_component_equality])
  >~ [‘get_var 6 t1 = SOME (Word l)’,‘l <+ 2w’] >-
   (fs [wordSemTheory.isWord_exists,theWord_def,wordSemTheory.get_var_def]
    \\ simp [XorLoop_code_def,eq_eval,wordSemTheory.flush_state_def,list_Seq_def,
             wordSemTheory.mem_store_def]
    \\ simp [wordSemTheory.state_component_equality])
  \\ fs [wordSemTheory.isWord_exists,theWord_def,wordSemTheory.get_var_def,
        read_word_def] \\ rfs [theWord_def] \\ fs []
  \\ simp [XorLoop_code_def,eq_eval]
  (* 4 loads *)
  \\ ntac 4 $ once_rewrite_tac [list_Seq_def]
  \\ simp [eq_eval]
  (* 3 arith *)
  \\ ntac 3 $ once_rewrite_tac [list_Seq_def]
  \\ simp [eq_eval]
  (* 2 stores *)
  \\ ntac 2 $ once_rewrite_tac [list_Seq_def]
  \\ simp [eq_eval,wordSemTheory.mem_store_def]
  (* 2 arith *)
  \\ ntac 2 $ once_rewrite_tac [list_Seq_def]
  \\ simp [eq_eval]
  (* tail call *)
  \\ simp [eq_eval,list_Seq_def]
  \\ fs [theWord_def]
  \\ qmatch_goalsub_abbrev_tac ‘evaluate (XorLoop_code c,t2)’
  \\ last_x_assum $ qspecl_then [‘l1’,‘l2’,‘t2’] mp_tac
  \\ impl_tac
  >-
   (simp [Abbr‘t2’,lookup_insert]
    \\ Cases_on ‘l’ \\ gvs [good_dimindex_def,dimword_def,WORD_LO]
    \\ asm_rewrite_tac [GSYM word_sub_def,addressTheory.word_arith_lemma2]
    \\ simp [dimword_def])
  \\ strip_tac
  \\ simp [Abbr‘t2’]
  \\ qpat_x_assum ‘evaluate _ = _’ kall_tac \\ fs []
  \\ simp [wordSemTheory.state_component_equality]
QED

Theorem assign_XorByte:
  op = MemOp XorByte ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ imp_res_tac state_rel_arch_width \\ drule0 (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ ‘names_opt ≠ NONE’ by (qpat_x_assum ‘op_requires_names _ ⇎ _’ mp_tac \\ EVAL_TAC \\ simp [])
  \\ gvs [GSYM IS_SOME_EQ_NOT_NONE,IS_SOME_EXISTS]
  \\ rename [‘cut_state_opt (SOME kept_names) s’]
  \\ drule_all state_rel_cut_state_opt_SOME \\ strip_tac
  \\ qpat_x_assum ‘_ (t with locals := y) NONE locs’ $ ASSUME_NAMED_TAC "with_locals"
  \\ qpat_x_assum `_  s t NONE locs`$ ASSUME_NAMED_TAC "old"
  \\ fs[do_app,dataSemTheory.allowed_op_def] \\ clean_tac
  \\ imp_res_tac get_vars_IMP_LENGTH
  \\ gvs [AllCaseEqs()]
  \\ gvs [LENGTH_EQ_NUM_compute]
  \\ qmatch_asmsub_rename_tac ‘get_vars [a1; a2] s.locals = SOME [RefPtr dst_b dst; RefPtr src_b src]’
  \\ ‘x.refs = s.refs’ by
       (qpat_x_assum ‘cut_state_opt _ _ = SOME x’ mp_tac
        \\ simp [dataSemTheory.cut_state_opt_def, dataSemTheory.cut_state_def, AllCaseEqs()]
        \\ rw [] \\ simp [])
  \\ fs []
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ LABEL_ASSUM "old" (assume_tac o REWRITE_RULE [state_rel_thm])
  \\ full_simp_tac std_ss [APPEND, GSYM APPEND_ASSOC]
  \\ rpt_drule0 memory_rel_get_vars_IMP \\ strip_tac
  \\ ‘good_dimindex (:'a) ∧ shift_length c < dimindex (:α)’ by fs [state_rel_thm]
  \\ dxrule memory_rel_swap \\ strip_tac
  \\ dxrule_all memory_rel_xor_bytes \\ strip_tac \\ gvs []
  \\ ‘good_dimindex (:'a) ∧ shift_length c < dimindex (:α)’ by fs [state_rel_thm]
  (* simulation of generated code *)
  \\ simp [assign_def,arg2_def,assign_XorByte_def,list_Seq_def]
  \\ gvs [wordSemTheory.get_vars_def,CaseEq"option"]
  \\ qpat_x_assum ‘get_var (adjust_var a1) t = SOME _’ assume_tac
  \\ dxrule_then drule_all get_var_get_real_addr_lemma
  \\ full_simp_tac std_ss [wordSemTheory.get_var_def]
  \\ dxrule_then drule_all word_exp_real_addr
  \\ rpt strip_tac
  \\ rpt $ qpat_x_assum ‘get_real_addr c t.store _ = SOME _’ kall_tac
  \\ ntac 2 $ once_rewrite_tac [list_Seq_def]
  \\ simp [eq_eval]
  (* load *)
  \\ once_rewrite_tac [list_Seq_def]
  \\ `dimindex (:'a) - c.len_size < dimindex (:'a)` by
       (fs [memory_rel_def,heap_in_memory_store_def] \\ decide_tac)
  \\ simp [eq_eval,word_exp_SmallLsr,GSYM decode_length_def]
  (* two adds *)
  \\ ntac 2 $ once_rewrite_tac [list_Seq_def]
  \\ simp [eq_eval,get_names_def]
  (* call *)
  \\ ‘(?md. lookup XorLoop_location t.code = SOME (4,XorLoop_code c,md))’ by
       fs [state_rel_def,code_rel_def,stubs_md_def,stubs_def,MAP_MAP_o,o_DEF]
  \\ drule cut_env_IMP_cut_envs \\ strip_tac \\ fs []
  \\ once_rewrite_tac [list_Seq_def]
  \\ simp [eq_eval,cut_envs_adjust_sets_insert_ODD,domain_adjust_sets]
  \\ Cases_on ‘env_to_list y2 t.permute’
  \\ simp [wordSemTheory.push_env_def]
  \\ qmatch_goalsub_abbrev_tac ‘evaluate (XorLoop_code c,t1)’
  \\ rename [‘insert 0 (Loc rl1 rl2) LN’]
  \\ drule evaluate_XorLoop
  \\ disch_then $ qspecl_then [‘c’,‘rl1’,‘rl2’,‘t1’] mp_tac
  \\ impl_tac
  >-
   (simp [Abbr‘t1’,wordSemTheory.get_var_def,lookup_insert]
    \\ irule LESS_LESS_EQ_TRANS
    \\ irule_at Any w2n_lt
    \\ rewrite_tac [wordSemTheory.MustTerminate_limit_def]
    \\ ‘dimword (:α) < 2 * dimword (:α)’ by gvs [good_dimindex_def,dimword_def]
    \\ decide_tac)
  \\ qpat_x_assum ‘lookup XorLoop_location _ = _’ kall_tac
  \\ strip_tac \\ simp []
  \\ simp [Abbr‘t1’,wordSemTheory.pop_env_def]
  \\ reverse $ IF_CASES_TAC
  >-
   (qsuff_tac ‘F’ >- rewrite_tac []
    \\ fs [domain_union,domain_fromAList_toAList]
    \\ pop_assum mp_tac
    \\ drule env_to_list_domain
    \\ simp_tac std_ss [AC UNION_COMM UNION_ASSOC])
  \\ simp [wordSemTheory.set_vars_def,alist_insert_def]
  \\ qpat_x_assum ‘evaluate (XorLoop_code c,_) = _’ kall_tac
  \\ fs [] \\ rpt var_eq_tac
  (* final part: proving state_rel *)
  \\ simp [list_Seq_def,eq_eval,data_to_wordTheory.Unit_def]
  \\ qpat_x_assum ‘state_rel c l1 l2 x t NONE locs’ mp_tac
  \\ simp [state_rel_thm,dataSemTheory.set_var_def,lookup_insert]
  \\ strip_tac \\ pop_assum kall_tac
  \\ ‘x.stack = s.stack ∧ x.stack_max = s.stack_max ∧ x.locals_size = s.locals_size ∧
      x.stack_frame_sizes = s.stack_frame_sizes ∧ x.limits = s.limits ∧
      x.safe_for_space = s.safe_for_space’ by
       (qpat_x_assum ‘cut_state_opt _ _ = SOME x’ mp_tac
        \\ simp [dataSemTheory.cut_state_opt_def, dataSemTheory.cut_state_def, AllCaseEqs()]
        \\ rw [] \\ simp [])
  \\ conj_tac >-
   (drule_all cut_envs_lookup_0
    \\ simp [lookup_union,lookup_fromAList,ALOOKUP_toAList])
  \\ conj_tac >-
   (gen_tac \\ IF_CASES_TAC \\ asm_simp_tac std_ss [adjust_var_11]
    \\ ‘dataSem$cut_env kept_names s.locals = SOME x.locals’ by
         (qpat_x_assum ‘cut_state_opt _ _ = SOME x’ mp_tac
          \\ simp [dataSemTheory.cut_state_opt_def, dataSemTheory.cut_state_def, AllCaseEqs()]
          \\ rw [] \\ simp [])
    \\ full_simp_tac std_ss [IS_SOME_lookup,domain_union] \\ strip_tac
    \\ drule_all IN_adjust_var_lemma \\ simp [])
  (* conj3: stack_size lower bound; conj4: stack_max upper bound.
     max_stack is constrained only by a conditional equation; resolve it to BB first. *)
  \\ qpat_x_assum ‘x.stack = s.stack’ (fn th => rewrite_tac [th])
  \\ qpat_x_assum ‘x.stack_max = s.stack_max’ (fn th => rewrite_tac [th])
  \\ qpat_x_assum ‘x.locals_size = s.locals_size’ (fn th => rewrite_tac [th])
  \\ qpat_x_assum ‘x.stack_frame_sizes = s.stack_frame_sizes’ (fn th => rewrite_tac [th])
  \\ ‘stack_size t.stack = size_of_stack s.stack’ by
       (irule stack_rel_IMP_size_of_stack \\ first_assum (irule_at Any))
  \\ pop_assum (fn th => rewrite_tac [GSYM th])
  \\ qpat_x_assum ‘t.stack_size = s.stack_frame_sizes’ (fn th => full_simp_tac std_ss [th])
  \\ qmatch_asmsub_abbrev_tac ‘max_stack ≠ BB ⇒ max_stack = OPTION_MAP2 MAX BB XX’
  \\ ‘max_stack = BB’ by
       (Cases_on ‘max_stack = BB’ >- asm_rewrite_tac []
        \\ first_x_assum drule \\ strip_tac
        \\ ‘OPTION_MAP2 MAX BB XX = BB’ by
             (qunabbrev_tac ‘BB’ \\ rewrite_tac [OPTION_MAP2_MAX_CANCEL])
        \\ fs [])
  \\ pop_assum (fn th => rewrite_tac [th])
  \\ conj_tac >-
   (qunabbrev_tac ‘BB’ \\ rewrite_tac [stack_size_eq]
    \\ simp [option_le_max_right,option_le_add,option_add_comm])
  \\ conj_tac >-
   (qunabbrev_tac ‘BB’ \\ qunabbrev_tac ‘XX’ \\ rewrite_tac [stack_size_eq]
    \\ ‘x.stack_frame_sizes = s.stack_frame_sizes’ by fs []
    \\ ‘x.locals_size = s.locals_size’ by fs []
    \\ ntac 2 (pop_assum (fn th => rewrite_tac [th]))
    \\ rewrite_tac [option_le_max,option_le_max_right]
    \\ rpt conj_tac
    >- (disj1_tac \\ first_assum ACCEPT_TAC)
    >- (disj2_tac \\ metis_tac [option_add_comm,option_le_add])
    >- (disj2_tac \\ metis_tac [option_add_comm,option_le_refl]))
  (* conj5: memory_rel.  The xor result memory_rel (over s.refs with the write,
     memory m1) is in scope; bridge the cut-invariant fields then rearrange the
     full env down to the cut env (kept-vars come from the XorLoop Call return). *)
  \\ ‘x.tstamps = s.tstamps ∧ x.space = s.space ∧ x.global = s.global’ by
       (qpat_x_assum ‘cut_state_opt _ _ = SOME x’ mp_tac
        \\ simp [dataSemTheory.cut_state_opt_def, dataSemTheory.cut_state_def, AllCaseEqs()]
        \\ rw [] \\ simp [])
  \\ qpat_x_assum ‘x.tstamps = s.tstamps’ (fn th => rewrite_tac [th])
  \\ qpat_x_assum ‘x.space = s.space’ (fn th => rewrite_tac [th])
  \\ qpat_x_assum ‘x.global = s.global’ (fn th => rewrite_tac [th])
  \\ once_rewrite_tac [insert_insert]
  \\ rewrite_tac [GSYM APPEND_ASSOC,APPEND]
  \\ irule memory_rel_insert \\ rewrite_tac [APPEND]
  \\ irule memory_rel_Unit \\ asm_rewrite_tac []
  \\ qpat_x_assum ‘_ t.mdomain _’ mp_tac
  \\ match_mp_tac memory_rel_rearrange
  \\ ‘cut_env kept_names s.locals = SOME x.locals’ by
       (qpat_x_assum ‘cut_state_opt _ _ = SOME x’ mp_tac
        \\ simp [dataSemTheory.cut_state_opt_def, dataSemTheory.cut_state_def, AllCaseEqs()]
        \\ rw [] \\ simp [])
  \\ simp [SF DNF_ss]
  \\ fs [join_env_def,inter_union_distrib]
  \\ drule_all cut_envs_inter \\ strip_tac \\ simp []
  \\ qsuff_tac ‘inter (fromAList q) (adjust_set x.locals) = inter t.locals (adjust_set x.locals)’
  >-
   (disch_then (fn th => rewrite_tac [th])
    \\ ‘x.locals = mk_wf (inter s.locals kept_names)’ by
         (imp_res_tac cut_state_opt_SOME_eq \\ asm_rewrite_tac [] \\ simp [])
    \\ rpt strip_tac \\ disj2_tac \\ disj2_tac \\ disj1_tac
    \\ gvs [MEM_MAP, MEM_FILTER, EXISTS_PROD, MEM_toAList, lookup_inter, AllCaseEqs()]
    \\ qexists_tac ‘p_1’
    \\ qpat_x_assum ‘lookup p_1 (adjust_set (inter s.locals kept_names)) = SOME ()’ mp_tac
    \\ simp [lookup_adjust_set, domain_inter, AllCaseEqs(), domain_lookup]
    \\ rw []
    \\ qpat_x_assum ‘lookup _ (inter s.locals kept_names) = SOME _’ mp_tac
    \\ simp [lookup_inter, AllCaseEqs()] \\ rw [] \\ simp [])
  \\ fs [spt_eq_thm,lookup_inter_alt]
  \\ rw [] \\ fs []
  \\ drule env_to_list_lookup_equiv
  \\ fs [lookup_insert,lookup_fromAList,adjust_var_11]
  \\ rpt strip_tac \\ fs []
  \\ fs [wordSemTheory.cut_envs_def,wordSemTheory.cut_env_def] \\ rveq
  \\ gvs [wordSemTheory.cut_names_def,AllCaseEqs()]
  \\ fs [lookup_inter_alt] \\ rw []
  \\ fs [IN_domain_adjust_set_inter]
  \\ gvs [adjust_sets_def]
  \\ qpat_x_assum ‘_ ∈ domain (adjust_set x.locals)’ mp_tac
  \\ qpat_x_assum ‘_ ∉ domain (adjust_set kept_names)’ mp_tac
  \\ ‘domain x.locals = domain s.locals ∩ domain kept_names’ by
       (imp_res_tac cut_state_opt_SOME_eq \\ asm_rewrite_tac []
        \\ simp [domain_mk_wf, domain_inter])
  \\ simp [domain_lookup, lookup_adjust_set, AllCaseEqs()]
  \\ rw [] \\ gvs [domain_lookup]
  \\ qpat_x_assum ‘lookup _ x.locals = SOME _’ mp_tac
  \\ qpat_x_assum ‘domain x.locals = _’ mp_tac
  \\ qpat_x_assum ‘lookup _ kept_names ≠ _’ mp_tac
  \\ rpt (pop_assum kall_tac)
  \\ simp [domain_lookup, EXTENSION, IN_INTER]
  \\ metis_tac [oneTheory.one]
QED

(* The single narrow cut state IS cut_locals of the original: alloc_lemma's
   size_of_heap (cut_locals ns s) is exactly size_of_heap x. *)

Theorem cut_state_opt_IMP_cut_locals:
  cut_state_opt (SOME ns) s = SOME x ==> cut_locals ns s = x
Proof
  gvs [dataSemTheory.cut_state_opt_def, dataSemTheory.cut_state_def,
       data_to_word_gcProofTheory.cut_locals_def, AllCaseEqs()]
QED

Theorem assign_ConfigGC:
   op = MemOp ConfigGC ==> ^assign_thm_goal
Proof
  rpt strip_tac
  >> ‘op_requires_names op’ by
       simp [dataLangTheory.op_requires_names_def,dataLangTheory.op_space_reset_def]
  >> ‘?ns. names_opt = SOME ns’ by (Cases_on ‘names_opt’ >> fs [])
  >> rveq >> fs []
  >> drule0 (data_to_word_gcProofTheory.evaluate_GiveUp |> GEN_ALL) >> rw [] >> fs []
  >> ‘t.termdep <> 0’ by fs []
  >> imp_res_tac data_to_word_gcProofTheory.state_rel_cut_IMP
  >> pop_assum mp_tac >> strip_tac
  >> imp_res_tac data_to_word_gcProofTheory.get_vars_IMP_LENGTH
  >> fs [dataSemTheory.do_app_def,dataSemTheory.allowed_op_def,AllCaseEqs()]
  >> gvs []
  >> drule_all data_to_word_gcProofTheory.state_rel_get_vars_IMP >> strip_tac
  >> Cases_on ‘vals’ >> fs []
  >> fs [dataSemTheory.do_app_aux_def,dataSemTheory.do_stack_def,AllCaseEqs()]
  >> rveq >> gvs []
  >> gvs [LENGTH_EQ_NUM_compute]
  >> fs [data_to_wordTheory.assign_def,EVAL ``op_requires_names (MemOp ConfigGC)``,
         data_to_wordTheory.arg2_def,data_to_wordTheory.assign_ConfigGC_def]
  >> fs [data_to_wordTheory.list_Seq_def,eq_eval]
  >> gvs [data_to_word_gcProofTheory.alloc_locals_insert_1]
  (* Stabilise the two argument values. *)
  >> qmatch_asmsub_rename_tac
       ‘get_vars [k1; k2] s.locals = SOME [Number i1; Number i2]’
  (* cut_env ns s.locals for narrow alloc_lemma application. *)
  >> ‘?env_narrow. dataSem$cut_env ns s.locals = SOME env_narrow’ by
       (fs [dataSemTheory.cut_env_def,dataSemTheory.cut_state_opt_def,
            dataSemTheory.cut_state_def,AllCaseEqs(),domain_lookup,SUBSET_DEF] >>
        metis_tac [sptreeTheory.lookup_insert,optionTheory.option_CLAUSES])
  (* x and s differ only in locals. *)
  >> ‘x.stack_max = s.stack_max ∧ x.limits = s.limits ∧ x.refs = s.refs ∧
      x.stack = s.stack ∧ x.global = s.global ∧ x.locals_size = s.locals_size ∧
      x.safe_for_space = s.safe_for_space ∧ x.peak_heap_length = s.peak_heap_length ∧
      x.stack_frame_sizes = s.stack_frame_sizes’ by
       (qpat_x_assum ‘cut_state_opt _ s = SOME x’ mp_tac >>
        simp [dataSemTheory.cut_state_opt_def,dataSemTheory.cut_state_def,AllCaseEqs()] >>
        rw [] >> fs [])
  (* s1 = x with the args-aware do_space updates (space_consumed ConfigGC = 0). *)
  >> ‘s1 = x with <|space := 0;
                    safe_for_space :=
                      (x.safe_for_space ∧
                       no_thunks_in_refs x.refs ∧
                       size_of_heap_args [Number i1; Number i2] x ≤ x.limits.heap_limit);
                    peak_heap_length :=
                      MAX x.peak_heap_length (size_of_heap_args [Number i1; Number i2] x)|>’ by
       (qpat_x_assum ‘do_space _ _ _ = _’ mp_tac >>
        simp [dataSemTheory.do_space_def,dataLangTheory.op_space_reset_def,
              dataSemTheory.space_consumed_def] >>
        simp [dataSemTheory.state_component_equality])
  >> drule cut_state_opt_IMP_cut_locals >> strip_tac
  >> reverse (Cases_on ‘c.call_empty_ffi’)
  >- (* no_ffi arm: SilentFFI reduces to Skip (¬c.call_empty_ffi). *)
     (fs [data_to_wordTheory.SilentFFI_def, wordSemTheory.evaluate_def]
  \\ qpat_x_assum `state_rel c l1 l2 s t NONE locs` assume_tac
  \\ qpat_abbrev_tac `alll = alloc _ _ _`
  \\ `?x1 x2. alll = (x1,x2)` by (Cases_on `alll` \\ fs [])
  \\ unabbrev_all_tac \\ fs []
  \\ drule (data_to_word_gcProofTheory.alloc_lemma)
  \\ fs [data_to_wordTheory.get_names_def,EVAL ``alloc_size 0``]
  \\ disch_then (qspecl_then [`env_narrow`,`x2`,`x1`,`ns`] mp_tac) \\ simp []
  \\ strip_tac
  \\ qexistsl_tac [`if x1 = NONE then NONE else x1`,
       `if x1 = NONE then
          x2 with locals := insert (adjust_var dest) (Word 0w) x2.locals
        else x2`]
  \\ Cases_on `x1 = SOME NotEnoughSpace` \\ fs []
  >- (* NES arm: alloc fails; show ¬safe_for_space via args-aware heap bound. *)
     (first_x_assum (qspec_then `0` mp_tac)
      \\ fs [EVAL ``alloc_size 0``]
      \\ strip_tac
      \\ conj_tac
      >- (irule backendPropsTheory.option_le_trans
          \\ qexists_tac `s.stack_max` \\ asm_rewrite_tac []
          \\ simp [backendPropsTheory.option_le_max_right])
      \\ strip_tac
      \\ Cases_on ‘no_thunks_in_refs s.refs’ \\ fs []
      \\ disj1_tac \\ disj2_tac
      \\ simp [NOT_LESS_EQUAL]
      \\ irule arithmeticTheory.LESS_LESS_EQ_TRANS
      \\ qexists_tac `size_of_heap x`
      \\ conj_tac \\ fs [size_of_heap_LE_args])
  >- (* Success arm: alloc succeeds; rebuild state_rel on set_var dest Unit. *)
     (qpat_x_assum `∀k. alloc _ _ _ = _ ⇒ _` (qspec_then `0` mp_tac)
      \\ simp [EVAL ``alloc_size 0:'a word``]
      \\ strip_tac
      \\ gvs []
      \\ `cut_locals ns s = s with locals := env_narrow` by
           fs [data_to_word_gcProofTheory.cut_locals_def]
      \\ pop_assum SUBST_ALL_TAC
      \\ qpat_x_assum `state_rel _ _ _ (s with <|locals := _; space := _|>) _ _ _` mp_tac
      \\ simp [state_rel_thm, dataSemTheory.set_var_def,
               wordSemTheory.set_var_def, lookup_insert, adjust_var_11,
               backendPropsTheory.option_le_max_right]
      \\ strip_tac
      \\ rw [backendPropsTheory.option_le_max_right]
      \\ gvs []
      \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
      \\ match_mp_tac memory_rel_insert \\ fs []
      \\ match_mp_tac memory_rel_Unit \\ fs []))
  (* ffi arm: SilentFFI performs an empty FFI call. *)
  \\ fs [data_to_wordTheory.get_names_def]
  \\ `∃y. wordSem$cut_env (adjust_sets ns) t.locals = SOME y` by
       metis_tac [data_to_word_gcProofTheory.cut_env_IMP_cut_env]
  \\ `evaluate (SilentFFI c 3 (adjust_sets ns), t) =
        (NONE, t with <|locals := y; fp_regs := FEMPTY;
                        memory := t.memory; ffi := t.ffi|>)` by
       (irule evaluate_SilentFFI_3 \\ metis_tac [])
  \\ fs []
  \\ fs [wordSemTheory.evaluate_def]
  \\ `t with <|locals := y; fp_regs := FEMPTY; memory := t.memory; ffi := s.ffi|> =
      t with <|locals := y; fp_regs := FEMPTY|>` by
       (qpat_x_assum `t.ffi = s.ffi` mp_tac \\ simp [wordSemTheory.state_component_equality])
  \\ fs []
  \\ `state_rel c l1 l2 (s with locals := env_narrow) (t with locals := y) NONE locs` by
       (irule data_to_word_gcProofTheory.state_rel_cut_env_cut_env \\ metis_tac [])
  \\ drule data_to_word_gcProofTheory.state_rel_with_fp_regs
  \\ disch_then (qspec_then `FEMPTY` assume_tac)
  \\ imp_res_tac cut_env_idempotent
  (* Apply alloc_lemma directed at the narrow-cut state_rel (operand t with locals := y). *)
  \\ qpat_abbrev_tac `alll = alloc _ _ (t with <|locals := y; fp_regs := FEMPTY|>)`
  \\ `?x1 x2. alll = (x1,x2)` by (Cases_on `alll` \\ fs [])
  \\ unabbrev_all_tac \\ fs []
  \\ qpat_x_assum `state_rel c l1 l2 (s with locals := env_narrow)
         (t with <|locals := y; fp_regs := FEMPTY|>) NONE locs`
       (mp_then Any mp_tac data_to_word_gcProofTheory.alloc_lemma)
  \\ disch_then (qspecl_then [`env_narrow`,`x2`,`x1`,`ns`] mp_tac)
  \\ fs [EVAL ``alloc_size 0``]
  \\ simp []
  \\ strip_tac
  \\ Cases_on `x1 = SOME NotEnoughSpace` \\ gvs []
  >- (* NES arm: alloc fails; show ¬safe_for_space via args-aware heap bound. *)
     (first_x_assum (qspec_then `0` mp_tac)
      \\ fs [EVAL ``alloc_size 0``]
      \\ strip_tac
      \\ conj_tac
      >- (irule backendPropsTheory.option_le_trans
          \\ qexists_tac `s.stack_max` \\ asm_rewrite_tac []
          \\ simp [backendPropsTheory.option_le_max_right])
      \\ Cases_on ‘no_thunks_in_refs s.refs’ \\ fs []
      \\ strip_tac \\ disj1_tac \\ disj2_tac
      \\ simp [NOT_LESS_EQUAL]
      \\ irule arithmeticTheory.LESS_LESS_EQ_TRANS
      \\ qexists_tac `size_of_heap (cut_locals ns s)`
      \\ conj_tac
      \\ fs [size_of_heap_LE_args, data_to_word_gcProofTheory.cut_locals_def]
      \\ gvs [])
  (* Success arm: alloc succeeds; eval post-alloc SilentFFI, rebuild state_rel. *)
  \\ qpat_x_assum `∀k. alloc _ _ _ = _ ⇒ _` (qspec_then `0` mp_tac)
  \\ simp [EVAL ``alloc_size 0:'a word``]
  \\ strip_tac
  \\ gvs []
  \\ `∃y'. wordSem$cut_env (adjust_sets ns) x2.locals = SOME y'` by
       (qpat_x_assum `state_rel c l1 l2 (s with <|locals := env_narrow; space := 0|>) x2 NONE locs` assume_tac
        \\ drule data_to_word_gcProofTheory.cut_env_IMP_cut_env
        \\ disch_then (qspecl_then [`env_narrow`,`ns`] mp_tac) \\ simp [])
  \\ `evaluate (SilentFFI c 3 (adjust_sets ns), x2) =
        (NONE, x2 with <|locals := y'; fp_regs := FEMPTY;
                         memory := x2.memory; ffi := x2.ffi|>)` by
       (irule evaluate_SilentFFI_3 \\ metis_tac [])
  \\ fs []
  \\ fs [wordSemTheory.evaluate_def]
  \\ qpat_x_assum `state_rel c l1 l2 (s with <|locals := env_narrow; space := 0|>) x2 NONE locs` assume_tac
  \\ drule (DISCH_ALL data_to_word_gcProofTheory.state_rel_cut_env_cut_env)
  \\ disch_then (qspecl_then [`y'`,`env_narrow`,`ns`] mp_tac)
  \\ simp [] \\ strip_tac
  \\ `cut_locals ns s = s with locals := env_narrow` by
       fs [data_to_word_gcProofTheory.cut_locals_def]
  \\ pop_assum SUBST_ALL_TAC
  \\ qpat_x_assum `state_rel _ _ _ (s with <|locals := _; space := _|>) (x2 with locals := y') _ _` mp_tac
  \\ simp [state_rel_thm, dataSemTheory.set_var_def,
           wordSemTheory.set_var_def, lookup_insert, adjust_var_11,
           backendPropsTheory.option_le_max_right]
  \\ strip_tac
  \\ rw [backendPropsTheory.option_le_max_right]
  \\ gvs []
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ match_mp_tac memory_rel_insert \\ fs []
  \\ match_mp_tac memory_rel_Unit \\ fs []
QED

(* Helper: do_app on RefByte gives a precise equation s' = s with <known-update>
   (args-aware single-cut form). Used to bridge s2_inner field equalities in
   assign_RefByte's Success arm. *)

Theorem do_app_RefByte_eq[local]:
  do_app (MemOp (RefByte fl)) [Number i; Number (&w2n (w:word8))] (s:('c,'ffi) dataSem$state) = Rval (v, s') ⇒
  ∃ptr. v = RefPtr T ptr ∧ ptr = (LEAST p. p ∉ domain s.refs) ∧ 0 ≤ i ∧
        s' = s with
             <|stack_max :=
                 OPTION_MAP2 MAX s.stack_max
                   (OPTION_MAP2 $+
                      (stack_consumed s.stack_frame_sizes s.limits
                         (MemOp (RefByte fl)) [Number i; Number (&w2n w)])
                      (OPTION_MAP2 $+ (size_of_stack s.stack) s.locals_size));
               refs := insert ptr (ByteArray fl (REPLICATE (Num i) w)) s.refs;
               space := 0;
               safe_for_space :=
                 (((Num i DIV (arch_size s.limits DIV 8) <
                    2 ** arch_size s.limits DIV arch_size s.limits ∧
                    Num i DIV (arch_size s.limits DIV 8) + 1 <
                    2 ** s.limits.length_limit ∧
                    small_num s.limits.arch_64_bit i) ∧
                   no_thunks_in_refs s.refs ∧
                   add_space_safe_args
                     (space_consumed s (MemOp (RefByte fl))
                        [Number i; Number (&w2n w)])
                     [Number i; Number (&w2n w)] s) ∧
                  the F
                    (OPTION_MAP ($> s.limits.stack_limit)
                       (OPTION_MAP2 $+
                          (stack_consumed s.stack_frame_sizes s.limits
                             (MemOp (RefByte fl)) [Number i; Number (&w2n w)])
                          (OPTION_MAP2 $+ (size_of_stack s.stack)
                             s.locals_size))));
               peak_heap_length :=
                 heap_peak_args
                   (space_consumed s (MemOp (RefByte fl))
                      [Number i; Number (&w2n w)])
                   [Number i; Number (&w2n w)] s|>
Proof
  simp [dataSemTheory.do_app_def, dataSemTheory.do_app_aux_def,
        dataSemTheory.do_space_def, dataSemTheory.do_stack_def,
        dataSemTheory.lim_safe_def, dataLangTheory.op_space_reset_def,
        dataSemTheory.allowed_op_def, dataSemTheory.consume_space_def,
        dataSemTheory.check_lim_def, AllCaseEqs()]
  >> strip_tac
  >> gvs []
  >> simp [dataSemTheory.state_component_equality, AC CONJ_COMM CONJ_ASSOC]
QED

(* Helper: lift inner-with on a dec_clock'd state to outer-with on call_env/push_env.
   Used to bridge the post-Call evaluate term to the shape expected by
   evaluate_IMP_domain_union (which has outer-with). *)

Theorem assign_RefByte:
  (?fl. op = MemOp (RefByte fl)) ==> ^assign_thm_goal
Proof
  (* PROLOGUE verified under single-cut (reaches the word Call to RefByte_location,
     goal/NES-bound now expressed via x with args-aware size_of_heap_args). *)
  rpt strip_tac
  \\ drule0 (evaluate_GiveUp2 |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs []
  \\ `option_le x.stack_max s2.stack_max` by metis_tac [do_app_stack_max]
  \\ rpt_drule0 data_to_word_gcProofTheory.state_rel_cut_IMP \\ strip_tac
  \\ fs [data_to_wordTheory.assign_def] \\ rveq
  \\ fs [dataLangTheory.op_requires_names_def,
         dataLangTheory.op_space_reset_def,dataSemTheory.cut_state_opt_def]
  \\ Cases_on `names_opt` \\ fs []
  \\ drule_all (state_rel_cut_state_opt_SOME |> SRULE [dataSemTheory.cut_state_opt_def])
  \\ strip_tac
  \\ qpat_x_assum `state_rel _ _ _ _ (t with locals := y) _ _` $ ASSUME_NAMED_TAC "with_locals"
  \\ imp_res_tac data_to_word_gcProofTheory.get_vars_IMP_LENGTH \\ fs [] \\ rw []
  \\ fs [do_app,dataSemTheory.allowed_op_def]
  \\ `?i b. vals = [Number i; Number b]` by (every_case_tac \\ fs [] \\ rw [] \\ NO_TAC)
  \\ clean_tac
  \\ imp_res_tac data_to_word_gcProofTheory.state_rel_get_vars_IMP
  \\ fs [LENGTH_EQ_2] \\ clean_tac
  \\ fs [LENGTH_EQ_2] \\ clean_tac
  \\ fs [data_to_wordTheory.arg2_def,data_to_wordTheory.assign_RefByte_def]
  \\ qmatch_asmsub_rename_tac `get_vars [k1; k2] s.locals = SOME [Number i; Number b]`
  \\ qmatch_asmsub_rename_tac `get_vars [adjust_var k1; adjust_var k2] t = SOME [w1; w2]`
  \\ qpat_x_assum `_ = Rval (v,s2)` mp_tac
  \\ reverse IF_CASES_TAC >- fs []
  \\ strip_tac \\ gvs []
  (* CALL SETUP (single-cut alignment): push x's env (cut by x'), apply RefByte_thm. *)
  \\ `dataSem$cut_env x' s.locals = SOME x.locals` by
       (qpat_x_assum `cut_state x' s = SOME x` mp_tac
        \\ simp [dataSemTheory.cut_state_def, AllCaseEqs()] \\ rw [] \\ fs [])
  \\ `state_rel c l1 l2 (s with clock := MustTerminate_limit(:'a))
        (t with <|clock := MustTerminate_limit(:'a); termdep := t.termdep - 1|>) NONE locs` by
       (qpat_assum `state_rel c l1 l2 s t NONE locs`
          (mp_tac o MATCH_MP (data_to_word_gcProofTheory.state_rel_with_clock
                                |> Q.GEN `k` |> Q.SPEC `MustTerminate_limit(:'a)`))
        \\ fs [data_to_word_gcProofTheory.state_rel_def])
  \\ drule0 data_to_word_gcProofTheory.cut_env_IMP_cut_envs \\ strip_tac
  \\ rpt_drule0 data_to_word_gcProofTheory.state_rel_call_env_push_env \\ fs []
  \\ disch_then drule0 \\ fs []
  \\ disch_then drule0 \\ fs []
  \\ disch_then (qspecl_then [`lookup RefByte_location t.stack_size`, `n`, `l`, `NONE`] mp_tac)
  \\ strip_tac
  \\ `(?md. lookup RefByte_location t.code = SOME (4, RefByte_code c,md))` by
       (qpat_x_assum `state_rel c l1 l2 s t NONE locs` assume_tac
        \\ drule0 data_to_word_gcProofTheory.lookup_RefByte_location \\ rw [])
  \\ `adjust_var k1 ≠ 1 ∧ adjust_var k2 ≠ 1` by
       (rw [data_to_wordTheory.adjust_var_def] \\ intLib.ARITH_TAC)
  \\ `lookup (adjust_var k1) t.locals = SOME w1 ∧ lookup (adjust_var k2) t.locals = SOME w2` by
       (qpat_x_assum `get_vars [adjust_var k1; adjust_var k2] t = _` mp_tac
        \\ simp [wordSemTheory.get_vars_def, wordSemTheory.get_var_def, AllCaseEqs()] \\ rw [])
  \\ simp [wordSemTheory.evaluate_def, wordSemTheory.set_var_def,
           wordSemTheory.word_exp_def, wordSemTheory.get_var_def,
           wordSemTheory.get_vars_def, lookup_insert,
           wordSemTheory.bad_dest_args_def,
           wordSemTheory.add_ret_loc_def, wordSemTheory.find_code_def,
           data_to_wordTheory.get_names_def,
           data_to_word_gcProofTheory.cut_envs_adjust_sets_ODD,
           domain_adjust_sets]
  \\ `(if fl then 0n else 8) < dimword (:α) DIV 8` by
       (fs [data_to_word_gcProofTheory.state_rel_def,
            miscTheory.good_dimindex_def, dimword_def] \\ rw [])
  \\ qpat_x_assum `state_rel c n l (call_env [Number i; Number (&w2n w)] _ _) (call_env [Loc n l; w1; w2] _ _) NONE _` assume_tac
  \\ drule0 (Q.SPEC `if fl then 0n else 8` (Q.GEN `n` data_to_word_gcProofTheory.state_rel_IMP_Number_arg))
  \\ impl_tac >- fs []
  \\ strip_tac
  \\ fs []
  \\ qmatch_assum_abbrev_tac `state_rel c n l (call_env _ _ st_inner_data) (call_env _ _ st_inner_word) NONE _`
  \\ qabbrev_tac `ts = call_env [Number i; Number (&w2n w); Number (&if fl then 0n else 8)]
                       (lookup RefByte_location t.stack_size) st_inner_data`
  \\ qabbrev_tac `twAbv = call_env [Loc n l; w1; w2; Word (n2w (2 * if fl then 0n else 8):α word)]
                       (lookup RefByte_location t.stack_size) st_inner_word`
  \\ `is_env (HD ts.stack)` by
       (unabbrev_all_tac
        \\ simp [dataSemTheory.call_env_def, dataSemTheory.push_env_def,
                 dataSemTheory.dec_clock_def, is_env_def] \\ metis_tac [])
  \\ `twAbv.clock = MustTerminate_limit (:'a) - 1` by
       (unabbrev_all_tac
        \\ simp [wordSemTheory.call_env_def, wordSemTheory.push_env_def,
                 wordSemTheory.dec_clock_def] \\ pairarg_tac \\ fs [])
  \\ qabbrev_tac `s_pop : ('c,'ffi) dataSem$state =
        s with <|locals := x.locals; clock := MustTerminate_limit (:'a) - 1;
                 stack_max := ts.stack_max; safe_for_space := ts.safe_for_space|>`
  \\ `pop_env ts = SOME s_pop` by
       (unabbrev_all_tac
        \\ simp [dataSemTheory.call_env_def, dataSemTheory.push_env_def,
                 dataSemTheory.pop_env_def, dataSemTheory.dec_clock_def,
                 dataSemTheory.state_component_equality])
  \\ `ts.locals_size = lookup RefByte_location ts.stack_frame_sizes` by
       (unabbrev_all_tac
        \\ simp [dataSemTheory.call_env_def, dataSemTheory.push_env_def,
                 dataSemTheory.dec_clock_def]
        \\ fs [data_to_word_gcProofTheory.state_rel_def])
  \\ `get_vars [0;1;2] ts.locals =
        SOME ([Number i; Number (&w2n w)] ++ [Number (&if fl then 0 else 8)])` by
       (unabbrev_all_tac
        \\ simp [dataSemTheory.get_vars_def, dataSemTheory.call_env_def,
                 dataSemTheory.get_var_def, dataSemTheory.push_env_def,
                 dataSemTheory.dec_clock_def, sptreeTheory.lookup_fromList])
  \\ `?s2_inner.
        do_app (MemOp (RefByte fl)) [Number i; Number (&w2n w)] s_pop =
          Rval (RefPtr T (LEAST ptr. ptr ∉ domain s.refs), s2_inner)` by
       (simp [Abbr `s_pop`]
        \\ simp [dataSemTheory.do_app_def, dataSemTheory.do_app_aux_def,
                 dataSemTheory.do_space_def, dataSemTheory.do_stack_def,
                 dataSemTheory.space_consumed_def,
                 dataLangTheory.op_space_reset_def,
                 dataSemTheory.allowed_op_def, dataSemTheory.check_lim_def]
        \\ metis_tac [])
  \\ rpt_drule0 RefByte_thm
  \\ disch_then (qspecl_then [`l2`, `l1`] mp_tac)
  \\ strip_tac
  \\ pop_assum strip_assume_tac
  \\ qmatch_goalsub_abbrev_tac `evaluate (RefByte_code c, twC)`
  \\ `twC = twAbv` by
       (unabbrev_all_tac
        \\ rw [wordSemTheory.call_env_def, wordSemTheory.push_env_def,
               wordSemTheory.dec_clock_def, wordSemTheory.state_component_equality]
        \\ pairarg_tac \\ fs [] \\ Cases_on `fl` \\ fs [])
  \\ fs []
  \\ Cases_on `q = SOME NotEnoughSpace` \\ fs []
  >- (* NES arm: alloc/Replicate fails. conj1 ffi; conj2 stack bound; conj3 heap disjunction. *)
     (conj_tac
      >- (qpat_x_assum `Abbrev (twAbv = _)`
            (assume_tac o REWRITE_RULE [markerTheory.Abbrev_def])
          \\ simp [wordSemTheory.call_env_def, wordSemTheory.push_env_def,
                   wordSemTheory.dec_clock_def, UNCURRY_DEF]
          \\ Cases_on `env_to_list y2 t.permute` \\ fs [])
      \\ conj_tac
      >- (qpat_x_assum `state_rel c l1 l2 s t NONE locs` assume_tac
          \\ `s.stack_frame_sizes = t.stack_size` by fs[data_to_word_gcProofTheory.state_rel_def]
          \\ `t.locals_size = s.locals_size` by fs[data_to_word_gcProofTheory.state_rel_def]
          \\ qpat_x_assum `do_app _ _ _ = _` mp_tac
          \\ simp [dataSemTheory.do_app_def, dataSemTheory.do_app_aux_def,
                   dataSemTheory.do_space_def, dataSemTheory.do_stack_def,
                   dataSemTheory.stack_consumed_def, dataSemTheory.consume_space_def,
                   dataSemTheory.with_fresh_ts_def, dataSemTheory.check_lim_def,
                   dataLangTheory.op_space_reset_def, dataSemTheory.allowed_op_def]
          \\ strip_tac
          \\ pop_assum (assume_tac o GSYM)
          \\ qpat_x_assum `option_le r'.stack_max s2_inner.stack_max` assume_tac
          \\ `∀z. option_le s2_inner.stack_max z ⇒ option_le r'.stack_max z` by
                metis_tac [backendPropsTheory.option_le_trans]
          \\ first_x_assum match_mp_tac
          \\ qpat_x_assum `s2_inner = _` (fn th => simp [th])
          \\ qpat_x_assum `Abbrev (s_pop = _)` (assume_tac o REWRITE_RULE [markerTheory.Abbrev_def])
          \\ qpat_x_assum `Abbrev (ts = _)` (assume_tac o REWRITE_RULE [markerTheory.Abbrev_def])
          \\ qpat_x_assum `Abbrev (st_inner_data = _)` (assume_tac o REWRITE_RULE [markerTheory.Abbrev_def])
          \\ `cut_state_opt (SOME x') s = SOME x` by fs [dataSemTheory.cut_state_opt_def]
          \\ imp_res_tac cut_state_opt_SOME_eq
          \\ gvs []
          \\ asm_simp_tac (srw_ss())[call_env_push_env_dec_clock_stack_max]
          \\ irule option_le_stackmax_bridge)
      \\ strip_tac
      \\ `cut_state_opt (SOME x') s = SOME x` by fs [dataSemTheory.cut_state_opt_def]
      \\ drule cut_state_opt_SOME_eq \\ strip_tac
      \\ `ts.limits = x.limits ∧ s_pop.limits = x.limits` by
           (qpat_x_assum `Abbrev (ts = _)` (assume_tac o REWRITE_RULE [markerTheory.Abbrev_def])
            \\ qpat_x_assum `Abbrev (st_inner_data = _)` (assume_tac o REWRITE_RULE [markerTheory.Abbrev_def])
            \\ qpat_x_assum `Abbrev (s_pop = _)` (assume_tac o REWRITE_RULE [markerTheory.Abbrev_def])
            \\ qpat_x_assum `x = _` (fn th => asm_rewrite_tac [th])
            \\ simp [dataSemTheory.call_env_def, dataSemTheory.push_env_def, dataSemTheory.dec_clock_def])
      \\ `size_of_heap s_pop = size_of_heap x` by
           (qpat_x_assum `Abbrev (s_pop = _)` (assume_tac o REWRITE_RULE [markerTheory.Abbrev_def])
            \\ qpat_x_assum `x = _` (fn th => asm_rewrite_tac [th])
            \\ simp [dataSemTheory.size_of_heap_def, dataSemTheory.stack_to_vs_def])
      \\ reverse $ Cases_on ‘no_thunks_in_refs x.refs’ >- asm_rewrite_tac []
      \\ ‘no_thunks_in_refs ts.refs’ by
        (unabbrev_all_tac \\ simp [call_env_def]
         \\ imp_res_tac cut_state_refs_same
         \\ metis_tac [])
      \\ `i < 0 ∨ ¬small_num x.limits.arch_64_bit i ∨
          ¬(Num i DIV (arch_size x.limits DIV 8) < dimword (:α) DIV arch_size x.limits) ∨
          ¬(Num i DIV (arch_size x.limits DIV 8) + 1 < 2 ** c.len_size) ∨
          x.limits.heap_limit < size_of_heap x + (Num i DIV (arch_size x.limits DIV 8) + 2)`
            by metis_tac []
      >- (mp_tac (intLib.COOPER_PROVE ``(i:int) < 0 ==> 0 <= i ==> F``) \\ fs [])
      >- (disj1_tac \\ disj1_tac \\ rpt disj2_tac \\ asm_rewrite_tac [])
      >- (disj1_tac \\ disj1_tac \\ disj1_tac
          \\ `dimword (:α) = 2 ** arch_size x.limits` by
               (qpat_x_assum `state_rel c l1 l2 s t NONE locs` assume_tac
                \\ `x.limits = s.limits` by (qpat_x_assum `x = _` (fn th => simp [th]))
                \\ fs [data_to_word_gcProofTheory.state_rel_def, miscTheory.good_dimindex_def,
                       data_to_word_gcProofTheory.limits_inv_def, dataSemTheory.arch_size_def, dimword_def])
          \\ fs [])
      >- (disj1_tac \\ disj1_tac \\ disj2_tac \\ disj1_tac
          \\ `c.len_size = x.limits.length_limit` by
               (qpat_x_assum `state_rel c l1 l2 s t NONE locs` assume_tac
                \\ `x.limits = s.limits` by (qpat_x_assum `x = _` (fn th => simp [th]))
                \\ fs [data_to_word_gcProofTheory.state_rel_def, data_to_word_gcProofTheory.limits_inv_def])
          \\ fs [])
      >- (disj1_tac \\ disj2_tac \\ disj2_tac \\ simp [NOT_LESS_EQUAL]
          \\ `x = s with locals := inter s.locals x'` by
               (qpat_x_assum `x = s with locals := mk_wf _` mp_tac \\ simp [])
          \\ gvs []
          \\ `space_consumed (s with locals := inter s.locals x') (MemOp (RefByte fl))
                [Number i; Number (&w2n w)] = Num i DIV (arch_size s.limits DIV 8) + 2` by
               simp [dataSemTheory.space_consumed_def, dataSemTheory.arch_size_def]
          \\ pop_assum (fn th => rewrite_tac [th])
          \\ `size_of_heap (s with locals := inter s.locals x') ≤
               size_of_heap_args [Number i; Number (&w2n w)] (s with locals := inter s.locals x')` by
               simp [size_of_heap_LE_args]
          \\ qpat_x_assum `_ < size_of_heap (s with locals := inter s.locals x') + _` mp_tac
          \\ qpat_x_assum `size_of_heap _ ≤ _` mp_tac
          \\ rpt (pop_assum kall_tac) \\ DECIDE_TAC))
  (* Success arm: pop_env, rebuild state_rel via word_ml_inv_insert. *)
  \\ qpat_x_assum `state_rel c l1 l2 _ r' (SOME [(RefPtr T _, _)]) _` assume_tac
  \\ drule data_to_word_gcProofTheory.state_rel_pop_env_IMP
  \\ qpat_x_assum `Abbrev (ts = _)` (assume_tac o REWRITE_RULE [markerTheory.Abbrev_def])
  \\ qpat_x_assum `Abbrev (st_inner_data = _)` (assume_tac o REWRITE_RULE [markerTheory.Abbrev_def])
  \\ simp [dataSemTheory.push_env_def, dataSemTheory.call_env_def,
           dataSemTheory.pop_env_def, dataSemTheory.dec_clock_def]
  \\ strip_tac
  \\ qpat_x_assum `Abbrev (twAbv = _)` (assume_tac o REWRITE_RULE [markerTheory.Abbrev_def])
  \\ qpat_x_assum `Abbrev (st_inner_word = _)` (assume_tac o REWRITE_RULE [markerTheory.Abbrev_def])
  \\ fs []
  \\ qpat_x_assum `state_rel c n l (call_env _ _ (push_env _ F _)) (call_env _ _ (push_env (y1,y2) NONE _)) _ _` assume_tac
  \\ drule state_rel_push_env_loc
  \\ disch_then assume_tac
  \\ fs [call_env_push_env_dec_clock_lift_locals]
  \\ drule_all evaluate_IMP_domain_union
  \\ disch_then assume_tac
  \\ fs []
  \\ fs [data_to_word_gcProofTheory.state_rel_def]
  \\ unabbrev_all_tac
  \\ fs []
  \\ simp [dataSemTheory.set_var_def, wordSemTheory.set_vars_def,
           wordSemTheory.set_var_def, sptreeTheory.alist_insert_def, lookup_insert]
  \\ `x = s with locals := x.locals` by
       (qpat_x_assum `cut_state x' s = SOME x` mp_tac
        \\ simp [dataSemTheory.cut_state_def]
        \\ qpat_x_assum `cut_env x' s.locals = SOME x.locals` (fn th => simp [th])
        \\ strip_tac \\ gvs [])
  \\ qpat_x_assum `do_app _ _ _ = Rval (_,s2_inner)`
       (strip_assume_tac o MATCH_MP do_app_RefByte_eq)
  \\ fs []
  \\ `x.code = s.code ∧ x.stack = s.stack ∧ x.locals_size = s.locals_size ∧
      x.stack_frame_sizes = s.stack_frame_sizes ∧ x.limits = s.limits ∧
      x.tstamps = s.tstamps ∧ x.global = s.global ∧ x.refs = s.refs ∧
      x.stack_max = s.stack_max ∧ x.ffi = s.ffi ∧ x.handler = s.handler ∧
      x.compile = s.compile ∧ x.compile_oracle = s.compile_oracle` by
       (qpat_x_assum `x = s with locals := x.locals` (fn th => once_rewrite_tac [th])
        \\ simp [])
  \\ fs []
  \\ conj_tac
  >- (rw [lookup_insert, data_to_word_gcProofTheory.adjust_var_11]
      \\ first_x_assum drule \\ simp [])
  \\ conj_tac
  >- (qpat_x_assum `option_le t2.stack_max _` mp_tac
      \\ simp [call_env_push_env_dec_clock_stack_max, dataSemTheory.stack_consumed_def]
      \\ strip_tac
      \\ irule backendPropsTheory.option_le_trans
      \\ goal_assum (drule_at Any)
      \\ irule option_le_stackmax_bridge)
  \\ asm_exists_tac \\ fs []
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ match_mp_tac word_ml_inv_insert \\ fs [flat_def]
QED

Theorem lookup_set_var:
  lookup x ((set_var x y z).locals) = SOME y
Proof
  rw[wordSemTheory.set_var_def,lookup_insert]
QED

Theorem lookup_2_call_env[local]:
  lookup 0 ((call_env (x::ts) a1 a2).locals) = SOME x ∧
  lookup 2 ((call_env (x::y::ts) a1 a2).locals) = SOME y ∧
  lookup 4 ((call_env (x::y::z::ts) a1 a2).locals) = SOME z
Proof
  gvs [wordSemTheory.call_env_def,lookup_fromList2,lookup_fromList]
QED

(* Binary (two-argument) instance of AllocVar_thm_nary, used by assign_RefArray. *)

Theorem AllocVar_thm_binary[local]:
  ∀c l1 l2 s (t:('a,'c,'ffi) wordSem$state) locs a1 a2 x' xa i vv limit q r.
    state_rel c l1 l2 s t NONE locs ∧
    dataSem$cut_env (sptree$list_insert [a1; a2] x') s.locals = SOME xa ∧
    get_vars [a1; a2] s.locals = SOME [Number (&i); vv] ∧
    get_var 1 t = SOME (Word (n2w (2 * i))) ∧
    2 * i < dimword (:'a) ∧
    evaluate (AllocVar c limit (sptree$list_insert [a1; a2] x'), t) = (q,r) ∧
    limit < dimword (:'a) DIV 8 ⇒
    (q = SOME NotEnoughSpace ⇒
       r.ffi = s.ffi ∧ option_le r.stack_max s.stack_max ∧
       (c.gc_kind ≠ None ∧ i < limit ∧ no_thunks_in_refs s.refs ⇒
          s.limits.heap_limit <
            size_of_heap_args [Number (&i); vv] (cut_locals x' s) + (i + 1))) ∧
    (q ≠ SOME NotEnoughSpace ⇒
       i < limit ∧
       state_rel c l1 l2
         (s with <|locals := xa; space := i + 1|>) r NONE locs ∧
       FLOOKUP r.store (Temp 29w) = FLOOKUP t.store (Temp 29w) ∧
       r.code = t.code ∧ r.code_buffer = t.code_buffer ∧
       r.data_buffer = t.data_buffer ∧ r.compile_oracle = t.compile_oracle ∧
       q = NONE)
Proof
  rpt gen_tac \\ strip_tac
  \\ drule_all AllocVar_thm_nary
  \\ simp []
QED

Theorem assign_RefArray:
  op = MemOp RefArray ==> ^assign_thm_goal
Proof
  rpt strip_tac \\ imp_res_tac state_rel_arch_width \\ drule0 (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ `option_le x.stack_max s2.stack_max` by
    metis_tac[do_app_stack_max]
  \\ rpt_drule0 state_rel_cut_IMP \\ strip_tac
  \\ fs [assign_def,GSYM dimword_def] \\ rveq
  \\ fs [dataLangTheory.op_requires_names_def,
         dataLangTheory.op_space_reset_def,cut_state_opt_def]
  \\ Cases_on `names_opt` \\ fs []
  \\ drule_all (state_rel_cut_state_opt_SOME |> SRULE [cut_state_opt_def])
  \\ strip_tac
  \\ qpat_x_assum ‘_ (t with locals := y) NONE locs’ $ ASSUME_NAMED_TAC "with_locals"
  \\ imp_res_tac get_vars_IMP_LENGTH \\ fs [] \\ rw []
  \\ fs [do_app, allowed_op_def]
  \\ `?i w. vals = [Number i; w]` by (every_case_tac \\ fs [] \\ NO_TAC)
  \\ clean_tac
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ fs [LENGTH_EQ_2] \\ clean_tac
  \\ fs [LENGTH_EQ_2] \\ clean_tac
  \\ Cases_on `0 <= i` \\ fs []
  \\ drule0 NONNEG_INT \\ strip_tac \\ rveq \\ fs []
  \\ rename1 `&i`
  \\ simp[Once list_Seq_def]
  \\ simp[Once wordSemTheory.evaluate_def]
  \\ rveq \\ fs [adjust_var_def,get_vars_SOME_IFF]
  \\ fs [get_vars_SOME_IFF_data]
  \\ drule_all state_rel_get_var_Number_IMP_alt
  \\ strip_tac \\ rveq
  \\ drule_then drule evaluate_BignumHalt2
  \\ reverse(Cases_on `small_int (dimindex (:α)) (&i)`) \\ fs [] \\ strip_tac \\ fs []
  >- (simp[arg2_def, assign_RefArray_def]
      \\ once_rewrite_tac [list_Seq_def]
      \\ simp[wordSemTheory.evaluate_def]
      \\ fs[adjust_var_def]
      \\ conj_tac
      >- (`option_le t.stack_max x.stack_max` by
            (markerLib.LABEL_ASSUM "with_locals" mp_tac
             \\ rewrite_tac[state_rel_thm] \\ strip_tac \\ fs[])
          \\ qpat_x_assum `option_le r'.stack_max t.stack_max` mp_tac
          \\ qpat_x_assum `option_le t.stack_max x.stack_max` mp_tac
          \\ qpat_x_assum `option_le x.stack_max (OPTION_MAP2 MAX x.stack_max _)`
               mp_tac
          \\ rpt (pop_assum kall_tac)
          \\ metis_tac[option_le_trans])
      >- (strip_tac \\ rpt disj1_tac
          \\ `dimword (:α) DIV 8 ≤ i` by
              (qpat_x_assum `¬small_int (dimindex (:α)) (&i)` mp_tac
               \\ rewrite_tac[small_int_def,GSYM dimword_def] \\ intLib.COOPER_TAC)
          \\ `arch_size x.limits = dimindex (:α)` by
              (`(x.limits.arch_64_bit ⇔ dimindex (:α) = 64) ∧
                good_dimindex (:α)` by
                  (markerLib.LABEL_ASSUM "with_locals" mp_tac
                   \\ rewrite_tac[state_rel_thm] \\ strip_tac
                   \\ fs[limits_inv_def])
               \\ fs[arch_size_def,good_dimindex_def]
               \\ Cases_on `x.limits.arch_64_bit` \\ fs[])
          \\ `2 ** arch_size x.limits = dimword (:α)` by
               asm_rewrite_tac[dimword_def]
          \\ `dimword (:α) DIV 16 ≤ dimword (:α) DIV 8` by
             (`dimword (:α) DIV 16 = dimword (:α) DIV 8 DIV 2` by
                simp[DIV_DIV_DIV_MULT]
              \\ pop_assum SUBST1_TAC \\ simp[DIV_LESS_EQ])
          \\ qpat_x_assum `2 ** arch_size x.limits = dimword (:α)`
               (fn th => rewrite_tac[th])
          \\ decide_tac))
  \\ simp[arg2_def, assign_RefArray_def]
  \\ once_rewrite_tac [list_Seq_def]
  \\ fs [wordSemTheory.evaluate_def,word_exp_rw]
  \\ fs [wordSemTheory.get_var_def,wordSemTheory.get_vars_def]
  \\ fs[adjust_var_def]
  \\ once_rewrite_tac [list_Seq_def]
  \\ fs [wordSemTheory.evaluate_def,word_exp_rw]
  \\ fs [wordSemTheory.get_var_def]
  \\ sg `w' = n2w (2 * i) /\ 2 * i < dimword (:'a)`
  >- (fs [state_rel_def,get_vars_SOME_IFF_data]
      \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,get_var_def]
      \\ qpat_x_assum `word_ml_inv _ _ (THE x.tstamps) _ x.refs _` kall_tac
      \\ rpt_drule0 word_ml_inv_get_var_IMP
      \\ fs [get_var_def,wordSemTheory.get_var_def,adjust_var_def]
      \\ qpat_assum `lookup _ s.locals = SOME (Number (&i))` assume_tac
      \\ rpt (disch_then drule0) \\ fs []
      \\ fs [word_ml_inv_def] \\ rw []
      \\ fs [abs_ml_inv_def,bc_stack_ref_inv_def,v_inv_def] \\ rfs []
      \\ rw [] \\ fs [word_addr_def,Smallnum_def] \\ rw []
      \\ fs [small_int_def,GSYM dimword_def,X_LT_DIV]
      \\ match_mp_tac minus_2_word_and_id
      \\ fs [word_index,word_mul_n2w,bitTheory.BIT0_ODD,ODD_MULT])
  \\ rveq \\ fs []
  \\ `1 < dimindex (:α)` by
       (fs [state_rel_def,EVAL ``good_dimindex (:α)``] \\ NO_TAC) \\ fs []
  \\ `state_rel c l1 l2 s (set_var 1 (Word (n2w (2 * i))) t) NONE locs` by
        fs [wordSemTheory.set_var_def,state_rel_insert_1]
  \\ `dataSem$cut_env x' s.locals = SOME x.locals` by
       (qpat_x_assum `cut_state x' s = SOME x` mp_tac
        \\ rpt (pop_assum kall_tac)
        \\ simp[cut_state_def,CaseEq"option"] \\ strip_tac \\ rveq \\ simp[])
  \\ rpt_drule0 AllocVar_thm
  \\ qabbrev_tac `limit = MIN (2 ** c.len_size) (dimword (:α) DIV 16)`
  \\ fs [get_var_set_var_thm]
  \\ Cases_on `evaluate
       (AllocVar c limit x',set_var 1 (Word (n2w (2 * i))) t)`
  \\ fs []
  \\ disch_then drule
  \\ impl_tac
  >- (unabbrev_all_tac \\ fs []
      \\ fs [state_rel_def,EVAL ``good_dimindex (:'a)``,dimword_def])
  \\ strip_tac \\ fs [set_vars_sing]
  \\ fs[get_names_def]
  \\ rename [‘list_insert [a1; a2]’]
  \\ sg `?xa. dataSem$cut_env (list_insert [a1; a2] x') s.locals = SOME xa`
  >- (qpat_x_assum `dataSem$cut_env x' s.locals = SOME x.locals` mp_tac
      \\ qpat_x_assum `get_var a1 s.locals = SOME (Number (&i))` mp_tac
      \\ qpat_x_assum `get_var a2 s.locals = SOME w` mp_tac
      \\ rpt (pop_assum kall_tac)
      \\ rw[cut_env_def,get_var_def,list_insert_def,domain_insert,domain_lookup]
      \\ gvs[SUBSET_DEF])
  \\ pop_assum strip_assume_tac
  \\ Cases_on `evaluate (AllocVar c limit (list_insert [a1; a2] x'),
                 set_var 1 (Word (n2w (2 * i))) t)`
  \\ `get_var 1 (set_var 1 (Word (n2w (2 * i))) t) = SOME (Word (n2w (2 * i)))`
        by fs[get_var_set_var_thm,wordSemTheory.get_var_def,
              wordSemTheory.set_var_def,lookup_insert]
  \\ qpat_x_assum `evaluate (AllocVar c limit x', _) = _` kall_tac
  \\ `get_vars [a1; a2] s.locals = SOME [Number (&i); w]` by
        fs [dataSemTheory.get_vars_def]
  \\ rpt_drule0 AllocVar_thm_binary
  \\ `limit < dimword (:α) DIV 8` by
       (unabbrev_all_tac \\ fs []
        \\ fs [state_rel_def,EVAL ``good_dimindex (:'a)``,dimword_def])
  \\ disch_then drule
  \\ strip_tac
  \\ Cases_on `q' = SOME NotEnoughSpace` \\ fs []
  >- (`x.stack_max = s.stack_max` by
         (qpat_x_assum `cut_state x' s = SOME x` mp_tac
          \\ rpt (pop_assum kall_tac)
          \\ simp[cut_state_def,CaseEq"option"] \\ strip_tac \\ rveq \\ simp[])
      \\ `x.limits = s.limits` by
         (qpat_x_assum `cut_state x' s = SOME x` mp_tac
          \\ rpt (pop_assum kall_tac)
          \\ simp[cut_state_def,CaseEq"option"] \\ strip_tac \\ rveq \\ simp[])
      \\ `cut_locals x' s = x` by
         (qpat_x_assum `cut_state x' s = SOME x` mp_tac
          \\ qpat_x_assum `dataSem$cut_env x' s.locals = SOME x.locals` mp_tac
          \\ rpt (pop_assum kall_tac)
          \\ simp[cut_locals_def,cut_state_def,CaseEq"option"]
          \\ rpt strip_tac \\ rveq \\ simp[])
      \\ conj_tac
      >- (qpat_x_assum `option_le _.stack_max s.stack_max` mp_tac
          \\ qpat_x_assum
               `option_le x.stack_max (OPTION_MAP2 MAX x.stack_max _)` mp_tac
          \\ qpat_x_assum `x.stack_max = s.stack_max` mp_tac
          \\ rpt (pop_assum kall_tac)
          \\ metis_tac [option_le_trans])
      \\ strip_tac
      \\ Cases_on ‘no_thunks_in_refs x.refs’ \\ fs []
      \\ ‘no_thunks_in_refs s.refs’ by
        (imp_res_tac cut_state_refs_same \\ metis_tac [])
      \\ spose_not_then strip_assume_tac
      \\ qpat_x_assum `_ ∧ _ ⇒ s.limits.heap_limit < _` mp_tac
      \\ impl_tac
      >- (fs [Abbr `limit`, small_int_def]
          \\ fs [good_dimindex_def,dimword_def,state_rel_def,arch_size_def,
                 limits_inv_def]
          \\ rfs [])
      \\ fs [space_consumed_def]
      \\ qpat_x_assum `x.limits = s.limits` (fn th => rewrite_tac [GSYM th])
      \\ qpat_x_assum `_ ≤ x.limits.heap_limit` mp_tac
      \\ rpt (pop_assum kall_tac)
      \\ decide_tac)
  \\ qmatch_asmsub_rename_tac `evaluate (AllocVar _ _ _,_) = (NONE,ralloc)`
  \\ rveq \\ fs []
  \\ simp[list_Seq_def]
  \\ clean_tac \\ fs [wordSemTheory.evaluate_def]
  \\ fs [wordSemTheory.bad_dest_args_def]
  \\ fs [wordSemTheory.add_ret_loc_def,wordSemTheory.find_code_def]
  \\ drule0 lookup_RefByte_location \\ strip_tac \\ fs [get_names_def]
  \\ fs [cut_state_opt_def,cut_state_def]
  \\ `ralloc.termdep = t.termdep` by
   (imp_res_tac wordSemTheory.evaluate_clock \\ fs [wordSemTheory.set_var_def])
  \\ fs[]
  \\ fs[wordSemTheory.get_vars_def,wordSemTheory.get_var_def,domain_adjust_sets]
  \\ `get_var a1 xa = SOME (Number (&i)) /\ get_var a2 xa = SOME w` by
       (qpat_x_assum `dataSem$cut_env (list_insert [a1; a2] x') s.locals = SOME xa` mp_tac
        \\ qpat_x_assum `get_var a1 s.locals = SOME (Number (&i))` mp_tac
        \\ qpat_x_assum `get_var a2 s.locals = SOME w` mp_tac
        \\ rpt (pop_assum kall_tac)
        \\ rw [cut_env_def,get_var_def,list_insert_def]
        \\ gvs [lookup_mk_wf,lookup_inter_alt])
  \\ drule state_rel_get_var_IMP
  \\ simp[]
  \\ disch_then imp_res_tac
  \\ fs[adjust_var_def]
  \\ drule state_rel_get_var_Number_IMP
  \\ simp[]
  \\ disch_then drule
  \\ disch_then drule
  \\ strip_tac
  \\ fs[adjust_var_def,wordSemTheory.get_var_def] >> rveq
  \\ drule (state_rel_cut_state_opt_SOME |> SRULE [cut_state_opt_def])
  \\ qabbrev_tac ‘s6 = x with <|locals := x.locals; space := i + 1|>’
  \\ ‘dataSem$cut_env x' xa = SOME x.locals’ by
       (drule_all cut_env_cut_env_list_insert \\ simp [])
  \\ ‘cut_state x' (s with <|locals := xa; space := i + 1|>) = SOME s6’ by
       (qunabbrev_tac ‘s6’
        \\ qpat_x_assum ‘dataSem$cut_env x' xa = SOME x.locals’ mp_tac
        \\ qpat_x_assum ‘s with locals := x.locals = x’ (mp_tac o GSYM)
        \\ rpt (pop_assum kall_tac)
        \\ rpt strip_tac
        \\ gvs [cut_state_def, dataSemTheory.state_component_equality])
  \\ disch_then $ drule_at $ Pos last
  \\ disch_then $ qspecl_then [‘[]’,‘[]’] mp_tac
  \\ impl_tac >- EVAL_TAC
  \\ strip_tac \\ gvs []
  \\ drule cut_env_IMP_cut_envs \\ strip_tac \\ simp []
  \\ fs [RefArray_code_def]
  \\ `1 < dimword (:'a) /\ 2 < dimword (:'a) /\
      shift (dimindex (:'a)) < dimword (:'a) /\
      shift_length c - shift (dimindex (:'a)) < dimword (:'a) /\
      dimindex (:'a) - c.len_size - 1 < dimword (:'a) /\
      dimindex (:'a) - c.len_size - 2 < dimword (:'a)` by
       (assume_tac dimindex_lt_dimword
        \\ `good_dimindex (:'a)` by fs [state_rel_def]
        \\ `shift_length c < dimindex (:'a)` by
              fs [state_rel_def,memory_rel_def,heap_in_memory_store_def]
        \\ fs [shift_def,good_dimindex_def,dimword_def] \\ decide_tac)
  \\ once_rewrite_tac [list_Seq_def]
  \\ fs [wordSemTheory.evaluate_def,word_exp_rw]
  \\ once_rewrite_tac [list_Seq_def]
  \\ gvs [lookup_2_call_env]
  \\ fs[lookup_fromList2,lookup_fromList]
  \\ fs[word_exp_rw,wordSemTheory.get_var_def]
  \\ IF_CASES_TAC
  THEN1 (fs [shift_def,state_rel_def,EVAL ``good_dimindex (:'a)``])
  \\ pop_assum kall_tac
  \\ fs[]
  \\ once_rewrite_tac [list_Seq_def]
  \\ once_rewrite_tac [wordSemTheory.evaluate_def]
  \\ simp [Once wordSemTheory.evaluate_def]
  \\ fs[wordSemTheory.dec_clock_def]
  \\ fs [word_exp_rw]
  \\ fs[EVAL ``(set_var x y z).store``]
  \\ `(?trig1. FLOOKUP ralloc.store TriggerGC = SOME (Word trig1)) /\
      (?eoh1. FLOOKUP ralloc.store EndOfHeap = SOME (Word eoh1)) /\
      (?cur1. FLOOKUP ralloc.store CurrHeap = SOME (Word cur1))` by
        (fs [state_rel_thm,memory_rel_def,heap_in_memory_store_def] \\ NO_TAC)
  \\ fs[lookup_set_var,wordSemTheory.set_store_def,FLOOKUP_SIMP,
        wordSemTheory.set_var_def]
  \\ simp[Once list_Seq_def]
  \\ simp [Once wordSemTheory.evaluate_def]
  \\ simp [Once wordSemTheory.evaluate_def]
  \\ fs [word_exp_rw]
  \\ simp [wordSemTheory.set_var_def,lookup_insert,wordSemTheory.set_store_def]
  \\ fs[FLOOKUP_UPDATE,FAPPLY_FUPDATE_THM]
  \\ simp [wordSemTheory.evaluate_def,word_exp_rw,FLOOKUP_SIMP,
           wordSemTheory.set_var_def]
  \\ simp[Once list_Seq_def]
  \\ simp [wordSemTheory.evaluate_def,word_exp_rw,FLOOKUP_SIMP,
           wordSemTheory.set_var_def,wordSemTheory.set_store_def,lookup_insert,
           wordSemTheory.get_var_def,wordSemTheory.mem_store_def]
  \\ fs[lookup_set_var]
  \\ IF_CASES_TAC
  THEN1 (fs [shift_def,state_rel_def,EVAL ``good_dimindex (:'a)``])
  \\ pop_assum kall_tac
  \\ fs[]
  \\ fs [word_exp_rw,wordSemTheory.set_store_def,lookup_insert,
         wordSemTheory.get_var_def,wordSemTheory.mem_store_def,
         FLOOKUP_UPDATE,FAPPLY_FUPDATE_THM]
  \\ fs[wordSemTheory.set_var_def,lookup_insert]
  \\ fs[lookup_fromList2,lookup_fromList]
  \\ simp[Once list_Seq_def]
  \\ simp[Once list_Seq_def]
  \\ simp[wordSemTheory.evaluate_def]
  \\ fs [word_exp_rw,wordSemTheory.set_store_def,lookup_insert,
         wordSemTheory.get_var_def,wordSemTheory.mem_store_def,
         lookup_2_call_env,wordSemTheory.set_var_def]
  \\ `n2w (2 * i) ⋙ 1 = n2w i` by
   (once_rewrite_tac [GSYM w2n_11] \\ rewrite_tac [w2n_lsr]
    \\ fs [ONCE_REWRITE_RULE[MULT_COMM]MULT_DIV])
  \\ fs [WORD_LEFT_ADD_DISTRIB]
  \\ `good_dimindex(:'a)` by fs [state_rel_def]
  \\ fs [shift_lsl]
  \\ qhdtm_assum `state_rel` (strip_assume_tac o REWRITE_RULE[state_rel_thm])
  \\ fs[]
  \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC]
  (* The (w,w') pair lives only in the args-augmented cut (a2 ∉ x'), so cons
     it from the augmented memory_rel and rearrange down to the narrow list. *)
  \\ sg ‘memory_rel c ralloc.be (THE s6.tstamps) s6.refs s6.space ralloc.store
           ralloc.memory ralloc.mdomain
           ((w,w')::
            (join_env s6.locals
               (toAList (inter (union y2 y1) (adjust_set s6.locals))) ++
             [(the_global s6.global,ralloc.store ' Globals)] ++
             flat s6.stack ralloc.stack))’
  >- (qpat_assum ‘state_rel c l1 l2 (s with <|locals := xa; space := i + 1|>)
        ralloc NONE locs’ (strip_assume_tac o REWRITE_RULE [state_rel_thm])
      \\ ‘s6 = s with <|locals := x.locals; space := i + 1|>’ by
           (qpat_x_assum ‘cut_state x' _ = SOME s6’ mp_tac
            \\ qpat_x_assum ‘dataSem$cut_env x' xa = SOME x.locals’ mp_tac
            \\ rpt (pop_assum kall_tac)
            \\ rpt strip_tac
            \\ gvs [cut_state_def]
            \\ simp [dataSemTheory.state_component_equality])
      \\ ‘lookup a2 xa = SOME w’ by fs [dataSemTheory.get_var_def]
      \\ ‘lookup (adjust_var a2) ralloc.locals = SOME w'’ by fs [adjust_var_def]
      \\ gvs []
      \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC]
      \\ rpt_drule0 memory_rel_lookup
      \\ match_mp_tac memory_rel_rearrange
      \\ ‘∀k v. lookup k x.locals = SOME v ⇒ lookup k xa = SOME v’ by
           (qpat_x_assum ‘dataSem$cut_env x' xa = SOME x.locals’ mp_tac
            \\ rpt (pop_assum kall_tac)
            \\ simp [dataSemTheory.cut_env_def, AllCaseEqs()]
            \\ strip_tac \\ rpt strip_tac
            \\ qpat_x_assum ‘lookup _ x.locals = SOME _’ mp_tac
            \\ qpat_x_assum ‘inter xa x' = x.locals’ (fn th => rewrite_tac [GSYM th])
            \\ simp [lookup_inter_alt])
      \\ ‘∀k v. lookup k (union y2 y1) = SOME v ⇒ lookup k ralloc.locals = SOME v’ by
           (rpt strip_tac \\ drule_all cut_env_lookup \\ simp [])
      \\ rw [] \\ fs []
      \\ disj2_tac \\ disj1_tac
      \\ drule_at (Pos last) join_env_submap_MEM \\ simp []
      \\ disch_then irule \\ rw [] \\ res_tac \\ simp [])
  \\ drule memory_rel_RefArray
  \\ qabbrev_tac `new = LEAST ptr. ptr ∉ domain x.refs`
  \\ `new ∉ domain x.refs` by metis_tac [LEAST_NOTIN_spt_DOMAIN]
  \\ `encode_header c 2 i = SOME (make_header c 2 i)` by
   (fs[encode_header_def,memory_rel_def,heap_in_memory_store_def]
    \\ reverse conj_tac THEN1
     (fs[encode_header_def,memory_rel_def,heap_in_memory_store_def,EXP_SUB]
      \\ unabbrev_all_tac \\ fs [ONCE_REWRITE_RULE [MULT_COMM] MULT_DIV]
      \\ rfs [good_dimindex_def,dimword_def])
    \\ `1 < dimindex (:α) − (c.len_size + 2)` by
     (qpat_assum `c.len_size + _ < dimindex (:α)` mp_tac
      \\ rpt (pop_assum kall_tac) \\ decide_tac)
    \\ fs[good_dimindex_def,dimword_def])
  \\ gvs [Abbr‘s6’]
  \\ rpt(disch_then drule)
  \\ impl_tac >- simp []
  \\ `good_dimindex(:'a)` by(FULL_SIMP_TAC std_ss [state_rel_def])
  \\ simp[intLib.COOPER_PROVE ``2 * k DIV 2 = k``]
  \\ strip_tac
  \\ fs [store_list_def,TWO_MUL_LSL]
  \\ fs [word_exp_rw,FLOOKUP_UPDATE,wordSemTheory.set_var_def,WORD_LEFT_ADD_DISTRIB]
  \\ qabbrev_tac `ww = eoh1 + -1w * bytes_in_word + -1w * (bytes_in_word * n2w i)`
  \\ qabbrev_tac `ww1 = trig1 + -1w * bytes_in_word + -1w * (bytes_in_word * n2w i)`
  \\ reverse IF_CASES_TAC
  >- (rfs[Smallnum_def] >>
      fs[memory_rel_def] >>
      imp_res_tac store_list_domain >>
      fs [word_exp_rw,FLOOKUP_UPDATE,wordSemTheory.set_var_def,
          WORD_LEFT_ADD_DISTRIB] >>
      qsuff_tac `eoh1 + -1w * bytes_in_word + -1w * (bytes_in_word * n2w i)
       = eoh1 + -1w * (bytes_in_word * n2w (i + 1))`
      >- (strip_tac >> fs[]) >>
      fs[GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB])
  \\ suspend "replicate"
QED

Resume assign_RefArray[replicate]:
  fs[list_Seq_def]
  \\ qmatch_goalsub_abbrev_tac `(Call _ _ _ _,bigenv)`
  \\ `(?md. lookup Replicate_location bigenv.code = SOME (5,Replicate_code c,md))`
      by(imp_res_tac lookup_RefByte_location
         \\ fs[lookup_insert,lookup_fromList2,lookup_fromList,
               wordSemTheory.dec_clock_def,Abbr `bigenv`])
  \\ drule (SIMP_RULE std_ss [PULL_EXISTS] Replicate_code_thm)
  \\ simp[wordSemTheory.get_var_def]
  \\ `i < bigenv.clock` by fs[Abbr`bigenv`]
  \\ disch_then(pop_assum o mp_then Any mp_tac)
  \\ qmatch_asmsub_abbrev_tac `insert 1 (Word www)`
  \\ `(eoh1 + bytes_in_word + -1w * (bytes_in_word * n2w (i + 1)))
      = www + bytes_in_word`
       by(fs[Abbr`www`,Smallnum_def,GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB])
  \\ fs[]
  \\ `store_list (www + bytes_in_word) (REPLICATE i w') bigenv.memory
                bigenv.mdomain = SOME m1`
     by(match_mp_tac EQ_TRANS >> HINT_EXISTS_TAC >>
        reverse conj_tac >- simp[] >>
        qpat_x_assum `store_list _ _ _ _ = _` kall_tac >>
        rw[Abbr `bigenv`] >>
        simp[make_header_def] >>
        rpt(AP_THM_TAC ORELSE AP_TERM_TAC) >>
        simp[Smallnum_def] >>
        simp[TWO_MUL_LSL] >>
        fs[word_mul_n2w,LEFT_ADD_DISTRIB] >>
        rw[Abbr`www`,Smallnum_def,TWO_MUL_LSL,Abbr`ww`,
           GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB] >>
        AP_TERM_TAC >> AP_TERM_TAC >>
        `arch_width_bits c.arch_width = dimindex (:'a)` by
          (qpat_x_assum `memory_rel c _ _ _ _ _ _ _ _`
             (fn th => ACCEPT_TAC (MATCH_MP memory_rel_arch_width th))) >>
        `c.len_size <> 0 /\ c.len_size + 9 < dimindex (:'a)` by
          (qpat_x_assum `memory_rel c _ _ _ _ _ _ _ _`
             (fn th => ACCEPT_TAC (MATCH_MP memory_rel_len_size th))) >>
        `dimindex (:α) - (c.len_size + 1) + 1 = dimindex (:α) - c.len_size`
          by DECIDE_TAC >>
        asm_rewrite_tac [word_add_n2w] >>
        irule shifted_header_or >>
        `4 <= dimindex (:α) - c.len_size` by DECIDE_TAC >>
        `2 ** 4 <= 2 ** (dimindex (:α) - c.len_size)` by
          (irule bitTheory.TWOEXP_MONO2 >> fs []) >>
        fs [])
  \\ disch_then drule
  \\ disch_then(mp_tac o CONV_RULE(RESORT_FORALL_CONV rev))
  \\ disch_then(qspecl_then [`3`,`2`,`4`,`1`,`0`] mp_tac)
  \\ simp[Abbr `bigenv`,lookup_insert,lookup_fromList2,lookup_fromList,
          Smallnum_def,lookup_2_call_env]
  \\ strip_tac
  \\ simp[]
  \\ CASE_TAC
  >- (sg ‘F’ \\ fs []
      \\ gvs [wordSemTheory.pop_env_def,wordSemTheory.push_env_def]
      \\ pairarg_tac \\ gvs [])
  \\ rename [‘domain t8.locals = domain y1 ∪ domain y2’]
  \\ ‘domain t8.locals = domain y1 ∪ domain y2’ by
    (qpat_x_assum ‘pop_env _ = _’ mp_tac
     \\ simp [wordSemTheory.pop_env_def,AllCaseEqs(),
             wordSemTheory.push_env_def,
             wordSemTheory.call_env_def]
     \\ pairarg_tac \\ simp []
     \\ strip_tac \\ gvs [domain_union,domain_fromAList_toAList]
     \\ drule env_to_list_domain
     \\ gvs [AC UNION_COMM UNION_ASSOC])
  \\ simp []
  \\ qpat_x_assum ‘pop_env _ = _’ mp_tac
  \\ fs[dataSemTheory.set_var_def]
  \\ simp [wordSemTheory.pop_env_def,AllCaseEqs(),
           wordSemTheory.push_env_def,
           wordSemTheory.call_env_def]
  \\ pairarg_tac \\ gvs [] \\ strip_tac \\ gvs []
  \\ simp [wordSemTheory.set_vars_def,alist_insert_def]
  \\ qpat_x_assum ‘state_rel _ _ _ _ _ _ _’ mp_tac
  \\ simp[state_rel_thm,lookup_insert,adjust_var_11]
  \\ rewrite_tac [GSYM adjust_var_def]
  \\ conj_tac
  >- (fs [code_oracle_rel_def,FLOOKUP_UPDATE,bytes_in_word_def,n2w_sub]
      \\ once_rewrite_tac [GSYM word_sub_def]
      \\ rewrite_tac [WORD_LEFT_SUB_DISTRIB]
      \\ fs [GSYM bytes_in_word_def]
      \\ simp [FUN_EQ_THM,o_DEF,shift_seq_def,FORALL_PROD]
      \\ rewrite_tac [GSYM WORD_ADD_ASSOC]
      \\ AP_TERM_TAC \\ fs []
      \\ rewrite_tac [WORD_ADD_ASSOC]
      \\ once_rewrite_tac [WORD_ADD_COMM]
      \\ rewrite_tac [WORD_ADD_ASSOC,wordsTheory.WORD_ADD_LINV]
      \\ fs [])
  \\ conj_tac
  >- (simp [lookup_union,lookup_fromAList,CaseEq"option",ALOOKUP_toAList]
      \\ disj1_tac \\ drule_all lookup_loc_lemma \\ simp_tac std_ss [])
  \\ conj_tac
  >- (simp [wordSemTheory.set_vars_def,alist_insert_def,lookup_insert,
            adjust_var_11]
      \\ rw [] \\ pop_assum mp_tac
      \\ rewrite_tac [IS_SOME_EXISTS,GSYM domain_lookup]
      \\ drule adjust_var_cut_env_IMP_MEM \\ simp []
      \\ simp_tac std_ss []
      \\ qpat_x_assum ‘dataSem$cut_env x' s.locals = SOME x.locals’ mp_tac
      \\ rpt $ pop_assum kall_tac
      \\ rewrite_tac [IS_SOME_EXISTS,GSYM domain_lookup]
      \\ gvs [cut_env_def,CaseEq"option"]
      \\ strip_tac
      \\ metis_tac [domain_inter,IN_INTER])
  \\ conj_tac
  >- (fs [wordSemTheory.call_env_def,wordSemTheory.push_env_def]
      \\ imp_res_tac evaluate_stack_max_le \\ fs[]
      \\ match_mp_tac option_le_trans \\ PURE_ONCE_REWRITE_TAC[CONJ_SYM]
      \\ goal_assum drule
      \\ rw[option_le_max_right,stack_size_eq,
            AC option_add_comm option_add_assoc])
  \\ conj_tac
  >- (fs [wordSemTheory.call_env_def,wordSemTheory.push_env_def]
      \\ drule_then match_mp_tac option_le_trans
      \\ imp_res_tac stack_rel_IMP_size_of_stack
      \\ rw[size_of_stack_eq,option_le_max_right,option_le_max,
            option_map2_max_add,AC option_add_comm option_add_assoc,
            option_le_eq_eqns,option_map2_max_add,stack_size_eq,option_le_add])
  \\ conj_tac
  >- gvs [FLOOKUP_SIMP]
  \\ simp [wordSemTheory.set_vars_def,alist_insert_def,lookup_insert,
        adjust_var_11]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ irule memory_rel_insert
  \\ simp [FAPPLY_FUPDATE_THM]
  \\ qhdtm_x_assum `memory_rel` mp_tac
  \\ `EndOfHeap <> TriggerGC` by fs []
  \\ pop_assum (fn th => fs [MATCH_MP FUPDATE_COMMUTES th])
  \\ fs [GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB,Abbr`ww1`]
  \\ `ww = www` by(unabbrev_all_tac >> simp[Smallnum_def])
  \\ simp[]
  \\ match_mp_tac (METIS_PROVE [] “x = y ⇒ x ⇒ y”)
  \\ AP_TERM_TAC
  \\ simp []
  \\ conj_tac >- gvs [make_ptr_def]
  \\ AP_TERM_TAC
  \\ AP_TERM_TAC
  \\ simp []
  \\ simp [lookup_inter_alt]
  \\ rw []
  \\ fs [lookup_union,lookup_fromAList,ALOOKUP_toAList]
  \\ imp_res_tac env_to_list_lookup_equiv
  \\ simp []
QED

Finalise assign_RefArray;

val _ = augment_srw_ss [rewrites [compiler_tag_mask_i2w]];

Theorem assign_LengthByte:
  op = MemOp LengthByte ==> ^assign_thm_goal
Proof
  rpt strip_tac
  \\ gvs [dataLangTheory.op_requires_names_def,
          dataLangTheory.op_space_reset_def,
          dataSemTheory.cut_state_opt_def]
  \\ gvs [do_app,AllCaseEqs(),allowed_op_def]
  \\ fs [assign_def,eq_eval,wordSemTheory.get_store_def]
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ gvs [LENGTH_EQ_NUM_compute]
  \\ imp_res_tac get_vars_IMP_LENGTH
  \\ gvs [LENGTH_EQ_NUM_compute]
  \\ last_x_assum mp_tac
  \\ simp [Once state_rel_thm] \\ strip_tac
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ drule0 (memory_rel_get_vars_IMP |> GEN_ALL)
  \\ disch_then drule0 \\ fs [set_var_def]
  \\ strip_tac
  \\ rpt_drule0 memory_rel_ByteArray_IMP \\ fs []
  \\ qpat_abbrev_tac`ttt = COND _ _ _`
  \\ rw []
  \\ fs [assign_def]
  \\ fs [wordSemTheory.get_vars_def]
  \\ `2 < dimword (:'a)` by
       (assume_tac dimindex_lt_dimword \\
        fs [good_dimindex_def] \\ decide_tac)
  \\ `dimindex (:'a) - shift (dimindex (:'a)) - c.len_size < dimword (:'a)` by
       (assume_tac dimindex_lt_dimword \\ decide_tac)
  \\ eval_tac
  \\ fs [wordSemTheory.get_var_def,wordSemTheory.get_var_imm_def]
  \\ fs [asmTheory.word_cmp_def,word_and_one_eq_0_iff
           |> SIMP_RULE (srw_ss()) []]
  \\ `shift_length c < dimindex (:α)` by (fs [memory_rel_def] \\ NO_TAC)
  \\ gvs [CaseEq"option"]
  \\ rename [`(real_addr c (adjust_var hh))`]
  \\ `word_exp t (real_addr c (adjust_var hh)) = SOME (Word a)` by (
    match_mp_tac (GEN_ALL get_real_addr_lemma)
    \\ fs [wordSemTheory.get_var_def] \\ NO_TAC) \\ fs []
  \\ simp [SF DNF_ss]
  \\ disj2_tac
  \\ pop_assum kall_tac
  \\ simp[]
  \\ `2 < dimindex (:'a)` by (
    fs [good_dimindex_def] \\ fs [])
  \\ fs [state_rel_thm] \\ fs [lookup_insert,adjust_var_11] \\ rw [] \\ fs []
  THEN1 (fs [good_dimindex_def] \\ rfs[shift_def])
  THEN1 fs [option_le_max_right]
  \\ fs [WORD_MUL_LSL,WORD_LEFT_ADD_DISTRIB,GSYM word_add_n2w]
  \\ fs [word_mul_n2w]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ match_mp_tac memory_rel_insert \\ fs []
  \\ fs[good_dimindex_def,markerTheory.Abbrev_def]
  \\ rfs[shift_def,bytes_in_word_def,WORD_LEFT_ADD_DISTRIB,word_mul_n2w]
  \\ match_mp_tac (IMP_memory_rel_Number_num3
       |> SIMP_RULE std_ss [WORD_MUL_LSL,word_mul_n2w]) \\ fs []
  \\ fs[good_dimindex_def]
QED

Theorem assign_Length:
  op = MemOp Length ==> ^assign_thm_goal
Proof
  rpt strip_tac
  \\ gvs [dataLangTheory.op_requires_names_def,
          dataLangTheory.op_space_reset_def,
          dataSemTheory.cut_state_opt_def]
  \\ gvs [do_app,AllCaseEqs(),allowed_op_def]
  \\ fs [assign_def,eq_eval,wordSemTheory.get_store_def]
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ gvs [LENGTH_EQ_NUM_compute]
  \\ imp_res_tac get_vars_IMP_LENGTH
  \\ gvs [LENGTH_EQ_NUM_compute]
  \\ last_x_assum mp_tac
  \\ simp [Once state_rel_thm] \\ strip_tac
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ drule0 (memory_rel_get_vars_IMP |> GEN_ALL)
  \\ disch_then drule0 \\ fs [set_var_def]
  \\ strip_tac
  \\ rpt_drule0 memory_rel_ValueArray_IMP \\ fs [] \\ rw []
  \\ fs [assign_def]
  \\ fs [wordSemTheory.get_vars_def]
  \\ `2 < dimword (:'a)` by
       (assume_tac dimindex_lt_dimword \\
        fs [good_dimindex_def] \\ decide_tac)
  \\ `dimindex (:'a) - c.len_size < dimword (:'a)` by
       (assume_tac dimindex_lt_dimword \\ decide_tac)
  \\ eval_tac
  \\ fs [wordSemTheory.get_var_def,wordSemTheory.get_var_imm_def]
  \\ fs [asmTheory.word_cmp_def,word_and_one_eq_0_iff
           |> SIMP_RULE (srw_ss()) []]
  \\ `shift_length c < dimindex (:α)` by (fs [memory_rel_def] \\ NO_TAC)
  \\ rename [`(real_addr c (adjust_var hh))`]
  \\ `word_exp t (real_addr c (adjust_var hh)) = SOME (Word a)` by
       (match_mp_tac (GEN_ALL get_real_addr_lemma)
        \\ gvs [wordSemTheory.get_var_def, AllCaseEqs()])
  \\ fs []
  \\ fs [GSYM NOT_LESS,GREATER_EQ]
  \\ `c.len_size <> 0` by
      (fs [memory_rel_def,heap_in_memory_store_def] \\ NO_TAC)
  \\ fs [NOT_LESS]
  \\ `~(dimindex (:α) <= 2)` by
         (fs [good_dimindex_def] \\ NO_TAC)
  \\ fs [state_rel_thm] \\ fs [lookup_insert,adjust_var_11] \\ rw [] \\ fs []
  >- fs [option_le_max_right]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ match_mp_tac memory_rel_insert \\ fs []
  \\ fs [decode_length_def]
  \\ match_mp_tac IMP_memory_rel_Number_num \\ fs []
QED

Theorem assign_BoundsCheckArray:
   assign c secn l dest (MemOp BoundsCheckArray) args names =
      case args of
      | [v1;v2] => (list_Seq [Assign 1
                               (let addr = real_addr c (adjust_var v1) in
                                let header = Load addr in
                                let k = arch_width_bits c.arch_width - c.len_size in
                                  ShiftN Lsr header k);
                              Assign 3 (ShiftVar (arch_width_bits c.arch_width) Ror (adjust_var v2) 1);
                              If Lower 3 (Reg 1)
                               (Assign (adjust_var dest) TRUE_CONST)
                               (Assign (adjust_var dest) FALSE_CONST)],l)
      | _ => (Skip:wordLang$prog,l)
Proof
  fs [assign_def] \\ every_case_tac \\ fs []
QED

Theorem assign_BoundsCheckArray[allow_rebind]:
  op = MemOp BoundsCheckArray ==> ^assign_thm_goal
Proof
  strip_tac
  \\ rpt strip_tac
  \\ gvs [dataLangTheory.op_requires_names_def,
          dataLangTheory.op_space_reset_def,
          dataSemTheory.cut_state_opt_def]
  \\ drule0 (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ imp_res_tac get_vars_IMP_LENGTH \\ fs [] \\ rw []
  \\ fs [do_app,allowed_op_def] \\ rfs [] \\ every_case_tac \\ fs []
  \\ clean_tac \\ fs []
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ fs [LENGTH_EQ_2] \\ clean_tac
  \\ fs [get_var_def]
  \\ `shift_length c - shift (dimindex (:'a)) < dimword (:'a) /\
      dimindex (:'a) - c.len_size < dimword (:'a) /\
      2 < dimword (:'a)` by
    (fs [dimindex_lt_dimword,state_rel_thm,memory_rel_def,heap_in_memory_store_def])
  \\ simp [state_rel_thm] \\ eval_tac
  \\ fs [state_rel_thm,option_le_max_right] \\ eval_tac
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ rpt_drule0 (memory_rel_get_vars_IMP |> GEN_ALL)
  \\ strip_tac
  \\ drule0 (GEN_ALL memory_rel_ValueArray_IMP) \\ fs [] \\ rw []
  \\ fs [assign_BoundsCheckArray]
  \\ fs [get_vars_SOME_IFF_data,get_vars_SOME_IFF]
  \\ qmatch_asmsub_rename_tac `(Number i,w2)`
  \\ `?wi. w2 = Word wi` by
    (drule0 memory_rel_tl \\ strip_tac
     \\ imp_res_tac memory_rel_any_Number_IMP \\ simp [] \\ NO_TAC)
  \\ rveq
  \\ once_rewrite_tac [list_Seq_def]
  \\ fs [eq_eval]
  \\ `shift_length c < dimindex (:α)` by (fs [memory_rel_def] \\ NO_TAC)
  \\ `word_exp t (real_addr c (adjust_var a1)) = SOME (Word a)` by
       (match_mp_tac (GEN_ALL get_real_addr_lemma)
        \\ fs [wordSemTheory.get_var_def] \\ NO_TAC) \\ fs []
  \\ fs [eq_eval,word_sh_def]
  \\ fs [list_Seq_def,eq_eval]
  \\ simp [Once word_exp_ShiftVar_bits]
  \\ `c.len_size < dimindex (:α) /\
      ~(dimindex (:α) ≥ c.len_size + dimindex (:α))` by
         (fs [memory_rel_def,heap_in_memory_store_def] \\ NO_TAC)
  \\ fs [eq_eval,WORD_LO_word_0,adjust_var_11]
  \\ fs [decode_length_def]
  \\ drule0 memory_rel_tl \\ strip_tac
  \\ drule0 (GEN_ALL memory_rel_bounds_check)
  \\ disch_then (qspec_then `LENGTH l'` mp_tac)
  \\ impl_tac THEN1
    (fs [small_int_def,dimword_def,good_dimindex_def] \\ rfs [])
  \\ strip_tac \\ fs []
  \\ qpat_abbrev_tac `bool_res <=> 0 ≤ i ∧ i < &LENGTH _`
  \\ Cases_on `bool_res`
  \\ fs [] \\ fs [lookup_insert,adjust_var_11] \\ rw [] \\ fs []
  \\ simp[inter_insert_ODD_adjust_set,GSYM Boolv_def,option_le_max_right]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ match_mp_tac memory_rel_insert \\ fs []
  \\ TRY (match_mp_tac memory_rel_Boolv_T \\ fs [])
  \\ TRY (match_mp_tac memory_rel_Boolv_F \\ fs [])
QED

Theorem assign_BoundsCheckByte:
   assign c secn l dest (MemOp (BoundsCheckByte leq)) args names =
      case args of
      | [v1;v2] => (list_Seq [Assign 1
                               (let addr = real_addr c (adjust_var v1) in
                                let header = Load addr in
                                let extra = (if arch_width_bits c.arch_width = 32 then 2 else 3) in
                                let k = arch_width_bits c.arch_width - c.len_size - extra in
                                  Op Sub [ShiftN Lsr header k; Const (&(arch_bytes c.arch_width))]);
                              Assign 3 (ShiftVar (arch_width_bits c.arch_width) Ror (adjust_var v2) 1);
                              (if leq then If NotLower 1 (Reg 3) else
                                           If Lower 3 (Reg 1))
                               (Assign (adjust_var dest) TRUE_CONST)
                               (Assign (adjust_var dest) FALSE_CONST)],l)
      | _ => (Skip:wordLang$prog,l)
Proof
  fs [assign_def,asmTheory.arch_bytes_def,shift_def] \\ every_case_tac \\ fs [asmTheory.arch_bytes_def,shift_def]
QED

Theorem assign_BoundsCheckByte[allow_rebind]:
  (∃leq. op = MemOp (BoundsCheckByte leq)) ==> ^assign_thm_goal
Proof
  strip_tac
  \\ rpt strip_tac
  \\ gvs [dataLangTheory.op_requires_names_def,
          dataLangTheory.op_space_reset_def,
          dataSemTheory.cut_state_opt_def]
  \\ drule0 (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ imp_res_tac get_vars_IMP_LENGTH \\ fs [] \\ rw []
  \\ fs [do_app,allowed_op_def] \\ rfs [] \\ every_case_tac \\ fs []
  \\ clean_tac \\ fs []
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ fs [LENGTH_EQ_2] \\ clean_tac
  \\ fs [get_var_def]
  \\ `shift_length c - shift (dimindex (:'a)) < dimword (:'a) /\
      dimindex (:'a) - c.len_size < dimword (:'a) /\
      2 < dimword (:'a)` by
    (fs [dimindex_lt_dimword,state_rel_thm,memory_rel_def,heap_in_memory_store_def])
  \\ simp [state_rel_thm] \\ eval_tac
  \\ fs [state_rel_thm,option_le_max_right] \\ eval_tac
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ rpt_drule0 (memory_rel_get_vars_IMP |> GEN_ALL)
  \\ strip_tac
  \\ drule0 (GEN_ALL memory_rel_ByteArray_IMP) \\ fs [] \\ rw []
  \\ fs [assign_BoundsCheckByte]
  \\ fs [get_vars_SOME_IFF_data,get_vars_SOME_IFF]
  \\ qmatch_asmsub_rename_tac `(Number i,w2)`
  \\ `?wi. w2 = Word wi` by
    (drule0 memory_rel_tl \\ strip_tac
     \\ imp_res_tac memory_rel_any_Number_IMP \\ simp [] \\ NO_TAC)
  \\ rveq
  \\ once_rewrite_tac [list_Seq_def]
  \\ fs [eq_eval]
  \\ `shift_length c < dimindex (:α)` by (fs [memory_rel_def] \\ NO_TAC)
  \\ `word_exp t (real_addr c (adjust_var a1)) = SOME (Word a)` by
       (match_mp_tac (GEN_ALL get_real_addr_lemma)
        \\ fs [wordSemTheory.get_var_def] \\ NO_TAC) \\ fs []
  \\ fs [eq_eval,word_sh_def]
  \\ fs [list_Seq_def,eq_eval]
  \\ simp [Once word_exp_ShiftVar_bits]
  \\ `c.len_size < dimindex (:α) /\
      ~(dimindex (:α) ≥ c.len_size + dimindex (:α))` by
         (fs [memory_rel_def,heap_in_memory_store_def] \\ NO_TAC)
  \\ fs [eq_eval,WORD_LO_word_0,adjust_var_11]
  \\ fs [good_dimindex_def] \\ rfs []
  \\ fs [decode_length_def,wordsTheory.WORD_NOT_LOWER]
  \\ drule0 memory_rel_tl \\ strip_tac
  \\ drule0 (GEN_ALL memory_rel_bounds_check)
  \\ disch_then (qspec_then `LENGTH l'` mp_tac)
  \\ impl_tac
  \\ TRY (fs [small_int_def,dimword_def,good_dimindex_def] \\ rfs [] \\ NO_TAC)
  \\ fs [GSYM word_add_n2w]
  \\ strip_tac \\ fs [bytes_in_word_def]
  \\ IF_CASES_TAC
  \\ fs [] \\ fs [lookup_insert,adjust_var_11] \\ rw [] \\ fs []
  \\ simp[inter_insert_ODD_adjust_set,GSYM Boolv_def,option_le_max_right]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ match_mp_tac memory_rel_insert \\ fs []
  \\ TRY (match_mp_tac memory_rel_Boolv_T \\ fs [])
  \\ TRY (match_mp_tac memory_rel_Boolv_F \\ fs [])
  \\ fs [good_dimindex_def]
QED

Theorem bit_len_lemma[local]:
  (n2w (k + w2n (bytes_in_word:'a word)) :'a word) ≪ 3 +
  (-1w * bytes_in_word) ≪ 3 = n2w (8 * k)
Proof
  rewrite_tac [WORD_MUL_LSL, GSYM WORD_LEFT_ADD_DISTRIB]
  \\ rewrite_tac [GSYM word_add_n2w, n2w_w2n, GSYM WORD_NEG_MUL,
                  GSYM WORD_ADD_ASSOC, WORD_ADD_RINV, WORD_ADD_0]
  \\ simp [word_mul_n2w]
QED

Theorem assign_BoundsCheckBit:
   assign c secn l dest (MemOp BoundsCheckBit) args names =
      case args of
      | [v1;v2] => (list_Seq [Assign 1
                               (let addr = real_addr c (adjust_var v1) in
                                let header = Load addr in
                                let extra = (if arch_width_bits c.arch_width = 32 then 2 else 3) in
                                let k = arch_width_bits c.arch_width - c.len_size - extra in
                                  ShiftN Lsl (Op Sub [ShiftN Lsr header k;
                                                      Const (&(arch_bytes c.arch_width))]) 3);
                              Assign 3 (ShiftVar (arch_width_bits c.arch_width) Ror (adjust_var v2) 1);
                              If Lower 3 (Reg 1)
                                 (Assign (adjust_var dest) TRUE_CONST)
                                 (Assign (adjust_var dest) FALSE_CONST)],l)
      | _ => (Skip:wordLang$prog,l)
Proof
  fs [assign_def,asmTheory.arch_bytes_def,shift_def] \\ every_case_tac \\ fs [asmTheory.arch_bytes_def,shift_def]
QED

Theorem assign_BoundsCheckBit[allow_rebind]:
  op = MemOp BoundsCheckBit ==> ^assign_thm_goal
Proof
  strip_tac
  \\ rpt strip_tac
  \\ gvs [dataLangTheory.op_requires_names_def,
          dataLangTheory.op_space_reset_def,
          dataSemTheory.cut_state_opt_def]
  \\ drule0 (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ imp_res_tac get_vars_IMP_LENGTH \\ fs [] \\ rw []
  \\ fs [do_app,allowed_op_def] \\ rfs [] \\ every_case_tac \\ fs []
  \\ clean_tac \\ fs []
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ fs [LENGTH_EQ_2] \\ clean_tac
  \\ fs [get_var_def]
  \\ `shift_length c - shift (dimindex (:'a)) < dimword (:'a) /\
      dimindex (:'a) - c.len_size < dimword (:'a) /\
      2 < dimword (:'a)` by
    (fs [dimindex_lt_dimword,state_rel_thm,memory_rel_def,heap_in_memory_store_def])
  \\ simp [state_rel_thm] \\ eval_tac
  \\ fs [state_rel_thm,option_le_max_right] \\ eval_tac
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ rpt_drule0 (memory_rel_get_vars_IMP |> GEN_ALL)
  \\ strip_tac
  \\ drule0 (GEN_ALL memory_rel_ByteArray_IMP) \\ fs [] \\ rw []
  \\ fs [assign_BoundsCheckBit]
  \\ fs [get_vars_SOME_IFF_data,get_vars_SOME_IFF]
  \\ qmatch_asmsub_rename_tac `(Number i,w2)`
  \\ `?wi. w2 = Word wi` by
    (drule0 memory_rel_tl \\ strip_tac
     \\ imp_res_tac memory_rel_any_Number_IMP \\ simp [] \\ NO_TAC)
  \\ rveq
  \\ once_rewrite_tac [list_Seq_def]
  \\ fs [eq_eval]
  \\ `shift_length c < dimindex (:α)` by (fs [memory_rel_def] \\ NO_TAC)
  \\ `word_exp t (real_addr c (adjust_var a1)) = SOME (Word a)` by
       (match_mp_tac (GEN_ALL get_real_addr_lemma)
        \\ fs [wordSemTheory.get_var_def] \\ NO_TAC) \\ fs []
  \\ fs [eq_eval,word_sh_def]
  \\ fs [list_Seq_def,eq_eval]
  \\ simp [Once word_exp_ShiftVar_bits]
  \\ `c.len_size < dimindex (:α) /\
      ~(dimindex (:α) ≥ c.len_size + dimindex (:α))` by
         (fs [memory_rel_def,heap_in_memory_store_def] \\ NO_TAC)
  \\ fs [eq_eval,WORD_LO_word_0,adjust_var_11]
  \\ fs [good_dimindex_def] \\ rfs []
  \\ fs [decode_length_def]
  \\ assume_tac (Q.INST [‘k’ |-> ‘LENGTH (l':word8 list)’] bit_len_lemma)
  \\ gvs [bytes_in_word_def, dimword_def]
  \\ fs [eq_eval, lookup_insert, adjust_var_11, asmTheory.word_cmp_def]
  \\ drule0 memory_rel_tl \\ strip_tac
  \\ drule0 (GEN_ALL memory_rel_bounds_check)
  \\ disch_then (qspec_then `8 * LENGTH l'` mp_tac)
  \\ impl_tac
  \\ TRY (fs [small_int_def,dimword_def,good_dimindex_def] \\ rfs [] \\ NO_TAC)
  \\ strip_tac \\ fs []
  \\ IF_CASES_TAC
  \\ fs [] \\ fs [lookup_insert,adjust_var_11] \\ rw [] \\ fs []
  \\ simp[inter_insert_ODD_adjust_set,GSYM Boolv_def,option_le_max_right]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ match_mp_tac memory_rel_insert \\ fs []
  \\ TRY (match_mp_tac memory_rel_Boolv_T \\ fs [])
  \\ TRY (match_mp_tac memory_rel_Boolv_F \\ fs [])
  \\ fs [good_dimindex_def]
QED

val _ = augment_srw_ss [rewrites [compiler_Smallnum_i2w]];

Theorem do_app_Ref:
   do_app (MemOp Ref) vals x =
    case consume_space (LENGTH vals + 1) x of
      NONE => Rerr (Rabort Rtype_error)
    | SOME s1 =>
      Rval
      (RefPtr T (LEAST ptr. ptr ∉ domain s1.refs),
         s1 with
           <| refs := insert (LEAST ptr. ptr ∉ domain s1.refs) (ValueArray vals) s1.refs;
           safe_for_space := (do_stack (MemOp Ref) vals (do_lim_safe s1 (MemOp Ref) vals)).safe_for_space;
           stack_max :=
             (do_stack (MemOp Ref) vals (do_lim_safe s1 (MemOp Ref) vals)).stack_max
           |>)
Proof
  fs [do_app,allowed_op_def,consume_space_def] \\ rw[] >> Cases_on `vals` \\ fs [LET_THM]
QED

Theorem assign_Ref:
   op = MemOp Ref ==> ^assign_thm_goal
Proof
  strip_tac
  \\ rpt strip_tac \\ imp_res_tac state_rel_arch_width
  \\ gvs [dataLangTheory.op_requires_names_def,
          dataLangTheory.op_space_reset_def,
          dataSemTheory.cut_state_opt_def]
  \\ drule0 (evaluate_GiveUp2 |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ imp_res_tac get_vars_IMP_LENGTH \\ fs []
  \\ fs [assign_def] \\ fs [do_app_Ref] \\ fs[do_app]
  \\ Cases_on `consume_space (LENGTH vals + 1) s` \\ fs [] \\ rveq
  \\ imp_res_tac get_vars_IMP_LENGTH \\ fs [] \\ clean_tac
  \\ fs [consume_space_def] \\ clean_tac
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ TOP_CASE_TAC \\ fs []
  >- (conj_tac >- (fs[state_rel_def] >> rw[option_le_max_right] >> metis_tac[option_le_trans]) >>
               fs[encode_header_def] >>
      fs[encode_header_def,state_rel_def,good_dimindex_def,limits_inv_def,dimword_def,
          memory_rel_def,heap_in_memory_store_def,consume_space_def,arch_size_def] >> rfs[NOT_LESS]
     )
  \\ `shift_length c - shift (dimindex (:'a)) < dimword (:'a)` by
       (fs [state_rel_thm] \\ assume_tac dimindex_lt_dimword \\ decide_tac)
  \\ simp [state_rel_thm] \\ eval_tac
  \\ fs [state_rel_thm] \\ eval_tac
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ drule0 (memory_rel_get_vars_IMP |> GEN_ALL)
  \\ disch_then drule0 \\ fs [NOT_LESS,DECIDE ``n + 1 <= m <=> n < m:num``]
  \\ strip_tac
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ qabbrev_tac `new = LEAST ptr. ptr ∉ domain s.refs`
  \\ `new ∉ domain s.refs` by metis_tac [LEAST_NOTIN_spt_DOMAIN]
  \\ qpat_assum `_ = LENGTH _` assume_tac
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ rpt_drule0 memory_rel_Ref \\ strip_tac
  \\ fs [list_Seq_def] \\ eval_tac
  \\ fs [wordSemTheory.set_store_def,FLOOKUP_UPDATE]
  \\ qpat_abbrev_tac `t5 = t with <| locals := _ ; store := _ |>`
  \\ pairarg_tac \\ fs []
  \\ `t.memory = t5.memory /\ t.mdomain = t5.mdomain` by
       (unabbrev_all_tac \\ fs []) \\ fs []
  \\ ntac 2 (pop_assum kall_tac)
  \\ drule0 evaluate_StoreEach
  \\ disch_then (qspecl_then [`3::MAP adjust_var args`,`1`,`c`] mp_tac)
  \\ impl_tac THEN1
   (fs [wordSemTheory.get_vars_def,Abbr`t5`,wordSemTheory.get_var_def,
        lookup_insert,get_vars_with_store,get_vars_adjust_var] \\ NO_TAC)
  \\ clean_tac \\ fs [] \\ UNABBREV_ALL_TAC
  \\ fs [lookup_insert,FAPPLY_FUPDATE_THM,adjust_var_11,FLOOKUP_UPDATE,
         code_oracle_rel_def,FLOOKUP_UPDATE]
  \\ rpt (qpat_x_assum `!x y z. _` kall_tac)
  \\ rw [] \\ fs [] \\ rw [] \\ fs []
  \\ fs [inter_insert_ODD_adjust_set]
  >- (rw[option_le_max_right] >> metis_tac[option_le_trans])
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ match_mp_tac memory_rel_insert \\ fs []
  \\ fs [make_ptr_def]
  \\ `TriggerGC <> EndOfHeap` by fs []
  \\ pop_assum (fn th => fs [MATCH_MP FUPDATE_COMMUTES th])
QED

Theorem assign_Update:
   op = MemOp Update ==> ^assign_thm_goal
Proof
  strip_tac
  \\ rpt strip_tac \\ imp_res_tac state_rel_arch_width
  \\ gvs [dataLangTheory.op_requires_names_def,
          dataLangTheory.op_space_reset_def,
          dataSemTheory.cut_state_opt_def]
  \\ drule0 (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ imp_res_tac get_vars_IMP_LENGTH \\ fs []
  \\ fs [do_app,allowed_op_def] \\ every_case_tac \\ fs [] \\ clean_tac
  \\ fs [INT_EQ_NUM_LEMMA] \\ clean_tac
  \\ fs [integerTheory.NUM_OF_INT,LENGTH_EQ_3] \\ clean_tac
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ fs [bvlSemTheory.Unit_def] \\ rveq
  \\ fs [GSYM bvlSemTheory.Unit_def] \\ rveq
  \\ fs [assign_def] \\ eval_tac \\ fs [state_rel_thm]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ drule0 (memory_rel_get_vars_IMP |> GEN_ALL)
  \\ disch_then drule0 \\ fs []
  \\ imp_res_tac get_vars_3_IMP \\ fs []
  \\ fs [integerTheory.NUM_OF_INT,LENGTH_EQ_3] \\ clean_tac
  \\ imp_res_tac get_vars_3_IMP \\ fs [] \\ strip_tac
  \\ drule0 reorder_lemma \\ strip_tac
  \\ drule0 (memory_rel_Update |> GEN_ALL) \\ fs []
  \\ strip_tac \\ clean_tac
  \\ `word_exp t (real_offset c (adjust_var a2)) = SOME (Word y)` by
        (match_mp_tac (GEN_ALL get_real_offset_lemma)
         \\ fs [wordSemTheory.get_var_def] \\ NO_TAC)
  \\ `word_exp t (real_addr c (adjust_var a1)) = SOME (Word x)` by
        (match_mp_tac (GEN_ALL get_real_addr_lemma)
         \\ fs [wordSemTheory.get_var_def] \\ NO_TAC)
  \\ fs [] \\ eval_tac \\ fs [EVAL ``word_exp s1 Unit``]
  \\ fs [wordSemTheory.mem_store_def]
  \\ fs [lookup_insert,adjust_var_11]
  \\ rw [] \\ fs [option_le_max_right]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ match_mp_tac memory_rel_insert \\ fs []
  \\ match_mp_tac memory_rel_Unit \\ fs []
  \\ first_x_assum (fn th => mp_tac th THEN match_mp_tac memory_rel_rearrange)
  \\ rw [] \\ fs []
QED

Theorem assign_El:
   op = MemOp El ==> ^assign_thm_goal
Proof
  strip_tac
  \\ rpt strip_tac \\ imp_res_tac state_rel_arch_width
  \\ gvs [dataLangTheory.op_requires_names_def,
          dataLangTheory.op_space_reset_def,
          dataSemTheory.cut_state_opt_def]
  \\ drule0 (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ imp_res_tac get_vars_IMP_LENGTH \\ fs []
  \\ fs [do_app,CaseEq"list",CaseEq"dataSem$v",CaseEq"bool"]
  \\ rveq \\ fs []
  THEN1
   (fs [INT_EQ_NUM_LEMMA] \\ clean_tac
    \\ fs [integerTheory.NUM_OF_INT,LENGTH_EQ_2] \\ clean_tac
    \\ imp_res_tac state_rel_get_vars_IMP
    \\ fs [assign_def] \\ eval_tac \\ fs [state_rel_thm]
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ drule0 (memory_rel_get_vars_IMP |> GEN_ALL)
    \\ disch_then drule0 \\ fs []
    \\ imp_res_tac get_vars_2_IMP \\ fs []
    \\ fs [integerTheory.NUM_OF_INT,LENGTH_EQ_2] \\ clean_tac
    \\ imp_res_tac get_vars_2_IMP \\ fs [] \\ strip_tac
    \\ drule0 (memory_rel_El |> GEN_ALL) \\ fs []
    \\ strip_tac \\ clean_tac
    \\ rename [`get_real_addr c t.store ptr_w = SOME x1`]
    \\ `word_exp t (real_offset c (adjust_var a2)) = SOME (Word y)` by
          (match_mp_tac (GEN_ALL get_real_offset_lemma)
           \\ fs [wordSemTheory.get_var_def] \\ NO_TAC)
    \\ `word_exp t (real_addr c (adjust_var a1)) = SOME (Word x1)` by
          (match_mp_tac (GEN_ALL get_real_addr_lemma)
           \\ fs [wordSemTheory.get_var_def] \\ NO_TAC)
    \\ fs [] \\ eval_tac
    \\ fs [lookup_insert,adjust_var_11]
    \\ rw [] \\ fs []
    THEN1 metis_tac [option_le_trans,option_le_max_right]
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ match_mp_tac memory_rel_insert \\ fs []
    \\ first_x_assum (fn th => mp_tac th THEN match_mp_tac memory_rel_rearrange)
    \\ fs [] \\ rw [] \\ fs [])
  \\ fs [INT_EQ_NUM_LEMMA] \\ clean_tac
  \\ fs [integerTheory.NUM_OF_INT,LENGTH_EQ_2] \\ clean_tac
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ fs [assign_def] \\ eval_tac \\ fs [state_rel_thm,option_le_max_right]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ drule0 (memory_rel_get_vars_IMP |> GEN_ALL)
  \\ disch_then drule0 \\ fs []
  \\ imp_res_tac get_vars_2_IMP \\ fs []
  \\ fs [integerTheory.NUM_OF_INT,LENGTH_EQ_2] \\ clean_tac
  \\ imp_res_tac get_vars_2_IMP \\ fs [] \\ strip_tac
  \\ fs [CaseEq"option",CaseEq"ref",CaseEq"bool"] \\ rveq \\ fs []
  \\ drule0 (memory_rel_Deref |> GEN_ALL) \\ fs []
  \\ strip_tac \\ clean_tac
  \\ `word_exp t (real_offset c (adjust_var a2)) = SOME (Word y)` by
        (match_mp_tac (GEN_ALL get_real_offset_lemma)
         \\ fs [wordSemTheory.get_var_def] \\ NO_TAC)
  \\ `word_exp t (real_addr c (adjust_var a1)) = SOME (Word x)` by
        (match_mp_tac (GEN_ALL get_real_addr_lemma)
         \\ fs [wordSemTheory.get_var_def] \\ NO_TAC)
  \\ fs [] \\ eval_tac
  \\ fs [lookup_insert,adjust_var_11]
  \\ rw [] \\ fs [option_le_max_right]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ match_mp_tac memory_rel_insert \\ fs []
  \\ first_x_assum (fn th => mp_tac th THEN match_mp_tac memory_rel_rearrange)
  \\ fs [] \\ rw [] \\ fs []
QED

Theorem assign_UpdateByte:
   op = MemOp UpdateByte ==> ^assign_thm_goal
Proof[exclude_simps = INT_OF_NUM NUM_EQ0]
  strip_tac
  \\ rpt strip_tac
  \\ gvs [dataLangTheory.op_requires_names_def,
          dataLangTheory.op_space_reset_def,
          dataSemTheory.cut_state_opt_def]
  \\ drule0 (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ imp_res_tac get_vars_IMP_LENGTH \\ fs[]
  \\ fs[do_app,allowed_op_def] \\ every_case_tac \\ fs[] \\ clean_tac
  \\ fs[LENGTH_EQ_NUM_compute] \\ clean_tac
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ fs[LENGTH_EQ_NUM_compute] \\ clean_tac
  \\ rename [‘get_vars [e1;e2;e3] s.locals’]
  \\ imp_res_tac get_vars_3_IMP
  \\ fs [] \\ rveq
  \\ fs[] \\ rveq
  \\ fs[state_rel_thm,set_var_def,option_le_max_right]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ rpt_drule0 (memory_rel_get_vars_IMP )
  \\ strip_tac
  \\ fs[get_vars_def]
  \\ every_case_tac \\ fs[] \\ clean_tac
  \\ rpt_drule0 memory_rel_ByteArray_IMP
  \\ strip_tac \\ clean_tac
  \\ rpt_drule0 get_var_get_real_addr_lemma
  \\ imp_res_tac memory_rel_tl
  \\ `small_int (dimindex (:'a)) i`
  by (
    simp[small_int_def]
    \\ fs[good_dimindex_def]
    \\ rfs[dimword_def]
    \\ intLib.COOPER_TAC )
  \\ rpt_drule0 memory_rel_Number_IMP
  \\ imp_res_tac memory_rel_tl
  \\ `small_int (dimindex (:'a)) (&w2n w)`
  by (match_mp_tac small_int_w2n \\ fs[])
  \\ rpt_drule0 memory_rel_Number_IMP
  \\ ntac 2 (qhdtm_x_assum`memory_rel` kall_tac)
  \\ ntac 2 strip_tac \\ clean_tac
  \\ qpat_x_assum`get_var (adjust_var e2) _ = _`assume_tac
  \\ rpt_drule0 get_real_byte_offset_lemma
  \\ simp[assign_def,list_Seq_def] \\ eval_tac
  \\ ‘2 MOD dimword (:α) = 2’ by
    fs [good_dimindex_def, dimword_def]
  \\ fs[wordSemTheory.get_var_def]
  \\ simp[lookup_insert,wordSemTheory.inst_def]
  \\ `1 < dimindex(:'a)` by fs[good_dimindex_def]
  \\ simp[wordSemTheory.get_var_def,Unit_def]
  \\ eval_tac
  \\ simp[lookup_insert]
  \\ rpt strip_tac
  \\ simp[Smallnum_i2w,GSYM integer_wordTheory.word_i2w_mul]
  \\ qspecl_then[`ii`,`1`](mp_tac o Q.GEN`ii` o SYM) WORD_MUL_LSL
  \\ `i2w 2 = 2w` by EVAL_TAC
  \\ simp[]
  \\ `i2w i << 1 >>> 1 = i2w i`
  by (
    match_mp_tac lsl_lsr
    \\ Cases_on`i`
    \\ fs[small_int_def,X_LT_DIV,dimword_def,integer_wordTheory.i2w_def] )
  \\ pop_assum (CHANGED_TAC o SUBST_ALL_TAC)
  \\ `w2w w << 1 >>> 1 = w2w w`
  by (
    match_mp_tac lsl_lsr
    \\ simp[w2n_w2w]
    \\ reverse IF_CASES_TAC >- fs[good_dimindex_def]
    \\ fs[small_int_def,GSYM dimword_def,X_LT_DIV])
  \\ pop_assum (CHANGED_TAC o SUBST_ALL_TAC)
  \\ simp[w2w_w2w]
  \\ `dimindex(:8) ≤ dimindex(:α)` by fs[good_dimindex_def]
  \\ simp[integer_wordTheory.w2w_i2w]
  \\ `i2w i = n2w (Num i)`
  by (
    rw[integer_wordTheory.i2w_def]
    \\ `F` by intLib.COOPER_TAC )
  \\ pop_assum (CHANGED_TAC o SUBST_ALL_TAC)
  \\ disch_then kall_tac
  \\ qpat_x_assum`∀i. _ ⇒ mem_load_byte_aux _ _ _ _ = _`(qspec_then`Num i`mp_tac)
  \\ impl_tac >- (Cases_on `i` \\ fs [])
  \\ simp[wordSemTheory.mem_load_byte_aux_def]
  \\ BasicProvers.TOP_CASE_TAC \\ fs[]
  \\ strip_tac
  \\ simp[wordSemTheory.mem_store_byte_aux_def]
  \\ simp[lookup_insert]
  \\ conj_tac >- rw[]
  \\ fs[inter_insert_ODD_adjust_set,option_le_max_right]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ match_mp_tac memory_rel_insert
  \\ simp[]
  \\ match_mp_tac memory_rel_Unit
  \\ first_x_assum(qspecl_then[`Num i`,`w`]mp_tac)
  \\ impl_tac >- (Cases_on `i` \\ fs [])
  \\ simp[theWord_def] \\ strip_tac
  \\ simp[WORD_ALL_BITS]
  \\ drule0 memory_rel_tl \\ simp[] \\ strip_tac
  \\ drule0 memory_rel_tl \\ simp[] \\ strip_tac
  \\ drule0 memory_rel_tl \\ simp[]
QED

Theorem assign_DerefByte:
   op = MemOp DerefByte ==> ^assign_thm_goal
Proof
  strip_tac
  \\ rpt strip_tac \\ imp_res_tac state_rel_arch_width
  \\ gvs [dataLangTheory.op_requires_names_def,
          dataLangTheory.op_space_reset_def,
          dataSemTheory.cut_state_opt_def]
  \\ drule0 (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ imp_res_tac get_vars_IMP_LENGTH \\ fs[]
  \\ fs[do_app,allowed_op_def] \\ every_case_tac \\ fs[] \\ clean_tac
  \\ fs[LENGTH_EQ_NUM_compute] \\ clean_tac
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ fs[LENGTH_EQ_NUM_compute] \\ clean_tac
  \\ imp_res_tac get_vars_2_IMP
  \\ fs[state_rel_thm,set_var_def,option_le_max_right]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ rpt_drule0 (memory_rel_get_vars_IMP )
  \\ strip_tac
  \\ fs[get_vars_def]
  \\ every_case_tac \\ fs[] \\ clean_tac
  \\ fs[]
  \\ rpt_drule0 memory_rel_ByteArray_IMP
  \\ strip_tac \\ clean_tac
  \\ first_x_assum(qspec_then`ARB`kall_tac)
  \\ rpt_drule0 get_var_get_real_addr_lemma
  \\ imp_res_tac memory_rel_tl
  \\ rename1 `i < &LENGTH l'`
  \\ `small_int (dimindex (:'a)) i`
  by (
    simp[small_int_def]
    \\ fs[good_dimindex_def]
    \\ rfs[dimword_def]
    \\ intLib.COOPER_TAC )
  \\ rpt_drule0 memory_rel_Number_IMP
  \\ qhdtm_x_assum`memory_rel` kall_tac
  \\ strip_tac
  \\ clean_tac
  \\ qpat_x_assum`get_var _ _ = SOME (Word(Smallnum _))`assume_tac
  \\ rpt_drule0 get_real_byte_offset_lemma
  \\ `2 < dimword (:'a)` by
       (assume_tac dimindex_lt_dimword \\ fs [good_dimindex_def] \\ decide_tac)
  \\ simp[assign_def,list_Seq_def] \\ eval_tac
  \\ simp[wordSemTheory.inst_def]
  \\ eval_tac
  \\ fs[Smallnum_i2w,GSYM integer_wordTheory.word_i2w_mul]
  \\ qspecl_then[`i2w i`,`1`](mp_tac o SYM) WORD_MUL_LSL
  \\ `i2w 2 = 2w` by EVAL_TAC
  \\ simp[]
  \\ `i2w i << 1 >>> 1 = i2w i`
  by (
    match_mp_tac lsl_lsr
    \\ REWRITE_TAC[GSYM integerTheory.INT_LT,
                   GSYM integerTheory.INT_MUL,
                   integer_wordTheory.w2n_i2w]
    \\ simp[]
    \\ Cases_on`i`
    \\ fs[dimword_def,integerTheory.INT_MOD,integerTheory.INT_MOD0,
          small_int_def,X_LT_DIV] )
  \\ simp[]
  \\ first_x_assum(qspec_then`Num i`mp_tac)
  \\ impl_tac >- ( Cases_on`i` \\ fs[] )
  \\ `i2w i = n2w (Num i)`
  by (
    rw[integer_wordTheory.i2w_def]
    \\ Cases_on`i` \\ fs[] )
  \\ fs[]
  \\ `~(1 >= dimindex(:'a))` by fs[good_dimindex_def]
  \\ simp[lookup_insert]
  \\ ntac 4 strip_tac
  \\ conj_tac >- rw[]
  \\ fs[inter_insert_ODD_adjust_set,option_le_max_right]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ match_mp_tac memory_rel_insert
  \\ qmatch_goalsub_abbrev_tac`(Number j,Word k)`
  \\ `small_int (dimindex (:α)) j` by (simp[Abbr`j`,small_int_w2n])
  \\ `k = Smallnum j`
  by (
    fs[small_int_def,Abbr`j`]
    \\ qmatch_goalsub_abbrev_tac`w2n w8`
    \\ Q.ISPEC_THEN`w8`strip_assume_tac w2n_lt
    \\ simp[integer_wordTheory.i2w_def,Smallnum_i2w]
    \\ simp[Abbr`k`,WORD_MUL_LSL]
    \\ simp[GSYM word_mul_n2w]
    \\ simp[w2w_def] )
  \\ simp[]
  \\ match_mp_tac IMP_memory_rel_Number
  \\ fs[]
QED

Theorem get_real_bit_offset_lemma:
  get_var v (t:('a,'c,'ffi) wordSem$state) = SOME (Word w) ∧ good_dimindex (:α) ∧
  arch_width_bits c.arch_width = dimindex(:'a) ⇒
  word_exp t (real_bit_offset c v) = SOME (Word ((w:'a word) ⋙ 4))
Proof
  rw[real_bit_offset_def,data_to_wordTheory.arch_size,wordSemTheory.get_var_def]
  \\ eval_tac \\ fs[good_dimindex_def,dimword_def,bytes_in_word_def]
QED

Theorem b2w_index[local]:
  i < dimindex (:'a) ⇒ ((b2w b : 'a word) ' i ⇔ i = 0 ∧ b)
Proof
  Cases_on ‘b’ \\ gvs [b2w_def, word_index]
QED

Theorem deref_bit_lemma[local]:
  small_int (dimindex (:'a)) (&n) ∧ good_dimindex (:'a) ⇒
  Smallnum (&n) ⋙ 4 = n2w (n DIV 8) :'a word ∧
  32 ≤ dimindex (:'a) ∧
  w2n ((7w && Smallnum (&n) ⋙ 1) :'a word) = n MOD 8 ∧
  n MOD 8 < dimindex (:α) ∧
  (∀b:word8. 1w && w2w b ⋙ (n MOD 8) = b2w (b ' (n MOD 8)) :'a word) ∧
  (∀(b:word8) x. w2w ((w2w b && ~((1w:'a word) ≪ (n MOD 8))) ‖
                       (b2w x ≪ (n MOD 8))) = ((n MOD 8 :+ x) b))
Proof
  strip_tac
  \\ ‘32 ≤ dimindex (:'a)’ by fs [good_dimindex_def]
  \\ asm_rewrite_tac []
  \\ conj_tac
  >-
   (simp [Smallnum_def]
    \\ rewrite_tac [GSYM w2n_11, w2n_lsr]
    \\ simp []
    \\ DEP_REWRITE_TAC [LESS_MOD]
    \\ conj_tac >- gvs [good_dimindex_def, dimword_def, small_int_def, DIV_LT_X]
    \\ Cases_on ‘n = 0’ >- simp []
    \\ rewrite_tac [GSYM (EVAL “2 * 8:num”)]
    \\ DEP_REWRITE_TAC [miscTheory.MULT_DIV_MULT] \\ simp [])
  \\ have ‘Smallnum (&n) ⋙ 1 = n2w n’
  >-
   (gvs [Smallnum_def] \\ rewrite_tac [GSYM w2n_11, w2n_lsr]
    \\ gvs [small_int_def, good_dimindex_def, dimword_def]
    \\ once_rewrite_tac [MULT_COMM]
    \\ DEP_REWRITE_TAC [MULT_DIV] \\ fs [])
  \\ have ‘n MOD 8 < dimword (:α) ∧ n MOD 8 < dimindex (:α)’
  >-
   (rw [] \\ irule LESS_TRANS
    \\ qexists_tac ‘8’
    \\ gvs [good_dimindex_def, dimword_def])
  \\ simp []
  \\ conj_tac
  >-
   (once_rewrite_tac [WORD_AND_COMM]
    \\ rewrite_tac [WORD_AND_EXP_SUB1, GSYM (EVAL “2 ** 3 - 1”)]
    \\ fs [])
  \\ simp [fcpTheory.CART_EQ, word_and_def, fcpTheory.FCP_BETA, word_or_def,
           word_lsr_def, word_lsl_def, w2w, word_1comp_def, wordsTheory.word_index,
           SF CONJ_ss]
  \\ once_rewrite_tac [fcpTheory.FCP_APPLY_UPDATE_THM] \\ gvs [b2w_index]
  \\ rw [] \\ eq_tac \\ rw [] \\ gvs []
QED

Theorem assign_DerefBit:
  op = MemOp DerefBit ==> ^assign_thm_goal
Proof
  strip_tac
  \\ rpt strip_tac \\ imp_res_tac state_rel_arch_width
  \\ gvs [dataLangTheory.op_requires_names_def,
          dataLangTheory.op_space_reset_def,
          dataSemTheory.cut_state_opt_def]
  \\ drule0 (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ imp_res_tac get_vars_IMP_LENGTH \\ fs[]
  \\ gvs [do_app, AllCaseEqs()]
  \\ fs[LENGTH_EQ_NUM_compute] \\ clean_tac
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ fs[LENGTH_EQ_NUM_compute] \\ clean_tac
  \\ imp_res_tac get_vars_2_IMP
  \\ fs[state_rel_thm,set_var_def,option_le_max_right]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ rpt_drule0 memory_rel_get_vars_IMP
  \\ strip_tac
  \\ gvs [get_vars_def, AllCaseEqs()]
  \\ rpt_drule0 memory_rel_ByteArray_IMP
  \\ strip_tac \\ clean_tac
  \\ qpat_x_assum ‘∀x._’ kall_tac
  \\ rpt_drule0 get_var_get_real_addr_lemma
  \\ imp_res_tac memory_rel_tl
  \\ rename1 `i < &(8 * LENGTH bytes)`
  \\ have `small_int (dimindex (:'a)) i`
  >-
   (simp[small_int_def]
    \\ fs[good_dimindex_def]
    \\ rfs[dimword_def]
    \\ intLib.COOPER_TAC)
  \\ rpt_drule0 memory_rel_Number_IMP
  \\ qhdtm_x_assum`memory_rel` kall_tac
  \\ strip_tac
  \\ clean_tac
  \\ qpat_x_assum`get_var _ _ = SOME (Word(Smallnum _))`assume_tac
  \\ rpt_drule0 get_real_bit_offset_lemma
  \\ simp [assign_def,list_Seq_def] \\ eval_tac
  \\ simp[wordSemTheory.inst_def] \\ eval_tac
  \\ ‘∃n. i = & n’ by intLib.COOPER_TAC \\ gvs []
  \\ drule_all deref_bit_lemma \\ strip_tac
  \\ first_x_assum $ qspec_then ‘n DIV 8’ mp_tac
  \\ impl_tac >- simp [DIV_LT_X]
  \\ strip_tac \\ simp [lookup_insert,adjust_var_11]
  \\ rpt disch_tac
  \\ conj_tac >- (rw [] \\ fs [])
  \\ fs[inter_insert_ODD_adjust_set,option_le_max_right]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ match_mp_tac memory_rel_insert \\ simp []
  \\ irule IMP_memory_rel_Cons_empty \\ simp []
  \\ imp_res_tac memory_rel_tl \\ fs []
  \\ conj_tac
  >-
   (rw [oneline multiwordTheory.b2n_def]
    \\ gvs [dimword_def,good_dimindex_def])
  \\ rewrite_tac [wordsTheory.LSL_BITWISE, BlockNil_def, GSYM multiwordTheory.b2w_def]
QED

Theorem bool_tag_lsr[local]:
  tag < 2 ∧ good_dimindex (:'a) ⇒ (n2w (2 * tag) :'a word) ⋙ 1 = b2w (tag = 1)
Proof
  rw [] \\ ‘tag = 0 ∨ tag = 1’ by decide_tac
  \\ gvs [b2w_def, wordsTheory.word_lsr_n2w, good_dimindex_def]
  \\ simp [wordsTheory.word_bits_n2w, bitTheory.BITS_THM]
QED

Theorem assign_UpdateBit:
  op = MemOp UpdateBit ==> ^assign_thm_goal
Proof
  strip_tac
  \\ rpt strip_tac \\ imp_res_tac state_rel_arch_width
  \\ gvs [dataLangTheory.op_requires_names_def,
          dataLangTheory.op_space_reset_def,
          dataSemTheory.cut_state_opt_def]
  \\ drule0 (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ `t.termdep <> 0` by fs[]
  \\ imp_res_tac get_vars_IMP_LENGTH \\ fs[]
  \\ gvs [do_app, AllCaseEqs()]
  \\ fs[LENGTH_EQ_NUM_compute] \\ clean_tac
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ fs[LENGTH_EQ_NUM_compute] \\ clean_tac
  \\ imp_res_tac get_vars_3_IMP
  \\ fs[state_rel_thm,set_var_def,option_le_max_right]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ rpt_drule0 memory_rel_get_vars_IMP
  \\ strip_tac
  \\ gvs [get_vars_def, AllCaseEqs()]
  \\ rpt_drule0 memory_rel_ByteArray_IMP
  \\ strip_tac \\ clean_tac
  \\ qpat_x_assum ‘∀x._’ $ mk_asm "here"
  \\ rpt_drule0 get_var_get_real_addr_lemma
  \\ imp_res_tac memory_rel_tl
  \\ rename1 `i < &(8 * LENGTH bytes)`
  \\ have `small_int (dimindex (:'a)) i`
  >-
   (simp[small_int_def]
    \\ fs[good_dimindex_def]
    \\ rfs[dimword_def]
    \\ intLib.COOPER_TAC)
  \\ rpt_drule0 memory_rel_Number_IMP
  \\ strip_tac \\ clean_tac
  \\ imp_res_tac memory_rel_tl
  \\ gvs [oneline dest_Boolv_def, AllCaseEqs()]
  \\ drule memory_rel_Block_IMP \\ simp [] \\ strip_tac \\ gvs []
  \\ ntac 3 (qhdtm_x_assum`memory_rel` kall_tac)
  \\ qpat_x_assum`get_var _ _ = SOME (Word(Smallnum _))`assume_tac
  \\ rpt_drule0 get_real_bit_offset_lemma
  \\ simp [assign_def,list_Seq_def] \\ eval_tac
  \\ simp[wordSemTheory.inst_def] \\ eval_tac
  \\ ‘∃n. i = & n’ by intLib.COOPER_TAC \\ gvs []
  \\ drule_all deref_bit_lemma \\ strip_tac
  \\ first_x_assum $ qspec_then ‘n DIV 8’ mp_tac
  \\ impl_keep_tac >- simp [DIV_LT_X]
  \\ strip_tac \\ simp [lookup_insert,adjust_var_11]
  \\ eval_tac \\ simp [lookup_insert]
  \\ drule_all bool_tag_lsr \\ strip_tac \\ asm_rewrite_tac []
  \\ asm_x "here" $ qspec_then ‘n DIV 8’ drule
  \\ gvs [wordSemTheory.mem_store_byte_aux_def,AllCaseEqs(),
          wordSemTheory.mem_load_byte_aux_def]
  \\ eval_tac
  \\ gvs [Unit_def, wordSemTheory.word_exp_def, lookup_insert, adjust_var_11]
  \\ rpt disch_tac
  \\ rw [] \\ fs []
  \\ fs[inter_insert_ODD_adjust_set,option_le_max_right]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ match_mp_tac memory_rel_insert \\ simp []
  \\ fs [theWord_def]
  \\ match_mp_tac memory_rel_Unit \\ fs []
  \\ metis_tac [memory_rel_tl]
QED

Theorem join_lemma[local] =
  METIS_PROVE [] “(b1 ⇒ x) ∧ (b2 ⇒ x) ⇒ (b1 ∨ b2 ⇒ x)”;

Theorem imp_assign[local] =
  DB.match ["-"] “_ ==> ^assign_thm_goal” |> map (#1 o #2)
  |> end_itlist (fn x => fn y => MATCH_MP join_lemma (CONJ x y));

Theorem assign_MemOp:
  (∃m. op = MemOp m) ⇒ ^assign_thm_goal
Proof
  strip_tac \\ strip_tac
  \\ irule imp_assign
  \\ asm_rewrite_tac []
  \\ rpt $ first_assum $ irule_at Any
  \\ gvs [] \\ Cases_on ‘m’ \\ gvs []
  \\ qhdtm_x_assum`do_app`mp_tac \\ EVAL_TAC
QED

