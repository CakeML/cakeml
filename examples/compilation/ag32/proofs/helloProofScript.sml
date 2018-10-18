open preamble
     semanticsPropsTheory backendProofTheory ag32_configProofTheory
     helloProgTheory helloCompileTheory

val _ = new_theory"helloProof";

(* TODO: move *)

val _ = temp_overload_on("nxt",
  ``λmc n ms. FUNPOW mc.target.next n ms``);

val v2w_sing = store_thm("v2w_sing",
  ``v2w [b] = if b then 1w else 0w``,
  Cases_on `b` \\ EVAL_TAC);

val TAKE_DROP_SUBLIST = Q.store_thm("TAKE_DROP_SUBLIST",
  `ll ≼ (DROP n ls) ∧ n < LENGTH ls ∧ (nlll = n + LENGTH ll) ⇒
   (TAKE n ls ++ ll ++ DROP nlll ls = ls)`,
  rw[IS_PREFIX_APPEND, LIST_EQ_REWRITE, LENGTH_TAKE_EQ, EL_APPEND_EQN, EL_DROP]
  \\ rw[] \\ fs[EL_TAKE]
  \\ fs[NOT_LESS, LESS_EQ_EXISTS]);

val ALIST_FUPDKEY_I = Q.store_thm("ALIST_FUPDKEY_I",
  `ALIST_FUPDKEY n I = I`,
  simp[FUN_EQ_THM]
  \\ Induct
  \\ simp[ALIST_FUPDKEY_def,FORALL_PROD]);

val byte_aligned_imp = Q.store_thm("byte_aligned_imp",
  `byte_aligned (x:word32) ⇒
   (((((31 >< 2) x):word30) @@ (0w:word2)) = x)`,
  rw[alignmentTheory.byte_aligned_def, alignmentTheory.aligned_def, alignmentTheory.align_def]
  \\ blastLib.FULL_BBLAST_TAC);

val dfn'Normal_PC = Q.store_thm("dfn'Normal_PC",
  `(dfn'Normal x s).PC = s.PC + 4w`,
  PairCases_on`x`
  \\ rw[ag32Theory.dfn'Normal_def]
  \\ rw[ag32Theory.norm_def]
  \\ simp[ag32Theory.ALU_def]
  \\ PURE_TOP_CASE_TAC \\ simp[ag32Theory.incPC_def]);

val dfn'Normal_MEM = Q.store_thm("dfn'Normal_MEM",
  `(dfn'Normal x s).MEM = s.MEM`,
  PairCases_on`x`
  \\ rw[ag32Theory.dfn'Normal_def]
  \\ rw[ag32Theory.norm_def]
  \\ simp[ag32Theory.ALU_def]
  \\ PURE_TOP_CASE_TAC \\ simp[ag32Theory.incPC_def]);

val dfn'LoadMEMByte_PC = Q.store_thm("dfn'LoadMEMByte_PC",
  `(dfn'LoadMEMByte x s).PC = s.PC + 4w`,
  PairCases_on`x`
  \\ rw[ag32Theory.dfn'LoadMEMByte_def]
  \\ simp[ag32Theory.incPC_def]);

val dfn'LoadMEMByte_MEM = Q.store_thm("dfn'LoadMEMByte_MEM",
  `(dfn'LoadMEMByte x s).MEM = s.MEM`,
  PairCases_on`x`
  \\ rw[ag32Theory.dfn'LoadMEMByte_def]
  \\ simp[ag32Theory.incPC_def]);

val dfn'Shift_PC = Q.store_thm("dfn'Shift_PC",
  `(ag32$dfn'Shift x s).PC = s.PC + 4w`,
  PairCases_on`x`
  \\ rw[ag32Theory.dfn'Shift_def]
  \\ simp[ag32Theory.incPC_def]);

val dfn'Shift_MEM = Q.store_thm("dfn'Shift_MEM",
  `(ag32$dfn'Shift x s).MEM = s.MEM`,
  PairCases_on`x`
  \\ rw[ag32Theory.dfn'Shift_def]
  \\ simp[ag32Theory.incPC_def]);

val dfn'LoadConstant_PC = Q.store_thm("dfn'LoadConstant_PC",
  `(ag32$dfn'LoadConstant x s).PC = s.PC + 4w`,
  PairCases_on`x`
  \\ rw[ag32Theory.dfn'LoadConstant_def]
  \\ simp[ag32Theory.incPC_def]);

val dfn'LoadConstant_MEM = Q.store_thm("dfn'LoadConstant_MEM",
  `(ag32$dfn'LoadConstant x s).MEM = s.MEM`,
  PairCases_on`x`
  \\ rw[ag32Theory.dfn'LoadConstant_def]
  \\ simp[ag32Theory.incPC_def]);

val dfn'JumpIfZero_MEM = Q.store_thm("dfn'JumpIfZero_MEM",
  `(ag32$dfn'JumpIfZero x s).MEM = s.MEM`,
  PairCases_on`x`
  \\ rw[ag32Theory.dfn'JumpIfZero_def, ag32Theory.ALU_def]
  \\ PURE_TOP_CASE_TAC \\ fs[ag32Theory.incPC_def] \\ rw[]);

val extract_fs_with_numchars_keeps_iostreams = Q.store_thm("extract_fs_with_numchars_keeps_iostreams",
  `∀ls fs fs' off.
   (extract_fs_with_numchars fs ls = SOME fs') ∧
   (ALOOKUP fs'.infds fd = SOME(IOStream nm, off)) ⇒
   ∃off'.
     (ALOOKUP fs.infds fd = SOME (IOStream nm, off')) ∧ off' ≤ off ∧
     (∀content.
       (ALOOKUP fs.files (IOStream nm) = SOME content) ∧ (off' = LENGTH content) ∧
       (∀fd' off'. (ALOOKUP fs.infds fd' = SOME (IOStream nm, off')) ⇒ (fd = fd'))
       ⇒
       ∃written.
         (ALOOKUP fs'.files (IOStream nm) = SOME (content ++ written)) ∧
         (off = off' + LENGTH written))`,
  Induct
  >- ( rw[basis_ffiTheory.extract_fs_with_numchars_def])
  \\ Cases
  \\ rw[basis_ffiTheory.extract_fs_with_numchars_def]
  \\ fs[CaseEq"option",CaseEq"ffi_result"]
  \\ fs[fsFFITheory.fs_ffi_part_def]
  \\ last_x_assum drule
  \\ disch_then drule
  \\ strip_tac \\ rveq
  \\ reverse(fs[CaseEq"bool"]) \\ rveq \\ fs[]
  \\ fs[fsFFITheory.ffi_open_in_def,
        fsFFITheory.ffi_open_out_def,
        fsFFITheory.ffi_write_def,
        fsFFITheory.ffi_read_def,
        fsFFITheory.ffi_close_def]
  \\ fs[OPTION_CHOICE_EQUALS_OPTION, CaseEq"list"]
  \\ TRY pairarg_tac \\ fs[] \\ rveq \\ fs[]
  \\ fs[fsFFITheory.closeFD_def,
        fsFFITheory.read_def,
        fsFFITheory.openFile_truncate_def,
        fsFFITheory.openFile_def,
        fsFFITheory.write_def]
  \\ TRY pairarg_tac \\ fs[]
  \\ rveq \\ fs[ALOOKUP_ADELKEY, fsFFIPropsTheory.bumpFD_forwardFD]
  \\ fs[CaseEq"bool"]
  \\ rfs[fsFFITheory.fsupdate_def, fsFFIPropsTheory.forwardFD_def, ALIST_FUPDKEY_ALOOKUP]
  \\ fs[CaseEq"option"]
  \\ fs[CaseEq"bool"]
  \\ Cases_on`v` \\ fs[]
  \\ rveq \\ fs[] \\ rfs[]
  \\ rw[] \\ fs[]
  \\ TRY(
    fsrw_tac[DNF_ss][] \\ fs[data_to_word_assignProofTheory.IMP]
    \\ NO_TAC)
  >- (
    Cases_on`fnm = IOStream nm` \\ fsrw_tac[DNF_ss][]
    \\ fs[FORALL_PROD] \\ rveq \\ fs[] \\ rfs[]
    \\ metis_tac[] )
  \\ fsrw_tac[DNF_ss][FORALL_PROD]);

val extract_fs_with_numchars_closes_iostreams = Q.store_thm("extract_fs_with_numchars_closes_iostreams",
  `∀ls fs fs' fd nm off.
   (extract_fs_with_numchars fs ls = SOME fs') ∧
   (∀fd off. ALOOKUP fs.infds fd ≠ SOME(IOStream nm, off))
   ⇒
   (ALOOKUP fs'.infds fd ≠ SOME(IOStream nm, off))`,
  Induct
  >- (
    rw[basis_ffiTheory.extract_fs_with_numchars_def]
    \\ metis_tac[] )
  \\ Cases
  \\ rw[basis_ffiTheory.extract_fs_with_numchars_def]
  \\ fs[CaseEq"option",CaseEq"ffi_result"]
  >- metis_tac[]
  \\ fs[fsFFITheory.fs_ffi_part_def]
  \\ last_x_assum drule
  \\ disch_then match_mp_tac
  \\ reverse(fs[CaseEq"bool"]) \\ rveq \\ fs[]
  \\ fs[fsFFITheory.ffi_open_in_def,
        fsFFITheory.ffi_open_out_def,
        fsFFITheory.ffi_write_def,
        fsFFITheory.ffi_read_def,
        fsFFITheory.ffi_close_def]
  \\ fs[OPTION_CHOICE_EQUALS_OPTION, CaseEq"list"]
  \\ TRY pairarg_tac \\ fs[] \\ rveq \\ fs[]
  \\ fs[fsFFITheory.closeFD_def,
        fsFFITheory.read_def,
        fsFFITheory.openFile_truncate_def,
        fsFFITheory.openFile_def,
        fsFFITheory.write_def]
  \\ TRY pairarg_tac \\ fs[]
  \\ rveq \\ fs[ALOOKUP_ADELKEY, fsFFITheory.bumpFD_def, ALIST_FUPDKEY_ALOOKUP]
  \\ rw[fsFFITheory.fsupdate_def, ALIST_FUPDKEY_ALOOKUP]
  \\ PURE_CASE_TAC \\ fs[CaseEq"option"]
  \\ CCONTR_TAC \\ fs[]);

val interference_implemented_def = Define`
  interference_implemented mc ffi_oracle ffi_rel md ms0 ⇔
    ∃next_interfer ccache_interfer ffi_interfer.
    (∀n. mc.next_interfer n = next_interfer) ∧
    (∀n. mc.ccache_interfer n = ccache_interfer) ∧
    (∀n. mc.ffi_interfer n = ffi_interfer) ∧
    ∀ms k0.
      (ms = FUNPOW mc.target.next k0 ms0) ∧
      (∀x. x ∉ md ∧ x ∉ mc.prog_addresses ⇒ (mc.target.get_byte ms x = mc.target.get_byte ms0 x))
      ⇒
      (mc.target.get_pc ms ∈ mc.prog_addresses ∧
       encoded_bytes_in_mem mc.target.config (mc.target.get_pc ms)
         (mc.target.get_byte ms) mc.prog_addresses ∧
       mc.target.state_ok ms
      ⇒
        ∃k. (next_interfer (mc.target.next ms)
             = FUNPOW mc.target.next k (mc.target.next ms)) ∧
            (ffi_rel ms = ffi_rel (mc.target.next ms)) ∧
            (ffi_rel (mc.target.next ms) =
             ffi_rel (FUNPOW mc.target.next k (mc.target.next ms))) ∧
            (∀x. x ∉ md ∨ x ∈ mc.prog_addresses ⇒
                  (mc.target.get_byte (FUNPOW mc.target.next k (mc.target.next ms)) x =
                   mc.target.get_byte (mc.target.next ms) x))) ∧
      ((mc.target.get_pc ms = mc.ccache_pc) ⇒
        ∃k. (ccache_interfer
             (mc.target.get_reg ms mc.ptr_reg,
              mc.target.get_reg ms mc.len_reg,ms)
             = FUNPOW mc.target.next k ms) ∧
            (ffi_rel ms =
             ffi_rel (FUNPOW mc.target.next k ms)) ∧
            (∀x. x ∉ md ∨ x ∈ mc.prog_addresses ⇒
              (mc.target.get_byte (FUNPOW mc.target.next k ms) x =
               mc.target.get_byte ms x))) ∧
        ∀ffi ffi_index bytes bytes2 new_ffi new_bytes.
          (ffi.oracle = ffi_oracle) ∧
          (find_index (mc.target.get_pc ms) mc.ffi_entry_pcs 0 = SOME ffi_index) ∧
          (read_ffi_bytearrays mc ms = (SOME bytes, SOME bytes2)) ∧
          (call_FFI ffi (EL ffi_index mc.ffi_names) bytes bytes2 =
            FFI_return new_ffi new_bytes) ∧
          (ffi_rel ms ffi.io_events)
          ⇒
          ∃k.
            (ffi_interfer (ffi_index,new_bytes,ms) =
             FUNPOW mc.target.next k ms) ∧
            (ffi_rel (FUNPOW mc.target.next k ms) new_ffi.io_events) ∧
            (∀x. x ∉ md ∨ x ∈ mc.prog_addresses ⇒
              (mc.target.get_byte (FUNPOW mc.target.next k ms) x =
               mc.target.get_byte ms x))`;

val evaluate_Halt_FUNPOW_next = Q.store_thm("evaluate_Halt_FUNPOW_next",
  `∀mc (ffi:'ffi ffi_state) k ms t ms' ffi'.
   interference_implemented mc ffi.oracle ffi_rel md ms ∧
   (ffi_rel ms ffi.io_events) ∧
   (evaluate mc ffi k ms = (Halt t, ms', ffi')) ⇒
     ∃k'. (ms' = FUNPOW mc.target.next k' ms) ∧
          (ffi_rel ms' ffi'.io_events) ∧
          (∀x. x ∉ md ∪ mc.prog_addresses ⇒ (mc.target.get_byte ms' x = mc.target.get_byte ms x)) ∧
          ((∀x. t ≠ FFI_outcome x) ⇒ (mc.target.get_pc ms' = mc.halt_pc)) ∧
          (((mc.target.get_reg ms' mc.ptr_reg = 0w) ∧ (∀x. t ≠ FFI_outcome x))
            ⇒ (t = Success))`,
  ho_match_mp_tac targetSemTheory.evaluate_ind
  \\ rpt gen_tac
  \\ strip_tac
  \\ rpt gen_tac
  \\ strip_tac
  \\ pop_assum mp_tac
  \\ simp[Once targetSemTheory.evaluate_def]
  \\ fs[CaseEq"bool",targetSemTheory.apply_oracle_def,shift_seq_def]
  \\ strip_tac \\ fs[] \\ rw[]
  \\ TRY (qexists_tac`0` \\ simp[] \\ NO_TAC)
  >- (
    last_x_assum mp_tac
    \\ impl_tac
    >- (
      fs[interference_implemented_def]
      \\ conj_tac >- (
        qx_gen_tac`k0`
        \\ strip_tac
        \\ first_assum(qspec_then`0`mp_tac)
        \\ impl_tac >- fs[]
        \\ disch_then(mp_tac o CONJUNCT1)
        \\ impl_tac >- fs[]
        \\ disch_then(qx_choose_then`k1`strip_assume_tac)
        \\ fs[GSYM FUNPOW_ADD]
        \\ first_x_assum(qspec_then`SUC(k0+k1)`mp_tac)
        \\ simp[FUNPOW] \\ strip_tac
        \\ rw[] \\ fs[ADD1,FUNPOW_ADD]
        \\ metis_tac[])
      \\ first_x_assum(qspec_then`0`mp_tac)
      \\ simp[] \\ rw[] \\ fs[] )
    \\ disch_then(qx_choose_then`k1`strip_assume_tac)
    \\ fs[interference_implemented_def]
    \\ first_x_assum(qspec_then`0`mp_tac)
    \\ impl_tac >- fs[]
    \\ simp[]
    \\ disch_then(qx_choose_then`k2`strip_assume_tac o CONJUNCT1)
    \\ fs[GSYM FUNPOW_ADD]
    \\ qexists_tac`k1+k2+1` \\ rw[FUNPOW_ADD])
  >- (
    last_x_assum mp_tac
    \\ impl_tac
    >- (
      conj_tac >- (
        fs[interference_implemented_def]
        \\ qx_gen_tac`k0`
        \\ first_assum(qspec_then`0`mp_tac)
        \\ impl_tac >- fs[]
        \\ disch_then(mp_tac o CONJUNCT1 o CONJUNCT2)
        \\ impl_tac >- fs[]
        \\ disch_then(qx_choose_then`k1`strip_assume_tac)
        \\ fs[GSYM FUNPOW_ADD] \\ rw[]
        \\ first_x_assum(qspec_then`k0+k1`mp_tac)
        \\ simp[]
        \\ disch_then(mp_tac o CONJUNCT2 o CONJUNCT2)
        \\ disch_then (first_assum o mp_then Any mp_tac)
        \\ disch_then match_mp_tac \\ rw[]
        \\ fs[targetSemTheory.read_ffi_bytearrays_def,
              targetSemTheory.read_ffi_bytearray_def])
      \\ fs[interference_implemented_def]
      \\ first_x_assum(qspec_then`0`mp_tac)
      \\ simp[]
      \\ disch_then(qx_choose_then`k1`strip_assume_tac o CONJUNCT1)
      \\ fs[GSYM FUNPOW_ADD])
    \\ disch_then(qx_choose_then`k1`strip_assume_tac)
    \\ fs[interference_implemented_def]
    \\ first_x_assum(qspec_then`0`mp_tac)
    \\ simp[]
    \\ disch_then(qx_choose_then`k2`strip_assume_tac o CONJUNCT1)
    \\ fs[GSYM FUNPOW_ADD]
    \\ qexists_tac`k1+k2` \\ rw[])
  >- (
    fs[CaseEq"option",CaseEq"prod"]
    \\ reverse(fs[CaseEq"ffi$ffi_result"]) \\ rfs[]
    >- ( qexists_tac`0` \\ rw[] )
    \\ first_x_assum drule
    \\ fs[]
    \\ impl_tac
    >- (
      conj_tac >- (
        fs[interference_implemented_def]
        \\ qx_gen_tac`k0`
        \\ first_assum(qspec_then`0`mp_tac)
        \\ impl_tac >- fs[]
        \\ disch_then(mp_tac o CONJUNCT2 o CONJUNCT2)
        \\ simp_tac(srw_ss())[]
        \\ disch_then (first_assum o mp_then Any mp_tac)
        \\ disch_then (first_assum o mp_then Any mp_tac)
        \\ disch_then (first_assum o mp_then Any mp_tac)
        \\ disch_then (first_assum o mp_then Any mp_tac)
        \\ impl_tac >- fs[]
        \\ disch_then(qx_choose_then`k1`strip_assume_tac)
        \\ fs[GSYM FUNPOW_ADD]
        \\ strip_tac
        \\ first_x_assum(qspec_then`k0+k1`mp_tac)
        \\ simp[] \\ rw[]
        \\ first_x_assum match_mp_tac
        \\ fs[targetSemTheory.read_ffi_bytearrays_def,
              targetSemTheory.read_ffi_bytearray_def]
        \\ goal_assum(first_assum o mp_then Any mp_tac)
        \\ fs[]
        \\ fs[ffiTheory.call_FFI_def]
        \\ fs[CaseEq"bool",CaseEq"oracle_result"]
        \\ rveq \\ simp[])
      \\ fs[interference_implemented_def]
      \\ first_x_assum(qspec_then`0`mp_tac)
      \\ simp[]
      \\ disch_then (first_assum o mp_then Any mp_tac)
      \\ impl_tac >- fs[]
      \\ disch_then(qx_choose_then`k1`strip_assume_tac)
      \\ fs[GSYM FUNPOW_ADD])
    \\ disch_then(qx_choose_then`k1`strip_assume_tac)
    \\ fs[interference_implemented_def]
    \\ first_x_assum(qspec_then`0`mp_tac)
    \\ simp[]
    \\ disch_then (first_assum o mp_then Any mp_tac)
    \\ impl_tac >- fs[]
    \\ disch_then(qx_choose_then`k2`strip_assume_tac)
    \\ fs[GSYM FUNPOW_ADD]
    \\ qexists_tac`k1+k2` \\ rw[]));

val machine_sem_Terminate_FUNPOW_next = Q.store_thm("machine_sem_Terminate_FUNPOW_next",
  `interference_implemented mc st.oracle ffi_rel md ms ∧
   (ffi_rel ms st.io_events) ∧
   machine_sem mc (st:'ffi ffi_state) ms (Terminate t io_events) ⇒
   ∃k. ffi_rel (nxt mc k ms) io_events ∧
       (∀x. x ∉ md ∪ mc.prog_addresses ⇒ (mc.target.get_byte (nxt mc k ms) x = mc.target.get_byte ms x)) ∧
       ((∀x. t ≠ FFI_outcome x) ⇒ (mc.target.get_pc (nxt mc k ms) = mc.halt_pc)) ∧
       ((mc.target.get_reg (nxt mc k ms) mc.ptr_reg = 0w) ∧ (∀x. t ≠ FFI_outcome x)
        ⇒ (t = Success))`,
  rw[targetSemTheory.machine_sem_def]
  \\ imp_res_tac evaluate_Halt_FUNPOW_next
  \\ rfs[] \\ PROVE_TAC[]);

val word_of_bytes_bytes_to_word = Q.store_thm("word_of_bytes_bytes_to_word",
  `∀be a bs k.
   LENGTH bs ≤ k ⇒
   (word_of_bytes be a bs = bytes_to_word k a bs 0w be)`,
  Induct_on`bs`
  >- (
    EVAL_TAC
    \\ Cases_on`k`
    \\ EVAL_TAC
    \\ rw[] )
  \\ rw[data_to_word_memoryProofTheory.word_of_bytes_def]
  \\ Cases_on`k` \\ fs[]
  \\ rw[data_to_word_memoryProofTheory.bytes_to_word_def]
  \\ AP_THM_TAC
  \\ AP_TERM_TAC
  \\ first_x_assum match_mp_tac
  \\ fs[]);

val word_of_bytes_extract_bytes_le_32 = Q.store_thm("word_of_bytes_extract_bytes_le_32",
  `word_of_bytes F 0w [(7 >< 0) w; (15 >< 8) w; (23 >< 16) w; (31 >< 24) w] = w : word32`,
  rw[data_to_word_memoryProofTheory.word_of_bytes_def]
  \\ rw[wordSemTheory.set_byte_def,wordSemTheory.byte_index_def,wordSemTheory.word_slice_alt_def]
  \\ blastLib.BBLAST_TAC);

val bytes_in_memory_EL = Q.store_thm("bytes_in_memory_EL",
  `∀a bs m md k. bytes_in_memory a bs m md ∧ k < LENGTH bs ⇒ (m (a + n2w k) = EL k bs)`,
  Induct_on`bs`
  \\ rw[asmSemTheory.bytes_in_memory_def]
  \\ Cases_on`k` \\ fs[]
  \\ first_x_assum drule
  \\ disch_then drule
  \\ simp[ADD1, GSYM word_add_n2w]);

val bytes_in_memory_in_domain = Q.store_thm("bytes_in_memory_in_domain",
  `∀a bs m md k. bytes_in_memory a bs m md ∧ k < LENGTH bs ⇒ ((a + n2w k) ∈ md)`,
  Induct_on`bs`
  \\ rw[asmSemTheory.bytes_in_memory_def]
  \\ Cases_on`k` \\ fs[]
  \\ first_x_assum drule
  \\ disch_then drule
  \\ simp[ADD1, GSYM word_add_n2w]);

val bytes_in_mem_bytes_in_memory = Q.store_thm("bytes_in_mem_bytes_in_memory",
  `∀a bs m md k. bytes_in_mem a bs m md k ⇔ bytes_in_memory a bs m (md DIFF k)`,
  Induct_on`bs` \\ EVAL_TAC \\ rw[]
  \\ rw[EQ_IMP_THM]);

val read_bytearray_IMP_bytes_in_memory = Q.store_thm("read_bytearray_IMP_bytes_in_memory",
  `∀p n m ba m' md.
   (n = LENGTH ba) ∧ w2n p + n < dimword(:'a) ∧
   (∀k. (p <=+ k ∧ k <+ p + n2w n) ⇒ k ∈ md ∧ (m k = SOME (m' k))) ∧
   (read_bytearray (p:'a word) n m = SOME ba) ⇒
   bytes_in_memory p ba m' md`,
  Induct_on`ba` \\ rw[] >- EVAL_TAC
  \\ simp[asmSemTheory.bytes_in_memory_def]
  \\ fs[read_bytearray_def, CaseEq"option"]
  \\ first_assum(qspec_then`p`mp_tac)
  \\ impl_tac
  >- (
    simp[WORD_LOWER_EQ_REFL]
    \\ Cases_on`p`
    \\ simp[word_add_n2w, word_lo_n2w] \\ fs[] )
  \\ rw[]
  \\ first_x_assum irule
  \\ Cases_on`p` \\ fs[ADD1,word_add_n2w]
  \\ qexists_tac`m` \\ fs[]
  \\ Cases \\ strip_tac
  \\ first_x_assum irule
  \\ simp[WORD_LOWER_EQ_REFL, word_ls_n2w]
  \\ fs[word_lo_n2w, word_ls_n2w] \\ rfs[]);

val read_bytearray_IMP_mem_SOME = Q.store_thm("read_bytearray_IMP_mem_SOME",
  `∀p n m ba.
   (read_bytearray p n m = SOME ba) ⇒
   ∀k. p <=+ k ∧ k <+ p + n2w n ⇒ IS_SOME (m k)`,
  Induct_on`n`
  \\ rw[read_bytearray_def] \\ fs[]
  >- (
    fs[WORD_LOWER_OR_EQ]
    \\ metis_tac[WORD_LOWER_NOT_EQ, WORD_LOWER_ANTISYM] )
  \\ fs[CaseEq"option"]
  \\ Cases_on`p = k` \\ fs[]
  \\ first_x_assum drule
  \\ disch_then irule
  \\ Cases_on`p` \\ Cases_on`k`
  \\ fs[word_add_n2w,word_ls_n2w,word_lo_n2w]
  \\ rveq \\ fs[ADD1]);

val IMP_word_list = Q.store_thm("IMP_word_list",
  `8 <= dimindex(:'a) ⇒
   ∀p ls m.
   (m = IMAGE (λk. (p + n2w k * (bytes_in_word:'a word), EL k ls)) (count (LENGTH ls))) ∧
   w2n p + LENGTH ls * w2n (bytes_in_word:'a word) < dimword(:'a)
   ⇒ word_list p ls m`,
  strip_tac
  \\ Induct_on`ls` \\ rw[word_list_def] >- EVAL_TAC
  \\ fs[]
  \\ first_x_assum(qspec_then`p + bytes_in_word`mp_tac)
  \\ impl_tac
  >- (
    fs[ADD1, LEFT_ADD_DISTRIB]
    \\ Cases_on`p` \\ Cases_on`bytes_in_word`
    \\ fs[word_add_n2w] )
  \\ qmatch_goalsub_abbrev_tac`word_list _ ls m2`
  \\ strip_tac
  \\ simp[set_sepTheory.STAR_def]
  \\ simp[set_sepTheory.one_def]
  \\ qexists_tac`m2`
  \\ simp[set_sepTheory.SPLIT_def]
  \\ conj_tac
  >- (
    simp[Abbr`m2`,EXTENSION]
    \\ qx_gen_tac`x`
    \\ Cases_on`x = (p,h)` \\ fs[]
    >- ( qexists_tac`0` \\ simp[] )
    \\ EQ_TAC \\ strip_tac \\ simp[]
    >- (
      qexists_tac`SUC k`
      \\ simp[GSYM word_add_n2w,ADD1,WORD_LEFT_ADD_DISTRIB])
    \\ Cases_on`k` >- fs[]
    \\ simp[]
    \\ qexists_tac`n`
    \\ simp[GSYM word_add_n2w,ADD1,WORD_LEFT_ADD_DISTRIB])
  \\ rw[Abbr`m2`]
  \\ Cases_on`k < LENGTH ls` \\ fs[]
  \\ rpt disj1_tac
  \\ rewrite_tac[GSYM WORD_ADD_ASSOC]
  \\ rewrite_tac[addressTheory.WORD_EQ_ADD_CANCEL]
  \\ Cases_on`bytes_in_word`
  \\ fs[word_add_n2w,word_mul_n2w,ADD1,LEFT_ADD_DISTRIB]
  \\ DEP_REWRITE_TAC[LESS_MOD]
  \\ fs[]
  \\ conj_tac >- (
    irule LESS_EQ_LESS_TRANS
    \\ qpat_x_assum`_ +_ < _`assume_tac
    \\ asm_exists_tac \\ fs[]
    \\ irule LESS_EQ_TRANS
    \\ qexists_tac`n * LENGTH ls`
    \\ simp[]
    \\ CONV_TAC(LAND_CONV (REWR_CONV MULT_COMM))
    \\ simp[] )
  \\ disj1_tac
  \\ fs[bytes_in_word_def]
  \\ rw[]
  \\ DEP_REWRITE_TAC[LESS_MOD]
  \\ simp[dimword_def,DIV_LT_X,DIV_EQ_0]
  \\ `dimindex(:'a) = 1 * dimindex(:'a)` by fs[]
  \\ pop_assum(CONV_TAC o LAND_CONV o REWR_CONV)
  \\ irule bitTheory.LESS_MULT_MONO2
  \\ simp[]);

val mem_eq_imp_asm_write_bytearray_eq = Q.store_thm("mem_eq_imp_asm_write_bytearray_eq",
  `∀a bs.
    (m1 k = m2 k) ⇒
    (asm_write_bytearray a bs m1 k = asm_write_bytearray a bs m2 k)`,
  Induct_on`bs`
  \\ rw[lab_to_targetProofTheory.asm_write_bytearray_def]
  \\ rw[APPLY_UPDATE_THM]);

val asm_write_bytearray_unchanged = Q.store_thm("asm_write_bytearray_unchanged",
  `∀a bs m z. (x <+ a ∨ a + n2w (LENGTH bs) <=+ x) ∧
    (w2n a + LENGTH bs < dimword(:'a)) ∧ (z = m x)
  ⇒ (asm_write_bytearray (a:'a word) bs m x = z)`,
  Induct_on`bs`
  \\ rw[lab_to_targetProofTheory.asm_write_bytearray_def,APPLY_UPDATE_THM]
  \\ TRY (
    Cases_on`a` \\ fs[word_ls_n2w,word_lo_n2w,word_add_n2w]
    \\ NO_TAC )
  \\ first_x_assum match_mp_tac
  \\ Cases_on`a`
  \\ Cases_on`x`
  \\ fs[word_ls_n2w,word_lo_n2w,word_add_n2w]);

val asm_write_bytearray_append = Q.store_thm("asm_write_bytearray_append",
  `∀a l1 l2 m.
   w2n a + LENGTH l1 + LENGTH l2 < dimword (:'a) ⇒
   (asm_write_bytearray (a:'a word) (l1 ++ l2) m =
    asm_write_bytearray (a + n2w (LENGTH l1)) l2 (asm_write_bytearray a l1 m))`,
  Induct_on`l1` \\ rw[lab_to_targetProofTheory.asm_write_bytearray_def]
  \\ rw[FUN_EQ_THM, APPLY_UPDATE_THM]
  \\ rw[]
  >- (
    irule (GSYM asm_write_bytearray_unchanged)
    \\ simp[APPLY_UPDATE_THM]
    \\ Cases_on`a` \\ simp[word_lo_n2w,word_add_n2w,word_ls_n2w]
    \\ fs[] )
  \\ fs[ADD1,GSYM word_add_n2w]
  \\ first_x_assum (qspec_then`a+1w`mp_tac)
  \\ simp[]
  \\ Cases_on`a` \\ fs[word_add_n2w]
  \\ disch_then drule
  \\ rw[]
  \\ irule mem_eq_imp_asm_write_bytearray_eq
  \\ simp[APPLY_UPDATE_THM]);

val asm_write_bytearray_EL = Q.store_thm("asm_write_bytearray_EL",
  `∀a bs m x. x < LENGTH bs ∧ LENGTH bs < dimword(:'a) ⇒
   (asm_write_bytearray (a:'a word) bs m (a + n2w x) = EL x bs)`,
  Induct_on`bs`
  \\ rw[lab_to_targetProofTheory.asm_write_bytearray_def,APPLY_UPDATE_THM]
  \\ Cases_on`x` \\ fs[]
  >- ( fs[addressTheory.WORD_EQ_ADD_CANCEL] )
  \\ first_x_assum drule
  \\ simp[ADD1,GSYM word_add_n2w]
  \\ metis_tac[WORD_ADD_ASSOC,WORD_ADD_COMM]);

(*
val align_eq_0_imp = Q.store_thm("align_eq_0_imp",
  `0 < p ⇒ ((align p a = 0w) ⇒ w2n a < 2 ** p)`,
  rw[alignmentTheory.align_w2n, dimword_def]
  \\ reverse(Cases_on`p ≤ dimindex(:'a)`)
  >- (
    qspec_then`a`assume_tac w2n_lt
    \\ fs[dimword_def]
    \\ irule LESS_LESS_EQ_TRANS
    \\ asm_exists_tac \\ fs[] )
  \\ fs[MOD_EQ_0_DIVISOR]
  \\ Cases_on`d` \\ fs[]
  >- (
    `1 < 2 ** p` by fs[ONE_LT_EXP]
    \\ fs[DIV_EQ_0] )
  \\ fs[MULT]
*)

val get_byte_word_of_bytes = Q.store_thm("get_byte_word_of_bytes",
  `good_dimindex(:'a) ⇒
   i < LENGTH ls ∧ LENGTH ls ≤ w2n (bytes_in_word:'a word) ⇒
  (get_byte (n2w i) (word_of_bytes be (0w:'a word) ls) be = EL i ls)`,
  strip_tac
  \\ `∃k. dimindex(:'a) DIV 8 = 2 ** k` by(
    fs[labPropsTheory.good_dimindex_def]
    \\ TRY(qexists_tac`2` \\ EVAL_TAC \\ NO_TAC)
    \\ TRY(qexists_tac`3` \\ EVAL_TAC \\ NO_TAC) )
  \\ strip_tac
  \\ Q.ISPECL_THEN[`be`,`0w`,`ls`,`2 ** k`]mp_tac word_of_bytes_bytes_to_word
  \\ impl_keep_tac >- (
    rfs[bytes_in_word_def, dimword_def]
    \\ fs[labPropsTheory.good_dimindex_def] \\ rfs[])
  \\ rw[]
  \\ DEP_REWRITE_TAC[data_to_word_memoryProofTheory.get_byte_bytes_to_word]
  \\ rw[]);

val word_msb_align = Q.store_thm("word_msb_align",
  `p < dimindex(:'a) ⇒ (word_msb (align p w) = word_msb (w:'a word))`,
  rw[alignmentTheory.align_bitwise_and,word_msb]
  \\ rw[data_to_word_memoryProofTheory.word_bit_and]
  \\ rw[data_to_word_memoryProofTheory.word_bit_lsl]
  \\ rw[word_bit_test, MOD_EQ_0_DIVISOR, dimword_def]);

val get_byte_EL_words_of_bytes = Q.store_thm("get_byte_EL_words_of_bytes",
  `∀be ls.
   i < LENGTH ls ∧ w2n (bytes_in_word:'a word) * LENGTH ls ≤ dimword(:'a) ∧ good_dimindex(:'a) ⇒
   (get_byte (n2w i : α word)
      (EL (w2n (byte_align ((n2w i):α word)) DIV (w2n (bytes_in_word:α word)))
        (words_of_bytes be ls)) be = EL i ls)`,
  completeInduct_on`i`
  \\ Cases_on`ls`
  \\ rw[data_to_word_memoryProofTheory.words_of_bytes_def]
  \\ qmatch_goalsub_abbrev_tac`MAX 1 bw`
  \\ `0 < bw` by (
     fs[Abbr`bw`,labPropsTheory.good_dimindex_def]
     \\ EVAL_TAC \\ fs[dimword_def] )
  \\ `MAX 1 bw = bw` by rw[MAX_DEF] \\ fs[]
  \\ Cases_on`i < bw` \\ fs[]
  >- (
    `byte_align (n2w i) = 0w`
    by(
      simp[alignmentTheory.byte_align_def]
      \\ irule imp_align_eq_0
      \\ fs[labPropsTheory.good_dimindex_def,Abbr`bw`]
      \\ rfs[bytes_in_word_def,dimword_def] )
    \\ simp[ZERO_DIV]
    \\ DEP_REWRITE_TAC[UNDISCH get_byte_word_of_bytes]
    \\ fs[LENGTH_TAKE_EQ]
    \\ Cases_on`i` \\ fs[EL_TAKE] )
  \\ fs[NOT_LESS]
  \\ pop_assum (strip_assume_tac o SIMP_RULE std_ss [LESS_EQ_EXISTS])
  \\ `byte_align (n2w (bw + p)) = n2w bw + byte_align (n2w p)`
  by (
    simp[GSYM word_add_n2w]
    \\ simp[alignmentTheory.byte_align_def]
    \\ DEP_REWRITE_TAC[align_add_aligned_gen]
    \\ simp[Abbr`bw`]
    \\ CONV_TAC(REWR_CONV(GSYM alignmentTheory.byte_aligned_def))
    \\ (data_to_word_assignProofTheory.byte_aligned_bytes_in_word
        |> Q.GEN`w` |> Q.SPEC`1w` |> UNDISCH |> mp_tac)
    \\ simp[] )
  \\ simp[]
  \\ DEP_REWRITE_TAC[w2n_add]
  \\ conj_tac
  >- (
    simp[Abbr`bw`]
    \\ reverse conj_tac >- (
      fs[labPropsTheory.good_dimindex_def,
         bytes_in_word_def]
      \\ EVAL_TAC \\ fs[] \\ EVAL_TAC )
    \\ simp[alignmentTheory.byte_align_def]
    \\ DEP_REWRITE_TAC[word_msb_align]
    \\ conj_tac >- ( fs[labPropsTheory.good_dimindex_def])
    \\ simp[word_msb_n2w]
    \\ qmatch_assum_abbrev_tac`bw * r ≤ dimword _`
    \\ `r ≤ dimword (:'a) DIV bw` by fs[X_LE_DIV]
    \\ `p < dimword(:'a) DIV bw` by fs[]
    \\ match_mp_tac bitTheory.NOT_BIT_GT_TWOEXP
    \\ fs[dimword_def, bytes_in_word_def]
    \\ fs[Abbr`bw`, labPropsTheory.good_dimindex_def]
    \\ rfs[] )
  \\ `bw < dimword(:'a)` by fs[Abbr`bw`, bytes_in_word_def]
  \\ simp[]
  \\ DEP_REWRITE_TAC[ADD_DIV_RWT]
  \\ simp[]
  \\ simp[EL_CONS,PRE_SUB1]
  \\ simp[GSYM word_add_n2w]
  \\ `n2w bw = byte_align (n2w bw)`
  by(
    fs[Abbr`bw`,bytes_in_word_def,alignmentTheory.byte_align_def]
    \\ fs[labPropsTheory.good_dimindex_def]
    \\ EVAL_TAC \\ fs[dimword_def] \\ EVAL_TAC )
  \\ pop_assum SUBST1_TAC
  \\ once_rewrite_tac[WORD_ADD_COMM]
  \\ simp[data_to_word_memoryProofTheory.get_byte_byte_align]
  \\ first_x_assum(qspec_then`p`mp_tac)
  \\ simp[]
  \\ disch_then(qspecl_then[`be`,`DROP (bw-1)t`]mp_tac)
  \\ impl_tac >- fs[ADD1]
  \\ simp[EL_DROP]);

val words_of_bytes_append_word = Q.store_thm("words_of_bytes_append_word",
  `0 < LENGTH l1 ∧ (LENGTH l1 = w2n (bytes_in_word:'a word)) ⇒
   (words_of_bytes be (l1 ++ l2) = word_of_bytes be (0w:'a word) l1 :: words_of_bytes be l2)`,
  rw[]
  \\ Cases_on`l1` \\ rw[data_to_word_memoryProofTheory.words_of_bytes_def] \\ fs[]
  \\ fs[MAX_DEF]
  \\ first_x_assum(assume_tac o SYM) \\ fs[ADD1]
  \\ rw[TAKE_APPEND,DROP_APPEND,DROP_LENGTH_NIL] \\ fs[]);

val get_mem_word_def = Define`
  get_mem_word (m:word32->word8) (pc:word32) : word32 =
  (m (pc + 3w) @@
   ((m (pc + 2w) @@
     ((m (pc + 1w) @@
       m (pc)) : word16)) :word24))`;

val get_mem_word_get_byte = Q.store_thm("get_mem_word_get_byte",
  `(∀x. r0 + n2w (4 * (LENGTH ll + k)) <=+ x ∧ x <+ r0 + n2w (4 * (LENGTH ll + k) + 4)
      ⇒ (m x = get_byte x (EL (w2n (byte_align x - r0) DIV 4) (ll ++ ls ++ lr)) F)) ∧
   (LENGTH ll = off) ∧
   k < LENGTH ls ∧ byte_aligned r0 ∧ (4 * (off + k)) < dimword(:31) ∧
   w2n r0 + (4 * (off + k) + 4) < dimword(:32)
   ⇒ (get_mem_word m (r0 + n2w (4 * (off + k))) = EL k ls)`,
  rw[get_mem_word_def]
  \\ ntac 4 (
    qmatch_goalsub_abbrev_tac`m x`
    \\ first_assum(qspec_then`x`mp_tac)
    \\ impl_tac
    >- (
      fs[Abbr`x`]
      \\ Cases_on`r0` \\ fs[word_add_n2w]
      \\ fs[word_ls_n2w, word_lo_n2w] )
    \\ disch_then SUBST_ALL_TAC
    \\ qunabbrev_tac`x`)
  \\ last_x_assum kall_tac
  \\ fs[alignmentTheory.byte_aligned_def, alignmentTheory.byte_align_def]
  \\ qmatch_goalsub_abbrev_tac`pc + 2w`
  \\ `aligned 2 pc`
  by (
    simp[Abbr`pc`]
    \\ (alignmentTheory.aligned_add_sub_cor
        |> SPEC_ALL |> UNDISCH |> CONJUNCT1 |> DISCH_ALL
        |> irule)
    \\ simp[]
    \\ simp[GSYM ALIGNED_eq_aligned]
    \\ simp[addressTheory.ALIGNED_n2w])
  \\ simp[align_add_aligned_gen]
  \\ simp[Abbr`pc`]
  \\ qmatch_goalsub_abbrev_tac`r0 + x`
  \\ `align 2 (r0 + x) = r0 + x` by fs[alignmentTheory.aligned_def]
  \\ `r0 + x = byte_align (r0 + x)` by fs[alignmentTheory.byte_align_def]
  \\ qhdtm_x_assum`align`SUBST_ALL_TAC
  \\ simp_tac(srw_ss())[]
  \\ pop_assum SUBST_ALL_TAC
  \\ once_rewrite_tac[WORD_ADD_COMM]
  \\ DEP_REWRITE_TAC[data_to_word_memoryProofTheory.get_byte_byte_align]
  \\ DEP_REWRITE_TAC[
       data_to_word_memoryProofTheory.get_byte_byte_align
       |> Q.GEN`a'` |> Q.SPEC`0w` |> SIMP_RULE(srw_ss())[]]
  \\ rewrite_tac[CONJ_ASSOC]
  \\ conj_tac >- EVAL_TAC
  \\ DEP_REWRITE_TAC[w2n_add]
  \\ DEP_REWRITE_TAC[ADD_DIV_RWT]
  \\ conj_tac >- ( simp[Abbr`x`] \\ EVAL_TAC )
  \\ conj_tac >- (
    fs[Abbr`x`, word_msb_n2w_numeric, NOT_LESS_EQUAL]
    \\ EVAL_TAC )
  \\ `w2n x DIV 4 = k + LENGTH ll`
  by (
    simp[Abbr`x`]
    \\ once_rewrite_tac[MULT_COMM]
    \\ simp[MULT_DIV] )
  \\ pop_assum SUBST_ALL_TAC
  \\ ntac 3 (
    qmatch_goalsub_abbrev_tac`w2n a`
    \\ pop_assum mp_tac \\ CONV_TAC(LAND_CONV EVAL)
    \\ strip_tac \\ simp[Abbr`a`] )
  \\ simp[EL_APPEND_EQN]
  \\ simp[wordSemTheory.get_byte_def, wordSemTheory.byte_index_def]
  \\ blastLib.BBLAST_TAC);

val backend_correct_asm_step_target_state_rel = Q.store_thm("backend_correct_asm_step_target_state_rel",
  `backend_correct t ∧
   target_state_rel t s1 ms ∧
   asm_step t.config s1 i s2
   ⇒
   ∃n.
   target_state_rel t s2 (FUNPOW t.next n ms) ∧
   (∀j. j < n ⇒
     (∀pc. pc ∈ all_pcs (LENGTH (t.config.encode i)) s1.pc 0 ⇒
             (t.get_byte (FUNPOW t.next j ms) pc = t.get_byte ms pc)) ∧
     (t.get_pc (FUNPOW t.next j ms) ∈
       all_pcs (LENGTH (t.config.encode i)) s1.pc t.config.code_alignment) ∧
     (t.state_ok (FUNPOW t.next j ms))) ∧
   (∀j x. j ≤ n ∧ x ∉ s1.mem_domain ⇒ (t.get_byte (FUNPOW t.next j ms) x = t.get_byte ms x))`,
  rw[asmPropsTheory.backend_correct_def]
  \\ first_x_assum drule
  \\ disch_then drule
  \\ strip_tac
  \\ first_x_assum(qspec_then`K I`mp_tac)
  \\ impl_tac >- ( EVAL_TAC \\ rw[] )
  \\ srw_tac[ETA_ss][]
  \\ imp_res_tac asmPropsTheory.asserts_IMP_FOLDR_COUNT_LIST
  \\ fs[FOLDR_FUNPOW, LENGTH_COUNT_LIST]
  \\ qexists_tac`SUC n`
  \\ simp[FUNPOW]
  \\ simp[GSYM FORALL_AND_THM]
  \\ gen_tac
  \\ Cases_on`j` \\ fs[]
  >- (
    fs[asmSemTheory.asm_step_def, asmPropsTheory.target_state_rel_def]
    \\ `t.config.encode i <> []`
    by ( fs[asmPropsTheory.target_ok_def, asmPropsTheory.enc_ok_def] )
    \\ Cases_on`t.config.encode i` \\ fs[asmSemTheory.bytes_in_memory_def]
    \\ fs[asmPropsTheory.all_pcs_thm]
    \\ qexists_tac`0` \\ fs[])
  \\ conj_tac
  >- (
    strip_tac
    \\ drule asmPropsTheory.asserts_IMP_FOLDR_COUNT_LIST_LESS
    \\ disch_then drule
    \\ simp[FOLDR_FUNPOW] )
  \\ ntac 2 strip_tac
  \\ drule asmPropsTheory.asserts2_every
  \\ strip_tac
  \\ qmatch_goalsub_rename_tac`SUC m`
  \\ qho_match_abbrev_tac`P ms (FUNPOW t.next (SUC m) ms)`
  \\ irule FUNPOW_refl_trans_chain
  \\ fs[ADD1,Abbr`P`]
  \\ simp[reflexive_def,transitive_def]);

val backend_correct_RTC_asm_step_target_state_rel = Q.store_thm("backend_correct_RTC_asm_step_target_state_rel",
  `backend_correct t ∧
   target_state_rel t s1 ms ∧
   RTC (λs1 s2. ∃i. asm_step t.config s1 i s2) s1 s2
   ⇒
   ∃n. target_state_rel t s2 (FUNPOW t.next n ms)`,
  strip_tac
  \\ first_assum(mp_then (Pat`RTC`) mp_tac (GEN_ALL RTC_lifts_invariants))
  \\ disch_then ho_match_mp_tac
  \\ reverse conj_tac
  >- ( qexists_tac`0` \\ rw[] )
  \\ rw[]
  \\ drule (GEN_ALL backend_correct_asm_step_target_state_rel)
  \\ disch_then drule
  \\ disch_then drule
  \\ rw[GSYM FUNPOW_ADD]
  \\ asm_exists_tac \\ rw[]);

val asm_step_target_configured = Q.store_thm("asm_step_target_configured",
  `asm_step c s1 i s2 ∧ target_configured s1 mc ⇒
   target_configured s2 mc`,
  rw[asmSemTheory.asm_step_def]
  \\ fs[lab_to_targetProofTheory.target_configured_def]);

val RTC_asm_step_target_configured = Q.store_thm("RTC_asm_step_target_configured",
  `RTC (λs1 s2. ∃i. asm_step c s1 i s2) s1 s2 ∧
   target_configured s1 mc ⇒
   target_configured s2 mc`,
  rw[]
  \\ first_assum(mp_then (Pat`RTC`) mp_tac (GEN_ALL RTC_lifts_invariants))
  \\ disch_then ho_match_mp_tac \\ rw[]
  \\ metis_tac[asm_step_target_configured]);

val RTC_asm_step_consts = Q.store_thm("RTC_asm_step_consts",
  `RTC (λs1 s2. ∃i. asm_step c s1 i s2) s1 s2
  ⇒ (s2.mem_domain = s1.mem_domain) ∧
    (s2.be = s1.be)`,
  rw[]
  \\ first_assum(mp_then (Pat`RTC`) mp_tac (GEN_ALL RTC_lifts_invariants))
  \\ disch_then ho_match_mp_tac \\ rw[]
  \\ fs[asmSemTheory.asm_step_def]
  \\ rw[]);

val mem_op_outside_mem_domain = Q.store_thm("mem_op_outside_mem_domain",
  `∀m n a s x. x ∉ s.mem_domain ∧ ¬(mem_op m n a s).failed ⇒ ((asmSem$mem_op m n a s).mem x = s.mem x)`,
  Cases \\ rw[asmSemTheory.mem_op_def]
  \\ fs[asmSemTheory.mem_load_def,
        asmSemTheory.mem_store_def,
        asmSemTheory.upd_reg_def, asmSemTheory.assert_def]
  \\ TRY pairarg_tac \\ fs[]
  \\ cheat (* local proof *));

val inst_outside_mem_domain = Q.store_thm("inst_outside_mem_domain",
  `∀i. x ∉ s.mem_domain ∧ ¬(inst i s).failed ⇒ ((inst i s).mem x = s.mem x)`,
  Cases \\ rw[asmSemTheory.inst_def]
  >- EVAL_TAC
  \\ rw[mem_op_outside_mem_domain]);

val asm_outside_mem_domain = Q.store_thm("asm_outside_mem_domain",
  `∀i p s x. x ∉ s.mem_domain ∧ ¬(asm i p s).failed ⇒ ((asm i p s).mem x = s.mem x)`,
  ho_match_mp_tac asmTheory.asm_induction
  \\ rw[asmSemTheory.asm_def]
  >- rw[inst_outside_mem_domain]
  >- rw[asmSemTheory.jump_to_offset_def]
  >- rw[asmSemTheory.jump_to_offset_def]
  >- (rw[asmSemTheory.jump_to_offset_def] >- EVAL_TAC)
  >- EVAL_TAC
  >- EVAL_TAC);

val asm_step_outside_mem_domain = Q.store_thm("asm_step_outside_mem_domain",
  `asm_step c s1 i s2 ⇒
   (∀x. x ∉ s1.mem_domain ⇒ (s2.mem x = s1.mem x))`,
  rw[asmSemTheory.asm_step_def]
  \\ rw[asm_outside_mem_domain]);

val RTC_asm_step_outside_mem_domain = Q.store_thm("RTC_asm_step_outside_mem_domain",
  `∀s1 s2. RTC (λs1 s2. ∃i. asm_step c s1 i s2) s1 s2
  ⇒ (∀a. a ∉ s1.mem_domain ⇒ (s2.mem a = s1.mem a))`,
  ho_match_mp_tac RTC_INDUCT
  \\ rw[]
  \\ drule asm_step_outside_mem_domain
  \\ disch_then drule \\ rw[]
  \\ fs[asmSemTheory.asm_step_def]
  \\ metis_tac[asmPropsTheory.asm_consts]);

val LENGTH_words_of_bytes = Q.store_thm("LENGTH_words_of_bytes",
  `8 ≤ dimindex(:'a) ⇒
   ∀be ls.
   (LENGTH (words_of_bytes be ls : 'a word list) =
    LENGTH ls DIV (w2n (bytes_in_word : 'a word)) +
    MIN 1 (LENGTH ls MOD (w2n (bytes_in_word : 'a word))))`,
  strip_tac
  \\ recInduct data_to_word_memoryProofTheory.words_of_bytes_ind
  \\ `1 ≤ w2n bytes_in_word`
  by (
    simp[bytes_in_word_def,dimword_def]
    \\ DEP_REWRITE_TAC[LESS_MOD]
    \\ rw[DIV_LT_X, X_LT_DIV, X_LE_DIV]
    \\ match_mp_tac LESS_TRANS
    \\ qexists_tac`2 ** dimindex(:'a)`
    \\ simp[] )
  \\ simp[data_to_word_memoryProofTheory.words_of_bytes_def]
  \\ conj_tac
  >- ( DEP_REWRITE_TAC[ZERO_DIV] \\ fs[] )
  \\ rw[ADD1]
  \\ `MAX 1 (w2n (bytes_in_word:'a word)) = w2n (bytes_in_word:'a word)`
      by rw[MAX_DEF]
  \\ fs[]
  \\ qmatch_goalsub_abbrev_tac`(m - n) DIV _`
  \\ Cases_on`m < n` \\ fs[]
  >- (
    `m - n = 0` by fs[]
    \\ simp[]
    \\ simp[LESS_DIV_EQ_ZERO]
    \\ rw[MIN_DEF]
    \\ fs[Abbr`m`] )
  \\ simp[SUB_MOD]
  \\ qspec_then`1`(mp_tac o GEN_ALL)(Q.GEN`q`DIV_SUB) \\ fs[]
  \\ disch_then kall_tac
  \\ Cases_on`m MOD n = 0` \\ fs[]
  >- (
    DEP_REWRITE_TAC[SUB_ADD]
    \\ fs[X_LE_DIV] )
  \\ `MIN 1 (m MOD n) = 1` by simp[MIN_DEF]
  \\ fs[]
  \\ `m DIV n - 1 + 1 = m DIV n` suffices_by fs[]
  \\ DEP_REWRITE_TAC[SUB_ADD]
  \\ fs[X_LE_DIV]);

val ag32_io_events_unchanged = Q.store_thm("ag32_io_events_unchanged",
  `Decode (
    let v : word32 = (31 >< 2) ms.PC : word30 @@ (0w:word2) in
      (ms.MEM (v + 3w) @@
       ((ms.MEM (v + 2w) @@
         ((ms.MEM (v + 1w) @@
           ms.MEM (v + 0w)) : word16)) : word24)))
    ≠ Interrupt
   ⇒
   ((Next ms).io_events = ms.io_events) `,
  rw[ag32Theory.Next_def]
  \\ rw[ag32Theory.Run_def]
  \\ PURE_CASE_TAC \\ fs[] \\ TRY(PairCases_on`p`)
  \\ rw[
    ag32Theory.dfn'Accelerator_def,
    ag32Theory.dfn'In_def,
    ag32Theory.dfn'Jump_def,
    ag32Theory.ALU_def,
    ag32Theory.dfn'JumpIfNotZero_def,
    ag32Theory.dfn'JumpIfZero_def,
    ag32Theory.dfn'LoadConstant_def,
    ag32Theory.dfn'LoadMEM_def,
    ag32Theory.dfn'LoadMEMByte_def,
    ag32Theory.dfn'LoadUpperConstant_def,
    ag32Theory.dfn'Normal_def,
    ag32Theory.norm_def,
    ag32Theory.dfn'Out_def,
    ag32Theory.dfn'Shift_def,
    ag32Theory.dfn'StoreMEM_def,
    ag32Theory.dfn'StoreMEMByte_def,
    ag32Theory.incPC_def]
  \\ PURE_CASE_TAC \\ fs[] \\ rw[]);

val ag32_enc_lengths = Q.store_thm("ag32_enc_lengths",
  `LENGTH (ag32_enc istr) ∈ {4;8;12;16}`,
  Cases_on`istr`
  \\ TRY(rename1`JumpCmp _ _ ri _` \\ Cases_on`ri`)
  \\ TRY(rename1`Inst i ` \\ Cases_on`i`)
  \\ TRY(rename1`Inst (Mem m _ ri) ` \\ Cases_on`m` \\ Cases_on`ri`)
  \\ TRY(rename1`Inst (Arith a) ` \\ Cases_on`a`)
  \\ TRY(rename1`Inst (Arith (Binop _ _ _ ri)) ` \\ Cases_on`ri`)
  \\  rw[ag32_targetTheory.ag32_enc_def,
         ag32_targetTheory.ag32_constant_def,
         ag32_targetTheory.ag32_jump_constant_def,
         ag32_targetTheory.ag32_encode_def,
         ag32_targetTheory.ag32_encode1_def]);

val ag32_enc_not_Interrupt = Q.store_thm("ag32_enc_not_Interrupt",
  `4 * k < LENGTH (ag32_enc istr) ⇒
   let bs = DROP (4 * k) (ag32_enc istr) in
   Decode (EL 3 bs @@ ((EL 2 bs @@ ((EL 1 bs @@ EL 0 bs) : word16)) : word24)) ≠ Interrupt`,
  Cases_on`istr`
  \\ TRY(rename1`JumpCmp _ _ ri _` \\ Cases_on`ri`)
  \\ TRY(rename1`Inst i ` \\ Cases_on`i`)
  \\ TRY(rename1`Inst (Mem m _ ri) ` \\ Cases_on`m` \\ Cases_on`ri`)
  \\ TRY(rename1`Inst (Arith a) ` \\ Cases_on`a`)
  \\ TRY(rename1`Inst (Arith (Binop _ _ _ ri)) ` \\ Cases_on`ri`)
  \\ rw[ag32_targetTheory.ag32_enc_def,
        ag32_targetTheory.ag32_encode_def,
        ag32_targetTheory.ag32_encode1_def,
        arm_stepTheory.concat_bytes,
        ag32_targetTheory.ag32_constant_def,
        ag32_targetTheory.ag32_jump_constant_def,
        ag32_targetProofTheory.Decode_Encode]
  \\ Cases_on`k` \\ fs[arm_stepTheory.concat_bytes, ag32_targetProofTheory.Decode_Encode]
  \\ qmatch_asmsub_rename_tac`4 * SUC k < _`
  \\ Cases_on`k` \\ fs[arm_stepTheory.concat_bytes, ag32_targetProofTheory.Decode_Encode]
  \\ qmatch_asmsub_rename_tac`4 * SUC (SUC k) < _`
  \\ Cases_on`k` \\ fs[arm_stepTheory.concat_bytes, ag32_targetProofTheory.Decode_Encode]
  \\ qmatch_asmsub_rename_tac`4 * SUC (SUC (SUC k)) < _`
  \\ Cases_on`k` \\ fs[arm_stepTheory.concat_bytes, ag32_targetProofTheory.Decode_Encode]);

val RTC_asm_step_ag32_target_state_rel_io_events = Q.store_thm("RTC_asm_step_ag32_target_state_rel_io_events",
  `target_state_rel ag32_target s1 ms ∧
   RTC (λs1 s2. ∃i. asm_step ag32_config s1 i s2) s1 s2
   ⇒
   ∃n. target_state_rel ag32_target s2 (FUNPOW Next n ms) ∧
       ((FUNPOW Next n ms).io_events = ms.io_events) ∧
       (∀x. x ∉ s1.mem_domain ⇒ ((FUNPOW Next n ms).MEM x = ms.MEM x))`,
  once_rewrite_tac[CONJ_COMM]
  \\ rewrite_tac[GSYM AND_IMP_INTRO]
  \\ qid_spec_tac`ms`
  \\ simp[RIGHT_FORALL_IMP_THM]
  \\ qho_match_abbrev_tac`RR^* s1 s2 ⇒ P s1 s2`
  \\ match_mp_tac RTC_INDUCT
  \\ simp[Abbr`P`,Abbr`RR`]
  \\ conj_tac
  >- ( rw[] \\ qexists_tac`0` \\ simp[] )
  \\ rpt gen_tac \\ strip_tac
  \\ ntac 2 strip_tac
  \\ ((MATCH_MP
        (REWRITE_RULE[GSYM AND_IMP_INTRO] backend_correct_asm_step_target_state_rel)
        ag32_targetProofTheory.ag32_backend_correct) |> GEN_ALL |> drule)
  \\ simp[SIMP_CONV(srw_ss())[ag32_targetTheory.ag32_target_def]``ag32_target.config``]
  \\ simp[SIMP_CONV(srw_ss())[ag32_targetTheory.ag32_target_def]``ag32_target.next``]
  \\ disch_then drule
  \\ strip_tac
  \\ first_x_assum drule
  \\ strip_tac
  \\ fs[GSYM FUNPOW_ADD]
  \\ once_rewrite_tac[CONJ_COMM]
  \\ asm_exists_tac \\ simp[]
  \\ `y.mem_domain = x.mem_domain`
  by ( fs[asmSemTheory.asm_step_def] \\ rveq \\ fs[] )
  \\ fs[]
  \\ ntac 4 (pop_assum kall_tac)
  \\ fs[asmSemTheory.asm_step_def]
  \\ `x.pc = ms.PC` by (
    fs[asmPropsTheory.target_state_rel_def, ag32_targetTheory.ag32_target_def] )
  \\ pop_assum SUBST_ALL_TAC
  \\ fs[SIMP_CONV(srw_ss())[ag32_targetTheory.ag32_target_def]``ag32_target.get_byte``]
  \\ fs[SIMP_CONV(srw_ss())[ag32_targetTheory.ag32_target_def]``ag32_target.state_ok``]
  \\ fs[SIMP_CONV(srw_ss())[ag32_targetTheory.ag32_target_def]``ag32_target.get_pc``]
  \\ fs[SIMP_CONV(srw_ss())[ag32_targetTheory.ag32_config_def]``ag32_config.encode``]
  \\ fs[SIMP_CONV(srw_ss())[ag32_targetTheory.ag32_config_def]``ag32_config.code_alignment``]
  \\ `bytes_in_memory ms.PC (ag32_enc i) ms.MEM x.mem_domain`
  by (
    fs[asmPropsTheory.target_state_rel_def]
    \\ irule asmPropsTheory.bytes_in_memory_change_mem
    \\ goal_assum(first_assum o mp_then Any mp_tac)
    \\ fs[SIMP_CONV(srw_ss())[ag32_targetTheory.ag32_target_def]``ag32_target.get_byte``]
    \\ rw[]
    \\ first_x_assum(irule o GSYM)
    \\ imp_res_tac asmPropsTheory.bytes_in_memory_all_pcs
    \\ fs[asmPropsTheory.all_pcs_thm, SUBSET_DEF, PULL_EXISTS]
    \\ first_x_assum(qspec_then`0`mp_tac)
    \\ simp[] )
  \\ `ag32_ok (FUNPOW Next n ms)` by fs[asmPropsTheory.target_state_rel_def, ag32_targetTheory.ag32_target_def]
  \\ qpat_x_assum`∀j x. _`kall_tac
  \\ ntac 3 (pop_assum mp_tac)
  \\ rpt (pop_assum kall_tac)
  \\ qid_spec_tac`ms`
  \\ Induct_on`n` \\ simp[]
  \\ rw[FUNPOW_SUC]
  \\ qho_match_abbrev_tac`f (Next (FUNPOW Next n ms)) = f ms`
  \\ match_mp_tac EQ_TRANS
  \\ qexists_tac`f (FUNPOW Next n ms)`
  \\ (reverse conj_tac >- ( fsrw_tac[DNF_ss][Abbr`f`] \\ first_x_assum irule \\ simp[] ) )
  \\ qunabbrev_tac`f`
  \\ irule ag32_io_events_unchanged
  \\ qmatch_goalsub_abbrev_tac`st.MEM`
  \\ `bytes_in_memory ms.PC (ag32_enc i) st.MEM x.mem_domain`
  by (
    irule asmPropsTheory.bytes_in_memory_change_mem
    \\ goal_assum(first_assum o mp_then Any mp_tac)
    \\ fsrw_tac[DNF_ss][asmPropsTheory.all_pcs_thm, PULL_EXISTS,Abbr`st`])
  \\ simp[]
  \\ qmatch_goalsub_abbrev_tac`m (pc + _)`
  \\ `ag32_ok st` by fs[Abbr`st`]
  \\ `aligned 2 st.PC` by rfs[ag32_targetTheory.ag32_target_def, ag32_targetTheory.ag32_ok_def]
  \\ `pc = st.PC`
  by (
    simp[Abbr`pc`]
    \\ pop_assum mp_tac
    \\ simp[alignmentTheory.aligned_extract]
    \\ blastLib.BBLAST_TAC )
  \\ qpat_x_assum`Abbrev(pc = _)`kall_tac
  \\ pop_assum SUBST_ALL_TAC
  \\ first_x_assum(qspec_then`n`mp_tac) \\ rw[]
  \\ fs[asmPropsTheory.all_pcs_thm]
  \\ qmatch_asmsub_rename_tac`4 * k < _`
  \\ Q.ISPECL_THEN[`TAKE (4 * k) (ag32_enc i)`, `DROP (4 * k) (ag32_enc i)`,`ms.PC`]mp_tac asmPropsTheory.bytes_in_memory_APPEND
  \\ simp[]
  \\ disch_then(drule o #1 o EQ_IMP_RULE o SPEC_ALL)
  \\ strip_tac
  \\ qmatch_goalsub_abbrev_tac`pc + _`
  \\ qmatch_asmsub_abbrev_tac`bytes_in_memory pc bs`
  \\ `∀j. j < 4 ⇒ (m (pc + n2w j) = EL j bs)`
  by (
    rw[]
    \\ Q.ISPECL_THEN[`TAKE j bs`,`DROP j bs`,`st.PC`]mp_tac asmPropsTheory.bytes_in_memory_APPEND
    \\ simp[]
    \\ disch_then(drule o #1 o EQ_IMP_RULE o SPEC_ALL)
    \\ simp[]
    \\ `j < LENGTH bs` by (
      fs[Abbr`bs`]
      \\ qspec_then`i`mp_tac(Q.GEN`istr`ag32_enc_lengths)
      \\ Cases_on`k` \\ fs[]
      \\ Cases_on`n'` \\ fs[]
      \\ Cases_on`n''` \\ fs[]
      \\ Cases_on`n'` \\ fs[] )
    \\ Cases_on`DROP j bs` \\ fs[DROP_NIL]
    \\ simp[asmSemTheory.bytes_in_memory_def]
    \\ rw[]
    \\ imp_res_tac DROP_EL_CONS
    \\ rfs[] )
  \\ simp[]
  \\ drule ag32_enc_not_Interrupt
  \\ simp[]
  \\ first_x_assum(qspec_then`0`mp_tac)
  \\ simp[]);

val ag32_init_asm_state_def = Define`
  ag32_init_asm_state mem md (r0:word32) = <|
    be := F;
    lr := 0 ;
    failed := F ;
    align := 2 ;
    pc := r0;
    mem := mem;
    mem_domain := md ;
    regs := ag32_init_regs r0
  |>`;

val is_ag32_init_state_def = ag32_targetTheory.is_ag32_init_state_def;

val target_state_rel_ag32_init = Q.store_thm("target_state_rel_ag32_init",
  `byte_aligned r0 ∧ is_ag32_init_state m r0 ms ⇒
   target_state_rel ag32_target
    (ag32_init_asm_state m md r0) ms`,
  rw[asmPropsTheory.target_state_rel_def]
  >- (
    rw[ag32_targetTheory.ag32_target_def, ag32_targetTheory.ag32_ok_def]
    \\ fs[is_ag32_init_state_def]
    \\ fs[alignmentTheory.byte_aligned_def])
  >- ( fs[is_ag32_init_state_def,ag32_init_asm_state_def] \\ EVAL_TAC \\ fs[] )
  >- ( fs[is_ag32_init_state_def,ag32_init_asm_state_def] \\ EVAL_TAC \\ fs[] )
  >- (
    fs[is_ag32_init_state_def,ag32_init_asm_state_def]
    \\ ntac 2 (pop_assum mp_tac)
    \\ EVAL_TAC \\ rw[]
    \\ EVAL_TAC \\ rw[])
  >- ( pop_assum mp_tac \\ EVAL_TAC ));

val memory_size_def = Define`
  memory_size = 128n * 10 ** 6`;

val cline_size_def = Define`
  cline_size = 2 * 1024n`;

val stdin_size_def = Define`
  stdin_size = 5 * 1024 * 1024n`;

val output_buffer_size_def = Define`
  output_buffer_size = 2048n`;

val heap_size_def = Define`
  heap_size = 100 * 1024 * 1024n`;

val startup_code_size_def = Define`
  startup_code_size = 288n`;

(* Memory Layout:

  +-------------------+
  | * CakeML data     |
  +-------------------+  about 23MB left for these
  | * CakeML code     |
  +-------------------+
  | * FFI call jumps  |  <= 176 ((9 + 2) * 16) bytes
  +-------------------+
  | CakeML stack/heap |  heap_size bytes (~100Mb)
  +-------------------+  <- mem_start + heap_start_offset
  | --- (padding) --- |  (will arrange for this to be 0)
  +-------------------+
  | FFI code          |  (4 * LENGTH ag32_ffi_code) bytes (~640b)
  +-------------------+
  | FFI call id       |  4 bytes (as a word)
  +-------------------+
  | output buffer     |  output_buffer_size bytes (~2Kb)
  +-------------------+
  | output length     |  4 bytes
  +-------------------+
  | output id         |  8 bytes (* ridiculously overpowered... *)
  +-------------------+
  | + stdin           |  stdin_size bytes (~5Mb)
  +-------------------+
  | + stdin length    |  4 bytes
  +-------------------+
  | stdin pointer     |  4 bytes
  +-------------------+
  | + cline args      |  cline_size bytes (~1024b)
  +-------------------+
  | + cline arg count |  4 bytes (as a word)
  +-------------------+  <- mem_start + startup_code_size
  | ---- padding ---- |
  +-------------------+
  | * startup code    |  (LENGTH startup_code) bytes (~72b, ≤216b (18*12))
  +-------------------+  <- mem_start

  The starred items depend on the output of the compiler;
  the other items are boilerplate for every application.
  The plussed items are set by the host before execution.
*)

val FFI_codes_def = Define`
  FFI_codes =
    [("exit", 0n)
    ;("get_arg_count", 1n)
    ;("get_arg_length", 2n)
    ;("get_arg", 3n)
    ;("read", 4n)
    ;("write", 5n)
    ;("open_in", 6n)
    ;("open_out", 7n)
    ;("close", 8n)]`;

val FFI_codes_covers_basis_ffi = Q.store_thm("FFI_codes_covers_basis_ffi",
  `∀name st conf bytes. basis_ffi_oracle name st conf bytes ≠ Oracle_final FFI_failed ⇒ name ∈ set (MAP FST FFI_codes)`,
  rw[basis_ffiTheory.basis_ffi_oracle_def]
  \\ pairarg_tac \\ fs[] \\ rveq
  \\ simp[FFI_codes_def]
  \\ pop_assum mp_tac
  \\ rpt(IF_CASES_TAC \\ fs[]));

val output_offset_def = Define`
  output_offset = startup_code_size + 4 + cline_size + 4 + 4 + stdin_size`;

val ffi_code_start_offset_def = Define`
  ffi_code_start_offset =
    output_offset + 8 + 4 + output_buffer_size + 4`;

val get_output_io_event_def = Define`
  get_output_io_event (IO_event name conf bs2) =
    if name = "write" then
      case MAP FST bs2 of (n1 :: n0 :: off1 :: off0 :: tll) =>
        let k = MIN (w22n [n1; n0]) output_buffer_size in
        if (SND (HD bs2) = 0w) then
          let written = TAKE k (DROP (w22n [off1; off0]) tll) in
            SOME (conf ++ [0w;0w;n1;n0] ++ written)
        else NONE
      | _ => NONE
    else NONE`;

val get_ag32_io_event_def = Define`
  get_ag32_io_event r0 m =
    let call_id = m (r0 + n2w (ffi_code_start_offset - 4)) in
    if call_id = n2w (THE (ALOOKUP FFI_codes "write")) then
      let n1 = m (r0 + n2w (output_offset + 10)) in
      let n0 = m (r0 + n2w (output_offset + 11)) in
      let n = w22n [n1; n0] in
        read_bytearray (r0 + n2w output_offset) (8 + 4 + n) (SOME o m)
    else NONE`;

val stdin_fs_def = Define`
  stdin_fs inp =
    <| files :=
       [(IOStream (strlit "stdout"), "")
       ;(IOStream (strlit "stderr"), "")
       ;(IOStream (strlit "stdin"), inp)]
     ; infds :=
       [(0, IOStream(strlit"stdin"), 0)
       ;(1, IOStream(strlit"stdout"), 0)
       ;(2, IOStream(strlit"stderr"), 0)]
     ; numchars := LGENLIST (K output_buffer_size) NONE
     |>`;

val wfFS_stdin_fs = Q.store_thm("wfFS_stdin_fs",
  `2 ≤ maxFD ⇒ wfFS (stdin_fs inp)`,
  rw[stdin_fs_def, fsFFIPropsTheory.wfFS_def] \\ rw[]
  \\ rw[fsFFIPropsTheory.liveFS_def]
  \\ rw[fsFFIPropsTheory.live_numchars_def]
  \\ qmatch_goalsub_abbrev_tac`always P ll`
  \\ `∀x. (x = ll) ⇒ always P x` suffices_by rw[]
  \\ ho_match_mp_tac always_coind
  \\ rw[]
  \\ qexists_tac`output_buffer_size`
  \\ conj_tac
  >- ( simp[Abbr`ll`] \\ simp[LGENLIST_EQ_CONS] )
  \\ simp[Abbr`P`]
  \\ EVAL_TAC);

val STD_streams_stdin_fs = Q.store_thm("STD_streams_stdin_fs",
  `STD_streams (stdin_fs inp)`,
  rw[fsFFIPropsTheory.STD_streams_def]
  \\ qexists_tac`0`
  \\ rw[stdin_fs_def]
  \\ rw[]);

val ag32_ffi_rel_def = Define`
  ag32_ffi_rel r0 ms io_events ⇔
    (MAP (get_ag32_io_event r0) ms.io_events =
     MAP get_output_io_event io_events)`;

val extract_write_def = Define`
  extract_write fd oevent =
    let conf = TAKE 8 oevent in
    if w82n conf = fd then
      SOME (DROP (8 + 4) oevent)
    else NONE`;

val extract_writes_def = Define`
  extract_writes fd oevents =
    FLAT (MAP (MAP (CHR o w2n) o THE) (FILTER IS_SOME (MAP (combin$C OPTION_BIND (extract_write fd)) oevents)))`;

(* TODO: why is this proof so slow? make it faster? *)
val extract_fs_extract_writes = Q.store_thm("extract_fs_extract_writes",
  `∀ls fs fs' off off' out rest.
   (extract_fs fs ls = SOME fs') ∧
   (* can only read/write up to output_buffer_size - this could be made more nuanced *)
   (fs.numchars = LGENLIST (K output_buffer_size) NONE) ∧
   (* IOStream of interest exists at the start *)
   (ALOOKUP fs.infds fd = SOME (IOStream nam, LENGTH out)) ∧
   (ALOOKUP fs.files (IOStream nam) = SOME out) ∧
   (* no non-IOStream files *)
   (∀nm. ¬inFS_fname fs (File nm)) ∧
   (* well-formedness invariants for the filesystem *)
   (∀fd fnm off. (ALOOKUP fs'.infds fd = SOME (fnm, off)) ⇒ inFS_fname fs' fnm) ∧
   (∀fd1 nm off1 fd2 off2. (* this one depends on us not being able to open IOStreams *)
     (ALOOKUP fs'.infds fd1 = SOME (IOStream nm, off1)) ∧
     (ALOOKUP fs'.infds fd2 = SOME (IOStream nm, off2))
     ⇒ (fd1 = fd2)) ∧
   (*
   (∀fd fnm off cont.
     (ALOOKUP fs'.infds fd = SOME (fnm, off)) ∧
     (ALOOKUP fs'.files fnm = SOME cont) ⇒ off ≤ LENGTH cont) ∧
   *)
   (* -- *)
   (* nothing has changed except the IOStream of interest -- is this actually necessary? *)
   (∀x. x ≠ fd ⇒ (ALOOKUP fs'.infds x = ALOOKUP fs.infds x)) ∧
   (∀fnm. fnm ≠ IOStream nam ⇒ (ALOOKUP fs'.files fnm = ALOOKUP fs.files fnm)) ∧
   (* and it has only changed by appending *)
   (ALOOKUP fs'.infds fd = SOME (IOStream nam, LENGTH out + LENGTH rest)) ∧
   (ALOOKUP fs'.files (IOStream nam) = SOME (out ++ rest))
   ⇒
   (extract_writes fd (MAP get_output_io_event ls) = rest)`,
  Induct
  >- (
    rw[basis_ffiTheory.extract_fs_def, extract_writes_def]
    \\ fs[basis_ffiTheory.extract_fs_with_numchars_def]
    \\ rveq \\ fs[] )
  \\ Cases
  \\ rpt gen_tac
  \\ fs[basis_ffiTheory.extract_fs_def, PULL_EXISTS]
  \\ rw[]
  \\ fs[basis_ffiTheory.extract_fs_with_numchars_def]
  \\ fs[get_output_io_event_def]
  \\ reverse(rw[])
  >- (
    fs[extract_writes_def]
    \\ first_x_assum irule
    \\ fs[CaseEq"option"]
    >- ( qexists_tac`fs` \\ fs[] \\ metis_tac[])
    \\ fs[CaseEq"ffi_result"]
    \\ qexists_tac`fs'` \\ fs[]
    \\ fs[fsFFITheory.fs_ffi_part_def]
    \\ rveq
    \\ fs[CaseEq"bool"] \\ rveq
    >- (
      fs[fsFFITheory.ffi_open_in_def, OPTION_CHOICE_EQUALS_OPTION] \\ rveq \\ fs[] \\ rfs[]
      \\ TRY (rpt conj_tac \\ first_x_assum MATCH_ACCEPT_TAC)
      \\ pairarg_tac \\ fs[] \\ rveq \\ fs[]
      \\ fs[fsFFITheory.openFile_def]
      \\ fs[fsFFIPropsTheory.inFS_fname_def]
      \\ imp_res_tac ALOOKUP_MEM
      \\ fs[MEM_MAP, PULL_EXISTS, EXISTS_PROD]
      \\ metis_tac[] )
    >- (
      fs[fsFFITheory.ffi_open_out_def, OPTION_CHOICE_EQUALS_OPTION] \\ rveq \\ fs[] \\ rfs[]
      \\ TRY (rpt conj_tac \\ first_x_assum MATCH_ACCEPT_TAC)
      \\ pairarg_tac \\ fs[] \\ rveq \\ fs[]
      \\ fs[fsFFITheory.openFile_truncate_def]
      \\ fs[fsFFIPropsTheory.inFS_fname_def]
      \\ imp_res_tac ALOOKUP_MEM
      \\ fs[MEM_MAP, PULL_EXISTS, EXISTS_PROD]
      \\ metis_tac[] )
    >- (
      fs[fsFFITheory.ffi_read_def, OPTION_CHOICE_EQUALS_OPTION] \\ rveq \\ fs[] \\ rfs[]
      \\ fs[CaseEq"list"]
      \\ fs[OPTION_CHOICE_EQUALS_OPTION] \\ rveq \\ fs[]
      \\ TRY (rpt conj_tac \\ first_x_assum MATCH_ACCEPT_TAC)
      \\ pairarg_tac \\ fs[] \\ rveq \\ fs[]
      \\ fs[fsFFITheory.read_def]
      \\ pairarg_tac \\ fs[] \\ rveq \\ fs[]
      \\ fs[fsFFITheory.bumpFD_def]
      \\ fs[fsFFIPropsTheory.inFS_fname_def]
      \\ fs[fsFFIPropsTheory.forwardFD_def, ALIST_FUPDKEY_ALOOKUP]
      \\ rw[]
      \\ TRY PURE_CASE_TAC \\ fs[]
      \\ TRY PURE_CASE_TAC \\ fs[CaseEq"option"]
      \\ rveq \\ fs[] \\ rfs[]
      >- metis_tac[]
      (*
      >- metis_tac[]
      >- metis_tac[]
      >- metis_tac[]
      *)
      \\ imp_res_tac ALOOKUP_MEM
      \\ reverse(Cases_on`fnm`)
      >- ( fs[MEM_MAP, PULL_EXISTS, EXISTS_PROD] \\ metis_tac[] )
      \\ drule (GEN_ALL extract_fs_with_numchars_keeps_iostreams)
      \\ simp[ALIST_FUPDKEY_ALOOKUP]
      \\ first_x_assum drule
      \\ simp[]
      \\ strip_tac
      \\ disch_then drule
      \\ simp[] )
    >- (
      reverse(fs[fsFFITheory.ffi_close_def, OPTION_CHOICE_EQUALS_OPTION] \\ rveq \\ fs[])
      >- metis_tac[]
      >- metis_tac[]
      \\ pairarg_tac \\ fs[] \\ rveq
      \\ fs[fsFFITheory.closeFD_def]
      \\ rveq \\ fs[]
      \\ fs[ALOOKUP_ADELKEY]
      \\ fs[fsFFIPropsTheory.inFS_fname_def]
      \\ drule (GEN_ALL extract_fs_with_numchars_closes_iostreams)
      \\ simp[ALOOKUP_ADELKEY]
      \\ Cases_on`w82n l = fd` \\ fs[]
      >- (
        rw[]
        \\ qexists_tac`w82n l` \\ simp[]
        \\ CCONTR_TAC \\ fs[]
        \\ metis_tac[] )
      \\ `ALOOKUP z.infds (w82n l) = SOME x` by metis_tac[]
      \\ rw[] \\ rw[] \\ rw[]
      >- metis_tac[]
      (*
      >- metis_tac[]
      *)
      \\ first_x_assum(qspec_then`w82n l`mp_tac) \\ rw[]
      \\ Cases_on`x` \\ fs[]
      \\ Cases_on`q = IOStream nam`
      >- (
        fs[] \\ CCONTR_TAC \\ fs[]
        \\ Cases_on`fd = fd'` \\ fs[] \\ rw[]
        \\ metis_tac[] )
      \\ `MEM q (MAP FST z.files)` by metis_tac[]
      \\ `IS_SOME (ALOOKUP z.files q)`
      by simp[data_to_word_gcProofTheory.IS_SOME_ALOOKUP_EQ]
      \\ fs[IS_SOME_EXISTS]
      \\ `ALOOKUP fs.files q = SOME x` by metis_tac[]
      \\ imp_res_tac ALOOKUP_MEM
      \\ fs[MEM_MAP, PULL_EXISTS, EXISTS_PROD]
      \\ reverse(Cases_on`q`) \\ fs[]
      >- metis_tac[]
      \\ CCONTR_TAC \\ fs[]
      \\ `fd = fd'` by metis_tac[]
      \\ rveq \\ fs[] )
    )
  \\ fs[fsFFITheory.fs_ffi_part_def]
  \\ fs[CaseEq"option",CaseEq"ffi_result"]
  \\ last_x_assum drule
  \\ fs[fsFFITheory.ffi_write_def]
  \\ fs[CaseEq"list"] \\ rveq
  \\ strip_tac
  \\ reverse IF_CASES_TAC
  >- (
    Cases_on`l0` \\ fs[LUPDATE_def]
    \\ fs[OPTION_CHOICE_EQUALS_OPTION]
    \\ TRY pairarg_tac \\ fs[]
    \\ fs[extract_writes_def]
    \\ first_x_assum irule
    \\ rveq
    \\ fs[] \\ rfs[]
    \\ metis_tac[])
  \\ Cases_on`l0` \\ fs[LUPDATE_def]
  \\ fs[OPTION_CHOICE_EQUALS_OPTION]
  \\ TRY pairarg_tac \\ fs[]
  \\ PairCases_on`h`
  \\ fs[] \\ rveq
  \\ fs[fsFFITheory.write_def]
  \\ pairarg_tac \\ fs[]
  \\ rfs[fsFFITheory.fsupdate_def]
  \\ rveq \\ fs[ALIST_FUPDKEY_ALOOKUP, LDROP1_THM]
  \\ rfs[]
  \\ qmatch_asmsub_abbrev_tac`extract_fs_with_numchars fs'`
  \\ qmatch_asmsub_abbrev_tac`ALIST_FUPDKEY fnm (K new_content)`
  \\ fs[extract_writes_def, extract_write_def]
  \\ simp[TAKE_APPEND]
  \\ simp[DROP_APPEND, DROP_LENGTH_TOO_LONG]
  \\ simp[TAKE_LENGTH_TOO_LONG]
  \\ reverse(Cases_on`w82n l = fd`) \\ fs[]
  >- (
    first_x_assum irule
    \\ simp[]
    \\ IF_CASES_TAC
    >- ( rveq \\ fs[] \\ metis_tac[] )
    \\ `inFS_fname fs fnm`
    by (
      simp[fsFFIPropsTheory.inFS_fname_def]
      \\ imp_res_tac ALOOKUP_MEM
      \\ simp[MEM_MAP, EXISTS_PROD]
      \\ asm_exists_tac \\ rw[] )
    \\ Cases_on`fnm` \\ rfs[]
    \\ first_assum(qspec_then`w82n l`mp_tac)
    \\ impl_tac >- fs[]
    \\ qpat_x_assum`ALOOKUP fs.infds (w82n l) = _`mp_tac
    \\ simp_tac(srw_ss())[]
    \\ ntac 2 strip_tac
    \\ last_assum drule
    \\ simp_tac(srw_ss())[fsFFIPropsTheory.inFS_fname_def]
    \\ strip_tac
    \\ drule (GEN_ALL extract_fs_with_numchars_keeps_iostreams)
    \\ disch_then drule
    \\ simp[Abbr`fs'`, ALIST_FUPDKEY_ALOOKUP]
    \\ qmatch_goalsub_abbrev_tac`_ + zz ≤ _`
    \\ strip_tac
    \\ reverse(Cases_on`zz = 0`) >- fs[]
    \\ qunabbrev_tac`zz`
    \\ pop_assum mp_tac
    \\ simp[]
    \\ once_rewrite_tac[output_buffer_size_def]
    \\ simp[]
    \\ strip_tac \\ fs[]
    \\ qunabbrev_tac`new_content`
    \\ fs[fsFFIPropsTheory.inFS_fname_def]
    \\ conj_tac
    >- (
      rw[]
      \\ PURE_CASE_TAC \\ fs[]
      \\ PURE_CASE_TAC \\ fs[] )
    \\ conj_tac >- metis_tac[]
    (*
    \\ conj_tac >- metis_tac[]
    *)
    \\ rw[]
    \\ PURE_CASE_TAC \\ fs[]
    \\ PURE_CASE_TAC \\ fs[])
  \\ fs[MAP_TAKE]
  \\ qmatch_goalsub_abbrev_tac`written ++ _`
  \\ rveq \\ fs[]
  \\ rveq \\ fs[]
  \\ drule (GEN_ALL extract_fs_with_numchars_keeps_iostreams)
  \\ disch_then drule
  \\ simp[Abbr`fs'`, ALIST_FUPDKEY_ALOOKUP]
  \\ simp[data_to_word_assignProofTheory.IMP]
  \\ strip_tac
  \\ qmatch_asmsub_abbrev_tac`off + nw`
  \\ fs[Abbr`new_content`]
  \\ `LENGTH written = nw`
  by (
    simp[Abbr`written`, LENGTH_TAKE_EQ]
    \\ rw[] \\ fs[Abbr`nw`] )
  \\ fs[Abbr`off`, DROP_LENGTH_TOO_LONG]
  \\ qmatch_asmsub_abbrev_tac`¬inFS_fname fs' (File _)`
  \\ `nw ≤ LENGTH rest` by fs[Abbr`nw`]
  \\ rfs[] \\ fs[]
  \\ qpat_x_assum`_ ⇒ _`mp_tac
  \\ impl_tac
  >- (
    rw[]
    \\ fs[CaseEq"option"]
    \\ CCONTR_TAC \\ fs[]
    \\ rveq
    \\ metis_tac[] )
  \\ strip_tac
  \\ rveq \\ fs[]
  \\ first_x_assum irule
  \\ fs[fsFFIPropsTheory.inFS_fname_def]
  \\ simp[Abbr`fs'`]
  \\ conj_tac
  >- ( rw[] \\ PURE_CASE_TAC \\ fs[] )
  \\ conj_tac >- metis_tac[]
  \\ rw[] \\ PURE_CASE_TAC \\ fs[] );

val length_ag32_ffi_code = Define`
  length_ag32_ffi_code = 668n`;

val heap_start_offset_def = Define`
  heap_start_offset =
    ffi_code_start_offset + length_ag32_ffi_code`;

val ffi_jumps_offset_def = Define`
  ffi_jumps_offset =
    heap_start_offset + heap_size`;

val ag32_ffi_return_code_def = Define`
  ag32_ffi_return_code = [
   Normal (fAdd, 1w, Imm 0w, Imm 0w);
   Normal (fSnd, 2w, Imm 0w, Imm 0w);
   Normal (fSnd, 3w, Imm 0w, Imm 0w);
   Normal (fSnd, 4w, Imm 0w, Imm 0w);
   Normal (fSnd, 5w, Imm 0w, Imm 0w);
   Normal (fSnd, 6w, Imm 0w, Imm 0w);
   Normal (fSnd, 7w, Imm 0w, Imm 0w);
   Normal (fSnd, 8w, Imm 0w, Imm 0w);
   Interrupt;
   Jump (fSnd, 0w, Reg 0w)]`;

val ag32_ffi_return_def = Define`
  ag32_ffi_return s =
  let s = dfn'Normal (fAdd, 1w, Imm 0w, Imm 0w) s in
  let s = dfn'Normal (fSnd, 2w, Imm 0w, Imm 0w) s in
  let s = dfn'Normal (fSnd, 3w, Imm 0w, Imm 0w) s in
  let s = dfn'Normal (fSnd, 4w, Imm 0w, Imm 0w) s in
  let s = dfn'Normal (fSnd, 5w, Imm 0w, Imm 0w) s in
  let s = dfn'Normal (fSnd, 6w, Imm 0w, Imm 0w) s in
  let s = dfn'Normal (fSnd, 7w, Imm 0w, Imm 0w) s in
  let s = dfn'Normal (fSnd, 8w, Imm 0w, Imm 0w) s in
  let s = dfn'Interrupt s in
  let s = dfn'Jump (fSnd, 0w, Reg 0w) s in
  s`;

val ag32_ffi_return_thm = Q.store_thm("ag32_ffi_return_thm",
  `(ag32_ffi_return s =
    s with <| PC := s.R 0w;
              R := ((0w =+ s.PC + n2w (4 * LENGTH ag32_ffi_return_code))
                   ((1w =+ 0w)
                   ((2w =+ 0w)
                   ((3w =+ 0w)
                   ((4w =+ 0w)
                   ((5w =+ 0w)
                   ((6w =+ 0w)
                   ((7w =+ 0w)
                   ((8w =+ 0w) s.R)))))))));
              io_events := SNOC s.MEM s.io_events;
              OverflowFlag := F;
              CarryFlag := F |>)`,
  rw[ag32_ffi_return_def]
  \\ rw[ag32Theory.dfn'Normal_def, ag32Theory.incPC_def, ag32Theory.ri2word_def,
        ag32Theory.norm_def, ag32Theory.ALU_def,
        ag32Theory.dfn'Interrupt_def, ag32Theory.dfn'Jump_def]
  \\ rw[ag32Theory.ag32_state_component_equality, APPLY_UPDATE_THM, FUN_EQ_THM]
  >- EVAL_TAC
  \\ rw[] \\ fs[]
  \\ EVAL_TAC);

fun next_tac n =
  let
    val sn = mk_var("s"^(Int.toString n), ``:ag32_state``)
  in
    rw[Once EXISTS_NUM] \\ disj2_tac \\ rw[FUNPOW]
    \\ qmatch_goalsub_abbrev_tac`Next ^sn`
    \\ rw[ag32Theory.Next_def]
    \\ qmatch_goalsub_abbrev_tac`pc + 2w`
    \\ simp[GSYM get_mem_word_def]
    \\ `^sn.PC = s.PC + n2w(4 * ^(numSyntax.term_of_int n))`
    by ( simp[Abbr`^sn`, dfn'Normal_PC] )
    \\ `byte_aligned ^sn.PC`
    by (
      simp[]
      \\ irule byte_aligned_add \\ simp[]
      \\ EVAL_TAC )
    \\ drule byte_aligned_imp
    \\ simp[]
    \\ disch_then kall_tac
    \\ qpat_x_assum`Abbrev(pc = _)`kall_tac
    \\ first_assum(qspec_then`^(numSyntax.term_of_int n)`mp_tac)
    \\ impl_tac >- EVAL_TAC
    \\ simp_tac(srw_ss())[ag32_ffi_return_code_def]
    \\ `^sn.MEM = s.MEM` by simp[Abbr`^sn`,dfn'Normal_MEM]
    \\ simp[]
    \\ disch_then kall_tac
    \\ simp[ag32_targetProofTheory.Decode_Encode]
    \\ simp[ag32Theory.Run_def]
  end

val ag32_ffi_return_code_thm = Q.store_thm("ag32_ffi_return_code_thm",
  `(∀k. k < LENGTH ag32_ffi_return_code ⇒
        (get_mem_word s.MEM (s.PC + n2w (4 * k)) =
         Encode (EL k ag32_ffi_return_code))) ∧ byte_aligned s.PC
   ⇒
   ∃k. (FUNPOW Next k s = ag32_ffi_return s)`,
  rw[ag32_ffi_return_def]
  \\ rw[Once EXISTS_NUM] \\ disj2_tac \\ rw[FUNPOW]
  \\ rw[ag32Theory.Next_def]
  \\ qmatch_goalsub_abbrev_tac`pc + 2w`
  \\ simp[GSYM get_mem_word_def]
  \\ first_assum(qspec_then`0`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ simp_tac(srw_ss())[]
  \\ imp_res_tac byte_aligned_imp \\ rfs[]
  \\ ntac 2 (pop_assum kall_tac)
  \\ disch_then kall_tac
  \\ simp[ag32_targetProofTheory.Decode_Encode]
  \\ simp[ag32_ffi_return_code_def, ag32Theory.Run_def]
  \\ EVERY (List.tabulate(8, next_tac o (curry(op +)1)))
  \\ rw[Once EXISTS_NUM] \\ disj2_tac \\ rw[FUNPOW]
  \\ qmatch_goalsub_abbrev_tac`Next s9`
  \\ rw[ag32Theory.Next_def]
  \\ qmatch_goalsub_abbrev_tac`pc + 2w`
  \\ simp[GSYM get_mem_word_def]
  \\ `s9.PC = s.PC + n2w(4 * 9)`
  by ( simp[Abbr`s9`, ag32Theory.dfn'Interrupt_def, ag32Theory.incPC_def] )
  \\ `byte_aligned s9.PC`
  by (
    simp[]
    \\ irule byte_aligned_add \\ simp[]
    \\ EVAL_TAC )
  \\ drule byte_aligned_imp
  \\ simp[]
  \\ disch_then kall_tac
  \\ qpat_x_assum`Abbrev(pc = _)`kall_tac
  \\ first_assum(qspec_then`9`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ simp_tac(srw_ss())[ag32_ffi_return_code_def]
  \\ `s9.MEM = s.MEM` by simp[Abbr`s9`,ag32Theory.dfn'Interrupt_def,ag32Theory.incPC_def]
  \\ simp[]
  \\ disch_then kall_tac
  \\ simp[ag32_targetProofTheory.Decode_Encode]
  \\ simp[ag32Theory.Run_def]
  \\ simp[Once EXISTS_NUM]);

(* exit
   PC is mem_start + ffi_code_start_offset  *)

val ag32_ffi_exit_entrypoint_def = Define`
  ag32_ffi_exit_entrypoint = 0n`;

val ag32_ffi_exit_def = Define`
  ag32_ffi_exit s =
    let s = dfn'Jump(fAdd, 5w, Imm 4w) s in
    let s = incPC () (s with R := (6w =+ w2w(((22 >< 0)(n2w (ffi_code_start_offset+4) :word32)):23 word)) s.R) in
    let s = incPC () (s with R := (6w =+ bit_field_insert 31 23 (((31 >< 23)(n2w (ffi_code_start_offset+4) :word32)):9 word) (s.R 6w)) s.R) in
    let s = incPC () (s with R := (5w =+ (s.R 5w) - (s.R 6w)) s.R) in
    let s = incPC () (s with MEM := ((s.R 5w) =+ 0w) s.MEM) in
    let s = incPC () (s with R := (5w =+ 0w) s.R) in
    let s = incPC () (s with R := (6w =+ 0w) s.R) in
    let s = incPC () (s with R := (7w =+ 0w) s.R) in
    let s = incPC () (s with <| R := (8w =+ 0w) s.R; OverflowFlag := F; CarryFlag := F|>) in
    let s = incPC () (s with io_events := s.io_events ++ [s.MEM]) in
    s`;

val ag32_ffi_exit_code_def = Define`
  ag32_ffi_exit_code =
    [Jump (fAdd, 5w, Imm 4w);
     LoadConstant(6w, F, (22 >< 0)((n2w (ffi_code_start_offset+4)):word32));
     LoadUpperConstant(6w, (31 >< 23)((n2w (ffi_code_start_offset+4)):word32));
     Normal (fSub, 5w, Reg 5w, Reg 6w);
     StoreMEMByte (Imm 0w, Reg 5w);
     Normal(fSnd, 5w, Imm 0w, Imm 0w);
     Normal(fSnd, 6w, Imm 0w, Imm 0w);
     Normal(fSnd, 7w, Imm 0w, Imm 0w);
     Normal(fAdd, 8w, Imm 0w, Imm 0w);
     Interrupt]`;

(* get_arg_count
   PC is mem_start + ffi_code_start_offset
         + 4 * LENGTH ag32_ffi_exit_code
   pointer is in r3 *)

val ag32_ffi_get_arg_count_entrypoint_def = Define`
  ag32_ffi_get_arg_count_entrypoint =
  ag32_ffi_exit_entrypoint + 4 * LENGTH ag32_ffi_exit_code`;

val ag32_ffi_get_arg_count_def = Define`
  ag32_ffi_get_arg_count s =
    let pc_offset = (ffi_code_start_offset - startup_code_size) + ag32_ffi_get_arg_count_entrypoint + 4 in
    let s = dfn'Jump(fAdd, 5w, Imm 4w) s in
    let s = incPC () (s with R := (6w =+ w2w(((22 >< 0)(n2w pc_offset :word32)):23 word)) s.R) in
    let s = incPC () (s with R := (6w =+ bit_field_insert 31 23 (((31 >< 23)(n2w pc_offset :word32)):9 word) (s.R 6w)) s.R) in
    let s = incPC () (s with R := (5w =+ (s.R 5w) - (s.R 6w)) s.R) in
    let s = dfn'LoadMEM (6w, Reg 5w) s in
    let s = incPC () (s with MEM := ((s.R 4w) =+ (7 >< 0) (s.R 6w)) s.MEM) in
    let s = incPC () (s with R := (6w =+ (s.R 6w) >>>~ 4w) s.R) in
    let s = dfn'Normal(fAdd, 4w, Reg 4w, Imm 4w) s in
    let s = incPC () (s with MEM := ((s.R 4w) =+ (7 >< 0) (s.R 6w)) s.MEM) in
    let s = incPC () (s with R := (6w =+ (n2w startup_code_size)) s.R) in
    let s = incPC () (s with R := (5w =+ (s.R 5w) - (s.R 6w)) s.R) in
    let s = incPC () (s with MEM := ((s.R 5w) =+ 1w) s.MEM) in
    let s = dfn'Normal(fSub, 4w, Reg 4w, Imm 4w) s in
    let s = incPC () (s with R := (5w =+ 0w) s.R) in
    let s = incPC () (s with R := (6w =+ 0w) s.R) in
    let s = incPC () (s with R := (7w =+ 0w) s.R) in
    let s = incPC () (s with <| R := (8w =+ 0w) s.R; OverflowFlag := F; CarryFlag := F|>) in
    let s = incPC () (s with io_events := s.io_events ++ [s.MEM]) in
    let s = s with <| R := (0w =+ s.PC + 4w) s.R; PC := s.R 0w |> in
    s`;

val ag32_ffi_get_arg_count_code_def = Define`
  ag32_ffi_get_arg_count_code =
    let pc_offset = (ffi_code_start_offset - startup_code_size) + ag32_ffi_get_arg_count_entrypoint + 4 in
    [Jump (fAdd, 5w, Imm 4w);
     LoadConstant(6w, F, (22 >< 0)((n2w pc_offset):word32));
     LoadUpperConstant(6w, (31 >< 23)((n2w pc_offset):word32));
     Normal (fSub, 5w, Reg 5w, Reg 6w);
     LoadMEM (6w, Reg 5w);
     StoreMEMByte (Reg 6w, Reg 4w);
     Shift (shiftLR, 6w, Reg 6w, Imm 4w);
     Normal (fAdd, 4w, Reg 4w, Imm 4w);
     StoreMEMByte (Reg 6w, Reg 4w);
     LoadConstant(6w, F, n2w startup_code_size);
     Normal (fSub, 5w, Reg 5w, Reg 6w);
     StoreMEMByte (Imm 1w, Reg 5w);
     Normal (fSub, 4w, Reg 4w, Imm 4w);
     Normal(fSnd, 5w, Imm 0w, Imm 0w);
     Normal(fSnd, 6w, Imm 0w, Imm 0w);
     Normal(fSnd, 7w, Imm 0w, Imm 0w);
     Normal(fAdd, 8w, Imm 0w, Imm 0w);
     Interrupt;
     Jump (fSnd, 0w, Reg 0w)]`;

(* get_arg_length
   PC is mem_start + ffi_code_start_offset
         + ag32_ffi_get_arg_count_entrypoint
         + 4 * LENGTH ag32_ffi_get_arg_count_code
   r3 contains pointer to byte array with the arg index: [index % 256, index / 256]
   the array should afterwards contain the length of the arg at index (in the same format) *)

val ag32_ffi_get_arg_length_entrypoint_def = Define`
  ag32_ffi_get_arg_length_entrypoint =
  ag32_ffi_get_arg_count_entrypoint + 4 * LENGTH ag32_ffi_get_arg_count_code`;

val ag32_ffi_get_arg_length_1_def = Define`
  ag32_ffi_get_arg_length_1 s =
    let pc_offset = ffi_code_start_offset +
                    ag32_ffi_get_arg_length_entrypoint +
                    4 in
    let s = dfn'Jump(fAdd, 5w, Imm 4w) s in
    let s = incPC () (s with R := (6w =+ w2w(((22 >< 0)(n2w pc_offset :word32)):23 word)) s.R) in
    let s = incPC () (s with R := (6w =+ bit_field_insert 31 23 (((31 >< 23)(n2w pc_offset :word32)):9 word) (s.R 6w)) s.R) in
    let s = dfn'Normal (fSub, 5w, Reg 5w, Reg 6w) s in
    let s = incPC () (s with MEM := ((s.R 5w) =+ 2w) s.MEM) in
    let s = incPC () (s with R := (7w =+ w2w (s.MEM (s.R 4w))) s.R) in
    let s = dfn'Normal (fAdd, 4w, Reg 4w, Imm 4w) s in
    let s = incPC () (s with R := (6w =+ w2w (s.MEM (s.R 4w))) s.R) in
    let s = incPC () (s with R := (6w =+ ((s.R 6w) <<~ 4w)) s.R) in
    let s = dfn'Normal (fAdd, 7w, Reg 6w, Reg 7w) s in
    let s = incPC () (s with R := (6w =+ (n2w (startup_code_size + 4))) s.R) in
    let s = dfn'Normal (fAdd, 5w, Reg 5w, Reg 6w) s in
    let s = incPC () (s with R := (6w =+ 0w) s.R) in
    s`;

val ag32_ffi_get_arg_length_2_def = tDefine"ag32_ffi_get_arg_length_2"`
  ag32_ffi_get_arg_length_2 s =
    if ∀n. s.MEM (s.R 5w + n2w n) ≠ 0w then s else
    let s = incPC () (s with R := (8w =+ w2w (s.MEM (s.R 5w))) s.R) in
    if (s.R 8w = 0w) then
      s with PC := s.PC + 4w * 4w
    else
      let s = incPC () (s with R := (6w =+ (s.R 6w + 1w)) s.R) in
      let s = incPC () (s with R := (5w =+ (s.R 5w + 1w)) s.R) in
      let s = s with PC := s.PC + 4w * - 4w in
      ag32_ffi_get_arg_length_2 s`
  (simp[APPLY_UPDATE_THM, ag32Theory.incPC_def]
   \\ wf_rel_tac`measure (λs. LEAST n. s.MEM (s.R 5w + (n2w n)) = 0w)`
   \\ rw[APPLY_UPDATE_THM]
   \\ Cases_on`n` \\ fs[] \\ rfs[]
   \\ numLib.LEAST_ELIM_TAC
   \\ conj_tac
   >- (
     qmatch_asmsub_rename_tac`SUC n`
     \\ qexists_tac`n`
     \\ fs[GSYM word_add_n2w,ADD1] )
   \\ rw[]
   \\ numLib.LEAST_ELIM_TAC
   \\ conj_tac >- metis_tac[]
   \\ rw[]
   \\ CCONTR_TAC \\ fs[NOT_LESS, LESS_EQ_EXISTS]
   \\ rw[]
   \\ qmatch_asmsub_rename_tac`s.MEM (n2w m + _) = 0w`
   \\ Cases_on`m` \\ fs[]
   \\ last_x_assum(qspec_then`n`mp_tac)
   \\ simp[ADD1]
   \\ fs[ADD1, GSYM word_add_n2w]);

val ag32_ffi_get_arg_length_3_def = Define`
  ag32_ffi_get_arg_length_3 s =
    let s = dfn'Normal (fSub, 4w, Reg 4w, Imm 4w) s in
    let s = incPC () (s with MEM := ((s.R 4w) =+ w2w (s.R 6w)) s.MEM) in
    let s = incPC () (s with R := (6w =+ (s.R 6w >>>~ 4w)) s.R) in
    let s = dfn'Normal (fAdd, 4w, Reg 4w, Imm 4w) s in
    let s = incPC () (s with MEM := ((s.R 4w) =+ w2w (s.R 6w)) s.MEM) in
    let s = incPC () (s with R := (5w =+ 0w) s.R) in
    let s = incPC () (s with R := (6w =+ 0w) s.R) in
    let s = incPC () (s with R := (7w =+ 0w) s.R) in
    let s = incPC () (s with <| R := (8w =+ 0w) s.R; OverflowFlag := F; CarryFlag := F|>) in
    let s = incPC () (s with io_events := s.io_events ++ [s.MEM]) in
    let s = s with <| R := (0w =+ s.PC + 4w) s.R; PC := s.R 0w |> in
    s`;

val ag32_ffi_get_arg_length_code_def = Define`
  ag32_ffi_get_arg_length_code =
    let pc_offset = ffi_code_start_offset +
                    ag32_ffi_get_arg_length_entrypoint +
                    4 in
    [Jump (fAdd, 5w, Imm 4w);
     LoadConstant(6w, F, (22 >< 0)((n2w pc_offset):word32));
     LoadUpperConstant(6w, (31 >< 23)((n2w pc_offset):word32));
     Normal (fSub, 5w, Reg 5w, Reg 6w); (* mem_start is now in r5 *)
     StoreMEMByte (Imm 2w, Reg 5w);
     LoadMEMByte (7w, Reg 4w);
     Normal (fAdd, 4w, Reg 4w, Imm 4w);
     LoadMEMByte (6w, Reg 4w);
     Shift (shiftLL, 6w, Reg 6w, Imm 4w);
     Normal (fAdd, 7w, Reg 6w, Reg 7w); (* index is now in r7 *)
     LoadConstant (6w, F, n2w (startup_code_size + 4));
     Normal (fAdd, 5w, Reg 5w, Reg 6w); (* r5 is now at start of args *)
     Normal (fSnd, 6w, Imm 0w, Imm 0w); (* r6 is length counter *)
     LoadMEMByte (8w, Reg 5w);
     JumpIfZero (fSnd, Imm (4w * 4w), Imm 0w, Reg 8w);
     Normal (fInc, 6w, Reg 6w, Imm 0w);
     Normal (fInc, 5w, Reg 5w, Imm 0w);
     JumpIfZero (fSnd, Imm (4w * -4w), Imm 0w, Imm 0w);
     Normal (fSub, 4w, Reg 4w, Imm 4w);
     StoreMEMByte (Reg 6w, Reg 4w);
     Shift (shiftLR, 6w, Reg 6w, Imm 4w);
     Normal (fAdd, 4w, Reg 4w, Imm 4w);
     StoreMEMByte (Reg 6w, Reg 4w);
     Normal(fSnd, 5w, Imm 0w, Imm 0w);
     Normal(fSnd, 6w, Imm 0w, Imm 0w);
     Normal(fSnd, 7w, Imm 0w, Imm 0w);
     Normal(fAdd, 8w, Imm 0w, Imm 0w);
     Interrupt;
     Jump (fSnd, 0w, Reg 0w)]`;

(* get_arg *)

val ag32_ffi_get_arg_entrypoint_def = Define`
  ag32_ffi_get_arg_entrypoint =
  ag32_ffi_get_arg_length_entrypoint + 4 * LENGTH ag32_ffi_get_arg_length_code`;

val ag32_ffi_get_arg_code_def = Define`
  ag32_ffi_get_arg_code = [Interrupt] (* TODO *)`;

(* read *)

val ag32_ffi_read_entrypoint_def = Define`
  ag32_ffi_read_entrypoint =
  ag32_ffi_get_arg_entrypoint + 4 * LENGTH ag32_ffi_get_arg_code`;

val ag32_ffi_read_code_def = Define`
  ag32_ffi_read_code = [Interrupt] (* TODO *)`;

(* write
   PC is mem_start + ffi_code_start_offset + ag32_ffi_write_entrypoint
   r1 contains pointer to byte array (conf) with the output id
   r2 contains length of r1 (should be 8)
   r3 contains pointer to byte array n1::n0::off1::off0::tll
   r4 contains LENGTH tll + 4
   postconditions:
     * written (THE (ALOOKUP FFI_codes "write")) at (mem_start + n2w (ffi_code_start_offset - 1))
     * if the following conditions hold
         - r2 contains 8
         - w82n conf ≤ 2
         - w22n [off1; off0] ≤ LENGTH tll
         - w22n [n1; n0] ≤ LENGTH tll - w22n [off1; off0]
       then
         - write 0w::n2w2(k) to array pointed by r3
         - write conf ++ [0w;0w;n1;n0] ++ (TAKE k (DROP (w22n [off1; off0]) tll))
           to mem_start + n2w output_offset
         where k = MIN (w22n [n1; n0]) output_buffer_size
       else
         - write 1w to the first byte pointed by r3
         - do not touch anything else in memory
     * r1,..,r8 are set to 0 and carry and overflow unset
     * exit happens at the end of the code, by jumping to r0
*)

val ag32_ffi_write_entrypoint_def = Define`
  ag32_ffi_write_entrypoint =
  ag32_ffi_read_entrypoint + 4 * LENGTH ag32_ffi_read_code`;

val ag32_ffi_write_set_id_code_def = Define`
  ag32_ffi_write_set_id_code =
    [Jump (fAdd, 5w, Imm 4w);
     LoadConstant(6w, F, n2w (ag32_ffi_write_entrypoint + 4));
     Normal (fSub, 5w, Reg 5w, Reg 6w);   (* r5 = mem_start + ffi_code_start_offset *)
     Normal (fDec, 5w, Reg 5w, Imm 0w);
     StoreMEMByte(Imm (n2w(THE(ALOOKUP FFI_codes "write"))), Reg 5w)]`;

val ag32_ffi_write_check_conf_code_def = Define`
  ag32_ffi_write_check_conf_code = [
     Normal (fEqual, 6w, Reg 2w, Imm 8w); (* r6 = (LENGTH conf = 8) *)
     Normal (fSub, 4w, Reg 4w, Imm 4w);   (* r4 = LENGTH tll *)
     LoadMEMByte (2w, Reg 1w);            (* r2 = conf7 *)
     Normal (fEqual, 7w, Reg 2w, Imm 0w); (* r7 = conf7 = 0 *)
     Normal (fAnd, 6w, Reg 6w, Reg 7w);   (* r6 = (LENGTH conf = 8) ∧ conf7 = 0 *)
     Normal (fInc, 1w, Reg 1w, Imm 1w);   (* r1 -> conf6::conf5...conf0 *)
     LoadMEMByte (2w, Reg 1w);            (* r2 = conf6 *)
     Normal (fEqual, 7w, Reg 2w, Imm 0w); (* r7 = conf6 = 0 *)
     Normal (fAnd, 6w, Reg 6w, Reg 7w);   (* r6 = (LENGTH conf = 8) ∧ conf{7..6} = 0 *)
     Normal (fInc, 1w, Reg 1w, Imm 1w);   (* r1 -> conf5::conf4...conf0 *)
     LoadMEMByte (2w, Reg 1w);            (* r2 = conf5 *)
     Normal (fEqual, 7w, Reg 2w, Imm 0w); (* r7 = conf5 = 0 *)
     Normal (fAnd, 6w, Reg 6w, Reg 7w);   (* r6 = (LENGTH conf = 8) ∧ conf{7..5} = 0 *)
     Normal (fInc, 1w, Reg 1w, Imm 1w);   (* r1 -> conf4::conf3...conf0 *)
     LoadMEMByte (2w, Reg 1w);            (* r2 = conf4 *)
     Normal (fEqual, 7w, Reg 2w, Imm 0w); (* r7 = conf4 = 0 *)
     Normal (fAnd, 6w, Reg 6w, Reg 7w);   (* r6 = (LENGTH conf = 8) ∧ conf{7..4} = 0 *)
     Normal (fInc, 1w, Reg 1w, Imm 1w);   (* r1 -> conf3::conf2...conf0 *)
     LoadMEMByte (2w, Reg 1w);            (* r2 = conf3 *)
     Normal (fEqual, 7w, Reg 2w, Imm 0w); (* r7 = conf3 = 0 *)
     Normal (fAnd, 6w, Reg 6w, Reg 7w);   (* r6 = (LENGTH conf = 8) ∧ conf{7..3} = 0 *)
     Normal (fInc, 1w, Reg 1w, Imm 1w);   (* r1 -> conf2::conf1::conf0 *)
     LoadMEMByte (2w, Reg 1w);            (* r2 = conf2 *)
     Normal (fEqual, 7w, Reg 2w, Imm 0w); (* r7 = conf2 = 0 *)
     Normal (fAnd, 6w, Reg 6w, Reg 7w);   (* r6 = (LENGTH conf = 8) ∧ conf{7..2} = 0 *)
     Normal (fInc, 1w, Reg 1w, Imm 1w);   (* r1 -> conf1::conf0 *)
     LoadMEMByte (2w, Reg 1w);            (* r2 = conf1 *)
     Normal (fEqual, 7w, Reg 2w, Imm 0w); (* r7 = conf1 = 0 *)
     Normal (fAnd, 6w, Reg 6w, Reg 7w);   (* r6 = (LENGTH conf = 8) ∧ conf{7..1} = 0 *)
     Normal (fInc, 1w, Reg 1w, Imm 1w);   (* r1 -> conf0 *)
     LoadMEMByte (2w, Reg 1w);            (* r2 = conf0 *)
     Normal (fLess, 7w, Reg 2w, Imm 3w);  (* r7 = conf0 < 3 *)
     Normal (fAnd, 6w, Reg 6w, Reg 7w)]   (* r6 = (LENGTH conf = 8) ∧ w82n conf < 3 *)`;

val ag32_ffi_write_load_noff_code_def = Define`
  ag32_ffi_write_load_noff_code = [       (* r3 -> n1::n0::off1::off0::... *)
     LoadMEMByte (1w, Reg 3w);            (* r1 = [0w; 0w; 0w; n1] *)
     Shift (shiftLL, 1w, Reg 1w, Imm 8w); (* r1 = [0w; 0w; n1; 0w] *)
     Normal (fInc, 3w, Reg 3w, Imm 1w);   (* r3 -> n0::off1::off0::... *)
     LoadMEMByte (8w, Reg 3w);            (* r8 = [0w; 0w; 0w; n0] *)
     Normal (fXor, 1w, Reg 1w, Reg 8w);   (* r1 = [0w; 0w; n1; n0] (= w22n [n1; n0]) *)
     Normal (fInc, 3w, Reg 3w, Imm 1w);   (* r3 -> off1::off0::... *)
     LoadMEMByte (7w, Reg 3w);            (* r7 = [0w; 0w; 0w; off1] *)
     Shift (shiftLL, 7w, Reg 7w, Imm 8w); (* r7 = [0w; 0w; off1; 0w] *)
     Normal (fInc, 3w, Reg 3w, Imm 1w);   (* r3 -> off0::... *)
     LoadMEMByte (8w, Reg 3w);            (* r8 = [0w; 0w; 0w; off0] *)
     Normal (fXor, 7w, Reg 7w, Reg 8w);   (* r7 = [0w; 0w; off1; off0] (= w22n [off1; off0]) *)
     Normal (fSub, 3w, Reg 3w, Imm 3w)]   (* r3 -> n1::n0::off1::off0::... *)`;

val ag32_ffi_write_check_lengths_code_def = Define`
  ag32_ffi_write_check_lengths_code = [
     Normal (fLower, 8w, Reg 4w, Reg 7w); (* r8 = LENGTH tll < w22n [off1; off0] *)
     Normal (fSub, 8w, Imm 1w, Reg 8w);   (* r8 = ¬(LENGTH tll < w22n [off1; off0] *)
     Normal (fAnd, 6w, Reg 6w, Reg 8w);   (* r6 = (LENGTH conf = 8) ∧ w82n conf < 3 ∧
                                                  w22n [off1; off0] ≤ LENGTH tll *)
     Normal (fSub, 4w, Reg 4w, Reg 7w);   (* r4 = LENGTH tll - w22n [off1; off0] *)
     Normal (fLower, 8w, Reg 4w, Reg 1w); (* r8 = LENGTH tll - w22n [off1; off0] < w22n [n1; n0] *)
     Normal (fSub, 8w, Imm 1w, Reg 8w);   (* r8 = ¬(LENGTH tll - w22n [off1; off0] < w22n [n1; n0] *)
     LoadConstant (4w, F, 4w * 36w);
     JumpIfZero (fAnd, Reg 4w, Reg 6w, Reg 8w)]`;

val ag32_ffi_write_write_header_code_def = Define`
  ag32_ffi_write_write_header_code = [
     LoadConstant(8w, F, n2w ((ffi_code_start_offset - 1) - output_offset));
     Normal (fSub, 5w, Reg 5w, Reg 8w);   (* r5 = mem_start + output_offset *)
     StoreMEM (Imm 0w, Reg 5w);
     Normal (fAdd, 5w, Reg 5w, Imm 4w);   (* r5 = mem_start + output_offset + 4 *)
     Shift (shiftLL, 2w, Reg 2w, Imm 24w);(* r2 = [conf0; 0w; 0w; 0w] *)
     StoreMEM (Reg 2w, Reg 5w);
     Normal (fAdd, 5w, Reg 5w, Imm 4w);   (* r5 = mem_start + output_offset + 8 *)
     StoreMEMByte (Imm 0w, Reg 5w);
     Normal (fInc, 5w, Reg 5w, Imm 1w);   (* r5 = mem_start + output_offset + 9 *)
     StoreMEMByte (Imm 0w, Reg 5w);
     Normal (fInc, 5w, Reg 5w, Imm 1w);   (* r5 = mem_start + output_offset + 10 *)
     Shift (shiftLR, 2w, Reg 1w, Imm 8w); (* r2 = [0w; 0w; 0w; n1] *)
     StoreMEMByte (Reg 2w, Reg 5w);
     Normal (fInc, 5w, Reg 5w, Imm 1w);   (* r5 = mem_start + output_offset + 11 *)
     StoreMEMByte (Reg 1w, Reg 5w);
     Normal (fInc, 5w, Reg 5w, Imm 1w);   (* r5 = mem_start + output_offset + 12 *)
     StoreMEMByte (Imm 0w, Reg 3w)]`;

val ag32_ffi_write_num_written_code_def = Define`
  ag32_ffi_write_num_written_code = [
     (* calculate k and write to mutable array *)
     Normal (fInc, 3w, Reg 3w, Imm 1w);   (* r3 -> n0::off1::off0::tll *)
     LoadConstant (8w, F, n2w output_buffer_size); (* r8 = output_buffer_size *)
     JumpIfZero (fLess, Imm 8w, Reg 8w, Reg 1w);  (* skip if ¬(output_buffer_size < w22n [n1; n0]) *)
     Normal (fSnd, 1w, Reg 1w, Reg 8w);   (* r1 = MIN output_buffer_size (w22n [n1; n0]) *)
     Shift (shiftLR, 8w, Reg 1w, Imm 8w); (* r8 = r1 DIV 256 *)
     StoreMEMByte (Reg 8w, Reg 3w);
     Normal (fInc, 3w, Reg 3w, Imm 1w);   (* r3 -> off1::off0::tll *)
     StoreMEMByte (Reg 1w, Reg 3w);
     Normal (fAdd, 3w, Reg 3w, Imm 2w);
     Normal (fAdd, 3w, Reg 3w, Reg 7w);   (* r3 -> DROP off tll *)
     LoadConstant (2w, F, 4w * 8w)]`;

val ag32_ffi_write_copy_code_def = Define`
  ag32_ffi_write_copy_code = [
     JumpIfZero (fSnd, Reg 2w, Imm 0w, Reg 1w);
     LoadMEMByte (8w, Reg 3w);
     StoreMEMByte (Reg 8w, Reg 5w);
     Normal (fInc, 3w, Reg 3w, Imm 1w);
     Normal (fInc, 5w, Reg 5w, Imm 1w);
     Normal (fDec, 1w, Reg 1w, Imm 1w);
     JumpIfZero (fSnd, Imm (4w * -6w), Imm 0w, Imm 0w)]`;

val ag32_ffi_write_code_def = Define`
  ag32_ffi_write_code =
     ag32_ffi_write_set_id_code ++
     ag32_ffi_write_check_conf_code ++
     ag32_ffi_write_load_noff_code ++
     ag32_ffi_write_check_lengths_code ++
     ag32_ffi_write_write_header_code ++
     ag32_ffi_write_num_written_code ++
     ag32_ffi_write_copy_code ++
     [ (* error case *) StoreMEMByte (Imm 1w, Reg 3w) ] ++
     ag32_ffi_return_code`;

val ag32_ffi_write_set_id_def = Define`
  ag32_ffi_write_set_id s =
    let s = dfn'Jump (fAdd, 5w, Imm 4w) s in
    let s = dfn'LoadConstant (6w, F, n2w (ag32_ffi_write_entrypoint + 4)) s in
    let s = dfn'Normal (fSub, 5w, Reg 5w, Reg 6w) s in
    let s = dfn'Normal (fDec, 5w, Reg 5w, Imm 0w) s in
    let s = dfn'StoreMEMByte (Imm (n2w(THE(ALOOKUP FFI_codes "write"))), Reg 5w) s in
    s`;

val ag32_ffi_write_set_id_thm = Q.store_thm("ag32_ffi_write_set_id_thm",
  `(s.PC = r0 + n2w (ffi_code_start_offset + ag32_ffi_write_entrypoint))
    ⇒
    ∃cf ov r6.
     (ag32_ffi_write_set_id s =
      s with <| PC := s.PC + n2w (4 * LENGTH ag32_ffi_write_set_id_code);
                R := ((6w =+ r6) ((5w =+ r0 + (n2w (ffi_code_start_offset - 1))) s.R));
                CarryFlag := cf;
                OverflowFlag := ov;
                MEM := ((r0 + n2w (ffi_code_start_offset - 1)) =+ n2w (THE (ALOOKUP FFI_codes "write"))) s.MEM |>)`,
  rw[ag32_ffi_write_set_id_def]
  \\ rw[ag32Theory.dfn'Jump_def, ag32Theory.ALU_def, ag32Theory.ri2word_def]
  \\ qmatch_goalsub_abbrev_tac`r0 + n2w off`
  \\ rw[ag32Theory.dfn'LoadConstant_def, ag32Theory.incPC_def]
  \\ rw[ag32Theory.dfn'Normal_def, ag32Theory.norm_def, ag32Theory.ALU_def,
        ag32Theory.ri2word_def, ag32Theory.incPC_def, APPLY_UPDATE_THM]
  \\ rw[ag32Theory.dfn'StoreMEMByte_def, ag32Theory.ri2word_def,
        ag32Theory.incPC_def, APPLY_UPDATE_THM]
  \\ rw[ag32Theory.ag32_state_component_equality, APPLY_UPDATE_THM, FUN_EQ_THM, Abbr`off`]
  \\ EVAL_TAC
  \\ rw[]
  \\ metis_tac[]);

val ag32_ffi_write_set_id_code_thm = Q.store_thm("ag32_ffi_write_set_id_code_thm",
  `(∀k. k < LENGTH ag32_ffi_write_set_id_code ⇒
        (get_mem_word s.MEM (s.PC + n2w (4 * k)) =
         Encode (EL k ag32_ffi_write_set_id_code))) ∧
   byte_aligned s.PC
   ⇒
   ∃k. (FUNPOW Next k s = ag32_ffi_write_set_id s)`,
  rw[ag32_ffi_write_set_id_def]
  \\ rw[Once EXISTS_NUM] \\ disj2_tac \\ rw[FUNPOW]
  \\ rw[ag32Theory.Next_def]
  \\ drule byte_aligned_imp \\ rw[]
  \\ pop_assum kall_tac
  \\ rw[GSYM get_mem_word_def]
  \\ first_assum(qspec_then`0`mp_tac)
  \\ simp_tac(srw_ss())[ag32_ffi_write_set_id_code_def]
  \\ disch_then kall_tac
  \\ simp[ag32_targetProofTheory.Decode_Encode]
  \\ simp[ag32Theory.Run_def]
  \\ rw[Once EXISTS_NUM] \\ disj2_tac \\ rw[FUNPOW]
  \\ rw[ag32Theory.Next_def]
  \\ qmatch_goalsub_abbrev_tac`s1.PC`
  \\ `(s.PC + 4w = s1.PC) ∧ (s1.MEM = s.MEM)`
  by ( simp[Abbr`s1`, ag32Theory.dfn'Jump_def, ag32Theory.ALU_def,ag32Theory.ri2word_def] )
  \\ `byte_aligned s1.PC`
  by (
    first_x_assum (CHANGED_TAC o SUBST1_TAC o SYM)
    \\ irule byte_aligned_add
    \\ simp[] \\ EVAL_TAC )
  \\ drule byte_aligned_imp \\ rw[]
  \\ pop_assum kall_tac
  \\ rw[GSYM get_mem_word_def]
  \\ first_assum(qspec_then`1`mp_tac)
  \\ simp_tac(srw_ss())[ag32_ffi_write_set_id_code_def]
  \\ simp[]
  \\ disch_then kall_tac
  \\ simp[ag32_targetProofTheory.Decode_Encode]
  \\ simp[ag32Theory.Run_def]
  \\ rw[Once EXISTS_NUM] \\ disj2_tac \\ rw[FUNPOW]
  \\ rw[ag32Theory.Next_def]
  \\ qmatch_goalsub_abbrev_tac`s2.PC`
  \\ `(s.PC + 8w = s2.PC) ∧ (s2.MEM = s.MEM)`
  by ( simp[Abbr`s2`, ag32Theory.dfn'LoadConstant_def, ag32Theory.incPC_def]
       \\ first_x_assum (CHANGED_TAC o SUBST1_TAC o SYM) \\ simp[] )
  \\ `byte_aligned s2.PC`
  by (
    first_x_assum (CHANGED_TAC o SUBST1_TAC o SYM)
    \\ irule byte_aligned_add
    \\ simp[] \\ EVAL_TAC )
  \\ drule byte_aligned_imp \\ rw[]
  \\ pop_assum kall_tac
  \\ rw[GSYM get_mem_word_def]
  \\ first_assum(qspec_then`2`mp_tac)
  \\ simp_tac(srw_ss())[ag32_ffi_write_set_id_code_def]
  \\ simp[]
  \\ disch_then kall_tac
  \\ simp[ag32_targetProofTheory.Decode_Encode]
  \\ simp[ag32Theory.Run_def]
  \\ rw[Once EXISTS_NUM] \\ disj2_tac \\ rw[FUNPOW]
  \\ rw[ag32Theory.Next_def]
  \\ qmatch_goalsub_abbrev_tac`s3.PC`
  \\ `(s.PC + n2w(3*4) = s3.PC) ∧ (s3.MEM = s.MEM)`
  by ( simp[Abbr`s3`, dfn'Normal_PC, dfn'Normal_MEM]
       \\ first_x_assum (CHANGED_TAC o SUBST1_TAC o SYM) \\ simp[] )
  \\ `byte_aligned s3.PC`
  by (
    first_x_assum (CHANGED_TAC o SUBST1_TAC o SYM)
    \\ irule byte_aligned_add
    \\ simp[] \\ EVAL_TAC )
  \\ drule byte_aligned_imp \\ rw[]
  \\ pop_assum kall_tac
  \\ rw[GSYM get_mem_word_def]
  \\ first_assum(qspec_then`3`mp_tac)
  \\ simp_tac(srw_ss())[ag32_ffi_write_set_id_code_def]
  \\ fs[]
  \\ disch_then kall_tac
  \\ simp[ag32_targetProofTheory.Decode_Encode]
  \\ simp[ag32Theory.Run_def]
  \\ rw[Once EXISTS_NUM] \\ disj2_tac \\ rw[FUNPOW]
  \\ rw[ag32Theory.Next_def]
  \\ qmatch_goalsub_abbrev_tac`s4.PC`
  \\ `(s.PC + n2w(4*4) = s4.PC) ∧ (s4.MEM = s.MEM)`
  by ( simp[Abbr`s4`, dfn'Normal_PC, dfn'Normal_MEM]
       \\ first_x_assum (CHANGED_TAC o SUBST1_TAC o SYM) \\ simp[] )
  \\ `byte_aligned s4.PC`
  by (
    first_x_assum (CHANGED_TAC o SUBST1_TAC o SYM)
    \\ irule byte_aligned_add
    \\ simp[] \\ EVAL_TAC )
  \\ drule byte_aligned_imp \\ rw[]
  \\ pop_assum kall_tac
  \\ rw[GSYM get_mem_word_def]
  \\ first_assum(qspec_then`4`mp_tac)
  \\ simp_tac(srw_ss())[ag32_ffi_write_set_id_code_def]
  \\ fs[]
  \\ disch_then kall_tac
  \\ simp[ag32_targetProofTheory.Decode_Encode]
  \\ simp[ag32Theory.Run_def]
  \\ rw[Once EXISTS_NUM]);

val ag32_ffi_write_check_conf_def = Define`
  ag32_ffi_write_check_conf s =
   let s = dfn'Normal (fEqual, 6w, Reg 2w, Imm 8w) s in
   let s = dfn'Normal (fSub, 4w, Reg 4w, Imm 4w) s in
   let s = dfn'LoadMEMByte (2w, Reg 1w) s in
   let s = dfn'Normal (fEqual, 7w, Reg 2w, Imm 0w) s in
   let s = dfn'Normal (fAnd, 6w, Reg 6w, Reg 7w) s in
   let s = dfn'Normal (fInc, 1w, Reg 1w, Imm 1w) s in
   let s = dfn'LoadMEMByte (2w, Reg 1w) s in
   let s = dfn'Normal (fEqual, 7w, Reg 2w, Imm 0w) s in
   let s = dfn'Normal (fAnd, 6w, Reg 6w, Reg 7w) s in
   let s = dfn'Normal (fInc, 1w, Reg 1w, Imm 1w) s in
   let s = dfn'LoadMEMByte (2w, Reg 1w) s in
   let s = dfn'Normal (fEqual, 7w, Reg 2w, Imm 0w) s in
   let s = dfn'Normal (fAnd, 6w, Reg 6w, Reg 7w) s in
   let s = dfn'Normal (fInc, 1w, Reg 1w, Imm 1w) s in
   let s = dfn'LoadMEMByte (2w, Reg 1w) s in
   let s = dfn'Normal (fEqual, 7w, Reg 2w, Imm 0w) s in
   let s = dfn'Normal (fAnd, 6w, Reg 6w, Reg 7w) s in
   let s = dfn'Normal (fInc, 1w, Reg 1w, Imm 1w) s in
   let s = dfn'LoadMEMByte (2w, Reg 1w) s in
   let s = dfn'Normal (fEqual, 7w, Reg 2w, Imm 0w) s in
   let s = dfn'Normal (fAnd, 6w, Reg 6w, Reg 7w) s in
   let s = dfn'Normal (fInc, 1w, Reg 1w, Imm 1w) s in
   let s = dfn'LoadMEMByte (2w, Reg 1w) s in
   let s = dfn'Normal (fEqual, 7w, Reg 2w, Imm 0w) s in
   let s = dfn'Normal (fAnd, 6w, Reg 6w, Reg 7w) s in
   let s = dfn'Normal (fInc, 1w, Reg 1w, Imm 1w) s in
   let s = dfn'LoadMEMByte (2w, Reg 1w) s in
   let s = dfn'Normal (fEqual, 7w, Reg 2w, Imm 0w) s in
   let s = dfn'Normal (fAnd, 6w, Reg 6w, Reg 7w) s in
   let s = dfn'Normal (fInc, 1w, Reg 1w, Imm 1w) s in
   let s = dfn'LoadMEMByte (2w, Reg 1w) s in
   let s = dfn'Normal (fLess, 7w, Reg 2w, Imm 3w) s in
   let s = dfn'Normal (fAnd, 6w, Reg 6w, Reg 7w) s in s`;

val ag32_ffi_write_check_conf_thm = Q.store_thm("ag32_ffi_write_check_conf_thm",
  `bytes_in_memory (s.R 1w) conf s.MEM md ∧ (w2n (s.R 2w) = LENGTH conf)
   ⇒
   ∃ov cf r1 r2 r7.
   (ag32_ffi_write_check_conf s =
    s with <| R := ((6w =+ v2w[(LENGTH conf = 8) ∧ w82n conf < 3])
                   ((2w =+ (if (LENGTH conf = 8) ∧ w82n conf < 3 then n2w (w82n conf) else r2))
                   ((4w =+ s.R 4w - 4w)
                   ((1w =+ r1)
                   ((7w =+ r7) s.R)))));
              PC := s.PC + n2w (4 * LENGTH ag32_ffi_write_check_conf_code);
              OverflowFlag := ov;
              CarryFlag := cf |>)`,
  rewrite_tac[ag32_ffi_write_check_conf_def]
  \\ strip_tac
  \\ simp_tac (srw_ss())
       [Q.SPECL[`fEqual`,`6w`]ag32Theory.dfn'Normal_def,
        ag32Theory.ri2word_def, ag32Theory.norm_def,
        ag32Theory.ALU_def, ag32Theory.incPC_def ]
  \\ CONV_TAC(PATH_CONV"rararararalrr"(SIMP_CONV(srw_ss()++LET_ss)[]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ simp_tac (srw_ss())
       [Q.SPECL[`fSub`]ag32Theory.dfn'Normal_def,
        ag32Theory.ri2word_def, ag32Theory.norm_def,
        ag32Theory.ALU_def, ag32Theory.incPC_def ]
  \\ CONV_TAC(PATH_CONV"rararararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ simp_tac (srw_ss()) [ag32Theory.dfn'LoadMEMByte_def, ag32Theory.incPC_def, ag32Theory.ri2word_def]
  \\ CONV_TAC(PATH_CONV"rararararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ simp_tac (srw_ss())
       [Q.SPECL[`fEqual`,`7w`]ag32Theory.dfn'Normal_def,
        ag32Theory.ri2word_def, ag32Theory.norm_def,
        ag32Theory.ALU_def, ag32Theory.incPC_def ]
  \\ CONV_TAC(PATH_CONV"rararararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ simp_tac (srw_ss())
       [Q.SPECL[`fAnd`]ag32Theory.dfn'Normal_def,
        ag32Theory.ri2word_def, ag32Theory.norm_def,
        ag32Theory.ALU_def, ag32Theory.incPC_def ]
  \\ CONV_TAC(PATH_CONV"rararararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ simp_tac (srw_ss())
       [Q.SPECL[`fInc`]ag32Theory.dfn'Normal_def,
        ag32Theory.ri2word_def, ag32Theory.norm_def,
        ag32Theory.ALU_def, ag32Theory.incPC_def ]
  \\ ntac 25 (
    CONV_TAC(PATH_CONV"rararararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
    \\ simp_tac (srw_ss()) [Once LET_THM])
  \\ CONV_TAC(PATH_CONV"rararararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ simp_tac (srw_ss())
       [ag32Theory.dfn'Normal_def,
        ag32Theory.ri2word_def, ag32Theory.norm_def,
        ag32Theory.ALU_def, ag32Theory.incPC_def ]
  \\ CONV_TAC(PATH_CONV"rararararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ CONV_TAC(PATH_CONV"rararararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ simp[ag32Theory.ag32_state_component_equality]
  \\ simp[ag32_ffi_write_check_conf_code_def]
  \\ simp[APPLY_UPDATE_THM, FUN_EQ_THM]
  \\ qexists_tac`s.R 1w + 7w`
  \\ qexists_tac`w2w (s.MEM (s.R 1w + 7w))`
  \\ qmatch_goalsub_abbrev_tac`if 7w = _ then r7 else _`
  \\ qexists_tac`r7`
  \\ reverse(Cases_on`LENGTH conf = 8`) \\ fs[]
  >- ( Cases_on`s.R 2w` \\ fs[] \\ rw[] \\ fs[] )
  \\ fs[LENGTH_EQ_NUM_compute]
  \\ rveq
  \\ fs[asmSemTheory.bytes_in_memory_def] \\ rveq
  \\ simp[MarshallingTheory.w82n_def, LEFT_ADD_DISTRIB]
  \\ Cases_on`s.R 2w` \\ fs[] \\ rveq
  \\ Cases \\ fs[]
  \\ Cases_on`7=n` \\ fs[]
  \\ Cases_on`4=n` \\ fs[]
  \\ Cases_on`1=n` \\ fs[]
  \\ rfs[Abbr`r7`]
  \\ Cases_on`s.R 1w` \\ fs[]
  \\ Cases_on`2=n` \\ fs[]
  >- (
    rw[]
    \\ rw[GSYM word_add_n2w]
    \\ qmatch_asmsub_rename_tac`s.R 1w = n2w r1`
    \\ Cases_on`s.MEM (n2w r1)` \\ fs[]
    \\ Cases_on`n` \\ fs[]
    \\ Cases_on`s.MEM (n2w r1 + 1w)` \\ fs[]
    \\ Cases_on`n` \\ fs[]
    \\ Cases_on`s.MEM (n2w r1 + 3w)` \\ fs[]
    \\ Cases_on`n` \\ fs[]
    \\ Cases_on`s.MEM (n2w r1 + 5w)` \\ fs[]
    \\ Cases_on`n` \\ fs[]
    \\ Cases_on`s.MEM (n2w r1 + 4w)` \\ fs[]
    \\ Cases_on`n` \\ fs[]
    \\ Cases_on`s.MEM (n2w r1 + 2w)` \\ fs[]
    \\ Cases_on`n` \\ fs[]
    \\ Cases_on`s.MEM (n2w r1 + 6w)` \\ fs[]
    \\ Cases_on`n` \\ fs[]
    \\ Cases_on`s.MEM (n2w r1 + 7w)` \\ fs[]
    \\ Cases_on`n` \\ fs[]
    \\ Cases_on`n'` \\ fs[]
    \\ Cases_on`n` \\ fs[] )
  \\ Cases_on`6=n` \\ fs[]
  \\ rveq \\ rw[]
  \\ qmatch_asmsub_rename_tac`s.R 1w = n2w r1`
  \\ Cases_on`s.MEM (n2w r1)` \\ fs[]
  \\ Cases_on`s.MEM (n2w r1 + 6w)` \\ fs[]
  \\ Cases_on`s.MEM (n2w r1 + 1w)` \\ fs[]
  \\ Cases_on`s.MEM (n2w r1 + 2w)` \\ fs[]
  \\ Cases_on`s.MEM (n2w r1 + 3w)` \\ fs[]
  \\ Cases_on`s.MEM (n2w r1 + 7w)` \\ fs[]
  \\ Cases_on`s.MEM (n2w r1 + 5w)` \\ fs[]
  \\ Cases_on`s.MEM (n2w r1 + 4w)` \\ fs[]
  \\ simp[w2w_n2w]
  \\ DEP_REWRITE_TAC[LESS_MOD]
  \\ qspecl_then[`7`,`0`]mp_tac bitTheory.BITSLT_THM
  \\ rw[]
  \\ TRY (
    qmatch_goalsub_rename_tac`BITS 7 0 m < _`
    \\ first_x_assum(qspec_then`m`mp_tac)
    \\ rw[] )
  \\ rw[bitTheory.BITS_ZERO3]
  \\ Cases_on`n` \\ fs[]
  \\ Cases_on`n'` \\ fs[]
  \\ Cases_on`n''` \\ fs[]
  \\ Cases_on`n'''` \\ fs[]
  \\ Cases_on`n''''` \\ fs[]
  \\ Cases_on`n''''''` \\ fs[]
  \\ Cases_on`n'''''''` \\ fs[]
  \\ Cases_on`n'''''` \\ fs[]
  \\ Cases_on`n` \\ fs[]
  \\ Cases_on`n'` \\ fs[]
  \\ simp[ADD1]
  \\ simp[word_lt_n2w]
  \\ qspecl_then[`31`,`n+3`]mp_tac bitTheory.NOT_BIT_GT_TWOEXP
  \\ simp[]);

fun next_tac n =
  let
    val sn = mk_var("s"^(Int.toString n), ``:ag32_state``)
  in
    rw[Once EXISTS_NUM] \\ disj2_tac \\ rw[FUNPOW]
    \\ qmatch_goalsub_abbrev_tac`Next ^sn`
    \\ rw[ag32Theory.Next_def]
    \\ qmatch_goalsub_abbrev_tac`pc + 2w`
    \\ simp[GSYM get_mem_word_def]
    \\ `^sn.PC = s.PC + n2w(4 * ^(numSyntax.term_of_int n))`
    by ( simp[Abbr`^sn`,
              dfn'Normal_PC,
              dfn'LoadMEMByte_PC,
              dfn'Shift_PC,
              dfn'LoadConstant_PC] )
    \\ `byte_aligned ^sn.PC`
    by (
      simp[]
      \\ irule byte_aligned_add \\ simp[]
      \\ EVAL_TAC )
    \\ drule byte_aligned_imp
    \\ simp[]
    \\ disch_then kall_tac
    \\ qpat_x_assum`Abbrev(pc = _)`kall_tac
    \\ last_assum(qspec_then`^(numSyntax.term_of_int n)`mp_tac)
    \\ impl_tac >- EVAL_TAC
    \\ simp_tac(srw_ss())[ag32_ffi_write_check_conf_code_def,
                          ag32_ffi_write_load_noff_code_def,
                          ag32_ffi_write_check_lengths_code_def,
                          ag32_ffi_write_write_header_code_def,
                          ag32_ffi_write_num_written_code_def,
                          ag32_ffi_write_copy_code_def]
    \\ `^sn.MEM = s.MEM`
    by simp[Abbr`^sn`,
            dfn'Normal_MEM,
            dfn'LoadMEMByte_MEM,
            dfn'Shift_MEM,
            dfn'LoadConstant_MEM]
    \\ simp[]
    \\ disch_then kall_tac
    \\ simp[ag32_targetProofTheory.Decode_Encode]
    \\ simp[ag32Theory.Run_def]
  end

val ag32_ffi_write_check_conf_code_thm = Q.store_thm("ag32_ffi_write_check_conf_code_thm",
  `(∀k. k < LENGTH ag32_ffi_write_check_conf_code ⇒
        (get_mem_word s.MEM (s.PC + n2w (4 * k)) =
         Encode (EL k ag32_ffi_write_check_conf_code))) ∧ byte_aligned s.PC
   ⇒
   ∃k. (FUNPOW Next k s = ag32_ffi_write_check_conf s)`,
  rw[ag32_ffi_write_check_conf_def]
  \\ rw[Once EXISTS_NUM] \\ disj2_tac \\ rw[FUNPOW]
  \\ rw[ag32Theory.Next_def]
  \\ qmatch_goalsub_abbrev_tac`pc + 2w`
  \\ simp[GSYM get_mem_word_def]
  \\ first_assum(qspec_then`0`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ simp_tac(srw_ss())[]
  \\ imp_res_tac byte_aligned_imp \\ rfs[]
  \\ ntac 2 (pop_assum kall_tac)
  \\ disch_then kall_tac
  \\ simp[ag32_targetProofTheory.Decode_Encode]
  \\ simp[ag32_ffi_write_check_conf_code_def, ag32Theory.Run_def]
  \\ EVERY (List.tabulate(32, next_tac o (curry(op +)1)))
  \\ rw[Once EXISTS_NUM]);

val ag32_ffi_write_check_conf_MEM = Q.store_thm("ag32_ffi_write_check_conf_MEM",
  `(ag32_ffi_write_check_conf s).MEM = s.MEM`,
  rw[ag32_ffi_write_check_conf_def, dfn'Normal_MEM, dfn'LoadMEMByte_MEM]);

val ag32_ffi_write_check_conf_PC = Q.store_thm("ag32_ffi_write_check_conf_PC",
  `(ag32_ffi_write_check_conf s).PC = s.PC + 132w`,
  rw[ag32_ffi_write_check_conf_def, dfn'Normal_PC, dfn'LoadMEMByte_PC]);

val ag32_ffi_write_check_conf_R = Q.store_thm("ag32_ffi_write_check_conf_R",
  `((ag32_ffi_write_check_conf s).R 3w = s.R 3w) ∧
   ((ag32_ffi_write_check_conf s).R 5w = s.R 5w)`,
  rw[ag32_ffi_write_check_conf_def,
     ag32Theory.dfn'Normal_def, ag32Theory.ri2word_def,
     ag32Theory.incPC_def, ag32Theory.ALU_def, ag32Theory.norm_def,
     ag32Theory.dfn'LoadMEMByte_def, ag32Theory.dfn'Shift_def, ag32Theory.shift_def,
     ag32Theory.dfn'LoadConstant_def, ag32Theory.dfn'JumpIfZero_def,
     APPLY_UPDATE_THM]);

val ag32_ffi_write_load_noff_def = Define`
  ag32_ffi_write_load_noff s =
  let s = dfn'LoadMEMByte (1w, Reg 3w) s in
  let s = dfn'Shift (shiftLL, 1w, Reg 1w, Imm 8w) s in
  let s = dfn'Normal (fInc, 3w, Reg 3w, Imm 1w) s in
  let s = dfn'LoadMEMByte (8w, Reg 3w) s in
  let s = dfn'Normal (fXor, 1w, Reg 1w, Reg 8w) s in
  let s = dfn'Normal (fInc, 3w, Reg 3w, Imm 1w) s in
  let s = dfn'LoadMEMByte (7w, Reg 3w) s in
  let s = dfn'Shift (shiftLL, 7w, Reg 7w, Imm 8w) s in
  let s = dfn'Normal (fInc, 3w, Reg 3w, Imm 1w) s in
  let s = dfn'LoadMEMByte (8w, Reg 3w) s in
  let s = dfn'Normal (fXor, 7w, Reg 7w, Reg 8w) s in
  let s = dfn'Normal (fSub, 3w, Reg 3w, Imm 3w) s in
  s`;

val ag32_ffi_write_load_noff_thm = Q.store_thm("ag32_ffi_write_load_noff_thm",
  `bytes_in_memory (s.R 3w) (n1::n0::off1::off0::tll) s.MEM md
   ⇒
   ∃r8 ov cf.
   (ag32_ffi_write_load_noff s =
    s with <| PC := s.PC + n2w (4 * LENGTH ag32_ffi_write_load_noff_code);
              OverflowFlag := ov;
              CarryFlag := cf;
              R := ((8w =+ r8)
                   ((1w =+ n2w (w22n [n1; n0]))
                   ((7w =+ n2w (w22n [off1; off0])) s.R))) |>)`,
  rewrite_tac[ag32_ffi_write_load_noff_def]
  \\ strip_tac
  \\ simp_tac (srw_ss())
       [Q.SPECL[`1w`]ag32Theory.dfn'LoadMEMByte_def,
        ag32Theory.ri2word_def, ag32Theory.norm_def,
        ag32Theory.ALU_def, ag32Theory.incPC_def ]
  \\ CONV_TAC(PATH_CONV"rararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ simp_tac (srw_ss())
       [Q.SPECL[`shiftLL`,`1w`]ag32Theory.dfn'Shift_def,
        ag32Theory.ri2word_def, ag32Theory.norm_def,
        ag32Theory.shift_def,
        ag32Theory.ALU_def, ag32Theory.incPC_def ]
  \\ CONV_TAC(PATH_CONV"rararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ simp_tac (srw_ss())
       [Q.SPECL[`fInc`]ag32Theory.dfn'Normal_def,
        ag32Theory.ri2word_def, ag32Theory.norm_def,
        ag32Theory.ALU_def, ag32Theory.incPC_def ]
  \\ CONV_TAC(PATH_CONV"rararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ simp_tac (srw_ss())
       [Q.SPECL[`8w`]ag32Theory.dfn'LoadMEMByte_def,
        ag32Theory.ri2word_def, ag32Theory.norm_def,
        ag32Theory.ALU_def, ag32Theory.incPC_def ]
  \\ CONV_TAC(PATH_CONV"rararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ simp_tac (srw_ss())
       [Q.SPECL[`fXor`]ag32Theory.dfn'Normal_def,
        ag32Theory.ri2word_def, ag32Theory.norm_def,
        ag32Theory.ALU_def, ag32Theory.incPC_def ]
  \\ CONV_TAC(PATH_CONV"rararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ CONV_TAC(PATH_CONV"rararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ simp_tac (srw_ss())
       [Q.SPECL[`7w`]ag32Theory.dfn'LoadMEMByte_def,
        ag32Theory.ri2word_def, ag32Theory.norm_def,
        ag32Theory.ALU_def, ag32Theory.incPC_def ]
  \\ CONV_TAC(PATH_CONV"rararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ simp_tac (srw_ss())
       [Q.SPECL[`shiftLL`,`7w`]ag32Theory.dfn'Shift_def,
        ag32Theory.ri2word_def, ag32Theory.norm_def,
        ag32Theory.shift_def,
        ag32Theory.ALU_def, ag32Theory.incPC_def ]
  \\ CONV_TAC(PATH_CONV"rararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ CONV_TAC(PATH_CONV"rararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ CONV_TAC(PATH_CONV"rararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ CONV_TAC(PATH_CONV"rararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ CONV_TAC(PATH_CONV"rararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ simp_tac (srw_ss())
       [Q.SPECL[]ag32Theory.dfn'Normal_def,
        ag32Theory.ri2word_def, ag32Theory.norm_def,
        ag32Theory.shift_def,
        ag32Theory.ALU_def, ag32Theory.incPC_def ]
  \\ CONV_TAC(PATH_CONV"rararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ simp[ag32Theory.ag32_state_component_equality]
  \\ simp[FUN_EQ_THM, APPLY_UPDATE_THM]
  \\ qmatch_goalsub_abbrev_tac`if 8w = _ then r8 else _`
  \\ qexists_tac`r8`
  \\ conj_tac >- EVAL_TAC
  \\ rw[MarshallingTheory.w22n_def,Abbr`r8`] \\ fs[]
  >- (
    Cases_on`off0` \\ Cases_on`off1` \\ fs[]
    \\ fs[asmSemTheory.bytes_in_memory_def] \\ rw[]
    \\ simp[w2w_n2w]
    \\ simp[bitTheory.BITS_ZERO3]
    \\ rw[GSYM word_add_n2w, GSYM word_mul_n2w]
    \\ simp[WORD_MUL_LSL]
    \\ DEP_REWRITE_TAC[GSYM WORD_ADD_XOR]
    \\ match_mp_tac (blastLib.BBLAST_PROVE
        ``w1 <+ 256w ==> (0w = (w1 && 256w * w2:word32))``)
    \\ fs [WORD_LO] )
  \\ fs[asmSemTheory.bytes_in_memory_def]
  \\ rw[]
  \\ Cases_on`s.MEM (s.R 1w)` \\ fs[]
  \\ Cases_on`s.MEM (s.R 3w)` \\ fs[]
  \\ Cases_on`s.MEM (s.R 3w + 1w)` \\ fs[]
  \\ simp[WORD_MUL_LSL]
  \\ simp[w2w_n2w]
  \\ simp[bitTheory.BITS_ZERO3]
  \\ DEP_REWRITE_TAC[GSYM WORD_ADD_XOR]
  \\ simp[GSYM word_mul_n2w, GSYM word_add_n2w]
  \\ match_mp_tac (blastLib.BBLAST_PROVE
      ``w1 <+ 256w ==> (0w = (w1 && 256w * w2:word32))``)
  \\ fs [WORD_LO]);

val ag32_ffi_write_load_noff_code_thm = Q.store_thm("ag32_ffi_write_load_noff_code_thm",
  `(∀k. k < LENGTH ag32_ffi_write_load_noff_code ⇒
        (get_mem_word s.MEM (s.PC + n2w (4 * k)) =
         Encode (EL k ag32_ffi_write_load_noff_code))) ∧ byte_aligned s.PC
   ⇒
   ∃k. (FUNPOW Next k s = ag32_ffi_write_load_noff s)`,
  rw[ag32_ffi_write_load_noff_def]
  \\ rw[Once EXISTS_NUM] \\ disj2_tac \\ rw[FUNPOW]
  \\ rw[ag32Theory.Next_def]
  \\ qmatch_goalsub_abbrev_tac`pc + 2w`
  \\ simp[GSYM get_mem_word_def]
  \\ first_assum(qspec_then`0`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ simp_tac(srw_ss())[]
  \\ imp_res_tac byte_aligned_imp \\ rfs[]
  \\ ntac 2 (pop_assum kall_tac)
  \\ disch_then kall_tac
  \\ simp[ag32_targetProofTheory.Decode_Encode]
  \\ simp[ag32_ffi_write_load_noff_code_def, ag32Theory.Run_def]
  \\ EVERY (List.tabulate(11, next_tac o (curry(op +)1)))
  \\ rw[Once EXISTS_NUM]);

val ag32_ffi_write_load_noff_MEM = Q.store_thm("ag32_ffi_write_load_noff_MEM",
  `(ag32_ffi_write_load_noff s).MEM = s.MEM`,
  rw[ag32_ffi_write_load_noff_def, dfn'Normal_MEM, dfn'LoadMEMByte_MEM, dfn'Shift_MEM]);

val ag32_ffi_write_load_noff_PC = Q.store_thm("ag32_ffi_write_load_noff_PC",
  `(ag32_ffi_write_load_noff s).PC = s.PC + 48w`,
  rw[ag32_ffi_write_load_noff_def, dfn'Normal_PC, dfn'LoadMEMByte_PC, dfn'Shift_PC]);

val ag32_ffi_write_load_noff_R = Q.store_thm("ag32_ffi_write_load_noff_R",
  `((ag32_ffi_write_load_noff s).R 3w = s.R 3w) ∧
   ((ag32_ffi_write_load_noff s).R 5w = s.R 5w)`,
  rw[ag32_ffi_write_load_noff_def,
     ag32Theory.dfn'Normal_def, ag32Theory.ri2word_def,
     ag32Theory.incPC_def, ag32Theory.ALU_def, ag32Theory.norm_def,
     ag32Theory.dfn'LoadMEMByte_def, ag32Theory.dfn'Shift_def, ag32Theory.shift_def,
     ag32Theory.dfn'LoadConstant_def, ag32Theory.dfn'JumpIfZero_def,
     APPLY_UPDATE_THM]);

val ag32_ffi_write_check_lengths_def = Define`
  ag32_ffi_write_check_lengths s =
  let s = dfn'Normal (fLower, 8w, Reg 4w, Reg 7w) s in
  let s = dfn'Normal (fSub, 8w, Imm 1w, Reg 8w) s in
  let s = dfn'Normal (fAnd, 6w, Reg 6w, Reg 8w) s in
  let s = dfn'Normal (fSub, 4w, Reg 4w, Reg 7w) s in
  let s = dfn'Normal (fLower, 8w, Reg 4w, Reg 1w) s in
  let s = dfn'Normal (fSub, 8w, Imm 1w, Reg 8w) s in
  let s = dfn'LoadConstant (4w, F, 4w * 36w) s in
  let s = dfn'JumpIfZero (fAnd, Reg 4w, Reg 6w, Reg 8w) s in
  s`;

val ag32_ffi_write_check_lengths_thm = Q.store_thm("ag32_ffi_write_check_lengths_thm",
  `(s.R 4w = n2w ltll) ∧ (s.R 7w = n2w off) ∧ (s.R 1w = n2w n) ∧ (s.R 6w = v2w [cnd]) ∧
   off < dimword(:16) ∧ n < dimword(:16) ∧ ltll < dimword (:32)
   ⇒
   ∃r4 r6 r8 cf ov.
   (ag32_ffi_write_check_lengths s =
    s with <| PC := if cnd ∧ off ≤ ltll ∧ n ≤ ltll - off
                    then s.PC + n2w (4 * LENGTH ag32_ffi_write_check_lengths_code)
                    else s.PC + n2w (4 * (LENGTH ag32_ffi_write_check_lengths_code + 35)) ;
              R := ((8w =+ r8)
                   ((4w =+ r4)
                   ((6w =+ r6) s.R)));
              CarryFlag := cf;
              OverflowFlag := ov |>)`,
  strip_tac
  \\ simp[ag32_ffi_write_check_lengths_def]
  \\ simp[ag32Theory.dfn'Normal_def, ag32Theory.ri2word_def,
          ag32Theory.norm_def, ag32Theory.ALU_def, ag32Theory.incPC_def,
          ag32Theory.dfn'LoadConstant_def, APPLY_UPDATE_THM]
  \\ simp[ag32Theory.dfn'JumpIfZero_def,ag32Theory.ri2word_def,
          ag32Theory.ALU_def,ag32Theory.incPC_def,APPLY_UPDATE_THM]
  \\ qmatch_goalsub_abbrev_tac`COND b1`
  \\ qmatch_goalsub_abbrev_tac`if b2 then _  + _ else _`
  \\ `b1 = ¬b2`
  by (
    unabbrev_all_tac
    \\ Cases_on`cnd` \\ fs[]
    \\ simp[NOT_LESS_EQUAL]
    \\ fs [WORD_LO]
    \\ Cases_on `ltll < off` \\ fs []
    \\ fs [NOT_LESS]
    \\ simp_tac std_ss [addressTheory.WORD_SUB_INTRO,addressTheory.word_arith_lemma2]
    \\ fs [] \\ rw [v2w_sing])
  \\ qpat_x_assum`Abbrev(b1 = _)`kall_tac
  \\ simp[] \\ rveq
  \\ IF_CASES_TAC
  \\ simp[ag32Theory.ag32_state_component_equality]
  \\ simp[ag32_ffi_write_check_lengths_code_def]
  \\ rw[FUN_EQ_THM, APPLY_UPDATE_THM]
  \\ qmatch_goalsub_abbrev_tac`if 4w = _ then r4 else _`
  \\ qexists_tac`r4`
  \\ qmatch_goalsub_abbrev_tac`if 6w = _ then r6 else _`
  \\ qexists_tac`r6`
  \\ qmatch_goalsub_abbrev_tac`if 8w = _ then r8 else _`
  \\ qexists_tac`r8`
  \\ rw[] \\ fs[]);

val ag32_ffi_write_check_lengths_code_thm = Q.store_thm("ag32_ffi_write_check_lengths_code_thm",
  `(∀k. k < LENGTH ag32_ffi_write_check_lengths_code ⇒
        (get_mem_word s.MEM (s.PC + n2w (4 * k)) =
         Encode (EL k ag32_ffi_write_check_lengths_code))) ∧ byte_aligned s.PC
   ⇒
   ∃k. (FUNPOW Next k s = ag32_ffi_write_check_lengths s)`,
  rw[ag32_ffi_write_check_lengths_def]
  \\ rw[Once EXISTS_NUM] \\ disj2_tac \\ rw[FUNPOW]
  \\ rw[ag32Theory.Next_def]
  \\ qmatch_goalsub_abbrev_tac`pc + 2w`
  \\ simp[GSYM get_mem_word_def]
  \\ first_assum(qspec_then`0`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ simp_tac(srw_ss())[]
  \\ imp_res_tac byte_aligned_imp \\ rfs[]
  \\ ntac 2 (pop_assum kall_tac)
  \\ disch_then kall_tac
  \\ simp[ag32_targetProofTheory.Decode_Encode]
  \\ simp[ag32_ffi_write_check_lengths_code_def, ag32Theory.Run_def]
  \\ EVERY (List.tabulate(7, next_tac o (curry(op +)1)))
  \\ rw[Once EXISTS_NUM]);

val ag32_ffi_write_check_lengths_MEM = Q.store_thm("ag32_ffi_write_check_lengths_MEM",
  `(ag32_ffi_write_check_lengths s).MEM = s.MEM`,
  rw[ag32_ffi_write_check_lengths_def, dfn'Normal_MEM, dfn'LoadConstant_MEM,
     dfn'JumpIfZero_MEM]);

val ag32_ffi_write_check_lengths_PC = Q.store_thm("ag32_ffi_write_check_lengths_PC",
  `(ag32_ffi_write_check_lengths s).PC ∈
    { s.PC + n2w (4 * LENGTH ag32_ffi_write_check_lengths_code );
      s.PC + n2w (4 * (LENGTH ag32_ffi_write_check_lengths_code + 35)) }`,
  reverse (
    rw[ag32_ffi_write_check_lengths_def, dfn'Normal_PC, dfn'LoadConstant_PC,
       ag32Theory.dfn'JumpIfZero_def, ag32Theory.ALU_def,
       ag32Theory.ri2word_def, ag32Theory.incPC_def ] )
  >- EVAL_TAC
  \\ rw[ag32Theory.dfn'LoadConstant_def, ag32Theory.incPC_def, APPLY_UPDATE_THM]
  \\ EVAL_TAC);

val ag32_ffi_write_check_lengths_R = Q.store_thm("ag32_ffi_write_check_lengths_R",
  `((ag32_ffi_write_check_lengths s).R 3w = s.R 3w) ∧
   ((ag32_ffi_write_check_lengths s).R 5w = s.R 5w)`,
  rw[ag32_ffi_write_check_lengths_def,
     ag32Theory.dfn'Normal_def, ag32Theory.ri2word_def,
     ag32Theory.incPC_def, ag32Theory.ALU_def, ag32Theory.norm_def,
     ag32Theory.dfn'LoadConstant_def, ag32Theory.dfn'JumpIfZero_def,
     APPLY_UPDATE_THM]);

val ag32_ffi_write_write_header_def = Define`
  ag32_ffi_write_write_header s =
  let s = dfn'LoadConstant(8w, F, n2w ((ffi_code_start_offset - 1) - output_offset)) s in
  let s = dfn'Normal (fSub, 5w, Reg 5w, Reg 8w) s in
  let s = dfn'StoreMEM (Imm 0w, Reg 5w) s in
  let s = dfn'Normal (fAdd, 5w, Reg 5w, Imm 4w) s in
  let s = dfn'Shift (shiftLL, 2w, Reg 2w, Imm 24w) s in
  let s = dfn'StoreMEM (Reg 2w, Reg 5w) s in
  let s = dfn'Normal (fAdd, 5w, Reg 5w, Imm 4w) s in
  let s = dfn'StoreMEMByte (Imm 0w, Reg 5w) s in
  let s = dfn'Normal (fInc, 5w, Reg 5w, Imm 1w) s in
  let s = dfn'StoreMEMByte (Imm 0w, Reg 5w) s in
  let s = dfn'Normal (fInc, 5w, Reg 5w, Imm 1w) s in
  let s = dfn'Shift (shiftLR, 2w, Reg 1w, Imm 8w) s in
  let s = dfn'StoreMEMByte (Reg 2w, Reg 5w) s in
  let s = dfn'Normal (fInc, 5w, Reg 5w, Imm 1w) s in
  let s = dfn'StoreMEMByte (Reg 1w, Reg 5w) s in
  let s = dfn'Normal (fInc, 5w, Reg 5w, Imm 1w) s in
  let s = dfn'StoreMEMByte (Imm 0w, Reg 3w) s in
  s`;

val ag32_ffi_write_write_header_thm = Q.store_thm("ag32_ffi_write_write_header_thm",
  `(s.R 5w = r0 + n2w (ffi_code_start_offset - 1)) ∧
    byte_aligned r0 ∧ w2n r0 + memory_size < dimword(:32) ∧
   (LENGTH conf = 8) ∧ (w82n conf < 3) ∧ (s.R 2w = n2w (w82n conf)) ∧
   (s.R 1w = n2w (w22n [n1; n0])) ∧ (s.R 3w ≠ r0 + n2w output_offset)
   ⇒
   ∃r2 r8 ov cf.
   (ag32_ffi_write_write_header s =
    s with <| PC := s.PC + n2w (4 * LENGTH ag32_ffi_write_write_header_code);
              R := ((5w =+ r0 + n2w (output_offset + 12))
                   ((8w =+ r8)
                   ((2w =+ r2) s.R)));
              MEM :=
                (((s.R 3w) =+ 0w)
                 (asm_write_bytearray (r0 + n2w output_offset) (conf ++ [0w; 0w; n1; n0]) s.MEM));
              OverflowFlag := ov;
              CarryFlag := cf |>)`,
  rewrite_tac[ag32_ffi_write_write_header_def]
  \\ strip_tac
  \\ simp_tac (srw_ss())
       [Q.SPECL[]ag32Theory.dfn'LoadConstant_def,
        ag32Theory.ri2word_def, ag32Theory.norm_def,
        ag32Theory.ALU_def, ag32Theory.incPC_def ]
  \\ CONV_TAC(PATH_CONV"rarararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ simp_tac (srw_ss())
       [Q.SPECL[`fSub`,`5w`]ag32Theory.dfn'Normal_def,
        ag32Theory.ri2word_def, ag32Theory.norm_def,
        ag32Theory.shift_def,
        ag32Theory.ALU_def, ag32Theory.incPC_def ]
  \\ CONV_TAC(PATH_CONV"rarararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ simp_tac (srw_ss())
       [Q.SPECL[]ag32Theory.dfn'StoreMEM_def,
        ag32Theory.ri2word_def, ag32Theory.norm_def,
        ag32Theory.ALU_def, ag32Theory.incPC_def ]
  \\ CONV_TAC(PATH_CONV"rarararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ qmatch_goalsub_abbrev_tac`adr + 2w`
  \\ `adr = r0 + n2w output_offset`
  by (
    simp[Abbr`adr`]
    \\ EVAL_TAC
    \\ blastLib.BBLAST_TAC
    \\ fs[alignmentTheory.byte_aligned_def, alignmentTheory.aligned_bitwise_and]
    \\ blastLib.FULL_BBLAST_TAC )
  \\ qpat_x_assum`Abbrev(adr = _)`kall_tac
  \\ qmatch_goalsub_rename_tac`_ with OverflowFlag := ov`
  \\ asm_simp_tac (srw_ss())[]
  \\ qmatch_goalsub_abbrev_tac`5w =+ r5`
  \\ `r5 = r0 + n2w output_offset`
  by ( simp[Abbr`r5`] \\ EVAL_TAC \\ simp[] )
  \\ qpat_x_assum`Abbrev(r5 = _)`kall_tac \\ rveq
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ simp_tac (srw_ss())
       [Q.SPECL[`fAdd`]ag32Theory.dfn'Normal_def,
        ag32Theory.ri2word_def, ag32Theory.norm_def,
        ag32Theory.ALU_def, ag32Theory.incPC_def ]
  \\ CONV_TAC(PATH_CONV"rarararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ simp_tac (srw_ss())
       [Q.SPECL[`shiftLL`]ag32Theory.dfn'Shift_def,
        ag32Theory.ri2word_def, ag32Theory.norm_def,
        ag32Theory.shift_def,
        ag32Theory.ALU_def, ag32Theory.incPC_def ]
  \\ CONV_TAC(PATH_CONV"rarararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ CONV_TAC(PATH_CONV"rarararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ qmatch_goalsub_abbrev_tac`adr + 2w`
  \\ `adr = r0 + n2w (output_offset + 4)`
  by (
    simp[Abbr`adr`]
    \\ EVAL_TAC
    \\ blastLib.BBLAST_TAC
    \\ fs[alignmentTheory.byte_aligned_def, alignmentTheory.aligned_bitwise_and]
    \\ blastLib.FULL_BBLAST_TAC )
  \\ qpat_x_assum`Abbrev(adr = _)`kall_tac \\ rveq
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ CONV_TAC(PATH_CONV"rarararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ simp_tac (srw_ss())
       [Q.SPECL[]ag32Theory.dfn'StoreMEMByte_def,
        ag32Theory.ri2word_def, ag32Theory.norm_def,
        ag32Theory.shift_def,
        ag32Theory.ALU_def, ag32Theory.incPC_def ]
  \\ CONV_TAC(PATH_CONV"rarararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ simp_tac (srw_ss())
       [Q.SPECL[`fInc`]ag32Theory.dfn'Normal_def,
        ag32Theory.ri2word_def, ag32Theory.norm_def,
        ag32Theory.ALU_def, ag32Theory.incPC_def ]
  \\ CONV_TAC(PATH_CONV"rarararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ CONV_TAC(PATH_CONV"rarararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ CONV_TAC(PATH_CONV"rarararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ simp_tac (srw_ss())
       [Q.SPECL[]ag32Theory.dfn'Shift_def,
        ag32Theory.ri2word_def, ag32Theory.norm_def,
        ag32Theory.shift_def,
        ag32Theory.ALU_def, ag32Theory.incPC_def ]
  \\ CONV_TAC(PATH_CONV"rarararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ CONV_TAC(PATH_CONV"rarararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ CONV_TAC(PATH_CONV"rarararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ CONV_TAC(PATH_CONV"rarararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ CONV_TAC(PATH_CONV"rarararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ CONV_TAC(PATH_CONV"rarararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ simp[APPLY_UPDATE_THM]
  \\ simp[ag32Theory.ag32_state_component_equality, APPLY_UPDATE_THM]
  \\ simp[ag32_ffi_write_write_header_code_def]
  \\ rw[FUN_EQ_THM, APPLY_UPDATE_THM]
  \\ qmatch_goalsub_abbrev_tac`if 2w = _ then r2 else _`
  \\ qmatch_goalsub_abbrev_tac`if 8w = _ then r8 else _`
  \\ qexists_tac`r2`
  \\ qexists_tac`r8`
  \\ reverse conj_tac
  >- ( rw[] \\ fs[] \\ rw[GSYM word_add_n2w] )
  \\ fs[LENGTH_EQ_NUM_compute]
  \\ rveq
  \\ simp[lab_to_targetProofTheory.asm_write_bytearray_def, APPLY_UPDATE_THM]
  \\ simp[EVAL``output_offset``]
  \\ Cases_on`r0` \\ fs[memory_size_def, word_add_n2w]
  \\ Cases
  \\ IF_CASES_TAC >- fs[]
  \\ simp_tac std_ss []
  \\ IF_CASES_TAC
  >- (
    full_simp_tac std_ss [n2w_11] \\ rfs[]
    \\ simp[MarshallingTheory.w22n_def, GSYM word_add_n2w, GSYM word_mul_n2w]
    \\ Cases_on`n0` \\ fs[] \\ rveq
    \\ blastLib.BBLAST_TAC )
  \\ IF_CASES_TAC
  >- (
    full_simp_tac std_ss [n2w_11] \\ rfs[Abbr`r2`]
    \\ simp[MarshallingTheory.w22n_def, GSYM word_add_n2w, GSYM word_mul_n2w]
    \\ Cases_on`n1` \\ fs[] \\ rveq
    \\ fs [GSYM w2w_def]
    \\ match_mp_tac (blastLib.BBLAST_PROVE
        ``w <+ 256w:word32 /\ (k = w2w w) ==> ((7 >< 0)
          ((256w * w + w2w (n0:word8)) ⋙ 8) = k:word8)``)
    \\ fs [w2w_def,WORD_LO])
  \\ IF_CASES_TAC
  >- ( full_simp_tac std_ss [n2w_11] \\ rfs[] )
  \\ IF_CASES_TAC
  >- ( full_simp_tac std_ss [n2w_11] \\ rfs[] )
  \\ IF_CASES_TAC
  >- (
    full_simp_tac std_ss [n2w_11] \\ rfs[]
    \\ fs[MarshallingTheory.w82n_def]
    \\ Cases_on`h` \\ fs[] \\ rveq \\ Cases_on`n''` \\ fs[]
    \\ Cases_on`h'` \\ fs[] \\ rveq \\ Cases_on`n'` \\ fs[]
    \\ Cases_on`h''` \\ fs[] \\ rveq \\ Cases_on`n'` \\ fs[]
    \\ Cases_on`h'''` \\ fs[] \\ rveq \\ Cases_on`n'` \\ fs[]
    \\ Cases_on`h''''` \\ fs[] \\ rveq \\ Cases_on`n'` \\ fs[]
    \\ Cases_on`h'''''` \\ fs[] \\ rveq \\ Cases_on`n'` \\ fs[]
    \\ Cases_on`h''''''` \\ fs[] \\ rveq \\ Cases_on`n'` \\ fs[]
    \\ Cases_on`h'''''''` \\ fs[] \\ rw[]
    \\ match_mp_tac (blastLib.BBLAST_PROVE
         ``w <+ 256w:word32 /\ (k = w2w w) ==> ((31 >< 24) (w ≪ 24) = k:word8)``)
    \\ fs [WORD_LO,w2w_def])
  \\ IF_CASES_TAC
  >- (
    full_simp_tac std_ss [n2w_11] \\ rfs[]
    \\ fs[MarshallingTheory.w82n_def]
    \\ Cases_on`h` \\ fs[] \\ rveq \\ Cases_on`n''` \\ fs[]
    \\ Cases_on`h'` \\ fs[] \\ rveq \\ Cases_on`n'` \\ fs[]
    \\ Cases_on`h''` \\ fs[] \\ rveq \\ Cases_on`n'` \\ fs[]
    \\ Cases_on`h'''` \\ fs[] \\ rveq \\ Cases_on`n'` \\ fs[]
    \\ Cases_on`h''''` \\ fs[] \\ rveq \\ Cases_on`n'` \\ fs[]
    \\ Cases_on`h'''''` \\ fs[] \\ rveq \\ Cases_on`n'` \\ fs[]
    \\ Cases_on`h''''''` \\ fs[] \\ rveq \\ Cases_on`n'` \\ fs[]
    \\ Cases_on`h'''''''` \\ fs[] \\ rw[]
    \\ blastLib.BBLAST_TAC)
  \\ IF_CASES_TAC
  >- (
    full_simp_tac std_ss [n2w_11] \\ rfs[]
    \\ fs[MarshallingTheory.w82n_def]
    \\ Cases_on`h` \\ fs[] \\ rveq \\ Cases_on`n''` \\ fs[]
    \\ Cases_on`h'` \\ fs[] \\ rveq \\ Cases_on`n'` \\ fs[]
    \\ Cases_on`h''` \\ fs[] \\ rveq \\ Cases_on`n'` \\ fs[]
    \\ Cases_on`h'''` \\ fs[] \\ rveq \\ Cases_on`n'` \\ fs[]
    \\ Cases_on`h''''` \\ fs[] \\ rveq \\ Cases_on`n'` \\ fs[]
    \\ Cases_on`h'''''` \\ fs[] \\ rveq \\ Cases_on`n'` \\ fs[]
    \\ Cases_on`h''''''` \\ fs[] \\ rveq \\ Cases_on`n'` \\ fs[]
    \\ Cases_on`h'''''''` \\ fs[] \\ rw[]
    \\ blastLib.BBLAST_TAC)
  \\ IF_CASES_TAC
  >- (
    full_simp_tac std_ss [n2w_11] \\ rfs[]
    \\ fs[MarshallingTheory.w82n_def]
    \\ Cases_on`h` \\ fs[] \\ rveq \\ Cases_on`n''` \\ fs[]
    \\ Cases_on`h'` \\ fs[] \\ rveq \\ Cases_on`n'` \\ fs[]
    \\ Cases_on`h''` \\ fs[] \\ rveq \\ Cases_on`n'` \\ fs[]
    \\ Cases_on`h'''` \\ fs[] \\ rveq \\ Cases_on`n'` \\ fs[]
    \\ Cases_on`h''''` \\ fs[] \\ rveq \\ Cases_on`n'` \\ fs[]
    \\ Cases_on`h'''''` \\ fs[] \\ rveq \\ Cases_on`n'` \\ fs[]
    \\ Cases_on`h''''''` \\ fs[] \\ rveq \\ Cases_on`n'` \\ fs[]
    \\ Cases_on`h'''''''` \\ fs[] \\ rw[]
    \\ blastLib.BBLAST_TAC)
  \\ IF_CASES_TAC
  >- (
    full_simp_tac std_ss [n2w_11] \\ rfs[]
    \\ fs[MarshallingTheory.w82n_def]
    \\ Cases_on`h` \\ fs[] \\ rveq \\ Cases_on`n''` \\ fs[]
    \\ Cases_on`h'` \\ fs[] \\ rveq \\ Cases_on`n'` \\ fs[]
    \\ Cases_on`h''` \\ fs[] \\ rveq \\ Cases_on`n'` \\ fs[]
    \\ Cases_on`h'''` \\ fs[] \\ rveq \\ Cases_on`n'` \\ fs[] )
  \\ IF_CASES_TAC
  >- (
    full_simp_tac std_ss [n2w_11] \\ rfs[]
    \\ fs[MarshallingTheory.w82n_def]
    \\ Cases_on`h` \\ fs[] \\ rveq \\ Cases_on`n''` \\ fs[]
    \\ Cases_on`h'` \\ fs[] \\ rveq \\ Cases_on`n'` \\ fs[]
    \\ Cases_on`h''` \\ fs[] \\ rveq \\ Cases_on`n'` \\ fs[] )
  \\ IF_CASES_TAC
  >- (
    full_simp_tac std_ss [n2w_11] \\ rfs[]
    \\ fs[MarshallingTheory.w82n_def]
    \\ Cases_on`h` \\ fs[] \\ rveq \\ Cases_on`n''` \\ fs[]
    \\ Cases_on`h'` \\ fs[] \\ rveq \\ Cases_on`n'` \\ fs[] )
  \\ IF_CASES_TAC
  >- (
    full_simp_tac std_ss [n2w_11] \\ rfs[]
    \\ fs[MarshallingTheory.w82n_def]
    \\ Cases_on`h` \\ fs[] \\ rveq \\ Cases_on`n''` \\ fs[])
  \\ simp[]);

val ag32_ffi_write_write_header_code_thm = Q.store_thm("ag32_ffi_write_write_header_code_thm",
  `(∀k. k < LENGTH ag32_ffi_write_write_header_code ⇒
        (get_mem_word s.MEM (s.PC + n2w (4 * k)) =
         Encode (EL k ag32_ffi_write_write_header_code)))
   ∧ (s.PC = r0 +
       n2w (ffi_code_start_offset + ag32_ffi_write_entrypoint
            + 4 * (LENGTH ag32_ffi_write_set_id_code)
            + 4 * (LENGTH ag32_ffi_write_check_conf_code)
            + 4 * (LENGTH ag32_ffi_write_load_noff_code)
            + 4 * (LENGTH ag32_ffi_write_check_lengths_code)))
   ∧ (s.R 5w = r0 + n2w (ffi_code_start_offset - 1)) ∧ byte_aligned r0
   ∧ w2n r0 + memory_size < dimword(:32)
   ⇒
   ∃k. (FUNPOW Next k s = ag32_ffi_write_write_header s)`,
  rw[ag32_ffi_write_write_header_def]
  \\ rw[Once EXISTS_NUM] \\ disj2_tac \\ rw[FUNPOW]
  \\ rw[ag32Theory.Next_def]
  \\ qmatch_goalsub_abbrev_tac`pc + 2w`
  \\ simp[GSYM get_mem_word_def]
  \\ first_assum(qspec_then`0`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ simp_tac(srw_ss())[]
  \\ pop_assum mp_tac
  \\ DEP_REWRITE_TAC[byte_aligned_imp]
  \\ conj_asm1_tac
  >- ( irule byte_aligned_add \\ simp[] \\ EVAL_TAC )
  \\ strip_tac \\ fs[] \\ rveq
  \\ disch_then kall_tac
  \\ simp[ag32_targetProofTheory.Decode_Encode]
  \\ simp[ag32_ffi_write_write_header_code_def, ag32Theory.Run_def]
  \\ EVERY (List.tabulate(2, next_tac o (curry(op +)1)))
  \\ rw[Once EXISTS_NUM] \\ disj2_tac \\ rw[FUNPOW]
  \\ qmatch_goalsub_abbrev_tac`Next s3`
  \\ rw[ag32Theory.Next_def]
  \\ qmatch_goalsub_abbrev_tac`pc + 2w`
  \\ simp[GSYM get_mem_word_def]
  \\ `s3.PC = s.PC + n2w(4 * 3)`
  by ( simp[Abbr`s3`, ag32Theory.dfn'StoreMEM_def, ag32Theory.incPC_def] )
  \\ `byte_aligned s3.PC`
  by (
    simp[]
    \\ irule byte_aligned_add \\ simp[]
    \\ EVAL_TAC )
  \\ drule byte_aligned_imp
  \\ simp[]
  \\ disch_then kall_tac
  \\ qpat_x_assum`Abbrev(pc = _)`kall_tac
  \\ first_assum(qspec_then`3`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ simp_tac(srw_ss())[ag32_ffi_write_write_header_code_def]
  \\ `s3.R 5w = r0 + n2w (output_offset)`
  by ( simp[Abbr`s3`, ag32Theory.dfn'StoreMEM_def, ag32Theory.incPC_def]
       \\ simp[Abbr`s2`,
               ag32Theory.dfn'Normal_def,
               ag32Theory.incPC_def,
               ag32Theory.ri2word_def,
               ag32Theory.norm_def,
               ag32Theory.ALU_def, APPLY_UPDATE_THM]
       \\ simp[Abbr`s1`, ag32Theory.dfn'LoadConstant_def, ag32Theory.incPC_def, APPLY_UPDATE_THM]
       \\ EVAL_TAC \\ simp[] )
  \\ `∀k. k < LENGTH ag32_ffi_write_write_header_code ⇒
    (get_mem_word s3.MEM (s.PC + n2w (4 * k)) =
     get_mem_word s.MEM (s.PC + n2w (4 * k)))`
  by (
    gen_tac \\ strip_tac
    \\ simp[get_mem_word_def]
    \\ qpat_x_assum`s3.R _  = _`mp_tac
    \\ simp[Abbr`s3`]
    \\ simp[ag32Theory.dfn'StoreMEM_def,
            ag32Theory.incPC_def,
            ag32Theory.ri2word_def]
    \\ DEP_REWRITE_TAC[byte_aligned_imp]
    \\ conj_tac >- (
      irule byte_aligned_add
      \\ simp[]
      \\ EVAL_TAC )
    \\ strip_tac
    \\ simp[APPLY_UPDATE_THM]
    \\ qpat_x_assum`k < _` mp_tac
    \\ CONV_TAC(LAND_CONV EVAL)
    \\ qpat_x_assum`Abbrev(s.PC = _)`mp_tac
    \\ CONV_TAC(LAND_CONV EVAL)
    \\ simp[markerTheory.Abbrev_def]
    \\ ntac 2 strip_tac
    \\ simp[EVAL``output_offset``]
    \\ Cases_on`r0` \\ fs[memory_size_def, word_add_n2w]
    \\ first_x_assum(qspec_then`k`mp_tac)
    \\ impl_tac >- (EVAL_TAC \\ fs[])
    \\ disch_then(SUBST1_TAC o SYM)
    \\ simp[get_mem_word_def, word_add_n2w] )
  \\ first_assum(qspec_then`3`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ simp[]
  \\ ntac 2 (disch_then kall_tac)
  \\ simp[ag32_targetProofTheory.Decode_Encode]
  \\ simp[ag32Theory.Run_def]
  \\ rw[Once EXISTS_NUM] \\ disj2_tac \\ rw[FUNPOW]
  \\ qmatch_goalsub_abbrev_tac`Next s4`
  \\ rw[ag32Theory.Next_def]
  \\ qmatch_goalsub_abbrev_tac`pc + 2w`
  \\ simp[GSYM get_mem_word_def]
  \\ `s4.PC = s.PC + n2w(4 * 4)`
  by ( simp[Abbr`s4`, dfn'Normal_PC] )
  \\ `byte_aligned s4.PC`
  by (
    simp[]
    \\ irule byte_aligned_add \\ simp[]
    \\ EVAL_TAC )
  \\ drule byte_aligned_imp
  \\ simp[]
  \\ disch_then kall_tac
  \\ qpat_x_assum`Abbrev(pc = _)`kall_tac
  \\ first_assum(qspec_then`4`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ `s4.MEM = s3.MEM` by simp[Abbr`s4`, dfn'Normal_MEM]
  \\ simp[]
  \\ disch_then kall_tac
  \\ last_assum(qspec_then`4`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ simp_tac(srw_ss())[ag32_ffi_write_write_header_code_def]
  \\ disch_then kall_tac
  \\ simp[ag32_targetProofTheory.Decode_Encode]
  \\ simp[ag32Theory.Run_def]
  \\ rw[Once EXISTS_NUM] \\ disj2_tac \\ rw[FUNPOW]
  \\ qmatch_goalsub_abbrev_tac`Next s5`
  \\ rw[ag32Theory.Next_def]
  \\ qmatch_goalsub_abbrev_tac`pc + 2w`
  \\ simp[GSYM get_mem_word_def]
  \\ `s5.PC = s.PC + n2w(4 * 5)`
  by ( simp[Abbr`s5`, dfn'Shift_PC] )
  \\ `byte_aligned s5.PC`
  by (
    simp[]
    \\ irule byte_aligned_add \\ simp[]
    \\ EVAL_TAC )
  \\ drule byte_aligned_imp
  \\ simp[]
  \\ disch_then kall_tac
  \\ qpat_x_assum`Abbrev(pc = _)`kall_tac
  \\ first_assum(qspec_then`5`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ `s5.MEM = s3.MEM` by simp[Abbr`s5`, dfn'Shift_MEM]
  \\ simp[]
  \\ disch_then kall_tac
  \\ last_assum(qspec_then`5`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ simp_tac(srw_ss())[ag32_ffi_write_write_header_code_def]
  \\ disch_then kall_tac
  \\ simp[ag32_targetProofTheory.Decode_Encode]
  \\ simp[ag32Theory.Run_def]
  \\ rw[Once EXISTS_NUM] \\ disj2_tac \\ rw[FUNPOW]
  \\ qmatch_goalsub_abbrev_tac`Next s6`
  \\ rw[ag32Theory.Next_def]
  \\ qmatch_goalsub_abbrev_tac`pc + 2w`
  \\ simp[GSYM get_mem_word_def]
  \\ `s6.PC = s.PC + n2w(4 * 6)`
  by ( simp[Abbr`s6`, ag32Theory.dfn'StoreMEM_def, ag32Theory.incPC_def] )
  \\ `byte_aligned s6.PC`
  by (
    simp[]
    \\ irule byte_aligned_add \\ simp[]
    \\ EVAL_TAC )
  \\ drule byte_aligned_imp
  \\ simp[]
  \\ disch_then kall_tac
  \\ qpat_x_assum`Abbrev(pc = _)`kall_tac
  \\ first_assum(qspec_then`6`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ last_assum(qspec_then`6`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ simp_tac(srw_ss())[ag32_ffi_write_write_header_code_def]
  \\ disch_then kall_tac
  \\ `s5.R 5w = r0 + n2w (output_offset + 4)`
  by (
    simp[Abbr`s5`]
    \\ simp[ag32Theory.dfn'Shift_def,
            ag32Theory.incPC_def,
            ag32Theory.ri2word_def,
            ag32Theory.shift_def,
            ag32Theory.ALU_def, APPLY_UPDATE_THM]
    \\ simp[Abbr`s4`]
    \\ simp[ag32Theory.dfn'Normal_def,
            ag32Theory.incPC_def,
            ag32Theory.ri2word_def,
            ag32Theory.norm_def,
            ag32Theory.ALU_def, APPLY_UPDATE_THM]
    \\ simp[GSYM word_add_n2w])
  \\ `∀k. k < LENGTH ag32_ffi_write_write_header_code ⇒
    (get_mem_word s6.MEM (s.PC + n2w (4 * k)) =
     get_mem_word s3.MEM (s.PC + n2w (4 * k)))`
  by (
    gen_tac \\ strip_tac
    \\ simp[get_mem_word_def]
    \\ simp[Abbr`s6`]
    \\ simp[ag32Theory.dfn'StoreMEM_def,
            ag32Theory.incPC_def,
            ag32Theory.ri2word_def]
    \\ DEP_REWRITE_TAC[byte_aligned_imp]
    \\ conj_tac
    >- ( irule byte_aligned_add \\ simp[] \\ EVAL_TAC )
    \\ simp[APPLY_UPDATE_THM]
    \\ simp[EVAL``output_offset``]
    \\ qpat_x_assum`Abbrev(s.PC = _)`mp_tac
    \\ CONV_TAC(LAND_CONV EVAL)
    \\ simp[markerTheory.Abbrev_def]
    \\ strip_tac
    \\ Cases_on`r0` \\ fs[memory_size_def, word_add_n2w]
    \\ qpat_x_assum`k < _`mp_tac
    \\ CONV_TAC(LAND_CONV EVAL) \\ strip_tac
    \\ simp[]
    \\ first_x_assum(qspec_then`k`mp_tac)
    \\ impl_tac >- (EVAL_TAC \\ fs[])
    \\ first_x_assum(qspec_then`k`mp_tac)
    \\ impl_tac >- (EVAL_TAC \\ fs[])
    \\ disch_then(SUBST1_TAC o SYM)
    \\ disch_then(SUBST1_TAC o SYM)
    \\ simp[get_mem_word_def, word_add_n2w] )
  \\ first_assum(qspec_then`6`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ simp[]
  \\ ntac 2 (disch_then kall_tac)
  \\ simp[ag32_targetProofTheory.Decode_Encode]
  \\ simp[ag32Theory.Run_def]
  \\ rw[Once EXISTS_NUM] \\ disj2_tac \\ rw[FUNPOW]
  \\ qmatch_goalsub_abbrev_tac`Next s7`
  \\ rw[ag32Theory.Next_def]
  \\ qmatch_goalsub_abbrev_tac`pc + 2w`
  \\ simp[GSYM get_mem_word_def]
  \\ `s7.PC = s.PC + n2w(4 * 7)`
  by ( simp[Abbr`s7`, dfn'Normal_PC] )
  \\ `byte_aligned s7.PC`
  by (
    simp[]
    \\ irule byte_aligned_add \\ simp[]
    \\ EVAL_TAC )
  \\ drule byte_aligned_imp
  \\ simp[]
  \\ disch_then kall_tac
  \\ qpat_x_assum`Abbrev(pc = _)`kall_tac
  \\ first_assum(qspec_then`7`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ `s7.MEM = s6.MEM` by simp[Abbr`s7`, dfn'Normal_MEM]
  \\ simp[]
  \\ disch_then kall_tac
  \\ last_assum(qspec_then`7`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ simp_tac(srw_ss())[ag32_ffi_write_write_header_code_def]
  \\ qpat_assum`∀k. _ ⇒ (_ s3.MEM _ = _)`(qspec_then`7`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ simp[]
  \\ ntac 2 (disch_then kall_tac)
  \\ simp[ag32_targetProofTheory.Decode_Encode]
  \\ simp[ag32Theory.Run_def]
  \\ rw[Once EXISTS_NUM] \\ disj2_tac \\ rw[FUNPOW]
  \\ qmatch_goalsub_abbrev_tac`Next s8`
  \\ rw[ag32Theory.Next_def]
  \\ qmatch_goalsub_abbrev_tac`pc + 2w`
  \\ simp[GSYM get_mem_word_def]
  \\ `s8.PC = s.PC + n2w(4 * 8)`
  by ( simp[Abbr`s8`, ag32Theory.dfn'StoreMEMByte_def, ag32Theory.incPC_def] )
  \\ `byte_aligned s8.PC`
  by (
    simp[]
    \\ irule byte_aligned_add \\ simp[]
    \\ EVAL_TAC )
  \\ drule byte_aligned_imp
  \\ simp[]
  \\ disch_then kall_tac
  \\ qpat_x_assum`Abbrev(pc = _)`kall_tac
  \\ first_assum(qspec_then`8`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ qpat_assum`∀k. _ ⇒ (_ s3.MEM _ = _)`(qspec_then`8`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ last_assum(qspec_then`8`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ simp_tac(srw_ss())[ag32_ffi_write_write_header_code_def]
  \\ ntac 2 (disch_then kall_tac)
  \\ `s7.R 5w = r0 + n2w (output_offset + 8)`
  by (
    simp[Abbr`s7`]
    \\ simp[ag32Theory.dfn'Normal_def,
            ag32Theory.incPC_def,
            ag32Theory.ri2word_def,
            ag32Theory.norm_def,
            ag32Theory.ALU_def, APPLY_UPDATE_THM]
    \\ simp[Abbr`s6`]
    \\ simp[ag32Theory.dfn'StoreMEM_def, ag32Theory.incPC_def]
    \\ simp[GSYM word_add_n2w] )
  \\ `∀k. k < LENGTH ag32_ffi_write_write_header_code ⇒
    (get_mem_word s8.MEM (s.PC + n2w (4 * k)) =
     get_mem_word s6.MEM (s.PC + n2w (4 * k)))`
  by (
    gen_tac \\ strip_tac
    \\ simp[get_mem_word_def]
    \\ simp[Abbr`s8`]
    \\ simp[ag32Theory.dfn'StoreMEMByte_def,
            ag32Theory.incPC_def,
            ag32Theory.ri2word_def, APPLY_UPDATE_THM]
    \\ simp[EVAL``output_offset``]
    \\ qpat_x_assum`Abbrev(s.PC = _)`mp_tac
    \\ CONV_TAC(LAND_CONV EVAL)
    \\ simp[markerTheory.Abbrev_def]
    \\ strip_tac
    \\ Cases_on`r0` \\ fs[memory_size_def, word_add_n2w]
    \\ qpat_x_assum`k < _`mp_tac
    \\ CONV_TAC(LAND_CONV EVAL) \\ strip_tac
    \\ simp[]
    \\ first_x_assum(qspec_then`k`mp_tac)
    \\ impl_tac >- (EVAL_TAC \\ fs[])
    \\ first_x_assum(qspec_then`k`mp_tac)
    \\ impl_tac >- (EVAL_TAC \\ fs[])
    \\ first_x_assum(qspec_then`k`mp_tac)
    \\ impl_tac >- (EVAL_TAC \\ fs[])
    \\ disch_then(SUBST1_TAC o SYM)
    \\ disch_then(SUBST1_TAC o SYM)
    \\ disch_then(SUBST1_TAC o SYM)
    \\ simp[get_mem_word_def, word_add_n2w] )
  \\ first_assum(qspec_then`8`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ simp[]
  \\ ntac 2 (disch_then kall_tac)
  \\ simp[ag32_targetProofTheory.Decode_Encode]
  \\ simp[ag32Theory.Run_def]
  \\ rw[Once EXISTS_NUM] \\ disj2_tac \\ rw[FUNPOW]
  \\ qmatch_goalsub_abbrev_tac`Next s9`
  \\ rw[ag32Theory.Next_def]
  \\ qmatch_goalsub_abbrev_tac`pc + 2w`
  \\ simp[GSYM get_mem_word_def]
  \\ `s9.PC = s.PC + n2w(4 * 9)`
  by ( simp[Abbr`s9`, dfn'Normal_PC] )
  \\ `byte_aligned s9.PC`
  by (
    simp[]
    \\ irule byte_aligned_add \\ simp[]
    \\ EVAL_TAC )
  \\ drule byte_aligned_imp
  \\ simp[]
  \\ disch_then kall_tac
  \\ qpat_x_assum`Abbrev(pc = _)`kall_tac
  \\ first_assum(qspec_then`9`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ `s9.MEM = s8.MEM` by simp[Abbr`s9`, dfn'Normal_MEM]
  \\ simp[]
  \\ disch_then kall_tac
  \\ last_assum(qspec_then`9`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ simp_tac(srw_ss())[ag32_ffi_write_write_header_code_def]
  \\ qpat_assum`∀k. _ ⇒ (_ s3.MEM _ = _)`(qspec_then`9`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ simp[]
  \\ qpat_assum`∀k. _ ⇒ (_ s6.MEM _ = _)`(qspec_then`9`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ simp[]
  \\ ntac 3 (disch_then kall_tac)
  \\ simp[ag32_targetProofTheory.Decode_Encode]
  \\ simp[ag32Theory.Run_def]
  \\ rw[Once EXISTS_NUM] \\ disj2_tac \\ rw[FUNPOW]
  \\ qmatch_goalsub_abbrev_tac`Next s10`
  \\ rw[ag32Theory.Next_def]
  \\ qmatch_goalsub_abbrev_tac`pc + 2w`
  \\ simp[GSYM get_mem_word_def]
  \\ `s10.PC = s.PC + n2w(4 * 10)`
  by ( simp[Abbr`s10`, ag32Theory.dfn'StoreMEMByte_def, ag32Theory.incPC_def] )
  \\ `byte_aligned s10.PC`
  by (
    simp[]
    \\ irule byte_aligned_add \\ simp[]
    \\ EVAL_TAC )
  \\ drule byte_aligned_imp
  \\ simp[]
  \\ disch_then kall_tac
  \\ qpat_x_assum`Abbrev(pc = _)`kall_tac
  \\ first_assum(qspec_then`10`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ qpat_assum`∀k. _ ⇒ (_ s3.MEM _ = _)`(qspec_then`10`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ qpat_assum`∀k. _ ⇒ (_ s6.MEM _ = _)`(qspec_then`10`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ simp[]
  \\ last_assum(qspec_then`10`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ simp_tac(srw_ss())[ag32_ffi_write_write_header_code_def]
  \\ ntac 3 (disch_then kall_tac)
  \\ `s9.R 5w = r0 + n2w (output_offset + 9)`
  by (
    simp[Abbr`s9`]
    \\ simp[ag32Theory.dfn'Normal_def,
            ag32Theory.incPC_def,
            ag32Theory.ri2word_def,
            ag32Theory.norm_def,
            ag32Theory.ALU_def, APPLY_UPDATE_THM]
    \\ simp[Abbr`s8`]
    \\ simp[ag32Theory.dfn'StoreMEMByte_def, ag32Theory.incPC_def]
    \\ simp[GSYM word_add_n2w] )
  \\ `∀k. k < LENGTH ag32_ffi_write_write_header_code ⇒
    (get_mem_word s10.MEM (s.PC + n2w (4 * k)) =
     get_mem_word s8.MEM (s.PC + n2w (4 * k)))`
  by (
    gen_tac \\ strip_tac
    \\ simp[get_mem_word_def]
    \\ simp[Abbr`s10`]
    \\ simp[ag32Theory.dfn'StoreMEMByte_def,
            ag32Theory.incPC_def,
            ag32Theory.ri2word_def, APPLY_UPDATE_THM]
    \\ simp[EVAL``output_offset``]
    \\ qpat_x_assum`Abbrev(s.PC = _)`mp_tac
    \\ CONV_TAC(LAND_CONV EVAL)
    \\ simp[markerTheory.Abbrev_def]
    \\ strip_tac
    \\ Cases_on`r0` \\ fs[memory_size_def, word_add_n2w]
    \\ qpat_x_assum`k < _`mp_tac
    \\ CONV_TAC(LAND_CONV EVAL) \\ strip_tac
    \\ simp[]
    \\ first_x_assum(qspec_then`k`mp_tac)
    \\ impl_tac >- (EVAL_TAC \\ fs[])
    \\ first_x_assum(qspec_then`k`mp_tac)
    \\ impl_tac >- (EVAL_TAC \\ fs[])
    \\ first_x_assum(qspec_then`k`mp_tac)
    \\ impl_tac >- (EVAL_TAC \\ fs[])
    \\ first_x_assum(qspec_then`k`mp_tac)
    \\ impl_tac >- (EVAL_TAC \\ fs[])
    \\ disch_then(SUBST1_TAC o SYM)
    \\ disch_then(SUBST1_TAC o SYM)
    \\ disch_then(SUBST1_TAC o SYM)
    \\ disch_then(SUBST1_TAC o SYM)
    \\ simp[get_mem_word_def, word_add_n2w] )
  \\ first_assum(qspec_then`10`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ simp[]
  \\ ntac 2 (disch_then kall_tac)
  \\ simp[ag32_targetProofTheory.Decode_Encode]
  \\ simp[ag32Theory.Run_def]
  \\ rw[Once EXISTS_NUM] \\ disj2_tac \\ rw[FUNPOW]
  \\ qmatch_goalsub_abbrev_tac`Next s11`
  \\ rw[ag32Theory.Next_def]
  \\ qmatch_goalsub_abbrev_tac`pc + 2w`
  \\ simp[GSYM get_mem_word_def]
  \\ `s11.PC = s.PC + n2w(4 * 11)`
  by ( simp[Abbr`s11`, dfn'Normal_PC] )
  \\ `byte_aligned s11.PC`
  by (
    simp[]
    \\ irule byte_aligned_add \\ simp[]
    \\ EVAL_TAC )
  \\ drule byte_aligned_imp
  \\ simp[]
  \\ disch_then kall_tac
  \\ qpat_x_assum`Abbrev(pc = _)`kall_tac
  \\ first_assum(qspec_then`11`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ `s11.MEM = s10.MEM` by simp[Abbr`s11`, dfn'Normal_MEM]
  \\ simp[]
  \\ disch_then kall_tac
  \\ last_assum(qspec_then`11`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ simp_tac(srw_ss())[ag32_ffi_write_write_header_code_def]
  \\ qpat_assum`∀k. _ ⇒ (_ s3.MEM _ = _)`(qspec_then`11`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ simp[]
  \\ qpat_assum`∀k. _ ⇒ (_ s6.MEM _ = _)`(qspec_then`11`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ simp[]
  \\ qpat_assum`∀k. _ ⇒ (_ s8.MEM _ = _)`(qspec_then`11`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ simp[]
  \\ ntac 4 (disch_then kall_tac)
  \\ simp[ag32_targetProofTheory.Decode_Encode]
  \\ simp[ag32Theory.Run_def]
  \\ rw[Once EXISTS_NUM] \\ disj2_tac \\ rw[FUNPOW]
  \\ qmatch_goalsub_abbrev_tac`Next s12`
  \\ rw[ag32Theory.Next_def]
  \\ qmatch_goalsub_abbrev_tac`pc + 2w`
  \\ simp[GSYM get_mem_word_def]
  \\ `s12.PC = s.PC + n2w(4 * 12)`
  by ( simp[Abbr`s12`, dfn'Shift_PC])
  \\ `byte_aligned s12.PC`
  by (
    simp[]
    \\ irule byte_aligned_add \\ simp[]
    \\ EVAL_TAC )
  \\ drule byte_aligned_imp
  \\ simp[]
  \\ disch_then kall_tac
  \\ qpat_x_assum`Abbrev(pc = _)`kall_tac
  \\ first_assum(qspec_then`12`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ `s12.MEM = s10.MEM` by simp[Abbr`s12`, dfn'Shift_MEM]
  \\ qpat_assum`∀k. _ ⇒ (_ s3.MEM _ = _)`(qspec_then`12`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ qpat_assum`∀k. _ ⇒ (_ s6.MEM _ = _)`(qspec_then`12`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ qpat_assum`∀k. _ ⇒ (_ s8.MEM _ = _)`(qspec_then`12`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ last_assum(qspec_then`12`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ simp_tac(srw_ss())[ag32_ffi_write_write_header_code_def]
  \\ simp[]
  \\ ntac 5 (disch_then kall_tac)
  \\ simp[ag32_targetProofTheory.Decode_Encode]
  \\ simp[ag32Theory.Run_def]
  \\ rw[Once EXISTS_NUM] \\ disj2_tac \\ rw[FUNPOW]
  \\ qmatch_goalsub_abbrev_tac`Next s13`
  \\ rw[ag32Theory.Next_def]
  \\ qmatch_goalsub_abbrev_tac`pc + 2w`
  \\ simp[GSYM get_mem_word_def]
  \\ `s13.PC = s.PC + n2w(4 * 13)`
  by ( simp[Abbr`s13`, ag32Theory.dfn'StoreMEMByte_def, ag32Theory.incPC_def] )
  \\ `byte_aligned s13.PC`
  by (
    simp[]
    \\ irule byte_aligned_add \\ simp[]
    \\ EVAL_TAC )
  \\ drule byte_aligned_imp
  \\ simp[]
  \\ disch_then kall_tac
  \\ qpat_x_assum`Abbrev(pc = _)`kall_tac
  \\ first_assum(qspec_then`13`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ qpat_assum`∀k. _ ⇒ (_ s3.MEM _ = _)`(qspec_then`13`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ qpat_assum`∀k. _ ⇒ (_ s6.MEM _ = _)`(qspec_then`13`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ qpat_assum`∀k. _ ⇒ (_ s8.MEM _ = _)`(qspec_then`13`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ qpat_assum`∀k. _ ⇒ (_ s10.MEM _ = _)`(qspec_then`13`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ last_assum(qspec_then`13`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ simp_tac(srw_ss())[ag32_ffi_write_write_header_code_def]
  \\ disch_then kall_tac
  \\ `s12.R 5w = r0 + n2w (output_offset + 10)`
  by (
    simp[Abbr`s12`]
    \\ simp[ag32Theory.dfn'Shift_def,
            ag32Theory.incPC_def,
            ag32Theory.ri2word_def,
            ag32Theory.shift_def,
            ag32Theory.ALU_def, APPLY_UPDATE_THM]
    \\ simp[Abbr`s11`]
    \\ simp[ag32Theory.dfn'Normal_def,
            ag32Theory.incPC_def,
            ag32Theory.ri2word_def,
            ag32Theory.norm_def,
            ag32Theory.ALU_def, APPLY_UPDATE_THM]
    \\ simp[Abbr`s10`]
    \\ simp[ag32Theory.dfn'StoreMEMByte_def,
            ag32Theory.incPC_def,
            ag32Theory.ri2word_def,
            ag32Theory.ALU_def, APPLY_UPDATE_THM]
    \\ simp[GSYM word_add_n2w] )
  \\ `∀k. k < LENGTH ag32_ffi_write_write_header_code ⇒
    (get_mem_word s13.MEM (s.PC + n2w (4 * k)) =
     get_mem_word s10.MEM (s.PC + n2w (4 * k)))`
  by (
    gen_tac \\ strip_tac
    \\ simp[get_mem_word_def]
    \\ simp[Abbr`s13`]
    \\ simp[ag32Theory.dfn'StoreMEMByte_def,
            ag32Theory.incPC_def,
            ag32Theory.ri2word_def, APPLY_UPDATE_THM]
    \\ simp[EVAL``output_offset``]
    \\ qpat_x_assum`Abbrev(s.PC = _)`mp_tac
    \\ CONV_TAC(LAND_CONV EVAL)
    \\ simp[markerTheory.Abbrev_def]
    \\ strip_tac
    \\ Cases_on`r0` \\ fs[memory_size_def, word_add_n2w]
    \\ qpat_x_assum`k < _`mp_tac
    \\ CONV_TAC(LAND_CONV EVAL) \\ strip_tac
    \\ simp[]
    \\ first_x_assum(qspec_then`k`mp_tac)
    \\ impl_tac >- (EVAL_TAC \\ fs[])
    \\ first_x_assum(qspec_then`k`mp_tac)
    \\ impl_tac >- (EVAL_TAC \\ fs[])
    \\ first_x_assum(qspec_then`k`mp_tac)
    \\ impl_tac >- (EVAL_TAC \\ fs[])
    \\ first_x_assum(qspec_then`k`mp_tac)
    \\ impl_tac >- (EVAL_TAC \\ fs[])
    \\ first_x_assum(qspec_then`k`mp_tac)
    \\ impl_tac >- (EVAL_TAC \\ fs[])
    \\ disch_then(SUBST1_TAC o SYM)
    \\ disch_then(SUBST1_TAC o SYM)
    \\ disch_then(SUBST1_TAC o SYM)
    \\ disch_then(SUBST1_TAC o SYM)
    \\ disch_then(SUBST1_TAC o SYM)
    \\ simp[get_mem_word_def, word_add_n2w] )
  \\ first_assum(qspec_then`13`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ simp[]
  \\ ntac 5 (disch_then kall_tac)
  \\ simp[ag32_targetProofTheory.Decode_Encode]
  \\ simp[ag32Theory.Run_def]
  \\ rw[Once EXISTS_NUM] \\ disj2_tac \\ rw[FUNPOW]
  \\ qmatch_goalsub_abbrev_tac`Next s14`
  \\ rw[ag32Theory.Next_def]
  \\ qmatch_goalsub_abbrev_tac`pc + 2w`
  \\ simp[GSYM get_mem_word_def]
  \\ `s14.PC = s.PC + n2w(4 * 14)`
  by ( simp[Abbr`s14`, dfn'Normal_PC] )
  \\ `byte_aligned s14.PC`
  by (
    simp[]
    \\ irule byte_aligned_add \\ simp[]
    \\ EVAL_TAC )
  \\ drule byte_aligned_imp
  \\ simp[]
  \\ disch_then kall_tac
  \\ qpat_x_assum`Abbrev(pc = _)`kall_tac
  \\ first_assum(qspec_then`14`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ `s14.MEM = s13.MEM` by simp[Abbr`s14`, dfn'Normal_MEM]
  \\ simp[]
  \\ disch_then kall_tac
  \\ last_assum(qspec_then`14`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ simp_tac(srw_ss())[ag32_ffi_write_write_header_code_def]
  \\ qpat_assum`∀k. _ ⇒ (_ s3.MEM _ = _)`(qspec_then`14`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ simp[]
  \\ qpat_assum`∀k. _ ⇒ (_ s6.MEM _ = _)`(qspec_then`14`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ simp[]
  \\ qpat_assum`∀k. _ ⇒ (_ s8.MEM _ = _)`(qspec_then`14`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ simp[]
  \\ qpat_assum`∀k. _ ⇒ (_ s10.MEM _ = _)`(qspec_then`14`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ simp[]
  \\ ntac 5 (disch_then kall_tac)
  \\ simp[ag32_targetProofTheory.Decode_Encode]
  \\ simp[ag32Theory.Run_def]
  \\ rw[Once EXISTS_NUM] \\ disj2_tac \\ rw[FUNPOW]
  \\ qmatch_goalsub_abbrev_tac`Next s15`
  \\ rw[ag32Theory.Next_def]
  \\ qmatch_goalsub_abbrev_tac`pc + 2w`
  \\ simp[GSYM get_mem_word_def]
  \\ `s15.PC = s.PC + n2w(4 * 15)`
  by ( simp[Abbr`s15`, ag32Theory.dfn'StoreMEMByte_def, ag32Theory.incPC_def] )
  \\ `byte_aligned s15.PC`
  by (
    simp[]
    \\ irule byte_aligned_add \\ simp[]
    \\ EVAL_TAC )
  \\ drule byte_aligned_imp
  \\ simp[]
  \\ disch_then kall_tac
  \\ qpat_x_assum`Abbrev(pc = _)`kall_tac
  \\ first_assum(qspec_then`15`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ qpat_assum`∀k. _ ⇒ (_ s3.MEM _ = _)`(qspec_then`15`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ qpat_assum`∀k. _ ⇒ (_ s6.MEM _ = _)`(qspec_then`15`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ qpat_assum`∀k. _ ⇒ (_ s8.MEM _ = _)`(qspec_then`15`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ qpat_assum`∀k. _ ⇒ (_ s10.MEM _ = _)`(qspec_then`15`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ qpat_assum`∀k. _ ⇒ (_ s13.MEM _ = _)`(qspec_then`15`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ last_assum(qspec_then`15`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ simp_tac(srw_ss())[ag32_ffi_write_write_header_code_def]
  \\ disch_then kall_tac
  \\ `s14.R 5w = r0 + n2w (output_offset + 11)`
  by (
    simp[Abbr`s14`]
    \\ simp[ag32Theory.dfn'Normal_def,
            ag32Theory.incPC_def,
            ag32Theory.ri2word_def,
            ag32Theory.norm_def,
            ag32Theory.ALU_def, APPLY_UPDATE_THM]
    \\ simp[Abbr`s13`]
    \\ simp[ag32Theory.dfn'StoreMEMByte_def,
            ag32Theory.incPC_def,
            ag32Theory.ri2word_def,
            ag32Theory.ALU_def, APPLY_UPDATE_THM]
    \\ simp[GSYM word_add_n2w] )
  \\ `∀k. k < LENGTH ag32_ffi_write_write_header_code ⇒
    (get_mem_word s15.MEM (s.PC + n2w (4 * k)) =
     get_mem_word s13.MEM (s.PC + n2w (4 * k)))`
  by (
    gen_tac \\ strip_tac
    \\ simp[get_mem_word_def]
    \\ simp[Abbr`s15`]
    \\ simp[ag32Theory.dfn'StoreMEMByte_def,
            ag32Theory.incPC_def,
            ag32Theory.ri2word_def, APPLY_UPDATE_THM]
    \\ simp[EVAL``output_offset``]
    \\ qpat_x_assum`Abbrev(s.PC = _)`mp_tac
    \\ CONV_TAC(LAND_CONV EVAL)
    \\ simp[markerTheory.Abbrev_def]
    \\ strip_tac
    \\ Cases_on`r0` \\ fs[memory_size_def, word_add_n2w]
    \\ qpat_x_assum`k < _`mp_tac
    \\ CONV_TAC(LAND_CONV EVAL) \\ strip_tac
    \\ simp[]
    \\ first_x_assum(qspec_then`k`mp_tac)
    \\ impl_tac >- (EVAL_TAC \\ fs[])
    \\ first_x_assum(qspec_then`k`mp_tac)
    \\ impl_tac >- (EVAL_TAC \\ fs[])
    \\ first_x_assum(qspec_then`k`mp_tac)
    \\ impl_tac >- (EVAL_TAC \\ fs[])
    \\ first_x_assum(qspec_then`k`mp_tac)
    \\ impl_tac >- (EVAL_TAC \\ fs[])
    \\ first_x_assum(qspec_then`k`mp_tac)
    \\ impl_tac >- (EVAL_TAC \\ fs[])
    \\ first_x_assum(qspec_then`k`mp_tac)
    \\ impl_tac >- (EVAL_TAC \\ fs[])
    \\ disch_then(SUBST1_TAC o SYM)
    \\ disch_then(SUBST1_TAC o SYM)
    \\ disch_then(SUBST1_TAC o SYM)
    \\ disch_then(SUBST1_TAC o SYM)
    \\ disch_then(SUBST1_TAC o SYM)
    \\ disch_then(SUBST1_TAC o SYM)
    \\ simp[get_mem_word_def, word_add_n2w] )
  \\ first_assum(qspec_then`15`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ simp[]
  \\ ntac 6 (disch_then kall_tac)
  \\ simp[ag32_targetProofTheory.Decode_Encode]
  \\ simp[ag32Theory.Run_def]
  \\ rw[Once EXISTS_NUM] \\ disj2_tac \\ rw[FUNPOW]
  \\ qmatch_goalsub_abbrev_tac`Next s16`
  \\ rw[ag32Theory.Next_def]
  \\ qmatch_goalsub_abbrev_tac`pc + 2w`
  \\ simp[GSYM get_mem_word_def]
  \\ `s16.PC = s.PC + n2w(4 * 16)`
  by ( simp[Abbr`s16`, dfn'Normal_PC] )
  \\ `byte_aligned s16.PC`
  by (
    simp[]
    \\ irule byte_aligned_add \\ simp[]
    \\ EVAL_TAC )
  \\ drule byte_aligned_imp
  \\ simp[]
  \\ disch_then kall_tac
  \\ qpat_x_assum`Abbrev(pc = _)`kall_tac
  \\ first_assum(qspec_then`16`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ `s16.MEM = s15.MEM` by simp[Abbr`s16`, dfn'Normal_MEM]
  \\ simp[]
  \\ disch_then kall_tac
  \\ last_assum(qspec_then`16`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ simp_tac(srw_ss())[ag32_ffi_write_write_header_code_def]
  \\ qpat_assum`∀k. _ ⇒ (_ s3.MEM _ = _)`(qspec_then`16`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ qpat_assum`∀k. _ ⇒ (_ s6.MEM _ = _)`(qspec_then`16`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ qpat_assum`∀k. _ ⇒ (_ s8.MEM _ = _)`(qspec_then`16`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ qpat_assum`∀k. _ ⇒ (_ s10.MEM _ = _)`(qspec_then`16`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ qpat_assum`∀k. _ ⇒ (_ s13.MEM _ = _)`(qspec_then`16`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ simp[]
  \\ ntac 6 (disch_then kall_tac)
  \\ simp[ag32_targetProofTheory.Decode_Encode]
  \\ simp[ag32Theory.Run_def]
  \\ simp[Once EXISTS_NUM]);

val ag32_ffi_write_write_header_PC = Q.store_thm("ag32_ffi_write_write_header_PC",
  `(ag32_ffi_write_write_header s).PC = s.PC + n2w(4 * LENGTH ag32_ffi_write_write_header_code)`,
  rw[ag32_ffi_write_write_header_def]
  \\ rw[Once ag32Theory.dfn'StoreMEMByte_def, ag32Theory.incPC_def]
  \\ rw[dfn'Normal_PC, dfn'Shift_PC, dfn'LoadConstant_PC]
  \\ rw[Once ag32Theory.dfn'StoreMEMByte_def, ag32Theory.incPC_def]
  \\ rw[dfn'Normal_PC, dfn'Shift_PC, dfn'LoadConstant_PC]
  \\ rw[Once ag32Theory.dfn'StoreMEMByte_def, ag32Theory.incPC_def]
  \\ rw[dfn'Normal_PC, dfn'Shift_PC, dfn'LoadConstant_PC]
  \\ rw[Once ag32Theory.dfn'StoreMEMByte_def, ag32Theory.incPC_def]
  \\ rw[dfn'Normal_PC, dfn'Shift_PC, dfn'LoadConstant_PC]
  \\ rw[Once ag32Theory.dfn'StoreMEMByte_def, ag32Theory.incPC_def]
  \\ rw[dfn'Normal_PC, dfn'Shift_PC, dfn'LoadConstant_PC]
  \\ rw[Once ag32Theory.dfn'StoreMEM_def, ag32Theory.incPC_def]
  \\ rw[dfn'Normal_PC, dfn'Shift_PC, dfn'LoadConstant_PC]
  \\ rw[Once ag32Theory.dfn'StoreMEM_def, ag32Theory.incPC_def]
  \\ rw[dfn'Normal_PC, dfn'Shift_PC, dfn'LoadConstant_PC]
  \\ EVAL_TAC);

val ag32_ffi_write_write_header_R = Q.store_thm("ag32_ffi_write_write_header_R",
  `((ag32_ffi_write_write_header s).R 3w = s.R 3w)`,
  rw[ag32_ffi_write_write_header_def]
  \\ rw[Once ag32Theory.dfn'StoreMEMByte_def, ag32Theory.incPC_def]
  \\ rw[Once ag32Theory.dfn'Normal_def, ag32Theory.incPC_def, ag32Theory.norm_def, ag32Theory.ALU_def, APPLY_UPDATE_THM]
  \\ rw[Once ag32Theory.dfn'StoreMEMByte_def, ag32Theory.incPC_def]
  \\ rw[Once ag32Theory.dfn'Normal_def, ag32Theory.incPC_def, ag32Theory.norm_def, ag32Theory.ALU_def, APPLY_UPDATE_THM]
  \\ rw[Once ag32Theory.dfn'StoreMEMByte_def, ag32Theory.incPC_def]
  \\ rw[Once ag32Theory.dfn'Shift_def, ag32Theory.incPC_def, APPLY_UPDATE_THM]
  \\ rw[Once ag32Theory.dfn'Normal_def, ag32Theory.incPC_def, ag32Theory.norm_def, ag32Theory.ALU_def, APPLY_UPDATE_THM]
  \\ rw[Once ag32Theory.dfn'StoreMEMByte_def, ag32Theory.incPC_def]
  \\ rw[Once ag32Theory.dfn'Normal_def, ag32Theory.incPC_def, ag32Theory.norm_def, ag32Theory.ALU_def, APPLY_UPDATE_THM]
  \\ rw[Once ag32Theory.dfn'StoreMEMByte_def, ag32Theory.incPC_def]
  \\ rw[Once ag32Theory.dfn'Normal_def, ag32Theory.incPC_def, ag32Theory.norm_def, ag32Theory.ALU_def, APPLY_UPDATE_THM]
  \\ rw[Once ag32Theory.dfn'StoreMEM_def, ag32Theory.incPC_def]
  \\ rw[Once ag32Theory.dfn'Shift_def, ag32Theory.incPC_def, APPLY_UPDATE_THM]
  \\ rw[Once ag32Theory.dfn'Normal_def, ag32Theory.incPC_def, ag32Theory.norm_def, ag32Theory.ALU_def, APPLY_UPDATE_THM]
  \\ rw[Once ag32Theory.dfn'StoreMEM_def, ag32Theory.incPC_def]
  \\ rw[Once ag32Theory.dfn'Normal_def, ag32Theory.incPC_def, ag32Theory.norm_def, ag32Theory.ALU_def, APPLY_UPDATE_THM]
  \\ rw[ag32Theory.dfn'LoadConstant_def, ag32Theory.incPC_def, APPLY_UPDATE_THM]);

val ag32_ffi_write_num_written_def = Define`
  ag32_ffi_write_num_written s =
  let s = dfn'Normal (fInc, 3w, Reg 3w, Imm 1w) s in
  let s0 = dfn'LoadConstant (8w, F, n2w output_buffer_size) s in
  let s = dfn'JumpIfZero (fLess, Imm 8w, Reg 8w, Reg 1w) s0 in
  let s = if s.PC = s0.PC + 4w then dfn'Normal (fSnd, 1w, Reg 1w, Reg 8w) s else s in
  let s = dfn'Shift (shiftLR, 8w, Reg 1w, Imm 8w) s in
  let s = dfn'StoreMEMByte (Reg 8w, Reg 3w) s in
  let s = dfn'Normal (fInc, 3w, Reg 3w, Imm 1w) s in
  let s = dfn'StoreMEMByte (Reg 1w, Reg 3w) s in
  let s = dfn'Normal (fAdd, 3w, Reg 3w, Imm 2w) s in
  let s = dfn'Normal (fAdd, 3w, Reg 3w, Reg 7w) s in
  let s = dfn'LoadConstant (2w, F, 4w * 8w) s in
  s`;

val ag32_ffi_write_num_written_thm = Q.store_thm("ag32_ffi_write_num_written_thm",
  `bytes_in_memory (s.R 3w) (0w::n0::off1::off0::tll) s.MEM md ∧
   (s.R 1w = n2w n) ∧ (k = MIN n output_buffer_size) ∧ n < dimword(:16)
   ⇒
   ∃r8 cf ov.
   (ag32_ffi_write_num_written s =
    s with <| PC := s.PC + n2w (4 * LENGTH ag32_ffi_write_num_written_code);
              MEM := asm_write_bytearray (s.R 3w) (0w::(n2w2 k)) s.MEM;
              R := ((8w =+ r8)
                   ((3w =+ s.R 3w + 4w + s.R 7w)
                   ((2w =+ 4w * 8w)
                   ((1w =+ n2w k) s.R))));
              CarryFlag := cf;
              OverflowFlag := ov |>)`,
  rewrite_tac[ag32_ffi_write_num_written_def]
  \\ strip_tac
  \\ simp_tac (srw_ss())
       [Q.SPECL[]ag32Theory.dfn'Normal_def,
        ag32Theory.ri2word_def, ag32Theory.norm_def,
        ag32Theory.ALU_def, ag32Theory.incPC_def ]
  \\ CONV_TAC(PATH_CONV"rararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ simp_tac (srw_ss())
       [Q.SPECL[]ag32Theory.dfn'LoadConstant_def,
        ag32Theory.ri2word_def, ag32Theory.norm_def,
        ag32Theory.shift_def,
        ag32Theory.ALU_def, ag32Theory.incPC_def ]
  \\ CONV_TAC(PATH_CONV"rararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ simp_tac (srw_ss())
       [Q.SPECL[]ag32Theory.dfn'JumpIfZero_def,
        ag32Theory.ri2word_def, ag32Theory.norm_def,
        ag32Theory.ALU_def, ag32Theory.incPC_def ]
  \\ CONV_TAC(PATH_CONV"rararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ CONV_TAC(PATH_CONV"rararalrr"(SIMP_CONV(srw_ss()++LET_ss)[APPLY_UPDATE_THM]))
  \\ qmatch_goalsub_abbrev_tac`if cnd then _ else _`
  \\ qmatch_asmsub_abbrev_tac`cnd = ((if cnd' then _ else _).PC = _)`
  \\ `cnd = ¬cnd'` by ( rw[Abbr`cnd`,Abbr`cnd'`] )
  \\ qpat_x_assum`Abbrev(cnd = _)`kall_tac
  \\ qunabbrev_tac`cnd'`
  \\ rveq
  \\ CONV_TAC(PATH_CONV"rararalrr"(SIMP_CONV(srw_ss())[]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ simp_tac (srw_ss())
       [Q.SPECL[]ag32Theory.dfn'Shift_def,
        ag32Theory.ri2word_def, ag32Theory.norm_def, ag32Theory.shift_def,
        ag32Theory.ALU_def, ag32Theory.incPC_def ]
  \\ CONV_TAC(PATH_CONV"rararalrr"(SIMP_CONV(srw_ss()++LET_ss)[COND_RAND,APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ simp_tac (srw_ss())
       [Q.SPECL[]ag32Theory.dfn'StoreMEMByte_def,
        ag32Theory.ri2word_def, ag32Theory.norm_def, ag32Theory.shift_def,
        ag32Theory.ALU_def, ag32Theory.incPC_def ]
  \\ CONV_TAC(PATH_CONV"rararalrr"(SIMP_CONV(srw_ss()++LET_ss)[COND_RAND,APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ CONV_TAC(PATH_CONV"rararalrr"(SIMP_CONV(srw_ss()++LET_ss)[COND_RAND,APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ CONV_TAC(PATH_CONV"rararalrr"(SIMP_CONV(srw_ss()++LET_ss)[COND_RAND,APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ CONV_TAC(PATH_CONV"rararalrr"(SIMP_CONV(srw_ss()++LET_ss)[COND_RAND,APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ CONV_TAC(PATH_CONV"rararalrr"(SIMP_CONV(srw_ss()++LET_ss)[COND_RAND,APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ CONV_TAC(PATH_CONV"rararalrr"(SIMP_CONV(srw_ss()++LET_ss)[COND_RAND,APPLY_UPDATE_THM]))
  \\ simp_tac (srw_ss()) [Once LET_THM]
  \\ simp[Once COND_RAND]
  \\ simp[Once COND_RATOR]
  \\ simp[ag32Theory.ag32_state_component_equality]
  \\ simp[EVAL``4 * LENGTH ag32_ffi_write_num_written_code``]
  \\ simp[FUN_EQ_THM, APPLY_UPDATE_THM]
  \\ qmatch_goalsub_abbrev_tac`v2w [cnd] = 0w`
  \\ fs[EVAL``output_buffer_size``]
  \\ rfs[word_lt_n2w]
  \\ `¬BIT 31 n` by
    fs [bitTheory.BIT_def,bitTheory.BITS_THM,LESS_DIV_EQ_ZERO] \\ fs[]
  \\ `MIN n 2048 = if cnd then 2048 else n` by rw[Abbr`cnd`,MIN_DEF]
  \\ fs[] \\ rveq
  \\ fs[asmSemTheory.bytes_in_memory_def]
  \\ fs[CaseEq"option"] \\ rveq
  \\ Cases_on`s.R 3w`
  \\ Cases_on`cnd` \\ fs[markerTheory.Abbrev_def]
  \\ qmatch_goalsub_abbrev_tac`if 8w = _ then r8 else _`
  \\ qexists_tac`r8` \\ simp[Abbr`r8`]
  \\ (reverse conj_tac >- (rw[] \\ fs[]))
  \\ rw[MarshallingTheory.n2w2_def, lab_to_targetProofTheory.asm_write_bytearray_def, APPLY_UPDATE_THM]
  \\ fs[] \\ rfs[word_add_n2w]
  \\ TRY (
    Cases_on`n' + 1 < dimword(:32)` \\ fs[]
    \\ `n' + 1  =dimword(:32)` by fs[]
    \\ fs[] \\ NO_TAC)
  \\ TRY (
    Cases_on`n' + 2 < dimword(:32)` \\ fs[]
    \\ Cases_on`n' = dimword(:32) - 1` \\ fs[]
    \\ Cases_on`n' = dimword(:32) - 2` \\ fs[]
    \\ NO_TAC)
  >- blastLib.BBLAST_TAC
  \\ fs [NOT_LESS]
  \\ match_mp_tac (blastLib.BBLAST_PROVE
      ``w <+ 256w:word32 /\ (k = w2w w) ==> ((7 >< 0) w = k:word8)``)
  \\ rewrite_tac [w2w_def,w2n_lsr,WORD_LO]
  \\ fs [DIV_LT_X]);

val ag32_ffi_write_num_written_code_thm = Q.store_thm("ag32_ffi_write_num_written_code_thm",
  `(∀k. k < LENGTH ag32_ffi_write_num_written_code ⇒
        (get_mem_word s.MEM (s.PC + n2w (4 * k)) =
         Encode (EL k ag32_ffi_write_num_written_code)))
   ∧ byte_aligned s.PC
   ∧ w2n s.PC + 4 * LENGTH ag32_ffi_write_num_written_code < dimword(:32)
   ∧ (∀k. k DIV 4 < LENGTH ag32_ffi_write_num_written_code ⇒ s.R 3w + 1w ≠ s.PC + n2w k)
   ∧ (∀k. k DIV 4 < LENGTH ag32_ffi_write_num_written_code ⇒ s.R 3w + 2w ≠ s.PC + n2w k)
   ⇒
   ∃k. (FUNPOW Next k s = ag32_ffi_write_num_written s)`,
  strip_tac
  \\ simp[ag32_ffi_write_num_written_def]
  \\ qmatch_goalsub_abbrev_tac`COND (t1.PC = t0.PC + 4w)`
  \\ simp[Once EXISTS_NUM] \\ disj2_tac \\ simp[FUNPOW]
  \\ simp[ag32Theory.Next_def]
  \\ qmatch_goalsub_abbrev_tac`pc + 2w`
  \\ simp[GSYM get_mem_word_def]
  \\ last_assum(qspec_then`0`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ simp_tac(srw_ss())[]
  \\ pop_assum mp_tac
  \\ DEP_REWRITE_TAC[byte_aligned_imp]
  \\ conj_tac >- rw[]
  \\ strip_tac \\ simp[Abbr`pc`]
  \\ disch_then kall_tac
  \\ simp[ag32_ffi_write_num_written_code_def]
  \\ simp[ag32_targetProofTheory.Decode_Encode]
  \\ simp[ag32Theory.Run_def]
  \\ qmatch_goalsub_abbrev_tac`dfn'Shift _ cs`
  \\ next_tac 1
  \\ simp[Abbr`t0`]
  \\ next_tac 2
  \\ `cs.PC = s.PC + n2w (4 * 4)`
  by (
    simp[Abbr`cs`]
    \\ rw[dfn'Normal_PC]
    \\ simp[Abbr`t1`]
    \\ fs[ag32Theory.dfn'JumpIfZero_def, ag32Theory.ri2word_def, ag32Theory.incPC_def, ag32Theory.ALU_def]
    \\ rw[] \\ fs[] \\ rfs[] )
  \\ qho_match_abbrev_tac`P t1`
  \\ `P cs` suffices_by (
    simp[Abbr`P`]
    \\ Cases_on`cs = t1` \\ simp[]
    \\ simp[Abbr`cs`]
    \\ CASE_TAC \\ fs[]
    \\ rw[]
    \\ qexists_tac`SUC m`
    \\ simp[FUNPOW]
    \\ simp[ag32Theory.Next_def]
    \\ qmatch_goalsub_abbrev_tac`pc + 2w`
    \\ simp[GSYM get_mem_word_def]
    \\ last_assum(qspec_then`3`mp_tac)
    \\ impl_tac >- EVAL_TAC
    \\ simp_tac(srw_ss())[ag32_ffi_write_num_written_code_def]
    \\ `t1.MEM = s.MEM` by simp[Abbr`t1`,dfn'JumpIfZero_MEM]
    \\ simp[]
    \\ qpat_x_assum`Abbrev(pc = _)`mp_tac
    \\ DEP_REWRITE_TAC[byte_aligned_imp]
    \\ conj_tac
    >- (
      irule byte_aligned_add
      \\ fs[]
      \\ EVAL_TAC )
    \\ strip_tac
    \\ simp[Abbr`pc`]
    \\ simp[ag32_targetProofTheory.Decode_Encode]
    \\ simp[ag32Theory.Run_def] )
  \\ simp[Abbr`P`]
  \\ `cs.MEM = s.MEM` by (
    simp[Abbr`cs`,Abbr`t1`]
    \\ rw[dfn'Normal_MEM, dfn'JumpIfZero_MEM] )
  \\ simp[Once EXISTS_NUM] \\ disj2_tac \\ simp[FUNPOW]
  \\ simp[ag32Theory.Next_def]
  \\ qmatch_goalsub_abbrev_tac`pc + 2w`
  \\ simp[GSYM get_mem_word_def]
  \\ last_assum(qspec_then`4`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ simp_tac(srw_ss())[ag32_ffi_write_num_written_code_def]
  \\ qpat_x_assum`Abbrev(pc = _)`mp_tac
  \\ DEP_REWRITE_TAC[byte_aligned_imp]
  \\ conj_tac
  >- ( irule byte_aligned_add \\ fs[] \\ EVAL_TAC )
  \\ strip_tac
  \\ simp[Abbr`pc`]
  \\ disch_then kall_tac
  \\ simp[ag32_targetProofTheory.Decode_Encode]
  \\ simp[ag32Theory.Run_def]
  \\ next_tac 5
  \\ simp[Once EXISTS_NUM] \\ disj2_tac \\ simp[FUNPOW]
  \\ qmatch_goalsub_abbrev_tac`Next s6`
  \\ simp[ag32Theory.Next_def]
  \\ qmatch_goalsub_abbrev_tac`pc + 2w`
  \\ simp[GSYM get_mem_word_def]
  \\ last_assum(qspec_then`6`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ `s6.PC = s.PC + n2w (4 * 6)`
  by ( simp[Abbr`s6`, ag32Theory.dfn'StoreMEMByte_def, ag32Theory.incPC_def] )
  \\ qpat_x_assum`Abbrev(pc = _)`mp_tac
  \\ DEP_REWRITE_TAC[byte_aligned_imp]
  \\ conj_tac
  >- ( simp[] \\ irule byte_aligned_add \\ fs[] \\ EVAL_TAC )
  \\ strip_tac \\ fs[Abbr`pc`]
  \\ `s5.R 3w = s.R 3w + 1w`
  by (
    simp[Abbr`s5`, ag32Theory.dfn'Shift_def, ag32Theory.incPC_def, APPLY_UPDATE_THM]
    \\ simp[Abbr`cs`, Abbr`t1`]
    \\ simp[ag32Theory.dfn'JumpIfZero_def, ag32Theory.ri2word_def, ag32Theory.ALU_def]
    \\ simp[ag32Theory.incPC_def, ag32Theory.dfn'Normal_def, ag32Theory.norm_def,
            ag32Theory.ri2word_def, ag32Theory.ALU_def]
    \\ qmatch_goalsub_abbrev_tac`v2w [cnd]`
    \\ `s2.R 3w = s.R 3w + 1w`
    by(
      simp[Abbr`s2`, ag32Theory.dfn'LoadConstant_def, ag32Theory.incPC_def, APPLY_UPDATE_THM]
      \\ simp[Abbr`s1`]
      \\ simp[ag32Theory.incPC_def, ag32Theory.dfn'Normal_def, ag32Theory.norm_def,
              ag32Theory.ri2word_def, ag32Theory.ALU_def]
      \\ simp[APPLY_UPDATE_THM] )
    \\ Cases_on`cnd` \\ rw[APPLY_UPDATE_THM] )
  \\ `∀k. k < LENGTH ag32_ffi_write_num_written_code ⇒
      (get_mem_word s6.MEM (s.PC + n2w (4 * k)) =
       Encode (EL k ag32_ffi_write_num_written_code))`
  by (
    qx_gen_tac`k`
    \\ strip_tac
    \\ last_x_assum drule
    \\ disch_then(SUBST1_TAC o SYM)
    \\ simp[Abbr`s6`, ag32Theory.dfn'StoreMEMByte_def, ag32Theory.incPC_def, ag32Theory.ri2word_def]
    \\ simp[get_mem_word_def, APPLY_UPDATE_THM]
    \\ fs[EVAL``LENGTH ag32_ffi_write_num_written_code``]
    \\ Cases_on`s.R 3w` \\ Cases_on`s.PC` \\ fs[word_add_n2w]
    \\ IF_CASES_TAC \\ fs[]
    >- ( last_x_assum(qspec_then`4 * k + 3`mp_tac) \\ simp[DIV_LT_X] )
    \\ IF_CASES_TAC \\ fs[]
    >- ( last_x_assum(qspec_then`4 * k + 2`mp_tac) \\ simp[DIV_LT_X] )
    \\ IF_CASES_TAC \\ fs[]
    >- ( last_x_assum(qspec_then`4 * k + 1`mp_tac) \\ simp[DIV_LT_X] )
    \\ IF_CASES_TAC \\ fs[]
    >- ( last_x_assum(qspec_then`4 * k + 0`mp_tac) \\ simp[DIV_LT_X] ) )
  \\ first_assum(qspec_then`6`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ simp[]
  \\ ntac 2 (disch_then kall_tac)
  \\ simp[ag32_targetProofTheory.Decode_Encode]
  \\ simp[ag32_ffi_write_num_written_code_def]
  \\ simp[ag32Theory.Run_def]
  \\ simp[Once EXISTS_NUM] \\ disj2_tac \\ simp[FUNPOW]
  \\ qmatch_goalsub_abbrev_tac`Next s7`
  \\ simp[ag32Theory.Next_def]
  \\ qmatch_goalsub_abbrev_tac`pc + 2w`
  \\ simp[GSYM get_mem_word_def]
  \\ last_assum(qspec_then`7`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ `s7.PC = s.PC + n2w (4 * 7)`
  by ( simp[Abbr`s7`, dfn'Normal_PC] )
  \\ qpat_x_assum`Abbrev(pc = _)`mp_tac
  \\ DEP_REWRITE_TAC[byte_aligned_imp]
  \\ conj_tac
  >- ( simp[] \\ irule byte_aligned_add \\ fs[] \\ EVAL_TAC )
  \\ strip_tac \\ fs[Abbr`pc`]
  \\ first_assum(qspec_then`7`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ simp[]
  \\ `s7.MEM = s6.MEM` by simp[Abbr`s7`, dfn'Normal_MEM]
  \\ simp[]
  \\ ntac 2 (disch_then kall_tac)
  \\ simp[ag32_targetProofTheory.Decode_Encode]
  \\ simp[ag32_ffi_write_num_written_code_def]
  \\ simp[ag32Theory.Run_def]
  \\ simp[Once EXISTS_NUM] \\ disj2_tac \\ simp[FUNPOW]
  \\ qmatch_goalsub_abbrev_tac`Next s8`
  \\ simp[ag32Theory.Next_def]
  \\ qmatch_goalsub_abbrev_tac`pc + 2w`
  \\ simp[GSYM get_mem_word_def]
  \\ `s8.PC = s.PC + n2w (4 * 8)`
  by ( simp[Abbr`s8`, ag32Theory.dfn'StoreMEMByte_def, ag32Theory.incPC_def] )
  \\ qpat_x_assum`Abbrev(pc = _)`mp_tac
  \\ DEP_REWRITE_TAC[byte_aligned_imp]
  \\ conj_tac
  >- ( simp[] \\ irule byte_aligned_add \\ fs[] \\ EVAL_TAC )
  \\ strip_tac \\ fs[Abbr`pc`]
  \\ `s7.R 3w = s.R 3w + 2w`
  by (
    simp[Abbr`s7`]
    \\ simp[ag32Theory.incPC_def, ag32Theory.dfn'Normal_def, ag32Theory.norm_def,
            ag32Theory.ri2word_def, ag32Theory.ALU_def]
      \\ simp[APPLY_UPDATE_THM]
      \\ simp[Abbr`s6`]
      \\ simp[ag32Theory.dfn'StoreMEMByte_def, ag32Theory.incPC_def])
  \\ `∀k. k < LENGTH ag32_ffi_write_num_written_code ⇒
      (get_mem_word s8.MEM (s.PC + n2w (4 * k)) =
       Encode (EL k ag32_ffi_write_num_written_code))`
  by (
    qx_gen_tac`k`
    \\ strip_tac
    \\ first_x_assum drule
    \\ disch_then(SUBST1_TAC o SYM)
    \\ simp[Abbr`s8`, ag32Theory.dfn'StoreMEMByte_def, ag32Theory.incPC_def, ag32Theory.ri2word_def]
    \\ simp[get_mem_word_def, APPLY_UPDATE_THM]
    \\ fs[EVAL``LENGTH ag32_ffi_write_num_written_code``]
    \\ Cases_on`s.R 3w` \\ Cases_on`s.PC` \\ fs[word_add_n2w]
    \\ IF_CASES_TAC \\ fs[]
    >- ( first_x_assum(qspec_then`4 * k + 3`mp_tac) \\ simp[DIV_LT_X] )
    \\ IF_CASES_TAC \\ fs[]
    >- ( first_x_assum(qspec_then`4 * k + 2`mp_tac) \\ simp[DIV_LT_X] )
    \\ IF_CASES_TAC \\ fs[]
    >- ( first_x_assum(qspec_then`4 * k + 1`mp_tac) \\ simp[DIV_LT_X] )
    \\ IF_CASES_TAC \\ fs[]
    >- ( first_x_assum(qspec_then`4 * k + 0`mp_tac) \\ simp[DIV_LT_X] ) )
  \\ first_assum(qspec_then`8`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ simp[]
  \\ disch_then kall_tac
  \\ simp[ag32_targetProofTheory.Decode_Encode]
  \\ simp[ag32_ffi_write_num_written_code_def]
  \\ simp[ag32Theory.Run_def]
  \\ simp[Once EXISTS_NUM] \\ disj2_tac \\ simp[FUNPOW]
  \\ qmatch_goalsub_abbrev_tac`Next s9`
  \\ simp[ag32Theory.Next_def]
  \\ qmatch_goalsub_abbrev_tac`pc + 2w`
  \\ simp[GSYM get_mem_word_def]
  \\ `s9.PC = s.PC + n2w (4 * 9)`
  by ( simp[Abbr`s9`, dfn'Normal_PC] )
  \\ qpat_x_assum`Abbrev(pc = _)`mp_tac
  \\ DEP_REWRITE_TAC[byte_aligned_imp]
  \\ conj_tac
  >- ( simp[] \\ irule byte_aligned_add \\ fs[] \\ EVAL_TAC )
  \\ strip_tac \\ fs[Abbr`pc`]
  \\ `s9.MEM = s8.MEM` by simp[Abbr`s9`, dfn'Normal_MEM]
  \\ first_assum(qspec_then`9`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ simp[]
  \\ simp[ag32_targetProofTheory.Decode_Encode]
  \\ simp[ag32_ffi_write_num_written_code_def]
  \\ disch_then kall_tac
  \\ simp[ag32Theory.Run_def]
  \\ simp[Once EXISTS_NUM] \\ disj2_tac \\ simp[FUNPOW]
  \\ qmatch_goalsub_abbrev_tac`Next s10`
  \\ simp[ag32Theory.Next_def]
  \\ qmatch_goalsub_abbrev_tac`pc + 2w`
  \\ simp[GSYM get_mem_word_def]
  \\ `s10.PC = s.PC + n2w (4 * 10)`
  by ( simp[Abbr`s10`, dfn'Normal_PC] )
  \\ qpat_x_assum`Abbrev(pc = _)`mp_tac
  \\ DEP_REWRITE_TAC[byte_aligned_imp]
  \\ conj_tac
  >- ( simp[] \\ irule byte_aligned_add \\ fs[] \\ EVAL_TAC )
  \\ strip_tac \\ fs[Abbr`pc`]
  \\ `s10.MEM = s9.MEM` by simp[Abbr`s10`, dfn'Normal_MEM]
  \\ first_assum(qspec_then`10`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ simp[]
  \\ simp[ag32_targetProofTheory.Decode_Encode]
  \\ simp[ag32_ffi_write_num_written_code_def]
  \\ disch_then kall_tac
  \\ simp[ag32Theory.Run_def]
  \\ simp[Once EXISTS_NUM]);

val ag32_ffi_write_copy_def = tDefine"ag32_ffi_write_copy_def"`
  ag32_ffi_write_copy s0 =
  let s = dfn'JumpIfZero (fSnd, Reg 2w, Imm 0w, Reg 1w) s0 in
  if (s0.R 1w = 0w) then s else
  let s = dfn'LoadMEMByte (8w, Reg 3w) s in
  let s = dfn'StoreMEMByte (Reg 8w, Reg 5w) s in
  let s = dfn'Normal (fInc, 3w, Reg 3w, Imm 1w) s in
  let s = dfn'Normal (fInc, 5w, Reg 5w, Imm 1w) s in
  let s0 = dfn'Normal (fDec, 1w, Reg 1w, Imm 1w) s in
  let s = dfn'JumpIfZero (fSnd, Imm (4w * -6w), Imm 0w, Imm 0w) s0 in
  ag32_ffi_write_copy s`
  (wf_rel_tac`measure (λs. w2n (s.R 1w))`
   \\ rw[ag32Theory.dfn'JumpIfZero_def, ag32Theory.ALU_def,
         ag32Theory.dfn'Normal_def, ag32Theory.norm_def,
         ag32Theory.dfn'LoadConstant_def,
         ag32Theory.dfn'StoreMEMByte_def, ag32Theory.dfn'LoadMEMByte_def,
         ag32Theory.ri2word_def, ag32Theory.incPC_def, APPLY_UPDATE_THM]
   \\ Cases_on`s0.R 1w` \\ fs[]
   \\ Cases_on`n` \\ fs[]
   \\ simp[ADD1, GSYM word_add_n2w]);

val ag32_ffi_write_copy_thm = Q.store_thm("ag32_ffi_write_copy_thm",
  `∀s written.
   bytes_in_memory (s.R 3w) written s.MEM md ∧ (w2n (s.R 1w) = LENGTH written) ∧
   DISJOINT md { w | s.R 5w <=+ w ∧ w <+ s.R 5w + n2w (LENGTH written) } ∧
   w2n (s.R 5w) + LENGTH written < dimword(:32) ∧
   w2n (s.R 3w) + LENGTH written < dimword(:32)
   ⇒
   ∃r1 r3 r5 r8.
   (ag32_ffi_write_copy s =
    s with <| PC := s.PC + s.R 2w;
              R := ((1w =+ r1)
                   ((3w =+ r3)
                   ((5w =+ r5)
                   ((8w =+ r8) s.R))));
              MEM := asm_write_bytearray (s.R 5w) written s.MEM |>)`,
  Induct_on`w2n (s.R 1w)` \\ rw[]
  >- (
    qpat_x_assum`0 = _`(assume_tac o SYM)
    \\ fs[read_bytearray_def, asmSemTheory.bytes_in_memory_def] \\ rw[]
    \\ rw[lab_to_targetProofTheory.asm_write_bytearray_def]
    \\ rw[Once ag32_ffi_write_copy_def, ag32Theory.dfn'LoadConstant_def,
          ag32Theory.incPC_def, APPLY_UPDATE_THM]
    \\ rw[ag32Theory.dfn'JumpIfZero_def, ag32Theory.ALU_def, ag32Theory.ri2word_def,
          ag32Theory.incPC_def, APPLY_UPDATE_THM]
    \\ rw[ag32Theory.ag32_state_component_equality]
    \\ rw[FUN_EQ_THM, APPLY_UPDATE_THM]
    \\ metis_tac[] )
  \\ fs[]
  \\ qpat_x_assum`SUC _ = _`(assume_tac o SYM)
  \\ Cases_on`written`
  \\ fs[read_bytearray_def, asmSemTheory.bytes_in_memory_def]
  \\ rw[] \\ fs[CaseEq"option"] \\ rw[]
  \\ rw[Once ag32_ffi_write_copy_def, ag32Theory.dfn'LoadConstant_def,
        ag32Theory.incPC_def, APPLY_UPDATE_THM] \\ fs[]
  \\ rw[ag32Theory.dfn'JumpIfZero_def, ag32Theory.incPC_def, ag32Theory.ri2word_def,
        ag32Theory.ALU_def, APPLY_UPDATE_THM]
  \\ rw[ag32Theory.dfn'LoadMEMByte_def, ag32Theory.incPC_def, ag32Theory.ri2word_def,
        APPLY_UPDATE_THM]
  \\ rw[ag32Theory.dfn'StoreMEMByte_def, ag32Theory.incPC_def, ag32Theory.ri2word_def,
        APPLY_UPDATE_THM]
  \\ rw[ag32Theory.dfn'Normal_def, ag32Theory.norm_def,
        ag32Theory.incPC_def, ag32Theory.ri2word_def,
        ag32Theory.ALU_def, APPLY_UPDATE_THM]
  \\ qmatch_goalsub_abbrev_tac`ag32_ffi_write_copy s'`
  \\ first_x_assum(qspec_then`s'`mp_tac)
  \\ simp[Abbr`s'`, APPLY_UPDATE_THM]
  \\ impl_keep_tac
  >- (
    Cases_on`s.R 1w` \\ fs[]
    \\ simp[ADD1]
    \\ simp[GSYM word_add_n2w] )
  \\ rveq
  \\ disch_then(qspec_then`t`mp_tac)
  \\ impl_tac
  >- (
    fs[]
    \\ reverse conj_asm2_tac
    >- (
      fs[IN_DISJOINT, data_to_word_assignProofTheory.IMP]
      \\ Cases_on`s.R 5w`
      \\ fs[ADD1, word_add_n2w]
      \\ Cases_on`s.R 3w` \\ fs[word_add_n2w]
      \\ gen_tac \\ strip_tac
      \\ first_x_assum drule
      \\ rw[]
      \\ Cases_on`s.R 1w` \\ rfs[word_add_n2w]
      \\ Cases_on`n''` \\ fs[ADD1, GSYM word_add_n2w]
      \\ first_x_assum match_mp_tac
      \\ Cases_on`x`
      \\ fs[word_ls_n2w] \\ rw[]
      \\ fs[word_add_n2w, word_ls_n2w]
      \\ Cases_on`n + 1 = dimword(:32)` \\ fs[]
      \\ `n + 1 < dimword(:32)` by fs[] \\ fs[])
    \\ irule asmPropsTheory.bytes_in_memory_change_mem
    \\ goal_assum(first_assum o mp_then Any mp_tac)
    \\ simp[APPLY_UPDATE_THM]
    \\ rw[]
    \\ Cases_on`s.R 1w` \\ fs[] \\ rfs[]
    \\ Cases_on`n'` \\ fs[ADD1, GSYM word_add_n2w] \\ rw[]
    \\ rfs[] \\ rw[]
    \\ fs[IN_DISJOINT, data_to_word_assignProofTheory.IMP]
    \\ drule (GEN_ALL asmPropsTheory.bytes_in_memory_all_pcs)
    \\ simp[asmPropsTheory.all_pcs_thm, SUBSET_DEF, PULL_EXISTS]
    \\ disch_then(qspec_then`0`mp_tac) \\ simp[]
    \\ disch_then drule
    \\ strip_tac
    \\ last_x_assum drule
    \\ Cases_on`s.R 3w` \\ fs[word_add_n2w]
    \\ fs[word_ls_n2w] \\ rfs[]
    \\ fs[word_lo_n2w] )
  \\ rw[]
  \\ rw[]
  \\ rw[ag32Theory.ag32_state_component_equality]
  \\ rw[FUN_EQ_THM, APPLY_UPDATE_THM]
  \\ map_every qexists_tac[`r1`,`r3`,`r5`,`r8`]
  \\ reverse conj_tac >- rw[]
  \\ rw[lab_to_targetProofTheory.asm_write_bytearray_def, APPLY_UPDATE_THM]
  >- (
    irule asm_write_bytearray_unchanged
    \\ simp[APPLY_UPDATE_THM]
    \\ Cases_on`s.R 1w` \\ fs[ADD1]
    \\ Cases_on`s.R 5w` \\ fs[word_add_n2w]
    \\ fs[word_lo_n2w, word_ls_n2w]
    \\ blastLib.BBLAST_TAC )
  \\ irule mem_eq_imp_asm_write_bytearray_eq
  \\ rw[APPLY_UPDATE_THM]);

val ag32_ffi_write_copy_code_thm = Q.store_thm("ag32_ffi_write_copy_code_thm",
  `∀s.
   (∀k. k < LENGTH ag32_ffi_write_copy_code ⇒
        (get_mem_word s.MEM (s.PC + n2w (4 * k)) =
         Encode (EL k ag32_ffi_write_copy_code)))
   ∧ byte_aligned s.PC
   ∧ w2n s.PC + 4 * LENGTH ag32_ffi_write_copy_code < dimword (:32)
   ∧ w2n (s.R 5w) + w2n (s.R 1w) < dimword(:32)
   ∧ DISJOINT { s.R 5w + n2w k | k | k < w2n (s.R 1w) }
              { s.PC + n2w k | k | k DIV 4 < LENGTH ag32_ffi_write_copy_code }
   ⇒
   ∃k. (FUNPOW Next k s = ag32_ffi_write_copy s)`,
  Induct_on`w2n(s.R 1w)` \\ rw[]
  >- (
    simp[Once ag32_ffi_write_copy_def]
    \\ Cases_on`s.R 1w` \\ fs[] \\ rw[]
    \\ qexists_tac`1` \\ rw[]
    \\ rw[ag32Theory.Next_def]
    \\ qmatch_goalsub_abbrev_tac`pc + 2w`
    \\ simp[GSYM get_mem_word_def]
    \\ last_assum(qspec_then`0`mp_tac)
    \\ impl_tac >- EVAL_TAC
    \\ simp_tac(srw_ss())[]
    \\ pop_assum mp_tac
    \\ DEP_REWRITE_TAC[byte_aligned_imp]
    \\ conj_tac >- rw[]
    \\ strip_tac \\ simp[Abbr`pc`]
    \\ disch_then kall_tac
    \\ simp[ag32_ffi_write_copy_code_def]
    \\ simp[ag32_targetProofTheory.Decode_Encode]
    \\ simp[ag32Theory.Run_def] )
  \\ simp[Once ag32_ffi_write_copy_def]
  \\ Cases_on`s.R 1w` \\ fs[]
  \\ simp[Once EXISTS_NUM] \\ disj2_tac \\ simp[FUNPOW]
  \\ simp[ag32Theory.Next_def]
  \\ qmatch_goalsub_abbrev_tac`pc + 2w`
  \\ simp[GSYM get_mem_word_def]
  \\ qpat_x_assum`Abbrev(pc = _)`mp_tac
  \\ DEP_REWRITE_TAC[byte_aligned_imp]
  \\ conj_tac
  >- ( simp[] \\ irule byte_aligned_add \\ fs[] \\ EVAL_TAC )
  \\ strip_tac \\ fs[Abbr`pc`]
  \\ first_assum(qspec_then`0`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ simp[]
  \\ simp[ag32_targetProofTheory.Decode_Encode]
  \\ simp[ag32_ffi_write_copy_code_def]
  \\ disch_then kall_tac
  \\ simp[ag32Theory.Run_def]
  \\ simp[Once EXISTS_NUM] \\ disj2_tac \\ simp[FUNPOW]
  \\ qmatch_goalsub_abbrev_tac`Next s1`
  \\ simp[ag32Theory.Next_def]
  \\ qmatch_goalsub_abbrev_tac`pc + 2w`
  \\ simp[GSYM get_mem_word_def]
  \\ `s1.PC = s.PC + n2w (4 * 1)`
  by ( simp[Abbr`s1`, ag32Theory.dfn'JumpIfZero_def, ag32Theory.ri2word_def,
            ag32Theory.ALU_def,ag32Theory.incPC_def] )
  \\ qpat_x_assum`Abbrev(pc = _)`mp_tac
  \\ DEP_REWRITE_TAC[byte_aligned_imp]
  \\ conj_tac
  >- ( simp[] \\ irule byte_aligned_add \\ fs[] \\ EVAL_TAC )
  \\ strip_tac \\ fs[Abbr`pc`]
  \\ `s1.MEM = s.MEM` by simp[Abbr`s1`, dfn'JumpIfZero_MEM]
  \\ first_assum(qspec_then`1`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ simp[]
  \\ simp[ag32_targetProofTheory.Decode_Encode]
  \\ simp[ag32_ffi_write_copy_code_def]
  \\ disch_then kall_tac
  \\ simp[ag32Theory.Run_def]
  \\ next_tac 2
  \\ simp[Once EXISTS_NUM] \\ disj2_tac \\ simp[FUNPOW]
  \\ qmatch_goalsub_abbrev_tac`Next s3`
  \\ simp[ag32Theory.Next_def]
  \\ qmatch_goalsub_abbrev_tac`pc + 2w`
  \\ simp[GSYM get_mem_word_def]
  \\ `s3.PC = s.PC + n2w (4 * 3)`
  by ( simp[Abbr`s3`, ag32Theory.dfn'StoreMEMByte_def, ag32Theory.incPC_def] )
  \\ qpat_x_assum`Abbrev(pc = _)`mp_tac
  \\ DEP_REWRITE_TAC[byte_aligned_imp]
  \\ conj_tac
  >- ( simp[] \\ irule byte_aligned_add \\ fs[] \\ EVAL_TAC )
  \\ strip_tac \\ fs[Abbr`pc`]
  \\ `s2.R 5w = s.R 5w`
  by (
    simp[Abbr`s2`]
    \\ simp[ag32Theory.incPC_def, ag32Theory.dfn'LoadMEMByte_def,
            ag32Theory.dfn'Normal_def, ag32Theory.norm_def,
            ag32Theory.ri2word_def, ag32Theory.ALU_def]
      \\ simp[APPLY_UPDATE_THM]
      \\ simp[Abbr`s1`]
      \\ simp[ag32Theory.dfn'JumpIfZero_def, ag32Theory.incPC_def,
              ag32Theory.dfn'Normal_def, ag32Theory.norm_def,
              ag32Theory.ri2word_def, ag32Theory.ALU_def] )
  \\ `∀k. k < LENGTH ag32_ffi_write_copy_code ⇒
      (get_mem_word s3.MEM (s.PC + n2w (4 * k)) =
       Encode (EL k ag32_ffi_write_copy_code))`
  by (
    qx_gen_tac`k`
    \\ strip_tac
    \\ first_x_assum drule
    \\ disch_then(SUBST1_TAC o SYM)
    \\ simp[Abbr`s3`, ag32Theory.dfn'StoreMEMByte_def, ag32Theory.incPC_def, ag32Theory.ri2word_def]
    \\ simp[get_mem_word_def, APPLY_UPDATE_THM]
    \\ fs[EVAL``LENGTH ag32_ffi_write_copy_code``]
    \\ Cases_on`s.R 5w` \\ Cases_on`s.PC` \\ fs[word_add_n2w]
    \\ IF_CASES_TAC \\ fs[IN_DISJOINT, data_to_word_assignProofTheory.IMP,PULL_EXISTS]
    >- ( first_x_assum(qspec_then`0`mp_tac) \\ simp[DIV_LT_X]
         \\ disch_then(qspec_then`4 * k + 3`mp_tac) \\ simp[])
    \\ IF_CASES_TAC \\ fs[]
    >- ( first_x_assum(qspec_then`0`mp_tac) \\ simp[DIV_LT_X]
         \\ disch_then(qspec_then`4 * k + 2`mp_tac) \\ simp[])
    \\ IF_CASES_TAC \\ fs[]
    >- ( first_x_assum(qspec_then`0`mp_tac) \\ simp[DIV_LT_X]
         \\ disch_then(qspec_then`4 * k + 1`mp_tac) \\ simp[])
    \\ IF_CASES_TAC \\ fs[]
    >- ( first_x_assum(qspec_then`0`mp_tac) \\ simp[DIV_LT_X]
         \\ disch_then(qspec_then`4 * k + 0`mp_tac) \\ simp[]))
  \\ first_assum(qspec_then`3`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ simp[]
  \\ disch_then kall_tac
  \\ simp[ag32_targetProofTheory.Decode_Encode]
  \\ simp[ag32_ffi_write_copy_code_def]
  \\ simp[ag32Theory.Run_def]
  \\ simp[Once EXISTS_NUM] \\ disj2_tac \\ simp[FUNPOW]
  \\ qmatch_goalsub_abbrev_tac`Next s4`
  \\ simp[ag32Theory.Next_def]
  \\ qmatch_goalsub_abbrev_tac`pc + 2w`
  \\ simp[GSYM get_mem_word_def]
  \\ `s4.PC = s.PC + n2w (4 * 4)`
  by ( simp[Abbr`s4`, dfn'Normal_PC])
  \\ qpat_x_assum`Abbrev(pc = _)`mp_tac
  \\ DEP_REWRITE_TAC[byte_aligned_imp]
  \\ conj_tac
  >- ( simp[] \\ irule byte_aligned_add \\ fs[] \\ EVAL_TAC )
  \\ strip_tac \\ fs[Abbr`pc`]
  \\ `s4.MEM = s3.MEM` by simp[Abbr`s4`, dfn'Normal_MEM]
  \\ first_assum(qspec_then`4`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ simp[]
  \\ simp[ag32_targetProofTheory.Decode_Encode]
  \\ simp[ag32_ffi_write_copy_code_def]
  \\ disch_then kall_tac
  \\ simp[ag32Theory.Run_def]
  \\ simp[Once EXISTS_NUM] \\ disj2_tac \\ simp[FUNPOW]
  \\ qmatch_goalsub_abbrev_tac`Next s5`
  \\ simp[ag32Theory.Next_def]
  \\ qmatch_goalsub_abbrev_tac`pc + 2w`
  \\ simp[GSYM get_mem_word_def]
  \\ `s5.PC = s.PC + n2w (4 * 5)`
  by ( simp[Abbr`s5`, dfn'Normal_PC])
  \\ qpat_x_assum`Abbrev(pc = _)`mp_tac
  \\ DEP_REWRITE_TAC[byte_aligned_imp]
  \\ conj_tac
  >- ( simp[] \\ irule byte_aligned_add \\ fs[] \\ EVAL_TAC )
  \\ strip_tac \\ fs[Abbr`pc`]
  \\ `s5.MEM = s3.MEM` by simp[Abbr`s5`, dfn'Normal_MEM]
  \\ first_assum(qspec_then`5`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ simp[]
  \\ simp[ag32_targetProofTheory.Decode_Encode]
  \\ simp[ag32_ffi_write_copy_code_def]
  \\ disch_then kall_tac
  \\ simp[ag32Theory.Run_def]
  \\ simp[Once EXISTS_NUM] \\ disj2_tac \\ simp[FUNPOW]
  \\ qmatch_goalsub_abbrev_tac`Next s6`
  \\ simp[ag32Theory.Next_def]
  \\ qmatch_goalsub_abbrev_tac`pc + 2w`
  \\ simp[GSYM get_mem_word_def]
  \\ `s6.PC = s.PC + n2w (4 * 6)`
  by ( simp[Abbr`s6`, dfn'Normal_PC])
  \\ qpat_x_assum`Abbrev(pc = _)`mp_tac
  \\ DEP_REWRITE_TAC[byte_aligned_imp]
  \\ conj_tac
  >- ( simp[] \\ irule byte_aligned_add \\ fs[] \\ EVAL_TAC )
  \\ strip_tac \\ fs[Abbr`pc`]
  \\ `s6.MEM = s3.MEM` by simp[Abbr`s6`, dfn'Normal_MEM]
  \\ first_assum(qspec_then`6`mp_tac)
  \\ impl_tac >- EVAL_TAC
  \\ simp[]
  \\ simp[ag32_targetProofTheory.Decode_Encode]
  \\ simp[ag32_ffi_write_copy_code_def]
  \\ disch_then kall_tac
  \\ simp[ag32Theory.Run_def]
  \\ qmatch_goalsub_abbrev_tac`_ = _ s7`
  \\ last_x_assum(qspec_then`s7`mp_tac)
  \\ impl_keep_tac
  >-(
    simp[Abbr`s7`, ag32Theory.dfn'JumpIfZero_def, ag32Theory.ri2word_def,ag32Theory.ALU_def]
    \\ simp[Abbr`s6`, ag32Theory.dfn'Normal_def, ag32Theory.norm_def,
            ag32Theory.ri2word_def,ag32Theory.ALU_def,ag32Theory.incPC_def,APPLY_UPDATE_THM]
    \\ simp[Abbr`s5`, ag32Theory.dfn'Normal_def, ag32Theory.norm_def,
            ag32Theory.ri2word_def,ag32Theory.ALU_def,ag32Theory.incPC_def,APPLY_UPDATE_THM]
    \\ simp[Abbr`s4`, ag32Theory.dfn'Normal_def, ag32Theory.norm_def,
            ag32Theory.ri2word_def,ag32Theory.ALU_def,ag32Theory.incPC_def,APPLY_UPDATE_THM]
    \\ simp[Abbr`s3`, ag32Theory.dfn'StoreMEMByte_def,ag32Theory.incPC_def]
    \\ simp[Abbr`s2`, ag32Theory.dfn'LoadMEMByte_def,ag32Theory.incPC_def,APPLY_UPDATE_THM]
    \\ simp[Abbr`s1`, ag32Theory.dfn'JumpIfZero_def, ag32Theory.incPC_def, ag32Theory.ri2word_def,
            ag32Theory.ALU_def]
    \\ simp[ADD1,GSYM word_add_n2w])
  \\ `s7.MEM = s3.MEM` by simp[Abbr`s7`, dfn'JumpIfZero_MEM]
  \\ `s7.PC = s.PC`
  by ( simp[Abbr`s7`, ag32Theory.dfn'JumpIfZero_def, ag32Theory.ri2word_def,ag32Theory.ALU_def])
  \\ `s7.R 5w = s.R 5w + 1w`
  by(
    simp[Abbr`s7`, ag32Theory.dfn'JumpIfZero_def, ag32Theory.ri2word_def,ag32Theory.ALU_def]
    \\ simp[Abbr`s6`, ag32Theory.dfn'Normal_def, ag32Theory.norm_def,
            ag32Theory.ri2word_def,ag32Theory.ALU_def,ag32Theory.incPC_def,APPLY_UPDATE_THM]
    \\ simp[Abbr`s5`, ag32Theory.dfn'Normal_def, ag32Theory.norm_def,
            ag32Theory.ri2word_def,ag32Theory.ALU_def,ag32Theory.incPC_def,APPLY_UPDATE_THM]
    \\ simp[Abbr`s4`, ag32Theory.dfn'Normal_def, ag32Theory.norm_def,
            ag32Theory.ri2word_def,ag32Theory.ALU_def,ag32Theory.incPC_def,APPLY_UPDATE_THM]
    \\ simp[Abbr`s3`, ag32Theory.dfn'StoreMEMByte_def,ag32Theory.incPC_def])
  \\ disch_then match_mp_tac
  \\ simp[]
  \\ Cases_on`s.R 5w` \\ Cases_on`s7.R 1w` \\ fs[word_add_n2w]
  \\ fs[ADD1,IN_DISJOINT,GSYM word_add_n2w,data_to_word_assignProofTheory.IMP,PULL_EXISTS]
  \\ rw[]
  \\ `k + 1 <n' + 1`by simp[]
  \\ first_x_assum drule
  \\ fs[word_add_n2w]);

val ag32_ffi_write_def = Define`
  ag32_ffi_write s =
  let s = ag32_ffi_write_set_id s in
  let s = ag32_ffi_write_check_conf s in
  let s0 = ag32_ffi_write_load_noff s in
  let s = ag32_ffi_write_check_lengths s0 in
  let s =
    if s.PC = s0.PC + n2w (4 * LENGTH ag32_ffi_write_check_lengths_code) then
      let s = ag32_ffi_write_write_header s in
      let s = ag32_ffi_write_num_written s in
              ag32_ffi_write_copy s
    else dfn'StoreMEMByte (Imm 1w, Reg 3w) s
  in ag32_ffi_return s`;

val ag32_ffi_write_code_thm = Q.store_thm("ag32_ffi_write_code_thm",
  `(∀k. k < LENGTH ag32_ffi_write_code ⇒
        (get_mem_word s.MEM (s.PC + n2w (4 * k)) =
         Encode (EL k ag32_ffi_write_code))) ∧
   (s.PC = r0 + n2w (ffi_code_start_offset + ag32_ffi_write_entrypoint)) ∧
   byte_aligned r0 ∧ w2n r0 + memory_size < dimword(:32) ∧
   bytes_in_memory (s.R 1w) conf s.MEM md ∧
   (w2n (s.R 2w) = LENGTH conf) ∧
   bytes_in_memory (s.R 3w) (n1::n0::off1::off0::tll) s.MEM md ∧
   (w2n (s.R 4w) = 4 + LENGTH tll) ∧
   w2n (s.R 3w) + 4 + LENGTH tll < dimword(:32) ∧ (* not sure whether/why this is needed: can't get from bytes_in_memory? *)
   DISJOINT md { s.PC + n2w k | k | k DIV 4 < LENGTH ag32_ffi_write_code } ∧
   DISJOINT md { w | r0 + n2w startup_code_size <=+ w ∧ w <+ r0 + n2w heap_start_offset }
   (* ∧ md ⊆ { w | w | r0 <+ w ∧ r0 + w <=+ r0 + n2w memory_size }*)
   ⇒
   ∃k. (FUNPOW Next k s = ag32_ffi_write s)`,
  rw[]
  \\ simp[ag32_ffi_write_def]
  \\ mp_tac ag32_ffi_write_set_id_code_thm
  \\ impl_tac
  >- (
    fs[ag32_ffi_write_code_def]
    \\ simp[EL_APPEND_EQN]
    \\ irule byte_aligned_add
    \\ simp[]
    \\ EVAL_TAC )
  \\ strip_tac
  \\ qmatch_asmsub_abbrev_tac`_ = s1`
  \\ qspec_then`s1`mp_tac(Q.GEN`s`ag32_ffi_write_check_conf_code_thm)
  \\ mp_tac ag32_ffi_write_set_id_thm
  \\ impl_tac >- rw[]
  \\ strip_tac \\ fs[]
  \\ pop_assum kall_tac
  \\ last_x_assum mp_tac
  \\ qho_match_abbrev_tac`P s.MEM ⇒ _`
  \\ strip_tac
  \\ `P s1.MEM`
  by (
    fs[Abbr`P`]
    \\ simp[Abbr`s1`]
    \\ fs[ag32_ffi_write_code_def]
    \\ qx_gen_tac`j`
    \\ strip_tac
    \\ first_x_assum(qspec_then`j`mp_tac)
    \\ impl_tac >- fs[]
    \\ simp[get_mem_word_def, APPLY_UPDATE_THM]
    \\ pop_assum mp_tac
    \\ EVAL_TAC \\ simp[]
    \\ Cases_on`r0` \\ fs[word_add_n2w, memory_size_def] )
  \\ fs[Abbr`P`]
  \\ `byte_aligned s1.PC`
  by (
    simp[Abbr`s1`]
    \\ irule byte_aligned_add
    \\ reverse conj_tac >- EVAL_TAC
    \\ irule byte_aligned_add
    \\ reverse conj_tac >- EVAL_TAC
    \\ simp[] )
  \\ impl_tac
  >- (
    simp[Abbr`s1`]
    \\ fs[ag32_ffi_write_code_def]
    \\ qx_gen_tac`j`
    \\ strip_tac
    \\ first_x_assum(qspec_then`j + LENGTH ag32_ffi_write_set_id_code`mp_tac)
    \\ impl_tac >- fs[]
    \\ simp[EL_APPEND_EQN, LEFT_ADD_DISTRIB, GSYM word_add_n2w] )
  \\ strip_tac
  \\ qspec_then`s1`mp_tac(Q.GEN`s`ag32_ffi_write_check_conf_thm)
  \\ impl_tac
  >- (
    simp[Abbr`s1`,APPLY_UPDATE_THM]
    \\ irule asmPropsTheory.bytes_in_memory_change_mem
    \\ goal_assum(last_assum o mp_then Any mp_tac)
    \\ simp[APPLY_UPDATE_THM] \\ rw[]
    \\ drule_then drule
        (GEN_ALL asmPropsTheory.bytes_in_memory_all_pcs
         |> SIMP_RULE(srw_ss())[asmPropsTheory.all_pcs_thm, SUBSET_DEF, PULL_EXISTS]
         |> CONV_RULE SWAP_FORALL_CONV |> Q.SPEC`0`
         |> SIMP_RULE(srw_ss())[])
    \\ qhdtm_x_assum`DISJOINT`mp_tac
    \\ simp[IN_DISJOINT, data_to_word_assignProofTheory.IMP]
    \\ ntac 2 strip_tac \\ first_x_assum drule
    \\ qpat_x_assum`_ = _`(assume_tac o SYM)
    \\ simp[]
    \\ EVAL_TAC
    \\ Cases_on`r0` \\ fs[memory_size_def, word_add_n2w]
    \\ fs[word_ls_n2w, word_lo_n2w] )
  \\ strip_tac
  \\ qmatch_asmsub_abbrev_tac`_ = s2`
  \\ `s2.MEM = s1.MEM` by simp[Abbr`s2`]
  \\ qspec_then`s2`mp_tac(Q.GEN`s`ag32_ffi_write_load_noff_code_thm)
  \\ `byte_aligned s2.PC` by (
    simp[Abbr`s2`]
    \\ irule byte_aligned_add
    \\ reverse conj_tac >- EVAL_TAC
    \\ simp[] )
  \\ impl_tac
  >- (
    simp[]
    \\ simp[Abbr`s2`]
    \\ fs[ag32_ffi_write_code_def]
    \\ qx_gen_tac`j`
    \\ strip_tac
    \\ first_x_assum(qspec_then`j + LENGTH ag32_ffi_write_set_id_code
                                  + LENGTH ag32_ffi_write_check_conf_code`mp_tac)
    \\ impl_tac >- fs[]
    \\ simp[EL_APPEND_EQN, LEFT_ADD_DISTRIB, GSYM word_add_n2w, Abbr`s1`]
    \\ qmatch_goalsub_abbrev_tac`get_mem_word _ y`
    \\ strip_tac
    \\ qmatch_goalsub_abbrev_tac`get_mem_word _ x`
    \\ `x = y` by (simp[Abbr`x`, Abbr`y`] \\ EVAL_TAC \\ simp[])
    \\ fs[])
  \\ strip_tac
  \\ qspec_then`s2`mp_tac(Q.GEN`s`ag32_ffi_write_load_noff_thm)
  \\ impl_tac
  >- (
    simp[Abbr`s2`,APPLY_UPDATE_THM]
    \\ simp[Abbr`s1`, APPLY_UPDATE_THM]
    \\ irule asmPropsTheory.bytes_in_memory_change_mem
    \\ goal_assum(last_assum o mp_then Any mp_tac)
    \\ simp[APPLY_UPDATE_THM] \\ rw[]
    \\ drule_then (drule o SIMP_RULE(srw_ss())[])
        (GEN_ALL asmPropsTheory.bytes_in_memory_all_pcs
         |> SIMP_RULE(srw_ss())[asmPropsTheory.all_pcs_thm, SUBSET_DEF, PULL_EXISTS]
         |> CONV_RULE SWAP_FORALL_CONV |> Q.SPEC`0`
         |> SIMP_RULE(srw_ss())[])
    \\ qhdtm_x_assum`DISJOINT`mp_tac
    \\ simp[IN_DISJOINT, data_to_word_assignProofTheory.IMP]
    \\ ntac 2 strip_tac \\ first_x_assum drule
    \\ qpat_x_assum`_ = _`(assume_tac o SYM)
    \\ simp[]
    \\ EVAL_TAC
    \\ Cases_on`r0` \\ fs[memory_size_def, word_add_n2w]
    \\ fs[word_ls_n2w, word_lo_n2w] )
  \\ strip_tac
  \\ qmatch_asmsub_abbrev_tac`_ = s3`
  \\ `s3.MEM = s1.MEM` by fs[Abbr`s3`, Abbr`s2`]
  \\ `byte_aligned s3.PC` by (
    simp[Abbr`s3`]
    \\ irule byte_aligned_add
    \\ reverse conj_tac >- EVAL_TAC
    \\ simp[] )
  \\ simp[]
  \\ qspec_then`s3`mp_tac(Q.GEN`s`ag32_ffi_write_check_lengths_code_thm)
  \\ impl_tac
  >- (
    simp[]
    \\ fs[ag32_ffi_write_code_def]
    \\ qx_gen_tac`j`
    \\ strip_tac
    \\ first_x_assum(qspec_then`j + LENGTH ag32_ffi_write_set_id_code
                                  + LENGTH ag32_ffi_write_check_conf_code
                                  + LENGTH ag32_ffi_write_load_noff_code`mp_tac)
    \\ impl_tac >- fs[]
    \\ simp[EL_APPEND_EQN, LEFT_ADD_DISTRIB, GSYM word_add_n2w, Abbr`s1`]
    \\ qmatch_goalsub_abbrev_tac`get_mem_word _ y`
    \\ strip_tac
    \\ qmatch_goalsub_abbrev_tac`get_mem_word _ x`
    \\ `x = y` by (simp[Abbr`x`, Abbr`y`, Abbr`s3`, Abbr`s2`] \\ EVAL_TAC \\ simp[])
    \\ fs[])
  \\ strip_tac
  \\ reverse IF_CASES_TAC
  >- (
    qmatch_asmsub_abbrev_tac`FUNPOW _ _ _ = s4`
    \\ `s4.MEM = s1.MEM` by fs[Abbr`s4`, ag32_ffi_write_check_lengths_MEM]
    \\ qmatch_goalsub_abbrev_tac`ag32_ffi_return s5`
    \\ qspec_then`s5`mp_tac(Q.GEN`s`ag32_ffi_return_code_thm)
    \\ qspec_then`s3`mp_tac (Q.GEN`s`ag32_ffi_write_check_lengths_PC)
    \\ simp[]
    \\ strip_tac
    \\ impl_tac
    >- (
      simp[Abbr`s5`, ag32Theory.dfn'StoreMEMByte_def, ag32Theory.incPC_def, ag32Theory.ri2word_def]
      \\ `s4.R 3w = s.R 3w`
      by (
        simp[Abbr`s4`, ag32_ffi_write_check_lengths_R]
        \\ simp[Abbr`s3`, APPLY_UPDATE_THM]
        \\ simp[Abbr`s2`, APPLY_UPDATE_THM]
        \\ simp[Abbr`s1`, APPLY_UPDATE_THM] )
      \\ reverse conj_tac
      >- (
        CONV_TAC(RAND_CONV EVAL)
        \\ simp[]
        \\ irule byte_aligned_add
        \\ simp[]
        \\ EVAL_TAC )
      \\ qx_gen_tac`j`
      \\ first_x_assum(qspec_then`j + LENGTH ag32_ffi_write_code
                                    - LENGTH ag32_ffi_return_code`mp_tac)
      \\ simp[ag32_ffi_write_code_def]
      \\ simp[EL_APPEND_EQN, LEFT_ADD_DISTRIB, GSYM word_add_n2w, Abbr`s1`]
      \\ ntac 2 strip_tac
      \\ first_x_assum drule
      \\ disch_then(SUBST1_TAC o SYM)
      \\ qmatch_goalsub_abbrev_tac`get_mem_word _ y = get_mem_word _ x`
      \\ `x = y` by (simp[Abbr`x`, Abbr`y`, Abbr`s3`, Abbr`s2`] \\ EVAL_TAC \\ simp[])
      \\ simp[APPLY_UPDATE_THM, get_mem_word_def]
      \\ pop_assum kall_tac
      \\ simp[Abbr`y`]
      \\ EVAL_TAC \\ simp[]
      \\ simp[Abbr`s3`, Abbr`s2`]
      \\ EVAL_TAC
      \\ simp[]
      \\ Cases_on`r0` \\ fs[memory_size_def, word_add_n2w]
      \\ qpat_x_assum`j < _`mp_tac \\ EVAL_TAC \\ strip_tac
      \\ simp[]
      \\ fs[asmSemTheory.bytes_in_memory_def]
      \\ qhdtm_x_assum`DISJOINT`mp_tac
      \\ qhdtm_x_assum`DISJOINT`mp_tac
      \\ simp[IN_DISJOINT]
      \\ EVAL_TAC
      \\ simp[data_to_word_assignProofTheory.IMP]
      \\ ntac 2 strip_tac
      \\ res_tac
      \\ Cases_on`s.R 3w` \\ fs[word_add_n2w]
      \\ fs[word_ls_n2w,  word_lo_n2w]
      \\ rfs[])
    \\ strip_tac
    \\ pop_assum(SUBST1_TAC o SYM)
    \\ `s5 = Next s4`
    by (
      simp[ag32Theory.Next_def]
      \\ qmatch_goalsub_abbrev_tac`pc + 2w`
      \\ pop_assum mp_tac
      \\ DEP_REWRITE_TAC[byte_aligned_imp]
      \\ conj_tac
      >- (
        CONV_TAC(RAND_CONV EVAL)
        \\ simp[]
        \\ irule byte_aligned_add
        \\ simp[]
        \\ EVAL_TAC )
      \\ simp[GSYM get_mem_word_def]
      \\ CONV_TAC(LAND_CONV EVAL) \\ simp[]
      \\ strip_tac \\ simp[Abbr`pc`]
      \\ first_x_assum(qspec_then`LENGTH ag32_ffi_write_set_id_code + (352 DIV 4)`mp_tac)
      \\ impl_tac >- EVAL_TAC
      \\ simp[]
      \\ qmatch_goalsub_abbrev_tac`get_mem_word s1mem`
      \\ simp[Abbr`s1`]
      \\ CONV_TAC(PATH_CONV"lrr"EVAL)
      \\ strip_tac
      \\ qmatch_goalsub_abbrev_tac`get_mem_word s1mem x`
      \\ qmatch_asmsub_abbrev_tac`get_mem_word s1mem y`
      \\ `x = y` by (
        simp[Abbr`x`,Abbr`y`]
        \\ simp[Abbr`s3`,Abbr`s2`]
        \\ EVAL_TAC
        \\ simp[] )
      \\ fs[]
      \\ simp[ag32_targetProofTheory.Decode_Encode]
      \\ simp[ag32Theory.Run_def] )
    \\ pop_assum SUBST1_TAC
    \\ qpat_x_assum`_ = s4`(SUBST1_TAC o SYM)
    \\ fs[] \\ rfs[]
    \\ qpat_x_assum`FUNPOW Next _ _ = s3`(SUBST1_TAC o SYM)
    \\ qpat_x_assum`FUNPOW Next _ _ = s2`(SUBST1_TAC o SYM)
    \\ qpat_x_assum`FUNPOW Next _ _ = s1`(SUBST1_TAC o SYM)
    \\ simp[GSYM FUNPOW_ADD, GSYM FUNPOW]
    \\ metis_tac[])
  \\ qspec_then`s3`mp_tac(GEN_ALL ag32_ffi_write_check_lengths_thm)
  \\ qmatch_asmsub_abbrev_tac`7w =+ n2w off`
  \\ qmatch_asmsub_abbrev_tac`6w =+ v2w [cnd]`
  \\ qmatch_asmsub_abbrev_tac`1w =+ n2w n`
  \\ disch_then(qspecl_then[`off`,`n`,`LENGTH tll`,`cnd`]mp_tac)
  \\ impl_tac
  >- (
    simp[Abbr`s3`, Abbr`s2`, APPLY_UPDATE_THM]
    \\ simp[Abbr`off`, Abbr`n`]
    \\ simp[MarshallingTheory.w22n_def]
    \\ Cases_on`n0` \\ Cases_on`n1` \\ fs[]
    \\ Cases_on`off0` \\ Cases_on`off1` \\ fs[]
    \\ fs[asmSemTheory.bytes_in_memory_def]
    \\ Cases_on`s1.R 4w` \\ fs[]
    \\ fs[Abbr`s1`, APPLY_UPDATE_THM]
    \\ simp[word_add_n2w] )
  \\ strip_tac
  \\ qmatch_asmsub_abbrev_tac`_ = s4`
  \\ `s4.MEM = s1.MEM` by simp[Abbr`s4`]
  \\ qspec_then`s4`mp_tac(Q.GEN`s`ag32_ffi_write_write_header_code_thm)
  \\ impl_tac
  >- (
    reverse conj_tac
    >- (
      simp[Abbr`s1`] \\ fs[]
      \\ simp[Abbr`s4`, APPLY_UPDATE_THM]
      \\ simp[Abbr`s3`, APPLY_UPDATE_THM]
      \\ simp[Abbr`s2`, APPLY_UPDATE_THM]
      \\ EVAL_TAC
      \\ simp[])
    \\ qx_gen_tac`j`
    \\ strip_tac
    \\ first_x_assum(qspec_then`j + LENGTH ag32_ffi_write_set_id_code
                                  + LENGTH ag32_ffi_write_check_conf_code
                                  + LENGTH ag32_ffi_write_load_noff_code
                                  + LENGTH ag32_ffi_write_check_lengths_code`mp_tac)
    \\ impl_tac >- (
      pop_assum mp_tac
      \\ EVAL_TAC \\ rw[] )
    \\ simp[ag32_ffi_write_code_def]
    \\ simp[EL_APPEND_EQN, LEFT_ADD_DISTRIB, GSYM word_add_n2w, Abbr`s1`]
    \\ qmatch_goalsub_abbrev_tac`get_mem_word _ y`
    \\ strip_tac
    \\ qmatch_goalsub_abbrev_tac`get_mem_word _ x`
    \\ `x = y` by (
      simp[Abbr`x`, Abbr`y`] \\ fs[]
      \\ simp[Abbr`s3`, Abbr`s2`]
      \\ EVAL_TAC \\ simp[])
    \\ fs[])
  \\ strip_tac
  \\ fs[]
  \\ qspec_then`s4`mp_tac(GEN_ALL ag32_ffi_write_write_header_thm)
  \\ disch_then(qspecl_then[`r0`,`n1`,`n0`,`conf`]mp_tac)
  \\ reverse(Cases_on`cnd`)
  >- (
    fs[Abbr`s4`]
    \\ qpat_x_assum`_ MOD _ = _`mp_tac
    \\ EVAL_TAC )
  \\ qpat_x_assum`Abbrev(T = _)`mp_tac
  \\ simp[markerTheory.Abbrev_def] \\ strip_tac
  \\ impl_tac
  >- (
    simp[]
    \\ simp[Abbr`s4`, APPLY_UPDATE_THM]
    \\ simp[Abbr`s3`, APPLY_UPDATE_THM]
    \\ simp[Abbr`s2`, APPLY_UPDATE_THM]
    \\ simp[Abbr`s1`, APPLY_UPDATE_THM]
    \\ fs[asmSemTheory.bytes_in_memory_def]
    \\ qpat_x_assum`s.R 3w ∈ _`mp_tac
    \\ qhdtm_x_assum`DISJOINT`mp_tac
    \\ simp[IN_DISJOINT, data_to_word_assignProofTheory.IMP]
    \\ ntac 2 strip_tac
    \\ first_x_assum drule
    \\ EVAL_TAC
    \\ Cases_on`r0` \\ Cases_on`s.R 3w` \\ fs[memory_size_def]
    \\ fs[word_add_n2w, word_ls_n2w, word_lo_n2w] )
  \\ strip_tac
  \\ qmatch_asmsub_abbrev_tac`_ = s5`
  \\ fs[]
  \\ qspec_then`s5`mp_tac(Q.GEN`s`ag32_ffi_write_num_written_code_thm)
  \\ `(∀k. k < LENGTH ag32_ffi_write_code ⇒
        (get_mem_word s5.MEM (s.PC + n2w (4 * k)) =
         Encode (EL k ag32_ffi_write_code)))`
  by (
    qx_gen_tac`j`
    \\ strip_tac
    \\ first_x_assum(qspec_then`j`mp_tac)
    \\ impl_tac >- fs[]
    \\ disch_then(SUBST1_TAC o SYM)
    \\ simp[]
    \\ simp[APPLY_UPDATE_THM, get_mem_word_def, Abbr`s5`]
    \\ EVAL_TAC \\ simp[]
    \\ simp[Abbr`s3`, Abbr`s2`,Abbr`s4`,APPLY_UPDATE_THM]
    \\ Cases_on`r0` \\ fs[memory_size_def, word_add_n2w]
    \\ qpat_x_assum`j < _`mp_tac \\ EVAL_TAC \\ strip_tac
    \\ simp[]
    \\ fs[asmSemTheory.bytes_in_memory_def]
    \\ qhdtm_x_assum`DISJOINT`mp_tac
    \\ qhdtm_x_assum`DISJOINT`mp_tac
    \\ simp[IN_DISJOINT]
    \\ EVAL_TAC
    \\ simp[data_to_word_assignProofTheory.IMP]
    \\ ntac 2 strip_tac
    \\ res_tac
    \\ `s1.R 3w = s.R 3w` by simp[Abbr`s1`,APPLY_UPDATE_THM]
    \\ Cases_on`s.R 3w` \\ fs[word_add_n2w]
    \\ fs[word_ls_n2w,  word_lo_n2w]
    \\ rfs[]
    \\ DEP_REWRITE_TAC[SIMP_RULE(srw_ss())[]asm_write_bytearray_unchanged]
    \\ fs[]
    \\ fs[word_ls_n2w, word_lo_n2w, word_add_n2w] )
  \\ impl_tac
  >- (
    conj_tac
    >- (
      qx_gen_tac`j`
      \\ strip_tac
      \\ first_x_assum(qspec_then`j + LENGTH ag32_ffi_write_set_id_code
                                    + LENGTH ag32_ffi_write_check_conf_code
                                    + LENGTH ag32_ffi_write_load_noff_code
                                    + LENGTH ag32_ffi_write_check_lengths_code
                                    + LENGTH ag32_ffi_write_write_header_code`mp_tac)
      \\ impl_tac >- (
        pop_assum mp_tac
        \\ EVAL_TAC \\ rw[] )
      \\ simp[ag32_ffi_write_code_def]
      \\ simp[EL_APPEND_EQN, LEFT_ADD_DISTRIB, GSYM word_add_n2w, Abbr`s1`]
      \\ qmatch_goalsub_abbrev_tac`get_mem_word _ y`
      \\ strip_tac
      \\ qmatch_goalsub_abbrev_tac`get_mem_word _ x`
      \\ first_x_assum(CHANGED_TAC o SUBST1_TAC o SYM)
      \\ `x = y` by (simp[Abbr`x`, Abbr`y`,Abbr`s5`,Abbr`s3`,Abbr`s2`] \\ EVAL_TAC \\ simp[])
      \\ fs[] )
    \\ simp[Abbr`s5`, APPLY_UPDATE_THM]
    \\ conj_tac
    >- (
      CONV_TAC(RAND_CONV EVAL)
      \\ simp[]
      \\ irule byte_aligned_add
      \\ simp[]
      \\ EVAL_TAC )
    \\ simp[Abbr`s3`, Abbr`s2`, Abbr`s4`, APPLY_UPDATE_THM, Abbr`s1`]
    \\ EVAL_TAC
    \\ simp[]
    \\ Cases_on`r0` \\ fs[memory_size_def, word_add_n2w]
    \\ simp[GSYM IMP_CONJ_THM, GSYM FORALL_AND_THM]
    \\ qx_gen_tac`j` \\ strip_tac
    \\ Cases_on`s.R 3w` \\ fs[word_add_n2w]
    \\ fs[DIV_LT_X]
    \\ fs[asmSemTheory.bytes_in_memory_def]
    \\ qpat_x_assum`n2w _ ∈ md`mp_tac
    \\ qhdtm_x_assum`DISJOINT`mp_tac
    \\ qhdtm_x_assum`DISJOINT`mp_tac
    \\ simp[IN_DISJOINT, data_to_word_assignProofTheory.IMP]
    \\ EVAL_TAC \\ simp[]
    \\ ntac 3 strip_tac
    \\ res_tac
    \\ fs[word_ls_n2w, word_lo_n2w, word_add_n2w]
    \\ rfs[])
  \\ strip_tac
  \\ `s5.R 3w = s.R 3w`
  by ( simp[Abbr`s5`, Abbr`s4`, Abbr`s3`, Abbr`s2`, Abbr`s1`, APPLY_UPDATE_THM] )
  \\ qspec_then`s5`mp_tac(CONV_RULE(RESORT_FORALL_CONV(sort_vars["s"]))(GEN_ALL ag32_ffi_write_num_written_thm))
  \\ simp[]
  \\ fs[asmSemTheory.bytes_in_memory_def]
  \\ `s4.R 3w = s.R 3w` by simp[Abbr`s4`, Abbr`s3`, Abbr`s2`, Abbr`s1`,APPLY_UPDATE_THM]
  \\ `s5.R 1w = n2w n`by simp[Abbr`s5`, Abbr`s4`, Abbr`s3`, APPLY_UPDATE_THM]
  \\ simp[]
  \\ disch_then(qspecl_then[`tll`,`n`,`md`]mp_tac)
  \\ impl_keep_tac
  >- (
    simp[]
    \\ simp[Abbr`s5`,APPLY_UPDATE_THM]
    \\ reverse conj_tac
    >- (
      simp[Abbr`n`,MarshallingTheory.w22n_def]
      \\ Cases_on`n0` \\Cases_on`n1` \\ fs[] )
    \\ irule asmPropsTheory.bytes_in_memory_change_mem
    \\ qexists_tac`s.MEM` \\ simp[]
    \\ simp[APPLY_UPDATE_THM]
    \\ Cases_on`s.R 3w` \\ simp[word_add_n2w] \\ fs[]
    \\ gen_tac \\ strip_tac
    \\ DEP_REWRITE_TAC[SIMP_RULE(srw_ss())[]asm_write_bytearray_unchanged]
    \\ simp[Abbr`s1`,APPLY_UPDATE_THM]
    \\ EVAL_TAC
    \\ Cases_on`r0` \\ fs[word_add_n2w, memory_size_def]
    \\ fs[word_ls_n2w,word_lo_n2w]
    \\ drule (GEN_ALL asmPropsTheory.bytes_in_memory_all_pcs)
    \\ disch_then(qspec_then`0`mp_tac)
    \\ simp[asmPropsTheory.all_pcs_thm, SUBSET_DEF, PULL_EXISTS]
    \\ disch_then drule
    \\ qhdtm_assum`DISJOINT`mp_tac
    \\ simp_tac (srw_ss()) [IN_DISJOINT,data_to_word_assignProofTheory.IMP]
    \\ ntac 2 strip_tac
    \\ first_x_assum drule
    \\ EVAL_TAC \\ simp[] )
  \\ strip_tac
  \\ qmatch_asmsub_abbrev_tac`_ = s6`
  \\ fs[]
  \\ qspec_then`s6`mp_tac ag32_ffi_write_copy_code_thm
  \\ `byte_aligned s6.PC`
  by (
    simp[Abbr`s6`]
    \\ irule byte_aligned_add
    \\ reverse conj_tac >- EVAL_TAC
    \\ simp[Abbr`s5`]
    \\ CONV_TAC(RAND_CONV EVAL)
    \\ simp[]
    \\ irule byte_aligned_add
    \\ reverse conj_tac >- EVAL_TAC
    \\ simp[] )
  \\ `s6.R 5w = r0 + n2w (output_offset + 12)`
  by (
    simp[Abbr`s6`, APPLY_UPDATE_THM]
    \\ simp[Abbr`s5`, APPLY_UPDATE_THM])
  \\ `s6.R 1w = n2w (MIN n output_buffer_size)`
  by (
    simp[Abbr`s6`, APPLY_UPDATE_THM]
    \\ simp[Abbr`s5`, APPLY_UPDATE_THM])
  \\ `s6.PC = r0 + n2w (ffi_code_start_offset + ag32_ffi_write_entrypoint +
                        4 * LENGTH ag32_ffi_write_set_id_code +
                        4 * LENGTH ag32_ffi_write_check_conf_code +
                        4 * LENGTH ag32_ffi_write_load_noff_code +
                        4 * LENGTH ag32_ffi_write_check_lengths_code +
                        4 * LENGTH ag32_ffi_write_write_header_code +
                        4 * LENGTH ag32_ffi_write_num_written_code )`
  by (
    simp[Abbr`s6`,Abbr`s5`,Abbr`s3`,Abbr`s2`,Abbr`s1`]
    \\ EVAL_TAC \\ simp[] )
  \\ qmatch_asmsub_abbrev_tac`s6.PC = r0 + n2w wcoff`
  \\ `(∀k. k < LENGTH ag32_ffi_write_code ⇒
        (get_mem_word s6.MEM (s.PC + n2w (4 * k)) =
         Encode (EL k ag32_ffi_write_code)))`
  by (
    qx_gen_tac`j`
    \\ strip_tac
    \\ full_simp_tac std_ss [GSYM ADD_ASSOC]
    \\ qmatch_asmsub_abbrev_tac`wcoff = _ + (_ + wcr)`
    \\ first_x_assum(qspec_then`j`mp_tac)
    \\ impl_tac >- (
      simp[Abbr`wcr`]
      \\ pop_assum mp_tac
      \\ EVAL_TAC \\ rw[] )
    \\ simp[]
    \\ qmatch_goalsub_abbrev_tac`get_mem_word _ y`
    \\ simp[get_mem_word_def,APPLY_UPDATE_THM,Abbr`s6`]
    \\ DEP_REWRITE_TAC[SIMP_RULE(srw_ss())[]asm_write_bytearray_unchanged]
    \\ simp[Abbr`y`,Abbr`wcoff`]
    \\ EVAL_TAC
    \\ Cases_on`r0` \\ fs[memory_size_def, word_add_n2w]
    \\ Cases_on`s.R 3w` \\ fs[word_add_n2w]
    \\ fs[word_ls_n2w, word_lo_n2w]
    \\ fs[GSYM word_add_n2w]
    \\ qpat_x_assum`n2w _ ∈ _`mp_tac
    \\ qhdtm_x_assum`DISJOINT`mp_tac
    \\ simp_tac (srw_ss()) [IN_DISJOINT,data_to_word_assignProofTheory.IMP]
    \\ EVAL_TAC
    \\ ntac 2 strip_tac
    \\ first_x_assum drule
    \\ simp[]
    \\ simp[word_ls_n2w, word_lo_n2w]
    \\ qpat_x_assum`j < _`mp_tac
    \\ EVAL_TAC
    \\ simp[])
  \\ impl_keep_tac
  >- (
    simp[]
    \\ reverse conj_tac
    >- (
      qpat_x_assum`Abbrev(wcoff = _)`mp_tac
      \\ EVAL_TAC
      \\ strip_tac \\ simp[Abbr`wcoff`]
      \\ Cases_on`r0` \\ fs[memory_size_def, word_add_n2w]
      \\ conj_tac >- rw[MIN_DEF]
      \\ simp[IN_DISJOINT, PULL_FORALL, data_to_word_assignProofTheory.IMP, PULL_EXISTS]
      \\ rpt gen_tac \\ strip_tac
      \\ simp[DIV_LT_X]
      \\ strip_tac
      \\ strip_tac
      \\ qpat_x_assum`_ = _`mp_tac
      \\ simp[] )
    \\ qx_gen_tac`j`
    \\ strip_tac
    \\ full_simp_tac std_ss [GSYM ADD_ASSOC]
    \\ qmatch_asmsub_abbrev_tac`wcoff = _ + (_ + wcr)`
    \\ first_x_assum(qspec_then`j + wcr DIV 4`mp_tac)
    \\ impl_tac >- (
      simp[Abbr`wcr`]
      \\ pop_assum mp_tac
      \\ EVAL_TAC \\ rw[] )
    \\ simp[ag32_ffi_write_code_def]
    \\ simp[EL_APPEND_EQN, GSYM LEFT_ADD_DISTRIB, GSYM word_add_n2w, Abbr`s1`, Abbr`wcr`]
    \\ once_rewrite_tac[MULT_COMM] \\ simp[MULT_DIV]
    \\ simp[LEFT_ADD_DISTRIB]
    \\ qmatch_goalsub_abbrev_tac`get_mem_word _ y`
    \\ strip_tac
    \\ qmatch_goalsub_abbrev_tac`get_mem_word _ x`
    \\ first_x_assum(CHANGED_TAC o SUBST1_TAC o SYM)
    \\ `x = y` by (
      simp[Abbr`x`, Abbr`y`,Abbr`wcoff`]
      \\ EVAL_TAC \\ simp[GSYM word_add_n2w] )
    \\ simp[])
  \\ strip_tac
  \\ qspec_then`s6`mp_tac ag32_ffi_write_copy_thm
  \\ `s6.R 3w = s5.R 3w + 4w + n2w off`
  by (
    simp[Abbr`s6`, APPLY_UPDATE_THM]
    \\ simp[Abbr`s5`, APPLY_UPDATE_THM]
    \\ simp[Abbr`s4`, APPLY_UPDATE_THM]
    \\ simp[Abbr`s3`, APPLY_UPDATE_THM] )
  \\ simp[]
  \\ disch_then(qspec_then`TAKE (MIN n output_buffer_size) (DROP off tll)`mp_tac)
  \\ simp[]
  \\ qmatch_asmsub_abbrev_tac`COND cnd`
  \\ `cnd`
  by (
    fs[Abbr`s4`]
    \\ Cases_on`cnd` \\ fs[]
    \\ qpat_x_assum`_ MOD _ = _`mp_tac
    \\ EVAL_TAC )
  \\ qunabbrev_tac`cnd` \\ fs[]
  \\ impl_tac >- (
    reverse conj_tac
    >- (
      Cases_on`s.R 3w` \\ fs[word_add_n2w]
      \\ EVAL_TAC
      \\ Cases_on`r0` \\ fs[memory_size_def, word_add_n2w]
      \\ simp[MIN_DEF]
      \\ simp[IN_DISJOINT]
      \\ Cases
      \\ fs[word_ls_n2w, word_lo_n2w]
      \\ CCONTR_TAC \\ fs[]
      \\ qhdtm_x_assum`DISJOINT`mp_tac
      \\ qhdtm_x_assum`DISJOINT`mp_tac
      \\ EVAL_TAC
      \\ simp[IN_DISJOINT, data_to_word_assignProofTheory.IMP]
      \\ strip_tac
      \\ first_x_assum drule
      \\ fs[word_ls_n2w, word_lo_n2w] )
    \\ `tll = TAKE off tll ++ DROP off tll` by metis_tac[TAKE_DROP]
    \\ qhdtm_x_assum`bytes_in_memory`mp_tac
    \\ pop_assum(fn th => CONV_TAC(LAND_CONV(ONCE_REWRITE_CONV[th])))
    \\ disch_then(mp_then Any mp_tac (#1(EQ_IMP_RULE (SPEC_ALL asmPropsTheory.bytes_in_memory_APPEND))))
    \\ simp[] \\ strip_tac
    \\ qmatch_goalsub_abbrev_tac`TAKE kk ll`
    \\ `ll = TAKE kk ll ++ DROP kk ll` by metis_tac[TAKE_DROP]
    \\ qhdtm_x_assum`bytes_in_memory`mp_tac
    \\ pop_assum(fn th => CONV_TAC(LAND_CONV(ONCE_REWRITE_CONV[th])))
    \\ disch_then(mp_then Any mp_tac (#1(EQ_IMP_RULE (SPEC_ALL asmPropsTheory.bytes_in_memory_APPEND))))
    \\ strip_tac
    \\ irule asmPropsTheory.bytes_in_memory_change_mem
    \\ goal_assum(first_assum o mp_then Any mp_tac)
    \\ simp[Abbr`s6`]
    \\ gen_tac \\ strip_tac
    \\ DEP_REWRITE_TAC[SIMP_RULE(srw_ss())[]asm_write_bytearray_unchanged]
    \\ Cases_on`s.R 3w`
    \\ simp[word_add_n2w, MarshallingTheory.n2w2_def]
    \\ simp[word_ls_n2w, word_lo_n2w]
    \\ fs[]
    \\ rfs[Abbr`ll`]
    \\ `kk ≤ n` by simp[Abbr`kk`]
    \\ fs[LENGTH_TAKE_EQ])
  \\ strip_tac
  \\ qmatch_asmsub_abbrev_tac`_ = s7`
  \\ fs[]
  \\ qspec_then`s7`mp_tac(Q.GEN`s`ag32_ffi_return_code_thm)
  \\ impl_tac >- (
    reverse conj_tac
    >- (
      simp[Abbr`s7`, Abbr`s6`, APPLY_UPDATE_THM, Abbr`wcoff`]
      \\ CONV_TAC(RAND_CONV EVAL) \\ simp[]
      \\ irule byte_aligned_add
      \\ simp[]
      \\ EVAL_TAC )
    \\ qx_gen_tac`j` \\ strip_tac
    \\ simp[Abbr`s7`]
    \\ `s6.R 2w = 32w` by simp[Abbr`s6`, APPLY_UPDATE_THM]
    \\ full_simp_tac std_ss [GSYM ADD_ASSOC]
    \\ qmatch_asmsub_abbrev_tac`wcoff = _ + (_ + wcr)`
    \\ qpat_x_assum`∀k. k < LENGTH ag32_ffi_write_code ⇒ _`
         (qspec_then`j + wcr DIV 4 + LENGTH ag32_ffi_write_copy_code + 1`mp_tac)
    \\ impl_tac >- (
      simp[Abbr`wcr`]
      \\ qpat_x_assum`j <_`mp_tac
      \\ EVAL_TAC \\ rw[] )
    \\ simp[ag32_ffi_write_code_def]
    \\ qpat_x_assum`j < _`mp_tac \\ strip_tac
    \\ simp[EL_APPEND_EQN, GSYM LEFT_ADD_DISTRIB, GSYM word_add_n2w, Abbr`s1`, Abbr`wcr`]
    \\ once_rewrite_tac[MULT_COMM] \\ simp[MULT_DIV]
    \\ simp[LEFT_ADD_DISTRIB]
    \\ qmatch_goalsub_abbrev_tac`get_mem_word _ y`
    \\ strip_tac
    \\ qmatch_goalsub_abbrev_tac`get_mem_word _ x`
    \\ first_x_assum(CHANGED_TAC o SUBST1_TAC o SYM)
    \\ `x = y` by (
      simp[Abbr`x`, Abbr`y`,Abbr`wcoff`]
      \\ EVAL_TAC \\ simp[GSYM word_add_n2w] )
    \\ qpat_x_assum`Abbrev(y = _)`kall_tac
    \\ pop_assum(SUBST_ALL_TAC o SYM)
    \\ simp[get_mem_word_def,APPLY_UPDATE_THM]
    \\ DEP_REWRITE_TAC[SIMP_RULE(srw_ss())[]asm_write_bytearray_unchanged]
    \\ simp[Abbr`x`,Abbr`wcoff`]
    \\ EVAL_TAC
    \\ Cases_on`r0` \\ fs[memory_size_def, word_add_n2w]
    \\ fs[word_add_n2w]
    \\ fs[word_ls_n2w, word_lo_n2w]
    \\ fs[GSYM word_add_n2w]
    \\ qpat_x_assum`j < _`mp_tac \\ EVAL_TAC
    \\ simp[MIN_DEF])
  \\ strip_tac
  \\ rpt(qpat_x_assum`FUNPOW Next _ _ = _`(assume_tac o SYM))
  \\ fs[]
  \\ simp[GSYM FUNPOW_ADD]
  \\ metis_tac[]);

(* open_in *)

val ag32_ffi_open_in_entrypoint_def = Define`
  ag32_ffi_open_in_entrypoint =
  ag32_ffi_write_entrypoint + 4 * LENGTH ag32_ffi_write_code`;

val ag32_ffi_open_in_code_def = Define`
  ag32_ffi_open_in_code = [Interrupt] (* TODO *)`;

(* open_out *)

val ag32_ffi_open_out_entrypoint_def = Define`
  ag32_ffi_open_out_entrypoint =
  ag32_ffi_open_in_entrypoint + 4 * LENGTH ag32_ffi_open_in_code`;

val ag32_ffi_open_out_code_def = Define`
  ag32_ffi_open_out_code = [Interrupt] (* TODO *)`;

(* close *)

val ag32_ffi_close_entrypoint_def = Define`
  ag32_ffi_close_entrypoint =
  ag32_ffi_open_out_entrypoint + 4 * LENGTH ag32_ffi_open_out_code`;

val ag32_ffi_close_code_def = Define`
  ag32_ffi_close_code = [Interrupt] (* TODO *)`;

(* FFI jumps
  - get byte array (length,pointer)s in (len_reg,ptr_reg) and (len2_reg,ptr2_reg) (these are r1-r4)
  - get return address in link_reg (r0)
  - PC is mem_start + ffi_jumps_offset + ffi_offset * index
  conventions on return (see ag32_ffi_interfer_def):
    r0 is the end of this ffi's code (i.e., entrypoint of the next ffi's code)
    r1-r8 are 0w
    overflow and carry are false
*)

val ffi_entrypoints_def = Define`
  ffi_entrypoints = [
    ("exit", ag32_ffi_exit_entrypoint);
    ("get_arg_count", ag32_ffi_get_arg_count_entrypoint);
    ("get_arg_length", ag32_ffi_get_arg_length_entrypoint);
    ("get_arg", ag32_ffi_get_arg_entrypoint);
    ("read", ag32_ffi_read_entrypoint);
    ("write", ag32_ffi_write_entrypoint);
    ("open_in", ag32_ffi_open_in_entrypoint);
    ("open_out", ag32_ffi_open_out_entrypoint);
    ("close", ag32_ffi_close_entrypoint)]`;

val ffi_exitpcs_def = Define`
  ffi_exitpcs = [
    ("exit", ffi_code_start_offset + ag32_ffi_get_arg_count_entrypoint);
    ("get_arg_count", ffi_code_start_offset + ag32_ffi_get_arg_length_entrypoint);
    ("get_arg_length", ffi_code_start_offset + ag32_ffi_get_arg_entrypoint);
    ("get_arg", ffi_code_start_offset + ag32_ffi_read_entrypoint);
    ("read", ffi_code_start_offset + ag32_ffi_write_entrypoint);
    ("write", ffi_code_start_offset + ag32_ffi_open_in_entrypoint);
    ("open_in", ffi_code_start_offset + ag32_ffi_open_out_entrypoint);
    ("open_out", ffi_code_start_offset + ag32_ffi_close_entrypoint);
    ("close", heap_start_offset) ]`;

val mk_jump_ag32_code_def = Define`
  mk_jump_ag32_code ffi_names name =
    let index = THE (INDEX_OF name ffi_names) in
    let entrypoint = THE (ALOOKUP ffi_entrypoints name) in
    let dist_to_ffi_code = length_ag32_ffi_code + heap_size + ffi_offset * index + 8 - entrypoint in
    [Encode(LoadConstant(5w, F, (22 >< 0)((n2w dist_to_ffi_code):word32)));
     Encode(LoadUpperConstant(5w, (31 >< 23)((n2w dist_to_ffi_code):word32)));
     Encode(Jump (fSub, 5w, Reg 5w));
     0w]`;

val ccache_jump_ag32_code_def = Define`
  ccache_jump_ag32_code = [Encode (Jump (fSnd, 0w, Reg 0w)); 0w; 0w; 0w]`;

val halt_jump_ag32_code_def = Define`
  halt_jump_ag32_code = [Encode (Jump (fAdd, 0w, Imm 0w)); 0w; 0w; 0w]`;

val ag32_ffi_jumps_def = Define`
  ag32_ffi_jumps ffi_names =
    FLAT (MAP (mk_jump_ag32_code ffi_names) ffi_names) ++ ccache_jump_ag32_code ++ halt_jump_ag32_code`;

val LENGTH_ag32_ffi_jumps =
  ``LENGTH (ag32_ffi_jumps nms)``
  |> EVAL
  |> SIMP_RULE(srw_ss()++LET_ss)
      [LENGTH_FLAT,MAP_MAP_o,o_DEF,mk_jump_ag32_code_def,
       Q.ISPEC`λx. 4n`SUM_MAP_K |> SIMP_RULE(srw_ss())[]]

val ag32_ffi_code_def = Define`
  ag32_ffi_code =
    MAP Encode (
      ag32_ffi_exit_code ++
      ag32_ffi_get_arg_count_code ++
      ag32_ffi_get_arg_length_code ++
      ag32_ffi_get_arg_code ++
      ag32_ffi_read_code ++
      ag32_ffi_write_code ++
      ag32_ffi_open_in_code ++
      ag32_ffi_open_out_code ++
      ag32_ffi_close_code)`;

val LENGTH_ag32_ffi_code = ``LENGTH ag32_ffi_code`` |> EVAL

val LENGTH_ag32_ffi_code_check = Q.store_thm("LENGTH_ag32_ffi_code_check",
  `4 * LENGTH ag32_ffi_code = length_ag32_ffi_code`,
  simp[LENGTH_ag32_ffi_code] \\ EVAL_TAC);

val code_start_offset_def = Define`
  code_start_offset num_ffis =
    ffi_jumps_offset +
    ffi_offset *
    (2 (* halt and ccache *) + num_ffis)`;

val startup_asm_code_def = Define`
  startup_asm_code
    (* r0: mem start reg: contains mem_start address, leave unaltered *)
    (* r1: temp reg *)
    (* r2: heap start reg: should be left with heap start address *)
    (* r3: temp reg - only required because of large immediates *)
    (* r4: heap end reg: should be left with heap end address *)
    (* desired initial words of heap:
         w0: bitmaps_ptr
         w1: bitmaps_ptr + bitmaps_length
         w2: bitmaps_ptr + bitmaps_length + bitmaps_buffer_length
         w3: code_buffer_ptr
         w4: code_buffer_ptr + code_buffer_length
       for now, we simply assume code_buffer_length and bitmaps_buffer_length are 0 (no Install)
       therefore, in our layout, we want to set things as follows:
       --------------- <- w1, w2
         CakeML data
       --------------- <- w0, w3, w4
         CakeML code
       --------------- <- start PC
    *)
    num_ffis (code_length:word32) bitmaps_length =
    (*
      r1 <- heap_start_offset
      r2 <- r0 + r1
      r1 <- (code_start_offset num_ffis)
      r4 <- r0 + r1
      r1 <- code_length
      r4 <- r4 + r1
      m[r2+0] <- r4
      m[r2+3] <- r4
      m[r2+4] <- r4
      r1 <- bitmaps_length
      r4 <- r4 + r1
      m[r2+1] <- r4
      m[r2+2] <- r4
      r1 <- heap_size
      r4 <- r2 + r1
      r1 <- (code_start_offset num_ffis)
      r1 <- r0 + r1
      jump r1
    *)
    [Inst (Const 1 (n2w heap_start_offset));
     Inst (Arith (Binop Add 2 0 (Reg 1)));
     Inst (Const 1 (n2w (code_start_offset num_ffis)));
     Inst (Arith (Binop Add 4 0 (Reg 1)));
     Inst (Const 1 code_length);
     Inst (Arith (Binop Add 4 4 (Reg 1)));
     Inst (Mem Store 4 (Addr 2 (0w * bytes_in_word)));
     Inst (Mem Store 4 (Addr 2 (3w * bytes_in_word)));
     Inst (Mem Store 4 (Addr 2 (4w * bytes_in_word)));
     Inst (Const 1 bitmaps_length);
     Inst (Arith (Binop Add 4 4 (Reg 1)));
     Inst (Mem Store 4 (Addr 2 (1w * bytes_in_word)));
     Inst (Mem Store 4 (Addr 2 (2w * bytes_in_word)));
     Inst (Const 1 (n2w heap_size));
     Inst (Arith (Binop Add 4 2 (Reg 1)));
     Inst (Const 1 (n2w (code_start_offset num_ffis)));
     Inst (Arith (Binop Add 1 0 (Reg 1)));
     JumpReg 1]`;

val LENGTH_startup_asm_code = save_thm("LENGTH_startup_asm_code",
  ``LENGTH (startup_asm_code n cl bl)`` |> EVAL);

val startup_asm_code_small_enough = Q.store_thm("startup_asm_code_small_enough",
  `∀i. LENGTH (ag32_enc i) * LENGTH (startup_asm_code n cl bl) ≤ startup_code_size`,
  gen_tac (* change startup_code_size definition if this does not go through *)
  \\ qspec_then`i`mp_tac (Q.GEN`istr`ag32_enc_lengths)
  \\ rw[LENGTH_startup_asm_code, startup_code_size_def]);

val ag32_prog_addresses_def = Define`
  ag32_prog_addresses num_ffis LENGTH_code LENGTH_data r0 =
    { w | r0 + n2w heap_start_offset <=+ w ∧ w <+ r0 + n2w (heap_start_offset + heap_size) } ∪
    { w | r0 + n2w (code_start_offset num_ffis) <=+ w ∧
          w <+ r0 + n2w (code_start_offset num_ffis + LENGTH_code + 4 * LENGTH_data) } `;

val ag32_startup_addresses_def = Define`
  ag32_startup_addresses r0 =
      { w | r0 <=+ w ∧ w <+ r0 + n2w startup_code_size } ∪
      { w | r0 + n2w heap_start_offset <=+ w ∧ w <+ r0 + n2w (heap_start_offset + 4 * 5) }`;

val ag32_ccache_interfer_def = Define`
  ag32_ccache_interfer num_ffis r0 (_,_,ms) =
    ms with <| PC := (ms.R 0w) ;
               R := (0w =+ r0 + n2w (ffi_jumps_offset + num_ffis * ffi_offset + 4)) ms.R |>`;

val ag32_ffi_write_mem_update_def = Define`
  ag32_ffi_write_mem_update name r0 conf bytes new_bytes mem =
    if (name = "write") ∧ (HD new_bytes = 0w) then
      case bytes of (n1 :: n0 :: off1 :: off0 :: tll) =>
        let k = MIN (w22n [n1; n0]) output_buffer_size in
        let written = TAKE k (DROP (w22n [off1; off0]) tll) in
          asm_write_bytearray (r0 + n2w output_offset) (conf ++ [0w;0w;n1;n0] ++ written) mem
    else mem`;

val ag32_ffi_interfer_def = Define`
  ag32_ffi_interfer ffi_names md r0 (index,new_bytes,ms) =
    let name = EL index ffi_names in
    let new_mem = ((r0 + n2w (ffi_code_start_offset - 1)) =+ n2w (THE (ALOOKUP FFI_codes name))) ms.MEM in
    let new_mem = asm_write_bytearray (ms.R 3w) new_bytes new_mem in
    let new_mem =
      ag32_ffi_write_mem_update name r0
        (THE (read_bytearray (ms.R 1w) (w2n (ms.R 2w)) (λa. if a ∈ md then SOME (ms.MEM a) else NONE)))
        (THE (read_bytearray (ms.R 3w) (w2n (ms.R 4w)) (λa. if a ∈ md then SOME (ms.MEM a) else NONE)))
        new_bytes new_mem in
    let exitpc = THE (ALOOKUP ffi_exitpcs name) in
        ms with
          <| PC := (ms.R 0w) ;
             R := ((0w =+ r0 + n2w exitpc)
                   ((1w =+ 0w)
                   ((2w =+ 0w)
                   ((3w =+ 0w)
                   ((4w =+ 0w)
                   ((5w =+ 0w)
                   ((6w =+ 0w)
                   ((7w =+ 0w)
                   ((8w =+ 0w) (ms.R)))))))))) ;
             CarryFlag := F ;
             OverflowFlag := F ;
             io_events := ms.io_events ++ [new_mem] ;
             MEM := new_mem |>`;

val ag32_machine_config_def = Define`
  ag32_machine_config ffi_names LENGTH_code LENGTH_data r0 =
  let num_ffis = LENGTH ffi_names in
  let md = ag32_prog_addresses num_ffis LENGTH_code LENGTH_data r0 in
  <|
    target := ag32_target;
    ptr_reg := 1;
    len_reg := 2;
    ptr2_reg := 3;
    len2_reg := 4;
    callee_saved_regs := [60; 61; 62];
    ffi_names := ffi_names ;
    ffi_entry_pcs := GENLIST (λi. r0 + n2w (ffi_jumps_offset + i * ffi_offset)) num_ffis;
    ccache_pc     := r0 + n2w (ffi_jumps_offset + (num_ffis + 0) * ffi_offset);
    halt_pc       := r0 + n2w (ffi_jumps_offset + (num_ffis + 1) * ffi_offset);
    prog_addresses := md ;
    next_interfer := K I ;
    ccache_interfer := K (ag32_ccache_interfer num_ffis r0) ;
    ffi_interfer := K (ag32_ffi_interfer ffi_names md r0)
  |>`

val is_ag32_machine_config_ag32_machine_config = Q.store_thm("is_ag32_machine_config_ag32_machine_config",
  `is_ag32_machine_config (ag32_machine_config a b c r0)`, EVAL_TAC);

val ag32_ffi_mem_domain_def = Define`
  ag32_ffi_mem_domain r0 =
    { w | r0 + n2w startup_code_size <=+ w ∧
          w <+ r0 + n2w ffi_code_start_offset }`;

val ag32_ffi_mem_domain_DISJOINT_prog_addresses = Q.store_thm("ag32_ffi_mem_domain_DISJOINT_prog_addresses",
  `num_ffis ≤ LENGTH FFI_codes ∧
   w2n (r0:word32) + memory_size < dimword (:32) ∧
   code_start_offset num_ffis + lc + ld ≤ memory_size
   ⇒
   DISJOINT (ag32_ffi_mem_domain r0) (ag32_prog_addresses num_ffis lc ld r0)`,
  EVAL_TAC
  \\ Cases_on`r0`
  \\ strip_tac
  \\ simp[IN_DISJOINT, PULL_FORALL]
  \\ rpt Cases
  \\ fs[LEFT_ADD_DISTRIB]
  \\ fs[word_lo_n2w, word_ls_n2w, word_add_n2w]
  \\ rfs[]);

val ag32_ffi_write_thm = Q.store_thm("ag32_ffi_write_thm",
  `bytes_in_memory (s.R 1w) conf s.MEM md ∧
   bytes_in_memory (s.R 3w) bytes s.MEM md ∧
   Abbrev(md = ag32_prog_addresses (LENGTH ffi_names) lc ld r0) ∧
   byte_aligned r0 ∧ w2n r0 + memory_size < dimword(:32) ∧
   LENGTH ffi_names ≤ LENGTH FFI_codes ∧
   code_start_offset (LENGTH ffi_names) + lc + 4 * ld < memory_size ∧
   (w2n (s.R 2w) = LENGTH conf) ∧
   (w2n (s.R 4w) = LENGTH bytes) ∧ w2n (s.R 3w) + LENGTH bytes < dimword(:32) (* ≤ w2n r0 + memory_size *) ∧
   (INDEX_OF "write" ffi_names = SOME index) ∧
   (ffi_write conf bytes fs = SOME (FFIreturn new_bytes fs')) ∧
   (fs.numchars = LGENLIST (K output_buffer_size) NONE) ∧
   (∀fd. IS_SOME (ALOOKUP fs.infds fd) ⇔ fd < 3) ∧ (* TODO: this will need to weaken *)
   (∀fd fnm off. (ALOOKUP fs.infds fd = SOME (fnm,off)) ⇒ IS_SOME(ALOOKUP fs.files fnm)) ∧
   (s.PC = r0 + n2w (ffi_code_start_offset + THE (ALOOKUP ffi_entrypoints "write")))
   ⇒
   (ag32_ffi_write s = ag32_ffi_interfer ffi_names md r0 (index, new_bytes, s))`,
  rw[ag32_ffi_interfer_def]
  \\ fs[GSYM find_index_INDEX_OF]
  \\ imp_res_tac find_index_is_MEM
  \\ imp_res_tac find_index_MEM
  \\ first_x_assum(qspec_then`0`mp_tac) \\ rw[]
  \\ simp[ag32_ffi_write_def]
  \\ qmatch_goalsub_abbrev_tac`ag32_ffi_return s'`
  \\ simp[ag32_ffi_return_thm]
  \\ simp[ag32Theory.ag32_state_component_equality]
  \\ qmatch_asmsub_abbrev_tac`if (s1.PC = _) then _ else _`
  \\ mp_tac ag32_ffi_write_set_id_thm
  \\ impl_tac
  >- ( simp[] \\ EVAL_TAC )
  \\ strip_tac \\ fs[]
  \\ pop_assum kall_tac
  \\ qmatch_asmsub_abbrev_tac`ag32_ffi_write_check_conf s2`
  \\ qspec_then`s2`mp_tac(Q.GENL[`s`]ag32_ffi_write_check_conf_thm)
  \\ impl_tac
  >- (
    simp[Abbr`s2`,APPLY_UPDATE_THM]
    \\ irule asmPropsTheory.bytes_in_memory_change_mem
    \\ goal_assum(first_assum o mp_then Any mp_tac)
    \\ rw[APPLY_UPDATE_THM]
    \\ imp_res_tac asmPropsTheory.bytes_in_memory_all_pcs
    \\ first_x_assum(qspec_then`0`mp_tac)
    \\ simp[asmPropsTheory.all_pcs_thm, SUBSET_DEF, PULL_EXISTS]
    \\ disch_then drule
    \\ simp[Abbr`md`]
    \\ simp[ag32_prog_addresses_def]
    \\ qpat_x_assum`r0 + _ = _`(assume_tac o SYM)
    \\ simp[]
    \\ EVAL_TAC
    \\ Cases_on`r0` \\ fs[word_add_n2w, memory_size_def]
    \\ fs[word_ls_n2w, word_lo_n2w, FFI_codes_def] )
  \\ strip_tac \\ fs[]
  \\ qmatch_asmsub_abbrev_tac`ag32_ffi_write_load_noff s3`
  \\ qpat_x_assum`_ = s3`kall_tac
  \\ fs[Abbr`s2`, APPLY_UPDATE_THM]
  \\ fs[fsFFITheory.ffi_write_def, CaseEq"list"]
  \\ rveq
  \\ qspec_then`s3`mp_tac(Q.GENL[`s`]ag32_ffi_write_load_noff_thm)
  \\ impl_tac
  >- (
    simp[Abbr`s3`,APPLY_UPDATE_THM]
    \\ irule asmPropsTheory.bytes_in_memory_change_mem
    \\ goal_assum(first_assum o mp_then Any mp_tac)
    \\ rw[APPLY_UPDATE_THM]
    \\ imp_res_tac asmPropsTheory.bytes_in_memory_all_pcs
    \\ first_x_assum(qspec_then`0`mp_tac)
    \\ first_x_assum(qspec_then`0`mp_tac)
    \\ simp[asmPropsTheory.all_pcs_thm, SUBSET_DEF, PULL_EXISTS]
    \\ disch_then drule
    \\ simp[Abbr`md`]
    \\ simp[ag32_prog_addresses_def]
    \\ qpat_x_assum`r0 + _ = _`(assume_tac o SYM)
    \\ simp[]
    \\ EVAL_TAC
    \\ Cases_on`r0` \\ fs[word_add_n2w, memory_size_def]
    \\ fs[word_ls_n2w, word_lo_n2w, FFI_codes_def] )
  \\ strip_tac \\ fs[]
  \\ pop_assum kall_tac
  \\ fs[APPLY_UPDATE_THM]
  \\ qmatch_asmsub_abbrev_tac`ag32_ffi_write_check_lengths s2`
  \\ qspec_then`s2`mp_tac(Q.GENL[`s`,`ltll`,`off`,`n`,`cnd`]ag32_ffi_write_check_lengths_thm)
  \\ disch_then(qspecl_then[`LENGTH tll`,`w22n [off1; off0]`,`w22n [n1; n0]`,
                            `(LENGTH conf = 8) ∧ w82n conf < 3`]mp_tac)
  \\ impl_tac
  >- (
    simp[Abbr`s2`,Abbr`s3`,APPLY_UPDATE_THM]
    \\ simp[MarshallingTheory.w22n_def]
    \\ Cases_on`s.R 4w` \\ fs[ADD1,word_add_n2w]
    \\ Cases_on`off0` \\ Cases_on`off1` \\ fs[]
    \\ Cases_on`n0` \\ Cases_on`n1` \\ fs[] )
  \\ strip_tac \\ fs[]
  \\ pop_assum kall_tac
  \\ fs[Abbr`s3`, APPLY_UPDATE_THM]
  \\ fs[Abbr`s2`, APPLY_UPDATE_THM]
  \\ qmatch_asmsub_abbrev_tac`COND cnd`
  \\ qmatch_asmsub_abbrev_tac`s' = if cnd' then _ else _`
  \\ `cnd' = cnd`
  by (
    simp[Abbr`cnd'`,Abbr`s1`]
    \\ Cases_on`cnd` \\ simp[]
    \\ EVAL_TAC \\ simp[] )
  \\ qpat_x_assum`Abbrev(cnd' = _)`kall_tac
  \\ rveq
  \\ reverse(Cases_on`cnd`) \\ fs[]
  >- (
    qpat_x_assum`Abbrev(s' = _)`mp_tac
    \\ simp[ag32Theory.dfn'StoreMEMByte_def, ag32Theory.incPC_def, ag32Theory.ri2word_def]
    \\ strip_tac
    \\ simp[Abbr`s'`]
    \\ simp[Abbr`s1`, APPLY_UPDATE_THM]
    \\ qmatch_asmsub_abbrev_tac`OPTION_CHOICE o1`
    \\ `o1 = NONE`
    by (
      simp[Abbr`o1`]
      \\ simp[EXISTS_PROD]
      \\ simp[fsFFITheory.write_def, EXISTS_PROD]
      \\ Cases_on`LENGTH conf = 8` \\ fs[]
      \\ last_x_assum(qspec_then`w82n conf`mp_tac)
      \\ Cases_on`w82n conf < 3` \\ fs[]
      \\ simp[IS_SOME_EXISTS]
      \\ strip_tac \\ simp[]
      \\ Cases_on`x` \\ simp[]
      \\ CCONTR_TAC \\ fs[]
      \\ Cases_on`ALOOKUP fs.files q` \\ fs[]
      \\ fs[markerTheory.Abbrev_def] )
    \\ fs[] \\ rveq
    \\ simp[LUPDATE_def]
    \\ qmatch_goalsub_abbrev_tac`A ∧ (B ∧ A)`
    \\ `A ∧ B` suffices_by rw[]
    \\ qunabbrev_tac`B`
    \\ reverse conj_tac
    >- (
      simp[FUN_EQ_THM, APPLY_UPDATE_THM]
      \\ EVAL_TAC
      \\ simp[] )
    \\ simp[Abbr`A`]
    \\ simp[ag32_ffi_write_mem_update_def]
    \\ simp[FUN_EQ_THM, APPLY_UPDATE_THM]
    \\ Cases
    \\ IF_CASES_TAC
    >- simp[lab_to_targetProofTheory.asm_write_bytearray_def, APPLY_UPDATE_THM]
    \\ IF_CASES_TAC
    >- (
      match_mp_tac EQ_SYM
      \\ fs[asmSemTheory.bytes_in_memory_def,
            lab_to_targetProofTheory.asm_write_bytearray_def]
      \\ simp[APPLY_UPDATE_THM]
      \\ rveq
      \\ IF_CASES_TAC
      >- (
        rpt(qpat_x_assum`_ ∈ md`mp_tac)
        \\ simp[Abbr`md`]
        \\ qpat_x_assum`r0 + _ = n2w n`(assume_tac o SYM)
        \\ simp[ag32_prog_addresses_def]
        \\ EVAL_TAC
        \\ fs[FFI_codes_def, LEFT_ADD_DISTRIB]
        \\ Cases_on`r0` \\ fs[memory_size_def]
        \\ fs[word_ls_n2w, word_lo_n2w, word_add_n2w] )
      \\ IF_CASES_TAC
      >- (
        rpt(qpat_x_assum`_ ∈ md`mp_tac)
        \\ simp[Abbr`md`]
        \\ qpat_x_assum`r0 + _ = n2w n`(assume_tac o SYM)
        \\ simp[ag32_prog_addresses_def]
        \\ EVAL_TAC
        \\ fs[FFI_codes_def, LEFT_ADD_DISTRIB]
        \\ Cases_on`r0` \\ fs[memory_size_def]
        \\ fs[word_ls_n2w, word_lo_n2w, word_add_n2w] )
      \\ IF_CASES_TAC
      >- (
        rpt(qpat_x_assum`_ ∈ md`mp_tac)
        \\ simp[Abbr`md`]
        \\ qpat_x_assum`r0 + _ = n2w n`(assume_tac o SYM)
        \\ simp[ag32_prog_addresses_def]
        \\ EVAL_TAC
        \\ fs[FFI_codes_def, LEFT_ADD_DISTRIB]
        \\ Cases_on`r0` \\ fs[memory_size_def]
        \\ fs[word_ls_n2w, word_lo_n2w, word_add_n2w] )
      \\ irule asm_write_bytearray_unchanged
      \\ simp[APPLY_UPDATE_THM]
      \\ conj_tac
      >- ( Cases_on`s.R 3w` \\ fs[ADD1, memory_size_def, word_add_n2w] )
      \\ Cases_on`s.R 3w`
      \\ fs[word_lo_n2w, word_ls_n2w, word_add_n2w]
      \\ fs[EVAL``code_start_offset _``, FFI_codes_def]
      \\ fs[LEFT_ADD_DISTRIB]
      \\ fs[EVAL``ffi_code_start_offset``]
      \\ Cases_on`r0` \\ fs[memory_size_def]
      \\ fs[word_add_n2w] \\ rfs[]
      \\ rveq \\ fs[] \\ rfs[]
      \\ qpat_x_assum`n2w n' ∈ _`mp_tac
      \\ simp[word_add_n2w, Abbr`md`]
      \\ simp[ag32_prog_addresses_def]
      \\ EVAL_TAC
      \\ simp[LEFT_ADD_DISTRIB])
    \\ simp[lab_to_targetProofTheory.asm_write_bytearray_def, APPLY_UPDATE_THM]
    \\ fs[asmSemTheory.bytes_in_memory_def] \\ rveq
    \\ IF_CASES_TAC \\ simp[]
    \\ IF_CASES_TAC \\ simp[]
    \\ IF_CASES_TAC \\ simp[]
    \\ match_mp_tac EQ_SYM
    \\ Cases_on`n2w n <+ s.R 3w + 4w ∨ s.R 3w + 4w + n2w (LENGTH tll) <=+ n2w n`
    >- (
      irule asm_write_bytearray_unchanged
      \\ simp[APPLY_UPDATE_THM]
      \\ Cases_on`s.R 3w` \\ fs[word_add_n2w] )
    \\ fs[WORD_NOT_LOWER, WORD_NOT_LOWER_EQUAL]
    \\ Cases_on`s.R 3w`
    \\ fs[word_add_n2w, word_ls_n2w, word_lo_n2w] \\ rfs[]
    \\ qpat_x_assum`_ ≤ n`mp_tac
    \\ rw[LESS_EQ_EXISTS] \\ fs[]
    \\ drule bytes_in_memory_EL
    \\ disch_then drule
    \\ rw[word_add_n2w]
    \\ qmatch_goalsub_rename_tac`n2w (a + (p + 4))`
    \\ `n2w(a + (p + 4)) = n2w(a+4) + n2w p:word32` by simp[word_add_n2w]
    \\ pop_assum SUBST_ALL_TAC
    \\ irule asm_write_bytearray_EL
    \\ simp[] )
  \\ pop_assum mp_tac \\ simp[markerTheory.Abbrev_def] \\ strip_tac
  \\ qspec_then`s1`mp_tac(Q.GEN`s`ag32_ffi_write_write_header_thm)
  \\ impl_tac
  >- (
    simp[Abbr`s1`, APPLY_UPDATE_THM]
    \\ fs[asmSemTheory.bytes_in_memory_def]
    \\ qpat_x_assum`s.R 3w ∈ _`mp_tac
    \\ simp[Abbr`md`]
    \\ EVAL_TAC
    \\ fs[FFI_codes_def]
    \\ simp[LEFT_ADD_DISTRIB]
    \\ Cases_on`r0` \\ Cases_on`s.R 3w` \\ fs[word_add_n2w]
    \\ fs[memory_size_def, word_ls_n2w, word_lo_n2w] )
  \\ strip_tac
  \\ qmatch_asmsub_abbrev_tac`_ = s2`
  \\ fs[]
  \\ fs[Abbr`s1`, APPLY_UPDATE_THM]
  \\ qhdtm_x_assum`ag32_ffi_write_write_header`kall_tac
  \\ qmatch_asmsub_abbrev_tac`1w =+ n2w n`
  \\ qspec_then`s2`mp_tac(Q.GENL[`s`,`k`]ag32_ffi_write_num_written_thm)
  \\ simp[]
  \\ impl_tac
  >- (
    simp[Abbr`s2`, APPLY_UPDATE_THM]
    \\ reverse conj_tac
    >- (
      simp[Abbr`n`, MarshallingTheory.w22n_def]
      \\ Cases_on`n0` \\ Cases_on`n1` \\ fs[] )
    \\ fs[asmSemTheory.bytes_in_memory_def]
    \\ simp[APPLY_UPDATE_THM]
    \\ Cases_on`s.R 3w` \\ fs[word_add_n2w]
    \\ rveq
    \\ DEP_REWRITE_TAC[asm_write_bytearray_append]
    \\ simp[EVAL``output_offset``]
    \\ Cases_on`r0` \\ fs[memory_size_def, word_add_n2w]
    \\ simp[lab_to_targetProofTheory.asm_write_bytearray_def, APPLY_UPDATE_THM]
    \\ EVAL_TAC \\ fs[]
    \\ qpat_x_assum`n2w n' ∈ _`mp_tac
    \\ simp[Abbr`md`]
    \\ EVAL_TAC \\ simp[LEFT_ADD_DISTRIB]
    \\ fs[FFI_codes_def]
    \\ fs[EVAL``code_start_offset _``]
    \\ fs[word_ls_n2w, word_lo_n2w]
    \\ disch_then assume_tac
    \\ conj_tac
    >- (
      irule asm_write_bytearray_unchanged
      \\ simp[APPLY_UPDATE_THM]
      \\ fs[word_ls_n2w, word_lo_n2w, word_add_n2w] )
    \\ conj_tac
    >- (
      irule asm_write_bytearray_unchanged
      \\ simp[APPLY_UPDATE_THM]
      \\ fs[word_ls_n2w, word_lo_n2w, word_add_n2w] )
    \\ conj_tac
    >- (
      irule asm_write_bytearray_unchanged
      \\ simp[APPLY_UPDATE_THM]
      \\ fs[word_ls_n2w, word_lo_n2w, word_add_n2w] )
    \\ qhdtm_x_assum`bytes_in_memory`mp_tac
    \\ EVAL_TAC \\ simp[LEFT_ADD_DISTRIB]
    \\ strip_tac
    \\ irule asmPropsTheory.bytes_in_memory_change_mem
    \\ goal_assum(first_assum o mp_then Any mp_tac)
    \\ simp[APPLY_UPDATE_THM]
    \\ qx_gen_tac`z` \\ strip_tac
    \\ simp[word_add_n2w]
    \\ match_mp_tac EQ_SYM
    \\ irule asm_write_bytearray_unchanged
    \\ simp[word_add_n2w, APPLY_UPDATE_THM]
    \\ simp[word_ls_n2w, word_lo_n2w])
  \\ strip_tac
  \\ qmatch_asmsub_abbrev_tac`_ = s3`
  \\ fs[]
  \\ fs[Abbr`s2`, APPLY_UPDATE_THM]
  \\ qhdtm_x_assum`ag32_ffi_write_num_written`kall_tac
  \\ qspec_then`s3`mp_tac(ag32_ffi_write_copy_thm)
  \\ qmatch_asmsub_abbrev_tac`LENGTH tll - off`
  \\ disch_then(qspec_then`TAKE (MIN n output_buffer_size) (DROP off tll)`mp_tac)
  \\ simp[]
  \\ impl_tac >- (
    simp[Abbr`s3`, APPLY_UPDATE_THM]
    \\ reverse conj_tac
    >- (
      Cases_on`s.R 3w` \\ fs[word_add_n2w]
      \\ EVAL_TAC
      \\ Cases_on`r0` \\ fs[memory_size_def, word_add_n2w]
      \\ simp[MIN_DEF]
      \\ simp[IN_DISJOINT]
      \\ Cases
      \\ fs[word_ls_n2w, word_lo_n2w]
      \\ simp[Abbr`md`]
      \\ EVAL_TAC \\ fs[]
      \\ fs[FFI_codes_def, LEFT_ADD_DISTRIB]
      \\ fs[word_ls_n2w, word_lo_n2w] )
    \\ fs[asmSemTheory.bytes_in_memory_def]
    \\ `tll = TAKE off tll ++ DROP off tll` by metis_tac[TAKE_DROP]
    \\ qhdtm_x_assum`bytes_in_memory`mp_tac
    \\ pop_assum(fn th => CONV_TAC(LAND_CONV(ONCE_REWRITE_CONV[th])))
    \\ disch_then(mp_then Any mp_tac (#1(EQ_IMP_RULE (SPEC_ALL asmPropsTheory.bytes_in_memory_APPEND))))
    \\ simp[] \\ strip_tac
    \\ qmatch_goalsub_abbrev_tac`TAKE kk ll`
    \\ `ll = TAKE kk ll ++ DROP kk ll` by metis_tac[TAKE_DROP]
    \\ qhdtm_x_assum`bytes_in_memory`mp_tac
    \\ pop_assum(fn th => CONV_TAC(LAND_CONV(ONCE_REWRITE_CONV[th])))
    \\ disch_then(mp_then Any mp_tac (#1(EQ_IMP_RULE (SPEC_ALL asmPropsTheory.bytes_in_memory_APPEND))))
    \\ strip_tac
    \\ irule asmPropsTheory.bytes_in_memory_change_mem
    \\ goal_assum(first_assum o mp_then Any mp_tac)
    \\ gen_tac \\ strip_tac
    \\ simp[lab_to_targetProofTheory.asm_write_bytearray_def]
    \\ simp[APPLY_UPDATE_THM]
    \\ simp[word_add_n2w]
    \\ DEP_REWRITE_TAC[SIMP_RULE(srw_ss())[]asm_write_bytearray_unchanged]
    \\ Cases_on`s.R 3w`
    \\ simp[word_add_n2w, MarshallingTheory.n2w2_def]
    \\ simp[word_ls_n2w, word_lo_n2w]
    \\ fs[]
    \\ rfs[Abbr`ll`]
    \\ `kk ≤ n` by simp[Abbr`kk`]
    \\ fs[LENGTH_TAKE_EQ]
    \\ simp[APPLY_UPDATE_THM]
    \\ DEP_REWRITE_TAC[SIMP_RULE(srw_ss())[]asm_write_bytearray_unchanged]
    \\ EVAL_TAC
    \\ simp[word_ls_n2w, word_lo_n2w, word_add_n2w]
    \\ Cases_on`r0` \\ fs[memory_size_def, word_add_n2w]
    \\ fs[word_ls_n2w, word_lo_n2w, word_add_n2w]
    \\ `kk ≤ LENGTH tll - off` by fs[] \\ fs[]
    \\ fs[FFI_codes_def, EVAL``code_start_offset _``] \\ rfs[]
    \\ `kk ≤ output_buffer_size` by simp[Abbr`kk`]
    \\ fs[EVAL``output_buffer_size``]
    \\ qpat_x_assum`n2w n'' ∈ _`mp_tac
    \\ simp[Abbr`md`]
    \\ EVAL_TAC
    \\ simp[LEFT_ADD_DISTRIB]
    \\ simp[word_ls_n2w, word_lo_n2w, word_add_n2w])
  \\ strip_tac
  \\ qunabbrev_tac`s'`
  \\ fs[]
  \\ simp[Abbr`s3`, APPLY_UPDATE_THM]
  \\ qmatch_goalsub_abbrev_tac`A ∧ B ∧ A`
  \\ `B ∧ A` suffices_by rw[]
  \\ simp[Abbr`B`, FUN_EQ_THM, APPLY_UPDATE_THM]
  \\ EVAL_TAC \\ simp[]
  \\ qhdtm_x_assum`ag32_ffi_write_copy`kall_tac
  \\ simp[Abbr`A`]
  \\ simp[ag32_ffi_write_mem_update_def, ADD1]
  \\ qmatch_goalsub_abbrev_tac`THE (bs:word8 list option)`
  \\ qmatch_asmsub_abbrev_tac`bytes_in_memory _ bs'`
  \\ `bs = SOME bs'`
  by (
    simp[Abbr`bs`]
    \\ irule data_to_word_assignProofTheory.IMP_read_bytearray_GENLIST
    \\ fs[Abbr`bs'`]
    \\ gen_tac \\ strip_tac
    \\ drule bytes_in_memory_EL
    \\ simp[]
    \\ drule bytes_in_memory_in_domain
    \\ simp[] )
  \\ simp[Abbr`bs`, Abbr`bs'`]
  \\ fs[fsFFITheory.write_def]
  \\ `∃x. ALOOKUP fs.infds (w82n conf) = SOME x` by metis_tac[IS_SOME_EXISTS]
  \\ fs[] \\ Cases_on`x` \\ fs[]
  \\ first_x_assum drule
  \\ simp[IS_SOME_EXISTS]
  \\ strip_tac \\ fs[]
  \\ rveq \\ simp[]
  \\ qmatch_goalsub_abbrev_tac`THE (bs:word8 list option)`
  \\ `bs = SOME conf`
  by (
    simp[Abbr`bs`]
    \\ irule data_to_word_assignProofTheory.IMP_read_bytearray_GENLIST
    \\ fs[]
    \\ gen_tac \\ strip_tac
    \\ conj_tac
    >- (
      once_rewrite_tac[WORD_ADD_COMM]
      \\ irule bytes_in_memory_in_domain
      \\ goal_assum(first_assum o mp_then Any mp_tac)
      \\ simp[] )
    \\ once_rewrite_tac[WORD_ADD_COMM]
    \\ irule bytes_in_memory_EL
    \\ simp[]
    \\ asm_exists_tac
    \\ simp[] )
  \\ simp[Abbr`bs`]
  \\ qmatch_goalsub_abbrev_tac`lhs = _`
  \\ DEP_ONCE_REWRITE_TAC[asm_write_bytearray_append]
  \\ simp[Abbr`lhs`]
  \\ conj_tac
  >- (
    EVAL_TAC
    \\ Cases_on`r0` \\ fs[memory_size_def, word_add_n2w]
    \\ rw[MIN_DEF] )
  \\ rewrite_tac[GSYM WORD_ADD_ASSOC, word_add_n2w]
  \\ AP_TERM_TAC
  \\ cheat (* local proof: (roughly) order of non-overlapping memory writes *));

val ag32_ffi_interfer_write = Q.store_thm("ag32_ffi_interfer_write",
  `ag32_ffi_rel r0 ms ios ∧
   (read_ffi_bytearrays (ag32_machine_config ffi_names lc ld r0) ms = (SOME conf, SOME bytes)) ∧
   (ffi_write conf bytes fs = SOME (FFIreturn bytes' fs')) ∧
   (INDEX_OF "write" ffi_names = SOME index) ∧
   w2n r0 + memory_size < dimword (:32) ∧
   LENGTH ffi_names ≤ LENGTH FFI_codes ∧
   code_start_offset (LENGTH ffi_names) + lc + 4 * ld < memory_size ∧
   (fs.numchars = LGENLIST (K output_buffer_size) NONE) ∧
   (∀k. k < LENGTH (ag32_ffi_jumps ffi_names) ⇒
        (get_mem_word ms.MEM (r0 + n2w (ffi_jumps_offset + 4 * k))
         = EL k (ag32_ffi_jumps ffi_names))) ∧
   (∀k. k < LENGTH ag32_ffi_write_code ⇒
        (get_mem_word ms.MEM (r0 + n2w (ffi_code_start_offset + THE (ALOOKUP ffi_entrypoints "write") + 4 * k))
         = Encode (EL k ag32_ffi_write_code)))
   ⇒
   ∃k.
     (ag32_ffi_interfer ffi_names
        (ag32_prog_addresses (LENGTH ffi_names) lc ld r0) r0
        (index,bytes',ms) = FUNPOW Next k ms) ∧
      ag32_ffi_rel r0 (FUNPOW Next k ms)
        (ios ++ [IO_event "write" conf (ZIP (bytes,bytes'))]) ∧
      ∀x. x ∉ ag32_ffi_mem_domain r0 ⇒ ((FUNPOW Next k ms).MEM x = ms.MEM x)`,
  strip_tac
  \\ fs[targetSemTheory.read_ffi_bytearrays_def]
  \\ fs[targetSemTheory.read_ffi_bytearray_def]
  \\ fs[EVAL``(ag32_machine_config a b c d).ptr2_reg``]
  \\ fs[EVAL``(ag32_machine_config a b c d).len2_reg``]
  \\ fs[EVAL``(ag32_machine_config a b c d).ptr_reg``]
  \\ fs[EVAL``(ag32_machine_config a b c d).len_reg``]
  \\ fs[EVAL``(ag32_machine_config a b c d).target.get_reg``]
  \\ fs[EVAL``(ag32_machine_config a b c d).target.get_byte``]
  \\ first_assum(mp_then Any mp_tac read_bytearray_IMP_bytes_in_memory)
  \\ last_assum(mp_then Any mp_tac read_bytearray_IMP_bytes_in_memory)
  \\ imp_res_tac read_bytearray_LENGTH \\ fs[]
  \\ qmatch_asmsub_abbrev_tac`_ ∈ md`
  \\ disch_then(qspecl_then[`ms.MEM`,`md`]mp_tac) \\ simp[]
  \\ impl_tac
  >- (
    conj_tac >- cheat (* byte array does not wrap *)
    \\ imp_res_tac read_bytearray_IMP_mem_SOME
    \\ fs[IS_SOME_EXISTS] )
  \\ strip_tac
  \\ disch_then(qspecl_then[`ms.MEM`,`md`]mp_tac) \\ simp[]
  \\ impl_tac
  >- (
    conj_tac >- cheat (* byte array does not wrap *)
    \\ imp_res_tac read_bytearray_IMP_mem_SOME
    \\ fs[IS_SOME_EXISTS] )
  \\ strip_tac
  \\ drule (GEN_ALL ag32_ffi_write_thm)
  \\ disch_then drule
  \\ qpat_x_assum`Abbrev(md = _)`mp_tac
  \\ CONV_TAC(LAND_CONV(SIMP_CONV(srw_ss()++LET_ss)[ag32_machine_config_def]))
  \\ strip_tac
  \\ disch_then drule
  \\ simp[]
  \\ disch_then(first_assum o mp_then Any mp_tac)
  (*
  ag32_ffi_write_code_thm
  *)
  \\ cheat);

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

val hello_startup_asm_code_eq =
  hello_startup_asm_code_def
  |> CONV_RULE(RAND_CONV EVAL)
  |> SIMP_RULE(srw_ss())[LENGTH_code,LENGTH_data,ffi_names]

val hello_startup_code_def = Define`
    hello_startup_code =
    FLAT (MAP ag32_enc hello_startup_asm_code)`;

val hello_startup_code_eq =
  hello_startup_code_def
  |> REWRITE_RULE[hello_startup_asm_code_eq]
  |> CONV_RULE(RAND_CONV (RAND_CONV ag32_targetLib.ag32_encode_conv))
  |> CONV_RULE(RAND_CONV listLib.FLAT_CONV)

val LENGTH_hello_startup_code =
  ``LENGTH hello_startup_code``
  |> (RAND_CONV(REWR_CONV hello_startup_code_eq)
      THENC listLib.LENGTH_CONV)

val words_of_bytes_hello_startup_code_eq =
  ``words_of_bytes F hello_startup_code :word32 list``
  |> REWRITE_CONV[hello_startup_code_eq]
  |> CONV_RULE(RAND_CONV EVAL)

val LENGTH_words_of_bytes_hello_startup_code =
  ``LENGTH (words_of_bytes F hello_startup_code : word32 list)``
  |> REWRITE_CONV[words_of_bytes_hello_startup_code_eq]
  |> CONV_RULE(RAND_CONV listLib.LENGTH_CONV)

val hello_init_memory_words_def = zDefine`
  hello_init_memory_words cl stdin =
    words_of_bytes F hello_startup_code ++
    REPLICATE ((startup_code_size - LENGTH hello_startup_code) DIV 4) 0w ++
    [n2w (LENGTH cl)] ++
    words_of_bytes F (PAD_RIGHT 0w cline_size (FLAT (MAP (SNOC 0w) (MAP (MAP (n2w o ORD) o explode) cl)))) ++
    [0w] ++
    [n2w (LENGTH stdin)] ++
    words_of_bytes F (PAD_RIGHT 0w stdin_size (MAP (n2w o ORD) stdin)) ++
    REPLICATE ((8 + 4 + output_buffer_size + 4) DIV 4) 0w ++
    ag32_ffi_code ++
    REPLICATE (heap_size DIV 4) 0w ++
    ag32_ffi_jumps (THE config.ffi_names) ++
    words_of_bytes F code ++
    data (* ++ padding of 0w out to memory_size: not included here *)
    `;

val hello_init_memory_def = Define`
  hello_init_memory r0 (cl, stdin) (k:word32) =
     get_byte k (EL (w2n (byte_align k - r0) DIV 4) (hello_init_memory_words cl stdin)) F`;

val LENGTH_hello_init_memory_words = Q.store_thm("LENGTH_hello_init_memory_words",
  `SUM (MAP strlen cl) + LENGTH cl ≤ cline_size ∧ LENGTH inp ≤ stdin_size ⇒
   (LENGTH (hello_init_memory_words cl inp) = 27572127)`, (* adjust as necessary *)
  simp[hello_init_memory_words_def]
  \\ simp[LENGTH_words_of_bytes_hello_startup_code,LENGTH_ag32_ffi_code,heap_size_def,
          output_buffer_size_def,startup_code_size_def,LENGTH_hello_startup_code,
          LENGTH_ag32_ffi_jumps, ffi_names, LENGTH_data]
  \\ simp[LENGTH_words_of_bytes, bitstringTheory.length_pad_right, LENGTH_code,
          bytes_in_word_def, LENGTH_FLAT, MAP_MAP_o, o_DEF, ADD1, SUM_MAP_PLUS,
          Q.ISPEC`λx. 1n`SUM_MAP_K |> SIMP_RULE(srw_ss())[]]
  \\ strip_tac
  \\ qmatch_goalsub_abbrev_tac`sz DIV 4`
  \\ `sz = stdin_size` by (rw[Abbr`sz`])
  \\ qpat_x_assum`Abbrev(sz = _)`kall_tac
  \\ qmatch_goalsub_abbrev_tac`_ + (cz DIV 4 + _)`
  \\ `cz = cline_size` by (rw[Abbr`cz`])
  \\ qpat_x_assum`Abbrev(cz = _)`kall_tac
  \\ rveq
  \\ qmatch_goalsub_abbrev_tac`_ = rhs`
  \\ rw[stdin_size_def, cline_size_def]);

val hello_machine_config_def = Define`
  hello_machine_config =
    ag32_machine_config (THE config.ffi_names) (LENGTH code) (LENGTH data)`;

val hello_machine_config_halt_pc =
  ``(hello_machine_config r0).halt_pc``
  |> EVAL |> SIMP_RULE(srw_ss())[ffi_names]

val hello_machine_config_ccache_pc =
  ``(hello_machine_config r0).ccache_pc``
  |> EVAL |> SIMP_RULE(srw_ss())[ffi_names]

val hello_init_memory_startup = Q.store_thm("hello_init_memory_startup",
  `byte_aligned r0 ∧ n < LENGTH hello_startup_code ⇒
   (hello_init_memory r0 inputs (r0 + (n2w n)) =
    EL n hello_startup_code)`,
  Cases_on`inputs`
  \\ strip_tac
  \\ simp[hello_init_memory_def]
  \\ fs[alignmentTheory.byte_aligned_def, alignmentTheory.byte_align_def]
  \\ simp[align_add_aligned_gen]
  \\ Q.ISPECL_THEN[`n`,`F`,`hello_startup_code`]mp_tac
       (Q.GEN`i`(INST_TYPE[alpha|->``:32``]get_byte_EL_words_of_bytes))
  \\ simp[bytes_in_word_def,LENGTH_hello_startup_code]
  \\ impl_tac >- EVAL_TAC
  \\ simp[alignmentTheory.byte_align_def]
  \\ simp[hello_init_memory_words_def]
  \\ rewrite_tac[GSYM APPEND_ASSOC]
  \\ DEP_REWRITE_TAC [EL_APPEND1]
  \\ conj_tac
  >- (
    simp[LENGTH_words_of_bytes_hello_startup_code]
    \\ fs[LENGTH_hello_startup_code, DIV_LT_X]
    \\ fs[alignmentTheory.align_w2n]
    \\ DEP_REWRITE_TAC[LESS_MOD]
    \\ fs[]
    \\ conj_tac
    \\ irule IMP_MULT_DIV_LESS
    \\ fs[] )
  \\ `r0 + n2w n = n2w n + byte_align r0`
  by (
    simp[alignmentTheory.byte_align_def, align_add_aligned_gen]
    \\ fs[alignmentTheory.aligned_def] )
  \\ pop_assum SUBST1_TAC
  \\ DEP_REWRITE_TAC[data_to_word_memoryProofTheory.get_byte_byte_align]
  \\ EVAL_TAC);

(* TODO: use get_mem_word in this theorem *)
val hello_init_memory_halt = Q.store_thm("hello_init_memory_halt",
  `byte_aligned r0 ∧
   (pc = (hello_machine_config r0).halt_pc) ∧
   SUM (MAP strlen cl) + LENGTH cl ≤ cline_size ∧ LENGTH inp ≤ stdin_size
  ⇒
   ((hello_init_memory r0 (cl,inp) (pc + 3w) @@
    ((hello_init_memory r0 (cl,inp) (pc + 2w) @@
      ((hello_init_memory r0 (cl,inp) (pc + 1w) @@
        hello_init_memory r0 (cl,inp) (pc)) : word16)) : word24)) =
    Encode (Jump (fAdd, 0w, Imm 0w)))`,
  strip_tac
  \\ qpat_x_assum`pc = _`(assume_tac o ONCE_REWRITE_RULE[GSYM markerTheory.Abbrev_def])
  \\ simp[hello_init_memory_def]
  \\ fs[alignmentTheory.byte_aligned_def, alignmentTheory.byte_align_def]
  \\ `aligned 2 pc`
  by (
    simp[Abbr`pc`, hello_machine_config_halt_pc]
    \\ (alignmentTheory.aligned_add_sub_cor
        |> SPEC_ALL |> UNDISCH |> CONJUNCT1 |> DISCH_ALL
        |> irule)
    \\ simp[]
    \\ EVAL_TAC )
  \\ simp[align_add_aligned_gen]
  \\ simp[Abbr`pc`]
  \\ rewrite_tac[hello_machine_config_halt_pc]
  \\ qmatch_goalsub_abbrev_tac`r0 + x`
  \\ `align 2 (r0 + x) = r0 + x` by fs[alignmentTheory.aligned_def, hello_machine_config_halt_pc]
  \\ `r0 + x = byte_align (r0 + x)` by fs[alignmentTheory.byte_align_def]
  \\ qhdtm_x_assum`align`SUBST_ALL_TAC
  \\ simp_tac(srw_ss())[]
  \\ pop_assum SUBST_ALL_TAC
  \\ once_rewrite_tac[WORD_ADD_COMM]
  \\ DEP_REWRITE_TAC[data_to_word_memoryProofTheory.get_byte_byte_align]
  \\ conj_tac >- EVAL_TAC
  \\ DEP_REWRITE_TAC[
       data_to_word_memoryProofTheory.get_byte_byte_align
       |> Q.GEN`a'` |> Q.SPEC`0w` |> SIMP_RULE(srw_ss())[]]
  \\ conj_tac >- EVAL_TAC
  \\ DEP_REWRITE_TAC[w2n_add]
  \\ DEP_REWRITE_TAC[ADD_DIV_RWT]
  \\ conj_tac
  >- ( simp[Abbr`x`] \\ EVAL_TAC )
  \\ conj_tac
  >- ( simp[Abbr`x`,LENGTH_data] \\ EVAL_TAC )
  \\ qmatch_goalsub_abbrev_tac`_ = h`
  \\ `∃l1 l2. (hello_init_memory_words cl inp = l1 ++ l2) ∧
              (LENGTH l1 = w2n x DIV 4) ∧
              (l2 <> [] ∧ (HD l2 = h))` by (
    simp[hello_init_memory_words_def, ag32_ffi_jumps_def]
    \\ qmatch_goalsub_abbrev_tac`l1 ++ halt_jump_ag32_code ++ _ ++ _`
    \\ qexists_tac`l1`
    \\ simp[halt_jump_ag32_code_def]
    \\ simp[Abbr`l1`,Abbr`x`]
    \\ simp[LENGTH_words_of_bytes_hello_startup_code, LENGTH_words_of_bytes, LENGTH_FLAT, bitstringTheory.length_pad_right]
    \\ simp[LENGTH_data, LENGTH_code]
    \\ simp[MAP_MAP_o, o_DEF, ADD1, ffi_names, SUM_MAP_PLUS]
    \\ simp[Q.ISPEC`λx. 1n`SUM_MAP_K |> SIMP_RULE(srw_ss())[]]
    \\ qmatch_goalsub_abbrev_tac`MIN 1 (cz MOD _)` \\ `cz = stdin_size` by ( simp[Abbr`cz`] )
    \\ qpat_x_assum`Abbrev(cz = _)`kall_tac \\ pop_assum SUBST_ALL_TAC
    \\ fs[stdin_size_def, bytes_in_word_def]
    \\ qmatch_goalsub_abbrev_tac`MIN 1 (sz MOD _)` \\ `sz = cline_size` by ( simp[Abbr`sz`] )
    \\ qpat_x_assum`Abbrev(sz = _)`kall_tac \\ pop_assum SUBST_ALL_TAC
    \\ simp[cline_size_def, bytes_in_word_def]
    \\ simp[LENGTH_ag32_ffi_code]
    \\ simp[LENGTH_hello_startup_code, startup_code_size_def, heap_size_def, output_buffer_size_def]
    \\ EVAL_TAC)
  \\ simp[EL_APPEND_EQN]
  \\ EVAL_TAC \\ simp[]
  \\ blastLib.BBLAST_TAC );

(* TODO: use get_mem_word in this theorem *)
val hello_init_memory_ccache = Q.store_thm("hello_init_memory_ccache",
  `byte_aligned r0 ∧
   (pc = (hello_machine_config r0).ccache_pc) ∧
   SUM (MAP strlen cl) + LENGTH cl ≤ cline_size ∧ LENGTH inp ≤ stdin_size
  ⇒
   ((hello_init_memory r0 (cl,inp) (pc + 3w) @@
    ((hello_init_memory r0 (cl,inp) (pc + 2w) @@
      ((hello_init_memory r0 (cl,inp) (pc + 1w) @@
        hello_init_memory r0 (cl,inp) (pc)) : word16)) : word24)) =
    Encode (Jump (fSnd, 0w, Reg 0w)))`,
  strip_tac
  \\ qpat_x_assum`pc = _`(assume_tac o ONCE_REWRITE_RULE[GSYM markerTheory.Abbrev_def])
  \\ simp[hello_init_memory_def]
  \\ fs[alignmentTheory.byte_aligned_def, alignmentTheory.byte_align_def]
  \\ `aligned 2 pc`
  by (
    simp[Abbr`pc`, hello_machine_config_ccache_pc]
    \\ (alignmentTheory.aligned_add_sub_cor
        |> SPEC_ALL |> UNDISCH |> CONJUNCT1 |> DISCH_ALL
        |> irule)
    \\ simp[]
    \\ EVAL_TAC )
  \\ simp[align_add_aligned_gen]
  \\ simp[Abbr`pc`]
  \\ rewrite_tac[hello_machine_config_ccache_pc]
  \\ qmatch_goalsub_abbrev_tac`r0 + x`
  \\ `align 2 (r0 + x) = r0 + x` by fs[alignmentTheory.aligned_def, hello_machine_config_ccache_pc]
  \\ `r0 + x = byte_align (r0 + x)` by fs[alignmentTheory.byte_align_def]
  \\ qhdtm_x_assum`align`SUBST_ALL_TAC
  \\ simp_tac(srw_ss())[]
  \\ pop_assum SUBST_ALL_TAC
  \\ once_rewrite_tac[WORD_ADD_COMM]
  \\ DEP_REWRITE_TAC[data_to_word_memoryProofTheory.get_byte_byte_align]
  \\ conj_tac >- EVAL_TAC
  \\ DEP_REWRITE_TAC[
       data_to_word_memoryProofTheory.get_byte_byte_align
       |> Q.GEN`a'` |> Q.SPEC`0w` |> SIMP_RULE(srw_ss())[]]
  \\ conj_tac >- EVAL_TAC
  \\ DEP_REWRITE_TAC[w2n_add]
  \\ DEP_REWRITE_TAC[ADD_DIV_RWT]
  \\ conj_tac
  >- ( simp[Abbr`x`] \\ EVAL_TAC )
  \\ conj_tac
  >- ( simp[Abbr`x`,LENGTH_data] \\ EVAL_TAC )
  \\ qmatch_goalsub_abbrev_tac`_ = h`
  \\ `∃l1 l2. (hello_init_memory_words cl inp = l1 ++ l2) ∧
              (LENGTH l1 = w2n x DIV 4) ∧
              (l2 <> [] ∧ (HD l2 = h))` by (
    simp[hello_init_memory_words_def, ag32_ffi_jumps_def]
    \\ qmatch_goalsub_abbrev_tac`l1 ++ ccache_jump_ag32_code ++ _ ++ _ ++ _`
    \\ qexists_tac`l1`
    \\ simp[ccache_jump_ag32_code_def]
    \\ simp[Abbr`l1`,Abbr`x`]
    \\ simp[LENGTH_words_of_bytes_hello_startup_code, LENGTH_words_of_bytes, LENGTH_FLAT, bitstringTheory.length_pad_right]
    \\ simp[LENGTH_data, LENGTH_code]
    \\ simp[MAP_MAP_o, o_DEF, ADD1, ffi_names, SUM_MAP_PLUS]
    \\ simp[Q.ISPEC`λx. 1n`SUM_MAP_K |> SIMP_RULE(srw_ss())[]]
    \\ qmatch_goalsub_abbrev_tac`MIN 1 (cz MOD _)` \\ `cz = stdin_size` by ( simp[Abbr`cz`] )
    \\ qpat_x_assum`Abbrev(cz = _)`kall_tac \\ pop_assum SUBST_ALL_TAC
    \\ fs[stdin_size_def, bytes_in_word_def]
    \\ qmatch_goalsub_abbrev_tac`MIN 1 (sz MOD _)` \\ `sz = cline_size` by ( simp[Abbr`sz`] )
    \\ qpat_x_assum`Abbrev(sz = _)`kall_tac \\ pop_assum SUBST_ALL_TAC
    \\ simp[cline_size_def, bytes_in_word_def]
    \\ simp[LENGTH_ag32_ffi_code]
    \\ simp[LENGTH_hello_startup_code, startup_code_size_def, heap_size_def, output_buffer_size_def]
    \\ EVAL_TAC)
  \\ simp[EL_APPEND_EQN]
  \\ EVAL_TAC \\ simp[]
  \\ blastLib.BBLAST_TAC );

(*
define the ag32 and asm states
that obtain after running startup code from ag32 init
and do the rest of the proof from there
*)

val hello_init_asm_state_def = Define`
  hello_init_asm_state r0 input =
    FOLDL (λs i. asm i (s.pc + n2w (LENGTH (ag32_enc i))) s)
      (ag32_init_asm_state
        (hello_init_memory r0 input)
        (ag32_startup_addresses r0)
        r0)
      (hello_startup_asm_code)`;

val (asm_tm, mk_asm, dest_asm, is_asm) = HolKernel.syntax_fns3 "asmSem" "asm"
val (asm_ok_tm, mk_asm_ok, dest_asm_ok, is_asm_ok) = HolKernel.syntax_fns2 "asm" "asm_ok"
val (ag32_enc_tm, mk_ag32_enc, dest_ag32_enc, is_ag32_enc) = HolKernel.syntax_fns1 "ag32_target" "ag32_enc"

val bare_asm_conv =
 (computeLib.compset_conv (wordsLib.words_compset())
   [computeLib.Extenders[
     asmLib.add_asm_compset,
     combinLib.add_combin_compset],
    computeLib.Defs [
      UPDATE_def,
      asmSemTheory.write_mem_word_def_compute],
    computeLib.Tys [``:'a asmSem$asm_state``]])

val asm_conv =
  Conv.memoize
    (fn tm =>
      SOME(list_of_triple (dest_asm tm))
      handle HOL_ERR _ => Lib.total (list_of_pair o dest_asm_ok) tm)
    (Redblackmap.mkDict (list_compare Term.compare))
    (fn tm => TypeBase.is_record tm orelse aconv tm T)
    (Feedback.mk_HOL_ERR "hello_ag32Proof" "asm_conv" "")
    bare_asm_conv

fun ag32_enc_conv tm =
  if is_ag32_enc tm
  then ag32_targetLib.ag32_encode_conv tm
  else NO_CONV tm

val bytes_in_memory_tac =
  simp[asmSemTheory.bytes_in_memory_def, LENGTH_code, ffi_names]
  \\ DEP_REWRITE_TAC[hello_init_memory_startup, hello_init_memory_startup |> Q.GEN`n` |> Q.SPEC`0` |> SIMP_RULE(srw_ss())[]]
  \\ simp[LENGTH_hello_startup_code]
  \\ rewrite_tac[hello_startup_code_eq] \\ EVAL_TAC
  \\ Cases_on`r0`
  \\ fs[word_ls_n2w,word_add_n2w,word_lo_n2w,
        alignmentTheory.byte_aligned_def,
        memory_size_def]

val mem_ok_tac =
  Cases_on`r0`
  \\ fs[word_ls_n2w,word_add_n2w,word_lo_n2w,
        alignmentTheory.byte_aligned_def,
        word_extract_n2w, memory_size_def,
        GSYM ALIGNED_eq_aligned, addressTheory.ALIGNED_n2w,
        bitTheory.BITS_ZERO3 ]

val mem_word_tac =
    rw[data_to_word_memoryProofTheory.word_of_bytes_def,
       wordSemTheory.set_byte_def, wordSemTheory.byte_index_def,
       lab_to_targetTheory.ffi_offset_def,LENGTH_code,
       wordSemTheory.word_slice_alt_def,LENGTH_data,heap_size_def,
       EVAL``heap_start_offset``, ffi_names, code_start_offset_def,
       EVAL``ffi_jumps_offset``]
    \\ blastLib.BBLAST_TAC

val _ = temp_overload_on("hello_asm_state0",
  ``(ag32_init_asm_state
      (hello_init_memory r0 (cl,inp))
      (ag32_startup_addresses r0)
      r0)``);

val hello_init_asm_state_asm_step = Q.store_thm("hello_init_asm_state_asm_step",
  `byte_aligned r0 ∧ w2n r0 + memory_size < dimword(:32) ∧
   SUM (MAP strlen cl) + LENGTH cl ≤ cline_size ∧
   LENGTH inp ≤ stdin_size ⇒
   let tr =
    (steps (λs i. asm i (s.pc + n2w (LENGTH (ag32_enc i))) s)
      hello_asm_state0
      hello_startup_asm_code) in
   steps_rel (asm_step (ag32_target.config)) hello_asm_state0 tr ∧
   let final_st = LAST (hello_asm_state0::(MAP SND tr)) in
   let ffi_names = THE config.ffi_names in
   let num_ffis = LENGTH ffi_names in
     (final_st.pc = r0 + n2w (code_start_offset num_ffis)) ∧
     (read_bytearray final_st.pc (LENGTH code)
       (λa. if a ∈ (hello_machine_config r0).prog_addresses then
               SOME (final_st.mem a) else NONE ) = SOME code) ∧
     let hs = r0 + n2w heap_start_offset in
     let ds = r0 + n2w (code_start_offset num_ffis + LENGTH code) in
     (final_st.regs 2 = hs) ∧
     (final_st.regs 4 = hs + n2w heap_size) ∧
     (word_of_bytes F 0w (GENLIST (final_st.mem o ((+) (hs + 0w * 4w)) o n2w) 4) =
      ds) ∧
     (word_of_bytes F 0w (GENLIST (final_st.mem o ((+) (hs + 1w * 4w)) o n2w) 4) =
      ds + n2w (4 * LENGTH data)) ∧
     (word_of_bytes F 0w (GENLIST (final_st.mem o ((+) (hs + 2w * 4w)) o n2w) 4) =
      ds + n2w (4 * LENGTH data)) ∧
     (word_of_bytes F 0w (GENLIST (final_st.mem o ((+) (hs + 3w * 4w)) o n2w) 4) =
      ds) ∧
     (word_of_bytes F 0w (GENLIST (final_st.mem o ((+) (hs + 4w * 4w)) o n2w) 4) =
      ds) ∧
     (∀k. k < 4 * LENGTH data + 4 ⇒
          (final_st.mem (ds + n2w k) =
           (hello_init_memory r0 (cl,inp)) (ds + n2w k)))`,
  strip_tac
  \\ qho_match_abbrev_tac`LET (λtr. (_ tr) ∧ P (_ tr)) _`
  \\ rewrite_tac[hello_startup_asm_code_eq,
                 EVAL``ag32_startup_addresses r0``]
  \\ simp[]
  \\ qmatch_goalsub_abbrev_tac`steps _ _ (i::tr)`
  \\ simp[steps_def, steps_rel_def]
  \\ qmatch_goalsub_abbrev_tac`asm_step c _ _ s2`
  \\ `c = ag32_config` by simp[Abbr`c`, ag32_targetTheory.ag32_target_def]
  \\ qpat_x_assum`Abbrev (c = _)`kall_tac
  \\ simp[asmSemTheory.asm_step_def, ag32_targetTheory.ag32_config, Abbr`i`]
  \\ qpat_x_assum`Abbrev (s2 = _)`mp_tac
  \\ CONV_TAC(ONCE_DEPTH_CONV ag32_enc_conv)
  \\ simp [ag32_init_asm_state_def]
  \\ `ag32_init_regs r0 = (λk. ag32_init_regs r0 k)` by simp[FUN_EQ_THM]
  \\ pop_assum SUBST1_TAC
  \\ simp[ag32_targetTheory.ag32_init_regs_def]
  \\ CONV_TAC (PATH_CONV "lrrr" asm_conv)
  \\ strip_tac
  \\ rewrite_tac[GSYM CONJ_ASSOC]
  \\ conj_tac >- bytes_in_memory_tac
  \\ conj_tac >- simp[Abbr`s2`]
  \\ conj_tac >- CONV_TAC asm_conv
  \\ qunabbrev_tac`tr`
  \\ rpt (
    qmatch_goalsub_abbrev_tac`steps _ _ (i::tr)`
    \\ simp[steps_def, steps_rel_def, Abbr`s2`]
    \\ qmatch_goalsub_abbrev_tac`asm_step _ _ _ s2`
    \\ simp[asmSemTheory.asm_step_def,
            ag32_targetTheory.ag32_config,
            Abbr`i`]
    \\ qpat_x_assum`Abbrev (s2 = _)`mp_tac
    \\ CONV_TAC(ONCE_DEPTH_CONV ag32_enc_conv)
    \\ simp[]
    \\ CONV_TAC (PATH_CONV "lrrr" asm_conv)
    \\ strip_tac
    \\ rewrite_tac[GSYM CONJ_ASSOC]
    \\ conj_tac >- (bytes_in_memory_tac)
    \\ qmatch_asmsub_abbrev_tac`_ with failed updated_by (K Z)`
    \\ `Z = F` by ( simp[Abbr`Z`] \\ mem_ok_tac)
    \\ qpat_x_assum`Abbrev(Z = _)` kall_tac
    \\ pop_assum SUBST_ALL_TAC
    \\ conj_tac >- ( simp[Abbr`s2`] \\ mem_ok_tac )
    \\ conj_tac >- CONV_TAC asm_conv
    \\ qunabbrev_tac`tr` )
  \\ simp[steps_def, steps_rel_def]
  \\ simp_tac (std_ss++LET_ss) [Abbr`s2`,Abbr`P`]
  \\ conj_tac >- (EVAL_TAC \\ simp[ffi_names])
  \\ conj_tac >- (
    simp[hello_machine_config_def,
         lab_to_targetTheory.ffi_offset_def,
         heap_size_def, memory_size_def, LENGTH_data,
         ag32_targetTheory.ag32_target_def]
    \\ match_mp_tac data_to_word_assignProofTheory.IMP_read_bytearray_GENLIST
    \\ simp[]
    \\ gen_tac \\ strip_tac
    \\ qpat_x_assum`_ < dimword _`mp_tac
    \\ CONV_TAC(LAND_CONV EVAL)
    \\ CONV_TAC(PATH_CONV"rlr" EVAL)
    \\ Cases_on`r0`
    \\ fs[word_add_n2w, word_ls_n2w, word_lo_n2w, LENGTH_code, LENGTH_data, ffi_names]
    \\ strip_tac
    \\ rewrite_tac[hello_init_memory_def]
    \\ qmatch_goalsub_abbrev_tac`i + k`
    \\ `byte_aligned ((n2w k):word32)` by(
      simp[Abbr`k`, GSYM word_add_n2w, alignmentTheory.byte_aligned_def]
      \\ (alignmentTheory.aligned_add_sub_cor
          |> SPEC_ALL |> UNDISCH |> CONJUNCT1 |> DISCH_ALL
          |> irule)
      \\ fs[alignmentTheory.byte_aligned_def]
      \\ EVAL_TAC )
    \\ `n2w k = byte_align ((n2w k):word32)`
    by (
      fs[alignmentTheory.byte_aligned_def,
         alignmentTheory.byte_align_def,
         alignmentTheory.aligned_def] )
    \\ once_rewrite_tac[GSYM word_add_n2w]
    \\ first_assum(CONV_TAC o PATH_CONV"lrllrr" o REWR_CONV)
    \\ DEP_REWRITE_TAC[data_to_word_memoryProofTheory.get_byte_byte_align]
    \\ conj_tac >- EVAL_TAC
    \\ `byte_align (n2w i + n2w k) : word32 = byte_align (n2w i) + n2w k`
    by (
      once_rewrite_tac[WORD_ADD_COMM]
      \\ rewrite_tac[alignmentTheory.byte_align_def]
      \\ irule align_add_aligned_gen
      \\ fs[alignmentTheory.byte_aligned_def] )
    \\ once_asm_rewrite_tac[]
    \\ qunabbrev_tac`k`
    \\ rewrite_tac[WORD_ADD_SUB_SYM]
    \\ rewrite_tac[GSYM word_add_n2w]
    \\ rewrite_tac[WORD_ADD_ASSOC]
    \\ rewrite_tac[WORD_SUB_ADD]
    \\ DEP_REWRITE_TAC[w2n_add]
    \\ conj_tac
    >- (
      reverse conj_tac >- EVAL_TAC
      \\ simp[alignmentTheory.byte_align_def]
      \\ simp[alignmentTheory.align_w2n]
      \\ simp[multiwordTheory.d_word_msb]
      \\ DEP_REWRITE_TAC[LESS_MOD]
      \\ fs[NOT_LESS_EQUAL]
      \\ conj_tac
      \\ irule IMP_MULT_DIV_LESS
      \\ fs[] )
    \\ simp[ADD_DIV_RWT]
    \\ rewrite_tac[hello_init_memory_words_def]
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
    \\ rewrite_tac[GSYM APPEND_ASSOC] \\ DEP_ONCE_REWRITE_TAC[EL_APPEND2]
    \\ simp[LENGTH_words_of_bytes, bitstringTheory.length_pad_right]
    \\ qmatch_goalsub_abbrev_tac`MIN 1 (sz MOD _)` \\ `sz = stdin_size` by ( simp[Abbr`sz`] )
    \\ qpat_x_assum`Abbrev(sz = _)`kall_tac \\ pop_assum SUBST_ALL_TAC
    \\ simp[stdin_size_def, bytes_in_word_def]
    \\ rewrite_tac[GSYM APPEND_ASSOC] \\ DEP_ONCE_REWRITE_TAC[EL_APPEND2]
    \\ simp[output_buffer_size_def]
    \\ rewrite_tac[GSYM APPEND_ASSOC] \\ DEP_ONCE_REWRITE_TAC[EL_APPEND2]
    \\ simp[LENGTH_ag32_ffi_code]
    \\ rewrite_tac[GSYM APPEND_ASSOC] \\ DEP_ONCE_REWRITE_TAC[EL_APPEND2]
    \\ simp[heap_size_def,alignmentTheory.byte_align_def,alignmentTheory.align_w2n]
    \\ rewrite_tac[GSYM APPEND_ASSOC] \\ DEP_ONCE_REWRITE_TAC[EL_APPEND2]
    \\ qmatch_goalsub_abbrev_tac`ll ≤ _`
    \\ pop_assum mp_tac
    \\ CONV_TAC(LAND_CONV EVAL)
    \\ simp[ffi_names]
    \\ CONV_TAC(LAND_CONV EVAL)
    \\ strip_tac \\ simp[Abbr`ll`]
    \\ simp[EL_APPEND_EQN, LENGTH_words_of_bytes,LENGTH_code]
    \\ reverse IF_CASES_TAC
    >- (
      pop_assum mp_tac
      \\ DEP_ONCE_REWRITE_TAC[LESS_MOD]
      \\ simp[bytes_in_word_def]
      \\ once_rewrite_tac[MULT_COMM]
      \\ DEP_REWRITE_TAC[MULT_DIV]
      \\ simp[DIV_LT_X]
      \\ DEP_REWRITE_TAC[IMP_MULT_DIV_LESS]
      \\ simp[] )
    \\ (alignmentTheory.byte_align_def
        |> SIMP_RULE (srw_ss()) [alignmentTheory.align_w2n]
        |> Q.ISPEC_THEN`(n2w i):word32`mp_tac)
    \\ simp[]
    \\ disch_then(mp_tac o CONV_RULE(REWR_CONV (GSYM w2n_11)))
    \\ rewrite_tac[w2n_n2w]
    \\ simp[]
    \\ disch_then(SUBST1_TAC o SYM)
    \\ `4 = w2n (bytes_in_word:word32)` by EVAL_TAC
    \\ pop_assum SUBST1_TAC
    \\ irule get_byte_EL_words_of_bytes
    \\ simp[LENGTH_code, bytes_in_word_def]
    \\ EVAL_TAC)
  \\ conj_tac >- EVAL_TAC
  \\ conj_tac >- (EVAL_TAC \\ simp[])
  \\ conj_tac >- mem_word_tac
  \\ conj_tac >- mem_word_tac
  \\ conj_tac >- mem_word_tac
  \\ conj_tac >- mem_word_tac
  \\ conj_tac >- mem_word_tac
  \\ simp_tac std_ss [asmSemTheory.asm_state_accfupds]
  \\ simp[LENGTH_code,ffi_names,EVAL``code_start_offset num_ffis``,LENGTH_data]
  \\ gen_tac \\ strip_tac
  \\ Cases_on`r0` \\ fs[memory_size_def]
  \\ rewrite_tac[word_add_n2w] \\ rw[]);

val hello_init_asm_state_RTC_asm_step = Q.store_thm("hello_init_asm_state_RTC_asm_step",
  `byte_aligned r0 ∧ w2n r0 + memory_size < dimword(:32) ∧
   SUM (MAP strlen cl) + LENGTH cl ≤ cline_size ∧
   LENGTH inp ≤ stdin_size
  ⇒
   (λx y. ∃i. asm_step ag32_config x i y)^* hello_asm_state0 (hello_init_asm_state r0 (cl,inp)) ∧
   let ffi_names = THE config.ffi_names in
   let num_ffis = LENGTH ffi_names in
   let hs = r0 + n2w heap_start_offset in
   let ds = r0 + n2w (code_start_offset num_ffis + LENGTH code) in
   ((hello_init_asm_state r0 (cl,inp)).pc = r0 + n2w (code_start_offset num_ffis)) ∧
   (read_bytearray (hello_init_asm_state r0 (cl,inp)).pc (LENGTH code)
      (λa. if a ∈ (hello_machine_config r0).prog_addresses then SOME ((hello_init_asm_state r0 (cl,inp)).mem a) else NONE)
      = SOME code) ∧
    ((hello_init_asm_state r0 (cl,inp)).regs 2 = hs) ∧
    ((hello_init_asm_state r0 (cl,inp)).regs 4 = hs + n2w heap_size) ∧
    (word_of_bytes F 0w (GENLIST ((hello_init_asm_state r0 (cl,inp)).mem o ((+)(hs + 0w * 4w)) o n2w) 4)
     = ds) ∧
    (word_of_bytes F 0w (GENLIST ((hello_init_asm_state r0 (cl,inp)).mem o ((+)(hs + 1w * 4w)) o n2w) 4)
     = ds + n2w (4 * LENGTH data)) ∧
    (word_of_bytes F 0w (GENLIST ((hello_init_asm_state r0 (cl,inp)).mem o ((+)(hs + 2w * 4w)) o n2w) 4)
     = ds + n2w (4 * LENGTH data)) ∧
    (word_of_bytes F 0w (GENLIST ((hello_init_asm_state r0 (cl,inp)).mem o ((+)(hs + 3w * 4w)) o n2w) 4)
     = ds) ∧
    (word_of_bytes F 0w (GENLIST ((hello_init_asm_state r0 (cl,inp)).mem o ((+)(hs + 4w * 4w)) o n2w) 4)
     = ds) ∧
    (∀k. k < 4 * LENGTH data + 4 ⇒
      ((hello_init_asm_state r0 (cl,inp)).mem (ds + n2w k) =
       hello_init_memory r0 (cl,inp) (ds + n2w k)))`,
  disch_then assume_tac
  \\ mp_tac (UNDISCH hello_init_asm_state_asm_step)
  \\ simp[]
  \\ strip_tac
  \\ drule steps_rel_LRC
  \\ strip_tac
  \\ (NRC_LRC |> EQ_IMP_RULE |> #2 |> Q.GEN`n` |> SIMP_RULE bool_ss [PULL_EXISTS] |> drule)
  \\ simp[]
  \\ strip_tac
  \\ drule NRC_RTC
  \\ fs[LAST_MAP_SND_steps_FOLDL, GSYM hello_init_asm_state_def]
  \\ fs[ag32_targetTheory.ag32_target_def]);

val target_state_rel_hello_init_asm_state = Q.store_thm("target_state_rel_hello_init_asm_state",
  `byte_aligned r0 ∧ w2n r0 + memory_size < dimword (:32) ∧
   SUM (MAP strlen cl) + LENGTH cl ≤ cline_size ∧
   LENGTH inp ≤ stdin_size ∧
   is_ag32_init_state (hello_init_memory r0 (cl,inp)) r0 ms ⇒
   ∃n. target_state_rel ag32_target (hello_init_asm_state r0 (cl,inp)) (FUNPOW Next n ms) ∧
       ((FUNPOW Next n ms).io_events = ms.io_events) ∧
       (∀x. x ∉ (ag32_startup_addresses r0) ⇒
         ((FUNPOW Next n ms).MEM x = ms.MEM x))`,
  strip_tac
  \\ imp_res_tac hello_init_asm_state_RTC_asm_step
  \\ drule (GEN_ALL target_state_rel_ag32_init)
  \\ disch_then drule
  \\ qmatch_goalsub_abbrev_tac`_ ∉ md`
  \\ disch_then(qspec_then`md`assume_tac)
  \\ drule (GEN_ALL RTC_asm_step_ag32_target_state_rel_io_events)
  \\ simp[EVAL``(ag32_init_asm_state m md r0).mem_domain``]);

val hello_startup_clock_def =
  new_specification("hello_startup_clock_def",["hello_startup_clock"],
  GEN_ALL (Q.SPEC`ms0`(Q.GEN`ms`target_state_rel_hello_init_asm_state))
  |> SIMP_RULE bool_ss [GSYM RIGHT_EXISTS_IMP_THM,SKOLEM_THM]);

val hello_good_init_state = Q.store_thm("hello_good_init_state",
  `byte_aligned r0 ∧ w2n r0 + memory_size < dimword(:32) ∧
   SUM (MAP strlen cl) + LENGTH cl ≤ cline_size ∧
   LENGTH inp ≤ stdin_size ∧
   is_ag32_init_state (hello_init_memory r0 (cl,inp)) r0 ms0 ⇒
   ∃io_regs cc_regs.
   good_init_state (hello_machine_config r0) (FUNPOW Next (hello_startup_clock r0 ms0 inp cl) ms0)
     (basis_ffi cl fs) code 0
     ((hello_init_asm_state r0 (cl,inp)) with mem_domain := (hello_machine_config r0).prog_addresses)
     (λk. Word
       (word_of_bytes F 0w (GENLIST (λi. (hello_init_asm_state r0 (cl,inp)).mem (k + n2w i)) 4)))
       ({w | (hello_init_asm_state r0 (cl,inp)).regs 2 <=+ w ∧
             w <+ (hello_init_asm_state r0 (cl,inp)).regs 4}
        ∪ {w | r0 + n2w (code_start_offset (LENGTH (THE config.ffi_names)) + LENGTH code) <=+ w ∧
               w <+ r0 + n2w(code_start_offset (LENGTH (THE config.ffi_names)) + LENGTH code + 4 * LENGTH data) })
     io_regs
     cc_regs`,
  strip_tac
  \\ drule hello_startup_clock_def \\ fs[]
  \\ disch_then drule \\ disch_then drule
  \\ disch_then drule
  \\ strip_tac
  \\ simp[lab_to_targetProofTheory.good_init_state_def,RIGHT_EXISTS_AND_THM]
  \\ drule hello_init_asm_state_RTC_asm_step
  \\ impl_tac >- fs[]
  \\ strip_tac
  \\ conj_tac >- (
    fs[hello_machine_config_def, ag32_machine_config_def]
    \\ fs[asmPropsTheory.target_state_rel_def]
    \\ fs[EVAL``ag32_target.get_byte``]
    \\ qx_gen_tac`a` \\ strip_tac
    \\ drule RTC_asm_step_consts
    \\ strip_tac \\ fs[]
    \\ `hello_asm_state0.mem_domain = ag32_startup_addresses r0` by (
      fs[ag32_init_asm_state_def] )
    \\ fs[]
    \\ Cases_on`a ∈ ag32_startup_addresses r0` \\ fs[]
    \\ drule RTC_asm_step_outside_mem_domain
    \\ simp[]
    \\ fs[is_ag32_init_state_def]
    \\ simp[ag32_init_asm_state_def])
  \\ conj_tac
  >- (
    Q.ISPEC_THEN `hello_machine_config r0 with prog_addresses := ag32_startup_addresses r0`
      drule (Q.GEN`mc` RTC_asm_step_target_configured)
    \\ simp[lab_to_targetProofTheory.target_configured_def]
    \\ impl_tac >- EVAL_TAC
    \\ strip_tac \\ fs[])
  \\ conj_tac >- (
    fs[asmPropsTheory.target_state_rel_def, hello_machine_config_def, ag32_machine_config_def] )
  \\ qabbrev_tac`num_ffis = LENGTH (THE config.ffi_names)`
  \\ `r0 + n2w (code_start_offset num_ffis) && 3w = 0w` by (
    EVAL_TAC
    \\ fs[alignmentTheory.aligned_bitwise_and, alignmentTheory.byte_aligned_def, Abbr`num_ffis`, ffi_names]
    \\ Cases_on`r0`
    \\ simp[word_add_n2w]
    \\ once_rewrite_tac[WORD_AND_COMM]
    \\ rewrite_tac[addressTheory.n2w_and_3]
    \\ qpat_x_assum`_ = 0w`mp_tac
    \\ once_rewrite_tac[WORD_AND_COMM]
    \\ rewrite_tac[addressTheory.n2w_and_3]
    \\ EVAL_TAC
    \\ simp[] )
  \\ `r0 + n2w (code_start_offset num_ffis) && 1w = 0w` by (
    EVAL_TAC
    \\ fs[alignmentTheory.aligned_bitwise_and, alignmentTheory.byte_aligned_def, Abbr`num_ffis`, ffi_names]
    \\ Cases_on`r0`
    \\ simp[word_add_n2w]
    \\ once_rewrite_tac[WORD_AND_COMM]
    \\ rewrite_tac[addressTheory.n2w_and_1]
    \\ qpat_x_assum`_ && n2w _ = 0w`mp_tac
    \\ once_rewrite_tac[WORD_AND_COMM]
    \\ rewrite_tac[addressTheory.n2w_and_3]
    \\ EVAL_TAC
    \\ simp[]
    \\ DEP_ONCE_REWRITE_TAC[LESS_MOD]
    \\ conj_tac
    >- (
      match_mp_tac LESS_LESS_EQ_TRANS
      \\ qexists_tac`4`
      \\ simp[MOD_LESS] )
    \\ strip_tac
    \\ DEP_ONCE_REWRITE_TAC[LESS_MOD]
    \\ conj_tac
    >- (
      match_mp_tac LESS_LESS_EQ_TRANS
      \\ qexists_tac`2`
      \\ simp[MOD_LESS] )
    \\ fs[MOD_EQ_0_DIVISOR]
    \\ qexists_tac`2 * d`
    \\ simp[] )
  \\ conj_tac >- (
    rewrite_tac[lab_to_targetProofTheory.start_pc_ok_def]
    \\ conj_tac >- (
      qpat_x_assum`_ < _`mp_tac
      \\ EVAL_TAC \\ simp[LENGTH_code, LENGTH_data, ffi_names, Abbr`num_ffis`]
      \\ Cases_on`r0`
      \\ fs[WORD_LOWER_OR_EQ,WORD_NOT_LOWER,word_add_n2w,word_ls_n2w,word_lo_n2w] )
    \\ conj_tac >- (
      qpat_x_assum`_ < _`mp_tac
      \\ EVAL_TAC \\ simp[LENGTH_code, LENGTH_data, ffi_names, Abbr`num_ffis`]
      \\ Cases_on`r0`
      \\ simp[WORD_LOWER_OR_EQ,WORD_NOT_LOWER,word_add_n2w,word_ls_n2w,word_lo_n2w] )
    \\ simp[lab_to_targetTheory.ffi_offset_def]
    \\ conj_tac >- (EVAL_TAC \\ simp[ffi_names,Abbr`num_ffis`])
    \\ conj_tac >- (EVAL_TAC \\ simp[ffi_names,Abbr`num_ffis`] )
    \\ conj_tac >- fs[]
    \\ rewrite_tac[EVAL``(hello_machine_config r0).ffi_names``]
    \\ fs[ffi_names, Abbr`num_ffis`,lab_to_targetTheory.ffi_offset_def, EVAL``code_start_offset n``]
    \\ simp[hello_machine_config_def, ffi_names, ag32_machine_config_def]
    \\ EVAL_TAC \\ simp[LENGTH_data, LENGTH_code]
    \\ Cases_on`r0`
    \\ fs[WORD_LOWER_OR_EQ,WORD_NOT_LOWER,word_add_n2w,word_ls_n2w,word_lo_n2w,memory_size_def] )
  \\ conj_tac >- (
    qpat_x_assum`_ && 3w = _`mp_tac
    \\ EVAL_TAC \\ fs[] )
  \\ conj_tac >- (
    rw[asmPropsTheory.interference_ok_def]
    \\ simp[EVAL``(hello_machine_config r0).target``]
    \\ simp[EVAL``(hello_machine_config r0).next_interfer``] )
  \\ simp[LEFT_EXISTS_AND_THM]
  \\ conj_tac >- (
    simp[lab_to_targetProofTheory.ffi_interfer_ok_def]
    \\ simp[hello_machine_config_def, ag32_machine_config_def]
    \\ simp[lab_to_targetTheory.ffi_offset_def,LENGTH_data,heap_size_def,Abbr`num_ffis`,ffi_names]
    \\ simp[EVAL``ag32_target.config``,labSemTheory.get_reg_value_def]
    \\ simp[ag32_ffi_interfer_def]
    \\ simp[LENGTH_ag32_ffi_code,LENGTH_code]
    \\ qmatch_goalsub_abbrev_tac`0w =+ v0`
    \\ qexists_tac`λk n. if n = 0 then SOME v0 else if n < 9 then SOME 0w else NONE`
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
      \\ simp[ag32_ffi_write_mem_update_def]
      \\ qmatch_goalsub_abbrev_tac`asm_write_bytearray p new_bytes m2`
      \\ `asm_write_bytearray p new_bytes m2 a = asm_write_bytearray p new_bytes t1.mem a`
      by (
        irule mem_eq_imp_asm_write_bytearray_eq
        \\ simp[Abbr`m2`, APPLY_UPDATE_THM] \\ rw[]
        \\ qpat_x_assum`_ ∈ _.mem_domain`mp_tac
        \\ qpat_x_assum`_ = _.mem_domain`(assume_tac o SYM)
        \\ simp[ag32_prog_addresses_def]
        \\ EVAL_TAC
        \\ Cases_on`r0` \\ fs[memory_size_def, word_add_n2w, word_ls_n2w, word_lo_n2w] )
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
      \\ Cases_on`r0` \\ fs[memory_size_def, word_add_n2w]
      \\ qpat_x_assum`_ ∈ _.mem_domain`mp_tac
      \\ qpat_x_assum`_ = _.mem_domain`(mp_tac o SYM)
      \\ simp[ag32_prog_addresses_def]
      \\ strip_tac
      \\ CONV_TAC(LAND_CONV EVAL)
      \\ Cases_on`a` \\ fs[word_ls_n2w, word_lo_n2w]
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
    \\ simp[SIMP_CONV (srw_ss()) [hello_machine_config_def,ag32_machine_config_def]``(hello_machine_config r0).target``]
    \\ rfs[]
    \\ first_x_assum(CONV_TAC o RAND_CONV o REWR_CONV o SYM)
    \\ AP_TERM_TAC
    \\ rw[FUN_EQ_THM]
    \\ rw[]
    \\ match_mp_tac EQ_SYM
    \\ fs[EVAL``ag32_target.get_byte``]
    \\ reverse(Cases_on`a ∈ ag32_startup_addresses r0`) \\ fs[]
    >- (
      drule RTC_asm_step_outside_mem_domain
      \\ simp[ag32_init_asm_state_def]
      \\ fs[is_ag32_init_state_def] )
    \\ imp_res_tac RTC_asm_step_consts \\ fs[]
    \\ fs[ag32_init_asm_state_def])
  \\ conj_tac >- (
    fs[bytes_in_mem_bytes_in_memory]
    \\ qpat_x_assum`_.pc = _`(assume_tac o SYM) \\ fs[]
    \\ irule read_bytearray_IMP_bytes_in_memory
    \\ goal_assum(first_assum o mp_then Any mp_tac)
    \\ simp[]
    \\ imp_res_tac RTC_asm_step_consts
    \\ qpat_x_assum`_ = _.pc`(assume_tac o SYM) \\ fs[]
    \\ EVAL_TAC
    \\ simp[LENGTH_data,LENGTH_code,Abbr`num_ffis`,ffi_names]
    \\ Cases_on`r0` \\  fs[word_add_n2w,memory_size_def]
    \\ Cases \\ fs[word_lo_n2w, word_ls_n2w])
  \\ conj_tac >- (
    qpat_x_assum`_ + _ < _`mp_tac
    \\ imp_res_tac RTC_asm_step_consts
    \\ fs[LENGTH_data,heap_size_def]
    \\ EVAL_TAC
    \\ simp[SUBSET_DEF, LENGTH_code, LENGTH_data, Abbr`num_ffis`, ffi_names]
    \\ Cases_on`r0` \\ fs[word_add_n2w]
    \\ strip_tac
    \\ simp[GSYM FORALL_AND_THM]
    \\ Cases
    \\ fs[word_lo_n2w, word_ls_n2w])
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
      \\ rewrite_tac[word_add_n2w, GSYM WORD_ADD_ASSOC]
      \\ conj_tac
      \\ (alignmentTheory.aligned_add_sub_cor
          |> SPEC_ALL |> UNDISCH |> CONJUNCT1 |> DISCH_ALL
          |> irule)
      \\ fs[]
      \\ EVAL_TAC )
    \\ disj2_tac
    \\ irule (SIMP_RULE (srw_ss()) [] byte_align_IN_IMP_IN_range)
    \\ simp[heap_size_def,LENGTH_data,LENGTH_code]
    \\ fs[alignmentTheory.byte_aligned_def,Abbr`hi`,heap_size_def]
    \\ conj_tac
    \\ (alignmentTheory.aligned_add_sub_cor
        |> SPEC_ALL |> UNDISCH |> CONJUNCT1 |> DISCH_ALL
        |> irule)
    \\ fs[]
    \\ simp[Abbr`num_ffis`,ffi_names]
    \\ EVAL_TAC )
  \\ conj_tac >- (
    simp[EVAL``(hello_machine_config r0).target.config``]
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
  `is_ag32_machine_config (hello_machine_config r0)`,
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
  `byte_aligned r0 ∧ w2n r0 + memory_size < dimword (:32) ∧
   SUM (MAP strlen cl) + LENGTH cl ≤ cline_size ∧
   LENGTH inp ≤ stdin_size ∧
   is_ag32_init_state (hello_init_memory r0 (cl,inp)) r0 ms0 ⇒
   installed code 0 data 0 config.ffi_names (basis_ffi cl fs)
     (heap_regs ag32_backend_config.stack_conf.reg_names)
     (hello_machine_config r0) (FUNPOW Next (hello_startup_clock r0 ms0 inp cl) ms0)`,
  disch_then assume_tac
  \\ CONV_TAC(PATH_CONV"llr"EVAL)
  \\ simp[backendProofTheory.installed_def]
  \\ simp[word_list_exists_def, set_sepTheory.SEP_CLAUSES, word_list_def]
  \\ simp[EVAL``(hello_machine_config r0).target.get_pc``]
  \\ strip_assume_tac(UNDISCH hello_good_init_state)
  \\ fs[]
  \\ drule hello_init_asm_state_RTC_asm_step
  \\ impl_tac >- fs[]
  \\ strip_tac
  \\ qmatch_asmsub_abbrev_tac`good_init_state _ _ _ _ _ t`
  \\ qexists_tac`t` \\ simp[Abbr`t`]
  \\ asm_exists_tac \\ rfs[]
  \\ qhdtm_x_assum`good_init_state` mp_tac
  \\ rewrite_tac[lab_to_targetProofTheory.good_init_state_def]
  \\ disch_then(assume_tac o el 1 o CONJUNCTS)
  \\ conj_tac
  >- (irule byte_aligned_add \\ simp[] \\ EVAL_TAC)
  \\ conj_tac
  >- (irule byte_aligned_add \\ simp[]
      \\ reverse conj_tac >- EVAL_TAC
      \\ irule byte_aligned_add \\ simp[]
      \\ EVAL_TAC)
  \\ conj_tac
  >- (irule byte_aligned_add \\ simp[ffi_names, LENGTH_code] \\ EVAL_TAC)
  \\ conj_tac
  >- (Cases_on`r0`
      \\ EVAL_TAC
      \\ fs[memory_size_def, heap_size_def])
  \\ conj_tac
  >- ( Cases_on`r0` \\ simp[WORD_LEFT_ADD_DISTRIB] \\ EVAL_TAC )
  \\ conj_tac
  >- (
    simp[IN_DISJOINT]
    \\ qpat_x_assum`_ < _`mp_tac
    \\ EVAL_TAC
    \\ simp[LENGTH_code,LENGTH_data,ffi_names]
    \\ strip_tac
    \\ Cases
    \\ Cases_on`r0`
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
    \\ Cases_on`r0` \\ fs[word_add_n2w]
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
      \\ (alignmentTheory.aligned_add_sub_cor
          |> SPEC_ALL |> UNDISCH |> CONJUNCT1 |> DISCH_ALL
          |> irule)
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
      \\ `ls = GENLIST (λi. hello_init_memory (n2w n) (cl,inp) (n2w (4 * (k + (off DIV 4)) + n + i))) 4`
      by ( simp[Abbr`ls`,Abbr`off`,LEFT_ADD_DISTRIB] )
      \\ qpat_x_assum`Abbrev(ls = _)`kall_tac
      \\ pop_assum SUBST_ALL_TAC
      \\ simp[Abbr`off`, GSYM word_add_n2w]
      \\ simp[hello_init_memory_def]
      \\ rewrite_tac[GSYM WORD_ADD_ASSOC]
      \\ `∀x:word32. get_byte (n2w n + x) = get_byte x`
      by (
        simp[Once ADD_COMM]
        \\ `(n2w n : word32) = byte_align ((n2w n):word32)`
        by ( fs[alignmentTheory.byte_aligned_def, alignmentTheory.byte_align_def, alignmentTheory.aligned_def] )
        \\ pop_assum SUBST1_TAC
        \\ simp[FUN_EQ_THM]
        \\ rpt gen_tac
        \\ match_mp_tac data_to_word_memoryProofTheory.get_byte_byte_align
        \\ EVAL_TAC )
      \\ simp[]
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
      \\ `∀x:word32. byte_align (n2w n + x) = byte_align x + n2w n`
      by (
        `(n2w n : word32) = byte_align ((n2w n):word32)`
        by ( fs[alignmentTheory.byte_aligned_def, alignmentTheory.byte_align_def, alignmentTheory.aligned_def] )
        \\ fs[alignmentTheory.byte_aligned_def, alignmentTheory.byte_align_def]
        \\ gen_tac
        \\ once_rewrite_tac[WORD_ADD_COMM]
        \\ DEP_REWRITE_TAC[align_add_aligned_gen]
        \\ simp[] )
      \\ rewrite_tac[GSYM WORD_ADD_ASSOC]
      \\ simp[]
      \\ rewrite_tac[GSYM WORD_ADD_ASSOC]
      \\ qmatch_goalsub_abbrev_tac`(_:word32) + zz`
      \\ `zz = 0w`
      by ( simp[Abbr`zz`, word_add_n2w] )
      \\ qpat_x_assum`Abbrev(zz = _)`kall_tac
      \\ rw[]
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
      \\ rewrite_tac[hello_init_memory_words_def]
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
      \\ simp[data_to_word_memoryProofTheory.word_of_bytes_def]
      \\ simp[wordSemTheory.get_byte_def, wordSemTheory.byte_index_def,
              wordSemTheory.set_byte_def, wordSemTheory.word_slice_alt_def]
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
      \\ qmatch_asmsub_abbrev_tac`4 * d + (p + m) = 4 * q`
      \\ qexists_tac`(q - d - m DIV 4)`
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
    \\ `ls = GENLIST (λi. hello_init_memory (n2w n) (cl,inp) (n2w (4 * (d + (off DIV 4)) + n + i))) 4`
    by ( simp[Abbr`ls`,Abbr`off`,LEFT_ADD_DISTRIB] )
    \\ qpat_x_assum`Abbrev(ls = _)`kall_tac
    \\ pop_assum SUBST_ALL_TAC
    \\ simp[Abbr`off`, GSYM word_add_n2w]
    \\ simp[hello_init_memory_def]
    \\ rewrite_tac[GSYM WORD_ADD_ASSOC]
    \\ `∀x:word32. get_byte (n2w n + x) = get_byte x`
    by (
      simp[Once ADD_COMM]
      \\ `(n2w n : word32) = byte_align ((n2w n):word32)`
      by ( fs[alignmentTheory.byte_aligned_def, alignmentTheory.byte_align_def, alignmentTheory.aligned_def] )
      \\ pop_assum SUBST1_TAC
      \\ simp[FUN_EQ_THM]
      \\ rpt gen_tac
      \\ match_mp_tac data_to_word_memoryProofTheory.get_byte_byte_align
      \\ EVAL_TAC )
    \\ simp[]
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
    \\ `∀x:word32. byte_align (n2w n + x) = byte_align x + n2w n`
    by (
      `(n2w n : word32) = byte_align ((n2w n):word32)`
      by ( fs[alignmentTheory.byte_aligned_def, alignmentTheory.byte_align_def, alignmentTheory.aligned_def] )
      \\ fs[alignmentTheory.byte_aligned_def, alignmentTheory.byte_align_def]
      \\ gen_tac
      \\ once_rewrite_tac[WORD_ADD_COMM]
      \\ DEP_REWRITE_TAC[align_add_aligned_gen]
      \\ simp[] )
    \\ rewrite_tac[GSYM WORD_ADD_ASSOC]
    \\ simp[]
    \\ rewrite_tac[GSYM WORD_ADD_ASSOC]
    \\ qmatch_goalsub_abbrev_tac`(_:word32) + zz`
    \\ `zz = 0w`
    by ( simp[Abbr`zz`, word_add_n2w] )
    \\ qpat_x_assum`Abbrev(zz = _)`kall_tac
    \\ rw[]
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
    \\ rewrite_tac[hello_init_memory_words_def]
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
    \\ simp[data_to_word_memoryProofTheory.word_of_bytes_def]
    \\ simp[wordSemTheory.get_byte_def, wordSemTheory.byte_index_def,
            wordSemTheory.set_byte_def, wordSemTheory.word_slice_alt_def]
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
    byte_aligned r0 ∧ w2n r0 + memory_size < dimword (:32) ∧
    SUM (MAP strlen cl) + LENGTH cl ≤ cline_size ∧
    LENGTH inp ≤ stdin_size ∧
    (mc = hello_machine_config r0) ∧
    (ms.PC = mc.halt_pc) ∧
    (∀x. mc.halt_pc <=+ x ∧ x <+ mc.halt_pc + 16w ⇒
         (mc.target.get_byte ms x = (hello_init_memory r0 (cl,inp)) x)) ⇒
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
    \\ (alignmentTheory.aligned_add_sub_cor
        |> SPEC_ALL |> UNDISCH |> CONJUNCT1 |> DISCH_ALL
        |> irule)
    \\ fs[alignmentTheory.byte_aligned_def]
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
  \\ impl_tac
  >- (
    simp[]
    \\ Cases_on`r0`
    \\ fs[word_add_n2w,word_ls_n2w,word_lo_n2w,memory_size_def]
    \\ simp[hello_machine_config_halt_pc, word_add_n2w]
    \\ fs[word_add_n2w,word_ls_n2w,word_lo_n2w,memory_size_def] )
  \\ first_assum(qspec_then`ms.PC + 1w`mp_tac)
  \\ impl_tac
  >- (
    simp[]
    \\ Cases_on`r0`
    \\ simp[hello_machine_config_halt_pc]
    \\ fs[word_add_n2w,word_ls_n2w,word_lo_n2w,memory_size_def] )
  \\ first_assum(qspec_then`ms.PC + 2w`mp_tac)
  \\ impl_tac
  >- (
    simp[]
    \\ Cases_on`r0`
    \\ simp[hello_machine_config_halt_pc]
    \\ fs[word_add_n2w,word_ls_n2w,word_lo_n2w,memory_size_def] )
  \\ first_x_assum(qspec_then`ms.PC + 3w`mp_tac)
  \\ impl_tac
  >- (
    simp[]
    \\ Cases_on`r0`
    \\ simp[hello_machine_config_halt_pc]
    \\ fs[word_add_n2w,word_ls_n2w,word_lo_n2w,memory_size_def] )
  \\ simp[]
  \\ simp[EVAL``(hello_machine_config r0).target.get_byte``]
  \\ rpt (disch_then SUBST_ALL_TAC)
  \\ qmatch_goalsub_abbrev_tac`_ @@ hello_init_memory r0 _ pc`
  \\ drule hello_init_memory_halt
  \\ impl_tac >- simp[]
  \\ simp[]
  \\ disch_then kall_tac
  \\ simp[ag32_targetProofTheory.Decode_Encode]
  \\ simp[ag32Theory.Run_def, ag32Theory.dfn'Jump_def]
  \\ simp[ag32Theory.ALU_def, ag32Theory.ri2word_def]
  \\ strip_tac
  \\ simp[Abbr`ms1`, APPLY_UPDATE_THM]);

val hello_interference_implemented = Q.store_thm("hello_interference_implemented",
  `byte_aligned r0 ∧ w2n r0 + memory_size < dimword (:32) ∧
   SUM (MAP strlen cl) + LENGTH cl ≤ cline_size ∧
   LENGTH inp ≤ stdin_size ∧
   is_ag32_init_state (hello_init_memory r0 (cl,inp)) r0 ms0 ∧
   Abbrev(ms = FUNPOW Next (hello_startup_clock r0 ms0 inp cl) ms0)
  ⇒
   interference_implemented
    (hello_machine_config r0)
    (basis_ffi cl (stdin_fs inp)).oracle
    (ag32_ffi_rel r0)
    (ag32_ffi_mem_domain r0) ms`,
  rw[interference_implemented_def]
  \\ simp[EVAL``(hello_machine_config r0).target.next``]
  \\ simp[EVAL``(hello_machine_config r0).target.get_byte``]
  \\ simp[EVAL``(hello_machine_config r0).target.get_pc``]
  \\ simp[EVAL``(hello_machine_config r0).target.get_reg``]
  \\ simp[EVAL``(hello_machine_config r0).ffi_entry_pcs``]
  \\ simp[ffi_names]
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
    \\ `(Next ms1).io_events = ms1.io_events` suffices_by rw[]
    \\ irule ag32_io_events_unchanged
    \\ simp[Abbr`ms1`]
    \\ `aligned 2 pc` by rfs[ag32_targetTheory.ag32_target_def, ag32_targetTheory.ag32_ok_def, EVAL``(hello_machine_config r0).target.state_ok``]
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
    \\ fs[EVAL``(hello_machine_config r0).target.config.code_alignment``]
    \\ fs[EVAL``(hello_machine_config r0).target.config.encode``]
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
        \\ (alignmentTheory.aligned_add_sub_cor
            |> SPEC_ALL |> UNDISCH |> CONJUNCT1 |> DISCH_ALL
            |> irule)
        \\ fs[alignmentTheory.byte_aligned_def]
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
      \\ impl_tac
      >- (
        simp[Abbr`pc`]
        \\ EVAL_TAC \\ simp[ffi_names, LENGTH_code, LENGTH_data]
        \\ Cases_on`r0`
        \\ fs[word_add_n2w,word_ls_n2w,word_lo_n2w,memory_size_def] )
      \\ first_assum(qspec_then`pc + 1w`mp_tac)
      \\ impl_tac
      >- (
        simp[Abbr`pc`]
        \\ EVAL_TAC \\ simp[ffi_names, LENGTH_code, LENGTH_data]
        \\ Cases_on`r0`
        \\ fs[word_add_n2w,word_ls_n2w,word_lo_n2w,memory_size_def] )
      \\ first_assum(qspec_then`pc + 2w`mp_tac)
      \\ impl_tac
      >- (
        simp[Abbr`pc`]
        \\ EVAL_TAC \\ simp[ffi_names, LENGTH_code, LENGTH_data]
        \\ Cases_on`r0`
        \\ fs[word_add_n2w,word_ls_n2w,word_lo_n2w,memory_size_def] )
      \\ first_assum(qspec_then`pc + 3w`mp_tac)
      \\ impl_tac
      >- (
        simp[Abbr`pc`]
        \\ EVAL_TAC \\ simp[ffi_names, LENGTH_code, LENGTH_data]
        \\ Cases_on`r0`
        \\ fs[word_add_n2w,word_ls_n2w,word_lo_n2w,memory_size_def] )
      \\ simp[]
      \\ ntac 4 (disch_then kall_tac)
      \\ drule hello_startup_clock_def
      \\ simp[]
      \\ disch_then drule
      \\ disch_then drule
      \\ disch_then drule
      \\ strip_tac
      \\ first_assum(qspec_then`pc`mp_tac)
      \\ impl_tac
      >- (
        simp[Abbr`pc`]
        \\ EVAL_TAC
        \\ simp[ffi_names,LENGTH_code,LENGTH_data]
        \\ Cases_on`r0`
        \\ fs[word_add_n2w,word_ls_n2w,word_lo_n2w,memory_size_def] )
      \\ first_assum(qspec_then`pc + 1w`mp_tac)
      \\ impl_tac
      >- (
        simp[Abbr`pc`]
        \\ EVAL_TAC
        \\ simp[ffi_names,LENGTH_code,LENGTH_data]
        \\ Cases_on`r0`
        \\ fs[word_add_n2w,word_ls_n2w,word_lo_n2w,memory_size_def] )
      \\ first_assum(qspec_then`pc + 2w`mp_tac)
      \\ impl_tac
      >- (
        simp[Abbr`pc`]
        \\ EVAL_TAC
        \\ simp[ffi_names,LENGTH_code,LENGTH_data]
        \\ Cases_on`r0`
        \\ fs[word_add_n2w,word_ls_n2w,word_lo_n2w,memory_size_def] )
      \\ first_assum(qspec_then`pc + 3w`mp_tac)
      \\ impl_tac
      >- (
        simp[Abbr`pc`]
        \\ EVAL_TAC
        \\ simp[ffi_names,LENGTH_code,LENGTH_data]
        \\ Cases_on`r0`
        \\ fs[word_add_n2w,word_ls_n2w,word_lo_n2w,memory_size_def] )
      \\ simp[]
      \\ ntac 4 (disch_then kall_tac)
      \\ fs[is_ag32_init_state_def]
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
  \\ fs[EVAL``(hello_machine_config r0).ffi_names``, ffi_names]
  \\ fs[ffiTheory.call_FFI_def,CaseEq"oracle_result",CaseEq"bool"]
  \\ rveq \\ rfs[basis_ffiTheory.basis_ffi_def]
  \\ qhdtm_x_assum`basis_ffi_oracle`mp_tac
  \\ simp[Once basis_ffiTheory.basis_ffi_oracle_def]
  \\ pairarg_tac \\ rw[CaseEq"option",CaseEq"ffi_result"]
  \\ qmatch_goalsub_abbrev_tac`_ = FUNPOW Next _ ms1`
  \\ drule (GEN_ALL ag32_ffi_interfer_write)
  \\ fs[hello_machine_config_def]
  \\ disch_then drule
  \\ fs[GSYM hello_machine_config_def]
  \\ disch_then drule
  \\ simp[ffi_names, INDEX_OF_def, INDEX_FIND_def]
  \\ impl_tac >- (
    conj_tac >- EVAL_TAC
    \\ conj_tac >- ( simp[LENGTH_data, LENGTH_code] \\ EVAL_TAC )
    \\ conj_tac >- cheat (* invariant on fs - can this be added to ag32_ffi_rel maybe?
                            otherwise interference_implemented needs to be tweaked... *)
    \\ conj_tac >- (
      rw[]
      \\ first_assum(mp_then Any mp_tac (GEN_ALL get_mem_word_get_byte))
      \\ disch_then(first_assum o mp_then Any mp_tac)
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
          \\ Cases_on`r0` \\ fs[memory_size_def] )
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
        \\ simp[hello_init_memory_words_def]
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
      \\ simp[GSYM(SIMP_RULE(srw_ss())[]hello_init_memory_def)]
      \\ drule hello_startup_clock_def
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
          \\ Cases_on`x` \\ Cases_on`r0` \\ fs[memory_size_def, word_add_n2w]
          \\ fs[word_ls_n2w, word_lo_n2w] \\ rfs[] )
        \\ simp[ffi_names, LENGTH_code, LENGTH_data]
        \\ qpat_x_assum`_ = ms1.PC`(assume_tac o SYM)
        \\ EVAL_TAC \\ simp[]
        \\ Cases_on`x` \\ Cases_on`r0` \\ fs[memory_size_def, word_add_n2w]
        \\ fs[word_ls_n2w, word_lo_n2w] \\ rfs[]
        \\ fs[EVAL``ffi_jumps_offset``, EVAL``ag32_ffi_jumps [_]``]
        \\ rfs[])
      \\ rw[]
      \\ first_x_assum irule
      \\ EVAL_TAC
      \\ fs[EVAL``ffi_jumps_offset``, EVAL``ag32_ffi_jumps [_]``]
      \\ Cases_on`x` \\ Cases_on`ms0.PC` \\ fs[memory_size_def, word_add_n2w]
      \\ fs[word_ls_n2w, word_lo_n2w] \\ rfs[])
    \\ rw[]
    \\ first_assum(mp_then Any mp_tac (GEN_ALL get_mem_word_get_byte))
    \\ qmatch_goalsub_abbrev_tac`4 * k + off`
    \\ disch_then(qspecl_then[`off DIV 4`,`ms1.MEM`,`MAP Encode ag32_ffi_write_code`]mp_tac)
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
      \\ simp[hello_init_memory_words_def]
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
    \\ simp[GSYM(SIMP_RULE(srw_ss())[]hello_init_memory_def)]
    \\ drule hello_startup_clock_def
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
        \\ Cases_on`x` \\ Cases_on`r0` \\ fs[memory_size_def, word_add_n2w]
        \\ fs[word_ls_n2w, word_lo_n2w] \\ rfs[] )
      \\ simp[ffi_names, LENGTH_code, LENGTH_data]
      \\ qpat_x_assum`_ = ms1.PC`(assume_tac o SYM)
      \\ EVAL_TAC \\ simp[]
      \\ Cases_on`x` \\ Cases_on`r0` \\ fs[memory_size_def, word_add_n2w]
      \\ fs[word_ls_n2w, word_lo_n2w] \\ rfs[]
      \\ fs[EVAL``LENGTH ag32_ffi_write_code``]
      \\ rfs[])
    \\ rw[]
    \\ first_x_assum irule
    \\ EVAL_TAC
    \\ fs[EVAL``LENGTH ag32_ffi_write_code``]
    \\ Cases_on`x` \\ Cases_on`ms0.PC` \\ fs[memory_size_def, word_add_n2w]
    \\ fs[word_ls_n2w, word_lo_n2w] \\ rfs[])
  \\ strip_tac
  \\ asm_exists_tac
  \\ simp[]
  \\ gen_tac
  \\ Cases_on`x ∈ ag32_ffi_mem_domain r0` \\ fs[]
  \\ mp_tac(GEN_ALL ag32_ffi_mem_domain_DISJOINT_prog_addresses)
  \\ simp[FFI_codes_def, IN_DISJOINT, PULL_FORALL]
  \\ simp[hello_machine_config_def, ag32_machine_config_def, ffi_names]
  \\ simp[data_to_word_assignProofTheory.IMP, AND_IMP_INTRO]
  \\ strip_tac
  \\ `F` suffices_by rw[]
  \\ pop_assum mp_tac
  \\ simp[]
  \\ first_x_assum match_mp_tac
  \\ simp[]
  \\ EVAL_TAC
  \\ simp[LENGTH_code, LENGTH_data]);

val hello_extract_writes_stdout = Q.store_thm("hello_extract_writes_stdout",
  `wfcl cl ∧ 2 ≤ maxFD ⇒
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
  >- rw[]
  >- rw[]);

val hello_ag32_next = Q.store_thm("hello_ag32_next",
  `byte_aligned r0 ∧ w2n r0 + memory_size < dimword (:32) ∧
   SUM (MAP strlen cl) + LENGTH cl ≤ cline_size ∧ wfcl cl ∧
   LENGTH inp ≤ stdin_size ∧ 2 ≤ maxFD ∧
   is_ag32_init_state (hello_init_memory r0 (cl,inp)) r0 ms0
  ⇒
   ∃k1. ∀k. k1 ≤ k ⇒
     let ms = FUNPOW Next k ms0 in
     let outs = MAP (get_ag32_io_event r0) ms.io_events in
       (ms.PC = (hello_machine_config r0).halt_pc) ∧
       outs ≼ MAP get_output_io_event (hello_io_events cl (stdin_fs inp)) ∧
       ((ms.R (n2w (hello_machine_config r0).ptr_reg) = 0w) ⇒
        (outs = MAP get_output_io_event (hello_io_events cl (stdin_fs inp))))`,
  rw[]
  \\ drule (GEN_ALL hello_machine_sem)
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
  \\ drule hello_interference_implemented
  \\ impl_tac >- fs[markerTheory.Abbrev_def]
  \\ strip_tac \\ rfs[]
  \\ disch_then drule
  \\ impl_tac >- (
    simp[ag32_ffi_rel_def,Abbr`st`]
    \\ EVAL_TAC
    \\ simp[Abbr`ms`]
    \\ drule hello_startup_clock_def
    \\ simp[]
    \\ rpt(disch_then drule)
    \\ fs[is_ag32_init_state_def])
  \\ strip_tac
  \\ drule (GEN_ALL hello_halted)
  \\ simp[]
  \\ disch_then drule
  \\ disch_then drule
  \\ disch_then(qspec_then`FUNPOW Next k ms`mp_tac)
  \\ strip_tac
  \\ qexists_tac`k + hello_startup_clock r0 ms0 inp cl`
  \\ qx_gen_tac`k2` \\ strip_tac
  \\ first_x_assum(qspec_then`k2-k-(hello_startup_clock r0 ms0 inp cl)`mp_tac)
  \\ impl_tac
  >- (
    conj_tac
    >- (
      fs[Abbr`mc`]
      \\ fs[EVAL``(hello_machine_config r0).target.get_pc``]
      \\ fs[Abbr`ms`, FUNPOW_ADD]
      \\ fs[EVAL``(hello_machine_config r0).target.next``]
      \\ first_x_assum irule
      \\ fs[markerTheory.Abbrev_def] )
    \\ fs[Abbr`mc`]
    \\ fs[EVAL``(hello_machine_config r0).target.next``]
    \\ fs[Abbr`ms`, FUNPOW_ADD]
    \\ drule hello_startup_clock_def
    \\ disch_then(qspec_then`ms0`mp_tac)
    \\ disch_then(first_assum o mp_then Any mp_tac)
    \\ impl_tac >- fs[]
    \\ strip_tac
    \\ fs[EVAL``(hello_machine_config r0).target.get_byte``]
    \\ fs[ag32_targetTheory.is_ag32_init_state_def] \\ rfs[]
    \\ rw[]
    \\ qmatch_goalsub_rename_tac`_ = _ a`
    \\ `a ∉ ag32_startup_addresses ms0.PC`
    by (
      EVAL_TAC
      \\ ntac 2 (pop_assum mp_tac)
      \\ EVAL_TAC
      \\ simp[ffi_names]
      \\ Cases_on`a` \\ Cases_on`ms0.PC`
      \\ simp[word_add_n2w]
      \\ simp[word_ls_n2w, word_lo_n2w]
      \\ fs[memory_size_def] )
    \\ first_x_assum drule
    \\ disch_then(assume_tac o SYM) \\ simp[]
    \\ first_x_assum irule
    \\ Cases_on`ms0.PC` \\ Cases_on`a`
    \\ fs[word_add_n2w, hello_machine_config_halt_pc]
    \\ simp[hello_machine_config_def, ag32_machine_config_def, ffi_names, ag32_prog_addresses_def, LENGTH_code, LENGTH_data]
    \\ EVAL_TAC
    \\ fs[word_lo_n2w, word_ls_n2w, memory_size_def] \\ rfs[])
  \\ fs[GSYM FUNPOW_ADD, Abbr`ms`]
  \\ strip_tac
  \\ fs[EVAL``(hello_machine_config r0).target.next``,Abbr`mc`,FUNPOW_ADD]
  \\ fs[EVAL``(hello_machine_config r0).target.get_reg``]
  \\ fs[EVAL``(hello_machine_config r0).target.get_pc``]
  \\ fs[EVAL``(hello_machine_config r0).ptr_reg``]
  \\ fs[ag32_ffi_rel_def]
  \\ conj_tac
  >- ( fs[IS_PREFIX_APPEND] \\ fs[markerTheory.Abbrev_def] )
  \\ strip_tac \\ fs[]
  \\ Cases_on`x` \\ fs[]
  \\ fs[markerTheory.Abbrev_def]);

val _ = export_theory();
