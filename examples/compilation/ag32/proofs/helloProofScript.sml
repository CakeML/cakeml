open preamble
     semanticsPropsTheory backendProofTheory ag32_configProofTheory
     helloProgTheory helloCompileTheory

val _ = new_theory"helloProof";

(* TODO: move *)

val _ = temp_overload_on("nxt",
  ``λmc n ms. FUNPOW mc.target.next n ms``);

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
  `LENGTH (ag32_enc istr) ∈ {4;8;12}`,
  Cases_on`istr`
  \\ TRY(rename1`JumpCmp _ _ ri _` \\ Cases_on`ri`)
  \\ TRY(rename1`Inst i ` \\ Cases_on`i`)
  \\ TRY(rename1`Inst (Mem m _ ri) ` \\ Cases_on`m` \\ Cases_on`ri`)
  \\ TRY(rename1`Inst (Arith a) ` \\ Cases_on`a`)
  \\ TRY(rename1`Inst (Arith (Binop _ _ _ ri)) ` \\ Cases_on`ri`)
  \\  rw[ag32_targetTheory.ag32_enc_def,
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
        ag32_targetProofTheory.Decode_Encode]
  \\ Cases_on`k` \\ fs[arm_stepTheory.concat_bytes, ag32_targetProofTheory.Decode_Encode]
  \\ qmatch_asmsub_rename_tac`4 * SUC k < _`
  \\ Cases_on`k` \\ fs[arm_stepTheory.concat_bytes, ag32_targetProofTheory.Decode_Encode]
  \\ qmatch_asmsub_rename_tac`4 * SUC (SUC k) < _`
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
      \\ Cases_on`n''` \\ fs[] )
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

(*
val ag32_ffi_rel_def = Define`
  ag32_ffi_rel r0 ms io_events ⇔
    (EVERY (λm. w2n (m r0) ≤ print_string_max_length) ms.io_events) ∧
    (io_events =
     MAP (λout. IO_event "print" (MAP (n2w o ORD) out) [])
       (MAP (extract_print_from_mem r0) ms.io_events))`;

val ag32_ffi_rel_get_print_string = Q.store_thm("ag32_ffi_rel_get_print_string",
  `ag32_ffi_rel r0 ms io_events ⇒
   (io_events =
     MAP (λout. IO_event "print" (MAP (n2w o ORD) out) [])
       (MAP (λm. get_print_string (r0,m)) ms.io_events))`,
  rw[ag32_ffi_rel_def]
  \\ AP_TERM_TAC
  \\ simp[MAP_EQ_f]
  \\ fs[EVERY_MEM]
  \\ simp[extract_print_from_mem_get_print_string]);
*)

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
  startup_code_size = 216n`;

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
  | FFI call id       |  4 bytes
  +-------------------+
  | output buffer     |  output_buffer_size bytes (~2Kb)
  +-------------------+
  | output length     |  4 bytes
  +-------------------+
  | + stdin           |  stdin_size bytes (~5Mb)
  +-------------------+
  | + stdin length    |  4 bytes
  +-------------------+
  | stdin pointer     |  4 bytes
  +-------------------+
  | + cline args      |  cline_size bytes (~1024b)
  +-------------------+
  | + cline arg count |  4 bytes
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

val ffi_code_start_offset_def = Define`
  ffi_code_start_offset =
    startup_code_size + 4 + cline_size + 4 + 4 + stdin_size + 4 + output_buffer_size + 4`;

val length_ag32_ffi_code = Define`
  length_ag32_ffi_code = 232n`;

val heap_start_offset_def = Define`
  heap_start_offset =
    ffi_code_start_offset + length_ag32_ffi_code`;

val ffi_jumps_offset_def = Define`
  ffi_jumps_offset =
    heap_start_offset + heap_size`;

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
   length (= 2) is in r3
   pointer is in r4 *)

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
   r3 contains length (=2)
   r4 contains pointer to byte array with the arg index: [index % 256, index / 256]
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

(*
;("get_arg", 3n)
;("read", 4n)
;("write", 5n)
;("open_in", 6n)
;("open_out", 7n)
;("close", 8n)
*)

(* FFI jumps
  - get byte array (length,pointer)s in (len_reg,ptr_reg) and (len2_reg,ptr2_reg) (these are r1-r4)
  - get return address in link_reg (r0)
  - PC is mem_start + ffi_jumps_offset + ffi_offset * index
  conventions on return:
    r0 is the end of this ffi's code (i.e., entrypoint of the next ffi's code)
    r1-r6 are 0w (* TODO: this is not currently satisfied *)
    overflow and carry are false
*)

val ffi_entrypoints_def = Define`
  ffi_entrypoints = [
    ("exit", ag32_ffi_exit_entrypoint);
    ("get_arg_count", ag32_ffi_get_arg_count_entrypoint);
    ("get_arg_length", ag32_ffi_get_arg_length_entrypoint) (* TODO: ... *)]`;

val ffi_exitpcs_def = Define`
  ffi_exitpcs = [
    ("exit", ffi_code_start_offset + ag32_ffi_get_arg_count_entrypoint);
    ("get_arg_count", ffi_code_start_offset + ag32_ffi_get_arg_length_entrypoint);
    ("get_arg_length", heap_start_offset) (* TODO: ... *)
    ]`;

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

(*
(* algorithm (shallow embedding) for the FFI implementation *)

val hello_ag32_ffi_1_def = Define`
  hello_ag32_ffi_1 s =
    let s = incPC () (s with R := ((4w =+ w2w(((22 >< 0)(n2w (heap_size + 4 * LENGTH data + 12) :word32)):23 word)) s.R)) in
    let s = incPC () (s with R := ((4w =+ bit_field_insert 31 23 (((31 >< 23)(n2w (heap_size + 4 * LENGTH data + 12) :word32)):9 word)
                                                                    (s.R 4w)) s.R)) in
    let s = incPC () (s with R := ((3w =+ (s.R 3w) - (s.R 4w)) s.R)) in
    let s = incPC () (s with MEM := ((s.R 3w) =+ (w2w (s.R 2w))) s.MEM) in
    let s = incPC () (s with <|
          R := ((2w =+ (s.R 3w) + (s.R 2w)) s.R)
        ; OverflowFlag := (w2i (s.R 3w + s.R 2w) ≠ w2i (s.R 3w) + w2i (s.R 2w)) |>) in
    s`;

val hello_ag32_ffi_2_def = tDefine"hello_ag32_ffi_2"`
  hello_ag32_ffi_2 s =
    if (s.R 3w) = (s.R 2w)
    then s with PC := s.PC + (4w * 6w)
    else
    let s = incPC () (incPC () (s with R := ((3w =+ (s.R 3w) + 1w) s.R))) in
    let s = incPC () (s with R := ((4w =+ w2w (s.MEM (s.R 1w))) s.R)) in
    let s = incPC () (s with MEM := (((s.R 3w) =+ w2w (s.R 4w)) s.MEM)) in
    let s = incPC () (s with R := ((1w =+ (s.R 1w) + 1w) s.R)) in
    hello_ag32_ffi_2 (s with PC := s.PC + (4w * -5w))`
  (simp[APPLY_UPDATE_THM,ag32Theory.incPC_def]
   \\ wf_rel_tac`measure (λs. w2n(s.R 2w - s.R 3w ))`
   \\ simp[APPLY_UPDATE_THM]
   \\ rw[]
   \\ Cases_on`s.R 3w`
   \\ Cases_on`s.R 2w`
   \\ fs[WORD_LEFT_ADD_DISTRIB]
   \\ rewrite_tac[WORD_ADD_ASSOC]
   \\ irule(SIMP_RULE(srw_ss())[]WORD_PRED_THM)
   \\ fs[]
   \\ fs[word_add_n2w]
   \\ rewrite_tac[WORD_SUM_ZERO, WORD_SUB_INTRO, WORD_EQ_NEG]
   \\ simp[]);

val hello_ag32_ffi_2_ind = theorem"hello_ag32_ffi_2_ind";

val hello_ag32_ffi_3_def = Define`
  hello_ag32_ffi_3 s =
    let s = incPC () (s with R := ((1w =+ 0w) s.R)) in
    let s = incPC () (s with R := ((2w =+ 0w) s.R)) in
    let s = incPC () (s with R := ((3w =+ 0w) s.R)) in
    let s = incPC () (s with R := ((4w =+ 0w) s.R)) in
    let s = incPC () (s with io_events := s.io_events ++ [s.MEM]) in
    s with <| PC := s.R 0w; R := ((0w =+ s.PC + 4w) s.R) |>`;

val hello_ag32_ffi_def = Define`
  hello_ag32_ffi s =
    hello_ag32_ffi_3 (hello_ag32_ffi_2 (hello_ag32_ffi_1 s))`;

val hello_ag32_ffi_1_spec = Q.store_thm("hello_ag32_ffi_1_spec",
  `(s.R 3w = r0 + n2w (heap_size + 4 * LENGTH data + 12)) ∧
   (s.R 2w = len)
   ⇒
   (hello_ag32_ffi_1 s =
    s with <| R := ((3w =+ r0) ((4w =+ n2w (heap_size + 4 * LENGTH data + 12)) ((2w =+ r0 + len) s.R)))
            ; PC := s.PC + 20w
            ; MEM := ((r0 =+ (w2w len)) s.MEM)
            ; OverflowFlag := (w2i (r0 + len) ≠ w2i r0 + w2i len)
            |>)`,
  rw[hello_ag32_ffi_1_def, ag32Theory.incPC_def]
  \\ simp[ag32Theory.ag32_state_component_equality, APPLY_UPDATE_THM, FUN_EQ_THM]
  \\ simp[LENGTH_data,heap_size_def]
  \\ rw[] \\ fs[]);

val hello_ag32_ffi_2_spec = Q.store_thm("hello_ag32_ffi_2_spec",
  `∀s i bs.
   (s.R 3w = r0 + i) ∧
   (s.R 2w = r0 + i + n2w (LENGTH bs)) ∧
   (s.R 1w = ptr + i) ∧
   (∀w. r0 + i <=+ w ∧ w <+ r0 + i + n2w (LENGTH bs) ⇒ w ∉ dm) ∧
   bytes_in_memory (ptr + i) bs s.MEM dm ∧
   w2n ptr + w2n i + LENGTH bs < dimword(:32) ∧
   w2n r0 + w2n i + 1 + LENGTH bs < dimword(:32)
   ⇒
   (∃r4.
    (hello_ag32_ffi_2 s =
     s with <| PC := s.PC + (4w * 6w)
             ; R  := ((1w =+ ptr + i + n2w (LENGTH bs))
                      ((3w =+ r0 + i + n2w (LENGTH bs))
                       ((4w =+ r4) s.R)))
             ; MEM := asm_write_bytearray (r0 + 1w + i) bs s.MEM
             |>))`,
  Induct_on`bs`
  >- (
    rw[lab_to_targetProofTheory.asm_write_bytearray_def]
    \\ simp[Once hello_ag32_ffi_2_def]
    \\ simp[ag32Theory.ag32_state_component_equality, FUN_EQ_THM, APPLY_UPDATE_THM]
    \\ qexists_tac`s.R 4w`
    \\ rw[] \\ rw[] )
  \\ rw[]
  \\ simp[Once hello_ag32_ffi_2_def]
  \\ IF_CASES_TAC
  >- (
    fs[]
    \\ Cases_on`i` \\ Cases_on`r0` \\ fs[word_add_n2w,ADD1]
    \\ qpat_x_assum`_ _  < _`assume_tac \\ fs[] )
  \\ simp[ag32Theory.incPC_def]
  \\ qmatch_goalsub_abbrev_tac`hello_ag32_ffi_2 s1`
  \\ first_x_assum(qspec_then`s1`mp_tac)
  \\ simp[Abbr`s1`, APPLY_UPDATE_THM]
  \\ disch_then(qspec_then`i + 1w`mp_tac)
  \\ impl_tac
  >- (
    fs[ADD1, GSYM word_add_n2w]
    \\ conj_tac
    >- (
      rw[]
      \\ first_x_assum match_mp_tac
      \\ fs[]
      \\ Cases_on`w`
      \\ Cases_on`i` \\ Cases_on`r0`
      \\ fs[word_add_n2w,word_ls_n2w]
      \\ rfs[] )
    \\ reverse conj_tac
    >- ( Cases_on`i` \\ Cases_on`r0` \\ fs[word_add_n2w] )
    \\ fs[asmSemTheory.bytes_in_memory_def]
    \\ irule asmPropsTheory.bytes_in_memory_change_mem
    \\ goal_assum(first_assum o mp_then Any mp_tac)
    \\ simp[APPLY_UPDATE_THM]
    \\ rw[] \\ fs[]
    \\ Cases_on`i` \\ fs[]
    \\ Cases_on`r0` \\ fs[]
    \\ Cases_on`ptr` \\ fs[word_lo_n2w, word_add_n2w,word_ls_n2w]
    \\ rfs[]
    \\ rpt(qpat_x_assum`_ _  < _`mp_tac)
    \\ strip_tac
    \\ strip_tac
    \\ fs[] \\ rw[]
    \\ `F` suffices_by fs[]
    \\ imp_res_tac asmPropsTheory.bytes_in_memory_all_pcs
    \\ pop_assum mp_tac
    \\ simp[asmPropsTheory.all_pcs_thm,SUBSET_DEF,PULL_EXISTS]
    \\ qexists_tac`0` \\ simp[]
    \\ qexists_tac`n` \\ simp[]
    \\ first_x_assum match_mp_tac
    \\ simp[word_add_n2w,word_ls_n2w,word_lo_n2w]
    \\ rfs[])
  \\ strip_tac
  \\ qexists_tac`r4`
  \\ qmatch_asmsub_abbrev_tac`hello_ag32_ffi_2 s1`
  \\ qmatch_goalsub_abbrev_tac`hello_ag32_ffi_2 s2`
  \\ `s1 = s2` by simp[Abbr`s1`,Abbr`s2`]
  \\ qunabbrev_tac`s1` \\ qunabbrev_tac`s2` \\ fs[]
  \\ simp[ag32Theory.ag32_state_component_equality]
  \\ simp[lab_to_targetProofTheory.asm_write_bytearray_def]
  \\ simp[APPLY_UPDATE_THM,FUN_EQ_THM,ADD1,GSYM word_add_n2w]
  \\ reverse(rw[])
  >- (
    match_mp_tac mem_eq_imp_asm_write_bytearray_eq
    \\ simp[APPLY_UPDATE_THM] )
  \\ fs[asmSemTheory.bytes_in_memory_def]
  \\ irule asm_write_bytearray_unchanged
  \\ simp[APPLY_UPDATE_THM]
  \\ Cases_on`i` \\ Cases_on`r0`
  \\ fs[word_add_n2w,word_ls_n2w,word_lo_n2w]
  \\ simp[w2w_w2w]
  \\ irule (GSYM WORD_ALL_BITS)
  \\ simp[]);

val hello_ag32_ffi_3_spec = Q.store_thm("hello_ag32_ffi_3_spec",
  `hello_ag32_ffi_3 s =
     s with <|
       R := (0w =+ s.PC + (4w * 6w)) ((4w =+ 0w) ((3w =+ 0w) ((2w =+ 0w) ((1w =+ 0w) s.R)))) ;
       PC := s.R 0w ;
       io_events := s.io_events ++ [s.MEM]
       |>`,
  rw[hello_ag32_ffi_3_def,ag32Theory.incPC_def]
  \\ rw[ag32Theory.ag32_state_component_equality,APPLY_UPDATE_THM]);

val hello_ag32_ffi_spec = Q.store_thm("hello_ag32_ffi_spec",
  `(s.R 3w = r0 + n2w (heap_size + 4 * LENGTH data + 12)) ∧
   (s.R 2w = n2w (LENGTH bs)) ∧
   (s.R 1w = ptr) ∧
   (∀w. r0 <=+ w ∧ w <+ r0 + n2w (LENGTH bs + 1) ⇒ w ∉ dm) ∧
   bytes_in_memory ptr bs s.MEM dm ∧
   w2n ptr + LENGTH bs < dimword(:32) ∧
   w2n r0 + LENGTH bs + 1 < dimword(:32)
   ⇒
   (hello_ag32_ffi s =
    s with <| R := ((0w =+ s.PC + 68w)
                    ((1w =+ 0w)
                    ((2w =+ 0w)
                    ((3w =+ 0w)
                    ((4w =+ 0w) s.R)))));
              MEM := asm_write_bytearray r0 ((n2w(LENGTH bs))::bs) s.MEM ;
              PC := s.R 0w;
              io_events := s.io_events ++ [(asm_write_bytearray r0 ((n2w(LENGTH bs))::bs) s.MEM)] ;
              OverflowFlag := (w2i (r0 + n2w (LENGTH bs)) ≠ w2i r0 + w2i ((n2w (LENGTH bs)):word32))
              |>)`,
  strip_tac
  \\ simp[hello_ag32_ffi_def]
  \\ drule (GEN_ALL hello_ag32_ffi_1_spec)
  \\ disch_then drule
  \\ disch_then SUBST_ALL_TAC
  \\ qmatch_goalsub_abbrev_tac`hello_ag32_ffi_2 s2`
  \\ qspecl_then[`s2`,`0w`,`bs`]mp_tac hello_ag32_ffi_2_spec
  \\ impl_tac >- (
    simp[Abbr`s2`,APPLY_UPDATE_THM] \\ fs[]
    \\ conj_tac >- (
      rw[]
      \\ first_x_assum match_mp_tac \\ fs[]
      \\ Cases_on`w` \\ Cases_on`r0`
      \\ fs[word_add_n2w,word_lo_n2w] \\ rfs[] )
    \\ irule asmPropsTheory.bytes_in_memory_change_mem
    \\ goal_assum(first_assum o mp_then Any mp_tac)
    \\ simp[APPLY_UPDATE_THM] \\ rw[]
    \\ Cases_on`s.R 1w` \\ fs[word_add_n2w]
    \\ qpat_x_assum`_ + LENGTH _ < _`assume_tac
    \\ fs[]
    \\ imp_res_tac asmPropsTheory.bytes_in_memory_all_pcs
    \\ first_x_assum(qspec_then`0`mp_tac)
    \\ simp[asmPropsTheory.all_pcs_thm,SUBSET_DEF,PULL_EXISTS]
    \\ disch_then drule
    \\ rw[word_add_n2w]
    \\ `F` suffices_by fs[]
    \\ pop_assum mp_tac \\ simp[]
    \\ first_x_assum match_mp_tac
    \\ simp[word_add_n2w, word_lo_n2w, word_ls_n2w])
  \\ disch_then(CHOOSE_THEN SUBST_ALL_TAC)
  \\ simp[hello_ag32_ffi_3_spec]
  \\ simp[Abbr`s2`,ag32Theory.ag32_state_component_equality,
          APPLY_UPDATE_THM,FUN_EQ_THM]
  \\ conj_asm1_tac
  >- (
    rw[]
    \\ simp[lab_to_targetProofTheory.asm_write_bytearray_def,APPLY_UPDATE_THM]
    \\ Cases_on`r0 + 1w <=+ x ∧ x <+ r0 + 1w + n2w (LENGTH bs)`
    >- (
      rw[]
      >- ( Cases_on`r0` \\ fs[word_add_n2w, word_ls_n2w,word_lo_n2w] \\ rfs[] )
      \\ Cases_on`r0` \\ Cases_on`x` \\ fs[word_add_n2w,word_ls_n2w,word_lo_n2w] \\ rfs[]
      \\ qmatch_goalsub_rename_tac`_ _ _ s.MEM (n2w m)`
      \\ Cases_on `m` \\ fs[ADD1]
      \\ qmatch_goalsub_rename_tac`_ _ _ s.MEM (n2w (m+1))`
      \\ `∃p. ((n2w (m+1):word32) = n2w (n+1) + n2w p) ∧ p < LENGTH bs` by (
        fs[LESS_EQ_EXISTS] \\ fs[word_add_n2w]
        \\ qexists_tac`p` \\ simp[]
        \\ rveq \\ fs[])
      \\ first_assum SUBST_ALL_TAC
      \\ DEP_REWRITE_TAC[asm_write_bytearray_EL]
      \\ simp[] )
    \\ DEP_REWRITE_TAC[SIMP_RULE std_ss [] asm_write_bytearray_unchanged]
    \\ rw[APPLY_UPDATE_THM, w2w_n2w]
    \\ Cases_on`x` \\ Cases_on`r0`
    \\ fs[word_add_n2w,word_ls_n2w,word_lo_n2w] \\ rfs[] )
  \\ rw[]);

(*
    on entering real FFI code:
      r0 = return address
      r1 = pointer to string
      r2 = length of string
      r3 = mem_start + heap_size + 4 * LENGTH data + 12
      r4 = (temporary)
    r4 <- heap_size + 4 * LENGTH data + 12
    r3 <- r3 - r4                                (* r3 is now mem_start *)
    m[r3] <- r2                                  (* write the length *)
    r2 <- r3 + r2                                (* r2 is now address to stop writing at *)
    jump forward 6 if r2 = r3
    r3 <- r3 + 1                                 (* increment target pointer *)
    r4 <- m[r1]
    m[r3] <- r4                                  (* (r2 - r3)'th char of string written *)
    r1 <- r1 + 1                                 (* increment string pointer *)
    jump back 5
    r1 <- 0w (* reset registers to    *)
    r2 <- 0w (* avoid having to       *)
    r3 <- 0w (* specify their values  *)
    r4 <- 0w (* in the io_regs oracle *)
    Interrupt
    jump to r0
      on exit:
      r0 = mem_start + heap_size + 4 * LENGTH data + 48 + LENGTH code + 4 * LENGTH hello_ag32_ffi_code
      r1 ... r4 = 0w
*)
val hello_ag32_ffi_code_def = Define`
  hello_ag32_ffi_code =
    [LoadConstant(4w, F, (22 >< 0)((n2w (heap_size + 4 * LENGTH data + 12)):word32))
    ;LoadUpperConstant(4w, (31 >< 23)((n2w (heap_size + 4 * LENGTH data + 12)):word32))
    ;Normal(fSub, 3w, Reg 3w, Reg 4w)
    ;StoreMEMByte(Reg 2w, Reg 3w)
    ;Normal(fAdd, 2w, Reg 2w, Reg 3w)
    ;JumpIfNotZero(fEqual, Imm (4w * 6w), Reg 2w, Reg 3w)
    ;Normal(fInc, 3w, Reg 3w, Imm 0w)
    ;LoadMEMByte(4w, Reg 1w)
    ;StoreMEMByte(Reg 4w, Reg 3w)
    ;Normal(fInc, 1w, Reg 1w, Imm 0w)
    ;JumpIfZero(fSnd, Imm (4w * -5w), Imm 0w, Imm 0w)
    ;Normal(fSnd, 1w, Imm 0w, Imm 0w)
    ;Normal(fSnd, 2w, Imm 0w, Imm 0w)
    ;Normal(fSnd, 3w, Imm 0w, Imm 0w)
    ;Normal(fSnd, 4w, Imm 0w, Imm 0w)
    ;Interrupt
    ;Jump(fSnd, 0w, Reg 0w)]`;

val LENGTH_hello_ag32_ffi_code =
  ``LENGTH hello_ag32_ffi_code``
  |> SIMP_CONV (srw_ss()) [hello_ag32_ffi_code_def]

*)

val ag32_ffi_code_def = Define`
  ag32_ffi_code =
    MAP Encode (
      ag32_ffi_exit_code ++
      ag32_ffi_get_arg_count_code ++
      ag32_ffi_get_arg_length_code (* TODO ++ the rest *) )`;

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
  gen_tac
  \\ qspec_then`i`mp_tac (Q.GEN`istr`ag32_enc_lengths)
  \\ rw[LENGTH_startup_asm_code, startup_code_size_def]);

val ag32_prog_addresses = Define`
  ag32_prog_addresses num_ffis LENGTH_code LENGTH_data r0 =
      { w | r0 <=+ w ∧ w <+ r0 + n2w startup_code_size } ∪
      { w | r0 + n2w heap_start_offset <=+ w ∧ w <+ r0 + n2w (heap_start_offset + heap_size) } ∪
      { w | r0 + n2w (code_start_offset num_ffis) <=+ w ∧
            w <+ r0 + n2w (code_start_offset num_ffis + LENGTH_code + 4 * LENGTH_data) } `;

val ag32_ccache_interfer_def = Define`
  ag32_ccache_interfer num_ffis r0 (_,_,ms) =
    ms with <| PC := (ms.R 0w) ;
               R := (0w =+ r0 + n2w(ffi_code_start_offset + num_ffis * ffi_offset + 4)) ms.R |>`;

val ag32_ffi_interfer_def = Define`
  ag32_ffi_interfer ffi_names r0 (index,new_bytes,ms) =
    let name = EL index ffi_names in
    let new_mem = (r0 =+ n2w (THE (ALOOKUP FFI_codes name))) ms.MEM in
    let new_mem = asm_write_bytearray (ms.R 4w) new_bytes new_mem in
    let exitpc = THE (ALOOKUP ffi_exitpcs name) in
        ms with
          <| PC := (ms.R 0w) ;
             R := ((0w =+ r0 + n2w exitpc)
                   ((1w =+ 0w)
                   ((2w =+ 0w)
                   ((3w =+ 0w)
                   ((4w =+ 0w)
                   ((5w =+ 0w)
                   ((6w =+ 0w) (ms.R)))))))) ;
             CarryFlag := F ;
             OverflowFlag := F ;
             io_events := ms.io_events ++ [new_mem] ;
             MEM := new_mem |>`;

val ag32_machine_config_def = Define`
  ag32_machine_config ffi_names LENGTH_code LENGTH_data r0 =
  let num_ffis = LENGTH ffi_names in
  <|
    target := ag32_target;
    ptr_reg := 1;
    len_reg := 2;
    ptr2_reg := 3;
    len2_reg := 4;
    callee_saved_regs := [60; 61; 62];
    ffi_names := ffi_names ;
    ffi_entry_pcs := GENLIST (λi. r0 + n2w (ffi_code_start_offset + i * ffi_offset)) num_ffis;
    ccache_pc     := r0 + n2w (ffi_code_start_offset + (num_ffis + 0) * ffi_offset);
    halt_pc       := r0 + n2w (ffi_code_start_offset + (num_ffis + 1) * ffi_offset);
    prog_addresses := ag32_prog_addresses num_ffis LENGTH_code LENGTH_data r0 ;
    next_interfer := K I ;
    ccache_interfer := K (ag32_ccache_interfer num_ffis r0) ;
    ffi_interfer := K (ag32_ffi_interfer ffi_names r0)
  |>`

val is_ag32_machine_config_ag32_machine_config = Q.store_thm("is_ag32_machine_config_ag32_machine_config",
  `is_ag32_machine_config (ag32_machine_config a b c r0)`, EVAL_TAC);

(* -- *)

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
  hello_init_memory_words args stdin =
    words_of_bytes F hello_startup_code ++
    REPLICATE ((startup_code_size - LENGTH hello_startup_code) DIV 4) 0w ++
    [n2w (LENGTH args)] ++
    words_of_bytes F (PAD_RIGHT 0w cline_size (FLAT (MAP (SNOC 0w) (MAP (MAP (n2w o ORD) o explode) args)))) ++
    [0w] ++
    [n2w (LENGTH stdin)] ++
    words_of_bytes F (PAD_RIGHT 0w stdin_size (MAP (n2w o ORD) stdin)) ++
    REPLICATE ((4 + output_buffer_size + 4) DIV 4) 0w ++
    ag32_ffi_code ++
    REPLICATE (heap_size DIV 4) 0w ++
    ag32_ffi_jumps (THE config.ffi_names) ++
    words_of_bytes F code ++
    data (* ++ padding of 0w out to memory_size: not included here *)
    `;

val hello_init_memory_def = Define`
  hello_init_memory r0 (args, stdin) (k:word32) =
     get_byte k (EL (w2n (byte_align k - r0) DIV 4) (hello_init_memory_words args stdin)) F`;

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

(*
val hello_init_memory_ccache = Q.store_thm("hello_init_memory_ccache",
  `byte_aligned r0 ∧
   (pc = r0 + n2w (heap_size + 4 * LENGTH data + ffi_offset))
  ⇒
   ((hello_init_memory r0 (pc + 3w) @@
    ((hello_init_memory r0 (pc + 2w) @@
      ((hello_init_memory r0 (pc + 1w) @@
        hello_init_memory r0 (pc)) : word16)) : word24)) =
    Encode (Jump (fSnd, 0w, Reg 0w)))`,
  strip_tac
  \\ pop_assum(assume_tac o ONCE_REWRITE_RULE[GSYM markerTheory.Abbrev_def])
  \\ simp[hello_init_memory_def]
  \\ fs[alignmentTheory.byte_aligned_def, alignmentTheory.byte_align_def]
  \\ `aligned 2 pc`
  by (
    simp[Abbr`pc`, LENGTH_data]
    \\ (alignmentTheory.aligned_add_sub_cor
        |> SPEC_ALL |> UNDISCH |> CONJUNCT1 |> DISCH_ALL
        |> irule)
    \\ simp[]
    \\ EVAL_TAC )
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
  \\ `∃l1 l2. (hello_init_memory_words = l1 ++ l2) ∧
              (LENGTH l1 = w2n x DIV 4) ∧
              (l2 <> [] ∧ (HD l2 = h))` by (
    simp[hello_init_memory_words_def]
    \\ qmatch_goalsub_abbrev_tac`l1 ++ (j::l2)`
    \\ qexists_tac`l1 ++ TAKE 4 (j::l2)`
    \\ simp[Abbr`l1`,Abbr`j`,Abbr`l2`]
    \\ simp[Abbr`x`,LENGTH_data,LENGTH_hello_startup_code,LENGTH_words_of_bytes_hello_startup_code]
    \\ EVAL_TAC )
  \\ simp[EL_APPEND_EQN]
  \\ EVAL_TAC \\ simp[]
  \\ blastLib.BBLAST_TAC );

val hello_init_memory_halt = Q.store_thm("hello_init_memory_halt",
  `byte_aligned r0 ∧
   (pc = r0 + n2w (heap_size + 4 * LENGTH data + 2 * ffi_offset))
  ⇒
   ((hello_init_memory r0 (pc + 3w) @@
    ((hello_init_memory r0 (pc + 2w) @@
      ((hello_init_memory r0 (pc + 1w) @@
        hello_init_memory r0 (pc)) : word16)) : word24)) =
    Encode (Jump (fAdd, 0w, Imm 0w)))`,
  strip_tac
  \\ pop_assum(assume_tac o ONCE_REWRITE_RULE[GSYM markerTheory.Abbrev_def])
  \\ simp[hello_init_memory_def]
  \\ fs[alignmentTheory.byte_aligned_def, alignmentTheory.byte_align_def]
  \\ `aligned 2 pc`
  by (
    simp[Abbr`pc`, LENGTH_data]
    \\ (alignmentTheory.aligned_add_sub_cor
        |> SPEC_ALL |> UNDISCH |> CONJUNCT1 |> DISCH_ALL
        |> irule)
    \\ simp[]
    \\ EVAL_TAC )
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
  \\ `∃l1 l2. (hello_init_memory_words = l1 ++ l2) ∧
              (LENGTH l1 = w2n x DIV 4) ∧
              (l2 <> [] ∧ (HD l2 = h))` by (
    simp[hello_init_memory_words_def]
    \\ qmatch_goalsub_abbrev_tac`l1 ++ (j::l2)`
    \\ qexists_tac`l1 ++ TAKE 8 (j::l2)`
    \\ simp[Abbr`l1`,Abbr`j`,Abbr`l2`]
    \\ simp[Abbr`x`,LENGTH_data,LENGTH_hello_startup_code,LENGTH_words_of_bytes_hello_startup_code]
    \\ EVAL_TAC )
  \\ simp[EL_APPEND_EQN]
  \\ EVAL_TAC \\ simp[]
  \\ blastLib.BBLAST_TAC );

val hello_init_memory_ffi_00 = Q.store_thm("hello_init_memory_ffi_00",
  `byte_aligned r0 ∧
   (pc = r0 + n2w (heap_size + 4 * LENGTH data))
  ⇒
   ((hello_init_memory r0 (pc + 3w) @@
    ((hello_init_memory r0 (pc + 2w) @@
      ((hello_init_memory r0 (pc + 1w) @@
        hello_init_memory r0 (pc)) : word16)) : word24)) =
    Encode (LoadConstant (3w, F, (n2w (40 + LENGTH code)))))`,
  strip_tac
  \\ pop_assum(assume_tac o ONCE_REWRITE_RULE[GSYM markerTheory.Abbrev_def])
  \\ simp[hello_init_memory_def]
  \\ fs[alignmentTheory.byte_aligned_def, alignmentTheory.byte_align_def]
  \\ `aligned 2 pc`
  by (
    simp[Abbr`pc`, LENGTH_data]
    \\ (alignmentTheory.aligned_add_sub_cor
        |> SPEC_ALL |> UNDISCH |> CONJUNCT1 |> DISCH_ALL
        |> irule)
    \\ simp[]
    \\ EVAL_TAC )
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
  \\ `∃l1 l2. (hello_init_memory_words = l1 ++ l2) ∧
              (LENGTH l1 = w2n x DIV 4) ∧
              (l2 <> [] ∧ (HD l2 = h))` by (
    simp[hello_init_memory_words_def]
    \\ qmatch_goalsub_abbrev_tac`l1 ++ (h::l2)`
    \\ qexists_tac`l1`
    \\ simp[Abbr`l1`,Abbr`l2`]
    \\ simp[Abbr`x`,LENGTH_data,LENGTH_hello_startup_code,LENGTH_words_of_bytes_hello_startup_code]
    \\ EVAL_TAC )
  \\ simp[EL_APPEND_EQN]
  \\ EVAL_TAC \\ simp[]
  \\ blastLib.BBLAST_TAC );

val hello_init_memory_ffi_01 = Q.store_thm("hello_init_memory_ffi_01",
  `byte_aligned r0 ∧
   (pc = r0 + n2w (heap_size + 4 * LENGTH data + 4))
  ⇒
   ((hello_init_memory r0 (pc + 3w) @@
    ((hello_init_memory r0 (pc + 2w) @@
      ((hello_init_memory r0 (pc + 1w) @@
        hello_init_memory r0 (pc)) : word16)) : word24)) =
    Encode (Normal (fAdd, 4w, Imm 0w, Imm 0w)))`,
  strip_tac
  \\ pop_assum(assume_tac o ONCE_REWRITE_RULE[GSYM markerTheory.Abbrev_def])
  \\ simp[hello_init_memory_def]
  \\ fs[alignmentTheory.byte_aligned_def, alignmentTheory.byte_align_def]
  \\ `aligned 2 pc`
  by (
    simp[Abbr`pc`, LENGTH_data]
    \\ (alignmentTheory.aligned_add_sub_cor
        |> SPEC_ALL |> UNDISCH |> CONJUNCT1 |> DISCH_ALL
        |> irule)
    \\ simp[]
    \\ EVAL_TAC )
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
  \\ `∃l1 l2. (hello_init_memory_words = l1 ++ l2) ∧
              (LENGTH l1 = w2n x DIV 4) ∧
              (l2 <> [] ∧ (HD l2 = h))` by (
    simp[hello_init_memory_words_def]
    \\ qmatch_goalsub_abbrev_tac`l1 ++ (j::l2)`
    \\ qexists_tac`l1 ++ [j]`
    \\ simp[Abbr`l1`,Abbr`l2`]
    \\ simp[Abbr`x`,LENGTH_data,LENGTH_hello_startup_code,LENGTH_words_of_bytes_hello_startup_code]
    \\ EVAL_TAC )
  \\ simp[EL_APPEND_EQN]
  \\ EVAL_TAC \\ simp[]
  \\ blastLib.BBLAST_TAC );

val hello_init_memory_ffi_02 = Q.store_thm("hello_init_memory_ffi_02",
  `byte_aligned r0 ∧
   (pc = r0 + n2w (heap_size + 4 * LENGTH data + 8))
  ⇒
   ((hello_init_memory r0 (pc + 3w) @@
    ((hello_init_memory r0 (pc + 2w) @@
      ((hello_init_memory r0 (pc + 1w) @@
        hello_init_memory r0 (pc)) : word16)) : word24)) =
    Encode (Jump (fAddWithCarry, 3w, Reg 3w)))`,
  strip_tac
  \\ pop_assum(assume_tac o ONCE_REWRITE_RULE[GSYM markerTheory.Abbrev_def])
  \\ simp[hello_init_memory_def]
  \\ fs[alignmentTheory.byte_aligned_def, alignmentTheory.byte_align_def]
  \\ `aligned 2 pc`
  by (
    simp[Abbr`pc`, LENGTH_data]
    \\ (alignmentTheory.aligned_add_sub_cor
        |> SPEC_ALL |> UNDISCH |> CONJUNCT1 |> DISCH_ALL
        |> irule)
    \\ simp[]
    \\ EVAL_TAC )
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
  \\ `∃l1 l2. (hello_init_memory_words = l1 ++ l2) ∧
              (LENGTH l1 = w2n x DIV 4) ∧
              (l2 <> [] ∧ (HD l2 = h))` by (
    simp[hello_init_memory_words_def]
    \\ qmatch_goalsub_abbrev_tac`l1 ++ (j::l2)`
    \\ qexists_tac`l1 ++ (TAKE 2 (j::l2))`
    \\ simp[Abbr`l1`,Abbr`j`,Abbr`l2`]
    \\ simp[Abbr`x`,LENGTH_data,LENGTH_hello_startup_code,LENGTH_words_of_bytes_hello_startup_code]
    \\ EVAL_TAC )
  \\ simp[EL_APPEND_EQN]
  \\ EVAL_TAC \\ simp[]
  \\ blastLib.BBLAST_TAC );

val hello_init_memory_ffi = Q.store_thm("hello_init_memory_ffi",
  `byte_aligned r0 ∧ k < LENGTH hello_ag32_ffi_code ∧
   (n = heap_size + 4 * LENGTH data + 3 * ffi_offset + LENGTH code) ⇒
   ((hello_init_memory r0 (r0 + n2w (4 * k + n + 3)) @@
    ((hello_init_memory r0 (r0 + n2w (4 * k + n + 2)) @@
     ((hello_init_memory r0 (r0 + n2w (4 * k + n + 1)) @@
       hello_init_memory r0 (r0 + n2w (4 * k + n))) : word16)) :word24))
   =
    Encode (EL k hello_ag32_ffi_code))`,
  strip_tac
  \\ pop_assum(assume_tac o ONCE_REWRITE_RULE[GSYM markerTheory.Abbrev_def])
  \\ simp[hello_init_memory_def]
  \\ fs[alignmentTheory.byte_aligned_def, alignmentTheory.byte_align_def]
  \\ simp[align_add_aligned_gen]
  \\ `aligned 2 ((n2w (4 * k)):word32)` by (
    rw[GSYM ALIGNED_eq_aligned, addressTheory.ALIGNED_n2w] )
  \\ simp[align_add_aligned_gen, GSYM word_add_n2w]
  \\ qmatch_goalsub_abbrev_tac`pc + 3w`
  \\ `byte_aligned pc`
  by (
    simp[Abbr`pc`]
    \\ DEP_REWRITE_TAC[byte_aligned_add]
    \\ fs[alignmentTheory.byte_aligned_def]
    \\ simp[Abbr`n`,LENGTH_data,LENGTH_code]
    \\ EVAL_TAC )
  \\ fs[byte_align_aligned]
  \\ pop_assum(SUBST1_TAC o SYM)
  \\ once_rewrite_tac[WORD_ADD_COMM]
  \\ DEP_REWRITE_TAC[data_to_word_memoryProofTheory.get_byte_byte_align]
  \\ conj_tac >- EVAL_TAC
  \\ DEP_REWRITE_TAC[
       data_to_word_memoryProofTheory.get_byte_byte_align
       |> Q.GEN`a'` |> Q.SPEC`0w` |> SIMP_RULE(srw_ss())[]]
  \\ conj_tac >- EVAL_TAC
  \\ once_rewrite_tac[word_add_n2w]
  \\ once_rewrite_tac[WORD_ADD_COMM]
  \\ DEP_REWRITE_TAC[align_add_aligned_gen]
  \\ conj_asm1_tac
  >- (
    simp[GSYM word_add_n2w]
    \\ (alignmentTheory.aligned_add_sub_cor
         |> SPEC_ALL |> UNDISCH |> CONJUNCT1 |> DISCH_ALL
         |> irule)
    \\ fs[Abbr`n`]
    \\ simp[LENGTH_data,LENGTH_code]
    \\ EVAL_TAC )
  \\ fs[]
  \\ simp[#1(EQ_IMP_RULE(SPEC_ALL alignmentTheory.aligned_def))]
  \\ simp[alignmentTheory.align_def]
  \\ fs[LENGTH_hello_ag32_ffi_code]
  \\ simp[Abbr`n`,LENGTH_code,LENGTH_data,lab_to_targetTheory.ffi_offset_def,heap_size_def]
  \\ DEP_REWRITE_TAC[ADD_DIV_RWT]
  \\ simp[]
  \\ once_rewrite_tac[MULT_COMM]
  \\ simp[MULT_DIV]
  \\ simp[hello_init_memory_words_def,EL_APPEND_EQN,
          LENGTH_data,LENGTH_words_of_bytes_hello_startup_code,heap_size_def,
          LENGTH_hello_startup_code]
  \\ simp[LENGTH_words_of_bytes,LENGTH_code,bytes_in_word_def]
  \\ simp[Once(GSYM EL_MAP),LENGTH_hello_ag32_ffi_code,SimpRHS]
  \\ simp[wordSemTheory.get_byte_def, wordSemTheory.byte_index_def]
  \\ blastLib.BBLAST_TAC);

val hello_ag32_ffi_2_code_correct = Q.store_thm("hello_ag32_ffi_2_code_correct",
  `∀s.
   (∀n. n < LENGTH (TAKE 6 (DROP 5 hello_ag32_ffi_code)) ⇒
      let pc = s.PC + n2w (4 * n) in
      ((s.MEM (pc + 3w) @@
      ((s.MEM (pc + 2w) @@
      ((s.MEM (pc + 1w) @@
      s.MEM pc) : word16)) : word24)) = Encode (EL n (TAKE 6 (DROP 5 hello_ag32_ffi_code))))) ∧
    byte_aligned s.PC ∧
    s.R 3w <=+ s.R 2w ∧
    s.R 2w <+ s.PC ∧ w2n (s.PC) + 4 * 6 < dimword(:32)
   ⇒
   ∃n.
   (FUNPOW Next n s = hello_ag32_ffi_2 s)`,
  ho_match_mp_tac hello_ag32_ffi_2_ind
  \\ rw[ag32Theory.incPC_def, APPLY_UPDATE_THM, hello_ag32_ffi_code_def]
  \\ simp[Once hello_ag32_ffi_2_def]
  \\ simp[ag32Theory.incPC_def, APPLY_UPDATE_THM]
  \\ IF_CASES_TAC
  >- (
    qexists_tac`1`
    \\ simp[]
    \\ simp[ag32Theory.Next_def]
    \\ simp[GSYM byte_align_extract]
    \\ simp[#1(EQ_IMP_RULE byte_align_aligned)]
    \\ first_assum(qspec_then`0`mp_tac)
    \\ simp_tac(srw_ss())[]
    \\ disch_then kall_tac
    \\ simp[ag32_targetProofTheory.Decode_Encode]
    \\ simp[ag32Theory.Run_def]
    \\ simp[ag32Theory.dfn'JumpIfNotZero_def,ag32Theory.ri2word_def,ag32Theory.ALU_def] )
  \\ fs[]
  \\ last_x_assum mp_tac
  \\ impl_tac >- (
    reverse conj_tac
    >- (
      Cases_on`s.R 2w`
      \\ Cases_on`s.R 3w`
      \\ fs[word_ls_n2w,word_add_n2w,word_lo_n2w] )
    \\ gen_tac \\ strip_tac
    \\ Cases_on`s.R 3w`
    \\ Cases_on`s.R 2w`
    \\ Cases_on`s.PC`
    \\ fs[word_ls_n2w,word_add_n2w,word_lo_n2w]
    \\ first_x_assum drule
    \\ simp[] )
  \\ disch_then(CHOOSE_THEN (assume_tac o SYM))
  \\ simp[]
  \\ simp[Once EXISTS_NUM]
  \\ disj2_tac
  \\ simp[FUNPOW]
  \\ pop_assum kall_tac
  \\ simp[ag32Theory.Next_def]
  \\ simp[GSYM byte_align_extract]
  \\ simp[#1(EQ_IMP_RULE byte_align_aligned)]
  \\ first_assum(qspec_then`0`mp_tac)
  \\ simp_tac(srw_ss())[]
  \\ disch_then kall_tac
  \\ simp[ag32_targetProofTheory.Decode_Encode]
  \\ simp[ag32Theory.Run_def]
  \\ simp[ag32Theory.dfn'JumpIfNotZero_def,ag32Theory.ri2word_def,ag32Theory.ALU_def,ag32Theory.incPC_def]
  \\ simp[Once EXISTS_NUM]
  \\ disj2_tac
  \\ simp[FUNPOW]
  \\ simp[ag32Theory.Next_def]
  \\ simp[GSYM byte_align_extract]
  \\ DEP_REWRITE_TAC[#1(EQ_IMP_RULE byte_align_aligned)]
  \\ DEP_REWRITE_TAC[byte_aligned_add]
  \\ conj_tac >- (fs[] \\ EVAL_TAC)
  \\ first_assum(qspec_then`1`mp_tac)
  \\ simp_tac(srw_ss())[]
  \\ disch_then kall_tac
  \\ simp[ag32_targetProofTheory.Decode_Encode]
  \\ simp[ag32Theory.Run_def]
  \\ simp[ag32Theory.dfn'Normal_def,ag32Theory.ri2word_def,ag32Theory.norm_def,
          ag32Theory.ALU_def,ag32Theory.incPC_def]
  \\ simp[Once EXISTS_NUM]
  \\ disj2_tac
  \\ simp[FUNPOW]
  \\ simp[ag32Theory.Next_def]
  \\ simp[GSYM byte_align_extract]
  \\ DEP_REWRITE_TAC[#1(EQ_IMP_RULE byte_align_aligned)]
  \\ DEP_REWRITE_TAC[byte_aligned_add]
  \\ conj_tac >- (fs[] \\ EVAL_TAC)
  \\ first_assum(qspec_then`2`mp_tac)
  \\ simp_tac(srw_ss())[]
  \\ disch_then kall_tac
  \\ simp[ag32_targetProofTheory.Decode_Encode]
  \\ simp[ag32Theory.Run_def]
  \\ simp[ag32Theory.dfn'LoadMEMByte_def,ag32Theory.ri2word_def,ag32Theory.incPC_def]
  \\ simp[Once EXISTS_NUM]
  \\ disj2_tac
  \\ simp[FUNPOW]
  \\ simp[ag32Theory.Next_def]
  \\ simp[GSYM byte_align_extract]
  \\ DEP_REWRITE_TAC[#1(EQ_IMP_RULE byte_align_aligned)]
  \\ DEP_REWRITE_TAC[byte_aligned_add]
  \\ conj_tac >- (fs[] \\ EVAL_TAC)
  \\ first_assum(qspec_then`3`mp_tac)
  \\ simp_tac(srw_ss())[APPLY_UPDATE_THM]
  \\ rpt (
    IF_CASES_TAC
    >- ( Cases_on`s.R 3w` \\ Cases_on`s.R 2w` \\ Cases_on`s.PC`
         \\ fs[word_add_n2w,word_ls_n2w,word_lo_n2w] ))
  \\ simp[]
  \\ disch_then kall_tac
  \\ simp[ag32_targetProofTheory.Decode_Encode]
  \\ simp[ag32Theory.Run_def]
  \\ simp[ag32Theory.dfn'StoreMEMByte_def,ag32Theory.ri2word_def,ag32Theory.incPC_def]
  \\ simp[Once EXISTS_NUM]
  \\ disj2_tac
  \\ simp[FUNPOW]
  \\ simp[ag32Theory.Next_def]
  \\ simp[GSYM byte_align_extract]
  \\ DEP_REWRITE_TAC[#1(EQ_IMP_RULE byte_align_aligned)]
  \\ DEP_REWRITE_TAC[byte_aligned_add]
  \\ conj_tac >- (fs[] \\ EVAL_TAC)
  \\ first_assum(qspec_then`4`mp_tac)
  \\ simp_tac(srw_ss())[APPLY_UPDATE_THM]
  \\ rpt (
    IF_CASES_TAC
    >- ( Cases_on`s.R 3w` \\ Cases_on`s.R 2w` \\ Cases_on`s.PC`
         \\ fs[word_add_n2w,word_ls_n2w,word_lo_n2w] \\ rfs[]))
  \\ simp[]
  \\ disch_then kall_tac
  \\ simp[ag32_targetProofTheory.Decode_Encode]
  \\ simp[ag32Theory.Run_def]
  \\ simp[ag32Theory.dfn'Normal_def,ag32Theory.ri2word_def,ag32Theory.norm_def,
          ag32Theory.ALU_def,ag32Theory.incPC_def]
  \\ simp[Once EXISTS_NUM]
  \\ disj2_tac
  \\ simp[FUNPOW]
  \\ simp[ag32Theory.Next_def]
  \\ simp[GSYM byte_align_extract]
  \\ DEP_REWRITE_TAC[#1(EQ_IMP_RULE byte_align_aligned)]
  \\ DEP_REWRITE_TAC[byte_aligned_add]
  \\ conj_tac >- (fs[] \\ EVAL_TAC)
  \\ first_assum(qspec_then`5`mp_tac)
  \\ simp_tac(srw_ss())[APPLY_UPDATE_THM]
  \\ ntac 4 (pop_assum kall_tac)
  \\ rpt (
    IF_CASES_TAC
    >- ( Cases_on`s.R 3w` \\ Cases_on`s.R 2w` \\ Cases_on`s.PC`
         \\ fs[word_add_n2w,word_ls_n2w,word_lo_n2w] \\ rfs[]))
  \\ simp[]
  \\ disch_then kall_tac
  \\ simp[ag32_targetProofTheory.Decode_Encode]
  \\ simp[ag32Theory.Run_def]
  \\ simp[ag32Theory.dfn'JumpIfZero_def,ag32Theory.ALU_def,ag32Theory.ri2word_def]
  \\ qexists_tac`n`
  \\ AP_TERM_TAC
  \\ simp[ag32Theory.ag32_state_component_equality]
  \\ simp[FUN_EQ_THM,APPLY_UPDATE_THM]
  \\ ntac 4 (pop_assum kall_tac)
  \\ rw[]
  \\ blastLib.BBLAST_TAC);

val hello_ag32_ffi_code_correct = Q.store_thm("hello_ag32_ffi_code_correct",
  `(∀n. n < LENGTH hello_ag32_ffi_code ⇒
      let pc = s.PC + n2w (4 * n) in
      ((s.MEM (pc + 3w) @@
      ((s.MEM (pc + 2w) @@
      ((s.MEM (pc + 1w) @@
      s.MEM pc) : word16)) : word24)) = Encode (EL n hello_ag32_ffi_code))) ∧
   byte_aligned s.PC ∧
   ¬ s.CarryFlag ∧
   ¬ s.OverflowFlag ∧
   bytes_in_memory (s.R 1w) bs s.MEM dm ∧
   (∀w. r0 <=+ w ∧ w <+ r0 + n2w (LENGTH bs) ⇒ w ∉ dm) ∧
   LENGTH bs ≤ print_string_max_length ∧
   w2n (s.R 1w) + LENGTH bs < dimword(:32) ∧
   w2n r0 + LENGTH bs < w2n s.PC + 16 ∧
   w2n s.PC + (4 * LENGTH hello_ag32_ffi_code) < dimword(:32) ∧
   (s.R 3w = r0 + n2w (heap_size + 4 * LENGTH data + 12)) ∧
   (s.R 2w = n2w (LENGTH bs)) ∧
   w2n r0 + memory_size < dimword(:32)
   ⇒
   ∃k. (FUNPOW Next k s = hello_ag32_ffi s)`,
  simp[hello_ag32_ffi_def]
  \\ strip_tac
  \\ simp[Once EXISTS_NUM]
  \\ disj2_tac
  \\ simp[FUNPOW]
  \\ first_assum(qspec_then`0`mp_tac)
  \\ simp_tac(srw_ss())[hello_ag32_ffi_code_def]
  \\ simp[ag32Theory.Next_def]
  \\ simp[GSYM byte_align_extract]
  \\ simp[#1(EQ_IMP_RULE byte_align_aligned)]
  \\ simp[ag32_targetProofTheory.Decode_Encode]
  \\ disch_then kall_tac
  \\ qspec_then`s.R 2w`(fn th => DEP_REWRITE_TAC[th])(Q.GEN`len`hello_ag32_ffi_1_spec)
  \\ simp[ag32Theory.Run_def]
  \\ simp[ag32Theory.dfn'LoadConstant_def,ag32Theory.incPC_def]
  \\ simp[Once EXISTS_NUM]
  \\ disj2_tac
  \\ simp[FUNPOW]
  \\ first_assum(qspec_then`1`mp_tac)
  \\ simp_tac(srw_ss())[hello_ag32_ffi_code_def]
  \\ simp[ag32Theory.Next_def]
  \\ simp[GSYM byte_align_extract]
  \\ DEP_REWRITE_TAC[#1(EQ_IMP_RULE byte_align_aligned)]
  \\ DEP_REWRITE_TAC[byte_aligned_add] \\ simp[]
  \\ conj_tac >- EVAL_TAC
  \\ disch_then kall_tac
  \\ simp[ag32_targetProofTheory.Decode_Encode]
  \\ simp[ag32Theory.Run_def]
  \\ simp[ag32Theory.dfn'LoadUpperConstant_def,ag32Theory.incPC_def]
  \\ simp[APPLY_UPDATE_THM]
  \\ qmatch_goalsub_abbrev_tac`4w =+ r4`
  \\ simp[Once EXISTS_NUM]
  \\ disj2_tac
  \\ simp[FUNPOW]
  \\ first_assum(qspec_then`2`mp_tac)
  \\ simp_tac(srw_ss())[hello_ag32_ffi_code_def]
  \\ simp[ag32Theory.Next_def]
  \\ simp[GSYM byte_align_extract]
  \\ DEP_REWRITE_TAC[#1(EQ_IMP_RULE byte_align_aligned)]
  \\ DEP_REWRITE_TAC[byte_aligned_add] \\ simp[]
  \\ conj_tac >- EVAL_TAC
  \\ disch_then kall_tac
  \\ simp[ag32_targetProofTheory.Decode_Encode]
  \\ simp[ag32Theory.Run_def]
  \\ simp[ag32Theory.dfn'Normal_def,ag32Theory.norm_def,
          ag32Theory.ALU_def,ag32Theory.incPC_def,ag32Theory.ri2word_def]
  \\ simp[APPLY_UPDATE_THM]
  \\ simp[Once EXISTS_NUM]
  \\ disj2_tac
  \\ simp[FUNPOW]
  \\ first_assum(qspec_then`3`mp_tac)
  \\ simp_tac(srw_ss())[hello_ag32_ffi_code_def]
  \\ simp[ag32Theory.Next_def]
  \\ simp[GSYM byte_align_extract]
  \\ DEP_REWRITE_TAC[#1(EQ_IMP_RULE byte_align_aligned)]
  \\ DEP_REWRITE_TAC[byte_aligned_add] \\ simp[]
  \\ conj_tac >- EVAL_TAC
  \\ disch_then kall_tac
  \\ simp[ag32_targetProofTheory.Decode_Encode]
  \\ simp[ag32Theory.Run_def]
  \\ simp[ag32Theory.dfn'StoreMEMByte_def,ag32Theory.ri2word_def,APPLY_UPDATE_THM,ag32Theory.incPC_def]
  \\ simp[LENGTH_data, heap_size_def, APPLY_UPDATE_THM,Abbr`r4`]
  \\ simp[Once EXISTS_NUM]
  \\ disj2_tac
  \\ simp[FUNPOW]
  \\ first_assum(qspec_then`4`mp_tac)
  \\ simp_tac(srw_ss())[hello_ag32_ffi_code_def]
  \\ simp[ag32Theory.Next_def]
  \\ simp[GSYM byte_align_extract]
  \\ DEP_REWRITE_TAC[#1(EQ_IMP_RULE byte_align_aligned)]
  \\ DEP_REWRITE_TAC[byte_aligned_add] \\ simp[]
  \\ conj_tac >- EVAL_TAC
  \\ simp[APPLY_UPDATE_THM]
  \\ rpt (
    IF_CASES_TAC
    >- ( Cases_on`r0` \\ Cases_on`s.PC`
         \\ fs[word_add_n2w,word_ls_n2w,word_lo_n2w,memory_size_def,
               ag32Theory.print_string_max_length_def,LENGTH_hello_ag32_ffi_code]
         \\ rfs[]))
  \\ simp[]
  \\ disch_then kall_tac
  \\ simp[ag32_targetProofTheory.Decode_Encode]
  \\ simp[ag32Theory.Run_def]
  \\ simp[ag32Theory.dfn'Normal_def,ag32Theory.ri2word_def,ag32Theory.norm_def,
          ag32Theory.ALU_def,ag32Theory.incPC_def,APPLY_UPDATE_THM]
  \\ qmatch_goalsub_abbrev_tac`FUNPOW _ _ ss`
  \\ qmatch_goalsub_abbrev_tac`hello_ag32_ffi_2 ss'`
  \\ `ss' = ss`
  by (
    simp[Abbr`ss`,Abbr`ss'`, ag32Theory.ag32_state_component_equality,
         APPLY_UPDATE_THM, FUN_EQ_THM]
    \\ Cases_on`s.R 2w`
    \\ Cases_on`r0`
    \\ fs[word_add_n2w]
    \\ fs[memory_size_def]
    \\ fs[word_ls_n2w, ag32Theory.print_string_max_length_def]
    \\ rw[] \\ fs[]
    \\ fs[w2w_n2w]
    \\ simp[integerTheory.INT_ADD_COMM]
    \\ blastLib.BBLAST_TAC)
  \\ qpat_x_assum`Abbrev(ss' = _)`kall_tac
  \\ pop_assum(SUBST_ALL_TAC)
  \\ qspec_then`ss`mp_tac hello_ag32_ffi_2_code_correct
  \\ impl_tac
  >- (
    simp[Abbr`ss`,APPLY_UPDATE_THM]
    \\ conj_tac
    >- (
      gen_tac
      \\ simp[LENGTH_hello_ag32_ffi_code]
      \\ strip_tac
      \\ rpt (
        IF_CASES_TAC
        >- ( Cases_on`r0` \\ Cases_on`s.PC`
             \\ fs[word_add_n2w,word_ls_n2w,word_lo_n2w,memory_size_def,
                   ag32Theory.print_string_max_length_def,LENGTH_hello_ag32_ffi_code]
             \\ rfs[]))
      \\ first_x_assum(qspec_then`n + 5`mp_tac)
      \\ fs[hello_ag32_ffi_code_def, LEFT_ADD_DISTRIB, GSYM word_add_n2w]
      \\ simp[EL_CONS,PRE_SUB1] \\ rw[]
      \\ qpat_x_assum`n < _`mp_tac
      \\ simp[NUMERAL_LESS_THM]
      \\ strip_tac \\ rveq \\ simp[] )
    \\ DEP_REWRITE_TAC[byte_aligned_add]
    \\ simp[]
    \\ conj_tac >- EVAL_TAC
    \\ Cases_on`r0` \\ Cases_on`s.PC` \\ Cases_on`s.R 1w`
    \\ fs[word_add_n2w,word_ls_n2w,word_lo_n2w,memory_size_def,ag32Theory.print_string_max_length_def]
    \\ fs[LENGTH_hello_ag32_ffi_code])
  \\ disch_then(CHOOSE_THEN assume_tac)
  \\ qspecl_then[`s.R 1w`,`ss`,`0w`,`bs`]mp_tac (Q.GEN`ptr`hello_ag32_ffi_2_spec)
  \\ impl_tac
  >- (
    fs[Abbr`ss`,APPLY_UPDATE_THM,memory_size_def,ag32Theory.print_string_max_length_def]
    \\ irule asmPropsTheory.bytes_in_memory_change_mem
    \\ goal_assum(first_assum o mp_then Any mp_tac)
    \\ simp[APPLY_UPDATE_THM] \\ rw[]
    \\ rw[] \\ fs[]
    \\ qmatch_asmsub_rename_tac`k < LENGTH bs`
    \\ Cases_on`s.R 1w` \\ fs[word_lo_n2w, word_add_n2w,word_ls_n2w]
    \\ rfs[]
    \\ rpt(qpat_x_assum`_ _  < _`mp_tac)
    \\ strip_tac
    \\ strip_tac
    \\ fs[] \\ rw[]
    \\ `F` suffices_by fs[]
    \\ imp_res_tac asmPropsTheory.bytes_in_memory_all_pcs
    \\ pop_assum mp_tac
    \\ simp[asmPropsTheory.all_pcs_thm,SUBSET_DEF,PULL_EXISTS]
    \\ qexists_tac`0` \\ simp[]
    \\ qexists_tac`k` \\ simp[]
    \\ first_x_assum match_mp_tac
    \\ simp[word_add_n2w,word_ls_n2w,word_lo_n2w])
  \\ disch_then(CHOOSE_THEN assume_tac)
  \\ simp[hello_ag32_ffi_3_spec]
  \\ qexists_tac`6+n`
  \\ rewrite_tac[FUNPOW_ADD]
  \\ simp[APPLY_UPDATE_THM]
  \\ ntac 2 (pop_assum kall_tac)
  \\ simp[Abbr`ss`,APPLY_UPDATE_THM]
  \\ simp[Once(numLib.SUC_RULE FUNPOW)]
  \\ simp[Once ag32Theory.Next_def]
  \\ simp[GSYM byte_align_extract]
  \\ DEP_REWRITE_TAC[#1(EQ_IMP_RULE byte_align_aligned)]
  \\ DEP_REWRITE_TAC[byte_aligned_add] \\ simp[]
  \\ conj_tac >- EVAL_TAC
  \\ DEP_REWRITE_TAC[SIMP_RULE(srw_ss())[]asm_write_bytearray_unchanged]
  \\ conj_tac >- (
    Cases_on`r0` \\ Cases_on`s.PC`
    \\ fs[word_add_n2w,word_ls_n2w,word_lo_n2w,memory_size_def,
          ag32Theory.print_string_max_length_def,LENGTH_hello_ag32_ffi_code] )
  \\ first_assum(qspec_then`11`mp_tac)
  \\ simp_tac(srw_ss())[hello_ag32_ffi_code_def,APPLY_UPDATE_THM]
  \\ rpt (
    IF_CASES_TAC
    >- ( Cases_on`r0` \\ Cases_on`s.PC`
         \\ fs[word_add_n2w,word_ls_n2w,word_lo_n2w,memory_size_def,
               ag32Theory.print_string_max_length_def,LENGTH_hello_ag32_ffi_code]
         \\ rfs[]))
  \\ simp[]
  \\ disch_then kall_tac
  \\ simp[ag32_targetProofTheory.Decode_Encode]
  \\ simp[ag32Theory.Run_def]
  \\ simp[ag32Theory.dfn'Normal_def,ag32Theory.ri2word_def,ag32Theory.norm_def,
          ag32Theory.ALU_def,ag32Theory.incPC_def,APPLY_UPDATE_THM]
  \\ simp[Once(numLib.SUC_RULE FUNPOW)]
  \\ simp[Once ag32Theory.Next_def]
  \\ simp[GSYM byte_align_extract]
  \\ DEP_REWRITE_TAC[#1(EQ_IMP_RULE byte_align_aligned)]
  \\ DEP_REWRITE_TAC[byte_aligned_add] \\ simp[]
  \\ conj_tac >- EVAL_TAC
  \\ DEP_REWRITE_TAC[SIMP_RULE(srw_ss())[]asm_write_bytearray_unchanged]
  \\ conj_tac >- (
    Cases_on`r0` \\ Cases_on`s.PC`
    \\ fs[word_add_n2w,word_ls_n2w,word_lo_n2w,memory_size_def,
          ag32Theory.print_string_max_length_def,LENGTH_hello_ag32_ffi_code] )
  \\ simp[APPLY_UPDATE_THM]
  \\ ntac 8 (pop_assum kall_tac)
  \\ rpt (
    IF_CASES_TAC
    >- ( Cases_on`r0` \\ Cases_on`s.PC`
         \\ fs[word_add_n2w,word_ls_n2w,word_lo_n2w,memory_size_def,
               ag32Theory.print_string_max_length_def,LENGTH_hello_ag32_ffi_code]
         \\ rfs[]))
  \\ first_assum(qspec_then`12`mp_tac)
  \\ simp_tac(srw_ss())[hello_ag32_ffi_code_def]
  \\ disch_then kall_tac
  \\ simp[ag32_targetProofTheory.Decode_Encode]
  \\ simp[ag32Theory.Run_def]
  \\ simp[ag32Theory.dfn'Normal_def,ag32Theory.ri2word_def,ag32Theory.norm_def,
          ag32Theory.ALU_def,ag32Theory.incPC_def,APPLY_UPDATE_THM]
  \\ simp[Once(numLib.SUC_RULE FUNPOW)]
  \\ simp[Once ag32Theory.Next_def]
  \\ simp[GSYM byte_align_extract]
  \\ DEP_REWRITE_TAC[#1(EQ_IMP_RULE byte_align_aligned)]
  \\ DEP_REWRITE_TAC[byte_aligned_add] \\ simp[]
  \\ conj_tac >- EVAL_TAC
  \\ ntac 4 (pop_assum kall_tac)
  \\ DEP_REWRITE_TAC[SIMP_RULE(srw_ss())[]asm_write_bytearray_unchanged]
  \\ conj_tac >- (
    Cases_on`r0` \\ Cases_on`s.PC`
    \\ fs[word_add_n2w,word_ls_n2w,word_lo_n2w,memory_size_def,
          ag32Theory.print_string_max_length_def,LENGTH_hello_ag32_ffi_code] )
  \\ simp[APPLY_UPDATE_THM]
  \\ rpt (
    IF_CASES_TAC
    >- ( Cases_on`r0` \\ Cases_on`s.PC`
         \\ fs[word_add_n2w,word_ls_n2w,word_lo_n2w,memory_size_def,
               ag32Theory.print_string_max_length_def,LENGTH_hello_ag32_ffi_code]
         \\ rfs[]))
  \\ first_assum(qspec_then`13`mp_tac)
  \\ simp_tac(srw_ss())[hello_ag32_ffi_code_def]
  \\ disch_then kall_tac
  \\ simp[ag32_targetProofTheory.Decode_Encode]
  \\ simp[ag32Theory.Run_def]
  \\ simp[ag32Theory.dfn'Normal_def,ag32Theory.ri2word_def,ag32Theory.norm_def,
          ag32Theory.ALU_def,ag32Theory.incPC_def,APPLY_UPDATE_THM]
  \\ ntac 4 (pop_assum kall_tac)
  \\ simp[Once(numLib.SUC_RULE FUNPOW)]
  \\ simp[Once ag32Theory.Next_def]
  \\ simp[GSYM byte_align_extract]
  \\ DEP_REWRITE_TAC[#1(EQ_IMP_RULE byte_align_aligned)]
  \\ DEP_REWRITE_TAC[byte_aligned_add] \\ simp[]
  \\ conj_tac >- EVAL_TAC
  \\ DEP_REWRITE_TAC[SIMP_RULE(srw_ss())[]asm_write_bytearray_unchanged]
  \\ conj_tac >- (
    Cases_on`r0` \\ Cases_on`s.PC`
    \\ fs[word_add_n2w,word_ls_n2w,word_lo_n2w,memory_size_def,
          ag32Theory.print_string_max_length_def,LENGTH_hello_ag32_ffi_code] )
  \\ simp[APPLY_UPDATE_THM]
  \\ rpt (
    IF_CASES_TAC
    >- ( Cases_on`r0` \\ Cases_on`s.PC`
         \\ fs[word_add_n2w,word_ls_n2w,word_lo_n2w,memory_size_def,
               ag32Theory.print_string_max_length_def,LENGTH_hello_ag32_ffi_code]
         \\ rfs[]))
  \\ first_assum(qspec_then`14`mp_tac)
  \\ simp_tac(srw_ss())[hello_ag32_ffi_code_def]
  \\ disch_then kall_tac
  \\ simp[ag32_targetProofTheory.Decode_Encode]
  \\ simp[ag32Theory.Run_def]
  \\ simp[ag32Theory.dfn'Normal_def,ag32Theory.ri2word_def,ag32Theory.norm_def,
          ag32Theory.ALU_def,ag32Theory.incPC_def,APPLY_UPDATE_THM]
  \\ ntac 4 (pop_assum kall_tac)
  \\ simp_tac std_ss [Once(numLib.SUC_RULE FUNPOW)]
  \\ simp_tac std_ss [Once ag32Theory.Next_def]
  \\ simp[]
  \\ simp[GSYM byte_align_extract]
  \\ DEP_REWRITE_TAC[#1(EQ_IMP_RULE byte_align_aligned)]
  \\ DEP_REWRITE_TAC[byte_aligned_add] \\ simp[]
  \\ conj_tac >- EVAL_TAC
  \\ DEP_REWRITE_TAC[SIMP_RULE(srw_ss())[]asm_write_bytearray_unchanged]
  \\ conj_tac >- (
    Cases_on`r0` \\ Cases_on`s.PC`
    \\ fs[word_add_n2w,word_ls_n2w,word_lo_n2w,memory_size_def,
          ag32Theory.print_string_max_length_def,LENGTH_hello_ag32_ffi_code] )
  \\ simp[APPLY_UPDATE_THM]
  \\ rpt (
    IF_CASES_TAC
    >- ( Cases_on`r0` \\ Cases_on`s.PC`
         \\ fs[word_add_n2w,word_ls_n2w,word_lo_n2w,memory_size_def,
               ag32Theory.print_string_max_length_def,LENGTH_hello_ag32_ffi_code]
         \\ rfs[]))
  \\ first_assum(qspec_then`15`mp_tac)
  \\ simp_tac(srw_ss())[hello_ag32_ffi_code_def]
  \\ disch_then kall_tac
  \\ simp[ag32_targetProofTheory.Decode_Encode]
  \\ simp[ag32Theory.Run_def]
  \\ simp[ag32Theory.dfn'Interrupt_def,ag32Theory.incPC_def]
  \\ ntac 4 (pop_assum kall_tac)
  \\ simp_tac std_ss [Once ag32Theory.Next_def]
  \\ simp[]
  \\ simp[GSYM byte_align_extract]
  \\ DEP_REWRITE_TAC[#1(EQ_IMP_RULE byte_align_aligned)]
  \\ DEP_REWRITE_TAC[byte_aligned_add] \\ simp[]
  \\ conj_tac >- EVAL_TAC
  \\ DEP_REWRITE_TAC[SIMP_RULE(srw_ss())[]asm_write_bytearray_unchanged]
  \\ conj_tac >- (
    Cases_on`r0` \\ Cases_on`s.PC`
    \\ fs[word_add_n2w,word_ls_n2w,word_lo_n2w,memory_size_def,
          ag32Theory.print_string_max_length_def,LENGTH_hello_ag32_ffi_code] )
  \\ simp[APPLY_UPDATE_THM]
  \\ rpt (
    IF_CASES_TAC
    >- ( Cases_on`r0` \\ Cases_on`s.PC`
         \\ fs[word_add_n2w,word_ls_n2w,word_lo_n2w,memory_size_def,
               ag32Theory.print_string_max_length_def,LENGTH_hello_ag32_ffi_code]
         \\ rfs[]))
  \\ first_assum(qspec_then`16`mp_tac)
  \\ simp_tac(srw_ss())[hello_ag32_ffi_code_def]
  \\ disch_then kall_tac
  \\ simp[ag32_targetProofTheory.Decode_Encode]
  \\ simp[ag32Theory.Run_def]
  \\ simp[ag32Theory.dfn'Jump_def,ag32Theory.ri2word_def,ag32Theory.ALU_def,APPLY_UPDATE_THM]);

(*
Memory layout:
  hz = heap_size is the heap+stack size in mebibytes (including the unusable FFI bytes)
  r0 gives the lowest software-usable address
  r0 .. r0 + 64 is used by the FFI implementation
  r0 + 64 .. r0 + hzMiB is the CakeML heap+stack space. The machine initial PC is r0 + 64, so this initially contains the startup code.
  r0 + hzMiB .. r0 + hzMiB + 4 * LENGTH data is the bitmaps
  r0 + hzMiB + 4 * LENGTH data is the FFI PC
  r0 + hzMiB + 4 * LENGTH data + 16 is the ccache PC
  r0 + hzMiB + 4 * LENGTH data + 32 is the halt PC
  r0 + hzMiB + 4 * LENGTH data + 48 is the initial PC for CakeML
  r0 + hzMiB + 4 * LENGTH data + 48 .. r0 + hzMiB + 4 * LENGTH data + 48 + LENGTH code is the code
  r0 + hzMiB + 4 * LENGTH data + 48 + LENGTH code .. r0 + hzMiB + 4 * LENGTH data + 48 + LENGTH code + 4 * LENGTH hello_ag32_ffi_code is the FFI implementation
  r0 + hzMiB + 4 * LENGTH data + 48 + LENGTH code + 4 * LENGTH hello_ag32_ffi_code .. r0 + memory_size MB is zeros
*)

*)

val hello_machine_config_def = Define`
  hello_machine_config =
    ag32_machine_config (THE config.ffi_names) (LENGTH code) (LENGTH data)`;

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
        (hello_machine_config r0).prog_addresses
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
      (hello_init_memory r0 (args,inp))
      (hello_machine_config r0).prog_addresses
      r0)``);

val hello_init_asm_state_asm_step = Q.store_thm("hello_init_asm_state_asm_step",
  `byte_aligned r0 ∧ w2n r0 + memory_size < dimword(:32) ∧
   SUM (MAP strlen args) + LENGTH args ≤ cline_size ∧
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
           (hello_init_memory r0 (args,inp)) (ds + n2w k)))`,
  strip_tac
  \\ qho_match_abbrev_tac`LET (λtr. (_ tr) ∧ P (_ tr)) _`
  \\ rewrite_tac[hello_startup_asm_code_eq,
                 SIMP_RULE(srw_ss())[LENGTH_data](EVAL``(hello_machine_config r0).prog_addresses``)]
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
   SUM (MAP strlen args) + LENGTH args ≤ cline_size ∧
   LENGTH inp ≤ stdin_size
  ⇒
   (λx y. ∃i. asm_step ag32_config x i y)^* hello_asm_state0 (hello_init_asm_state r0 (args,inp)) ∧
   let ffi_names = THE config.ffi_names in
   let num_ffis = LENGTH ffi_names in
   let hs = r0 + n2w heap_start_offset in
   let ds = r0 + n2w (code_start_offset num_ffis + LENGTH code) in
   ((hello_init_asm_state r0 (args,inp)).pc = r0 + n2w (code_start_offset num_ffis)) ∧
   (read_bytearray (hello_init_asm_state r0 (args,inp)).pc (LENGTH code)
      (λa. if a ∈ (hello_machine_config r0).prog_addresses then SOME ((hello_init_asm_state r0 (args,inp)).mem a) else NONE)
      = SOME code) ∧
    ((hello_init_asm_state r0 (args,inp)).regs 2 = hs) ∧
    ((hello_init_asm_state r0 (args,inp)).regs 4 = hs + n2w heap_size) ∧
    (word_of_bytes F 0w (GENLIST ((hello_init_asm_state r0 (args,inp)).mem o ((+)(hs + 0w * 4w)) o n2w) 4)
     = ds) ∧
    (word_of_bytes F 0w (GENLIST ((hello_init_asm_state r0 (args,inp)).mem o ((+)(hs + 1w * 4w)) o n2w) 4)
     = ds + n2w (4 * LENGTH data)) ∧
    (word_of_bytes F 0w (GENLIST ((hello_init_asm_state r0 (args,inp)).mem o ((+)(hs + 2w * 4w)) o n2w) 4)
     = ds + n2w (4 * LENGTH data)) ∧
    (word_of_bytes F 0w (GENLIST ((hello_init_asm_state r0 (args,inp)).mem o ((+)(hs + 3w * 4w)) o n2w) 4)
     = ds) ∧
    (word_of_bytes F 0w (GENLIST ((hello_init_asm_state r0 (args,inp)).mem o ((+)(hs + 4w * 4w)) o n2w) 4)
     = ds) ∧
    (∀k. k < 4 * LENGTH data + 4 ⇒
      ((hello_init_asm_state r0 (args,inp)).mem (ds + n2w k) =
       hello_init_memory r0 (args,inp) (ds + n2w k)))`,
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
   SUM (MAP strlen args) + LENGTH args ≤ cline_size ∧
   LENGTH inp ≤ stdin_size ∧
   is_ag32_init_state (hello_init_memory r0 (args,inp)) r0 ms ⇒
   ∃n. target_state_rel ag32_target (hello_init_asm_state r0 (args,inp)) (FUNPOW Next n ms) ∧
       ((FUNPOW Next n ms).io_events = ms.io_events) ∧
       (∀x. x ∉ (hello_machine_config r0).prog_addresses ⇒
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

(*

val hello_good_init_state = Q.store_thm("hello_good_init_state",
  `byte_aligned r0 ∧ w2n r0 + memory_size < dimword(:32) ∧
   SUM (MAP strlen args) + LENGTH args ≤ cline_size ∧
   LENGTH inp ≤ stdin_size ∧
   is_ag32_init_state (hello_init_memory r0 (args,inp)) r0 ms0 ⇒
   ∃io_regs cc_regs.
   good_init_state (hello_machine_config r0) (FUNPOW Next (hello_startup_clock r0 ms0 inp args) ms0)
     ag_ffi code 0 (hello_init_asm_state r0 (args,inp))
     (λk. Word
       (word_of_bytes F 0w (GENLIST (λi. (hello_init_asm_state r0 (args,inp)).mem (k + n2w i)) 4)))
       ({w | (hello_init_asm_state r0 (args,inp)).regs 2 <=+ w ∧
             w <+ (hello_init_asm_state r0 (args,inp)).regs 4}
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
  \\ conj_tac >- ( fs[hello_machine_config_def, ag32_machine_config_def] )
  \\ drule hello_init_asm_state_RTC_asm_step
  \\ impl_tac >- fs[]
  \\ strip_tac
  \\ conj_tac
  >- (
    irule RTC_asm_step_target_configured
    \\ once_rewrite_tac[CONJ_COMM]
    \\ asm_exists_tac \\ fs[]
    \\ simp[lab_to_targetProofTheory.target_configured_def]
    \\ EVAL_TAC)
  \\ conj_tac >- (
    fs[asmPropsTheory.target_state_rel_def, hello_machine_config_def, ag32_machine_config_def] )
  \\ `r0 + n2w (heap_size + 4 * LENGTH data + 3 * ffi_offset) && 3w = 0w` by (
    fs[alignmentTheory.aligned_bitwise_and, alignmentTheory.byte_aligned_def]
    \\ Cases_on`r0`
    \\ simp[word_add_n2w]
    \\ once_rewrite_tac[WORD_AND_COMM]
    \\ rewrite_tac[addressTheory.n2w_and_3]
    \\ qpat_x_assum`_ = 0w`mp_tac
    \\ once_rewrite_tac[WORD_AND_COMM]
    \\ rewrite_tac[addressTheory.n2w_and_3]
    \\ EVAL_TAC
    \\ simp[] )
  \\ `r0 + n2w (heap_size + 4 * LENGTH data + 3 * ffi_offset) && 1w = 0w` by (
    fs[alignmentTheory.aligned_bitwise_and, alignmentTheory.byte_aligned_def]
    \\ Cases_on`r0`
    \\ simp[word_add_n2w]
    \\ once_rewrite_tac[WORD_AND_COMM]
    \\ rewrite_tac[addressTheory.n2w_and_1]
    \\ qpat_x_assum`_ && n2w _ = 0w`mp_tac
    \\ once_rewrite_tac[WORD_AND_COMM]
    \\ rewrite_tac[addressTheory.n2w_and_3]
    \\ EVAL_TAC
    \\ simp[LENGTH_data]
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
      \\ EVAL_TAC \\ simp[LENGTH_code, LENGTH_data, ffi_names]
      \\ Cases_on`r0`
      \\ fs[WORD_LOWER_OR_EQ,WORD_NOT_LOWER,word_add_n2w,word_ls_n2w,word_lo_n2w] )
    \\ conj_tac >- (
      qpat_x_assum`_ < _`mp_tac
      \\ EVAL_TAC \\ simp[LENGTH_code, LENGTH_data, ffi_names]
      \\ Cases_on`r0`
      \\ simp[WORD_LOWER_OR_EQ,WORD_NOT_LOWER,word_add_n2w,word_ls_n2w,word_lo_n2w] )
    \\ simp[lab_to_targetTheory.ffi_offset_def]
    \\ conj_tac >- (EVAL_TAC \\ simp[ffi_names])
    \\ conj_tac >- (
      rpt(qpat_x_assum`_ = 0w`mp_tac)
      \\ EVAL_TAC \\ simp[LENGTH_data] )
    \\ rewrite_tac[EVAL``(hello_machine_config r0).ffi_names``]
    \\ reverse Cases >- rw[]
    \\ strip_tac
    \\ conj_tac >- (
      qpat_x_assum`_ + _ < _`mp_tac
      \\ EVAL_TAC
      \\ Cases_on`r0`
      \\ simp[WORD_LOWER_OR_EQ,WORD_NOT_LOWER,word_add_n2w,word_ls_n2w,LENGTH_data] )
    \\ conj_tac >- (
      qpat_x_assum`_ + _ < _`mp_tac
      \\ EVAL_TAC
      \\ Cases_on`r0`
      \\ simp[WORD_LOWER_OR_EQ,WORD_NOT_LOWER,word_add_n2w,word_ls_n2w,LENGTH_data] )
    \\ conj_tac >- (
      qpat_x_assum`_ + _ < _`mp_tac
      \\ EVAL_TAC
      \\ Cases_on`r0`
      \\ simp[WORD_LOWER_OR_EQ,WORD_NOT_LOWER,word_add_n2w,word_ls_n2w,LENGTH_data] )
    \\ EVAL_TAC \\ rw[LENGTH_data] )
  \\ conj_tac >- (
    qpat_x_assum`_ && 3w = _`mp_tac
    \\ EVAL_TAC \\ fs[LENGTH_data, LENGTH_code] )
  \\ conj_tac >- (
    rw[asmPropsTheory.interference_ok_def]
    \\ simp[EVAL``(hello_machine_config r0).target``]
    \\ simp[EVAL``(hello_machine_config r0).next_interfer``] )
  \\ simp[LEFT_EXISTS_AND_THM]
  \\ conj_tac >- (
    simp[lab_to_targetProofTheory.ffi_interfer_ok_def]
    \\ simp[hello_machine_config_def]
    \\ simp[lab_to_targetTheory.ffi_offset_def,LENGTH_data,heap_size_def]
    \\ simp[EVAL``ag32_target.config``,labSemTheory.get_reg_value_def]
    \\ simp[LENGTH_hello_ag32_ffi_code,LENGTH_code]
    \\ qmatch_goalsub_abbrev_tac`0w =+ v0`
    \\ qexists_tac`λk n. if n = 0 then SOME v0 else if n < 5 then SOME 0w else NONE`
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
      \\ `st.oracle = ag_ffi.oracle` by metis_tac[RTC_call_FFI_rel_consts]
      \\ fs[EVAL``ag_ffi.oracle``]
      \\ pop_assum kall_tac
      \\ fs[CaseEq"option",CaseEq"bool",CaseEq"oracle_result"]
      \\ fs[NULL_EQ]
      \\ simp[lab_to_targetProofTheory.asm_write_bytearray_def]
      \\ simp[APPLY_UPDATE_THM]
      \\ fs[targetSemTheory.read_ffi_bytearrays_def]
      \\ fs[targetSemTheory.read_ffi_bytearray_def]
      \\ qmatch_goalsub_abbrev_tac`read_bytearray r1 r2 m1`
      \\ qmatch_asmsub_abbrev_tac`read_bytearray r1 r2 m2`
      \\ `m1 = m2`
      by (
        simp[Abbr`m1`,Abbr`m2`]
        \\ qpat_x_assum`_ = t1.mem_domain`(assume_tac o SYM)
        \\ simp[] )
      \\ fs[Abbr`m1`]
      \\ IF_CASES_TAC
      >- (
        qpat_x_assum`_ = t1.mem_domain`(assume_tac o SYM)
        \\ qpat_x_assum`_ ∈ _`mp_tac
        \\ simp[]
        \\ Cases_on`a` \\ simp[word_ls_n2w,word_lo_n2w,word_add_n2w]
        \\ fs[memory_size_def] )
      \\ irule asm_write_bytearray_unchanged
      \\ simp[]
      \\ Cases_on`r0` \\ fs[memory_size_def]
      \\ Cases_on`a` \\ fs[word_ls_n2w,word_lo_n2w,word_add_n2w]
      \\ qpat_x_assum`_ ∈ _`mp_tac
      \\ qpat_x_assum`_ = t1.mem_domain`(assume_tac o SYM)
      \\ simp[word_ls_n2w,word_lo_n2w,word_add_n2w])
    \\ simp[APPLY_UPDATE_THM]
    \\ rpt strip_tac
    \\ IF_CASES_TAC \\ simp[labSemTheory.get_reg_value_def]
    \\ IF_CASES_TAC \\ simp[labSemTheory.get_reg_value_def]
    \\ IF_CASES_TAC \\ simp[labSemTheory.get_reg_value_def]
    \\ IF_CASES_TAC \\ simp[labSemTheory.get_reg_value_def]
    \\ IF_CASES_TAC \\ simp[labSemTheory.get_reg_value_def] )
  \\ conj_tac >- (
    rw[lab_to_targetProofTheory.ccache_interfer_ok_def,
       hello_machine_config_def, lab_to_targetTheory.ffi_offset_def,
       LENGTH_data, heap_size_def, EVAL``ag32_target.config``]
    \\ qmatch_goalsub_abbrev_tac`0w =+ v0`
    \\ qexists_tac`λk n. if n = 0 then SOME v0 else NONE`
    \\ EVAL_TAC \\ rw[]
    \\ IF_CASES_TAC \\ simp[labSemTheory.get_reg_value_def] )
  \\ conj_asm1_tac >- (
    simp[targetSemTheory.code_loaded_def]
    \\ fs[asmPropsTheory.target_state_rel_def]
    \\ simp[SIMP_CONV (srw_ss()) [hello_machine_config_def]``(hello_machine_config r0).target``]
    \\ rfs[]
    \\ first_x_assum(CONV_TAC o RAND_CONV o REWR_CONV o SYM)
    \\ AP_TERM_TAC
    \\ rw[FUN_EQ_THM]
    \\ rw[]
    \\ match_mp_tac EQ_SYM
    \\ first_x_assum irule
    \\ imp_res_tac RTC_asm_step_consts \\ fs[]
    \\ qpat_x_assum`_ ∈ _`mp_tac
    \\ simp[hello_machine_config_def,ag32_init_asm_state_def] )
  \\ conj_tac >- (
    simp[bytes_in_mem_bytes_in_memory]
    \\ qpat_x_assum`_.pc = _`(assume_tac o SYM) \\ fs[]
    \\ irule read_bytearray_IMP_bytes_in_memory
    \\ goal_assum(first_assum o mp_then Any mp_tac)
    \\ simp[]
    \\ imp_res_tac RTC_asm_step_consts
    \\ qpat_x_assum`_ = _.pc`(assume_tac o SYM) \\ fs[]
    \\ EVAL_TAC
    \\ simp[LENGTH_data,LENGTH_code]
    \\ Cases_on`r0` \\  fs[word_add_n2w,memory_size_def]
    \\ Cases \\ fs[word_lo_n2w, word_ls_n2w])
  \\ conj_tac >- (
    qpat_x_assum`_ + _ < _`mp_tac
    \\ imp_res_tac RTC_asm_step_consts
    \\ fs[LENGTH_data,heap_size_def]
    \\ EVAL_TAC
    \\ simp[SUBSET_DEF, LENGTH_code, LENGTH_data]
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
      \\ conj_tac
      \\ (alignmentTheory.aligned_add_sub_cor
          |> SPEC_ALL |> UNDISCH |> CONJUNCT1 |> DISCH_ALL
          |> irule)
      \\ fs[]
      \\ EVAL_TAC )
    \\ disj2_tac
    \\ irule (SIMP_RULE (srw_ss()) [] byte_align_IN_IMP_IN_range)
    \\ simp[heap_size_def,LENGTH_data]
    \\ fs[alignmentTheory.byte_aligned_def,Abbr`hi`,heap_size_def]
    \\ conj_tac
    \\ (alignmentTheory.aligned_add_sub_cor
        |> SPEC_ALL |> UNDISCH |> CONJUNCT1 |> DISCH_ALL
        |> irule)
    \\ fs[]
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
    \\ `n2w i : word32 = n2w p + n2w (4 * (i DIV 4))` by metis_tac[word_add_n2w]
    \\ pop_assum(fn th => CONV_TAC(RAND_CONV(REWRITE_CONV[th])))
    \\ `n2w (4 * (i DIV 4)) : word32 = byte_align (n2w (4 * (i DIV 4)))`
    by (
      simp[alignmentTheory.byte_align_def]
      \\ simp[GSYM alignmentTheory.aligned_def]
      \\ simp[GSYM ALIGNED_eq_aligned,addressTheory.ALIGNED_n2w] )
    \\ pop_assum(CONV_TAC o PATH_CONV"rllrr" o REWR_CONV)
    \\ DEP_REWRITE_TAC[data_to_word_memoryProofTheory.get_byte_byte_align]
    \\ conj_tac >- EVAL_TAC
    \\ `p < 4`
    by (
      `p = i - 4 * (i DIV 4)` by fs[]
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
    \\ Cases_on`p` \\ fs[] >- metis_tac[]
    \\ qmatch_asmsub_rename_tac`SUC p < _`
    \\ Cases_on`p` \\ fs[] >- metis_tac[]
    \\ qmatch_asmsub_rename_tac`SUC (SUC p) < _`
    \\ Cases_on`p` \\ fs[] >- metis_tac[]
    \\ qmatch_asmsub_rename_tac`SUC (SUC (SUC p)) < _`
    \\ Cases_on`p` \\ fs[] >- metis_tac[] )
  \\ simp[LENGTH_code]);

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

val lemma = Q.prove(
  `byte_aligned r0 ∧ w2n r0 + memory_size < dimword (:32) ∧
   is_ag32_init_state (hello_init_memory r0) r0 ms0 ⇒
   installed code 0 data 0 config.ffi_names ag_ffi
     (heap_regs ag32_backend_config.stack_conf.reg_names)
     (hello_machine_config r0) (FUNPOW Next (hello_startup_clock r0 ms0) ms0)`,
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
  \\ asm_exists_tac \\ rfs[]
  \\ qhdtm_x_assum`good_init_state` mp_tac
  \\ rewrite_tac[lab_to_targetProofTheory.good_init_state_def]
  \\ disch_then(assume_tac o el 1 o CONJUNCTS)
  \\ conj_tac
  >- (irule byte_aligned_add \\ simp[] \\ EVAL_TAC)
  \\ conj_tac
  >- (irule byte_aligned_add \\ simp[] \\ EVAL_TAC)
  \\ conj_tac
  >- (irule byte_aligned_add \\ simp[] \\ EVAL_TAC)
  \\ conj_tac
  >- (Cases_on`r0` \\ simp[word_ls_n2w, word_add_n2w]
      \\ fs[memory_size_def, heap_size_def])
  \\ conj_tac
  >- ( Cases_on`r0` \\ simp[WORD_LEFT_ADD_DISTRIB] \\ EVAL_TAC )
  \\ conj_tac
  >- (
    simp[IN_DISJOINT]
    \\ qpat_x_assum`_ < _`mp_tac
    \\ EVAL_TAC
    \\ simp[LENGTH_code,LENGTH_data]
    \\ strip_tac
    \\ Cases
    \\ Cases_on`r0`
    \\ fs[word_add_n2w,word_ls_n2w,word_lo_n2w] )
  \\ conj_tac
  >- (
    rw[LENGTH_data, bytes_in_word_def]
    \\ simp[hello_init_memory_words_def, EL_APPEND_EQN,
            heap_size_def, EL_REPLICATE, LENGTH_data] )
  \\ conj_tac >- simp[bytes_in_word_def, GSYM word_add_n2w, word_mul_n2w]
  \\ conj_tac >- (
    fs[asmPropsTheory.target_state_rel_def,
       hello_machine_config_def,ag32_targetTheory.ag32_target_def]
    \\ simp[bytes_in_word_def, GSYM word_add_n2w, GSYM word_mul_n2w] )
  \\ conj_tac >- (
    fs[asmPropsTheory.target_state_rel_def,
       hello_machine_config_def,ag32_targetTheory.ag32_target_def]
    \\ simp[bytes_in_word_def, GSYM word_add_n2w, GSYM word_mul_n2w] )
  \\ conj_tac >- (
    irule IMP_word_list
    \\ fs[LENGTH_data, heap_size_def, bytes_in_word_def, memory_size_def]
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
      \\ simp[hello_init_memory_def]
      \\ fs[alignmentTheory.byte_align_def, alignmentTheory.align_w2n, word_add_n2w]
      \\ DEP_REWRITE_TAC[ADD_DIV_RWT] \\ simp[]
      \\ fs[alignmentTheory.byte_aligned_def, GSYM ALIGNED_eq_aligned, addressTheory.ALIGNED_n2w]
      \\ `4 * k DIV 4 = k` by (once_rewrite_tac[MULT_COMM] \\ simp[MULT_DIV] )
      \\ pop_assum SUBST_ALL_TAC
      \\ simp[LEFT_ADD_DISTRIB]
      \\ fs[MOD_EQ_0_DIVISOR]
      \\ `4 * d DIV 4 = d` by (once_rewrite_tac[MULT_COMM] \\ simp[MULT_DIV] )
      \\ pop_assum SUBST_ALL_TAC
      \\ simp[]
      \\ DEP_REWRITE_TAC[ADD_DIV_RWT] \\ simp[]
      \\ `4 * k DIV 4 = k` by (once_rewrite_tac[MULT_COMM] \\ simp[MULT_DIV] )
      \\ pop_assum SUBST_ALL_TAC
      \\ rewrite_tac[ADD_ASSOC]
      \\ simp[GSYM LEFT_ADD_DISTRIB]
      \\ `n2w (4 * (d + k)) :word32 = byte_align (n2w (4 * (d + k)))`
      by (
        simp[alignmentTheory.byte_align_def, GSYM alignmentTheory.aligned_def]
        \\ simp[GSYM ALIGNED_eq_aligned, addressTheory.ALIGNED_n2w] )
      \\ simp[GSYM word_add_n2w]
      \\ pop_assum SUBST_ALL_TAC
      \\ once_rewrite_tac[WORD_ADD_COMM]
      \\ DEP_REWRITE_TAC[data_to_word_memoryProofTheory.get_byte_byte_align]
      \\ conj_tac >- EVAL_TAC
      \\ simp[hello_init_memory_words_def,EL_APPEND_EQN,heap_size_def,LENGTH_data,
              LENGTH_words_of_bytes_hello_startup_code,LENGTH_hello_startup_code]
      \\ simp[data_to_word_memoryProofTheory.word_of_bytes_def]
      \\ simp[wordSemTheory.get_byte_def, wordSemTheory.byte_index_def,
              wordSemTheory.set_byte_def, wordSemTheory.word_slice_alt_def]
      \\ blastLib.BBLAST_TAC)
    \\ qmatch_asmsub_rename_tac`_ <=+ p`
    \\ Cases_on`p` \\ fs[word_ls_n2w,word_lo_n2w] \\ rfs[] \\ rw[]
    \\ qmatch_asmsub_rename_tac`_ <= q`
    \\ qmatch_asmsub_abbrev_tac`l ≤ q`
    \\ fs[LESS_EQ_EXISTS]
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
    \\ simp[Abbr`l`,GSYM word_add_n2w]
    \\ simp[word_add_n2w]
    \\ first_assum(qspec_then`4 * d + 0`mp_tac)
    \\ first_assum(qspec_then`4 * d + 1`mp_tac)
    \\ first_assum(qspec_then`4 * d + 2`mp_tac)
    \\ first_x_assum(qspec_then`4 * d + 3`mp_tac)
    \\ simp[]
    \\ rpt(disch_then kall_tac)
    \\ simp[GSYM word_add_n2w]
    \\ simp[hello_init_memory_def]
    \\ fs[alignmentTheory.byte_align_def, alignmentTheory.align_w2n, word_add_n2w]
    \\ DEP_REWRITE_TAC[ADD_DIV_RWT] \\ simp[]
    \\ fs[alignmentTheory.byte_aligned_def, GSYM ALIGNED_eq_aligned, addressTheory.ALIGNED_n2w]
    \\ `4 * d DIV 4 = d` by (once_rewrite_tac[MULT_COMM] \\ simp[MULT_DIV] )
    \\ pop_assum SUBST_ALL_TAC
    \\ simp[LEFT_ADD_DISTRIB]
    \\ fs[MOD_EQ_0_DIVISOR]
    \\ qmatch_goalsub_rename_tac`4 * k DIV 4`
    \\ `4 * k DIV 4 = k` by (once_rewrite_tac[MULT_COMM] \\ simp[MULT_DIV] )
    \\ pop_assum SUBST_ALL_TAC
    \\ simp[]
    \\ DEP_REWRITE_TAC[ADD_DIV_RWT] \\ simp[]
    \\ `4 * d DIV 4 = d` by (once_rewrite_tac[MULT_COMM] \\ simp[MULT_DIV] )
    \\ pop_assum SUBST_ALL_TAC
    \\ rewrite_tac[ADD_ASSOC]
    \\ simp[GSYM LEFT_ADD_DISTRIB]
    \\ `n2w (4 * (d + k)) :word32 = byte_align (n2w (4 * (d + k)))`
    by (
      simp[alignmentTheory.byte_align_def, GSYM alignmentTheory.aligned_def]
      \\ simp[GSYM ALIGNED_eq_aligned, addressTheory.ALIGNED_n2w] )
    \\ simp[GSYM word_add_n2w]
    \\ pop_assum SUBST_ALL_TAC
    \\ once_rewrite_tac[WORD_ADD_COMM]
    \\ DEP_REWRITE_TAC[data_to_word_memoryProofTheory.get_byte_byte_align]
    \\ conj_tac >- EVAL_TAC
    \\ simp[hello_init_memory_words_def,EL_APPEND_EQN,heap_size_def,LENGTH_data,
            LENGTH_words_of_bytes_hello_startup_code,LENGTH_hello_startup_code]
    \\ simp[data_to_word_memoryProofTheory.word_of_bytes_def]
    \\ simp[EL_MAP, LENGTH_data]
    \\ simp[wordSemTheory.get_byte_def, wordSemTheory.byte_index_def,
            wordSemTheory.set_byte_def, wordSemTheory.word_slice_alt_def]
    \\ blastLib.BBLAST_TAC)
  \\ EVAL_TAC
  \\ rewrite_tac[hello_ag32CompileTheory.config_def]
  \\ EVAL_TAC);

val hello_machine_sem =
  compile_correct_applied
  |> C MATCH_MP (UNDISCH lemma)
  |> DISCH_ALL
  |> curry save_thm "hello_machine_sem";

val hello_halted = Q.store_thm("hello_halted",
  `∀ms.
    byte_aligned r0 ∧ w2n r0 + memory_size < dimword (:32) ∧
    (mc = hello_machine_config r0) ∧
    (ms.PC = mc.halt_pc) ∧
    (∀x. r0 + n2w (heap_size + 4 * LENGTH data + 32) <=+ x ∧
         x <+ r0 + n2w (heap_size + 4 * LENGTH data + 36) ⇒
         (mc.target.get_byte ms x = (hello_init_memory r0) x)) ⇒
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
    \\ simp[hello_machine_config_def]
    \\ (alignmentTheory.aligned_add_sub_cor
        |> SPEC_ALL |> UNDISCH |> CONJUNCT1 |> DISCH_ALL
        |> irule)
    \\ fs[alignmentTheory.byte_aligned_def]
    \\ simp[LENGTH_data, heap_size_def, lab_to_targetTheory.ffi_offset_def]
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
    \\ simp[hello_machine_config_def]
    \\ simp[LENGTH_data,heap_size_def,lab_to_targetTheory.ffi_offset_def]
    \\ fs[word_add_n2w,word_ls_n2w,word_lo_n2w,memory_size_def])
  \\ first_assum(qspec_then`ms.PC + 1w`mp_tac)
  \\ impl_tac
  >- (
    simp[]
    \\ Cases_on`r0`
    \\ simp[hello_machine_config_def]
    \\ fs[word_add_n2w,word_ls_n2w,word_lo_n2w,memory_size_def,heap_size_def,LENGTH_data,lab_to_targetTheory.ffi_offset_def] )
  \\ first_assum(qspec_then`ms.PC + 2w`mp_tac)
  \\ impl_tac
  >- (
    simp[]
    \\ Cases_on`r0`
    \\ simp[hello_machine_config_def]
    \\ fs[word_add_n2w,word_ls_n2w,word_lo_n2w,memory_size_def,heap_size_def,LENGTH_data,lab_to_targetTheory.ffi_offset_def] )
  \\ first_x_assum(qspec_then`ms.PC + 3w`mp_tac)
  \\ impl_tac
  >- (
    simp[]
    \\ Cases_on`r0`
    \\ simp[hello_machine_config_def]
    \\ fs[word_add_n2w,word_ls_n2w,word_lo_n2w,memory_size_def,heap_size_def,LENGTH_data,lab_to_targetTheory.ffi_offset_def] )
  \\ simp[]
  \\ simp[EVAL``(hello_machine_config r0).target.get_byte``]
  \\ rpt (disch_then SUBST_ALL_TAC)
  \\ qmatch_goalsub_abbrev_tac`_ @@ hello_init_memory r0 pc`
  \\ drule hello_init_memory_halt
  \\ impl_tac
  >- ( simp[Abbr`pc`,hello_machine_config_def] )
  \\ simp[]
  \\ disch_then kall_tac
  \\ simp[ag32_targetProofTheory.Decode_Encode]
  \\ simp[ag32Theory.Run_def, ag32Theory.dfn'Jump_def]
  \\ simp[ag32Theory.ALU_def, ag32Theory.ri2word_def]
  \\ strip_tac
  \\ simp[Abbr`ms1`, APPLY_UPDATE_THM]);

val hello_ag32_next = Q.store_thm("hello_ag32_next",
  `byte_aligned r0 ∧ w2n r0 + memory_size < dimword (:32) ∧
   is_ag32_init_state (hello_init_memory r0) r0 ms0
  ⇒
   ∃k1. ∀k. k1 ≤ k ⇒
     let ms = FUNPOW Next k ms0 in
     let outs = MAP (λm. get_print_string (r0,m)) ms.io_events in
       (ms.PC = (hello_machine_config r0).halt_pc) ∧
       outs ≼ hello_outputs ∧
       ((ms.R (n2w (hello_machine_config r0).ptr_reg) = 0w) ⇒ (outs = hello_outputs))`,
  disch_then assume_tac
  \\ mp_tac hello_machine_sem
  \\ impl_tac >- fs[] \\ strip_tac
  \\ fs[extend_with_resource_limit_def]
  \\ qmatch_asmsub_abbrev_tac`machine_sem mc st ms`
  \\ `∃b. machine_sem mc st ms b` by metis_tac[machine_sem_total]
  \\ fs[SUBSET_DEF, IN_DEF]
  \\ first_x_assum drule
  \\ disch_then(assume_tac o ONCE_REWRITE_RULE[GSYM markerTheory.Abbrev_def])
  \\ `∃x y. b = Terminate x y` by fs[markerTheory.Abbrev_def] \\ rveq
  \\ first_x_assum(mp_then Any mp_tac (GEN_ALL machine_sem_Terminate_FUNPOW_next))
  \\ disch_then(qspecl_then[`{w | r0 <=+ w ∧ w <=+ r0 + n2w print_string_max_length}`,`ag32_ffi_rel r0`]mp_tac)
  \\ impl_tac >- (
    conj_tac
    >- (
      simp[interference_implemented_def, Abbr`mc`]
      \\ rewrite_tac[hello_machine_config_def, targetSemTheory.machine_config_accfupds]
      \\ simp_tac std_ss []
      \\ simp[EVAL``ag32_target.get_pc``,
              EVAL``ag32_target.get_reg``,
              EVAL``ag32_target.next``,
              EVAL``ag32_target.get_byte``]
      \\ qx_gen_tac`k0`
      \\ strip_tac
      \\ conj_tac
      >- (
        qmatch_goalsub_abbrev_tac`inmd ∧ encoded_bytes_in_mem _ pc m md ∧ _ ⇒ _`
        \\ `inmd ⇔ pc ∈ md` by ( simp[Abbr`inmd`,Abbr`md`] )
        \\ qpat_x_assum`Abbrev(inmd ⇔ _)`kall_tac
        \\ pop_assum SUBST_ALL_TAC
        \\ strip_tac
        \\ qexists_tac`0`
        \\ simp[]
        \\ simp[ag32_ffi_rel_def, FUN_EQ_THM]
        \\ qmatch_goalsub_abbrev_tac`ms1.io_events`
        \\ `(Next ms1).io_events = ms1.io_events` suffices_by rw[]
        \\ irule ag32_io_events_unchanged
        \\ simp[Abbr`ms1`]
        \\ `aligned 2 pc` by rfs[ag32_targetTheory.ag32_target_def, ag32_targetTheory.ag32_ok_def]
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
        \\ fs[EVAL``ag32_target.config.code_alignment``]
        \\ fs[EVAL``ag32_target.config.encode``]
        \\ `4 ≤ LENGTH (DROP (4 * k) (ag32_enc i))` by (
          qspec_then`i`mp_tac(Q.GEN`istr`ag32_enc_lengths)
          \\ simp[]
          \\ strip_tac \\ fs[]
          \\ Cases_on`k` \\ fs[]
          \\ Cases_on`n` \\ fs[]
          \\ Cases_on`n'` \\ fs[] )
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
        pop_assum mp_tac
        \\ simp[LENGTH_data,LENGTH_code,heap_size_def,lab_to_targetTheory.ffi_offset_def,
                ag32Theory.print_string_max_length_def]
        \\ ntac 2 strip_tac
        \\ qexists_tac`1`
        \\ simp[]
        \\ conj_asm1_tac
        >- (
          simp[ag32Theory.Next_def]
          \\ qmatch_goalsub_abbrev_tac`pc' + 2w`
          \\ qmatch_asmsub_abbrev_tac`_.PC = pc`
          \\ `aligned 2 pc`
          by (
            simp[Abbr`pc`]
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
            \\ Cases_on`r0`
            \\ fs[word_add_n2w,word_ls_n2w,word_lo_n2w,memory_size_def] )
          \\ first_assum(qspec_then`pc + 1w`mp_tac)
          \\ impl_tac
          >- (
            simp[Abbr`pc`]
            \\ Cases_on`r0`
            \\ fs[word_add_n2w,word_ls_n2w,word_lo_n2w,memory_size_def] )
          \\ first_assum(qspec_then`pc + 2w`mp_tac)
          \\ impl_tac
          >- (
            simp[Abbr`pc`]
            \\ Cases_on`r0`
            \\ fs[word_add_n2w,word_ls_n2w,word_lo_n2w,memory_size_def] )
          \\ first_assum(qspec_then`pc + 3w`mp_tac)
          \\ impl_tac
          >- (
            simp[Abbr`pc`]
            \\ Cases_on`r0`
            \\ fs[word_add_n2w,word_ls_n2w,word_lo_n2w,memory_size_def] )
          \\ simp[]
          \\ ntac 4 (disch_then kall_tac)
          \\ drule hello_startup_clock_def
          \\ simp[]
          \\ disch_then drule
          \\ strip_tac
          \\ first_assum(qspec_then`pc`mp_tac)
          \\ impl_tac
          >- (
            simp[Abbr`pc`, hello_machine_config_def, heap_size_def,
                 LENGTH_data, LENGTH_code, lab_to_targetTheory.ffi_offset_def]
            \\ Cases_on`r0`
            \\ fs[word_add_n2w,word_ls_n2w,word_lo_n2w,memory_size_def] )
          \\ first_assum(qspec_then`pc + 1w`mp_tac)
          \\ impl_tac
          >- (
            simp[Abbr`pc`, hello_machine_config_def, heap_size_def,
                 LENGTH_data, LENGTH_code, lab_to_targetTheory.ffi_offset_def]
            \\ Cases_on`r0`
            \\ fs[word_add_n2w,word_ls_n2w,word_lo_n2w,memory_size_def] )
          \\ first_assum(qspec_then`pc + 2w`mp_tac)
          \\ impl_tac
          >- (
            simp[Abbr`pc`, hello_machine_config_def, heap_size_def,
                 LENGTH_data, LENGTH_code, lab_to_targetTheory.ffi_offset_def]
            \\ Cases_on`r0`
            \\ fs[word_add_n2w,word_ls_n2w,word_lo_n2w,memory_size_def] )
          \\ first_assum(qspec_then`pc + 3w`mp_tac)
          \\ impl_tac
          >- (
            simp[Abbr`pc`, hello_machine_config_def, heap_size_def,
                 LENGTH_data, LENGTH_code, lab_to_targetTheory.ffi_offset_def]
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
          \\ simp[Abbr`pc`]
          \\ simp[ag32Theory.ri2word_def])
        \\ pop_assum(SUBST_ALL_TAC o SYM)
        \\ conj_tac >- simp[ag32_ffi_rel_def,FUN_EQ_THM]
        \\ simp[] )
      \\ rpt gen_tac
      \\ strip_tac
      \\ fs[lab_to_targetTheory.ffi_offset_def, heap_size_def,
            LENGTH_data, LENGTH_code, LENGTH_hello_ag32_ffi_code,
            ag32Theory.print_string_max_length_def]
      \\ qmatch_goalsub_abbrev_tac`read_bytearray r1 r2 m`
      \\ `read_bytearray r1 r2 m = SOME bytes`
      by (
        fs[targetSemTheory.read_ffi_bytearrays_def]
        \\ fs[targetSemTheory.read_ffi_bytearray_def]
        \\ fs[EVAL``ag32_target.get_reg``]
        \\ fs[EVAL``ag32_target.get_byte``]
        \\ fsrw_tac[ETA_ss][] )
      \\ simp[]
      \\ simp[Once EXISTS_NUM]
      \\ disj2_tac
      \\ simp[FUNPOW]
      \\ fs[find_index_def]
      \\ qpat_x_assum`_ = _.PC`(assume_tac o SYM)
      \\ qmatch_asmsub_abbrev_tac`_.PC = pc`
      \\ simp[ag32Theory.Next_def]
      \\ qmatch_goalsub_abbrev_tac`pc' + 2w`
      \\ `aligned 2 pc`
      by (
        simp[Abbr`pc`]
        \\ (alignmentTheory.aligned_add_sub_cor
            |> SPEC_ALL |> UNDISCH |> CONJUNCT1 |> DISCH_ALL
            |> irule)
        \\ fs[alignmentTheory.byte_aligned_def]
        \\ EVAL_TAC )
      \\ `pc = pc'`
      by (
        pop_assum mp_tac
        \\ unabbrev_all_tac
        \\ rveq
        \\ simp[alignmentTheory.aligned_extract]
        \\ blastLib.BBLAST_TAC )
      \\ qpat_x_assum`Abbrev(pc' = _)` kall_tac
      \\ pop_assum (SUBST_ALL_TAC o SYM)
      \\ EVERY(List.tabulate(4, (fn i =>
        first_assum(qspec_then`pc + n2w ^(numSyntax.term_of_int i)`mp_tac)
        \\ impl_tac
        >- (
          simp[Abbr`pc`]
          \\ Cases_on`r0`
          \\ fs[word_add_n2w,word_ls_n2w,word_lo_n2w,memory_size_def] ))))
      \\ simp[]
      \\ ntac 4 (disch_then kall_tac)
      \\ drule hello_startup_clock_def
      \\ simp[]
      \\ disch_then drule
      \\ strip_tac
      \\ EVERY(List.tabulate(4, (fn i =>
        first_assum(qspec_then`pc + n2w ^(numSyntax.term_of_int i)`mp_tac)
        \\ impl_tac
        >- (
          simp[Abbr`pc`, hello_machine_config_def, heap_size_def,
               LENGTH_data, LENGTH_code, lab_to_targetTheory.ffi_offset_def]
          \\ Cases_on`r0`
          \\ fs[word_add_n2w,word_ls_n2w,word_lo_n2w,memory_size_def] ))))
      \\ simp[]
      \\ ntac 4 (disch_then kall_tac)
      \\ `ms0.MEM = hello_init_memory r0`
      by ( fs[is_ag32_init_state_def] )
      \\ simp[]
      \\ DEP_REWRITE_TAC[hello_init_memory_ffi_00]
      \\ conj_tac >- ( simp[Abbr`pc`, LENGTH_data] \\ EVAL_TAC )
      \\ simp[ag32_targetProofTheory.Decode_Encode]
      \\ simp[LENGTH_code]
      \\ qmatch_goalsub_abbrev_tac`_ = FUNPOW Next _ ss`
      \\ pop_assum mp_tac
      \\ simp[ag32Theory.Run_def]
      \\ simp[ag32Theory.dfn'LoadConstant_def, ag32Theory.incPC_def]
      \\ strip_tac \\ simp[Abbr`ss`]
      \\ simp[Abbr`pc`]
      \\ simp[Once EXISTS_NUM]
      \\ disj2_tac
      \\ simp[FUNPOW]
      \\ simp[ag32Theory.Next_def]
      \\ qmatch_goalsub_abbrev_tac`pc' + 2w`
      \\ qmatch_goalsub_abbrev_tac`_ with PC := r0 + offset`
      \\ `aligned 2 (r0 + offset)`
      by (
        simp[Abbr`offset`]
        \\ (alignmentTheory.aligned_add_sub_cor
            |> SPEC_ALL |> UNDISCH |> CONJUNCT1 |> DISCH_ALL
            |> irule)
        \\ fs[alignmentTheory.byte_aligned_def]
        \\ EVAL_TAC )
      \\ `pc' = r0 + offset`
      by (
        simp[Abbr`pc'`,Abbr`offset`]
        \\ rveq
        \\ pop_assum mp_tac
        \\ simp[alignmentTheory.aligned_extract]
        \\ blastLib.BBLAST_TAC )
      \\ qpat_x_assum`Abbrev(pc' = _)`kall_tac
      \\ pop_assum SUBST_ALL_TAC
      \\ qunabbrev_tac`offset`
      \\ qmatch_goalsub_abbrev_tac`pc + 2w`
      \\ EVERY(List.tabulate(4, (fn i =>
        last_assum(qspec_then`pc + n2w ^(numSyntax.term_of_int i)`mp_tac)
        \\ impl_tac
        >- (
          simp[Abbr`pc`]
          \\ Cases_on`r0`
          \\ fs[word_add_n2w,word_ls_n2w,word_lo_n2w,memory_size_def] ))))
      \\ simp[]
      \\ ntac 4 (disch_then kall_tac)
      \\ EVERY(List.tabulate(4, (fn i =>
        first_assum(qspec_then`pc + n2w ^(numSyntax.term_of_int i)`mp_tac)
        \\ impl_tac
        >- (
          simp[Abbr`pc`, hello_machine_config_def, heap_size_def,
               LENGTH_data, LENGTH_code, lab_to_targetTheory.ffi_offset_def]
          \\ Cases_on`r0`
          \\ fs[word_add_n2w,word_ls_n2w,word_lo_n2w,memory_size_def] ))))
      \\ simp[]
      \\ ntac 4 (disch_then kall_tac)
      \\ DEP_REWRITE_TAC[hello_init_memory_ffi_01]
      \\ conj_tac >- ( simp[Abbr`pc`, LENGTH_data] \\ EVAL_TAC )
      \\ simp[ag32_targetProofTheory.Decode_Encode]
      \\ qmatch_goalsub_abbrev_tac`_ = FUNPOW Next _ ss`
      \\ pop_assum mp_tac
      \\ simp[ag32Theory.Run_def]
      \\ rveq
      \\ simp[ag32Theory.dfn'Normal_def,ag32Theory.norm_def,ag32Theory.incPC_def,ag32Theory.ALU_def,ag32Theory.ri2word_def]
      \\ qmatch_goalsub_abbrev_tac`_ with OverflowFlag := ov`
      \\ `ov = F`
      by ( simp[Abbr`ov`] \\ EVAL_TAC )
      \\ qpat_x_assum`Abbrev(ov = _)`kall_tac
      \\ pop_assum SUBST_ALL_TAC
      \\ strip_tac \\ simp[Abbr`ss`]
      \\ simp[Abbr`pc`]
      \\ simp[Once EXISTS_NUM]
      \\ disj2_tac
      \\ simp[FUNPOW]
      \\ simp[ag32Theory.Next_def]
      \\ qmatch_goalsub_abbrev_tac`pc' + 2w`
      \\ qmatch_goalsub_abbrev_tac`_ with PC := r0 + offset`
      \\ `aligned 2 (r0 + offset)`
      by (
        simp[Abbr`offset`]
        \\ (alignmentTheory.aligned_add_sub_cor
            |> SPEC_ALL |> UNDISCH |> CONJUNCT1 |> DISCH_ALL
            |> irule)
        \\ fs[alignmentTheory.byte_aligned_def]
        \\ EVAL_TAC )
      \\ `pc' = r0 + offset`
      by (
        simp[Abbr`pc'`,Abbr`offset`]
        \\ rveq
        \\ pop_assum mp_tac
        \\ simp[alignmentTheory.aligned_extract]
        \\ blastLib.BBLAST_TAC )
      \\ qpat_x_assum`Abbrev(pc' = _)`kall_tac
      \\ pop_assum SUBST_ALL_TAC
      \\ qunabbrev_tac`offset`
      \\ qmatch_goalsub_abbrev_tac`pc + 2w`
      \\ EVERY(List.tabulate(4, (fn i =>
        last_assum(qspec_then`pc + n2w ^(numSyntax.term_of_int i)`mp_tac)
        \\ impl_tac
        >- (
          simp[Abbr`pc`]
          \\ Cases_on`r0`
          \\ fs[word_add_n2w,word_ls_n2w,word_lo_n2w,memory_size_def] ))))
      \\ simp[]
      \\ ntac 4 (disch_then kall_tac)
      \\ EVERY(List.tabulate(4, (fn i =>
        first_assum(qspec_then`pc + n2w ^(numSyntax.term_of_int i)`mp_tac)
        \\ impl_tac
        >- (
          simp[Abbr`pc`, hello_machine_config_def, heap_size_def,
               LENGTH_data, LENGTH_code, lab_to_targetTheory.ffi_offset_def]
          \\ Cases_on`r0`
          \\ fs[word_add_n2w,word_ls_n2w,word_lo_n2w,memory_size_def] ))))
      \\ simp[]
      \\ ntac 4 (disch_then kall_tac)
      \\ DEP_REWRITE_TAC[hello_init_memory_ffi_02]
      \\ conj_tac >- ( simp[Abbr`pc`, LENGTH_data] \\ EVAL_TAC )
      \\ simp[ag32_targetProofTheory.Decode_Encode]
      \\ simp[ag32Theory.Run_def]
      \\ simp[ag32Theory.dfn'Jump_def,ag32Theory.ALU_def,ag32Theory.ri2word_def]
      \\ simp[Abbr`pc`]
      \\ simp[APPLY_UPDATE_THM]
      \\ qmatch_goalsub_abbrev_tac`_ with CarryFlag := cv`
      \\ `cv = F`
      by ( simp[Abbr`cv`] \\ Cases_on`r0` \\ fs[word_add_n2w,memory_size_def] )
      \\ qpat_x_assum`Abbrev(cv = _)`kall_tac
      \\ pop_assum SUBST_ALL_TAC
      \\ qmatch_goalsub_abbrev_tac`_ = FUNPOW Next _ ss`
      \\ first_assum(mp_then Any mp_tac read_bytearray_IMP_bytes_in_memory)
      \\ qhdtm_x_assum`call_FFI`mp_tac
      \\ simp[ffiTheory.call_FFI_def]
      \\ simp[Abbr`st`]
      \\ simp[EVAL``ag_ffi``]
      \\ simp[CaseEq"bool",CaseEq"option",CaseEq"oracle_result",NULL_EQ]
      \\ strip_tac \\ rveq
      \\ imp_res_tac read_bytearray_LENGTH
      \\ simp[]
      \\ disch_then(qspecl_then[`ss.MEM`,`{w | r1 <=+ w ∧ w <+ r1 + n2w r2}`]mp_tac)
      \\ impl_tac
      >- (
        reverse conj_asm2_tac
        >- (
          Cases
          \\ Cases_on`r1`
          \\ Cases_on`r0`
          \\ simp[word_add_n2w,word_lo_n2w,word_ls_n2w,Abbr`m`,Abbr`ss`]
          \\ fs[memory_size_def]
          \\ drule read_bytearray_IMP_mem_SOME
          \\ simp[word_add_n2w]
          \\ disch_then(qspec_then`n2w n`mp_tac)
          \\ simp[word_lo_n2w,word_ls_n2w,IS_SOME_EXISTS] )
        \\ Cases_on`r1` \\ fs[word_add_n2w]
        \\ Cases_on`r2` \\ fs[]
        \\ Cases_on`bytes` \\ fs[]
        \\ fs[read_bytearray_def]
        \\ fs[CaseEq"option"]
        \\ qpat_x_assum`m _ = _`mp_tac
        \\ simp[Abbr`m`]
        \\ Cases_on`r0`
        \\ fs[word_add_n2w, memory_size_def,word_ls_n2w, word_lo_n2w] )
      \\ `r1 = ss.R 1w` by simp[Abbr`ss`,APPLY_UPDATE_THM]
      \\ pop_assum SUBST1_TAC
      \\ strip_tac
      \\ first_assum(mp_then Any mp_tac hello_ag32_ffi_code_correct)
      \\ impl_tac
      >- (
        simp[Abbr`ss`,APPLY_UPDATE_THM]
        \\ conj_tac
        >- (
          ntac 2 strip_tac
          \\ qmatch_goalsub_abbrev_tac`_.MEM pc`
          \\ last_assum(qspec_then`pc`mp_tac)
          \\ impl_tac
          >- (
            simp[Abbr`pc`]
            \\ fs[LENGTH_hello_ag32_ffi_code]
            \\ Cases_on`r0` \\ fs[word_add_n2w]
            \\ fs[word_ls_n2w,word_lo_n2w,memory_size_def] )
          \\ disch_then SUBST_ALL_TAC
          \\ qunabbrev_tac`pc`
          \\ qmatch_goalsub_abbrev_tac`(FUNPOW _ _ _).MEM pc`
          \\ last_assum(qspec_then`pc`mp_tac)
          \\ impl_tac
          >- (
            simp[Abbr`pc`]
            \\ fs[LENGTH_hello_ag32_ffi_code]
            \\ Cases_on`r0` \\ fs[word_add_n2w]
            \\ fs[word_ls_n2w,word_lo_n2w,memory_size_def] )
          \\ disch_then SUBST_ALL_TAC
          \\ qunabbrev_tac`pc`
          \\ qmatch_goalsub_abbrev_tac`(FUNPOW _ _ _).MEM pc`
          \\ last_assum(qspec_then`pc`mp_tac)
          \\ impl_tac
          >- (
            simp[Abbr`pc`]
            \\ fs[LENGTH_hello_ag32_ffi_code]
            \\ Cases_on`r0` \\ fs[word_add_n2w]
            \\ fs[word_ls_n2w,word_lo_n2w,memory_size_def] )
          \\ disch_then SUBST_ALL_TAC
          \\ qunabbrev_tac`pc`
          \\ qmatch_goalsub_abbrev_tac`(FUNPOW _ _ _).MEM pc`
          \\ last_assum(qspec_then`pc`mp_tac)
          \\ impl_tac
          >- (
            simp[Abbr`pc`]
            \\ fs[LENGTH_hello_ag32_ffi_code]
            \\ Cases_on`r0` \\ fs[word_add_n2w]
            \\ fs[word_ls_n2w,word_lo_n2w,memory_size_def] )
          \\ disch_then SUBST_ALL_TAC
          \\ qunabbrev_tac`pc`
          \\ qmatch_goalsub_abbrev_tac`_.MEM pc`
          \\ first_assum(qspec_then`pc`mp_tac)
          \\ impl_tac
          >- (
            simp[Abbr`pc`,hello_machine_config_def,heap_size_def,
                 LENGTH_code,LENGTH_data,lab_to_targetTheory.ffi_offset_def]
            \\ fs[LENGTH_hello_ag32_ffi_code]
            \\ Cases_on`r0` \\ fs[word_add_n2w]
            \\ fs[word_ls_n2w,word_lo_n2w,memory_size_def] )
          \\ simp[] \\ disch_then kall_tac
          \\ qunabbrev_tac`pc`
          \\ qmatch_goalsub_abbrev_tac`_.MEM pc`
          \\ first_assum(qspec_then`pc`mp_tac)
          \\ impl_tac
          >- (
            simp[Abbr`pc`,hello_machine_config_def,heap_size_def,
                 LENGTH_code,LENGTH_data,lab_to_targetTheory.ffi_offset_def]
            \\ fs[LENGTH_hello_ag32_ffi_code]
            \\ Cases_on`r0` \\ fs[word_add_n2w]
            \\ fs[word_ls_n2w,word_lo_n2w,memory_size_def] )
          \\ simp[] \\ disch_then kall_tac
          \\ qunabbrev_tac`pc`
          \\ qmatch_goalsub_abbrev_tac`_.MEM pc`
          \\ first_assum(qspec_then`pc`mp_tac)
          \\ impl_tac
          >- (
            simp[Abbr`pc`,hello_machine_config_def,heap_size_def,
                 LENGTH_code,LENGTH_data,lab_to_targetTheory.ffi_offset_def]
            \\ fs[LENGTH_hello_ag32_ffi_code]
            \\ Cases_on`r0` \\ fs[word_add_n2w]
            \\ fs[word_ls_n2w,word_lo_n2w,memory_size_def] )
          \\ simp[] \\ disch_then kall_tac
          \\ qunabbrev_tac`pc`
          \\ qmatch_goalsub_abbrev_tac`_.MEM pc`
          \\ first_assum(qspec_then`pc`mp_tac)
          \\ impl_tac
          >- (
            simp[Abbr`pc`,hello_machine_config_def,heap_size_def,
                 LENGTH_code,LENGTH_data,lab_to_targetTheory.ffi_offset_def]
            \\ fs[LENGTH_hello_ag32_ffi_code]
            \\ Cases_on`r0` \\ fs[word_add_n2w]
            \\ fs[word_ls_n2w,word_lo_n2w,memory_size_def] )
          \\ simp[] \\ disch_then kall_tac
          \\ qunabbrev_tac`pc`
          \\ match_mp_tac (
            hello_init_memory_ffi
            |> SIMP_RULE(srw_ss())
                 [LENGTH_data,heap_size_def,LENGTH_code,
                  lab_to_targetTheory.ffi_offset_def,GSYM word_add_n2w]
            |> GEN_ALL)
          \\ simp[] )
        \\ conj_tac
        >- (
          match_mp_tac byte_aligned_add
          \\ fs[] \\ EVAL_TAC )
        \\ simp[heap_size_def,LENGTH_data,LENGTH_hello_ag32_ffi_code]
        \\ simp[ag32Theory.print_string_max_length_def]
        \\ Cases_on`r0` \\ fs[memory_size_def,word_add_n2w]
        \\ fs[Abbr`r2`]
        \\ qmatch_asmsub_abbrev_tac`read_bytearray r1 (w2n len)`
        \\ simp[GSYM word_add_n2w]
        \\ Cases_on`len` \\ Cases_on`r1` \\ simp[word_add_n2w]
        \\ conj_tac
        >- (
          Cases
          \\ simp[word_ls_n2w, word_lo_n2w]
          \\ fs[]
          \\ Cases_on`bytes` \\ fs[]
          \\ rveq
          \\ fs[read_bytearray_def]
          \\ fs[CaseEq"option"]
          \\ qpat_x_assum`m _ = _`mp_tac
          \\ simp[Abbr`m`, word_lo_n2w, word_ls_n2w] )
        \\ fs[]
        \\ Cases_on`bytes` \\ fs[]
        \\ rveq
        \\ fs[read_bytearray_def]
        \\ fs[CaseEq"option"]
        \\ qpat_x_assum`m _ = _`mp_tac
        \\ simp[Abbr`m`, word_lo_n2w, word_ls_n2w] )
      \\ first_assum(mp_then Any mp_tac (GEN_ALL hello_ag32_ffi_spec))
      \\ disch_then(qspec_then`r0`mp_tac)
      \\ impl_tac
      >- (
        simp[Abbr`ss`,APPLY_UPDATE_THM,LENGTH_data,heap_size_def]
        \\ conj_tac >- simp[Abbr`r2`]
        \\ Cases_on`r0` \\ Cases_on`r1` \\ simp[]
        \\ fs[memory_size_def, word_add_n2w]
        \\ conj_tac
        >- (
          Cases
          \\ fs[word_ls_n2w, word_lo_n2w]
          \\ Cases_on`r2` \\ fs[read_bytearray_def]
          \\ fs[CaseEq"option"]
          \\ qpat_x_assum`m _ = _`mp_tac
          \\ simp[Abbr`m`]
          \\ simp[word_ls_n2w,word_lo_n2w] )
        \\ Cases_on`r2` \\ fs[read_bytearray_def]
        \\ fs[CaseEq"option"]
        \\ qpat_x_assum`m _ = _`mp_tac \\ simp[Abbr`m`]
        \\ simp[word_ls_n2w,word_lo_n2w] )
      \\ rw[]
      \\ qexists_tac`k` \\ simp[Abbr`ss`]
      \\ conj_tac
      >- (
        simp[APPLY_UPDATE_THM]
        \\ simp[ag32Theory.ag32_state_component_equality]
        \\ Cases_on`r0` \\ fs[memory_size_def,word_add_n2w]
        \\ simp[FUN_EQ_THM,APPLY_UPDATE_THM]
        \\ qpat_x_assum`Abbrev(LENGTH _ = _ )`mp_tac
        \\ simp[markerTheory.Abbrev_def]
        \\ Cases_on`(FUNPOW Next k0 ms).R 2w`
        \\ simp[word_add_n2w]
        \\ simp[lab_to_targetProofTheory.asm_write_bytearray_def,APPLY_UPDATE_THM]
        \\ rw[] \\ rw[]
        \\ simp[w2w_n2w])
      \\ conj_tac
      >- (
        qhdtm_x_assum`ag32_ffi_rel`mp_tac
        \\ simp[ag32_ffi_rel_def]
        \\ simp[extract_print_from_mem_def,MAP_MAP_o,n2w_ORD_CHR_w2n]
        \\ simp[lab_to_targetProofTheory.asm_write_bytearray_def,APPLY_UPDATE_THM]
        \\ simp[ag32Theory.print_string_max_length_def]
        \\ strip_tac
        \\ simp[LIST_EQ_REWRITE]
        \\ gen_tac \\ strip_tac
        \\ IF_CASES_TAC
        >- ( fs[addressTheory.WORD_EQ_ADD_CANCEL] \\ rfs[] )
        \\ qmatch_goalsub_rename_tac`r0 + n2w (n + 1)`
        \\ `r0 + n2w (n + 1) = r0 + 1w + n2w n` by simp[GSYM word_add_n2w]
        \\ pop_assum SUBST_ALL_TAC
        \\ match_mp_tac EQ_SYM
        \\ match_mp_tac asm_write_bytearray_EL
        \\ simp[])
      \\ Cases
      \\ disch_then assume_tac
      \\ simp[lab_to_targetProofTheory.asm_write_bytearray_def, APPLY_UPDATE_THM]
      \\ IF_CASES_TAC
      >- (
        Cases_on`r0` \\ rw[] \\ fs[memory_size_def, word_ls_n2w, word_lo_n2w, word_add_n2w] \\ rfs[] )
      \\ match_mp_tac asm_write_bytearray_unchanged
      \\ simp[]
      \\ ntac 2(pop_assum mp_tac)
      \\ Cases_on`r0` \\ fs[memory_size_def]
      \\ fs[word_add_n2w, word_ls_n2w, word_lo_n2w])
    \\ simp[ag32_ffi_rel_def,Abbr`st`]
    \\ CONV_TAC(PATH_CONV"rl" EVAL)
    \\ simp[]
    \\ simp[Abbr`ms`]
    \\ drule hello_startup_clock_def
    \\ simp[]
    \\ fs[is_ag32_init_state_def])
  \\ strip_tac
  \\ drule hello_halted
  \\ simp[]
  \\ disch_then(qspec_then`FUNPOW Next k ms`mp_tac)
  \\ strip_tac
  \\ qexists_tac`k + hello_startup_clock r0 ms0`
  \\ qx_gen_tac`k2` \\ strip_tac
  \\ first_x_assum(qspec_then`k2-k-(hello_startup_clock r0 ms0)`mp_tac)
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
    \\ impl_tac >- fs[]
    \\ strip_tac
    \\ fs[EVAL``(hello_machine_config r0).target.get_byte``]
    \\ fs[ag32_targetTheory.is_ag32_init_state_def] \\ rfs[]
    \\ rw[]
    \\ first_x_assum irule
    \\ qmatch_goalsub_rename_tac`z ∉ _`
    \\ Cases_on`r0` \\ Cases_on`z` \\ fs[word_add_n2w, word_ls_n2w, word_lo_n2w, heap_size_def, LENGTH_data]
    \\ EVAL_TAC
    \\ fs[LENGTH_data, ag32Theory.print_string_max_length_def, LENGTH_code]
    \\ fs[word_ls_n2w, word_lo_n2w]
    \\ fs[memory_size_def] \\ rfs[] )
  \\ fs[GSYM FUNPOW_ADD, Abbr`ms`]
  \\ strip_tac
  \\ fs[Abbr`mc`,FUNPOW_ADD,hello_machine_config_def,EVAL``ag32_target.next``]
  \\ fs[EVAL``ag32_target.get_pc``]
  \\ fs[EVAL``ag32_target.get_reg``]
  \\ imp_res_tac ag32_ffi_rel_get_print_string
  \\ unabbrev_all_tac \\ fs[] \\ rveq \\ fs[]
  \\ rveq \\ fs[IS_PREFIX_APPEND]
  \\ first_x_assum(mp_tac o Q.AP_TERM`MAP (MAP (CHR o w2n) o FST o SND o dest_IO_event)`)
  \\ simp[MAP_MAP_o, Once o_DEF, CHR_w2n_n2w_ORD]
  \\ simp[Once o_DEF, MAP_MAP_o, CHR_w2n_n2w_ORD]
  \\ simp[Once o_DEF, MAP_MAP_o, CHR_w2n_n2w_ORD]
  \\ srw_tac[ETA_ss][]
  \\ simp[Once o_DEF, MAP_MAP_o, CHR_w2n_n2w_ORD]
  \\ srw_tac[ETA_ss][]);

*)

val _ = export_theory();
