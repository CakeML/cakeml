(*
  Verify that the ag32 implementation of the FFI primitives satisfies
  interference_implemented.
*)
open preamble
  ag32_memoryTheory
  ag32_machine_configTheory
  ag32_ffi_codeProofTheory
  ag32_memoryProofTheory
local open blastLib basis_ffiTheory in end

val _ = new_theory"ag32_basis_ffiProof";

(* TODO: move *)

Theorem INDEX_OF_IMP_EL:
   !xs x index. (INDEX_OF x xs = SOME index) ==> (EL index xs = x)
Proof
  rw [GSYM find_index_INDEX_OF]
  \\ imp_res_tac find_index_LESS_LENGTH \\ fs[]
  \\ imp_res_tac find_index_is_MEM
  \\ imp_res_tac find_index_MEM
  \\ first_x_assum (qspec_then `0` mp_tac)
  \\ fs []
QED

Theorem INDEX_OF_REVERSE:
   ALL_DISTINCT ls ⇒
   INDEX_OF x (REVERSE ls) = OPTION_MAP (λn. LENGTH ls - 1 - n) (INDEX_OF x ls)
Proof
  rw[GSYM find_index_INDEX_OF]
  \\ Cases_on`find_index x ls 0`
  >- ( fs[GSYM find_index_NOT_MEM] )
  \\ imp_res_tac find_index_ALL_DISTINCT_REVERSE
  \\ fs[]
QED

Theorem bytes_in_memory_UPDATE_GT:
    k <+ (pc:word32) ∧
  LENGTH ls <= 2**31 ∧
  ¬word_msb pc ∧
  bytes_in_memory pc ls m dm ⇒
  bytes_in_memory pc ls ((k =+ v)m) dm
Proof
  rw[]>>
  match_mp_tac bytes_in_memory_change_mem>>
  asm_exists_tac>>fs[APPLY_UPDATE_THM]>>
  ntac 2 strip_tac>>
  `k <+ pc + n2w n` by
    (match_mp_tac WORD_LOWER_LOWER_EQ_TRANS>>
    asm_exists_tac>>fs[]>>
    fs[WORD_LS]>>
    DEP_REWRITE_TAC [w2n_add]>>
    fs[word_msb_n2w_numeric])>>
  rw[]>>fs[WORD_LOWER_REFL]
QED

Theorem bytes_in_memory_UPDATE_LT:
    (w2n pc + (LENGTH ls) <= w2n (k:word32)) ∧
  LENGTH ls <= 2**31 ∧
  ¬word_msb pc ∧
  bytes_in_memory pc ls m dm ⇒
  bytes_in_memory pc ls ((k =+ v)m) dm
Proof
  rw[]>>
  match_mp_tac bytes_in_memory_change_mem>>
  asm_exists_tac>>fs[APPLY_UPDATE_THM]>>
  ntac 2 strip_tac>>
  `n + w2n pc < w2n k` by fs[]>>
  rw[]>>
  CCONTR_TAC>> pop_assum kall_tac>>
  pop_assum mp_tac>>
  DEP_REWRITE_TAC [w2n_add]>>
  fs[word_msb_n2w_numeric]
QED

Theorem bytes_in_memory_asm_write_bytearray_LT:
    (w2n pc + (LENGTH ls) <= w2n (k:word32)) ∧
  (w2n k + (LENGTH bs) < dimword(:32))∧
  LENGTH ls <= 2**31 ∧
  ¬word_msb pc ∧
  bytes_in_memory pc ls m dm ⇒
  bytes_in_memory pc ls (asm_write_bytearray k bs m) dm
Proof
  rw[]>>
  match_mp_tac bytes_in_memory_change_mem>>
  asm_exists_tac>>fs[APPLY_UPDATE_THM]>>
  ntac 2 strip_tac>>
  `n + w2n pc < w2n k` by fs[]>>
  rw[]>>
  match_mp_tac EQ_SYM>>
  match_mp_tac asm_write_bytearray_unchanged>>
  simp[]>>
  DISJ1_TAC>>simp[WORD_LO]>>
  DEP_REWRITE_TAC [w2n_add]>>
  fs[word_msb_n2w_numeric]
QED

Theorem asm_write_bytearray_UPDATE:
    x ≠ pc ⇒
  asm_write_bytearray a ls ((pc =+ v) m) x =
  asm_write_bytearray a ls m x
Proof
  rw[]>>
  match_mp_tac mem_eq_imp_asm_write_bytearray_eq >>
  fs[APPLY_UPDATE_THM]
QED

Theorem set_mem_word_asm_write_bytearray_commute_LT:
    (pc <+ a) ∧
  (pc+1w <+ a) ∧
  (pc+2w <+ a) ∧
  (pc+3w <+ a) ∧
  w2n a + LENGTH ls < dimword(:32)
  ⇒
  set_mem_word pc w
    (asm_write_bytearray a ls m) =
  asm_write_bytearray a ls (set_mem_word pc w m)
Proof
  rw[FUN_EQ_THM]>>
  imp_res_tac asm_write_bytearray_unchanged>>
  fs[set_mem_word_def]>>
  simp[APPLY_UPDATE_THM]>>
  rw[]>>fs[APPLY_UPDATE_THM]>>
  metis_tac[asm_write_bytearray_UPDATE]
QED

Theorem asm_write_bytearray_append2:
   ∀a l1 l2 m.
   (asm_write_bytearray (a:word32) (l1 ++ l2) m =
    asm_write_bytearray a l1 (asm_write_bytearray (a + n2w (LENGTH l1)) l2 m))
Proof
  Induct_on`l1` \\ rw[asm_write_bytearray_def]
  \\ AP_TERM_TAC
  \\ fs[ADD1,GSYM word_add_n2w]
QED

val _ = temp_overload_on("nxt",
  ``λmc n ms. FUNPOW mc.target.next n ms``);

val interference_implemented_def = Define`
  interference_implemented mc ffi_rel md ms0 ⇔
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
       (∀x. x ∉ mc.prog_addresses ⇒ (mc.target.get_byte (mc.target.next ms) x = mc.target.get_byte ms x)) ∧
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
          (find_index (mc.target.get_pc ms) mc.ffi_entry_pcs 0 = SOME ffi_index) ∧
          (read_ffi_bytearrays mc ms = (SOME bytes, SOME bytes2)) ∧
          (call_FFI ffi (EL ffi_index mc.ffi_names) bytes bytes2 =
            FFI_return new_ffi new_bytes) ∧
          (ffi_rel ms ffi)
          ⇒
          ∃k.
            (ffi_interfer (ffi_index,new_bytes,ms) =
             FUNPOW mc.target.next k ms) ∧
            (ffi_rel (FUNPOW mc.target.next k ms) new_ffi) ∧
            (∀x. x ∉ md ∧
                 x ∉ all_words (mc.target.get_reg ms mc.ptr2_reg) (LENGTH bytes2) ⇒
              (mc.target.get_byte (FUNPOW mc.target.next k ms) x =
               mc.target.get_byte ms x))`;

Theorem evaluate_Halt_FUNPOW_next:
   ∀mc (ffi:'ffi ffi_state) k ms t ms' ffi'.
   interference_implemented mc ffi_rel md ms ∧ ffi_rel ms ffi ∧
   (evaluate mc ffi k ms = (Halt t, ms', ffi')) ⇒
     ∃k'. (ms' = FUNPOW mc.target.next k' ms) ∧
          (ffi_rel ms' ffi') ∧
          (∀x. x ∉ md ∪ mc.prog_addresses ⇒ (mc.target.get_byte ms' x = mc.target.get_byte ms x)) ∧
          ((∀x. t ≠ FFI_outcome x) ⇒ (mc.target.get_pc ms' = mc.halt_pc)) ∧
          (((mc.target.get_reg ms' mc.ptr_reg = 0w) ∧ (∀x. t ≠ FFI_outcome x))
            ⇒ (t = Success))
Proof
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
      \\ simp[] \\ rw[] \\ fs[]
      \\ metis_tac[])
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
      \\ fs[GSYM FUNPOW_ADD]
      \\ metis_tac[])
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
    \\ last_x_assum drule
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
        \\ disch_then(qx_choose_then`k1`strip_assume_tac)
        \\ fs[GSYM FUNPOW_ADD]
        \\ strip_tac
        \\ first_x_assum(qspec_then`k0+k1`mp_tac)
        \\ simp[]
        \\ impl_tac
        >- (
          rw[]
          \\ first_x_assum irule
          \\ rw[]
          \\ fs[targetSemTheory.read_ffi_bytearrays_def]
          \\ imp_res_tac targetPropsTheory.read_ffi_bytearray_IMP_SUBSET_prog_addresses
          \\ fs[SUBSET_DEF]
          \\ metis_tac[] )
        \\ rw[]
        \\ first_x_assum match_mp_tac
        \\ fs[targetSemTheory.read_ffi_bytearrays_def,
              targetSemTheory.read_ffi_bytearray_def]
        \\ goal_assum(first_assum o mp_then Any mp_tac)
        \\ fs[])
      \\ fs[interference_implemented_def]
      \\ first_x_assum(qspec_then`0`mp_tac)
      \\ simp[]
      \\ disch_then (first_assum o mp_then Any mp_tac)
      \\ impl_tac >- fs[]
      \\ disch_then(qx_choose_then`k1`strip_assume_tac)
      \\ fs[GSYM FUNPOW_ADD]
      \\ metis_tac[evaluatePropsTheory.call_FFI_rel_def])
    \\ disch_then(qx_choose_then`k1`strip_assume_tac)
    \\ fs[interference_implemented_def]
    \\ first_x_assum(qspec_then`0`mp_tac)
    \\ simp[]
    \\ disch_then (first_assum o mp_then Any mp_tac)
    \\ impl_tac >- fs[]
    \\ disch_then(qx_choose_then`k2`strip_assume_tac)
    \\ fs[GSYM FUNPOW_ADD]
    \\ qexists_tac`k1+k2` \\ rw[]
    \\ first_x_assum match_mp_tac \\ fs []
    \\ fs [targetSemTheory.read_ffi_bytearrays_def]
    \\ imp_res_tac targetPropsTheory.read_ffi_bytearray_IMP_SUBSET_prog_addresses
    \\ fs [SUBSET_DEF] \\ metis_tac [])
QED

Theorem machine_sem_Terminate_FUNPOW_next:
   interference_implemented mc ffi_rel md ms ∧
   (ffi_rel ms st) ∧
   machine_sem mc (st:'ffi ffi_state) ms (Terminate t io_events) ⇒
   ∃k st'.
     ffi_rel (nxt mc k ms) st' ∧ (io_events = st'.io_events) ∧
       (∀x. x ∉ md ∪ mc.prog_addresses ⇒ (mc.target.get_byte (nxt mc k ms) x = mc.target.get_byte ms x)) ∧
       ((∀x. t ≠ FFI_outcome x) ⇒ (mc.target.get_pc (nxt mc k ms) = mc.halt_pc)) ∧
       ((mc.target.get_reg (nxt mc k ms) mc.ptr_reg = 0w) ∧ (∀x. t ≠ FFI_outcome x)
        ⇒ (t = Success))
Proof
  rw[targetSemTheory.machine_sem_def]
  \\ imp_res_tac evaluate_Halt_FUNPOW_next
  \\ rfs[] \\ PROVE_TAC[]
QED

Theorem word_of_bytes_extract_bytes_le_32:
   word_of_bytes F 0w [(7 >< 0) w; (15 >< 8) w; (23 >< 16) w; (31 >< 24) w] = w : word32
Proof
  rw[word_of_bytes_def]
  \\ rw[set_byte_def,byte_index_def,word_slice_alt_def]
  \\ blastLib.BBLAST_TAC
QED

Theorem bytes_in_mem_bytes_in_memory:
   ∀a bs m md k. bytes_in_mem a bs m md k ⇔ bytes_in_memory a bs m (md DIFF k)
Proof
  Induct_on`bs` \\ EVAL_TAC \\ rw[]
  \\ rw[EQ_IMP_THM]
QED

Theorem read_bytearray_IMP_bytes_in_memory_WORD_LOWER:
   ∀p n m ba m' md.
   (n = LENGTH ba) ∧ w2n p + n < dimword(:'a) ∧
   (∀k. (p <=+ k ∧ k <+ p + n2w n) ⇒ k ∈ md ∧ (m k = SOME (m' k))) ∧
   (read_bytearray (p:'a word) n m = SOME ba) ⇒
   bytes_in_memory p ba m' md
Proof
  Induct_on`ba` \\ rw[] >- EVAL_TAC
  \\ simp[bytes_in_memory_def]
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
  \\ fs[word_lo_n2w, word_ls_n2w] \\ rfs[]
QED

Theorem bytes_in_memory_IMP_asm_write_bytearray:
   !bs a m. bytes_in_memory a bs m md ==> (asm_write_bytearray a bs m = m)
Proof
  rw [FUN_EQ_THM]
  \\ irule asm_write_bytearray_id
  \\ metis_tac [bytes_in_memory_EL]
QED

Theorem IMP_word_list:
   8 <= dimindex(:'a) ⇒
   ∀p ls m.
   (m = IMAGE (λk. (p + n2w k * (bytes_in_word:'a word), EL k ls)) (count (LENGTH ls))) ∧
   w2n p + LENGTH ls * w2n (bytes_in_word:'a word) < dimword(:'a)
   ⇒ word_list p ls m
Proof
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
  \\ simp[]
QED

(*
Theorem align_eq_0_imp
  `0 < p ⇒ ((align p a = 0w) ⇒ w2n a < 2 ** p)`
  (rw[alignmentTheory.align_w2n, dimword_def]
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

Theorem asm_step_target_configured:
   asm_step c s1 i s2 ∧ target_configured s1 mc ⇒
   target_configured s2 mc
Proof
  rw[asmSemTheory.asm_step_def]
  \\ fs[targetSemTheory.target_configured_def]
QED

Theorem RTC_asm_step_target_configured:
   RTC (λs1 s2. ∃i. asm_step c s1 i s2) s1 s2 ∧
   target_configured s1 mc ⇒
   target_configured s2 mc
Proof
  rw[]
  \\ first_assum(mp_then (Pat`RTC`) mp_tac (GEN_ALL RTC_lifts_invariants))
  \\ disch_then ho_match_mp_tac \\ rw[]
  \\ metis_tac[asm_step_target_configured]
QED

Theorem ag32_io_events_unchanged:
   Decode (
    let v : word32 = (31 >< 2) ms.PC : word30 @@ (0w:word2) in
      (ms.MEM (v + 3w) @@
       ((ms.MEM (v + 2w) @@
         ((ms.MEM (v + 1w) @@
           ms.MEM (v + 0w)) : word16)) : word24)))
    ≠ Interrupt
   ⇒
   ((Next ms).io_events = ms.io_events)
Proof
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
  \\ PURE_CASE_TAC \\ fs[] \\ rw[]
QED

Theorem ag32_enc_not_Interrupt:
   4 * k < LENGTH (ag32_enc istr) ⇒
   let bs = DROP (4 * k) (ag32_enc istr) in
   Decode (EL 3 bs @@ ((EL 2 bs @@ ((EL 1 bs @@ EL 0 bs) : word16)) : word24)) ≠ Interrupt
Proof
  Cases_on`istr`
  \\ TRY(rename1`JumpCmp _ _ ri _` \\ Cases_on`ri`)
  \\ TRY(rename1`Inst i ` \\ Cases_on`i`)
  \\ TRY(rename1`Inst (Mem m _ ri) ` \\ Cases_on`m` \\ Cases_on`ri`)
  \\ TRY(rename1`Inst (Arith a) ` \\ Cases_on`a`)
  \\ TRY(rename1`Inst (Arith (Binop _ _ _ ri)) ` \\ Cases_on`ri`)
  \\ rw[ag32_targetTheory.ag32_enc_def,
        ag32_targetTheory.ag32_encode_def,
        ag32_targetTheory.ag32_encode1_def,
        ag32_targetProofTheory.concat_bytes,
        ag32_targetTheory.ag32_constant_def,
        ag32_targetTheory.ag32_jump_constant_def,
        ag32_targetProofTheory.Decode_Encode]
  \\ Cases_on`k` \\ fs[ag32_targetProofTheory.concat_bytes, ag32_targetProofTheory.Decode_Encode]
  \\ qmatch_asmsub_rename_tac`4 * SUC k < _`
  \\ Cases_on`k` \\ fs[ag32_targetProofTheory.concat_bytes, ag32_targetProofTheory.Decode_Encode]
  \\ qmatch_asmsub_rename_tac`4 * SUC (SUC k) < _`
  \\ Cases_on`k` \\ fs[ag32_targetProofTheory.concat_bytes, ag32_targetProofTheory.Decode_Encode]
  \\ qmatch_asmsub_rename_tac`4 * SUC (SUC (SUC k)) < _`
  \\ Cases_on`k` \\ fs[ag32_targetProofTheory.concat_bytes, ag32_targetProofTheory.Decode_Encode]
QED

Theorem RTC_asm_step_ag32_target_state_rel_io_events:
   target_state_rel ag32_target s1 ms ∧
   RTC (λs1 s2. ∃i. asm_step ag32_config s1 i s2) s1 s2
   ⇒
   ∃n. target_state_rel ag32_target s2 (FUNPOW Next n ms) ∧
       ((FUNPOW Next n ms).io_events = ms.io_events) ∧
       (∀x. x ∉ s1.mem_domain ⇒ ((FUNPOW Next n ms).MEM x = ms.MEM x))
Proof
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
        (REWRITE_RULE[GSYM AND_IMP_INTRO] targetPropsTheory.encoder_correct_asm_step_target_state_rel)
        ag32_targetProofTheory.ag32_encoder_correct) |> GEN_ALL |> drule)
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
    \\ irule bytes_in_memory_change_mem
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
    irule bytes_in_memory_change_mem
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
  \\ Q.ISPECL_THEN[`TAKE (4 * k) (ag32_enc i)`, `DROP (4 * k) (ag32_enc i)`,`ms.PC`]mp_tac bytes_in_memory_APPEND
  \\ simp[]
  \\ disch_then(drule o #1 o EQ_IMP_RULE o SPEC_ALL)
  \\ strip_tac
  \\ qmatch_goalsub_abbrev_tac`pc + _`
  \\ qmatch_asmsub_abbrev_tac`bytes_in_memory pc bs`
  \\ `∀j. j < 4 ⇒ (m (pc + n2w j) = EL j bs)`
  by (
    rw[]
    \\ Q.ISPECL_THEN[`TAKE j bs`,`DROP j bs`,`st.PC`]mp_tac bytes_in_memory_APPEND
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
    \\ simp[bytes_in_memory_def]
    \\ rw[]
    \\ imp_res_tac DROP_EL_CONS
    \\ rfs[] )
  \\ simp[]
  \\ drule ag32_enc_not_Interrupt
  \\ simp[]
  \\ first_x_assum(qspec_then`0`mp_tac)
  \\ simp[]
QED

val read_bytearray_IMP_domain = store_thm("read_bytearray_IMP_domain", (* replace uses with read_bytearray_IMP_mem_SOME *)
  ``!n a xs.
      (read_bytearray a n
        (λa. if a ∈ md then SOME (m a) else NONE) = SOME xs) ==>
      !i. i < n ==> a + n2w i IN md``,
  Induct \\ fs [read_bytearray_def] \\ rw []
  \\ fs [option_case_eq] \\ rveq \\ fs []
  \\ res_tac
  \\ Cases_on `i` \\ fs [ADD1,GSYM word_add_n2w]);

(* -- *)

Theorem startup_asm_code_small_enough:
   ∀i. LENGTH (ag32_enc i) * LENGTH (startup_asm_code n cl bl) ≤ startup_code_size
Proof
  gen_tac (* change startup_code_size definition if this does not go through *)
  \\ qspec_then`i`mp_tac (Q.GEN`istr`ag32_enc_lengths)
  \\ rw[LENGTH_startup_asm_code, startup_code_size_def]
QED

(* TODO: this is not true until exit is implemented
Theorem FFI_codes_covers_basis_ffi:
   ∀name st conf bytes. basis_ffi_oracle name st conf bytes ≠ Oracle_final FFI_failed ⇒ name ∈ set (MAP FST FFI_codes)
Proof
  rw[basis_ffiTheory.basis_ffi_oracle_def]
  \\ pairarg_tac \\ fs[] \\ rveq
  \\ simp[FFI_codes_def]
  \\ pop_assum mp_tac
  \\ rpt(IF_CASES_TAC \\ fs[])
QED
*)

val get_output_io_event_def = Define`
  get_output_io_event (IO_event name conf bs2) =
    if name = "write" then
      case MAP FST bs2 of (n1 :: n0 :: off1 :: off0 :: tll) =>
        let k = MIN (w22n [n1; n0]) output_buffer_size in
        if (SND (HD bs2) = 0w) then
          let written = TAKE k (DROP (w22n [off1; off0]) tll) in
            SOME (conf ++ [0w;0w;n1;n0] ++ written)
        else SOME []
      | _ => NONE
    else NONE`;

val get_ag32_io_event_def = Define`
  get_ag32_io_event m =
    let call_id = m (n2w (ffi_code_start_offset - 1)) in
    if call_id = n2w (THE (ALOOKUP FFI_codes "write")) then
      if m (n2w output_offset) = 0w then
        let n1 = m (n2w (output_offset + 10)) in
        let n0 = m (n2w (output_offset + 11)) in
        let n = MIN (w22n [n1; n0]) output_buffer_size in
          read_bytearray (n2w output_offset) (8 + 4 + n) (SOME o m)
      else SOME []
    else NONE`;

val is_ag32_init_state_def = ag32_targetTheory.is_ag32_init_state_def;

Theorem target_state_rel_ag32_init:
   is_ag32_init_state m ms ⇒
   target_state_rel ag32_target
    (ag32_init_asm_state m md) ms
Proof
  rw[asmPropsTheory.target_state_rel_def]
  >- (
    rw[ag32_targetTheory.ag32_target_def, ag32_targetTheory.ag32_ok_def]
    \\ fs[is_ag32_init_state_def]
    \\ fs[alignmentTheory.byte_aligned_def]
    \\ EVAL_TAC)
  >- ( fs[is_ag32_init_state_def,ag32_init_asm_state_def] \\ EVAL_TAC \\ fs[] )
  >- ( fs[is_ag32_init_state_def,ag32_init_asm_state_def] \\ EVAL_TAC \\ fs[] )
  >- (
    fs[is_ag32_init_state_def,ag32_init_asm_state_def]
    \\ ntac 2 (pop_assum mp_tac)
    \\ EVAL_TAC \\ rw[]
    \\ EVAL_TAC \\ rw[])
  >- ( pop_assum mp_tac \\ EVAL_TAC )
QED

val stdin_fs_def = Define`
  stdin_fs inp =
    <| inode_tbl :=
       [(UStream (strlit "stdout"), "")
       ;(UStream (strlit "stderr"), "")
       ;(UStream (strlit "stdin"), inp)]
     ; infds :=
       [(0, UStream(strlit"stdin"), ReadMode, 0)
       ;(1, UStream(strlit"stdout"), WriteMode, 0)
       ;(2, UStream(strlit"stderr"), WriteMode, 0)]
     ; files := []
     ; numchars := LGENLIST (K output_buffer_size) NONE
     ; maxFD := 2
     |>`;

Theorem wfFS_stdin_fs:
   wfFS (stdin_fs inp)
Proof
  rw[stdin_fs_def, fsFFIPropsTheory.wfFS_def] \\ rw[]
  \\ rw[fsFFIPropsTheory.liveFS_def,fsFFIPropsTheory.consistentFS_def]
  \\ rw[fsFFIPropsTheory.live_numchars_def]
  \\ qmatch_goalsub_abbrev_tac`always P ll`
  \\ `∀x. (x = ll) ⇒ always P x` suffices_by rw[]
  \\ ho_match_mp_tac always_coind
  \\ rw[]
  \\ qexists_tac`output_buffer_size`
  \\ conj_tac
  >- ( simp[Abbr`ll`] \\ simp[LGENLIST_EQ_CONS] )
  \\ simp[Abbr`P`]
  \\ EVAL_TAC
QED

Theorem STD_streams_stdin_fs:
   STD_streams (stdin_fs inp)
Proof
  rw[fsFFIPropsTheory.STD_streams_def]
  \\ qexists_tac`0`
  \\ rw[stdin_fs_def]
  \\ rw[]
  \\ rw[EQ_IMP_THM]
QED

val ag32_fs_ok_def = Define`
  ag32_fs_ok fs ⇔
   (fs.numchars = LGENLIST (K output_buffer_size) NONE) ∧
   (∀fd. IS_SOME (ALOOKUP fs.infds fd) ⇔ fd < 3) ∧ (* this needs to change for close *)
   (∀fd ino md off.
     (ALOOKUP fs.infds fd = SOME (ino,md,off)) ⇒
     ∃cnt. (ALOOKUP fs.inode_tbl ino = SOME cnt) ∧ (fd ∈ {1;2} ⇒ (off = LENGTH cnt))) ∧
   (∀fnm. ALOOKUP fs.inode_tbl (File fnm) = NONE) ∧
   (* maybe *) fs.maxFD ≤ 2 ∧
   STD_streams fs`;

val ag32_stdin_implemented_def = Define`
  ag32_stdin_implemented fs m ⇔
    ∃off inp.
      (ALOOKUP fs.infds 0 = SOME (UStream(strlit"stdin"), ReadMode, off)) ∧
      (ALOOKUP fs.inode_tbl (UStream(strlit"stdin")) = SOME inp) ∧
      (get_mem_word m (n2w stdin_offset) = n2w off) ∧
      (get_mem_word m (n2w (stdin_offset + 4)) = n2w (LENGTH inp)) ∧
      off ≤ LENGTH inp ∧ LENGTH inp ≤ stdin_size ∧
      bytes_in_memory (n2w (stdin_offset + 8)) (MAP (n2w o ORD) inp)
        m (all_words (n2w (stdin_offset + 8)) (LENGTH inp))`;

val ag32_cline_implemented_def = Define`
  ag32_cline_implemented cl m ⇔
    (get_mem_word m (n2w startup_code_size) = n2w (LENGTH cl)) ∧
    SUM (MAP strlen cl) + LENGTH cl ≤ cline_size ∧
    EVERY validArg cl ∧ cl ≠ [] ∧
    bytes_in_memory (n2w (startup_code_size  + 4))
      (FLAT (MAP (SNOC 0w) (MAP (MAP (n2w o ORD) o explode) cl)))
      m (all_words (n2w (startup_code_size + 4)) (SUM (MAP strlen cl) + LENGTH cl))`;

val ag32_ffi_rel_def = Define`
  ag32_ffi_rel ms ffi ⇔
    (MAP get_ag32_io_event ms.io_events =
     MAP get_output_io_event ffi.io_events) ∧
    (ffi.oracle = basis_ffi_oracle) ∧
    (ag32_fs_ok (SND ffi.ffi_state)) ∧
    (ag32_stdin_implemented (SND ffi.ffi_state) ms.MEM) ∧
    (ag32_cline_implemented (FST ffi.ffi_state) ms.MEM)`;

val extract_write_def = Define`
  extract_write fd oevent =
    if NULL oevent then NONE else
      let conf = TAKE 8 oevent in
      if (w82n conf = fd) then
        SOME (DROP (8 + 4) oevent)
      else NONE`;

val extract_writes_def = Define`
  extract_writes fd oevents =
    FLAT (MAP (MAP (CHR o w2n) o THE) (FILTER IS_SOME (MAP (combin$C OPTION_BIND (extract_write fd)) oevents)))`;

(* TODO: why is this proof so slow? make it faster? *)
Theorem extract_fs_extract_writes:
   ∀ls fs fs' off off' out rest.
   (extract_fs fs ls = SOME fs') ∧
   (* can only read/write up to output_buffer_size - this could be made more nuanced *)
   (fs.numchars = LGENLIST (K output_buffer_size) NONE) ∧
   (* UStream of interest exists at the start *)
   (ALOOKUP fs.infds fd = SOME (UStream nam, WriteMode, LENGTH out)) ∧
   (ALOOKUP fs.inode_tbl (UStream nam)  = SOME out) ∧
   (* no non-UStream files *)
   (∀ino. ALOOKUP fs.inode_tbl (File ino) = NONE) ∧
   (* well-formedness invariants for the filesystem *)
   (∀fd fnm md off. ¬ (ALOOKUP fs'.infds fd = SOME (File fnm, md, off))) ∧
   (∀fd1 nm md1 off1 fd2 md2 off2. (* this one depends on us not being able to open UStreams *)
     (ALOOKUP fs'.infds fd1 = SOME (UStream nm, md1, off1)) ∧
     (ALOOKUP fs'.infds fd2 = SOME (UStream nm, md2, off2))
     ⇒ (fd1 = fd2)) ∧
   (* -- *)
   (* nothing has changed except the UStream of interest -- is this actually necessary? *)
   (∀x. x ≠ fd ⇒ (OPTREL (inv_image (=) FST) (ALOOKUP fs'.infds x) (ALOOKUP fs.infds x))) ∧
   (∀fnm. inFS_fname fs' fnm = inFS_fname fs fnm) ∧
   (* and it has only changed by appending *)
   (ALOOKUP fs'.infds fd = SOME (UStream nam, WriteMode, LENGTH out + LENGTH rest)) ∧
   (ALOOKUP fs'.inode_tbl (UStream nam) = SOME (out ++ rest))
   ⇒
   (extract_writes fd (MAP get_output_io_event ls) = rest)
Proof
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
      \\ fs[fsFFIPropsTheory.forwardFD_def, AFUPDKEY_ALOOKUP]
      \\ rw[]
      \\ TRY PURE_CASE_TAC \\ fs[]
      \\ TRY PURE_CASE_TAC \\ fs[CaseEq"option"]
      \\ rveq \\ fs[] \\ rfs[]
      >- ( first_x_assum drule \\ simp[OPTREL_def] )
      >- metis_tac[]
      >- metis_tac[])
    >- (
      reverse(fs[fsFFITheory.ffi_close_def, OPTION_CHOICE_EQUALS_OPTION] \\ rveq \\ fs[])
      \\ pairarg_tac \\ fs[] \\ rveq
      \\ fs[fsFFITheory.closeFD_def]
      \\ pairarg_tac \\ fs[]
      \\ rveq \\ fs[]
      \\ fs[ALOOKUP_ADELKEY]
      \\ fs[fsFFIPropsTheory.inFS_fname_def]
      \\ drule (GEN_ALL basis_ffiTheory.extract_fs_with_numchars_closes_iostreams)
      \\ simp[ALOOKUP_ADELKEY]
      \\ Cases_on`w82n l = fd` \\ fs[]
      \\ rw[]
      \\ fs[DISJ_EQ_IMP]
      \\ simp[OPTREL_def, FORALL_PROD]
      \\ first_x_assum drule
      \\ simp[OPTREL_def]
      \\ rpt strip_tac
      \\ fs[] \\ rveq \\ fs[]
      \\ qpat_assum `ALOOKUP z.infds x = SOME x0` (K (PairCases_on`x0`))
      \\ qpat_assum `ALOOKUP z.infds x = SOME (x00,_,_)`
            (K(reverse(Cases_on`x00` \\ fs[]) >- metis_tac[]))
      \\ pop_assum mp_tac \\ simp[]
      \\ first_x_assum drule
      \\ simp[OPTREL_def]
      \\ rpt strip_tac
      \\ fs[] \\ rveq \\ fs[]
      )
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
    \\ fs[extract_writes_def, extract_write_def]
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
  \\ rveq \\ fs[AFUPDKEY_ALOOKUP, LDROP1_THM]
  \\ rfs[]
  \\ qmatch_asmsub_abbrev_tac`extract_fs_with_numchars fs'`
  \\ qmatch_asmsub_abbrev_tac`AFUPDKEY fnm (K new_content)`
  \\ fs[extract_writes_def, extract_write_def]
  \\ simp[TAKE_APPEND]
  \\ simp[DROP_APPEND, DROP_LENGTH_TOO_LONG]
  \\ simp[TAKE_LENGTH_TOO_LONG]
  \\ reverse(Cases_on`w82n l = fd`) \\ fs[]
  >- (
    first_x_assum irule
    \\ simp[]
    \\ IF_CASES_TAC
    >- (
      rveq \\ fs[]
      \\ first_x_assum drule
      \\ simp[Once OPTREL_def, EXISTS_PROD]
      \\ metis_tac[] )
    \\ reverse(Cases_on`fnm` \\ rfs[])
    >- metis_tac[NOT_SOME_NONE]
    \\ first_assum(qspec_then`w82n l`mp_tac)
    \\ impl_tac >- fs[]
    \\ qpat_x_assum`ALOOKUP fs.infds (w82n l) = _`mp_tac
    \\ simp_tac(srw_ss())[Once OPTREL_def, EXISTS_PROD]
    \\ ntac 2 strip_tac
    \\ last_assum drule
    \\ simp_tac(srw_ss())[fsFFIPropsTheory.inFS_fname_def]
    \\ strip_tac
    \\ drule (GEN_ALL basis_ffiTheory.extract_fs_with_numchars_keeps_iostreams)
    \\ disch_then drule
    \\ simp[Abbr`fs'`, AFUPDKEY_ALOOKUP]
    \\ qmatch_goalsub_abbrev_tac`_ + zz ≤ _`
    \\ strip_tac
    \\ fs[fsFFIPropsTheory.inFS_fname_def]
    \\ rw[]
    \\ fs[OPTREL_def, FORALL_PROD]
    \\ PURE_CASE_TAC \\ fs[]
    \\ PURE_CASE_TAC \\ fs[]
    \\ metis_tac[NOT_SOME_NONE,SOME_11])
  \\ fs[MAP_TAKE]
  \\ qmatch_goalsub_abbrev_tac`written ++ _`
  \\ rveq \\ fs[]
  \\ rveq \\ fs[]
  \\ drule (GEN_ALL basis_ffiTheory.extract_fs_with_numchars_keeps_iostreams)
  \\ disch_then drule
  \\ simp[Abbr`fs'`, AFUPDKEY_ALOOKUP]
  \\ simp[data_to_word_assignProofTheory.IMP]
  \\ strip_tac
  \\ qmatch_asmsub_abbrev_tac`off + nw`
  \\ fs[Abbr`new_content`]
  \\ `LENGTH written = nw`
  by (
    simp[Abbr`written`, LENGTH_TAKE_EQ]
    \\ rw[] \\ fs[Abbr`nw`] )
  \\ fs[Abbr`off`, DROP_LENGTH_TOO_LONG]
  \\ `nw ≤ LENGTH rest` by fs[Abbr`nw`]
  \\ rfs[] \\ fs[]
  \\ qpat_x_assum`_ ⇒ _`mp_tac
  \\ impl_tac
  >- (
    rw[]
    \\ fs[CaseEq"option"]
    \\ CCONTR_TAC \\ fs[]
    \\ rveq
    \\ first_x_assum(qspec_then`fd'`mp_tac)
    \\ simp[OPTREL_def, FORALL_PROD]
    \\ metis_tac[] )
  \\ strip_tac
  \\ rveq \\ fs[]
  \\ first_x_assum irule
  \\ fs[fsFFIPropsTheory.inFS_fname_def]
  \\ rw[] \\ PURE_CASE_TAC \\ fs[]
  \\ metis_tac[]
QED

Theorem ag32_ffi_write_thm:
   bytes_in_memory (s.R 1w) conf s.MEM md ∧
   bytes_in_memory (s.R 3w) bytes s.MEM md ∧
   Abbrev(md = ag32_prog_addresses (LENGTH ffi_names) lc ld) ∧
   LENGTH ffi_names ≤ LENGTH FFI_codes ∧
   code_start_offset (LENGTH ffi_names) + lc + 4 * ld < memory_size ∧
   (w2n (s.R 2w) = LENGTH conf) ∧
   (w2n (s.R 4w) = LENGTH bytes) ∧ w2n (s.R 3w) + LENGTH bytes < dimword(:32) ∧
   (INDEX_OF "write" ffi_names = SOME index) ∧
   (ffi_write conf bytes fs = SOME (FFIreturn new_bytes fs')) ∧
   ag32_fs_ok fs ∧
   (s.PC = n2w (ffi_code_start_offset + THE (ALOOKUP ffi_entrypoints "write")))
   ⇒
   (ag32_ffi_write s = ag32_ffi_interfer ffi_names md (index, new_bytes, s))
Proof
     simp[ag32_ffi_interfer_def]
  \\ strip_tac
  \\ drule INDEX_OF_IMP_EL \\ strip_tac
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
    \\ irule bytes_in_memory_change_mem
    \\ goal_assum(first_assum o mp_then Any mp_tac)
    \\ rw[APPLY_UPDATE_THM]
    \\ imp_res_tac asmPropsTheory.bytes_in_memory_all_pcs
    \\ first_x_assum(qspec_then`0`mp_tac)
    \\ simp[asmPropsTheory.all_pcs_thm, SUBSET_DEF, PULL_EXISTS]
    \\ disch_then drule
    \\ simp[Abbr`md`]
    \\ simp[ag32_prog_addresses_def]
    \\ qpat_x_assum`n2w (_ - _) = _`(assume_tac o SYM)
    \\ simp[]
    \\ EVAL_TAC
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
    \\ irule bytes_in_memory_change_mem
    \\ goal_assum(first_assum o mp_then Any mp_tac)
    \\ rw[APPLY_UPDATE_THM]
    \\ imp_res_tac asmPropsTheory.bytes_in_memory_all_pcs
    \\ first_x_assum(qspec_then`0`mp_tac)
    \\ first_x_assum(qspec_then`0`mp_tac)
    \\ simp[asmPropsTheory.all_pcs_thm, SUBSET_DEF, PULL_EXISTS]
    \\ disch_then drule
    \\ simp[Abbr`md`]
    \\ simp[ag32_prog_addresses_def]
    \\ qpat_x_assum`n2w(_ - _)= _`(assume_tac o SYM)
    \\ simp[]
    \\ EVAL_TAC
    \\ fs[word_ls_n2w, word_lo_n2w, FFI_codes_def] )
  \\ strip_tac \\ fs[]
  \\ pop_assum kall_tac
  \\ fs[APPLY_UPDATE_THM]
  \\ qmatch_asmsub_abbrev_tac`ag32_ffi_write_check_lengths s2`
  \\ qspec_then`s2`mp_tac(Q.GENL[`s`,`ltll`,`off`,`n`,`cnd`]ag32_ffi_write_check_lengths_thm)
  \\ disch_then(qspecl_then[`LENGTH tll`,`w22n [off1; off0]`,`w22n [n1; n0]`,
                            `(LENGTH conf = 8) ∧ w82n conf < 3 ∧ 0 < w82n conf`]mp_tac)
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
      \\ fs[ag32_fs_ok_def]
      \\ Cases_on`LENGTH conf = 8` \\ fs[]
      \\ last_x_assum(qspec_then`w82n conf`mp_tac)
      \\ Cases_on`w82n conf < 3` \\ fs[]
      \\ simp[IS_SOME_EXISTS]
      \\ strip_tac \\ simp[]
      \\ PairCases_on`x` \\ simp[]
      \\ CCONTR_TAC \\ fs[]
      \\ Cases_on`ALOOKUP fs.inode_tbl x0` \\ fs[]
      \\ fs[markerTheory.Abbrev_def]
      \\ fs[fsFFIPropsTheory.STD_streams_def]
      \\ last_x_assum(qspecl_then[`0`,`ReadMode`,`inp`]mp_tac)
      \\ simp[] \\ rfs[])
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
    \\ simp[ag32_ffi_mem_update_def]
    \\ simp[FUN_EQ_THM, APPLY_UPDATE_THM]
    \\ Cases
    \\ IF_CASES_TAC \\ fs[]
    \\ IF_CASES_TAC
    >- simp[asm_write_bytearray_def, APPLY_UPDATE_THM]
    \\ IF_CASES_TAC
    >- (
      match_mp_tac EQ_SYM
      \\ fs[bytes_in_memory_def, asm_write_bytearray_def]
      \\ simp[APPLY_UPDATE_THM]
      \\ rveq
      \\ IF_CASES_TAC
      >- (
        rpt(qpat_x_assum`_ ∈ md`mp_tac)
        \\ simp[Abbr`md`]
        \\ qpat_x_assum`_ = n2w n`(mp_tac o SYM)
        \\ Cases_on`s.R 3w`
        \\ simp[ag32_prog_addresses_def,word_add_n2w]
        \\ EVAL_TAC
        \\ fs[FFI_codes_def, LEFT_ADD_DISTRIB]
        \\ fs[word_ls_n2w, word_lo_n2w, word_add_n2w] )
      \\ IF_CASES_TAC
      >- (
        rpt(qpat_x_assum`_ ∈ md`mp_tac)
        \\ simp[Abbr`md`]
        \\ qpat_x_assum`_ = n2w n`(mp_tac o SYM)
        \\ Cases_on`s.R 3w`
        \\ simp[ag32_prog_addresses_def, word_add_n2w]
        \\ EVAL_TAC
        \\ fs[FFI_codes_def, LEFT_ADD_DISTRIB]
        \\ fs[word_ls_n2w, word_lo_n2w, word_add_n2w] )
      \\ IF_CASES_TAC
      >- (
        rpt(qpat_x_assum`_ ∈ md`mp_tac)
        \\ simp[Abbr`md`]
        \\ qpat_x_assum`_ = n2w n`(mp_tac o SYM)
        \\ Cases_on`s.R 3w`
        \\ simp[ag32_prog_addresses_def, word_add_n2w]
        \\ EVAL_TAC
        \\ fs[FFI_codes_def, LEFT_ADD_DISTRIB]
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
      \\ fs[word_add_n2w] \\ rfs[]
      \\ rveq \\ fs[] \\ rfs[]
      \\ qpat_x_assum`n2w n' ∈ _`mp_tac
      \\ simp[word_add_n2w, Abbr`md`]
      \\ simp[ag32_prog_addresses_def]
      \\ EVAL_TAC
      \\ simp[LEFT_ADD_DISTRIB])
    \\ simp[asm_write_bytearray_def, APPLY_UPDATE_THM]
    \\ fs[bytes_in_memory_def] \\ rveq
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
    \\ fs[bytes_in_memory_def]
    \\ qpat_x_assum`s.R 3w ∈ _`mp_tac
    \\ simp[Abbr`md`]
    \\ EVAL_TAC
    \\ fs[FFI_codes_def]
    \\ simp[LEFT_ADD_DISTRIB]
    \\ Cases_on`s.R 3w` \\ fs[word_add_n2w]
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
    \\ fs[bytes_in_memory_def]
    \\ simp[APPLY_UPDATE_THM]
    \\ Cases_on`s.R 3w` \\ fs[word_add_n2w]
    \\ rveq
    \\ DEP_REWRITE_TAC[asm_write_bytearray_append]
    \\ simp[EVAL``output_offset``]
    \\ fs[memory_size_def, word_add_n2w]
    \\ simp[asm_write_bytearray_def, APPLY_UPDATE_THM]
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
    \\ irule bytes_in_memory_change_mem
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
  \\ qspec_then`s3`mp_tac(ag32_ffi_copy_thm)
  \\ qmatch_asmsub_abbrev_tac`LENGTH tll - off`
  \\ disch_then(qspec_then`TAKE (MIN n output_buffer_size) (DROP off tll)`mp_tac)
  \\ simp[]
  \\ impl_tac >- (
    simp[Abbr`s3`, APPLY_UPDATE_THM]
    \\ reverse conj_tac
    >- (
      Cases_on`s.R 3w` \\ fs[word_add_n2w]
      \\ EVAL_TAC
      \\ fs[memory_size_def, word_add_n2w]
      \\ simp[MIN_DEF]
      \\ simp[IN_DISJOINT]
      \\ Cases
      \\ fs[word_ls_n2w, word_lo_n2w]
      \\ simp[Abbr`md`]
      \\ EVAL_TAC \\ fs[]
      \\ fs[FFI_codes_def, LEFT_ADD_DISTRIB]
      \\ fs[word_ls_n2w, word_lo_n2w] )
    \\ fs[bytes_in_memory_def]
    \\ `tll = TAKE off tll ++ DROP off tll` by metis_tac[TAKE_DROP]
    \\ qhdtm_x_assum`bytes_in_memory`mp_tac
    \\ pop_assum(fn th => CONV_TAC(LAND_CONV(ONCE_REWRITE_CONV[th])))
    \\ disch_then(mp_then Any mp_tac (#1(EQ_IMP_RULE (SPEC_ALL bytes_in_memory_APPEND))))
    \\ simp[] \\ strip_tac
    \\ qmatch_goalsub_abbrev_tac`TAKE kk ll`
    \\ `ll = TAKE kk ll ++ DROP kk ll` by metis_tac[TAKE_DROP]
    \\ qhdtm_x_assum`bytes_in_memory`mp_tac
    \\ pop_assum(fn th => CONV_TAC(LAND_CONV(ONCE_REWRITE_CONV[th])))
    \\ disch_then(mp_then Any mp_tac (#1(EQ_IMP_RULE (SPEC_ALL bytes_in_memory_APPEND))))
    \\ strip_tac
    \\ irule bytes_in_memory_change_mem
    \\ goal_assum(first_assum o mp_then Any mp_tac)
    \\ gen_tac \\ strip_tac
    \\ simp[asm_write_bytearray_def]
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
  \\ qhdtm_x_assum`ag32_ffi_copy`kall_tac
  \\ simp[Abbr`A`]
  \\ simp[ag32_ffi_mem_update_def, ADD1]
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
  \\ `∃x. ALOOKUP fs.infds (w82n conf) = SOME x` by metis_tac[IS_SOME_EXISTS, ag32_fs_ok_def]
  \\ fs[] \\ PairCases_on`x` \\ fs[]
  \\ fs[ag32_fs_ok_def]
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
    \\ rw[MIN_DEF] )
  \\ qmatch_asmsub_rename_tac`mode = WriteMode`
  \\ Cases_on`mode`
  >- (
    fs[fsFFIPropsTheory.STD_streams_def]
    \\ qpat_x_assum`_ < 3`mp_tac
    \\ simp[NUMERAL_LESS_THM]
    \\ first_x_assum(qspecl_then[`w82n conf`,`WriteMode`,`LENGTH err`]mp_tac)
    \\ first_x_assum(qspecl_then[`w82n conf`,`WriteMode`,`LENGTH out`]mp_tac)
    \\ rw[] )
  \\ fs[]
  \\ rveq \\ fs[]
  \\ rewrite_tac[GSYM WORD_ADD_ASSOC, word_add_n2w]
  \\ AP_TERM_TAC
  \\ simp[FUN_EQ_THM]
  \\ Cases
  \\ simp[asm_write_bytearray_def, APPLY_UPDATE_THM]
  \\ IF_CASES_TAC
  >- (
    irule EQ_SYM
    \\ irule asm_write_bytearray_unchanged
    \\ simp[APPLY_UPDATE_THM]
    \\ EVAL_TAC
    \\ fs[word_add_n2w, word_ls_n2w, word_lo_n2w]
    \\ qpat_x_assum`read_bytearray (n2w _) _ _ = _`assume_tac
    \\ drule read_bytearray_IMP_mem_SOME
    \\ simp[IS_SOME_EXISTS]
    \\ disch_then(qspec_then`n2w n' + n2w 0`mp_tac)
    \\ simp[IN_all_words, PULL_EXISTS]
    \\ disch_then(qspec_then`0`mp_tac)
    \\ simp[Abbr`md`]
    \\ EVAL_TAC
    \\ simp[LEFT_ADD_DISTRIB]
    \\ fs[LEFT_ADD_DISTRIB, word_ls_n2w, word_lo_n2w, word_add_n2w]
    \\ fs[FFI_codes_def] )
  \\ simp[MarshallingTheory.n2w2_def]
  \\ simp[asm_write_bytearray_def, APPLY_UPDATE_THM]
  \\ IF_CASES_TAC
  >- (
    irule EQ_SYM
    \\ irule asm_write_bytearray_unchanged
    \\ simp[APPLY_UPDATE_THM]
    \\ EVAL_TAC
    \\ fs[word_add_n2w, memory_size_def]
    \\ fs[word_ls_n2w, word_lo_n2w]
    \\ qpat_x_assum`read_bytearray (s.R 3w) _ _ = _`assume_tac
    \\ drule read_bytearray_IMP_mem_SOME
    \\ simp[IS_SOME_EXISTS]
    \\ simp[IN_all_words, PULL_EXISTS]
    \\ disch_then(qspec_then`0`mp_tac)
    \\ simp[Abbr`md`]
    \\ Cases_on`s.R 3w`
    \\ EVAL_TAC
    \\ simp[LEFT_ADD_DISTRIB]
    \\ fs[LEFT_ADD_DISTRIB, word_ls_n2w, word_lo_n2w, word_add_n2w]
    \\ fs[FFI_codes_def] \\ rfs[])
  \\ IF_CASES_TAC
  >- (
    irule EQ_SYM
    \\ irule asm_write_bytearray_unchanged
    \\ simp[APPLY_UPDATE_THM]
    \\ EVAL_TAC
    \\ fs[word_add_n2w, memory_size_def]
    \\ fs[word_ls_n2w, word_lo_n2w]
    \\ qpat_x_assum`read_bytearray (s.R 3w) _ _ = _`assume_tac
    \\ drule read_bytearray_IMP_mem_SOME
    \\ simp[IS_SOME_EXISTS]
    \\ simp[IN_all_words, PULL_EXISTS]
    \\ disch_then(qspec_then`0`mp_tac)
    \\ simp[Abbr`md`]
    \\ Cases_on`s.R 3w`
    \\ EVAL_TAC
    \\ simp[LEFT_ADD_DISTRIB]
    \\ fs[LEFT_ADD_DISTRIB, word_ls_n2w, word_lo_n2w, word_add_n2w]
    \\ fs[FFI_codes_def] \\ rfs[])
  \\ irule mem_eq_imp_asm_write_bytearray_eq
  \\ simp[APPLY_UPDATE_THM]
  \\ IF_CASES_TAC
  >- (
    IF_CASES_TAC
    >- (
      fs[word_add_n2w, memory_size_def]
      \\ qpat_x_assum`read_bytearray (s.R 3w) _ _ = _`assume_tac
      \\ drule read_bytearray_IMP_mem_SOME
      \\ simp[IS_SOME_EXISTS]
      \\ simp[IN_all_words, PULL_EXISTS]
      \\ disch_then(qspec_then`0`mp_tac)
      \\ simp[Abbr`md`]
      \\ Cases_on`s.R 3w`
      \\ EVAL_TAC
      \\ simp[LEFT_ADD_DISTRIB]
      \\ fs[LEFT_ADD_DISTRIB, word_ls_n2w, word_lo_n2w, word_add_n2w]
      \\ fs[FFI_codes_def] \\ rfs[]
      \\ fs[EVAL``ffi_code_start_offset``]
      \\ rfs[])
    \\ irule EQ_SYM
    \\ irule asm_write_bytearray_unchanged
    \\ simp[APPLY_UPDATE_THM]
    \\ fs[word_add_n2w, memory_size_def]
    \\ Cases_on`s.R 3w`
    \\ fs[LEFT_ADD_DISTRIB, word_ls_n2w, word_lo_n2w, word_add_n2w]
    \\ fs[EVAL``ffi_code_start_offset``]
    \\ rfs[]
    \\ qpat_x_assum`read_bytearray (n2w _) _ _ = _`assume_tac
    \\ drule read_bytearray_IMP_mem_SOME
    \\ simp[IS_SOME_EXISTS, IN_all_words, PULL_EXISTS]
    \\ disch_then(qspec_then`0`mp_tac)
    \\ impl_tac
    >- (
      asm_simp_tac bool_ss []
      \\ simp[IN_all_words] )
    \\ simp[Abbr`md`]
    \\ EVAL_TAC
    \\ fs[LEFT_ADD_DISTRIB, word_ls_n2w, word_lo_n2w, word_add_n2w]
    \\ fs[FFI_codes_def] \\ rfs[] )
  \\ IF_CASES_TAC
  >- (
    `LENGTH tll + 4 = SUC(SUC(SUC(SUC(LENGTH tll))))` by simp[ADD1]
    \\ full_simp_tac std_ss [read_bytearray_def]
    \\ fs[CaseEq"bool",CaseEq"option"])
  \\ irule EQ_SYM
  \\ DEP_REWRITE_TAC[asm_write_bytearray_id]
  \\ simp[APPLY_UPDATE_THM]
  \\ gen_tac \\ strip_tac
  \\ IF_CASES_TAC
  >- (
    fs[word_add_n2w, memory_size_def]
    \\ qpat_x_assum`read_bytearray (s.R 3w) _ _ = _`assume_tac
    \\ drule read_bytearray_IMP_mem_SOME
    \\ simp[IS_SOME_EXISTS, IN_all_words, PULL_EXISTS]
    \\ disch_then(qspec_then`0`mp_tac)
    \\ simp[Abbr`md`]
    \\ Cases_on`s.R 3w`
    \\ EVAL_TAC
    \\ simp[LEFT_ADD_DISTRIB]
    \\ fs[LEFT_ADD_DISTRIB, word_ls_n2w, word_lo_n2w, word_add_n2w]
    \\ fs[FFI_codes_def] \\ rfs[]
    \\ fs[EVAL``ffi_code_start_offset``]
    \\ rfs[])
  \\ drule bytes_in_memory_EL
  \\ disch_then(qspec_then`j + 4`mp_tac)
  \\ simp[EL_CONS,PRE_SUB1]
  \\ simp[GSYM word_add_n2w]
QED

Theorem ag32_ffi_read_thm:
   bytes_in_memory (s.R 1w) conf s.MEM md ∧
   bytes_in_memory (s.R 3w) bytes s.MEM md ∧
   Abbrev(md = ag32_prog_addresses (LENGTH ffi_names) lc ld) ∧
   LENGTH ffi_names ≤ LENGTH FFI_codes ∧
   code_start_offset (LENGTH ffi_names) + lc + 4 * ld < memory_size ∧
   (w2n (s.R 2w) = LENGTH conf) ∧
   (w2n (s.R 4w) = LENGTH bytes) ∧ w2n (s.R 3w) + LENGTH bytes < dimword(:32) ∧
   (INDEX_OF "read" ffi_names = SOME index) ∧
   (ffi_read conf bytes fs = SOME (FFIreturn new_bytes fs')) ∧
   ag32_fs_ok fs ∧ ag32_stdin_implemented fs s.MEM ∧
   (s.PC = n2w (ffi_code_start_offset + THE (ALOOKUP ffi_entrypoints "read")))
   ⇒
   (ag32_ffi_read s = ag32_ffi_interfer ffi_names md (index, new_bytes, s))
Proof
  simp[ag32_ffi_interfer_def]
  \\ strip_tac
  \\ drule INDEX_OF_IMP_EL \\ strip_tac
  \\ simp[ag32_ffi_read_def]
  \\ qmatch_goalsub_abbrev_tac`ag32_ffi_return s'`
  \\ simp[ag32_ffi_return_thm]
  \\ simp[ag32Theory.ag32_state_component_equality]
  \\ qmatch_asmsub_abbrev_tac`if (s1.PC = _) then _ else _`
  \\ fs[ag32_ffi_read_set_id_thm]
  \\ qmatch_asmsub_abbrev_tac`ag32_ffi_read_check_conf s2`
  \\ qspec_then`s2`mp_tac(Q.GENL[`s`]ag32_ffi_read_check_conf_thm)
  \\ impl_tac
  >- (
    simp[Abbr`s2`,APPLY_UPDATE_THM]
    \\ irule bytes_in_memory_change_mem
    \\ goal_assum(first_assum o mp_then Any mp_tac)
    \\ rw[APPLY_UPDATE_THM]
    \\ imp_res_tac asmPropsTheory.bytes_in_memory_all_pcs
    \\ first_x_assum(qspec_then`0`mp_tac)
    \\ simp[asmPropsTheory.all_pcs_thm, SUBSET_DEF, PULL_EXISTS]
    \\ disch_then drule
    \\ simp[Abbr`md`]
    \\ simp[ag32_prog_addresses_def]
    \\ qpat_x_assum`n2w (_ - _) = _`(assume_tac o SYM)
    \\ simp[]
    \\ EVAL_TAC
    \\ fs[word_ls_n2w, word_lo_n2w, FFI_codes_def] )
  \\ strip_tac \\ fs[]
  \\ qmatch_asmsub_abbrev_tac`ag32_ffi_read_load_lengths s3`
  \\ qpat_x_assum`_ = s3`kall_tac
  \\ fs[Abbr`s2`, APPLY_UPDATE_THM]
  \\ fs[fsFFITheory.ffi_read_def, CaseEq"list"]
  \\ rveq
  \\ fs[ag32_stdin_implemented_def]
  \\ qspecl_then[`s3`,`LENGTH inp`]mp_tac(Q.GENL[`s`,`len`]ag32_ffi_read_load_lengths_thm)
  \\ impl_tac
  >- (
    simp[Abbr`s3`,APPLY_UPDATE_THM]
    \\ reverse conj_tac
    >- (
      fs[get_mem_word_def, APPLY_UPDATE_THM]
      \\ fs[EVAL``ffi_code_start_offset``,EVAL``stdin_offset``] )
    \\ fs[bytes_in_memory_def, APPLY_UPDATE_THM]
    \\ rpt(qpat_x_assum`_ ∈ md`mp_tac)
    \\ simp[Abbr`md`]
    \\ simp[ag32_prog_addresses_def]
    \\ EVAL_TAC
    \\ Cases_on`s.R 3w`
    \\ fs[word_ls_n2w, word_lo_n2w, FFI_codes_def, word_add_n2w] )
  \\ strip_tac \\ fs[]
  \\ pop_assum kall_tac
  \\ fs[APPLY_UPDATE_THM]
  \\ qmatch_asmsub_abbrev_tac`ag32_ffi_read_check_length s2`
  \\ qspec_then`s2`mp_tac(Q.GENL[`s`,`ltll`,`n`,`cnd`]ag32_ffi_read_check_length_thm)
  \\ disch_then(qspecl_then[`LENGTH tll`,`w22n [n1; n0]`,
                            `(LENGTH conf = 8) ∧ (w82n conf = 0)`]mp_tac)
  \\ impl_tac
  >- (
    simp[Abbr`s2`,Abbr`s3`,APPLY_UPDATE_THM]
    \\ simp[MarshallingTheory.w22n_def]
    \\ Cases_on`s.R 4w` \\ fs[ADD1,word_add_n2w]
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
      \\ simp[fsFFITheory.read_def, EXISTS_PROD]
      \\ fs[ag32_fs_ok_def]
      \\ Cases_on`LENGTH conf = 8` \\ fs[]
      \\ last_x_assum(qspec_then`w82n conf`mp_tac)
      \\ Cases_on`w82n conf < 3` \\ fs[]
      \\ simp[IS_SOME_EXISTS]
      \\ strip_tac \\ simp[]
      \\ PairCases_on`x` \\ simp[]
      \\ CCONTR_TAC \\ fs[]
      \\ fs[markerTheory.Abbrev_def]
      \\ qpat_x_assum`w82n _ < _`mp_tac
      \\ simp[NUMERAL_LESS_THM]
      \\ fs[fsFFIPropsTheory.STD_streams_def]
      \\ first_x_assum(qspecl_then[`w82n conf`,`WriteMode`,`LENGTH err`]mp_tac)
      \\ first_x_assum(qspecl_then[`w82n conf`,`WriteMode`,`LENGTH out`]mp_tac)
      \\ rw[])
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
    \\ simp[ag32_ffi_mem_update_def]
    \\ simp[FUN_EQ_THM, APPLY_UPDATE_THM]
    \\ Cases
    \\ IF_CASES_TAC
    >- simp[asm_write_bytearray_def, APPLY_UPDATE_THM]
    \\ IF_CASES_TAC
    >- (
      match_mp_tac EQ_SYM
      \\ fs[bytes_in_memory_def, asm_write_bytearray_def]
      \\ simp[APPLY_UPDATE_THM]
      \\ rveq
      \\ fs[EVAL``ffi_code_start_offset``] \\ rfs[] \\ rveq
      \\ IF_CASES_TAC
      >- (
        rpt(qpat_x_assum`_ ∈ md`mp_tac)
        \\ simp[Abbr`md`]
        \\ Cases_on`s.R 3w`
        \\ simp[ag32_prog_addresses_def,word_add_n2w]
        \\ EVAL_TAC
        \\ fs[FFI_codes_def, LEFT_ADD_DISTRIB])
      \\ IF_CASES_TAC
      >- (
        rpt(qpat_x_assum`_ ∈ md`mp_tac)
        \\ simp[Abbr`md`]
        \\ Cases_on`s.R 3w`
        \\ simp[ag32_prog_addresses_def, word_add_n2w]
        \\ EVAL_TAC
        \\ fs[FFI_codes_def, LEFT_ADD_DISTRIB])
      \\ IF_CASES_TAC
      >- (
        rpt(qpat_x_assum`_ ∈ md`mp_tac)
        \\ simp[Abbr`md`]
        \\ Cases_on`s.R 3w`
        \\ simp[ag32_prog_addresses_def, word_add_n2w]
        \\ EVAL_TAC
        \\ fs[FFI_codes_def, LEFT_ADD_DISTRIB])
      \\ irule asm_write_bytearray_unchanged
      \\ simp[APPLY_UPDATE_THM]
      \\ conj_tac
      >- ( Cases_on`s.R 3w` \\ fs[ADD1, memory_size_def, word_add_n2w] )
      \\ Cases_on`s.R 3w`
      \\ fs[word_lo_n2w, word_ls_n2w, word_add_n2w]
      \\ fs[EVAL``code_start_offset _``, FFI_codes_def]
      \\ fs[LEFT_ADD_DISTRIB]
      \\ fs[EVAL``ffi_code_start_offset``]
      \\ fs[word_add_n2w] \\ rfs[]
      \\ rveq \\ fs[] \\ rfs[]
      \\ qpat_x_assum`n2w n' ∈ _`mp_tac
      \\ simp[word_add_n2w, Abbr`md`]
      \\ simp[ag32_prog_addresses_def]
      \\ EVAL_TAC
      \\ simp[LEFT_ADD_DISTRIB])
    \\ simp[asm_write_bytearray_def, APPLY_UPDATE_THM]
    \\ fs[bytes_in_memory_def] \\ rveq
    \\ IF_CASES_TAC \\ simp[]
    \\ IF_CASES_TAC \\ simp[]
    \\ IF_CASES_TAC \\ simp[]
    \\ match_mp_tac EQ_SYM
    \\ Cases_on`n2w n <+ s.R 3w + 4w ∨ s.R 3w + 4w + n2w (LENGTH tll) <=+ n2w n`
    >- (
      irule asm_write_bytearray_unchanged
      \\ simp[APPLY_UPDATE_THM]
      \\ fs[EVAL``ffi_code_start_offset``] \\ rfs[]
      \\ Cases_on`s.R 3w` \\ fs[word_add_n2w] )
    \\ fs[WORD_NOT_LOWER, WORD_NOT_LOWER_EQUAL]
    \\ fs[EVAL``ffi_code_start_offset``] \\ rfs[]
    \\ Cases_on`s.R 3w`
    \\ fs[word_add_n2w, word_ls_n2w, word_lo_n2w] \\ rfs[]
    \\ qpat_x_assum`_ ≤ n`mp_tac
    \\ rw[LESS_EQ_EXISTS] \\ fs[]
    \\ qpat_x_assum`bytes_in_memory (n2w (_ + 4)) _ _ _`assume_tac
    \\ drule bytes_in_memory_EL
    \\ disch_then drule
    \\ rw[word_add_n2w]
    \\ qmatch_goalsub_rename_tac`n2w (a + (p + 4))`
    \\ `n2w(a + (p + 4)) = n2w(a+4) + n2w p:word32` by simp[word_add_n2w]
    \\ pop_assum SUBST_ALL_TAC
    \\ irule asm_write_bytearray_EL
    \\ simp[] )
  \\ pop_assum mp_tac \\ simp[markerTheory.Abbrev_def] \\ strip_tac
  \\ qspecl_then[`s1`,`w22n[n1;n0]`,`LENGTH inp - off`]mp_tac
       (Q.GENL[`s`,`n`,`lcmo`,`k`]ag32_ffi_read_num_written_thm)
  \\ simp[]
  \\ impl_tac
  >- (
    simp[Abbr`s1`, APPLY_UPDATE_THM]
    \\ reverse conj_tac
    >- (
      simp[MarshallingTheory.w22n_def]
      \\ Cases_on`n0` \\ Cases_on`n1` \\ fs[]
      \\ fs[stdin_size_def])
    \\ fs[bytes_in_memory_def]
    \\ simp[APPLY_UPDATE_THM]
    \\ Cases_on`s.R 3w` \\ fs[word_add_n2w]
    \\ rveq
    \\ fs[EVAL``ffi_code_start_offset``]
    \\ rpt(qpat_x_assum`_ ∈ md`mp_tac)
    \\ simp[Abbr`md`]
    \\ EVAL_TAC \\ simp[LEFT_ADD_DISTRIB]
    \\ fs[FFI_codes_def]
    \\ fs[EVAL``code_start_offset _``]
    \\ fs[word_ls_n2w, word_lo_n2w, memory_size_def]
    \\ rpt (disch_then assume_tac)
    \\ qpat_x_assum`bytes_in_memory (n2w (_ + 4)) _ _ _`mp_tac
    \\ EVAL_TAC \\ simp[LEFT_ADD_DISTRIB]
    \\ strip_tac
    \\ irule bytes_in_memory_change_mem
    \\ goal_assum(first_assum o mp_then Any mp_tac)
    \\ simp[APPLY_UPDATE_THM]
    \\ qx_gen_tac`z` \\ strip_tac
    \\ simp[word_add_n2w])
  \\ strip_tac
  \\ qmatch_asmsub_abbrev_tac`_ = s2`
  \\ fs[]
  \\ fs[Abbr`s1`, APPLY_UPDATE_THM]
  \\ qhdtm_x_assum`ag32_ffi_read_num_written`kall_tac
  \\ qmatch_asmsub_abbrev_tac`off + k`
  \\ qspecl_then[`all_words (n2w (stdin_offset + 8)) (LENGTH inp)`,`s2`,`MAP (n2w o ORD) (TAKE k (DROP off inp))`]
      mp_tac(Q.GEN`md`ag32_ffi_copy_thm)
  \\ impl_tac >- (
    simp[Abbr`s2`, APPLY_UPDATE_THM, Abbr`s'`]
    \\ `MAP (n2w o ORD) inp : word8 list =
        MAP (n2w o ORD) (TAKE off inp) ++
        MAP (n2w o ORD) (DROP off inp)`
    by (
      rewrite_tac[GSYM MAP_APPEND]
      \\ AP_TERM_TAC
      \\ MATCH_ACCEPT_TAC (GSYM TAKE_DROP) )
    \\ pop_assum SUBST_ALL_TAC
    \\ fs[bytes_in_memory_APPEND]
    \\ rfs[LENGTH_TAKE]
    \\ `MAP (n2w o ORD) (DROP off inp) : word8 list =
        MAP (n2w o ORD) (TAKE k (DROP off inp)) ++
        MAP (n2w o ORD) (DROP k (DROP off inp))`
    by (
      rewrite_tac[GSYM MAP_APPEND]
      \\ AP_TERM_TAC
      \\ MATCH_ACCEPT_TAC (GSYM TAKE_DROP) )
    \\ pop_assum SUBST_ALL_TAC
    \\ fs[bytes_in_memory_APPEND]
    \\ `k ≤ LENGTH inp - off` by simp[Abbr`k`, MIN_DEF]
    \\ fs[LENGTH_TAKE]
    \\ conj_tac
    >- (
      irule bytes_in_memory_change_mem
      \\ fs[word_add_n2w]
      \\ goal_assum(first_assum o mp_then Any mp_tac)
      \\ rw[]
      \\ DEP_REWRITE_TAC[set_mem_word_neq]
      \\ conj_tac
      >- (EVAL_TAC \\ simp[] \\ fs[EVAL``stdin_size``])
      \\ match_mp_tac EQ_SYM
      \\ irule asm_write_bytearray_unchanged
      \\ simp[APPLY_UPDATE_THM]
      \\ fs[EVAL``stdin_size``, EVAL``ffi_code_start_offset``, EVAL``stdin_offset``]
      \\ fs[bytes_in_memory_def]
      \\ qpat_x_assum`s.R 3w ∈ md`mp_tac
      \\ simp[Abbr`md`] \\ Cases_on`s.R 3w`
      \\ EVAL_TAC
      \\ fs[word_ls_n2w, word_lo_n2w, FFI_codes_def])
    \\ fs[EVAL``stdin_size``]
    \\ fs[EVAL``stdin_offset``]
    \\ `k ≤ w22n [n1; n0]` by simp[Abbr`k`, MIN_DEF]
    \\ fs[ADD1]
    \\ Cases_on`s.R 3w` \\ fs[word_add_n2w]
    \\ simp[IN_DISJOINT]
    \\ Cases
    \\ fs[word_ls_n2w, word_lo_n2w]
    \\ fs[bytes_in_memory_def]
    \\ qpat_x_assum`n2w n ∈ md`mp_tac
    \\ simp[Abbr`md`]
    \\ EVAL_TAC \\ simp[]
    \\ fs[word_ls_n2w, word_lo_n2w, FFI_codes_def, LEFT_ADD_DISTRIB, EVAL``code_start_offset _``,
          memory_size_def, IN_all_words, word_add_n2w]
    \\ CCONTR_TAC \\ fs[] \\ rveq \\ fs[] \\ rfs[] )
  \\ strip_tac
  \\ qunabbrev_tac`s'`
  \\ fs[]
  \\ qhdtm_x_assum`ag32_ffi_copy`kall_tac
  \\ simp[Abbr`s2`, APPLY_UPDATE_THM]
  \\ qmatch_goalsub_abbrev_tac`A ∧ B ∧ A`
  \\ `B ∧ A` suffices_by rw[]
  \\ simp[Abbr`B`, FUN_EQ_THM, APPLY_UPDATE_THM]
  \\ EVAL_TAC \\ simp[]
  \\ simp[Abbr`A`]
  \\ simp[ag32_ffi_mem_update_def, ADD1]
  \\ reverse(fs[OPTION_CHOICE_EQUALS_OPTION])
  \\ TRY pairarg_tac \\ fs[] \\ rveq \\ fs[LUPDATE_def]
  >- ( fs[fsFFITheory.read_def, ag32_fs_ok_def] )
  \\ fs[fsFFITheory.read_def]
  \\ `SUC strm = output_buffer_size + 1`
  by ( fs[ag32_fs_ok_def] )
  \\ fs[]
  \\ `∃l1 l0. n2w2 (LENGTH l) = [l1; l0]` by simp[MarshallingTheory.n2w2_def]
  \\ simp[]
  \\ `w22n [l1; l0] = LENGTH l` by (
    pop_assum(SUBST1_TAC o SYM)
    \\ irule MarshallingTheory.w22n_n2w2
    \\ rveq \\ simp[LENGTH_TAKE_EQ]
    \\ simp[Abbr`k`]
    \\ EVAL_TAC )
  \\ simp[]
  \\ DEP_REWRITE_TAC[get_mem_word_asm_write_bytearray_UNCHANGED_LT]
  \\ conj_tac
  >- (
    fs[bytes_in_memory_def]
    \\ qpat_x_assum`s.R 3w ∈ _`mp_tac
    \\ simp[Abbr`md`]
    \\ EVAL_TAC
    \\ Cases_on`s.R 3w` \\ fs[FFI_codes_def, LEFT_ADD_DISTRIB, ADD1, word_add_n2w]
    \\ fs[word_ls_n2w, word_lo_n2w]
    \\ fs[memory_size_def, EVAL``code_start_offset _``]
    \\ `k ≤ output_buffer_size + 1` by simp[Abbr`k`]
    \\ pop_assum mp_tac \\ EVAL_TAC
    \\ rveq \\ simp[LENGTH_TAKE_EQ] )
  \\ DEP_REWRITE_TAC[get_mem_word_UPDATE]
  \\ conj_tac >- EVAL_TAC
  \\ simp[word_add_n2w]
  \\ `LENGTH l = k`
  by ( rveq \\ simp[LENGTH_TAKE_EQ] \\ simp[Abbr`k`] )
  \\ fs[]
  \\ DEP_REWRITE_TAC [GSYM set_mem_word_asm_write_bytearray_commute_LT]
  \\ conj_asm1_tac >- (
    EVAL_TAC>>fs[]>> fs[ADD1]
    \\ fs[bytes_in_memory_def]
    \\ qpat_x_assum`s.R 3w ∈ md`mp_tac
    \\ simp[Abbr`md`]
    \\ EVAL_TAC
    \\ Cases_on`s.R 3w` \\ fs[FFI_codes_def, LEFT_ADD_DISTRIB, word_add_n2w]
    \\ `k ≤ LENGTH tll` by simp[Abbr`k`] \\ fs[]
    \\ fs[word_ls_n2w, word_lo_n2w, EVAL``code_start_offset _``, memory_size_def])
  \\ AP_TERM_TAC
  \\ simp[asm_write_bytearray_def]
  \\ rw[FUN_EQ_THM]
  \\ simp[APPLY_UPDATE_THM]
  \\ IF_CASES_TAC
  >-
    (`s.R 3w <+ s.R 3w +4w` by
      blastLib.FULL_BBLAST_TAC>>
    irule asm_write_bytearray_unchanged>>
    fs[APPLY_UPDATE_THM]>>
    rveq>>fs[])
  \\ IF_CASES_TAC
  >-
    (`s.R 3w+1w <+ s.R 3w +4w` by
      blastLib.FULL_BBLAST_TAC>>
    irule asm_write_bytearray_unchanged>>
    fs[APPLY_UPDATE_THM]>>
    rveq>>fs[])
  \\ IF_CASES_TAC
  >-
    (`s.R 3w+2w <+ s.R 3w +4w` by
      blastLib.FULL_BBLAST_TAC>>
    irule asm_write_bytearray_unchanged>>
    fs[APPLY_UPDATE_THM]>>
    rveq>>fs[])
  \\ IF_CASES_TAC
  >-
    (`s.R 3w+3w <+ s.R 3w +4w` by
      blastLib.FULL_BBLAST_TAC>>
    irule asm_write_bytearray_unchanged>>
    fs[APPLY_UPDATE_THM]>>
    rveq>>fs[]>>
    rw[]
    >-
      (pop_assum mp_tac>>
      EVAL_TAC>>
      fs[bytes_in_memory_def]
      \\ qpat_x_assum`s.R 3w ∈ _`mp_tac
      \\ simp[Abbr`md`]
      \\ EVAL_TAC
      \\ Cases_on`s.R 3w` \\ fs[]
      \\ fs[word_add_n2w, LEFT_ADD_DISTRIB, EVAL``code_start_offset _``, memory_size_def]
      \\ fs[FFI_codes_def, word_ls_n2w, word_lo_n2w])
    >>
    fs[bytes_in_memory_def])
  \\ simp[asm_write_bytearray_append2]
  \\ qpat_abbrev_tac `smm = (_ =+ _) s.MEM`
  \\ DEP_REWRITE_TAC [asm_write_bytearray_UPDATE]
  \\ simp[]
  \\ match_mp_tac mem_eq_imp_asm_write_bytearray_eq
  \\ AP_THM_TAC
  \\ match_mp_tac (GSYM bytes_in_memory_IMP_asm_write_bytearray)
  \\ qpat_x_assum`bytes_in_memory (s.R 3w) _ _ _` mp_tac
  \\ qmatch_goalsub_abbrev_tac`_ _ lss _ _`
  \\ `?ll. LENGTH ll = LENGTH l + 4 ∧ lss = ll ++ DROP (STRLEN l) tll` by
    (fs[Abbr`lss`]>>
    qexists_tac`n1::n0::pad1::pad2::TAKE (STRLEN l) tll` >>
    fs[markerTheory.Abbrev_def,MIN_DEF])
  \\ simp[bytes_in_memory_APPEND,GSYM word_add_n2w,Abbr`smm`]
  \\ strip_tac
  \\ match_mp_tac bytes_in_memory_change_mem
  \\ asm_exists_tac
  \\ rw[APPLY_UPDATE_THM]
  \\ drule bytes_in_memory_in_domain
  \\ simp[]
  \\ disch_then drule
  \\ simp[Abbr`md`]
  \\ EVAL_TAC
  \\ Cases_on`s.R 3w` \\ fs[word_add_n2w, LEFT_ADD_DISTRIB]
  \\ fs[EVAL``code_start_offset _``,EVAL``FFI_codes``]
  \\ fs[word_ls_n2w, word_lo_n2w, memory_size_def]
  \\ rfs[EVAL``ffi_code_start_offset``]
  \\ qpat_x_assum`_ = _ MOD _`mp_tac
  \\ simp[]
QED

Theorem ag32_ffi_get_arg_count_thm:
   bytes_in_memory (s.R 1w) conf s.MEM md ∧
   bytes_in_memory (s.R 3w) bytes s.MEM md ∧
   Abbrev(md = ag32_prog_addresses (LENGTH ffi_names) lc ld) ∧
   LENGTH ffi_names ≤ LENGTH FFI_codes ∧
   code_start_offset (LENGTH ffi_names) + lc + 4 * ld < memory_size ∧
   (w2n (s.R 2w) = LENGTH conf) ∧
   (w2n (s.R 4w) = LENGTH bytes) ∧ w2n (s.R 3w) + LENGTH bytes < dimword(:32) ∧
   (INDEX_OF "get_arg_count" ffi_names = SOME index) ∧
   (ffi_get_arg_count conf bytes (cl:mlstring list) = SOME (FFIreturn new_bytes cl')) ∧
   ag32_cline_implemented cl s.MEM ∧
   (s.PC = n2w (ffi_code_start_offset + THE (ALOOKUP ffi_entrypoints "get_arg_count")))
   ⇒
   (ag32_ffi_get_arg_count s = ag32_ffi_interfer ffi_names md (index, new_bytes, s))
Proof
  simp[ag32_ffi_interfer_def]
  \\ strip_tac
  \\ drule INDEX_OF_IMP_EL
  \\ rw[ag32_ffi_get_arg_count_def]
  \\ fs[ag32_cline_implemented_def]
  \\ drule ag32_ffi_get_arg_count_main_thm
  \\ impl_tac >- ( fs[cline_size_def] )
  \\ strip_tac \\ fs[]
  \\ pop_assum kall_tac
  \\ simp[ag32_ffi_return_thm]
  \\ simp[ag32Theory.ag32_state_component_equality]
  \\ simp[APPLY_UPDATE_THM, FUN_EQ_THM]
  \\ qmatch_goalsub_abbrev_tac`A ∧ B ∧ _`
  \\ `B` by ( simp[Abbr`B`] \\ EVAL_TAC \\ rw[] )
  \\ simp[]
  \\ qunabbrev_tac`B`
  \\ pop_assum kall_tac
  \\ simp[Abbr`A`]
  \\ simp[ag32_ffi_mem_update_def]
  \\ fs[clFFITheory.ffi_get_arg_count_def]
QED

Theorem get_mem_arg_thm:
   ∀cl i a.
   bytes_in_memory a (FLAT (MAP (SNOC 0w) cl)) m md ∧
   i < LENGTH cl ∧ EVERY (EVERY ((<>)0w)) cl
   ⇒
   get_mem_arg m a i = (a + n2w (SUM (MAP LENGTH (TAKE (i+1) cl)) + i),
                        EL i cl)
Proof
  Induct \\ simp[]
  \\ gen_tac
  \\ Cases
  \\ simp[get_mem_arg_def]
  >- (
    rw[bytes_in_memory_APPEND]
    \\ rw[get_next_mem_arg_LEAST]
    \\ simp[whileTheory.OLEAST_def]
    \\ reverse IF_CASES_TAC
    >- ( fs[SNOC_APPEND, bytes_in_memory_APPEND, bytes_in_memory_def] )
    \\ simp[]
    \\ numLib.LEAST_ELIM_TAC
    \\ conj_tac >- metis_tac[]
    \\ fs[SNOC_APPEND, bytes_in_memory_APPEND, bytes_in_memory_def]
    \\ gen_tac \\ strip_tac
    \\ qmatch_goalsub_rename_tac`l MOD _`
    \\ `l = LENGTH h` suffices_by (
      rw[]
      \\ rw[LIST_EQ_REWRITE]
      \\ imp_res_tac bytes_in_memory_EL )
    \\ `¬(LENGTH h < l)` by metis_tac[]
    \\ imp_res_tac bytes_in_memory_EL
    \\ fs[EVERY_MEM, MEM_EL]
    \\ Cases_on`l < LENGTH h` \\ fs[]
    \\ metis_tac[] )
  \\ rw[bytes_in_memory_APPEND]
  \\ first_x_assum drule
  \\ disch_then drule
  \\ rw[]
  \\ simp[get_next_mem_arg_LEAST, whileTheory.OLEAST_def]
  \\ reverse IF_CASES_TAC
  >- ( fs[SNOC_APPEND, bytes_in_memory_APPEND, bytes_in_memory_def] )
  \\ simp[]
  \\ numLib.LEAST_ELIM_TAC
  \\ conj_tac >- metis_tac[]
  \\ gen_tac \\ strip_tac
  \\ fs[ADD1, GSYM word_add_n2w]
  \\ first_x_assum(CHANGED_TAC o SUBST1_TAC o SYM)
  \\ AP_THM_TAC \\ AP_TERM_TAC
  \\ AP_THM_TAC \\ AP_TERM_TAC
  \\ AP_TERM_TAC \\ AP_TERM_TAC
  \\ qmatch_goalsub_rename_tac`l = _`
  \\ fs[SNOC_APPEND, bytes_in_memory_APPEND, bytes_in_memory_def]
  \\ `¬(LENGTH h < l)` by metis_tac[]
  \\ Cases_on`l < LENGTH h` \\ fs[]
  \\ imp_res_tac bytes_in_memory_EL
  \\ fs[EVERY_MEM, MEM_EL]
  \\ metis_tac[]
QED

Theorem ag32_ffi_get_arg_length_thm:
   bytes_in_memory (s.R 1w) conf s.MEM md ∧
   bytes_in_memory (s.R 3w) bytes s.MEM md ∧
   Abbrev(md = ag32_prog_addresses (LENGTH ffi_names) lc ld) ∧
   LENGTH ffi_names ≤ LENGTH FFI_codes ∧
   code_start_offset (LENGTH ffi_names) + lc + 4 * ld < memory_size ∧
   (w2n (s.R 2w) = LENGTH conf) ∧
   (w2n (s.R 4w) = LENGTH bytes) ∧ w2n (s.R 3w) + LENGTH bytes < dimword(:32) ∧
   (INDEX_OF "get_arg_length" ffi_names = SOME index) ∧
   (ffi_get_arg_length conf bytes (cl:mlstring list) = SOME (FFIreturn new_bytes cl')) ∧
   ag32_cline_implemented cl s.MEM ∧
   (s.PC = n2w (ffi_code_start_offset + THE (ALOOKUP ffi_entrypoints "get_arg_length")))
   ⇒
   (ag32_ffi_get_arg_length s = ag32_ffi_interfer ffi_names md (index, new_bytes, s))
Proof
  simp[ag32_ffi_interfer_def]
  \\ strip_tac
  \\ drule INDEX_OF_IMP_EL
  \\ rw[ag32_ffi_get_arg_length_def]
  \\ fs[ag32_cline_implemented_def]
  \\ fs[clFFITheory.ffi_get_arg_length_def]
  \\ fs[LENGTH_EQ_NUM_compute]
  \\ rveq \\ fs[]
  \\ drule ag32_ffi_get_arg_length_setup_thm
  \\ impl_tac
  >- (
    simp[Abbr`md`]
    \\ EVAL_TAC
    \\ fs[FFI_codes_def, LEFT_ADD_DISTRIB, word_ls_n2w] )
  \\ strip_tac \\ fs[]
  \\ pop_assum kall_tac
  \\ qmatch_goalsub_abbrev_tac`ag32_ffi_get_arg_length_loop s1`
  \\ qmatch_asmsub_rename_tac`bytes_in_memory _ [i1; i0]`
  \\ qspecl_then[`s1`,`w2n i1 + 256 * w2n i0`]mp_tac(Q.GENL[`s`,`index`]ag32_ffi_get_arg_length_loop_thm)
  \\ impl_tac
  >- (
    simp[Abbr`s1`, APPLY_UPDATE_THM]
    \\ Cases_on`cl` \\ fs[bytes_in_memory_def]
    \\ fs[SNOC_APPEND]
    \\ fs[bytes_in_memory_APPEND]
    \\ fs[bytes_in_memory_def]
    \\ qexists_tac`strlen h`
    \\ rw[]
    \\ pop_assum mp_tac
    \\ EVAL_TAC
    \\ fs[IN_all_words, EVAL``cline_size``] )
  \\ strip_tac \\ fs[]
  \\ fs[Abbr`s1`, APPLY_UPDATE_THM]
  \\ pop_assum kall_tac
  \\ qmatch_goalsub_abbrev_tac`ag32_ffi_get_arg_length_store s1`
  \\ qmatch_asmsub_abbrev_tac`4w =+ n2w(n + 1)`
  \\ qspecl_then[`s1`,`n`]mp_tac(Q.GENL[`s`,`n`]ag32_ffi_get_arg_length_store_thm)
  \\ qmatch_goalsub_abbrev_tac`EL ix cl`
  \\ `n = strlen (EL ix cl)`
  by (
    simp[Abbr`n`]
    \\ qmatch_asmsub_abbrev_tac`FLAT (MAP _ bl)`
    \\ qspec_then`bl`(mp_tac o Q.GENL[`m`,`md`]) get_mem_arg_thm
    \\ disch_then(fn th => DEP_REWRITE_TAC[th])
    \\ simp[Abbr`bl`, EL_MAP]
    \\ simp[EVERY_MAP, ORD_BOUND]
    \\ qmatch_asmsub_abbrev_tac`bytes_in_memory _ _ _ dm`
    \\ qexists_tac`dm`
    \\ reverse conj_tac
    >- (
      fs[EVERY_MEM, clFFITheory.validArg_def]
      \\ gen_tac \\ strip_tac
      \\ Cases \\ rw[] \\ strip_tac \\ rveq
      \\ rfs[] )
    \\ irule bytes_in_memory_change_mem
    \\ goal_assum(first_assum o mp_then Any mp_tac)
    \\ rw[APPLY_UPDATE_THM]
    \\ ntac 2 (pop_assum mp_tac)
    \\ EVAL_TAC
    \\ simp[LENGTH_FLAT, MAP_MAP_o, o_DEF, ADD1]
    \\ simp[SUM_MAP_PLUS]
    \\ simp[Q.ISPEC`λx. 1n`SUM_MAP_K |> SIMP_RULE(srw_ss())[]]
    \\ fs[EVAL``cline_size``] \\ rw[]
    \\ qpat_x_assum`_ = _ MOD _`mp_tac
    \\ simp[])
  \\ impl_tac >-
    ( simp[Abbr`s1`, APPLY_UPDATE_THM] >>
       fs[EVERY_MEM, clFFITheory.validArg_def, MEM_EL, PULL_EXISTS]
       \\ res_tac \\ fs[])
  \\ strip_tac \\ fs[]
  \\ fs[Abbr`s1`, APPLY_UPDATE_THM]
  \\ pop_assum kall_tac
  \\ simp[ag32_ffi_return_thm]
  \\ simp[ag32Theory.ag32_state_component_equality]
  \\ simp[APPLY_UPDATE_THM, FUN_EQ_THM]
  \\ qmatch_goalsub_abbrev_tac`A ∧ B ∧ _`
  \\ `B` by ( simp[Abbr`B`] \\ EVAL_TAC \\ rw[] )
  \\ simp[]
  \\ qunabbrev_tac`B`
  \\ pop_assum kall_tac
  \\ simp[Abbr`A`]
  \\ simp[ag32_ffi_mem_update_def]
  \\ simp[asm_write_bytearray_def, APPLY_UPDATE_THM]
QED

Theorem ag32_ffi_get_arg_thm:
   bytes_in_memory (s.R 1w) conf s.MEM md ∧
   bytes_in_memory (s.R 3w) bytes s.MEM md ∧
   Abbrev(md = ag32_prog_addresses (LENGTH ffi_names) lc ld) ∧
   LENGTH ffi_names ≤ LENGTH FFI_codes ∧
   code_start_offset (LENGTH ffi_names) + lc + 4 * ld < memory_size ∧
   (w2n (s.R 2w) = LENGTH conf) ∧
   (w2n (s.R 4w) = LENGTH bytes) ∧ w2n (s.R 3w) + LENGTH bytes < dimword(:32) ∧
   (INDEX_OF "get_arg" ffi_names = SOME index) ∧
   (ffi_get_arg conf bytes (cl:mlstring list) = SOME (FFIreturn new_bytes cl')) ∧
   ag32_cline_implemented cl s.MEM ∧
   (s.PC = n2w (ffi_code_start_offset + THE (ALOOKUP ffi_entrypoints "get_arg")))
   ⇒
   (ag32_ffi_get_arg s = ag32_ffi_interfer ffi_names md (index, new_bytes, s))
Proof
  simp[ag32_ffi_interfer_def]
  \\ strip_tac
  \\ drule INDEX_OF_IMP_EL
  \\ rw[ag32_ffi_get_arg_def]
  \\ fs[ag32_cline_implemented_def]
  \\ fs[clFFITheory.ffi_get_arg_def]
  \\ fs[LENGTH_EQ_NUM_compute]
  \\ rveq \\ fs[]
  \\ Cases_on`bytes` \\ fs[]
  \\ Cases_on`t` \\ fs[]
  \\ qmatch_asmsub_rename_tac`bytes_in_memory (s.R 3w) (i0::i1::bytes) _ _`
  \\ `bytes_in_memory (s.R 3w) [i0; i1] s.MEM md` by fs[bytes_in_memory_def]
  \\ drule ag32_ffi_get_arg_setup_thm
  \\ impl_tac
  >- (
    simp[Abbr`md`]
    \\ EVAL_TAC
    \\ fs[FFI_codes_def, LEFT_ADD_DISTRIB, word_ls_n2w] )
  \\ strip_tac \\ fs[]
  \\ pop_assum kall_tac
  \\ qmatch_goalsub_abbrev_tac`ag32_ffi_get_arg_find s1`
  \\ qspecl_then[`s1`,`w2n i0 + 256 * w2n i1`]mp_tac(Q.GENL[`s`,`index`]ag32_ffi_get_arg_find_thm)
  \\ impl_tac
  >- (
    simp[Abbr`s1`, APPLY_UPDATE_THM]
    \\ Cases_on`cl` \\ fs[bytes_in_memory_def]
    \\ fs[SNOC_APPEND]
    \\ fs[bytes_in_memory_APPEND]
    \\ fs[bytes_in_memory_def]
    \\ qexists_tac`strlen h`
    \\ rw[]
    \\ pop_assum mp_tac
    \\ EVAL_TAC
    \\ fs[IN_all_words, EVAL``cline_size``] )
  \\ strip_tac \\ fs[]
  \\ fs[Abbr`s1`, APPLY_UPDATE_THM]
  \\ pop_assum kall_tac
  \\ qmatch_goalsub_abbrev_tac`ag32_ffi_get_arg_store s1`
  \\ qmatch_goalsub_abbrev_tac`EL ix cl`
  \\ qspecl_then[`s1`,`strlen (EL ix cl)`]mp_tac(Q.GENL[`s`,`n`]ag32_ffi_get_arg_store_thm)
  \\ qmatch_asmsub_abbrev_tac`5w =+ a`
  \\ `a = n2w (startup_code_size + 4 + SUM (MAP strlen (TAKE ix cl)) + ix)`
  by (
    simp[Abbr`a`]
    \\ Cases_on`ix = 0` \\ simp[]
    \\ `ix - 1 < LENGTH cl` by fs[]
    \\ qmatch_goalsub_abbrev_tac`get_mem_arg m`
    \\ qpat_x_assum`bytes_in_memory (n2w (_ + 4)) _ _ _`assume_tac
    \\ drule bytes_in_memory_change_mem
    \\ disch_then(qspec_then`m`mp_tac)
    \\ impl_tac
    >- (
      simp[Abbr`m`, APPLY_UPDATE_THM]
      \\ rw[]
      \\ fs[LENGTH_FLAT, MAP_MAP_o, o_DEF, ADD1, SUM_MAP_PLUS]
      \\ fs[Q.ISPEC`λx. 1n`SUM_MAP_K |> SIMP_RULE(srw_ss())[]]
      \\ ntac 2 (pop_assum mp_tac)
      \\ CONV_TAC(LAND_CONV EVAL)
      \\ fs[EVAL``cline_size``] \\ rw[]
      \\ qpat_x_assum` _ = _  MOD _ `mp_tac
      \\ simp[] )
    \\ strip_tac
    \\ drule get_mem_arg_thm
    \\ simp[]
    \\ disch_then drule
    \\ impl_tac
    >- (
      fs[EVERY_MEM, MEM_MAP, PULL_EXISTS, ORD_BOUND, DISJ_EQ_IMP]
      \\ gen_tac \\ strip_tac \\ Cases
      \\ simp[] \\ strip_tac \\ rveq
      \\ res_tac
      \\ fs[clFFITheory.validArg_def] )
    \\ simp[]
    \\ disch_then kall_tac
    \\ simp[word_add_n2w]
    \\ simp[MAP_TAKE, MAP_MAP_o, o_DEF]
    \\ srw_tac[ETA_ss][] )
  \\ qpat_x_assum`Abbrev(a = _)`kall_tac
  \\ qpat_x_assum`bytes_in_memory _ (FLAT _) _ _`mp_tac
  \\ Q.ISPECL_THEN[`ix`,`cl`](fn th => CONV_TAC(PATH_CONV"lrl"(ONCE_REWRITE_CONV[SYM th])))TAKE_DROP
  \\ simp[bytes_in_memory_APPEND]
  \\ strip_tac
  \\ qmatch_asmsub_abbrev_tac`bytes_in_memory a'`
  \\ `a' = a`
  by (
    simp[Abbr`a'`, word_add_n2w]
    \\ fs[LENGTH_FLAT, MAP_MAP_o, o_DEF, ADD1, SUM_MAP_PLUS]
    \\ fs[Q.ISPEC`λx. 1n`SUM_MAP_K |> SIMP_RULE(srw_ss())[]] )
  \\ qpat_x_assum`Abbrev(a' = _)`kall_tac
  \\ drule DROP_EL_CONS
  \\ strip_tac
  \\ fs[bytes_in_memory_def, bytes_in_memory_APPEND, SNOC_APPEND]
  \\ impl_tac
  >- (
    simp[markerTheory.Abbrev_def]
    \\ qpat_x_assum`a' = a`SUBST_ALL_TAC
    \\ qpat_x_assum`a = _`(assume_tac o SYM)
    \\ simp[Abbr`s1`, APPLY_UPDATE_THM]
    \\ simp[whileTheory.OLEAST_def]
    \\ simp[GSYM CONJ_ASSOC]
    \\ conj_asm1_tac
    >- (
      qexists_tac`strlen (EL ix cl)`
      \\ rw[]
      \\ pop_assum mp_tac
      \\ qpat_x_assum`_ ≤ cline_size`mp_tac
      \\ Q.ISPECL_THEN[`ix`,`cl`](fn th => CONV_TAC(PATH_CONV"lrlrr"(ONCE_REWRITE_CONV[SYM th])))TAKE_DROP
      \\ simp[SUM_APPEND, cline_size_def, EVAL``ffi_code_start_offset``, EVAL``startup_code_size``]
      \\ simp[word_add_n2w] )
    \\ numLib.LEAST_ELIM_TAC
    \\ conj_tac >- metis_tac[]
    \\ gen_tac \\ strip_tac
    \\ `n ≤ strlen (EL ix cl)`
    by (
      CCONTR_TAC \\ fs[NOT_LESS_EQUAL]
      \\ first_x_assum drule
      \\ simp[] \\ rw[]
      \\ pop_assum mp_tac
      \\ qpat_x_assum`_ ≤ cline_size`mp_tac
      \\ Q.ISPECL_THEN[`ix`,`cl`](fn th => CONV_TAC(PATH_CONV"lrlrr"(ONCE_REWRITE_CONV[SYM th])))TAKE_DROP
      \\ simp[SUM_APPEND, cline_size_def, EVAL``ffi_code_start_offset``, EVAL``startup_code_size``]
      \\ simp[word_add_n2w] )
    \\ Cases_on`n < strlen (EL ix cl)`
    \\ fs[word_add_n2w, EL_MAP, ORD_BOUND]
    >- (
      fs[clFFITheory.validArg_def, MEM_EL, EVERY_MEM, PULL_EXISTS]
      \\ last_x_assum drule
      \\ simp[]
      \\ disj2_tac
      \\ asm_exists_tac \\ simp[]
      \\ qpat_x_assum`bytes_in_memory a _ _ _`assume_tac
      \\ drule bytes_in_memory_EL
      \\ disch_then(qspec_then`n`mp_tac)
      \\ simp[EL_MAP]
      \\ Cases_on`EL n (explode (EL ix cl))` \\ fs[]
      \\ qpat_x_assum`_ = 0w`mp_tac
      \\ rw[]
      \\ qpat_x_assum`_ ≤ cline_size`mp_tac
      \\ Q.ISPECL_THEN[`ix`,`cl`](fn th => CONV_TAC(PATH_CONV"lrlrr"(ONCE_REWRITE_CONV[SYM th])))TAKE_DROP
      \\ fs[SUM_APPEND, cline_size_def, EVAL``ffi_code_start_offset``, EVAL``startup_code_size``]
      \\ fs[word_add_n2w]
      \\ strip_tac
      \\ qpat_x_assum`_ = _ MOD _`mp_tac
      \\ simp[] )
    \\ gen_tac \\ strip_tac
    \\ qpat_x_assum`s.R 3w ∈ _`mp_tac
    \\ simp[Abbr`md`]
    \\ EVAL_TAC
    \\ fs[FFI_codes_def]
    \\ fs[LEFT_ADD_DISTRIB, ADD1, EVAL``code_start_offset _``, memory_size_def]
    \\ Cases_on`s.R 3w` \\ fs[word_add_n2w, word_ls_n2w, word_lo_n2w]
    \\ qpat_x_assum`_ ≤ cline_size`mp_tac
    \\ Q.ISPECL_THEN[`ix`,`cl`](fn th => CONV_TAC(PATH_CONV"lrlrr"(ONCE_REWRITE_CONV[SYM th])))TAKE_DROP
    \\ fs[SUM_APPEND, cline_size_def, EVAL``ffi_code_start_offset``, EVAL``startup_code_size``]
    \\ fs[word_add_n2w]
    \\ strip_tac
    \\ rfs[] \\ fs[]
    \\ rveq
    \\ fs[word_add_n2w])
  \\ strip_tac \\ fs[]
  \\ pop_assum kall_tac
  \\ simp[ag32_ffi_return_thm]
  \\ simp[Abbr`s1`, APPLY_UPDATE_THM]
  \\ simp[ag32Theory.ag32_state_component_equality]
  \\ simp[ag32_ffi_mem_update_def, APPLY_UPDATE_THM, FUN_EQ_THM]
  \\ qmatch_goalsub_abbrev_tac`A ∧ B ∧ _`
  \\ `B` by ( simp[Abbr`B`] \\ EVAL_TAC \\ rw[] )
  \\ simp[]
  \\ qunabbrev_tac`B`
  \\ pop_assum kall_tac
  \\ simp[Abbr`A`]
  \\ simp[asm_write_bytearray_append2]
  \\ rw[]
  \\ qmatch_goalsub_abbrev_tac`asm_write_bytearray _ ls`
  \\ `ls = MAP (n2w o ORD) (explode (EL ix cl))`
  by (
    simp[Abbr`ls`, LIST_EQ_REWRITE, EL_MAP]
    \\ qpat_x_assum`bytes_in_memory _ (MAP _ _) _ _`assume_tac
    \\ drule bytes_in_memory_EL
    \\ simp[] \\ strip_tac
    \\ simp[EL_MAP]
    \\ rw[]
    \\ qpat_x_assum`_ ≤ cline_size`mp_tac
    \\ Q.ISPECL_THEN[`ix`,`cl`](fn th => CONV_TAC(PATH_CONV"lrlrr"(ONCE_REWRITE_CONV[SYM th])))TAKE_DROP
    \\ fs[SUM_APPEND, cline_size_def, EVAL``ffi_code_start_offset``, EVAL``startup_code_size``]
    \\ fs[word_add_n2w]
    \\ qpat_x_assum`_ = _ MOD _`mp_tac
    \\ fs[EVAL``cline_size``]
    \\ rveq
    \\ rw[] \\ fs[] \\ rfs[]
    \\ qpat_x_assum`_ = _ MOD _`mp_tac
    \\ fs[])
  \\ simp[]
  \\ AP_THM_TAC
  \\ AP_TERM_TAC
  \\ irule EQ_SYM
  \\ simp[FUN_EQ_THM] \\ gen_tac
  \\ irule asm_write_bytearray_id
  \\ simp[EL_DROP]
  \\ rw[]
  \\ qpat_x_assum`bytes_in_memory _ bytes _ _`assume_tac
  \\ simp[APPLY_UPDATE_THM]
  \\ IF_CASES_TAC
  >- (
    pop_assum mp_tac
    \\ qpat_x_assum`_ ≤ cline_size`mp_tac
    \\ Q.ISPECL_THEN[`ix`,`cl`](fn th => CONV_TAC(PATH_CONV"lrlrr"(ONCE_REWRITE_CONV[SYM th])))TAKE_DROP
    \\ fs[SUM_APPEND, cline_size_def, EVAL``ffi_code_start_offset``, EVAL``startup_code_size``]
    \\ fs[word_add_n2w]
    \\ Cases_on`s.R 3w` \\ fs[word_add_n2w]
    \\ rw[] \\ fs[ADD1]
    \\ qpat_x_assum`n2w n ∈ _`mp_tac
    \\ simp[Abbr`md`]
    \\ EVAL_TAC \\ simp[]
    \\ fs[LEFT_ADD_DISTRIB, memory_size_def, EVAL``code_start_offset _``]
    \\ fs[word_add_n2w, word_ls_n2w, word_lo_n2w] )
  \\ Cases_on`j + strlen (EL ix cl) = 0` \\ simp[word_add_n2w]
  \\ Cases_on`j + strlen (EL ix cl) = 1` \\ simp[word_add_n2w]
  \\ drule bytes_in_memory_EL
  \\ disch_then(qspec_then`j + strlen(EL ix cl) - 2`mp_tac)
  \\ simp[]
  \\ Cases_on`s.R 3w` \\ simp[word_add_n2w]
  \\ simp[EL_CONS, PRE_SUB1]
QED

Theorem ag32_ffi_open_in_thm:
   bytes_in_memory (s.R 1w) conf s.MEM md ∧
   bytes_in_memory (s.R 3w) bytes s.MEM md ∧
   Abbrev(md = ag32_prog_addresses (LENGTH ffi_names) lc ld) ∧
   LENGTH ffi_names ≤ LENGTH FFI_codes ∧
   code_start_offset (LENGTH ffi_names) + lc + 4 * ld < memory_size ∧
   (w2n (s.R 2w) = LENGTH conf) ∧
   (w2n (s.R 4w) = LENGTH bytes) ∧ w2n (s.R 3w) + LENGTH bytes < dimword(:32) ∧
   (INDEX_OF "open_in" ffi_names = SOME index) ∧
   (ffi_open_in conf bytes fs = SOME (FFIreturn new_bytes fs')) ∧
   ag32_fs_ok fs ∧
   (s.PC = n2w (ffi_code_start_offset + THE (ALOOKUP ffi_entrypoints "open_in")))
   ⇒
   (ag32_ffi_open_in s = ag32_ffi_interfer ffi_names md (index, new_bytes, s))
Proof
  simp[ag32_ffi_interfer_def]
  \\ strip_tac
  \\ drule INDEX_OF_IMP_EL
  \\ rw[ag32_ffi_open_in_def,ag32_ffi_fail_def]
  \\ simp[ag32Theory.dfn'StoreMEMByte_def, ag32Theory.incPC_def, ag32Theory.ri2word_def,ag32Theory.dfn'LoadConstant_def]
  \\ simp[ag32_ffi_return_thm]
  \\ simp[ag32Theory.ag32_state_component_equality]
  \\ qmatch_goalsub_abbrev_tac`A ∧ B ∧ C ∧ _`
  \\ `B` by (
    simp[Abbr`B`] \\ EVAL_TAC \\ rw[] )
  \\ `C` by (
    simp[Abbr`C`]  \\EVAL_TAC
    \\ simp[FUN_EQ_THM,APPLY_UPDATE_THM])
  \\ simp[Abbr`A`,ag32_ffi_mem_update_def,FUN_EQ_THM]
  \\ rw[]
  \\ EVAL_TAC
  \\ simp[APPLY_UPDATE_THM]
  \\ match_mp_tac EQ_SYM
  \\ Cases_on`bytes`
  >- ( fs[fsFFITheory.ffi_open_in_def] )
  \\ `new_bytes = 1w :: t` by (
    fs[fsFFITheory.ffi_open_in_def,OPTION_CHOICE_EQUALS_OPTION]
    >-
      (pairarg_tac>>fs[fsFFITheory.openFile_def]>>
      fs[ag32_fs_ok_def]>>
      imp_res_tac fsFFIPropsTheory.STD_streams_nextFD>>
      fs[])
    >>
    rw[]>>fs[LUPDATE_def])
  \\ simp[asm_write_bytearray_def,APPLY_UPDATE_THM]
  \\ IF_CASES_TAC >> fs[]
  \\ IF_CASES_TAC
  >-
    (match_mp_tac asm_write_bytearray_unchanged >>
    fs[APPLY_UPDATE_THM]>>
    fs[bytes_in_memory_def]
    \\ rveq
    \\ qpat_x_assum`_ ∈ md`mp_tac
    \\ simp[Abbr`md`]
    \\ Cases_on`s.R 3w`
    \\ EVAL_TAC
    \\ fs[word_ls_n2w, word_lo_n2w, EVAL``code_start_offset _``, memory_size_def, LEFT_ADD_DISTRIB])
  >>
    fs[bytes_in_memory_def]>>
    drule bytes_in_memory_change_mem>>
    qmatch_goalsub_abbrev_tac`_ _ t mm x`>>
    disch_then(qspec_then`mm` mp_tac)>>
    impl_tac
    >-
      (rw[Abbr`mm`,APPLY_UPDATE_THM]>>
      rfs[]>>
      drule bytes_in_memory_in_domain
      \\ disch_then drule
      \\ simp[Abbr`md`]
      \\ Cases_on`s.R 3w`
      \\ EVAL_TAC
      \\ fs[word_ls_n2w, word_lo_n2w, EVAL``code_start_offset _``, memory_size_def, LEFT_ADD_DISTRIB]
      \\ fs[word_add_n2w]
      \\ strip_tac \\ fs[] \\ rfs[ADD1]
      \\ qpat_x_assum`_ = _ MOD _`mp_tac \\ simp[])
    >>
    strip_tac>>
    drule bytes_in_memory_IMP_asm_write_bytearray>>
    fs[Abbr`mm`,APPLY_UPDATE_THM]
QED

Theorem ag32_ffi_open_out_thm:
   bytes_in_memory (s.R 1w) conf s.MEM md ∧
   bytes_in_memory (s.R 3w) bytes s.MEM md ∧
   Abbrev(md = ag32_prog_addresses (LENGTH ffi_names) lc ld) ∧
   LENGTH ffi_names ≤ LENGTH FFI_codes ∧
   code_start_offset (LENGTH ffi_names) + lc + 4 * ld < memory_size ∧
   (w2n (s.R 2w) = LENGTH conf) ∧
   (w2n (s.R 4w) = LENGTH bytes) ∧ w2n (s.R 3w) + LENGTH bytes < dimword(:32) ∧
   (INDEX_OF "open_out" ffi_names = SOME index) ∧
   (ffi_open_out conf bytes fs = SOME (FFIreturn new_bytes fs')) ∧
   ag32_fs_ok fs ∧
   (s.PC = n2w (ffi_code_start_offset + THE (ALOOKUP ffi_entrypoints "open_out")))
   ⇒
   (ag32_ffi_open_out s = ag32_ffi_interfer ffi_names md (index, new_bytes, s))
Proof
  simp[ag32_ffi_interfer_def]
  \\ strip_tac
  \\ drule INDEX_OF_IMP_EL
  \\ rw[ag32_ffi_open_out_def,ag32_ffi_fail_def]
  \\ simp[ag32Theory.dfn'StoreMEMByte_def, ag32Theory.incPC_def, ag32Theory.ri2word_def,ag32Theory.dfn'LoadConstant_def]
  \\ simp[ag32_ffi_return_thm]
  \\ simp[ag32Theory.ag32_state_component_equality]
  \\ qmatch_goalsub_abbrev_tac`A ∧ B ∧ C ∧ _`
  \\ `B` by (
    simp[Abbr`B`] \\ EVAL_TAC \\ rw[] )
  \\ `C` by (
    simp[Abbr`C`]  \\EVAL_TAC
    \\ simp[FUN_EQ_THM,APPLY_UPDATE_THM])
  \\ simp[Abbr`A`,ag32_ffi_mem_update_def,FUN_EQ_THM]
  \\ rw[]
  \\ EVAL_TAC
  \\ simp[APPLY_UPDATE_THM]
  \\ match_mp_tac EQ_SYM
  \\ Cases_on`bytes`>>fs[]
  >- ( fs[fsFFITheory.ffi_open_out_def] )
  \\ `new_bytes = 1w :: t` by (
    fs[fsFFITheory.ffi_open_out_def,OPTION_CHOICE_EQUALS_OPTION]
    >-
      (pairarg_tac>>fs[fsFFITheory.openFile_truncate_def]>>
      fs[ag32_fs_ok_def]>>
      imp_res_tac fsFFIPropsTheory.STD_streams_nextFD>>
      fs[])
    >>
    rw[]>>fs[LUPDATE_def])
  \\ simp[asm_write_bytearray_def,APPLY_UPDATE_THM]
  \\ IF_CASES_TAC >> fs[]
  \\ IF_CASES_TAC
  >-
    (match_mp_tac asm_write_bytearray_unchanged >>
    fs[APPLY_UPDATE_THM]>>
    fs[bytes_in_memory_def]
    \\ rveq
    \\ qpat_x_assum`_ ∈ md`mp_tac
    \\ simp[Abbr`md`]
    \\ Cases_on`s.R 3w`
    \\ EVAL_TAC
    \\ fs[word_ls_n2w, word_lo_n2w, EVAL``code_start_offset _``, memory_size_def, LEFT_ADD_DISTRIB])
  >>
    fs[bytes_in_memory_def]>>
    drule bytes_in_memory_change_mem>>
    qmatch_goalsub_abbrev_tac`_ _ t mm x`>>
    disch_then(qspec_then`mm` mp_tac)>>
    impl_tac
    >-
      (rw[Abbr`mm`,APPLY_UPDATE_THM]>>
      rfs[]>>
      drule bytes_in_memory_in_domain
      \\ disch_then drule
      \\ simp[Abbr`md`]
      \\ Cases_on`s.R 3w`
      \\ EVAL_TAC
      \\ fs[word_ls_n2w, word_lo_n2w, EVAL``code_start_offset _``, memory_size_def, LEFT_ADD_DISTRIB]
      \\ fs[word_add_n2w]
      \\ strip_tac \\ fs[] \\ rfs[ADD1]
      \\ qpat_x_assum`_ = _ MOD _`mp_tac \\ simp[])
    >>
    strip_tac>>
    drule bytes_in_memory_IMP_asm_write_bytearray>>
    fs[Abbr`mm`,APPLY_UPDATE_THM]
QED

Theorem ag32_ffi_close_thm:
   bytes_in_memory (s.R 1w) conf s.MEM md ∧
   bytes_in_memory (s.R 3w) bytes s.MEM md ∧
   Abbrev(md = ag32_prog_addresses (LENGTH ffi_names) lc ld) ∧
   LENGTH ffi_names ≤ LENGTH FFI_codes ∧
   code_start_offset (LENGTH ffi_names) + lc + 4 * ld < memory_size ∧
   (w2n (s.R 2w) = LENGTH conf) ∧
   (w2n (s.R 4w) = LENGTH bytes) ∧ w2n (s.R 3w) + LENGTH bytes < dimword(:32) ∧
   (INDEX_OF "close" ffi_names = SOME index) ∧
   (ffi_close conf bytes fs = SOME (FFIreturn new_bytes fs')) ∧
   ag32_fs_ok fs ∧
   (s.PC = n2w (ffi_code_start_offset + THE (ALOOKUP ffi_entrypoints "close")))
   ⇒
   (ag32_ffi_close s = ag32_ffi_interfer ffi_names md (index, new_bytes, s))
Proof
  simp[ag32_ffi_interfer_def]
  \\ strip_tac
  \\ drule INDEX_OF_IMP_EL
  \\ rw[ag32_ffi_close_def,ag32_ffi_fail_def]
  \\ simp[ag32Theory.dfn'StoreMEMByte_def, ag32Theory.incPC_def, ag32Theory.ri2word_def,ag32Theory.dfn'LoadConstant_def]
  \\ simp[ag32_ffi_return_thm]
  \\ simp[ag32Theory.ag32_state_component_equality]
  \\ qmatch_goalsub_abbrev_tac`A ∧ B ∧ C ∧ _`
  \\ `B` by (
    simp[Abbr`B`] \\ EVAL_TAC \\ rw[] )
  \\ `C` by (
    simp[Abbr`C`]  \\EVAL_TAC
    \\ simp[FUN_EQ_THM,APPLY_UPDATE_THM])
  \\ simp[Abbr`A`,ag32_ffi_mem_update_def,FUN_EQ_THM]
  \\ rw[]
  \\ EVAL_TAC
  \\ simp[APPLY_UPDATE_THM]
  \\ match_mp_tac EQ_SYM
  \\ Cases_on`bytes`>>fs[]
  >- fs[fsFFITheory.ffi_close_def]
  \\ `new_bytes = 1w :: t` by (
    fs[fsFFITheory.ffi_close_def,OPTION_CHOICE_EQUALS_OPTION]
    >-
      (pairarg_tac>>fs[fsFFITheory.closeFD_def]>>
       pairarg_tac \\ fs[] \\ rveq
       \\ fs[ag32_fs_ok_def]
       \\ metis_tac[NOT_SOME_NONE])
    >>
    rw[]>>fs[LUPDATE_def])
  \\ simp[asm_write_bytearray_def,APPLY_UPDATE_THM]
  \\ IF_CASES_TAC >> fs[]
  \\ IF_CASES_TAC
  >-
    (match_mp_tac asm_write_bytearray_unchanged >>
    fs[APPLY_UPDATE_THM]>>
    fs[bytes_in_memory_def]
    \\ rveq
    \\ qpat_x_assum`_ ∈ md`mp_tac
    \\ simp[Abbr`md`]
    \\ Cases_on`s.R 3w`
    \\ EVAL_TAC
    \\ fs[word_ls_n2w, word_lo_n2w, EVAL``code_start_offset _``, memory_size_def, LEFT_ADD_DISTRIB])
  >>
    fs[bytes_in_memory_def]>>
    drule bytes_in_memory_change_mem>>
    qmatch_goalsub_abbrev_tac`_ _ t mm x`>>
    disch_then(qspec_then`mm` mp_tac)>>
    impl_tac
    >-
      (rw[Abbr`mm`,APPLY_UPDATE_THM]>>
      rfs[]>>
      drule bytes_in_memory_in_domain
      \\ disch_then drule
      \\ simp[Abbr`md`]
      \\ Cases_on`s.R 3w`
      \\ EVAL_TAC
      \\ fs[word_ls_n2w, word_lo_n2w, EVAL``code_start_offset _``, memory_size_def, LEFT_ADD_DISTRIB]
      \\ fs[word_add_n2w]
      \\ strip_tac \\ fs[] \\ rfs[ADD1]
      \\ qpat_x_assum`_ = _ MOD _`mp_tac \\ simp[])
    >>
    strip_tac>>
    drule bytes_in_memory_IMP_asm_write_bytearray>>
    fs[Abbr`mm`,APPLY_UPDATE_THM]
QED

Theorem ag32_ffi__thm:
   bytes_in_memory (s.R 1w) conf s.MEM md ∧
   bytes_in_memory (s.R 3w) bytes s.MEM md ∧
   Abbrev(md = ag32_prog_addresses (LENGTH ffi_names) lc ld) ∧
   LENGTH ffi_names ≤ LENGTH FFI_codes ∧
   code_start_offset (LENGTH ffi_names) + lc + 4 * ld < memory_size ∧
   (w2n (s.R 2w) = LENGTH conf) ∧
   (w2n (s.R 4w) = LENGTH bytes) ∧ w2n (s.R 3w) + LENGTH bytes < dimword(:32) ∧
   (INDEX_OF "" ffi_names = SOME index) ∧
   (s.PC = n2w (ffi_code_start_offset + THE (ALOOKUP ffi_entrypoints "")))
   ⇒
   (ag32_ffi_ s = ag32_ffi_interfer ffi_names md (index, bytes, s))
Proof
  reverse (rw[ag32_ffi_interfer_def])
  >-
    (drule INDEX_OF_IMP_EL >> fs[])
  >> simp[ag32_ffi__def]
  \\ rw[ag32Theory.dfn'Normal_def, ag32Theory.incPC_def, ag32Theory.ri2word_def,
        ag32Theory.norm_def, ag32Theory.ALU_def,
        ag32Theory.dfn'Interrupt_def, ag32Theory.dfn'Jump_def]
  \\ rw[ag32Theory.ag32_state_component_equality, APPLY_UPDATE_THM, FUN_EQ_THM]
  \\ EVAL_TAC
QED

Theorem ag32_fs_ok_stdin_fs:
   ag32_fs_ok (stdin_fs inp)
Proof
  rw[ag32_fs_ok_def, STD_streams_stdin_fs]
  \\ rw[stdin_fs_def]
  \\ fs[stdin_fs_def, CaseEq"bool"]
QED

Theorem ag32_ffi_rel_write_mem_update:
   (ffi_write conf bytes fs = SOME (FFIreturn new_bytes fs')) ∧
   (m ((n2w (ffi_code_start_offset - 1)):word32) = n2w (THE (ALOOKUP FFI_codes "write"))) ∧
    ag32_fs_ok fs
   ⇒
   (get_ag32_io_event
     (ag32_ffi_mem_update "write" conf bytes new_bytes m)
    = get_output_io_event (IO_event "write" conf (ZIP (bytes,new_bytes))))
Proof
  rw[]
  \\ imp_res_tac fsFFIPropsTheory.ffi_write_length
  \\ fs[fsFFITheory.ffi_write_def]
  \\ fs[CaseEq"list"]
  \\ rveq
  \\ simp[get_output_io_event_def, MAP_ZIP]
  \\ rewrite_tac[GSYM EL] \\ simp[EL_ZIP]
  \\ reverse IF_CASES_TAC
  >- (
    simp[ag32_ffi_mem_update_def]
    \\ simp[get_ag32_io_event_def, APPLY_UPDATE_THM]
    \\ IF_CASES_TAC
    >- (pop_assum mp_tac \\ EVAL_TAC)
    \\ simp[] )
  \\ simp[ag32_ffi_mem_update_def]
  \\ simp[get_ag32_io_event_def]
  \\ reverse(Cases_on`LENGTH conf = 8` \\ fs[])
  >- ( rveq \\ fs[LUPDATE_def] )
  \\ reverse(Cases_on`w22n [off1; off0] ≤ LENGTH tll` \\ fs[])
  >- ( rveq \\ fs[LUPDATE_def] )
  \\ fs[fsFFITheory.write_def]
  \\ Cases_on`ALOOKUP fs.infds (w82n conf)` \\ fs[]
  >- ( rveq \\ fs[LUPDATE_def] )
  \\ pairarg_tac \\ fs[]
  \\ fs[ag32_fs_ok_def]
  \\ `∃cnt. (ALOOKUP fs.inode_tbl ino = SOME cnt)` by metis_tac[]
  \\ reverse(fs[OPTION_CHOICE_EQUALS_OPTION])
  >- ( rveq \\ fs[LUPDATE_def] )
  >- ( rveq \\ fs[LUPDATE_def] )
  \\ rveq \\ fs[]
  \\ `w82n conf < 3` by metis_tac[IS_SOME_EXISTS]
  \\ `HD conf = 0w`
  by (
    fs[LENGTH_EQ_NUM_compute]
    \\ rveq \\ fs[MarshallingTheory.w82n_def]
    \\ Cases_on`h` \\ fs[] )
  \\ conj_tac
  >- (
    irule asm_write_bytearray_unchanged
    \\ simp[]
    \\ fs[EVAL``output_offset``, EVAL``ffi_code_start_offset``]
    \\ simp[word_add_n2w, word_ls_n2w, word_lo_n2w]
    \\ simp[EVAL``output_buffer_size``]
    \\ simp[MIN_DEF] )
  \\ reverse IF_CASES_TAC
  >- (
    fs[LENGTH_EQ_NUM_compute]
    \\ rveq \\ fs[]
    \\ rveq
    \\ fs[asm_write_bytearray_def, APPLY_UPDATE_THM] )
  \\ qmatch_goalsub_abbrev_tac`w22n [n1'; n0']`
  \\ `n1' = n1`
  by (
    simp[Abbr`n1'`]
    \\ qmatch_goalsub_abbrev_tac`asm_write_bytearray _ ls`
    \\ `n1 = EL 10 ls` by ( simp[Abbr`ls`, EL_APPEND_EQN] )
    \\ pop_assum SUBST1_TAC
    \\ simp[GSYM word_add_n2w]
    \\ irule asm_write_bytearray_EL
    \\ simp[Abbr`ls`]
    \\ simp[MIN_DEF, output_buffer_size_def] )
  \\ qpat_x_assum`Abbrev(n1' = _)`kall_tac
  \\ `n0' = n0`
  by (
    simp[Abbr`n0'`]
    \\ qmatch_goalsub_abbrev_tac`asm_write_bytearray _ ls`
    \\ `n0 = EL 11 ls` by ( simp[Abbr`ls`, EL_APPEND_EQN] )
    \\ pop_assum SUBST1_TAC
    \\ simp[GSYM word_add_n2w]
    \\ irule asm_write_bytearray_EL
    \\ simp[Abbr`ls`]
    \\ simp[MIN_DEF, output_buffer_size_def] )
  \\ qpat_x_assum`Abbrev(n0' = _)`kall_tac
  \\ irule data_to_word_assignProofTheory.IMP_read_bytearray_GENLIST
  \\ simp[]
  \\ gen_tac \\ strip_tac
  \\ `n2w i + n2w output_offset :word32= (n2w output_offset) + n2w i` by simp[]
  \\ pop_assum SUBST1_TAC
  \\ DEP_REWRITE_TAC[asm_write_bytearray_EL]
  \\ simp[]
  \\ simp[MIN_DEF, output_buffer_size_def]
QED

Theorem ag32_fs_ok_ffi_write:
   (ffi_write conf bytes fs = SOME (FFIreturn bytes' fs')) ∧ ag32_fs_ok fs ⇒
   ag32_fs_ok fs'
Proof
  rw[fsFFITheory.ffi_write_def,CaseEq"list"]
  \\ fs[ag32_fs_ok_def]
  \\ `STD_streams fs'`
  by (
    fs[OPTION_CHOICE_EQUALS_OPTION] \\ rveq \\ fs[]
    \\ pairarg_tac \\ fs[] \\ rveq
    \\ fs[fsFFITheory.write_def]
    \\ pairarg_tac \\ fs[] \\ rveq
    \\ irule fsFFIPropsTheory.STD_streams_fsupdate
    \\ simp[]
    \\ first_x_assum drule
    \\ simp[] )
  \\ conj_tac
  >- (
    fs[OPTION_CHOICE_EQUALS_OPTION] \\ rveq \\ fs[]
    \\ pairarg_tac \\ fs[fsFFITheory.write_def]
    \\ pairarg_tac \\ fs[]
    \\ rw[fsFFITheory.fsupdate_def, LDROP1_THM] )
  \\ conj_tac
  >- (
    fs[OPTION_CHOICE_EQUALS_OPTION] \\ rveq \\ fs[]
    \\ pairarg_tac \\ fs[fsFFITheory.write_def]
    \\ pairarg_tac \\ fs[]
    \\ rw[fsFFITheory.fsupdate_def, AFUPDKEY_ALOOKUP]
    \\ PURE_TOP_CASE_TAC \\ simp[] \\ rw[]
    \\ metis_tac[NOT_SOME_NONE, IS_SOME_EXISTS] )
  \\ fs[OPTION_CHOICE_EQUALS_OPTION, fsFFITheory.write_def]
  \\ rpt(pairarg_tac \\ fs[])
  \\ rveq \\ fs[fsFFITheory.fsupdate_def, AFUPDKEY_ALOOKUP, LDROP1_THM]
  \\ rw[]
  \\ fs[CaseEq"option"]
  \\ PairCases_on`v` \\ fs[]
  \\ fs[CaseEq"bool",PULL_EXISTS] \\ rveq
  >- (
    first_x_assum drule
    \\ rw[] \\ rw[]
    \\ Cases_on`ino = ino'` \\ fs[]
    \\ strip_tac \\ fs[] )
  \\ first_assum drule
  \\ strip_tac \\ fs[]
  \\ Cases_on`ino = ino'` \\ fs[]
  \\ fs[LENGTH_TAKE_EQ]
  \\ qmatch_goalsub_abbrev_tac`f12 ⇒ _`
  \\ strip_tac \\ fs[] \\ rveq
  \\ `w82n conf < 3` by metis_tac[IS_SOME_EXISTS]
  \\ pop_assum mp_tac
  \\ simp[NUMERAL_LESS_THM]
  \\ first_x_assum(qspec_then`w82n conf`mp_tac)
  \\ simp[]
  \\ rw[] \\ fs[] \\ rw[] \\ fs[] \\ rfs[]
  \\ qpat_x_assum`STD_streams fs`mp_tac
  \\ simp[fsFFIPropsTheory.STD_streams_def]
  \\ strip_tac
  \\ TRY (
    first_x_assum(qspecl_then[`2`,`WriteMode`,`LENGTH err`]mp_tac)
    \\ simp[] \\ strip_tac \\ rveq
    \\ first_x_assum(qspecl_then[`fd`,`WriteMode`,`LENGTH out`]mp_tac)
    \\ simp[] \\ NO_TAC )
  \\ TRY (
    first_x_assum(qspecl_then[`fd`,`WriteMode`,`LENGTH err`]mp_tac)
    \\ simp[] \\ strip_tac \\ rveq
    \\ first_x_assum(qspecl_then[`1`,`WriteMode`,`LENGTH out`]mp_tac)
    \\ simp[] \\ NO_TAC )
  \\ TRY (
    last_x_assum(qspecl_then[`0`,`ReadMode`,`inp`]mp_tac)
    \\ simp[] \\ NO_TAC )
QED

Theorem ag32_stdin_implemented_ffi_write:
     STD_streams fs ∧
  ag32_stdin_implemented fs m ∧
   ffi_write conf bytes fs = SOME (FFIreturn bytes' fs') ∧
   w2n (ms.R 3w) + LENGTH bytes' < 4294967296 ∧
   n2w heap_start_offset <=+ ms.R 3w
   ⇒
   ag32_stdin_implemented fs'
     (ag32_ffi_mem_update "write" conf bytes bytes'
       (asm_write_bytearray (ms.R 3w) bytes'
         ((n2w (ffi_code_start_offset - 1) =+
           n2w (THE (ALOOKUP FFI_codes "write"))) m)))
Proof
  rw[ag32_stdin_implemented_def]
  \\ qexists_tac`off`
  \\ qexists_tac`inp`
  \\ simp[]
  \\ CONJ_TAC>- (
    fs[fsFFITheory.ffi_write_def,fsFFITheory.write_def]>>
    every_case_tac>>
    fs[OPTION_CHOICE_EQUALS_OPTION, LUPDATE_def] \\ rveq \\ fs[] \\
    rpt(pairarg_tac>>fs[])>>
    fs[OPTION_CHOICE_EQUALS_OPTION, LUPDATE_def] \\ rveq \\ fs[] \\
    fs[fsFFITheory.fsupdate_def]>>
    simp[AFUPDKEY_ALOOKUP]>>
    rw[]>>fs[])
  \\ CONJ_TAC>- (
    fs[fsFFITheory.ffi_write_def,fsFFITheory.write_def]>>
    every_case_tac>>
    fs[OPTION_CHOICE_EQUALS_OPTION, LUPDATE_def] \\ rveq \\ fs[] \\
    rpt(pairarg_tac>>fs[])>>
    fs[OPTION_CHOICE_EQUALS_OPTION, LUPDATE_def] \\ rveq \\ fs[] \\
    fs[fsFFITheory.fsupdate_def]>>
    simp[AFUPDKEY_ALOOKUP]>>
    rw[]>>fs[]>>
    fs[fsFFIPropsTheory.STD_streams_def]>>
    rfs[])
  \\ simp[CONJ_ASSOC]
  \\ conj_tac
  >- (
    fs[fsFFITheory.ffi_write_def,fsFFITheory.write_def, EVAL``heap_start_offset``]
    \\ every_case_tac
    \\ fs[OPTION_CHOICE_EQUALS_OPTION, LUPDATE_def] \\ rveq \\ fs[]
    \\ simp[ag32_ffi_mem_update_def]
    >- (
      fs[fsFFITheory.write_def]>>
      rpt(pairarg_tac>>fs[])>>rveq>>fs[]>>
      DEP_REWRITE_TAC [get_mem_word_asm_write_bytearray_UNCHANGED_LT,get_mem_word_UPDATE]>>
      fs[]>>EVAL_TAC>>
      fs[MarshallingTheory.n2w2_def,MarshallingTheory.w22n_def,MIN_DEF]>>
      blastLib.FULL_BBLAST_TAC)
    >>
      DEP_REWRITE_TAC [get_mem_word_UPDATE,get_mem_word_asm_write_bytearray_UNCHANGED_LT]>>
      fs[]>>EVAL_TAC>>
      blastLib.FULL_BBLAST_TAC)
  >>
    (
    fs[fsFFITheory.ffi_write_def,fsFFITheory.write_def]
    \\ every_case_tac
    \\ fs[OPTION_CHOICE_EQUALS_OPTION, LUPDATE_def] \\ rveq \\ fs[]
    \\ simp[ag32_ffi_mem_update_def]
    >- (
      fs[fsFFITheory.write_def]>>
      rpt(pairarg_tac>>fs[])>>rveq>>fs[]>>
      DEP_REWRITE_TAC[bytes_in_memory_UPDATE_LT,bytes_in_memory_asm_write_bytearray_LT]>>
      fs[stdin_size_def]>>EVAL_TAC>>fs[MIN_DEF]>>
      `5242880+2300 ≤ w2n (ms.R 3w)` suffices_by fs[]>>
      simp[]>>
      fs[WORD_LS,EVAL``heap_start_offset``])
    >>
    DEP_REWRITE_TAC[bytes_in_memory_UPDATE_LT,bytes_in_memory_asm_write_bytearray_LT]>>
    fs[stdin_size_def]>>
    EVAL_TAC>>fs[]>>
    `5242880+2300 ≤ w2n (ms.R 3w)` suffices_by fs[]>>
    simp[]>>
    fs[WORD_LS,EVAL``heap_start_offset``])
QED

Theorem ag32_cline_implemented_ffi_write:
   ag32_cline_implemented cl m ∧
   w2n (ms.R 3w) + LENGTH bytes' < dimword(:32) ∧
   n2w heap_start_offset <=+ ms.R 3w ∧
   (ffi_write conf bytes fs = SOME (FFIreturn bytes' fs'))
   ⇒
   ag32_cline_implemented cl
     (ag32_ffi_mem_update "write" conf bytes bytes'
       (asm_write_bytearray (ms.R 3w) bytes'
         ((n2w (ffi_code_start_offset - 1) =+
           n2w (THE (ALOOKUP FFI_codes "write"))) m)))
Proof
  simp[ag32_cline_implemented_def]
  \\ strip_tac
  \\ qmatch_goalsub_abbrev_tac`get_mem_word m'`
  \\ pop_assum mp_tac
  \\ simp[ag32_ffi_mem_update_def]
  \\ imp_res_tac fsFFIPropsTheory.ffi_write_length
  \\ fs[fsFFITheory.ffi_write_def, CaseEq"list"]
  \\ rveq
  \\ strip_tac
  \\ conj_tac
  >- (
    simp[Abbr`m'`]
    \\ IF_CASES_TAC
    >- (
      DEP_REWRITE_TAC[get_mem_word_asm_write_bytearray_UNCHANGED_LT]
      \\ conj_tac
      >- (
        EVAL_TAC \\ fs[]
        \\ Cases_on`ms.R 3w` \\ fs[]
        \\ fs[word_ls_n2w, word_lo_n2w]
        \\ simp[LENGTH_TAKE_EQ_MIN]
        \\ qmatch_goalsub_abbrev_tac`LENGTH conf + (k + _)`
        \\ `k ≤ 2048` by simp[Abbr`k`]
        \\ reverse(Cases_on`LENGTH conf = 8` \\ fs[])
        >- ( rveq \\ fs[LUPDATE_def] )
        \\ fs[EVAL``heap_start_offset``] )
      \\ DEP_REWRITE_TAC[get_mem_word_UPDATE]
      \\ conj_tac >- EVAL_TAC
      \\ simp[] )
    \\ DEP_REWRITE_TAC[get_mem_word_UPDATE]
    \\ conj_tac >- EVAL_TAC
    \\ DEP_REWRITE_TAC[get_mem_word_asm_write_bytearray_UNCHANGED_LT]
    \\ conj_tac
    >- (
      EVAL_TAC \\ fs[]
      \\ Cases_on`ms.R 3w` \\ fs[]
      \\ fs[word_ls_n2w, word_lo_n2w]
      \\ fs[EVAL``heap_start_offset``] )
    \\ DEP_REWRITE_TAC[get_mem_word_UPDATE]
    \\ conj_tac >- EVAL_TAC
    \\ simp[] )
  \\ irule bytes_in_memory_change_mem
  \\ goal_assum(first_assum o mp_then Any mp_tac)
  \\ simp[LENGTH_FLAT, MAP_MAP_o, o_DEF, ADD1, SUM_MAP_PLUS]
  \\ simp[Q.ISPEC`λx. 1n`SUM_MAP_K |> SIMP_RULE(srw_ss())[]]
  \\ rw[]
  \\ simp[Abbr`m'`]
  \\ rw[]
  >- (
    irule EQ_SYM
    \\ irule asm_write_bytearray_unchanged_all_words
    \\ conj_tac
    >- (
      simp[IN_all_words, LENGTH_TAKE_EQ_MIN]
      \\ EVAL_TAC
      \\ simp[DISJ_EQ_IMP]
      \\ qmatch_goalsub_abbrev_tac`LENGTH conf + (k + _)`
      \\ `k ≤ 2048` by simp[Abbr`k`]
      \\ reverse(Cases_on`LENGTH conf = 8` \\ fs[])
      >- ( rveq \\ fs[LUPDATE_def] )
      \\ fs[EVAL``cline_size``] )
    \\ irule EQ_SYM
    \\ irule asm_write_bytearray_unchanged_all_words
    \\ conj_tac
    >- (
      simp[IN_all_words, word_add_n2w, ADD1, DISJ_EQ_IMP]
      \\ Cases_on`ms.R 3w` \\ fs[EVAL``heap_start_offset``, ADD1]
      \\ simp[word_add_n2w, EVAL``startup_code_size``]
      \\ rw[]
      \\ fs[EVAL``cline_size``]
      \\ fs[word_lo_n2w, word_ls_n2w] )
    \\ simp[APPLY_UPDATE_THM]
    \\ rw[]
    \\ pop_assum mp_tac
    \\ EVAL_TAC
    \\ fs[EVAL``cline_size``] )
  \\ simp[APPLY_UPDATE_THM]
  \\ IF_CASES_TAC
  >- (
    pop_assum mp_tac
    \\ EVAL_TAC
    \\ fs[EVAL``cline_size``] )
  \\ irule EQ_SYM
  \\ irule asm_write_bytearray_unchanged_all_words
  \\ conj_tac
  >- (
    simp[IN_all_words, word_add_n2w, ADD1, DISJ_EQ_IMP]
    \\ Cases_on`ms.R 3w` \\ fs[EVAL``heap_start_offset``, ADD1]
    \\ simp[word_add_n2w, EVAL``startup_code_size``]
    \\ rw[]
    \\ fs[EVAL``cline_size``]
    \\ fs[word_lo_n2w, word_ls_n2w] )
  \\ simp[APPLY_UPDATE_THM]
  \\ rw[]
  \\ pop_assum mp_tac
  \\ EVAL_TAC
  \\ fs[EVAL``cline_size``]
QED

Theorem ag32_ffi_rel_read_mem_update:
   (ffi_read conf bytes fs = SOME (FFIreturn new_bytes fs')) ∧
   (m ((n2w (ffi_code_start_offset - 1)):word32) = n2w (THE (ALOOKUP FFI_codes "read"))) ∧
    ag32_fs_ok fs
   ⇒
   (get_ag32_io_event
     (ag32_ffi_mem_update "read" conf bytes new_bytes m)
    = get_output_io_event (IO_event "read" conf (ZIP (bytes,new_bytes))))
Proof
  rw[]
  \\ imp_res_tac fsFFIPropsTheory.ffi_read_length
  \\ fs[fsFFITheory.ffi_read_def]
  \\ fs[CaseEq"list"]
  \\ rveq
  \\ simp[get_output_io_event_def, MAP_ZIP]
  \\ simp[ag32_ffi_mem_update_def]
  \\ fs[]
  \\ PURE_CASE_TAC \\ fs[]
  \\ PURE_TOP_CASE_TAC \\ fs[]
  \\ PURE_TOP_CASE_TAC \\ fs[]
  \\ simp[get_ag32_io_event_def]
  \\ reverse(Cases_on`LENGTH conf = 8` \\ fs[])
  >- ( rveq \\ fs[LUPDATE_def] \\ rveq \\ simp[] \\ EVAL_TAC)
  \\ reverse(Cases_on`LENGTH tll ≥ w22n [n1; n0]`) \\ fs[]
  >- ( rveq \\ fs[LUPDATE_def] \\ rveq \\ simp[] \\ EVAL_TAC)
  \\ fs[fsFFITheory.read_def]
  \\ Cases_on`ALOOKUP fs.infds (w82n conf)` \\ fs[]
  >- ( rveq \\ fs[LUPDATE_def] \\ rveq \\ simp[] \\ EVAL_TAC)
  \\ pairarg_tac \\ fs[]
  \\ fs[ag32_fs_ok_def]
  \\ `IS_SOME (ALOOKUP fs.inode_tbl ino)` by metis_tac[IS_SOME_EXISTS]
  \\ fs[IS_SOME_EXISTS, PULL_EXISTS, EXISTS_PROD] \\ fs[]
  \\ rveq \\ fs[]
  \\ reverse(Cases_on`md` \\ fs[LUPDATE_def]) \\ rveq \\ fs[]
  \\ DEP_ONCE_REWRITE_TAC [set_mem_word_neq]>> fs[]>>
  EVAL_TAC
QED

Theorem ag32_fs_ok_ffi_read:
   (ffi_read conf bytes fs = SOME (FFIreturn bytes' fs')) ∧ ag32_fs_ok fs ⇒
   ag32_fs_ok fs'
Proof
  rw[fsFFITheory.ffi_read_def,CaseEq"list"]
  \\ fs[ag32_fs_ok_def]
  \\ `STD_streams fs'`
  by (
    fs[OPTION_CHOICE_EQUALS_OPTION] \\ rveq \\ fs[]
    \\ pairarg_tac \\ fs[] \\ rveq
    \\ fs[fsFFITheory.read_def]
    \\ pairarg_tac \\ fs[] \\ rveq
    \\ reverse(Cases_on`w82n conf = 1 ∨ w82n conf = 2`)
    >- ( fs[fsFFIPropsTheory.STD_streams_bumpFD] )
    \\ qhdtm_x_assum`STD_streams`mp_tac
    \\ simp[Once fsFFIPropsTheory.STD_streams_def]
    \\ strip_tac
    \\ first_x_assum(qspecl_then[`w82n conf`,`WriteMode`,`LENGTH err`]mp_tac)
    \\ first_x_assum(qspecl_then[`w82n conf`,`WriteMode`,`LENGTH out`]mp_tac)
    \\ fs[] )
  \\ fs[OPTION_CHOICE_EQUALS_OPTION, fsFFITheory.read_def]
  \\ rpt(pairarg_tac \\ fs[])
  \\ rveq \\ fs[fsFFITheory.fsupdate_def, AFUPDKEY_ALOOKUP, LDROP1_THM,
                fsFFITheory.bumpFD_def]
  \\ conj_tac
  >- (
    rw[] \\ every_case_tac \\ fs[]
    \\ metis_tac[IS_SOME_EXISTS, NOT_SOME_NONE])
  \\ rw[]
  \\ fs[CaseEq"option"]
  \\ PairCases_on`v` \\ fs[]
  \\ fs[CaseEq"bool",PULL_EXISTS] \\ rveq
  >- (
    first_x_assum drule
    \\ rw[] \\ rw[]
    \\ Cases_on`ino = ino'` \\ fs[])
QED

Theorem ag32_stdin_implemented_ffi_read:
   ag32_fs_ok fs ∧
   ag32_stdin_implemented fs m ∧
   ffi_read conf bytes fs = SOME (FFIreturn bytes' fs') ∧
   w2n (ms.R 3w) + LENGTH bytes' < 4294967296 ∧
   n2w heap_start_offset <=+ ms.R 3w
   (* you may assume more here from the context where this is used *)
   ⇒
   ag32_stdin_implemented fs'
     (ag32_ffi_mem_update "read" conf bytes bytes'
       (asm_write_bytearray (ms.R 3w) bytes'
         ((n2w (ffi_code_start_offset - 1) =+
           n2w (THE (ALOOKUP FFI_codes "read"))) m)))
Proof
  rw[]>>fs[fsFFITheory.ffi_read_def, fsFFITheory.read_def]>>
  fs[CaseEq"list"]>>
  fs[OPTION_CHOICE_EQUALS_OPTION] \\ rveq \\ fs[] \\ rfs[]
  >- (
    rpt(pairarg_tac>>fs[])>>rveq>>
    fs[ag32_stdin_implemented_def]>>fs[]>>
    fs[ag32_ffi_mem_update_def,MarshallingTheory.n2w2_def,MarshallingTheory.w22n_def]>>
    DEP_REWRITE_TAC[get_mem_word_set_mem_word]>>
    CONJ_TAC>-
      EVAL_TAC>>
    DEP_REWRITE_TAC[get_mem_word_asm_write_bytearray_UNCHANGED_LT,get_mem_word_UPDATE]>>
    CONJ_TAC>- (
      EVAL_TAC>>
      fs[EVAL``heap_start_offset``] >>
      rpt(CONJ_TAC>- blastLib.FULL_BBLAST_TAC)>>
      fs[MIN_DEF]>>rw[]>>fs[] >>
      blastLib.FULL_BBLAST_TAC)>>
    fs[word_add_n2w]>>
    qmatch_goalsub_abbrev_tac`ls MOD _`>>
    qexists_tac`ls`>>simp[]>>
    rw[]
    >-
      (simp[fsFFITheory.bumpFD_def,AFUPDKEY_ALOOKUP]>>
      reverse IF_CASES_TAC
      >- (
        fs[ag32_fs_ok_def]
        \\ `w82n conf < 3` by metis_tac[IS_SOME_EXISTS]
        \\ fs[fsFFIPropsTheory.STD_streams_def]
        \\ first_x_assum(qspecl_then[`w82n conf`,`WriteMode`,`LENGTH err`]mp_tac)
        \\ first_x_assum(qspecl_then[`w82n conf`,`WriteMode`,`LENGTH out`]mp_tac)
        \\ qpat_x_assum`_ < 3`mp_tac
        \\ simp[NUMERAL_LESS_THM] )
      >>
      fs[Abbr`ls`]>>
      qmatch_goalsub_abbrev_tac`nn = _`>>
      qspec_then`256` assume_tac DIVISION>>fs[]>>
      pop_assum(qspec_then`nn` assume_tac)>>
      `SUC strm = output_buffer_size + 1` by rfs[ag32_fs_ok_def, ADD1] >>
      `nn ≤ output_buffer_size + 1` by simp[Abbr`nn`, MIN_DEF] >>
      fs[EVAL``output_buffer_size``])
    >-
      (pop_assum mp_tac>>EVAL_TAC)
    >- (
      fs[ag32_fs_ok_def]
      \\ `w82n conf < 3` by metis_tac[IS_SOME_EXISTS]
      \\ fs[fsFFIPropsTheory.STD_streams_def]
      \\ first_x_assum(qspecl_then[`w82n conf`,`WriteMode`,`LENGTH err`]mp_tac)
      \\ first_x_assum(qspecl_then[`w82n conf`,`WriteMode`,`LENGTH out`]mp_tac)
      \\ qpat_x_assum`_ < 3`mp_tac
      \\ simp[NUMERAL_LESS_THM]
      \\ rw[] \\ fs[] \\ rveq
      \\ rfs[] \\ rveq
      \\ fs[EVAL``output_buffer_size``]
      \\ simp[Abbr`ls`]
      \\ fs[EVAL``stdin_size``]
      \\ qmatch_goalsub_abbrev_tac`k MOD 256`
      \\ `k < 256` by rw[Abbr`k`, MIN_DEF, DIV_LT_X] \\ fs[]
      \\ qmatch_goalsub_abbrev_tac`j MOD 256`
      \\ simp[Abbr`k`]
      \\ qmatch_goalsub_abbrev_tac`_ + k`
      \\ `k = j` by (
        simp[Abbr`k`]
        \\ qspec_then`256`mp_tac DIVISION
        \\ simp[] )
      \\ rw[]
      \\ pop_assum kall_tac
      \\ `j ≤ LENGTH content - inp'` by simp[Abbr`j`]
      \\ simp[])
    >>
      simp[set_mem_word_def]>>
      ntac 4 (DEP_ONCE_REWRITE_TAC[bytes_in_memory_UPDATE_GT])>>
      DEP_REWRITE_TAC[bytes_in_memory_asm_write_bytearray_LT,bytes_in_memory_UPDATE_LT]>>
      fs[stdin_size_def]>>
      EVAL_TAC>>fs[]>>
      fs[WORD_LS,EVAL``heap_start_offset``])
  >>
  fs[ag32_stdin_implemented_def]>>
  simp[ag32_ffi_mem_update_def]>>
  simp[LUPDATE_def]>>
  DEP_REWRITE_TAC [get_mem_word_UPDATE,get_mem_word_asm_write_bytearray_UNCHANGED_LT,bytes_in_memory_asm_write_bytearray_LT,bytes_in_memory_UPDATE_LT]>>
  fs[]>>
  EVAL_TAC>>fs[stdin_size_def]>>
  `5242880+2300 ≤ w2n (ms.R 3w)` by
    fs[WORD_LS,EVAL``heap_start_offset``]>>
  fs[]>>
  Cases_on`ms.R 3w` \\ fs[word_lo_n2w]
QED

Theorem ag32_cline_implemented_ffi_read:
   ag32_cline_implemented cl m ∧
   w2n (ms.R 3w) + LENGTH bytes' < dimword(:32) ∧
   n2w heap_start_offset <=+ ms.R 3w ∧
   (ffi_read conf bytes fs = SOME (FFIreturn bytes' fs'))
   ⇒
   ag32_cline_implemented cl
     (ag32_ffi_mem_update "read" conf bytes bytes'
       (asm_write_bytearray (ms.R 3w) bytes'
         ((n2w (ffi_code_start_offset - 1) =+
           n2w (THE (ALOOKUP FFI_codes "read"))) m)))
Proof
  simp[ag32_cline_implemented_def]
  \\ strip_tac
  \\ qmatch_goalsub_abbrev_tac`get_mem_word m'`
  \\ pop_assum mp_tac
  \\ simp[ag32_ffi_mem_update_def]
  \\ imp_res_tac fsFFIPropsTheory.ffi_read_length
  \\ fs[fsFFITheory.ffi_read_def, CaseEq"list"]
  \\ rveq
  \\ Cases_on`bytes'` \\ fs[]
  \\ Cases_on`t` \\ fs[]
  \\ Cases_on`t'` \\ fs[]
  \\ CONV_TAC(PATH_CONV"lrr"(REWR_CONV EQ_SYM_EQ)) \\ simp[]
  \\ strip_tac
  \\ conj_tac
  >- (
    simp[Abbr`m'`]
    \\ IF_CASES_TAC
    >- (
      DEP_REWRITE_TAC[get_mem_word_set_mem_word]
      \\ CONJ_TAC  >- EVAL_TAC
      \\ IF_CASES_TAC
      >- (pop_assum mp_tac \\ EVAL_TAC)
      \\ DEP_REWRITE_TAC[get_mem_word_asm_write_bytearray_UNCHANGED_LT]
      \\ conj_tac
      >- (
        EVAL_TAC \\ fs[]
        \\ Cases_on`ms.R 3w` \\ fs[]
        \\ fs[word_ls_n2w, word_lo_n2w]
        \\ fs[EVAL``heap_start_offset``] )
      \\ DEP_REWRITE_TAC[get_mem_word_UPDATE]
      \\ conj_tac >- EVAL_TAC
      \\ simp[] )
    \\ DEP_REWRITE_TAC[get_mem_word_asm_write_bytearray_UNCHANGED_LT]
    \\ conj_tac
    >- (
      EVAL_TAC \\ fs[]
      \\ Cases_on`ms.R 3w` \\ fs[]
      \\ fs[word_ls_n2w, word_lo_n2w]
      \\ fs[EVAL``heap_start_offset``] )
    \\ DEP_REWRITE_TAC[get_mem_word_UPDATE]
    \\ conj_tac >- EVAL_TAC
    \\ simp[] )
  \\ irule bytes_in_memory_change_mem
  \\ goal_assum(first_assum o mp_then Any mp_tac)
  \\ simp[LENGTH_FLAT, MAP_MAP_o, o_DEF, ADD1, SUM_MAP_PLUS]
  \\ simp[Q.ISPEC`λx. 1n`SUM_MAP_K |> SIMP_RULE(srw_ss())[]]
  \\ rw[]
  \\ simp[Abbr`m'`]
  \\ rw[]
  >- (
    irule EQ_SYM
    \\ DEP_REWRITE_TAC[set_mem_word_neq]
    \\ conj_tac
    >- (
      EVAL_TAC
      \\ fs[EVAL``cline_size``] )
    \\ irule asm_write_bytearray_unchanged_all_words
    \\ conj_tac
    >- (
      simp[IN_all_words]
      \\ EVAL_TAC
      \\ simp[DISJ_EQ_IMP]
      \\ fs[EVAL``cline_size``]
      \\ Cases_on`ms.R 3w` \\ fs[EVAL``heap_start_offset``, ADD1]
      \\ fs[word_lo_n2w, word_ls_n2w, word_add_n2w] )
    \\ simp[APPLY_UPDATE_THM]
    \\ rw[]
    \\ pop_assum mp_tac
    \\ EVAL_TAC
    \\ fs[EVAL``cline_size``] )
  \\ irule EQ_SYM
  \\ irule asm_write_bytearray_unchanged_all_words
  \\ conj_tac
  >- (
    simp[IN_all_words, word_add_n2w, ADD1, DISJ_EQ_IMP]
    \\ Cases_on`ms.R 3w` \\ fs[EVAL``heap_start_offset``, ADD1]
    \\ simp[word_add_n2w, EVAL``startup_code_size``]
    \\ fs[EVAL``cline_size``]
    \\ fs[word_lo_n2w, word_ls_n2w] )
  \\ simp[APPLY_UPDATE_THM]
  \\ rw[]
  \\ pop_assum mp_tac
  \\ EVAL_TAC
  \\ fs[EVAL``cline_size``]
QED

Theorem ag32_fs_ok_ffi_open_in:
   (ffi_open_in conf bytes fs = SOME (FFIreturn bytes' fs')) ∧ ag32_fs_ok fs ⇒
   ag32_fs_ok fs'
Proof
  rw[fsFFITheory.ffi_open_in_def,CaseEq"list"]
  \\ fs[ag32_fs_ok_def]
  \\ fs[OPTION_CHOICE_EQUALS_OPTION]
  \\ rpt(pairarg_tac \\ fs[])
  \\ rveq \\ fs[]
  \\ fs[fsFFITheory.openFile_def]
QED

Theorem ag32_fs_ok_ffi_open_out:
   (ffi_open_out conf bytes fs = SOME (FFIreturn bytes' fs')) ∧ ag32_fs_ok fs ⇒
   ag32_fs_ok fs'
Proof
  rw[fsFFITheory.ffi_open_out_def,CaseEq"list"]
  \\ fs[ag32_fs_ok_def]
  \\ fs[OPTION_CHOICE_EQUALS_OPTION]
  \\ rpt(pairarg_tac \\ fs[])
  \\ rveq \\ fs[]
  \\ fs[fsFFITheory.openFile_truncate_def]
QED

Theorem ag32_fs_ok_ffi_close:
   (ffi_close conf bytes fs = SOME (FFIreturn bytes' fs')) ∧ ag32_fs_ok fs ⇒
   ag32_fs_ok fs'
Proof
  rw[fsFFITheory.ffi_close_def,CaseEq"list"]
  \\ fs[ag32_fs_ok_def]
  \\ fs[OPTION_CHOICE_EQUALS_OPTION]
  \\ rpt(pairarg_tac \\ fs[])
  \\ rveq \\ fs[]
  \\ fs[fsFFITheory.closeFD_def]
  \\ rveq \\ fs[]
  \\ simp[ALOOKUP_ADELKEY]
  \\ pairarg_tac \\ fs[]
  \\ metis_tac[NOT_SOME_NONE]
QED

Theorem ag32_stdin_implemented_ffi_open_in:
   ag32_fs_ok fs ∧
   ag32_stdin_implemented fs m ∧
   ffi_open_in conf bytes fs = SOME (FFIreturn bytes' fs') ∧
   w2n (ms.R 3w) + LENGTH bytes' < 4294967296 ∧
   n2w heap_start_offset <=+ ms.R 3w
   ⇒
   ag32_stdin_implemented fs'
     (asm_write_bytearray (ms.R 3w) bytes'
       ((n2w (ffi_code_start_offset - 1) =+
         n2w (THE (ALOOKUP FFI_codes "open_in"))) m))
Proof
  rw[]
  \\ fs[fsFFITheory.ffi_open_in_def]
  \\ qhdtm_x_assum`OPTION_CHOICE`mp_tac
  \\ simp[OPTION_CHOICE_EQUALS_OPTION]
  \\ qmatch_goalsub_abbrev_tac`A ∨ B ⇒ _`
  \\ Cases_on`B`
  >- (
    simp[Abbr`A`]
    \\ fs[markerTheory.Abbrev_def, DISJ_EQ_IMP]
    \\ rveq
    \\ fs[ag32_stdin_implemented_def]
    \\ conj_tac
    >- (
      DEP_REWRITE_TAC[get_mem_word_asm_write_bytearray_UNCHANGED_LT]
      \\ Cases_on`ms.R 3w` \\ fs[EVAL``heap_start_offset``,EVAL``stdin_offset``]
      \\ fs[word_ls_n2w, word_lo_n2w]
      \\ DEP_REWRITE_TAC[get_mem_word_UPDATE]
      \\ conj_tac >- EVAL_TAC \\ simp[] )
    \\ conj_tac
    >- (
      DEP_REWRITE_TAC[get_mem_word_asm_write_bytearray_UNCHANGED_LT]
      \\ Cases_on`ms.R 3w` \\ fs[EVAL``heap_start_offset``,EVAL``stdin_offset``]
      \\ fs[word_ls_n2w, word_lo_n2w]
      \\ DEP_REWRITE_TAC[get_mem_word_UPDATE]
      \\ conj_tac >- EVAL_TAC \\ simp[] )
    \\ DEP_REWRITE_TAC[bytes_in_memory_asm_write_bytearray_LT]
    \\ Cases_on`ms.R 3w` \\ fs[EVAL``heap_start_offset``,EVAL``stdin_offset``]
    \\ fs[EVAL``stdin_size``]
    \\ fs[word_ls_n2w, word_lo_n2w]
    \\ DEP_REWRITE_TAC[bytes_in_memory_UPDATE_LT]
    \\ fs[] \\ EVAL_TAC \\ fs[] )
  \\ rw[]
  \\ pop_assum mp_tac
  \\ simp[markerTheory.Abbrev_def]
  \\ strip_tac \\ fs[]
  \\ pairarg_tac \\ fs[]
  \\ rveq
  \\ fs[ag32_stdin_implemented_def]
  \\ fs[fsFFITheory.openFile_def]
  \\ rveq \\ fs[]
  \\ fs[ag32_fs_ok_def]
  \\ imp_res_tac fsFFIPropsTheory.STD_streams_nextFD
  \\ simp[]
  \\ fs[]
QED

Theorem ag32_cline_implemented_ffi_open_in:
   ag32_cline_implemented cl m ∧
   w2n (ms.R 3w) + LENGTH bytes' < dimword(:32) ∧
   n2w heap_start_offset <=+ ms.R 3w ∧
   (ffi_open_in conf bytes fs = SOME (FFIreturn bytes' fs'))
   ⇒
   ag32_cline_implemented cl
       (asm_write_bytearray (ms.R 3w) bytes'
         ((n2w (ffi_code_start_offset - 1) =+
           n2w (THE (ALOOKUP FFI_codes "open_in"))) m))
Proof
  simp[ag32_cline_implemented_def]
  \\ strip_tac
  \\ conj_tac
  >- (
    DEP_REWRITE_TAC[get_mem_word_asm_write_bytearray_UNCHANGED_LT]
    \\ Cases_on`ms.R 3w` \\ fs[EVAL``heap_start_offset``,EVAL``startup_code_size``]
    \\ fs[word_ls_n2w, word_lo_n2w]
    \\ DEP_REWRITE_TAC[get_mem_word_UPDATE]
    \\ conj_tac >- EVAL_TAC \\ simp[] )
  \\ DEP_REWRITE_TAC[bytes_in_memory_asm_write_bytearray_LT]
  \\ Cases_on`ms.R 3w` \\ fs[EVAL``heap_start_offset``,EVAL``startup_code_size``]
  \\ simp[LENGTH_FLAT, MAP_MAP_o, o_DEF, ADD1]
  \\ simp[SUM_MAP_PLUS]
  \\ simp[Q.ISPEC`λx. 1n`SUM_MAP_K |> SIMP_RULE(srw_ss())[]]
  \\ fs[EVAL``cline_size``]
  \\ fs[word_ls_n2w, word_lo_n2w]
  \\ DEP_REWRITE_TAC[bytes_in_memory_UPDATE_LT]
  \\ simp[LENGTH_FLAT, MAP_MAP_o, o_DEF, ADD1]
  \\ simp[SUM_MAP_PLUS]
  \\ simp[Q.ISPEC`λx. 1n`SUM_MAP_K |> SIMP_RULE(srw_ss())[]]
  \\ fs[EVAL``ffi_code_start_offset``]
  \\ fs[MAP_MAP_o, o_DEF]
QED

Theorem ag32_stdin_implemented_ffi_open_out:
   ag32_fs_ok fs ∧
   ag32_stdin_implemented fs m ∧
   ffi_open_out conf bytes fs = SOME (FFIreturn bytes' fs') ∧
   w2n (ms.R 3w) + LENGTH bytes' < 4294967296 ∧
   n2w heap_start_offset <=+ ms.R 3w
   ⇒
   ag32_stdin_implemented fs'
     (asm_write_bytearray (ms.R 3w) bytes'
       ((n2w (ffi_code_start_offset - 1) =+
         n2w (THE (ALOOKUP FFI_codes "open_out"))) m))
Proof
  rw[]
  \\ fs[fsFFITheory.ffi_open_out_def]
  \\ qhdtm_x_assum`OPTION_CHOICE`mp_tac
  \\ simp[OPTION_CHOICE_EQUALS_OPTION]
  \\ qmatch_goalsub_abbrev_tac`A ∨ B ⇒ _`
  \\ Cases_on`B`
  >- (
    simp[Abbr`A`]
    \\ fs[markerTheory.Abbrev_def, DISJ_EQ_IMP]
    \\ rveq
    \\ fs[ag32_stdin_implemented_def]
    \\ conj_tac
    >- (
      DEP_REWRITE_TAC[get_mem_word_asm_write_bytearray_UNCHANGED_LT]
      \\ Cases_on`ms.R 3w` \\ fs[EVAL``heap_start_offset``,EVAL``stdin_offset``]
      \\ fs[word_ls_n2w, word_lo_n2w]
      \\ DEP_REWRITE_TAC[get_mem_word_UPDATE]
      \\ conj_tac >- EVAL_TAC \\ simp[] )
    \\ conj_tac
    >- (
      DEP_REWRITE_TAC[get_mem_word_asm_write_bytearray_UNCHANGED_LT]
      \\ Cases_on`ms.R 3w` \\ fs[EVAL``heap_start_offset``,EVAL``stdin_offset``]
      \\ fs[word_ls_n2w, word_lo_n2w]
      \\ DEP_REWRITE_TAC[get_mem_word_UPDATE]
      \\ conj_tac >- EVAL_TAC \\ simp[] )
    \\ DEP_REWRITE_TAC[bytes_in_memory_asm_write_bytearray_LT]
    \\ Cases_on`ms.R 3w` \\ fs[EVAL``heap_start_offset``,EVAL``stdin_offset``]
    \\ fs[EVAL``stdin_size``]
    \\ fs[word_ls_n2w, word_lo_n2w]
    \\ DEP_REWRITE_TAC[bytes_in_memory_UPDATE_LT]
    \\ fs[] \\ EVAL_TAC \\ fs[] )
  \\ rw[]
  \\ pop_assum mp_tac
  \\ simp[markerTheory.Abbrev_def]
  \\ strip_tac \\ fs[]
  \\ pairarg_tac \\ fs[]
  \\ rveq
  \\ fs[ag32_stdin_implemented_def]
  \\ fs[fsFFITheory.openFile_truncate_def]
  \\ rveq \\ fs[]
  \\ fs[ag32_fs_ok_def]
  \\ imp_res_tac fsFFIPropsTheory.STD_streams_nextFD
  \\ simp[]
  \\ fs[]
QED

Theorem ag32_cline_implemented_ffi_open_out:
   ag32_cline_implemented cl m ∧
   w2n (ms.R 3w) + LENGTH bytes' < dimword(:32) ∧
   n2w heap_start_offset <=+ ms.R 3w ∧
   (ffi_open_out conf bytes fs = SOME (FFIreturn bytes' fs'))
   ⇒
   ag32_cline_implemented cl
       (asm_write_bytearray (ms.R 3w) bytes'
         ((n2w (ffi_code_start_offset - 1) =+
           n2w (THE (ALOOKUP FFI_codes "open_out"))) m))
Proof
  simp[ag32_cline_implemented_def]
  \\ strip_tac
  \\ conj_tac
  >- (
    DEP_REWRITE_TAC[get_mem_word_asm_write_bytearray_UNCHANGED_LT]
    \\ Cases_on`ms.R 3w` \\ fs[EVAL``heap_start_offset``,EVAL``startup_code_size``]
    \\ fs[word_ls_n2w, word_lo_n2w]
    \\ DEP_REWRITE_TAC[get_mem_word_UPDATE]
    \\ conj_tac >- EVAL_TAC \\ simp[] )
  \\ DEP_REWRITE_TAC[bytes_in_memory_asm_write_bytearray_LT]
  \\ Cases_on`ms.R 3w` \\ fs[EVAL``heap_start_offset``,EVAL``startup_code_size``]
  \\ simp[LENGTH_FLAT, MAP_MAP_o, o_DEF, ADD1]
  \\ simp[SUM_MAP_PLUS]
  \\ simp[Q.ISPEC`λx. 1n`SUM_MAP_K |> SIMP_RULE(srw_ss())[]]
  \\ fs[EVAL``cline_size``]
  \\ fs[word_ls_n2w, word_lo_n2w]
  \\ DEP_REWRITE_TAC[bytes_in_memory_UPDATE_LT]
  \\ simp[LENGTH_FLAT, MAP_MAP_o, o_DEF, ADD1]
  \\ simp[SUM_MAP_PLUS]
  \\ simp[Q.ISPEC`λx. 1n`SUM_MAP_K |> SIMP_RULE(srw_ss())[]]
  \\ fs[EVAL``ffi_code_start_offset``]
  \\ fs[MAP_MAP_o, o_DEF]
QED

Theorem ag32_stdin_implemented_ffi_close:
   ag32_fs_ok fs ∧
   ag32_stdin_implemented fs m ∧
   ffi_close conf bytes fs = SOME (FFIreturn bytes' fs') ∧
   w2n (ms.R 3w) + LENGTH bytes' < 4294967296 ∧
   n2w heap_start_offset <=+ ms.R 3w
   ⇒
   ag32_stdin_implemented fs'
     (asm_write_bytearray (ms.R 3w) bytes'
       ((n2w (ffi_code_start_offset - 1) =+
         n2w (THE (ALOOKUP FFI_codes "close"))) m))
Proof
  rw[]
  \\ fs[fsFFITheory.ffi_close_def]
  \\ qhdtm_x_assum`OPTION_CHOICE`mp_tac
  \\ simp[OPTION_CHOICE_EQUALS_OPTION]
  \\ qmatch_goalsub_abbrev_tac`A ∨ B ⇒ _`
  \\ Cases_on`B`
  >- (
    simp[Abbr`A`]
    \\ fs[markerTheory.Abbrev_def, DISJ_EQ_IMP]
    \\ rveq
    \\ fs[ag32_stdin_implemented_def]
    \\ conj_tac
    >- (
      DEP_REWRITE_TAC[get_mem_word_asm_write_bytearray_UNCHANGED_LT]
      \\ Cases_on`ms.R 3w` \\ fs[EVAL``heap_start_offset``,EVAL``stdin_offset``]
      \\ fs[word_ls_n2w, word_lo_n2w]
      \\ DEP_REWRITE_TAC[get_mem_word_UPDATE]
      \\ conj_tac >- EVAL_TAC \\ simp[] )
    \\ conj_tac
    >- (
      DEP_REWRITE_TAC[get_mem_word_asm_write_bytearray_UNCHANGED_LT]
      \\ Cases_on`ms.R 3w` \\ fs[EVAL``heap_start_offset``,EVAL``stdin_offset``]
      \\ fs[word_ls_n2w, word_lo_n2w]
      \\ DEP_REWRITE_TAC[get_mem_word_UPDATE]
      \\ conj_tac >- EVAL_TAC \\ simp[] )
    \\ DEP_REWRITE_TAC[bytes_in_memory_asm_write_bytearray_LT]
    \\ Cases_on`ms.R 3w` \\ fs[EVAL``heap_start_offset``,EVAL``stdin_offset``]
    \\ fs[EVAL``stdin_size``]
    \\ fs[word_ls_n2w, word_lo_n2w]
    \\ DEP_REWRITE_TAC[bytes_in_memory_UPDATE_LT]
    \\ fs[] \\ EVAL_TAC \\ fs[] )
  \\ rw[]
  \\ pop_assum mp_tac
  \\ simp[markerTheory.Abbrev_def]
  \\ strip_tac \\ fs[]
  \\ pairarg_tac \\ fs[]
  \\ rveq
  \\ fs[ag32_stdin_implemented_def]
  \\ fs[fsFFITheory.closeFD_def]
  \\ pairarg_tac \\ fs[]
  \\ rveq \\ fs[]
  \\ simp[ALOOKUP_ADELKEY]
  \\ fs[ag32_fs_ok_def]
  \\ res_tac
  \\ rfs[]
QED

Theorem ag32_cline_implemented_ffi_close:
   ag32_cline_implemented cl m ∧
   w2n (ms.R 3w) + LENGTH bytes' < dimword(:32) ∧
   n2w heap_start_offset <=+ ms.R 3w ∧
   (ffi_close conf bytes fs = SOME (FFIreturn bytes' fs'))
   ⇒
   ag32_cline_implemented cl
       (asm_write_bytearray (ms.R 3w) bytes'
         ((n2w (ffi_code_start_offset - 1) =+
           n2w (THE (ALOOKUP FFI_codes "close"))) m))
Proof
  simp[ag32_cline_implemented_def]
  \\ strip_tac
  \\ conj_tac
  >- (
    DEP_REWRITE_TAC[get_mem_word_asm_write_bytearray_UNCHANGED_LT]
    \\ Cases_on`ms.R 3w` \\ fs[EVAL``heap_start_offset``,EVAL``startup_code_size``]
    \\ fs[word_ls_n2w, word_lo_n2w]
    \\ DEP_REWRITE_TAC[get_mem_word_UPDATE]
    \\ conj_tac >- EVAL_TAC \\ simp[] )
  \\ DEP_REWRITE_TAC[bytes_in_memory_asm_write_bytearray_LT]
  \\ Cases_on`ms.R 3w` \\ fs[EVAL``heap_start_offset``,EVAL``startup_code_size``]
  \\ simp[LENGTH_FLAT, MAP_MAP_o, o_DEF, ADD1]
  \\ simp[SUM_MAP_PLUS]
  \\ simp[Q.ISPEC`λx. 1n`SUM_MAP_K |> SIMP_RULE(srw_ss())[]]
  \\ fs[EVAL``cline_size``]
  \\ fs[word_ls_n2w, word_lo_n2w]
  \\ DEP_REWRITE_TAC[bytes_in_memory_UPDATE_LT]
  \\ simp[LENGTH_FLAT, MAP_MAP_o, o_DEF, ADD1]
  \\ simp[SUM_MAP_PLUS]
  \\ simp[Q.ISPEC`λx. 1n`SUM_MAP_K |> SIMP_RULE(srw_ss())[]]
  \\ fs[EVAL``ffi_code_start_offset``]
  \\ fs[MAP_MAP_o, o_DEF]
QED

Theorem ag32_stdin_implemented_ffi_get_arg_count:
   ag32_stdin_implemented fs m ∧
   ffi_get_arg_count conf bytes (cl:mlstring list) = SOME (FFIreturn bytes' cl') ∧
   w2n (ms.R 3w) + LENGTH bytes' < 4294967296 ∧
   n2w heap_start_offset <=+ ms.R 3w
   ⇒
   ag32_stdin_implemented fs
     (asm_write_bytearray (ms.R 3w) bytes'
       ((n2w (ffi_code_start_offset - 1) =+
         n2w (THE (ALOOKUP FFI_codes "get_arg_count"))) m))
Proof
  rw[]
  \\ fs[ag32_stdin_implemented_def]
  \\ conj_tac
  >- (
    DEP_REWRITE_TAC[get_mem_word_asm_write_bytearray_UNCHANGED_LT]
    \\ Cases_on`ms.R 3w` \\ fs[EVAL``heap_start_offset``,EVAL``stdin_offset``]
    \\ fs[word_ls_n2w, word_lo_n2w]
    \\ DEP_REWRITE_TAC[get_mem_word_UPDATE]
    \\ conj_tac >- EVAL_TAC \\ simp[] )
  \\ conj_tac
  >- (
    DEP_REWRITE_TAC[get_mem_word_asm_write_bytearray_UNCHANGED_LT]
    \\ Cases_on`ms.R 3w` \\ fs[EVAL``heap_start_offset``,EVAL``stdin_offset``]
    \\ fs[word_ls_n2w, word_lo_n2w]
    \\ DEP_REWRITE_TAC[get_mem_word_UPDATE]
    \\ conj_tac >- EVAL_TAC \\ simp[] )
  \\ DEP_REWRITE_TAC[bytes_in_memory_asm_write_bytearray_LT]
  \\ Cases_on`ms.R 3w` \\ fs[EVAL``heap_start_offset``,EVAL``stdin_offset``]
  \\ fs[EVAL``stdin_size``]
  \\ fs[word_ls_n2w, word_lo_n2w]
  \\ DEP_REWRITE_TAC[bytes_in_memory_UPDATE_LT]
  \\ fs[] \\ EVAL_TAC \\ fs[]
QED

Theorem ag32_cline_implemented_ffi_get_arg_count:
   ag32_cline_implemented cl m ∧
   w2n (ms.R 3w) + LENGTH bytes' < dimword(:32) ∧
   n2w heap_start_offset <=+ ms.R 3w ∧
   (ffi_get_arg_count conf bytes cl = SOME (FFIreturn bytes' cl'))
   ⇒
   ag32_cline_implemented cl'
       (asm_write_bytearray (ms.R 3w) bytes'
         ((n2w (ffi_code_start_offset - 1) =+
           n2w (THE (ALOOKUP FFI_codes "get_arg_count"))) m))
Proof
  simp[ag32_cline_implemented_def]
  \\ strip_tac
  \\ fs[clFFITheory.ffi_get_arg_count_def] \\ rveq
  \\ conj_tac
  >- (
    DEP_REWRITE_TAC[get_mem_word_asm_write_bytearray_UNCHANGED_LT]
    \\ Cases_on`ms.R 3w` \\ fs[EVAL``heap_start_offset``,EVAL``startup_code_size``]
    \\ fs[word_ls_n2w, word_lo_n2w]
    \\ DEP_REWRITE_TAC[get_mem_word_UPDATE]
    \\ conj_tac >- EVAL_TAC \\ simp[] )
  \\ DEP_REWRITE_TAC[bytes_in_memory_asm_write_bytearray_LT]
  \\ Cases_on`ms.R 3w` \\ fs[EVAL``heap_start_offset``,EVAL``startup_code_size``]
  \\ simp[LENGTH_FLAT, MAP_MAP_o, o_DEF, ADD1]
  \\ simp[SUM_MAP_PLUS]
  \\ simp[Q.ISPEC`λx. 1n`SUM_MAP_K |> SIMP_RULE(srw_ss())[]]
  \\ fs[EVAL``cline_size``]
  \\ fs[word_ls_n2w, word_lo_n2w]
  \\ DEP_REWRITE_TAC[bytes_in_memory_UPDATE_LT]
  \\ simp[LENGTH_FLAT, MAP_MAP_o, o_DEF, ADD1]
  \\ simp[SUM_MAP_PLUS]
  \\ simp[Q.ISPEC`λx. 1n`SUM_MAP_K |> SIMP_RULE(srw_ss())[]]
  \\ fs[EVAL``ffi_code_start_offset``]
  \\ fs[MAP_MAP_o, o_DEF]
QED

Theorem ag32_stdin_implemented_ffi_get_arg_length:
   ag32_stdin_implemented fs m ∧
   ffi_get_arg_length conf bytes (cl:mlstring list) = SOME (FFIreturn bytes' cl') ∧
   w2n (ms.R 3w) + LENGTH bytes' < 4294967296 ∧
   n2w heap_start_offset <=+ ms.R 3w
   ⇒
   ag32_stdin_implemented fs
     (asm_write_bytearray (ms.R 3w) bytes'
       ((n2w (ffi_code_start_offset - 1) =+
         n2w (THE (ALOOKUP FFI_codes "get_arg_length"))) m))
Proof
  rw[]
  \\ fs[ag32_stdin_implemented_def]
  \\ conj_tac
  >- (
    DEP_REWRITE_TAC[get_mem_word_asm_write_bytearray_UNCHANGED_LT]
    \\ Cases_on`ms.R 3w` \\ fs[EVAL``heap_start_offset``,EVAL``stdin_offset``]
    \\ fs[word_ls_n2w, word_lo_n2w]
    \\ DEP_REWRITE_TAC[get_mem_word_UPDATE]
    \\ conj_tac >- EVAL_TAC \\ simp[] )
  \\ conj_tac
  >- (
    DEP_REWRITE_TAC[get_mem_word_asm_write_bytearray_UNCHANGED_LT]
    \\ Cases_on`ms.R 3w` \\ fs[EVAL``heap_start_offset``,EVAL``stdin_offset``]
    \\ fs[word_ls_n2w, word_lo_n2w]
    \\ DEP_REWRITE_TAC[get_mem_word_UPDATE]
    \\ conj_tac >- EVAL_TAC \\ simp[] )
  \\ DEP_REWRITE_TAC[bytes_in_memory_asm_write_bytearray_LT]
  \\ Cases_on`ms.R 3w` \\ fs[EVAL``heap_start_offset``,EVAL``stdin_offset``]
  \\ fs[EVAL``stdin_size``]
  \\ fs[word_ls_n2w, word_lo_n2w]
  \\ DEP_REWRITE_TAC[bytes_in_memory_UPDATE_LT]
  \\ fs[] \\ EVAL_TAC \\ fs[]
QED

Theorem ag32_cline_implemented_ffi_get_arg_length:
   ag32_cline_implemented cl m ∧
   w2n (ms.R 3w) + LENGTH bytes' < dimword(:32) ∧
   n2w heap_start_offset <=+ ms.R 3w ∧
   (ffi_get_arg_length conf bytes cl = SOME (FFIreturn bytes' cl'))
   ⇒
   ag32_cline_implemented cl'
       (asm_write_bytearray (ms.R 3w) bytes'
         ((n2w (ffi_code_start_offset - 1) =+
           n2w (THE (ALOOKUP FFI_codes "get_arg_length"))) m))
Proof
  simp[ag32_cline_implemented_def]
  \\ strip_tac
  \\ fs[clFFITheory.ffi_get_arg_length_def] \\ rveq
  \\ conj_tac
  >- (
    DEP_REWRITE_TAC[get_mem_word_asm_write_bytearray_UNCHANGED_LT]
    \\ Cases_on`ms.R 3w` \\ fs[EVAL``heap_start_offset``,EVAL``startup_code_size``]
    \\ fs[word_ls_n2w, word_lo_n2w]
    \\ DEP_REWRITE_TAC[get_mem_word_UPDATE]
    \\ conj_tac >- EVAL_TAC \\ simp[] )
  \\ DEP_REWRITE_TAC[bytes_in_memory_asm_write_bytearray_LT]
  \\ Cases_on`ms.R 3w` \\ fs[EVAL``heap_start_offset``,EVAL``startup_code_size``]
  \\ simp[LENGTH_FLAT, MAP_MAP_o, o_DEF, ADD1]
  \\ simp[SUM_MAP_PLUS]
  \\ simp[Q.ISPEC`λx. 1n`SUM_MAP_K |> SIMP_RULE(srw_ss())[]]
  \\ fs[EVAL``cline_size``]
  \\ fs[word_ls_n2w, word_lo_n2w]
  \\ DEP_REWRITE_TAC[bytes_in_memory_UPDATE_LT]
  \\ simp[LENGTH_FLAT, MAP_MAP_o, o_DEF, ADD1]
  \\ simp[SUM_MAP_PLUS]
  \\ simp[Q.ISPEC`λx. 1n`SUM_MAP_K |> SIMP_RULE(srw_ss())[]]
  \\ fs[EVAL``ffi_code_start_offset``]
  \\ fs[MAP_MAP_o, o_DEF]
QED

(* TODO: many of these theorems could be deduplicated: the assumptions
         differing between them might not even be necessary *)
Theorem ag32_stdin_implemented_ffi_get_arg:
   ag32_stdin_implemented fs m ∧
   ffi_get_arg conf bytes (cl:mlstring list) = SOME (FFIreturn bytes' cl') ∧
   w2n (ms.R 3w) + LENGTH bytes' < 4294967296 ∧
   n2w heap_start_offset <=+ ms.R 3w
   ⇒
   ag32_stdin_implemented fs
     (asm_write_bytearray (ms.R 3w) bytes'
       ((n2w (ffi_code_start_offset - 1) =+
         n2w (THE (ALOOKUP FFI_codes "get_arg"))) m))
Proof
  rw[]
  \\ fs[ag32_stdin_implemented_def]
  \\ conj_tac
  >- (
    DEP_REWRITE_TAC[get_mem_word_asm_write_bytearray_UNCHANGED_LT]
    \\ Cases_on`ms.R 3w` \\ fs[EVAL``heap_start_offset``,EVAL``stdin_offset``]
    \\ fs[word_ls_n2w, word_lo_n2w]
    \\ DEP_REWRITE_TAC[get_mem_word_UPDATE]
    \\ conj_tac >- EVAL_TAC \\ simp[] )
  \\ conj_tac
  >- (
    DEP_REWRITE_TAC[get_mem_word_asm_write_bytearray_UNCHANGED_LT]
    \\ Cases_on`ms.R 3w` \\ fs[EVAL``heap_start_offset``,EVAL``stdin_offset``]
    \\ fs[word_ls_n2w, word_lo_n2w]
    \\ DEP_REWRITE_TAC[get_mem_word_UPDATE]
    \\ conj_tac >- EVAL_TAC \\ simp[] )
  \\ DEP_REWRITE_TAC[bytes_in_memory_asm_write_bytearray_LT]
  \\ Cases_on`ms.R 3w` \\ fs[EVAL``heap_start_offset``,EVAL``stdin_offset``]
  \\ fs[EVAL``stdin_size``]
  \\ fs[word_ls_n2w, word_lo_n2w]
  \\ DEP_REWRITE_TAC[bytes_in_memory_UPDATE_LT]
  \\ fs[] \\ EVAL_TAC \\ fs[]
QED

Theorem ag32_cline_implemented_ffi_get_arg:
   ag32_cline_implemented cl m ∧
   w2n (ms.R 3w) + LENGTH bytes' < dimword(:32) ∧
   n2w heap_start_offset <=+ ms.R 3w ∧
   (ffi_get_arg conf bytes cl = SOME (FFIreturn bytes' cl'))
   ⇒
   ag32_cline_implemented cl'
       (asm_write_bytearray (ms.R 3w) bytes'
         ((n2w (ffi_code_start_offset - 1) =+
           n2w (THE (ALOOKUP FFI_codes "get_arg"))) m))
Proof
  simp[ag32_cline_implemented_def]
  \\ strip_tac
  \\ fs[clFFITheory.ffi_get_arg_def] \\ rveq
  \\ conj_tac
  >- (
    DEP_REWRITE_TAC[get_mem_word_asm_write_bytearray_UNCHANGED_LT]
    \\ Cases_on`ms.R 3w` \\ fs[EVAL``heap_start_offset``,EVAL``startup_code_size``]
    \\ fs[word_ls_n2w, word_lo_n2w]
    \\ DEP_REWRITE_TAC[get_mem_word_UPDATE]
    \\ conj_tac >- EVAL_TAC \\ simp[] )
  \\ DEP_REWRITE_TAC[bytes_in_memory_asm_write_bytearray_LT]
  \\ Cases_on`ms.R 3w` \\ fs[EVAL``heap_start_offset``,EVAL``startup_code_size``]
  \\ simp[LENGTH_FLAT, MAP_MAP_o, o_DEF, ADD1]
  \\ simp[SUM_MAP_PLUS]
  \\ simp[Q.ISPEC`λx. 1n`SUM_MAP_K |> SIMP_RULE(srw_ss())[]]
  \\ fs[EVAL``cline_size``]
  \\ fs[word_ls_n2w, word_lo_n2w]
  \\ DEP_REWRITE_TAC[bytes_in_memory_UPDATE_LT]
  \\ simp[LENGTH_FLAT, MAP_MAP_o, o_DEF, ADD1]
  \\ simp[SUM_MAP_PLUS]
  \\ simp[Q.ISPEC`λx. 1n`SUM_MAP_K |> SIMP_RULE(srw_ss())[]]
  \\ fs[EVAL``ffi_code_start_offset``]
  \\ fs[MAP_MAP_o, o_DEF]
QED

Theorem ag32_ffi_interfer_write:
   ag32_ffi_rel ms ffi ∧
   (read_ffi_bytearrays (ag32_machine_config ffi_names lc ld) ms = (SOME conf, SOME bytes)) ∧
   (call_FFI ffi "write" conf bytes = FFI_return ffi' bytes') ∧
   (INDEX_OF "write" ffi_names = SOME index) ∧ ALL_DISTINCT ffi_names ∧
   w2n (ms.R 3w) + LENGTH bytes < dimword (:32) ∧
   LENGTH ffi_names ≤ LENGTH FFI_codes ∧
   code_start_offset (LENGTH ffi_names) + lc + 4 * ld < memory_size ∧
   (ms.PC = n2w (ffi_jumps_offset + (LENGTH ffi_names - 1 - index) * ffi_offset)) ∧
   (∀k. k < LENGTH (ag32_ffi_jumps ffi_names) ⇒
        (get_mem_word ms.MEM (n2w (ffi_jumps_offset + 4 * k))
         = EL k (ag32_ffi_jumps ffi_names))) ∧
   (∀k. k < LENGTH ag32_ffi_write_code ⇒
        (get_mem_word ms.MEM (n2w (ffi_code_start_offset + THE (ALOOKUP ffi_entrypoints "write") + 4 * k))
         = Encode (EL k ag32_ffi_write_code)))
   ⇒
   ∃k.
     (ag32_ffi_interfer ffi_names
        (ag32_prog_addresses (LENGTH ffi_names) lc ld)
        (index,bytes',ms) = FUNPOW Next k ms) ∧
      ag32_ffi_rel (FUNPOW Next k ms) ffi' ∧
      ∀x. x ∉ ag32_ffi_mem_domain /\ x ∉ all_words (ms.R 3w) (LENGTH bytes) ⇒
          ((FUNPOW Next k ms).MEM x = ms.MEM x)
Proof
  strip_tac
  \\ fs[targetSemTheory.read_ffi_bytearrays_def]
  \\ fs[targetSemTheory.read_ffi_bytearray_def]
  \\ fs[EVAL``(ag32_machine_config a b c).ptr2_reg``]
  \\ fs[EVAL``(ag32_machine_config a b c).len2_reg``]
  \\ fs[EVAL``(ag32_machine_config a b c).ptr_reg``]
  \\ fs[EVAL``(ag32_machine_config a b c).len_reg``]
  \\ fs[EVAL``(ag32_machine_config a b c).target.get_reg``]
  \\ fs[EVAL``(ag32_machine_config a b c).target.get_byte``]
  \\ first_assum(mp_then Any mp_tac asmPropsTheory.read_bytearray_IMP_bytes_in_memory)
  \\ last_assum(mp_then Any mp_tac asmPropsTheory.read_bytearray_IMP_bytes_in_memory)
  \\ imp_res_tac read_bytearray_LENGTH \\ fs[]
  \\ qmatch_asmsub_abbrev_tac`_ ∈ md`
  \\ disch_then(qspecl_then[`ms.MEM`,`md`]mp_tac) \\ simp[]
  \\ impl_tac
  >- (
    imp_res_tac read_bytearray_IMP_mem_SOME
    \\ fs[IS_SOME_EXISTS] )
  \\ strip_tac
  \\ disch_then(qspecl_then[`ms.MEM`,`md`]mp_tac) \\ simp[]
  \\ impl_tac
  >- (
    imp_res_tac read_bytearray_IMP_mem_SOME
    \\ fs[IS_SOME_EXISTS] )
  \\ strip_tac
  \\ drule (GEN_ALL mk_jump_ag32_code_thm)
  \\ simp[]
  \\ disch_then drule \\ simp[]
  \\ simp[ffi_entrypoints_def]
  \\ impl_tac
  >- (
    gen_tac \\ strip_tac
    \\ qmatch_goalsub_abbrev_tac`ffi_offset * ix`
    \\ last_x_assum(qspec_then`ix * (ffi_offset DIV 4) + k`mp_tac)
    \\ impl_tac
    >- (
      simp[LENGTH_ag32_ffi_jumps,Abbr`ix`]
      \\ EVAL_TAC
      \\ fs[FFI_codes_def])
    \\ simp[LEFT_ADD_DISTRIB, GSYM word_add_n2w]
    \\ `4 * (ix * (ffi_offset DIV 4)) = ix * ffi_offset`
    by ( EVAL_TAC \\ simp[] )
    \\ pop_assum SUBST1_TAC
    \\ simp[]
    \\ disch_then kall_tac
    \\ simp[ag32_ffi_jumps_def]
    \\ rewrite_tac[GSYM APPEND_ASSOC]
    \\ DEP_REWRITE_TAC[EL_APPEND1]
    \\ simp[LENGTH_FLAT, MAP_MAP_o, o_DEF]
    \\ simp[Once mk_jump_ag32_code_def]
    \\ simp[Q.ISPEC`λx. 4n`SUM_MAP_K |> SIMP_RULE(srw_ss())[]]
    \\ conj_tac
    >- (
      EVAL_TAC
      \\ fs[FFI_codes_def, Abbr`ix`]
      \\ fs[GSYM find_index_INDEX_OF]
      \\ imp_res_tac find_index_LESS_LENGTH
      \\ fs[] )
    \\ simp[lab_to_targetTheory.ffi_offset_def]
    \\ irule EL_FLAT_MAP_mk_jump_ag32_code
    \\ simp[INDEX_OF_REVERSE])
  \\ strip_tac
  \\ qmatch_asmsub_abbrev_tac`_ = ms1`
  \\ `(ms.MEM = ms1.MEM) ∧
      (ms.R 1w = ms1.R 1w) ∧
      (ms.R 3w = ms1.R 3w)` by simp[Abbr`ms1`,APPLY_UPDATE_THM] \\ fs[]
  \\ drule (GEN_ALL ag32_ffi_write_thm)
  \\ disch_then drule
  \\ qpat_x_assum`Abbrev(md = _)`mp_tac
  \\ CONV_TAC(LAND_CONV(SIMP_CONV(srw_ss()++LET_ss)[ag32_machine_config_def]))
  \\ strip_tac
  \\ disch_then drule
  \\ simp[]
  \\ qhdtm_x_assum`call_FFI`mp_tac
  \\ simp[ffiTheory.call_FFI_def]
  \\ `ffi.oracle = basis_ffi_oracle` by fs[ag32_ffi_rel_def]
  \\ simp[basis_ffiTheory.basis_ffi_oracle_def]
  \\ pairarg_tac \\ simp[]
  \\ simp[CaseEq"option",CaseEq"oracle_result",CaseEq"bool",CaseEq"ffi_result"]
  \\ strip_tac
  \\ var_eq_tac
  \\ var_eq_tac
  \\ var_eq_tac
  \\ disch_then(first_assum o mp_then Any mp_tac)
  \\ simp[]
  \\ qpat_x_assum`ms.R _ = _`kall_tac
  \\ qpat_x_assum`ms.R _ = _`kall_tac
  \\ qpat_x_assum`ms.MEM = _`kall_tac
  \\ impl_tac
  >- (
    simp[Abbr`ms1`, APPLY_UPDATE_THM]
    \\ fs[ag32_ffi_rel_def]
    \\ EVAL_TAC)
  \\ strip_tac
  \\ `EL index ffi_names = "write"`
  by (
    fs[GSYM find_index_INDEX_OF]
    \\ imp_res_tac find_index_is_MEM
    \\ imp_res_tac find_index_MEM
    \\ first_x_assum(qspec_then`0`mp_tac)
    \\ simp[] )
  \\ `ag32_ffi_interfer ffi_names md (index,bytes',ms) =
      ag32_ffi_interfer ffi_names md (index,bytes',ms1)`
  by (
    simp[ag32_ffi_interfer_def, ag32Theory.ag32_state_component_equality]
    \\ simp[Abbr`ms1`, APPLY_UPDATE_THM]
    \\ simp[FUN_EQ_THM, APPLY_UPDATE_THM] )
  \\ qspec_then`ms1`mp_tac (CONV_RULE(RESORT_FORALL_CONV(sort_vars["s"]))(GEN_ALL ag32_ffi_write_code_thm))
  \\ fs[Abbr`ms1`, APPLY_UPDATE_THM]
  \\ fs[ffi_entrypoints_def, GSYM word_add_n2w]
  \\ disch_then drule \\ simp[]
  \\ qmatch_asmsub_abbrev_tac`FUNPOW _ _ _ = ms1`
  \\ `∃n1 n0 off1 off0 tll. bytes = n1::n0::off1::off0::tll`
  by ( fs[fsFFITheory.ffi_write_def] \\ fs[CaseEq"list"] )
  \\ rveq
  \\ disch_then drule
  \\ fs[]
  \\ impl_tac
  >- (
    reverse conj_tac
    >- (
      simp[Abbr`md`]
      \\ EVAL_TAC
      \\ fs[IN_DISJOINT, LEFT_ADD_DISTRIB, FFI_codes_def]
      \\ fs[memory_size_def, word_add_n2w]
      \\ simp[PULL_FORALL]
      \\ Cases \\ Cases
      \\ fs[word_ls_n2w, word_lo_n2w, DIV_LT_X] )
    \\ simp[Abbr`md`]
    \\ EVAL_TAC
    \\ fs[EVAL``code_start_offset _``]
    \\ fs[IN_DISJOINT, LEFT_ADD_DISTRIB, FFI_codes_def]
    \\ fs[memory_size_def, word_add_n2w]
    \\ simp[PULL_FORALL]
    \\ Cases \\ Cases
    \\ fs[word_ls_n2w, word_lo_n2w, DIV_LT_X]
    \\ conj_tac
    >- (
      CCONTR_TAC
      \\ fs[]
      \\ rveq \\ fs[]
      \\ qpat_x_assum`_ MOD _ < _`mp_tac \\ simp[]
      \\ qpat_x_assum`_ ≤ _ MOD _`mp_tac \\ simp[] )
    \\ simp[data_to_word_assignProofTheory.IMP]
    \\ strip_tac
    \\ qx_gen_tac`j`
    \\ Cases_on`j < 428` \\ simp[])
  \\ strip_tac
  \\ qexists_tac`k'+k`
  \\ simp[FUNPOW_ADD]
  \\ qpat_x_assum`ag32_ffi_interfer _ _ _ = _`(assume_tac o SYM)
  \\ simp[]
  \\ simp[ag32_ffi_interfer_def]
  \\ fs[ag32_ffi_rel_def]
  \\ conj_tac
  >- (
    fs[]
    \\ conj_tac
    >- (
      irule ag32_ffi_rel_write_mem_update
      \\ fs[]
      \\ reverse conj_tac
      >- ( asm_exists_tac \\ fs[] )
      \\ irule asm_write_bytearray_unchanged
      \\ simp[APPLY_UPDATE_THM]
      \\ Cases_on`ms.R 3w` \\ fs[memory_size_def]
      \\ qpat_x_assum`_ = w2n (ms.R 4w)`(assume_tac o SYM)
      \\ imp_res_tac fsFFIPropsTheory.ffi_write_length \\ fs[ADD1]
      \\ EVAL_TAC \\ fs[]
      \\ Cases_on`ms.R 4w` \\ fs[word_ls_n2w, word_lo_n2w, word_add_n2w]
      \\ fs[bytes_in_memory_def]
      \\ qpat_x_assum`n2w n ∈ md` mp_tac
      \\ simp[Abbr`md`]
      \\ EVAL_TAC
      \\ simp[word_add_n2w, LEFT_ADD_DISTRIB]
      \\ fs[word_lo_n2w, word_ls_n2w]
      \\ fs[EVAL``code_start_offset _``])
    \\ conj_tac
    >- metis_tac[ag32_fs_ok_ffi_write]
    \\ conj_tac
    >- (
      match_mp_tac ag32_stdin_implemented_ffi_write
      \\ fs[ag32_fs_ok_def]
      \\ drule bytes_in_memory_in_domain
      \\ disch_then(qspec_then`0` assume_tac)>>fs[Abbr`md`]
      \\ pop_assum mp_tac
      \\ EVAL_TAC
      \\ Cases_on`ms.R 3w` \\ fs[FFI_codes_def, LEFT_ADD_DISTRIB, word_ls_n2w, word_lo_n2w])
    \\ match_mp_tac ag32_cline_implemented_ffi_write
    \\ fs[bytes_in_memory_def]
    \\ qpat_x_assum`ms.R 3w ∈ md` mp_tac
    \\ simp[Abbr`md`]
    \\ EVAL_TAC
    \\ Cases_on`ms.R 3w`
    \\ fs[word_lo_n2w, word_ls_n2w, EVAL``code_start_offset _``,
          FFI_codes_def, LEFT_ADD_DISTRIB, memory_size_def, word_add_n2w])
  \\ rw[]
  \\ simp[ag32_ffi_mem_update_def]
  \\ reverse IF_CASES_TAC
  >- (
    simp[APPLY_UPDATE_THM]
    \\ IF_CASES_TAC
    >- (
      qpat_x_assum`x ∉ ag32_ffi_mem_domain`mp_tac
      \\ rveq
      \\ simp[ag32_ffi_mem_domain_def]
      \\ EVAL_TAC
      \\ fs[word_add_n2w, memory_size_def]
      \\ fs[word_ls_n2w, word_lo_n2w] )
    \\ irule asm_write_bytearray_unchanged_all_words
    \\ qpat_x_assum`_ = w2n (ms.R 4w)`(assume_tac o SYM)
    \\ simp []
    \\ Cases_on`ms.R 3w` \\ fs[memory_size_def]
    \\ simp[APPLY_UPDATE_THM]
    \\ imp_res_tac fsFFIPropsTheory.ffi_write_length
    \\ fs[ADD1]
    \\ fs[word_add_n2w]
    \\ IF_CASES_TAC \\ fs[]
    \\ qpat_x_assum`x ∉ ag32_ffi_mem_domain`mp_tac
    \\ rveq
    \\ simp[ag32_ffi_mem_domain_def]
    \\ EVAL_TAC
    \\ fs[word_ls_n2w, word_lo_n2w, word_add_n2w] )
  \\ irule asm_write_bytearray_unchanged
  \\ qpat_x_assum`_ = w2n (ms.R 4w)`(assume_tac o SYM)
  \\ Cases_on`ms.R 3w` \\ fs[memory_size_def]
  \\ qpat_x_assum`_ = w2n (ms.R 2w)`(assume_tac o SYM) \\ fs[]
  \\ fs[word_add_n2w]
  \\ fs[EVAL``output_offset``]
  \\ Cases_on`x` \\ fs[word_lo_n2w, word_ls_n2w]
  \\ qmatch_goalsub_abbrev_tac`LENGTH conf + ll`
  \\ pop_assum mp_tac
  \\ simp[LENGTH_TAKE_EQ]
  \\ reverse IF_CASES_TAC
  >- (
    fs[ADD1]
    \\ fs[fsFFITheory.ffi_write_def]
    \\ fs[OPTION_CHOICE_EQUALS_OPTION, LUPDATE_def] \\ rveq \\ fs[]
    \\ pairarg_tac \\ fs[fsFFITheory.write_def]
    \\ pairarg_tac \\ fs[] \\ rveq )
  \\ simp[EVAL``output_buffer_size``]
  \\ `LENGTH conf = 8` by (
    fs[fsFFITheory.ffi_write_def]
    \\ fs[OPTION_CHOICE_EQUALS_OPTION, LUPDATE_def] \\ rveq \\ fs[] )
  \\ strip_tac
  \\ simp[Abbr`ll`]
  \\ conj_tac >- simp[MIN_DEF]
  \\ conj_tac
  >- (
    irule EQ_SYM
    \\ irule asm_write_bytearray_unchanged_alt
    \\ simp[APPLY_UPDATE_THM]
    \\ conj_tac
    >- (
      fs[data_to_word_assignProofTheory.IMP]
      \\ CCONTR_TAC \\ fs[]
      \\ qpat_x_assum`_ ∉ all_words _ _`mp_tac
      \\ simp[]
      \\ once_rewrite_tac[WORD_ADD_COMM]
      \\ simp[IN_all_words]
      \\ asm_exists_tac \\ rw[])
    \\ EVAL_TAC \\ simp[]
    \\ IF_CASES_TAC \\ simp[]
    \\ qpat_x_assum`_ ∉ ag32_ffi_mem_domain`mp_tac
    \\ rveq \\ EVAL_TAC
    \\ simp[] )
  \\ simp[MIN_DEF]
  \\ fs[data_to_word_assignProofTheory.IMP]
  \\ fs[EVAL``output_buffer_size``]
  \\ qpat_x_assum`_ ∉ ag32_ffi_mem_domain`mp_tac
  \\ EVAL_TAC
  \\ simp[]
QED

Theorem ag32_ffi_interfer_read:
   ag32_ffi_rel ms ffi ∧ (SND ffi.ffi_state = fs) ∧
   (read_ffi_bytearrays (ag32_machine_config ffi_names lc ld) ms = (SOME conf, SOME bytes)) ∧
   (call_FFI ffi "read" conf bytes = FFI_return ffi' bytes') ∧
   (INDEX_OF "read" ffi_names = SOME index) ∧ ALL_DISTINCT ffi_names ∧
   w2n (ms.R 3w) + LENGTH bytes < dimword (:32) ∧
   LENGTH ffi_names ≤ LENGTH FFI_codes ∧
   code_start_offset (LENGTH ffi_names) + lc + 4 * ld < memory_size ∧
   (ms.PC = n2w (ffi_jumps_offset + (LENGTH ffi_names - (index + 1)) * ffi_offset)) ∧
   (∀k. k < LENGTH (ag32_ffi_jumps ffi_names) ⇒
        (get_mem_word ms.MEM (n2w (ffi_jumps_offset + 4 * k))
         = EL k (ag32_ffi_jumps ffi_names))) ∧
   (∀k. k < LENGTH ag32_ffi_read_code ⇒
        (get_mem_word ms.MEM (n2w (ffi_code_start_offset + THE (ALOOKUP ffi_entrypoints "read") + 4 * k))
         = Encode (EL k ag32_ffi_read_code)))
   ⇒
   ∃k.
     (ag32_ffi_interfer ffi_names
        (ag32_prog_addresses (LENGTH ffi_names) lc ld)
        (index,bytes',ms) = FUNPOW Next k ms) ∧
      ag32_ffi_rel (FUNPOW Next k ms) ffi' ∧
      ∀x. x ∉ ag32_ffi_mem_domain ∧
          x ∉ all_words (ms.R 3w) (LENGTH bytes) ⇒
          ((FUNPOW Next k ms).MEM x = ms.MEM x)
Proof
  strip_tac
  \\ fs[targetSemTheory.read_ffi_bytearrays_def]
  \\ fs[targetSemTheory.read_ffi_bytearray_def]
  \\ fs[EVAL``(ag32_machine_config a b c).ptr2_reg``]
  \\ fs[EVAL``(ag32_machine_config a b c).len2_reg``]
  \\ fs[EVAL``(ag32_machine_config a b c).ptr_reg``]
  \\ fs[EVAL``(ag32_machine_config a b c).len_reg``]
  \\ fs[EVAL``(ag32_machine_config a b c).target.get_reg``]
  \\ fs[EVAL``(ag32_machine_config a b c).target.get_byte``]
  \\ first_assum(mp_then Any mp_tac asmPropsTheory.read_bytearray_IMP_bytes_in_memory)
  \\ last_assum(mp_then Any mp_tac asmPropsTheory.read_bytearray_IMP_bytes_in_memory)
  \\ imp_res_tac read_bytearray_LENGTH \\ fs[]
  \\ qmatch_asmsub_abbrev_tac`_ ∈ md`
  \\ disch_then(qspecl_then[`ms.MEM`,`md`]mp_tac) \\ simp[]
  \\ impl_tac
  >- (
    imp_res_tac read_bytearray_IMP_mem_SOME
    \\ fs[IS_SOME_EXISTS] )
  \\ strip_tac
  \\ disch_then(qspecl_then[`ms.MEM`,`md`]mp_tac) \\ simp[]
  \\ impl_tac
  >- (
    imp_res_tac read_bytearray_IMP_mem_SOME
    \\ fs[IS_SOME_EXISTS] )
  \\ strip_tac
  \\ drule (GEN_ALL mk_jump_ag32_code_thm)
  \\ simp[]
  \\ disch_then drule \\ simp[]
  \\ simp[ffi_entrypoints_def]
  \\ impl_tac
  >- (
    gen_tac \\ strip_tac
    \\ qmatch_goalsub_abbrev_tac`ffi_offset * ix`
    \\ last_x_assum(qspec_then`ix * (ffi_offset DIV 4) + k`mp_tac)
    \\ impl_tac
    >- (
      simp[LENGTH_ag32_ffi_jumps,Abbr`ix`]
      \\ EVAL_TAC
      \\ fs[FFI_codes_def])
    \\ simp[LEFT_ADD_DISTRIB, GSYM word_add_n2w]
    \\ `4 * (ix * (ffi_offset DIV 4)) = ix * ffi_offset`
    by ( EVAL_TAC \\ simp[] )
    \\ pop_assum SUBST1_TAC
    \\ simp[]
    \\ disch_then kall_tac
    \\ simp[ag32_ffi_jumps_def]
    \\ rewrite_tac[GSYM APPEND_ASSOC]
    \\ DEP_REWRITE_TAC[EL_APPEND1]
    \\ simp[LENGTH_FLAT, MAP_MAP_o, o_DEF]
    \\ simp[Once mk_jump_ag32_code_def]
    \\ simp[Q.ISPEC`λx. 4n`SUM_MAP_K |> SIMP_RULE(srw_ss())[]]
    \\ conj_tac
    >- (
      EVAL_TAC
      \\ fs[FFI_codes_def,Abbr`ix`]
      \\ fs[GSYM find_index_INDEX_OF]
      \\ imp_res_tac find_index_LESS_LENGTH
      \\ fs[] )
    \\ simp[EVAL``ffi_offset``]
    \\ irule EL_FLAT_MAP_mk_jump_ag32_code
    \\ simp[INDEX_OF_REVERSE])
  \\ strip_tac
  \\ qmatch_asmsub_abbrev_tac`_ = ms1`
  \\ `(ms.MEM = ms1.MEM) ∧
      (ms.R 1w = ms1.R 1w) ∧
      (ms.R 3w = ms1.R 3w)` by simp[Abbr`ms1`,APPLY_UPDATE_THM] \\ fs[]
  \\ drule (GEN_ALL ag32_ffi_read_thm)
  \\ disch_then drule
  \\ qpat_x_assum`Abbrev(md = _)`mp_tac
  \\ CONV_TAC(LAND_CONV(SIMP_CONV(srw_ss()++LET_ss)[ag32_machine_config_def]))
  \\ strip_tac
  \\ disch_then (first_assum o mp_then Any mp_tac)
  \\ simp[]
  \\ qhdtm_x_assum`call_FFI`mp_tac
  \\ simp[ffiTheory.call_FFI_def]
  \\ `ffi.oracle = basis_ffi_oracle` by fs[ag32_ffi_rel_def]
  \\ simp[basis_ffiTheory.basis_ffi_oracle_def]
  \\ pairarg_tac \\ simp[]
  \\ simp[CaseEq"option",CaseEq"oracle_result",CaseEq"bool",CaseEq"ffi_result"]
  \\ strip_tac
  \\ var_eq_tac
  \\ var_eq_tac
  \\ var_eq_tac
  \\ disch_then(first_assum o mp_then Any mp_tac)
  \\ simp[]
  \\ qpat_x_assum`ms.R _ = _`kall_tac
  \\ qpat_x_assum`ms.R _ = _`kall_tac
  \\ qpat_x_assum`ms.MEM = _`kall_tac
  \\ simp[LEFT_FORALL_IMP_THM]
  \\ impl_tac
  >- (
    simp[Abbr`ms1`, APPLY_UPDATE_THM]
    \\ fs[ag32_ffi_rel_def, ag32_stdin_implemented_def]
    \\ EVAL_TAC \\ fs [markerTheory.Abbrev_def]
    \\ qexists_tac`off` \\ qexists_tac`LENGTH inp`
    \\ fs[EVAL``stdin_size``])
  \\ strip_tac
  \\ `EL index ffi_names = "read"`
  by (
    fs[GSYM find_index_INDEX_OF]
    \\ imp_res_tac find_index_is_MEM
    \\ imp_res_tac find_index_MEM
    \\ first_x_assum(qspec_then`0`mp_tac)
    \\ simp[] )
  \\ `ag32_ffi_interfer ffi_names md (index,bytes',ms) =
      ag32_ffi_interfer ffi_names md (index,bytes',ms1)`
  by (
    simp[ag32_ffi_interfer_def, ag32Theory.ag32_state_component_equality]
    \\ simp[Abbr`ms1`, APPLY_UPDATE_THM]
    \\ simp[FUN_EQ_THM, APPLY_UPDATE_THM] )
  \\ qspec_then`ms1`mp_tac (CONV_RULE(RESORT_FORALL_CONV(sort_vars["s"]))(GEN_ALL ag32_ffi_read_code_thm))
  \\ fs[Abbr`ms1`, APPLY_UPDATE_THM]
  \\ fs[ffi_entrypoints_def, GSYM word_add_n2w]
  \\ disch_then drule \\ simp[]
  \\ qmatch_asmsub_abbrev_tac`FUNPOW _ _ _ = ms1`
  \\ `∃n1 n0 off1 off0 tll. bytes = n1::n0::off1::off0::tll`
  by ( fs[fsFFITheory.ffi_read_def] \\ fs[CaseEq"list"] )
  \\ rveq
  \\ disch_then drule
  \\ fs[]
  \\ impl_tac
  >- (
    conj_tac
    >- ( fs[ag32_ffi_rel_def, ag32_stdin_implemented_def, word_add_n2w, EVAL``stdin_size``] )
    \\ conj_tac
    >- ( fs[ag32_ffi_rel_def, ag32_stdin_implemented_def, word_add_n2w, EVAL``stdin_size``] )
    \\ rewrite_tac[Once CONJ_ASSOC]
    \\ reverse conj_tac
    >- (
      simp[Abbr`md`]
      \\ fs[ag32_ffi_rel_def, ag32_stdin_implemented_def, word_add_n2w]
      \\ fs[EVAL``stdin_size``]
      \\ EVAL_TAC
      \\ fs[IN_DISJOINT, LEFT_ADD_DISTRIB, FFI_codes_def]
      \\ fs[memory_size_def, word_add_n2w]
      \\ simp[PULL_FORALL]
      \\ Cases \\ Cases
      \\ fs[word_ls_n2w, word_lo_n2w, DIV_LT_X]
      \\ Cases \\ Cases
      \\ fs[word_ls_n2w, word_lo_n2w, DIV_LT_X]
      \\ fs[LEFT_ADD_DISTRIB, EVAL``code_start_offset _``]
      \\ fs[DISJ_EQ_IMP]
      \\ rw[] \\ strip_tac \\ fs[])
    \\ fs[bytes_in_memory_def]
    \\ qpat_x_assum`ms.R 3w ∈ _`mp_tac
    \\ simp[Abbr`md`]
    \\ EVAL_TAC
    \\ Cases_on`ms.R 3w` \\ fs[memory_size_def, LEFT_ADD_DISTRIB, word_add_n2w, EVAL``code_start_offset _``]
    \\ fs[word_ls_n2w, word_lo_n2w])
  \\ strip_tac
  \\ qexists_tac`k'+k`
  \\ simp[FUNPOW_ADD]
  \\ qpat_x_assum`ag32_ffi_interfer _ _ _ = _`(assume_tac o SYM)
  \\ simp[]
  \\ simp[ag32_ffi_interfer_def]
  \\ fs[ag32_ffi_rel_def]
  \\ `!i. i < LENGTH bytes' ==> ms.R 3w + n2w i IN md` by
   (Cases_on `ms.R 4w` \\ fs [] \\ rveq \\ fs []
    \\ drule read_bytearray_IMP_domain \\ fs [])
  \\ conj_tac >- (
    fs[]
    \\ conj_tac
    >- (
      irule ag32_ffi_rel_read_mem_update
      \\ fs[]
      \\ reverse conj_tac
      >- ( asm_exists_tac \\ fs[] )
      \\ irule asm_write_bytearray_unchanged
      \\ simp[APPLY_UPDATE_THM]
      \\ Cases_on`ms.R 3w` \\ fs[memory_size_def]
      \\ qpat_x_assum`_ = w2n (ms.R 4w)`(assume_tac o SYM)
      \\ imp_res_tac fsFFIPropsTheory.ffi_read_length \\ fs[ADD1]
      \\ EVAL_TAC \\ fs[]
      \\ Cases_on`ms.R 4w` \\ fs[word_ls_n2w, word_lo_n2w, word_add_n2w]
      \\ fs[bytes_in_memory_def]
      \\ qpat_x_assum`n2w n ∈ md` mp_tac
      \\ simp[Abbr`md`]
      \\ EVAL_TAC
      \\ simp[word_add_n2w, LEFT_ADD_DISTRIB]
      \\ fs[word_lo_n2w, word_ls_n2w]
      \\ fs[EVAL``code_start_offset _``])
    \\ conj_tac
    >- metis_tac[ag32_fs_ok_ffi_read]
    \\ conj_tac >- (
      match_mp_tac ag32_stdin_implemented_ffi_read
      \\ fs[]
      \\ drule bytes_in_memory_in_domain
      \\ disch_then(qspec_then`0` assume_tac)>>fs[Abbr`md`]
      \\ pop_assum mp_tac
      \\ EVAL_TAC
      \\ fs[FFI_codes_def, EVAL``code_start_offset _``,memory_size_def,LEFT_ADD_DISTRIB]
      \\ Cases_on`ms.R 3w`
      \\ fs[word_lo_n2w, word_ls_n2w])
    \\ match_mp_tac (GEN_ALL ag32_cline_implemented_ffi_read)
    \\ fs[bytes_in_memory_def]
    \\ goal_assum(first_assum o mp_then Any mp_tac)
    \\ qpat_x_assum`ms.R 3w ∈ md` mp_tac
    \\ simp[Abbr`md`]
    \\ EVAL_TAC
    \\ Cases_on`ms.R 3w`
    \\ fs[word_lo_n2w, word_ls_n2w, EVAL``code_start_offset _``,
          FFI_codes_def, LEFT_ADD_DISTRIB, memory_size_def, word_add_n2w])
  \\ gen_tac \\ strip_tac
  \\ simp[ag32_ffi_mem_update_def]
  \\ imp_res_tac read_bytearray_LENGTH \\ fs[ADD1]
  \\ qpat_x_assum`_ = w2n _`(assume_tac o SYM) \\ fs[]
  \\ PURE_TOP_CASE_TAC \\ fs[]
  \\ PURE_TOP_CASE_TAC \\ fs[]
  \\ PURE_TOP_CASE_TAC \\ fs[]
  \\ reverse PURE_TOP_CASE_TAC \\ fs[IN_all_words]
  >- (
    match_mp_tac asm_write_bytearray_unchanged_alt
    \\ qpat_x_assum`x ∉ _` mp_tac
    \\ fs [ag32_ffi_mem_domain_def]
    \\ `startup_code_size < 2**32-1 /\
        (ffi_code_start_offset − 1) < 2**32-1` by EVAL_TAC
    \\ Cases_on `x` \\ fs [WORD_LO,WORD_LS]
    \\ fs [METIS_PROVE [] ``(~b \/ c) <=> (b ==> c)``,NOT_LESS]
    \\ fs [APPLY_UPDATE_THM,bool_case_eq]
    \\ strip_tac
    \\ reverse conj_tac >- metis_tac[NOT_LESS]
    \\ rpt strip_tac
    \\ DISJ2_TAC \\ pop_assum mp_tac \\ pop_assum mp_tac \\ EVAL_TAC \\ fs [] )
  \\ fs[fsFFITheory.ffi_read_def]
  \\ fs[OPTION_CHOICE_EQUALS_OPTION, LUPDATE_def]
  \\ pairarg_tac \\ fs[] \\ rveq
  \\ DEP_REWRITE_TAC[get_mem_word_asm_write_bytearray_UNCHANGED_LT]
  \\ conj_tac
  >- (
    fs[bytes_in_memory_def]
    \\ qpat_x_assum`ms.R 3w ∈ _`mp_tac
    \\ Cases_on`ms.R 3w`
    \\ simp[Abbr`md`]
    \\ EVAL_TAC
    \\ fs[FFI_codes_def, LEFT_ADD_DISTRIB, word_lo_n2w, word_ls_n2w, EVAL``stdin_offset``, memory_size_def, EVAL``code_start_offset _``] )
  \\ DEP_REWRITE_TAC[set_mem_word_neq]
  \\ conj_tac
  >- (
    EVAL_TAC
    \\ qpat_x_assum`x ∉ _`mp_tac
    \\ EVAL_TAC
    \\ Cases_on`x`
    \\ simp[word_ls_n2w, word_lo_n2w] )
  \\ irule asm_write_bytearray_unchanged_all_words
  \\ simp[APPLY_UPDATE_THM]
  \\ rw[IN_all_words]
  \\ qpat_x_assum`_ ∉ _`mp_tac
  \\ EVAL_TAC
QED

Theorem ag32_ffi_interfer_open_in:
   ag32_ffi_rel ms ffi ∧ (SND ffi.ffi_state = fs) ∧
   (read_ffi_bytearrays (ag32_machine_config ffi_names lc ld) ms = (SOME conf, SOME bytes)) ∧
   (call_FFI ffi "open_in" conf bytes = FFI_return ffi' bytes') ∧
   (INDEX_OF "open_in" ffi_names = SOME index) ∧ ALL_DISTINCT ffi_names ∧
   w2n (ms.R 3w) + LENGTH bytes < dimword (:32) ∧
   LENGTH ffi_names ≤ LENGTH FFI_codes ∧
   code_start_offset (LENGTH ffi_names) + lc + 4 * ld < memory_size ∧
   (ms.PC = n2w (ffi_jumps_offset + (LENGTH ffi_names - (index + 1)) * ffi_offset)) ∧
   (∀k. k < LENGTH (ag32_ffi_jumps ffi_names) ⇒
        (get_mem_word ms.MEM (n2w (ffi_jumps_offset + 4 * k))
         = EL k (ag32_ffi_jumps ffi_names))) ∧
   (∀k. k < LENGTH ag32_ffi_open_in_code ⇒
        (get_mem_word ms.MEM (n2w (ffi_code_start_offset + THE (ALOOKUP ffi_entrypoints "open_in") + 4 * k))
         = Encode (EL k ag32_ffi_open_in_code)))
   ⇒
   ∃k.
     (ag32_ffi_interfer ffi_names
        (ag32_prog_addresses (LENGTH ffi_names) lc ld)
        (index,bytes',ms) = FUNPOW Next k ms) ∧
      ag32_ffi_rel (FUNPOW Next k ms) ffi' ∧
      ∀x. x ∉ ag32_ffi_mem_domain ∧
          x ∉ all_words (ms.R 3w) (LENGTH bytes) ⇒
          ((FUNPOW Next k ms).MEM x = ms.MEM x)
Proof
  strip_tac
  \\ fs[targetSemTheory.read_ffi_bytearrays_def]
  \\ fs[targetSemTheory.read_ffi_bytearray_def]
  \\ fs[EVAL``(ag32_machine_config a b c).ptr2_reg``]
  \\ fs[EVAL``(ag32_machine_config a b c).len2_reg``]
  \\ fs[EVAL``(ag32_machine_config a b c).ptr_reg``]
  \\ fs[EVAL``(ag32_machine_config a b c).len_reg``]
  \\ fs[EVAL``(ag32_machine_config a b c).target.get_reg``]
  \\ fs[EVAL``(ag32_machine_config a b c).target.get_byte``]
  \\ first_assum(mp_then Any mp_tac asmPropsTheory.read_bytearray_IMP_bytes_in_memory)
  \\ last_assum(mp_then Any mp_tac asmPropsTheory.read_bytearray_IMP_bytes_in_memory)
  \\ imp_res_tac read_bytearray_LENGTH \\ fs[]
  \\ qmatch_asmsub_abbrev_tac`_ ∈ md`
  \\ disch_then(qspecl_then[`ms.MEM`,`md`]mp_tac) \\ simp[]
  \\ impl_tac
  >- (
    imp_res_tac read_bytearray_IMP_mem_SOME
    \\ fs[IS_SOME_EXISTS] )
  \\ strip_tac
  \\ disch_then(qspecl_then[`ms.MEM`,`md`]mp_tac) \\ simp[]
  \\ impl_tac
  >- (
    imp_res_tac read_bytearray_IMP_mem_SOME
    \\ fs[IS_SOME_EXISTS] )
  \\ strip_tac
  \\ drule (GEN_ALL mk_jump_ag32_code_thm)
  \\ simp[]
  \\ disch_then drule \\ simp[]
  \\ simp[ffi_entrypoints_def]
  \\ impl_tac
  >- (
    gen_tac \\ strip_tac
    \\ qmatch_goalsub_abbrev_tac`ffi_offset * ix`
    \\ last_x_assum(qspec_then`ix * (ffi_offset DIV 4) + k`mp_tac)
    \\ impl_tac
    >- (
      simp[LENGTH_ag32_ffi_jumps,Abbr`ix`]
      \\ EVAL_TAC
      \\ fs[FFI_codes_def])
    \\ simp[LEFT_ADD_DISTRIB, GSYM word_add_n2w]
    \\ `4 * (ix * (ffi_offset DIV 4)) = ix * ffi_offset`
    by ( EVAL_TAC \\ simp[] )
    \\ pop_assum SUBST1_TAC
    \\ simp[]
    \\ disch_then kall_tac
    \\ simp[ag32_ffi_jumps_def]
    \\ rewrite_tac[GSYM APPEND_ASSOC]
    \\ DEP_REWRITE_TAC[EL_APPEND1]
    \\ simp[LENGTH_FLAT, MAP_MAP_o, o_DEF]
    \\ simp[Once mk_jump_ag32_code_def]
    \\ simp[Q.ISPEC`λx. 4n`SUM_MAP_K |> SIMP_RULE(srw_ss())[]]
    \\ conj_tac
    >- (
      EVAL_TAC
      \\ fs[FFI_codes_def,Abbr`ix`]
      \\ fs[GSYM find_index_INDEX_OF]
      \\ imp_res_tac find_index_LESS_LENGTH
      \\ fs[] )
    \\ simp[EVAL``ffi_offset``]
    \\ irule EL_FLAT_MAP_mk_jump_ag32_code
    \\ simp[INDEX_OF_REVERSE])
  \\ strip_tac
  \\ qmatch_asmsub_abbrev_tac`_ = ms1`
  \\ `(ms.MEM = ms1.MEM) ∧
      (ms.R 1w = ms1.R 1w) ∧
      (ms.R 3w = ms1.R 3w)` by simp[Abbr`ms1`,APPLY_UPDATE_THM] \\ fs[]
  \\ drule (GEN_ALL ag32_ffi_open_in_thm)
  \\ disch_then drule
  \\ qpat_x_assum`Abbrev(md = _)`mp_tac
  \\ CONV_TAC(LAND_CONV(SIMP_CONV(srw_ss()++LET_ss)[ag32_machine_config_def]))
  \\ strip_tac
  \\ disch_then (first_assum o mp_then Any mp_tac)
  \\ simp[]
  \\ qhdtm_x_assum`call_FFI`mp_tac
  \\ simp[ffiTheory.call_FFI_def]
  \\ `ffi.oracle = basis_ffi_oracle` by fs[ag32_ffi_rel_def]
  \\ simp[basis_ffiTheory.basis_ffi_oracle_def]
  \\ pairarg_tac \\ simp[]
  \\ simp[CaseEq"option",CaseEq"oracle_result",CaseEq"bool",CaseEq"ffi_result"]
  \\ strip_tac
  \\ var_eq_tac
  \\ var_eq_tac
  \\ var_eq_tac
  \\ disch_then(first_assum o mp_then Any mp_tac)
  \\ simp[]
  \\ qpat_x_assum`ms.R _ = _`kall_tac
  \\ qpat_x_assum`ms.R _ = _`kall_tac
  \\ qpat_x_assum`ms.MEM = _`kall_tac
  \\ simp[LEFT_FORALL_IMP_THM]
  \\ impl_tac
  >- (
    simp[Abbr`ms1`, APPLY_UPDATE_THM]
    \\ reverse conj_tac >- EVAL_TAC
    \\ fs[ag32_ffi_rel_def])
  \\ strip_tac
  \\ `EL index ffi_names = "open_in"`
  by (
    fs[GSYM find_index_INDEX_OF]
    \\ imp_res_tac find_index_is_MEM
    \\ imp_res_tac find_index_MEM
    \\ first_x_assum(qspec_then`0`mp_tac)
    \\ simp[] )
  \\ `ag32_ffi_interfer ffi_names md (index,bytes',ms) =
      ag32_ffi_interfer ffi_names md (index,bytes',ms1)`
  by (
    simp[ag32_ffi_interfer_def, ag32Theory.ag32_state_component_equality]
    \\ simp[Abbr`ms1`, APPLY_UPDATE_THM]
    \\ simp[FUN_EQ_THM, APPLY_UPDATE_THM] )
  \\ qspec_then`ms1`mp_tac (CONV_RULE(RESORT_FORALL_CONV(sort_vars["s"]))(GEN_ALL ag32_ffi_open_in_code_thm))
  \\ fs[Abbr`ms1`, APPLY_UPDATE_THM]
  \\ fs[ffi_entrypoints_def, GSYM word_add_n2w]
  \\ impl_tac >- (
    EVAL_TAC
    \\ Cases_on`ms.R 3w` \\ fs[]
    \\ CCONTR_TAC \\ fs[] \\ fs[] \\ rveq
    \\ Cases_on`bytes` \\ fs[fsFFITheory.ffi_open_in_def]
    \\ fs[bytes_in_memory_def]
    \\ qpat_x_assum`_ ∈ md`mp_tac
    \\ simp[Abbr`md`]
    \\ EVAL_TAC
    \\ fs[word_ls_n2w, word_lo_n2w]
    \\ fs(map EVAL [``LENGTH FFI_codes``,``memory_size``,``code_start_offset _``]) )
  \\ qmatch_asmsub_abbrev_tac`FUNPOW _ _ _ = ms1`
  \\ strip_tac
  \\ qexists_tac`k'+k`
  \\ simp[FUNPOW_ADD]
  \\ qpat_x_assum`ag32_ffi_interfer _ _ _ = _`(assume_tac o SYM)
  \\ simp[]
  \\ simp[ag32_ffi_interfer_def]
  \\ fs[ag32_ffi_rel_def]
  \\ `!i. i < LENGTH bytes' ==> ms.R 3w + n2w i IN md` by
   (Cases_on `ms.R 4w` \\ fs [] \\ rveq \\ fs []
    \\ drule read_bytearray_IMP_domain \\ fs [])
  \\ simp[ag32_ffi_mem_update_def]
  \\ conj_tac >- (
    conj_tac
    >- (
      simp[get_output_io_event_def, get_ag32_io_event_def]
      \\ DEP_ONCE_REWRITE_TAC[SIMP_RULE(srw_ss())[]asm_write_bytearray_unchanged]
      \\ CONV_TAC(PATH_CONV"rl" EVAL) \\ simp[]
      \\ Cases_on`ms.R 3w` \\ fs[memory_size_def]
      \\ qpat_x_assum`_ = w2n (ms.R 4w)`(assume_tac o SYM)
      \\ imp_res_tac fsFFIPropsTheory.ffi_open_in_length \\ fs[ADD1]
      \\ EVAL_TAC \\ fs[]
      \\ Cases_on`ms.R 4w` \\ fs[word_ls_n2w, word_lo_n2w, word_add_n2w]
      \\ Cases_on`bytes`
      >- ( fs[fsFFITheory.ffi_open_in_def] )
      \\ fs[bytes_in_memory_def]
      \\ qpat_x_assum`n2w n ∈ md` mp_tac
      \\ simp[Abbr`md`]
      \\ EVAL_TAC
      \\ simp[word_add_n2w, LEFT_ADD_DISTRIB]
      \\ fs[word_lo_n2w, word_ls_n2w]
      \\ fs[EVAL``code_start_offset _``])
    \\ conj_tac
    >- metis_tac[ag32_fs_ok_ffi_open_in]
    \\ rveq
    \\ conj_tac
    >- (
      irule ag32_stdin_implemented_ffi_open_in
      \\ fs[PULL_EXISTS]
      \\ asm_exists_tac \\ fs[]
      \\ asm_exists_tac \\ fs[]
      \\ imp_res_tac fsFFIPropsTheory.ffi_open_in_length
      \\ fs[fsFFITheory.ffi_open_in_def]
      \\ Cases_on`bytes` \\ fs[]
      \\ first_x_assum(qspec_then`0`mp_tac)
      \\ simp[Abbr`md`]
      \\ EVAL_TAC
      \\ Cases_on`ms.R 3w` \\ simp[word_add_n2w, word_ls_n2w, word_lo_n2w]
      \\ fs[FFI_codes_def] )
    \\ irule ag32_cline_implemented_ffi_open_in
    \\ fs[PULL_EXISTS]
    \\ asm_exists_tac \\ fs[]
    \\ imp_res_tac fsFFIPropsTheory.ffi_open_in_length
    \\ fs[fsFFITheory.ffi_open_in_def]
    \\ Cases_on`bytes` \\ fs[]
    \\ first_x_assum(qspec_then`0`mp_tac)
    \\ simp[Abbr`md`]
    \\ EVAL_TAC
    \\ Cases_on`ms.R 3w` \\ simp[word_add_n2w, word_ls_n2w, word_lo_n2w]
    \\ fs[FFI_codes_def] )
  \\ gen_tac \\ strip_tac
  \\ irule asm_write_bytearray_unchanged_all_words
  \\ qpat_x_assum`_ = w2n _`(assume_tac o SYM) \\ fs[]
  \\ rw[APPLY_UPDATE_THM]
  \\ qpat_x_assum`_ ∉ ag32_ffi_mem_domain`mp_tac
  \\ EVAL_TAC
QED

Theorem ag32_ffi_interfer_open_out:
   ag32_ffi_rel ms ffi ∧ (SND ffi.ffi_state = fs) ∧
   (read_ffi_bytearrays (ag32_machine_config ffi_names lc ld) ms = (SOME conf, SOME bytes)) ∧
   (call_FFI ffi "open_out" conf bytes = FFI_return ffi' bytes') ∧
   (INDEX_OF "open_out" ffi_names = SOME index) ∧ ALL_DISTINCT ffi_names ∧
   w2n (ms.R 3w) + LENGTH bytes < dimword (:32) ∧
   LENGTH ffi_names ≤ LENGTH FFI_codes ∧
   code_start_offset (LENGTH ffi_names) + lc + 4 * ld < memory_size ∧
   (ms.PC = n2w (ffi_jumps_offset + (LENGTH ffi_names - (index + 1)) * ffi_offset)) ∧
   (∀k. k < LENGTH (ag32_ffi_jumps ffi_names) ⇒
        (get_mem_word ms.MEM (n2w (ffi_jumps_offset + 4 * k))
         = EL k (ag32_ffi_jumps ffi_names))) ∧
   (∀k. k < LENGTH ag32_ffi_open_out_code ⇒
        (get_mem_word ms.MEM (n2w (ffi_code_start_offset + THE (ALOOKUP ffi_entrypoints "open_out") + 4 * k))
         = Encode (EL k ag32_ffi_open_out_code)))
   ⇒
   ∃k.
     (ag32_ffi_interfer ffi_names
        (ag32_prog_addresses (LENGTH ffi_names) lc ld)
        (index,bytes',ms) = FUNPOW Next k ms) ∧
      ag32_ffi_rel (FUNPOW Next k ms) ffi' ∧
      ∀x. x ∉ ag32_ffi_mem_domain ∧
          x ∉ all_words (ms.R 3w) (LENGTH bytes) ⇒
          ((FUNPOW Next k ms).MEM x = ms.MEM x)
Proof
  strip_tac
  \\ fs[targetSemTheory.read_ffi_bytearrays_def]
  \\ fs[targetSemTheory.read_ffi_bytearray_def]
  \\ fs[EVAL``(ag32_machine_config a b c).ptr2_reg``]
  \\ fs[EVAL``(ag32_machine_config a b c).len2_reg``]
  \\ fs[EVAL``(ag32_machine_config a b c).ptr_reg``]
  \\ fs[EVAL``(ag32_machine_config a b c).len_reg``]
  \\ fs[EVAL``(ag32_machine_config a b c).target.get_reg``]
  \\ fs[EVAL``(ag32_machine_config a b c).target.get_byte``]
  \\ first_assum(mp_then Any mp_tac asmPropsTheory.read_bytearray_IMP_bytes_in_memory)
  \\ last_assum(mp_then Any mp_tac asmPropsTheory.read_bytearray_IMP_bytes_in_memory)
  \\ imp_res_tac read_bytearray_LENGTH \\ fs[]
  \\ qmatch_asmsub_abbrev_tac`_ ∈ md`
  \\ disch_then(qspecl_then[`ms.MEM`,`md`]mp_tac) \\ simp[]
  \\ impl_tac
  >- (
    imp_res_tac read_bytearray_IMP_mem_SOME
    \\ fs[IS_SOME_EXISTS] )
  \\ strip_tac
  \\ disch_then(qspecl_then[`ms.MEM`,`md`]mp_tac) \\ simp[]
  \\ impl_tac
  >- (
    imp_res_tac read_bytearray_IMP_mem_SOME
    \\ fs[IS_SOME_EXISTS] )
  \\ strip_tac
  \\ drule (GEN_ALL mk_jump_ag32_code_thm)
  \\ simp[]
  \\ disch_then drule \\ simp[]
  \\ simp[ffi_entrypoints_def]
  \\ impl_tac
  >- (
    gen_tac \\ strip_tac
    \\ qmatch_goalsub_abbrev_tac`ffi_offset * ix`
    \\ last_x_assum(qspec_then`ix * (ffi_offset DIV 4) + k`mp_tac)
    \\ impl_tac
    >- (
      simp[LENGTH_ag32_ffi_jumps,Abbr`ix`]
      \\ EVAL_TAC
      \\ fs[FFI_codes_def])
    \\ simp[LEFT_ADD_DISTRIB, GSYM word_add_n2w]
    \\ `4 * (ix * (ffi_offset DIV 4)) = ix * ffi_offset`
    by ( EVAL_TAC \\ simp[] )
    \\ pop_assum SUBST1_TAC
    \\ simp[]
    \\ disch_then kall_tac
    \\ simp[ag32_ffi_jumps_def]
    \\ rewrite_tac[GSYM APPEND_ASSOC]
    \\ DEP_REWRITE_TAC[EL_APPEND1]
    \\ simp[LENGTH_FLAT, MAP_MAP_o, o_DEF]
    \\ simp[Once mk_jump_ag32_code_def]
    \\ simp[Q.ISPEC`λx. 4n`SUM_MAP_K |> SIMP_RULE(srw_ss())[]]
    \\ conj_tac
    >- (
      EVAL_TAC
      \\ fs[FFI_codes_def,Abbr`ix`]
      \\ fs[GSYM find_index_INDEX_OF]
      \\ imp_res_tac find_index_LESS_LENGTH
      \\ fs[] )
    \\ simp[EVAL``ffi_offset``]
    \\ irule EL_FLAT_MAP_mk_jump_ag32_code
    \\ simp[INDEX_OF_REVERSE])
  \\ strip_tac
  \\ qmatch_asmsub_abbrev_tac`_ = ms1`
  \\ `(ms.MEM = ms1.MEM) ∧
      (ms.R 1w = ms1.R 1w) ∧
      (ms.R 3w = ms1.R 3w)` by simp[Abbr`ms1`,APPLY_UPDATE_THM] \\ fs[]
  \\ drule (GEN_ALL ag32_ffi_open_out_thm)
  \\ disch_then drule
  \\ qpat_x_assum`Abbrev(md = _)`mp_tac
  \\ CONV_TAC(LAND_CONV(SIMP_CONV(srw_ss()++LET_ss)[ag32_machine_config_def]))
  \\ strip_tac
  \\ disch_then (first_assum o mp_then Any mp_tac)
  \\ simp[]
  \\ qhdtm_x_assum`call_FFI`mp_tac
  \\ simp[ffiTheory.call_FFI_def]
  \\ `ffi.oracle = basis_ffi_oracle` by fs[ag32_ffi_rel_def]
  \\ simp[basis_ffiTheory.basis_ffi_oracle_def]
  \\ pairarg_tac \\ simp[]
  \\ simp[CaseEq"option",CaseEq"oracle_result",CaseEq"bool",CaseEq"ffi_result"]
  \\ strip_tac
  \\ var_eq_tac
  \\ var_eq_tac
  \\ var_eq_tac
  \\ disch_then(first_assum o mp_then Any mp_tac)
  \\ simp[]
  \\ qpat_x_assum`ms.R _ = _`kall_tac
  \\ qpat_x_assum`ms.R _ = _`kall_tac
  \\ qpat_x_assum`ms.MEM = _`kall_tac
  \\ simp[LEFT_FORALL_IMP_THM]
  \\ impl_tac
  >- (
    simp[Abbr`ms1`, APPLY_UPDATE_THM]
    \\ reverse conj_tac >- EVAL_TAC
    \\ fs[ag32_ffi_rel_def])
  \\ strip_tac
  \\ `EL index ffi_names = "open_out"`
  by (
    fs[GSYM find_index_INDEX_OF]
    \\ imp_res_tac find_index_is_MEM
    \\ imp_res_tac find_index_MEM
    \\ first_x_assum(qspec_then`0`mp_tac)
    \\ simp[] )
  \\ `ag32_ffi_interfer ffi_names md (index,bytes',ms) =
      ag32_ffi_interfer ffi_names md (index,bytes',ms1)`
  by (
    simp[ag32_ffi_interfer_def, ag32Theory.ag32_state_component_equality]
    \\ simp[Abbr`ms1`, APPLY_UPDATE_THM]
    \\ simp[FUN_EQ_THM, APPLY_UPDATE_THM] )
  \\ qspec_then`ms1`mp_tac (CONV_RULE(RESORT_FORALL_CONV(sort_vars["s"]))(GEN_ALL ag32_ffi_open_out_code_thm))
  \\ fs[Abbr`ms1`, APPLY_UPDATE_THM]
  \\ fs[ffi_entrypoints_def, GSYM word_add_n2w]
  \\ impl_tac >- (
    EVAL_TAC
    \\ Cases_on`ms.R 3w` \\ fs[]
    \\ CCONTR_TAC \\ fs[] \\ fs[] \\ rveq
    \\ Cases_on`bytes` \\ fs[fsFFITheory.ffi_open_out_def]
    \\ fs[bytes_in_memory_def]
    \\ qpat_x_assum`_ ∈ md`mp_tac
    \\ simp[Abbr`md`]
    \\ EVAL_TAC
    \\ fs[word_ls_n2w, word_lo_n2w]
    \\ fs(map EVAL [``LENGTH FFI_codes``,``memory_size``,``code_start_offset _``]) )
  \\ qmatch_asmsub_abbrev_tac`FUNPOW _ _ _ = ms1`
  \\ strip_tac
  \\ qexists_tac`k'+k`
  \\ simp[FUNPOW_ADD]
  \\ qpat_x_assum`ag32_ffi_interfer _ _ _ = _`(assume_tac o SYM)
  \\ simp[]
  \\ simp[ag32_ffi_interfer_def]
  \\ fs[ag32_ffi_rel_def]
  \\ `!i. i < LENGTH bytes' ==> ms.R 3w + n2w i IN md` by
   (Cases_on `ms.R 4w` \\ fs [] \\ rveq \\ fs []
    \\ drule read_bytearray_IMP_domain \\ fs [])
  \\ simp[ag32_ffi_mem_update_def]
  \\ conj_tac >- (
    conj_tac
    >- (
      simp[get_output_io_event_def, get_ag32_io_event_def]
      \\ DEP_ONCE_REWRITE_TAC[SIMP_RULE(srw_ss())[]asm_write_bytearray_unchanged]
      \\ CONV_TAC(PATH_CONV"rl" EVAL) \\ simp[]
      \\ Cases_on`ms.R 3w` \\ fs[memory_size_def]
      \\ qpat_x_assum`_ = w2n (ms.R 4w)`(assume_tac o SYM)
      \\ imp_res_tac fsFFIPropsTheory.ffi_open_out_length \\ fs[ADD1]
      \\ EVAL_TAC \\ fs[]
      \\ Cases_on`ms.R 4w` \\ fs[word_ls_n2w, word_lo_n2w, word_add_n2w]
      \\ Cases_on`bytes`
      >- ( fs[fsFFITheory.ffi_open_out_def] )
      \\ fs[bytes_in_memory_def]
      \\ qpat_x_assum`n2w n ∈ md` mp_tac
      \\ simp[Abbr`md`]
      \\ EVAL_TAC
      \\ simp[word_add_n2w, LEFT_ADD_DISTRIB]
      \\ fs[word_lo_n2w, word_ls_n2w]
      \\ fs[EVAL``code_start_offset _``])
    \\ conj_tac
    >- metis_tac[ag32_fs_ok_ffi_open_out]
    \\ `n2w heap_start_offset <=+ ms.R 3w`
    by (
      imp_res_tac fsFFIPropsTheory.ffi_open_out_length
      \\ fs[fsFFITheory.ffi_open_out_def]
      \\ Cases_on`bytes` \\ fs[]
      \\ first_x_assum(qspec_then`0`mp_tac)
      \\ simp[Abbr`md`]
      \\ EVAL_TAC
      \\ Cases_on`ms.R 3w` \\ simp[word_add_n2w, word_ls_n2w, word_lo_n2w]
      \\ fs[FFI_codes_def] )
    \\ rveq
    \\ conj_tac
    >- (
      irule ag32_stdin_implemented_ffi_open_out
      \\ fs[PULL_EXISTS]
      \\ asm_exists_tac \\ fs[]
      \\ asm_exists_tac \\ fs[])
    \\ irule ag32_cline_implemented_ffi_open_out
    \\ fs[PULL_EXISTS]
    \\ asm_exists_tac \\ fs[])
  \\ gen_tac \\ strip_tac
  \\ irule asm_write_bytearray_unchanged_all_words
  \\ qpat_x_assum`_ = w2n _`(assume_tac o SYM) \\ fs[]
  \\ rw[APPLY_UPDATE_THM]
  \\ qpat_x_assum`_ ∉ ag32_ffi_mem_domain`mp_tac
  \\ EVAL_TAC
QED

Theorem ag32_ffi_interfer_close:
   ag32_ffi_rel ms ffi ∧ (SND ffi.ffi_state = fs) ∧
   (read_ffi_bytearrays (ag32_machine_config ffi_names lc ld) ms = (SOME conf, SOME bytes)) ∧
   (call_FFI ffi "close" conf bytes = FFI_return ffi' bytes') ∧
   (INDEX_OF "close" ffi_names = SOME index) ∧ ALL_DISTINCT ffi_names ∧
   w2n (ms.R 3w) + LENGTH bytes < dimword (:32) ∧
   LENGTH ffi_names ≤ LENGTH FFI_codes ∧
   code_start_offset (LENGTH ffi_names) + lc + 4 * ld < memory_size ∧
   (ms.PC = n2w (ffi_jumps_offset + (LENGTH ffi_names - (index + 1)) * ffi_offset)) ∧
   (∀k. k < LENGTH (ag32_ffi_jumps ffi_names) ⇒
        (get_mem_word ms.MEM (n2w (ffi_jumps_offset + 4 * k))
         = EL k (ag32_ffi_jumps ffi_names))) ∧
   (∀k. k < LENGTH ag32_ffi_close_code ⇒
        (get_mem_word ms.MEM (n2w (ffi_code_start_offset + THE (ALOOKUP ffi_entrypoints "close") + 4 * k))
         = Encode (EL k ag32_ffi_close_code)))
   ⇒
   ∃k.
     (ag32_ffi_interfer ffi_names
        (ag32_prog_addresses (LENGTH ffi_names) lc ld)
        (index,bytes',ms) = FUNPOW Next k ms) ∧
      ag32_ffi_rel (FUNPOW Next k ms) ffi' ∧
      ∀x. x ∉ ag32_ffi_mem_domain ∧
          x ∉ all_words (ms.R 3w) (LENGTH bytes) ⇒
          ((FUNPOW Next k ms).MEM x = ms.MEM x)
Proof
  strip_tac
  \\ fs[targetSemTheory.read_ffi_bytearrays_def]
  \\ fs[targetSemTheory.read_ffi_bytearray_def]
  \\ fs[EVAL``(ag32_machine_config a b c).ptr2_reg``]
  \\ fs[EVAL``(ag32_machine_config a b c).len2_reg``]
  \\ fs[EVAL``(ag32_machine_config a b c).ptr_reg``]
  \\ fs[EVAL``(ag32_machine_config a b c).len_reg``]
  \\ fs[EVAL``(ag32_machine_config a b c).target.get_reg``]
  \\ fs[EVAL``(ag32_machine_config a b c).target.get_byte``]
  \\ first_assum(mp_then Any mp_tac asmPropsTheory.read_bytearray_IMP_bytes_in_memory)
  \\ last_assum(mp_then Any mp_tac asmPropsTheory.read_bytearray_IMP_bytes_in_memory)
  \\ imp_res_tac read_bytearray_LENGTH \\ fs[]
  \\ qmatch_asmsub_abbrev_tac`_ ∈ md`
  \\ disch_then(qspecl_then[`ms.MEM`,`md`]mp_tac) \\ simp[]
  \\ impl_tac
  >- (
    imp_res_tac read_bytearray_IMP_mem_SOME
    \\ fs[IS_SOME_EXISTS] )
  \\ strip_tac
  \\ disch_then(qspecl_then[`ms.MEM`,`md`]mp_tac) \\ simp[]
  \\ impl_tac
  >- (
    imp_res_tac read_bytearray_IMP_mem_SOME
    \\ fs[IS_SOME_EXISTS] )
  \\ strip_tac
  \\ drule (GEN_ALL mk_jump_ag32_code_thm)
  \\ simp[]
  \\ disch_then drule \\ simp[]
  \\ simp[ffi_entrypoints_def]
  \\ impl_tac
  >- (
    gen_tac \\ strip_tac
    \\ qmatch_goalsub_abbrev_tac`ffi_offset * ix`
    \\ last_x_assum(qspec_then`ix * (ffi_offset DIV 4) + k`mp_tac)
    \\ impl_tac
    >- (
      simp[LENGTH_ag32_ffi_jumps,Abbr`ix`]
      \\ EVAL_TAC
      \\ fs[FFI_codes_def])
    \\ simp[LEFT_ADD_DISTRIB, GSYM word_add_n2w]
    \\ `4 * (ix * (ffi_offset DIV 4)) = ix * ffi_offset`
    by ( EVAL_TAC \\ simp[] )
    \\ pop_assum SUBST1_TAC
    \\ simp[]
    \\ disch_then kall_tac
    \\ simp[ag32_ffi_jumps_def]
    \\ rewrite_tac[GSYM APPEND_ASSOC]
    \\ DEP_REWRITE_TAC[EL_APPEND1]
    \\ simp[LENGTH_FLAT, MAP_MAP_o, o_DEF]
    \\ simp[Once mk_jump_ag32_code_def]
    \\ simp[Q.ISPEC`λx. 4n`SUM_MAP_K |> SIMP_RULE(srw_ss())[]]
    \\ conj_tac
    >- (
      EVAL_TAC
      \\ fs[FFI_codes_def,Abbr`ix`]
      \\ fs[GSYM find_index_INDEX_OF]
      \\ imp_res_tac find_index_LESS_LENGTH
      \\ fs[] )
    \\ simp[EVAL``ffi_offset``]
    \\ irule EL_FLAT_MAP_mk_jump_ag32_code
    \\ simp[INDEX_OF_REVERSE])
  \\ strip_tac
  \\ qmatch_asmsub_abbrev_tac`_ = ms1`
  \\ `(ms.MEM = ms1.MEM) ∧
      (ms.R 1w = ms1.R 1w) ∧
      (ms.R 3w = ms1.R 3w)` by simp[Abbr`ms1`,APPLY_UPDATE_THM] \\ fs[]
  \\ drule (GEN_ALL ag32_ffi_close_thm)
  \\ disch_then drule
  \\ qpat_x_assum`Abbrev(md = _)`mp_tac
  \\ CONV_TAC(LAND_CONV(SIMP_CONV(srw_ss()++LET_ss)[ag32_machine_config_def]))
  \\ strip_tac
  \\ disch_then (first_assum o mp_then Any mp_tac)
  \\ simp[]
  \\ qhdtm_x_assum`call_FFI`mp_tac
  \\ simp[ffiTheory.call_FFI_def]
  \\ `ffi.oracle = basis_ffi_oracle` by fs[ag32_ffi_rel_def]
  \\ simp[basis_ffiTheory.basis_ffi_oracle_def]
  \\ pairarg_tac \\ simp[]
  \\ simp[CaseEq"option",CaseEq"oracle_result",CaseEq"bool",CaseEq"ffi_result"]
  \\ strip_tac
  \\ var_eq_tac
  \\ var_eq_tac
  \\ var_eq_tac
  \\ disch_then(first_assum o mp_then Any mp_tac)
  \\ simp[]
  \\ qpat_x_assum`ms.R _ = _`kall_tac
  \\ qpat_x_assum`ms.R _ = _`kall_tac
  \\ qpat_x_assum`ms.MEM = _`kall_tac
  \\ simp[LEFT_FORALL_IMP_THM]
  \\ impl_tac
  >- (
    simp[Abbr`ms1`, APPLY_UPDATE_THM]
    \\ reverse conj_tac >- EVAL_TAC
    \\ fs[ag32_ffi_rel_def])
  \\ strip_tac
  \\ `EL index ffi_names = "close"`
  by (
    fs[GSYM find_index_INDEX_OF]
    \\ imp_res_tac find_index_is_MEM
    \\ imp_res_tac find_index_MEM
    \\ first_x_assum(qspec_then`0`mp_tac)
    \\ simp[] )
  \\ `ag32_ffi_interfer ffi_names md (index,bytes',ms) =
      ag32_ffi_interfer ffi_names md (index,bytes',ms1)`
  by (
    simp[ag32_ffi_interfer_def, ag32Theory.ag32_state_component_equality]
    \\ simp[Abbr`ms1`, APPLY_UPDATE_THM]
    \\ simp[FUN_EQ_THM, APPLY_UPDATE_THM] )
  \\ qspec_then`ms1`mp_tac (CONV_RULE(RESORT_FORALL_CONV(sort_vars["s"]))(GEN_ALL ag32_ffi_close_code_thm))
  \\ fs[Abbr`ms1`, APPLY_UPDATE_THM]
  \\ fs[ffi_entrypoints_def, GSYM word_add_n2w]
  \\ impl_tac >- (
    EVAL_TAC
    \\ Cases_on`ms.R 3w` \\ fs[]
    \\ CCONTR_TAC \\ fs[] \\ fs[] \\ rveq
    \\ Cases_on`bytes` \\ fs[fsFFITheory.ffi_close_def]
    \\ fs[bytes_in_memory_def]
    \\ qpat_x_assum`_ ∈ md`mp_tac
    \\ simp[Abbr`md`]
    \\ EVAL_TAC
    \\ fs[word_ls_n2w, word_lo_n2w]
    \\ fs(map EVAL [``LENGTH FFI_codes``,``memory_size``,``code_start_offset _``]) )
  \\ qmatch_asmsub_abbrev_tac`FUNPOW _ _ _ = ms1`
  \\ strip_tac
  \\ qexists_tac`k'+k`
  \\ simp[FUNPOW_ADD]
  \\ qpat_x_assum`ag32_ffi_interfer _ _ _ = _`(assume_tac o SYM)
  \\ simp[]
  \\ simp[ag32_ffi_interfer_def]
  \\ fs[ag32_ffi_rel_def]
  \\ `!i. i < LENGTH bytes' ==> ms.R 3w + n2w i IN md` by
   (Cases_on `ms.R 4w` \\ fs [] \\ rveq \\ fs []
    \\ drule read_bytearray_IMP_domain \\ fs [])
  \\ simp[ag32_ffi_mem_update_def]
  \\ conj_tac >- (
    conj_tac
    >- (
      simp[get_output_io_event_def, get_ag32_io_event_def]
      \\ DEP_ONCE_REWRITE_TAC[SIMP_RULE(srw_ss())[]asm_write_bytearray_unchanged]
      \\ CONV_TAC(PATH_CONV"rl" EVAL) \\ simp[]
      \\ Cases_on`ms.R 3w` \\ fs[memory_size_def]
      \\ qpat_x_assum`_ = w2n (ms.R 4w)`(assume_tac o SYM)
      \\ imp_res_tac fsFFIPropsTheory.ffi_close_length \\ fs[ADD1]
      \\ EVAL_TAC \\ fs[]
      \\ Cases_on`ms.R 4w` \\ fs[word_ls_n2w, word_lo_n2w, word_add_n2w]
      \\ Cases_on`bytes`
      >- ( fs[fsFFITheory.ffi_close_def] )
      \\ fs[bytes_in_memory_def]
      \\ qpat_x_assum`n2w n ∈ md` mp_tac
      \\ simp[Abbr`md`]
      \\ EVAL_TAC
      \\ simp[word_add_n2w, LEFT_ADD_DISTRIB]
      \\ fs[word_lo_n2w, word_ls_n2w]
      \\ fs[EVAL``code_start_offset _``])
    \\ conj_tac
    >- metis_tac[ag32_fs_ok_ffi_close]
    \\ `n2w heap_start_offset <=+ ms.R 3w`
    by (
      imp_res_tac fsFFIPropsTheory.ffi_close_length
      \\ fs[fsFFITheory.ffi_close_def]
      \\ Cases_on`bytes` \\ fs[]
      \\ first_x_assum(qspec_then`0`mp_tac)
      \\ simp[Abbr`md`]
      \\ EVAL_TAC
      \\ Cases_on`ms.R 3w` \\ simp[word_add_n2w, word_ls_n2w, word_lo_n2w]
      \\ fs[FFI_codes_def] )
    \\ rveq
    \\ conj_tac
    >- (
      irule ag32_stdin_implemented_ffi_close
      \\ fs[PULL_EXISTS]
      \\ asm_exists_tac \\ fs[]
      \\ asm_exists_tac \\ fs[])
    \\ irule ag32_cline_implemented_ffi_close
    \\ fs[PULL_EXISTS]
    \\ asm_exists_tac \\ fs[])
  \\ gen_tac \\ strip_tac
  \\ irule asm_write_bytearray_unchanged_all_words
  \\ qpat_x_assum`_ = w2n _`(assume_tac o SYM) \\ fs[]
  \\ rw[APPLY_UPDATE_THM]
  \\ qpat_x_assum`_ ∉ ag32_ffi_mem_domain`mp_tac
  \\ EVAL_TAC
QED

val ag32_ffi_get_arg_count_entrypoint_thm =
    EVAL “ag32_ffi_get_arg_count_entrypoint”
val ffi_code_start_offset_thm = EVAL “ffi_code_start_offset”

Theorem ag32_ffi_interfer_get_arg_count:
   ag32_ffi_rel ms ffi ∧
   (read_ffi_bytearrays (ag32_machine_config ffi_names lc ld) ms = (SOME conf, SOME bytes)) ∧
   (call_FFI ffi "get_arg_count" conf bytes = FFI_return ffi' bytes') ∧
   (INDEX_OF "get_arg_count" ffi_names = SOME index) ∧ ALL_DISTINCT ffi_names ∧
   w2n (ms.R 3w) + LENGTH bytes < dimword (:32) ∧
   LENGTH ffi_names ≤ LENGTH FFI_codes ∧
   code_start_offset (LENGTH ffi_names) + lc + 4 * ld < memory_size ∧
   (ms.PC = n2w (ffi_jumps_offset + (LENGTH ffi_names - (index + 1)) * ffi_offset)) ∧
   (∀k. k < LENGTH (ag32_ffi_jumps ffi_names) ⇒
        (get_mem_word ms.MEM (n2w (ffi_jumps_offset + 4 * k))
         = EL k (ag32_ffi_jumps ffi_names))) ∧
   (∀k. k < LENGTH ag32_ffi_get_arg_count_code ⇒
        (get_mem_word ms.MEM (n2w (ffi_code_start_offset + THE (ALOOKUP ffi_entrypoints "get_arg_count") + 4 * k))
         = Encode (EL k ag32_ffi_get_arg_count_code)))
   ⇒
   ∃k.
     (ag32_ffi_interfer ffi_names
        (ag32_prog_addresses (LENGTH ffi_names) lc ld)
        (index,bytes',ms) = FUNPOW Next k ms) ∧
      ag32_ffi_rel (FUNPOW Next k ms) ffi' ∧
      ∀x. x ∉ ag32_ffi_mem_domain ∧
          x ∉ all_words (ms.R 3w) (LENGTH bytes) ⇒
          ((FUNPOW Next k ms).MEM x = ms.MEM x)
Proof
  strip_tac
  \\ fs[targetSemTheory.read_ffi_bytearrays_def]
  \\ fs[targetSemTheory.read_ffi_bytearray_def]
  \\ fs[EVAL``(ag32_machine_config a b c).ptr2_reg``]
  \\ fs[EVAL``(ag32_machine_config a b c).len2_reg``]
  \\ fs[EVAL``(ag32_machine_config a b c).ptr_reg``]
  \\ fs[EVAL``(ag32_machine_config a b c).len_reg``]
  \\ fs[EVAL``(ag32_machine_config a b c).target.get_reg``]
  \\ fs[EVAL``(ag32_machine_config a b c).target.get_byte``]
  \\ first_assum(mp_then Any mp_tac asmPropsTheory.read_bytearray_IMP_bytes_in_memory)
  \\ last_assum(mp_then Any mp_tac asmPropsTheory.read_bytearray_IMP_bytes_in_memory)
  \\ imp_res_tac read_bytearray_LENGTH \\ fs[]
  \\ qmatch_asmsub_abbrev_tac`_ ∈ md`
  \\ disch_then(qspecl_then[`ms.MEM`,`md`]mp_tac) \\ simp[]
  \\ impl_tac
  >- (
    imp_res_tac read_bytearray_IMP_mem_SOME
    \\ fs[IS_SOME_EXISTS] )
  \\ strip_tac
  \\ disch_then(qspecl_then[`ms.MEM`,`md`]mp_tac) \\ simp[]
  \\ impl_tac
  >- (
    imp_res_tac read_bytearray_IMP_mem_SOME
    \\ fs[IS_SOME_EXISTS] )
  \\ strip_tac
  \\ drule (GEN_ALL mk_jump_ag32_code_thm)
  \\ simp[]
  \\ disch_then drule \\ simp[]
  \\ simp[ffi_entrypoints_def]
  \\ impl_tac
  >- (
    gen_tac \\ strip_tac
    \\ qmatch_goalsub_abbrev_tac`ffi_offset * ix`
    \\ last_x_assum(qspec_then`ix * (ffi_offset DIV 4) + k`mp_tac)
    \\ impl_tac
    >- (
      simp[LENGTH_ag32_ffi_jumps,Abbr`ix`]
      \\ EVAL_TAC
      \\ fs[FFI_codes_def])
    \\ simp[LEFT_ADD_DISTRIB, GSYM word_add_n2w]
    \\ `4 * (ix * (ffi_offset DIV 4)) = ix * ffi_offset`
    by ( EVAL_TAC \\ simp[] )
    \\ pop_assum SUBST1_TAC
    \\ simp[]
    \\ disch_then kall_tac
    \\ simp[ag32_ffi_jumps_def]
    \\ rewrite_tac[GSYM APPEND_ASSOC]
    \\ DEP_REWRITE_TAC[EL_APPEND1]
    \\ simp[LENGTH_FLAT, MAP_MAP_o, o_DEF]
    \\ simp[Once mk_jump_ag32_code_def]
    \\ simp[Q.ISPEC`λx. 4n`SUM_MAP_K |> SIMP_RULE(srw_ss())[]]
    \\ conj_tac
    >- (
      EVAL_TAC
      \\ fs[FFI_codes_def,Abbr`ix`]
      \\ fs[GSYM find_index_INDEX_OF]
      \\ imp_res_tac find_index_LESS_LENGTH
      \\ fs[] )
    \\ simp[lab_to_targetTheory.ffi_offset_def]
    \\ irule EL_FLAT_MAP_mk_jump_ag32_code
    \\ simp[INDEX_OF_REVERSE])
  \\ strip_tac
  \\ qmatch_asmsub_abbrev_tac`_ = ms1`
  \\ `(ms.MEM = ms1.MEM) ∧
      (ms.R 1w = ms1.R 1w) ∧
      (ms.R 3w = ms1.R 3w)` by simp[Abbr`ms1`,APPLY_UPDATE_THM] \\ fs[]
  \\ drule (GEN_ALL ag32_ffi_get_arg_count_thm)
  \\ disch_then drule
  \\ qpat_x_assum`Abbrev(md = _)`mp_tac
  \\ CONV_TAC(LAND_CONV(SIMP_CONV(srw_ss()++LET_ss)[ag32_machine_config_def]))
  \\ strip_tac
  \\ disch_then (first_assum o mp_then Any mp_tac)
  \\ simp[]
  \\ qhdtm_x_assum`call_FFI`mp_tac
  \\ simp[ffiTheory.call_FFI_def]
  \\ `ffi.oracle = basis_ffi_oracle` by fs[ag32_ffi_rel_def]
  \\ simp[basis_ffiTheory.basis_ffi_oracle_def]
  \\ pairarg_tac \\ simp[]
  \\ simp[CaseEq"option",CaseEq"oracle_result",CaseEq"bool",CaseEq"ffi_result"]
  \\ strip_tac
  \\ var_eq_tac
  \\ var_eq_tac
  \\ var_eq_tac
  \\ disch_then(first_assum o mp_then Any mp_tac)
  \\ simp[]
  \\ qpat_x_assum`ms.R _ = _`kall_tac
  \\ qpat_x_assum`ms.R _ = _`kall_tac
  \\ qpat_x_assum`ms.MEM = _`kall_tac
  \\ simp[LEFT_FORALL_IMP_THM]
  \\ impl_tac
  >- (
    simp[Abbr`ms1`, APPLY_UPDATE_THM]
    \\ fs[ag32_ffi_rel_def, ag32_cline_implemented_def]
    \\ EVAL_TAC \\ fs [markerTheory.Abbrev_def])
  \\ strip_tac
  \\ `EL index ffi_names = "get_arg_count"`
  by (
    fs[GSYM find_index_INDEX_OF]
    \\ imp_res_tac find_index_is_MEM
    \\ imp_res_tac find_index_MEM
    \\ first_x_assum(qspec_then`0`mp_tac)
    \\ simp[] )
  \\ `ag32_ffi_interfer ffi_names md (index,bytes',ms) =
      ag32_ffi_interfer ffi_names md (index,bytes',ms1)`
  by (
    simp[ag32_ffi_interfer_def, ag32Theory.ag32_state_component_equality]
    \\ simp[Abbr`ms1`, APPLY_UPDATE_THM]
    \\ simp[FUN_EQ_THM, APPLY_UPDATE_THM] )
  \\ qspec_then`ms1`mp_tac (CONV_RULE(RESORT_FORALL_CONV(sort_vars["s"]))(GEN_ALL ag32_ffi_get_arg_count_code_thm))
  \\ fs[Abbr`ms1`, APPLY_UPDATE_THM]
  \\ fs[ffi_entrypoints_def, GSYM word_add_n2w] >> impl_tac
  >- (fs[word_add_n2w, ag32_ffi_get_arg_count_entrypoint_thm,
         ffi_code_start_offset_thm] >> reverse conj_tac >- EVAL_TAC >>
      simp[DIV_LT_X, ag32_ffi_get_arg_count_code_def,
           ag32_ffi_get_arg_count_main_code_def, ag32_ffi_return_code_def] >>
      qx_gen_tac `i` >> spose_not_then strip_assume_tac >>
      `ms.R 3w ∈ md`
        by (Cases_on `bytes` >>
            fs[bytes_in_memory_def,
               clFFITheory.ffi_get_arg_count_def]) >>
      pop_assum mp_tac >>
      simp[Abbr‘md’, ag32_prog_addresses_def, heap_start_offset_def,
           ffi_code_start_offset_thm, code_start_offset_def,
           length_ag32_ffi_code_def, ffi_jumps_offset_def,
           lab_to_targetTheory.ffi_offset_def, heap_size_def] >>
      simp[word_ls_n2w, word_lo_n2w] >>
      fs[FFI_codes_def])
  \\ qmatch_asmsub_abbrev_tac`FUNPOW _ _ _ = ms1`
  \\ strip_tac
  \\ qexists_tac`k'+k`
  \\ simp[FUNPOW_ADD]
  \\ qpat_x_assum`ag32_ffi_interfer _ _ _ = _`(assume_tac o SYM)
  \\ simp[]
  \\ simp[ag32_ffi_interfer_def]
  \\ fs[ag32_ffi_rel_def]
  \\ `!i. i < LENGTH bytes' ==> ms.R 3w + n2w i IN md` by
   (Cases_on `ms.R 4w` \\ fs [] \\ rveq \\ fs []
    \\ drule read_bytearray_IMP_domain \\ fs [])
  \\ conj_tac >- (
    fs[]
    \\ conj_tac
    >- (
      simp[ag32_ffi_mem_update_def]
      \\ simp[get_output_io_event_def]
      \\ simp[get_ag32_io_event_def, APPLY_UPDATE_THM]
      \\ DEP_ONCE_REWRITE_TAC[SIMP_RULE(srw_ss())[]asm_write_bytearray_unchanged]
      \\ simp[APPLY_UPDATE_THM]
      \\ EVAL_TAC
      \\ fs[clFFITheory.ffi_get_arg_count_def]
      \\ rveq \\ fs[]
      \\ first_x_assum(qspec_then`0`mp_tac)
      \\ simp[Abbr`md`]
      \\ Cases_on`ms.R 3w`
      \\ EVAL_TAC
      \\ fs[word_add_n2w, word_ls_n2w, word_lo_n2w, LEFT_ADD_DISTRIB, FFI_codes_def])
    \\ simp[ag32_ffi_mem_update_def]
    \\ `n2w heap_start_offset <=+ ms.R 3w`
    by (
      fs[clFFITheory.ffi_get_arg_count_def]
      \\ Cases_on`bytes` \\ fs[]
      \\ first_x_assum(qspec_then`0`mp_tac)
      \\ simp[Abbr`md`]
      \\ EVAL_TAC
      \\ Cases_on`ms.R 3w` \\ simp[word_add_n2w, word_ls_n2w, word_lo_n2w]
      \\ fs[FFI_codes_def] )
    \\ conj_tac
    >- (
      irule ag32_stdin_implemented_ffi_get_arg_count
      \\ fs[PULL_EXISTS]
      \\ asm_exists_tac \\ fs[] )
    \\ irule ag32_cline_implemented_ffi_get_arg_count
    \\ fs[PULL_EXISTS]
    \\ asm_exists_tac \\ fs[])
  \\ gen_tac \\ strip_tac
  \\ simp[ag32_ffi_mem_update_def]
  \\ imp_res_tac read_bytearray_LENGTH \\ fs[ADD1]
  \\ qpat_x_assum`_ = w2n _`(assume_tac o SYM) \\ fs[]
  \\ irule asm_write_bytearray_unchanged_all_words
  \\ simp[APPLY_UPDATE_THM]
  \\ rw[]
  \\ qpat_x_assum`_ ∉ ag32_ffi_mem_domain`mp_tac
  \\ EVAL_TAC
QED

Theorem cline_in_memory_has_n_args:
   ∀l cls a.
   bytes_in_memory a (FLAT (MAP (SNOC 0w) cls)) m md ∧
   l ≤ LENGTH cls ∧ EVERY (EVERY ((<>)0w)) cls
  ⇒
   has_n_args m a l
Proof
  Induct
  >> simp[has_n_args_def]
  \\ Cases \\ simp[]
  \\ rw[bytes_in_memory_APPEND]
  \\ first_x_assum drule
  \\ simp[] \\ strip_tac
  \\ fs[ADD1, GSYM word_add_n2w]
  \\ goal_assum(first_assum o mp_then Any mp_tac)
  \\ fs[SNOC_APPEND, bytes_in_memory_APPEND, bytes_in_memory_def]
  \\ imp_res_tac bytes_in_memory_EL
  \\ simp[]
  \\ fs[EVERY_MEM, MEM_EL, DISJ_EQ_IMP]
QED

Theorem ag32_ffi_interfer_get_arg_length:
   ag32_ffi_rel ms ffi ∧
   (read_ffi_bytearrays (ag32_machine_config ffi_names lc ld) ms = (SOME conf, SOME bytes)) ∧
   (call_FFI ffi "get_arg_length" conf bytes = FFI_return ffi' bytes') ∧
   (INDEX_OF "get_arg_length" ffi_names = SOME index) ∧ ALL_DISTINCT ffi_names ∧
   w2n (ms.R 3w) + LENGTH bytes < dimword (:32) ∧
   LENGTH ffi_names ≤ LENGTH FFI_codes ∧
   code_start_offset (LENGTH ffi_names) + lc + 4 * ld < memory_size ∧
   (ms.PC = n2w (ffi_jumps_offset + (LENGTH ffi_names - (index+1)) * ffi_offset)) ∧
   (∀k. k < LENGTH (ag32_ffi_jumps ffi_names) ⇒
        (get_mem_word ms.MEM (n2w (ffi_jumps_offset + 4 * k))
         = EL k (ag32_ffi_jumps ffi_names))) ∧
   (∀k. k < LENGTH ag32_ffi_get_arg_length_code ⇒
        (get_mem_word ms.MEM (n2w (ffi_code_start_offset + THE (ALOOKUP ffi_entrypoints "get_arg_length") + 4 * k))
         = Encode (EL k ag32_ffi_get_arg_length_code)))
   ⇒
   ∃k.
     (ag32_ffi_interfer ffi_names
        (ag32_prog_addresses (LENGTH ffi_names) lc ld)
        (index,bytes',ms) = FUNPOW Next k ms) ∧
      ag32_ffi_rel (FUNPOW Next k ms) ffi' ∧
      ∀x. x ∉ ag32_ffi_mem_domain ∧
          x ∉ all_words (ms.R 3w) (LENGTH bytes) ⇒
          ((FUNPOW Next k ms).MEM x = ms.MEM x)
Proof
  strip_tac
  \\ fs[targetSemTheory.read_ffi_bytearrays_def]
  \\ fs[targetSemTheory.read_ffi_bytearray_def]
  \\ fs[EVAL``(ag32_machine_config a b c).ptr2_reg``]
  \\ fs[EVAL``(ag32_machine_config a b c).len2_reg``]
  \\ fs[EVAL``(ag32_machine_config a b c).ptr_reg``]
  \\ fs[EVAL``(ag32_machine_config a b c).len_reg``]
  \\ fs[EVAL``(ag32_machine_config a b c).target.get_reg``]
  \\ fs[EVAL``(ag32_machine_config a b c).target.get_byte``]
  \\ first_assum(mp_then Any mp_tac asmPropsTheory.read_bytearray_IMP_bytes_in_memory)
  \\ last_assum(mp_then Any mp_tac asmPropsTheory.read_bytearray_IMP_bytes_in_memory)
  \\ imp_res_tac read_bytearray_LENGTH \\ fs[]
  \\ qmatch_asmsub_abbrev_tac`_ ∈ md`
  \\ disch_then(qspecl_then[`ms.MEM`,`md`]mp_tac) \\ simp[]
  \\ impl_tac
  >- (
    imp_res_tac read_bytearray_IMP_mem_SOME
    \\ fs[IS_SOME_EXISTS] )
  \\ strip_tac
  \\ disch_then(qspecl_then[`ms.MEM`,`md`]mp_tac) \\ simp[]
  \\ impl_tac
  >- (
    imp_res_tac read_bytearray_IMP_mem_SOME
    \\ fs[IS_SOME_EXISTS] )
  \\ strip_tac
  \\ drule (GEN_ALL mk_jump_ag32_code_thm)
  \\ simp[]
  \\ disch_then drule \\ simp[]
  \\ simp[ffi_entrypoints_def]
  \\ impl_tac
  >- (
    gen_tac \\ strip_tac
    \\ qmatch_goalsub_abbrev_tac`ffi_offset * ix`
    \\ last_x_assum(qspec_then`ix * (ffi_offset DIV 4) + k`mp_tac)
    \\ impl_tac
    >- (
      simp[LENGTH_ag32_ffi_jumps,Abbr`ix`]
      \\ EVAL_TAC
      \\ fs[FFI_codes_def])
    \\ simp[LEFT_ADD_DISTRIB, GSYM word_add_n2w]
    \\ `4 * (ix * (ffi_offset DIV 4)) = ix * ffi_offset`
    by ( EVAL_TAC \\ simp[] )
    \\ pop_assum SUBST1_TAC
    \\ simp[]
    \\ disch_then kall_tac
    \\ simp[ag32_ffi_jumps_def]
    \\ rewrite_tac[GSYM APPEND_ASSOC]
    \\ DEP_REWRITE_TAC[EL_APPEND1]
    \\ simp[LENGTH_FLAT, MAP_MAP_o, o_DEF]
    \\ simp[Once mk_jump_ag32_code_def]
    \\ simp[Q.ISPEC`λx. 4n`SUM_MAP_K |> SIMP_RULE(srw_ss())[]]
    \\ conj_tac
    >- (
      EVAL_TAC
      \\ fs[FFI_codes_def,Abbr`ix`]
      \\ fs[GSYM find_index_INDEX_OF]
      \\ imp_res_tac find_index_LESS_LENGTH
      \\ fs[] )
    \\ simp[lab_to_targetTheory.ffi_offset_def]
    \\ irule EL_FLAT_MAP_mk_jump_ag32_code
    \\ simp[INDEX_OF_REVERSE])
  \\ strip_tac
  \\ qmatch_asmsub_abbrev_tac`_ = ms1`
  \\ `(ms.MEM = ms1.MEM) ∧
      (ms.R 1w = ms1.R 1w) ∧
      (ms.R 3w = ms1.R 3w)` by simp[Abbr`ms1`,APPLY_UPDATE_THM] \\ fs[]
  \\ drule (GEN_ALL ag32_ffi_get_arg_length_thm)
  \\ disch_then drule
  \\ qpat_x_assum`Abbrev(md = _)`mp_tac
  \\ CONV_TAC(LAND_CONV(SIMP_CONV(srw_ss()++LET_ss)[ag32_machine_config_def]))
  \\ strip_tac
  \\ disch_then (first_assum o mp_then Any mp_tac)
  \\ simp[]
  \\ qhdtm_x_assum`call_FFI`mp_tac
  \\ simp[ffiTheory.call_FFI_def]
  \\ `ffi.oracle = basis_ffi_oracle` by fs[ag32_ffi_rel_def]
  \\ simp[basis_ffiTheory.basis_ffi_oracle_def]
  \\ pairarg_tac \\ simp[]
  \\ simp[CaseEq"option",CaseEq"oracle_result",CaseEq"bool",CaseEq"ffi_result"]
  \\ strip_tac
  \\ var_eq_tac
  \\ var_eq_tac
  \\ var_eq_tac
  \\ disch_then(first_assum o mp_then Any mp_tac)
  \\ simp[]
  \\ qpat_x_assum`ms.R _ = _`kall_tac
  \\ qpat_x_assum`ms.R _ = _`kall_tac
  \\ qpat_x_assum`ms.MEM = _`kall_tac
  \\ simp[LEFT_FORALL_IMP_THM]
  \\ impl_tac
  >- (
    simp[Abbr`ms1`, APPLY_UPDATE_THM]
    \\ fs[ag32_ffi_rel_def, ag32_cline_implemented_def]
    \\ EVAL_TAC \\ fs [markerTheory.Abbrev_def])
  \\ strip_tac
  \\ `EL index ffi_names = "get_arg_length"`
  by (
    fs[GSYM find_index_INDEX_OF]
    \\ imp_res_tac find_index_is_MEM
    \\ imp_res_tac find_index_MEM
    \\ first_x_assum(qspec_then`0`mp_tac)
    \\ simp[] )
  \\ `ag32_ffi_interfer ffi_names md (index,bytes',ms) =
      ag32_ffi_interfer ffi_names md (index,bytes',ms1)`
  by (
    simp[ag32_ffi_interfer_def, ag32Theory.ag32_state_component_equality]
    \\ simp[Abbr`ms1`, APPLY_UPDATE_THM]
    \\ simp[FUN_EQ_THM, APPLY_UPDATE_THM] )
  \\ qspec_then`ms1`mp_tac (CONV_RULE(RESORT_FORALL_CONV(sort_vars["s"]))(GEN_ALL ag32_ffi_get_arg_length_code_thm))
  \\ fs[Abbr`ms1`, APPLY_UPDATE_THM]
  \\ fs[ffi_entrypoints_def, GSYM word_add_n2w]
  \\ disch_then(qspec_then`md`mp_tac)
  \\ `∃l0 l1. bytes = [l0; l1]`
  by ( fs[clFFITheory.ffi_get_arg_length_def, LENGTH_EQ_NUM_compute] )
  \\ disch_then(qspecl_then[`l1`,`l0`]mp_tac)
  >> impl_tac >- (
    conj_tac >- EVAL_TAC
    \\ fs[]
    \\ fs[clFFITheory.ffi_get_arg_length_def]
    \\ fs[ag32_ffi_rel_def]
    \\ fs[ag32_cline_implemented_def] \\ rveq
    \\ conj_tac
    >- (
      simp[Abbr`md`]
      \\ EVAL_TAC
      \\ simp[]
      \\ fs[LEFT_ADD_DISTRIB, word_add_n2w, word_ls_n2w, word_lo_n2w, memory_size_def, EVAL``code_start_offset _``] )
    \\ conj_tac
    >- (
      simp[Abbr`md`]
      \\ EVAL_TAC
      \\ simp[]
      \\ fs[LEFT_ADD_DISTRIB, word_add_n2w, word_ls_n2w, word_lo_n2w, memory_size_def, EVAL``code_start_offset _``] )
    \\ qmatch_goalsub_abbrev_tac`get_mem_arg m`
    \\ last_assum(mp_then Any mp_tac (GEN_ALL bytes_in_memory_UPDATE_LT))
    \\ qmatch_asmsub_abbrev_tac`m = (kk =+ v) _`
    \\ disch_then(qspecl_then[`v`,`kk`]mp_tac)
    \\ impl_tac
    >- (
      simp[Abbr`kk`]
      \\ EVAL_TAC
      \\ simp[LENGTH_FLAT, MAP_MAP_o, o_DEF, ADD1]
      \\ simp[SUM_MAP_PLUS]
      \\ simp[Q.ISPEC`λx. 1n`SUM_MAP_K |> SIMP_RULE(srw_ss())[]]
      \\ fs[EVAL``cline_size``] )
    \\ simp[] \\ strip_tac
    \\ qmatch_goalsub_abbrev_tac`get_mem_arg _ _ i`
    \\ drule get_mem_arg_thm
    \\ disch_then(qspec_then`i`mp_tac)
    \\ impl_keep_tac
    >- (
      fs[MAP_MAP_o]
      \\ fs[EVERY_MEM, MEM_MAP, PULL_EXISTS]
      \\ gen_tac \\ strip_tac
      \\ Cases
      \\ fs[]
      \\ simp[DISJ_EQ_IMP]
      \\ strip_tac \\ rveq
      \\ fs[clFFITheory.validArg_def] )
    \\ simp[word_add_n2w]
    \\ disch_then kall_tac
    \\ fs[EL_MAP]
    \\ fs[EVERY_MEM, clFFITheory.validArg_def]
    \\ last_assum(qspec_then`EL i cls`mp_tac)
    \\ impl_tac >- metis_tac[MEM_EL]
    \\ simp[] \\ strip_tac
    \\ irule cline_in_memory_has_n_args
    \\ goal_assum(first_assum o mp_then Any mp_tac)
    \\ fs[Abbr`i`]
    \\ simp[EVERY_MEM])
  \\ pop_assum kall_tac
  \\ qmatch_asmsub_abbrev_tac`FUNPOW _ _ _ = ms1`
  \\ strip_tac
  \\ qexists_tac`k'+k`
  \\ simp[FUNPOW_ADD]
  \\ qpat_x_assum`ag32_ffi_interfer _ _ _ = _`(assume_tac o SYM)
  \\ simp[]
  \\ simp[ag32_ffi_interfer_def]
  \\ fs[ag32_ffi_rel_def]
  \\ `!i. i < LENGTH bytes' ==> ms.R 3w + n2w i IN md` by
   (Cases_on `ms.R 4w` \\ fs [] \\ rveq \\ fs []
    \\ drule read_bytearray_IMP_domain \\ fs [])
  \\ conj_tac >- (
    fs[]
    \\ conj_tac
    >- (
      simp[ag32_ffi_mem_update_def]
      \\ simp[get_output_io_event_def]
      \\ simp[get_ag32_io_event_def, APPLY_UPDATE_THM]
      \\ DEP_ONCE_REWRITE_TAC[SIMP_RULE(srw_ss())[]asm_write_bytearray_unchanged]
      \\ simp[APPLY_UPDATE_THM]
      \\ EVAL_TAC
      \\ fs[clFFITheory.ffi_get_arg_length_def]
      \\ rveq \\ fs[]
      \\ first_x_assum(qspec_then`0`mp_tac)
      \\ simp[Abbr`md`]
      \\ Cases_on`ms.R 3w`
      \\ EVAL_TAC
      \\ fs[word_add_n2w, word_ls_n2w, word_lo_n2w, LEFT_ADD_DISTRIB, FFI_codes_def])
    \\ `n2w heap_start_offset <=+ ms.R 3w`
    by (
      fs[clFFITheory.ffi_get_arg_length_def]
      \\ Cases_on`bytes` \\ fs[]
      \\ first_x_assum(qspec_then`0`mp_tac)
      \\ simp[Abbr`md`]
      \\ EVAL_TAC
      \\ Cases_on`ms.R 3w` \\ simp[word_add_n2w, word_ls_n2w, word_lo_n2w]
      \\ fs[FFI_codes_def] )
    \\ simp[ag32_ffi_mem_update_def]
    \\ conj_tac
    >- (
      irule ag32_stdin_implemented_ffi_get_arg_length
      \\ fs[PULL_EXISTS]
      \\ asm_exists_tac \\ fs[] )
    \\ irule ag32_cline_implemented_ffi_get_arg_length
    \\ fs[PULL_EXISTS]
    \\ asm_exists_tac \\ fs[])
  \\ gen_tac \\ strip_tac
  \\ simp[ag32_ffi_mem_update_def]
  \\ imp_res_tac read_bytearray_LENGTH \\ fs[ADD1]
  \\ qpat_x_assum`_ = w2n _`(assume_tac o SYM) \\ fs[]
  \\ irule asm_write_bytearray_unchanged_all_words
  \\ simp[APPLY_UPDATE_THM]
  \\ rw[]
  \\ qpat_x_assum`_ ∉ ag32_ffi_mem_domain`mp_tac
  \\ EVAL_TAC
QED

Theorem ag32_ffi_interfer_get_arg:
   ag32_ffi_rel ms ffi ∧
   (read_ffi_bytearrays (ag32_machine_config ffi_names lc ld) ms = (SOME conf, SOME bytes)) ∧
   (call_FFI ffi "get_arg" conf bytes = FFI_return ffi' bytes') ∧
   (INDEX_OF "get_arg" ffi_names = SOME index) ∧ ALL_DISTINCT ffi_names ∧
   w2n (ms.R 3w) + LENGTH bytes < dimword (:32) ∧
   LENGTH ffi_names ≤ LENGTH FFI_codes ∧
   code_start_offset (LENGTH ffi_names) + lc + 4 * ld < memory_size ∧
   (ms.PC = n2w (ffi_jumps_offset + (LENGTH ffi_names - (index+1)) * ffi_offset)) ∧
   (∀k. k < LENGTH (ag32_ffi_jumps ffi_names) ⇒
        (get_mem_word ms.MEM (n2w (ffi_jumps_offset + 4 * k))
         = EL k (ag32_ffi_jumps ffi_names))) ∧
   (∀k. k < LENGTH ag32_ffi_get_arg_code ⇒
        (get_mem_word ms.MEM (n2w (ffi_code_start_offset + THE (ALOOKUP ffi_entrypoints "get_arg") + 4 * k))
         = Encode (EL k ag32_ffi_get_arg_code)))
   ⇒
   ∃k.
     (ag32_ffi_interfer ffi_names
        (ag32_prog_addresses (LENGTH ffi_names) lc ld)
        (index,bytes',ms) = FUNPOW Next k ms) ∧
      ag32_ffi_rel (FUNPOW Next k ms) ffi' ∧
      ∀x. x ∉ ag32_ffi_mem_domain ∧
          x ∉ all_words (ms.R 3w) (LENGTH bytes) ⇒
          ((FUNPOW Next k ms).MEM x = ms.MEM x)
Proof
  strip_tac
  \\ fs[targetSemTheory.read_ffi_bytearrays_def]
  \\ fs[targetSemTheory.read_ffi_bytearray_def]
  \\ fs[EVAL``(ag32_machine_config a b c).ptr2_reg``]
  \\ fs[EVAL``(ag32_machine_config a b c).len2_reg``]
  \\ fs[EVAL``(ag32_machine_config a b c).ptr_reg``]
  \\ fs[EVAL``(ag32_machine_config a b c).len_reg``]
  \\ fs[EVAL``(ag32_machine_config a b c).target.get_reg``]
  \\ fs[EVAL``(ag32_machine_config a b c).target.get_byte``]
  \\ first_assum(mp_then Any mp_tac asmPropsTheory.read_bytearray_IMP_bytes_in_memory)
  \\ last_assum(mp_then Any mp_tac asmPropsTheory.read_bytearray_IMP_bytes_in_memory)
  \\ imp_res_tac read_bytearray_LENGTH \\ fs[]
  \\ qmatch_asmsub_abbrev_tac`_ ∈ md`
  \\ disch_then(qspecl_then[`ms.MEM`,`md`]mp_tac) \\ simp[]
  \\ impl_tac
  >- (
    imp_res_tac read_bytearray_IMP_mem_SOME
    \\ fs[IS_SOME_EXISTS] )
  \\ strip_tac
  \\ disch_then(qspecl_then[`ms.MEM`,`md`]mp_tac) \\ simp[]
  \\ impl_tac
  >- (
    imp_res_tac read_bytearray_IMP_mem_SOME
    \\ fs[IS_SOME_EXISTS] )
  \\ strip_tac
  \\ drule (GEN_ALL mk_jump_ag32_code_thm)
  \\ simp[]
  \\ disch_then drule \\ simp[]
  \\ simp[ffi_entrypoints_def]
  \\ impl_tac
  >- (
    gen_tac \\ strip_tac
    \\ qmatch_goalsub_abbrev_tac`ffi_offset * ix`
    \\ last_x_assum(qspec_then`ix * (ffi_offset DIV 4) + k`mp_tac)
    \\ impl_tac
    >- (
      simp[LENGTH_ag32_ffi_jumps,Abbr`ix`]
      \\ EVAL_TAC
      \\ fs[FFI_codes_def])
    \\ simp[LEFT_ADD_DISTRIB, GSYM word_add_n2w]
    \\ `4 * (ix * (ffi_offset DIV 4)) = ix * ffi_offset`
    by ( EVAL_TAC \\ simp[] )
    \\ pop_assum SUBST1_TAC
    \\ simp[]
    \\ disch_then kall_tac
    \\ simp[ag32_ffi_jumps_def]
    \\ rewrite_tac[GSYM APPEND_ASSOC]
    \\ DEP_REWRITE_TAC[EL_APPEND1]
    \\ simp[LENGTH_FLAT, MAP_MAP_o, o_DEF]
    \\ simp[Once mk_jump_ag32_code_def]
    \\ simp[Q.ISPEC`λx. 4n`SUM_MAP_K |> SIMP_RULE(srw_ss())[]]
    \\ conj_tac
    >- (
      EVAL_TAC
      \\ fs[FFI_codes_def,Abbr`ix`]
      \\ fs[GSYM find_index_INDEX_OF]
      \\ imp_res_tac find_index_LESS_LENGTH
      \\ fs[] )
    \\ simp[lab_to_targetTheory.ffi_offset_def]
    \\ irule EL_FLAT_MAP_mk_jump_ag32_code
    \\ simp[INDEX_OF_REVERSE])
  \\ strip_tac
  \\ qmatch_asmsub_abbrev_tac`_ = ms1`
  \\ `(ms.MEM = ms1.MEM) ∧
      (ms.R 1w = ms1.R 1w) ∧
      (ms.R 3w = ms1.R 3w)` by simp[Abbr`ms1`,APPLY_UPDATE_THM] \\ fs[]
  \\ drule (GEN_ALL ag32_ffi_get_arg_thm)
  \\ disch_then drule
  \\ qpat_x_assum`Abbrev(md = _)`mp_tac
  \\ CONV_TAC(LAND_CONV(SIMP_CONV(srw_ss()++LET_ss)[ag32_machine_config_def]))
  \\ strip_tac
  \\ disch_then (first_assum o mp_then Any mp_tac)
  \\ simp[]
  \\ qhdtm_x_assum`call_FFI`mp_tac
  \\ simp[ffiTheory.call_FFI_def]
  \\ `ffi.oracle = basis_ffi_oracle` by fs[ag32_ffi_rel_def]
  \\ simp[basis_ffiTheory.basis_ffi_oracle_def]
  \\ pairarg_tac \\ simp[]
  \\ simp[CaseEq"option",CaseEq"oracle_result",CaseEq"bool",CaseEq"ffi_result"]
  \\ strip_tac
  \\ var_eq_tac
  \\ var_eq_tac
  \\ var_eq_tac
  \\ disch_then(first_assum o mp_then Any mp_tac)
  \\ simp[]
  \\ qpat_x_assum`ms.R _ = _`kall_tac
  \\ qpat_x_assum`ms.R _ = _`kall_tac
  \\ qpat_x_assum`ms.MEM = _`kall_tac
  \\ simp[LEFT_FORALL_IMP_THM]
  \\ impl_tac
  >- (
    simp[Abbr`ms1`, APPLY_UPDATE_THM]
    \\ fs[ag32_ffi_rel_def, ag32_cline_implemented_def]
    \\ EVAL_TAC \\ fs [markerTheory.Abbrev_def])
  \\ strip_tac
  \\ `EL index ffi_names = "get_arg"`
  by (
    fs[GSYM find_index_INDEX_OF]
    \\ imp_res_tac find_index_is_MEM
    \\ imp_res_tac find_index_MEM
    \\ first_x_assum(qspec_then`0`mp_tac)
    \\ simp[] )
  \\ `ag32_ffi_interfer ffi_names md (index,bytes',ms) =
      ag32_ffi_interfer ffi_names md (index,bytes',ms1)`
  by (
    simp[ag32_ffi_interfer_def, ag32Theory.ag32_state_component_equality]
    \\ simp[Abbr`ms1`, APPLY_UPDATE_THM]
    \\ simp[FUN_EQ_THM, APPLY_UPDATE_THM] )
  \\ qspec_then`ms1`mp_tac (CONV_RULE(RESORT_FORALL_CONV(sort_vars["s"]))(GEN_ALL ag32_ffi_get_arg_code_thm))
  \\ fs[Abbr`ms1`, APPLY_UPDATE_THM]
  \\ fs[ffi_entrypoints_def, GSYM word_add_n2w]
  \\ disch_then(qspec_then`md`mp_tac)
  \\ `∃l0 l1 t. bytes = l0::l1::t`
  by ( fs[clFFITheory.ffi_get_arg_def]
       \\ Cases_on`bytes` \\ fs[]
       \\ Cases_on`t` \\ fs[])
  \\ disch_then(qspecl_then[`l1`,`l0`]mp_tac)
  >> impl_tac >- (
    conj_tac >- EVAL_TAC
    \\ fs[bytes_in_memory_def]
    \\ fs[clFFITheory.ffi_get_arg_def]
    \\ fs[ag32_ffi_rel_def]
    \\ fs[ag32_cline_implemented_def] \\ rveq
    \\ conj_tac
    >- (
      simp[Abbr`md`]
      \\ EVAL_TAC
      \\ simp[]
      \\ fs[LEFT_ADD_DISTRIB, word_add_n2w, word_ls_n2w, word_lo_n2w, memory_size_def, EVAL``code_start_offset _``] )
    \\ conj_tac
    >- (
      qmatch_goalsub_abbrev_tac`has_n_args m`
      \\ last_assum(mp_then Any mp_tac (GEN_ALL bytes_in_memory_UPDATE_LT))
      \\ qmatch_asmsub_abbrev_tac`m = (kk =+ v) _`
      \\ disch_then(qspecl_then[`v`,`kk`]mp_tac)
      \\ impl_tac
      >- (
        simp[Abbr`kk`]
        \\ EVAL_TAC
        \\ simp[LENGTH_FLAT, MAP_MAP_o, o_DEF, ADD1]
        \\ simp[SUM_MAP_PLUS]
        \\ simp[Q.ISPEC`λx. 1n`SUM_MAP_K |> SIMP_RULE(srw_ss())[]]
        \\ fs[EVAL``cline_size``] )
      \\ strip_tac
      \\ irule cline_in_memory_has_n_args \\ rfs[word_add_n2w]
      \\ goal_assum(first_assum o mp_then Any mp_tac)
      \\ fs[]
      \\ fs[EVERY_MEM, MEM_MAP, PULL_EXISTS, clFFITheory.validArg_def]
      \\ gen_tac \\ strip_tac \\ Cases
      \\ fs[DISJ_EQ_IMP]
      \\ strip_tac \\ rveq \\ fs[])
    \\ qmatch_goalsub_abbrev_tac`get_mem_arg m`
    \\ last_assum(mp_then Any mp_tac (GEN_ALL bytes_in_memory_UPDATE_LT))
    \\ qmatch_asmsub_abbrev_tac`m = (kk =+ v) _`
    \\ disch_then(qspecl_then[`v`,`kk`]mp_tac)
    \\ impl_tac
    >- (
      simp[Abbr`kk`]
      \\ EVAL_TAC
      \\ simp[LENGTH_FLAT, MAP_MAP_o, o_DEF, ADD1]
      \\ simp[SUM_MAP_PLUS]
      \\ simp[Q.ISPEC`λx. 1n`SUM_MAP_K |> SIMP_RULE(srw_ss())[]]
      \\ fs[EVAL``cline_size``] )
    \\ simp[] \\ strip_tac
    \\ qmatch_goalsub_abbrev_tac`0 < i`
    \\ reverse IF_CASES_TAC
    >- (
      simp[Abbr`kk`]
      \\ Cases_on`cls` \\ fs[]
      \\ fs[bytes_in_memory_def, bytes_in_memory_APPEND, SNOC_APPEND]
      \\ qexists_tac`strlen h`
      \\ fs[word_add_n2w]
      \\ fs[EVAL``cline_size``, EVAL``ffi_code_start_offset``, EVAL``startup_code_size``]
      \\ fs[EVAL``LENGTH ag32_ffi_get_arg_code``, EVAL``ag32_ffi_get_arg_entrypoint``]
      \\ qpat_x_assum`ms.R 3w ∈ md`mp_tac
      \\ simp[Abbr`md`]
      \\ EVAL_TAC
      \\ Cases_on`ms.R 3w` \\ fs[word_add_n2w, word_ls_n2w, word_lo_n2w, memory_size_def, EVAL``code_start_offset _``]
      \\ fs[FFI_codes_def, LEFT_ADD_DISTRIB]
      \\ rw[] \\ CCONTR_TAC \\ fs[] \\ rfs[] \\ fs[])
    \\ drule get_mem_arg_thm
    \\ disch_then(qspec_then`i-1`mp_tac)
    \\ impl_keep_tac
    >- (
      fs[MAP_MAP_o]
      \\ fs[EVERY_MEM, MEM_MAP, PULL_EXISTS]
      \\ gen_tac \\ strip_tac
      \\ Cases
      \\ fs[]
      \\ simp[DISJ_EQ_IMP]
      \\ strip_tac \\ rveq
      \\ fs[clFFITheory.validArg_def] )
    \\ simp[word_add_n2w]
    \\ disch_then kall_tac
    \\ simp[Abbr`kk`]
    \\ fs[EVAL``ffi_code_start_offset``, EVAL``startup_code_size``]
    \\ fs[EVAL``LENGTH ag32_ffi_get_arg_code``, EVAL``ag32_ffi_get_arg_entrypoint``]
    \\ qpat_x_assum`bytes_in_memory (n2w _) _ ms.MEM _`assume_tac
    \\ qexists_tac`strlen(EL i cls)` \\ simp[]
    \\ fs[MAP_TAKE, MAP_MAP_o, o_DEF]
    \\ fs[GSYM MAP_TAKE]
    \\ simp[CONJ_ASSOC]
    \\ reverse conj_tac
    >- (
      qpat_x_assum`ms.R 3w ∈ md`mp_tac
      \\ simp[Abbr`md`]
      \\ EVAL_TAC
      \\ Cases_on`ms.R 3w` \\ fs[word_add_n2w, word_ls_n2w, word_lo_n2w, memory_size_def, EVAL``code_start_offset _``]
      \\ fs[FFI_codes_def, LEFT_ADD_DISTRIB]
      \\ rw[] \\ CCONTR_TAC \\ fs[] \\ rfs[] \\ fs[])
    \\ pop_assum mp_tac
    \\ qpat_x_assum`_ ≤ cline_size`mp_tac
    \\ Q.ISPECL_THEN[`i`,`cls`](fn th => CONV_TAC(PATH_CONV"lrlrr"(ONCE_REWRITE_CONV[SYM th])))TAKE_DROP
    \\ fs[SUM_APPEND, cline_size_def, EVAL``ffi_code_start_offset``, EVAL``startup_code_size``]
    \\ fs[word_add_n2w]
    \\ strip_tac
    \\ Q.ISPECL_THEN[`i`,`cls`](fn th => CONV_TAC(PATH_CONV"lrllr"(ONCE_REWRITE_CONV[SYM th])))TAKE_DROP
    \\ simp[bytes_in_memory_APPEND]
    \\ simp[LENGTH_FLAT, MAP_MAP_o, o_DEF, ADD1, SUM_MAP_PLUS]
    \\ simp[Q.ISPEC`λx. 1n`SUM_MAP_K |> SIMP_RULE(srw_ss())[]]
    \\ fs[word_add_n2w]
    \\ strip_tac
    \\ fs[SNOC_APPEND, bytes_in_memory_APPEND]
    \\ fsrw_tac[ETA_ss][]
    \\ `SUM (MAP strlen (TAKE i cls)) + SUM (MAP strlen (DROP i cls)) = SUM (MAP strlen cls)`
    by (
      rewrite_tac[GSYM SUM_APPEND, GSYM MAP_APPEND]
      \\ AP_TERM_TAC \\ AP_TERM_TAC
      \\ simp[] )
    \\ fs[]
    \\ `strlen (EL i cls) ≤ SUM (MAP strlen (DROP i cls))`
    by (
      irule SUM_MAP_MEM_bound
      \\ simp[Once listTheory.MEM_DROP] )
    \\ reverse conj_tac
    >- (
      qpat_x_assum`ms.R 3w ∈ md`mp_tac
      \\ simp[Abbr`md`]
      \\ CONV_TAC(LAND_CONV EVAL)
      \\ Cases_on`ms.R 3w` \\ fs[word_add_n2w, word_ls_n2w, word_lo_n2w, memory_size_def, EVAL``code_start_offset _``])
    \\ qpat_x_assum`bytes_in_memory (n2w _) _ _ _`assume_tac
    \\ drule bytes_in_memory_EL
    \\ disch_then(qspec_then`strlen(EL i cls)`mp_tac)
    \\ simp[LENGTH_FLAT, MAP_MAP_o, o_DEF, ADD1, SUM_MAP_PLUS]
    \\ simp[Q.ISPEC`λx. 1n`SUM_MAP_K |> SIMP_RULE(srw_ss())[]]
    \\ fs[word_add_n2w]
    \\ strip_tac
    \\ DEP_ONCE_REWRITE_TAC[DROP_EL_CONS]
    \\ simp[EL_APPEND1, EL_APPEND2])
  \\ pop_assum kall_tac
  \\ qmatch_asmsub_abbrev_tac`FUNPOW _ _ _ = ms1`
  \\ strip_tac
  \\ qexists_tac`k'+k`
  \\ simp[FUNPOW_ADD]
  \\ qpat_x_assum`ag32_ffi_interfer _ _ _ = _`(assume_tac o SYM)
  \\ simp[]
  \\ simp[ag32_ffi_interfer_def]
  \\ fs[ag32_ffi_rel_def]
  \\ `!i. i < LENGTH bytes' ==> ms.R 3w + n2w i IN md` by
   (Cases_on `ms.R 4w` \\ fs [] \\ rveq \\ fs []
    \\ drule read_bytearray_IMP_domain \\ fs [])
  \\ conj_tac >- (
    fs[]
    \\ conj_tac
    >- (
      simp[ag32_ffi_mem_update_def]
      \\ simp[get_output_io_event_def]
      \\ simp[get_ag32_io_event_def, APPLY_UPDATE_THM]
      \\ DEP_ONCE_REWRITE_TAC[SIMP_RULE(srw_ss())[]asm_write_bytearray_unchanged]
      \\ simp[APPLY_UPDATE_THM]
      \\ EVAL_TAC
      \\ fs[clFFITheory.ffi_get_arg_def]
      \\ rveq \\ fs[]
      \\ first_x_assum(qspec_then`0`mp_tac)
      \\ simp[Abbr`md`]
      \\ Cases_on`ms.R 3w`
      \\ EVAL_TAC
      \\ fs[word_add_n2w, word_ls_n2w, word_lo_n2w, LEFT_ADD_DISTRIB, FFI_codes_def])
    \\ `n2w heap_start_offset <=+ ms.R 3w`
    by (
      fs[clFFITheory.ffi_get_arg_def]
      \\ Cases_on`bytes` \\ fs[]
      \\ first_x_assum(qspec_then`0`mp_tac)
      \\ simp[Abbr`md`]
      \\ EVAL_TAC
      \\ Cases_on`ms.R 3w` \\ simp[word_add_n2w, word_ls_n2w, word_lo_n2w]
      \\ fs[FFI_codes_def] )
    \\ simp[ag32_ffi_mem_update_def]
    \\ conj_tac
    >- (
      irule ag32_stdin_implemented_ffi_get_arg
      \\ fs[PULL_EXISTS]
      \\ asm_exists_tac \\ fs[] )
    \\ irule ag32_cline_implemented_ffi_get_arg
    \\ fs[PULL_EXISTS]
    \\ asm_exists_tac \\ fs[])
  \\ gen_tac \\ strip_tac
  \\ simp[ag32_ffi_mem_update_def]
  \\ imp_res_tac read_bytearray_LENGTH \\ fs[ADD1]
  \\ qpat_x_assum`_ = w2n _`(assume_tac o SYM) \\ fs[]
  \\ irule asm_write_bytearray_unchanged_all_words
  \\ simp[APPLY_UPDATE_THM]
  \\ rw[]
  \\ qpat_x_assum`_ ∉ ag32_ffi_mem_domain`mp_tac
  \\ EVAL_TAC
QED

Theorem ag32_ffi_interfer_:
   ag32_ffi_rel ms ffi ∧
   (read_ffi_bytearrays (ag32_machine_config ffi_names lc ld) ms = (SOME conf, SOME bytes)) ∧
   (call_FFI ffi "" conf bytes = FFI_return ffi' bytes') ∧
   (INDEX_OF "" ffi_names = SOME index) ∧ ALL_DISTINCT ffi_names ∧
   w2n (ms.R 3w) + LENGTH bytes < dimword (:32) ∧
   LENGTH ffi_names ≤ LENGTH FFI_codes ∧
   code_start_offset (LENGTH ffi_names) + lc + 4 * ld < memory_size ∧
   (ms.PC = n2w (ffi_jumps_offset + (LENGTH ffi_names - (index+1)) * ffi_offset)) ∧
   (∀k. k < LENGTH (ag32_ffi_jumps ffi_names) ⇒
        (get_mem_word ms.MEM (n2w (ffi_jumps_offset + 4 * k))
         = EL k (ag32_ffi_jumps ffi_names))) ∧
   (∀k. k < LENGTH ag32_ffi__code ⇒
        (get_mem_word ms.MEM (n2w (ffi_code_start_offset + THE (ALOOKUP ffi_entrypoints "") + 4 * k))
         = Encode (EL k ag32_ffi__code)))
   ⇒
   ∃k.
     (ag32_ffi_interfer ffi_names
        (ag32_prog_addresses (LENGTH ffi_names) lc ld)
        (index,bytes',ms) = FUNPOW Next k ms) ∧
      ag32_ffi_rel (FUNPOW Next k ms) ffi' ∧
      ∀x. x ∉ ag32_ffi_mem_domain ∧
          x ∉ all_words (ms.R 3w) (LENGTH bytes) ⇒
          ((FUNPOW Next k ms).MEM x = ms.MEM x)
Proof
  strip_tac
  \\ fs[targetSemTheory.read_ffi_bytearrays_def]
  \\ fs[targetSemTheory.read_ffi_bytearray_def]
  \\ fs[EVAL``(ag32_machine_config a b c).ptr2_reg``]
  \\ fs[EVAL``(ag32_machine_config a b c).len2_reg``]
  \\ fs[EVAL``(ag32_machine_config a b c).ptr_reg``]
  \\ fs[EVAL``(ag32_machine_config a b c).len_reg``]
  \\ fs[EVAL``(ag32_machine_config a b c).target.get_reg``]
  \\ fs[EVAL``(ag32_machine_config a b c).target.get_byte``]
  \\ first_assum(mp_then Any mp_tac asmPropsTheory.read_bytearray_IMP_bytes_in_memory)
  \\ last_assum(mp_then Any mp_tac asmPropsTheory.read_bytearray_IMP_bytes_in_memory)
  \\ imp_res_tac read_bytearray_LENGTH \\ fs[]
  \\ qmatch_asmsub_abbrev_tac`_ ∈ md`
  \\ disch_then(qspecl_then[`ms.MEM`,`md`]mp_tac) \\ simp[]
  \\ impl_tac
  >- (
    imp_res_tac read_bytearray_IMP_mem_SOME
    \\ fs[IS_SOME_EXISTS] )
  \\ strip_tac
  \\ disch_then(qspecl_then[`ms.MEM`,`md`]mp_tac) \\ simp[]
  \\ impl_tac
  >- (
    imp_res_tac read_bytearray_IMP_mem_SOME
    \\ fs[IS_SOME_EXISTS] )
  \\ strip_tac
  \\ drule (GEN_ALL mk_jump_ag32_code_thm)
  \\ simp[]
  \\ disch_then drule \\ simp[]
  \\ simp[ffi_entrypoints_def]
  \\ impl_tac
  >- (
    gen_tac \\ strip_tac
    \\ qmatch_goalsub_abbrev_tac`ffi_offset * ix`
    \\ last_x_assum(qspec_then`ix * (ffi_offset DIV 4) + k`mp_tac)
    \\ impl_tac
    >- (
      simp[LENGTH_ag32_ffi_jumps,Abbr`ix`]
      \\ EVAL_TAC
      \\ fs[FFI_codes_def])
    \\ simp[LEFT_ADD_DISTRIB, GSYM word_add_n2w]
    \\ `4 * (ix * (ffi_offset DIV 4)) = ix * ffi_offset`
    by ( EVAL_TAC \\ simp[] )
    \\ pop_assum SUBST1_TAC
    \\ simp[]
    \\ disch_then kall_tac
    \\ simp[ag32_ffi_jumps_def]
    \\ rewrite_tac[GSYM APPEND_ASSOC]
    \\ DEP_REWRITE_TAC[EL_APPEND1]
    \\ simp[LENGTH_FLAT, MAP_MAP_o, o_DEF]
    \\ simp[Once mk_jump_ag32_code_def]
    \\ simp[Q.ISPEC`λx. 4n`SUM_MAP_K |> SIMP_RULE(srw_ss())[]]
    \\ conj_tac
    >- (
      EVAL_TAC
      \\ fs[FFI_codes_def,Abbr`ix`]
      \\ fs[GSYM find_index_INDEX_OF]
      \\ imp_res_tac find_index_LESS_LENGTH
      \\ fs[] )
    \\ simp[EVAL``ffi_offset``]
    \\ irule EL_FLAT_MAP_mk_jump_ag32_code
    \\ simp[INDEX_OF_REVERSE])
  \\ strip_tac
  \\ qmatch_asmsub_abbrev_tac`_ = ms1`
  \\ `(ms.MEM = ms1.MEM) ∧
      (ms.R 1w = ms1.R 1w) ∧
      (ms.R 3w = ms1.R 3w)` by simp[Abbr`ms1`,APPLY_UPDATE_THM] \\ fs[]
  \\ drule (GEN_ALL ag32_ffi__thm)
  \\ disch_then drule
  \\ qpat_x_assum`Abbrev(md = _)`mp_tac
  \\ CONV_TAC(LAND_CONV(SIMP_CONV(srw_ss()++LET_ss)[ag32_machine_config_def]))
  \\ strip_tac
  \\ disch_then (first_assum o mp_then Any mp_tac)
  \\ simp[]
  \\ qhdtm_x_assum`call_FFI`mp_tac
  \\ simp[ffiTheory.call_FFI_def]
  \\ `ffi.oracle = basis_ffi_oracle` by fs[ag32_ffi_rel_def]
  \\ simp[basis_ffiTheory.basis_ffi_oracle_def]
  \\ strip_tac
  \\ var_eq_tac
  \\ var_eq_tac
  \\ impl_tac >-(
    simp[Abbr`ms1`,APPLY_UPDATE_THM]>>
    EVAL_TAC)
  \\ strip_tac
  \\ imp_res_tac INDEX_OF_IMP_EL
  \\ `ag32_ffi_interfer ffi_names md (index,bytes',ms) =
      ag32_ffi_interfer ffi_names md (index,bytes',ms1)`
  by (
    simp[ag32_ffi_interfer_def, ag32Theory.ag32_state_component_equality] >>
    simp[Abbr`ms1`,FUN_EQ_THM, APPLY_UPDATE_THM])>>
  qspec_then`ms1`mp_tac (CONV_RULE(RESORT_FORALL_CONV(sort_vars["s"]))(GEN_ALL ag32_ffi__code_thm))
  \\ fs[Abbr`ms1`, APPLY_UPDATE_THM]
  \\ fs[ffi_entrypoints_def, GSYM word_add_n2w]
  \\ qmatch_asmsub_abbrev_tac`FUNPOW _ _ _ = ms1`
  \\ impl_tac >- EVAL_TAC
  \\ strip_tac
  \\ qexists_tac`k'+k`
  \\ simp[FUNPOW_ADD]
  \\ qpat_x_assum`ag32_ffi_interfer _ _ _ = _`(assume_tac o SYM)
  \\ simp[]
  \\ simp[ag32_ffi_interfer_def]
  \\ fs[ag32_ffi_rel_def]
  \\ `EL index ffi_names = ""`
  by (
    fs[GSYM find_index_INDEX_OF]
    \\ imp_res_tac find_index_is_MEM
    \\ imp_res_tac find_index_MEM
    \\ first_x_assum(qspec_then`0`mp_tac)
    \\ simp[] )
  \\ `!i. i < LENGTH bytes ==> ms.R 3w + n2w i IN md` by
   (Cases_on `ms.R 4w` \\ fs [] \\ rveq \\ fs []
    \\ drule read_bytearray_IMP_domain \\ fs [])
  \\ simp[ag32_ffi_mem_update_def]
  \\ conj_tac >- (
    simp[Abbr`ms1`,ag32Theory.ag32_state_component_equality]>>
    simp[APPLY_UPDATE_THM,FUN_EQ_THM])
  \\ simp[Abbr`ms1`]
QED

Theorem SUBSET_ffi_names_IMP_LENGTH_LESS_EQ:
   set ffi_names ⊆ set (MAP FST ffi_exitpcs) ∧ ALL_DISTINCT ffi_names
   ⇒ LENGTH ffi_names ≤ LENGTH FFI_codes
Proof
  rw[ffi_exitpcs_def, FFI_codes_def]
  \\ drule ALL_DISTINCT_CARD_LIST_TO_SET
  \\ disch_then(SUBST1_TAC o SYM)
  \\ qmatch_asmsub_abbrev_tac`_ ⊆ t`
  \\ Q.ISPEC_THEN`t`mp_tac CARD_SUBSET
  \\ impl_tac >- simp[Abbr`t`]
  \\ disch_then drule
  \\ simp[Abbr`t`]
QED

Theorem ag32_good_init_state:
   SUM (MAP strlen cl) + LENGTH cl ≤ cline_size ∧
   LENGTH inp ≤ stdin_size ∧
   set ffi_names ⊆ set (MAP FST ffi_exitpcs) ∧ ALL_DISTINCT ffi_names ∧
   code_start_offset (LENGTH ffi_names) + LENGTH code + 4 * LENGTH data < memory_size ∧
   byte_aligned ((n2w (LENGTH code)):word32) ∧
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
     cc_regs
Proof
  strip_tac
  \\ imp_res_tac SUBSET_ffi_names_IMP_LENGTH_LESS_EQ
  \\ simp[targetSemTheory.good_init_state_def,RIGHT_EXISTS_AND_THM]
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
    \\ simp[targetSemTheory.target_configured_def]
    \\ impl_tac >- EVAL_TAC
    \\ strip_tac \\ fs[])
  \\ conj_tac >- (
    fs[asmPropsTheory.target_state_rel_def, ag32_machine_config_def] )
  \\ qabbrev_tac`num_ffis = LENGTH ffi_names`
  \\ `(n2w (code_start_offset num_ffis) && 3w) = 0w:word32` by (
    EVAL_TAC
    \\ fs[alignmentTheory.aligned_bitwise_and, alignmentTheory.byte_aligned_def, Abbr`num_ffis`, FFI_codes_def]
    \\ qpat_x_assum`_ ≤ _`mp_tac
    \\ simp[LESS_OR_EQ]
    \\ CONV_TAC(LAND_CONV(SIMP_CONV(srw_ss())[NUMERAL_LESS_THM]))
    \\ rpt(pop_assum kall_tac)
    \\ strip_tac \\ simp[])
  \\ `(n2w (code_start_offset num_ffis) && 1w) = 0w:word32` by (
    EVAL_TAC
    \\ fs[alignmentTheory.aligned_bitwise_and, alignmentTheory.byte_aligned_def, Abbr`num_ffis`, FFI_codes_def]
    \\ qpat_x_assum`_ ≤ _`mp_tac
    \\ simp[LESS_OR_EQ]
    \\ CONV_TAC(LAND_CONV(SIMP_CONV(srw_ss())[NUMERAL_LESS_THM]))
    \\ rpt(pop_assum kall_tac)
    \\ strip_tac \\ simp[])
  \\ conj_tac >- (
    rewrite_tac[targetSemTheory.start_pc_ok_def]
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
    \\ qpat_x_assum`(_ && 3w) = _`mp_tac \\ fs[]
    \\ simp[ag32_init_asm_state_def] )
  \\ conj_tac >- (
    rw[asmPropsTheory.interference_ok_def]
    \\ simp[EVAL``(ag32_machine_config _ _ _).target``]
    \\ simp[EVAL``(ag32_machine_config _ _ _).next_interfer``] )
  \\ simp[LEFT_EXISTS_AND_THM]
  \\ conj_tac >- (
    simp[targetSemTheory.ffi_interfer_ok_def]
    \\ simp[ag32_machine_config_def]
    \\ simp[lab_to_targetTheory.ffi_offset_def,heap_size_def]
    \\ simp[EVAL``ag32_target.config``,targetSemTheory.get_reg_value_def]
    \\ simp[ag32_ffi_interfer_def]
    \\ simp[LENGTH_ag32_ffi_code]
    \\ qexists_tac`λk i n. if n = 0 then OPTION_MAP n2w (ALOOKUP ffi_exitpcs i)
                           else if i = "" then if n = 5 then SOME 0w else NONE
                           else if n < 9 then SOME 0w else NONE`
    \\ rpt gen_tac
    \\ Cases_on`EL index ffi_names = ""`
    \\ srw_tac[ETA_ss][]
    \\ fs[asmPropsTheory.target_state_rel_def]
    \\ fs[ag32_targetTheory.ag32_target_def]
    \\ fs[ag32_targetTheory.ag32_ok_def]
    \\ fs[ag32_targetTheory.ag32_config_def]
    >- (
      fs[ffiTheory.call_FFI_def]
      \\ rveq
      \\ reverse conj_tac
      >- (
        rw[]
        \\ rw[APPLY_UPDATE_THM, targetSemTheory.get_reg_value_def, EVAL``ALOOKUP ffi_exitpcs ""``] )
      \\ rw[]
      \\ irule EQ_SYM
      \\ irule asm_write_bytearray_id
      \\ gen_tac \\ strip_tac
      \\ irule bytes_in_memory_EL
      \\ simp[]
      \\ qexists_tac`all_words (t1.regs 3) (LENGTH bytes2)`
      \\ irule asmPropsTheory.read_bytearray_IMP_bytes_in_memory
      \\ fs[targetSemTheory.read_ffi_bytearrays_def]
      \\ fs[targetSemTheory.read_ffi_bytearray_def]
      \\ imp_res_tac read_bytearray_LENGTH \\ fs[]
      \\ goal_assum(first_assum o mp_then Any mp_tac)
      \\ rw[]
      \\ drule read_bytearray_IMP_mem_SOME
      \\ simp[]
      \\ disch_then drule
      \\ simp[IS_SOME_EXISTS] )
    \\ `IS_SOME(ALOOKUP ffi_exitpcs (EL index ffi_names))`
    by (
      simp[data_to_word_gcProofTheory.IS_SOME_ALOOKUP_EQ]
      \\ fs[SUBSET_DEF]
      \\ first_x_assum irule
      \\ simp[MEM_EL]
      \\ asm_exists_tac \\ simp[] )
    \\ reverse conj_tac
    >- (
      simp[APPLY_UPDATE_THM]
      \\ rpt strip_tac
      \\ fs[IS_SOME_EXISTS]
      \\ rpt(IF_CASES_TAC \\ simp[targetSemTheory.get_reg_value_def]))
    \\ rw[]
    \\ rfs[ffiTheory.call_FFI_def]
    \\ `st.oracle = (basis_ffi cl fs).oracle` by metis_tac[evaluatePropsTheory.RTC_call_FFI_rel_consts]
    \\ fs[basis_ffiTheory.basis_ffi_def]
    \\ `EL index ffi_names ∈ set(MAP FST FFI_codes)` by (
      fs[SUBSET_DEF]
      \\ fs[FFI_codes_def, ffi_exitpcs_def]
      \\ fs[IS_SOME_EXISTS]
      \\ fs[CaseEq"bool"]
      \\ rfs[])
    \\ qmatch_asmsub_abbrev_tac`MEM nm (MAP _ _)`
    \\ qpat_x_assum`MEM nm _`mp_tac
    \\ simp[Once FFI_codes_def]
    \\ strip_tac \\ rveq \\ fs[]
    \\ qmatch_asmsub_abbrev_tac`oracle_result_CASE r`
    \\ pop_assum mp_tac
    \\ simp[basis_ffiTheory.basis_ffi_oracle_def]
    \\ strip_tac \\ fs[Abbr`r`]
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
      \\ qpat_x_assum` _ < memory_size`mp_tac
      \\ EVAL_TAC \\ simp[])
    \\ TRY (
      CHANGED_TAC(fs[fsFFITheory.ffi_read_def])
      \\ fs[CaseEq"list"] \\ rveq
      \\ PURE_TOP_CASE_TAC \\ fs[]
      \\ PURE_TOP_CASE_TAC \\ fs[]
      \\ PURE_TOP_CASE_TAC \\ fs[]
      \\ reverse IF_CASES_TAC >- rw[]
      \\ rw[]
      \\ qmatch_goalsub_abbrev_tac`set_mem_word x y m a`
      \\ qpat_x_assum`m a = _`(SUBST1_TAC o SYM)
      \\ irule set_mem_word_neq
      \\ qpat_x_assum`_ ∈ _.mem_domain`mp_tac
      \\ qpat_x_assum`_ = _.mem_domain`(mp_tac o SYM)
      \\ simp[ag32_prog_addresses_def, Abbr`x`]
      \\ strip_tac
      \\ qpat_x_assum`_ < memory_size`mp_tac
      \\ EVAL_TAC
      \\ Cases_on`a` \\ fs[word_ls_n2w, word_lo_n2w, word_add_n2w]
      \\ NO_TAC)
    \\ reverse IF_CASES_TAC
    >- (
      rw[APPLY_UPDATE_THM]
      \\ qpat_x_assum`_ ∈ _.mem_domain`mp_tac
      \\ qpat_x_assum`_ = _.mem_domain`(assume_tac o SYM)
      \\ simp[ag32_prog_addresses_def]
      \\ qpat_x_assum`_ < memory_size`mp_tac
      \\ EVAL_TAC \\ simp[])
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
    \\ qpat_x_assum`_ < memory_size`mp_tac
    \\ CONV_TAC(LAND_CONV EVAL)
    \\ Cases_on`a` \\ fs[word_ls_n2w, word_lo_n2w, word_add_n2w]
    \\ rw[MIN_DEF])
  \\ conj_tac >- (
    rw[targetSemTheory.ccache_interfer_ok_def, ag32_machine_config_def,
       lab_to_targetTheory.ffi_offset_def, ag32_ccache_interfer_def,
       heap_size_def, EVAL``ag32_target.config``]
    \\ qmatch_goalsub_abbrev_tac`0w =+ v0`
    \\ qexists_tac`λk n. if n = 0 then SOME v0 else NONE`
    \\ EVAL_TAC \\ rw[]
    \\ IF_CASES_TAC \\ simp[targetSemTheory.get_reg_value_def] )
  \\ conj_asm1_tac >- (
    simp[targetSemTheory.code_loaded_def]
    \\ fs[asmPropsTheory.target_state_rel_def]
    \\ simp[SIMP_CONV (srw_ss()) [ag32_machine_config_def]``(ag32_machine_config _ _ _).target``]
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
    \\ qpat_x_assum`_ < memory_size`mp_tac
    \\ EVAL_TAC \\ simp[] \\ strip_tac
    \\ Cases \\ fs[word_lo_n2w, word_ls_n2w, word_add_n2w])
  \\ conj_tac >- (
    imp_res_tac asmPropsTheory.RTC_asm_step_consts
    \\ fs[heap_size_def]
    \\ qpat_x_assum`_ < memory_size`mp_tac
    \\ EVAL_TAC
    \\ simp[SUBSET_DEF]
    \\ strip_tac
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
    \\ simp[heap_size_def]
    \\ conj_asm2_tac
    >- (
      simp[GSYM word_add_n2w]
      \\ qmatch_goalsub_abbrev_tac`z + _`
      \\ Q.ISPECL_THEN[`z`,`LENGTH data`]mp_tac(Q.GENL[`a`,`i`]backendProofTheory.byte_aligned_mult)
      \\ impl_tac >- EVAL_TAC
      \\ simp[bytes_in_word_def, word_add_n2w, word_mul_n2w]
      \\ fs[word_add_n2w] )
    \\ simp[GSYM word_add_n2w]
    \\ irule byte_aligned_add
    \\ simp[byte_aligned_code_start_offset])
  \\ conj_tac >- (
    simp[EVAL``(ag32_machine_config _ _ _).target.config``]
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
      \\ simp[GSYM addressTheory.ALIGNED_eq_aligned,addressTheory.ALIGNED_n2w] )
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
  \\ fs[memory_size_def]
QED

(* TODO more things can be pulled out of here *)
Theorem ag32_installed:
   SUM (MAP strlen cl) + LENGTH cl ≤ cline_size ∧
   LENGTH inp ≤ stdin_size ∧
   set ffi_names ⊆ set (MAP FST ffi_exitpcs) ∧ ALL_DISTINCT ffi_names ∧
   code_start_offset (LENGTH ffi_names) + LENGTH code + 4 * LENGTH data < memory_size ∧
   byte_aligned ((n2w (LENGTH code)):word32) ∧
   is_ag32_init_state (init_memory code data ffi_names (cl,inp)) ms0 ∧
   target_state_rel ag32_target
     (init_asm_state code data ffi_names (cl,inp))
     (FUNPOW Next startup_clock ms0) ∧
   (∀x.
     x ∉ ag32_startup_addresses ⇒
       ((FUNPOW Next startup_clock ms0).MEM x = ms0.MEM x))
   ⇒
   installed code 0 data 0 (SOME ffi_names) (basis_ffi cl fs)
     (heap_regs ag32_backend_config.stack_conf.reg_names)
     (ag32_machine_config ffi_names (LENGTH code) (LENGTH data))
     (FUNPOW Next startup_clock ms0)
Proof
  disch_then assume_tac
  \\ CONV_TAC(PATH_CONV"llr"EVAL)
  \\ simp[targetSemTheory.installed_def]
  \\ simp[word_list_exists_def, set_sepTheory.SEP_CLAUSES, word_list_def]
  \\ simp[EVAL``(ag32_machine_config _ _ _).target.get_pc``]
  \\ strip_assume_tac(UNDISCH ag32_good_init_state)
  \\ last_x_assum strip_assume_tac
  \\ drule (GEN_ALL init_asm_state_RTC_asm_step)
  \\ disch_then drule
  \\ imp_res_tac SUBSET_ffi_names_IMP_LENGTH_LESS_EQ
  \\ disch_then drule
  \\ disch_then drule
  \\ strip_tac
  \\ qmatch_asmsub_abbrev_tac`good_init_state _ _ _ _ _ t`
  \\ qexists_tac`t` \\ simp[Abbr`t`]
  \\ asm_exists_tac \\ fs[]
  \\ qhdtm_x_assum`good_init_state` mp_tac
  \\ rewrite_tac[targetSemTheory.good_init_state_def]
  \\ disch_then(assume_tac o el 1 o CONJUNCTS)
  \\ conj_tac >- EVAL_TAC
  \\ conj_tac >- EVAL_TAC
  \\ conj_tac >- (
    rewrite_tac[GSYM word_add_n2w]
    \\ irule byte_aligned_add
    \\ simp[byte_aligned_code_start_offset] )
  \\ conj_tac >- EVAL_TAC
  \\ conj_tac >- EVAL_TAC
  \\ conj_tac
  >- (
    simp[IN_DISJOINT]
    \\ qpat_x_assum`_ < memory_size`mp_tac
    \\ EVAL_TAC
    \\ fs[FFI_codes_def]
    \\ strip_tac
    \\ Cases
    \\ fs[word_add_n2w,word_ls_n2w,word_lo_n2w] )
  \\ conj_tac >- fs[word_add_n2w, bytes_in_word_def, word_mul_n2w]
  \\ conj_tac >- fs[word_add_n2w, bytes_in_word_def, word_mul_n2w]
  \\ conj_tac >- (
    fs[asmPropsTheory.target_state_rel_def, ag32_machine_config_def,
       ag32_targetTheory.ag32_target_def]
    \\ simp[bytes_in_word_def, GSYM word_add_n2w, GSYM word_mul_n2w] )
  \\ conj_tac >- (
    fs[asmPropsTheory.target_state_rel_def, ag32_machine_config_def,
       ag32_targetTheory.ag32_target_def]
    \\ simp[bytes_in_word_def, GSYM word_add_n2w, GSYM word_mul_n2w] )
  \\ CONV_TAC (RAND_CONV EVAL THENC SIMP_CONV std_ss [])
  \\ irule IMP_word_list
  \\ conj_tac >- fs[bytes_in_word_def, memory_size_def]
  \\ conj_tac >- fs[]
  \\ simp[EXTENSION,FORALL_PROD,set_sepTheory.IN_fun2set, bytes_in_word_def]
  \\ qx_genl_tac[`w`,`a`]
  \\ qmatch_goalsub_abbrev_tac`n2w low <=+ w`
  \\ qmatch_goalsub_abbrev_tac`w <+ n2w hi`
  (* TODO try to break this part out *)
  \\ reverse (rw [EQ_IMP_THM])
  \\ fs [word_mul_n2w, word_add_n2w, word_lo_n2w, word_ls_n2w,
         memory_size_def, EL_MAP]
  >- fs [Abbr`hi`]
  >- fs [Abbr`hi`]
  >-
   (simp [IN_DEF]
    \\ simp [GSYM word_add_n2w]
    \\ irule byte_aligned_add
    \\ conj_tac
    >-
     (fs [Abbr`low`]
      \\ simp [GSYM word_add_n2w]
      \\ irule byte_aligned_add
      \\ simp [byte_aligned_code_start_offset])
    \\ simp [alignmentTheory.byte_aligned_def, GSYM word_mul_n2w,
             GSYM addressTheory.ALIGNED_eq_aligned]
    \\ qspecl_then [`0w`, `n2w k`] mp_tac addressTheory.ALIGNED_MULT
    \\ simp [EVAL ``ALIGNED 0w``])
  \\ `byte_aligned (n2w (code_start_offset (LENGTH ffi_names)) : word32)`
      by metis_tac [byte_aligned_code_start_offset]
  >-
   (first_assum (qspec_then `4 * k + 0` mp_tac)
    \\ first_assum (qspec_then `4 * k + 1` mp_tac)
    \\ first_assum (qspec_then `4 * k + 2` mp_tac)
    \\ first_x_assum (qspec_then `4 * k + 3` mp_tac)
    \\ simp []
    \\ ntac 4 (disch_then kall_tac)
    \\ qmatch_goalsub_abbrev_tac `word_of_bytes _ _ ls`
    \\ `low MOD 4 = 0`
      by (fs [Abbr `low`, alignmentTheory.byte_aligned_def,
              GSYM addressTheory.ALIGNED_eq_aligned, addressTheory.ALIGNED_n2w,
              MOD_EQ_0_DIVISOR, GSYM LEFT_ADD_DISTRIB])
    \\ `4 * (low DIV 4) = low` by fs [MULT_EQ_DIV]
    \\ `ls = GENLIST (λi.
          init_memory code data ffi_names (cl,inp)
            (n2w (4 * (k + (low DIV 4)) + i))) 4`
      by simp [Abbr `ls`, LEFT_ADD_DISTRIB]
    \\ qpat_x_assum`Abbrev(ls = _)`kall_tac
    \\ pop_assum SUBST_ALL_TAC
    \\ simp [GSYM word_add_n2w]
    \\ irule init_memory_data
    \\ fs [Abbr `hi`, memory_size_def, Abbr `low`])
  \\ Cases_on `w` \\ fs [word_ls_n2w, word_lo_n2w] \\ rfs [] \\ rw []
  \\ qmatch_asmsub_rename_tac `_ <= q`
  \\ qmatch_asmsub_abbrev_tac `l ≤ q`
  \\ qpat_x_assum `l ≤ q`mp_tac
  \\ simp [LESS_EQ_EXISTS] \\ strip_tac
  \\ `∃d. p = 4 * d`
    by (fs [IN_DEF, alignmentTheory.byte_aligned_def,
            GSYM addressTheory.ALIGNED_eq_aligned,
            addressTheory.ALIGNED_n2w]
        \\ fs [MOD_EQ_0_DIVISOR] \\ rfs []
        \\ fs [Abbr `l`] \\ rveq
        \\ qmatch_asmsub_abbrev_tac `p + m = 4 * D`
        \\ qexists_tac`(D - m DIV 4)`
        \\ simp[Abbr `m`, Abbr `D`, Abbr `low`]
        \\ intLib.ARITH_TAC)
  \\ qexists_tac `d`
  \\ reverse conj_tac
  >- (unabbrev_all_tac \\ rfs [])
  \\ conj_tac
  >- (unabbrev_all_tac \\ fs [])
  \\ `l = low ` by (unabbrev_all_tac \\ rfs [])
  \\ pop_assum SUBST_ALL_TAC
  \\ first_assum (qspec_then `4 * d + 0` mp_tac)
  \\ first_assum (qspec_then `4 * d + 1` mp_tac)
  \\ first_assum (qspec_then `4 * d + 2` mp_tac)
  \\ first_x_assum (qspec_then `4 * d + 3` mp_tac)
  \\ impl_keep_tac >- (unabbrev_all_tac \\ rfs []) \\ fs []
  \\ simp [word_add_n2w]
  \\ ntac 4 (disch_then kall_tac)
  \\ DEP_REWRITE_TAC [EL_MAP]
  \\ conj_tac >- (unabbrev_all_tac \\ fs [])
  \\ fs []
  \\ qmatch_goalsub_abbrev_tac `word_of_bytes _ _ ls`
  \\ `low MOD 4 = 0`
    by (fs [Abbr `low`, alignmentTheory.byte_aligned_def,
            GSYM addressTheory.ALIGNED_eq_aligned, addressTheory.ALIGNED_n2w,
            MOD_EQ_0_DIVISOR, GSYM LEFT_ADD_DISTRIB])
  \\ `4 * (low DIV 4) = low` by fs [MULT_EQ_DIV]
  \\ `ls = GENLIST (λi.
        init_memory code data ffi_names (cl,inp)
          (n2w (4 * (d + (low DIV 4)) + i))) 4`
    by simp [LEFT_ADD_DISTRIB]
  \\ qpat_x_assum`Abbrev(ls = _)`kall_tac
  \\ pop_assum SUBST_ALL_TAC
  \\ simp [GSYM word_add_n2w]
  \\ irule init_memory_data
  \\ fs [Abbr `hi`, memory_size_def, Abbr `low`]
QED

Theorem ag32_halted:
   ∀ms.
    SUM (MAP strlen cl) + LENGTH cl ≤ cline_size ∧
    LENGTH inp ≤ stdin_size ∧
    LENGTH ffi_names ≤ LENGTH FFI_codes ∧
    (mc = ag32_machine_config ffi_names (LENGTH code) (LENGTH data)) ∧
    (ms.PC = mc.halt_pc) ∧
    (∀x. mc.halt_pc <=+ x ∧ x <+ mc.halt_pc + 16w ⇒
         (mc.target.get_byte ms x = (init_memory code data ffi_names (cl,inp)) x)) ⇒
    ∀k. ((FUNPOW Next k ms).io_events = ms.io_events) ∧
        ((FUNPOW Next k ms).PC = ms.PC) ∧
        ((FUNPOW Next k ms).MEM = ms.MEM) ∧
        (∀w. w ≠ 0w ⇒ ((FUNPOW Next k ms).R w = ms.R w))
Proof
  gen_tac \\ strip_tac \\ rveq
  \\ Induct >- rw[]
  \\ simp[FUNPOW_SUC]
  \\ qmatch_goalsub_abbrev_tac`ms1.io_events`
  \\ pop_assum mp_tac
  \\ simp[ag32Theory.Next_def]
  \\ qmatch_goalsub_abbrev_tac`pc' + 2w`
  \\ qmatch_asmsub_abbrev_tac`_.PC = pc`
  \\ `byte_aligned pc`
  by (
    simp[Abbr`pc`]
    \\ simp[ag32_machine_config_def]
    \\ simp[lab_to_targetTheory.ffi_offset_def, GSYM word_add_n2w]
    \\ irule byte_aligned_add
    \\ conj_tac >- EVAL_TAC
    \\ simp[alignmentTheory.byte_aligned_def, GSYM addressTheory.ALIGNED_eq_aligned, addressTheory.ALIGNED_n2w]
    \\ EVAL_TAC )
  \\ `pc = pc'`
  by (
    pop_assum mp_tac
    \\ simp[alignmentTheory.byte_aligned_def]
    \\ unabbrev_all_tac
    \\ simp[alignmentTheory.aligned_extract]
    \\ blastLib.BBLAST_TAC )
  \\ qpat_x_assum`Abbrev(pc' = _)` kall_tac
  \\ pop_assum (SUBST_ALL_TAC o SYM)
  \\ fs[Abbr`pc`]
  \\ first_assum(qspec_then`ms.PC`mp_tac)
  \\ impl_tac >- (
    fs[ag32_machine_config_def, FFI_codes_def]
    \\ EVAL_TAC \\ fs[] )
  \\ first_assum(qspec_then`ms.PC + 1w`mp_tac)
  \\ impl_tac >- (
    fs[ag32_machine_config_def, FFI_codes_def]
    \\ EVAL_TAC \\ fs[] )
  \\ first_assum(qspec_then`ms.PC + 2w`mp_tac)
  \\ impl_tac >- (
    fs[ag32_machine_config_def, FFI_codes_def]
    \\ EVAL_TAC \\ fs[] )
  \\ first_x_assum(qspec_then`ms.PC + 3w`mp_tac)
  \\ impl_tac >- (
    fs[ag32_machine_config_def, FFI_codes_def]
    \\ EVAL_TAC \\ fs[] )
  \\ simp[]
  \\ simp[EVAL``(ag32_machine_config _ _ _).target.get_byte``]
  \\ rpt (disch_then SUBST_ALL_TAC)
  \\ qmatch_goalsub_abbrev_tac`_ @@ init_memory _ _ _ _ pc`
  \\ first_assum(mp_then Any mp_tac(GEN_ALL init_memory_halt))
  \\ simp[]
  \\ disch_then drule
  \\ disch_then drule
  \\ pop_assum mp_tac
  \\ simp[ag32_machine_config_def]
  \\ strip_tac
  \\ simp[get_mem_word_def]
  \\ disch_then kall_tac
  \\ simp[ag32_targetProofTheory.Decode_Encode]
  \\ simp[ag32Theory.Run_def, ag32Theory.dfn'Jump_def]
  \\ simp[ag32Theory.ALU_def, ag32Theory.ri2word_def]
  \\ strip_tac
  \\ simp[Abbr`ms1`, APPLY_UPDATE_THM]
QED

fun ffi_tac
  ag32_ffi_interfer_xxx
  ag32_ffi_xxx_code =
  match_mp_tac(GEN_ALL(ag32_ffi_interfer_xxx))
  \\ asm_exists_tac \\ simp[]
  \\ fs[EVAL``(ag32_machine_config _ _ _).ffi_names``]
  \\ conj_tac
  >- (
    simp[GSYM find_index_INDEX_OF]
    \\ simp[find_index_ALL_DISTINCT_EL_eq] )
  \\ rw[]
  \\ qmatch_goalsub_abbrev_tac`4 * k + off`
  \\ qspecl_then[`off DIV 4`,`ms1.MEM`,`MAP Encode ^ag32_ffi_xxx_code`]mp_tac
      (GEN_ALL get_mem_word_get_byte)
  \\ simp[EL_MAP,LEFT_ADD_DISTRIB]
  \\ `4 * (off DIV 4) = off` by (simp[Abbr`off`] \\ EVAL_TAC)
  \\ simp[]
  \\ disch_then match_mp_tac
  \\ pop_assum kall_tac
  \\ qexists_tac`DROP (off DIV 4 + LENGTH ^ag32_ffi_xxx_code) (init_memory_words code data ffi_names cl inp)`
  \\ qexists_tac`TAKE (off DIV 4) (init_memory_words code data ffi_names cl inp)`
  \\ reverse conj_tac
  >- (
    simp[LENGTH_TAKE_EQ, LENGTH_init_memory_words]
    \\ simp[Abbr`off`]
    \\ pop_assum mp_tac
    \\ qpat_x_assum`_ < memory_size` mp_tac
    \\ simp[EVAL``ffi_code_start_offset``]
    \\ fs[LENGTH_ag32_ffi_jumps, FFI_codes_def]
    \\ EVAL_TAC \\ fs[] )
  \\ simp[LENGTH_TAKE_EQ, LENGTH_init_memory_words]
  \\ pop_assum mp_tac
  \\ CONV_TAC(LAND_CONV EVAL)
  \\ strip_tac \\ simp[Abbr`off`]
  \\ rw[]
  \\ qmatch_goalsub_abbrev_tac`EL _ mw`
  \\ `mw = init_memory_words code data ffi_names cl inp`
  by (
    simp[Abbr`mw`]
    \\ match_mp_tac TAKE_DROP_SUBLIST
    \\ simp[]
    \\ reverse conj_tac
    >- simp[LENGTH_init_memory_words]
    \\ simp[IS_PREFIX_APPEND]
    \\ simp[init_memory_words_def]
    \\ simp[ag32_ffi_code_def]
    \\ rewrite_tac[GSYM APPEND_ASSOC]
    \\ qmatch_goalsub_abbrev_tac`MAP Encode ^ag32_ffi_xxx_code ++ l2`
    \\ simp[]
    \\ qmatch_goalsub_abbrev_tac`l1 ++ MAP Encode ^ag32_ffi_xxx_code ++ l2`
    \\ qmatch_goalsub_abbrev_tac`DROP n`
    \\ `n = LENGTH l1`
    by (
      simp[Abbr`n`, Abbr`l1`, LENGTH_ag32_ffi_code, heap_size_def, output_buffer_size_def]
      \\ simp[LENGTH_words_of_bytes, bitstringTheory.length_pad_right,
              bytes_in_word_def, LENGTH_FLAT, MAP_MAP_o, o_DEF, ADD1, SUM_MAP_PLUS,
              Q.ISPEC`λx. 1n`SUM_MAP_K |> SIMP_RULE(srw_ss())[]]
      \\ qmatch_goalsub_abbrev_tac`sz DIV 4`
      \\ `sz DIV 4 + (startup_code_size - sz) DIV 4 = startup_code_size DIV 4`
      by (
        DEP_REWRITE_TAC[GSYM ADD_DIV_RWT]
        \\ simp[LENGTH_startup_code_MOD_4, Abbr`sz`]
        \\ once_rewrite_tac[ADD_COMM]
        \\ DEP_REWRITE_TAC[SUB_ADD]
        \\ simp[LENGTH_startup_code])
      \\ rewrite_tac[ADD_ASSOC]
      \\ simp[Abbr`sz`]
      \\ simp[EVAL``startup_code_size``]
      \\ qmatch_goalsub_abbrev_tac`sz DIV 4`
      \\ `sz = stdin_size` by (rw[Abbr`sz`])
      \\ qpat_x_assum`Abbrev(sz = _)`kall_tac
      \\ qpat_abbrev_tac`cz = if _ < cline_size then _ else _`
      \\ `cz = cline_size` by (rw[Abbr`cz`])
      \\ qpat_x_assum`Abbrev(cz = _)`kall_tac
      \\ rveq
      \\ simp[LENGTH_startup_code_MOD_4]
      \\ rw[stdin_size_def, cline_size_def]
      \\ EVAL_TAC)
    \\ rewrite_tac[GSYM APPEND_ASSOC]
    \\ asm_rewrite_tac[DROP_LENGTH_APPEND]
    \\ simp[])
  \\ qpat_x_assum`Abbrev(mw = _)`kall_tac
  \\ rw[]
  \\ simp[GSYM init_memory_def]
  \\ fs[is_ag32_init_state_def]
  \\ rfs[]
  \\ `ms1.MEM x = ms.MEM x`
  by (
    first_x_assum irule
    \\ simp[ag32_machine_config_def]
    \\ conj_tac
    >- (
      EVAL_TAC
      \\ fs[EVAL``LENGTH ^ag32_ffi_xxx_code``]
      \\ Cases_on`x` \\ fs[word_add_n2w]
      \\ fs[word_ls_n2w, word_lo_n2w] \\ rfs[] )
    \\ qpat_x_assum`_ < memory_size` mp_tac
    \\ EVAL_TAC \\ simp[]
    \\ Cases_on`x` \\ fs[word_add_n2w, FFI_codes_def]
    \\ fs[word_ls_n2w, word_lo_n2w] \\ rfs[]
    \\ fs[EVAL``LENGTH ^ag32_ffi_xxx_code``]
    \\ rfs[])
  \\ rw[]
  \\ first_x_assum irule
  \\ EVAL_TAC
  \\ fs[EVAL``LENGTH ^ag32_ffi_xxx_code``]
  \\ Cases_on`x` \\ fs[word_add_n2w]
  \\ fs[word_ls_n2w, word_lo_n2w] \\ rfs[];

Theorem ag32_interference_implemented:
   SUM (MAP strlen cl) + LENGTH cl ≤ cline_size ∧
   LENGTH inp ≤ stdin_size ∧
   set ffi_names ⊆ set (MAP FST ffi_exitpcs) ∧ ALL_DISTINCT ffi_names ∧
   code_start_offset (LENGTH ffi_names) + LENGTH code + 4 * LENGTH data < memory_size ∧
   is_ag32_init_state (init_memory code data ffi_names (cl,inp)) ms0 ∧
   Abbrev(ms = FUNPOW Next startup_clock ms0) ∧
   (∀x. x ∉ ag32_startup_addresses ⇒ (ms.MEM x = ms0.MEM x))
  ⇒
   interference_implemented
    (ag32_machine_config ffi_names (LENGTH code) (LENGTH data))
    (ag32_ffi_rel)
    (ag32_ffi_mem_domain) ms
Proof
  rw[interference_implemented_def]
  \\ simp[EVAL``(ag32_machine_config _ _ _).target.next``]
  \\ simp[EVAL``(ag32_machine_config _ _ _).target.get_byte``]
  \\ simp[EVAL``(ag32_machine_config _ _ _).target.get_pc``]
  \\ simp[EVAL``(ag32_machine_config _ _ _).target.get_reg``]
  \\ simp[SIMP_CONV(srw_ss()++LET_ss)[ag32_machine_config_def]
            ``(ag32_machine_config _ _ _).ffi_entry_pcs``]
  \\ simp[Once ag32_machine_config_def]
  \\ simp[Once ag32_machine_config_def]
  \\ simp[Once ag32_machine_config_def]
  \\ qx_gen_tac`k0`
  \\ strip_tac
  \\ imp_res_tac SUBSET_ffi_names_IMP_LENGTH_LESS_EQ
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
      \\ `aligned 2 pc`
        by rfs[ag32_targetTheory.ag32_target_def, ag32_targetTheory.ag32_ok_def, EVAL``(ag32_machine_config _ _ _).target.state_ok``]
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
      \\ fs[EVAL``(ag32_machine_config _ _ _).target.config.code_alignment``]
      \\ fs[EVAL``(ag32_machine_config _ _ _).target.config.encode``]
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
        \\ Q.ISPECL_THEN[`TAKE j bs`,`DROP j bs`,`pc`]mp_tac bytes_in_memory_APPEND
        \\ simp[]
        \\ disch_then(drule o #1 o EQ_IMP_RULE o SPEC_ALL)
        \\ simp[]
        \\ Cases_on`DROP j bs` \\ fs[DROP_NIL]
        \\ simp[bytes_in_memory_def]
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
    \\ qmatch_goalsub_rename_tac`ino = UStream _`
    \\ Cases_on`ino = UStream (strlit"stdin")` \\ simp[]
    \\ Cases_on`ALOOKUP (SND x.ffi_state).inode_tbl (UStream(strlit"stdin"))` \\ simp[]
    \\ qmatch_goalsub_rename_tac`off ≤ LENGTH input`
    \\ Cases_on`off ≤ LENGTH input ∧ LENGTH input ≤ stdin_size` \\ fs[] \\ rveq
    \\ `∀i. i < 8 + LENGTH cnt ⇒ ((Next ms1).MEM (n2w (stdin_offset + i)) = m (n2w (stdin_offset + i)))`
    by (
      rw[]
      \\ first_x_assum irule
      \\ rw[Abbr`md`]
      \\ qpat_x_assum`_ < memory_size`mp_tac
      \\ EVAL_TAC
      \\ fs[EVAL``stdin_size``,FFI_codes_def]
      \\ simp[ word_lo_n2w, word_ls_n2w])
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
      \\ irule bytes_in_memory_change_mem
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
      \\ qpat_x_assum`_ < memory_size`mp_tac
      \\ EVAL_TAC
      \\ simp[word_lo_n2w, word_ls_n2w]
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
    \\ irule bytes_in_memory_change_mem
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
        simp[Abbr`pc`, ag32_machine_config_def, GSYM word_add_n2w]
        \\ (alignmentTheory.aligned_add_sub_cor
            |> SPEC_ALL |> UNDISCH |> CONJUNCT1 |> DISCH_ALL
            |> irule)
        \\ conj_tac >- EVAL_TAC
        \\ simp[GSYM addressTheory.ALIGNED_eq_aligned, addressTheory.ALIGNED_n2w]
        \\ EVAL_TAC \\ simp[] )
      \\ `pc = pc'`
      by (
        pop_assum mp_tac
        \\ unabbrev_all_tac
        \\ simp[alignmentTheory.aligned_extract]
        \\ blastLib.BBLAST_TAC )
      \\ qpat_x_assum`Abbrev(pc' = _)` kall_tac
      \\ pop_assum (SUBST_ALL_TAC o SYM)
      \\ first_assum(qspec_then`pc`mp_tac)
      \\ impl_tac >- (
        simp[Abbr`pc`]
        \\ qpat_x_assum`_ < memory_size`mp_tac \\ EVAL_TAC
        \\ fs[FFI_codes_def, word_ls_n2w, word_lo_n2w])
      \\ first_assum(qspec_then`pc + 1w`mp_tac)
      \\ impl_tac >- (
        simp[Abbr`pc`]
        \\ qpat_x_assum`_ < memory_size`mp_tac \\ EVAL_TAC
        \\ fs[FFI_codes_def, word_ls_n2w, word_lo_n2w])
      \\ first_assum(qspec_then`pc + 2w`mp_tac)
      \\ impl_tac >- (
        simp[Abbr`pc`]
        \\ qpat_x_assum`_ < memory_size`mp_tac \\ EVAL_TAC
        \\ fs[FFI_codes_def, word_ls_n2w, word_lo_n2w])
      \\ first_assum(qspec_then`pc + 3w`mp_tac)
      \\ impl_tac >- (
        simp[Abbr`pc`]
        \\ qpat_x_assum`_ < memory_size`mp_tac \\ EVAL_TAC
        \\ fs[FFI_codes_def, word_ls_n2w, word_lo_n2w])
      \\ simp[]
      \\ ntac 4 (disch_then kall_tac)
      \\ last_assum(qspec_then`pc`mp_tac)
      \\ impl_tac >- (
        simp[Abbr`pc`]
        \\ qpat_x_assum`_ < memory_size`mp_tac \\ EVAL_TAC
        \\ fs[FFI_codes_def, word_ls_n2w, word_lo_n2w])
      \\ last_assum(qspec_then`pc + 1w`mp_tac)
      \\ impl_tac >- (
        simp[Abbr`pc`]
        \\ qpat_x_assum`_ < memory_size`mp_tac \\ EVAL_TAC
        \\ fs[FFI_codes_def, word_ls_n2w, word_lo_n2w])
      \\ last_assum(qspec_then`pc + 2w`mp_tac)
      \\ impl_tac >- (
        simp[Abbr`pc`]
        \\ qpat_x_assum`_ < memory_size`mp_tac \\ EVAL_TAC
        \\ fs[FFI_codes_def, word_ls_n2w, word_lo_n2w])
      \\ last_assum(qspec_then`pc + 3w`mp_tac)
      \\ impl_tac >- (
        simp[Abbr`pc`]
        \\ qpat_x_assum`_ < memory_size`mp_tac \\ EVAL_TAC
        \\ fs[FFI_codes_def, word_ls_n2w, word_lo_n2w])
      \\ simp[]
      \\ ntac 4 (disch_then kall_tac)
      \\ fs[is_ag32_init_state_def]
      \\ simp[GSYM get_mem_word_def]
      \\ DEP_REWRITE_TAC[init_memory_ccache]
      \\ conj_tac
      >- ( simp[Abbr`pc`] \\ EVAL_TAC \\ simp[])
      \\ simp[ag32_targetProofTheory.Decode_Encode]
      \\ simp[ag32Theory.Run_def]
      \\ simp[ag32Theory.dfn'Jump_def]
      \\ simp[ag32Theory.ALU_def]
      \\ simp[ag32Theory.ri2word_def]
      \\ rpt(AP_TERM_TAC ORELSE AP_THM_TAC)
      \\ simp[Abbr`pc`]
      \\ EVAL_TAC \\ fs[FFI_codes_def])
    \\ pop_assum(SUBST_ALL_TAC o SYM)
    \\ conj_tac >- simp[ag32_ffi_rel_def,FUN_EQ_THM]
    \\ simp[] )
  \\ rpt gen_tac
  \\ simp[EVAL``(ag32_machine_config _ _ _).ptr2_reg``]
  \\ qmatch_goalsub_abbrev_tac`ag32_ffi_rel ms1`
  \\ `∀k. k < LENGTH (ag32_ffi_jumps (ffi_names)) ⇒
         (get_mem_word ms1.MEM (n2w (ffi_jumps_offset + 4 * k)) =
          EL k (ag32_ffi_jumps (ffi_names)))`
  by (
    rw[]
    \\ first_assum(mp_then Any mp_tac (GEN_ALL get_mem_word_get_byte))
    \\ disch_then(qspec_then`ffi_jumps_offset DIV 4`mp_tac)
    \\ simp[LEFT_ADD_DISTRIB]
    \\ mp_tac(EVAL``4 * (ffi_jumps_offset DIV 4) = ffi_jumps_offset``)
    \\ simp[] \\ disch_then kall_tac
    \\ disch_then match_mp_tac
    \\ qexists_tac`DROP (ffi_jumps_offset DIV 4 + LENGTH (ag32_ffi_jumps ffi_names))
                        (init_memory_words code data ffi_names cl inp)`
    \\ qexists_tac`TAKE (ffi_jumps_offset DIV 4) (init_memory_words code data ffi_names cl inp)`
    \\ reverse conj_tac
    >- (
      simp[LENGTH_TAKE_EQ]
      \\ reverse conj_tac
      >- (
        pop_assum mp_tac
        \\ simp[LENGTH_ag32_ffi_jumps]
        \\ EVAL_TAC
        \\ fs[FFI_codes_def])
      \\ rw[]
      \\ pop_assum mp_tac
      \\ simp[]
      \\ CONV_TAC(LAND_CONV EVAL)
      \\ simp[LENGTH_init_memory_words] )
    \\ simp[LENGTH_TAKE_EQ]
    \\ reverse IF_CASES_TAC
    >- (
      `F` suffices_by rw[]
      \\ pop_assum mp_tac
      \\ simp[LENGTH_init_memory_words, LENGTH_ag32_ffi_jumps]
      \\ EVAL_TAC
      \\ fs[FFI_codes_def])
    \\ rw[]
    \\ qmatch_goalsub_abbrev_tac`EL _ mw`
    \\ `mw = init_memory_words code data ffi_names cl inp`
    by (
      simp[Abbr`mw`]
      \\ match_mp_tac TAKE_DROP_SUBLIST
      \\ simp[]
      \\ reverse conj_tac
      >- (
        simp[LENGTH_init_memory_words, LENGTH_ag32_ffi_jumps]
        \\ EVAL_TAC
        \\ fs[FFI_codes_def])
      \\ simp[IS_PREFIX_APPEND]
      \\ simp[init_memory_words_def]
      \\ qmatch_goalsub_abbrev_tac`l1 ++ ag32_ffi_jumps _ ++ _ ++ _`
      \\ `ffi_jumps_offset DIV 4 = LENGTH l1`
      by (
        simp[Abbr`l1`, LENGTH_ag32_ffi_code, heap_size_def,
             output_buffer_size_def, startup_code_size_def]
        \\ CONV_TAC(LAND_CONV EVAL)
        \\ simp[LENGTH_words_of_bytes, bitstringTheory.length_pad_right,
                bytes_in_word_def, LENGTH_FLAT, MAP_MAP_o, o_DEF, ADD1, SUM_MAP_PLUS,
                Q.ISPEC`λx. 1n`SUM_MAP_K |> SIMP_RULE(srw_ss())[]]
        \\ qmatch_goalsub_abbrev_tac`sz DIV 4`
        \\ `sz DIV 4 + (240 - sz) DIV 4 = 240 DIV 4`
        by (
          DEP_REWRITE_TAC[GSYM ADD_DIV_RWT]
          \\ simp[LENGTH_startup_code_MOD_4, Abbr`sz`]
          \\ simp[GSYM (EVAL``startup_code_size``)]
          \\ once_rewrite_tac[ADD_COMM]
          \\ DEP_REWRITE_TAC[SUB_ADD]
          \\ simp[LENGTH_startup_code]
          \\ EVAL_TAC )
        \\ rewrite_tac[ADD_ASSOC] \\ pop_assum SUBST1_TAC
        \\ simp[Abbr`sz`]
        \\ qmatch_goalsub_abbrev_tac`sz DIV 4`
        \\ `sz = stdin_size` by (rw[Abbr`sz`])
        \\ qpat_x_assum`Abbrev(sz = _)`kall_tac
        \\ qmatch_goalsub_abbrev_tac`_ + (cz DIV 4 + _)`
        \\ `cz = cline_size` by (rw[Abbr`cz`])
        \\ qpat_x_assum`Abbrev(cz = _)`kall_tac
        \\ rveq
        \\ rw[stdin_size_def, cline_size_def, LENGTH_startup_code_MOD_4])
      \\ rewrite_tac[GSYM APPEND_ASSOC]
      \\ asm_rewrite_tac[DROP_LENGTH_APPEND]
      \\ simp[])
    \\ qpat_x_assum`Abbrev(mw = _)`kall_tac
    \\ rw[]
    \\ simp[GSYM init_memory_def]
    \\ `ms1.MEM x = ms.MEM x`
    by (
      first_x_assum irule
      \\ simp[ag32_machine_config_def]
      \\ conj_tac
      >- (
        EVAL_TAC
        \\ fs[EVAL``ffi_jumps_offset``, LENGTH_ag32_ffi_jumps]
        \\ Cases_on`x` \\ fs[ word_add_n2w]
        \\ fs[word_ls_n2w, word_lo_n2w] \\ rfs[]
        \\ ntac 3 (pop_assum mp_tac)
        \\ fs[FFI_codes_def])
      \\ qpat_x_assum`_ < memory_size`mp_tac
      \\ EVAL_TAC \\ simp[]
      \\ Cases_on`x` \\ fs[word_add_n2w, FFI_codes_def]
      \\ fs[word_ls_n2w, word_lo_n2w] \\ rfs[]
      \\ fs[EVAL``ffi_jumps_offset``, LENGTH_ag32_ffi_jumps]
      \\ rfs[])
    \\ fs[is_ag32_init_state_def] \\ rfs[]
    \\ first_x_assum irule
    \\ EVAL_TAC
    \\ fs[EVAL``ffi_jumps_offset``, LENGTH_ag32_ffi_jumps, FFI_codes_def]
    \\ Cases_on`x` \\ fs[word_add_n2w]
    \\ fs[word_ls_n2w, word_lo_n2w] \\ rfs[])
  \\ strip_tac
  \\ `LENGTH bytes2 + w2n (ms1.R 3w) < dimword (:32)`
  by (
    fs[targetSemTheory.read_ffi_bytearrays_def,
       targetSemTheory.read_ffi_bytearray_def,
       EVAL``(ag32_machine_config _ _ _).target.get_reg``,
       EVAL``(ag32_machine_config _ _ _).ptr2_reg``,
       EVAL``(ag32_machine_config _ _ _).len2_reg``]
    \\ drule (SIMP_RULE(srw_ss())[PULL_EXISTS, IS_SOME_EXISTS]read_bytearray_no_wrap)
    \\ simp[]
    \\ Cases_on`ms1.R 4w` \\ fs[]
    \\ imp_res_tac read_bytearray_LENGTH \\ fs[]
    \\ strip_tac
    \\ first_x_assum irule
    \\ Cases_on`ms1.R 3w` \\ fs[]
    \\ EVAL_TAC
    \\ fs[memory_size_def, FFI_codes_def]
    \\ Cases
    \\ simp[word_ls_n2w, word_lo_n2w] )
  \\ qmatch_asmsub_abbrev_tac`find_index _ ls`
  \\ `ALL_DISTINCT ls`
  by (
    simp[Abbr`ls`, ALL_DISTINCT_GENLIST]
    \\ fs[FFI_codes_def]
    \\ EVAL_TAC \\ rw[] \\ rfs[] )
  \\ drule find_index_ALL_DISTINCT_EL_eq
  \\ strip_tac \\ fs[]
  \\ pop_assum kall_tac
  \\ qpat_x_assum`ALL_DISTINCT _` kall_tac
  \\ fs[Abbr`ls`]
  \\ rfs[EL_REVERSE, PRE_SUB1]
  \\ qpat_x_assum`_ ⊆ _`mp_tac
  \\ simp[ffi_exitpcs_def, SUBSET_DEF]
  \\ simp[MEM_EL, PULL_EXISTS]
  \\ disch_then(qspec_then`ffi_index`mp_tac)
  \\ impl_tac >- fs[]
  (*
  \\ Cases_on`EL ffi_index ffi_names = "exit"` \\ fs[]
  >- ... (* remove exit from the list ? or implement it *)
  *)
  \\ Cases_on`EL ffi_index ffi_names = ""` \\ fs[]
  >- ffi_tac ag32_ffi_interfer_ ``ag32_ffi__code``
  \\ Cases_on`EL ffi_index ffi_names = "read"` \\ fs[]
  >- ffi_tac ag32_ffi_interfer_read ``ag32_ffi_read_code``
  \\ Cases_on`EL ffi_index ffi_names = "close"` \\ fs[]
  >- ffi_tac ag32_ffi_interfer_close ``ag32_ffi_close_code``
  \\ Cases_on`EL ffi_index ffi_names = "open_in"` \\ fs[]
  >- ffi_tac ag32_ffi_interfer_open_in ``ag32_ffi_open_in_code``
  \\ Cases_on`EL ffi_index ffi_names = "write"` \\ fs[]
  >- ffi_tac ag32_ffi_interfer_write ``ag32_ffi_write_code``
  \\ Cases_on`EL ffi_index ffi_names = "get_arg_count"` \\ fs[]
  >- ffi_tac ag32_ffi_interfer_get_arg_count ``ag32_ffi_get_arg_count_code``
  \\ Cases_on`EL ffi_index ffi_names = "get_arg"` \\ fs[]
  >- ffi_tac ag32_ffi_interfer_get_arg ``ag32_ffi_get_arg_code``
  \\ Cases_on`EL ffi_index ffi_names = "get_arg_length"` \\ fs[]
  >- ffi_tac ag32_ffi_interfer_get_arg_length ``ag32_ffi_get_arg_length_code``
  \\ Cases_on`EL ffi_index ffi_names = "open_out"` \\ fs[]
  >- ffi_tac ag32_ffi_interfer_open_out ``ag32_ffi_open_out_code``
QED

Theorem ag32_next:
   SUM (MAP strlen cl) + LENGTH cl ≤ cline_size ∧ wfcl cl ∧
   LENGTH inp ≤ stdin_size ∧
   set ffi_names ⊆ set (MAP FST ffi_exitpcs) ∧ ALL_DISTINCT ffi_names ∧
   code_start_offset (LENGTH ffi_names) + LENGTH code + 4 * LENGTH data < memory_size ∧
   is_ag32_init_state (init_memory code data ffi_names (cl,inp)) ms0 ∧
   Abbrev(ms = FUNPOW Next startup_clock ms0) ∧
   (ms.io_events = ms0.io_events) ∧
   (∀x. x ∉ ag32_startup_addresses ⇒ (ms.MEM x = ms0.MEM x)) ∧
   machine_sem (ag32_machine_config ffi_names (LENGTH code) (LENGTH data)) (basis_ffi cl (stdin_fs inp))
     ms ⊆ extend_with_resource_limit {Terminate Success io_events}
  ⇒
   ∃k1. ∀k. k1 ≤ k ⇒
     let ms = FUNPOW Next k ms0 in
     let outs = MAP (get_ag32_io_event) ms.io_events in
       (ms.PC = (ag32_machine_config ffi_names (LENGTH code) (LENGTH data)).halt_pc) ∧
       (get_mem_word ms.MEM ms.PC = Encode (Jump (fAdd,0w,Imm 0w))) ∧
       outs ≼ MAP get_output_io_event io_events ∧
       ((ms.R (n2w (ag32_machine_config ffi_names (LENGTH code) (LENGTH data)).ptr_reg) = 0w) ⇒
        (outs = MAP get_output_io_event io_events))
Proof
  rw[]
  \\ fs[semanticsPropsTheory.extend_with_resource_limit_def]
  \\ qmatch_asmsub_abbrev_tac`machine_sem mc st ms`
  \\ `∃b. machine_sem mc st ms b` by metis_tac[targetPropsTheory.machine_sem_total]
  \\ qpat_x_assum`machine_sem _ _ _ ⊆ _`mp_tac
  \\ simp[SUBSET_DEF, IN_DEF] \\ strip_tac
  \\ first_x_assum drule
  \\ disch_then(assume_tac o ONCE_REWRITE_RULE[GSYM markerTheory.Abbrev_def])
  \\ `∃x y. b = Terminate x y` by fs[markerTheory.Abbrev_def] \\ rveq
  \\ first_x_assum(mp_then Any mp_tac (GEN_ALL machine_sem_Terminate_FUNPOW_next))
  \\ first_assum(mp_then Any mp_tac (GEN_ALL ag32_interference_implemented))
  \\ simp[]
  \\ rpt(disch_then drule)
  \\ strip_tac \\ rfs[]
  \\ disch_then drule
  \\ impl_tac >-
  (
    simp[ag32_ffi_rel_def,Abbr`st`]
    \\ conj_tac
    >- (
      EVAL_TAC
      \\ simp[Abbr`ms`]
      \\ fs[is_ag32_init_state_def])
    \\ simp[basis_ffiTheory.basis_ffi_def]
    \\ simp[ag32_fs_ok_stdin_fs]
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
        \\ simp[Abbr`m`, init_memory_def]
        \\ simp[init_memory_words_def]
        \\ rewrite_tac[GSYM APPEND_ASSOC]
        \\ qmatch_goalsub_abbrev_tac`([0w] ++ lr)`
        \\ rewrite_tac[APPEND_ASSOC]
        \\ qmatch_goalsub_abbrev_tac`ll ++ [0w] ++ lr`
        \\ map_every qexists_tac[`ll`,`lr`]
        \\ simp[]
        \\ simp[Abbr`ll`]
        \\ simp[LENGTH_words_of_bytes, bitstringTheory.length_pad_right,
                bytes_in_word_def, LENGTH_FLAT, MAP_MAP_o, o_DEF, ADD1, SUM_MAP_PLUS,
                Q.ISPEC`λx. 1n`SUM_MAP_K |> SIMP_RULE(srw_ss())[]]
        \\ qmatch_goalsub_abbrev_tac`sz DIV 4`
        \\ `sz DIV 4 + (startup_code_size - sz) DIV 4 = startup_code_size DIV 4`
        by (
          DEP_REWRITE_TAC[GSYM ADD_DIV_RWT]
          \\ simp[LENGTH_startup_code_MOD_4, Abbr`sz`]
          \\ once_rewrite_tac[ADD_COMM]
          \\ DEP_REWRITE_TAC[SUB_ADD]
          \\ simp[LENGTH_startup_code])
        \\ rewrite_tac[ADD_ASSOC] \\ pop_assum SUBST1_TAC
        \\ simp[Abbr`sz`]
        \\ qpat_abbrev_tac`cz = if _ < cline_size then _ else _`
        \\ `cz = cline_size` by (rw[Abbr`cz`])
        \\ qpat_x_assum`Abbrev(cz = _)`kall_tac
        \\ simp[LENGTH_startup_code_MOD_4] \\ EVAL_TAC )
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
        \\ simp[Abbr`m`, init_memory_def]
        \\ simp[init_memory_words_def]
        \\ rewrite_tac[GSYM APPEND_ASSOC]
        \\ qmatch_goalsub_abbrev_tac`([n2w(LENGTH inp)] ++ lr)`
        \\ rewrite_tac[APPEND_ASSOC]
        \\ qmatch_goalsub_abbrev_tac`ll ++ [n2w(LENGTH inp)] ++ lr`
        \\ map_every qexists_tac[`ll`,`lr`]
        \\ simp[]
        \\ simp[Abbr`ll`]
        \\ simp[LENGTH_words_of_bytes, bitstringTheory.length_pad_right,
                bytes_in_word_def, LENGTH_FLAT, MAP_MAP_o, o_DEF, ADD1, SUM_MAP_PLUS,
                Q.ISPEC`λx. 1n`SUM_MAP_K |> SIMP_RULE(srw_ss())[]]
        \\ qmatch_goalsub_abbrev_tac`sz DIV 4`
        \\ `sz DIV 4 + (startup_code_size - sz) DIV 4 = startup_code_size DIV 4`
        by (
          DEP_REWRITE_TAC[GSYM ADD_DIV_RWT]
          \\ simp[LENGTH_startup_code_MOD_4, Abbr`sz`]
          \\ once_rewrite_tac[ADD_COMM]
          \\ DEP_REWRITE_TAC[SUB_ADD]
          \\ simp[LENGTH_startup_code])
        \\ rewrite_tac[ADD_ASSOC] \\ pop_assum SUBST1_TAC
        \\ simp[Abbr`sz`]
        \\ qpat_abbrev_tac`cz = if _ < cline_size then _ else _`
        \\ `cz = cline_size` by (rw[Abbr`cz`])
        \\ qpat_x_assum`Abbrev(cz = _)`kall_tac
        \\ simp[LENGTH_startup_code_MOD_4] \\ EVAL_TAC )
      \\ irule bytes_in_memory_change_mem
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
      \\ irule asmPropsTheory.read_bytearray_IMP_bytes_in_memory
      \\ qexists_tac`SOME o m2`
      \\ qexists_tac`LENGTH inp`
      \\ simp[]
      \\ irule data_to_word_assignProofTheory.IMP_read_bytearray_GENLIST
      \\ simp[]
      \\ simp[init_memory_def]
      (* TODO: this could be an init_memory_stdin lemma *)
      \\ `byte_aligned ((n2w (stdin_offset + 8)):word32)` by EVAL_TAC
      \\ `n2w (stdin_offset + 8) = byte_align (n2w (stdin_offset + 8)) : word32`
      by (
        fs[alignmentTheory.byte_align_def, alignmentTheory.byte_aligned_def]
        \\ fs[alignmentTheory.aligned_def] )
      \\ first_assum(SUBST1_TAC)
      \\ gen_tac
      \\ DEP_REWRITE_TAC[data_to_word_memoryProofTheory.get_byte_byte_align]
      \\ pop_assum (SUBST1_TAC o SYM)
      \\ conj_tac >- EVAL_TAC
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
      \\ simp[]
      \\ fs[EVAL``stdin_size``, EVAL``stdin_offset``]
      \\ DEP_REWRITE_TAC[ADD_DIV_RWT] \\ simp[]
      \\ rewrite_tac[init_memory_words_def]
      \\ LET_ELIM_TAC
      \\ qmatch_goalsub_abbrev_tac`ll ++ words_of_bytes _ (_ _ (_ _ inp))`
      \\ qmatch_goalsub_abbrev_tac`EL (_ + off)`
      \\ `LENGTH ll = off`
      by (
        simp[Abbr`ll`, Abbr`off`]
        \\ simp[LENGTH_words_of_bytes, bitstringTheory.length_pad_right, LENGTH_FLAT,
                bytes_in_word_def, MAP_MAP_o, o_DEF, ADD1, SUM_MAP_PLUS]
        \\ simp[Q.ISPEC`λx. 1n`SUM_MAP_K |> SIMP_RULE(srw_ss())[]]
        \\ qmatch_goalsub_abbrev_tac`sz DIV 4`
        \\ `sz DIV 4 + (startup_code_size - sz) DIV 4 = startup_code_size DIV 4`
        by (
          DEP_REWRITE_TAC[GSYM ADD_DIV_RWT]
          \\ simp[LENGTH_startup_code_MOD_4, Abbr`sz`, Abbr`sc`]
          \\ once_rewrite_tac[ADD_COMM]
          \\ DEP_REWRITE_TAC[SUB_ADD]
          \\ simp[LENGTH_startup_code])
        \\ rewrite_tac[ADD_ASSOC] \\ pop_assum SUBST1_TAC
        \\ simp[Abbr`sz`,Abbr`sc`]
        \\ qpat_abbrev_tac`cz = if _ < cline_size then _ else _`
        \\ `cz = cline_size` by (rw[Abbr`cz`])
        \\ qpat_x_assum`Abbrev(cz = _)`kall_tac
        \\ simp[LENGTH_startup_code_MOD_4] \\ EVAL_TAC )
      \\ rewrite_tac[GSYM APPEND_ASSOC] \\ DEP_ONCE_REWRITE_TAC[EL_APPEND2]
      \\ simp[]
      \\ rewrite_tac[GSYM APPEND_ASSOC]
      \\ DEP_REWRITE_TAC[EL_APPEND1]
      \\ simp[LENGTH_words_of_bytes, bitstringTheory.length_pad_right,
              LENGTH_FLAT, bytes_in_word_def, MAP_MAP_o, o_DEF, ADD1, SUM_MAP_PLUS]
      \\ qmatch_goalsub_abbrev_tac`MIN 1 (cz MOD _)` \\ `cz = stdin_size` by ( simp[Abbr`cz`,EVAL``stdin_size``] )
      \\ qpat_x_assum`Abbrev(cz = _)`kall_tac \\ pop_assum SUBST_ALL_TAC
      \\ simp[EVAL``stdin_size``]
      \\ simp[DIV_LT_X]
      \\ conj_tac
      >- (
        simp[alignmentTheory.align_w2n]
        \\ qmatch_goalsub_abbrev_tac`a MOD _`
        \\ `a < dimword(:32)` by (
          simp[Abbr`a`]
          \\ irule IMP_MULT_DIV_LESS
          \\ simp[] )
        \\ pop_assum mp_tac \\ simp[] \\ strip_tac
        \\ simp[Abbr`a`]
        \\ irule IMP_MULT_DIV_LESS
        \\ simp[] )
      \\ `align 2 (n2w i) = byte_align (n2w i) : word32` by EVAL_TAC
      \\ pop_assum SUBST_ALL_TAC
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
      \\ simp[Abbr`m`, init_memory_def]
      \\ simp[init_memory_words_def]
      \\ rewrite_tac[GSYM APPEND_ASSOC]
      \\ qmatch_goalsub_abbrev_tac`([n2w (LENGTH cl)] ++ lr)`
      \\ rewrite_tac[APPEND_ASSOC]
      \\ qmatch_goalsub_abbrev_tac`ll ++ [n2w (LENGTH cl)] ++ lr`
      \\ map_every qexists_tac[`ll`,`lr`]
      \\ simp[]
      \\ simp[Abbr`ll`, LENGTH_words_of_bytes, bytes_in_word_def]
      \\ qmatch_goalsub_abbrev_tac`sz DIV 4`
      \\ `sz DIV 4 + (startup_code_size - sz) DIV 4 = startup_code_size DIV 4`
      by (
        DEP_REWRITE_TAC[GSYM ADD_DIV_RWT]
        \\ simp[LENGTH_startup_code_MOD_4, Abbr`sz`]
        \\ once_rewrite_tac[ADD_COMM]
        \\ DEP_REWRITE_TAC[SUB_ADD]
        \\ simp[LENGTH_startup_code])
      \\ rewrite_tac[ADD_ASSOC] \\ pop_assum SUBST1_TAC
      \\ simp[Abbr`sz`, LENGTH_startup_code_MOD_4]
      \\ EVAL_TAC )
    \\ irule bytes_in_memory_change_mem
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
    \\ simp[init_memory_def]
    \\ `byte_aligned ((n2w (startup_code_size + 4)):word32)` by EVAL_TAC
    \\ `n2w (startup_code_size + 4) = byte_align (n2w (startup_code_size + 4)) : word32`
    by (
      fs[alignmentTheory.byte_align_def, alignmentTheory.byte_aligned_def]
      \\ fs[alignmentTheory.aligned_def] )
    \\ first_assum(SUBST1_TAC)
    \\ gen_tac
    \\ DEP_REWRITE_TAC[data_to_word_memoryProofTheory.get_byte_byte_align]
    \\ pop_assum (SUBST1_TAC o SYM)
    \\ conj_tac >- EVAL_TAC
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
    \\ simp[]
    \\ fs[EVAL``cline_size``, EVAL``startup_code_size``]
    \\ DEP_REWRITE_TAC[ADD_DIV_RWT] \\ simp[]
    \\ rewrite_tac[init_memory_words_def]
    \\ LET_ELIM_TAC
    \\ qmatch_goalsub_abbrev_tac`ll ++ words_of_bytes _ (_ _ _ (FLAT _))`
    \\ qmatch_goalsub_abbrev_tac`EL (_ + off)`
    \\ `LENGTH ll = off`
    by (
      simp[Abbr`ll`, Abbr`off`]
      \\ simp[LENGTH_words_of_bytes, bitstringTheory.length_pad_right, LENGTH_FLAT,
              bytes_in_word_def, MAP_MAP_o, o_DEF, ADD1, SUM_MAP_PLUS]
      \\ qmatch_goalsub_abbrev_tac`sz DIV 4`
      \\ `sz DIV 4 + (startup_code_size - sz) DIV 4 = startup_code_size DIV 4`
      by (
        DEP_REWRITE_TAC[GSYM ADD_DIV_RWT]
        \\ simp[LENGTH_startup_code_MOD_4, Abbr`sz`, Abbr`sc`]
        \\ once_rewrite_tac[ADD_COMM]
        \\ DEP_REWRITE_TAC[SUB_ADD]
        \\ simp[LENGTH_startup_code])
      \\ rewrite_tac[ADD_ASSOC] \\ pop_assum SUBST1_TAC
      \\ simp[Abbr`sz`,Abbr`sc`]
      \\ simp[LENGTH_startup_code_MOD_4] \\ EVAL_TAC )
    \\ rewrite_tac[GSYM APPEND_ASSOC] \\ DEP_ONCE_REWRITE_TAC[EL_APPEND2]
    \\ simp[]
    \\ rewrite_tac[GSYM APPEND_ASSOC]
    \\ DEP_REWRITE_TAC[EL_APPEND1]
    \\ qpat_x_assum`_ ∨ _`kall_tac
    \\ fs[LENGTH_words_of_bytes, bitstringTheory.length_pad_right,
          LENGTH_FLAT, bytes_in_word_def, MAP_MAP_o, o_DEF, ADD1, SUM_MAP_PLUS]
    \\ fs[Q.ISPEC`λx. 1n`SUM_MAP_K |> SIMP_RULE(srw_ss())[]]
    \\ qpat_abbrev_tac`cz = if _ < cline_size then _ else _`
    \\ `cz = cline_size` by (rw[Abbr`cz`] \\ fs[EVAL``cline_size``])
    \\ qpat_x_assum`Abbrev(cz = _)`kall_tac
    \\ simp[DIV_LT_X]
    \\ conj_tac
    >- (
      simp[alignmentTheory.align_w2n]
      \\ qmatch_goalsub_abbrev_tac`a MOD _`
      \\ `a < dimword(:32)` by (
        simp[Abbr`a`]
        \\ irule IMP_MULT_DIV_LESS
        \\ simp[] )
      \\ pop_assum mp_tac \\ simp[] \\ strip_tac
      \\ simp[Abbr`a`]
      \\ EVAL_TAC
      \\ fs[DIV_LT_X])
    \\ `align 2 (n2w i) = byte_align (n2w i) : word32` by EVAL_TAC
    \\ pop_assum SUBST_ALL_TAC
    \\ `4 = w2n (bytes_in_word:word32)` by EVAL_TAC
    \\ pop_assum SUBST1_TAC
    \\ DEP_REWRITE_TAC[get_byte_EL_words_of_bytes]
    \\ simp[bitstringTheory.length_pad_right]
    \\ fs[LENGTH_words_of_bytes, bitstringTheory.length_pad_right,
          LENGTH_FLAT, bytes_in_word_def, MAP_MAP_o, o_DEF, ADD1, SUM_MAP_PLUS]
    \\ fs[Q.ISPEC`λx. 1n`SUM_MAP_K |> SIMP_RULE(srw_ss())[]]
    \\ fs[EVAL``cline_size``]
    \\ simp[PAD_RIGHT]
    \\ DEP_REWRITE_TAC[EL_APPEND1]
    \\ fs[LENGTH_words_of_bytes, bitstringTheory.length_pad_right,
          LENGTH_FLAT, bytes_in_word_def, MAP_MAP_o, o_DEF, ADD1, SUM_MAP_PLUS]
    \\ fs[Q.ISPEC`λx. 1n`SUM_MAP_K |> SIMP_RULE(srw_ss())[]]
    \\ EVAL_TAC)
  \\ strip_tac
  \\ first_assum(mp_then Any mp_tac (GEN_ALL ag32_halted))
  \\ simp[]
  \\ disch_then drule
  \\ imp_res_tac SUBSET_ffi_names_IMP_LENGTH_LESS_EQ
  \\ disch_then drule
  \\ disch_then(qspecl_then[`data`,`code`,`FUNPOW Next k ms`]mp_tac)
  \\ strip_tac
  \\ qexists_tac`k + startup_clock`
  \\ qx_gen_tac`k2` \\ strip_tac
  \\ first_x_assum(qspec_then`k2-k-startup_clock`mp_tac)
  \\ impl_tac
  >- (
    conj_tac
    >- (
      fs[Abbr`mc`]
      \\ fs[EVAL``(ag32_machine_config _ _ _).target.get_pc``]
      \\ fs[Abbr`ms`, FUNPOW_ADD]
      \\ fs[EVAL``(ag32_machine_config _ _ _).target.next``]
      \\ first_x_assum irule
      \\ fs[markerTheory.Abbrev_def] )
    \\ fs[Abbr`mc`]
    \\ fs[EVAL``(ag32_machine_config _ _ _).target.next``]
    \\ fs[Abbr`ms`, FUNPOW_ADD]
    \\ fs[EVAL``(ag32_machine_config _ _ _).target.get_byte``]
    \\ fs[ag32_targetTheory.is_ag32_init_state_def] \\ rfs[]
    \\ rw[]
    \\ qmatch_goalsub_rename_tac`_ = _ a`
    \\ `a ∉ ag32_startup_addresses`
    by (
      EVAL_TAC
      \\ ntac 2 (pop_assum mp_tac)
      \\ qpat_x_assum`_ < memory_size`mp_tac
      \\ EVAL_TAC
      \\ fs[FFI_codes_def]
      \\ Cases_on`a` \\ Cases_on`ms0.PC`
      \\ simp[word_add_n2w]
      \\ simp[word_ls_n2w, word_lo_n2w])
    \\ first_x_assum drule
    \\ disch_then(assume_tac o SYM) \\ simp[]
    \\ first_x_assum irule
    \\ Cases_on`a`
    \\ fs[ag32_machine_config_def, word_add_n2w, EVAL``ffi_jumps_offset``, EVAL``ffi_offset``, LENGTH_ag32_ffi_jumps]
    \\ qpat_x_assum`_ < memory_size`mp_tac
    \\ EVAL_TAC
    \\ fs[word_lo_n2w, word_ls_n2w, FFI_codes_def] \\ rfs[])
  \\ fs[GSYM FUNPOW_ADD, Abbr`ms`]
  \\ strip_tac
  \\ fs[EVAL``(ag32_machine_config _ _ _).target.next``,Abbr`mc`,FUNPOW_ADD]
  \\ fs[EVAL``(ag32_machine_config _ _ _).target.get_reg``]
  \\ fs[EVAL``(ag32_machine_config _ _ _).target.get_pc``]
  \\ fs[EVAL``(ag32_machine_config _ _ _).ptr_reg``]
  \\ fs[ag32_ffi_rel_def]
  \\ conj_tac
  >- (
    fs[EVAL``(ag32_machine_config _ _ _).target.get_byte``]
    \\ first_assum(mp_then Any mp_tac (GEN_ALL init_memory_halt))
    \\ disch_then(first_assum o mp_then Any mp_tac)
    \\ simp[]
    \\ disch_then(first_assum o mp_then Any mp_tac)
    \\ simp[ag32_machine_config_def]
    \\ disch_then(qspecl_then[`data`,`code`](SUBST1_TAC o SYM))
    \\ irule(GEN_ALL get_mem_word_change_mem)
    \\ qx_gen_tac `j`
    \\ strip_tac
    \\ qmatch_goalsub_abbrev_tac`m2 a = _`
    \\ qpat_x_assum`∀x. _ ⇒ m2 _ = _`(qspec_then`a`mp_tac)
    \\ impl_tac
    >- (
      simp[Abbr`a`]
      \\ qpat_x_assum`_ < memory_size`mp_tac
      \\ EVAL_TAC
      \\ fs[word_add_n2w, word_ls_n2w, word_lo_n2w] )
    \\ disch_then(SUBST1_TAC)
    \\ rfs[is_ag32_init_state_def]
    \\ first_x_assum irule
    \\ simp[Abbr`a`]
    \\ qpat_x_assum`_ < memory_size`mp_tac
    \\ EVAL_TAC
    \\ fs[word_add_n2w, word_ls_n2w, word_lo_n2w] )
  \\ conj_tac
  >- ( fs[IS_PREFIX_APPEND] \\ fs[markerTheory.Abbrev_def] )
  \\ strip_tac \\ fs[]
  \\ Cases_on`x` \\ fs[]
  \\ fs[markerTheory.Abbrev_def]
QED

val _ = export_theory();
