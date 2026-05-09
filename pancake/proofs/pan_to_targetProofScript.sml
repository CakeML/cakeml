(*

composing semantics correctness from pan to target

*)
Theory pan_to_targetProof
Ancestors
  backendProof stackProps stack_to_labProof lab_to_targetProof
  pan_to_wordProof pan_to_target wordConvsProof
Libs
  preamble blastLib[qualified]


Overload stack_remove_prog_comp[local] = ``stack_remove$prog_comp``
Overload stack_alloc_prog_comp[local] = ``stack_alloc$prog_comp``
Overload stack_names_prog_comp[local] = ``stack_names$prog_comp``
Overload word_to_word_compile[local] = ``word_to_word$compile``
Overload word_to_stack_compile[local] = ``word_to_stack$compile``
Overload stack_to_lab_compile[local] = ``stack_to_lab$compile``
Overload pan_to_word_compile_prog[local] = ``pan_to_word$compile_prog``

Definition pancake_good_code_def:
  pancake_good_code pan_code = EVERY good_panops pan_code
End

Theorem pan_to_lab_good_code_lemma:
  compile c.stack_conf c.data_conf lim1 lim2 offs stack_prog = code ∧
  compile asm_conf3 word_prog = (bm, wc, fs, stack_prog) ∧
  word_to_word$compile word_conf asm_conf3 word_prog0 = (col, word_prog) ∧
  compile_prog asm_conf3.ISA pan_prog = word_prog0 ∧
  stack_to_labProof$labels_ok code ∧
  all_enc_ok_pre conf code
  ⇒
  lab_to_targetProof$good_code conf LN code
Proof
  (* start of 'good_code' proof for initial compilation *)
  rw []
  \\ qmatch_asmsub_abbrev_tac `stack_to_labProof$labels_ok lab_prog`
  \\ fs[lab_to_targetProofTheory.good_code_def]
  \\ CONJ_TAC >- fs[Abbr `lab_prog`, stack_to_labTheory.compile_def]
  \\ CONJ_ASM1_TAC >- (
  fs [stack_to_labProofTheory.labels_ok_def]
  \\ qpat_x_assum `all_enc_ok_pre _ _` kall_tac
  \\ first_x_assum (fn t => mp_tac t \\ match_mp_tac EVERY_MONOTONIC)
  \\ simp[] \\ Cases \\ simp[]
  \\ metis_tac [labPropsTheory.EVERY_sec_label_ok]
  )
  \\ CONJ_TAC >- (
  fs [stack_to_labProofTheory.labels_ok_def]
  \\ qmatch_asmsub_abbrev_tac `ALL_DISTINCT (MAP ff _)`
  \\ `ff = Section_num` by
    (simp[Abbr`ff`,FUN_EQ_THM]>>Cases>>simp[])
  \\ fs [])
  \\ CONJ_TAC >- (
  fs [stack_to_labProofTheory.labels_ok_def]
  \\ first_x_assum (fn t => mp_tac t \\ match_mp_tac EVERY_MONOTONIC
  \\ simp[] \\ Cases \\ simp[] \\ NO_TAC)
  )
  \\ qpat_x_assum`Abbrev(lab_prog = _)` mp_tac
  \\ simp[markerTheory.Abbrev_def]
  \\disch_then (assume_tac o SYM)
  \\ drule stack_to_labProofTheory.stack_to_lab_stack_good_handler_labels
  \\ simp []
  \\ disch_then match_mp_tac
  \\ qmatch_asmsub_abbrev_tac ‘word_to_word$compile _ _ wprog’
  \\ pop_assum $ (assume_tac o GSYM o REWRITE_RULE [markerTheory.Abbrev_def])
  \\ drule pan_to_word_good_handlers
  \\ disch_tac
  \\ drule word_good_handlers_word_to_word
  \\ disch_then (qspecl_then [‘word_conf’, ‘asm_conf3’] assume_tac)
  \\ drule (INST_TYPE [beta|->alpha] word_to_stackProofTheory.word_to_stack_good_handler_labels)
  \\ strip_tac
  \\ pop_assum $ irule
  \\ simp []
  \\ qexists_tac ‘asm_conf3’>>gs[]
QED

(* move *)
Theorem word_to_stack_compile_FST:
  word_to_stack_compile mc.target.config wprog = (bitmaps,c'',fs,p) ⇒
  MAP FST p =
  raise_stub_location::store_consts_stub_location::MAP FST wprog
Proof
  strip_tac>>gs[word_to_stackTheory.compile_def]>>
  pairarg_tac>>gs[]>>rveq>>gs[]>>
  drule_then irule word_to_stackProofTheory.MAP_FST_compile_word_to_stack
QED

Theorem pan_to_stack_first_ALL_DISTINCT:
  pan_to_word_compile_prog mc.target.config.ISA pan_code = wprog0 ∧
  word_to_word_compile c.word_to_word_conf mc.target.config wprog0 = (col,wprog) ∧ mc.target.config.ISA ≠ Ag32 ∧
  word_to_stack_compile mc.target.config wprog = (bitmaps,c'',fs,p) ∧
  ALL_DISTINCT (MAP FST (functions pan_code)) ⇒
  ALL_DISTINCT (MAP FST p)
Proof
  strip_tac>>drule pan_to_wordProofTheory.first_compile_prog_all_distinct>>
  strip_tac>>
  drule backendProofTheory.compile_to_word_conventions2>>
  impl_tac
  >- (irule_at Any EVERY_MONOTONIC>>
      qexists ‘λ_. mc.target.config.ISA ≠ Ag32’>>
      simp[FORALL_PROD])>>
  strip_tac>>
  gs[]>>
  qpat_x_assum ‘MAP FST wprog = _’ $ assume_tac o GSYM>>gs[]>>
  drule word_to_stack_compile_FST>>
  strip_tac>>gs[]>>
  drule pan_to_wordProofTheory.pan_to_word_compile_prog_lab_min>>
  strip_tac>>
  gs[GSYM EVERY_MAP]>>EVAL_TAC>>gs[EVERY_MEM]>>
  rw[]>- (first_x_assum $ qspec_then ‘5’ assume_tac>>gs[])>>
  first_x_assum $ qspec_then ‘6’ assume_tac>>gs[]>>
  metis_tac[FST,SND,PAIR]
QED

Theorem pan_to_stack_compile_lab_pres:
  pan_to_word$compile_prog mc.target.config.ISA pan_code = wprog0 ∧
  word_to_word_compile c.word_to_word_conf mc.target.config wprog0 =(col,wprog) ∧ mc.target.config.ISA ≠ Ag32 ∧
  word_to_stack_compile mc.target.config wprog = (bitmaps,c'',fs,p) ∧
  ALL_DISTINCT (MAP FST (functions pan_code)) ⇒
  ALL_DISTINCT (MAP FST p) ∧
  EVERY (λn. n ≠ 0 ∧ n ≠ 1 ∧ n ≠ 2 ∧ n ≠ gc_stub_location) (MAP FST p) ∧
  EVERY
  (λ(n,p).
     (let
        labs = extract_labels p
      in
        EVERY (λ(l1,l2). l1 = n ∧ l2 ≠ 0 ∧ l2 ≠ 1) labs ∧
        ALL_DISTINCT labs)) p
Proof
  strip_tac>>
  drule pan_to_wordProofTheory.pan_to_word_compile_lab_pres>>strip_tac>>
  gs[]>>
  drule backendProofTheory.compile_to_word_conventions2>>
  impl_tac
  >- (irule_at Any EVERY_MONOTONIC>>
      qexists ‘λ_. mc.target.config.ISA ≠ Ag32’>>
      simp[FORALL_PROD])>>
  strip_tac>>
  drule pan_to_wordProofTheory.first_compile_prog_all_distinct>>
  strip_tac>>gs[]>>
  ‘EVERY
   (λ(n,m,p).
      (let
         labs = extract_labels p
       in
         EVERY (λ(l1,l2). l1 = n ∧ l2 ≠ 0 ∧ l2 ≠ 1) labs ∧
         ALL_DISTINCT labs)) wprog’
    by (gs[EVERY2_EVERY]>>gs[EVERY_EL]>>ntac 2 strip_tac>>
        ntac 3 (first_x_assum $ qspec_then ‘n’ assume_tac)>>
        pairarg_tac>>gs[EL_ZIP, wordConvsTheory.labels_rel_def]>>
        pairarg_tac>>gs[EL_MAP]>>strip_tac>>strip_tac>>
        ‘EL n (MAP FST wprog) = EL n (MAP FST wprog0)’ by rfs[]>>
        gs[EL_MAP]>>
        pairarg_tac>>gs[]>>
        ‘(l1, l2) ∈ set (extract_labels p'')’
          by (gs[MEM_SET_TO_LIST, SUBSET_DEF]>>
              first_assum irule>>metis_tac[MEM_EL])>>
        gs[MEM_EL]>>
        first_x_assum $ qspec_then ‘n''''’ assume_tac>>
        gs[]>>pairarg_tac>>gs[])>>
  drule (INST_TYPE [beta|->alpha] word_to_stackProofTheory.word_to_stack_compile_lab_pres)>>
  disch_then $ qspec_then ‘mc.target.config’ assume_tac>>
  drule_all pan_to_stack_first_ALL_DISTINCT>>
  strip_tac>>gs[]>>
  strip_tac>>gs[backend_commonTheory.stack_num_stubs_def]>>
  gs[backend_commonTheory.word_num_stubs_def,
     wordLangTheory.store_consts_stub_location_def,
     wordLangTheory.raise_stub_location_def,
     stackLangTheory.gc_stub_location_def,
     backend_commonTheory.stack_num_stubs_def]>>
  drule pan_to_wordProofTheory.pan_to_word_compile_prog_lab_min>>
  gs[GSYM EVERY_MAP, EVERY_MEM]>>ntac 3 strip_tac>>
  first_x_assum $ qspec_then ‘n’ assume_tac>>gs[]
QED

Theorem pan_to_lab_labels_ok:
  pan_to_word_compile_prog mc.target.config.ISA pan_code = wprog0 ∧
  word_to_word_compile c.word_to_word_conf mc.target.config wprog0 = (col,wprog) ∧ mc.target.config.ISA ≠ Ag32 ∧
  word_to_stack_compile mc.target.config wprog = (bitmaps,c'',fs,p) ∧
  stack_to_lab_compile c.stack_conf c.data_conf max_heap sp mc.target.config.addr_offset p = lprog ∧
  ALL_DISTINCT (MAP FST (functions pan_code)) ⇒
  labels_ok lprog
Proof
  strip_tac>>
  qpat_x_assum ‘_ = lprog’ (assume_tac o GSYM)>>gs[]>>
  irule stack_to_labProofTheory.stack_to_lab_compile_lab_pres>>
  drule_all pan_to_stack_compile_lab_pres>>gs[]
QED

(** stack_to_lab$good_code **)

Theorem word_to_stack_good_code_lemma:
  word_to_word_compile c.word_to_word_conf mc.target.config
  (pan_to_word_compile_prog mc.target.config.ISA pan_code) = (col,wprog) ∧
  mc.target.config.ISA ≠ Ag32 ∧
  word_to_stack_compile mc.target.config wprog = (bitmaps,c'',fs,p) ∧
  LENGTH mc.target.config.avoid_regs + 13 ≤ mc.target.config.reg_count ∧
  (* from backend_config_ok c *)
  ALL_DISTINCT (MAP FST (functions pan_code)) ⇒
  good_code (mc.target.config.reg_count −
             (LENGTH mc.target.config.avoid_regs + 3)) p
Proof
  (* a bit slow *)
  gs[stack_to_labProofTheory.good_code_def]>>strip_tac>>
  qmatch_asmsub_abbrev_tac ‘word_to_word_compile _ _ wprog0 = _’>>
  qpat_x_assum ‘Abbrev (wprog0 = _)’ (assume_tac o GSYM o REWRITE_RULE [markerTheory.Abbrev_def])>>
  drule_at (Pat ‘word_to_word_compile _ _ _ = _’) pan_to_stack_compile_lab_pres>>
  disch_then drule_all>>strip_tac>>gs[]>>
  drule backendProofTheory.compile_to_word_conventions2>>
  impl_tac
  >- (irule_at Any EVERY_MONOTONIC>>
      qexists ‘λ_. mc.target.config.ISA ≠ Ag32’>>
      simp[FORALL_PROD])>>
  strip_tac>>
  drule pan_to_wordProofTheory.first_compile_prog_all_distinct>>
  strip_tac>>gs[]>>
  drule word_to_stack_compile_FST>>strip_tac>>
  drule word_to_stackProofTheory.word_to_stack_stack_convs>>
  gs[]>>impl_tac
  >- (gs[EVERY_EL]>>
      ntac 2 strip_tac>>
      ntac 3 (first_x_assum $ qspec_then ‘n’ assume_tac)>>
      gs[]>>
      pairarg_tac>>gs[]>>
      pairarg_tac>>gs[]>>simp[EL_MAP])>>
  strip_tac>>gs[backend_commonTheory.stack_num_stubs_def]>>
  gs[EVERY_EL]>>rpt strip_tac>>
  pairarg_tac>>gs[EL_MAP]>>
  qpat_x_assum ‘∀n. _ ⇒ alloc_arg _’ $ qspec_then ‘n’ assume_tac>>
  gs[]>>

  drule pan_to_word_compile_prog_lab_min>>
  gs[GSYM EVERY_MAP]>>
  qpat_x_assum ‘MAP FST _ = MAP FST _’ $ assume_tac o GSYM>>
  gs[]>>
  gs[GSYM EVERY_MAP, EVERY_MEM]>>strip_tac>>
  ‘MEM k (MAP FST p)’
    by (gs[MEM_MAP]>>gs[MEM_EL]>>gs[PULL_EXISTS]>>
        first_assum $ irule_at (Pos last)>>gs[])>>
  gs[backend_commonTheory.word_num_stubs_def,
     wordLangTheory.store_consts_stub_location_def,
     wordLangTheory.raise_stub_location_def,
     backend_commonTheory.stack_num_stubs_def]>>
  first_x_assum $ qspec_then ‘k’ assume_tac>>gs[]
QED

(* move *)
Theorem good_dimindex_0w_8w:
  good_dimindex (:α) ⇒ (0w:α word) ≤ 8w ∧ -8w ≤ (0w:α word)
Proof
  strip_tac>>
  fs[WORD_LE,miscTheory.good_dimindex_def,word_2comp_n2w,
     dimword_def,word_msb_n2w]
QED

(* move *)
Theorem FLOOKUP_MAP_KEYS_LINV:
  f PERMUTES 𝕌(:α) ⇒
  FLOOKUP (MAP_KEYS (LINV f 𝕌(:α)) m) (i:α) = FLOOKUP m (f i)
Proof
  strip_tac>>
  drule BIJ_LINV_INV>>strip_tac>>
  drule BIJ_LINV_BIJ>>strip_tac>>
  gs[BIJ_DEF]>>
  mp_tac (GEN_ALL $ INST_TYPE [beta|->alpha,gamma|->beta] FLOOKUP_MAP_KEYS_MAPPED)>>
  disch_then $ qspecl_then [‘m’, ‘f i’, ‘LINV f 𝕌(:α)’] mp_tac>>
  gs[]>>
  last_x_assum assume_tac>>
  drule LINV_DEF>>
  disch_then $ qspec_then ‘i’ mp_tac>>
  impl_tac >- gs[]>>
  strip_tac>>pop_assum (fn h => rewrite_tac[h])
QED

(* move to stack_to_labProof *)
Theorem full_make_init_be:
  (FST(full_make_init a b c d e f g h i j k)).be ⇔ h.be
Proof
  fs[stack_to_labProofTheory.full_make_init_def]>>
  fs[stack_allocProofTheory.make_init_def]>>
  simp[stack_removeProofTheory.make_init_any_def,
       stack_removeProofTheory.make_init_opt_def]>>
  every_case_tac>>fs[]>>
  imp_res_tac stackPropsTheory.evaluate_consts>>
  EVAL_TAC>>fs[]>>
  EVAL_TAC>>fs[]
QED

Definition pan_installed_def:
  pan_installed bytes cbspace bitmaps data_sp ffi_names (r1,r2) (mc_conf:('a,'state,'b) machine_config) shmem_extra ms p_mem p_dom sdm' ⇔
  ∃t m io_regs cc_regs bitmap_ptr bitmaps_dm sdm.
  let heap_stack_dm = { w | t.regs r1 <=+ w ∧ w <+ t.regs r2 } in
    (∀a. a ∈ p_dom ⇒ m a = p_mem a) ∧
    good_init_state mc_conf ms bytes cbspace t m (heap_stack_dm ∪ bitmaps_dm) sdm io_regs cc_regs ∧ sdm' = sdm ∩ byte_aligned ∧
    byte_aligned (t.regs r1) /\

    byte_aligned (t.regs r2) /\
    byte_aligned bitmap_ptr /\
    t.regs r1 ≤₊ t.regs r2 /\
    1024w * bytes_in_word ≤₊ t.regs r2 - t.regs r1 /\
    DISJOINT heap_stack_dm bitmaps_dm ∧
    m (t.regs r1) = Word bitmap_ptr ∧
    m (t.regs r1 + bytes_in_word) =
    Word (bitmap_ptr + bytes_in_word * n2w (LENGTH bitmaps)) ∧
    m (t.regs r1 + 2w * bytes_in_word) =
    Word (bitmap_ptr + bytes_in_word * n2w data_sp +
          bytes_in_word * n2w (LENGTH bitmaps)) ∧
    m (t.regs r1 + 3w * bytes_in_word) =
    Word (mc_conf.target.get_pc ms + n2w (LENGTH bytes)) ∧
    m (t.regs r1 + 4w * bytes_in_word) =
    Word (mc_conf.target.get_pc ms + n2w cbspace + n2w (LENGTH bytes)) ∧
    (word_list bitmap_ptr (MAP Word bitmaps) *
     word_list_exists (bitmap_ptr + bytes_in_word * n2w (LENGTH bitmaps)) data_sp)
    (fun2set (m,byte_aligned ∩ bitmaps_dm)) ∧
    ffi_names = SOME mc_conf.ffi_names ∧
    (!i. mmio_pcs_min_index mc_conf.ffi_names = SOME i ==>
         MAP (\rec. w2n (mc_conf.target.get_pc ms) + rec.entry_pc) shmem_extra =
         DROP i (MAP w2n mc_conf.ffi_entry_pcs) ∧
         mc_conf.mmio_info =
         ZIP (GENLIST (λindex. index + i) (LENGTH shmem_extra),
             (MAP (λrec. (rec.nbytes, Addr rec.addr_reg (n2w rec.addr_off), rec.reg,
                        n2w rec.exit_pc + mc_conf.target.get_pc ms))
                                                           shmem_extra)) ∧
    cbspace + LENGTH bytes + ffi_offset * (i + 3) < dimword (:'a))
End

Theorem pan_installed_imp_installed:
  pan_installed bytes cbspace bitmaps data_sp ffi_names (r1,r2) mc_conf shmem_extra ms p_mem p_dom sdm ⇒
  installed bytes cbspace bitmaps data_sp ffi_names (r1,r2) mc_conf shmem_extra ms
Proof
  rw[pan_installed_def, targetSemTheory.installed_def]>>
  metis_tac[]
QED

(* memory update *)
Theorem fun2set_update_eq[simp]:
  fun2set (m, md) = fun2set (m', md) ⇒
  fun2set (m⦇x ↦ a⦈, md) = fun2set (m'⦇x ↦ a⦈, md)
Proof
  strip_tac>>
  gs[set_sepTheory.fun2set_eq,UPDATE_def]>>
  IF_CASES_TAC>>gs[]
QED

Theorem get_var_const_memory[simp]:
  wordSem$get_var x (y with memory := m) = get_var x y
Proof
  gs[wordSemTheory.get_var_def]
QED

Theorem set_var_const_memory[simp]:
  wordSem$set_var v x (y with memory := m) = (set_var v x y) with memory := m
Proof
  gs[wordSemTheory.set_var_def]
QED

Theorem unset_var_const_memory[simp]:
  wordSem$unset_var v (y with memory := m) = (unset_var v y) with memory := m
Proof
  gs[wordSemTheory.unset_var_def]
QED

Theorem get_vars_const_memory[simp]:
  wordSem$get_vars x (y with memory := m) = get_vars x y
Proof
  Induct_on`x`>>srw_tac[][wordSemTheory.get_vars_def]
QED

Theorem set_vars_const_memory[simp]:
  wordSem$set_vars vs xs (y with memory := m) = (set_vars vs xs y) with memory := m
Proof
  Induct_on`xs`>>srw_tac[][wordSemTheory.set_vars_def]
QED

Theorem get_var_imm_const_memory[simp]:
  wordSem$get_var_imm ri (s with memory := m) = get_var_imm ri s
Proof
  Cases_on ‘ri’>>gs[wordSemTheory.get_var_imm_def]
QED

Theorem mem_load_const_memory[simp]:
  fun2set (s.memory,s.mdomain) = fun2set (m,s.mdomain) ⇒
  wordSem$mem_load ad (s with memory := m) = mem_load ad s
Proof
  strip_tac>>gs[wordSemTheory.mem_load_def]>>
  IF_CASES_TAC>>gs[set_sepTheory.fun2set_eq]
QED

Theorem mem_store_const_memory[simp]:
  fun2set (s.memory,s.mdomain) = fun2set (m,s.mdomain) ⇒
  (mem_store ad w s = NONE ⇔ wordSem$mem_store ad w (s with memory := m) = NONE) ∧
  (mem_store ad w s = SOME (s with memory:= s.memory⦇ad↦w⦈) ⇔
     wordSem$mem_store ad w (s with memory := m) =
     SOME (s with memory := m⦇ad↦w⦈))
Proof
  strip_tac>>gs[wordSemTheory.mem_store_def]
QED

Theorem mem_load_32_const_memory[simp]:
  fun2set (m,dm) = fun2set (m',dm) ⇒
  wordSem$mem_load_32 m dm be ad = mem_load_32 m' dm be ad
Proof
  strip_tac>>gs[wordSemTheory.mem_load_32_alt]>>
  rpt (TOP_CASE_TAC>>gs[set_sepTheory.fun2set_eq])>>
  last_x_assum $ qspec_then ‘byte_align ad’ assume_tac>>gvs[]
QED

Theorem mem_store_32_const_memory:
  fun2set (m, dm) = fun2set (m', dm) ⇒
  (mem_store_32 m dm be ad hw = NONE ⇔ wordSem$mem_store_32 m' dm be ad hw = NONE) ∧
  (fun2set (THE (mem_store_32 m dm be ad hw), dm) =
    fun2set (THE (wordSem$mem_store_32 m' dm be ad hw), dm))
Proof
  strip_tac>>gs[wordSemTheory.mem_store_32_alt]>>
  rpt (TOP_CASE_TAC>>gs[set_sepTheory.fun2set_eq])>>
  rpt strip_tac>>
  simp[APPLY_UPDATE_THM]
QED

Theorem word_exp_const_memory[simp]:
  ∀s exp m.
  fun2set (s.memory,s.mdomain) = fun2set (m, s.mdomain) ⇒
  wordSem$word_exp (s with memory := m) exp = word_exp s exp
Proof
  recInduct wordSemTheory.word_exp_ind>>rw[wordSemTheory.word_exp_def]>>
  fs[PULL_FORALL]>>fs[Once SWAP_FORALL_THM]>>
  first_x_assum $ qspec_then ‘m’ assume_tac>>gs[]>>
  ‘the_words (MAP (λa. word_exp (s with memory := m) a) wexps) =
   the_words (MAP (λa. word_exp s a) wexps)’
    by (Induct_on ‘wexps’>>gs[]>>rpt strip_tac>>gs[]>>
        Cases_on ‘word_exp s h’>>gs[]>>
        gs[wordSemTheory.the_words_def])>>gs[]
QED

Theorem mem_load_byte_aux_const_memory[simp]:
  fun2set (m,dm) = fun2set (m',dm) ⇒
  wordSem$mem_load_byte_aux m' dm be w =
  mem_load_byte_aux m dm be w
Proof
  strip_tac>>gs[wordSemTheory.mem_load_byte_aux_def]>>
  gs[set_sepTheory.fun2set_eq]>>
  first_x_assum $ qspec_then ‘byte_align w’ assume_tac>>
  rpt (CASE_TAC>>gs[])
QED

Theorem mem_store_byte_aux_const_memory:
  fun2set (m,dm) = fun2set (m',dm) ⇒
  (mem_store_byte_aux m dm be w b = NONE ⇔
     mem_store_byte_aux m' dm be w b = NONE) ∧
  (fun2set (THE (wordSem$mem_store_byte_aux m' dm be w b),dm) =
   fun2set (THE (mem_store_byte_aux m dm be w b), dm))
Proof
  gs[set_sepTheory.fun2set_eq]>>rpt strip_tac>>
  gs[wordSemTheory.mem_store_byte_aux_def]
  >- (first_x_assum $ qspec_then ‘byte_align w’ assume_tac>>
      rpt (CASE_TAC>>gs[]))>>
  first_assum $ qspec_then ‘a’ assume_tac>>
  first_x_assum $ qspec_then ‘byte_align w’ assume_tac>>
  rpt (CASE_TAC>>gs[])>>gs[UPDATE_def]>>IF_CASES_TAC>>gs[]
QED

Theorem read_bytearray_const_memory[simp]:
  fun2set (m,dm) = fun2set (m',dm) ⇒
  misc$read_bytearray ptr len (mem_load_byte_aux m dm be) =
  read_bytearray ptr len (mem_load_byte_aux m' dm be)
Proof
  strip_tac>>
  imp_res_tac mem_load_byte_aux_const_memory>>
  metis_tac[]
QED

Theorem write_bytearray_const_memory[simp]:
  ∀ls ptr m.
  fun2set (m,dm) = fun2set (m',dm) ⇒
  fun2set (wordSem$write_bytearray ptr ls m dm be, dm) =
  fun2set (write_bytearray ptr ls m' dm be, dm)
Proof
  Induct>>gs[wordSemTheory.write_bytearray_def]>>
  rpt strip_tac>>gs[]>>
  first_x_assum $ qspecl_then [‘ptr+1w’, ‘m’] assume_tac>>rfs[]>>
  drule mem_store_byte_aux_const_memory>>strip_tac>>
  first_x_assum $ qspecl_then [‘ptr’, ‘be’, ‘h’] assume_tac>>fs[]>>
  rpt (CASE_TAC>>fs[])
QED

Theorem inst_const_memory:
  fun2set (s.memory,s.mdomain) = fun2set (m, s.mdomain) ⇒
  (inst i s = NONE ⇔ wordSem$inst i (s with memory := m) = NONE) ∧
  (inst i s ≠ NONE ⇒
   (∃m'. THE (wordSem$inst i (s with memory := m)) =
         (THE (inst i s)) with memory := m' ∧
         (let x = THE (inst i s) in
            fun2set (x.memory,x.mdomain) = fun2set (m',x.mdomain))))
Proof
  (* a bit slow *)
  Induct_on ‘i’>>gs[wordSemTheory.inst_def]>>
  strip_tac
  >- metis_tac[]
  >- (ntac 2 strip_tac>>
      gs[wordSemTheory.assign_def, wordSemTheory.set_var_def]>>
      CASE_TAC>>gs[word_exp_const_memory]>>gvs[]>>metis_tac[])
  >- (rpt strip_tac>>
      gs[wordSemTheory.assign_def, wordSemTheory.set_var_def]>>
      rpt (CASE_TAC>>fs[])>>
      gs[]>>rpt (FULL_CASE_TAC>>gs[])>>gvs[]>>metis_tac[])
  >- (rpt strip_tac>>
      rpt (CASE_TAC>>gs[])>>
      imp_res_tac mem_load_byte_aux_const_memory>>gs[]>>
      imp_res_tac mem_store_byte_aux_const_memory>>gs[]>>
      imp_res_tac mem_store_32_const_memory>>gs[]>>
      imp_res_tac mem_load_32_const_memory>>gs[]>>
      imp_res_tac mem_store_const_memory>>gs[]>>
      imp_res_tac mem_load_const_memory>>gs[]>>
      ntac 2 $ first_x_assum $ qspecl_then [‘w2w c’, ‘s.be’, ‘c''’] assume_tac>>
      ntac 2 $ first_x_assum $ qspecl_then [‘c''’, ‘s.be’, ‘w2w c’] assume_tac>>
      gs[wordSemTheory.set_var_def]>>
      gs[wordSemTheory.mem_store_def]>>
      rpt (FULL_CASE_TAC>>gs[])>>gvs[]>>TRY (metis_tac[])>>
      irule_at Any fun2set_update_eq>>gs[]>>metis_tac[])>>
  rpt strip_tac>>
  gs[wordSemTheory.get_fp_var_def,
     wordSemTheory.set_fp_var_def,
     wordSemTheory.get_var_def,
     wordSemTheory.set_var_def]>>
  rpt (CASE_TAC>>gs[])>>gvs[]>>
  rpt (FULL_CASE_TAC>>gs[])>>gvs[]>>
  metis_tac[]
QED

Theorem const_writes_const_memory:
  ∀c' c words m m' md.
  fun2set (m,md) = fun2set (m',md) ⇒
  fun2set (wordSem$const_writes c' c words m,md) =
  fun2set (wordSem$const_writes c' c words m',md)
Proof
  Induct_on ‘words’>>srw_tac[][wordSemTheory.const_writes_def]>>
  rename1 ‘h::words’>>Cases_on ‘h’>>
  gs[wordSemTheory.const_writes_def]
QED

Theorem share_inst_const_memory[simp]:
  ∀s op v c m.
  fun2set (s.memory,s.mdomain) = fun2set (m, s.mdomain) ∧
  share_inst op v c s = (res, t) ⇒
  t.memory = s.memory ∧ t.mdomain = s.mdomain ∧
  share_inst op v c (s with memory := m) = (res, t with memory := m)
Proof
  rpt strip_tac>>Cases_on ‘op’>>
  gs[wordSemTheory.share_inst_def,
     wordSemTheory.sh_mem_load_def,
     wordSemTheory.sh_mem_load_byte_def,
     wordSemTheory.sh_mem_load16_def,
     wordSemTheory.sh_mem_load32_def,
     wordSemTheory.sh_mem_store_def,
     wordSemTheory.sh_mem_store_byte_def,
     wordSemTheory.sh_mem_store16_def,
     wordSemTheory.sh_mem_store32_def,
     ffiTheory.call_FFI_def]>>
  every_case_tac>>gvs[]>>
  fs[wordSemTheory.sh_mem_set_var_def,
     wordSemTheory.set_var_def,
     wordSemTheory.flush_state_def]>>gvs[]
QED

Theorem mem_upd_lemma[local]:
  ((s : ('a, 'b, 'c) wordSem$state) with memory := ARB) = (t with memory := ARB) ==>
  ?m. s = (t with memory := m)
Proof
  simp [wordSemTheory.state_component_equality]
QED

Theorem push_env_mem_upd[local]:
  ! env params s.
  push_env env params (s with memory := m) =
  (push_env env params s with memory := m)
Proof
  recInduct wordSemTheory.push_env_ind
  \\ simp [wordSemTheory.push_env_def]
  \\ rw []
  \\ rpt (pairarg_tac \\ fs [])
  \\ fs []
QED

Theorem push_env_mem_const[local]:
  ! env params s.
  (push_env env params s).memory = s.memory /\
  (push_env env params s).mdomain = s.mdomain
Proof
  recInduct wordSemTheory.push_env_ind
  \\ simp [wordSemTheory.push_env_def]
  \\ rw []
  \\ rpt (pairarg_tac \\ fs [])
  \\ fs []
QED

Theorem cut_state_with_mem_const[local]:
  cut_state x ((s:('a, 'b, 'c) wordSem$state) with memory := m) =
  OPTION_MAP (λs'. s' with memory := m) (cut_state x s)
Proof
  simp [wordSemTheory.cut_state_def]
  \\ Cases_on ‘cut_env x s.locals’ \\ simp []
QED

(* memory update lemma for evaluate *)
Theorem memory_swap_lemma1[local]:
  ∀prog st res rst m.
  wordSem$evaluate (prog, (st:(α,β,γ) wordSem$state)) = (res, rst) ∧
  fun2set (st.memory, st.mdomain) = fun2set (m, st.mdomain) ∧
  no_alloc_code st.code ∧ no_install_code st.code ∧
  no_alloc prog ∧ no_install prog ⇒
  (∃st'. evaluate (prog, st with memory := m) = (res, st') /\
        (st' with memory := ARB) = (rst with memory := ARB) /\
        fun2set (rst.memory, rst.mdomain) = fun2set (st'.memory, rst.mdomain))
Proof
  recInduct (name_ind_cases [] wordSemTheory.evaluate_ind)
  \\ srw_tac [] [wordSemTheory.evaluate_def]
  \\ (TRY (qpat_assum ‘no_install (Loop _ _ _)’ mp_tac
           \\ simp [Once wordConvsTheory.no_install_def] \\ strip_tac))
  \\ fs [wordSemTheory.call_env_def, wordConvsTheory.no_alloc_def,
    wordConvsTheory.no_install_def, wordSemTheory.flush_state_def,
    wordSemTheory.dec_clock_def]
  >~ [`Case (Inst i, _)`]
  >- (
    imp_res_tac inst_const_memory
    \\ fs [CaseEq "option"] \\ gvs []
    \\ rpt (first_x_assum (qspec_then `i` assume_tac))
    \\ gs [GSYM IS_SOME_EQ_NOT_NONE, IS_SOME_EXISTS]
  )
  >~ [`Case (MustTerminate _, _)`]
  >- (
    fs [UNCURRY_eq_pair, CaseEq "bool"] \\ gvs []
    \\ first_x_assum (qspec_then `m` assume_tac) \\ fs []
    \\ imp_res_tac mem_upd_lemma
    \\ gs []
  )
  >~ [`Case (Seq _ _, _)`]
  >- (
    gs [UNCURRY_eq_pair]
    \\ first_x_assum (qspec_then `m` assume_tac)
    \\ gs [CaseEq "bool"]
    \\ imp_res_tac mem_upd_lemma
    \\ fs []
    \\ imp_res_tac wordPropsTheory.no_install_evaluate_const_code
    \\ fs []
  )
  >~ [`Case (Raise _, rst)`]
  >- (
    fs [CaseEq "option"] \\ gvs []
    \\ fs [wordSemTheory.jump_exc_def, CaseEq "list"]
    \\ Cases_on `rst.handler < LENGTH rst.stack` \\ fs []
    \\ gvs []
    \\ every_case_tac \\ fs []
    \\ gvs []
  )
  >~ [`Case (FFI _ _ _ _ _ _, _)`]
  >- (
    fs [CaseEq "option", CaseEq "word_loc"] \\ gvs []
    \\ imp_res_tac read_bytearray_const_memory
    \\ gs []
    \\ every_case_tac \\ gvs []
  )
  >~ [`Case (ShareInst _ _ _, _)`]
  >- (
    fs [CaseEq "option", CaseEq "word_loc"] \\ gvs []
    \\ drule_all share_inst_const_memory
    \\ SIMP_TAC bool_ss []
    \\ simp []
  )
  >~ [`Case (Call _ _ _ _, _)`]
  >- (
    fs [CaseEq "option", CaseEq "word_loc", CaseEq "bool"] \\ gvs []
    \\ fs [CaseEq "prod"] \\ gvs []
    \\ drule wordPropsTheory.no_alloc_find_code
    \\ drule_at (Pos (el 2)) wordPropsTheory.no_install_find_code
    \\ simp [] \\ rpt strip_tac
    \\ fs [CaseEq "option", CaseEq "bool", CaseEq "prod"] \\ gvs []
    \\ fs [CaseEq "wordSem$result"] \\ gvs []
    \\ fs [push_env_mem_upd, push_env_mem_const]
    \\ last_x_assum (qspec_then `m` assume_tac)
    \\ gs[wordSemTheory.pop_env_def, wordSemTheory.set_var_def,
          wordSemTheory.set_vars_def, alist_insert_def]
    \\ fs [AllCaseEqs ()] \\ gvs []
    \\ imp_res_tac mem_upd_lemma \\ gs []
    \\ imp_res_tac wordPropsTheory.no_install_evaluate_const_code
    \\ gvs [PULL_EXISTS,SF DNF_ss]
  )
  >~ [`Case (Loop _ _ _, _)`]
  >- suspend "Loop"
  \\ (
    fs [wordSemTheory.get_var_def, wordSemTheory.set_var_def,
        wordSemTheory.unset_var_def, CaseEq "option", CaseEq "word_loc", CaseEq "bool",
        get_vars_const_memory, UNCURRY_eq_pair]
    \\ gvs []
    \\ imp_res_tac  mem_upd_lemma
    \\ gs [wordSemTheory.set_vars_def, wordSemTheory.set_store_def,
        const_writes_const_memory, wordSemTheory.mem_store_def]
    \\ gvs []
    \\ NO_TAC
  )
QED

Resume memory_swap_lemma1[Loop]:
  Cases_on ‘cut_state (names,LN) s’ \\ gvs []
  >- (qexists_tac ‘rst with memory := m’
      \\ simp [cut_state_with_mem_const,
               wordSemTheory.state_component_equality])
  \\ Cases_on ‘wordSem$evaluate (c,x)’ \\ gvs []
  \\ subgoal ‘fun2set (x.memory,x.mdomain) = fun2set (m,x.mdomain) ∧
              no_alloc_code x.code ∧ no_install_code x.code’
  >- (imp_res_tac wordPropsTheory.cut_state_const \\ gvs [])
  \\ first_x_assum (qspec_then ‘m’ mp_tac) \\ fs []
  \\ disch_then (qx_choose_then ‘st_v’ strip_assume_tac)
  \\ qabbrev_tac ‘mem' = st_v.memory’
  \\ subgoal ‘st_v = r with memory := mem'’
  >- (qpat_x_assum ‘st_v with memory := ARB = _ with memory := ARB’ mp_tac
      \\ simp [Abbr ‘mem'’, wordSemTheory.state_component_equality])
  \\ pop_assum SUBST_ALL_TAC
  \\ simp [cut_state_with_mem_const]
  \\ Cases_on ‘cont_loop q’ \\ gvs []
  >- (
    Cases_on ‘r.clock = 0’ \\ gvs []
    >- (
      first_x_assum (qspec_then ‘mem'’ mp_tac)
      \\ impl_tac
      >- (subgoal ‘x.code = r.code’
          >- (qspecl_then [‘c’,‘x’,‘q’,‘r’]
                mp_tac wordPropsTheory.no_install_evaluate_const_code
              \\ simp [])
          \\ simp [wordSemTheory.STOP_def, stackSemTheory.STOP_def,
                   Once wordConvsTheory.no_alloc_def,
                   Once wordConvsTheory.no_install_def]
          \\ gvs [])
      \\ disch_then (qx_choose_then ‘st_loop’ strip_assume_tac)
      \\ qexists_tac ‘st_loop’
      \\ gvs []
    )
    \\ qexists_tac ‘r with <|locals := LN; locals_size := SOME 0;
                             store := FEMPTY; stack := []; memory := mem'|>’
    \\ simp [wordSemTheory.state_component_equality]
  )
  \\ Cases_on ‘q = SOME (Break 0)’ \\ gvs []
  >- (
    Cases_on ‘cut_state (exit_names,LN) r’ \\ gvs []
    >- (imp_res_tac wordPropsTheory.cut_state_const \\ gvs [])
    \\ qexists_tac ‘r with memory := mem'’
    \\ simp [wordSemTheory.state_component_equality]
  )
  \\ qexists_tac ‘r with memory := mem'’
  \\ simp [wordSemTheory.state_component_equality]
QED

Finalise memory_swap_lemma1;

(* avoid changing subsequent proof by rephrasing back into earlier form *)
Theorem memory_swap_lemma[local]:
  ∀prog st res rst m.
  wordSem$evaluate (prog, (st:(α,β,γ) wordSem$state)) = (res, rst) ∧
  fun2set (st.memory, st.mdomain) = fun2set (m, st.mdomain) ∧
  no_alloc_code st.code ∧ no_install_code st.code ∧
  no_alloc prog ∧ no_install prog ⇒
  (∃m'. evaluate (prog, st with memory := m) = (res, rst with memory := m') ∧
        fun2set (rst.memory, rst.mdomain) = fun2set (m', rst.mdomain))
Proof
  rw []
  \\ drule_all memory_swap_lemma1
  \\ rw []
  \\ imp_res_tac  mem_upd_lemma
  \\ simp []
  \\ metis_tac []
QED

Theorem word_semantics_memory_update:
  fun2set (s.memory,s.mdomain) = fun2set (m,s.mdomain) ∧
  no_alloc_code s.code ∧ no_install_code s.code ⇒
  wordSem$semantics ((s with memory := m):(α,β,'ffi) wordSem$state) start ≠ Fail ⇒
  wordSem$semantics s start =
  wordSem$semantics ((s with memory := m):(α,β,'ffi) wordSem$state) start
Proof
  strip_tac>>
  gs[wordSemTheory.semantics_def]>>
  IF_CASES_TAC >> full_simp_tac(srw_ss())[] >>
  DEEP_INTRO_TAC some_intro >> simp[] >>
  strip_tac>>
  strip_tac
  >- (strip_tac>>gs[]>>
      IF_CASES_TAC>>gs[]
      >- (Cases_on ‘r=SOME TimeOut’>>gs[]>>
          qmatch_asmsub_abbrev_tac ‘FST ev’>>
          Cases_on ‘ev’>>gs[]>>rename1 ‘(q,r')’>>
          drule memory_swap_lemma>>
          fs[wordConvsTheory.no_alloc_def,
             wordConvsTheory.no_install_def]>>
          qexists_tac ‘m’>>gs[]>>
          strip_tac>>strip_tac>>
          ‘q = r’
            by (Cases_on ‘k < k'’>>gs[]
                >- (qpat_x_assum ‘evaluate _ = (r, _)’ assume_tac>>
                    drule wordPropsTheory.evaluate_add_clock>>
                    strip_tac>>pop_assum $ qspec_then ‘k' - k’ assume_tac>>gs[])>>
                gs[NOT_LESS]>>
                drule wordPropsTheory.evaluate_add_clock>>
                strip_tac>>pop_assum $ qspec_then ‘k - k'’ assume_tac>>gs[]>>
                Cases_on ‘q’>>rename1 ‘SOME x'’>>Cases_on ‘x'’>>gs[])>>
          Cases_on ‘r’>>rename1 ‘SOME x'’>>Cases_on ‘x'’>>gs[]>>
          first_x_assum $ qspec_then ‘k'’ assume_tac>>gs[])>>
      DEEP_INTRO_TAC some_intro >> simp[] >>
      strip_tac

      >- (strip_tac>>
          first_x_assum $ qspec_then ‘k’ assume_tac>>
          qmatch_asmsub_abbrev_tac ‘FST ev’>>
          Cases_on ‘ev’>>gs[]>>rename1 ‘(q,r')’>>
          drule memory_swap_lemma>>fs[]>>
          fs[wordConvsTheory.no_alloc_def,
             wordConvsTheory.no_install_def]>>
          disch_then $ qspec_then ‘m’ assume_tac>>gs[]>>
          strip_tac>>gs[]>>
          Cases_on ‘r'' = SOME TimeOut’>>gs[]>>
          Cases_on ‘q = SOME TimeOut’>>gs[]>>
          ‘q = r'' ∧ t'.ffi.io_events = r'.ffi.io_events’
            by (Cases_on ‘k < k'’>>gs[]
                >- (qpat_x_assum ‘evaluate _ = (q, _)’ assume_tac>>
                    drule wordPropsTheory.evaluate_add_clock>>
                    strip_tac>>pop_assum $ qspec_then ‘k' - k’ assume_tac>>gs[])>>
                gs[NOT_LESS]>>
                drule wordPropsTheory.evaluate_add_clock>>
                strip_tac>>pop_assum $ qspec_then ‘k - k'’ assume_tac>>gs[])>>gs[]>>
          Cases_on ‘r''’>>gs[]>>rename1 ‘SOME x''’>>Cases_on ‘x''’>>gs[])>>
      first_x_assum $ qspec_then ‘k’ assume_tac>>
      qmatch_asmsub_abbrev_tac ‘FST ev’>>
      Cases_on ‘ev’>>gs[]>>rename1 ‘(q,r')’>>
      qexists_tac ‘k’>>gs[]>>
      drule memory_swap_lemma>>fs[]>>
      fs[wordConvsTheory.no_alloc_def,
         wordConvsTheory.no_install_def]>>
      disch_then $ qspec_then ‘m’ assume_tac>>gs[]>>metis_tac[])>>
  IF_CASES_TAC>>gs[]
  >- (qmatch_asmsub_abbrev_tac ‘FST ev’>>
      Cases_on ‘ev’>>gs[]>>rename1 ‘(q,r)’>>
      drule memory_swap_lemma>>fs[]>>
      fs[wordConvsTheory.no_alloc_def,
         wordConvsTheory.no_install_def]>>
      qexists_tac ‘m’>>gs[]>>
      strip_tac>>
      strip_tac>>
      last_x_assum $ qspec_then ‘k’ assume_tac>>gs[]>>
      last_x_assum $ qspec_then ‘k’ assume_tac>>gs[])>>
  DEEP_INTRO_TAC some_intro >> simp[] >>
  strip_tac>>strip_tac
  >- (strip_tac>>
      drule memory_swap_lemma>>fs[]>>
      fs[wordConvsTheory.no_alloc_def,
         wordConvsTheory.no_install_def]>>
      qexists_tac ‘m’>>gs[]>>
      strip_tac>>
      strip_tac>>gs[]>>
      last_x_assum $ qspec_then ‘k’ assume_tac>>gs[]>>
      last_x_assum $ qspec_then ‘k’ assume_tac>>gs[])>>
  irule lprefix_lubTheory.IMP_build_lprefix_lub_EQ>>
  conj_tac
  >- (rw[lprefix_chain_def]>>
      Cases_on ‘k < k'’
      >- (irule OR_INTRO_THM1>>gs[LPREFIX_fromList]>>
          gs[from_toList]>>
          irule IS_PREFIX_TRANS>>
          irule_at Any wordPropsTheory.evaluate_add_clock_io_events_mono>>gs[]>>
          qexists_tac ‘k' - k’>>gs[])>>
      irule OR_INTRO_THM2>>gs[LPREFIX_fromList]>>
      gs[from_toList]>>
      irule IS_PREFIX_TRANS>>
      irule_at Any wordPropsTheory.evaluate_add_clock_io_events_mono>>gs[]>>
      qexists_tac ‘k - k'’>>gs[])>>
  conj_tac
  >- (rw[lprefix_chain_def]>>
      Cases_on ‘k < k'’
      >- (irule OR_INTRO_THM1>>gs[LPREFIX_fromList]>>
          gs[from_toList]>>
          irule IS_PREFIX_TRANS>>
          irule_at Any wordPropsTheory.evaluate_add_clock_io_events_mono>>gs[]>>
          qexists_tac ‘k' - k’>>gs[])>>
      irule OR_INTRO_THM2>>gs[LPREFIX_fromList]>>
      gs[from_toList]>>
      irule IS_PREFIX_TRANS>>
      irule_at Any wordPropsTheory.evaluate_add_clock_io_events_mono>>gs[]>>
      qexists_tac ‘k - k'’>>gs[])>>
  conj_tac
  >- (gs[lprefix_rel_def]>>strip_tac>>strip_tac>>gs[LPREFIX_fromList]>>
      irule_at Any EQ_REFL>>gs[from_toList]>>
      qmatch_goalsub_abbrev_tac ‘SND ev’>>
      Cases_on ‘ev’>>gs[]>>
      qexists_tac ‘k’>>gs[]>>
      drule memory_swap_lemma>>gs[]>>strip_tac>>
      fs[wordConvsTheory.no_alloc_def,
         wordConvsTheory.no_install_def]>>
      first_x_assum $ qspec_then ‘m’ assume_tac>>gs[])>>
  gs[lprefix_rel_def]>>strip_tac>>strip_tac>>gs[LPREFIX_fromList]>>
  irule_at Any EQ_REFL>>gs[from_toList]>>
  qexists_tac ‘k’>>gs[]>>
  qpat_abbrev_tac ‘ev = evaluate (Call _ _ _ _, s with clock := _)’>>
  Cases_on ‘ev’>>gs[]>>
  drule memory_swap_lemma>>gs[]>>strip_tac>>
  fs[wordConvsTheory.no_alloc_def,
     wordConvsTheory.no_install_def]>>
  first_x_assum $ qspec_then ‘m’ assume_tac>>gs[]
QED

(* accounting for the resources *)

Theorem word_to_word_compile_no_install_no_alloc:
  word_to_word$compile wconf aconf progs0 = (col, progs) ∧
  ALL_DISTINCT (MAP FST progs0) ∧
  no_mt_code (fromAList progs0) ∧
  no_install_code (fromAList progs0) ⇒
  no_install_code (fromAList progs) ∧
  (no_alloc_code (fromAList progs0) ⇒ no_alloc_code (fromAList progs))
Proof
  strip_tac>>gs[word_to_wordTheory.compile_def]>>
  rpt (pairarg_tac>>gs[])>>
  gvs[]>>
  DEP_REWRITE_TAC[word_to_wordProofTheory.no_mt_code_full_compile_single]>>
  simp []>>
  conj_asm1_tac >- (
    fs[word_to_wordTheory.next_n_oracle_def]>>every_case_tac>>gvs[]
  )>>
  fs[wordPropsTheory.no_install_code_def, wordPropsTheory.no_alloc_code_def,
        lookup_fromAList]>>
  fs[wordConvsTheory.no_install_subprogs_def,
        wordConvsTheory.no_alloc_subprogs_def]>>
  rw[]>>drule ALOOKUP_MEM>>strip_tac>>
  gs[PAIR_FST_SND_EQ, MEM_MAP]>>
  irule wordConvsProofTheory.compile_single_not_created_subprogs>>
  first_x_assum irule>>
  gs[MEM_ZIP]>>
  drule_at Any ALOOKUP_ALL_DISTINCT_EL>>
  rw[]>>
  drule_then (irule_at Any) EQ_TRANS>>
  simp[PAIR_FST_SND_EQ]
QED

Theorem no_alloc_word_evaluate:
  ∀prog s res t.
  wordSem$evaluate (prog,s) = (res,t) ∧
  no_install_code s.code ∧ no_alloc_code s.code ∧
  no_install prog ∧ no_alloc prog ⇒
  res ≠ SOME NotEnoughSpace
Proof
  recInduct (name_ind_cases [] wordSemTheory.evaluate_ind)>>
  rw[wordConvsTheory.no_alloc_def,
     wordConvsTheory.no_install_def,
     wordConvsTheory.no_mt_def,
     wordSemTheory.evaluate_def]
  >~ [`Case (Call _ _ _ _, _)`]
  >- (
    fs [CaseEq "option", CaseEq "word_loc", CaseEq "bool"] >> gvs [] >>
    fs [CaseEq "prod"] >> gvs [] >>
    drule wordPropsTheory.no_alloc_find_code >>
    drule_at (Pos (el 2)) wordPropsTheory.no_install_find_code >>
    CCONTR_TAC >> gs [] >>
    fs [CaseEq "option", CaseEq "bool", CaseEq "prod"] >>
    imp_res_tac wordPropsTheory.no_install_evaluate_const_code >>
    gvs [] >>
    fs[AllCaseEqs (), UNCURRY_eq_pair, wordSemTheory.set_var_def,
       wordSemTheory.pop_env_def] >> gvs []
  )
  >~ [`Case (ShareInst op _ _, _)`]
  >- (
    fs [CaseEq "option", CaseEq "word_loc"] >>
    Cases_on `op` >>
    gs[wordSemTheory.share_inst_def,
         wordSemTheory.sh_mem_load_def, wordSemTheory.sh_mem_load_byte_def,
         wordSemTheory.sh_mem_store_def, wordSemTheory.sh_mem_store_byte_def,
         wordSemTheory.sh_mem_load16_def, wordSemTheory.sh_mem_store16_def,
         wordSemTheory.sh_mem_load32_def, wordSemTheory.sh_mem_store32_def,
         ffiTheory.call_FFI_def]>>
    every_case_tac>>
    fs[wordSemTheory.sh_mem_set_var_def,
         wordSemTheory.set_var_def, wordSemTheory.flush_state_def]>>
    gvs[]
  )
  >~ [`Case (Loop _ _ _, _)`]
  >- (
    CCONTR_TAC >> fs[] >>
    gvs[AllCaseEqs(), UNCURRY_eq_pair] >>
    imp_res_tac wordPropsTheory.cut_state_const >>
    imp_res_tac wordPropsTheory.no_install_evaluate_const_code >>
    gs[wordSemTheory.STOP_def, wordConvsTheory.no_install_def,
       wordConvsTheory.no_alloc_def] >>
    Cases_on `res` >> gvs[wordSemTheory.exit_loop_def] >>
    rename1 `SOME r` >>
    Cases_on `r` >>
    gvs[wordSemTheory.exit_loop_def, wordSemTheory.cont_loop_def]
  )
  >>
  CCONTR_TAC>> fs[]>>
  fs[AllCaseEqs (), UNCURRY_eq_pair]>>
  imp_res_tac wordPropsTheory.no_install_evaluate_const_code>>
  gs[]
QED

Theorem panLang_wordSem_neq_NotEnoughSpace:
  evaluate (Call NONE (SOME start) [0] NONE, s with clock := k) = (res, t) ∧
  ALL_DISTINCT (MAP FST (functions pan_code)) ∧
  word_to_word_compile c.word_to_word_conf mc.target.config
                       (pan_to_word_compile_prog mc.target.config.ISA pan_code) = (col,wprog) ∧
  s.code = fromAList wprog ⇒
  res ≠ SOME NotEnoughSpace
Proof
  rw[]>>
  qmatch_asmsub_abbrev_tac ‘wordSem$evaluate (prg, _) = _’ >>
  ‘no_install prg /\ no_alloc prg /\ no_mt prg’
    by gs[wordConvsTheory.no_alloc_def, wordConvsTheory.no_install_def,
          wordConvsTheory.no_mt_def, Abbr ‘prg’]>>
  qmatch_asmsub_abbrev_tac ‘word_to_word_compile _ _ wprog0’>>
  qpat_x_assum ‘Abbrev (_ = _)’ (assume_tac o GSYM o REWRITE_RULE [markerTheory.Abbrev_def])>>
  ‘ALL_DISTINCT (MAP FST wprog0)’
    by (drule pan_to_wordProofTheory.first_compile_prog_all_distinct>>
        strip_tac>>gvs[])>>
  drule_then irule no_alloc_word_evaluate >>
  imp_res_tac pan_to_word_compile_prog_no_install_code>>
  imp_res_tac pan_to_word_compile_prog_no_alloc_code>>
  imp_res_tac pan_to_word_compile_prog_no_mt_code>>
  drule word_to_word_compile_no_install_no_alloc>>
  simp []
QED

Theorem inst_stack_size_const_panLang:
  ∀i s t.
  wordSem$inst i s = SOME t ==>
  t.stack_size = s.stack_size
Proof
  Induct>>rw[wordSemTheory.inst_def,wordSemTheory.assign_def]>>
  fs [AllCaseEqs (), UNCURRY_eq_pair] >>
  gvs [wordSemTheory.word_exp_def,
          wordSemTheory.set_var_def,
          wordSemTheory.mem_store_def,
          wordSemTheory.get_fp_var_def,
          wordSemTheory.get_var_def,
          wordSemTheory.get_vars_def]
QED

Theorem inst_stack_limit_const_panLang:
  ∀i s t.
  wordSem$inst i s = SOME t ==>
  t.stack_limit = s.stack_limit
Proof
  Induct>>rw[wordSemTheory.inst_def,wordSemTheory.assign_def]>>
  fs [AllCaseEqs (), UNCURRY_eq_pair] >>
  gvs[wordSemTheory.word_exp_def,
          wordSemTheory.set_var_def,
          wordSemTheory.mem_store_def,
          wordSemTheory.get_fp_var_def,
          wordSemTheory.get_var_def,
          wordSemTheory.get_vars_def]
QED

Theorem inst_stack_max_const_panLang:
  ∀i s t.
  wordSem$inst i s = SOME t ==>
  t.stack_max = s.stack_max
Proof
  Induct>>rw[wordSemTheory.inst_def,wordSemTheory.assign_def]>>
  fs [AllCaseEqs (), UNCURRY_eq_pair] >>
  gvs[wordSemTheory.word_exp_def,
          wordSemTheory.set_var_def,
          wordSemTheory.mem_store_def,
          wordSemTheory.get_fp_var_def,
          wordSemTheory.get_var_def,
          wordSemTheory.get_vars_def]
QED

Theorem share_inst_modifies:
  wordSem$share_inst op v ad s = (res, t) ==>
  ? ls ffi stk lsz st.
  t = (s with <| locals := ls; ffi := ffi;
        stack := stk; locals_size := lsz; store := st |>)
Proof
  Cases_on ‘op’>>
  gs[wordSemTheory.share_inst_def,
     wordSemTheory.sh_mem_load_def,
     wordSemTheory.sh_mem_load_def,
     wordSemTheory.sh_mem_load_byte_def,
     wordSemTheory.sh_mem_load16_def,
     wordSemTheory.sh_mem_load32_def,
     wordSemTheory.sh_mem_store_def,
     wordSemTheory.sh_mem_store_byte_def,
     wordSemTheory.sh_mem_store16_def,
     wordSemTheory.sh_mem_store32_def,
     ffiTheory.call_FFI_def]>>
  every_case_tac >>
  fs[wordSemTheory.sh_mem_set_var_def,
         wordSemTheory.set_var_def,
         wordSemTheory.flush_state_def]>>gvs[] >>
  rw [] >>
  simp [wordSemTheory.state_component_equality]
QED

Theorem evaluate_stack_size_limit_const_panLang:
  ∀prog s res t.
  wordSem$evaluate (prog, s) = (res,t) ∧
  no_install prog ∧ no_install_code s.code ∧
  no_alloc prog ∧ no_alloc_code s.code ==>
  t.stack_size = s.stack_size /\ t.stack_limit = s.stack_limit
Proof
  recInduct (name_ind_cases [] wordSemTheory.evaluate_ind)>>
  simp[wordSemTheory.evaluate_def,wordSemTheory.flush_state_def]>>
  rpt conj_tac>>rpt (gen_tac ORELSE disch_tac)>>
  gs[wordConvsTheory.no_install_def,
     wordConvsTheory.no_alloc_def,
     wordConvsTheory.no_mt_def,
     wordSemTheory.jump_exc_def,
     wordSemTheory.get_var_def, wordSemTheory.mem_store_def]
  >~ [`Case (Call _ _ _ _, _)`]
  >- (
    fs [CaseEq "option"]
    \\ fs [CaseEq "option", CaseEq "prod", CaseEq "bool"] \\ gvs []
    \\ imp_res_tac wordPropsTheory.no_install_find_code
    \\ imp_res_tac wordPropsTheory.no_alloc_find_code
    \\ imp_res_tac wordPropsTheory.no_install_evaluate_const_code
    \\ gs []
    \\ gs [wordSemTheory.set_var_def, wordSemTheory.call_env_def,
         wordSemTheory.pop_env_def]
    \\ fs [AllCaseEqs (), UNCURRY_eq_pair] \\ gvs []
  )
  \\ fs [AllCaseEqs (), UNCURRY_eq_pair] \\ gvs []
  \\ TRY (drule inst_stack_size_const_panLang)
  \\ TRY (drule inst_stack_limit_const_panLang)
  \\ imp_res_tac wordPropsTheory.no_install_evaluate_const_code
  \\ imp_res_tac share_inst_modifies
  \\ gs []
  \\ imp_res_tac wordPropsTheory.cut_state_const \\ gvs []
  \\ imp_res_tac wordPropsTheory.no_install_evaluate_const_code \\ gs []
  \\ gs [wordSemTheory.STOP_def, wordConvsTheory.no_install_def,
         wordConvsTheory.no_alloc_def]
QED

Definition compile_prog_max_def:
  compile_prog_max c mc prog =
    let asm_conf = mc.target.config in
    let prog = pan_to_word$compile_prog asm_conf.ISA prog in
    let (col,wprog) = word_to_word$compile c.word_to_word_conf asm_conf prog in
    let (bm,c',fs,p) = word_to_stack$compile asm_conf wprog in
    let max = max_depth c'.stack_frame_size (full_call_graph InitGlobals_location (fromAList wprog)) in
      (from_stack asm_conf c LN p bm, max)
End

Definition option_lt_def[simp]:
  (option_lt n0 NONE ⇔ T) ∧ (option_lt NONE (SOME n1) ⇔ F) ∧
  (option_lt (SOME n1) (SOME n2) ⇔ n1 < n2:num)
End

Theorem option_lt_SOME:
  option_lt x (SOME n) = (∃m. x = SOME m ∧ m < n)
Proof
  Cases_on ‘x’>>fs[]
QED


Theorem from_pan_to_lab_no_install:
  ALL_DISTINCT (MAP FST (functions pan_code)) ∧ ac.ISA ≠ Ag32 ∧
  pan_to_word_compile_prog isa pan_code = wprog0 ∧
  word_to_word_compile wc ac wprog0 = (col, wprog) ∧
  word_to_stack_compile ac wprog = (bm, c, fs, p) ⇒
  no_install (stack_to_lab_compile scc dc lim regc off p)
Proof
  strip_tac>>
  imp_res_tac first_compile_prog_all_distinct>>
  first_x_assum $ qspec_then ‘isa’ assume_tac>>
  drule pan_to_word_compile_prog_no_install_code>>strip_tac>>
  drule pan_to_word_compile_prog_no_mt_code>>strip_tac>>
  gs[]>>
  drule_all word_to_word_compile_no_install_no_alloc>>strip_tac>>
  ‘MAP FST wprog0 = MAP FST wprog’ by
    (drule compile_to_word_conventions2>>
     impl_tac
     >- (irule_at Any EVERY_MONOTONIC>>
         qexists ‘λ_. ac.ISA ≠ Ag32’>>simp[FORALL_PROD])>>
     gvs[])>>fs[]>>
  drule_all word_to_stackProofTheory.word_to_stack_compile_no_install>>strip_tac>>
  irule (SRULE[] $ stack_to_labProofTheory.stack_to_lab_compile_no_install)>>fs[]
QED

Theorem n2w_sub_alt[local]:
  ∀a b. b ≤ a ⇒ n2w (a - b) = n2w a + -1w * n2w b
Proof
  rpt strip_tac >>
  irule EQ_TRANS >>
  drule_then (irule_at (Pos hd)) n2w_sub >>
  simp[] >>
  metis_tac[WORD_NEG_MUL]
QED

Theorem aligned_n2w_IMP[local]:
  aligned k ((n2w n):'a word) ∧ n < dimword(:'a) ⇒ divides (2**k) n
Proof
  rw[aligned_w2n,dimword_def] >>
  gvs[dividesTheory.DIVIDES_MOD_0]
QED

(* TODO: move *)
Theorem word_list_exists_addresses:
  (word_list_exists a n) (fun2set (d, addresses (a:'a word) m)) ∧ good_dimindex(:'a) ∧ m < dimword(:'a) DIV w2n(bytes_in_word:'a word) ⇒ n = m
Proof
  rw[word_list_exists_def,set_sepTheory.SEP_EXISTS_THM] >>
  imp_res_tac data_to_word_gcProofTheory.word_list_IMP_limit >>
  gvs[word_list_exists_def,set_sepTheory.SEP_EXISTS_THM,set_sepTheory.fun2set_def,
     set_sepTheory.STAR_def,set_sepTheory.SPLIT_def,set_sepTheory.cond_def] >>
  rpt $ pop_assum mp_tac >>
  qid_spec_tac ‘xs’ >>
  qid_spec_tac ‘a’ >>
  qid_spec_tac ‘m’ >>
  Induct_on ‘xs’ >>
  Cases_on ‘m’ >>
  rw[miscTheory.word_list_def,stack_removeProofTheory.addresses_def]
  >- (gvs[set_sepTheory.emp_def,FUN_EQ_THM, SF DNF_ss])
  >- gvs[set_sepTheory.STAR_def,set_sepTheory.SPLIT_def,set_sepTheory.one_def, SF DNF_ss] >>
  gvs[set_sepTheory.STAR_def,set_sepTheory.one_def,set_sepTheory.SPLIT_def] >>
  ‘v = {(a', d a') | a' ∈ addresses (a + bytes_in_word) n}’
    by(gvs[SET_EQ_SUBSET,SUBSET_DEF] >>
       rw[] >>
       fs[SF DNF_ss] >>
       res_tac >>
       gvs[] >>
       gvs[stack_removeProofTheory.addresses_thm] >>
       FULL_SIMP_TAC std_ss [GSYM WORD_ADD_ASSOC, addressTheory.WORD_EQ_ADD_CANCEL] >>
       gvs[good_dimindex_def,bytes_in_word_def,dimword_def,word_add_n2w,word_mul_n2w]) >>
  rveq >>
  first_x_assum drule >>
  simp[]
QED

Theorem good_dimindex_div_mul:
  good_dimindex(:α) ⇒ a * dimindex(:α) DIV 8 = a * (dimindex (:α) DIV 8)
Proof
  rw[good_dimindex_def] >>
  rw[] >>
  intLib.COOPER_TAC
QED

Theorem InitGlobals_location_eq_first_name:
  InitGlobals_location = first_name
Proof
  EVAL_TAC
QED

(* resource_limit' *)
Theorem pan_to_target_compile_semantics:
  compile_prog_max c mc pan_code = (SOME (bytes, bitmaps, c'), stack_max) ∧
  pancake_good_code pan_code ∧
  distinct_params (functions pan_code) ∧
  ALL_DISTINCT (MAP FST(functions pan_code)) ∧
  s.code = FEMPTY ∧
  s.locals = FEMPTY ∧
  s.globals = FEMPTY ∧
  size_of_eids pan_code < dimword (:α) ∧
  FDOM s.eshapes = FDOM ((get_eids(functions pan_code)):mlstring |-> 'a word) ∧
  backend_config_ok mc.target.config c ∧ lab_to_targetProof$mc_conf_ok mc ∧
  mc_init_ok mc.target.config c mc ∧ mc.target.config.ISA ≠ Ag32 ∧
  0w <₊ mc.target.get_reg ms mc.len_reg ∧
  globals_size = SUM (MAP size_of_shape (dec_shapes (compile_prog pan_code))) ∧
  mc.target.get_reg ms mc.len_reg  <₊ mc.target.get_reg ms mc.ptr2_reg ∧
  mc.target.get_reg ms mc.len_reg = s.base_addr ∧
  globals_allocatable s pan_code ∧
  heap_len = w2n ((mc.target.get_reg ms mc.ptr2_reg) + -1w * s.base_addr) DIV (dimindex (:α) DIV 8) ∧
  s.top_addr = s.base_addr + bytes_in_word * n2w heap_len - n2w(globals_size*dimindex (:α) DIV 8) ∧
  globals_size ≤ heap_len ∧
  s.memaddrs = addresses (mc.target.get_reg ms mc.len_reg) (heap_len-globals_size) ∧
  aligned (shift (:'a) + 1) ((mc.target.get_reg ms mc.ptr2_reg) + -1w * (mc.target.get_reg ms mc.len_reg)) ∧
  adj_ptr2 = (mc.target.get_reg ms mc.len_reg) + bytes_in_word * n2w max_stack_alloc ∧
  adj_ptr4 = (mc.target.get_reg ms mc.len2_reg) - bytes_in_word * n2w max_stack_alloc ∧
  adj_ptr2 ≤₊ (mc.target.get_reg ms mc.ptr2_reg) ∧
  (mc.target.get_reg ms mc.ptr2_reg) ≤₊ adj_ptr4 ∧
  w2n (mc.target.get_reg ms mc.ptr2_reg + -1w * (mc.target.get_reg ms mc.len_reg)) ≤
  w2n (bytes_in_word:'a word) * (2 * max_heap_limit (:'a) c.data_conf -1) ∧
  w2n (bytes_in_word:'a word) * (2 * max_heap_limit (:'a) c.data_conf -1) < dimword (:'a) ∧
  s.ffi = ffi ∧ mc.target.config.big_endian = s.be ∧
  OPTION_ALL (EVERY $ \x. ∃s. x = ExtCall s) c.lab_conf.ffi_names ∧
  pan_installed bytes cbspace bitmaps data_sp c'.lab_conf.ffi_names
                (heap_regs c.stack_conf.reg_names) mc
                c'.lab_conf.shmem_extra ms
                (wlab_wloc o s.memory)
                s.memaddrs s.sh_memaddrs ∧
  start = «main» ∧
  semantics_decls s start pan_code ≠ Fail ⇒
  machine_sem (mc:(α,β,γ) machine_config) (ffi:'ffi ffi_state) ms ⊆
              extend_with_resource_limit'
              (option_lt stack_max (SOME (FST (read_limits mc.target.config c mc ms))))
              {semantics_decls (s:('a,'ffi) panSem$state) start pan_code}
Proof

  strip_tac>>
  last_x_assum mp_tac>>
  rewrite_tac[compile_prog_max_def]>>
  rewrite_tac[backendTheory.from_stack_def]>>
  rewrite_tac[backendTheory.from_lab_def]>>
  strip_tac>>gs[]>>
  pairarg_tac>>gs[]>>
  pairarg_tac>>gs[]>>
  rename1 ‘_ = (col, wprog)’>>
  qmatch_asmsub_abbrev_tac ‘attach_bitmaps _ _ _ tprog = _’>>
  qmatch_asmsub_abbrev_tac ‘Abbrev (_ = compile _ _ lprog)’>>
  (* unfolding done *)

  (* apply lab_to_target *)
  irule SUBSET_TRANS>>
  irule_at Any (lab_to_targetProofTheory.semantics_compile |>
                  REWRITE_RULE [semanticsPropsTheory.implements'_def,
                                semanticsPropsTheory.extend_with_resource_limit'_def])>>

  qpat_x_assum ‘Abbrev (tprog = _)’
               (assume_tac o GSYM o REWRITE_RULE[markerTheory.Abbrev_def])>>
  Cases_on ‘tprog’>>gs[backendTheory.attach_bitmaps_def]>>
  rename1 ‘compile _ _ _ = SOME x’>>Cases_on ‘x’>>
  rename1 ‘compile _ _ _ = SOME (tprog, ltconf)’>>
  gs[]>>
  qabbrev_tac ‘hp = heap_regs c.stack_conf.reg_names’>>
  Cases_on ‘hp’>>gs[]>>

  (* no_install_or_no_share_mem *)
  ‘no_install lprog’ by
    (fs[Abbr ‘lprog’]>>
     irule from_pan_to_lab_no_install>>
     rpt (first_assum $ irule_at Any)>>
     metis_tac[mc_init_ok_def])>>
  ‘no_install_or_no_share_mem lprog mc.ffi_names’
    by fs[lab_to_targetProofTheory.no_install_or_no_share_mem_def]>>

  (* compiler_orackle_ok *)
  qmatch_asmsub_abbrev_tac ‘stack_to_lab_compile _ _ max_heap sp _ _’>>
  qabbrev_tac ‘lorac = λn:num.
                         (ltconf, []:(num # 'a stack_rawcallProof$prog) list, []:'a word list)’>>
  qabbrev_tac ‘sorac =
               (λn:num.
                  (λ(c',p,b:'a word list).
                     (c',
                      compile_no_stubs c.stack_conf.reg_names
                                       c.stack_conf.jump
                                       mc.target.config.addr_offset sp p))
                  (lorac n))’>>

  imp_res_tac backendProofTheory.compile_to_word_conventions2>>
  gs[backendProofTheory.mc_init_ok_def]>>
  gs[backendTheory.attach_bitmaps_def]>>
  gs[backendProofTheory.backend_config_ok_def]>>
  gs[pan_installed_def]>>gs[]>>

  ‘no_share_mem_inst lprog ⇒
   compiler_oracle_ok sorac ltconf.labels (LENGTH bytes)
                      mc.target.config mc.ffi_names’
    by (
    gs[Abbr ‘sorac’]>>gs[Abbr ‘lorac’]>>
    simp [lab_to_targetProofTheory.compiler_oracle_ok_def]>>
    ‘ltconf.pos = LENGTH bytes’
      by (gs[lab_to_targetTheory.compile_def]>>
          drule backendProofTheory.compile_lab_LENGTH>>
          strip_tac>>gs[])>>gs[]>>
    gvs[stack_to_labTheory.compile_no_stubs_def]>>
    gs[stack_namesTheory.compile_def]>>
    gs[lab_to_targetProofTheory.good_code_def]>>
    gs[labPropsTheory.get_labels_def,backendPropsTheory.restrict_nonzero_def]>>
    fs[labPropsTheory.no_share_mem_inst_def,labSemTheory.asm_fetch_aux_def])>>
  first_assum $ irule_at Any>>gs[]>> (* no_install_or_no_share_mem *)
  first_assum $ irule_at Any>>gs[]>>  (* lab_to_target$compile *)

  ‘EVERY (λ(_,_,_). T) (pan_to_word_compile_prog mc.target.config.ISA pan_code)’ by
    (rw[]>>simp[EVERY_MEM,FORALL_PROD])>>fs[]>>

  ‘good_code mc.target.config (LN:num sptree$num_map sptree$num_map) lprog’
    by (
    irule (INST_TYPE [beta|-> ``:num``] pan_to_lab_good_code_lemma)>>
    gs[]>>
    rpt (first_assum $ irule_at Any)>>
    qpat_x_assum ‘Abbrev (lprog = _)’
                 (assume_tac o GSYM o REWRITE_RULE [markerTheory.Abbrev_def])>>
    first_assum $ irule_at Any>>
    qmatch_asmsub_abbrev_tac ‘word_to_word_compile _ _ wprog0 = _’>>
    qpat_x_assum ‘Abbrev (wprog0 = _)’
                 (assume_tac o GSYM o REWRITE_RULE [markerTheory.Abbrev_def])>>
    (* labels_ok *)
    drule_all pan_to_lab_labels_ok>>strip_tac>>gs[]>>
    (* all_enc_ok_pre mc.target.config lprog *)
    ‘byte_offset_ok mc.target.config 0w’
      by (gs[lab_to_targetProofTheory.mc_conf_ok_def]>>
          drule good_dimindex_0w_8w>>gs[])>>
    gs[stack_to_labTheory.compile_def]>>rveq>>
    irule stack_to_labProofTheory.compile_all_enc_ok_pre>>gs[]>>
    (irule stack_namesProofTheory.stack_names_stack_asm_ok>>
     gs[]>>
     irule stack_removeProofTheory.stack_remove_stack_asm_name>>
     gs[lab_to_targetProofTheory.mc_conf_ok_def]>>
     gs[stackPropsTheory.reg_name_def, Abbr ‘sp’]>>
     irule stack_allocProofTheory.stack_alloc_stack_asm_convs>>
     gs[stackPropsTheory.reg_name_def]>>
     assume_tac (GEN_ALL stack_rawcallProofTheory.stack_alloc_stack_asm_convs)>>
     first_x_assum (qspecl_then [‘p’, ‘mc.target.config’] assume_tac)>>gs[]>>
     (* reshaping... *)
     gs[GSYM EVERY_CONJ]>>
     simp[LAMBDA_PROD]>>
     ‘p = SND (SND (SND (word_to_stack_compile mc.target.config wprog)))’
       by gs[]>>
     pop_assum $ (fn h => rewrite_tac[h])>>
     irule word_to_stackProofTheory.word_to_stack_stack_asm_convs>>
     gs[]>>
     irule EVERY_MONOTONIC>>
     qpat_assum ‘EVERY _ wprog’ $ irule_at Any>>
     rpt strip_tac>>pairarg_tac>>gs[]>>
     first_x_assum $ irule>>
     irule pan_to_word_every_inst_ok_less>>metis_tac[pancake_good_code_def])>>
    gs[])>>
  gs[]>>
  first_assum $ irule_at Any>>gs[]>>
  simp[Once SWAP_EXISTS_THM]>>
  qexists_tac ‘sorac’>>fs[]>>
  ‘ltconf = c'.lab_conf’ by gvs[]>>gs[]>>

  qpat_assum ‘compile _ _ lprog = SOME _’ mp_tac>>
  rewrite_tac[lab_to_targetTheory.compile_def]>>strip_tac>>
  drule_all backendProofTheory.compile_lab_IMP_mmio_pcs_min_index>>
  strip_tac>>
  fs[]>>rfs[]>>
  conj_tac>- (Cases_on ‘c.lab_conf.ffi_names’>>fs[])>>

  qmatch_goalsub_abbrev_tac ‘labSem$semantics labst’>>

  mp_tac (GEN_ALL stack_to_labProofTheory.full_make_init_semantics
            |> INST_TYPE [beta|-> “:lab_to_target$config”, gamma|-> “:'ffi”])>>

  gs[lab_to_targetProofTheory.mc_conf_ok_def]>>
  disch_then (qspec_then ‘labst’ mp_tac)>>gs[]>>
  ‘labst.code = stack_to_lab_compile
                c.stack_conf c.data_conf
                (2 * max_heap_limit (:α) c.data_conf − 1)
                (mc.target.config.reg_count −
                 (LENGTH mc.target.config.avoid_regs + 3))
                mc.target.config.addr_offset p’
    by gs[Abbr ‘labst’, Abbr ‘lprog’,lab_to_targetProofTheory.make_init_def]>>
  disch_then $ drule_at Any>>gs[]>>
  qabbrev_tac ‘sopt =
               full_make_init c.stack_conf c.data_conf max_heap
                              sp mc.target.config.addr_offset
                              bitmaps p labst
                              (set mc.callee_saved_regs) data_sp lorac’>>
  Cases_on ‘sopt’>>gs[]>>
  rename1 ‘_ = (sst, opt)’>>
  disch_then $ drule_at (Pos hd)>>
  ‘labst.compile_oracle =
   (λn. (λ(c',p,b).
           (c', compile_no_stubs c.stack_conf.reg_names c.stack_conf.jump
                                 mc.target.config.addr_offset sp p)) (lorac n))’
    by gs[Abbr ‘labst’, Abbr ‘sorac’,lab_to_targetProofTheory.make_init_def]>>
  gs[]>>
  ‘¬MEM labst.link_reg mc.callee_saved_regs ∧ labst.pc = 0 ∧
   (∀k i n. MEM k mc.callee_saved_regs ⇒ labst.io_regs n i k = NONE) ∧
   (∀k n. MEM k mc.callee_saved_regs ⇒ labst.cc_regs n k = NONE) ∧
   (∀x. x ∈ labst.mem_domain ⇒ w2n x MOD (dimindex (:α) DIV 8) = 0) ∧
   (∀x. x ∈ labst.shared_mem_domain ⇒ w2n x MOD (dimindex (:α) DIV 8) = 0) ∧
   good_code sp p ∧ (∀n. good_code sp (FST (SND (lorac n)))) ∧
   10 ≤ sp ∧
   (MEM (find_name c.stack_conf.reg_names (sp + 1))
    mc.callee_saved_regs ∧
    MEM (find_name c.stack_conf.reg_names (sp + 2))
        mc.callee_saved_regs) ∧ mc.len2_reg = labst.len2_reg ∧
   mc.ptr2_reg = labst.ptr2_reg ∧ mc.len_reg = labst.len_reg ∧
   mc.ptr_reg = labst.ptr_reg ∧ labst.shared_mem_domain = s.sh_memaddrs ∧
   (case mc.target.config.link_reg of NONE => 0 | SOME n => n) =
   labst.link_reg ∧ ¬labst.failed’
    by (gs[Abbr ‘labst’, Abbr ‘sp’,
           lab_to_targetProofTheory.make_init_def]>>
        gs[Abbr ‘lorac’]>>
        drule backendProofTheory.byte_aligned_MOD>>gs[]>>
        strip_tac>>
        drule_all word_to_stack_good_code_lemma>>
        rw[]>>
        gs[stack_to_labProofTheory.good_code_def])>>
  gs[]>>

  ‘memory_assumption c.stack_conf.reg_names bitmaps data_sp labst’
    by (
    gs[stack_to_labProofTheory.memory_assumption_def]>>
    qpat_assum ‘Abbrev (labst = _)’ mp_tac>>
    rewrite_tac[markerTheory.Abbrev_def]>>
    rewrite_tac[lab_to_targetProofTheory.make_init_def,
                labSemTheory.state_component_equality]>>
    simp[]>>strip_tac>>gs[]>>
    gs[backendProofTheory.heap_regs_def]>>

    qpat_x_assum ‘_ (fun2set _)’ assume_tac>>

    rewrite_tac[Once INTER_COMM]>>
    rewrite_tac[UNION_OVER_INTER]>>
    rewrite_tac[Once UNION_COMM]>>
    irule miscTheory.fun2set_disjoint_union>>
    gs[]>>
    conj_tac >- (
      irule backendProofTheory.word_list_exists_imp>>
      gs[]>>
      ‘(w2n:'a word -> num) bytes_in_word = dimindex (:α) DIV 8’ by
        rfs [miscTheory.good_dimindex_def,bytes_in_word_def,dimword_def]>>
      conj_tac >- (
        fs [] \\ match_mp_tac IMP_MULT_DIV_LESS \\ fs [w2n_lt]
        \\ rfs [miscTheory.good_dimindex_def])>>
      fs [stack_removeProofTheory.addresses_thm]>>
      ‘0 < dimindex (:α) DIV 8’ by
        rfs [miscTheory.good_dimindex_def]>>
      gs[]
      \\ qabbrev_tac `a = t.regs q`
      \\ qabbrev_tac `b = t.regs r`
      \\ qpat_x_assum `a <=+ b` assume_tac
      \\ old_drule WORD_LS_IMP \\ strip_tac \\ fs [EXTENSION]
      \\ fs [IN_DEF,PULL_EXISTS,bytes_in_word_def,word_mul_n2w]
      \\ rw [] \\ reverse eq_tac THEN1
       (rw [] \\ fs [] \\ qexists_tac `i * (dimindex (:α) DIV 8)` \\ fs []
        \\ `0 < dimindex (:α) DIV 8` by rfs [miscTheory.good_dimindex_def]
        \\ old_drule X_LT_DIV \\ disch_then (fn th => fs [th])
        \\ fs [RIGHT_ADD_DISTRIB]
        \\ fs [GSYM word_mul_n2w,GSYM bytes_in_word_def]
        \\ fs [byte_aligned_mult])
      \\ rw [] \\ fs []
      \\ `i < dimword (:'a)` by metis_tac [LESS_TRANS,w2n_lt] \\ fs []
      \\ qexists_tac `i DIV (dimindex (:α) DIV 8)`
      \\ rfs [alignmentTheory.byte_aligned_def,
              ONCE_REWRITE_RULE [WORD_ADD_COMM] alignmentTheory.aligned_add_sub]
      \\ fs [aligned_w2n]
      \\ old_drule DIVISION
      \\ disch_then (qspec_then `i` (strip_assume_tac o GSYM))
      \\ `2 ** LOG2 (dimindex (:α) DIV 8) = dimindex (:α) DIV 8` by
        (fs [miscTheory.good_dimindex_def] \\ NO_TAC)
      \\ fs [] \\ rfs [] \\ `-1w * a + b = b - a` by fs []
      \\ full_simp_tac std_ss []
      \\ Cases_on `a` \\ Cases_on `b`
      \\ full_simp_tac std_ss [WORD_LS,addressTheory.word_arith_lemma2]
      \\ fs [] \\ match_mp_tac DIV_LESS_DIV \\ fs []
      \\ rfs [] \\ fs [] \\ match_mp_tac MOD_SUB_LEMMA \\ fs [])>>
    irule DISJOINT_INTER>>gs[DISJOINT_SYM])>>
  gs[]>>

  (* apply stack_to_lab *)
  strip_tac>>
  ‘semantics InitGlobals_location sst ≠ Fail ⇒
   semantics labst ≠ Fail’ by rw[]>>
  pop_assum $ irule_at Any>>

  irule_at Any $ METIS_PROVE [] “∀x y z. x = y ∧ y ∈ z ⇒ x ∈ z”>>
  pop_assum $ irule_at Any>>

  (* word_to_stack *)

  (* instantiate / discharge *)
  ‘FST (word_to_stack_compile mc.target.config wprog) ≼ sst.bitmaps ∧
   sst.code = fromAList p’
    by (
    gs[stack_to_labProofTheory.full_make_init_def]>>
    gs[stack_removeProofTheory.make_init_opt_def]>>
    Cases_on ‘opt’>>gs[]>>
    gs[stack_removeProofTheory.make_init_any_def,
       stack_allocProofTheory.make_init_def,
       stack_to_labProofTheory.make_init_def,
       stack_namesProofTheory.make_init_def]>>
    qmatch_asmsub_abbrev_tac ‘evaluate (init_code gengc _ _, s')’>>
    qmatch_asmsub_abbrev_tac ‘make_init_opt _ _ _ _ coracle jump off _ code _’>>
    Cases_on ‘evaluate (init_code gengc max_heap sp, s')’>>gs[]>>
    rename1 ‘evaluate _ = (q', r')’>>
    Cases_on ‘q'’>>gs[]>>rveq>>
    gs[stackSemTheory.state_component_equality]>>
    Cases_on ‘make_init_opt gengc max_heap bitmaps data_sp coracle jump off sp code s'’>>
    gs[stackSemTheory.state_component_equality]>>
    gs[stack_removeProofTheory.make_init_opt_def]>>
    gs[stack_removeProofTheory.init_reduce_def]>>
    gs[stack_removeProofTheory.init_prop_def]>>
    rveq>>gs[stackSemTheory.state_component_equality])>>

  drule_at Any word_to_stackProofTheory.compile_semantics>>
  gs[]>>

  ‘EVERY (λ(n,m,prog).
            flat_exp_conventions prog ∧
            post_alloc_conventions
            (mc.target.config.reg_count −
             (LENGTH mc.target.config.avoid_regs + 5)) prog) wprog’
    by (qpat_x_assum ‘EVERY _ wprog’ assume_tac>>
        gs[EVERY_EL]>>rpt strip_tac>>
        first_x_assum $ qspec_then ‘n’ assume_tac>>
        pairarg_tac>>gs[])>>gs[]>>
  disch_then (qspec_then ‘InitGlobals_location’ mp_tac)>>
  disch_then (qspec_then ‘λn. ((LENGTH bitmaps, c'.lab_conf), [])’ mp_tac)>>

  qmatch_goalsub_abbrev_tac ‘init_state_ok _ _ _ worac’>>

  ‘¬ NULL bitmaps ∧ HD bitmaps = 4w’
    by (drule word_to_stackProofTheory.compile_word_to_stack_bitmaps>>
        strip_tac>>Cases_on ‘bitmaps’>>gs[])>>
  ‘ALOOKUP wprog raise_stub_location = NONE ∧
   ALOOKUP wprog store_consts_stub_location = NONE’
    by (
    qmatch_asmsub_abbrev_tac ‘word_to_word_compile _ _ wprog0 = _’>>
    qpat_x_assum ‘Abbrev (wprog0 = _)’ (assume_tac o GSYM o REWRITE_RULE [markerTheory.Abbrev_def])>>
    drule pan_to_word_compile_prog_lab_min>>
    gs[GSYM EVERY_MAP]>>
    rewrite_tac[ALOOKUP_NONE, EVERY_MEM]>>
    qpat_x_assum ‘MAP FST _ = MAP FST _’ $ assume_tac o GSYM>>
    strip_tac>>gs[]>>
    gs[wordLangTheory.raise_stub_location_def, EL_MAP,
       wordLangTheory.store_consts_stub_location_def,
       backend_commonTheory.word_num_stubs_def,
       backend_commonTheory.stack_num_stubs_def]>>
    first_assum $ qspec_then ‘5’ assume_tac>>
    first_x_assum $ qspec_then ‘6’ assume_tac>>gs[])>>gs[]>>

  ‘init_state_ok
   mc.target.config
   (mc.target.config.reg_count −
    (LENGTH mc.target.config.avoid_regs + 5)) sst worac’
    by (
    irule stack_to_labProofTheory.IMP_init_state_ok>>
    gs[]>>
    Cases_on ‘opt’>>gs[]>>rename1 ‘(sst, SOME xxx)’>>
    MAP_EVERY qexists_tac [‘data_sp’, ‘c.data_conf’, ‘labst’, ‘max_heap’, ‘p’, ‘set mc.callee_saved_regs’,
                           ‘c.stack_conf’, ‘sp’, ‘mc.target.config.addr_offset’, ‘TL bitmaps’, ‘xxx’]>>

    ‘4w::TL bitmaps = bitmaps’ by (rveq>>gs[]>>metis_tac[CONS])>>gs[]>>
    conj_tac >-
     (strip_tac>>gs[Abbr ‘worac’]>>strip_tac>>
      pop_assum kall_tac>>
      pop_assum (fn h => once_rewrite_tac[GSYM h])>>gs[])>>
    gs[Abbr ‘worac’]>>
    qpat_x_assum ‘_ = (sst, SOME _)’ mp_tac>>
    gs[Abbr ‘lorac’]>>
    pairarg_tac>>gs[]>>
    gs[word_to_stackTheory.compile_def]>>
    pairarg_tac>>gs[]>>
    gs[word_to_stackTheory.compile_word_to_stack_def]>>
    rveq>>gs[]>>rw[])>>gs[]>>

  (* apply word_to_stack *)
  qmatch_goalsub_abbrev_tac ‘wordSem$semantics wst _’>>
  strip_tac>>

  (* elim stackSem ≠ Fail *)
  ‘semantics wst InitGlobals_location ≠ Fail ⇒
   semantics InitGlobals_location sst ≠ Fail’
    by (rw[]>>
        gs[semanticsPropsTheory.extend_with_resource_limit'_def]>>
        gs[semanticsPropsTheory.extend_with_resource_limit_def]>>
        FULL_CASE_TAC>>gs[])>>
  pop_assum $ irule_at Any>>

  ‘semantics wst InitGlobals_location ≠ Fail ⇒
   (∀res t k. evaluate (Call NONE (SOME InitGlobals_location) [0] NONE, wst with clock := k) = (res, t) ⇒ res ≠ SOME Error)’
    by (simp[wordSemTheory.semantics_def]>>
        IF_CASES_TAC>>gs[]>>
        rpt strip_tac>>
        first_x_assum $ qspec_then ‘k’ assume_tac>>gs[])>>

  (* actually apply word_to_stack *)
  irule_at Any $ METIS_PROVE [SUBSET_DEF] “∀z A B. A ⊆ B ∧ z ∈ A ⇒ z ∈ B”>>
  first_x_assum $ irule_at Any>>

  gs[semanticsPropsTheory.extend_with_resource_limit'_def]>>

  ‘∀(x:behaviour set) y a b f. x = y ∧ (b ⇒ a) ∧ (∀x. x ⊆ f x) ⇒ (if a then x else f x) ⊆ (if b then y else f y)’
    by (rpt strip_tac>>IF_CASES_TAC>>gs[]>>IF_CASES_TAC>>gs[])>>
  pop_assum $ irule_at Any>>

  (* word_to_word *)
  drule (word_to_wordProofTheory.word_to_word_compile_semantics |> INST_TYPE [beta |-> “: num # lab_to_target$config”])>>

  disch_then (qspecl_then [‘wst’, ‘InitGlobals_location’, ‘wst with code := fromAList (pan_to_word_compile_prog mc.target.config.ISA pan_code)’] mp_tac)>>
  gs[]>>
  ‘gc_fun_const_ok wst.gc_fun ∧
   no_install_code (fromAList (pan_to_word_compile_prog mc.target.config.ISA pan_code)) ∧
   no_alloc_code (fromAList (pan_to_word_compile_prog mc.target.config.ISA pan_code)) ∧
   no_mt_code (fromAList (pan_to_word_compile_prog mc.target.config.ISA pan_code))’
    by (conj_tac >- (
         gs[Abbr ‘wst’, word_to_stackProofTheory.make_init_def]>>
         gs[stack_to_labProofTheory.full_make_init_def,
            stack_removeProofTheory.make_init_opt_def]>>
         Cases_on ‘opt’>>gs[]>>
         gs[stack_removeProofTheory.make_init_any_def,
            stack_allocProofTheory.make_init_def,
            stack_to_labProofTheory.make_init_def,
            stack_namesProofTheory.make_init_def]>>
         rveq>>
         gs[stackSemTheory.state_component_equality]>>
         irule data_to_word_gcProofTheory.gc_fun_const_ok_word_gc_fun)>>
        conj_tac >- (
         irule pan_to_word_compile_prog_no_install_code>>
         metis_tac[])>>
        conj_tac >- (
         irule pan_to_word_compile_prog_no_alloc_code>>
         metis_tac[])>>
        irule pan_to_word_compile_prog_no_mt_code>>
        metis_tac[])>>gs[]>>
  ‘ALL_DISTINCT (MAP FST (pan_to_word_compile_prog mc.target.config.ISA pan_code)) ∧
   wst.stack = [] ∧ wst.code = fromAList wprog ∧
   lookup 0 wst.locals = SOME (Loc 1 0) ∧
   wst = wst with code := wst.code’
    by (
    drule pan_to_wordProofTheory.first_compile_prog_all_distinct>>
    strip_tac>>
    gs[Abbr ‘wst’, word_to_stackProofTheory.make_init_def])>>gs[]>>

  (* remove wordSem1 ≠ Fail *)
  qmatch_goalsub_abbrev_tac ‘fromAList wprog0’>>
  strip_tac>>
  qmatch_asmsub_abbrev_tac ‘semantics wst0 _ ≠ Fail’>>
  ‘semantics wst0 InitGlobals_location ≠ Fail ⇒
   semantics wst InitGlobals_location ≠ Fail’
    by (rw[]>>gs[])>>
  pop_assum $ irule_at Any>>

  ‘semantics wst0 InitGlobals_location ≠ Fail ⇒
         ∀t k. evaluate (Call NONE (SOME InitGlobals_location) [0] NONE,wst with clock := k) ≠ (SOME Error,t)’
    by (strip_tac>>gs[])>>
  qpat_x_assum ‘semantics wst _ ≠ Fail ⇒ _’ kall_tac>>

  (* apply word_to_word *)
  irule_at Any EQ_TRANS>>
  qpat_x_assum ‘_ ≠ Fail ⇒ _ = _’ $ (irule_at Any) o GSYM>>
  gs[]>>rewrite_tac[Once CONJ_COMM]>>
  gs[GSYM CONJ_ASSOC]>>

  (* misc *)
  ‘(wst.be ⇔ s.be) ∧ wst.ffi = ffi’
    (* prove this before unfolding full_make_init *)
    by (gs[Abbr ‘wst’,
           word_to_stackProofTheory.make_init_def]>>
        qmatch_asmsub_abbrev_tac ‘fmi = (sst, opt)’>>
        ‘sst = FST fmi’ by gs[]>>gs[]>>
        conj_tac
        >- (fs[Abbr ‘fmi’]>>
            gs[full_make_init_be]>>
            qpat_x_assum ‘Abbrev (labst = _)’ ((fn h => rewrite_tac[h]) o REWRITE_RULE [markerTheory.Abbrev_def])>>
            rewrite_tac[lab_to_targetProofTheory.make_init_def]>>
            simp[labSemTheory.state_component_equality])>>
        ‘labst.ffi = ffi’
          by (gs[Abbr ‘labst’, lab_to_targetProofTheory.make_init_simp])>>
        irule EQ_TRANS>>pop_assum $ irule_at Any>>
        fs[Abbr ‘fmi’]>>gs[stack_to_labProofTheory.full_make_init_ffi])>>gs[]>>

  (* move init_code_thm here *)
  (* first, take apart full_make_init to expose init_code *)
  qpat_x_assum ‘_ = (sst, opt)’ mp_tac>>

  simp[stack_to_labProofTheory.full_make_init_def]>>
  simp[stack_removeProofTheory.make_init_opt_def,
       stack_allocProofTheory.make_init_def,
       stack_namesProofTheory.make_init_def,
       stack_to_labProofTheory.make_init_def,
       stack_removeProofTheory.make_init_any_def]>>
  Cases_on ‘opt’>>gs[Abbr ‘lorac’]>>
  qmatch_goalsub_abbrev_tac ‘evaluate (initc, ssx)’>>
  Cases_on ‘evaluate (initc, ssx)’>>gs[]>>
  rename1 ‘evaluate (_,ssx) = (res,sss)’>>
  Cases_on ‘res’>>gs[]>>

  qpat_x_assum ‘_ = labst.len2_reg’ $ assume_tac o GSYM>>
  qpat_x_assum ‘_ = labst.ptr2_reg’ $ assume_tac o GSYM>>
  qpat_x_assum ‘_ = labst.len_reg’ $ assume_tac o GSYM>>
  qpat_x_assum ‘_ = labst.ptr_reg’ $ assume_tac o GSYM>>
  fs[heap_regs_def]>>
  qpat_x_assum ‘_ = q’ $ assume_tac o GSYM>>
  qpat_x_assum ‘_ = r’ $ assume_tac o GSYM>>
  gs[]>>ntac 2 $ pop_assum kall_tac>>

  ‘mc.len2_reg ≠ mc.len_reg ∧ mc.ptr2_reg ≠ mc.len_reg ∧
   mc.len2_reg ≠ mc.ptr2_reg’
    by (
    gs[BIJ_DEF, INJ_DEF]>>
    conj_tac >- (
      CCONTR_TAC>>
      last_x_assum $ qspecl_then [‘4’, ‘2’] assume_tac>>
      gs[])>>
    conj_tac >- (
      CCONTR_TAC>>
      last_x_assum $ qspecl_then [‘3’, ‘2’] assume_tac>>
      gs[])>>
    CCONTR_TAC>>
    last_x_assum $ qspecl_then [‘3’, ‘4’] assume_tac>>
    gs[])>>

  qmatch_goalsub_abbrev_tac ‘init_reduce gck jump off _ mprog _ _’>>
  simp[o_DEF]>>strip_tac>>gs[]>>

  (* introduce init_code_thm *)
  ‘lookup stack_err_lab ssx.code = SOME (halt_inst 2w)’
    by
    (gs[Abbr ‘ssx’]>>
     gs[lookup_fromAList,stack_removeTheory.compile_def]>>
     gs[stack_removeTheory.init_stubs_def,
        stack_removeTheory.stack_err_lab_def])>>
  gs[Abbr ‘initc’]>>
  drule_at Any stack_removeProofTheory.init_code_thm>>
  ‘ssx.compile_oracle =
   (I ## MAP (stack_remove_prog_comp jump off sp) ## I)
   ∘ (I ## MAP stack_alloc_prog_comp ## I) ∘ (λn. (ltconf,[],[]))’
    by gs[Abbr ‘ssx’,o_DEF]>>
  disch_then $ drule_at Any>>
  simp[o_DEF]>>
  pop_assum kall_tac>> (* ssx.compile_oracle *)

  ‘code_rel jump off sp mprog ssx.code’
    by (
    simp[stack_removeProofTheory.code_rel_def]>>
    gs[Abbr ‘ssx’, Abbr ‘mprog’]>>
    gs[lookup_fromAList,domain_fromAList]>>
    gs[stack_removeTheory.compile_def]>>
    gs[stack_removeProofTheory.prog_comp_eta]>>
    reverse conj_asm1_tac
    >- (
      simp[stack_removeTheory.init_stubs_def]>>
      rewrite_tac[Once UNION_COMM]>>
      gs[MAP_MAP_o,o_DEF,LAMBDA_PROD]>>
      ‘set (MAP (λ(p1,p2). p1) (compile c.data_conf (compile p))) =
       set (MAP FST (compile c.data_conf (compile p)))’
        by (
        gs[LIST_TO_SET_MAP]>>
        irule IMAGE_CONG>>rw[]>>pairarg_tac>>gs[])>>
      gs[])>>
    ntac 3 strip_tac>>
    conj_tac >- (
      qpat_x_assum ‘good_code _ p’ mp_tac>>
      simp[stack_to_labProofTheory.good_code_def]>>
      strip_tac>>
      gs[Once (GSYM stack_rawcallProofTheory.stack_rawcall_reg_bound)]>>
      drule stack_allocProofTheory.stack_alloc_reg_bound>>
      disch_then $ qspecl_then [‘compile p’,‘c.data_conf’] assume_tac>>
      gs[EVERY_MEM]>>
      pop_assum irule>>
      drule ALOOKUP_MEM>>strip_tac>>
      gs[MEM_MAP]>>
      pop_assum $ irule_at Any>>gs[])>>
    irule EQ_TRANS>>
    irule_at Any (ALOOKUP_prefix |> BODY_CONJUNCTS |> tl |> hd)>>
    reverse conj_asm2_tac>-gs[ALOOKUP_MAP]>>
    gs[stack_removeTheory.init_stubs_def]>>
    mp_tac (GEN_ALL pan_to_wordProofTheory.pan_to_word_compile_prog_lab_min)>>
    disch_then $ qspecl_then [‘wprog0’,‘pan_code’, ‘mc.target.config.ISA’] mp_tac>>
    impl_tac>- gs[Abbr ‘wprog0’]>>
    simp[GSYM EVERY_MAP]>>
    qpat_assum ‘MAP FST wprog = MAP FST _’ (fn h => PURE_REWRITE_TAC[GSYM h])>>

    drule word_to_stack_compile_FST>>
    gs[wordLangTheory.raise_stub_location_def,
       wordLangTheory.store_consts_stub_location_def]>>
    gs[backend_commonTheory.word_num_stubs_def]>>
    gs[backend_commonTheory.stack_num_stubs_def]>>
    strip_tac>>
    strip_tac>>
    gs[ALOOKUP_MAP]>>

    gs[stack_allocTheory.compile_def]>>
    gs[stack_rawcallTheory.compile_def]>>
    gs[ALOOKUP_APPEND]>>
    Cases_on ‘ALOOKUP (stubs c.data_conf) n’>>
    gs[stack_allocTheory.stubs_def,
       stackLangTheory.gc_stub_location_def,
       backend_commonTheory.stack_num_stubs_def]>>

    gs[MAP_MAP_o,stack_allocTheory.prog_comp_def,o_DEF,LAMBDA_PROD]>>
    drule ALOOKUP_MEM>>gs[MEM_MAP]>>
    strip_tac>>
    pairarg_tac>>gs[]>>
    ‘MEM p1 (MAP FST p)’
      by (gs[MEM_MAP]>>first_assum $ irule_at (Pos last)>>gs[])>>gs[]>>
    gs[EVERY_MEM]>>
    first_x_assum $ qspec_then ‘p1’ assume_tac>>gs[])>>
  disch_then $ drule_at Any>>
  ‘init_code_pre sp bitmaps data_sp ssx’
    by
    (simp[stack_removeProofTheory.init_code_pre_def]>>
     gs[stack_to_labProofTheory.memory_assumption_def]>>
     gs[Abbr ‘ssx’]>>
     gs[FLOOKUP_MAP_KEYS_LINV]>>
     MAP_EVERY qexists_tac [‘ptr2’, ‘ptr3’, ‘ptr4’, ‘bitmap_ptr'’]>>
     gs[]>>
     gs[flookup_fupdate_list]>>
     gs[REVERSE_DEF, ALOOKUP_APPEND]>>
     gs[]>>
     conj_tac >- simp[domain_fromAList, stack_removeTheory.compile_def,
                      stack_removeTheory.init_stubs_def]>>
     conj_tac >-
      (qpat_x_assum ‘MEM (_ _ sp) _’ $ irule_at Any>>
       simp[Once EQ_SYM_EQ]>>irule LINV_DEF>>
       gs[BIJ_DEF]>>metis_tac[])>>
     conj_tac >-
      (qpat_x_assum ‘MEM (_ _ (_+1)) _’ $ irule_at Any>>
       simp[Once EQ_SYM_EQ]>>irule LINV_DEF>>
       gs[BIJ_DEF]>>metis_tac[])>>
     (qpat_x_assum ‘MEM (_ _ (_+2)) _’ $ irule_at Any>>
      simp[Once EQ_SYM_EQ]>>irule LINV_DEF>>
      gs[BIJ_DEF]>>metis_tac[]))>>
  disch_then $ drule_at Any>>
  disch_then $ drule_at Any>>
  disch_then $ qspec_then ‘gck’ assume_tac>>gs[]>>

  ‘(w2n:'a word -> num) bytes_in_word = dimindex (:α) DIV 8’
    by fs[good_dimindex_def,bytes_in_word_def,dimword_def]>>
  ‘sss.regs ' (sp + 2) = Word (s.base_addr) ∧
   sss.regs ' (sp + 1) = Word (mc.target.get_reg ms mc.ptr2_reg
                               + 48w * bytes_in_word:'a word) ∧

   mc.target.get_reg ms mc.ptr2_reg = w3 ∧
   mc.target.get_reg ms mc.len2_reg = w4 ∧
   sss.sh_mdomain = sdm ∩ byte_aligned ∧
   t.regs mc.len_reg = w2 ∧
   t.regs mc.len2_reg = w4’
    by (
    gs[Abbr ‘ssx’, Abbr ‘labst’]>>
    fs[lab_to_targetProofTheory.make_init_def]>>

    gs[stack_removeProofTheory.init_prop_def]>>

    qpat_x_assum ‘init_reduce _ _ _ _ _ _ _ _ _ = x'’ (assume_tac o GSYM)>>fs[]>>
    fs[stack_removeProofTheory.init_reduce_def]>>

    gs[FLOOKUP_MAP_KEYS_LINV]>>
    gs[flookup_fupdate_list]>>
    gs[REVERSE_DEF, ALOOKUP_APPEND]>>

    ‘store_init (is_gen_gc c.data_conf.gc_kind) sp CurrHeap =
     (INR (sp + 2) :'a word + num)’
      by gs[stack_removeTheory.store_init_def, APPLY_UPDATE_LIST_ALOOKUP]>>
    gs[]>>

    ‘ALL_DISTINCT
     (MAP FST (MAP (λn. case
                        store_init (is_gen_gc c.data_conf.gc_kind) sp n
                        of
                          INL w => (n,Word w)
                        | INR i => (n,sss.regs ' i)) store_list))’
      by (rewrite_tac[stack_removeTheory.store_list_def,
                      stack_removeTheory.store_init_def,
                      APPLY_UPDATE_LIST_ALOOKUP]>>
          gs[APPLY_UPDATE_LIST_ALOOKUP])>>

    gs[flookup_fupdate_list]>>
    gs[REVERSE_DEF, ALOOKUP_APPEND]>>
    gs[alookup_distinct_reverse]>>

    gs[stack_removeTheory.store_list_def,
       stack_removeTheory.store_init_def,
       APPLY_UPDATE_LIST_ALOOKUP]>>

    (* need target_state_rel *)
    gs[targetSemTheory.good_init_state_def]>>
    gs[asmPropsTheory.target_state_rel_def]>>

    qpat_assum ‘∀i. _ ⇒ mc.target.get_reg ms _ = t.regs _’ assume_tac>>
    first_x_assum $ qspec_then ‘mc.len_reg’ mp_tac>>
    impl_tac>-fs[asmTheory.reg_ok_def]>>
    strip_tac>>gs[]>>

    qpat_x_assum ‘FLOOKUP sss.regs (sp + 2) = SOME _’ mp_tac>>
    qpat_x_assum ‘sss.regs ' _ = Word curr’ mp_tac>>
    simp[FLOOKUP_DEF]>>ntac 2 strip_tac>>
    gs[wordSemTheory.theWord_def]>>
    (* base_addr done *)

    gs[stack_removeProofTheory.state_rel_def]>>
    Cases_on ‘FLOOKUP sss.regs (sp + 1)’>>gs[]>>
    rename1 ‘FLOOKUP _ (sp + 1) = SOME xxx’>>Cases_on ‘xxx’>>gs[]>>
    gs[flookup_thm]>>
    gs[wordSemTheory.theWord_def]>>
    gs[FLOOKUP_MAP_KEYS_LINV]>>
    gs[flookup_fupdate_list]>>
    gs[REVERSE_DEF, ALOOKUP_APPEND]>>
    gs[wordSemTheory.theWord_def]>>
    qpat_assum ‘∀i. _ ⇒ mc.target.get_reg ms _ = t.regs _’ assume_tac>>
    first_assum $ qspec_then ‘mc.len_reg’ mp_tac>>
    impl_tac>-fs[asmTheory.reg_ok_def]>>
    first_assum $ qspec_then ‘mc.ptr2_reg’ mp_tac>>
    impl_tac>-fs[asmTheory.reg_ok_def]>>
    first_x_assum $ qspec_then ‘mc.len2_reg’ mp_tac>>
    impl_tac>-fs[asmTheory.reg_ok_def]>>
    ntac 2 strip_tac>>gs[]>>
    ‘(w3 + -1w * s.base_addr) ⋙ (shift (:α) + 1) ≪ (shift (:α) + 1)
     = w3 + -1w * s.base_addr’
      by (irule data_to_word_gcProofTheory.lsr_lsl>>gs[])>>
    gs[backendProofTheory.heap_regs_def]>>
    qpat_x_assum ‘w2 = _’ $ assume_tac o GSYM>>fs[])>>
  (* memory domain done *)

  (* memory shift *)
  qpat_x_assum ‘FLOOKUP sss.regs (sp + 2) = _’ mp_tac>>
  gs[flookup_thm]>>strip_tac>>gs[]>>
  ‘(w3 + -1w * s.base_addr) ⋙ (shift (:α) + 1) ≪ (shift (:α) + 1)
   = w3 + -1w * s.base_addr’
    by (irule data_to_word_gcProofTheory.lsr_lsl>>gs[])>>
  gs[]>>

  ‘w2n (-1w * w2 + w3 + bytes_in_word * n2w (LENGTH store_list)) DIV
   (dimindex (:α) DIV 8)  − LENGTH store_list =
   w2n (-1w * w2 + w3) DIV (dimindex (:α) DIV 8)’
    by
    (simp[SUB_RIGHT_EQ]>>
     irule OR_INTRO_THM1>>
     irule EQ_TRANS>>
     irule_at Any ADD_DIV_ADD_DIV>>
     ‘0 < dimindex (:'a) DIV 8’ by gs[good_dimindex_def]>>fs[]>>
     ‘(LENGTH store_list) * (dimindex (:'a) DIV 8)
      = w2n (bytes_in_word:'a word * n2w (LENGTH store_list))’
       by fs[good_dimindex_def,bytes_in_word_def,dimword_def,
             word_mul_def,stack_removeTheory.store_list_def]>>
     pop_assum (fn h => rewrite_tac[h])>>

     rewrite_tac[Once word_add_def]>>
     rewrite_tac[w2n_n2w]>>
     ‘w2n (w3 − w2) + w2n (bytes_in_word:'a word * n2w (LENGTH store_list)) < dimword (:'a)’
       by (irule LESS_EQ_LESS_TRANS>>
           qexists_tac ‘w2n w4’>>
           simp[w2n_lt]>>
           ‘w2n (-1w * w2 + w3) ≤ w2n w4 - w2n (bytes_in_word:'a word * n2w (LENGTH store_list))’
             by (irule LESS_EQ_TRANS>>
                 qexists_tac ‘w2n (w4 + -1w * (bytes_in_word:'a word * n2w max_stack_alloc))’>>
                 rewrite_tac[Once WORD_ADD_COMM]>>
                 rewrite_tac[Once (GSYM WORD_NEG_MUL)]>>
                 rewrite_tac[GSYM word_sub_def]>>
                 ‘w3 - w2  <₊ w4 + -1w * (bytes_in_word * n2w max_stack_alloc)’
                   by (irule WORD_LOWER_LOWER_EQ_TRANS>>
                       last_assum $ irule_at Any>>
                       simp[]>>
                       rewrite_tac[Once WORD_ADD_LEFT_LO2]>>
                       conj_tac >-
                        (rewrite_tac[GSYM (cj 1 WORD_LO_word_0)]>>
                         irule WORD_LOWER_EQ_LOWER_TRANS>>
                         last_assum $ irule_at Any>>simp[])>>
                       irule OR_INTRO_THM1>>
                       rewrite_tac[GSYM WORD_NEG_MUL]>>
                       rewrite_tac[WORD_NEG_NEG]>>
                       simp[]>>
                       rewrite_tac[GSYM (cj 1 WORD_LO_word_0)]>>simp[])>>
                 drule (iffLR WORD_LO)>>strip_tac>>
                 drule LESS_IMP_LESS_OR_EQ>>strip_tac>>
                 fs[]>>
                 rewrite_tac[Once word_add_def]>>
                 rewrite_tac[w2n_n2w]>>
                 rewrite_tac[Once word_mul_def]>>
                 simp[w2n_minus1]>>
                 simp[LEFT_SUB_DISTRIB]>>
                 ‘w2n (bytes_in_word:'a word * n2w max_stack_alloc) ≤
                  dimword (:α) * w2n (bytes_in_word:'a word * n2w max_stack_alloc)’
                   by fs[good_dimindex_def,bytes_in_word_def,dimword_def,
                         stack_removeTheory.max_stack_alloc_def]>>
                 simp[GSYM LESS_EQ_ADD_SUB]>>
                 rewrite_tac[Once ADD_COMM]>>
                 ‘w2n (bytes_in_word:'a word * n2w max_stack_alloc) ≤ w2n w4’
                   by (
                   ‘1024w * bytes_in_word:'a word ≤₊ w4’
                      by (irule WORD_LOWER_EQ_TRANS>>
                          first_assum $ irule_at Any>>
                          rewrite_tac[WORD_ADD_LEFT_LS2]>>
                          irule OR_INTRO_THM2>>
                          qpat_assum ‘w2 ≤₊ w4’ $
                                     assume_tac o REWRITE_RULE[WORD_LOWER_OR_EQ]>>
                          gs[]>>
                          strip_tac>>gs[])>>
                   drule (iffLR WORD_LS)>>strip_tac>>
                   gs[good_dimindex_def,bytes_in_word_def,dimword_def,
                      stack_removeTheory.max_stack_alloc_def])>>
                 drule LESS_EQ_ADD_SUB>>
                 disch_then $ qspec_then
                            ‘dimword(:'a) *
                             w2n (bytes_in_word:'a word * n2w max_stack_alloc)’
                            assume_tac>>
                 pop_assum (fn h => rewrite_tac[h])>>
                 rewrite_tac[Once MULT_COMM]>>
                 assume_tac ZERO_LT_dimword>>
                 simp[MOD_TIMES]>>
                 ‘w2n w4 - w2n (bytes_in_word:'a word * n2w max_stack_alloc)
                  < dimword(:'a)’
                   by (simp[SUB_RIGHT_LESS]>>
                       irule LESS_TRANS>>
                       irule_at Any w2n_lt>>
                       fs[good_dimindex_def,bytes_in_word_def,dimword_def,
                          stack_removeTheory.max_stack_alloc_def])>>
                 simp[LESS_MOD]>>
                 fs[good_dimindex_def,bytes_in_word_def,dimword_def,
                    stack_removeTheory.max_stack_alloc_def,
                    stack_removeTheory.store_list_def])>>
           fs[SUB_LEFT_LESS_EQ]>>
           fs[WORD_SUM_ZERO])>>
     rewrite_tac[Once (GSYM WORD_ADD_COMM)]>>
     rewrite_tac[GSYM WORD_NEG_MUL]>>
     rewrite_tac[GSYM word_sub_def]>>
     simp[LESS_MOD])>>
  gs[]>>

  (* pan_to_word *)

  fs [InitGlobals_location_eq_first_name]>>
  ‘wst0.code = fromAList (pan_to_word_compile_prog mc.target.config.ISA pan_code)’
    by gs[Abbr ‘wst0’, wordSemTheory.state_component_equality]>>

  drule_at Any (INST_TYPE [beta|-> “:num # lab_to_target$config”]
                pan_to_wordProofTheory.state_rel_imp_semantics)>>gs[]>>
  rpt $ disch_then $ drule_at Any>>gs[]>>
  simp[GSYM PULL_EXISTS] >>

  impl_tac
  >- (gs[Abbr ‘wst0’]>>
      gs[]>>

      gs[Abbr ‘wst’, Abbr ‘worac’,
         word_to_stackProofTheory.make_init_def]>>gvs[]>>
      fs[stack_removeProofTheory.init_reduce_def]>>
      gs[wordSemTheory.theWord_def]>>

      ‘store_init gck sp CurrHeap =
       (INR (sp + 2) :'a word + num)’
        by gs[stack_removeTheory.store_init_def, APPLY_UPDATE_LIST_ALOOKUP]>>
      gs[]>>

      ‘ALL_DISTINCT (MAP FST (MAP
                              (λn.
                                 case
                                 store_init gck sp n
                                 of
                                   INL w => (n,Word w)
                                 | INR i => (n,sss.regs ' i)) store_list))’
        by (rewrite_tac[stack_removeTheory.store_list_def,
                        stack_removeTheory.store_init_def,
                        APPLY_UPDATE_LIST_ALOOKUP]>>
            gs[APPLY_UPDATE_LIST_ALOOKUP])>>
      gs[flookup_fupdate_list]>>
      gs[ALOOKUP_APPEND]>>
      gs[alookup_distinct_reverse]>>
      fs[stack_removeTheory.store_list_def,
         stack_removeTheory.store_init_def,
         APPLY_UPDATE_LIST_ALOOKUP,
         wordSemTheory.theWord_def] >>
      conj_tac
      >- (rpt strip_tac >>
          irule EQ_TRANS >>
          first_x_assum $ irule_at (Pos last) >>
          simp[] >>
          irule EQ_TRANS >>
          irule_at (Pos hd) EQ_SYM >>
          irule_at (Pos hd) $ iffLR set_sepTheory.fun2set_eq >>
          first_assum $ irule_at $ Pos hd >>
          simp[] >>
          conj_tac
          >- (gs[stack_removeProofTheory.addresses_thm] >>
              irule_at Any EQ_REFL >>
              simp[]) >>
          gs[Abbr ‘ssx’, Abbr ‘labst’]>>
          rewrite_tac[lab_to_targetProofTheory.make_init_def]>>simp[]>>
          gs[wordSemTheory.theWord_def]>>
          gs[set_sepTheory.fun2set_eq]) >>
      conj_tac
      >- (rw[no_labels_def] >>
          irule_at Any EQ_TRANS >>
          irule_at (Pos hd) EQ_SYM >>
          irule_at (Pos hd) $ iffLR set_sepTheory.fun2set_eq >>
          first_assum $ irule_at $ Pos hd >>
          simp[] >>
          gs[Abbr ‘ssx’, Abbr ‘labst’]>>
          rewrite_tac[lab_to_targetProofTheory.make_init_def]>>simp[]>>
          gs[wordSemTheory.theWord_def]>>
          gs[set_sepTheory.fun2set_eq]>>
          qpat_x_assum ‘good_init_state _ _ _ _ _ _ _ _ _ _’ mp_tac >>
          simp[targetSemTheory.good_init_state_def] >>
          ‘byte_aligned a’
            by(gs[stack_removeProofTheory.addresses_thm] >>
               simp[PURE_ONCE_REWRITE_RULE [WORD_ADD_COMM] byte_aligned_mult]) >>
          pop_assum mp_tac >>
          rpt $ pop_assum kall_tac >>
          metis_tac[byte_align_aligned]) >>
      conj_tac
      >- (rw[SET_EQ_SUBSET,SUBSET_DEF,stack_removeProofTheory.addresses_thm,
             addressTheory.WORD_EQ_ADD_CANCEL,WORD_EQ_ADD_RCANCEL]
          >- (simp[addressTheory.WORD_EQ_ADD_CANCEL] >>
              qmatch_goalsub_abbrev_tac ‘_ < www’ >>
              Cases_on ‘i < www’
              >- (disj1_tac >> irule_at Any EQ_REFL >> simp[]) >>
              disj2_tac >>
              simp[WORD_EQ_ADD_RCANCEL] >>
              qexists ‘i - www’ >>
              gs[Abbr ‘www’,NOT_LESS] >>
              gs[good_dimindex_def,bytes_in_word_def,word_mul_n2w,word_add_n2w] >>
              simp[REWRITE_RULE[wordsTheory.word_sub_def] addressTheory.word_arith_lemma2] >>
              ‘∀x. 32 * x DIV 8 = 4 * x’
                by(rpt $ pop_assum kall_tac >>
                   strip_tac >>
                   irule_at Any EQ_TRANS >>
                   irule_at (Pos last) $ Q.SPEC ‘4*x’ MULT_TO_DIV >>
                   qexists ‘8’ >>
                   intLib.COOPER_TAC) >>
              pop_assum $ simp o single >>
              ‘∀x. 64 * x DIV 8 = 8 * x’
                by(rpt $ pop_assum kall_tac >>
                   strip_tac >>
                   irule_at Any EQ_TRANS >>
                   irule_at (Pos last) $ Q.SPEC ‘8*x’ MULT_TO_DIV >>
                   qexists ‘8’ >>
                   intLib.COOPER_TAC) >>
              pop_assum $ simp o single >>
              PURE_REWRITE_TAC[GSYM LEFT_ADD_DISTRIB,LT_MULT_LCANCEL] >>
              simp[SUB_LEFT_SUB] >>
              simp[LEFT_ADD_DISTRIB])
          >- (irule_at Any EQ_REFL >> simp[])
          >- (simp[WORD_EQ_ADD_RCANCEL] >>
              qexists ‘(w2n
                        (-1w * mc.target.get_reg ms mc.len_reg +
                         mc.target.get_reg ms mc.ptr2_reg) DIV (dimindex (:α) DIV 8)) + i - SUM (MAP size_of_shape (dec_shapes (compile_prog pan_code)))
                      ’ >>
              simp[] >>
              gs[good_dimindex_def,bytes_in_word_def,word_mul_n2w,word_add_n2w] >>
              simp[REWRITE_RULE[wordsTheory.word_sub_def] addressTheory.word_arith_lemma2] >>
              ‘∀x. 32 * x DIV 8 = 4 * x’
                by(rpt $ pop_assum kall_tac >>
                   strip_tac >>
                   irule_at Any EQ_TRANS >>
                   irule_at (Pos last) $ Q.SPEC ‘4*x’ MULT_TO_DIV >>
                   qexists ‘8’ >>
                   intLib.COOPER_TAC) >>
              pop_assum $ simp o single >>
              ‘∀x. 64 * x DIV 8 = 8 * x’
                by(rpt $ pop_assum kall_tac >>
                   strip_tac >>
                   irule_at Any EQ_TRANS >>
                   irule_at (Pos last) $ Q.SPEC ‘8*x’ MULT_TO_DIV >>
                   qexists ‘8’ >>
                   intLib.COOPER_TAC) >>
              pop_assum $ simp o single >>
              PURE_REWRITE_TAC[GSYM LEFT_ADD_DISTRIB,LT_MULT_LCANCEL] >>
              simp[SUB_LEFT_SUB] >>
              simp[LEFT_ADD_DISTRIB])) >>
      gvs[Abbr ‘sp’] >>
      gs[word_to_stackProofTheory.make_init_def]>>
      gs[Abbr ‘labst’,Abbr ‘ssx’] >>
      gs[stack_removeProofTheory.init_prop_def,flookup_fupdate_list] >>

      qpat_x_assum ‘(word_list_exists _ len * word_list_exists _ _) _’ mp_tac >>
      PURE_REWRITE_TAC[Once WORD_ADD_COMM] >>
      PURE_REWRITE_TAC[GSYM stack_removeProofTheory.word_list_exists_ADD] >>
      simp[] >>
      strip_tac >>
      drule word_list_exists_addresses >>
      impl_tac
      >- (simp[] >>
          gs[good_dimindex_def,dimword_def,DIV_LT_X] >>
          irule LESS_LESS_EQ_TRANS >>
          irule_at (Pos hd) w2n_lt >>
          simp[dimword_def]) >>
      ‘2w:'a word * (bytes_in_word * n2w len) = bytes_in_word * n2w(2*len)’
        by simp[GSYM word_mul_n2w] >>
      pop_assum SUBST_ALL_TAC >>
      disch_then $ simp o single >>
      simp[] >>
      PURE_REWRITE_TAC[WORD_EQ_ADD_LCANCEL,GSYM WORD_ADD_ASSOC] >>
      conj_tac
      >- (simp[bytes_in_word_def,word_mul_n2w] >> PURE_REWRITE_TAC[GSYM WORD_NEG_MUL] >>
          gs[good_dimindex_def] >>
          PURE_REWRITE_TAC[DECIDE “32:num = 8*4”,DECIDE “64:num = 8*8”,GSYM MULT_ASSOC] >>
          PURE_REWRITE_TAC[SIMP_RULE std_ss [] $ Q.SPEC ‘8’ MULT_DIV
                           |> PURE_ONCE_REWRITE_RULE[MULT_COMM]] >>
          simp[]) >>
      irule byte_aligned_add >>
      drule pan_globalsProofTheory.byte_aligned_bytes_in_word_mul >>
      simp[good_dimindex_div_mul,bytes_in_word_def,GSYM word_mul_n2w,
           Once bytes_in_word_def] >>
      strip_tac >>
      conj_tac >- metis_tac[WORD_MULT_ASSOC] >>
      irule byte_aligned_add >>
      conj_tac >- metis_tac[WORD_MULT_COMM] >>
      simp[])>>
  gs[]>>

  (* resource_limit implication *)
  strip_tac>>
  reverse conj_tac
  >- (strip_tac>>
      gs[semanticsPropsTheory.extend_with_resource_limit_def]>>
      once_rewrite_tac[GSYM UNION_ASSOC]>>
      simp[SUBSET_UNION])>>
  qpat_x_assum ‘_ = stack_max’ $ assume_tac o GSYM>>
  gs[wordSemTheory.word_lang_safe_for_space_def]>>
  pop_assum kall_tac>>
  rpt strip_tac>>
  drule word_depthProofTheory.max_depth_Call_NONE>>
  disch_then $ qspec_then ‘fromAList wprog’ assume_tac>>gs[]>>
  gs[option_lt_SOME]>>
  ‘res ≠ SOME Error’
    by (first_x_assum $ qspecl_then [‘t'’, ‘k’] assume_tac>>gs[])>>gs[]>>

  drule evaluate_stack_size_limit_const_panLang>>
  impl_tac >-
   (gs[Abbr ‘wst’,
       wordConvsTheory.no_mt_def,
       wordConvsTheory.no_alloc_def,
       wordConvsTheory.no_install_def]>>
    drule_all word_to_word_compile_no_install_no_alloc>>strip_tac>>
    gs[])>>
  strip_tac>>

  gs[backendProofTheory.read_limits_def]>>
  gs[stack_removeProofTheory.get_stack_heap_limit_def]>>
  gs[stack_removeProofTheory.get_stack_heap_limit'_def]>>
  gs[stack_removeProofTheory.get_stack_heap_limit''_def]>>
  gs[WORD_LO]>>
  ‘¬ (w2n (bytes_in_word:'a word * n2w max_heap) <
      w2n (w3 + -1w * s.base_addr))’
    by (gs[NOT_LESS]>>
        irule LESS_EQ_TRANS>>
        first_assum $ irule_at Any>>
        simp[word_mul_def])>>gs[]>>
  pop_assum $ kall_tac>>
  ‘(w3 + -1w * s.base_addr) ⋙ (shift (:α) + 1) ≪ (shift (:α) + 1) =
   w3 + -1w * s.base_addr’
    by (irule data_to_word_gcProofTheory.lsr_lsl>>gs[])>>gs[]>>
  pop_assum $ kall_tac>>

  qpat_x_assum ‘word_to_stack$compile _ _ = _’ mp_tac>>
  simp[word_to_stackTheory.compile_def]>>
  pairarg_tac>>gs[]>>
  strip_tac>>
  qpat_x_assum ‘_ = c''’ $ assume_tac o GSYM>>gs[]>>

  gs[Abbr ‘wst’, Abbr ‘worac’]>>
  gs[word_to_stackProofTheory.make_init_def]>>
  qpat_x_assum ‘_ = sst’ $ assume_tac o GSYM>>gs[]>>
  qpat_x_assum ‘init_reduce _ _ _ _ _ _ _ _ _ = x'’ $ assume_tac o GSYM>>gs[]>>
  gs[stack_removeProofTheory.init_reduce_def]>>
  gs[stack_removeProofTheory.LENGTH_read_mem]>>
  pop_assum kall_tac>>
  pop_assum kall_tac>>

  drule backendProofTheory.compile_word_to_stack_sfs_aux>>
  strip_tac>>

  qpat_x_assum ‘option_le _ _’ mp_tac>>
  simp[mapi_Alist]>>
  qmatch_goalsub_abbrev_tac ‘max_depth (fromAList (MAP f _)) _’>>
  ‘fromAList (MAP f (toAList (fromAList wprog))) =
   map (λ(arg_count,prog).
          FST
          (SND
           (compile_prog mc.target.config prog arg_count
            (mc.target.config.reg_count −
             (LENGTH mc.target.config.avoid_regs + 5))
            (Nil,0)))) (fromAList (toAList (fromAList wprog)))’
    by (irule EQ_TRANS>>
        irule_at Any (GSYM map_fromAList)>>
        gs[Abbr ‘f’]>>gs[LAMBDA_PROD])>>
  gs[]>>
  simp[wf_fromAList,fromAList_toAList]>>
  pop_assum kall_tac>>
  simp[map_fromAList]>>gs[LAMBDA_PROD]>>
  strip_tac>>gs[wordSemTheory.stack_size_def]>>
  gs[data_to_wordProofTheory.option_le_SOME]>>
  qpat_x_assum ‘m' < _’ assume_tac>>
  gs[wordSemTheory.theWord_def]>>
  qpat_x_assum ‘w2n _ ≤ max_heap * _’ assume_tac>>
  qpat_x_assum ‘aligned _ _’ assume_tac>>

  irule LESS_EQ_TRANS>>
  first_assum $ irule_at Any>>gs[]>>
  simp[LESS_EQ_IFF_LESS_SUC]>>
  irule LESS_LESS_EQ_TRANS>>
  first_assum $ irule_at Any>>
  rewrite_tac[LESS_OR_EQ]>>
  irule OR_INTRO_THM2>>simp[]>>
  qpat_x_assum ‘48w * _ = _ * _’ $ assume_tac>>
  ‘LENGTH store_list = 48’
  by simp[stack_removeTheory.store_list_def]>>
  fs[]>>

  ‘0 < dimindex (:'a) DIV 8’ by fs[good_dimindex_def]>>
  qpat_x_assum ‘w3 ≤₊ w4 + _’ assume_tac>>
  qpat_x_assum ‘_ ≤ max_heap’ assume_tac>>
  qpat_x_assum ‘max_heap * _ < _’ assume_tac>>
  blastLib.BBLAST_TAC>>
  rewrite_tac[SUC_ONE_ADD]>>

  rewrite_tac[Once (GSYM WORD_ADD_ASSOC)]>>
  rewrite_tac[Once WORD_ADD_COMM]>>
  rewrite_tac[Once (GSYM word_sub_def)]>>
  ‘1024w * bytes_in_word:'a word ≤₊ w4’
    by (irule WORD_LOWER_EQ_TRANS>>
        first_assum $ irule_at Any>>
        rewrite_tac[WORD_ADD_LEFT_LS2]>>
        irule OR_INTRO_THM2>>
        qpat_assum ‘w2 ≤₊ w4’ $ assume_tac o REWRITE_RULE[WORD_LOWER_OR_EQ]>>
        gs[]>>
        strip_tac>>gs[])>>
  ‘49w * bytes_in_word:'a word <₊ w4’
  by (
    irule WORD_LOWER_LOWER_EQ_TRANS>>
    first_assum $ irule_at Any>>
    gs[WORD_LO,bytes_in_word_def,good_dimindex_def,dimword_def])>>
  ‘w3 ≤₊ w4 + -49w * bytes_in_word:'a word’
    by (irule WORD_LOWER_EQ_TRANS>>
        first_assum $ irule_at Any>>
        simp[stack_removeTheory.max_stack_alloc_def]>>
        ‘-255w = -49w + -206w’ by simp[]>>
        pop_assum (fn h => rewrite_tac[h])>>
        rewrite_tac[WORD_RIGHT_ADD_DISTRIB]>>
        once_rewrite_tac[WORD_ADD_ASSOC]>>
        rewrite_tac[Once WORD_ADD_COMM]>>
        rewrite_tac[WORD_ADD_LEFT_LS2]>>
        irule OR_INTRO_THM2>>
        conj_tac >-
         (simp[GSYM (cj 1 WORD_LO_word_0)]>>
          rewrite_tac[Once WORD_ADD_RIGHT_LO]>>
          ‘¬(-49w * bytes_in_word ≤₊ 0w)’
            by gs[WORD_LS,bytes_in_word_def,good_dimindex_def,
                  dimword_def]>>fs[])>>
        irule OR_INTRO_THM1>>
        rewrite_tac[Once WORD_ADD_RIGHT_LO]>>
        ‘¬(-49w * bytes_in_word ≤₊ -(-206w * bytes_in_word))’
          by (rewrite_tac[WORD_NOT_LOWER_EQUAL]>>
              once_rewrite_tac[WORD_NEG_MUL]>>
              rewrite_tac[Once (GSYM WORD_MULT_ASSOC)]>>
              once_rewrite_tac[GSYM WORD_NEG_MUL]>>
              rewrite_tac[Once WORD_LESS_NEG_LEFT]>>
              rewrite_tac[WORD_NEG_NEG]>>
              conj_tac >-
               gs[bytes_in_word_def,good_dimindex_def,dimword_def]>>
              irule OR_INTRO_THM2>>
              once_rewrite_tac[WORD_NEG_MUL]>>
              rewrite_tac[Once (GSYM WORD_MULT_ASSOC)]>>
              simp[WORD_LO,word_mul_def]>>
              gs[bytes_in_word_def,good_dimindex_def,
                 dimword_def,w2n_minus1])>>fs[]>>
        irule OR_INTRO_THM2>>
        irule WORD_LOWER_LOWER_EQ_TRANS>>
        first_assum $ irule_at Any>>
        gs[WORD_LO,bytes_in_word_def,good_dimindex_def,dimword_def])>>
  fs[word_sub_w2n]>>
  ‘byte_aligned (w3 - w2)’
    by (simp[Once WORD_NEG_MUL]>>
        simp[byte_aligned_def]>>
        ‘LOG2 (dimindex (:'a) DIV 8) < shift (:'a) + 1’
          by gs[backend_commonTheory.word_shift_def,
                good_dimindex_def]>>
        drule_all aligned_imp>>rw[])>>
  qpat_assum ‘byte_aligned (w3 - _)’ $ assume_tac o REWRITE_RULE[byte_aligned_def]>>
  qpat_assum ‘byte_aligned w2’ $ assume_tac o REWRITE_RULE[byte_aligned_def]>>
  drule_all (iffLR (aligned_add_sub |> cj 2))>>strip_tac>>
  fs[GSYM byte_aligned_def]>>
  drule_all (byte_aligned_MOD |> REWRITE_RULE[SPECIFICATION])>>strip_tac>>
  gs[MOD_EQ_0_DIVISOR]>>
  simp[Q.SPECL [‘dimindex (:'a) DIV 8’, ‘0’] DIV_MULT |> SIMP_RULE (std_ss)[]]>>

  drule (iffLR WORD_LS)>>strip_tac>>
  gs[]>>
  pop_assum $ assume_tac o ONCE_REWRITE_RULE[MULT_COMM]>>
  ONCE_REWRITE_TAC[MULT_COMM]>>
  drule_all DIV_SUB>>strip_tac>>
  pop_assum (fn h => simp[h])>>

  (* -49w *)
  rewrite_tac[Once WORD_NEG_MUL]>>
  rewrite_tac[Once (GSYM WORD_MULT_ASSOC)]>>
  rewrite_tac[Once (GSYM WORD_NEG_MUL)]>>
  rewrite_tac[Once (GSYM word_sub_def)]>>
  ‘49w * bytes_in_word ≤₊ w4’ by fs[WORD_LOWER_IMP_LOWER_OR_EQ]>>
  gs[word_sub_w2n]>>
  drule (iffLR WORD_LS)>>
  simp[word_mul_def]>>
 ‘(w2n:'a word -> num) bytes_in_word = dimindex (:α) DIV 8’
    by fs[good_dimindex_def,bytes_in_word_def,dimword_def]>>fs[]>>
  ‘49 * (dimindex (:'a) DIV 8) < dimword (:'a)’
    by gs[good_dimindex_def,dimword_def]>>
  fs[MOD_LESS]>>
  ONCE_REWRITE_TAC[MULT_COMM]>>strip_tac>>
  drule_all DIV_SUB>>strip_tac>>
  pop_assum (fn h => simp[h])>>

  (* w4 *)
  qpat_x_assum ‘byte_aligned w4’ assume_tac>>
  drule_all (byte_aligned_MOD |> REWRITE_RULE[SPECIFICATION])>>strip_tac>>
  gs[MOD_EQ_0_DIVISOR]>>
  simp[Q.SPECL [‘dimindex (:'a) DIV 8’, ‘0’] DIV_MULT |> SIMP_RULE (std_ss)[]]>>

  rewrite_tac[SUB_PLUS]>>
  rewrite_tac[SUB_RIGHT_ADD]>>

  qpat_x_assum ‘w3 ≤₊ w4 + _’ assume_tac>>
  drule (iffLR WORD_LS)>>
  rewrite_tac[Once WORD_NEG_MUL]>>
  rewrite_tac[Once (GSYM WORD_MULT_ASSOC)]>>
  rewrite_tac[Once (GSYM WORD_NEG_MUL)]>>
  rewrite_tac[Once (GSYM word_sub_def)]>>
  fs[word_sub_w2n]>>
  simp[word_mul_def]>>
  rewrite_tac[GSYM RIGHT_SUB_DISTRIB]>>
  rewrite_tac[LE_MULT_RCANCEL]>>
  rw[]
QED

val _ = check_thm pan_to_target_compile_semantics;
