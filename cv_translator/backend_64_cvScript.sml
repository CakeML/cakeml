(*
  Translate arch-size-specific functions to cv equations.
*)

(* The following line is (and shall remain) the only difference between
   the 32-bit and 64-bit versions of this file. *)
Theory backend_64_cv[no_sig_docs]
Ancestors
  cv_std backend_cv to_data_cv backend
Libs
  preamble cv_transLib

val arch_size = if String.isSubstring "32" (current_theory()) then “:32” else “:64”;

val arch_spec = INST_TYPE [alpha |-> arch_size];
val arch_spec_beta = INST_TYPE [beta |-> arch_size];

val _ = cv_memLib.use_long_names := true;

Overload Num[local] = “cv$Num”;
Overload Pair[local] = “cv$Pair”;

val _ = cv_trans (alignmentTheory.aligned_w2n |> arch_spec);;
val _ = cv_trans (asmTheory.offset_ok_def |> arch_spec);
val _ = cv_trans (lab_to_targetTheory.section_labels_def |> arch_spec);
val _ = cv_trans (lab_to_targetTheory.compute_labels_alt_def |> arch_spec);
val _ = cv_trans (lab_to_targetTheory.lines_upd_lab_len_def |> arch_spec);
val _ = cv_auto_trans (lab_to_targetTheory.get_jump_offset_def |> arch_spec);

val pre = cv_trans_pre "" (lab_to_targetTheory.upd_lab_len_def |> arch_spec);
Theorem lab_to_target_upd_lab_len_pre[cv_pre]:
  ∀pos v. lab_to_target_upd_lab_len_pre pos v
Proof
  Induct_on ‘v’ \\ simp [Once pre]
QED

val _ = cv_trans (lab_to_targetTheory.add_nop_def |> arch_spec);

val pre = cv_trans_pre "" (lab_to_targetTheory.pad_section_def |> arch_spec);
Theorem lab_to_target_pad_section_pre[cv_pre,local]:
  ∀nop v aux. lab_to_target_pad_section_pre nop v aux
Proof
  Induct_on ‘v’ \\ simp [Once pre]
QED

val _ = cv_trans (lab_to_targetTheory.pad_code_def |> arch_spec);

Theorem to_shmem_rec[local]:
  <| entry_pc := ep ;
     nbytes := nb ;
     access_addr := aa ;
     reg := r ;
     exit_pc := ex |>
   = shmem_rec ep nb aa r ex
Proof
  gvs [lab_to_targetTheory.shmem_rec_component_equality]
QED

val pre = cv_trans_pre "" (lab_to_targetTheory.get_shmem_info_def
                          |> SRULE [to_shmem_rec] |> arch_spec);

Theorem lab_to_target_get_shmem_info_pre[cv_pre]:
  ∀v pos ffi_names shmem_info.
    lab_to_target_get_shmem_info_pre v pos ffi_names shmem_info
Proof
  ho_match_mp_tac lab_to_targetTheory.get_shmem_info_ind
  \\ rw [] \\ simp [Once pre] \\ gvs [to_shmem_rec]
QED

Theorem bytes_in_word_def[cv_inline] =
  bytes_in_word_def |> arch_spec |> CONV_RULE (RAND_CONV EVAL);

Theorem shift_def[cv_inline] =
  backend_commonTheory.word_shift_def |> arch_spec |> CONV_RULE (RAND_CONV EVAL);

val _ = data_to_wordTheory.get_gen_size_def |> arch_spec |> SRULE [] |> cv_trans;

val _ = stack_to_labTheory.compile_jump_def |> arch_spec |> cv_trans;
val _ = stack_to_labTheory.is_Seq_def |> arch_spec |> cv_trans;

val pre = stack_to_labTheory.flatten_def |> arch_spec |> cv_trans_pre "";
Theorem stack_to_lab_flatten_pre[cv_pre,local]:
  ∀t p n m. stack_to_lab_flatten_pre t p n m
Proof
  ho_match_mp_tac stack_to_labTheory.flatten_ind \\ rw [] \\ simp [Once pre]
QED

val _ = stack_allocTheory.next_lab_def |> arch_spec |> cv_trans;
val _ = stack_to_labTheory.prog_to_section_def |> arch_spec |> cv_trans;
val _ = stack_namesTheory.ri_find_name_def |> arch_spec |> cv_trans;
val _ = stack_namesTheory.inst_find_name_def |> arch_spec |> cv_trans;
val _ = stack_namesTheory.comp_def |> arch_spec |> cv_trans;
val _ = stack_namesTheory.prog_comp_def |> arch_spec_beta |> cv_trans;
val _ = stack_namesTheory.compile_def |> arch_spec |> cv_auto_trans;
val _ = stack_removeTheory.word_offset_def |> arch_spec |> cv_trans;
val _ = stack_removeTheory.store_offset_def |> arch_spec |> cv_trans;
val _ = stack_removeTheory.halt_inst_def |> arch_spec |> cv_trans;
val _ = stack_removeTheory.single_stack_alloc_def |> arch_spec |> cv_auto_trans;
val _ = stack_removeTheory.stack_alloc_def |> arch_spec |> cv_auto_trans;
val _ = stack_removeTheory.single_stack_free_def |> arch_spec |> cv_auto_trans;
val _ = stack_removeTheory.stack_free_def |> arch_spec |> cv_auto_trans;
val _ = stackLangTheory.list_Seq_def |> arch_spec |> cv_trans;
val _ = stack_removeTheory.copy_each_def |> arch_spec |> cv_trans;
val _ = stack_removeTheory.copy_loop_def |> arch_spec |> cv_trans;
val _ = cv_trans_rec (stack_removeTheory.upshift_def |> arch_spec)
 (WF_REL_TAC ‘measure $ cv$c2n o SND’ \\ Cases \\ gvs [] \\ rw [] \\ gvs []);
val _ = cv_trans_rec (stack_removeTheory.downshift_def |> arch_spec)
 (WF_REL_TAC ‘measure $ cv$c2n o SND’ \\ Cases \\ gvs [] \\ rw [] \\ gvs []);
val _ = stack_removeTheory.stack_store_def |> arch_spec |> cv_trans;
val _ = stack_removeTheory.stack_load_def |> arch_spec |> cv_trans;
val _ = stack_removeTheory.comp_def |> arch_spec |> cv_trans;
val _ = stack_removeTheory.prog_comp_def |> arch_spec_beta |> cv_trans;
val _ = stack_removeTheory.store_list_code_def |> arch_spec |> cv_trans;
val _ = stack_removeTheory.init_memory_def |> arch_spec |> cv_trans;
val _ = (stack_removeTheory.init_code_def |> arch_spec
           |> SRULE [EVAL “REVERSE store_list”,stack_removeTheory.store_init_def,
                     APPLY_UPDATE_THM,miscTheory.UPDATE_LIST_def]) |> cv_trans
val _ = stack_removeTheory.init_stubs_def |> arch_spec |> cv_trans;
val _ = stack_removeTheory.compile_def |> arch_spec |> cv_auto_trans;

val _ = stack_allocTheory.memcpy_code_def |> arch_spec |> cv_trans;
val _ = stack_allocTheory.clear_top_inst_def |> arch_spec |> cv_trans;
val _ = stack_allocTheory.word_gc_move_code_def |> arch_spec |> cv_trans;
val _ = stack_allocTheory.word_gc_move_list_code_def |> arch_spec |> cv_trans;
val _ = stack_allocTheory.word_gc_move_loop_code_def |> arch_spec |> cv_trans;
val _ = stack_allocTheory.word_gc_move_bitmap_code_def |> arch_spec |> cv_trans;
val _ = stack_allocTheory.word_gc_move_bitmaps_code_def |> arch_spec |> cv_trans;
val _ = stack_allocTheory.word_gc_move_roots_bitmaps_code_def |> arch_spec |> cv_trans;
val _ = stack_allocTheory.word_gen_gc_move_code_def |> arch_spec |> cv_trans;
val _ = stack_allocTheory.word_gen_gc_partial_move_code_def |> arch_spec |> cv_trans;
val _ = stack_allocTheory.word_gen_gc_move_bitmap_code_def |> arch_spec |> cv_trans;
val _ = stack_allocTheory.word_gen_gc_partial_move_bitmap_code_def |> arch_spec |> cv_trans;
val _ = stack_allocTheory.word_gen_gc_move_bitmaps_code_def |> arch_spec |> cv_trans;
val _ = stack_allocTheory.word_gen_gc_partial_move_bitmaps_code_def |> arch_spec |> cv_trans;
val _ = stack_allocTheory.word_gen_gc_move_roots_bitmaps_code_def |> arch_spec |> cv_trans;
val _ = stack_allocTheory.word_gen_gc_partial_move_roots_bitmaps_code_def |> arch_spec |> cv_trans;
val _ = stack_allocTheory.word_gen_gc_move_list_code_def |> arch_spec |> cv_trans;
val _ = stack_allocTheory.word_gen_gc_partial_move_list_code_def |> arch_spec |> cv_trans;
val _ = stack_allocTheory.word_gen_gc_move_data_code_def |> arch_spec |> cv_trans;
val _ = stack_allocTheory.word_gen_gc_partial_move_ref_list_code_def |> arch_spec |> cv_trans;
val _ = stack_allocTheory.word_gen_gc_partial_move_data_code_def |> arch_spec |> cv_trans;
val _ = stack_allocTheory.word_gen_gc_move_refs_code_def |> arch_spec |> cv_trans;
val _ = stack_allocTheory.word_gen_gc_move_loop_code_def |> arch_spec |> cv_trans;
val _ = stack_allocTheory.word_gc_partial_or_full_def |> arch_spec |> cv_trans;
val _ = stack_allocTheory.SetNewTrigger_def |> arch_spec |> cv_trans;
val _ = stack_allocTheory.word_gc_code_def |> arch_spec |> cv_trans;
val _ = stack_allocTheory.stubs_def |> arch_spec |> cv_auto_trans;
val _ = stack_allocTheory.stub_names_def |> arch_spec |> cv_auto_trans;
val _ = stack_allocTheory.next_lab_def |> arch_spec |> cv_trans;

val pre = stack_allocTheory.comp_def |> arch_spec |> cv_trans_pre "";
Theorem stack_alloc_comp_pre[cv_pre,local]:
  ∀n m p. stack_alloc_comp_pre n m p
Proof
  ho_match_mp_tac stack_allocTheory.comp_ind \\ rw [] \\ simp [Once pre]
QED

val _ = stack_allocTheory.prog_comp_def |> arch_spec |> cv_trans;
val _ = stack_allocTheory.compile_def |> arch_spec |> SRULE [stack_allocTheory.stubs_def]
                                                   |> cv_auto_trans;

val _ = stack_rawcallTheory.seq_stack_alloc_def |> arch_spec |> cv_trans;
val _ = stack_rawcallTheory.collect_info_def |> arch_spec |> cv_trans;
val _ = stack_rawcallTheory.dest_case_def |> arch_spec |> cv_trans;
val _ = stack_rawcallTheory.comp_seq_def |> arch_spec |> cv_trans;
val _ = stack_rawcallTheory.comp_def |> arch_spec |> cv_trans;
val _ = stack_rawcallTheory.comp_top_def |> arch_spec |> cv_trans;
val _ = stack_rawcallTheory.compile_def |> arch_spec |> cv_auto_trans;
val _ = stack_to_labTheory.compile_def |> arch_spec |> cv_auto_trans;
val _ = word_to_stackTheory.format_var_def |> cv_trans;
val _ = word_to_stackTheory.wReg1_def |> arch_spec |> cv_trans;
val _ = word_to_stackTheory.wReg2_def |> arch_spec |> cv_trans;
val _ = word_to_stackTheory.wStackLoad_def |> arch_spec |> cv_trans;
val _ = word_to_stackTheory.wStackStore_def |> arch_spec |> cv_trans;
val _ = word_to_stackTheory.wMoveSingle_def |> arch_spec |> cv_trans;
val _ = word_to_stackTheory.wMoveAux_def |> arch_spec |> cv_trans;
val _ = word_to_stackTheory.wInst_def |> arch_spec |> cv_auto_trans;
val _ = word_to_stackTheory.wMove_def |> arch_spec |> cv_auto_trans;
val _ = word_to_stackTheory.bits_to_word_def |> arch_spec |> cv_trans;

Theorem cv_DROP_lemma[local]:
  ∀n cv_xs. cv_size (cv_DROP (Num n) cv_xs) ≤ cv_size cv_xs
Proof
  Induct \\ rw [] \\ simp [Once cv_DROP_def]
  \\ Cases_on ‘cv_xs’ \\ gvs []
  \\ irule LESS_EQ_TRANS
  \\ pop_assum $ irule_at Any \\ gvs []
QED

val _ = cv_trans_rec (word_to_stackTheory.word_list_def |> arch_spec)
 (WF_REL_TAC ‘measure $ cv_size o FST’ \\ Cases \\ rw []
  \\ Cases_on ‘cv_d’ \\ gvs []
  >- (last_x_assum mp_tac \\ simp [cv_LENGTH_def,Once cv_LEN_def] \\ gvs [])
  \\ rename [‘Num n’] \\ Cases_on ‘n’ \\ gvs []
  \\ simp [Once cv_DROP_def]
  \\ irule LESS_EQ_LESS_TRANS \\ irule_at Any cv_DROP_lemma \\ gvs []);

val _ = word_to_stackTheory.write_bitmap_def |> arch_spec |> SRULE [] |> cv_auto_trans;
val _ = word_to_stackTheory.wLive_def |> arch_spec |> cv_trans;
val _ = word_to_stackTheory.SeqStackFree_def |> arch_spec |> cv_trans;
val _ = word_to_stackTheory.call_dest_def |> arch_spec |> cv_auto_trans;
val _ = word_to_stackTheory.stack_free_def |> arch_spec |> cv_trans;
val _ = word_to_stackTheory.stack_move_def |> arch_spec |> cv_trans;
val _ = word_to_stackTheory.StackArgs_def |> arch_spec |> cv_trans;
val _ = word_to_stackTheory.StackHandlerArgs_def |> arch_spec |> cv_trans;
val _ = word_to_stackTheory.PushHandler_def |> arch_spec |> cv_trans;
val _ = word_to_stackTheory.PopHandler_def |> arch_spec |> cv_trans;
val _ = word_to_stackTheory.chunk_to_bits_def |> arch_spec |> cv_trans;
val _ = word_to_stackTheory.chunk_to_bitmap_def |> arch_spec |> cv_trans;
val _ = word_to_stackTheory.raise_stub_def |> arch_spec |> cv_trans;
val _ = word_to_stackTheory.store_consts_stub_def |> arch_spec |> cv_trans;
val _ = word_to_stackTheory.copy_ret_def |> arch_spec |> cv_auto_trans;

Theorem cv_rep_if_lt[cv_rep]:
  cv_rep p1a c1a Num m /\
  cv_rep p1b c1b Num n /\
  cv_rep p2 c2 f t /\
  cv_rep p3 c3 f e ==>
  cv_rep (p1a /\ p1b /\ (m < n ==> p2) /\ (~(m < n) ==> p3))
         (cv_if (cv_sub c1b c1a) c2 c3) f (if m < n then t else e)
Proof
  fs [cv_repTheory.cv_rep_def] \\ rw [] \\ gvs []
  \\ Cases_on ‘n - m’ \\ gvs []
QED

val _ = cv_trans_rec (word_to_stackTheory.const_words_to_bitmap_def |> arch_spec |> SRULE [])
 (WF_REL_TAC ‘measure $ cv$c2n o SND’ \\ Cases \\ gvs []
  \\ gvs [cvTheory.c2b_def] \\ Cases_on ‘m’ \\ gvs []);

val _ = wordLangTheory.max_var_inst_def |> arch_spec |> cv_trans

val pre = max_var_exp_eq |> arch_spec |> cv_trans_pre "";
Theorem wordLang_max_var_exp_pre[cv_pre]:
  (∀v. wordLang_max_var_exp_pre v) ∧
  (∀v. backend_cv_max_var_exp_list_pre v)
Proof
  ho_match_mp_tac wordLangTheory.exp_induction \\ rw [] \\ simp [Once pre]
QED

val _ = wordLangTheory.max_var_def |> arch_spec |> cv_auto_trans;

val pre = every_stack_var'_eq |> arch_spec |> cv_trans_pre "";
Theorem backend_cv_every_stack_var'_pre[cv_pre]:
  ∀v m. backend_cv_every_stack_var'_pre m v
Proof
  ho_match_mp_tac (wordLangTheory.every_stack_var_ind
    |> Q.SPEC ‘λx. Q’ |> SRULE [] |> GEN_ALL)
  \\ rw [] \\ simp [Once pre]
QED

val _ = apply_colour_imm'_eq |> arch_spec |> cv_trans;
val _ = apply_colour_inst'_eq |> arch_spec |> cv_trans;

val pre = apply_colour_exp'_eq |> arch_spec |> cv_trans_pre "";
Theorem backend_cv_apply_colour_exp'_pre[cv_pre]:
  (∀v colour. backend_cv_apply_colour_exp'_pre colour v) ∧
  (∀v colour. backend_cv_apply_colour_exp'_list_pre colour v)
Proof
  ho_match_mp_tac wordLangTheory.exp_induction \\ rw [] \\ simp [Once pre]
QED

val pre = apply_colour'_eq |> arch_spec |> cv_auto_trans_pre "";
Theorem apply_colour'_pre[cv_pre]:
  ∀v colour. backend_cv_apply_colour'_pre colour v
Proof
  ho_match_mp_tac (word_allocTheory.apply_colour_ind
                  |> Q.SPEC ‘λx. Q’ |> SRULE [] |> GEN_ALL)
  \\ rw [] \\ simp [Once pre]
QED

val _ = oracle_colour_ok_eq |> arch_spec |> cv_auto_trans;

val pre = get_reads_exp_eq |> arch_spec |> cv_trans_pre "";
Theorem word_alloc_get_reads_exp_pre[cv_pre]:
  (∀v. word_alloc_get_reads_exp_pre v) ∧
  (∀v. backend_cv_get_reads_exp_list_pre v)
Proof
  ho_match_mp_tac wordLangTheory.exp_induction \\ rw [] \\ simp [Once pre]
QED

val _ = word_allocTheory.get_delta_inst_def |> arch_spec |> cv_trans;
val _ = word_allocTheory.get_clash_tree_def |> arch_spec |> cv_trans;
val _ = word_removeTheory.remove_must_terminate_def |> arch_spec |> cv_trans;

val pre = word_allocTheory.remove_dead_def |> arch_spec |> cv_auto_trans_pre "";
Theorem word_alloc_remove_dead_pre[cv_pre]:
  ∀v live nlive. word_alloc_remove_dead_pre v live nlive
Proof
  ho_match_mp_tac word_allocTheory.remove_dead_ind \\ rw [] \\ simp [Once pre]
QED

val _ = word_allocTheory.remove_dead_prog_def |> arch_spec |> cv_trans;

val _ = word_instTheory.op_consts_def |> arch_spec |> cv_trans;

val _ = word_instTheory.reduce_const_def |> arch_spec |> cv_auto_trans;

val _ = wordLangTheory.word_op_def |> arch_spec |> cv_auto_trans;

val pre = word_instTheory.optimize_consts_def |> arch_spec |> cv_auto_trans_pre "";
Theorem optimize_consts_pre:
  ∀op ls. op ≠ Sub ⇒ word_inst_optimize_consts_pre op ls
Proof
  simp [Once pre]
  \\ gvs [wordLangTheory.word_op_def |> oneline, AllCaseEqs()]
  \\ rw [] \\ gvs []
  \\ Cases_on ‘PARTITION is_const ls’ \\ gvs []
  \\ Cases_on ‘op’ \\ gvs []
QED

val _ = word_instTheory.convert_sub_def |> arch_spec |> cv_auto_trans;

val pre = pull_exp_eq |> arch_spec |> cv_trans_pre "";
Theorem word_inst_pull_exp_pre[cv_pre]:
  (∀v. word_inst_pull_exp_pre v) ∧
  (∀v. backend_cv_pull_exp_list_pre v)
Proof
  ho_match_mp_tac wordLangTheory.exp_induction \\ rw [] \\ simp [Once pre]
  \\ rw [] \\ gvs [] \\ TRY (pop_assum mp_tac \\ simp [Once pre] \\ NO_TAC)
  \\ irule optimize_consts_pre \\ gvs []
QED

val pre = flatten_exp_eq |> arch_spec |> cv_trans_pre "";
Theorem word_inst_flatten_exp_pre[cv_pre]:
  (∀v. word_inst_flatten_exp_pre v) ∧
  (∀v. backend_cv_flatten_exp_list_pre v)
Proof
  qsuff_tac
    ‘∀n. (∀v. exp_size (K 0) v = n ⇒ word_inst_flatten_exp_pre v) ∧
         (∀v. list_size (exp_size (K 0)) v = n ⇒ backend_cv_flatten_exp_list_pre v)’
  >- metis_tac []
  \\ completeInduct_on ‘n’ \\ reverse (rw []) \\ gvs [PULL_FORALL]
  \\ simp [Once pre]
QED

val _ = cv_trans word_instTheory.three_to_two_reg_def;

val _ = cv_trans word_instTheory.three_to_two_reg_prog_def;

val _ = word_cseTheory.add_to_data_aux_def |> arch_spec
         |> SRULE [GSYM lookup_listCmp_def, GSYM insert_listCmp_def] |> cv_auto_trans;
val _ = word_cseTheory.wordToNum_def |> arch_spec |> cv_trans;
val _ = word_cseTheory.regImmToNumList_def |> arch_spec |> cv_trans;
val _ = word_cseTheory.arithToNumList_def |> arch_spec |> cv_trans;
val _ = word_cseTheory.instToNumList_def |> arch_spec |> cv_trans;
val _ = word_cseTheory.add_to_data_def |> arch_spec |> cv_trans;
val _ = word_cseTheory.word_cseInst_def |> arch_spec |> cv_trans;
val _ = word_cseTheory.word_cse_def |> arch_spec |> cv_trans;
val _ = word_cseTheory.word_common_subexp_elim_def |> arch_spec |> cv_trans;

val _ = word_allocTheory.limit_var_def |> arch_spec |> cv_trans;
val _ = word_allocTheory.setup_ssa_def |> arch_spec |> cv_trans;
val _ = word_allocTheory.ssa_cc_trans_inst_def |> arch_spec |> cv_trans;

val pre = ssa_cc_trans_exp_eq |> arch_spec |> cv_trans_pre "";
Theorem word_alloc_ssa_cc_trans_exp_pre[cv_pre,local]:
  (∀v t. word_alloc_ssa_cc_trans_exp_pre t v) ∧
  (∀v t. backend_cv_ssa_cc_trans_exp_list_pre t v)
Proof
  ho_match_mp_tac wordLangTheory.exp_induction \\ rw [] \\ simp [Once pre]
QED

val pre = word_allocTheory.ssa_cc_trans_def |> arch_spec |> cv_auto_trans_pre "";
Theorem word_alloc_ssa_cc_trans_pre[cv_pre]:
  ∀v ssa na. word_alloc_ssa_cc_trans_pre v ssa na
Proof
  ho_match_mp_tac word_allocTheory.ssa_cc_trans_ind \\ rw[] \\ simp [Once pre]
QED

val _ = word_allocTheory.full_ssa_cc_trans_def |> arch_spec |> cv_trans;

val _ = word_simpTheory.SmartSeq_def |> arch_spec |> cv_trans;
val _ = word_simpTheory.Seq_assoc_def |> arch_spec |> cv_trans;
val _ = word_simpTheory.const_fp_inst_cs_def |> arch_spec |> cv_trans;
val _ = word_simpTheory.strip_const_def |> arch_spec |> cv_trans;
val _ = wordLangTheory.word_sh_def |> arch_spec
          |> SRULE [GREATER_EQ,wordsTheory.word_asr_n2w] |> cv_trans;

val pre = const_fp_exp_eq |> arch_spec |> cv_auto_trans_pre "";
Theorem word_simp_const_fp_exp_pre[cv_pre,local]:
  (∀t v. word_simp_const_fp_exp_pre t v) ∧
  (∀t v. backend_cv_const_fp_exp_list_pre t v)
Proof
  ho_match_mp_tac wordLangTheory.exp_induction \\ rw [] \\ simp [Once pre]
QED

val pre = word_simpTheory.const_fp_loop_def |> arch_spec |> cv_auto_trans_pre "";
Theorem word_simp_const_fp_loop_pre[cv_pre,local]:
  ∀v cs. word_simp_const_fp_loop_pre v cs
Proof
  ho_match_mp_tac word_simpTheory.const_fp_loop_ind \\ rw[] \\ simp [Once pre]
QED

val _ = word_simpTheory.const_fp_def |> arch_spec |> cv_trans;
val _ = word_simpTheory.is_simple_def |> arch_spec |> cv_trans;
val _ = word_simpTheory.dest_Raise_num_def |> arch_spec |> cv_trans;
val _ = word_simpTheory.try_if_hoist2_def |> arch_spec |> cv_trans;
val _ = word_simpTheory.rewrite_duplicate_if_max_reassoc_def |> arch_spec |> cv_trans;
val _ = word_simpTheory.try_if_hoist1_def |> arch_spec |> cv_trans;
val _ = word_simpTheory.simp_duplicate_if_def |> arch_spec |> cv_trans;
val _ = word_simpTheory.compile_exp_def |> arch_spec |> cv_trans;

val _ = data_to_wordTheory.real_addr_def |> arch_spec
          |> SRULE [backend_commonTheory.word_shift_def] |> cv_trans;
val _ = data_to_wordTheory.real_offset_def |> arch_spec |> SRULE [] |> cv_trans;
val _ = data_to_wordTheory.real_byte_offset_def |> arch_spec |> SRULE [] |> cv_trans;
val _ = data_to_wordTheory.make_header_def |> arch_spec |> SRULE [] |> cv_trans;
val _ = data_to_wordTheory.make_byte_header_def |> arch_spec |> SRULE [] |> cv_trans;
val _ = data_to_wordTheory.encode_header_def |> arch_spec |> SRULE [] |> cv_trans;
val _ = data_to_wordTheory.adjust_sets_def |> cv_trans;
val _ = data_to_wordTheory.GiveUp_def |> arch_spec |> SRULE [] |> cv_trans;
val _ = data_to_wordTheory.BignumHalt_def |> arch_spec |> SRULE [] |> cv_trans;
val _ = data_to_wordTheory.list_Seq_def |> arch_spec |> cv_trans;
val _ = data_to_wordTheory.SilentFFI_def |> arch_spec |> SRULE [] |> cv_trans;
val _ = data_to_wordTheory.ShiftVar_def |> arch_spec |> SRULE [] |> cv_trans;
val _ = data_to_wordTheory.AllocVar_def |> arch_spec |> SRULE [] |> cv_trans;
val _ = data_to_wordTheory.StoreEach_def |> arch_spec |> SRULE [] |> cv_trans;
val _ = data_to_wordTheory.WriteWord64_def |> arch_spec |> SRULE [] |> cv_trans;
val _ = data_to_wordTheory.WriteWord64_on_32_def |> arch_spec |> SRULE [] |> cv_trans;
val _ = data_to_wordTheory.WriteWord32_on_32_def |> arch_spec |> SRULE [] |> cv_trans;
val _ = data_to_wordTheory.WordShift64_on_32_def |> arch_spec |> SRULE [] |> cv_trans;
val _ = data_to_wordTheory.WordOp64_on_32_def |> arch_spec |> SRULE [] |> cv_trans;
val _ = data_to_wordTheory.LoadBignum_def |> arch_spec |> SRULE [] |> cv_trans;
val _ = data_to_wordTheory.LoadWord64_def |> arch_spec |> SRULE [] |> cv_trans;
val _ = data_to_wordTheory.AnyHeader_def |> arch_spec |> SRULE [] |> cv_trans;
val _ = data_to_wordTheory.tag_mask_def |> arch_spec |> SRULE [] |> cv_trans;
val _ = data_to_wordTheory.AddNumSize_def |> arch_spec |> SRULE [] |> cv_trans;
val _ = data_to_wordTheory.SmallLsr_def |> arch_spec |> SRULE [] |> cv_trans;
val _ = data_to_wordTheory.Smallnum_def |> arch_spec |> SRULE [] |> cv_trans;
val _ = data_to_wordTheory.WriteLastByte_aux_def |> arch_spec |> SRULE [] |> cv_trans;
val _ = data_to_wordTheory.WriteLastBytes_def |> arch_spec |> SRULE [] |> cv_trans;
val _ = data_to_wordTheory.MakeBytes_def |> arch_spec |> SRULE [] |> cv_trans;
val _ = data_to_wordTheory.all_ones_def |> arch_spec |> SRULE []
        |> SRULE [wordsTheory.word_2comp_n2w,wordsTheory.word_slice_n2w] |> cv_trans;
val _ = cv_trans GREATER_DEF;
val _ = data_to_wordTheory.maxout_bits_def |> arch_spec
        |> SRULE [GSYM GREATER_DEF] |> cv_trans;
val _ = data_to_wordTheory.ptr_bits_def |> arch_spec |> SRULE [] |> cv_trans;
val _ = data_to_wordTheory.Maxout_bits_code_def |> arch_spec
          |> SRULE [backend_commonTheory.word_shift_def] |> cv_trans;
val _ = data_to_wordTheory.Make_ptr_bits_code_def |> arch_spec
          |> SRULE [backend_commonTheory.word_shift_def] |> cv_trans;
val _ = byteTheory.byte_index_def |> arch_spec |> cv_trans;

val _ = cv_trans byteTheory.set_byte_32 handle HOL_ERR _ =>
        cv_trans byteTheory.set_byte_64;

val _ = byteTheory.bytes_to_word_def |> arch_spec |> cv_trans;
val _ = data_to_wordTheory.write_bytes_def |> arch_spec |> SRULE [LET_THM] |> cv_trans;
val _ = data_to_wordTheory.lookup_mem_def |> arch_spec |> cv_trans;

val pre = cv_trans_pre_rec ""
  (multiwordTheory.n2mw_def |> SRULE [n2w_mod] |> arch_spec |> SRULE [])
  (WF_REL_TAC ‘measure cv$c2n’
   \\ Cases \\ gvs [DIV_LT_X] \\ Cases_on ‘m’ \\ gvs []);
Theorem multiword_2mw_pre[cv_pre]:
  ∀n. multiword_n2mw_pre n
Proof
  ho_match_mp_tac (multiwordTheory.n2mw_ind |> arch_spec)
  \\ rw [] \\ simp [Once pre]
QED

Theorem lemma[local]:
  ∀i. Num (ABS i) = Num i
Proof
  Cases \\ gvs []
QED

val _ = multiwordTheory.i2mw_def |> arch_spec |> SRULE [lemma] |> cv_trans;

val _ = data_to_wordTheory.part_to_words_def |> arch_spec
          |> SRULE [backend_commonTheory.word_shift_def,GSYM GREATER_DEF,
                    data_to_wordTheory.small_int_def,
                    data_to_wordTheory.byte_len_def] |> cv_auto_trans;
val _ = data_to_wordTheory.parts_to_words_def |> arch_spec
          |> SRULE [backend_commonTheory.word_shift_def] |> cv_trans;
val _ = data_to_wordTheory.const_parts_to_words_def |> arch_spec
          |> SRULE [backend_commonTheory.word_shift_def] |> cv_trans;
val _ = data_to_wordTheory.MemEqList_def |> arch_spec |> cv_trans;
val _ = data_to_wordTheory.get_Word_def |> arch_spec |> cv_trans;
val _ = get_words_def |> arch_spec |> cv_trans;
val _ = data_to_wordTheory.getWords_def |> arch_spec_beta |> cv_trans;
val cv_getWords_def = fetch "-" "cv_data_to_word_getWords_def";

Theorem cv_getWords_lemma[local]:
  ∀g acc. cv_size (cv_snd (cv_data_to_word_getWords g acc)) ≤ cv_size g
Proof
  Induct \\ gvs []
  \\ simp [Once cv_getWords_def]
  \\ rpt gen_tac
  \\ rpt (IF_CASES_TAC \\ gvs [])
  \\ irule LESS_EQ_TRANS
  \\ first_x_assum $ irule_at $ Pos hd \\ gvs []
QED

val pre = cv_trans_pre_rec "" (data_to_wordTheory.StoreAnyConsts_def |> arch_spec)
  (WF_REL_TAC ‘measure $ λ(_,_,_,xs,_). cv_size xs’
   \\ reverse (rw []) >- cv_termination_tac
   \\ simp [Once cv_getWords_def]
   \\ Cases_on ‘cv_v’ \\ gvs []
   \\ Cases_on ‘g’ \\ gvs []
   \\ irule LESS_EQ_LESS_TRANS
   \\ irule_at Any cv_getWords_lemma \\ gvs []);

Theorem data_to_word_StoreAnyConsts_pre[cv_pre]:
  ∀r1 r2 r3 v v0. data_to_word_StoreAnyConsts_pre r1 r2 r3 v v0
Proof
  ho_match_mp_tac data_to_wordTheory.StoreAnyConsts_ind \\ rw [] \\ simp [Once pre]
QED

val locs_thm =
  DB.find "location_def" |> map fst |> filter (fn s => fst s = "data_to_word") |> map snd
  |> map (fetch "data_to_word") |> map (EVAL o lhs o concl) |> LIST_CONJ;

val code_defs =
  DB.find "_code_def" |> map fst |> filter (fn s => fst s = "data_to_word") |> map snd
  |> map (fetch "data_to_word");

Theorem inline = [data_to_wordTheory.Unit_def,
                  backend_commonTheory.partial_app_tag_def,
                  backend_commonTheory.closure_tag_def,
                  locs_thm, to_adjust_vars, COND_RATOR,
                  GSYM GREATER_DEF, to_get_words,
                  backend_commonTheory.word_shift_def,
                  data_to_wordTheory.list_Seq_def] |> LIST_CONJ;

val assigns =
  code_defs @ (data_to_wordTheory.all_assign_defs |> CONJUNCTS)
  |> map (SRULE [inline] o arch_spec) |> rev;

val problem_count = assigns
  |> mapi (fn i => fn th => (i+1,th))
  |> filter (fn (i,th) => not (can cv_trans th)) |> map fst
  |> map (fn i => print ("cv_trans (el " ^ int_to_string i ^ " assigns)\n"))
  |> length

val _ = problem_count = 0 orelse failwith("Some assign_def didn't translate")

val _ = cv_trans (data_to_wordTheory.assign_def |> arch_spec |> SRULE
  [data_to_wordTheory.arg1_def, to_adjust_vars,
   data_to_wordTheory.arg2_def,
   data_to_wordTheory.arg3_def,
   data_to_wordTheory.arg4_def])

val _ = cv_trans (data_to_wordTheory.force_thunk_def |> arch_spec);

val pre = data_to_wordTheory.comp_def |> arch_spec |> SRULE [to_adjust_vars] |> cv_trans_pre "";
Theorem data_to_word_comp_pre[cv_pre,local]:
  ∀c secn l p. data_to_word_comp_pre c secn l p
Proof
  ho_match_mp_tac (data_to_wordTheory.comp_ind |> arch_spec)
  \\ rw [] \\ simp [Once pre]
QED

val _ = data_to_wordTheory.compile_part_def |> arch_spec |> cv_trans;
val _ = map_compile_part_def |> arch_spec |> cv_trans;

val _ = word_bignumTheory.generated_bignum_stubs_def
  |> SPEC_ALL |> CONV_RULE (RAND_CONV EVAL) |> arch_spec |> SRULE [] |> cv_trans;

val _ = word_allocTheory.get_prefs_def |> arch_spec |> cv_auto_trans;
val _ = word_allocTheory.add1_lhs_const_def |> arch_spec |> cv_trans;
val _ = word_allocTheory.add1_lhs_reg_def |> arch_spec |> cv_trans;
val _ = word_allocTheory.add1_rhs_reg_def |> arch_spec |> cv_trans;
val _ = word_allocTheory.add1_lhs_mem_def |> arch_spec |> cv_trans;
val _ = word_allocTheory.add1_rhs_mem_def |> arch_spec |> cv_trans;
val _ = word_allocTheory.get_heu_inst_def |> arch_spec |> cv_trans;

val pre = word_allocTheory.get_heu_def |> arch_spec |> cv_auto_trans_pre "";
Theorem word_alloc_get_heu_pre[cv_pre]:
  ∀fc v0 v. word_alloc_get_heu_pre fc v0 v
Proof
  simp [FORALL_PROD]
  \\ ho_match_mp_tac word_allocTheory.get_heu_ind \\ rw [] \\ simp [Once pre]
QED

val _ = word_allocTheory.get_heuristics_def |> arch_spec |> cv_auto_trans;
