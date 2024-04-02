(*
  Translate arch-size-specific functions to cv equations.
*)
open preamble cv_transLib cv_stdTheory backend_cvTheory;
open backendTheory;

val _ = new_theory "backend_64_cv";

fun allowing_rebind f = Feedback.trace ("Theory.allow_rebinds", 1) f
val cv_trans_pre = allowing_rebind cv_trans_pre;
val cv_auto_trans_pre = allowing_rebind cv_auto_trans_pre;

val arch_spec = INST_TYPE [alpha |-> “:64”];
val arch_spec_beta = INST_TYPE [beta |-> “:64”];

val _ = cv_trans (alignmentTheory.aligned_w2n |> arch_spec);;
val _ = cv_trans (asmTheory.offset_ok_def |> arch_spec);
val _ = cv_trans (lab_to_targetTheory.section_labels_def |> arch_spec);
val _ = cv_trans (lab_to_targetTheory.compute_labels_alt_def |> arch_spec);
val _ = cv_trans (lab_to_targetTheory.lines_upd_lab_len_def |> arch_spec);
val _ = cv_auto_trans (lab_to_targetTheory.get_jump_offset_def |> arch_spec);

val pre = cv_trans_pre (lab_to_targetTheory.upd_lab_len_def |> arch_spec);

Theorem upd_lab_len_pre[cv_pre]:
  ∀pos v. upd_lab_len_pre pos v
Proof
  Induct_on ‘v’ \\ simp [Once pre]
QED

val _ = cv_trans (lab_to_targetTheory.add_nop_def |> arch_spec);

val pre = cv_trans_pre (lab_to_targetTheory.pad_section_def |> arch_spec);

Theorem pad_section_pre[cv_pre,local]:
  ∀nop v aux. pad_section_pre nop v aux
Proof
  Induct_on ‘v’ \\ simp [Once pre]
QED

val _ = cv_trans (lab_to_targetTheory.pad_code_def |> arch_spec);

Theorem bytes_in_word_def[cv_inline] =
  bytes_in_word_def |> arch_spec |> CONV_RULE (RAND_CONV EVAL);

Theorem shift_def[cv_inline] =
  backend_commonTheory.word_shift_def |> arch_spec |> CONV_RULE (RAND_CONV EVAL);

val _ = data_to_wordTheory.get_gen_size_def |> arch_spec |> SRULE [] |> cv_trans;

val _ = stack_to_labTheory.compile_jump_def |> arch_spec |> cv_trans;
val _ = stack_to_labTheory.is_Seq_def |> arch_spec |> cv_trans;

val pre = stack_to_labTheory.flatten_def |> arch_spec |> cv_trans_pre;
Theorem flatten_pre[cv_pre,local]:
  ∀t p n m. flatten_pre t p n m
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

val pre = stack_allocTheory.comp_def |> arch_spec |> cv_trans_pre;
Theorem comp_pre[cv_pre,local]:
  ∀n m p. comp_pre n m p
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
val _ = word_to_stackTheory.wRegImm2_def |> arch_spec |> cv_trans;
val _ = word_to_stackTheory.wStackLoad_def |> arch_spec |> cv_trans;
val _ = word_to_stackTheory.wStackStore_def |> arch_spec |> cv_trans;
val _ = word_to_stackTheory.wMoveSingle_def |> arch_spec |> cv_trans;
val _ = word_to_stackTheory.wMoveAux_def |> arch_spec |> cv_trans;
val _ = word_to_stackTheory.wInst_def |> arch_spec |> cv_auto_trans;
val _ = word_to_stackTheory.wMove_def |> arch_spec |> cv_auto_trans;
val _ = word_to_stackTheory.bits_to_word_def |> arch_spec |> cv_trans;

Triviality cv_DROP_lemma:
  ∀n cv_xs. cv_sum_depth (cv_DROP (Num n) cv_xs) ≤ cv_sum_depth cv_xs
Proof
  Induct \\ rw [] \\ simp [Once cv_DROP_def]
  \\ Cases_on ‘cv_xs’ \\ gvs []
  \\ irule LESS_EQ_TRANS
  \\ pop_assum $ irule_at Any \\ gvs []
QED

val _ = cv_trans_rec (word_to_stackTheory.word_list_def |> arch_spec)
 (WF_REL_TAC ‘measure $ cv_sum_depth o FST’ \\ Cases \\ rw []
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

Theorem cv_rep_if_lt[cv_rep]:
  cv_rep p1 c1a Num m /\
  cv_rep p1 c1b Num n /\
  cv_rep p2 c2 f t /\
  cv_rep p3 c3 f e ==>
  cv_rep (p1 /\ (m < n ==> p2) /\ (~(m < n) ==> p3))
         (cv_if (cv_sub c1b c1a) c2 c3) f (if m < n then t else e)
Proof
  fs [cv_repTheory.cv_rep_def] \\ rw [] \\ gvs []
  \\ Cases_on ‘n - m’ \\ gvs []
QED

val _ = cv_trans_rec (word_to_stackTheory.const_words_to_bitmap_def |> arch_spec |> SRULE [])
 (WF_REL_TAC ‘measure $ cv$c2n o SND’ \\ Cases \\ gvs []
  \\ gvs [cvTheory.c2b_def] \\ Cases_on ‘m’ \\ gvs []);

val pre = word_to_stackTheory.comp_def |> arch_spec |> cv_auto_trans_pre;
Theorem comp_pre[cv_pre,local]:
  ∀v bs kf. comp_pre v bs kf
Proof
  ho_match_mp_tac word_to_stackTheory.comp_ind \\ rw [] \\ simp [Once pre]
QED

val _ = cv_trans miscTheory.list_max_def;
val _ = cv_trans (miscTheory.max3_def |> PURE_REWRITE_RULE [GREATER_DEF]);

val _ = wordLangTheory.max_var_inst_def |> arch_spec |> cv_trans

val _ = max_var_word_exp_def |> arch_spec |> cv_trans

val _ = wordLangTheory.max_var_def |> arch_spec |> cv_trans;
val _ = word_to_stackTheory.compile_prog_def |> arch_spec |> cv_trans;

val pre = word_to_stackTheory.compile_word_to_stack_def |> arch_spec_beta |> cv_trans_pre;
Theorem compile_word_to_stack_pre[cv_pre]:
  ∀k v bitmaps. compile_word_to_stack_pre k v bitmaps
Proof
  ho_match_mp_tac word_to_stackTheory.compile_word_to_stack_ind
  \\ rw [] \\ simp [Once pre]
QED

val arch_spec = INST_TYPE [alpha |-> “:64”];
val arch_spec_beta = INST_TYPE [beta |-> “:64”];

val pre = every_stack_var'_eq |> arch_spec |> cv_trans_pre
Theorem every_stack_var'_pre[cv_pre]:
  ∀v m. every_stack_var'_pre m v
Proof
  ho_match_mp_tac (wordLangTheory.every_stack_var_ind
    |> Q.SPEC ‘λx. Q’ |> SRULE [] |> GEN_ALL)
  \\ rw [] \\ simp [Once pre]
QED

val _ = apply_colour_imm'_eq |> arch_spec |> cv_trans;
val _ = apply_colour_inst'_eq |> arch_spec |> cv_trans;

val pre = apply_colour_exp'_eq |> arch_spec |> cv_trans_pre;
Theorem apply_colour_exp'_pre[cv_pre]:
  (∀v colour. apply_colour_exp'_pre colour v) ∧
  (∀v colour. apply_colour_exp'_list_pre colour v)
Proof
  ho_match_mp_tac wordLangTheory.exp_induction \\ rw [] \\ simp [Once pre]
QED

val pre = apply_colour'_eq |> arch_spec |> cv_auto_trans_pre;
Theorem apply_colour'_pre[cv_pre]:
  ∀v colour. apply_colour'_pre colour v
Proof
  ho_match_mp_tac (word_allocTheory.apply_colour_ind
                  |> Q.SPEC ‘λx. Q’ |> SRULE [] |> GEN_ALL)
  \\ rw [] \\ simp [Once pre]
QED

val _ = oracle_colour_ok_eq |> arch_spec |> cv_auto_trans;

val pre = get_reads_exp_eq |> arch_spec |> cv_trans_pre;
Theorem get_reads_exp_pre[cv_pre]:
  (∀v. get_reads_exp_pre v) ∧
  (∀v. get_reads_exp_list_pre v)
Proof
  ho_match_mp_tac wordLangTheory.exp_induction \\ rw [] \\ simp [Once pre]
QED

val _ = word_allocTheory.get_delta_inst_def |> arch_spec |> cv_trans;
val _ = word_allocTheory.get_clash_tree_def |> arch_spec |> cv_trans;
val _ = word_removeTheory.remove_must_terminate_def |> arch_spec |> cv_trans;

val _ = export_theory();
