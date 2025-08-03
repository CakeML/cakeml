(*
  Translate ag32-specialised functions to cv equations.
*)
open preamble cv_transLib cv_stdTheory backend_cvTheory backend_32_cvTheory;
open backend_ag32Theory ag32Theory ag32_targetTheory to_data_cvTheory;
open export_ag32Theory ag32_configTheory;

val _ = new_theory "backend_ag32_cv";

(*---------------------------------------------------------------------------*
  Translation of instruction encoder
 *---------------------------------------------------------------------------*)

Theorem IN_INSERT[cv_inline,local] = IN_INSERT;
Theorem NOT_IN_EMPTY[cv_inline,local] = NOT_IN_EMPTY;

val _ = cv_trans ag32Theory.funcT2num_thm;
val _ = cv_trans ag32Theory.shiftT2num_thm;
val _ = cv_trans ag32Theory.ri2bits_def;
val _ = cv_trans ag32Theory.enc_def;
val _ = cv_trans ag32Theory.encShift_def;
val _ = cv_trans ag32Theory.Encode_def;
val _ = cv_trans ag32_targetTheory.ag32_encode1_def;
val _ = cv_trans ag32_targetTheory.ag32_constant_def;
val _ = cv_trans ag32_targetTheory.ag32_jump_constant_def;
val _ = cv_trans ag32_targetTheory.ag32_cmp_def;
val _ = cv_trans ag32_targetTheory.ag32_bop_def;
val _ = cv_trans ag32_targetTheory.ag32_sh_def;

val _ = cv_auto_trans (ag32_targetTheory.ag32_encode_def
                         |> SRULE [LIST_BIND_def,FUN_EQ_THM]);

val _ = cv_trans ag32_targetTheory.ag32_enc_def;

(*---------------------------------------------------------------------------*
  Remaining ag32-specific functions
 *---------------------------------------------------------------------------*)

val pre = cv_auto_trans_pre "" comp_ag32_def;

Theorem comp_ag32_pre[cv_pre,local]:
  ∀v bs kf. comp_ag32_pre v bs kf
Proof
  gen_tac \\ completeInduct_on ‘prog_size (K 0) v’
  \\ rw [] \\ gvs [PULL_FORALL]
  \\ rw [] \\ simp [Once pre]
  \\ rw [] \\ gvs []
  \\ last_x_assum irule
  \\ gvs [wordLangTheory.prog_size_def]
QED

val _ = cv_auto_trans compile_prog_ag32_def;

val pre = cv_auto_trans_pre "" compile_word_to_stack_ag32_def;

Theorem compile_word_to_stack_ag32_pre[cv_pre]:
  ∀k v bitmaps. compile_word_to_stack_ag32_pre k v bitmaps
Proof
  Induct_on`v`
  \\ rw [] \\ simp [Once pre]
QED

Triviality fp_ok_false:
  fp_ok_ag32 v = F
Proof
  Cases_on ‘v’ \\ gvs [fp_ok_ag32_def |> SRULE [fp_reg_ok_ag32_def]]
QED

val _ = cv_auto_trans (inst_ok_ag32_def
          |> SRULE [fp_ok_false,alignmentTheory.aligned_w2n,asmTheory.offset_ok_def,LET_THM]);

val _ = cv_auto_trans (asm_ok_ag32_def
          |> SRULE [alignmentTheory.aligned_w2n,asmTheory.offset_ok_def,LET_THM]);

val _ = cv_auto_trans line_ok_light_ag32_def;
val _ = cv_auto_trans sec_ok_light_ag32_def;

val pre = cv_trans_pre "" enc_lines_again_ag32_def;

Theorem enc_lines_again_ag32_pre[cv_pre,local]:
  ∀labs ffis pos v0 v. enc_lines_again_ag32_pre labs ffis pos v0 v
Proof
  Induct_on ‘v0’ \\ simp [Once pre]
QED

val pre = cv_trans_pre "" enc_secs_again_ag32_def;

Theorem enc_secs_again_ag32_pre[cv_pre,local]:
  ∀pos labs ffis v. enc_secs_again_ag32_pre pos labs ffis v
Proof
  Induct_on ‘v’ \\ simp [Once pre]
QED

val pre = cv_auto_trans_pre "" remove_labels_loop_ag32_def;

Theorem remove_labels_loop_ag32_pre[cv_pre]:
  ∀clock pos init_labs ffis sec_list.
    remove_labels_loop_ag32_pre clock pos init_labs ffis sec_list
Proof
  Induct_on ‘clock’ \\ simp [Once pre]
QED

val _ = cv_trans enc_line_ag32_def;
val _ = cv_auto_trans enc_sec_ag32_def;
val _ = cv_auto_trans enc_sec_list_ag32_def;
val _ = cv_trans remove_labels_ag32_def;
val _ = cv_auto_trans compile_lab_ag32_def;
val _ = cv_trans lab_to_target_ag32_def;
val _ = cv_trans from_lab_ag32_def;

val _ = cv_trans (from_stack_ag32_def
  |> SRULE [data_to_wordTheory.max_heap_limit_def,backend_commonTheory.word_shift_def]);

val _ = cv_auto_trans from_word_ag32_def;

val pre = cv_trans_pre "" get_forced_ag32_def;
Theorem get_forced_ag32_pre[cv_pre,local]:
  ∀v acc. get_forced_ag32_pre v acc
Proof
  gen_tac \\ completeInduct_on ‘prog_size (K 0) v’
  \\ rw [] \\ gvs [PULL_FORALL]
  \\ simp [Once pre] \\ rw []
  \\ gvs [] \\ last_x_assum $ irule
  \\ gvs [wordLangTheory.prog_size_def]
QED

val _ = cv_trans word_alloc_inlogic_ag32_def;

val pre = cv_trans_pre "" inst_select_exp_ag32_def;
Theorem inst_select_exp_ag32_pre[cv_pre]:
  ∀v tar temp. inst_select_exp_ag32_pre tar temp v
Proof
  gen_tac \\ completeInduct_on ‘exp_size (K 0) v’
  \\ rw [] \\ gvs [PULL_FORALL]
  \\ rw [] \\ simp [Once pre]
  \\ rw [] \\ gvs []
  \\ last_x_assum irule
  \\ gvs [wordLangTheory.exp_size_def]
QED

val pre = cv_trans_pre "" inst_select_ag32_def;
Theorem inst_select_ag32_pre[cv_pre,local]:
  ∀v temp. inst_select_ag32_pre temp v
Proof
  gen_tac \\ completeInduct_on ‘prog_size (K 0) v’
  \\ rw [] \\ gvs [PULL_FORALL]
  \\ simp [Once pre] \\ rw []
  \\ first_x_assum irule \\ gvs [wordLangTheory.prog_size_def]
QED

val pre = each_inlogic_ag32_def |> cv_trans_pre "";
Theorem each_inlogic_ag32_pre[cv_pre,local]:
  ∀v. each_inlogic_ag32_pre v
Proof
  Induct \\ rw [] \\ simp [Once pre]
QED

val _ = cv_trans word_to_word_inlogic_ag32_def;
val _ = cv_trans from_word_0_ag32_def;

val _ = cv_trans (compile_0_ag32_def
                    |> SRULE [data_to_wordTheory.stubs_def,
                              backend_32_cvTheory.inline,
                              to_map_compile_part]);

val _ = cv_trans backend_ag32Theory.to_word_0_ag32_def;
val _ = cv_auto_trans backend_ag32Theory.to_livesets_0_ag32_def;

(* export *)

val _ = cv_auto_trans
        (export_ag32Theory.ag32_export_def
           |> REWRITE_RULE [to_words_line_word,
                            to_words_line_byte,
                            split16_eq_chunks16]);

(* main translations below *)

val _ = cv_trans backend_ag32Theory.to_livesets_ag32_def;
val _ = cv_trans backend_ag32Theory.compile_cake_ag32_def;
val _ = cv_auto_trans backend_ag32Theory.compile_cake_explore_ag32_def;

(* lemma used by automation *)

Theorem set_asm_conf_ag32_backend_config:
  set_asm_conf ag32_backend_config ag32_config = ag32_backend_config
Proof
  irule backendTheory.set_asm_conf_id \\ EVAL_TAC
QED

val _ = Feedback.set_trace "TheoryPP.include_docs" 0;
val _ = export_theory();
