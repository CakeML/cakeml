(*
  Translate x64-specialised functions to cv equations.
*)
Theory backend_x64_cv[no_sig_docs]
Ancestors
  cv_std backend_cv backend_64_cv backend_x64 x64 x64_target
  to_data_cv export_x64 x64_config
Libs
  preamble cv_transLib

(*---------------------------------------------------------------------------*
  Translation of instruction encoder
 *---------------------------------------------------------------------------*)

Theorem IN_INSERT[cv_inline,local] = IN_INSERT;
Theorem NOT_IN_EMPTY[cv_inline,local] = NOT_IN_EMPTY;

val _ = cv_trans asmSemTheory.is_test_def;

Theorem total_num2Zreg[local]:
  total_num2Zreg n =
      if n = 1 then RCX else
      if n = 2 then RDX else
      if n = 3 then RBX else
      if n = 4 then RSP else
      if n = 5 then RBP else
      if n = 6 then RSI else
      if n = 7 then RDI else
      if n = 8 then zR8 else
      if n = 9 then zR9 else
      if n = 10 then zR10 else
      if n = 11 then zR11 else
      if n = 12 then zR12 else
      if n = 13 then zR13 else
      if n = 14 then zR14 else
      if n = 15 then zR15 else RAX
Proof
  ntac 8 (Cases_on ‘n’ >- EVAL_TAC \\ Cases_on ‘n'’ >- EVAL_TAC)
  \\ simp [ADD1] \\ EVAL_TAC \\ simp []
QED

Theorem num2Zreg_w2n[cv_inline]:
  num2Zreg (w2n r) = total_num2Zreg (w2n (r:word4))
Proof
  Cases_on ‘r’ \\ gvs [] \\ EVAL_TAC \\ gvs []
QED

Theorem num2Zreg_w2n_w3[cv_inline]:
  num2Zreg (w2n r) = total_num2Zreg (w2n (r:word3))
Proof
  Cases_on ‘r’ \\ gvs [] \\ EVAL_TAC \\ gvs []
QED

val _ = cv_trans total_num2Zreg;
val _ = cv_trans x64_targetTheory.x64_sh_def;
val _ = cv_trans x64_targetTheory.x64_cmp_def;
val _ = cv_trans x64_targetTheory.x64_bop_def;
val _ = cv_trans x64_targetTheory.x64_ast_def;

val _ = cv_trans x64Theory.e_imm8_def;
val _ = cv_trans x64Theory.e_imm16_def;
val _ = cv_trans x64Theory.e_imm32_def;
val _ = cv_trans x64Theory.e_imm64_def;
val _ = cv_trans x64Theory.e_imm_8_32_def;
val _ = cv_trans x64Theory.Zreg2num_thm;

Theorem fix_num_case[local]:
  (case (n:num) of 0 => x | 1 => y | v => z) =
  if n = 0 then x else if n = 1 then y else z
Proof
  rw [] \\ gvs []
QED

val _ = cv_trans (x64Theory.e_ModRM_def |> REWRITE_RULE [fix_num_case]);
val _ = cv_trans x64Theory.rex_prefix_def;
val _ = cv_trans x64Theory.e_opsize_def;
val _ = cv_trans x64Theory.e_opsize_imm_def;
val _ = cv_trans x64Theory.e_rax_imm_def;
val _ = cv_trans x64Theory.e_rm_imm_def;
val _ = cv_trans x64Theory.e_rm_imm8_def;
val _ = cv_trans x64Theory.e_rm_imm8b_def;
val _ = cv_trans x64Theory.e_gen_rm_reg_def;
val _ = cv_trans x64Theory.e_opc_def;
val _ = cv_trans x64Theory.xmm_mem_to_rm_def;
val _ = cv_trans sse_compare2num_thm;
val _ = cv_trans sse_logic2num_thm;
val _ = cv_trans Zbinop_name2num_thm;
val _ = cv_trans Zbit_test_name2num_thm;
val _ = cv_trans Zcond2num_thm;
val _ = cv_trans Zsize_width_def;
val _ = cv_trans is_rax_def;
val _ = cv_trans not_byte_def;
val _ = cv_trans x64Theory.encode_sse_binop_def;
val _ = cv_trans x64Theory.encode_sse_def;

Definition znop_def:
  znop (n:num) =
    if n = 1 then [144w] else
    if n = 2 then [102w; 144w] else
    if n = 3 then [15w; 31w; 0w] else
    if n = 4 then [15w; 31w; 64w; 0w] else
    if n = 5 then [15w; 31w; 68w; 0w; 0w] else
    if n = 6 then [102w; 15w; 31w; 68w; 0w; 0w] else
    if n = 7 then [15w; 31w; 128w; 0w; 0w; 0w; 0w] else
    if n = 8 then [15w; 31w; 132w; 0w; 0w; 0w; 0w; 0w] else
    if n = 9 then [102w; 15w; 31w; 132w; 0w; 0w; 0w; 0w; 0w] else [] : word8 list
End

val _ = cv_trans znop_def;

Theorem to_znop[local]:
 (case n of
  | 1 => [144w]
  | 2 => [102w; 144w]
  | 3 => [15w; 31w; 0w]
  | 4 => [15w; 31w; 64w; 0w]
  | 5 => [15w; 31w; 68w; 0w; 0w]
  | 6 => [102w; 15w; 31w; 68w; 0w; 0w]
  | 7 => [15w; 31w; 128w; 0w; 0w; 0w; 0w]
  | 8 => [15w; 31w; 132w; 0w; 0w; 0w; 0w; 0w]
  | 9 => [102w; 15w; 31w; 132w; 0w; 0w; 0w; 0w; 0w]
  | _ => []) = znop n
Proof
  Cases_on ‘n’ \\ EVAL_TAC
QED

val _ = cv_trans (x64Theory.encode_def |> SRULE [to_znop, GSYM GREATER_DEF]);
val _ = cv_trans x64_targetTheory.x64_encode_def;

val _ = cv_auto_trans (x64_targetTheory.x64_enc_def |>
          SRULE [combinTheory.o_DEF, LIST_BIND_def, FUN_EQ_THM, x64_dec_fail_def]);

(*---------------------------------------------------------------------------*
  Remaining x64-specific functions
 *---------------------------------------------------------------------------*)

val pre = cv_auto_trans_pre "" comp_x64_def;

Theorem comp_x64_pre[cv_pre,local]:
  ∀v bs kf. comp_x64_pre v bs kf
Proof
  gen_tac \\ completeInduct_on ‘prog_size (K 0) v’
  \\ rw [] \\ gvs [PULL_FORALL]
  \\ rw [] \\ simp [Once pre]
  \\ rw [] \\ gvs []
  \\ last_x_assum irule
  \\ gvs [wordLangTheory.prog_size_def]
QED

val _ = cv_auto_trans compile_prog_x64_def;

val pre = cv_auto_trans_pre "" compile_word_to_stack_x64_def;

Theorem compile_word_to_stack_x64_pre[cv_pre]:
  ∀k v bitmaps. compile_word_to_stack_x64_pre k v bitmaps
Proof
  Induct_on`v`
  \\ rw [] \\ simp [Once pre]
QED

Theorem fp_reg_ok_x64_def[local,cv_inline] = fp_reg_ok_x64_def;

val _ = cv_auto_trans inst_ok_x64_def;
val _ = cv_auto_trans asm_ok_x64_def;
val _ = cv_auto_trans line_ok_light_x64_def;
val _ = cv_auto_trans sec_ok_light_x64_def;

val pre = cv_trans_pre "" enc_lines_again_x64_def;

Theorem enc_lines_again_x64_pre[cv_pre,local]:
  ∀labs ffis pos v0 v. enc_lines_again_x64_pre labs ffis pos v0 v
Proof
  Induct_on ‘v0’ \\ simp [Once pre]
QED

val pre = cv_trans_pre "" enc_secs_again_x64_def;

Theorem enc_secs_again_x64_pre[cv_pre,local]:
  ∀pos labs ffis v. enc_secs_again_x64_pre pos labs ffis v
Proof
  Induct_on ‘v’ \\ simp [Once pre]
QED

val pre = cv_auto_trans_pre "" remove_labels_loop_x64_def;

Theorem remove_labels_loop_x64_pre[cv_pre]:
  ∀clock pos init_labs ffis sec_list.
    remove_labels_loop_x64_pre clock pos init_labs ffis sec_list
Proof
  Induct_on ‘clock’ \\ simp [Once pre]
QED

val _ = cv_trans enc_line_x64_def;
val _ = cv_auto_trans enc_sec_x64_def;
val _ = cv_auto_trans enc_sec_list_x64_def;
val _ = cv_trans remove_labels_x64_def;
val _ = cv_auto_trans compile_lab_x64_def;
val _ = cv_trans lab_to_target_x64_def;
val _ = cv_trans from_lab_x64_def;

val _ = cv_trans (from_stack_x64_def
  |> SRULE [data_to_wordTheory.max_heap_limit_def,backend_commonTheory.word_shift_def]);

val _ = cv_auto_trans from_word_x64_def;

val pre = cv_trans_pre "" get_forced_x64_def;
Theorem get_forced_x64_pre[cv_pre,local]:
  ∀v acc. get_forced_x64_pre v acc
Proof
  gen_tac \\ completeInduct_on ‘prog_size (K 0) v’
  \\ rw [] \\ gvs [PULL_FORALL]
  \\ simp [Once pre] \\ rw []
  \\ gvs [] \\ last_x_assum $ irule
  \\ gvs [wordLangTheory.prog_size_def]
QED

val _ = cv_trans word_alloc_inlogic_x64_def;

val pre = cv_trans_pre "" inst_select_exp_x64_def;
Theorem inst_select_exp_x64_pre[cv_pre]:
  ∀v tar temp. inst_select_exp_x64_pre tar temp v
Proof
  gen_tac \\ completeInduct_on ‘exp_size (K 0) v’
  \\ rw [] \\ gvs [PULL_FORALL]
  \\ rw [] \\ simp [Once pre]
  \\ rw [] \\ gvs []
  \\ last_x_assum irule
  \\ gvs [wordLangTheory.exp_size_def]
QED

val pre = cv_trans_pre "" inst_select_x64_def;
Theorem inst_select_x64_pre[cv_pre,local]:
  ∀v temp. inst_select_x64_pre temp v
Proof
  gen_tac \\ completeInduct_on ‘prog_size (K 0) v’
  \\ rw [] \\ gvs [PULL_FORALL]
  \\ simp [Once pre] \\ rw []
  \\ first_x_assum irule \\ gvs [wordLangTheory.prog_size_def]
QED

val pre = each_inlogic_x64_def |> cv_trans_pre "";
Theorem each_inlogic_x64_pre[cv_pre,local]:
  ∀v. each_inlogic_x64_pre v
Proof
  Induct \\ rw [] \\ simp [Once pre]
QED

val _ = cv_trans word_to_word_inlogic_x64_def;
val _ = cv_trans from_word_0_x64_def;

val _ = cv_trans (compile_0_x64_def
                    |> SRULE [data_to_wordTheory.stubs_def,
                              backend_64_cvTheory.inline,
                              to_map_compile_part]);

val _ = cv_trans backend_x64Theory.to_word_0_x64_def;
val _ = cv_auto_trans backend_x64Theory.to_livesets_0_x64_def;

val _ = cv_auto_trans (backend_x64Theory.to_word_all_x64_def
                         |> SRULE [data_to_wordTheory.stubs_def,to_map_compile_part,
                                   backend_64_cvTheory.inline]);
val _ = cv_trans backend_x64Theory.to_stack_all_x64_def;
val _ = cv_trans (backend_x64Theory.to_lab_all_x64_def
                    |> SRULE [data_to_wordTheory.max_heap_limit_def,
                              backend_64_cvTheory.inline]);

(* export *)

Definition export_funcs_alt_def:
  export_funcs_alt [] e = e ∧
  export_funcs_alt (x::xs) e = export_funcs_alt xs (export_func e x)
End

Theorem export_funcs_alt_thm:
  ∀xs e. export_funcs_alt xs e = FOLDL export_func e xs
Proof
  Induct >> rw[export_funcs_alt_def]
QED

val _ = cv_auto_trans export_funcs_alt_def;

val _ = cv_auto_trans
        (export_x64Theory.export_funcs_def
           |> SRULE [combinTheory.o_DEF, combinTheory.C_DEF,GSYM export_funcs_alt_thm,
                     MEM_EXISTS]);

val _ = cv_auto_trans
        (export_x64Theory.x64_export_def
           |> REWRITE_RULE [to_words_line_word,
                            to_words_line_byte,
                            split16_eq_chunks16]);

(* main translations below *)

val _ = cv_trans backend_x64Theory.to_livesets_x64_def;
val _ = cv_trans backend_x64Theory.compile_cake_x64_def;
val _ = cv_auto_trans backend_x64Theory.compile_cake_explore_x64_def;

(* lemma used by automation *)

Theorem set_asm_conf_x64_backend_config:
  set_asm_conf x64_backend_config x64_config = x64_backend_config
Proof
  irule backendTheory.set_asm_conf_id \\ EVAL_TAC
QED

