(*
  Translate arm8-specialised functions to cv equations.
*)
open preamble cv_transLib cv_stdTheory backend_cvTheory backend_64_cvTheory;
open backend_arm8Theory arm8Theory arm8_targetTheory to_data_cvTheory;
open export_arm8Theory arm8_configTheory;

val _ = new_theory "backend_arm8_cv";

(*---------------------------------------------------------------------------*
  Translation of instruction encoder
 *---------------------------------------------------------------------------*)

Theorem IN_INSERT[cv_inline,local] = IN_INSERT;
Theorem NOT_IN_EMPTY[cv_inline,local] = NOT_IN_EMPTY;

Theorem word_len[cv_inline,local] = word_len_def;
Theorem v2w_sing[cv_inline,local] = miscTheory.v2w_sing;

val _ = cv_trans e_LoadStoreImmediate_def;
val _ = cv_trans ExtendType2num_thm;
val _ = cv_trans e_LoadStoreRegister_def;
val res = cv_trans_pre $ SRULE [word_len_def] e_load_store_def;

Theorem e_load_store_pre[cv_pre]:
  ∀i. e_load_store_pre i
Proof
  simp[res] >> simp[IS_SOME_EXISTS, PULL_EXISTS]
QED

val _ = cv_trans e_branch_def;
val _ = cv_trans e_crc_def;
val _ = cv_trans e_debug_def;
val _ = cv_trans e_system_def;

Theorem e_sf_word32_F[cv_inline,local] =
  e_sf_def |> INST_TYPE [``:'N`` |-> ``:32``] |>
  SRULE [word_len_def, v2w_sing]

Theorem e_sf_word64_T[cv_inline,local] =
  e_sf_def |> INST_TYPE [``:'N`` |-> ``:64``] |>
  SRULE [word_len_def, v2w_sing]

val _ = cv_trans ShiftType2num_thm;
val highest_set_bit_pre =
  cv_trans_pre (HighestSetBit_def |> INST_TYPE [``:'N`` |-> ``:7``]);

Theorem HighestSetBit_pre[cv_pre,local]:
  ∀w. HighestSetBit_pre w
Proof
  simp[highest_set_bit_pre]
QED

Theorem cv_inline_v2w_Ones[cv_inline,local] = v2w_Ones;

val _ = cv_trans (bitstringTheory.replicate_def |> SRULE [GSYM REPLICATE_GENLIST]);
val _ = cv_trans (Ones_def |> SRULE [PAD_LEFT, GSYM REPLICATE_GENLIST]);
val _ = cv_trans cv_primTheory.v2n_custom_def;
val _ = cv_trans (INST_TYPE [``:'N`` |-> ``:32``] Replicate_def);
val _ = cv_trans (INST_TYPE [``:'N`` |-> ``:64``] Replicate_def);
val _ = cv_auto_trans (INST_TYPE [``:'M`` |-> ``:32``] DecodeBitMasks_def);
val _ = cv_auto_trans (INST_TYPE [``:'M`` |-> ``:64``] DecodeBitMasks_def);

Definition CountTrailing_T_def:
  CountTrailing_T w =
    if w = 0w then 0n
    else if word_bit 0 w then 0
    else 1 + CountTrailing_T (w >>> 1)
End

Definition CountTrailing_F_def:
  CountTrailing_F w =
    if ¬word_bit 0 w then 0n
    else 1 + CountTrailing_F (w >>> 1)
Termination
  WF_REL_TAC `measure w2n` >> rw[] >>
  Cases_on `w` >> gvs[w2n_lsr] >>
  simp[DIV_LT_X] >> Cases_on `n` >> gvs[]
End

val count_trailing_tac =
  (WF_REL_TAC `measure cv_size` >> cv_termination_tac >>
   gvs[GSYM cv_primTheory.cv_rep_exp] >>
   Cases_on `cv_w` >> gvs[] >>
   rw[DIV_LT_X] >> Cases_on `m` >> gvs[])

val _ = cv_trans_rec (INST_TYPE [alpha |-> ``:32``] CountTrailing_T_def)
                     count_trailing_tac;
val _ = cv_trans_rec (INST_TYPE [alpha |-> ``:64``] CountTrailing_T_def)
                     count_trailing_tac;
val _ = cv_trans_rec (INST_TYPE [alpha |-> ``:32``] CountTrailing_F_def)
                     count_trailing_tac;
val _ = cv_trans_rec (INST_TYPE [alpha |-> ``:64``] CountTrailing_F_def)
                     count_trailing_tac;

Theorem cv_inline_CountTrailing_T[cv_inline,local]:
  ∀w. CountTrailing (T,w) = CountTrailing_T w
Proof
  recInduct CountTrailing_T_ind >> rw[] >>
  once_rewrite_tac[CountTrailing_def, CountTrailing_T_def] >>
  rw[] >> gvs[]
QED

Theorem cv_inline_CountTrailing_F[cv_inline,local]:
  ∀w. CountTrailing (F,w) = if w = -1w then 0 else CountTrailing_F w
Proof
  rw[] >- simp[Once CountTrailing_def] >>
  pop_assum mp_tac >> qid_spec_tac `w` >>
  recInduct CountTrailing_F_ind >> rw[] >>
  once_rewrite_tac[CountTrailing_def, CountTrailing_F_def] >>
  rw[] >> gvs[] >> first_x_assum irule >>
  Cases_on `w` >> gvs[GSYM n2w_DIV] >> simp[word_eq_n2w] >>
  gvs[bitTheory.MOD_2EXP_MAX_def, bitTheory.MOD_2EXP_def, dimword_def] >>
  simp[DIV_MOD_MOD_DIV] >>
  qsuff_tac `n DIV 2 < 2 ** dimindex (:'a) - 1` >> gvs[] >> simp[DIV_LT_X] >>
  pop_assum mp_tac >> rpt $ pop_assum kall_tac >>
  `dimindex (:'a) ≠ 0` by gvs[] >>
  rename1 `x ≠ 0` >> Induct_on `x` >> rw[] >> gvs[EXP] >>
  Cases_on `x` >> gvs[]
QED

val _ = cv_trans EncodeLogicalOp_def;
val _ = cv_trans (INST_TYPE [``:'N`` |-> ``:32``] EncodeBitMaskAux_def);
val _ = cv_trans (INST_TYPE [``:'N`` |-> ``:32``] EncodeBitMask_def);
val _ = cv_trans (INST_TYPE [``:'N`` |-> ``:64``] EncodeBitMaskAux_def);
val _ = cv_trans (INST_TYPE [``:'N`` |-> ``:64``] EncodeBitMask_def);
val _ = cv_trans RevOp2num_thm;
val _ = cv_trans e_data_def;
val _ = cv_trans SystemHintOp2num_thm;
val _ = cv_trans MemBarrierOp2num_thm;
val _ = cv_trans arm8Theory.Encode_def;
val _ = cv_trans arm8_encode_def;

val _ = cv_trans NoOperation_def;
val _ = cv_trans arm8_enc_mov_imm_def;
val _ = cv_trans arm8_encode_fail_def;
val _ = cv_trans arm8_load_store_ast_def;
val _ = cv_trans cmp_cond_def;
val _ = cv_trans asmSemTheory.is_test_def;
val bop_enc_pre = cv_trans_pre bop_enc_def;
val arm8_ast_pre = cv_trans_pre (SRULE [SF LET_ss] arm8_ast_def);

Theorem arm8_ast_pre[cv_pre]:
  ∀v. arm8_ast_pre v
Proof
  simp[arm8_ast_pre, bop_enc_pre]
QED

val _ = cv_auto_trans (arm8_targetTheory.arm8_enc_def |>
                       SRULE [combinTheory.o_DEF, LIST_BIND_def, FUN_EQ_THM]);

(*---------------------------------------------------------------------------*
  Remaining arm8-specific functions
 *---------------------------------------------------------------------------*)

Triviality fp_reg_ok_arm8_def[cv_inline] = fp_reg_ok_arm8_def;

val _ = cv_auto_trans inst_ok_arm8_def;
val _ = cv_auto_trans asm_ok_arm8_def;
val _ = cv_auto_trans line_ok_light_arm8_def;
val _ = cv_auto_trans sec_ok_light_arm8_def;

val pre = cv_trans_pre enc_lines_again_arm8_def;

Theorem enc_lines_again_arm8_pre[cv_pre,local]:
  ∀labs ffis pos v0 v. enc_lines_again_arm8_pre labs ffis pos v0 v
Proof
  Induct_on ‘v0’ \\ simp [Once pre]
QED

val pre = cv_trans_pre enc_secs_again_arm8_def;

Theorem enc_secs_again_arm8_pre[cv_pre,local]:
  ∀pos labs ffis v. enc_secs_again_arm8_pre pos labs ffis v
Proof
  Induct_on ‘v’ \\ simp [Once pre]
QED

val pre = cv_auto_trans_pre remove_labels_loop_arm8_def;

Theorem remove_labels_loop_arm8_pre[cv_pre]:
  ∀clock pos init_labs ffis sec_list.
    remove_labels_loop_arm8_pre clock pos init_labs ffis sec_list
Proof
  Induct_on ‘clock’ \\ simp [Once pre]
QED

val _ = cv_trans enc_line_arm8_def;
val _ = cv_auto_trans enc_sec_arm8_def;
val _ = cv_auto_trans enc_sec_list_arm8_def;
val _ = cv_trans remove_labels_arm8_def;
val _ = cv_auto_trans compile_lab_arm8_def;
val _ = cv_trans lab_to_target_arm8_def;
val _ = cv_trans from_lab_arm8_def;

val _ = cv_trans (from_stack_arm8_def
  |> SRULE [data_to_wordTheory.max_heap_limit_def,backend_commonTheory.word_shift_def]);

val _ = cv_auto_trans from_word_arm8_def;

val pre = cv_trans_pre get_forced_arm8_def;
Theorem get_forced_arm8_pre[cv_pre,local]:
  ∀v acc. get_forced_arm8_pre v acc
Proof
  gen_tac \\ completeInduct_on ‘prog_size (K 0) v’
  \\ rw [] \\ gvs [PULL_FORALL]
  \\ simp [Once pre] \\ rw []
  \\ gvs [] \\ last_x_assum $ irule
  \\ gvs [wordLangTheory.prog_size_def]
QED

val _ = cv_trans word_alloc_inlogic_arm8_def;

val pre = cv_trans_pre inst_select_exp_arm8_def;
Theorem inst_select_exp_arm8_pre[cv_pre]:
  ∀v tar temp. inst_select_exp_arm8_pre tar temp v
Proof
  gen_tac \\ completeInduct_on ‘exp_size (K 0) v’
  \\ rw [] \\ gvs [PULL_FORALL]
  \\ rw [] \\ simp [Once pre]
  \\ rw [] \\ gvs []
  \\ last_x_assum irule
  \\ gvs [wordLangTheory.exp_size_def]
QED

val pre = cv_trans_pre inst_select_arm8_def;
Theorem inst_select_arm8_pre[cv_pre,local]:
  ∀v temp. inst_select_arm8_pre temp v
Proof
  gen_tac \\ completeInduct_on ‘prog_size (K 0) v’
  \\ rw [] \\ gvs [PULL_FORALL]
  \\ simp [Once pre] \\ rw []
  \\ first_x_assum irule \\ gvs [wordLangTheory.prog_size_def]
QED

val pre = each_inlogic_arm8_def |> cv_trans_pre;
Theorem each_inlogic_arm8_pre[cv_pre,local]:
  ∀v. each_inlogic_arm8_pre v
Proof
  Induct \\ rw [] \\ simp [Once pre]
QED

val _ = cv_trans word_to_word_inlogic_arm8_def;
val _ = cv_trans from_word_0_arm8_def;

val _ = cv_trans (compile_0_arm8_def
                    |> SRULE [data_to_wordTheory.stubs_def,
                              backend_64_cvTheory.inline,
                              to_map_compile_part]);

val _ = cv_trans backend_arm8Theory.to_word_0_arm8_def;
val _ = cv_auto_trans backend_arm8Theory.to_livesets_0_arm8_def;

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
        (export_arm8Theory.export_funcs_def
           |> SRULE [combinTheory.o_DEF, combinTheory.C_DEF,GSYM export_funcs_alt_thm,
                     MEM_EXISTS]);

val _ = cv_auto_trans
        (export_arm8Theory.arm8_export_def
           |> REWRITE_RULE [to_words_line_word,
                            to_words_line_byte,
                            split16_eq_chunks16]);

(* main two translations below *)

val _ = cv_trans backend_arm8Theory.to_livesets_arm8_def;
val _ = cv_trans backend_arm8Theory.compile_cake_arm8_def;

(* lemma used by automation *)

Theorem set_asm_conf_arm8_backend_config:
  set_asm_conf arm8_backend_config arm8_config = arm8_backend_config
Proof
  irule backendTheory.set_asm_conf_id \\ EVAL_TAC
QED

val _ = Feedback.set_trace "TheoryPP.include_docs" 0;
val _ = export_theory();
