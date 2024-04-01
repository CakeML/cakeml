(*
  Translate cv version of arm8 specialised backend functions.
*)
open preamble cv_transLib cv_stdTheory;
open backend_arm8Theory arm8Theory arm8_targetTheory;

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
  (WF_REL_TAC `measure cv_sum_depth` >> cv_termination_tac >>
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
  Translation of instruction encoder
 *---------------------------------------------------------------------------*)

(* generic *)

val _ = cv_trans sptreeTheory.fromAList_def;

val _ = cv_trans lab_to_targetTheory.lab_inst_def;
val _ = cv_auto_trans lab_to_targetTheory.get_ffi_index_def;
val _ = cv_auto_trans lab_to_targetTheory.find_pos_def;
val _ = cv_auto_trans lab_to_targetTheory.get_label_def;
val _ = cv_trans lab_to_targetTheory.pad_bytes_def;
val _ = cv_auto_trans lab_filterTheory.filter_skip_def;
val _ = cv_auto_trans lab_to_targetTheory.prog_to_bytes_def;
val _ = cv_auto_trans lab_to_targetTheory.zero_labs_acc_exist_def;
val _ = cv_auto_trans lab_to_targetTheory.find_ffi_names_def;
val _ = TypeBase.accessors_of “:lab_to_target$inc_config” |> map cv_trans;
val _ = TypeBase.accessors_of “:environment” |> map cv_trans;

val _ = cv_trans num_list_enc_decTheory.append_rev_def;

Triviality make_cv_term_provable:
  (if n < 30 then x else y) = (if n = 0n then x else if 30 ≤ n then y else x)
Proof
  rw [] \\ gvs []
QED

val pre = cv_trans_pre $
  SRULE [make_cv_term_provable] num_list_enc_decTheory.num_to_chars_def;

Theorem num_to_chars_pre[cv_pre,local]:
  ∀n. num_to_chars_pre n
Proof
  completeInduct_on ‘n’ \\ simp [Once pre] \\ rw []
  \\ ‘n MOD 30 < 30’ by gs [] \\ decide_tac
QED

val _ = cv_trans num_list_enc_decTheory.rev_nums_to_chars_def;

Triviality spt_enc_def[cv_inline] = num_list_enc_decTheory.spt_enc_def;

val _ = cv_auto_trans backend_enc_decTheory.data_to_word_config_enc_def;
val _ = cv_auto_trans backend_enc_decTheory.word_to_word_config_enc_def;
val _ = cv_auto_trans backend_enc_decTheory.word_to_stack_config_enc_def;
val _ = cv_auto_trans backend_enc_decTheory.stack_to_lab_config_enc_def;
val _ = cv_auto_trans backend_enc_decTheory.lab_to_target_inc_config_enc_def;
val _ = cv_auto_trans backend_enc_decTheory.tap_config_enc_def;

(* environment encoding *)

val tms = backend_enc_decTheory.environment_enc_def
            |> concl |> find_terms (can (match_term “namespace_enc _”)) |> map rand;
val tm1 = el 1 tms;
val tm2 = el 2 tms;

fun spec_namespace_enc' tm1 suffix = let
  val name = "namespace_enc'" ^ suffix
  val name_list = "namespace_enc'" ^ suffix ^ "_list"
  val r = “namespace_enc' ^tm1”
  val r_list = “namespace_enc'_list ^tm1”
  val v = mk_var(name,type_of r)
  val v_list = mk_var(name_list,type_of r_list)
  val tm = num_list_enc_decTheory.namespace_enc'_def
    |> CONJUNCTS |> map (ISPEC tm1 o Q.GEN ‘e’ o SPEC_ALL) |> LIST_CONJ |> SRULE [LET_THM]
    |> concl |> subst [r |-> v, r_list |-> v_list]
  val tac =  WF_REL_TAC ‘measure (λx. case x of
                         | INL x => namespace_size (K 0) (K 0) (K 0) x
                         | INR x => namespace1_size (K 0) (K 0) (K 0) x)’
  val def = tDefine name [ANTIQUOTE tm] tac
  val _ = cv_auto_trans def
  val cs = def |> CONJUNCTS |> map (fst o strip_comb o lhs o concl o SPEC_ALL)
  val c = hd cs
  val c_list = last cs
  val goal = mk_conj(mk_eq(r,c),mk_eq(r_list,c_list))
  val res = prove(goal,
                  simp [FUN_EQ_THM]
                  \\ ho_match_mp_tac (fetch "-" (name ^ "_ind"))
                  \\ simp [def,num_list_enc_decTheory.namespace_enc'_def])
  in res end

val res1 = spec_namespace_enc' tm1 "_1";
val res2 = spec_namespace_enc' tm2 "_2";

val _ = cv_trans num_list_enc_decTheory.namespace_depth_def;

val _ = cv_trans (backend_enc_decTheory.environment_enc_def
                    |> SRULE [res1,res2,num_list_enc_decTheory.namespace_enc_def,
                              num_list_enc_decTheory.prod_enc_def]);

val _ = cv_auto_trans backend_enc_decTheory.source_to_flat_config_enc_def;

(* closLang const encoding *)

val const_exp = backend_enc_decTheory.const_enc'_def
                |> SRULE [SF ETA_ss, num_tree_enc_decTheory.list_enc'_def];
val const_exps = MAP |> CONJUNCTS |> map (Q.ISPEC ‘const_enc'’);

val name = "const_enc_aux"
val c = “const_enc'”
val r = mk_var(name,type_of c)
val c_list = “MAP const_enc'”
val r_list = mk_var(name ^ "_list",type_of c_list)

Definition const_enc_aux_def:
  ^(LIST_CONJ (CONJUNCTS const_exp @ const_exps |> map SPEC_ALL)
           |> concl |> subst [c|->r,c_list|->r_list])
End

val _ = cv_auto_trans const_enc_aux_def;

Theorem const_enc_aux_thm[cv_inline,local]:
  const_enc' = const_enc_aux ∧
  MAP const_enc' = const_enc_aux_list
Proof
  gvs [FUN_EQ_THM] \\ Induct
  \\ gvs [const_enc_aux_def,backend_enc_decTheory.const_enc'_def,
          num_tree_enc_decTheory.list_enc'_def,SF ETA_ss]
QED

(* bvl_exp encoding *)

val bvl_exp = backend_enc_decTheory.bvl_exp_enc'_def
                |> SRULE [SF ETA_ss, num_tree_enc_decTheory.list_enc'_def];
val bvl_exps = MAP |> CONJUNCTS |> map (Q.ISPEC ‘bvl_exp_enc'’);

val name = "bvl_exp_enc_aux"
val c = “bvl_exp_enc'”
val r = mk_var(name,type_of c)
val c_list = “MAP bvl_exp_enc'”
val r_list = mk_var(name ^ "_list",type_of c_list)

Definition bvl_exp_enc_aux_def:
  ^(LIST_CONJ (CONJUNCTS bvl_exp @ bvl_exps |> map SPEC_ALL)
           |> concl |> subst [c|->r,c_list|->r_list])
End

val _ = cv_auto_trans bvl_exp_enc_aux_def;

Theorem bvl_exp_enc_aux_thm[cv_inline,local]:
  bvl_exp_enc' = bvl_exp_enc_aux ∧
  MAP bvl_exp_enc' = bvl_exp_enc_aux_list
Proof
  gvs [FUN_EQ_THM] \\ Induct
  \\ gvs [bvl_exp_enc_aux_def,backend_enc_decTheory.bvl_exp_enc'_def,
          num_tree_enc_decTheory.list_enc'_def,SF ETA_ss]
QED

val _ = cv_auto_trans backend_enc_decTheory.bvl_to_bvi_config_enc_def;

(* closLang_exp encoding *)

val closLang_exp = backend_enc_decTheory.closLang_exp_enc'_def
                |> SRULE [SF ETA_ss, num_tree_enc_decTheory.list_enc'_def];
val closLang_exps = MAP |> CONJUNCTS |> map (Q.ISPEC ‘closLang_exp_enc'’);
val closLang_exps1 = MAP |> CONJUNCTS |> map (Q.ISPEC ‘pair_enc' num_enc' closLang_exp_enc'’);

val name = "closLang_exp_enc_aux"
val c = “closLang_exp_enc'”
val r = mk_var(name,type_of c)
val c_list = “MAP closLang_exp_enc'”
val r_list = mk_var(name ^ "_list",type_of c_list)
val c_list1 = “MAP $ pair_enc' num_enc' closLang_exp_enc'”
val r_list1 = mk_var(name ^ "_list1",type_of c_list1)

Definition closLang_exp_enc_aux_def:
  ^(CONJUNCTS closLang_exp @ closLang_exps @ closLang_exps1
    |> map (SPEC_ALL o SIMP_RULE bool_ss [FORALL_PROD,
              num_tree_enc_decTheory.pair_enc'_def]) |> LIST_CONJ
    |> concl |> subst [c|->r,c_list|->r_list,c_list1|->r_list1])
Termination
  WF_REL_TAC ‘measure $ λx. case x of
              | INL x => closLang$exp_size x
              | INR (INL xs) => list_size closLang$exp_size xs
              | INR (INR ys) => list_size (pair_size (λx.x) closLang$exp_size) ys’
  \\ gvs [closLangTheory.exp_size_eq]
End

val pre = cv_auto_trans_pre closLang_exp_enc_aux_def;

Theorem closLang_exp_enc_aux_pre[cv_pre,local]:
  (∀v. closLang_exp_enc_aux_pre v) ∧
  (∀v. closLang_exp_enc_aux_list_pre v) ∧
  (∀v. closLang_exp_enc_aux_list1_pre v)
Proof
  ho_match_mp_tac closLang_exp_enc_aux_ind \\ rw [] \\ simp [Once pre]
QED

Theorem closLang_exp_enc_aux_thm[cv_inline,local]:
  closLang_exp_enc' = closLang_exp_enc_aux ∧
  MAP closLang_exp_enc' = closLang_exp_enc_aux_list ∧
  MAP (pair_enc' num_enc' closLang_exp_enc') = closLang_exp_enc_aux_list1
Proof
  gvs [FUN_EQ_THM] \\ ho_match_mp_tac closLang_exp_enc_aux_ind
  \\ gvs [closLang_exp_enc_aux_def,SF ETA_ss,
          backend_enc_decTheory.closLang_exp_enc'_def,
          num_tree_enc_decTheory.pair_enc'_def,
          num_tree_enc_decTheory.list_enc'_def]
QED

(* closLang val_approx encoding *)

val val_approx_exp = backend_enc_decTheory.val_approx_enc'_def
                |> SRULE [SF ETA_ss, num_tree_enc_decTheory.list_enc'_def];
val val_approx_exps = MAP |> CONJUNCTS |> map (Q.ISPEC ‘val_approx_enc'’);

val name = "val_approx_enc_aux"
val c = “val_approx_enc'”
val r = mk_var(name,type_of c)
val c_list = “MAP val_approx_enc'”
val r_list = mk_var(name ^ "_list",type_of c_list)

Definition val_approx_enc_aux_def:
  ^(LIST_CONJ (CONJUNCTS val_approx_exp @ val_approx_exps |> map SPEC_ALL)
           |> concl |> subst [c|->r,c_list|->r_list])
End

val _ = cv_auto_trans val_approx_enc_aux_def;

Theorem val_approx_enc_aux_thm[cv_inline,local]:
  val_approx_enc' = val_approx_enc_aux ∧
  MAP val_approx_enc' = val_approx_enc_aux_list
Proof
  gvs [FUN_EQ_THM] \\ Induct
  \\ gvs [val_approx_enc_aux_def,backend_enc_decTheory.val_approx_enc'_def,
          num_tree_enc_decTheory.list_enc'_def,SF ETA_ss]
QED

val _ = cv_auto_trans backend_enc_decTheory.clos_to_bvl_config_enc_def;

val _ = cv_auto_trans backend_enc_decTheory.inc_config_enc_def;
val _ = cv_trans backend_enc_decTheory.encode_backend_config_def;
val _ = cv_auto_trans backend_asmTheory.attach_bitmaps_def;

(* 64-bit *)

val arch_spec = INST_TYPE [alpha |-> “:64”];

val _ = cv_trans (alignmentTheory.aligned_w2n |> arch_spec);;
val _ = cv_trans (asmTheory.offset_ok_def |> arch_spec);
val _ = cv_trans (lab_to_targetTheory.section_labels_def |> arch_spec);
val _ = cv_trans (lab_to_targetTheory.compute_labels_alt_def |> arch_spec);
val _ = cv_trans (lab_to_targetTheory.lines_upd_lab_len_def |> arch_spec);

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

(* arm8 specific *)

Triviality fp_reg_ok_arm8_def[cv_inline] = fp_reg_ok_arm8_def;

val _ = cv_auto_trans inst_ok_arm8_def;
val _ = cv_auto_trans asm_ok_arm8_def;
val _ = cv_auto_trans line_ok_light_arm8_def;
val _ = cv_auto_trans sec_ok_light_arm8_def;
val _ = cv_auto_trans (lab_to_targetTheory.get_jump_offset_def |> arch_spec);

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

(* ----------------------------------------------------------------------------------- *)

(*
stack_to_labTheory.compile_def

from_stack_arm8_def
from_word_arm8_def
from_word_0_arm8_def
get_forced_arm8_def
word_alloc_inlogic_arm8_def
each_inlogic_arm8_def
word_to_word_inlogic_arm8_def
to_word_0_arm8_def
compile_0_arm8_def |> SRULE [data_to_wordTheory.stubs_def]
compile_cake_arm8_def
*)

val _ = export_theory();
