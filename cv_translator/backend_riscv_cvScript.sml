(*
  Translate RISC-V-specialised functions to cv equations.
*)
Theory backend_riscv_cv[no_sig_docs]
Ancestors
  cv_std backend_cv backend_word_cv backend_riscv riscv riscv_target
  to_data_cv export_riscv riscv_config
Libs
  preamble cv_transLib

Theorem IN_INSERT[cv_inline,local] = IN_INSERT;
Theorem NOT_IN_EMPTY[cv_inline,local] = NOT_IN_EMPTY;

Theorem v2w_sing[cv_inline,local] = miscTheory.v2w_sing;

val _ = cv_trans riscvTheory.opc_def;
val _ = cv_trans riscvTheory.amofunc_def;
val _ = cv_trans riscvTheory.Rtype_def;
val _ = cv_trans riscvTheory.R4type_def;
val _ = cv_trans riscvTheory.Itype_def;
val _ = cv_trans riscvTheory.Stype_def;
val _ = cv_trans riscvTheory.SBtype_def;
val _ = cv_trans riscvTheory.Utype_def;
val _ = cv_trans riscvTheory.UJtype_def;
val _ = cv_trans riscvTheory.Encode_def;

val _ = cv_auto_trans (riscv_const32_def |> SRULE [word_bit]);
val _ = cv_trans (riscv_bop_r_def |> SRULE [FUN_EQ_THM]);
val shv_pre = cv_trans_pre "" (riscv_shv_def |> SRULE [FUN_EQ_THM]);
val bop_i_pre = cv_trans_pre "" (riscv_bop_i_def |> SRULE [FUN_EQ_THM]);
val sh_pre = cv_trans_pre "" (riscv_sh_def |> SRULE [FUN_EQ_THM]);
val ast_pre = cv_auto_trans_pre ""
  (riscv_ast_def |> CONJUNCTS |> map GEN_ALL |> LIST_CONJ |> SIMP_RULE
    (srw_ss() ++ DatatypeSimps.expand_type_quants_ss [``:memop``])
    [word_bit,riscv_memop_def,LET_THM,FORALL_AND_THM]);

Theorem riscv_ast_pre[cv_pre]:
  !v. riscv_ast_pre v
Proof
  simp [ast_pre,bop_i_pre,sh_pre,shv_pre]
  \\ Cases \\ simp []
QED

val _ = cv_auto_trans (riscv_targetTheory.riscv_enc_def
  |> SRULE [combinTheory.o_DEF,LIST_BIND_def,FUN_EQ_THM]);

fun word_tyvars ty =
  case total dest_thy_type ty of
    NONE => []
  | SOME {Thy="fcp",Tyop="cart",Args=[_,v]} =>
      if is_vartype v then [v] else word_tyvars v
  | SOME {Args,...} => List.concat (map word_tyvars Args);

fun arch_spec th =
  find_terms (K true) (concl th)
  |> List.concat o map (word_tyvars o type_of) |> mk_set
  |> map (fn v => v |-> ``:64``)
  |> (fn s => INST_TYPE s th);

val pre = cv_auto_trans_pre "" (comp_riscv_def |> arch_spec);

Theorem comp_riscv_pre[cv_pre,local]:
  ∀perf v bs kf. comp_riscv_pre perf v bs kf
Proof
  gen_tac \\ gen_tac \\ completeInduct_on `prog_size v`
  \\ rw [] \\ gvs [PULL_FORALL]
  \\ rw [] \\ simp [Once pre]
  \\ rw [] \\ gvs []
  \\ last_x_assum irule
  \\ gvs []
QED

val _ = cv_auto_trans (compile_prog_riscv_def |> arch_spec);

val pre = cv_auto_trans_pre "" (compile_word_to_stack_riscv_def |> arch_spec);

Theorem compile_word_to_stack_riscv_pre[cv_pre]:
  ∀perf k v bitmaps. compile_word_to_stack_riscv_pre perf k v bitmaps
Proof
  Induct_on`v`
  \\ rw [] \\ simp [Once pre]
QED

Theorem fp_reg_ok_riscv_def[local,cv_inline] = (fp_reg_ok_riscv_def |> arch_spec);

val _ = cv_auto_trans (inst_ok_riscv_def |> arch_spec);
val _ = cv_auto_trans (asm_ok_riscv_def |> arch_spec);
val _ = cv_auto_trans (line_ok_light_riscv_def |> arch_spec);
val _ = cv_auto_trans (sec_ok_light_riscv_def |> arch_spec);

val pre = cv_trans_pre "" (enc_lines_again_riscv_def |> arch_spec);

Theorem enc_lines_again_riscv_pre[cv_pre,local]:
  ∀labs ffis pos v0 v. enc_lines_again_riscv_pre labs ffis pos v0 v
Proof
  Induct_on `v0` \\ simp [Once pre]
QED

val pre = cv_trans_pre "" (enc_secs_again_riscv_def |> arch_spec);

Theorem enc_secs_again_riscv_pre[cv_pre,local]:
  ∀pos labs ffis v. enc_secs_again_riscv_pre pos labs ffis v
Proof
  Induct_on `v` \\ simp [Once pre]
QED

val pre = cv_auto_trans_pre "" (remove_labels_loop_riscv_def |> arch_spec);

Theorem remove_labels_loop_riscv_pre[cv_pre]:
  ∀clock pos init_labs ffis sec_list.
    remove_labels_loop_riscv_pre clock pos init_labs ffis sec_list
Proof
  Induct_on `clock` \\ simp [Once pre]
QED

val _ = cv_trans (enc_line_riscv_def |> arch_spec);
val _ = cv_auto_trans (enc_sec_riscv_def |> arch_spec);
val _ = cv_auto_trans (enc_sec_list_riscv_def |> arch_spec);
val _ = cv_trans (remove_labels_riscv_def |> arch_spec);
val _ = cv_auto_trans (compile_lab_riscv_def |> arch_spec);
val _ = cv_trans (lab_to_target_riscv_def |> arch_spec);
val _ = cv_trans from_lab_riscv_def;

val _ = cv_trans ((from_stack_riscv_def |> arch_spec)
  |> SRULE [data_to_wordTheory.max_heap_limit_def,backend_commonTheory.word_shift_def]);

val _ = cv_auto_trans (from_word_riscv_def |> arch_spec);

val pre = cv_trans_pre "" (get_forced_riscv_def |> arch_spec);
Theorem get_forced_riscv_pre[cv_pre,local]:
  ∀v acc. get_forced_riscv_pre v acc
Proof
  gen_tac \\ completeInduct_on `prog_size v`
  \\ rw [] \\ gvs [PULL_FORALL]
  \\ simp [Once pre] \\ rw []
  \\ gvs [] \\ last_x_assum $ irule
  \\ gvs []
QED

val _ = cv_trans (word_alloc_inlogic_riscv_def |> arch_spec);

val pre = cv_trans_pre "" (inst_select_exp_riscv_def |> arch_spec);
Theorem inst_select_exp_riscv_pre[cv_pre]:
  ∀bits v tar temp. inst_select_exp_riscv_pre bits tar temp v
Proof
  gen_tac \\ gen_tac \\ completeInduct_on `exp_size v`
  \\ rw [] \\ gvs [PULL_FORALL]
  \\ rw [] \\ simp [Once pre]
  \\ rw [] \\ gvs []
  \\ last_x_assum irule
  \\ gvs []
QED

val pre = cv_trans_pre "" (inst_select_riscv_def |> arch_spec);
Theorem inst_select_riscv_pre[cv_pre,local]:
  ∀bits v temp. inst_select_riscv_pre bits temp v
Proof
  gen_tac \\ gen_tac \\ completeInduct_on `prog_size v`
  \\ rw [] \\ gvs [PULL_FORALL]
  \\ simp [Once pre] \\ rw []
  \\ first_x_assum irule \\ gvs []
QED

val pre = (each_inlogic_riscv_def |> arch_spec) |> cv_trans_pre "";
Theorem each_inlogic_riscv_pre[cv_pre,local]:
  ∀v. each_inlogic_riscv_pre v
Proof
  Induct \\ rw [] \\ simp [Once pre]
QED

val _ = cv_trans (word_to_word_inlogic_riscv_def |> arch_spec);
val _ = cv_trans (from_word_0_riscv_def |> arch_spec);

Theorem stubs_md_def[cv_inline,local] =
  data_to_wordTheory.stubs_md_def |> arch_spec;

val _ = cv_auto_trans ((compile_0_riscv_def |> arch_spec)
                    |> SRULE [stubs_md_def,data_to_wordTheory.stubs_def,
                              backend_word_cvTheory.inline,
                              to_map_compile_part]);

val _ = cv_trans (backend_riscvTheory.to_word_0_riscv_def |> arch_spec);
val _ = cv_auto_trans (backend_riscvTheory.to_livesets_0_riscv_def
                        |> arch_spec |> INST_TYPE [beta |-> ``:metadata``]);

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
        (export_riscvTheory.export_funcs_def
           |> SRULE [combinTheory.o_DEF, combinTheory.C_DEF,GSYM export_funcs_alt_thm,
                     MEM_EXISTS]);

val _ = cv_auto_trans
        (export_riscvTheory.riscv_export_def
           |> REWRITE_RULE [to_words_line_word,
                            to_words_line_byte,
                            split16_eq_chunks16]);

val _ = cv_trans (backend_riscvTheory.to_livesets_riscv_def |> arch_spec);
val _ = cv_trans (backend_riscvTheory.compile_cake_riscv_def |> arch_spec);
val _ = cv_auto_trans (backend_riscvTheory.compile_cake_explore_riscv_def |> arch_spec);
