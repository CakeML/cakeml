(*
  Translate the wordLang backend and shared compiler interface.
*)
Theory from_wordProg[no_sig_docs]
Ancestors
  ml_translator reg_allocProg std_prelude word_to_stack word_simp
  word_alloc word_inst backend[qualified] backend_passes compiler_common export
Libs
  preamble ml_translatorLib

val _ = temp_delsimps ["NORMEQ_CONV", "lift_disj_eq", "lift_imp_disj"]

val _ = translation_extends "reg_allocProg";
val _ = ml_translatorLib.use_sub_check true;

val _ = ml_translatorLib.ml_prog_update (ml_progLib.open_module "from_wordProg");

val RW = REWRITE_RULE

val _ = add_preferred_thy "-";

Theorem NOT_NIL_AND_LEMMA[local]:
  (b <> [] /\ x) = if b = [] then F else x
Proof
  Cases_on `b` THEN FULL_SIMP_TAC std_ss []
QED

val extra_preprocessing = ref [MEMBER_INTRO,MAP];

fun def_of_const tm = let
  val {Thy,Name,...} = dest_thy_const tm
  val def = DB.fetch Thy (Name ^ "_pmatch") handle HOL_ERR _ =>
            DB.fetch Thy (Name ^ "_def") handle HOL_ERR _ =>
            DB.fetch Thy (Name ^ "_DEF") handle HOL_ERR _ =>
            DB.fetch Thy (Name ^ "_thm") handle HOL_ERR _ =>
            DB.fetch Thy Name
  val insts = match_type (type_of (prim_mk_const {Thy = Thy, Name = Name}))
                         (type_of tm)
  in def |> INST_TYPE insts |> REWRITE_RULE (!extra_preprocessing)
         |> CONV_RULE (DEPTH_CONV BETA_CONV)
         |> REWRITE_RULE [NOT_NIL_AND_LEMMA] end;

val _ = find_def_for_const := def_of_const;
val _ = use_long_names := true;

val _ = register_type “:wordLang$prog”;
val EqualityType_prog = EqualityType_rule [] “:wordLang$prog”;

(* ------------------------------------------------------------------------- *)
(* word_to_word                                                              *)
(* ------------------------------------------------------------------------- *)

val res = word_cseTheory.map_insert_def |> DefnBase.one_line_ify NONE |> translate;

val res = translate word_cseTheory.bm_inter_eq_def;
val res = translate word_cseTheory.merge_data_def;

val _ = translate word_cseTheory.intToNum_def;

Theorem word_cse_inttonum_side:
  word_cse_inttonum_side i
Proof
  rw [fetch "-" "word_cse_inttonum_side_def"] \\ intLib.COOPER_TAC
QED
val _ = word_cse_inttonum_side |> update_precondition;

val res = translate (word_cseTheory.word_cseInst_def);
val res = translate_no_ind (word_cseTheory.word_cse_def);

Theorem word_cse_ind[local]:
  word_cse_word_cse_ind
Proof
  rewrite_tac [fetch "-" "word_cse_word_cse_ind_def"]
  \\ rpt gen_tac \\ rpt disch_tac
  \\ ONCE_REWRITE_TAC [SWAP_FORALL_THM]
  \\ ho_match_mp_tac (wordLangTheory.max_var_ind
       |> Q.SPEC `λbits p. P p` |> SRULE [] |> Q.GEN `P`)
  \\ rpt strip_tac
  \\ last_x_assum irule
  \\ fs []
QED
val _ = word_cse_ind |> update_precondition;

val res = translate (word_cseTheory.word_common_subexp_elim_def);

val _ = res |> hyp |> null orelse
        failwith ("Unproved side condition in the translation of " ^
                  "word_cseTheory.word_common_subexp_elim_def.");

val res = translate (word_copyTheory.copy_prop_def);

val res = translate (word_unreachTheory.remove_unreach_def);

val _ = translate (word_simpTheory.const_fp_inst_cs_def)

val _ = translate word_simpTheory.int_op_def;
val _ = translate word_simpTheory.int_unsigned_def;
val _ = translate word_simpTheory.int_signed_def;
val _ = translate word_simpTheory.int_sh_def;
Theorem int_unsigned_nonnegative[local,simp]:
  ∀bits i. 0 ≤ int_unsigned bits i
Proof
  rw [word_simpTheory.int_unsigned_def]
  \\ mp_tac (Q.SPECL [`i`,`&(2 ** bits)`] integerTheory.INT_MOD_BOUNDS)
  \\ simp []
QED

Theorem word_simp_int_sh_side[local]:
  ∀bits sh i j. word_simp_int_sh_side bits sh i j
Proof
  simp [fetch "-" "word_simp_int_sh_side_def", int_unsigned_nonnegative]
QED
val _ = update_precondition word_simp_int_sh_side;

val _ = translate word_simpTheory.int_cmp_def;

(* TODO: remove when pmatch is fixed *)
val _ = translate (word_simpTheory.const_fp_loop_def)

val _ = translate (word_simpTheory.is_simple_pmatch_def)
val _ = translate (word_simpTheory.dest_Raise_num_pmatch_def)
val _ = translate (word_simpTheory.try_if_hoist2_def)
val _ = translate (word_simpTheory.try_if_hoist1_def)
val _ = translate (word_simpTheory.Seq_assoc_def)
val _ = translate (word_simpTheory.simp_duplicate_if_def)

val _ = translate (word_simpTheory.compile_exp_def)

val _ = translate (wordLangTheory.max_var_inst_def)
val _ = translate (wordLangTheory.max_var_def)

val _ = translate (word_instTheory.is_Lookup_CurrHeap_pmatch)
val res = translate_no_ind (word_instTheory.inst_select_exp_pmatch |> SIMP_RULE std_ss [word_mul_def,word_2comp_def])

Theorem inst_select_exp_ind[local]:
  word_inst_inst_select_exp_ind
Proof
  rewrite_tac [fetch "-" "word_inst_inst_select_exp_ind_def"]
  \\ rpt gen_tac
  \\ rpt (disch_then strip_assume_tac)
  \\ match_mp_tac (latest_ind ())
  \\ rpt strip_tac
  \\ last_x_assum (match_mp_tac o MP_CANON)
  \\ rpt strip_tac
  \\ fs [FORALL_PROD]
  \\ rveq
  THEN1
   (last_x_assum (match_mp_tac o MP_CANON)
    \\ fs [] \\ rveq \\ fs [])
  THEN1
   (Cases_on `exp` \\ fs []
    \\ Cases_on `b` \\ fs []
    \\ Cases_on `l` \\ fs []
    \\ Cases_on `t` \\ fs []
    \\ Cases_on `h'` \\ fs []
    \\ Cases_on `t'` \\ fs [])
  \\ fs []
  \\ Cases_on `e2` \\ fs []
QED

val _ = inst_select_exp_ind |> update_precondition;

val _ = translate (word_instTheory.op_consts_pmatch)

val _ = translate (word_instTheory.convert_sub_pmatch |> SIMP_RULE std_ss [word_2comp_def,word_mul_def])

val r = translate (word_instTheory.pull_exp_def(*_pmatch*)) (* TODO: MAP pull_exp inside pmatch seems to throw the translator into an infinite loop *)

val word_inst_pull_exp_side = Q.prove(`
  ∀x. word_inst_pull_exp_side x ⇔ T`,
  ho_match_mp_tac word_instTheory.pull_exp_ind>>rw[]>>
  simp[Once (fetch "-" "word_inst_pull_exp_side_def"),
      fetch "-" "word_inst_optimize_consts_side_def",
      word_simpTheory.int_op_def]>>
  metis_tac[]) |> update_precondition

val _ = translate (word_instTheory.inst_select_def(*pmatch*))

val _ = translate (word_allocTheory.list_next_var_rename_move_def)
val _ = translate word_allocTheory.force_rename_def

val _ = translate (word_allocTheory.ssa_reconcile_def);
val _ = translate (word_allocTheory.loop_setup_def);

val _ = translate (word_allocTheory.ssa_cc_trans_inst_def)
val _ = translate (word_allocTheory.full_ssa_cc_trans_def)

val _ = translate (word_allocTheory.remove_dead_inst_def)
val _ = translate (word_allocTheory.get_live_inst_def)
val _ = translate (word_allocTheory.get_live_def)
val _ = translate (word_allocTheory.remove_dead_def)
val _ = translate (word_allocTheory.remove_dead_prog_def)

Theorem lem[local]:
  dimindex(:64) = 64 ∧
  dimindex(:32) = 32
Proof
  EVAL_TAC
QED

val _ = translate (word_allocTheory.get_forced_pmatch
                  |> SIMP_RULE (bool_ss++ARITH_ss) [lem])

val _ = translate (word_allocTheory.get_delta_inst_def)
val _ = translate (word_allocTheory.get_clash_tree_def)
val _ = translate (wordLangTheory.every_var_inst_def)
val _ = translate word_allocTheory.select_reg_alloc_def
val _ = translate ( word_allocTheory.word_alloc_def)

val _ = translate word_instTheory.three_to_two_reg_def;
val _ = translate word_instTheory.three_to_two_reg_prog_def;
val _ = translate word_removeTheory.remove_must_terminate_def;
val _ = translate word_to_wordTheory.compile_alt;

(* ------------------------------------------------------------------------- *)
(* word_to_stack                                                             *)
(* ------------------------------------------------------------------------- *)

val _ = translate word_to_stackTheory.bits_to_word_def;
val _ = translate word_to_stackTheory.word_list_def;
val _ = translate word_to_stackTheory.chunk_to_bits_def;
val _ = translate word_to_stackTheory.chunk_to_bitmap_def;
val _ = translate word_to_stackTheory.const_words_to_bitmap_def;
Theorem word_to_stack_chunk_to_bitmap_side_total[local]:
  ∀bits ws. word_to_stack_chunk_to_bitmap_side bits ws
Proof
  rw [fetch "-" "word_to_stack_chunk_to_bitmap_side_def"]
  \\ mp_tac (Q.SPECL [`v1`,`&(2 ** bits)`] integerTheory.INT_MOD_BOUNDS)
  \\ simp []
QED
val _ = update_precondition word_to_stack_chunk_to_bitmap_side_total;

Theorem word_to_stack_const_words_to_bitmap_side_total[local]:
  ∀bits ws ws_len. word_to_stack_const_words_to_bitmap_side bits ws ws_len
Proof
  ho_match_mp_tac word_to_stackTheory.const_words_to_bitmap_ind
  \\ rpt strip_tac
  \\ once_rewrite_tac [fetch "-" "word_to_stack_const_words_to_bitmap_side_def"]
  \\ gvs [word_to_stack_chunk_to_bitmap_side_total]
QED
val _ = update_precondition word_to_stack_const_words_to_bitmap_side_total;

val _ = translate (word_to_stackTheory.write_bitmap_def
  |> REWRITE_RULE (!extra_preprocessing));
val _ = translate (word_to_stackTheory.wLive_def |> SIMP_RULE std_ss [LET_THM]);

val _ = translate parmoveTheory.fstep_def

val parmove_fstep_side = Q.prove(`
  ∀x. parmove_fstep_side x ⇔ T`,
  EVAL_TAC>>rw[]>>Cases_on`v18`>>fs[]) |> update_precondition

val _ = translate (word_to_stackTheory.wMove_def)

val _ = translate (word_to_stackTheory.call_dest_def)

val _ = translate (word_to_stackTheory.wInst_def)

val _ = translate (word_to_stackTheory.perf_call_prefix_def)
(* top-level vals must not call functions (no_ptr_eq), so unfold list_Seq *)
val _ = translate (word_to_stackTheory.perf_call_suffix_def
                   |> REWRITE_RULE [stackLangTheory.list_Seq_def])

val _ = translate (word_to_stackTheory.num_stack_ret_def |> INST_TYPE [alpha|->``:num``])
val _ = translate (word_to_stackTheory.skip_free_def |> INST_TYPE [alpha|->``:num``,beta|->``:num``])
val _ = translate (word_to_stackTheory.copy_ret_def |> INST_TYPE [alpha|->``:num``,beta|->``:num``])
val _ = translate (word_to_stackTheory.stack_arg_count_def |> INST_TYPE [alpha|->``:num``,beta|->``:num``])
val _ = translate (word_to_stackTheory.StackArgs_def |> INST_TYPE [alpha|->``:num``,beta|->``:num``])
val _ = translate (word_to_stackTheory.StackHandlerArgs_def |> INST_TYPE [alpha|->``:num``,beta|->``:num``])
val _ = translate (word_to_stackTheory.PushHandler_def |> INST_TYPE [alpha|->``:num``,beta|->``:num``])
val _ = translate (word_to_stackTheory.PopHandler_def |> INST_TYPE [alpha|->``:num``,beta|->``:num``])

val _ = translate word_to_stackTheory.comp_def;
val _ = translate (word_to_stackTheory.compile_word_to_stack_def
  |> INST_TYPE [alpha |-> “:num”]);
val _ = translate word_to_stackTheory.compile_def;

val _ = translate backendTheory.from_word_def;

val _ = translate backendTheory.from_word_0_def;

val r = presLangTheory.word_exp_to_display_def |> translate
val r = presLangTheory.ws_to_display_def |> translate
val r = presLangTheory.word_seqs_def |> translate

val r = presLangTheory.word_prog_to_display_def

          |> REWRITE_RULE [presLangTheory.string_imp_def]
          |> translate

val r = presLangTheory.word_fun_to_display_def |> translate

val _ = register_type “:any_prog”;

val res = translate (data_to_wordTheory.max_heap_limit_def
  |> SIMP_RULE std_ss [backend_commonTheory.word_shift_def]);

val r = backend_passesTheory.word_internal_all_def |> translate;

val r = backend_passesTheory.from_lab_all_def |> translate;

val r = backend_passesTheory.from_stack_all_def |> translate;

val r = backend_passesTheory.from_word_all_def |> translate;

val r = backend_passesTheory.from_word_0_all_def |> translate;

val r = presLangTheory.word_to_strs_def |> translate
val r = presLangTheory.stack_to_strs_def |> translate
val r = labLangTheory.Section_num_def |> translate
val r = labLangTheory.Section_metadata_def |> translate
val r = presLangTheory.lab_to_strs_def |> translate

val r = backend_passesTheory.any_prog_pp_def |> translate;
val r = backend_passesTheory.pp_with_title_def |> translate;
val _ = ml_translatorLib.ml_prog_update (ml_progLib.close_module NONE);

val _ = use_long_names := false;
val _ = translate lexer_implTheory.num_from_dec_string_alt_def;
val _ = translate lexer_implTheory.num_from_hex_string_alt_def;

Theorem unhex_alt_side_total[local]:
  ∀c. unhex_alt_side c
Proof
  simp [Once (fetch "-" "unhex_alt_side_def"),
        Once (fetch "-" "unhex_side_def"),isDigit_def,isHexDigit_def]
  \\ Cases \\ fs [ORD_CHR]
  \\ strip_tac \\ fs []
QED

Theorem num_from_dec_string_alt_side:
  ∀x. num_from_dec_string_alt_side x
Proof
  simp [Once (fetch "-" "num_from_dec_string_alt_side_def"),
        Once (fetch "-" "s2n_side_def"),hol_baseProgTheory.l2n_side,
        unhex_alt_side_total]
QED

val _ = update_precondition num_from_dec_string_alt_side;

Theorem num_from_hex_string_alt_side:
  ∀x. num_from_hex_string_alt_side x
Proof
  simp [Once (fetch "-" "num_from_hex_string_alt_side_def"),
        Once (fetch "-" "s2n_side_def"),hol_baseProgTheory.l2n_side,
        unhex_alt_side_total]
QED

val _ = update_precondition num_from_hex_string_alt_side;
val _ = use_long_names := true;

val res = translate all_bytes_eq
val res = translate byte_to_string_eq
val res = translate escape_sym_char_def
val res = translate get_sym_label_def
val res = translate get_sym_labels_def
val res = translate emit_symbol_def
val res = translate emit_symbols_def

Theorem export_byte_to_string_side_total[local]:
  ∀b. export_byte_to_string_side b
Proof
  fs [fetch "-" "export_byte_to_string_side_def"]
  \\ Cases \\ fs [] \\ EVAL_TAC \\ fs []
QED

val _ = update_precondition export_byte_to_string_side_total;

val res = translate split16_def;
val res = translate preamble_def;
val res = translate (data_buffer_def |> CONV_RULE (RAND_CONV EVAL));
val res = translate (code_buffer_def |> CONV_RULE (RAND_CONV EVAL));

fun is_strcat_lits tm =
let val (t1,t2) = stringSyntax.dest_strcat tm in
  stringSyntax.is_string_literal t1 andalso
              stringSyntax.is_string_literal t2
              end handle HOL_ERR _ => false
val res = translate
          ( data_section_def
              |> SIMP_RULE std_ss [MAP]
              |> CONV_RULE(DEPTH_CONV(EVAL o (assert is_strcat_lits)))
              |> SIMP_RULE std_ss [mlstringTheory.implode_STRCAT]
              |> SIMP_RULE std_ss [mlstringTheory.strcat_assoc]
              |> SIMP_RULE std_ss [GSYM mlstringTheory.implode_STRCAT]
              |> CONV_RULE(DEPTH_CONV(EVAL o (assert is_strcat_lits)))
              |> SIMP_RULE std_ss [mlstringTheory.implode_STRCAT])
(* -- *)

val res = translate comm_strlit_def;
val res = translate newl_strlit_def;
val res = translate comma_cat_def;

val res = translate words_line_def;

val res = translate word_to_string_def;
(* -- *)

val _ = translate compiler_commonTheory.find_next_newline_def;
val _ = translate compiler_commonTheory.safe_substring_def;
val _ = translate compiler_commonTheory.get_nth_line_def;
val _ = translate compiler_commonTheory.locs_to_string_def;

val res = translate compiler_commonTheory.parse_bool_def;
val res = translate compiler_commonTheory.parse_num_def;

val res = translate compiler_commonTheory.find_str_def;
val res = translate compiler_commonTheory.find_strs_def;
val res = translate compiler_commonTheory.find_bool_def;
val res = translate compiler_commonTheory.find_num_def;
val res = translate compiler_commonTheory.get_err_str_def;

val res = translate compiler_commonTheory.parse_num_list_def;

(* comma_tokens treats strings as char lists so we switch modes temporarily *)
val res = translate compiler_commonTheory.comma_tokens_def;
val res = translate compiler_commonTheory.parse_nums_def;

val res = translate clos_knownTheory.default_inline_factor_def;
val res = translate clos_knownTheory.default_max_body_size_def;
val res = translate clos_knownTheory.mk_config_def;
val res = translate clos_to_bvlTheory.max_app_limit_def;
val res = translate compiler_commonTheory.parse_clos_conf_def;
val res = translate compiler_commonTheory.parse_bvl_conf_def;
val res = translate compiler_commonTheory.parse_wtw_conf_def;
val res = translate compiler_commonTheory.parse_gc_def;
val res = translate compiler_commonTheory.parse_data_conf_def;
val res = translate compiler_commonTheory.parse_stack_conf_def;
val res = translate (compiler_commonTheory.parse_tap_conf_def
                     |> REWRITE_RULE [MEMBER_INTRO]);
val res = translate compiler_commonTheory.parse_lab_conf_def;


val res = translate backendTheory.prim_src_config_eq;

(* x64 *)
val res = translate x64_configTheory.x64_names_def;
val res = translate export_x64Theory.startup_def;
val res = translate export_x64Theory.ffi_asm_def;
val res = translate export_x64Theory.windows_ffi_asm_def;
val res = translate export_x64Theory.export_func_def;
val res = translate export_x64Theory.export_funcs_def;
val res = translate export_x64Theory.x64_export_def;
val res = translate
          (x64_configTheory.x64_backend_config_def
             |> SIMP_RULE(srw_ss())[FUNION_FUPDATE_1]);

(* riscv *)
val res = translate riscv_configTheory.riscv_names_def;
val res = translate export_riscvTheory.startup_def;
val res = translate export_riscvTheory.ffi_asm_def;
val res = translate export_riscvTheory.export_func_def;
val res = translate export_riscvTheory.export_funcs_def;
val res = translate export_riscvTheory.riscv_export_def;
val res = translate
          (riscv_configTheory.riscv_backend_config_def
             |> SIMP_RULE(srw_ss())[FUNION_FUPDATE_1]);

(* mips *)
val res = translate mips_configTheory.mips_names_def;
val res = translate export_mipsTheory.startup_def;
val res = translate export_mipsTheory.ffi_asm_def;
val res = translate export_mipsTheory.export_func_def;
val res = translate export_mipsTheory.export_funcs_def;
val res = translate export_mipsTheory.mips_export_def;
val res = translate
          (mips_configTheory.mips_backend_config_def
             |> SIMP_RULE(srw_ss())[FUNION_FUPDATE_1]);

(* arm8 *)
val res = translate arm8_configTheory.arm8_names_def;
val res = translate export_arm8Theory.startup_def;
val res = translate export_arm8Theory.ffi_asm_def;
val res = translate export_arm8Theory.export_func_def;
val res = translate export_arm8Theory.export_funcs_def;
val res = translate (export_arm8Theory.arm8_code_buffer_def
                       |> CONV_RULE (RAND_CONV EVAL));
val res = translate export_arm8Theory.arm8_export_def;
val res = translate
          (arm8_configTheory.arm8_backend_config_def
             |> SIMP_RULE(srw_ss())[FUNION_FUPDATE_1]);

(* ag32 *)
val res = translate ag32_configTheory.ag32_names_def;
val res = translate export_ag32Theory.ag32_export_def;
val res = translate
  (ag32_configTheory.ag32_backend_config_def
   |> SIMP_RULE(srw_ss())[FUNION_FUPDATE_1]);

(* arm7 *)
(* top-level vals must not call functions (no_ptr_eq), so the register
   name map is evaluated to sptree constructors (as the other targets'
   *_names_def already are) *)
val res = translate (arm7_configTheory.arm7_names_def |> CONV_RULE (RAND_CONV EVAL));
val res = translate export_arm7Theory.startup_def;
val res = translate export_arm7Theory.ffi_asm_def;
val res = translate export_arm7Theory.export_func_def;
val res = translate export_arm7Theory.export_funcs_def;
val res = translate export_arm7Theory.arm7_export_def;
val res = translate
  (arm7_configTheory.arm7_backend_config_def
   |> SIMP_RULE(srw_ss())[FUNION_FUPDATE_1]);

val _ = translate (compiler_commonTheory.extend_conf_def |> REWRITE_RULE [MEMBER_INTRO]);
val _ = translate (compiler_commonTheory.parse_target_def |> REWRITE_RULE [MEMBER_INTRO]);
val _ = translate (compiler_commonTheory.add_tap_output_def |> REWRITE_RULE [MEMBER_INTRO]);
val _ = translate (compiler_commonTheory.has_version_flag_def |> REWRITE_RULE [MEMBER_INTRO]);
val _ = translate (compiler_commonTheory.has_help_flag_def |> REWRITE_RULE [MEMBER_INTRO]);
val _ = translate (compiler_commonTheory.is_error_msg_def |> REWRITE_RULE [MEMBER_INTRO]);
val _ = translate (compiler_commonTheory.print_option_def |> REWRITE_RULE [MEMBER_INTRO]);
val _ = translate backendTheory.ffinames_to_string_list_def;

val _ = ml_translatorLib.clean_on_exit := true;
