(*
  Shared translation of the 64-bit compiler backends and command-line interface.
*)
Theory compiler64CommonProg[no_sig_docs]
Ancestors
  mipsProg compiler export ml_translator basis_ffi[qualified]
Libs
  preamble ml_translatorLib cfLib basis

open preamble
     mipsProgTheory compilerTheory
     exportTheory
     ml_translatorLib ml_translatorTheory
open cfLib basis

val _ = temp_delsimps ["NORMEQ_CONV", "lift_disj_eq", "lift_imp_disj"]

val _ = translation_extends "mipsProg";

val _ = ml_translatorLib.ml_prog_update (ml_progLib.open_module "compiler64Prog");
val _ = ml_translatorLib.use_sub_check true;

val _ = (ml_translatorLib.trace_timing_to
         := SOME "compiler64CommonProg_translate_timing.txt")

val () = Globals.max_print_depth := 15;

val () = use_long_names := true;

val spec64 = INST_TYPE[alpha|->``:64``]

val res = translate $ errorLogMonadTheory.return_def;
val res = translate $ errorLogMonadTheory.bind_def;
val res = translate $ errorLogMonadTheory.log_def;
val res = translate $ errorLogMonadTheory.error_def;

val res = translate $ listTheory.OPT_MMAP_def;

Theorem OPT_MMAP_eq_MAP[local]:
  OPT_MMAP f xs = (OPT_MMAP I o MAP f) xs
Proof
  simp [miscTheory.OPT_MMAP_MAP_o]
QED

(* move recursion out of OPT_MMAP to aid the translator *)
val res = panStaticTheory.sh_bd_from_sh_def
  |> REWRITE_RULE [OPT_MMAP_eq_MAP]
  |> SIMP_RULE std_ss [o_DEF]
  |> translate;

val res = translate $ panStaticTheory.sh_bd_from_bd_def;
val res = translate $ panStaticTheory.sh_bd_has_shape_def;
val res = translate $ panStaticTheory.sh_bd_eq_shapes_def;
val res = translate $ panStaticTheory.index_sh_bd_def;
val res = translate $ panStaticTheory.field_sh_bd_def;
val res = translate $ panStaticTheory.based_merge_def;
val res = translate $ panStaticTheory.sh_bd_branch_def;
val res = translate $ panStaticTheory.branch_loc_inf_def;
val res = translate $ panStaticTheory.seq_loc_inf_def;

val res = translate $ panStaticTheory.last_to_str_def;
val res = translate $ panStaticTheory.next_is_reachable_def;
val res = translate $ panStaticTheory.next_now_unreachable_def;
val res = translate $ spec64 $ panStaticTheory.reached_warnable_def;
val res = translate $ panStaticTheory.branch_last_stmt_def;
val res = translate $ panStaticTheory.seq_last_stmt_def;

val res = translate $ panStaticTheory.get_scope_desc_def;
val res = translate $ panStaticTheory.get_scope_msg_def;
val res = translate $ panStaticTheory.get_redec_msg_def;
val res = translate $ panStaticTheory.get_memop_msg_def;
val res = translate $ panStaticTheory.get_oparg_msg_def;
val res = translate $ panStaticTheory.get_unreach_msg_def;
val res = translate $ panStaticTheory.get_rogue_msg_def;
val res = translate $ panStaticTheory.get_non_word_msg_def;
val res = translate $ panStaticTheory.get_shape_mismatch_msg_def;
val res = translate $ panStaticTheory.get_implementation_err_msg_def;

val res = translate $ panStaticTheory.first_repeat_def;
val res = translate $ panStaticTheory.binop_to_str_def;
val res = translate $ panStaticTheory.panop_to_str_def;
val res = translate $ panStaticTheory.primop_to_str_def;
val res = translate $ panStaticTheory.sh_bd_to_str_def;

val res = translate $ alistTheory.ADELKEY_def;

val res = translate $ panStaticTheory.primitive_idents_def;
val res = translate $ panStaticTheory.add_primitive_hint_def;

val res = translate $ panStaticTheory.check_fun_name_def;
val res = translate $ panStaticTheory.check_global_var_def;
val res = translate $ panStaticTheory.check_local_var_def;
val res = translate $ panStaticTheory.check_redec_var_def;
val res = translate $ panStaticTheory.check_export_params_def;
val res = translate $ panStaticTheory.check_operands_def;
val res = translate $ panStaticTheory.check_primitive_args_def;
val res = translate $ panStaticTheory.check_func_args_def;
val res = translate $ panStaticTheory.check_struct_fields_def;
val res = translate $ panStaticTheory.check_shape_def;
val res = translate $ panStaticTheory.check_id_shapes_def;

val res = translate $ spec64 $ panStaticTheory.static_check_exp_def;
val res = translate $ spec64 $ panStaticTheory.static_check_prog_def;
val res = translate $ spec64 $ panStaticTheory.static_check_progs_def;
val res = translate $ spec64 $ panStaticTheory.static_check_decls_def;
val res = translate $ INST_TYPE[alpha|->``:staterr``] $
  INST_TYPE[beta|->``:64``] $ panStaticTheory.static_check_names_def;
val res = translate $ spec64 $ panStaticTheory.static_check_def;

val _ = res |> hyp |> null orelse
        failwith ("Unproved side condition in the translation of " ^
                  "panStaticTheory.static_check_def.");

Definition max_heap_limit_64_def:
  max_heap_limit_64 c =
    ^(spec64 data_to_wordTheory.max_heap_limit_def
      |> SPEC_ALL
      |> SIMP_RULE (srw_ss())[backend_commonTheory.word_shift_def]
      |> concl |> rhs)
End

val res = translate max_heap_limit_64_def

Theorem max_heap_limit_64_thm:
  max_heap_limit (:64) = max_heap_limit_64
Proof
  rw [FUN_EQ_THM] >> EVAL_TAC
QED

val r = translate presLangTheory.default_tap_config_def;

val def = spec64
          (backendTheory.attach_bitmaps_def
             |> Q.GENL[`c'`,`bytes`,`c`]
             |> Q.ISPECL[`lab_conf:lab_to_target$config`,`bytes:word8 list`,`c:backend$config`])

val res = translate def

val def = spec64 backendTheory.compile_def
  |> REWRITE_RULE[max_heap_limit_64_thm]

val res = translate def

val _ = register_type “:64 any_prog”

val r = backend_passesTheory.to_flat_all_def |> spec64 |> translate;
val r = backend_passesTheory.to_clos_all_def |> spec64 |> translate;
val r = backend_passesTheory.to_bvl_all_def |> spec64 |> translate;
val r = backend_passesTheory.to_bvi_all_def |> spec64 |> translate;

Theorem backend_passes_to_bvi_all_side[local]:
  backend_passes_to_bvi_all_side c p
Proof
  fs [fetch "-" "backend_passes_to_bvi_all_side_def"]
  \\ rewrite_tac [GSYM LENGTH_NIL,bvl_inlineTheory.LENGTH_remove_ticks]
  \\ fs []
QED

val _ = update_precondition backend_passes_to_bvi_all_side

val r = backend_passesTheory.to_data_all_def |> spec64 |> translate;

val r = backend_passesTheory.word_internal_all_def |> spec64 |> translate;

val r = backend_passesTheory.to_word_all_def |> spec64
          |> REWRITE_RULE [data_to_wordTheory.stubs_def,APPEND] |> translate;

val r = backend_passesTheory.to_stack_all_def |> spec64
          |> REWRITE_RULE[max_heap_limit_64_thm] |> translate;

val r = backend_passesTheory.to_lab_all_def |> spec64
          |> REWRITE_RULE[max_heap_limit_64_thm] |> translate;

val r = backend_passesTheory.to_target_all_def |> spec64 |> translate;

val r = backend_passesTheory.from_lab_all_def |> spec64 |> translate;

val r = backend_passesTheory.from_stack_all_def |> spec64
          |> REWRITE_RULE[max_heap_limit_64_thm] |> translate;

val r = backend_passesTheory.from_word_all_def |> spec64 |> translate;

val r = backend_passesTheory.from_word_0_all_def |> spec64
          |> REWRITE_RULE[max_heap_limit_64_thm] |> translate;

val r = presLangTheory.word_to_strs_def |> spec64 |> translate
val r = presLangTheory.stack_to_strs_def |> spec64 |> translate
val r = presLangTheory.lab_to_strs_def |> spec64 |> translate

val r = backend_passesTheory.any_prog_pp_def |> spec64 |> translate;
val r = backend_passesTheory.pp_with_title_def |> translate;
val r = backend_passesTheory.compile_tap_def |> spec64 |> translate;

val _ = r |> hyp |> null orelse
        failwith ("Unproved side condition in the translation of " ^
                  "backend_passesTheory.compile_tap_def.");

val r = pan_passesTheory.pan_to_target_all_def |> spec64
          |> REWRITE_RULE [NULL_EQ] |> translate;

val r = pan_passesTheory.opsize_to_display_def |> translate;
val r = pan_passesTheory.insert_es_def |> translate;
val r = pan_passesTheory.varkind_to_str_def |> translate;
Theorem lem[local]:
  dimindex(:64) = 64
Proof
  EVAL_TAC
QED
val r = pan_passesTheory.primop_to_display_def |> translate;
val r = pan_passesTheory.pan_exp_to_display_def |> spec64 |> SIMP_RULE std_ss [byteTheory.bytes_in_word_def,lem] |> translate;
val r = pan_passesTheory.crep_exp_to_display_def |> spec64 |> translate;
val r = pan_passesTheory.loop_exp_to_display_def |> spec64 |> translate;

val r = pan_passesTheory.dest_annot_def |> spec64 |> translate;
val r = pan_passesTheory.pan_seqs_def |> spec64 |> translate;
val r = pan_passesTheory.crep_seqs_def |> spec64 |> translate;
val r = pan_passesTheory.loop_seqs_def |> spec64 |> translate;
val r = pan_passesTheory.pan_prog_to_display_def |> spec64 |> translate;
val r = pan_passesTheory.crep_prog_to_display_def |> spec64 |> translate;
val r = pan_passesTheory.loop_prog_to_display_def |> spec64 |> translate;
val r = pan_passesTheory.pan_fun_to_display_def |> spec64 |> translate;
val r = pan_passesTheory.crep_fun_to_display_def |> spec64 |> translate;
val r = pan_passesTheory.loop_fun_to_display_def |> spec64 |> translate;
val r = pan_passesTheory.pan_to_strs_def |> spec64 |> translate;
val r = pan_passesTheory.crep_to_strs_def |> spec64 |> translate;
val r = pan_passesTheory.loop_to_strs_def |> spec64 |> translate;
val r = pan_passesTheory.any_pan_prog_pp_def |> spec64 |> translate;

val r = pan_passesTheory.pan_compile_tap_def |> spec64 |> translate;

val _ = r |> hyp |> null orelse
        failwith ("Unproved side condition in the translation of " ^
                  "pan_passesTheory.pan_compile_tap_def.");

(* exportTheory *)
(* TODO: exportTheory functions that don't depend on the word size
   should probably be moved up to to_dataProg or something*)
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

(* val res = translate space_line_def; *)

(* TODO: maybe do this directly to the definition of data_section *)
fun is_strcat_lits tm =
let val (t1,t2) = stringSyntax.dest_strcat tm in
  stringSyntax.is_string_literal t1 andalso
              stringSyntax.is_string_literal t2
              end handle HOL_ERR _ => false
fun is_strlit_var tm =
is_var (mlstringSyntax.dest_strlit tm)
       handle HOL_ERR _ => false
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

val res = translate (spec64 word_to_string_def);
(* -- *)

(* compilerTheory *)

val res = translate compilerTheory.find_next_newline_def;

val res = translate compilerTheory.safe_substring_def;

val _ = translate compilerTheory.get_nth_line_def;
val _ = translate compilerTheory.locs_to_string_def;
val _ = translate compilerTheory.parse_cml_input_def;
val _ = translate (compilerTheory.parse_sexp_input_def
                     |> PURE_REWRITE_RULE[fromSexpTheory.sexpdec_alt_intro1]);

val def = spec64 (compilerTheory.compile_def);
val res = translate def;

val res = translate (primTypesTheory.prim_tenv_def
                       |> CONV_RULE (RAND_CONV EVAL));

val res = translate inferTheory.init_config_def;

(* Compiler interface in compilerTheory
  TODO: some of these should be moved up, see comment above on exportScript
 *)
val res = translate error_to_str_def;

val res = translate parse_bool_def;
val res = translate parse_num_def;

val res = translate find_str_def;
val res = translate find_strs_def;
val res = translate find_bool_def;
val res = translate find_num_def;
val res = translate get_err_str_def;

val res = translate parse_num_list_def;

(* comma_tokens treats strings as char lists so we switch modes temporarily *)
val res = translate comma_tokens_def;
val res = translate parse_nums_def;

val res = translate clos_knownTheory.default_inline_factor_def;
val res = translate clos_knownTheory.default_max_body_size_def;
val res = translate clos_knownTheory.mk_config_def;
val res = translate parse_clos_conf_def;
val res = translate parse_bvl_conf_def;
val res = translate parse_wtw_conf_def;
val res = translate parse_gc_def;
val res = translate parse_data_conf_def;
val res = translate parse_stack_conf_def;
val res = translate parse_tap_conf_def;
val res = translate (parse_lab_conf_def |> spec64);

val res = translate (parse_top_config_def |> SIMP_RULE (srw_ss()) []);

(* Translations for each 64-bit target
  Note: ffi_asm is translated multiple times...
 *)

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

(* Leave the module now, so that key things are available in the toplevel
   namespace for main. *)
val _ = ml_translatorLib.ml_prog_update (ml_progLib.close_module NONE);

(* Rest of the translation *)
val res = translate (extend_conf_def |> spec64 |> SIMP_RULE (srw_ss()) [MEMBER_INTRO]);
val res = translate parse_target_64_def;
val res = translate add_tap_output_def;

val res = format_compiler_result_def
            |> Q.GENL[`bytes`,`c`]
            |> Q.ISPECL[`bytes:word8 list`,`c:backend$config`]
            |> spec64
            |> translate;

val res = translate backendTheory.ffinames_to_string_list_def;

val res = translate compile_64_def;

val _ = res |> hyp |> null orelse
        failwith ("Unproved side condition in the translation of " ^
                  "compile_64_def.");

val res = translate $ spec64 compile_pancake_def;

val res = translate pancake_backend_conf_def;

val res = translate compile_pancake_64_def;

val _ = res |> hyp |> null orelse
        failwith ("Unproved side condition in the translation of " ^
                  "compile_pancake_64_def.");

val res = translate (has_version_flag_def |> SIMP_RULE (srw_ss()) [MEMBER_INTRO])
val res = translate (has_help_flag_def |> SIMP_RULE (srw_ss()) [MEMBER_INTRO])
val res = translate print_option_def
val res = translate current_build_info_str_def
val res = translate compilerTheory.help_string_def;
val res = translate (newsTheory.query_news_def |> SIMP_RULE (srw_ss()) [MEMBER_INTRO])
val res = translate parse_pancake_feature_def
val res = translate print_bool_def

Definition nonzero_exit_code_for_error_msg_def:
  nonzero_exit_code_for_error_msg e =
  if compiler$is_error_msg e then
    (let a = empty_ffi «nonzero_exit» in
       ml_translator$force_out_of_memory_error ())
  else ()
End

val res = translate compilerTheory.is_error_msg_def;
val res = translate nonzero_exit_code_for_error_msg_def;
