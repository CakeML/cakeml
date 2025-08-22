(*
  Finish translation of the 32-bit version of the compiler.
*)
Theory compiler32Prog
Ancestors
  compiler export ml_translator ag32Prog[qualified]
  arm7Prog[qualified] basis_ffi[qualified]
Libs
  preamble ml_translatorLib cfLib basis

open preamble;
open compilerTheory
     exportTheory
     ml_translatorLib ml_translatorTheory;
open cfLib basis;

val _ = temp_delsimps ["NORMEQ_CONV", "lift_disj_eq", "lift_imp_disj"]

val _ = translation_extends "ag32Prog";
val _ = ml_translatorLib.use_string_type true;
val _ = ml_translatorLib.use_sub_check true;

val _ = ml_translatorLib.ml_prog_update (ml_progLib.open_module "compiler32Prog");

val () = Globals.max_print_depth := 15;

val () = use_long_names := true;

val spec32 = INST_TYPE[alpha|->``:32``]

val res = translate $ errorLogMonadTheory.return_def;
val res = translate $ errorLogMonadTheory.bind_def;
val res = translate $ errorLogMonadTheory.log_def;
val res = translate $ errorLogMonadTheory.error_def;

val res = translate $ panStaticTheory.based_merge_def;
val res = translate $ panStaticTheory.based_cmp_def;
val res = translate $ panStaticTheory.branch_vbases_def;
val res = translate $ panStaticTheory.seq_vbases_def;

val res = translate $ panStaticTheory.last_to_str_def;
val res = translate $ panStaticTheory.next_is_reachable_def;
val res = translate $ panStaticTheory.next_now_unreachable_def;
val res = translate $ spec32 $ panStaticTheory.reached_warnable_def;
val res = translate $ panStaticTheory.branch_last_stmt_def;
val res = translate $ panStaticTheory.seq_last_stmt_def;

val res = translate $ panStaticTheory.get_scope_desc_def;
val res = translate $ panStaticTheory.get_scope_msg_def;
val res = translate $ panStaticTheory.get_redec_msg_def;
val res = translate $ panStaticTheory.get_memop_msg_def;
val res = translate $ panStaticTheory.get_oparg_msg_def;
val res = translate $ panStaticTheory.get_unreach_msg_def;
val res = translate $ panStaticTheory.get_rogue_msg_def;

val res = translate $ panStaticTheory.first_repeat_def;
val res = translate $ panStaticTheory.binop_to_str_def;
val res = translate $ panStaticTheory.panop_to_str_def;

val res = translate $ panStaticTheory.scope_check_global_var_def;
val res = translate $ panStaticTheory.scope_check_local_var_def;
val res = translate $ panStaticTheory.scope_check_var_def;
val res = translate $ panStaticTheory.scope_check_fun_name_def;

val res = translate $ spec32 $ panStaticTheory.static_check_exp_def;
val res = translate $ panStaticTheory.check_redec_var_def;
val res = translate $ spec32 $ panStaticTheory.static_check_prog_def;
val res = translate $ spec32 $ panStaticTheory.static_check_funs_def;
val res = translate $ spec32 $ panStaticTheory.static_check_globals_def;
val res = translate $ spec32 $ panStaticTheory.static_check_def;

Definition max_heap_limit_32_def:
  max_heap_limit_32 c =
    ^(spec32 data_to_wordTheory.max_heap_limit_def
      |> SPEC_ALL
      |> SIMP_RULE (srw_ss())[backend_commonTheory.word_shift_def]
      |> concl |> rhs)
End

val res = translate max_heap_limit_32_def

Theorem max_heap_limit_32_thm:
   max_heap_limit (:32) = max_heap_limit_32
Proof
  rw[FUN_EQ_THM] \\ EVAL_TAC
QED

val r = translate presLangTheory.default_tap_config_def;

val def = spec32
  (backendTheory.attach_bitmaps_def
   |> Q.GENL[`c'`,`bytes`,`c`]
   |> Q.ISPECL[`lab_conf:'a lab_to_target$config`,`bytes:word8 list`,`c:'a backend$config`])

val res = translate def

val def = spec32 backendTheory.compile_def
  |> REWRITE_RULE[max_heap_limit_32_thm]

val res = translate def

val _ = register_type “:32 any_prog”

val r = backend_passesTheory.to_flat_all_def |> spec32 |> translate;
val r = backend_passesTheory.to_clos_all_def |> spec32 |> translate;
val r = backend_passesTheory.to_bvl_all_def |> spec32 |> translate;
val r = backend_passesTheory.to_bvi_all_def |> spec32 |> translate;

Triviality backend_passes_to_bvi_all_side:
  backend_passes_to_bvi_all_side c p
Proof
  fs [fetch "-" "backend_passes_to_bvi_all_side_def"]
  \\ rewrite_tac [GSYM LENGTH_NIL,bvl_inlineTheory.LENGTH_remove_ticks]
  \\ fs []
QED

val _ = update_precondition backend_passes_to_bvi_all_side

val r = backend_passesTheory.to_data_all_def |> spec32 |> translate;

val r = backend_passesTheory.word_internal_def |> spec32 |> translate;

val r = backend_passesTheory.to_word_all_def |> spec32
          |> REWRITE_RULE [data_to_wordTheory.stubs_def,APPEND] |> translate;

val r = backend_passesTheory.to_stack_all_def |> spec32
          |> REWRITE_RULE[max_heap_limit_32_thm] |> translate;

val r = backend_passesTheory.to_lab_all_def |> spec32
          |> REWRITE_RULE[max_heap_limit_32_thm] |> translate;

val r = backend_passesTheory.to_target_all_def |> spec32 |> translate;

val r = backend_passesTheory.from_lab_all_def |> spec32 |> translate;

val r = backend_passesTheory.from_stack_all_def |> spec32
          |> REWRITE_RULE[max_heap_limit_32_thm] |> translate;

val r = backend_passesTheory.from_word_all_def |> spec32 |> translate;

val r = backend_passesTheory.from_word_0_all_def |> spec32
          |> REWRITE_RULE[max_heap_limit_32_thm] |> translate;

val r = presLangTheory.word_to_strs_def |> spec32 |> translate
val r = presLangTheory.stack_to_strs_def |> spec32 |> translate
val r = presLangTheory.lab_to_strs_def |> spec32 |> translate

val r = backend_passesTheory.any_prog_pp_def |> spec32 |> translate;
val r = backend_passesTheory.pp_with_title_def |> translate;
val r = backend_passesTheory.compile_tap_def |> spec32 |> translate;

val _ = r |> hyp |> null orelse
        failwith ("Unproved side condition in the translation of " ^
                  "backend_passesTheory.compile_tap_def.");

val r = pan_passesTheory.pan_to_target_all_def |> spec32
          |> REWRITE_RULE [NULL_EQ] |> translate;

val r = pan_passesTheory.opsize_to_display_def |> translate;
val r = pan_passesTheory.shape_to_str_def |> translate;
val r = pan_passesTheory.insert_es_def |> translate;
val r = pan_passesTheory.varkind_to_str_def |> translate;
Triviality lem:
  dimindex(:32) = 32
Proof
  EVAL_TAC
QED
val r = pan_passesTheory.pan_exp_to_display_def |> spec32 |> SIMP_RULE std_ss [byteTheory.bytes_in_word_def,lem] |> translate;
val r = pan_passesTheory.crep_exp_to_display_def |> spec32 |> translate;
val r = pan_passesTheory.loop_exp_to_display_def |> spec32 |> translate;

val r = pan_passesTheory.dest_annot_def |> spec32 |> translate;
val r = pan_passesTheory.pan_seqs_def |> spec32 |> translate;
val r = pan_passesTheory.crep_seqs_def |> spec32 |> translate;
val r = pan_passesTheory.loop_seqs_def |> spec32 |> translate;
val r = pan_passesTheory.pan_prog_to_display_def |> spec32 |> translate;
val r = pan_passesTheory.crep_prog_to_display_def |> spec32 |> translate;
val r = pan_passesTheory.loop_prog_to_display_def |> spec32 |> translate;
val r = pan_passesTheory.pan_fun_to_display_def |> spec32 |> translate;
val r = pan_passesTheory.crep_fun_to_display_def |> spec32 |> translate;
val r = pan_passesTheory.loop_fun_to_display_def |> spec32 |> translate;
val r = pan_passesTheory.pan_to_strs_def |> spec32 |> translate;
val r = pan_passesTheory.crep_to_strs_def |> spec32 |> translate;
val r = pan_passesTheory.loop_to_strs_def |> spec32 |> translate;
val r = pan_passesTheory.any_pan_prog_pp_def |> spec32 |> translate;

val r = pan_passesTheory.pan_compile_tap_def |> spec32 |> translate;

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

val export_byte_to_string_side_def = prove(
  ``!b. export_byte_to_string_side b``,
  fs [fetch "-" "export_byte_to_string_side_def"]
  \\ Cases \\ fs [] \\ EVAL_TAC \\ fs [])
  |> update_precondition;

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
  |> SIMP_RULE std_ss [mlstringTheory.implode_STRCAT |> REWRITE_RULE[mlstringTheory.implode_def]]
  |> SIMP_RULE std_ss [mlstringTheory.strcat_assoc]
  |> SIMP_RULE std_ss [GSYM(mlstringTheory.implode_STRCAT |> REWRITE_RULE[mlstringTheory.implode_def])]
  |> CONV_RULE(DEPTH_CONV(EVAL o (assert is_strcat_lits)))
  |> SIMP_RULE std_ss [mlstringTheory.implode_STRCAT |> REWRITE_RULE[mlstringTheory.implode_def]]
  |> CONV_RULE(DEPTH_CONV(RATOR_CONV (REWR_CONV (SYM mlstringTheory.implode_def)) o (assert is_strlit_var))))
(* -- *)

val res = translate comm_strlit_def;
val res = translate newl_strlit_def;
val res = translate comma_cat_def;

val res = translate words_line_def;

val res = translate (spec32 word_to_string_def);
(* -- *)

(* compilerTheory *)

val res = translate compilerTheory.find_next_newline_def;

val res = translate compilerTheory.safe_substring_def;

val _ = translate compilerTheory.get_nth_line_def;
val _ = translate compilerTheory.locs_to_string_def;
val _ = translate compilerTheory.parse_cml_input_def;
val _ = translate (compilerTheory.parse_sexp_input_def
                   |> PURE_REWRITE_RULE[fromSexpTheory.sexpdec_alt_intro1]);

val def = spec32 (compilerTheory.compile_def);
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
val _ = ml_translatorLib.use_string_type false;
val res = translate comma_tokens_def;
val res = translate parse_nums_def;
val _ = ml_translatorLib.use_string_type true;

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
val res = translate (parse_lab_conf_def |> spec32)

val res = translate (parse_top_config_def |> SIMP_RULE (srw_ss()) []);

(* Translations for each 32-bit target
  Note: ffi_asm is translated multiple times...
*)

val res = translate backendTheory.prim_src_config_eq;

(* ag32 *)
val res = translate ag32_configTheory.ag32_names_def;
val res = translate export_ag32Theory.ag32_export_def;
val res = translate
  (ag32_configTheory.ag32_backend_config_def
   |> SIMP_RULE(srw_ss())[FUNION_FUPDATE_1]);

(* arm7 *)
val res = translate arm7_configTheory.arm7_names_def;
val res = translate export_arm7Theory.startup_def;
val res = translate export_arm7Theory.ffi_asm_def;
val res = translate export_arm7Theory.export_func_def;
val res = translate export_arm7Theory.export_funcs_def;
val res = translate export_arm7Theory.arm7_export_def;
val res = translate
  (arm7_configTheory.arm7_backend_config_def
   |> SIMP_RULE(srw_ss())[FUNION_FUPDATE_1]);

(* Leave the module now, so that key things are available in the toplevel
   namespace for main. *)
val _ = ml_translatorLib.ml_prog_update (ml_progLib.close_module NONE);

(* Rest of the translation *)
val res = translate (extend_conf_def |> spec32 |> SIMP_RULE (srw_ss()) [MEMBER_INTRO]);
val res = translate parse_target_32_def;
val res = translate add_tap_output_def;

val res = translate backendTheory.ffinames_to_string_list_def;

val res = format_compiler_result_def
        |> Q.GENL[`bytes`,`c`]
        |> Q.ISPECL[`bytes:word8 list`,`c:'a backend$config`]
        |> spec32
        |> translate;

val res = translate compile_32_def;

val res = translate (has_version_flag_def |> SIMP_RULE (srw_ss()) [MEMBER_INTRO])
val res = translate (has_help_flag_def |> SIMP_RULE (srw_ss()) [MEMBER_INTRO])
val res = translate print_option_def
val res = translate current_build_info_str_def
val res = translate compilerTheory.help_string_def;

Definition nonzero_exit_code_for_error_msg_def:
  nonzero_exit_code_for_error_msg e =
    if compiler$is_error_msg e then
      (let a = empty_ffi (strlit "nonzero_exit") in
         ml_translator$force_out_of_memory_error ())
    else ()
End

val res = translate compilerTheory.is_error_msg_def;
val res = translate nonzero_exit_code_for_error_msg_def;

val res = translate $ spec32 compile_pancake_def;

val res = translate compile_pancake_32_def;

val res = translate (has_pancake_flag_def |> SIMP_RULE (srw_ss()) [MEMBER_INTRO])

val main = process_topdecs`
  fun main u =
    let
      val cl = CommandLine.arguments ()
    in
      if compiler_has_help_flag cl then
        print compiler_help_string
      else if compiler_has_version_flag cl then
        print compiler_current_build_info_str
      else if compiler_has_pancake_flag cl then
        case compiler_compile_pancake_32 cl (TextIO.inputAll TextIO.stdIn)  of
          (c, e) => (print_app_list c; TextIO.output TextIO.stdErr e;
                     compiler32prog_nonzero_exit_code_for_error_msg e)
      else
        case compiler_compile_32 cl (TextIO.inputAll TextIO.stdIn)  of
          (c, e) => (print_app_list c; TextIO.output TextIO.stdErr e;
                     compiler32prog_nonzero_exit_code_for_error_msg e)
    end`;

val res = append_prog main;

val main_v_def = fetch "-" "main_v_def";

Theorem main_spec:
   app (p:'ffi ffi_proj) main_v
     [Conv NONE []] (STDIO fs * COMMANDLINE cl)
     (POSTv uv.
       &UNIT_TYPE () uv
       * STDIO (full_compile_32 (TL cl) (get_stdin fs) fs)
       * COMMANDLINE cl)
Proof
  xcf_with_def main_v_def
  \\ xlet_auto >- (xcon \\ xsimpl)
  \\ xlet_auto
  >- (
    (* TODO: xlet_auto: why doesn't xsimpl work here on its own? *)
    CONV_TAC SWAP_EXISTS_CONV \\ qexists_tac`cl`
    \\ xsimpl )
  \\ reverse(Cases_on`STD_streams fs`) >- (fs[STDIO_def] \\ xpull)
  (* TODO: it would be nice if this followed more directly.
           either (or both):
             - make STD_streams assert "stdin" is in the files
             - make wfFS separate from wfFS, so STDIO fs will imply wfFS fs *)
  \\ reverse(Cases_on`∃inp pos. stdin fs inp pos`)
  >- (
    fs[STDIO_def,IOFS_def] \\ xpull \\ fs[stdin_def]
    \\ `F` suffices_by fs[]
    \\ fs[wfFS_def,STD_streams_def,MEM_MAP,Once EXISTS_PROD,PULL_EXISTS]
    \\ fs[EXISTS_PROD]
    \\ metis_tac[ALOOKUP_FAILS,ALOOKUP_MEM,NOT_SOME_NONE,SOME_11,PAIR_EQ,option_CASES] )
  \\ fs[get_stdin_def]
  \\ SELECT_ELIM_TAC
  \\ simp[FORALL_PROD,EXISTS_PROD]
  \\ conj_tac >- metis_tac[] \\ rw[]
  \\ imp_res_tac stdin_11 \\ rw[]
  \\ imp_res_tac stdin_get_file_content
  \\ xlet_auto >- xsimpl
  \\ xif
  >-
   (simp[full_compile_32_def]
    \\ xapp
    \\ CONV_TAC SWAP_EXISTS_CONV
    \\ qexists_tac `help_string`
    \\ fs [compilerTheory.help_string_def,
           fetch "-" "compiler_help_string_v_thm"]
    \\ xsimpl
    \\ rename1 `add_stdout _ (strlit string)`
    \\ CONV_TAC SWAP_EXISTS_CONV
    \\ qexists_tac`fs`
    \\ xsimpl)
  \\ xlet_auto >- xsimpl
  \\ xif
  >- (
    simp[full_compile_32_def]
    \\ xapp
    \\ CONV_TAC SWAP_EXISTS_CONV
    \\ qexists_tac `current_build_info_str`
    \\ fs [compilerTheory.current_build_info_str_def,
           fetch "-" "compiler_current_build_info_str_v_thm"]
    \\ xsimpl
    \\ rename1 `add_stdout _ (strlit string)`
    \\ CONV_TAC SWAP_EXISTS_CONV
    \\ qexists_tac`fs`
    \\ xsimpl)
  >> xlet_auto>-xsimpl
  >> xif
  >- (
     xlet_auto >- (xsimpl \\ fs[INSTREAM_stdin, STD_streams_get_mode])
     \\ fs [GSYM HOL_STRING_TYPE_def]
     \\ xlet_auto >- xsimpl
     \\ fs [full_compile_32_def]
     \\ pairarg_tac
     \\ fs[ml_translatorTheory.PAIR_TYPE_def]
     \\ gvs[CaseEq "bool"]
     \\ xmatch
     \\ xlet_auto >- xsimpl

     \\ qmatch_goalsub_abbrev_tac `STDIO fs'`
     \\ xlet `POSTv uv. &UNIT_TYPE () uv * STDIO (add_stderr fs' err) *
        COMMANDLINE cl`
     THEN1
      (xapp_spec output_stderr_spec \\ xsimpl
       \\ qexists_tac `COMMANDLINE cl`
       \\ asm_exists_tac \\ xsimpl
       \\ qexists_tac `fs'` \\ xsimpl)
     \\ xapp
     \\ asm_exists_tac \\ simp [] \\ xsimpl)
  \\ xlet_auto >- (xsimpl \\ fs[INSTREAM_stdin, STD_streams_get_mode])
  \\ fs [GSYM HOL_STRING_TYPE_def]
  \\ xlet_auto >- xsimpl
  \\ fs [full_compile_32_def]
  \\ pairarg_tac
  \\ fs[ml_translatorTheory.PAIR_TYPE_def]
  \\ xmatch
  \\ xlet_auto >- xsimpl
  \\ qmatch_goalsub_abbrev_tac `STDIO fs'`
  \\ xlet `POSTv uv. &UNIT_TYPE () uv * STDIO (add_stderr fs' err) *
                     COMMANDLINE cl`
  THEN1
   (xapp_spec output_stderr_spec \\ xsimpl
    \\ qexists_tac `COMMANDLINE cl`
    \\ asm_exists_tac \\ xsimpl
    \\ qexists_tac `fs'` \\ xsimpl)
  \\ xapp
  \\ asm_exists_tac \\ simp [] \\ xsimpl
QED

Theorem main_whole_prog_spec:
   whole_prog_spec main_v cl fs NONE
    ((=) (full_compile_32 (TL cl) (get_stdin fs) fs))
Proof
  simp[whole_prog_spec_def,UNCURRY]
  \\ qmatch_goalsub_abbrev_tac`fs1 = _ with numchars := _`
  \\ qexists_tac`fs1`
  \\ reverse conj_tac >-
    rw[Abbr`fs1`,full_compile_32_def,UNCURRY,
       GSYM fastForwardFD_with_numchars,
       GSYM add_stdo_with_numchars, with_same_numchars]
  \\ simp [SEP_CLAUSES]
  \\ match_mp_tac(MP_CANON(MATCH_MP app_wgframe main_spec))
  \\ xsimpl
QED

val (semantics_thm,prog_tm) =
  whole_prog_thm (get_ml_prog_state()) "main" main_whole_prog_spec;

Definition compiler32_prog_def:
  compiler32_prog = ^prog_tm
End

Theorem semantics_compiler32_prog =
  semantics_thm
  |> PURE_ONCE_REWRITE_RULE[GSYM compiler32_prog_def]
  |> DISCH_ALL
  |> SIMP_RULE (srw_ss()) [AND_IMP_INTRO,GSYM CONJ_ASSOC]

val () = Feedback.set_trace "TheoryPP.include_docs" 0;
val _ = ml_translatorLib.reset_translation(); (* because this translation won't be continued *)
