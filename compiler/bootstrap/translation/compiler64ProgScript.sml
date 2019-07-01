(*
  Finish translation of the 64-bit version of the compiler.
*)
open preamble
     mipsProgTheory compilerTheory
     exportTheory
     ml_translatorLib ml_translatorTheory
open cfLib basis

val _ = new_theory"compiler64Prog";

val _ = translation_extends "mipsProg";

val _ = ml_translatorLib.ml_prog_update (ml_progLib.open_module "compiler64Prog");

val _ = (ml_translatorLib.trace_timing_to
    := SOME "compiler64Prog_translate_timing.txt")

val () = Globals.max_print_depth := 15;

val () = use_long_names := true;

val spec64 = INST_TYPE[alpha|->``:64``]

val max_heap_limit_64_def = Define`
  max_heap_limit_64 c =
    ^(spec64 data_to_wordTheory.max_heap_limit_def
      |> SPEC_ALL
      |> SIMP_RULE (srw_ss())[backend_commonTheory.word_shift_def]
      |> concl |> rhs)`;

val res = translate max_heap_limit_64_def

Theorem max_heap_limit_64_thm:
   max_heap_limit (:64) = max_heap_limit_64
Proof
  rw[FUN_EQ_THM] \\ EVAL_TAC
QED

(*

val def = spec64 backendTheory.compile_explorer_def

val res = translate def

val backend_compile_explorer_side = Q.prove(`
  ∀x y. backend_compile_explorer_side x y = T`,
  simp[definition"backend_compile_explorer_side_def",PULL_FORALL] \\
  rpt gen_tac \\ ntac 3 strip_tac \\
  qmatch_goalsub_abbrev_tac`compile c.do_mti c.max_app [z]` \\
  `∃a. compile c.do_mti c.max_app [z] = [a]` by
    (Cases_on`c.do_mti`>>fs[clos_mtiTheory.compile_def]>>
    metis_tac[clos_mtiTheory.intro_multi_sing])>>
  specl_args_of_then ``renumber_code_locs_list``
    (clos_numberTheory.renumber_code_locs_length|>CONJUNCT1) assume_tac>>
  rfs[LENGTH_EQ_NUM_compute] \\
  strip_tac \\ fs[]) |> update_precondition;

*)

val def = spec64
  (backendTheory.attach_bitmaps_def
   |> Q.GENL[`bitmaps`,`bytes`,`c`]
   |> Q.ISPECL[`bitmaps:'a word list`,`bytes:word8 list`,`c:'a lab_to_target$config`])

val res = translate def

val def = spec64 backendTheory.compile_tap_def
  |> REWRITE_RULE[max_heap_limit_64_thm]

val res = translate def

val def = spec64 backendTheory.compile_def

val res = translate def

(* exportTheory *)
(* TODO: exportTheory functions that don't depend on the word size
   should probably be moved up to to_dataProg or something*)
val res = translate all_bytes_eq
val res = translate byte_to_string_eq

val export_byte_to_string_side_def = prove(
  ``!b. export_byte_to_string_side b``,
  fs [fetch "-" "export_byte_to_string_side_def"]
  \\ Cases \\ fs [] \\ EVAL_TAC \\ fs [])
  |> update_precondition;

val res = translate split16_def;
val res = translate preamble_def;

val res = translate space_line_def;

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

val res = translate (spec64 word_to_string_def);
(* -- *)

(* compilerTheory *)

val def = spec64 (PURE_REWRITE_RULE[fromSexpTheory.sexpdec_alt_intro1]compilerTheory.compile_def);

val _ = translate compilerTheory.locs_to_string_def;
val res = translate def

val res = translate basisProgTheory.basis_def

val res = translate (primTypesTheory.prim_tenv_def
                     |> CONV_RULE (RAND_CONV EVAL));

val res = translate inferTheory.init_config_def;

(* Compiler interface in compilerTheory
  TODO: some of these should be moved up, see comment above on exportScript
*)
val res = translate error_to_str_def;

val compiler_error_to_str_side_thm = prove(
  ``compiler_error_to_str_side x = T``,
  fs [fetch "-" "compiler_error_to_str_side_def"])
  |> update_precondition;

val res = translate parse_bool_def;
val res = translate parse_num_def;

val res = translate find_str_def;
val res = translate find_strs_def;
val res = translate find_bool_def;
val res = translate find_num_def;
val res = translate get_err_str_def;

val res = translate parse_num_list_def;
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

val res = translate (parse_top_config_def |> SIMP_RULE (srw_ss()) [default_heap_sz_def,default_stack_sz_def]);

(* Translations for each 64-bit target
  Note: ffi_asm is translated multiple times...
*)

(* x64 *)
val res = translate x64_configTheory.x64_names_def;
val res = translate export_x64Theory.ffi_asm_def;
val res = translate export_x64Theory.windows_ffi_asm_def;
val res = translate export_x64Theory.x64_export_def;
val res = translate
  (x64_configTheory.x64_backend_config_def
   |> SIMP_RULE(srw_ss())[FUNION_FUPDATE_1]);

(* riscv *)
val res = translate riscv_configTheory.riscv_names_def;
val res = translate export_riscvTheory.ffi_asm_def;
val res = translate export_riscvTheory.riscv_export_def;
val res = translate
  (riscv_configTheory.riscv_backend_config_def
   |> SIMP_RULE(srw_ss())[FUNION_FUPDATE_1]);

(* mips *)
val res = translate mips_configTheory.mips_names_def;
val res = translate export_mipsTheory.ffi_asm_def;
val res = translate export_mipsTheory.mips_export_def;
val res = translate
  (mips_configTheory.mips_backend_config_def
   |> SIMP_RULE(srw_ss())[FUNION_FUPDATE_1]);

(* arm8 *)
val res = translate arm8_configTheory.arm8_names_def;
val res = translate export_arm8Theory.ffi_asm_def;
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
        |> Q.GENL[`bytes`,`heap`,`stack`,`c`]
        |> Q.ISPECL[`bytes:word8 list`,`heap:num`,`stack:num`,`c:'a lab_to_target$config`]
        |> spec64
        |> translate;

val res = translate compile_64_def;

val res = translate (has_version_flag_def |> SIMP_RULE (srw_ss()) [MEMBER_INTRO])
val res = translate print_option_def
val res = translate current_build_info_str_def

val nonzero_exit_code_for_error_msg_def = Define `
  nonzero_exit_code_for_error_msg e =
    if compiler$is_error_msg e then
      ml_translator$force_out_of_memory_error () else ()`;

val res = translate compilerTheory.is_error_msg_def;
val res = translate nonzero_exit_code_for_error_msg_def;

val main = process_topdecs`
  fun main u =
    let
      val cl = CommandLine.arguments ()
    in
      if compiler_has_version_flag cl then
        print compiler_current_build_info_str
      else
        case compiler_compile_64 cl (String.explode (TextIO.inputAll TextIO.stdIn))  of
          (c, e) => (print_app_list c; TextIO.output TextIO.stdErr e;
                     compiler64prog_nonzero_exit_code_for_error_msg e)
    end`;

val res = append_prog main;

val st = get_ml_prog_state()

Theorem main_spec:
   app (p:'ffi ffi_proj) ^(fetch_v "main" st)
     [Conv NONE []] (STDIO fs * COMMANDLINE cl)
     (POSTv uv.
       &UNIT_TYPE () uv
       * STDIO (full_compile_64 (TL cl) (get_stdin fs) fs)
       * COMMANDLINE cl)
Proof
  xcf "main" st
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
  >- (
    simp[full_compile_64_def]
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
  \\ xlet_auto >- (xsimpl \\ fs[INSTREAM_stdin, STD_streams_get_mode])
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ fs [full_compile_64_def]
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
   whole_prog_spec ^(fetch_v "main" st) cl fs NONE
    ((=) (full_compile_64 (TL cl) (get_stdin fs) fs))
Proof
  simp[whole_prog_spec_def,UNCURRY]
  \\ qmatch_goalsub_abbrev_tac`fs1 = _ with numchars := _`
  \\ qexists_tac`fs1`
  \\ reverse conj_tac >-
    rw[Abbr`fs1`,full_compile_64_def,UNCURRY,
       GSYM fastForwardFD_with_numchars,
       GSYM add_stdo_with_numchars, with_same_numchars]
  \\ simp [SEP_CLAUSES]
  \\ match_mp_tac(MP_CANON(MATCH_MP app_wgframe main_spec))
  \\ xsimpl
QED

val (semantics_thm,prog_tm) = whole_prog_thm st "main" main_whole_prog_spec;

val compiler64_prog_def = Define`compiler64_prog = ^prog_tm`;

val semantics_compiler64_prog =
  semantics_thm
  |> PURE_ONCE_REWRITE_RULE[GSYM compiler64_prog_def]
  |> DISCH_ALL
  |> SIMP_RULE (srw_ss()) [AND_IMP_INTRO,GSYM CONJ_ASSOC]
  |> curry save_thm "semantics_compiler64_prog";

val () = Feedback.set_trace "TheoryPP.include_docs" 0;
val _ = export_theory();
