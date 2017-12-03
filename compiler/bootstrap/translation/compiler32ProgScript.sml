open preamble
     arm6ProgTheory compilerTheory
     exportTheory
     ml_translatorLib ml_translatorTheory
open cfLib basis

val _ = new_theory"compiler32Prog";

val _ = translation_extends "arm6Prog";

val () = Globals.max_print_depth := 15;

val () = use_long_names := true;

val spec32 = INST_TYPE[alpha|->``:32``]

val max_heap_limit_32_def = Define`
  max_heap_limit_32 c =
    ^(spec32 data_to_wordTheory.max_heap_limit_def
      |> SPEC_ALL
      |> SIMP_RULE (srw_ss())[wordLangTheory.shift_def]
      |> concl |> rhs)`;

val res = translate max_heap_limit_32_def

val max_heap_limit_32_thm = Q.store_thm("max_heap_limit_32_thm",
  `max_heap_limit (:32) = max_heap_limit_32`,
  rw[FUN_EQ_THM] \\ EVAL_TAC);

val def = spec32 backendTheory.compile_explorer_def

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

val def = spec32
  (backendTheory.attach_bitmaps_def
   |> Q.GENL[`bitmaps`,`bytes`,`c`]
   |> Q.ISPECL[`bitmaps:'a word list`,`bytes:word8 list`,`c:'a lab_to_target$config`])

val res = translate def

val def = spec32 backendTheory.compile_def
  |> REWRITE_RULE[max_heap_limit_32_thm]

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

val res = translate (spec32 word_to_string_def);
(* -- *)

(* compilerTheory *)

val def = spec32 compilerTheory.compile_def

val _ = translate compilerTheory.locs_to_string_def;
val res = translate def

val res = translate basisProgTheory.basis_def

val res = translate inferTheory.init_config_def;

(* Compiler interface in compilerTheory
  TODO: some of these should be moved up, see comment above on exportScript
*)
val res = translate error_to_str_def;

val res = translate parse_num_def;

val res = translate find_str_def;
val res = translate find_bool_def;
val res = translate find_num_def;
val res = translate get_err_str_def;

val res = translate parse_num_list_def;
val res = translate comma_tokens_def;
val res = translate parse_nums_def;

val res = translate parse_clos_conf_def;
val res = translate parse_bvl_conf_def;
val res = translate parse_wtw_conf_def;
val res = translate parse_gc_def;
val res = translate parse_data_conf_def;
val res = translate parse_stack_conf_def;

val res = translate (parse_top_config_def |> SIMP_RULE (srw_ss()) [default_heap_sz_def,default_stack_sz_def]);

(* Translations for each 32-bit target
  Note: ffi_asm is translated multiple times...
*)

(* arm6 *)
val res = translate arm6_configTheory.arm6_names_def;
val res = translate export_arm6Theory.ffi_asm_def;
val res = translate export_arm6Theory.arm6_export_def;
val res = translate
  (arm6_configTheory.arm6_backend_config_def
   |> SIMP_RULE(srw_ss())[FUNION_FUPDATE_1]);

(* Rest of the translation *)
val res = translate (extend_conf_def |> spec32 |> SIMP_RULE (srw_ss()) [MEMBER_INTRO]);
val res = translate parse_target_32_def;

val res = format_compiler_result_def
        |> Q.GENL[`bytes`,`heap`,`stack`,`c`]
        |> Q.ISPECL[`bytes:word8 list`,`heap:num`,`stack:num`,`c:'a lab_to_target$config`]
        |> spec32
        |> translate;

val res = translate compile_32_def;

val res = translate (has_version_flag_def |> SIMP_RULE (srw_ss()) [MEMBER_INTRO])
val res = translate print_option_def
val res = translate current_build_info_str_def

val main = process_topdecs`
  fun main u =
    let
      val cl = CommandLine.arguments ()
    in
      if compiler_has_version_flag cl then
        print compiler_current_build_info_str
      else
        case compiler_compile_32 cl (String.explode (TextIO.inputAll TextIO.stdIn))  of
          (c, e) => (print_app_list c; TextIO.output TextIO.stdErr e)
    end`;

val res = append_prog main;

val st = get_ml_prog_state()

val full_compile_32_def = Define `
  full_compile_32 cl inp =
    if has_version_flag cl then
      (List [current_build_info_str], implode"", F)
    else
      let (a,b) = compile_32 cl inp in (a,b,T)`

val main_spec = Q.store_thm("main_spec",
  `app (p:'ffi ffi_proj) ^(fetch_v "main" st)
     [Conv NONE []] (STDIO fs * COMMANDLINE cl)
     (POSTv uv.
       &UNIT_TYPE () uv *
       (let (out,err,b) = full_compile_32 (TL (MAP implode cl)) (get_stdin fs) in
        let fs' = if b then fastForwardFD fs 0 else fs in
         STDIO (add_stderr (add_stdout fs' (explode (concat (append out)))) (explode err)))
      * COMMANDLINE cl)`,
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
  >-
   (pairarg_tac \\ fs []
    \\ rfs [full_compile_32_def] \\ rw []
    \\ xapp
    \\ CONV_TAC SWAP_EXISTS_CONV
    \\ qexists_tac `current_build_info_str`
    \\ fs [compilerTheory.current_build_info_str_def,
           fetch "-" "compiler_current_build_info_str_v_thm"]
    \\ xsimpl
    \\ rename1 `add_stdout _ string`
    \\ fs [concat_def, explode_thm]
    \\ `!str. ?pos. stderr (add_stdout fs str) pos` by
      metis_tac [stdo_def, STD_streams_def, STD_streams_add_stdout]
    \\ pop_assum (qspec_then `string` strip_assume_tac)
    \\ imp_res_tac add_stdo_nil \\ xsimpl
    \\ qexists_tac `COMMANDLINE cl` \\ xsimpl
    \\ qexists_tac `fs` \\ xsimpl)
  \\ xlet_auto >- (xsimpl \\ metis_tac[stdin_v_thm,stdIn_def])
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ fs [full_compile_32_def]
  \\ rpt (pairarg_tac \\ fs []) \\ rw []
  \\ fs[ml_translatorTheory.PAIR_TYPE_def]
  \\ xmatch
  (* TODO: xlet_auto: why does xlet_auto not work? *)
  \\ xlet_auto_spec(SOME (Q.SPEC`fastForwardFD fs 0`(Q.GEN`fs`basisProgTheory.print_app_list_spec)))
  >- xsimpl
  \\ xapp_spec output_stderr_spec
  \\ xsimpl
  \\ qmatch_goalsub_abbrev_tac`STDIO fs'`
  \\ CONV_TAC(RESORT_EXISTS_CONV List.rev)
  \\ qexists_tac`fs'` \\ xsimpl
  \\ instantiate
  \\ simp[Abbr`fs'`,mlstringTheory.concat_thm]
  \\ xsimpl);

val spec = main_spec |> UNDISCH_ALL |> SIMP_RULE (srw_ss())[STDIO_def,LET_THM,UNCURRY] |> add_basis_proj;
val name = "main"
val (semantics_thm,prog_tm) = call_thm st name spec;

val compiler32_prog_def = Define`compiler32_prog = ^prog_tm`;

val th =
  semantics_thm
  |> PURE_ONCE_REWRITE_RULE[GSYM compiler32_prog_def]

val semantics_compiler32_prog =
  th
  |> DISCH_ALL
  |> SIMP_RULE (srw_ss()) [STD_streams_add_stderr,STD_streams_add_stdout,STD_streams_fastForwardFD,
                           AND_IMP_INTRO,GSYM CONJ_ASSOC, full_compile_32_def]
  |> curry save_thm "semantics_compiler32_prog";

val () = Feedback.set_trace "TheoryPP.include_docs" 0;
val _ = export_theory();
