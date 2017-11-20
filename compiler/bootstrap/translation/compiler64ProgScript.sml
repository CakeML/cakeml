open preamble
     to_target64ProgTheory compilerTheory
     exportTheory
     ml_translatorLib ml_translatorTheory

val _ = new_theory"compiler64Prog";

val _ = translation_extends "to_target64Prog";

val () = Globals.max_print_depth := 15;

val () = use_long_names := true;

val spec64 = INST_TYPE[alpha|->``:64``]

val max_heap_limit_64_def = Define`
  max_heap_limit_64 c =
    ^(spec64 data_to_wordTheory.max_heap_limit_def
      |> SPEC_ALL
      |> SIMP_RULE (srw_ss())[wordLangTheory.shift_def]
      |> concl |> rhs)`;

val res = translate max_heap_limit_64_def

val max_heap_limit_64_thm = Q.store_thm("max_heap_limit_64_thm",
  `max_heap_limit (:64) = max_heap_limit_64`,
  rw[FUN_EQ_THM] \\ EVAL_TAC);

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

val def = spec64
  (backendTheory.attach_bitmaps_def
   |> Q.GENL[`bitmaps`,`bytes`,`c`]
   |> Q.ISPECL[`bitmaps:'a word list`,`bytes:word8 list`,`c:'a lab_to_target$config`])

val res = translate def

val def = spec64 backendTheory.compile_def
  |> REWRITE_RULE[max_heap_limit_64_thm]

val res = translate def

val def = spec64 compilerTheory.compile_def

val _ = translate compilerTheory.locs_to_string_def;
val res = translate def

val res = translate basisProgTheory.basis_def

val res = translate inferTheory.init_config_def;

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
(* -- *)

val res = translate (spec64 word_to_string_def);

(* Compiler interface in compilerTheory *)
val res = translate error_to_str_def;

val res = translate parse_num_def;

val res = translate find_parse_def;

val res = translate comma_tokens_def;

val res = translate parse_num_list_def;

val res = translate parse_nums_def;

val res = translate find_parse_nums_def;

val r = translate (extend_with_args_def |> spec64 |> SIMP_RULE (srw_ss()) [MEMBER_INTRO])

val r = translate (parse_heap_stack_def |> SIMP_RULE (srw_ss()) [default_heap_sz_def,default_stack_sz_def])

val r = format_compiler_result_def
        |> Q.GENL[`bytes`,`heap`,`stack`,`c`]
        |> Q.ISPECL[`bytes:word8 list`,`heap:num`,`stack:num`,`c:'a lab_to_target$config`]
        |> spec64
        |> translate;

(* --- These are used in compiler_xxxProgTheory --- *)
val r = translate (has_version_flag_def |> SIMP_RULE (srw_ss()) [MEMBER_INTRO])
val r = translate print_option_def
val r = translate current_build_info_str_def
(* ------------------------------------------------ *)

val r = translate (compile_to_bytes_def |> spec64 |> SIMP_RULE (srw_ss()) [MEMBER_INTRO])

val () = Feedback.set_trace "TheoryPP.include_docs" 0;

val _ = export_theory();
