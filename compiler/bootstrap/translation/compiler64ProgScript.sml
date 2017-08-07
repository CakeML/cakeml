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

val def = spec64 backendTheory.compile_def
  |> REWRITE_RULE[max_heap_limit_64_thm]

val res = translate def

val def = spec64 compilerTheory.compile_def

val _ = translate compilerTheory.locs_to_string_def;
val res = translate def

val res = translate basisProgTheory.basis_def

val res = translate inferTheory.init_config_def;

(* Helper functions in exportTheory translated here since they should be common
   for all encoders *)
val res = translate all_bytes_eq
val res = translate byte_to_string_eq

val export_byte_to_string_side_def = prove(
  ``!b. export_byte_to_string_side b``,
  fs [fetch "-" "export_byte_to_string_side_def"]
  \\ Cases \\ fs [] \\ EVAL_TAC \\ fs [])
  |> update_precondition;

val res = translate byte_strlit_def;
val res = translate comm_strlit_def;
val res = translate newl_strlit_def;
val res = translate comma_cat_def;
val res = translate num_to_str_def;

val num_to_str_side_def = prove(
  ``!n. export_num_to_str_side n``,
  ho_match_mp_tac num_to_str_ind \\ rw []
  \\ once_rewrite_tac [fetch "-" "export_num_to_str_side_def"] \\ fs []
  \\ `n MOD 10 < 10` by fs [LESS_MOD] \\ decide_tac)
  |> update_precondition;

val res = translate bytes_row_def;
val res = translate split16_def;

(* Compiler interface in compilerTheory *)
val res = translate error_to_str_def;

val res = translate parse_num_def;

val res = translate find_parse_def;

val res = translate comma_tokens_def;

val res = translate parse_num_list_def;

val res = translate parse_nums_def;

val res = translate find_parse_nums_def;

val spec64 = INST_TYPE[alpha|->``:64``];

val _ = translate (extend_with_args_def |> spec64 |> SIMP_RULE (srw_ss()) [MEMBER_INTRO])

val _ = translate (parse_heap_stack_def |> SIMP_RULE (srw_ss()) [default_heap_sz_def,default_stack_sz_def])

val r = translate (format_compiler_result_def |> Q.GEN`bytes` |> Q.ISPEC`bytes:word8 list`)

val r = translate (compile_to_bytes_def |> spec64)

(*
(* sexp compiler translation -
   TODO: finish, and move parts of this to separate translation file?
   current problem: sexpPEG is not translatable because it uses too much ARB
*)

(* TODO: this is duplicated in parserProgTheory *)
val monad_unitbind_assert = Q.prove(
  `!b x. monad_unitbind (assert b) x = if b then x else NONE`,
  Cases THEN EVAL_TAC THEN SIMP_TAC std_ss []);
val OPTION_BIND_THM = Q.store_thm("OPTION_BIND_THM",
  `!x y. OPTION_BIND x y = case x of NONE => NONE | SOME i => y i`,
  Cases THEN SRW_TAC [] []);
(* -- *)

val r = translate simpleSexpPEGTheory.pnt_def
val r = translate pegTheory.ignoreR_def
val r = translate pegTheory.choicel_def
val r = translate simpleSexpPEGTheory.sexpPEG_def

val r =
  simpleSexpParseTheory.parse_sexp_def
  |> SIMP_RULE std_ss[monad_unitbind_assert,OPTION_BIND_THM,
                  pegexecTheory.pegparse_def,
                  simpleSexpPEGTheory.wfG_sexpPEG,UNCURRY,GSYM NULL_EQ]
  |> translate;

val r = translate (sexp_compile_to_bytes_def |> spec64)
*)

val () = Feedback.set_trace "TheoryPP.include_docs" 0;

val _ = export_theory();
