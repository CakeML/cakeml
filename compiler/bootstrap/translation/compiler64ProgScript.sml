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
  rw[definition"backend_compile_explorer_side_def"] \\
  cheat (* TODO: these are all here because to_dataProg does not save the precondition proofs for closLang passes *))
  |> update_precondition

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

val _ = translate (compile_to_bytes_def |> spec64)

val () = Feedback.set_trace "TheoryPP.include_docs" 0;

val _ = export_theory();
