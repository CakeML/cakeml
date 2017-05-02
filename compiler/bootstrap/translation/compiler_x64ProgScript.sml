open preamble
     x64ProgTheory
     export_x64Theory
     x64_configTheory
     ml_translatorLib cfTacticsLib
     ioProgLib

val () = new_theory "compiler_x64Prog";

val () = translation_extends "x64Prog";

val res = translate inferTheory.init_config_def;

val res = translate x64_names_def;

val res = translate all_bytes_eq
val res = translate byte_to_string_eq

val byte_to_string_side_def = prove(
  ``!b. byte_to_string_side b``,
  fs [fetch "-" "byte_to_string_side_def"]
  \\ Cases \\ fs [] \\ EVAL_TAC \\ fs [])
  |> update_precondition;

val res = translate byte_strlit_def;
val res = translate comm_strlit_def;
val res = translate newl_strlit_def;
val res = translate comma_cat_def;
val res = translate num_to_str_def;

val num_to_str_side_def = prove(
  ``!n. num_to_str_side n``,
  ho_match_mp_tac num_to_str_ind \\ rw []
  \\ once_rewrite_tac [fetch "-" "num_to_str_side_def"] \\ fs []
  \\ `n MOD 10 < 10` by fs [LESS_MOD] \\ decide_tac)
  |> update_precondition;

val res = translate bytes_row_def;
val res = translate split16_def;
val res = translate ffi_asm_def;
val res = translate x64_export_def;

val res = translate
  (x64_backend_config_def
   |> SIMP_RULE(srw_ss())[FUNION_FUPDATE_1])

val error_to_str_def = Define`
  (error_to_str ParseError = strlit "### ERROR: parse error\n") /\
  (error_to_str (TypeError s) = concat [strlit "### ERROR: type error\n"; s; strlit "\n"]) /\
  (error_to_str CompileError = strlit "### ERROR: compile error\n")`;

val res = translate error_to_str_def;

(* TODO: translator fails inside mlstringLib.mlstring_case_conv
  when the following definition just matches against (strlit str) directly
*)
val parse_num_def = Define`
  parse_num str =
  let str = explode str in
  if EVERY isDigit str
  then
    SOME (num_from_dec_string_alt str)
  else NONE `

val res = translate parse_num_def;

val find_parse_def = Define`
  (find_parse flag [] = NONE) ∧
  (find_parse flag (x::xs) =
    if isPrefix flag x then
      parse_num (substring x (strlen flag) (strlen x))
    else find_parse flag xs)`

val res = translate find_parse_def;

val comma_tokens_def = Define `
  (comma_tokens acc xs [] = if NULL xs then acc else acc ++ [implode xs]) /\
  (comma_tokens acc (xs:string) (c::(cs:string)) =
    if c = #"," then
      comma_tokens (acc ++ if NULL xs then [] else [implode xs]) [] cs
    else
      comma_tokens acc (STRCAT xs [c]) cs)`

val res = translate comma_tokens_def;

val parse_num_list_def = Define`
  (parse_num_list [] = []) /\
  (parse_num_list (x::xs) =
     case parse_num x of
     | NONE => parse_num_list xs
     | SOME n => n :: parse_num_list xs)`

val res = translate parse_num_list_def;

val parse_nums_def = Define `
  parse_nums str =
    SOME (parse_num_list (comma_tokens [] [] (explode str)))`

val res = translate parse_nums_def;

val find_parse_nums_def = Define`
  (find_parse_nums flag [] = NONE) ∧
  (find_parse_nums flag (x::xs) =
    if isPrefix flag x then
      parse_nums (substring x (strlen flag) (strlen x))
    else find_parse_nums flag xs)`

val res = translate find_parse_nums_def;

(* parses a list of strings to configurations and modifies the configuration *)
val extend_with_args_def = Define`
  extend_with_args ls conf =
    let multi = ¬(MEMBER (strlit"--no_multi") ls) in
    let known = ¬(MEMBER (strlit"--no_known") ls) in
    let call = ¬(MEMBER (strlit"--no_call") ls) in
    let remove = ¬(MEMBER (strlit"--no_remove") ls) in
    let maxapp = find_parse (strlit "--max_app=") ls in
    let clos = conf.clos_conf in
    let updated_clos =
      clos with <|
        do_mti:= multi; do_known:= known;
        do_call:= call; do_remove:= remove;
        max_app:= (case maxapp of NONE => clos.max_app | SOME v => v)
      |> in
    let inlinesz = find_parse (strlit "--inline_size=") ls in
    let expcut = find_parse (strlit "--exp_cut=") ls in
    let splitmain = ¬(MEMBER (strlit"--no_split") ls) in
    let bvl = conf.bvl_conf in
    let updated_bvl =
      bvl with <|
        inline_size_limit:= case inlinesz of NONE => bvl.inline_size_limit | SOME v => v;
        exp_cut:= case expcut of NONE => bvl.exp_cut | SOME v => v;
        split_main_at_seq := splitmain
      |> in
    let gc_none = (MEMBER (strlit"--gc=none") ls) in
    let gc_simple = (MEMBER (strlit"--gc=simple") ls) in
    let gc_gen = (MEMBER (strlit"--gc=gen") ls) in
    let gc_gen_sizes = find_parse_nums (strlit "--gc=gen") ls in
    let data = conf.data_conf in
    let updated_data =
	data with <| gc_kind :=
		  case gc_gen_sizes of
		  | SOME gs => Generational gs
		  | NONE =>
   		      if gc_none then None else
		      if gc_simple then Simple else
		      if gc_gen then Generational [] else data.gc_kind |> in
    let regalg = find_parse (strlit "--reg_alg=") ls in
    let wtw = conf.word_to_word_conf in
    let updated_wtw =
      wtw with <|reg_alg:= case regalg of NONE => wtw.reg_alg | SOME v =>v |> in
    conf with <|clos_conf := updated_clos; bvl_conf:=updated_bvl; word_to_word_conf := updated_wtw|>`

val spec64 = INST_TYPE[alpha|->``:64``];

val _ = translate (extend_with_args_def |> spec64 )

val compile_to_bytes_def = Define `
  compile_to_bytes c input =
    case compiler$compile c basis input of
    | Failure err => (List[], error_to_str err)
    | Success (bytes,ffis) => (x64_export ffis 400 100 bytes, implode "")`;

val compiler_x64_def = Define`
  compiler_x64 cl = compile_to_bytes
    <| inferencer_config := init_config;
       backend_config := extend_with_args cl x64_backend_config |>`;

val res = translate
  (compiler_x64_def
   |> SIMP_RULE (srw_ss()) [compile_to_bytes_def,FUN_EQ_THM,compilerTheory.compile_def]);

val main = process_topdecs`
  fun main u =
    let
      val cl = Commandline.arguments ()
    in
      case compiler_x64 cl (read_all [])  of
        (c, e) => (print_app_list c; print_err e)
    end`;

val res = ml_prog_update(ml_progLib.add_prog main I)
val st = get_ml_prog_state()

val main_spec = Q.store_thm("main_spec",
  `cl ≠ [] ∧ EVERY validArg cl ∧ LENGTH (FLAT cl) + LENGTH cl ≤ 256 ⇒
   app (p:'ffi ffi_proj) ^(fetch_v "main" st)
     [Conv NONE []] (STDOUT out * STDERR err * (STDIN inp F * COMMANDLINE cl))
     (POSTv uv. &UNIT_TYPE () uv *
      STDOUT (out ++ (FLAT (MAP explode (append (FST(compiler_x64 (TL(MAP implode cl)) inp)))))) *
      STDERR (err ++ explode (SND(compiler_x64 (TL(MAP implode cl)) inp))) *
       (STDIN "" T * COMMANDLINE cl))`,
  strip_tac
  \\ xcf "main" st
  \\ qmatch_abbrev_tac`_ frame _`
  \\ xlet`POSTv uv. &UNIT_TYPE () uv * frame`
  >- (xcon \\ xsimpl)
  \\ xlet`POSTv av. &LIST_TYPE STRING_TYPE (TL (MAP implode cl)) av * frame`
  >- (xapp \\ instantiate \\ simp[Abbr`frame`] \\ xsimpl
      \\ simp[LENGTH_FLAT,MAP_MAP_o,o_DEF]
      \\ Q.ISPECL_THEN[`STRLEN`]mp_tac SUM_MAP_PLUS
      \\ disch_then(qspecl_then[`K 1`,`cl`]mp_tac)
      \\ simp[GSYM LENGTH_FLAT,MAP_K_REPLICATE,SUM_REPLICATE])
  \\ xlet`POSTv nv. &LIST_TYPE CHAR [] nv * frame`
  >- (xcon \\ xsimpl \\ EVAL_TAC)
  \\ qunabbrev_tac`frame`
  \\ xlet`POSTv cv. &LIST_TYPE CHAR inp cv * STDIN "" T * STDOUT out * STDERR err * COMMANDLINE cl`
  >- ( xapp \\ instantiate \\ xsimpl
      \\ map_every qexists_tac[`STDOUT out * STDERR err * COMMANDLINE cl`,`F`,`inp`]
      \\ xsimpl)
  \\ qmatch_abbrev_tac`_ frame _`
  \\ qmatch_goalsub_abbrev_tac`append (FST res)`
  \\ xlet`POSTv xv. &PAIR_TYPE (MISC_APP_LIST_TYPE STRING_TYPE) STRING_TYPE res xv * frame`
  >- (xapp \\ instantiate \\ xsimpl \\ cheat)
  \\ xmatch
  \\ Cases_on `res` \\ qmatch_goalsub_abbrev_tac`FST (c,e)`
  \\ every_case_tac \\ fs [ml_translatorTheory.PAIR_TYPE_def]
  \\ rw[validate_pat_def,pat_typechecks_def,pat_without_Pref_def,
     ALL_DISTINCT,astTheory.pat_bindings_def,terminationTheory.pmatch_def]
  \\ qunabbrev_tac`frame`
  \\ qmatch_goalsub_abbrev_tac`STDOUT (out ++ output)`
  \\ xlet `POSTv xv. &UNIT_TYPE () xv * STDOUT (out ++ output) *
           STDERR err * (STDIN "" T * COMMANDLINE cl)`
  \\ xapp \\ instantiate
  >- (CONV_TAC(SWAP_EXISTS_CONV) \\ qexists_tac`out` \\ xsimpl)
  \\ CONV_TAC(SWAP_EXISTS_CONV) \\ qexists_tac`err` \\ xsimpl
  );

val spec = main_spec |> UNDISCH_ALL |> add_basis_proj;
val name = "main"
val (semantics_thm,prog_tm) = call_thm st name spec;

val entire_program_def = Define`entire_program = ^prog_tm`;

val semantics_entire_program =
  semantics_thm
  |> PURE_ONCE_REWRITE_RULE[GSYM entire_program_def]
  |> CONV_RULE(PATH_CONV"b"(SIMP_CONV std_ss [APPEND])) (* remove STRCAT "" *)
  |> CONV_RULE(RENAME_VARS_CONV["io_events"])
  |> DISCH_ALL |> GEN_ALL
  |> CONV_RULE(RENAME_VARS_CONV["inp","cls"])
  |> curry save_thm "semantics_entire_program";

val () = Feedback.set_trace "TheoryPP.include_docs" 0;

val () = export_theory();
