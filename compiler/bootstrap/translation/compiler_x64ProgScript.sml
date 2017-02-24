open preamble
     x64ProgTheory
     export_x64Theory
     configTheory
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
  (x64_compiler_config_def
   |> SIMP_RULE(srw_ss())[FUNION_FUPDATE_1])

val error_to_str_def = Define`
  (error_to_str ParseError = "### ERROR: parse error") /\
  (error_to_str TypeError = "### ERROR: type error") /\
  (error_to_str CompileError = "### ERROR: compile error")`;

val res = translate error_to_str_def;

val compile_to_bytes_def = Define `
  compile_to_bytes c input =
    case compiler$compile c basis input of
    | Failure err => error_to_str err
    | Success (bytes,ffis) => explode (x64_export ffis 400 100 bytes)`;

(* TODO: x64_compiler_config should be called x64_backend_config *)
val compiler_x64_def = Define`
  compiler_x64 = compile_to_bytes
    <| inferencer_config := init_config;
       backend_config := x64_compiler_config |>`;

val res = translate
  (compiler_x64_def
   |> SIMP_RULE (srw_ss()) [compile_to_bytes_def,FUN_EQ_THM,compilerTheory.compile_def]);

val main = process_topdecs`
  fun main u =
    let
      val cl = Commandline.arguments ()
    in
      write_list (compiler_x64 (read_all []))
    end`;

val res = ml_prog_update(ml_progLib.add_prog main I)
val st = get_ml_prog_state()

(* TODO: move *)
val MAP_K_REPLICATE = Q.store_thm("MAP_K_REPLICATE",
  `MAP (K x) ls = REPLICATE (LENGTH ls) x`,
  Induct_on`ls` \\ rw[REPLICATE]);
(* -- *)

val main_spec = Q.store_thm("main_spec",
  `cl ≠ [] ∧ EVERY validArg cl ∧ LENGTH (FLAT cl) + LENGTH cl ≤ 256 ⇒
   app (p:'ffi ffi_proj) ^(fetch_v "main" st)
     [Conv NONE []] (STDOUT out * (STDIN inp F * COMMANDLINE cl))
     (POSTv uv. &UNIT_TYPE () uv * (STDOUT (out ++ (compiler_x64 inp)) * (STDIN "" T * COMMANDLINE cl)))`,
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
  \\ xlet`POSTv cv. &LIST_TYPE CHAR inp cv * STDIN "" T * STDOUT out * COMMANDLINE cl`
  >- (xapp \\ instantiate \\ xsimpl
      \\ map_every qexists_tac[`STDOUT out * COMMANDLINE cl`,`F`,`inp`]
      \\ xsimpl )
  \\ qmatch_abbrev_tac`_ frame _`
  \\ xlet`POSTv xv. &LIST_TYPE CHAR (compiler_x64 inp) xv * frame`
  >- (xapp \\ instantiate \\ xsimpl)
  \\ xapp \\ instantiate
  \\ simp[Abbr`frame`]
  \\ map_every qexists_tac[`STDIN "" T * COMMANDLINE cl`,`out`]
  \\ xsimpl);

val spec = main_spec |> UNDISCH_ALL |> add_basis_proj;
val name = "main"
val (semantics_thm,prog_tm) = call_thm st name spec;

val entire_program_def = Define`entire_program = ^prog_tm`;

val semantics_entire_program =
  semantics_thm
  |> PURE_ONCE_REWRITE_RULE[GSYM entire_program_def]
  |> CONV_RULE(PATH_CONV"brrr"(SIMP_CONV std_ss [APPEND])) (* remove STRCAT "" *)
  (* TODO: change call_main_thm_basis to existentially quantify an io_list instead? *)
  |> CONV_RULE(RENAME_VARS_CONV["st"])
  |> DISCH_ALL |> GEN_ALL
  |> CONV_RULE(RENAME_VARS_CONV["inp","cls"])
  |> curry save_thm "semantics_entire_program";

val () = Feedback.set_trace "TheoryPP.include_docs" 0;

val () = export_theory();
