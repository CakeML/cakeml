open preamble
     x64ProgTheory
     compiler_x64Theory
     x64_configTheory
     export_x64Theory
     ml_translatorLib cfTacticsLib
     ioProgLib

val () = new_theory "sexp_compiler_x64Prog";

val () = translation_extends "x64Prog";

val res = translate x64_names_def;

val res = translate ffi_asm_def;
val res = translate x64_export_def;

val res = translate
  (x64_backend_config_def
   |> SIMP_RULE(srw_ss())[FUNION_FUPDATE_1])

val res = translate sexp_compiler_x64_def

val main = process_topdecs`
  fun main u =
    let
      val cl = Commandline.arguments ()
    in
      case sexp_compiler_x64 cl (read_all [])  of
        (c, e) => (print_app_list c; print_err e)
    end`;

val res = ml_prog_update(ml_progLib.add_prog main I)
val st = get_ml_prog_state()

val main_spec = Q.store_thm("main_spec",
  `app (p:'ffi ffi_proj) ^(fetch_v "main" st)
     [Conv NONE []] (STDOUT out * STDERR err * (STDIN inp F * COMMANDLINE cl))
     (POSTv uv. &UNIT_TYPE () uv *
      STDOUT (out ++ (FLAT (MAP explode (append (FST(sexp_compiler_x64 (TL(MAP implode cl)) inp)))))) *
      STDERR (err ++ explode (SND(sexp_compiler_x64 (TL(MAP implode cl)) inp))) *
       (STDIN "" T * COMMANDLINE cl))`,
  xcf "main" st
  \\ qmatch_abbrev_tac`_ frame _`
  \\ xlet`POSTv uv. &UNIT_TYPE () uv * frame`
  >- (xcon \\ xsimpl)
  \\ xlet`POSTv av. &LIST_TYPE STRING_TYPE (TL (MAP implode cl)) av * frame`
  >- (xapp \\ xsimpl \\ CONV_TAC SWAP_EXISTS_CONV \\ qexists_tac`cl` \\
      unabbrev_all_tac \\ xsimpl)
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
  >- (xapp \\ instantiate \\ xsimpl)
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
  |> CONV_RULE(RENAME_VARS_CONV["inp","files","cls"])
  |> curry save_thm "semantics_entire_program";

val () = Feedback.set_trace "TheoryPP.include_docs" 0;

val () = export_theory();
