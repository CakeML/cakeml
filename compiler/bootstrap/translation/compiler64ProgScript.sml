(*
  Finish translation of the 64-bit version of the compiler.
*)
open preamble
     mipsProgTheory compilerTheory
     exportTheory
     ml_translatorLib ml_translatorTheory
open cfLib basis

val _ = temp_delsimps ["NORMEQ_CONV", "lift_disj_eq", "lift_imp_disj"]

val _ = new_theory"compiler64Prog";

val _ = translation_extends "mipsProg";

val _ = ml_translatorLib.ml_prog_update (ml_progLib.open_module "compiler64Prog");
val _ = ml_translatorLib.use_string_type true;
val _ = ml_translatorLib.use_sub_check true;

val _ = (ml_translatorLib.trace_timing_to
         := SOME "compiler64Prog_translate_timing.txt")

val () = Globals.max_print_depth := 15;

val () = use_long_names := true;

val spec64 = INST_TYPE[alpha|->``:64``]

val res = translate $ spec64 panStaticTheory.based_merge_def;
val res = translate $ spec64 panStaticTheory.based_cmp_def;
val res = translate $ spec64 panStaticTheory.seq_vbases_def;
val res = translate $ spec64 panStaticTheory.branch_vbases_def;
val res = translate $ spec64 panStaticTheory.last_to_str_def;
val res = translate $ spec64 panStaticTheory.last_is_exit_def;
val res = translate $ spec64 panStaticTheory.next_is_reachable_def;
val res = translate $ spec64 panStaticTheory.next_now_unreachable_def;
val res = translate $ spec64 panStaticTheory.reached_warnable_def;
val res = translate $ spec64 panStaticTheory.seq_last_stmt_def;
val res = translate $ spec64 panStaticTheory.branch_last_stmt_def;
val res = translate $ spec64 panStaticTheory.first_repeat_def;
val res = translate $ spec64 panStaticTheory.binop_to_str_def;
val res = translate $ spec64 panStaticTheory.panop_to_str_def;

val res = translate $ spec64 $ panStaticTheory.static_check_exp_def;
val res = translate $ spec64 $ panStaticTheory.static_check_prog_def;
val res = translate $
  INST_TYPE[beta|->``:64``] panStaticTheory.static_check_funs_def;
val res = translate $ INST_TYPE[beta|->``:64``] panStaticTheory.static_check_def;

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
  rw[FUN_EQ_THM] \\ EVAL_TAC
QED

val r = translate presLangTheory.default_tap_config_def;

val def = spec64
          (backendTheory.attach_bitmaps_def
             |> Q.GENL[`c'`,`bytes`,`c`]
             |> Q.ISPECL[`lab_conf:'a lab_to_target$config`,`bytes:word8 list`,`c:'a backend$config`])

val res = translate def

val def = spec64 backendTheory.compile_def
  |> REWRITE_RULE[max_heap_limit_64_thm]

val res = translate def

val _ = register_type “:64 any_prog”

val r = backend_passesTheory.to_flat_all_def |> spec64 |> translate;
val r = backend_passesTheory.to_clos_all_def |> spec64 |> translate;
val r = backend_passesTheory.to_bvl_all_def |> spec64 |> translate;
val r = backend_passesTheory.to_bvi_all_def |> spec64 |> translate;

Triviality backend_passes_to_bvi_all_side:
  backend_passes_to_bvi_all_side c p
Proof
  fs [fetch "-" "backend_passes_to_bvi_all_side_def"]
  \\ rewrite_tac [GSYM LENGTH_NIL,bvl_inlineTheory.LENGTH_remove_ticks]
  \\ fs []
QED

val _ = update_precondition backend_passes_to_bvi_all_side

val r = backend_passesTheory.to_data_all_def |> spec64 |> translate;

val r = backend_passesTheory.word_internal_def |> spec64 |> translate;

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
val r = pan_passesTheory.shape_to_str_def |> translate;
val r = pan_passesTheory.insert_es_def |> translate;
Triviality lem:
  dimindex(:64) = 64
Proof
  EVAL_TAC
QED
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
            |> Q.ISPECL[`bytes:word8 list`,`c:'a backend$config`]
            |> spec64
            |> translate;

val res = translate backendTheory.ffinames_to_string_list_def;

val res = translate compile_64_def;

val res = translate $ spec64 compile_pancake_def;

val res = translate compile_pancake_64_def;

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

(* incremental compiler *)

Definition compiler_for_eval_def:
  compiler_for_eval = compile_inc_progs_for_eval x64_config
End

Triviality upper_w2w_eq_I:
  backend$upper_w2w = (I:word64 -> word64)
Proof
  fs [backendTheory.upper_w2w_def,FUN_EQ_THM]
QED

val compiler_for_eval_alt =
“compiler_for_eval (id,c,decs)”
  |> SIMP_CONV std_ss [backendTheory.compile_inc_progs_for_eval_eq,
                       compiler_for_eval_def, EVAL “x64_config.reg_count”,
                       backendTheory.ensure_fp_conf_ok_def,
                       EVAL “LENGTH x64_config.avoid_regs”,
                       EVAL “x64_config.fp_reg_count”,
                       EVAL “x64_config.two_reg_arith”,listTheory.MAP_ID,
                       EVAL “x64_config.addr_offset”,upper_w2w_eq_I,
                       EVAL “x64_config.ISA”, EVAL “x86_64 = ARMv7”]

val r = translate (lab_to_targetTheory.to_shmem_info_def |> spec64);
val r = translate (lab_to_targetTheory.inc_config_to_config_def |> spec64);
val r = translate (lab_to_targetTheory.to_inc_shmem_info_def |> spec64);
val r = translate (lab_to_targetTheory.config_to_inc_config_def |> spec64);
val r = translate (backendTheory.inc_config_to_config_def |> spec64);
val r = translate (backendTheory.config_to_inc_config_def |> spec64);
val r = translate (word_to_wordTheory.compile_single_def |> spec64);
val r = translate (word_to_wordTheory.full_compile_single_def |> spec64);
val r = translate (word_to_wordTheory.full_compile_single_for_eval_def |> spec64);
val _ = (next_ml_names := ["compiler_for_eval"]);
val r = translate compiler_for_eval_alt;

(* fun eval_prim env s1 decs s2 bs ws = Eval [env,s1,decs,s2,bs,ws] *)
val _ = append_prog
        “[Dlet (Locs (POSN 1 2) (POSN 2 21)) (Pvar "eval_prim")
          (Fun "x" (Mat (Var (Short "x"))
                    [(Pcon NONE [Pvar "env"; Pvar "s1"; Pvar "decs";
                                 Pvar "s2"; Pvar "bs"; Pvar "ws"],
                      App Eval [Var (Short "env"); Var (Short "s1"); Var (Short "decs");
                                Var (Short "s2"); Var (Short "bs"); Var (Short "ws")])]))]”;

Datatype:
  eval_res = Compile_error 'a | Eval_result 'b 'c | Eval_exn 'd 'e
End

val _ = register_type “:('a,'b,'c,'d,'e) eval_res”;

val _ = (append_prog o process_topdecs) `
fun eval ((s1,next_gen), (env,id), decs) =
case compiler_for_eval ((id,0),(s1,decs)) of
  None => Compile_error "ERROR: failed to compile input\n"
| Some (s2,(bs,ws)) =>
    let
val new_env = eval_prim (env,s1,decs,s2,bs,ws)
    in Eval_result (new_env,next_gen) (s2,next_gen+1) end
                   handle e => Eval_exn e (s2,next_gen+1) `

val exn_msg_dec = process_topdecs ‘
val _ = (TextIO.print (!Repl.errorMessage);
         print_pp (pp_exn (!Repl.exn));
         print "\n")’

Definition report_exn_dec_def:
  report_exn_dec = ^exn_msg_dec
End

val _ = (next_ml_names := ["report_exn_dec"]);
val r = translate report_exn_dec_def;

val _ = (append_prog o process_topdecs) `
fun report_exn e =
(Repl.exn := e;
 Repl.errorMessage := "EXCEPTION: ";
 report_exn_dec)`

val error_msg_dec = process_topdecs ‘
val _ = (TextIO.print (!Repl.errorMessage))’

Definition report_error_dec_def:
  report_error_dec = ^error_msg_dec
End

val _ = (next_ml_names := ["report_error_dec"]);
val r = translate report_error_dec_def;

val _ = (append_prog o process_topdecs) `
fun report_error msg =
(Repl.errorMessage := msg;
 report_error_dec)`

val _ = (next_ml_names := ["roll_back"]);
val r = translate repl_check_and_tweakTheory.roll_back_def;

val _ = (next_ml_names := ["check_and_tweak"]);
val r = translate repl_check_and_tweakTheory.check_and_tweak_def;

val _ = (append_prog o process_topdecs) `
fun repl (parse, types, conf, env, decs, input_str) =
(* input_str is passed in here only for error reporting purposes *)
case check_and_tweak (decs, (types, input_str)) of
  Inl msg => repl (parse, types, conf, env, report_error msg, "")
| Inr (safe_decs, new_types) =>
    (* here safe_decs are guaranteed to not crash;
         the last declaration of safe_decs calls !Repl.readNextString *)
    case eval (conf, env, safe_decs) of
      Compile_error msg => repl (parse, types, conf, env, report_error msg, "")
    | Eval_exn e new_conf =>
        repl (parse, roll_back (types, new_types), new_conf, env, report_exn e, "")
    | Eval_result new_env new_conf =>
        (* check whether the program that ran has loaded in new input *)
        if !Repl.isEOF then () (* exit if there is no new input *) else
          let val new_input = !Repl.nextString in
            (* if there is new input: parse the input and recurse *)
            case parse new_input of
              Inl msg      => repl (parse, new_types, new_conf, new_env, report_error msg, "")
            | Inr new_decs => repl (parse, new_types, new_conf, new_env, new_decs, new_input)
                                   end `

val _ = (next_ml_names := ["init_types"]);
val r = translate repl_init_typesTheory.repl_init_types_eq;

Definition parse_cakeml_syntax_def:
  parse_cakeml_syntax input =
  case parse_prog (lexer_fun (explode input)) of
  | Success _ x _ => INR x
  | Failure l _ => INL (strlit "Parsing failed at " ^ locs_to_string input (SOME l))
End

Definition parse_ocaml_syntax_def:
  parse_ocaml_syntax input =
  case caml_parser$run (explode input) of
  | INR res => INR res
  | INL (l,err) => INL
                   (err ^ «\nParsing failed at » ^ locs_to_string input (SOME l))
End

Definition select_parse_def:
  select_parse cl =
  if MEMBER (strlit "--candle") cl
  then parse_ocaml_syntax
  else parse_cakeml_syntax
End

val r = translate parse_cakeml_syntax_def;
val r = translate parse_ocaml_syntax_def;
val _ = (next_ml_names := ["select_parse"]);
val r = translate select_parse_def;

Definition init_next_string_def:
  init_next_string cl = if MEM (strlit "--candle") cl then "candle" else ""
End

val _ = (next_ml_names := ["init_next_string"]);
val res = translate (init_next_string_def |> REWRITE_RULE [MEMBER_INTRO]);

val _ = (append_prog o process_topdecs) `
fun start_repl (cl,s1) =
let
val parse = select_parse cl
val types = init_types
val conf = (s1,1)
val env = (repl_init_env, 0)
val decs = []
val input_str = ""
val _ = (Repl.nextString := init_next_string cl)
in
  repl (parse, types, conf, env, decs, input_str)
       end`

val _ = (append_prog o process_topdecs) `
fun run_interactive_repl cl =
let
val cs = Repl.charsFrom "config_enc_str.txt"
val s1 = decodeProg.decode_backend_config cs
in
  start_repl (cl,s1)
             end`

Definition has_repl_flag_def:
  has_repl_flag cl ⇔ MEM (strlit "--repl") cl ∨ MEM (strlit "--candle") cl
End

val _ = (next_ml_names := ["compiler_has_repl_flag"]);
val res = translate (has_repl_flag_def |> REWRITE_RULE [MEMBER_INTRO]);

val res = translate (has_pancake_flag_def |> SIMP_RULE (srw_ss()) [MEMBER_INTRO])

val main = process_topdecs`
fun main u =
let
val cl = CommandLine.arguments ()
in
  if compiler_has_repl_flag cl then
    run_interactive_repl cl
  else if compiler_has_help_flag cl then
    print compiler_help_string
  else if compiler_has_version_flag cl then
    print compiler_current_build_info_str
  else if compiler_has_pancake_flag cl then
    case compiler_compile_pancake_64 cl (TextIO.inputAll TextIO.stdIn)  of
      (c, e) => (print_app_list c; TextIO.output TextIO.stdErr e;
                 compiler64prog_nonzero_exit_code_for_error_msg e)
  else
    case compiler_compile_64 cl (TextIO.inputAll TextIO.stdIn)  of
      (c, e) => (print_app_list c; TextIO.output TextIO.stdErr e;
                 compiler64prog_nonzero_exit_code_for_error_msg e)
                end`;

val res = append_prog main;

val main_v_def = fetch "-" "main_v_def";

Theorem main_spec:
  ¬has_repl_flag (TL cl) ⇒
  app (p:'ffi ffi_proj) main_v
      [Conv NONE []] (STDIO fs * COMMANDLINE cl)
      (POSTv uv.
       &UNIT_TYPE () uv
       * STDIO (full_compile_64 (TL cl) (get_stdin fs) fs)
       * COMMANDLINE cl)
Proof
  rpt strip_tac
  \\ xcf_with_def main_v_def
  \\ xlet_auto >- (xcon \\ xsimpl)
  \\ xlet_auto >- xsimpl
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
  \\ first_x_assum $ irule_at $ Pos hd \\ simp []
  \\ xlet_auto >- xsimpl
  \\ xif
  >-
   (simp[full_compile_64_def]
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
  >> xlet_auto>-xsimpl
  >> xif
  >- (
  xlet_auto >- (xsimpl \\ fs[INSTREAM_stdin, STD_streams_get_mode])
  \\ fs [GSYM HOL_STRING_TYPE_def]
  \\ xlet_auto >- xsimpl
  \\ fs [full_compile_64_def]
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
  \\ fs [full_compile_64_def]
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
  \\ asm_exists_tac \\ simp [] \\ xsimpl
QED

Theorem main_whole_prog_spec:
  ¬has_repl_flag (TL cl) ⇒
  whole_prog_spec main_v cl fs NONE
                  ((=) (full_compile_64 (TL cl) (get_stdin fs) fs))
Proof
  strip_tac
  \\ simp[whole_prog_spec_def,UNCURRY]
  \\ qmatch_goalsub_abbrev_tac`fs1 = _ with numchars := _`
  \\ qexists_tac`fs1`
  \\ reverse conj_tac >-
   rw[Abbr`fs1`,full_compile_64_def,UNCURRY,
      GSYM fastForwardFD_with_numchars,
      GSYM add_stdo_with_numchars, with_same_numchars]
  \\ simp [SEP_CLAUSES]
  \\ match_mp_tac (MP_CANON(MATCH_MP app_wgframe (UNDISCH main_spec)))
  \\ xsimpl
QED

val (semantics_thm,prog_tm) =
whole_prog_thm (get_ml_prog_state()) "main" (main_whole_prog_spec |> UNDISCH);

Definition compiler64_prog_def:
  compiler64_prog = ^prog_tm
End

Theorem semantics_compiler64_prog =
  semantics_thm
    |> PURE_ONCE_REWRITE_RULE[GSYM compiler64_prog_def]
    |> DISCH_ALL
    |> SIMP_RULE (srw_ss()) [AND_IMP_INTRO,GSYM CONJ_ASSOC]

(* saving a tidied up final theorem *)

val th =
get_ml_prog_state ()
  (* |> ml_progLib.clean_state *)
  |> ml_progLib.remove_snocs
  |> ml_progLib.get_thm
  |> REWRITE_RULE [ml_progTheory.ML_code_def]

                  Triviality BUTLAST_compiler64_prog:
                    ^(mk_eq(concl th |> rator |> rator |> rand,“BUTLAST compiler64_prog”))
Proof
  CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [compiler64_prog_def]))
  \\ CONV_TAC (RAND_CONV (PURE_REWRITE_CONV [listTheory.FRONT_CONS]))
  \\ EVAL_TAC
QED

val th1 = th
            |> CONV_RULE (PATH_CONV "llr" (REWR_CONV BUTLAST_compiler64_prog))
            |> CONV_RULE (RAND_CONV (EVAL THENC REWRITE_CONV
                                     (DB.find "_refs_def" |> map (#1 o #2)) THENC
                                     SIMP_CONV std_ss [APPEND_NIL,APPEND]))

Theorem Decls_FRONT_compiler64_prog = th1

Theorem LAST_compiler64_prog = EVAL “LAST compiler64_prog”;

val () = Feedback.set_trace "TheoryPP.include_docs" 0;
val _ = ml_translatorLib.reset_translation(); (* because this translation won't be continued *)
val _ = export_theory();
