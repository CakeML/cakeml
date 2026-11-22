(*
  Shared host selection, REPL and entry points for the native compiler programs.
*)
Theory compiler_mainProg[no_sig_docs]
Ancestors
  compiler_commonProg compiler compiler_common export ml_translator
  basis_ffi[qualified]
Libs
  preamble ml_translatorLib cfLib basis

Datatype:
  compiler_host = HostX64 | HostArm8
End

Definition host_config_def:
  host_config HostX64 = x64_config ∧
  host_config HostArm8 = arm8_config
End

Definition host_args_def:
  host_args host cl =
    if host = HostArm8 ∧ find_str «--target=» cl = NONE then
      «--target=arm8» :: cl
    else cl
End

Theorem host_args_x64[simp]:
  host_args HostX64 cl = cl
Proof
  simp [host_args_def]
QED

Theorem host_args_explicit:
  find_str «--target=» cl = SOME target_name ⇒ host_args host cl = cl
Proof
  simp [host_args_def]
QED

Theorem host_args_arm8_default:
  find_str «--target=» cl = NONE ⇒
  parse_target (host_args HostArm8 cl) =
    INL (arm8_backend_config,arm8_export,arm8_config)
Proof
  simp [host_args_def, compiler_commonTheory.parse_target_def,
        compiler_commonTheory.find_str_def]
  >> simp [EVAL “isPrefix «--target=» «--target=arm8»”,
           EVAL “extract «--target=arm8» 9 NONE”]
QED

val _ = temp_delsimps ["NORMEQ_CONV", "lift_disj_eq", "lift_imp_disj"];
val _ = translation_extends "compiler_commonProg";
val _ = ml_translatorLib.use_sub_check true;
val _ = use_long_names := true;

val _ = register_type ``:compiler_host``;
val _ = next_ml_names := ["host_args"];
val r = translate host_args_def;

Definition compiler_for_eval_def:
  compiler_for_eval host = compile_inc_progs_for_eval (host_config host)
End

Definition bitmap_to_word64_def:
  bitmap_to_word64 (n:num) = (n2w n :word64)
End

val r = translate bitmap_to_word64_def;

Theorem upper_n2w_Arch64[local]:
  upper_n2w Arch64 = bitmap_to_word64
Proof
  simp [FUN_EQ_THM, backend_commonTheory.upper_n2w_def,
        bitmap_to_word64_def]
QED

val compiler_for_eval_alt =
  [``HostX64``, ``HostArm8``]
  |> map (fn host =>
       ``compiler_for_eval ^host (id,c,ds)``
       |> SIMP_CONV std_ss
            [compiler_for_eval_def, host_config_def,
             backendTheory.compile_inc_progs_for_eval_eq,
             backendTheory.ensure_fp_conf_ok_def,
             EVAL ``x64_config.reg_count``, EVAL ``arm8_config.reg_count``,
             EVAL ``LENGTH x64_config.avoid_regs``,
             EVAL ``LENGTH arm8_config.avoid_regs``,
             EVAL ``x64_config.fp_reg_count``, EVAL ``arm8_config.fp_reg_count``,
             EVAL ``x64_config.two_reg_arith``, EVAL ``arm8_config.two_reg_arith``,
             EVAL ``x64_config.addr_offset``, EVAL ``arm8_config.addr_offset``,
             EVAL ``x64_config.ISA``, EVAL ``arm8_config.ISA``,
             EVAL ``x86_64 = ARMv7``, EVAL ``ARMv8 = ARMv7``,
             asmTheory.arch_wordsize_def, upper_n2w_Arch64,
             listTheory.MAP_ID])
  |> LIST_CONJ;

val r = translate word_to_wordTheory.full_compile_single_for_eval_def;

Theorem ws_to_chars_eq[local]:
  ws_to_chars [] = [] /\
  ws_to_chars (w::ws) = CHR (w2n w) :: ws_to_chars ws
Proof
  fs [semanticPrimitivesTheory.ws_to_chars_def]
QED

val r = translate ws_to_chars_eq;

Theorem semanticprimitives_ws_to_chars_side[local]:
  !ws. semanticprimitives_ws_to_chars_side ws
Proof
  `!w:word8. w2n w < 256` by (
    strip_tac
    >> assume_tac (w2n_lt |> INST_TYPE [alpha |-> ``:8``])
    >> `dimword (:8) = 256` by EVAL_TAC
    >> fs [])
  >> Induct
  >> simp [Once (fetch "-" "semanticprimitives_ws_to_chars_side_def")]
QED

val _ = update_precondition semanticprimitives_ws_to_chars_side;
val _ = next_ml_names := ["compiler_for_eval"];
val r = translate compiler_for_eval_alt;

(* the two primitive uses of Eval: a one-argument call that installs the
   compiler (its state and a closure implementing it), and a two-argument
   call that evaluates declarations in an environment and returns the new
   environment paired with an error message ("" on success) *)
val _ = append_prog
  ``[Dlet (Locs (1,2) (2,21)) (Pvar «eval_init_prim»)
      (Fun «x» (App Eval [Var (Short «x»)]));
     Dlet (Locs (1,2) (2,21)) (Pvar «eval_prim»)
      (Fun «x» (Mat (Var (Short «x»))
        [(Pcon NONE [Pvar «env»; Pvar «decs»],
          App Eval [Var (Short «env»); Var (Short «decs»)])]))]``;

Datatype:
  eval_res = Compile_error 'a | Eval_result 'b | Eval_exn 'c
End

val _ = register_type ``:('a,'b,'c) eval_res``;

(* the compiler closure given to Eval: it signals failure by raising Bind *)
Quote add_cakeml:
  fun compiler_fun host (id, st, decs) =
    case compiler_for_eval host (id,(st,decs)) of
      None => raise Bind
    | Some (st2,(bs,ws)) => (st2,bs,ws)
End

Quote add_cakeml:
  fun eval (env, decs) =
    let
      val (new_env, msg) = eval_prim (env, decs)
    in
      if msg = "" then Eval_result new_env
      else Compile_error "ERROR: failed to compile input\n"
    end
    handle e => Eval_exn e
End

Quote exn_msg_dec = cakeml:
  val _ = (TextIO.print (!Repl.errorMessage);
           print_pp (pp_exn (!Repl.exn));
           print "\n")
End

Definition report_exn_dec_def:
  report_exn_dec = ^exn_msg_dec
End

val _ = next_ml_names := ["report_exn_dec"];
val r = translate report_exn_dec_def;

Quote add_cakeml:
  fun report_exn e =
  (Repl.exn := e;
   Repl.errorMessage := "EXCEPTION: ";
   report_exn_dec)
End

Quote error_msg_dec = cakeml:
  val _ = TextIO.print (!Repl.errorMessage)
End

Definition report_error_dec_def:
  report_error_dec = ^error_msg_dec
End

val _ = next_ml_names := ["report_error_dec"];
val r = translate report_error_dec_def;

Quote add_cakeml:
  fun report_error msg =
  (Repl.errorMessage := msg;
   report_error_dec)
End

val _ = next_ml_names := ["roll_back"];
val r = translate repl_check_and_tweakTheory.roll_back_def;
val _ = next_ml_names := ["check_and_tweak"];
val r = translate repl_check_and_tweakTheory.check_and_tweak_def;

Quote add_cakeml:
  fun repl (parse, types, env, decs, input_str) =
  case check_and_tweak (decs, (types, input_str)) of
    Inl msg => repl (parse, types, env, report_error msg, "")
  | Inr (safe_decs, new_types) =>
      case eval (env, safe_decs) of
        Compile_error msg =>
          repl (parse, types, env, report_error msg, "")
      | Eval_exn e =>
          repl (parse, roll_back (types, new_types), env, report_exn e, "")
      | Eval_result new_env =>
          if !Repl.isEOF then () else
            let
              val (parsed_input, new_input) =
                case !Repl.nextInput of
                  Inl text => (parse text, text)
                | Inr decs => (Inr decs, "")
            in
              case parsed_input of
                Inl msg =>
                  repl (parse, new_types, new_env, report_error msg, "")
              | Inr new_decs =>
                  repl (parse, new_types, new_env, new_decs, new_input)
            end
End

val _ = next_ml_names := ["init_types"];
val r = translate repl_init_typesTheory.repl_init_types_eq;

Definition parse_cakeml_syntax_def:
  parse_cakeml_syntax input =
  case parse_prog (lexer_fun (explode input)) of
  | Success _ x _ => INR x
  | Failure l _ => INL («Parsing failed at » ^ locs_to_string input (SOME l))
End

val _ = next_ml_names := ["parse_cakeml_syntax"];
val r = translate parse_cakeml_syntax_def;

Definition boot_marker_def:
  boot_marker cl = if MEM «--candle» cl then «candle» else «»
End

val _ = next_ml_names := ["boot_marker"];
val r = translate (boot_marker_def |> REWRITE_RULE [MEMBER_INTRO]);

Quote add_cakeml:
  fun start_repl cl =
    let
      val parse = parse_cakeml_syntax
      val types = init_types
      val env = repl_init_env
      val decs = []
      val input_str = ""
      val _ = Repl.nextInput := Inl (boot_marker cl)
    in
      repl (parse, types, env, decs, input_str)
    end
End

(* the only target-specific step of the REPL: installing the compiler for
   the host in Eval *)
Quote add_cakeml:
  fun run_interactive_repl (host,cl) =
    let
      val cs = Repl.charsFrom "config_enc_str.txt"
      val s1 = decodeProg.decode_backend_config cs
      val _ = eval_init_prim (s1, compiler_fun host)
    in
      start_repl cl
    end
End

Definition has_repl_flag_def:
  has_repl_flag cl <=> MEM «--repl» cl \/ MEM «--candle» cl
End

val _ = next_ml_names := ["compiler_has_repl_flag"];
val r = translate (has_repl_flag_def |> REWRITE_RULE [MEMBER_INTRO]);

Definition full_compile_host_def:
  full_compile_host host cl inp fs =
  if has_help_flag cl then
    add_stdout fs help_string
  else if has_version_flag cl then
    add_stdout fs current_build_info_str
  else
    let (out, err) = compile_main (host_args host cl) inp in
      add_stderr (add_stdout (fastForwardFD fs 0) (concat (append out))) err
End

Theorem full_compile_host_x64:
  full_compile_host HostX64 cl inp fs = full_compile cl inp fs
Proof
  simp [full_compile_host_def,full_compile_def]
QED

Quote add_cakeml:
  fun main_host (host,u) =
  let
    val cl = CommandLine.arguments ()
  in
    if compiler_has_repl_flag cl then
      run_interactive_repl (host,cl)
    else if compiler_common_has_help_flag cl then
      print compiler_help_string
    else if compiler_common_has_version_flag cl then
      print compiler_current_build_info_str
    else
      case compiler_compile_main (host_args host cl)
             (String.explode (TextIO.inputAll (TextIO.openStdIn ()))) of
        (c,e) => (print_app_list c; TextIO.output TextIO.stdErr e;
                   compiler_commonprog_nonzero_exit_code_for_error_msg e)
  end
End

val main_host_v_def = fetch "-" "main_host_v_def";

Theorem main_host_spec:
  COMPILER_MAINPROG_COMPILER_HOST_TYPE host host_v /\
  ~has_repl_flag (TL cl) /\ IS_SOME (stdin_content fs) ==>
  app (p:'ffi ffi_proj) main_host_v
      [Conv NONE [host_v; Conv NONE []]] (STDIO fs * COMMANDLINE cl)
      (POSTv uv.
       &UNIT_TYPE () uv
       * STDIO (full_compile_host host (TL cl) (get_stdin fs) fs)
       * COMMANDLINE cl)
Proof
  rpt strip_tac
  \\ xcf_with_def main_host_v_def
  \\ xmatch
  \\ xlet_auto >- (xcon \\ xsimpl)
  \\ xlet_auto >- xsimpl
  \\ reverse (Cases_on `STD_streams fs`)
  >- (fs [STDIO_def] \\ xpull)
  \\ reverse (Cases_on `?inp pos. stdin fs inp pos`)
  >- (
    fs [STDIO_def,IOFS_def] \\ xpull \\ fs [stdin_def]
    \\ `F` suffices_by fs []
    \\ fs [wfFS_def,STD_streams_def,MEM_MAP,Once EXISTS_PROD,PULL_EXISTS]
    \\ fs [EXISTS_PROD]
    \\ metis_tac [ALOOKUP_FAILS,ALOOKUP_MEM,NOT_SOME_NONE,SOME_11,
                  PAIR_EQ,option_CASES])
  \\ fs [get_stdin_def]
  \\ SELECT_ELIM_TAC
  \\ simp [FORALL_PROD,EXISTS_PROD]
  \\ conj_tac >- metis_tac []
  \\ rw []
  \\ imp_res_tac stdin_11 \\ rw []
  \\ imp_res_tac stdin_get_fd_content
  \\ xlet_auto >- xsimpl
  \\ xif
  \\ first_x_assum $ irule_at $ Pos hd \\ simp []
  \\ xlet_auto >- xsimpl
  \\ xif
  >- (
    simp [full_compile_host_def]
    \\ xapp
    \\ CONV_TAC SWAP_EXISTS_CONV
    \\ qexists_tac `help_string`
    \\ fs [compilerTheory.help_string_def,compiler_help_string_v_thm]
    \\ xsimpl
    \\ rename1 `add_stdout _ (strlit string)`
    \\ CONV_TAC SWAP_EXISTS_CONV
    \\ qexists_tac `fs`
    \\ xsimpl)
  \\ xlet_auto >- xsimpl
  \\ xif
  >- (
    simp [full_compile_host_def]
    \\ xapp
    \\ CONV_TAC SWAP_EXISTS_CONV
    \\ qexists_tac `current_build_info_str`
    \\ fs [compilerTheory.current_build_info_str_def,
           compiler_current_build_info_str_v_thm]
    \\ xsimpl
    \\ rename1 `add_stdout _ (strlit string)`
    \\ CONV_TAC SWAP_EXISTS_CONV
    \\ qexists_tac `fs`
    \\ xsimpl)
  \\ rename1 `stdin fs source_input stdin_position`
  \\ `stdin_content fs = SOME source_input /\ stdin_position = 0` by (
    gvs [stdin_def,get_fd_content_def]
    \\ fs [stdin_content_def,IS_SOME_EXISTS])
  \\ gvs []
  \\ xlet_auto >- (xcon \\ xsimpl)
  \\ xlet_auto_spec (SOME openStdIn_spec_str) >- xsimpl
  \\ xlet `POSTv v. &STRING_TYPE (implode source_input) v *
                   STDIO (fastForwardFD fs 0) * COMMANDLINE cl`
  >- (
    xapp
    \\ qexistsl_tac [`COMMANDLINE cl`,`source_input`,`fs`,`0`]
    \\ fs [STD_streams_get_mode]
    \\ xsimpl)
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ namedCases_on `compiler$compile_main (host_args host (TL cl)) source_input`
       ["compiler_output compiler_diagnostics"]
  \\ gvs [full_compile_host_def,ml_translatorTheory.PAIR_TYPE_def]
  \\ xmatch
  \\ xlet_auto >- xsimpl
  \\ qmatch_goalsub_abbrev_tac `STDIO output_fs`
  \\ xlet `POSTv uv. &UNIT_TYPE () uv *
                   STDIO (add_stderr output_fs compiler_diagnostics) *
                   COMMANDLINE cl`
  >- (
    xapp_spec output_stderr_spec
    \\ xsimpl
    \\ qexists_tac `COMMANDLINE cl`
    \\ asm_exists_tac \\ xsimpl
    \\ qexists_tac `output_fs` \\ xsimpl)
  \\ xapp
  \\ asm_exists_tac \\ simp [] \\ xsimpl
QED

Theorem full_compile_host_with_numchars:
  full_compile_host host cl inp (fs with numchars := ns) =
  full_compile_host host cl inp fs with numchars := ns
Proof
  rw [full_compile_host_def,UNCURRY,fastForwardFD_with_numchars,
      add_stdo_with_numchars]

QED
