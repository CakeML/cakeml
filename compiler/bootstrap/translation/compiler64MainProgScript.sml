(*
  Shared entry points for the native 64-bit compiler programs.
*)
Theory compiler64MainProg[no_sig_docs]
Ancestors
  compiler64CommonProg compiler64Host compiler export ml_translator
  basis_ffi[qualified]
Libs
  preamble ml_translatorLib cfLib basis

open preamble compiler64CommonProgTheory compiler64HostTheory compilerTheory
     exportTheory ml_translatorLib ml_translatorTheory
open cfLib basis

val _ = temp_delsimps ["NORMEQ_CONV", "lift_disj_eq", "lift_imp_disj"];
val _ = translation_extends "compiler64CommonProg";
val _ = ml_translatorLib.use_sub_check true;
val _ = use_long_names := true;

val spec64 = INST_TYPE [alpha |-> ``:64``];

val _ = register_type ``:compiler64_host``;
val _ = next_ml_names := ["host_args"];
val r = translate host_args_def;

Definition compiler_for_eval_def:
  compiler_for_eval host = compile_inc_progs_for_eval (host_config host)
End

Theorem upper_w2w_eq_I[local]:
  backend_common$upper_w2w = (I:word64 -> word64)
Proof
  fs [backend_commonTheory.upper_w2w_def,FUN_EQ_THM]
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
             listTheory.MAP_ID, upper_w2w_eq_I])
  |> LIST_CONJ;

val r = translate (word_to_wordTheory.compile_single_def |> spec64);
val r = translate (word_to_wordTheory.full_compile_single_def |> spec64);
val r = translate (word_to_wordTheory.full_compile_single_for_eval_def |> spec64);

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

val _ = append_prog
  ``[Dlet (Locs (POSN 1 2) (POSN 2 21)) (Pvar «eval_prim»)
      (Fun «x» (Mat (Var (Short «x»))
        [(Pcon NONE [Pvar «env»; Pvar «s1»; Pvar «decs»;
                     Pvar «s2»; Pvar «bs»; Pvar «ws»],
          App Eval [Var (Short «env»); Var (Short «s1»); Var (Short «decs»);
                    Var (Short «s2»); Var (Short «bs»); Var (Short «ws»)])]))]``;

Datatype:
  eval_res = Compile_error 'a | Eval_result 'b 'c | Eval_exn 'd 'e
End

val _ = register_type ``:('a,'b,'c,'d,'e) eval_res``;

Quote add_cakeml:
  fun eval (host, ((s1,next_gen), (env,id), decs)) =
    case compiler_for_eval host ((id,0),(s1,decs)) of
      None => Compile_error "ERROR: failed to compile input\n"
    | Some (s2,(bs,ws)) =>
        let
          val new_env = eval_prim (env,s1,decs,s2,bs,ws)
        in Eval_result (new_env,next_gen) (s2,next_gen+1) end
        handle e => Eval_exn e (s2,next_gen+1)
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
  fun repl (host, parse, types, conf, env, decs, input_str) =
  case check_and_tweak (decs, (types, input_str)) of
    Inl msg => repl (host, parse, types, conf, env, report_error msg, "")
  | Inr (safe_decs, new_types) =>
      case eval (host, (conf, env, safe_decs)) of
        Compile_error msg =>
          repl (host, parse, types, conf, env, report_error msg, "")
      | Eval_exn e new_conf =>
          repl (host, parse, roll_back (types, new_types), new_conf, env,
                report_exn e, "")
      | Eval_result new_env new_conf =>
          if !Repl.isEOF then () else
            let val new_input = !Repl.nextString in
              case parse new_input of
                Inl msg =>
                  repl (host, parse, new_types, new_conf, new_env,
                        report_error msg, "")
              | Inr new_decs =>
                  repl (host, parse, new_types, new_conf, new_env,
                        new_decs, new_input)
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

Definition parse_ocaml_syntax_def:
  parse_ocaml_syntax input =
  case caml_parser$run (explode input) of
  | INR res => INR res
  | INL (l,err) =>
      INL (err ^ «\nParsing failed at » ^ locs_to_string input (SOME l))
End

Definition select_parse_def:
  select_parse cl =
  if MEMBER «--candle» cl then parse_ocaml_syntax else parse_cakeml_syntax
End

val r = translate parse_cakeml_syntax_def;
val r = translate parse_ocaml_syntax_def;
val _ = next_ml_names := ["select_parse"];
val r = translate select_parse_def;

Definition init_next_string_def:
  init_next_string cl = if MEM «--candle» cl then «candle» else «»
End

val _ = next_ml_names := ["init_next_string"];
val r = translate (init_next_string_def |> REWRITE_RULE [MEMBER_INTRO]);

Quote add_cakeml:
  fun start_repl (host,cl,s1) =
    let
      val parse = select_parse cl
      val types = init_types
      val conf = (s1,1)
      val env = (repl_init_env, 0)
      val decs = []
      val input_str = ""
      val _ = Repl.nextString := init_next_string cl
    in
      repl (host, parse, types, conf, env, decs, input_str)
    end
End

Quote add_cakeml:
  fun run_interactive_repl (host,cl) =
    let
      val cs = Repl.charsFrom "config_enc_str.txt"
      val s1 = decodeProg.decode_backend_config cs
    in
      start_repl (host,cl,s1)
    end
End

Definition has_repl_flag_def:
  has_repl_flag cl <=> MEM «--repl» cl \/ MEM «--candle» cl
End

val _ = next_ml_names := ["compiler_has_repl_flag"];
val r = translate (has_repl_flag_def |> REWRITE_RULE [MEMBER_INTRO]);
val r = translate (has_pancake_flag_def |> SIMP_RULE (srw_ss()) [MEMBER_INTRO]);

Definition full_compile_host_def:
  full_compile_host host cl inp fs =
  if has_help_flag cl then
    add_stdout fs help_string
  else if has_version_flag cl then
    add_stdout fs current_build_info_str
  else
    case parse_pancake_feature cl of
      SOME rest => add_stdout fs $ print_bool $ news$query_news rest
    | NONE =>
        let (out, err) =
            if has_pancake_flag cl then
              compile_pancake_64 (host_args host cl) inp
            else
              compile_64 (host_args host cl) inp
        in
          add_stderr (add_stdout (fastForwardFD fs 0) (concat (append out))) err
End

Theorem full_compile_host_x64:
  full_compile_host HostX64 cl inp fs = full_compile_64 cl inp fs
Proof
  simp [full_compile_host_def,full_compile_64_def]
QED

Quote add_cakeml:
  fun main_host (host,u) =
  let
    val cl = CommandLine.arguments ()
  in
    if compiler_has_repl_flag cl then
      run_interactive_repl (host,cl)
    else if compiler_has_help_flag cl then
      print compiler_help_string
    else if compiler_has_version_flag cl then
      print compiler_current_build_info_str
    else
      case compiler_parse_pancake_feature cl of
        Some rest => print (compiler_print_bool (news_query_news rest))
      | None =>
          let val compile_cl = host_args host cl in
            if compiler_has_pancake_flag cl then
              case compiler_compile_pancake_64 compile_cl
                     (String.explode (TextIO.inputAll (TextIO.openStdIn ()))) of
                (c,e) => (print_app_list c; TextIO.output TextIO.stdErr e;
                           compiler64commonprog_nonzero_exit_code_for_error_msg e)
            else
              case compiler_compile_64 compile_cl
                     (String.explode (TextIO.inputAll (TextIO.openStdIn ()))) of
                (c,e) => (print_app_list c; TextIO.output TextIO.stdErr e;
                           compiler64commonprog_nonzero_exit_code_for_error_msg e)
          end
  end
End

val main_host_v_def = fetch "-" "main_host_v_def";

Theorem main_host_spec:
  COMPILER64HOST_COMPILER64_HOST_TYPE host host_v /\
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
  \\ imp_res_tac stdin_get_file_content
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
  \\ xlet_auto >- xsimpl
  \\ gvs [oneline std_preludeTheory.OPTION_TYPE_def]
  \\ reverse PURE_FULL_CASE_TAC
  \\ gvs []
  >- (
    xmatch
    \\ xlet_auto >- xsimpl
    \\ xlet_auto >- xsimpl
    \\ simp [full_compile_host_def]
    \\ xapp
    \\ first_assum $ irule_at $ Pos hd
    \\ qexists_tac `fs`
    \\ xsimpl)
  \\ xmatch
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ xif
  \\ (
    xlet_auto >- (xcon \\ xsimpl)
    \\ rename [`stdin fs inp pos`]
    \\ `stdin_content fs = SOME inp /\ pos = 0` by (
      gvs [stdin_def,get_file_content_def]
      \\ fs [stdin_content_def,IS_SOME_EXISTS])
    \\ gvs []
    \\ xlet_auto_spec (SOME openStdIn_spec_str) >- xsimpl
    \\ xlet `POSTv v. &STRING_TYPE (implode inp) v *
                    STDIO (fastForwardFD fs 0) * COMMANDLINE cl`
    >- (
      xapp
      \\ qexistsl [`COMMANDLINE cl`, `inp`, `fs`, `0`]
      \\ xsimpl)
    \\ xlet_auto >- xsimpl
    \\ xlet_auto >- xsimpl
    \\ fs [full_compile_host_def]
    \\ pairarg_tac
    \\ fs [ml_translatorTheory.PAIR_TYPE_def]
    \\ gvs [CaseEq "bool"]
    \\ xmatch
    \\ xlet_auto >- xsimpl
    \\ qmatch_goalsub_abbrev_tac `STDIO output_fs`
    \\ xlet `POSTv uv. &UNIT_TYPE () uv *
                      STDIO (add_stderr output_fs err) * COMMANDLINE cl`
    >- (
      xapp_spec output_stderr_spec \\ xsimpl
      \\ qexists_tac `COMMANDLINE cl`
      \\ asm_exists_tac \\ xsimpl
      \\ qexists_tac `output_fs` \\ xsimpl)
    \\ xapp
    \\ asm_exists_tac \\ simp [] \\ xsimpl)
QED

Theorem full_compile_host_with_numchars:
  full_compile_host host cl inp (fs with numchars := ns) =
  full_compile_host host cl inp fs with numchars := ns
Proof
  rw [full_compile_host_def,UNCURRY,fastForwardFD_with_numchars,
      add_stdo_with_numchars]
  \\ Cases_on `parse_pancake_feature cl`
  \\ simp []
QED
