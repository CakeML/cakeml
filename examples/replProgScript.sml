(*
  The CakeML REPL
*)

open preamble basis

val welcome_message_def = Define`
  welcome_message = "CakeML\n"`;

val prompt_def = Define`
  prompt = "> "`;

val res = translate welcome_message_def;
val res = translate prompt_def;

val magic_eval_exp =
  ``Fun "exp" (App Eval [Var(Short"env"); Var(Short"exp")])``;
val add_magic_eval =
  ml_progLib.add_Dlet_Fun
    ``unknown_loc`` ``"magic_eval"``
    ``"env"`` magic_eval_exp;

val magic_lookup_exp =
  ``Fun "id" (App EnvLookup [Var(Short"env"); Var(Short"id")])``;
val add_magic_lookup =
  ml_progLib.add_Dlet_Fun
    ``unknown_loc`` ``"magic_lookup"``
    ``"env"`` magic_lookup_exp;

val () = ml_translatorLib.ml_prog_update add_magic_eval;
val () = ml_translatorLib.ml_prog_update add_magic_lookup;

val exn_infer_t_def = Define`
  exn_infer_t = Infer_Tapp [] Texn_num`;

val parse_REPLCommand_tm = ``
  peg_exec cmlPEG (nt (mkNT REPLCommand

val dummy_printer_def = Define`
  dummy_printer _ = strlit"?"`;

val val_string_def = Define`
  val_string name inf_type ppd_value =
    concat [strlit"val ", name, strlit" : ",
            inf_type_to_string inf_type, " = ",
            ppd_value, "\n"]`;

(* TODO: Can this actually work? What is the type of pp_map?
         It can't have a type, so it can't come from the translator...
val repl_pp_fun_def = Define`
  repl_pp_fun pp_map inf_type v =
    case ALOOKUP pp_map inf_type of
    | NONE => dummy_printer v
    | SOME pp_fun => pp_fun v`;
*)

(*
  fun repl_build_and_format_output pp_map env bindings =
    String.concatWith "\n"
      (List.map (fn (name, inf_type) =>
                  val_string name inf_type
                    (repl_pp_fun pp_map inf_type (magic_lookup env name)))
                bindings)
*)

(* REP -- the L is to come later... *)
val rep_ast = process_topdecs`
  fun rep state =
    case state of (inf_state, env, pp_map) =>
      case TextIO.inputLine TextIO.stdIn of
        None => None
      | Some line =>
          case CakeML.repl_parse line of
            Some (Decls prog) =>
              case CakeML.infertype inf_state prog of
                Failure (_, msg) =>
                  (TextIO.print_err msg;
                   TextIO.print_err "\n";
                   Some state)
              | Success new_stuff =>
                  case Some (magic_eval env prog)
                        handle e =>
                          (TextIO.print_err "Exception raised: ";
                           TextIO.print_err (CakeML.repl_pp_fun pp_map CakeML.exn_infer_t e);
                           TextIO.print_err ("\n");
                           None)
                  of
                    None => Some state
                  | Some env =>
                      let
                        val output = CakeML.repl_build_and_format_output pp_map env
                                       (get_bindings new_stuff)
                        val state = (CakeML.extend_inf_state inf_state new_stuff,
                                     env, pp_map)
                      in
                        (TextIO.print output;
                         Some state)
                      end
          | Some (InstallPP parsed_exp) =>
              let val prog = add_repl_printer_name_dec parsed_exp (* this could be done by CakeML.repl_parse *) in
                case CakeML.infertype inf_state prog of
                  Failure (_, msg) =>
                    (TextIO.print_err "Printer does not typecheck: ";
                     TextIO.print_err msg;
                     Some state)
                | Success new_inf_state =>
                    case Some (magic_eval env prog)
                         handle _ => None
                    of
                      None => (TextIO.print_err "Printer expression raised exception\n"; Some state)
                      Some pp_env =>
                        Some
                        (case CakeML.repl_get_pp_type_key new_inf_state of
                           None => (TextIO.print_err "Printer does not have a reasonable type\n";
                                    state)
                         | Some key =>
                            (inf_state, env,
                             CakeML.repl_extend_pp_map key
                               (magic_lookup pp_env repl_printer_name)))
              end
          | None => (TextIO.print_err "Cannot understand input\n";
                     Some state)`;

val main_ast = process_topdecs`
  fun main u =
    let
      val u = TextIO.print welcome_banner
      val u = TextIO.print prompt


