(*
  The CakeML REPL
*)

open preamble basis
(*
  TODO: add this to INCLUDES as necessary
  val () = loadPath := "../compiler/inference/" :: !loadPath;
  val () = loadPath := "../compiler/parsing/" :: !loadPath;
*)
local open lexer_funTheory cmlParseTheory
           infer_tTheory inferTheory
in end

val _ = new_theory"replProg";

val _ = set_grammar_ancestry[
  "infer_t","infer",
  "tokenUtils","cmlPtreeConversion","cmlParse",
  "lexer_fun"];
val _ = temp_tight_equality();

val welcome_message_def = Define`
  welcome_message = strlit"CakeML\n"`;

val prompt_def = Define`
  prompt = strlit"> "`;

val res = translate welcome_message_def;
val res = translate prompt_def;

val magic_eval_exp =
  ``Fun "exp" (App Eval [Var(Short"env"); Var(Short"exp")])``;
val add_magic_eval =
  ml_progLib.add_Dlet_Fun
    ``unknown_loc`` ``"magic_eval"``
    ``"env"`` magic_eval_exp "magic_eval_v";

val magic_lookup_exp =
  ``Fun "id" (App EnvLookup [Var(Short"env"); Var(Short"id")])``;
val add_magic_lookup =
  ml_progLib.add_Dlet_Fun
    ``unknown_loc`` ``"magic_lookup"``
    ``"env"`` magic_lookup_exp "magic_lookup_v";

val () = ml_translatorLib.ml_prog_update add_magic_eval;
val () = ml_translatorLib.ml_prog_update add_magic_lookup;

val exn_infer_t_def = Define`
  exn_infer_t = Infer_Tapp [] Texn_num`;

val _ = Datatype`
  top_level = REPLCommand mlstring exp | TopLevelDecs (dec list)`;

val ptree_REPLCommand_def = Define`
  ptree_REPLCommand (Lf _) = NONE ∧
  ptree_REPLCommand (Nd nont args) =
    if FST nont <> mkNT nREPLCommand then NONE
    else
      case args of
      | [pt1; pt2] =>
        OPTION_BIND (destLf pt1)
          (λsym. OPTION_BIND (destTOK sym)
            (λtok. OPTION_BIND (destREPLIDT tok)
              (λrid. OPTION_BIND (ptree_Expr nEbase pt2)
                       (λexp. SOME (REPLCommand (implode rid) exp)))))
      | _ => NONE`;

val ptree_TopLevel_def = Define`
  ptree_TopLevel (Lf _) = NONE ∧
  ptree_TopLevel (Nd nont args) =
    if FST nont <> mkNT nTopLevel then NONE
    else
      case args of
        [pt] =>
          OPTION_CHOICE
            (ptree_REPLCommand pt)
            (OPTION_MAP TopLevelDecs (ptree_TopLevelDecs pt))
      | _ => NONE`;

val lex_and_parse_TopLevel_def = Define`
  lex_and_parse_TopLevel line =
    case destResult (cmlpegexec nTopLevel (lexer_fun line)) of
    | SOME ([], [pt]) => (ptree_TopLevel pt)
    | _ => NONE`;

val repl_printer_name_def = Define`
  repl_printer_name = "_ pp"`;
  (* TODO: not a strlit, since the AST doesn't have mlstrings in it *)

val add_repl_printer_name_dec_def = Define`
  add_repl_printer_name_dec exp =
    Dlet unknown_loc (Pvar repl_printer_name) exp`;

val _ = Datatype`repl_inf_state = <| ienv : inf_env; next_id : num |>`;

val repl_infertype_prog_def = Define`
  repl_infertype_prog inf_state prog =
    case infer_ds inf_state.ienv prog
           (init_infer_state <| next_uvar := 0; subst := FEMPTY;
                                next_id := inf_state.next_id |>)
    of
      (Success new_ienv, st) =>
        Success <| ienv := new_ienv; next_id := st.next_id |>
    | (Failure x, _) => Failure x`;

val repl_extend_inf_state_def = Define`
  repl_extend_inf_state inf_state new_stuff =
    <| ienv := extend_dec_ienv new_stuff.ienv inf_state.ienv
     ; next_id := new_stuff.next_id |>`;

val dummy_printer_def = Define`
  dummy_printer _ = strlit"?"`;

val val_string_def = Define`
  val_string inf_state name inf_type ppd_value =
    concat [strlit"val "; name;
            strlit": "; FST(inf_type_to_string inf_state.ienv.inf_t inf_type);
            strlit" = "; ppd_value; strlit"\n"]`;

(* TODO: Can this actually work? What is the type of pp_map?
         It can't have a type, so it can't come from the translator...
val repl_pp_fun_def = Define`
  repl_pp_fun pp_map inf_type v =
    case ALOOKUP pp_map inf_type of
    | NONE => dummy_printer v
    | SOME pp_fun => pp_fun v`;
*)

(*
  fun repl_build_and_format_output inf_state pp_map env bindings =
    String.concatWith "\n"
      (List.map (fn (name, inf_type) =>
                  val_string inf_state name inf_type
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
          case lex_and_parse_TopLevel line of
            Some (TopLevelDecs prog) =>
              case repl_infertype_prog inf_state prog of
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
                        val new_inf_state = repl_extend_inf_state inf_state new_stuff
                        val output = repl_build_and_format_output new_inf_state pp_map env
                                       (get_bindings new_stuff)
                        val state = (new_inf_state, env, pp_map)
                      in
                        (TextIO.print output;
                         Some state)
                      end
          | Some (REPLCommand ("InstallPP", parsed_exp)) =>
              let val prog = add_repl_printer_name_dec parsed_exp in
                case repl_infertype_prog inf_state prog of
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
          | _ => (TextIO.print_err "Cannot understand input\n";
                  Some state)`;

val main_ast = process_topdecs`
  fun main u =
    let
      val u = TextIO.print welcome_banner
      val u = TextIO.print prompt


