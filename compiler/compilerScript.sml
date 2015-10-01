open preamble
     lexer_funTheory
     cmlParseTheory
     inferTheory
     source_to_targetTheory

val _ = new_theory"compiler";

val _ = Datatype`
  config =
    <| inferencer_config : inferencer_config
     ; backend_config : α source_to_target$config
     |>`;

val compile_def = Define`
  compile c input =
    case parse_prog (lexer_fun input) of
    | NONE => Failure "parse error"
    | SOME prog =>
        case infertype_prog c.inferencer_config prog of
        | NONE => Failure "type error"
        | SOME ic =>
            case source_to_target$compile c.backend_config prog of
            | NONE => Failure "compile error"
            | SOME (bytes,bc) =>
              Success (bytes, <| inferencer_config := ic
                               ; backend_config := bc
                               |>)`;

val _ = export_theory();
