open preamble
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
  compile c tokens =
    case parse_prog tokens of
    | NONE => Failure "parse error"
    | SOME prog =>
        case infertype_prog c.inferencer_config prog of
        | NONE => Failure "type error"
        | SOME inferencer_config =>
            case compile c.backend_config prog of
            | NONE => Failure "compile error"
            | SOME (bytes,backend_config) =>
              Success (bytes, <| inferencer_config := inferencer_config
                               ; backend_config := backend_config
                               |>)`;

val _ = export_theory();
