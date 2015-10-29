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

val _ = Datatype`compile_error = ParseError | TypeError | CompileError`;

val compile_def = Define`
  compile c prelude input =
    case parse_prog (lexer_fun input) of
    | NONE => Failure ParseError
    | SOME prog =>
       case infertype_prog c.inferencer_config (prelude ++ prog) of
       | NONE => Failure TypeError
       | SOME ic =>
          case source_to_target$compile c.backend_config (prelude ++ prog) of
          | NONE => Failure CompileError
          | SOME (bytes,bc) =>
            Success (bytes, <| inferencer_config := ic
                             ; backend_config := bc
                             |>)`;

val _ = export_theory();
