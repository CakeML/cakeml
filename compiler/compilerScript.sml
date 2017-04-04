open preamble
     lexer_funTheory
     cmlParseTheory
     inferTheory
     backendTheory

val _ = new_theory"compiler";

val _ = Datatype`
  config =
    <| inferencer_config : inferencer_config
     ; backend_config : α backend$config
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
          case backend$compile c.backend_config (prelude ++ prog) of
          | NONE => Failure CompileError
          | SOME (bytes,limit) => Success (bytes,limit)`;

val _ = export_theory();
