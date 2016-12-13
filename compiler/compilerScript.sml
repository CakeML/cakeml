open preamble
     lexer_funTheory
     cmlParseTheory
     inferTheory
     backendTheory
     basisProgTheory

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

val encode_error_def = Define`
  (encode_error ParseError = (n2w 1 : word8)) ∧
  (encode_error TypeError = n2w 2) ∧
  (encode_error CompileError = n2w 3)`;

val compile_to_bytes_def = Define`
  compile_to_bytes c input =
    case compile c basis input of
    | Failure err => [encode_error err]
    | Success (bytes,ffis) => (n2w(LENGTH ffis))::bytes`;

val _ = export_theory();
