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

val _ = Datatype`compile_error = ParseError | TypeError string | CompileError`;

val locs_to_string_def = Define `
  (locs_to_string NONE = "unknown location") ∧
  (locs_to_string (SOME (startl, endl)) =
    "location starting at row " ++ toString startl.row ++ " column " ++ toString startl.col ++
    ", ending at row "  ++ toString startl.row ++ " column " ++ toString startl.col)`;

val compile_def = Define`
  compile c prelude input =
    case parse_prog (lexer_fun input) of
    | NONE => Failure ParseError
    | SOME prog =>
       case infertype_prog c.inferencer_config (prelude ++ prog) of
       | Failure (locs, msg) =>
           Failure (TypeError (msg ++ " at " ++ locs_to_string locs))
       | Success ic =>
          case backend$compile c.backend_config (prelude ++ prog) of
          | NONE => Failure CompileError
          | SOME (bytes,limit) => Success (bytes,limit)`;

val _ = export_theory();
