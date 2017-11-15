open preamble
     lexer_funTheory lexer_implTheory
     cmlParseTheory
     inferTheory
     backendTheory
     mlintTheory mlstringTheory basisProgTheory
     fromSexpTheory simpleSexpParseTheory

val _ = new_theory"compiler";

(* == Build info =========================================================== *)

val current_version_tm = mlstring_from_proc "git" ["rev-parse", "HEAD"]
val poly_version_tm = mlstring_from_proc "poly" ["-v"]
val hol_version_tm =
  let
    val holdir = Option.valOf (OS.Process.getEnv "HOLDIR")
  in
    mlstring_from_proc_from holdir "git" ["rev-parse", "HEAD"]
  end
  handle _ => Term `NONE : mlstring option`

val date_str = Date.toString (Date.fromTimeUniv (Time.now ())) ^ " UTC"
val date_tm = Term `strlit^(stringSyntax.fromMLstring date_str)`

(* Information about the current build *)
val _ = Datatype `
  current_build_info =
    <| git_commit : mlstring option
     ; date       : mlstring
     ; hol_commit : mlstring option
     ; polyml     : mlstring option |>`

val current_info_def = Define
  `current_info =
     <| git_commit := ^current_version_tm
      ; date       := ^date_tm
      ; hol_commit := ^hol_version_tm
      ; polyml     := ^poly_version_tm |>`

val print_option_def = Define `
  print_option h x =
    case x of
      NONE => strlit""
    | SOME y => h ^ strlit": " ^ y ^ strlit"\n"`

val current_build_info_toString_def = Define `
  current_build_info_toString b =
    let commit = print_option (strlit"CakeML") b.git_commit in
    let hol    = print_option (strlit"HOL4") b.hol_commit in
    let poly   = print_option (strlit"PolyML") b.polyml in
      (List [
       (concat
         [ strlit"The CakeML compiler\n"
         ; strlit"Build date: "; b.date; strlit"\n\n"
         ; strlit"Version details:\n"
         ; commit; hol; poly ])], implode"")`

(* ========================================================================= *)

val _ = Datatype`
  config =
    <| inferencer_config : inferencer_config
     ; backend_config : α backend$config
     ; input_is_sexp : bool
     |>`;

val _ = Datatype`compile_error = ParseError | TypeError mlstring | CompileError`;

val locs_to_string_def = Define `
  (locs_to_string NONE = implode "unknown location") ∧
  (locs_to_string (SOME (Locs startl endl)) =
    if Locs startl endl = unknown_loc then
      implode "unknown location"
    else
      concat
        [implode "location starting at row ";
         toString &startl.row;
         implode " column ";
         toString &startl.col;
         implode ", ending at row ";
         toString &endl.row;
         implode " column ";
         toString &endl.col])`;

(* this is a rather annoying feature of peg_exec requiring locs... *)
val _ = overload_on("add_locs",``MAP (λc. (c,unknown_loc))``);

val compile_def = Define`
  compile c prelude input =
    case
      if c.input_is_sexp
      then OPTION_BIND (parse_sexp (add_locs input)) (sexplist sexptop)
      else parse_prog (lexer_fun input)
    of
    | NONE => Failure ParseError
    | SOME prog =>
       case infertype_prog c.inferencer_config (prelude ++ prog) of
       | Failure (locs, msg) =>
           Failure (TypeError (concat [msg; implode " at "; locs_to_string locs]))
       | Success ic =>
          case backend$compile c.backend_config (prelude ++ prog) of
          | NONE => Failure CompileError
          | SOME (bytes,c) => Success (bytes,c)`;

val compile_explorer_def = Define`
  compile_explorer c prelude input =
    case
      if c.input_is_sexp
      then OPTION_BIND (parse_sexp (add_locs input)) (sexplist sexptop)
      else parse_prog (lexer_fun input)
    of
    | NONE => Failure ParseError
    | SOME prog =>
       case infertype_prog c.inferencer_config (prelude ++ prog) of
       | Failure (locs, msg) => Failure (TypeError (concat [msg; implode " at "; locs_to_string locs]))
       | Success ic => Success (backend$compile_explorer c.backend_config (prelude ++ prog))`

(* The top-level compiler *)
val error_to_str_def = Define`
  (error_to_str ParseError = strlit "### ERROR: parse error\n") /\
  (error_to_str (TypeError s) = concat [strlit "### ERROR: type error\n"; s; strlit "\n"]) /\
  (error_to_str CompileError = strlit "### ERROR: compile error\n")`;

(* TODO: translator fails inside mlstringLib.mlstring_case_conv
  when the following definition just matches against (strlit str) directly *)
val parse_num_def = Define`
  parse_num str =
  let str = explode str in
  if EVERY isDigit str
  then
    SOME (num_from_dec_string_alt str)
  else NONE `

val find_parse_def = Define`
  (find_parse flag [] = NONE) ∧
  (find_parse flag (x::xs) =
    if isPrefix flag x then
      parse_num (extract x (strlen flag) NONE)
    else find_parse flag xs)`

val comma_tokens_def = Define `
  (comma_tokens acc xs [] = if NULL xs then acc else acc ++ [implode xs]) /\
  (comma_tokens acc (xs:string) (c::(cs:string)) =
    if c = #"," then
      comma_tokens (acc ++ if NULL xs then [] else [implode xs]) [] cs
    else
      comma_tokens acc (STRCAT xs [c]) cs)`

val parse_num_list_def = Define`
  (parse_num_list [] = []) /\
  (parse_num_list (x::xs) =
     case parse_num x of
     | NONE => parse_num_list xs
     | SOME n => n :: parse_num_list xs)`

val parse_nums_def = Define `
  parse_nums str =
    SOME (parse_num_list (comma_tokens [] [] (explode str)))`

val find_parse_nums_def = Define`
  (find_parse_nums flag [] = NONE) ∧
  (find_parse_nums flag (x::xs) =
    if isPrefix flag x then
      parse_nums (extract x (strlen flag) NONE)
    else find_parse_nums flag xs)`

(* parses a list of strings to configurations and modifies the configuration *)
val extend_with_args_def = Define`
  extend_with_args ls conf =
    (* closLang optimisation flags *)
    let multi = ¬(MEM (strlit"--no_multi") ls) in
    let known = ¬(MEM (strlit"--no_known") ls) in
    let call = ¬(MEM (strlit"--no_call") ls) in
    let maxapp = find_parse (strlit "--max_app=") ls in
    let clos = conf.clos_conf in
    let updated_clos =
      clos with <|
        do_mti:= multi; do_known:= known;
        do_call:= call;
        max_app:= (case maxapp of NONE => clos.max_app | SOME v => v)
      |> in
    (* bvl optimisation flags *)
    let inlinesz = find_parse (strlit "--inline_size=") ls in
    let expcut = find_parse (strlit "--exp_cut=") ls in
    let splitmain = ¬(MEM (strlit"--no_split") ls) in
    let bvl = conf.bvl_conf in
    let updated_bvl =
      bvl with <|
        inline_size_limit:= case inlinesz of NONE => bvl.inline_size_limit | SOME v => v;
        exp_cut:= case expcut of NONE => bvl.exp_cut | SOME v => v;
        split_main_at_seq := splitmain
      |> in
    (* choice of GC *)
    let gc_none = (MEM (strlit"--gc=none") ls) in
    let gc_simple = (MEM (strlit"--gc=simple") ls) in
    let gc_gen = (MEM (strlit"--gc=gen") ls) in
    let gc_gen_sizes = find_parse_nums (strlit "--gc=gen") ls in
    let data = conf.data_conf in
    let updated_data =
	data with <| gc_kind :=
		  case gc_gen_sizes of
		  | SOME gs => Generational gs
		  | NONE =>
   		      if gc_none then None else
		      if gc_simple then Simple else
		      if gc_gen then Generational [] else data.gc_kind |> in
    (* choice of register allocator *)
    let regalg = find_parse (strlit "--reg_alg=") ls in
    let wtw = conf.word_to_word_conf in
    let updated_wtw =
      wtw with <|reg_alg:= case regalg of NONE => wtw.reg_alg | SOME v =>v |> in
    conf with <|clos_conf := updated_clos; bvl_conf:=updated_bvl; word_to_word_conf := updated_wtw|>`

(* Default stack and heap limits *)
val default_heap_sz_def = Define`
  default_heap_sz = 1000n`

val default_stack_sz_def = Define`
  default_stack_sz = 1000n`

val parse_heap_stack_def = Define`
  parse_heap_stack ls =
    let heap =
      case find_parse (strlit "--heap_size=") ls of
        NONE => default_heap_sz
      | SOME v => v in
    let stack =
      case find_parse (strlit "--stack_size=") ls of
        NONE => default_stack_sz
      | SOME v => v in
    (heap,stack)`

(* Check for version flag *)
val has_version_flag_def = Define `
  has_version_flag ls = MEM (strlit"--version") ls`

val format_compiler_result_def = Define`
  format_compiler_result bytes_export (heap:num) (stack:num) (Failure err) =
    (List[]:mlstring app_list, error_to_str err) ∧
  format_compiler_result bytes_export heap stack
    (Success ((bytes:word8 list),(data:'a word list),(c:'a lab_to_target$config))) =
    (bytes_export (the [] c.ffi_names) heap stack bytes data, implode "")`;

(* The top-level compiler with almost everything instantiated except the top-level configuration *)

val compile_to_bytes_def = Define `
  compile_to_bytes backend_conf bytes_export cl input =
  if has_version_flag cl then
    current_build_info_toString current_info
  else
    let ext_conf = extend_with_args cl backend_conf in
    let (heap,stack) = parse_heap_stack cl in
    let compiler_conf =
      <| inferencer_config := init_config;
         backend_config := ext_conf;
         input_is_sexp := MEM (strlit"--sexp") cl |> in
    format_compiler_result bytes_export heap stack
      (compiler$compile compiler_conf basis input)`;

val _ = export_theory();
