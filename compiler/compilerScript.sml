open preamble
     lexer_funTheory lexer_implTheory
     cmlParseTheory
     inferTheory
     backendTheory
     mlintTheory mlstringTheory basisProgTheory
     fromSexpTheory simpleSexpParseTheory

open x64_configTheory export_x64Theory
open arm8_configTheory export_arm8Theory
open riscv_configTheory export_riscvTheory
open mips_configTheory export_mipsTheory
open arm6_configTheory export_arm6Theory

val _ = new_theory"compiler";

(* == Build info =========================================================== *)

val current_version_tm = mlstring_from_proc "git" ["rev-parse", "HEAD"]
(*"*)
val poly_version_tm = mlstring_from_proc "poly" ["-v"]
val hol_version_tm =
  let
    val holdir = Option.valOf (OS.Process.getEnv "HOLDIR")
  in
    mlstring_from_proc_from holdir "git" ["rev-parse", "HEAD"]
  end
  handle _ => Term `NONE : mlstring option`

val date_str = Date.toString (Date.fromTimeUniv (Time.now ())) ^ " UTC\n"
val date_tm = Term `strlit^(stringSyntax.fromMLstring date_str)`

val print_option_def = Define `
  print_option h x =
    case x of
      NONE => strlit""
    | SOME y => h ^ strlit" " ^ y ^ strlit"\n"`

val current_build_info_str_tm = EVAL ``
    let commit = print_option (strlit"CakeML:") ^current_version_tm in
    let hol    = print_option (strlit"HOL4:  ") ^hol_version_tm in
    let poly   = print_option (strlit"PolyML:") ^poly_version_tm in
      concat
        [ strlit"The CakeML compiler\n\n"
        ; strlit"Version details:\n"
        ; ^date_tm; strlit"\n"
        ; commit; hol; poly ]``
  |> concl |> rhs

val current_build_info_str_def = Define `
  current_build_info_str = ^current_build_info_str_tm`

(* ========================================================================= *)

val _ = Datatype`
  config =
    <| inferencer_config : inferencer_config
     ; backend_config : α backend$config
     ; input_is_sexp : bool
     |>`;

val _ = Datatype`compile_error = ParseError | TypeError mlstring | CompileError | ConfigError mlstring`;

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
  (error_to_str (ConfigError s) = concat [strlit "### ERROR: config error\n"; s; strlit "\n"]) /\
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

(* Finds the first occurence of the flag and
  returns the rest of the string after it *)
val find_str_def = Define`
  (find_str flag [] = NONE) ∧
  (find_str flag (x::xs) =
    if isPrefix flag x then
      SOME (extract x (strlen flag) NONE)
    else
      find_str flag xs)`

(* If flag is not present then F, else if it is present then
   we should not get any config string afterwards *)
val find_bool_def = Define`
  find_bool flag ls =
  case find_str flag ls of
    NONE => INL F
  | SOME rest =>
    if rest = strlit "" then INL T
    else INR (concat [strlit"Did not expect the argument: ";rest;strlit " for flag: ";flag])`

(* If flag is not present then INL default, else if it is present then
   the rest of the config string should be a number *)
val find_num_def = Define`
  find_num flag ls default =
  case find_str flag ls of
    NONE => INL default
  | SOME rest =>
  case parse_num rest of
    SOME n => INL n
  | NONE => INR (concat [strlit"Unable to parse as num: ";rest;strlit " for flag: ";flag])`

val get_err_str = Define`
  (get_err_str (INL n) = strlit"") ∧
  (get_err_str (INR n) = concat[n;strlit"\n"])`

(* All the numbers must parse *)
val parse_num_list_def = Define`
  (parse_num_list [] = INL []) /\
  (parse_num_list (x::xs) =
     case parse_num x of
       NONE => INR (concat [strlit"Unable to parse as num: ";x])
     | SOME n =>
       case parse_num_list xs of
         INR s => INR s
       | INL ns => INL (n::ns))`

val comma_tokens_def = Define `
  (comma_tokens acc xs [] = if NULL xs then acc else acc ++ [implode xs]) /\
  (comma_tokens acc (xs:string) (c::(cs:string)) =
    if c = #"," then
      comma_tokens (acc ++ if NULL xs then [] else [implode xs]) [] cs
    else
      comma_tokens acc (STRCAT xs [c]) cs)`


val parse_nums_def = Define `
  parse_nums str = (parse_num_list (comma_tokens [] [] (explode str)))`

(*
  EVAL``find_bool (strlit "--nomul") [strlit "asf";strlit"--nomul"]``
  EVAL``find_bool (strlit "--nomul") [strlit "asf";strlit"--nomul=fdsa"]``
  EVAL``find_num (strlit "--fl") [strlit "asf";strlit"--f1234"] 5n``
*)

(*
  Each of these is a helper function that extends a conf
  It either returns an INL extended_conf or INR error_string
  TODO: use pmatch for this...
*)

(* clos_conf *)
val parse_clos_conf_def = Define`
  parse_clos_conf ls clos =
  let multi = find_bool (strlit"--no_multi") ls in
  let known = find_bool (strlit"--no_known") ls in
  let call = find_bool (strlit"--no_call") ls in
  let maxapp = find_num (strlit "--max_app=") ls clos.max_app in
  case (multi,known,call,maxapp) of
    (INL m,INL k,INL c,INL n) =>
    (INL
      (clos with <|
        do_mti   := ¬m;
        do_known := ¬k;
        do_call  := ¬c;
        max_app  := n
       |>))
  | _ =>
    INR (concat [get_err_str multi;
                 get_err_str known;
                 get_err_str call;
                 get_err_str maxapp])`

(* bvl *)
val parse_bvl_conf_def = Define`
  parse_bvl_conf ls bvl =
  let inlinesz = find_num (strlit "--inline_size=") ls bvl.inline_size_limit in
  let expcut = find_num (strlit "--exp_cut=") ls bvl.exp_cut in
  let splitmain = find_bool (strlit"--no_split") ls in
  case (inlinesz,expcut,splitmain) of
    (INL i,INL e,INL m) =>
    INL
      (bvl with <|
        inline_size_limit := i;
        exp_cut           := e;
        split_main_at_seq := ¬m
      |>)
  | _ =>
    INR (concat [get_err_str inlinesz;
                 get_err_str expcut;
                 get_err_str splitmain])`

(* wtw *)
val parse_wtw_conf_def = Define`
  parse_wtw_conf ls wtw =
  let regalg = find_num (strlit "--reg_alg=") ls wtw.reg_alg in
  case regalg of
    INL r => INL (wtw with <|reg_alg:= r |>)
  | INR s => INR (get_err_str regalg)`

val parse_gc_def = Define`
  parse_gc ls default =
  case find_str (strlit"--gc=") ls of
    NONE => INL default
  | SOME rest =>
    if rest = strlit"none" then INL None
    else if rest = strlit"simple" then INL Simple
    else if isPrefix (strlit "gen") rest then
      case parse_nums (extract rest (strlen (strlit"gen")) NONE) of
        INL ls => INL (Generational ls)
      | INR s =>
        INR (concat [strlit"Error parsing GenGC argument: ";s])
    else INR (concat [strlit"Unrecognized GC option: ";rest])`

(*
EVAL ``parse_gc [strlit "--gc=gen1234,1234,1234"] def``
*)

(* Copy of conf_ok from data_to_word *)
val conf_ok_check_def = Define`
  conf_ok_check (:'a) c <=>
    shift_length c < dimindex (:α) ∧
    shift (:α) ≤ shift_length c ∧ c.len_size ≠ 0 ∧
    c.len_size + 7 < dimindex (:α)`

(* data *)
val parse_data_conf_def = Define`
  parse_data_conf ls data =
  let tag_bits = find_num (strlit "--tag_bits=") ls data.tag_bits in
  let len_bits = find_num (strlit "--len_bits=") ls data.len_bits in
  let pad_bits = find_num (strlit "--pad_bits=") ls data.pad_bits in
  let len_size = find_num (strlit "--len_size=") ls data.len_size in
  let gc = parse_gc ls data.gc_kind in
  case (tag_bits,len_bits,pad_bits,len_size,gc) of
    (INL tb,INL lb,INL pb,INL ls,INL gc) =>
      (* TODO: check conf_ok here and raise error if violated *)
      INL (data with
      <| tag_bits := tb;
         len_bits := lb;
         pad_bits := pb;
         len_size := ls;
         gc_kind  := gc |>)
  | _ =>
     INR (concat [get_err_str tag_bits;
                  get_err_str len_bits;
                  get_err_str pad_bits;
                  get_err_str len_size;
                  get_err_str gc])`

(* stack *)
val parse_stack_conf_def = Define`
  parse_stack_conf ls stack =
  let jump = find_bool (strlit"--no_jump") ls in
  case jump of
    INL j => INL (stack with jump:=¬j)
  | INR s => INR s`

val extend_conf_def = Define`
  extend_conf ls conf =
  let clos = parse_clos_conf ls conf.clos_conf in
  let bvl = parse_bvl_conf ls conf.bvl_conf in
  let wtw = parse_wtw_conf ls conf.word_to_word_conf in
  let data = parse_data_conf ls conf.data_conf in
  let stack = parse_stack_conf ls conf.stack_conf in
  case (clos,bvl,wtw,data,stack) of
    (INL clos,INL bvl,INL wtw,INL data,INL stack) =>
      INL (conf with
        <|clos_conf         := clos;
          bvl_conf          := bvl;
          word_to_word_conf := wtw;
          data_conf         := data;
          stack_conf        := stack|>)
    | _ =>
      INR (concat [get_err_str clos;
               get_err_str bvl;
               get_err_str wtw;
               get_err_str data;
               get_err_str stack]) `

(* Defaults to x64 if no target given *)
val parse_target_64_def = Define`
  parse_target_64 ls =
  case find_str (strlit"--target=") ls of
    NONE => INL (x64_backend_config,x64_export)
  | SOME rest =>
    if rest = strlit"x64" then INL (x64_backend_config,x64_export)
    else if rest = strlit"arm8" then INL (arm8_backend_config,arm8_export)
    else if rest = strlit"mips" then INL (mips_backend_config,mips_export)
    else if rest = strlit"riscv" then INL (riscv_backend_config,riscv_export)
    else INR (concat [strlit"Unrecognized 64-bit target option: ";rest])`

(* Defaults to arm6, currently no other 32-bit architecture*)
val parse_target_32_def = Define`
  parse_target_32 ls =
  case find_str (strlit"--target=") ls of
    NONE => INL (arm6_backend_config,arm6_export)
  | SOME rest =>
    if rest = strlit"arm6" then INL (arm6_backend_config,arm6_export)
    else INR (concat [strlit"Unrecognized 32-bit target option: ";rest])`

(* Default stack and heap limits *)
val default_heap_sz_def = Define`
  default_heap_sz = 1000n`

val default_stack_sz_def = Define`
  default_stack_sz = 1000n`

val parse_top_config_def = Define`
  parse_top_config ls =
  let heap = find_num (strlit"--heap_size=") ls default_heap_sz in
  let stack = find_num (strlit"--stack_size=") ls default_stack_sz in
  let sexp = find_bool (strlit"--sexp") ls in
  case (heap,stack,sexp) of
    (INL heap,INL stack,INL sexp) =>
      INL (heap,stack,sexp)
  | _ => INR (concat [get_err_str heap;
               get_err_str stack;
               get_err_str sexp])`

(* Check for version flag
   TODO: fix this
*)
val has_version_flag_def = Define `
  has_version_flag ls = MEM (strlit"--version") ls`

val format_compiler_result_def = Define`
  format_compiler_result bytes_export (heap:num) (stack:num) (Failure err) =
    (List[]:mlstring app_list, error_to_str err) ∧
  format_compiler_result bytes_export heap stack
    (Success ((bytes:word8 list),(data:'a word list),(c:'a lab_to_target$config))) =
    (bytes_export (the [] c.ffi_names) heap stack bytes data, implode "")`;

(* The top-level compiler with everything instantiated except it doesn't do exporting *)

(* The top-level compiler with almost everything instantiated except the top-level configuration *)
val compile_64_def = Define`
  compile_64 cl input =
  let confexp = parse_target_64 cl in
  let topconf = parse_top_config cl in
  case (confexp,topconf) of
    (INL (conf,export), INL(heap,stack,sexp)) =>
    (let ext_conf = extend_conf cl conf in
    case ext_conf of
      INL ext_conf =>
        let compiler_conf =
          <| inferencer_config := init_config;
             backend_config    := ext_conf;
             input_is_sexp     := sexp |> in
        (case compiler$compile compiler_conf basis input of
          Success (bytes,data,c) =>
            (export (the [] c.ffi_names) heap stack bytes data, implode "")
        | Failure err => (List [],error_to_str err))
    | INR err =>
    (List[],error_to_str (ConfigError (get_err_str ext_conf))))
  | _ =>
    (List[],error_to_str (ConfigError (concat [get_err_str confexp;get_err_str topconf])))`

val compile_32_def = Define`
  compile_32 cl input =
  let confexp = parse_target_32 cl in
  let topconf = parse_top_config cl in
  case (confexp,topconf) of
    (INL (conf,export), INL(heap,stack,sexp)) =>
    (let ext_conf = extend_conf cl conf in
    case ext_conf of
      INL ext_conf =>
        let compiler_conf =
          <| inferencer_config := init_config;
             backend_config    := ext_conf;
             input_is_sexp     := sexp |> in
        (case compiler$compile compiler_conf basis input of
          Success (bytes,data,c) =>
            (export (the [] c.ffi_names) heap stack bytes data, implode "")
        | Failure err => (List [],error_to_str err))
    | INR err =>
    (List[],error_to_str (ConfigError (get_err_str ext_conf))))
  | _ =>
    (List[],error_to_str (ConfigError (concat [get_err_str confexp;get_err_str topconf])))`

val _ = export_theory();
