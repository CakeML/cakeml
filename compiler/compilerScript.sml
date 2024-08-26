(*
  Definition of the CakeML compiler as a function that takes a list of command
  line arguments and a string corresponding to standard input, and produces a
  pair of output strings for standard error and standard output (the latter
  containing the generated machine code if successful).
*)
open preamble
     lexer_funTheory lexer_implTheory
     cmlParseTheory
     inferTheory
     backendTheory backend_passesTheory
     mlintTheory mlstringTheory basisProgTheory
     fromSexpTheory simpleSexpParseTheory

open x64_configTheory export_x64Theory
open arm8_configTheory export_arm8Theory
open riscv_configTheory export_riscvTheory
open mips_configTheory export_mipsTheory
open arm7_configTheory export_arm7Theory
open ag32_configTheory export_ag32Theory
open panPtreeConversionTheory pan_to_targetTheory panScopeTheory pan_passesTheory

val _ = new_theory"compiler";

val help_string = (* beginning of --help string *) ‘

Usage:  cake [OPTIONS] < input_file > output_file

The cake executable is usually invoked as shown above. The different
OPTIONS are described in the OPTIONS listing below.

One can also run the cake execuable as follows to print a listing of
the type of each top-level binding (including the bindings made in
the standard basis library).

Usage:  cake --types < input_file

One can invoke the cake executable to print this help message (--help)
or version information (--version) without an input_file:

Usage:  cake --version
Usage:  cake --help

OPTIONS:

  --repl        starts an interactive read-eval-print loop; all other
                flags are ignored, when the --repl flag is present

  --reg_alg=N   N is a natural number that specifies the register
                allocation algorithm to use:
                   0   - simple allocator, no spill heuristics
                   1   - simple allocator, spill heuristics
                   2   - IRC allocator, no spill heuristics (default)
                   3   - IRC allocator, spill heuristics
                   >=4 - linear scan allocator

  --gc=G        specifies garbage collector type; here G is one of:
                   none   - no garbage collector is used
                   simple - a non-generational Cheney (default)
                   genN   - a generational Cheney garbage collector is
                            used; the size of the nursery generation is
                            N machine words (example: --gc=gen5000)

  --target=T    specifies that compilation should produce code for target
                T, where T can be one of x64, arm8, mips, riscv for
                the 64-bit compiler; for the 32-bit compiler T can be
                one of arm7 and ag32.

  --sexp=B      B can be either true or false; here false means that the
                input will be parsed as normal CakeML concrete syntax;
                true means that the input is parsed as an s-expression.

  --print_sexp  causes the cake to print the given program in
                s-expression format; with this option, the compiler
                does not generate machine code.

  --exclude_prelude=B   here B can be either true or false; the default
                is false; setting this to true causes the compiler not
                to include the standard basis library.

  --skip_type_inference=B   here B can be either true or false; the
                default is false; true will make the compiler skip
                type inference. There are no gurantees of safety if
                the type inferencer is skipped.

  --explore     outputs intermediate forms of the compiled program

  --pancake     takes a pancake program as input

  --main_return=B   here B can be either true or false; the default is
                false; setting this to true causes the main function to
                return to caller instead of exit; this option is
                required to use multiple entry points with Pancake.

ADDITIONAL OPTIONS:

Optimisations can be configured using the following advanced options.

  --jump=B   true means conditional jumps to be used for out-of-stack checks
  --multi=B  true means clos_to_bvl phase is to use multi optimisation
  --known=B  true means clos_to_bvl phase is to use known optimisation
  --call=B   true means clos_to_bvl phase is to use call optimisation
  --inline_factor=N  threshold used by for ClosLang inliner in known pass
  --max_body_size=N  threshold used by for ClosLang inliner in known pass
  --max_app=N   max number of optimised curried applications in multi pass
  --inline_size=N  threshold used by for BVL inliner pass
  --exp_cut=N  threshold for when to cut large expression into subfunctions
  --split=B  true means main expression will be split at sequencing (;)
  --tag_bits=N  number of tag bits in every pointer
  --len_bits=N  number of length bits in every pointer
  --pad_bits=N  number of zero padding in every pointer
  --len_size=N  size of length field in heap object header cells
  --emit_empty_ffi=B  true emits debugging FFI calls for use with DEBUG_FFI
  --hash_size=N  size of the memoization table used by instruction encoder

’ (* end of --help string *)

(* == Build info =========================================================== *)

val current_version_tm = mlstring_from_proc "git" ["rev-parse", "HEAD"]
(*"*)
val poly_version_tm = mlstring_from_proc "poly" ["-v"]
val hol_version_tm = mlstring_from_proc "git" ["-C", Globals.HOLDIR, "rev-parse", "HEAD"]

val date_str = Date.toString (Date.fromTimeUniv (Time.now ())) ^ " UTC\n"
val date_tm = Term `strlit^(stringSyntax.fromMLstring date_str)`

Definition print_option_def:
  print_option h x =
    case x of
      NONE => strlit""
    | SOME y => h ^ strlit" " ^ y ^ strlit"\n"
End

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

Definition current_build_info_str_def:
  current_build_info_str = ^current_build_info_str_tm
End

(* ========================================================================= *)

Datatype:
  config =
    <| inferencer_config : inf_env
     ; backend_config : α backend$config
     ; input_is_sexp       : bool
     ; exclude_prelude     : bool
     ; skip_type_inference : bool
     ; only_print_types    : bool
     ; only_print_sexp     : bool
     |>
End

fun drop_until p [] = []
  | drop_until p (x::xs) = if p x then x::xs else drop_until p xs;

val help_string_tm =
  help_string |> hd |> (fn QUOTE s => s) |> explode
  |> drop_until (fn c => c = #"\n") |> tl |> implode
  |> stringSyntax.fromMLstring;

Definition help_string_def:
  help_string = strlit ^help_string_tm
End

Datatype:
  compile_error = ParseError mlstring
                | TypeError mlstring
                | AssembleError
                | ConfigError mlstring
                | ScopeError unbound
                | WarningError mlstring
                (* | ShapeError mlstring
                | StaticError mlstring *)
End

Definition find_next_newline_def:
  find_next_newline n s =
    if strlen s ≤ n then n else
      if strsub s n = #"\n" then n else
        find_next_newline (n+1) s
Termination
  WF_REL_TAC ‘measure (λ(n,s). strlen s - n)’
End

Definition safe_substring_def:
  safe_substring s n l =
    let k = strlen s in
      if k ≤ n then strlit "" else
        if n + l ≤ k then
          substring s n l
        else substring s n (k - n)
End

Definition get_nth_line_def:
  get_nth_line k s n =
    if k = 0 then
      let n1 = find_next_newline n s in
        safe_substring s n (n1 - n)
    else
      get_nth_line (k-1:num) s (find_next_newline n s + 1)
End

Definition locs_to_string_def:
  (locs_to_string input NONE = implode "unknown location") ∧
  (locs_to_string input (SOME (Locs startl endl)) =
    case startl of
    | POSN r c =>
       (let line = get_nth_line r input 0 in
        let len = strlen line in
        let stop =
          (case endl of POSN r1 c1 => (if r1 = r then c1 else len) | _ => len) in
        let underline =
          concat (REPLICATE c (strlit " ") ++ REPLICATE ((stop - c) + 1) (strlit [CHR 94])) in
          concat [strlit "line "; toString (r+1); strlit "\n\n";
                  line; strlit "\n";
                  underline;  strlit "\n"])
    | _ => implode "unknown location")
End

(* this is a rather annoying feature of peg_exec requiring locs... *)
Overload add_locs = ``MAP (λc. (c,unknown_loc))``

Definition parse_sexp_input_def:
  parse_sexp_input input =
    let err = strlit "Parsing of sexp syntax failed" in
      case parse_sexp (add_locs input) of
      | NONE => INL err
      | SOME x => case sexplist sexpdec x of
                  | NONE => INL err
                  | SOME x => INR x
End

Definition parse_cml_input_def:
  parse_cml_input input =
    case parse_prog (lexer_fun input) of
    | Failure l _ => INL (strlit "Parsing failed at " ^ locs_to_string (implode input) (SOME l))
    | Success _ x _ => INR x
End

Definition compile_def:
  compile c prelude input =
    let _ = empty_ffi (strlit "finished: start up") in
    case
      if c.input_is_sexp
      then parse_sexp_input input
      else parse_cml_input input
    of
    | INL msg => (Failure (ParseError msg), Nil)
    | INR prog =>
       let _ = empty_ffi (strlit "finished: lexing and parsing") in
       let full_prog = if c.exclude_prelude then prog else prelude ++ prog in
       case
         if c.skip_type_inference
         then Success c.inferencer_config
         else infertype_prog c.inferencer_config full_prog
       of
       | Failure (locs, msg) =>
           (Failure (TypeError (concat [msg; implode " at ";
               locs_to_string (implode input) locs])), Nil)
       | Success ic =>
          let _ = empty_ffi (strlit "finished: type inference") in
          if c.only_print_types then
            (Failure (TypeError (concat ([strlit "\n"] ++
                                         inf_env_to_types_string ic ++
                                         [strlit "\n"]))), Nil)
          else if c.only_print_sexp then
            (Failure (TypeError (implode(print_sexp (listsexp (MAP decsexp full_prog))))),Nil)
          else
          case backend_passes$compile_tap c.backend_config full_prog of
          | (NONE, td) => (Failure AssembleError, td)
          | (SOME (bytes,data,c), td) => (Success (bytes,data,c), td)
End

Definition compile_pancake_def:
  compile_pancake c input =
  let _ = empty_ffi (strlit "finished: start up") in
  case panPtreeConversion$parse_funs_to_ast input of
  | INR errs =>
    ((Failure $ ParseError $ concat $
       MAP (λ(msg,loc). concat [msg; strlit " at ";
                                locs_to_string (implode input) (SOME loc); strlit "\n"])
           errs), Nil, [])
  | INL funs =>
      case scope_check funs of
      | (error unb, warn_strs) => (Failure (ScopeError unb),Nil, MAP WarningError warn_strs)
      | (return (), warn_strs) =>
          let _ = empty_ffi (strlit "finished: lexing and parsing") in
          case pan_passes$pan_compile_tap c funs of
          | (NONE,td) => (Failure AssembleError,td, MAP WarningError warn_strs)
          | (SOME (bytes,data,c),td) => (Success (bytes,data,c),td, MAP WarningError warn_strs)
End

(* The top-level compiler *)
Definition error_to_str_def:
  (error_to_str (ParseError s) =
     concat [strlit "### ERROR: parse error\n"; s; strlit "\n"]) /\
  (error_to_str (TypeError s) =
     (* if the first char in the message is a newline char then it isn't an error *)
     if (if strlen s = 0 then T else
         if strsub s 0 = #"\n" then F else T) then
       concat [strlit "### ERROR: type error\n"; s; strlit "\n"]
     else s) /\
  (error_to_str (ConfigError s) = concat [strlit "### ERROR: config error\n"; s; strlit "\n"]) /\
  (error_to_str AssembleError = strlit "### ERROR: assembly error\n") /\
  (error_to_str (ScopeError unb) =
    case unb of
    | UnbVar v fname =>
      concat [strlit "### ERROR: scope error\nvariable "; v; strlit " is not in scope in "; fname; strlit "\n"]
    | UnbFunc f fname =>
      concat [strlit "### ERROR: scope error\nfunction "; f; strlit " is not in scope in "; fname; strlit "\n"]) /\
  (error_to_str (WarningError s) = concat [strlit "### WARNING:\n"; s; strlit "\n"])
End

Definition is_error_msg_def:
  is_error_msg x = mlstring$isPrefix (strlit "###") x
End

(* TODO: translator fails inside mlstringLib.mlstring_case_conv
  when the following definition just matches against (strlit str) directly *)
Definition parse_num_def:
  parse_num str =
  let str = explode str in
  if EVERY isDigit str
  then
    SOME (num_from_dec_string_alt str)
  else NONE
End

Definition parse_bool_def:
  parse_bool str =
  if str = strlit "true" then SOME T
  else if str = strlit "false" then SOME F
  else NONE
End

(* Finds the first occurence of the flag and
  returns the rest of the string after it *)
Definition find_str_def:
  (find_str flag [] = NONE) ∧
  (find_str flag (x::xs) =
    if isPrefix flag x then
      SOME (extract x (strlen flag) NONE)
    else
      find_str flag xs)
End

(* Finds all occurences of the flag as a prefix, returning
   the remainder in each occurence. *)
Definition find_strs_def:
  (find_strs flag [] = []) /\
  (find_strs flag (x::xs) =
    if isPrefix flag x then
      (extract x (strlen flag) NONE) :: find_strs flag xs
    else
      find_strs flag xs)
End

(* If flag is not present then F, else if it is present then
   we should not get any config string afterwards *)
Definition find_bool_def:
  find_bool flag ls default =
  case find_str flag ls of
    NONE => INL default
  | SOME rest =>
    case parse_bool rest of
      SOME b => INL b
    | NONE => INR (concat [strlit"Unable to parse as bool: ";rest;strlit " for flag: ";flag])
End

(* If flag is not present then INL default, else if it is present then
   the rest of the config string should be a number *)
Definition find_num_def:
  find_num flag ls default =
  case find_str flag ls of
    NONE => INL default
  | SOME rest =>
  case parse_num rest of
    SOME n => INL n
  | NONE => INR (concat [strlit"Unable to parse as num: ";rest;strlit " for flag: ";flag])
End

Definition get_err_str_def:
  (get_err_str (INL n) = strlit"") ∧
  (get_err_str (INR n) = concat[n;strlit"\n"])
End

(* All the numbers must parse *)
Definition parse_num_list_def:
  (parse_num_list [] = INL []) /\
  (parse_num_list (x::xs) =
     case parse_num x of
       NONE => INR (concat [strlit"Unable to parse as num: ";x])
     | SOME n =>
       case parse_num_list xs of
         INR s => INR s
       | INL ns => INL (n::ns))
End

Definition comma_tokens_def:
  (comma_tokens acc xs [] = if NULL xs then acc else acc ++ [implode xs]) /\
  (comma_tokens acc (xs:string) (c::(cs:string)) =
    if c = #"," then
      comma_tokens (acc ++ if NULL xs then [] else [implode xs]) [] cs
    else
      comma_tokens acc (STRCAT xs [c]) cs)
End


Definition parse_nums_def:
  parse_nums str = (parse_num_list (comma_tokens [] [] (explode str)))
End

(*
  EVAL``find_bool (strlit "--mul=") [strlit "asf";strlit"--mul=fse"] F``
  EVAL``find_bool (strlit "--nomul") [strlit "asf";strlit"--nomul=fdsa"] T``
  EVAL``find_num (strlit "--fl") [strlit "asf";strlit"--f1234"] 5n``
*)

(*
  Each of these is a helper function that extends a conf
  It either returns an INL extended_conf or INR error_string
  TODO: use pmatch for this...
*)

(* clos_conf *)
Definition parse_clos_conf_def:
  parse_clos_conf ls clos =
  let multi = find_bool (strlit"--multi=") ls clos.do_mti in
  let known = find_bool (strlit"--known=") ls (IS_SOME clos.known_conf) in
  let inline_factor = find_num (strlit"--inline_factor=") ls default_inline_factor in
  let call = find_bool (strlit"--call=") ls clos.do_call in
  let maxapp = find_num (strlit "--max_app=") ls clos.max_app in
  case (multi,known,inline_factor,call,maxapp) of
    (INL m,INL k,INL i,INL c,INL n) =>
    if k then
    (let max_body_size = find_num (strlit"--max_body_size=") ls (default_max_body_size n i) in
     case max_body_size of
      (INL x) =>
      INL
        (clos with <|
          do_mti   := m;
          known_conf := SOME (clos_known$mk_config x i);
          do_call  := c;
          max_app  := n
         |>)
      | _ => INR (concat [get_err_str max_body_size]))
    else
    (INL
      (clos with <|
        do_mti   := m;
        known_conf := NONE;
        do_call  := c;
        max_app  := n
       |>))
  | _ =>
    INR (concat [get_err_str multi;
                 get_err_str known;
                 get_err_str inline_factor;
                 get_err_str call;
                 get_err_str maxapp])
End

(* bvl *)
Definition parse_bvl_conf_def:
  parse_bvl_conf ls bvl =
  let inlinesz = find_num (strlit "--inline_size=") ls bvl.inline_size_limit in
  let expcut = find_num (strlit "--exp_cut=") ls bvl.exp_cut in
  let splitmain = find_bool (strlit"--split=") ls bvl.split_main_at_seq in
  case (inlinesz,expcut,splitmain) of
    (INL i,INL e,INL m) =>
    INL
      (bvl with <|
        inline_size_limit := i;
        exp_cut           := e;
        split_main_at_seq := m
      |>)
  | _ =>
    INR (concat [get_err_str inlinesz;
                 get_err_str expcut;
                 get_err_str splitmain])
End

(* wtw *)
Definition parse_wtw_conf_def:
  parse_wtw_conf ls wtw =
    let regalg = find_num (strlit "--reg_alg=") ls wtw.reg_alg in
      case regalg of
        INL r => INL (wtw with <|reg_alg:= r |>)
      | INR s => INR (get_err_str regalg)
End

Definition parse_gc_def:
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
    else INR (concat [strlit"Unrecognized GC option: ";rest])
End

(*
EVAL ``parse_gc [strlit "--gc=gen1234,1234,1234"] def``
*)

(* Copy of conf_ok from data_to_word *)
Definition conf_ok_check_def:
  conf_ok_check (:'a) c <=>
    shift_length c < dimindex (:α) ∧
    shift (:α) ≤ shift_length c ∧ c.len_size ≠ 0 ∧
    c.len_size + 7 < dimindex (:α)
End

(* data *)
Definition parse_data_conf_def:
  parse_data_conf ls data =
  let tag_bits = find_num (strlit "--tag_bits=") ls data.tag_bits in
  let len_bits = find_num (strlit "--len_bits=") ls data.len_bits in
  let pad_bits = find_num (strlit "--pad_bits=") ls data.pad_bits in
  let len_size = find_num (strlit "--len_size=") ls data.len_size in
  let empty_FFI= find_bool (strlit"--emit_empty_ffi=") ls data.call_empty_ffi in
  let gc = parse_gc ls data.gc_kind in
  case (tag_bits,len_bits,pad_bits,len_size,gc,empty_FFI) of
    (INL tb,INL lb,INL pb,INL ls,INL gc, INL empty_FFI) =>
      (* TODO: check conf_ok here and raise error if violated *)
      INL (data with
      <| tag_bits := tb;
         len_bits := lb;
         pad_bits := pb;
         len_size := ls;
         gc_kind  := gc;
         call_empty_ffi := empty_FFI |>)
  | _ =>
     INR (concat [get_err_str tag_bits;
                  get_err_str len_bits;
                  get_err_str pad_bits;
                  get_err_str len_size;
                  get_err_str gc;
                  get_err_str empty_FFI])
End

(* stack *)
Definition parse_stack_conf_def:
  parse_stack_conf ls stack =
  let jump = find_bool (strlit"--jump=") ls stack.jump in
  case jump of
    INL j => INL (stack with jump:=j)
  | INR s => INR s
End

(* tap *)
Definition parse_tap_conf_def:
  parse_tap_conf ls stack =
    INL (<| explore_flag := MEMBER (strlit"--explore") ls |>)
End

(* lab *)
Definition parse_lab_conf_def:
  parse_lab_conf ls lab =
    let hs = find_num (strlit "--hash_size=") ls lab.hash_size in
      case hs of
        INL r => INL (lab with <|hash_size := r |>)
      | INR s => INR s
End

Definition extend_conf_def:
  extend_conf ls conf =
  let clos = parse_clos_conf ls conf.clos_conf in
  let bvl = parse_bvl_conf ls conf.bvl_conf in
  let wtw = parse_wtw_conf ls conf.word_to_word_conf in
  let data = parse_data_conf ls conf.data_conf in
  let stack = parse_stack_conf ls conf.stack_conf in
  let tap = parse_tap_conf ls conf.tap_conf in
  let lab = parse_lab_conf ls conf.lab_conf in
  case (clos,bvl,wtw,data,stack,tap,lab) of
    (INL clos,INL bvl,INL wtw,INL data,INL stack,INL tap, INL lab) =>
      INL (conf with
        <|clos_conf         := clos;
          bvl_conf          := bvl;
          word_to_word_conf := wtw;
          data_conf         := data;
          stack_conf        := stack;
          tap_conf          := tap;
          lab_conf          := lab|>)
    | _ =>
      INR (concat [get_err_str clos;
               get_err_str bvl;
               get_err_str wtw;
               get_err_str data;
               get_err_str stack;
               get_err_str tap;
               get_err_str lab])
End

(* Defaults to x64 if no target given *)
Definition parse_target_64_def:
  parse_target_64 ls =
  case find_str (strlit"--target=") ls of
    NONE => INL (x64_backend_config,x64_export)
  | SOME rest =>
    if rest = strlit"x64" then INL (x64_backend_config,x64_export)
    else if rest = strlit"arm8" then INL (arm8_backend_config,arm8_export)
    else if rest = strlit"mips" then INL (mips_backend_config,mips_export)
    else if rest = strlit"riscv" then INL (riscv_backend_config,riscv_export)
    else INR (concat [strlit"Unrecognized 64-bit target option: ";rest])
End

(* Defaults to arm7 if no target given *)
Definition parse_target_32_def:
  parse_target_32 ls =
  case find_str (strlit"--target=") ls of
    NONE => INL (arm7_backend_config,arm7_export)
  | SOME rest =>
    if rest = strlit"arm7" then INL (arm7_backend_config,arm7_export)
    else if rest = strlit"ag32" then INL (ag32_backend_config,ag32_export)
    else INR (concat [strlit"Unrecognized 32-bit target option: ";rest])
End

Definition parse_top_config_def:
  parse_top_config ls =
  let sexp = find_bool (strlit"--sexp=") ls F in
  let prelude = find_bool (strlit"--exclude_prelude=") ls F in
  let typeinference = find_bool (strlit"--skip_type_inference=") ls F in
  let sexpprint = MEMBER (strlit"--print_sexp") ls in
  let onlyprinttypes = MEMBER (strlit"--types") ls in
  let mainreturn = find_bool (strlit"--main_return=") ls F in
  case (sexp,prelude,typeinference,mainreturn) of
    (INL sexp,INL prelude,INL typeinference,INL mainreturn) =>
      INL (sexp,prelude,typeinference,onlyprinttypes,sexpprint,mainreturn)
  | _ => INR (concat [
               get_err_str sexp;
               get_err_str prelude;
               get_err_str typeinference;
               get_err_str mainreturn])
End

(* Check for version flag *)
Definition has_version_flag_def:
  has_version_flag ls = MEM (strlit"--version") ls
End

(* Check for version help *)
Definition has_help_flag_def:
  has_help_flag ls = MEM (strlit"--help") ls
End

(* Check for pancake flag *)
Definition has_pancake_flag_def:
  has_pancake_flag ls = MEM (strlit"--pancake") ls
End

Definition format_compiler_result_def:
  format_compiler_result bytes_export (Failure err) =
    (List[]:mlstring app_list, error_to_str err) ∧
  format_compiler_result bytes_export
    (Success ((bytes:word8 list),(data:'a word list),(c:'a backend$config))) =
    (bytes_export (the [] c.lab_conf.ffi_names) bytes data, implode "")
End

(* FIXME TODO: this is an awful workaround to avoid implementing a file writer
   right now. *)
Definition add_tap_output_def:
  add_tap_output td out =
    if td = Nil then out else td :mlstring app_list
End

(* The top-level compiler with everything instantiated except it doesn't do exporting *)

(* The top-level compiler with almost everything instantiated except the top-level configuration *)
Definition compile_64_def:
  compile_64 cl input =
  let confexp = parse_target_64 cl in
  let topconf = parse_top_config cl in
  case (confexp,topconf) of
    (INL (conf,export), INL(sexp,prelude,typeinfer,onlyprinttypes,sexpprint,mainret)) =>
    (let ext_conf = extend_conf cl conf in
    case ext_conf of
      INL ext_conf =>
        let compiler_conf =
          <| inferencer_config   := init_config;
             backend_config      := ext_conf;
             input_is_sexp       := sexp;
             exclude_prelude     := prelude;
             skip_type_inference := typeinfer;
             only_print_types    := onlyprinttypes;
             only_print_sexp     := sexpprint;
             |> in
        (case compiler$compile compiler_conf basis input of
          (Success (bytes,data,c), td) =>
            (add_tap_output td (export
              (ffinames_to_string_list
                $ the [] c.lab_conf.ffi_names)
                bytes data c.symbols c.exported mainret F),
              implode "")
        | (Failure err, td) => (add_tap_output td (List []), error_to_str err))
    | INR err =>
    (List[], error_to_str (ConfigError (get_err_str ext_conf))))
  | _ =>
    (List[], error_to_str (ConfigError (concat [get_err_str confexp;get_err_str topconf])))
End

Definition compile_pancake_64_def:
  compile_pancake_64 cl input =
  let confexp = parse_target_64 cl in
  case confexp of
  | INR err => (List[], error_to_str (ConfigError err))
  | INL (conf, export) =>
      let topconf = parse_top_config cl in
      case (topconf) of
      | INR err => (List[], error_to_str (ConfigError err))
      | INL (sexp,prelude,typeinfer,onlyprinttypes,sexpprint,mainret) =>
          let ext_conf = extend_conf cl conf in
          case ext_conf of
          | INR err =>
              (List[], error_to_str (ConfigError (get_err_str ext_conf)))
          | INL ext_conf =>
              case compiler$compile_pancake ext_conf input of
              | (Failure err, td, warns) =>
                  (List[], concat (MAP error_to_str (err::warns)))
              | (Success (bytes, data, c), td, warns) =>
                  (add_tap_output td
                    (export (ffinames_to_string_list $
                      the [] c.lab_conf.ffi_names) bytes data c.symbols
                      c.exported mainret T),
                   concat (MAP error_to_str warns))
End

Definition full_compile_64_def:
  full_compile_64 cl inp fs =
  if has_help_flag cl then
    add_stdout fs help_string
  else if has_version_flag cl then
    add_stdout fs current_build_info_str
  else
    let (out, err) =
        if has_pancake_flag cl then
          compile_pancake_64 cl inp
        else
          compile_64 cl inp
    in
      add_stderr (add_stdout (fastForwardFD fs 0) (concat (append out))) err
End

Definition compile_32_def:
  compile_32 cl input =
  let confexp = parse_target_32 cl in
  let topconf = parse_top_config cl in
  case (confexp,topconf) of
    (INL (conf,export), INL(sexp,prelude,typeinfer,onlyprinttypes,sexpprint,mainret)) =>
    (let ext_conf = extend_conf cl conf in
    case ext_conf of
      INL ext_conf =>
        let compiler_conf =
          <| inferencer_config   := init_config;
             backend_config      := ext_conf;
             input_is_sexp       := sexp;
             exclude_prelude     := prelude;
             skip_type_inference := typeinfer;
             only_print_types    := onlyprinttypes;
             only_print_sexp     := sexpprint;
             |> in
        (case compiler$compile compiler_conf basis input of
          (Success (bytes,data,c), td) =>
            (add_tap_output td (export
              (ffinames_to_string_list $
                the [] c.lab_conf.ffi_names)
                bytes data c.symbols c.exported mainret F),
              implode "")
        | (Failure err, td) => (List [], error_to_str err))
    | INR err =>
    (List[], error_to_str (ConfigError (get_err_str ext_conf))))
  | _ =>
    (List[], error_to_str (ConfigError (concat [get_err_str confexp;get_err_str topconf])))
End

Definition compile_pancake_32_def:
  compile_pancake_32 cl input =
  let confexp = parse_target_32 cl in
  case confexp of
  | INR err => (List[], error_to_str (ConfigError err))
  | INL (conf, export) =>
      let topconf = parse_top_config cl in
      case (topconf) of
      | INR err => (List[], error_to_str (ConfigError err))
      | INL (sexp,prelude,typeinfer,onlyprinttypes,sexpprint,mainret) =>
          let ext_conf = extend_conf cl conf in
          case ext_conf of
          | INR err =>
              (List[], error_to_str (ConfigError (get_err_str ext_conf)))
          | INL ext_conf =>
              case compiler$compile_pancake ext_conf input of
              | (Failure err, td, warns) =>
                  (List[], concat (MAP error_to_str (err::warns)))
              | (Success (bytes, data, c), td, warns) =>
                  (add_tap_output td
                    (export (ffinames_to_string_list $
                      the [] c.lab_conf.ffi_names) bytes data c.symbols
                      c.exported mainret T),
                   concat (MAP error_to_str warns))
End

Definition full_compile_32_def:
  full_compile_32 cl inp fs =
  if has_help_flag cl then
    add_stdout fs help_string
  else if has_version_flag cl then
    add_stdout fs current_build_info_str
  else
    let (out, err) =
        if has_pancake_flag cl then
          compile_pancake_32 cl inp
        else
          compile_32 cl inp
    in
      add_stderr (add_stdout (fastForwardFD fs 0) (concat (append out))) err
End

val _ = export_theory();
