(*
  Definition of the CakeML compiler as a function that takes a list of command
  line arguments and a string corresponding to standard input, and produces a
  pair of output strings for standard error and standard output (the latter
  containing the generated machine code if successful).
*)
Theory compiler
Ancestors
  compiler_common cmlParse infer backend_passes mlint basisProg
  mlsexp ast_sexp
Libs
  preamble

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
                T, where T can be one of x64, arm8, mips, riscv, arm7
                and ag32. The default is x64.

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

  --main_return=B   here B can be either true or false; the default is
                false; setting this to true causes the main function to
                return to caller instead of exit; this option is
                required to use multiple entry points.

ADDITIONAL OPTIONS:

Optimisations can be configured using the following advanced options.

  --jump=B    true means conditional jumps to be used for out-of-stack checks
  --multi=B   true means clos_to_bvl phase is to use multi optimisation
  --known=B   true means clos_to_bvl phase is to use known optimisation
  --call=B    true means clos_to_bvl phase is to use call optimisation
  --tmc=B     true means tail-call modulo cons optimisations is used
  --tailrec=B true means attempts to turn functions into tail-rec form
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
  --perf_callgraph=B  unverified: emit C-stack shadowing so `perf record
                --call-graph fp` produces correct call graphs (x64 only)

’ (* end of --help string *)

(* == Build info =========================================================== *)

val current_version_tm = mlstring_from_proc "git" ["rev-parse", "HEAD"]
(*"*)
val poly_version_tm = mlstring_from_proc "poly" ["-v"]
val hol_version_tm = mlstring_from_proc "git" ["-C", Globals.HOLDIR, "rev-parse", "HEAD"]

val date_str = Date.toString (Date.fromTimeUniv (Time.now ())) ^ " UTC\n"
val date_tm = Term `strlit^(stringSyntax.fromMLstring date_str)`

val current_build_info_str_tm = EVAL ``
    let commit = print_option «CakeML:» ^current_version_tm in
    let hol    = print_option «HOL4:  » ^hol_version_tm in
    let poly   = print_option «PolyML:» ^poly_version_tm in
      concat
        [ «The CakeML compiler\n\n»
        ; «Version details:\n»
        ; ^date_tm; «\n»
        ; commit; hol; poly ]``
  |> concl |> rhs

Definition current_build_info_str_def:
  current_build_info_str = ^current_build_info_str_tm
End

(* ========================================================================= *)

Datatype:
  config =
    <| inferencer_config   : inf_env
     ; backend_config      : backend$config
     ; asm_config          : asm_config
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
End

Definition ast_locs_to_string_def:
  ast_locs_to_string input (SOME (Locs (r1,c1) (r2,c2))) =
    locs_to_string input
      (SOME (location$Locs (POSN (Num (ABS r1)) (Num (ABS c1)))
                           (POSN (Num (ABS r2)) (Num (ABS c2))))) ∧
  ast_locs_to_string input _ = locs_to_string input NONE
End

Definition parse_sexp_input_def:
  parse_sexp_input input =
    let err = «Parsing of sexp syntax failed: » in
      case mlsexp$parse input of
      | INL (perr, _) => INL (err ^ perr)
      | INR (x, _) =>
        case ast_sexp$to_dec_list x of
        | NONE => INL (err ^ «to_dec_list returned NONE»)
        | SOME x => INR x
End

Definition parse_cml_input_def:
  parse_cml_input input =
    case parse_prog (lexer_fun input) of
    | Failure l _ => INL («Parsing failed at » ^ locs_to_string (implode input) (SOME l))
    | Success _ x _ => INR x
End

Definition compile_def:
  compile c prelude input =
    let _ = empty_ffi «finished: start up» in
    case
      if c.input_is_sexp
      then parse_sexp_input input
      else parse_cml_input input
    of
    | INL msg => (M_failure (ParseError msg), Nil)
    | INR prog =>
       let _ = empty_ffi «finished: lexing and parsing» in
       let full_prog = if c.exclude_prelude then prog else prelude ++ prog in
       case
         if c.skip_type_inference
         then M_success c.inferencer_config
         else infertype_prog c.inferencer_config full_prog
       of
       | M_failure (locs, msg) =>
           (M_failure (TypeError (concat [msg; « at »;
               ast_locs_to_string (implode input) locs])), Nil)
       | M_success ic =>
          let _ = empty_ffi «finished: type inference» in
          if c.only_print_types then
            (M_failure (TypeError (concat ([«\n»] ++
                                         inf_env_to_types_string ic ++
                                         [«\n»]))), Nil)
          else if c.only_print_sexp then
            (M_failure (TypeError (
               («\n» ^ sexp_to_string (ast_sexp$from_dec_list full_prog)))),Nil)
          else
          case backend_passes$compile_tap c.asm_config c.backend_config full_prog of
          | (NONE, td) => (M_failure AssembleError, td)
          | (SOME (bytes,data,c), td) => (M_success (bytes,data,c), td)
End

(* The top-level compiler *)
Definition error_to_str_def:
  (error_to_str (ParseError s) =
     concat [«### ERROR: parse error\n»; s; «\n»]) /\
  (error_to_str (TypeError s) =
     (* if the first char in the message is a newline char then it isn't an error *)
     if (if strlen s = 0 then T else
         if strsub s 0 = #"\n" then F else T) then
       concat [«### ERROR: type error\n»; s; «\n»]
     else s) /\
  (error_to_str (ConfigError s) = concat [«### ERROR: config error\n»; s; «\n»]) /\
  (error_to_str AssembleError = «### ERROR: assembly error\n»)
End

Definition parse_top_config_def:
  parse_top_config ls =
  let sexp = find_bool «--sexp=» ls F in
  let prelude = find_bool «--exclude_prelude=» ls F in
  let typeinference = find_bool «--skip_type_inference=» ls F in
  let sexpprint = MEMBER «--print_sexp» ls in
  let onlyprinttypes = MEMBER «--types» ls in
  let mainreturn = find_bool «--main_return=» ls F in
  case (sexp,prelude,typeinference,mainreturn) of
    (INL sexp,INL prelude,INL typeinference,INL mainreturn) =>
      INL (sexp,prelude,typeinference,onlyprinttypes,sexpprint,mainreturn)
  | _ => INR (concat [
               get_err_str sexp;
               get_err_str prelude;
               get_err_str typeinference;
               get_err_str mainreturn])
End

Definition format_compiler_result_def:
  format_compiler_result bytes_export (M_failure err) =
    (List[]:mlstring app_list, error_to_str err) ∧
  format_compiler_result bytes_export
    (M_success ((bytes:word8 list),(data:num list),(c:backend$config))) =
    (bytes_export (the [] c.lab_conf.ffi_names) bytes data, implode "")
End

(* Compile CakeML using command-line options. *)
Definition compile_main_def:
  compile_main cl input =
  let confexp = parse_target cl in
  let topconf = parse_top_config cl in
  case (confexp,topconf) of
    (INL (conf,export,aconf), INL(sexp,prelude,typeinfer,onlyprinttypes,sexpprint,mainret)) =>
    (let ext_conf = extend_conf cl conf in
    case ext_conf of
      INL ext_conf =>
        let compiler_conf =
          <| inferencer_config   := init_config;
             backend_config      := ext_conf;
             asm_config           := aconf;
             input_is_sexp       := sexp;
             exclude_prelude     := prelude;
             skip_type_inference := typeinfer;
             only_print_types    := onlyprinttypes;
             only_print_sexp     := sexpprint;
             |> in
        (case compiler$compile compiler_conf basis input of
          (M_success (bytes,data,c), td) =>
            (add_tap_output td (export
              (ffinames_to_string_list
                $ the [] c.lab_conf.ffi_names)
                bytes data c.symbols c.exported mainret F),
              implode "")
        | (M_failure err, td) => (add_tap_output td (List []), error_to_str err))
    | INR err =>
    (List[], error_to_str (ConfigError (get_err_str ext_conf))))
  | _ =>
    (List[], error_to_str (ConfigError (concat [get_err_str confexp;get_err_str topconf])))
End

Definition full_compile_def:
  full_compile cl inp fs =
  if has_help_flag cl then
    add_stdout fs help_string
  else if has_version_flag cl then
    add_stdout fs current_build_info_str
  else
    let (out, err) = compile_main cl inp in
      add_stderr (add_stdout (fastForwardFD fs 0) (concat (append out))) err
End
