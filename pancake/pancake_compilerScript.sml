(*
  Command-line interface for the standalone Pancake compiler.
*)
Theory pancake_compiler
Ancestors
  compiler_common basis_ffi panPtreeConversion pan_to_target panStatic pan_passes news
Libs
  preamble

Datatype:
  compile_error = ParseError mlstring
                | AssembleError
                | ConfigError mlstring
                | StaticError staterr
End

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
        [ «The Pancake compiler\n\n»
        ; «Version details:\n»
        ; ^date_tm; «\n»
        ; commit; hol; poly ]``
  |> concl |> rhs

Definition current_build_info_str_def:
  current_build_info_str = ^current_build_info_str_tm
End

Definition help_string_def:
  help_string = concat
    [«Usage: pancake [OPTIONS] < input_file > output_file\n»;
     «\n»;
     «Compiles Pancake source to assembly with garbage collection disabled.\n»;
     «\n»;
     «--help                 print this help\n»;
     «--version              print build information\n»;
     «--target=T             x64, arm8, mips, riscv, arm7 or ag32 (default: native)\n»;
     «--pancake_feature=T     query support for feature T (see pancake/NEWS.md)\n»;
     «--no_warn              silence warnings\n»;
     «--main_return=B        return to caller instead of exit (default: false)\n»;
     «--explore              print intermediate compiler forms\n»;
     «--reg_alg=N            register allocator (default: 2)\n»;
     «--jump=B               conditional out-of-stack checks\n»;
     «--hash_size=N          instruction encoder memoization table size\n»;
     «--perf_callgraph=B     C-stack shadowing for perf (x64 only)\n»]
End

Definition error_to_str_def:
  (error_to_str (ParseError s) =
     concat [«### ERROR: parse error\n»; s; «\n»]) /\
  (error_to_str (ConfigError s) = concat [«### ERROR: config error\n»; s; «\n»]) /\
  (error_to_str AssembleError = «### ERROR: assembly error\n») /\
  (error_to_str (StaticError e) =
    case e of
      ScopeErr   s => concat [«### ERROR: scope error\n»;  s; «\n»]
    | WarningErr s => concat [«# WARNING:\n»;              s; «\n»]
    | GenErr     s => concat [«### ERROR: static error\n»; s; «\n»]
    | ShapeErr   s => concat [«### ERROR: shape error\n»;  s; «\n»])
End

Definition compile_pancake_def:
  compile_pancake asm_conf c input =
  let _ = empty_ffi «finished: start up» in
  case panPtreeConversion$parse_topdecs_to_ast input of
  | INR errs =>
    ((M_failure $ ParseError $ concat $
       MAP (λ(msg,loc). concat [msg; « at »;
                                locs_to_string (implode input) (SOME loc); «\n»])
           errs), Nil, [])
  | INL (funs:decl list) =>
      case static_check funs of
      | (error e, warns) => (M_failure $ StaticError e, Nil, MAP StaticError warns)
      | (return (), warns) =>
          let _ = empty_ffi «finished: lexing and parsing» in
          case pan_passes$pan_compile_tap asm_conf c funs of
          | (NONE,td) => (M_failure AssembleError, td, MAP StaticError warns)
          | (SOME (bytes,data:num list,c),td) => (M_success (bytes,data,c), td, MAP StaticError warns)
End

Definition print_bool_def:
  print_bool b = if b then «true» else «false»
End

Definition parse_pancake_feature_def:
  parse_pancake_feature ls =
  case find_str «--pancake_feature=» ls of
    NONE => NONE
  | SOME rest => SOME rest
End

Datatype:
  target = PancakeX64 | PancakeArm8 | PancakeRiscv
End

Definition parse_target_def:
  parse_target native cl =
    compiler_common$parse_target (case native of
      PancakeX64 => cl
    | PancakeArm8 => cl ++ [«--target=arm8»]
    | PancakeRiscv => cl ++ [«--target=riscv»])
End

Definition extend_conf_def:
  extend_conf cl conf =
    case compiler_common$extend_conf cl conf of
      INR err => INR err
    | INL c => INL (c with data_conf := (c.data_conf with gc_kind := None))
End

Definition compile_main_def:
  compile_main native cl input =
    let confexp = parse_target native cl in
    let mainret = find_bool «--main_return=» cl F in
    let nowarn = MEM «--no_warn» cl in
    case (confexp,mainret) of
      (INL (conf,export,aconf),INL mainret) =>
        (case extend_conf cl conf of
          INR err => (List [], error_to_str (ConfigError err))
        | INL ext_conf =>
            case compile_pancake aconf ext_conf input of
              (M_failure err,td,warns) =>
                (List [], concat (MAP error_to_str
                  (err::(if nowarn then [] else warns))))
            | (M_success (bytes,data,c),td,warns) =>
                (add_tap_output td
                  (export (ffinames_to_string_list (the [] c.lab_conf.ffi_names))
                    bytes data c.symbols c.exported mainret T),
                 concat (MAP error_to_str (if nowarn then [] else warns))))
    | _ => (List [], error_to_str (ConfigError
             (concat [get_err_str confexp; get_err_str mainret])))
End

Definition full_compile_def:
  full_compile native cl inp fs =
    if has_help_flag cl then add_stdout fs help_string
    else if has_version_flag cl then add_stdout fs current_build_info_str
    else case parse_pancake_feature cl of
      SOME feature => add_stdout fs (print_bool (query_news feature))
    | NONE =>
        let (out,err) = compile_main native cl inp in
          add_stderr (add_stdout (fastForwardFD fs 0) (concat (append out))) err
End

Theorem full_compile_with_numchars:
  pancake_compiler$full_compile native cl inp (fs with numchars := ns) =
  pancake_compiler$full_compile native cl inp fs with numchars := ns
Proof
  rw [full_compile_def,UNCURRY,fsFFIPropsTheory.fastForwardFD_with_numchars,
      TextIOProofTheory.add_stdo_with_numchars]
  \\ Cases_on `parse_pancake_feature cl`
  \\ simp []
QED
