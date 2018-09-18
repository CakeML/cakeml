open preamble ml_hol_kernelProgTheory
     mlintTheory StringProgTheory
     readerTheory reader_initTheory
     CommandLineProofTheory TextIOProofTheory

val _ = new_theory"readerIO"

val _ = temp_overload_on ("monad_bind", ``st_ex_bind``);
val _ = temp_overload_on ("monad_unitbind", ``\x y. st_ex_bind x (\z. y)``);
val _ = temp_overload_on ("return", ``st_ex_return``);
val _ = temp_overload_on ("failwith", ``raise_Fail``);
val _ = temp_add_monadsyntax()

(* Necessary to compose different monads *)
val _ = Datatype `
  state_refs =
    <| holrefs : hol_refs      (* HOL kernel state *)
     ; stdio   : IO_fs         (* STDIO            *)
     ; cl      : mlstring list (* Commandline args *)
     |>`

(* TODO derive automatically *)
val _ = overload_on("stdio",      ``liftM state_refs_stdio   stdio_fupd``);
val _ = overload_on("holrefs",    ``liftM state_refs_holrefs holrefs_fupd``);
val _ = overload_on("commandline",``liftM state_refs_cl      cl_fupd``);

(* ------------------------------------------------------------------------- *)
(* Wrap the emptyffi call in return.                                         *)
(* ------------------------------------------------------------------------- *)

val ffi_msg_def = Define `
  ffi_msg msg = return (empty_ffi msg)`;

(* ------------------------------------------------------------------------- *)
(* Monadic wrappers for readLine                                             *)
(* ------------------------------------------------------------------------- *)

(* Matching process_line *)

val readLine_wrap_def = Define `
  readLine_wrap (line, s) =
    if invalid_line line then
      return (INR s)
    else
        handle_Fail
          (do s <- readLine (unescape_ml (fix_fun_typ (str_prefix line))) s;
              return (INR s) od)
          (\e. return (INL e))`;

(* Matching process_lines *)

val readLines_def = Define `
  readLines s lines =
    case lines of
      [] =>
        do
          ffi_msg (strlit"finished: readLines");
          ctxt <- holrefs (context ());
          msg <- return (msg_success s ctxt);
          ffi_msg (strlit"finished: generate message");
          stdio (print msg)
        od
    | ln::ls =>
        do
          res <- holrefs (readLine_wrap (ln, s));
          case res of
            INL e =>
                do
                  ffi_msg (strlit"finished: readLines");
                  stdio (print_err (line_Fail s e))
                od
          | INR s => readLines (next_line s) ls
        od`

(* Matching read_file *)

val readFile_def = Define `
  readFile fname =
    do
      ffi_msg (strlit"starting...");
      lines <- stdio (inputLinesFrom fname);
      ffi_msg (strlit"finished: inputLinesFrom");
      case lines of
        NONE => stdio (print_err (msg_bad_name fname))
      | SOME ls => readLines init_state ls
    od`

(* Wrap away the exception *)

val init_reader_wrap_def = Define `
  init_reader_wrap () =
    handle_Fail
      (do
         init_reader ();
         return (INR ())
       od)
      (\e. return (INL e))`;

(* Matching reader_main *)

val readMain_def = Define `
  readMain () =
    do
      args <- commandline (arguments ());
      case args of
        [fname] =>
          do
            res <- holrefs (init_reader_wrap ());
            case res of
              INL e => stdio (print_err (msg_axioms e))
            | INR () => readFile fname
          od
      | _ => stdio (print_err msg_usage)
    od`;

val _ = export_theory()

