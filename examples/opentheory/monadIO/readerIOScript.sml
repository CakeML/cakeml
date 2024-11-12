(*
  The OpenTheory article reader defined using an IO monad for the
  basis library.
*)
open preamble ml_hol_kernelProgTheory
     mlintTheory StringProgTheory
     readerTheory reader_initTheory
     CommandLineProofTheory TextIOProofTheory

val _ = new_theory"readerIO"

Overload monad_bind[local] = ``st_ex_bind``
Overload monad_unitbind[local] = ``\x y. st_ex_bind x (\z. y)``
Overload monad_ignore_bind[local] = ``\x y. st_ex_bind x (\z. y)``
Overload return[local] = ``st_ex_return``
Overload failwith[local] = ``raise_Fail``
val _ = temp_add_monadsyntax()

(* Necessary to compose different monads *)
Datatype:
  state_refs =
    <| holrefs : hol_refs      (* HOL kernel state *)
     ; stdio   : IO_fs         (* STDIO            *)
     ; cl      : mlstring list (* Commandline args *)
     |>
End

(* TODO derive automatically *)
Overload stdio = ``liftM state_refs_stdio stdio_fupd``
Overload holrefs = ``liftM state_refs_holrefs holrefs_fupd``
Overload commandline = ``liftM state_refs_cl cl_fupd``

(* ------------------------------------------------------------------------- *)
(* Wrap the emptyffi call in return.                                         *)
(* ------------------------------------------------------------------------- *)

Definition ffi_msg_def:
  ffi_msg msg = return (empty_ffi msg)
End

(* ------------------------------------------------------------------------- *)
(* Monadic wrappers for readLine                                             *)
(* ------------------------------------------------------------------------- *)

(* Matching process_line *)

Definition readLine_wrap_def:
  readLine_wrap (line, s) =
    if invalid_line line then
      return (INR s)
    else
        handle_Fail
          (do s <- readLine (unescape_ml (fix_fun_typ (str_prefix line))) s;
              return (INR s) od)
          (\e. return (INL e))
End

(* Matching process_lines *)

Definition readLines_def:
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
        od
End

(* Matching read_file *)

Definition readFile_def:
  readFile fname =
    do
      ffi_msg (strlit"starting...");
      lines <- stdio (inputLinesFrom fname);
      ffi_msg (strlit"finished: inputLinesFrom");
      case lines of
        NONE => stdio (print_err (msg_bad_name fname))
      | SOME ls => readLines init_state ls
    od
End

(* Wrap away the exception *)

Definition init_reader_wrap_def:
  init_reader_wrap () =
    handle_Fail
      (do
         init_reader ();
         return (INR ())
       od)
      (\e. return (INL e))
End

(* Matching reader_main *)

Definition readMain_def:
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
    od
End

val _ = export_theory()
