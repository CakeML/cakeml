open preamble ml_hol_kernelProgTheory
     mlintTheory StringProgTheory
     readerTheory

val _ = new_theory"readerIO"

val _ = temp_overload_on ("monad_bind", ``st_ex_bind``);
val _ = temp_overload_on ("monad_unitbind", ``\x y. st_ex_bind x (\z. y)``);
val _ = temp_overload_on ("monad_ignore_bind", ``\x y. st_ex_bind x (\z. y)``);
val _ = temp_overload_on ("return", ``st_ex_return``);
val _ = temp_overload_on ("failwith", ``raise_Fail``);
val _ = temp_add_monadsyntax()

(* Lifting between different state-exception monads *)
(* TODO this will be defined elsewhere on another branch *)
val liftM = Define `
  liftM (read:'d->'a) write (op: ('a,'b,'c) M) =
    (λstate. let (ret,new) = op (read state) in
               (ret, write (K new) state))`;

(* Necessary to compose different monads *)
val _ = Datatype `
  state_refs =
    <| holrefs : hol_refs      (* HOL kernel state *)
     ; stdio   : IO_fs         (* STDIO            *)
     ; cl      : mlstring list (* Commandline args *)
     |>`

(* TODO derive automatically *)
val _ = overload_on("stdio",``liftM state_refs_stdio stdio_fupd``);
val _ = overload_on("holrefs",``liftM state_refs_holrefs holrefs_fupd``);
val _ = overload_on("cl",``liftM state_refs_cl cl_fupd``);

(* ------------------------------------------------------------------------- *)
(* Lifted operations                                                         *)
(* ------------------------------------------------------------------------- *)

(* These are defined to match their CF specs *)

val print_err_def = Define `
  print_err s = (\fs. (Success (), add_stderr fs s))`;

val print_def = Define `
  print s = (\fs. (Success (), add_stdout fs s))`;

val inputLine_def = Define `
  inputLine fd = (\fs. (Success (OPTION_MAP implode (lineFD fs fd)),
                  lineForwardFD fs fd))`;

(* TODO fix *)
val inputLinesFrom_def = Define `
  inputLinesFrom fname = (\fs. (Success ([]: mlstring list), fs))`;

val getArgs_def = Define `
  getArgs = (\cmdl. (Success (TL cmdl), cmdl))`;

(* ------------------------------------------------------------------------- *)
(* Monadic wrappers for readLine                                             *)
(* ------------------------------------------------------------------------- *)

(* Wrapper to get rid of the exceptions *)
val readLine_wrap_def = Define `
  readLine_wrap line s =
    handle_Fail
      (do s <- readLine line s;
          return (INR s) od)
      (\e. return (INL (line_Fail s e)))`;

(* Read all lines in the file, stop on errors. *)
val readLines_def = Define `
  readLines s lines =
    case lines of
      [] => return (INR s)
    | l::ls =>
      do
        if invalid_line l then
          readLines (next_line s) ls
        else
          do
            res <- holrefs (readLine_wrap l s);
            case res of
              INR s => readLines (next_line s) ls
            | INL e => do
                         stdio (print_err e);
                         return (INL s)
                       od
          od
      od`

(* ------------------------------------------------------------------------- *)
(* Monadic program entry-point                                               *)
(* ------------------------------------------------------------------------- *)

val reader_main_def = Define `
  reader_main () =
    do
      args <- cl getArgs;
      case args of
        [fname] =>
          do
            lines <- stdio (inputLinesFrom fname);
            holrefs (set_reader_ctxt ());
            res <- readLines init_state lines;
            case res of
              INL _ => return ()
            | INR s =>
                stdio (print
                  (concat [strlit"OK! "; toString (lines_read s);
                           strlit" lines read.\n"]))
          od
      | _ => stdio (print_err (strlit"<error message placeholder>"))
    od`;

val _ = export_theory()

