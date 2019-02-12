(*
  An example showing how to use the monadic translator to translate
  monadic functions using references (no arrays, no exceptions).
*)

(* Load the CakeML basic stuff *)
open preamble basisProgTheory

(*
 * Those libraries are used in the translation
 *)
open ml_monad_translatorLib ml_monad_translator_interfaceLib

(* For IO: print, arguments, name *)
open TextIOProofTheory CommandLineProofTheory

val _ = new_theory "fibProg"

val _ = translation_extends "basisProg";

(*
 * Pattern matching
 * Note that `dtcase` has to be used from now on in the
 * function definitions (and not `case`)
 *)
val _ = patternMatchesLib.ENABLE_PMATCH_CASES();

(* Create the data type to handle the references and I/O. *)
val _ = Datatype `
  state_references = <| commandline : mlstring list
                      ; stdio : IO_fs |>`;

(* Data type for the exceptions *)
val _ = Hol_datatype`
  state_exn = Fail`;

val config =  global_state_config |>
              with_state ``:state_references``;
val config = with_exception ``:state_exn`` config

val config = with_commandline "commandline" "stdio" config;

(* Initialize the translation *)
val _ = start_translation config;

val _ = overload_on("stdio",``liftM state_references_stdio stdio_fupd``);
val _ = overload_on("commandline",``liftM state_references_commandline commandline_fupd``);

val hd_def = Define `
  hd l = dtcase l of [] => raise_Fail | x::l' => return x`;

val str_to_num_def = Define `
  str_to_num (s:mlstring) =
    dtcase mlint$fromString s of
      NONE => raise_Fail
    | SOME i => if i < 0i then raise_Fail else return (Num i)`;

val fiba_def = Define`
  fiba i j n = if n = 0n then (i:num) else fiba j (i+j) (n-1)`;

val num_to_str_def = Define `
  num_to_str (n:num) = mlint$toString (& n)`

val fibm_def = Define`
  fibm () =
    do
      (args:mlstring list) <- commandline (arguments ()) ;
      (a:mlstring) <- hd args ;
      n <- str_to_num a ;
      stdio (print (num_to_str (fiba 0 1 n))) ;
      stdio (print (strlit "\n"))
    od otherwise do
            name <- commandline (name ()) ;
            stdio (print_err (strlit"usage: " ^ name ^ strlit" <n>\n"))
          od`

val IMP_STAR_GC = store_thm("IMP_STAR_GC", (* TODO: move *)
  ``(STAR a x) s /\ (y = GC) ==> (STAR a y) s``,
  fs [set_sepTheory.STAR_def]
  \\ rw[] \\ asm_exists_tac \\ fs []
  \\ EVAL_TAC
  \\ fs [set_sepTheory.SEP_EXISTS_THM]
  \\ qexists_tac `K T` \\ fs []);

(* TODO move *)
val stdio_INTRO = prove(
  ``(!st. EvalM ro env st exp
            (MONAD UNIT_TYPE exc_ty f)
            (MONAD_IO,p:'ffi ffi_proj)) ==>
    (!st. EvalM ro env st exp
            (MONAD UNIT_TYPE exc_ty (stdio f))
            (STATE_REFERENCES,p:'ffi ffi_proj))``,
  fs [ml_monad_translatorTheory.EvalM_def] \\ rw []
  \\ first_x_assum (qspecl_then [`st.stdio`,`s`] mp_tac)
  \\ impl_tac
  THEN1 (fs [ml_monad_translatorBaseTheory.REFS_PRED_def]
         \\ fs [fetch "-" "STATE_REFERENCES_def"]
         \\ qabbrev_tac `a = MONAD_IO st.stdio`
         \\ qabbrev_tac `b = GC`
         \\ fs [AC set_sepTheory.STAR_ASSOC set_sepTheory.STAR_COMM]
         \\ last_x_assum mp_tac
         \\ metis_tac [IMP_STAR_GC])
  \\ disch_then strip_assume_tac
  \\ asm_exists_tac \\ fs []
  \\ fs [ml_monad_translatorBaseTheory.REFS_PRED_FRAME_def,
        semanticPrimitivesTheory.state_component_equality]
  \\ rveq \\ fs [ml_monad_translatorTheory.MONAD_def]
  \\ Cases_on `f st.stdio` \\ fs []
  \\ every_case_tac
  \\ rveq \\ fs []
  \\ fs [fetch "-" "STATE_REFERENCES_def"]
  \\ rw []
  \\ first_x_assum (qspec_then `COMMANDLINE st.commandline * F'` mp_tac)
  \\ fs [AC set_sepTheory.STAR_COMM set_sepTheory.STAR_ASSOC]
  \\ fs [ml_monadBaseTheory.liftM_def]
  \\ rw []
  \\ fs [set_sepTheory.STAR_COMM]);

(* TODO move *)
val commandline_INTRO = prove(
  ``(!st. EvalM ro env st exp
            (MONAD ret_ty exc_ty f)
            (COMMANDLINE,p:'ffi ffi_proj)) ==>
    (!st. EvalM ro env st exp
            (MONAD ret_ty exc_ty (commandline f))
            (STATE_REFERENCES,p:'ffi ffi_proj))``,
  fs [ml_monad_translatorTheory.EvalM_def] \\ rw []
  \\ first_x_assum (qspecl_then [`st.commandline`,`s`] mp_tac)
  \\ impl_tac
  THEN1 (fs [ml_monad_translatorBaseTheory.REFS_PRED_def]
         \\ fs [fetch "-" "STATE_REFERENCES_def"]
         \\ qabbrev_tac `a = COMMANDLINE st.commandline`
         \\ qabbrev_tac `b = GC`
         \\ fs [AC set_sepTheory.STAR_ASSOC set_sepTheory.STAR_COMM]
         \\ last_x_assum mp_tac
         \\ metis_tac [IMP_STAR_GC])
  \\ disch_then strip_assume_tac
  \\ asm_exists_tac \\ fs []
  \\ fs [ml_monad_translatorBaseTheory.REFS_PRED_FRAME_def,
        semanticPrimitivesTheory.state_component_equality]
  \\ rveq \\ fs [ml_monad_translatorTheory.MONAD_def]
  \\ Cases_on `f st.commandline` \\ fs []
  \\ every_case_tac
  \\ rveq \\ fs []
  \\ fs [fetch "-" "STATE_REFERENCES_def"]
  \\ rw []
  \\ first_x_assum (qspec_then `MONAD_IO st.stdio * F'` mp_tac)
  \\ fs [AC set_sepTheory.STAR_COMM set_sepTheory.STAR_ASSOC]
  \\ fs [ml_monadBaseTheory.liftM_def]
  \\ rw []);

val EvalM_stdio_print = prove(
  ``Eval env exp (STRING_TYPE x) /\
    (nsLookup env.v (Short "print") = SOME TextIO_print_v) ==>
    EvalM F env st (App Opapp [Var (Short "print"); exp])
      (MONAD UNIT_TYPE STATE_EXN_TYPE (stdio (print x)))
      (STATE_REFERENCES,p:'ffi ffi_proj)``,
  metis_tac [stdio_INTRO,EvalM_print]);

val EvalM_stdio_print_err = prove(
  ``Eval env exp (STRING_TYPE x) /\
    (nsLookup env.v (Long "TextIO" (Short "print_err")) = SOME TextIO_print_err_v) ==>
    EvalM F env st (App Opapp [Var (Long "TextIO" (Short "print_err")); exp])
      (MONAD UNIT_TYPE STATE_EXN_TYPE (stdio (print_err x)))
      (STATE_REFERENCES,p:'ffi ffi_proj)``,
  metis_tac [stdio_INTRO,EvalM_print_err]);

val EvalM_commandline_name = prove(
  ``Eval env exp (UNIT_TYPE x) /\
    (nsLookup env.v (Long "CommandLine" (Short "name")) =
       SOME CommandLine_name_v) ==>
    EvalM F env st (App Opapp [Var (Long "CommandLine" (Short "name")); exp])
      (MONAD STRING_TYPE STATE_EXN_TYPE (commandline (name x)))
      (STATE_REFERENCES,p:'ffi ffi_proj)``,
  metis_tac [commandline_INTRO,EvalM_name]);

val EvalM_commandline_arguments = prove(
  ``Eval env exp (UNIT_TYPE x) /\
    (nsLookup env.v (Long "CommandLine" (Short "arguments")) =
       SOME CommandLine_arguments_v) ==>
    EvalM F env st (App Opapp [Var (Long "CommandLine" (Short "arguments")); exp])
      (MONAD (LIST_TYPE STRING_TYPE) STATE_EXN_TYPE (commandline (arguments x)))
      (STATE_REFERENCES,p:'ffi ffi_proj)``,
  metis_tac [commandline_INTRO,EvalM_arguments]);

val _ = add_access_pattern EvalM_stdio_print;
val _ = add_access_pattern EvalM_stdio_print_err;
val _ = add_access_pattern EvalM_commandline_name
val _ = add_access_pattern EvalM_commandline_arguments
val _ = ignore_type ``:IO_fs``;

val res = m_translate hd_def
val res = m_translate str_to_num_def

val str_to_num_side = Q.prove (
  `str_to_num_side st1 v2 <=> T`,
  rw [fetch "-" "str_to_num_side_def"]
  \\ intLib.COOPER_TAC)
  |> update_precondition;

val res = translate num_to_str_def
val res = translate fiba_def

val res = m_translate fibm_def

val _ = export_theory ();
