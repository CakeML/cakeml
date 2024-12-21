(*
  An example showing how to use the monadic translator to translate
  monadic functions using references, stdio, and commandline
  (no arrays, no exceptions).
*)

(* Load the interface to the monadic translator, and basis for IO *)
open preamble basisProgTheory ml_monad_translator_interfaceLib

val _ = new_theory "fibProg"

val _ = translation_extends "basisProg";

(*
 * Pattern matching
 * Note that `dtcase` has to be used from now on in the
 * function definitions (and not `case`)
 *)
val _ = patternMatchesLib.ENABLE_PMATCH_CASES();

(* Create the data type to handle the references and I/O. *)
Datatype:
  state_references = <| commandline : mlstring list
                      ; stdio : IO_fs |>
End

(* Data type for the exceptions *)
Datatype:
  state_exn = Fail
End

val config =  global_state_config |>
              with_state ``:state_references`` |>
              with_exception ``:state_exn`` |>
              with_commandline "commandline" "stdio";

(* Initialize the translation *)
val _ = start_translation config;

(* Monadic translations *)
Definition hd_def:
  hd l = dtcase l of [] => raise_Fail | x::l' => return x
End

Definition str_to_num_def:
  str_to_num (s:mlstring) =
    dtcase mlint$fromString s of
      NONE => raise_Fail
    | SOME i => if i < 0i then raise_Fail else return (Num i)
End

Definition fiba_def:
  fiba i j n = if n = 0n then (i:num) else fiba j (i+j) (n-1)
End

Definition num_to_str_def:
  num_to_str (n:num) = mlint$toString (& n)
End

Definition fibm_def:
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
          od
End

val res = m_translate hd_def
val res = m_translate str_to_num_def

val str_to_num_side = Q.prove (
  `str_to_num_side st1 v2 <=> T`,
  rw [fetch "-" "str_to_num_side_def"] >> intLib.COOPER_TAC
  )
  |> update_precondition;

val res = translate num_to_str_def
val res = translate fiba_def
val res = m_translate fibm_def

val _ = export_theory ();
