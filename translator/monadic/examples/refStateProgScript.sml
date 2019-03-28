(*
  An example showing how to use the monadic translator to translate
  monadic functions using references (no arrays, no exceptions).
*)
open preamble ml_monad_translator_interfaceLib

val _ = new_theory "refStateProg"

(* Pattern matching
 * Note that `dtcase` has to be used from now on in the function definitions (and not `case`)
 *)
val _ = patternMatchesLib.ENABLE_PMATCH_CASES();

(* Create the data type to handle the references.
   In this example, the data type has only one field, which means that
   the translation will only generate one reference.
   It is of course possible to use as many as needed.
 *)
val _ = Hol_datatype `
  state_refs = <| the_num_ref : num |>`;

(* Create the translation configuration *)
val config =  global_state_config |>
              with_state ``:state_refs`` |>
              with_refs [("the_num_ref", ``0 : num``)]

(*
 * We can now use the resulting monadic functions in new definitions:
 *)

(* A very simple monadic function *)
val simple_fun_def = Define `simple_fun x = return x`;

(* A recursive monadic function *)
val rec_fun_def = Define `
  rec_fun l = dtcase l of [] => return (0 : num)
                   | x::l' => do x <- rec_fun l'; return (1+x) od`;

(* A monadic function calling other monadic functions *)
val calling_fun_def = Define `
  calling_fun l = do x <- rec_fun l; simple_fun x od`;

(* A monadic function using the store *)
val store_fun_def = Define `
  store_fun x = do y <- get_the_num_ref; set_the_num_ref (x + y) od`;

(* Other *)
val if_fun_def = Define `
  if_fun (x : num) y = if x > y then return T else return F`;

(* ... *)

(* Intialise the translation *)
val _ = start_translation config;

(* The polymorphism of simple_fun is taken into account *)
val simple_fun_v_thm = simple_fun_def |> m_translate;

(* It is of course possible to translate recursive functions *)
val def = rec_fun_def
val rec_fun_v_thm = rec_fun_def |> m_translate;

(* And others... *)
val calling_fun_v_thm = calling_fun_def |> m_translate;
val store_fun_v_thm = store_fun_def |> m_translate;
val if_fun_v_thm = if_fun_def |> m_translate;

(* ... *)

val _ = export_theory ();
