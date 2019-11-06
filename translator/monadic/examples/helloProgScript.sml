(*
  An example showing how to use the monadic translator to translate
  monadic functions using IO primitives from the basis library.
*)

(* Load the interface to the monadic translator, and basis for IO *)
open preamble basisProgTheory ml_monad_translator_interfaceLib

(* Load cfMonadLib for the cf app spec *)
open cfMonadLib

val _ = new_theory "helloProg"

val _ = translation_extends "basisProg";

(* Pattern matching
 * Note that `dtcase` has to be used from now on in the
 * function definitions (and not `case`)
 *)
val _ = patternMatchesLib.ENABLE_PMATCH_CASES();

(* Create the data type to handle the references and I/O. *)
val _ = Datatype `
  state_refs = <| the_num_ref : num
                ; stdio : IO_fs |>`;

val config =  global_state_config |>
              with_state ``:state_refs`` |>
              with_refs [("the_num_ref", ``0 : num``)] |>
              with_stdio "stdio";

(* Initialize the translation *)
val _ = start_translation config;

(* A very simple monadic function *)
val simple_fun_def = Define `simple_fun x = return x`;

(* A recursive monadic function *)
val rec_fun_def = Define `
  rec_fun l = dtcase l of []    => return (0 : num)
                        | x::l' => do x <- rec_fun l'; return (1+x) od`;

(* A monadic function calling other monadic functions *)
val calling_fun_def = Define `
  calling_fun l = do x <- rec_fun l; simple_fun x od`;

(* A monadic function using the store *)
val store_fun_def = Define `
  store_fun x = do y <- get_the_num_ref; set_the_num_ref (x + y) od`;

val io_fun_def = Define `
  io_fun x = do y <- get_the_num_ref; set_the_num_ref (x + y) od`;

(* Other *)
val if_fun_def = Define `
  if_fun (x : num) y = if x > y then return T else return F`;

(* The polymorphism of simple_fun is taken into account *)
val simple_fun_v_thm = simple_fun_def |> m_translate;

(* It is of course possible to translate recursive functions *)
val rec_fun_v_thm = rec_fun_def |> m_translate;

(* And others... *)
val calling_fun_v_thm = calling_fun_def |> m_translate;
val store_fun_v_thm = store_fun_def |> m_translate;
val if_fun_v_thm = if_fun_def |> m_translate;

val hello_def = Define `
  hello (u:unit) = stdio (print (implode "Hello")) : (state_refs, unit, unit) M`

val res = m_translate hello_def;

val hello_app_thm = save_thm("hello_app_thm",
  cfMonadLib.mk_app_of_ArrowP res |> SPEC_ALL);

val _ = export_theory ();
