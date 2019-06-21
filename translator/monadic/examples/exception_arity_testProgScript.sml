(*
  A test file for the support of exceptions
*)

open preamble ml_monad_translator_interfaceLib

val _ = new_theory "exception_arity_testProg"

(* Data type for the exceptions *)
val _ = Hol_datatype`
  state_exn = Fail1
            | Fail2 of int
            | Fail3 of string => bool
            | Fail4 of int => num => string`;

(* Translator configuration *)
val config = global_state_config |>
             with_exception ``:state_exn``;

(* Parser overloadings for exceptions *)
val _ = temp_overload_on("failwith", ``raise_Fail1``);
val _ = temp_overload_on("handle_fail", ``handle_Fail1``);

(* TRANSLATION: initialisation *)
val _ = start_translation config;

(* Translate *)
val raise1_def = Define `raise1 x = if x then return 1n else raise_Fail1`
val r1 = m_translate raise1_def

val raise2_def = Define `raise2 x = raise_Fail2 x`
val r2 = m_translate raise2_def

val raise3_def = Define `raise3 x y = raise_Fail3 x y`
val r3 = m_translate raise3_def

val raise4_def = Define `raise4 x y z = raise_Fail4 x y z`
val r4 = m_translate raise4_def

val handle1_def = Define `
  handle1 n = handle_Fail1 (return n) (return n)`
val rh1 = m_translate handle1_def

val handle2_def = Define `
  handle2 n = handle_Fail2 (return n) (\x. return n)`
val rh2 = m_translate handle2_def

val handle3_def = Define `
  handle3 n = handle_Fail3 (return n) (\x y. return n)`
val rh3 = m_translate handle3_def

val handle4_def = Define `
  handle4 n = handle_Fail4 (return n) (\x y z. return n)`
val rh4 = m_translate handle4_def

(* ... *)

val _ = export_theory();
