(*
  A test file for the support of exceptions
*)

open preamble ml_monad_translator_interfaceLib

val _ = new_theory "exception_arity_testProg"

(* Data type for the exceptions *)
Datatype:
  state_exn = Fail1
            | Fail2 int
            | Fail3 string bool
            | Fail4 int num string
End

(* Translator configuration *)
val config = global_state_config |>
             with_exception ``:state_exn``;

(* Parser overloadings for exceptions *)
Overload failwith = ``raise_Fail1``
Overload handle_fail = ``handle_Fail1``

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

Definition handle1_def:
  handle1 n = handle_Fail1 (return n) (return n)
End
val rh1 = m_translate handle1_def

Definition handle2_def:
  handle2 n = handle_Fail2 (return n) (\x. return n)
End
val rh2 = m_translate handle2_def

Definition handle3_def:
  handle3 n = handle_Fail3 (return n) (\x y. return n)
End
val rh3 = m_translate handle3_def

Definition handle4_def:
  handle4 n = handle_Fail4 (return n) (\x y z. return n)
End
val rh4 = m_translate handle4_def

(* ... *)

val _ = export_theory();
