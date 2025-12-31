(*
  An example showing how to use the monadic translator to translate
  monadic functions using exceptions (no references, no arrays).
*)
Theory exceptionProg
Libs
  preamble ml_monad_translator_interfaceLib
Ancestors
  ml_monad_translator

val _ = set_up_monadic_translator ();

val _ = patternMatchesLib.ENABLE_PMATCH_CASES();

(* No references/arays, so use unit for the state type *)
val state_type = ``:unit``;

(* Data type for the exceptions *)
Datatype:
  state_exn = Fail1 string | Fail2 int
End

(* Translator configuration *)
val config = global_state_config |>
             with_exception ``:state_exn``;

(* Parser overloadings for exceptions *)
Overload failwith = ``raise_Fail1``
Overload handle_fail = ``handle_Fail1``

(* It is possible to define the exception handling functions by hand:

Definition failwith_def:
  failwith x = \(state : state_refs). (M_failure (Fail1 x), state)
End
Definition handle_fail_def:
  handle_fail x f = \(state : state_refs). dtcase x state of
    (M_success x, state) => (M_success x, state)
  | (M_failure (Fail1 e), state) => f e state
  | other => other
End
...

*)

(*
 * It is now possible to use these functions in new definitions:
 *)

Definition assert_def:
  assert b = if b then failwith "assert" else return ()
End

Definition decrease_def:
  decrease n = monad_ignore_bind (assert (n > (0:num))) (return (n-1))
End

Definition handle_decrease_def:
  handle_decrease n = handle_fail (decrease n) (\e. return 0)
End

(* Translate *)
val _ = start_translation config;

val assert_v_thm = assert_def |> m_translate;
val decrease_v_thm = decrease_def |> m_translate;
val handle_decrease = handle_decrease_def |> m_translate;

(**********)
