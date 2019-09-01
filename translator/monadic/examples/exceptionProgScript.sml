(*
  An example showing how to use the monadic translator to translate
  monadic functions using exceptions (no references, no arrays).
*)
open preamble ml_monad_translator_interfaceLib

val _ = new_theory "exceptionProg";

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
val _ = temp_overload_on("failwith", ``raise_Fail1``);
val _ = temp_overload_on("handle_fail", ``handle_Fail1``);

(* It is possible to define the exception handling functions by hand:

val failwith_def = Define `
  failwith x = \(state : state_refs). (Failure (Fail1 x), state)`;
val handle_fail_def = Define `
  handle_fail x f = \(state : state_refs). dtcase x state of
    (Success x, state) => (Success x, state)
  | (Failure (Fail1 e), state) => f e state
  | other => other`
...

*)

(*
 * It is now possible to use these functions in new definitions:
 *)

val assert_def = Define `
  assert b = if b then failwith "assert" else return ()`;

val decrease_def = Define `
  decrease n = monad_ignore_bind (assert (n > (0:num))) (return (n-1))`;

val handle_decrease_def = Define `
  handle_decrease n = handle_fail (decrease n) (\e. return 0)`;

(* Translate *)
val _ = start_translation config;

val assert_v_thm = assert_def |> m_translate;
val decrease_v_thm = decrease_def |> m_translate;
val handle_decrease = handle_decrease_def |> m_translate;

(**********)

val _ = export_theory();
