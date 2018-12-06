(*
  An example showing how to use the monadic translator to translate
  monadic functions using exceptions (no references, no arrays).
*)
open preamble ml_monadBaseLib
open ml_monad_translatorTheory ml_monad_translatorLib

val _ = new_theory "exceptionProg"

val _ = ParseExtras.temp_loose_equality();
val _ = monadsyntax.temp_add_monadsyntax();
val _ = patternMatchesLib.ENABLE_PMATCH_CASES();

(* Some overloadings for the parser *)
val _ = temp_overload_on ("monad_bind", ``st_ex_bind``);
val _ = temp_overload_on ("monad_unit_bind", ``\x y. st_ex_bind x (\z. y)``);
val _ = temp_overload_on ("monad_ignore_bind", ``\x y. st_ex_bind x (\z. y)``);
val _ = temp_overload_on ("return", ``st_ex_return``);

(* Need to hide "state" because of semanticPrimitives *)
val _ = hide "state";

val _ = (use_full_type_names := false);

(* No references/arays, so use unit for the state type *)
val state_type = ``:unit``;
val _ = register_type ``:unit``;

(* Data type for the exceptions *)
val _ = Hol_datatype`
  state_exn = Fail1 of string | Fail2 of int`;

(* It is necessary to register that type for the CakeML program to be able to use it*)
val _ = register_type ``:tvarN``;
val _ = register_exn_type ``:state_exn``;
val STATE_EXN_TYPE_def = theorem"STATE_EXN_TYPE_def";

(* Generate the monadic functions to handle the exceptions *)
val exn_functions = define_monad_exception_functions ``:state_exn`` state_type;
val _ = temp_overload_on("failwith", ``raise_Fail1``);
val _ = temp_overload_on("handle_fail", ``handle_Fail1``);

(* It is possible to define the exceptions handling functions by hand:

val failwith_def = Define `failwith x = \(state : state_refs). (Failure (Fail1 x), state)`;
val handle_fail_def = Define `handle_fail x f = \(state : state_refs). dtcase x state of
(Success x, state) => (Success x, state)
| (Failure (Fail1 e), state) => f e state
| other => other`
...

*)

(*
 * It is now possible to use those functions in new definitions:
 *)

val assert_def = Define `assert b = if b then failwith "assert" else return ()`
val decrease_def = Define `decrease n = monad_ignore_bind (assert (n > (0:num))) (return (n-1))`;
val handle_decrease_def = Define `handle_decrease n = handle_fail (decrease n) (\e. return 0)`;

(* ... *)

(* TRANSLATION: initialisation *)
(* No references *)
val refs_init_list = [] : (string * thm * thm * thm) list;

(* No arrays *)
val rarrays_init_list = [] : (string * thm * thm * thm * thm * thm * thm * thm) list;
val farrays_init_list = [] : (string * (int * thm) * thm * thm * thm * thm * thm) list;

(* Name for the store invariant *)
val store_hprop_name = "STATE_STORE";

(* The parameter for the exceptions *)
val exn_ri_def = STATE_EXN_TYPE_def;

(* No additional type theories *)
val type_theories = [] : string list;

(* We don't want to add more conditions than what the monadic translator will automatically generate for the store invariant *)
val store_pinv_opt = NONE : (thm * thm) option;

val extra_hprop = NONE : term option;

(* Initialize the translation *)
val (monad_parameters, store_translation, exn_specs) =
    start_static_init_fixed_store_translation refs_init_list
                                              rarrays_init_list
                                              farrays_init_list
                                              store_hprop_name
                                              state_type
                                              exn_ri_def
                                              exn_functions
                                              type_theories
                                              store_pinv_opt
                                              extra_hprop;

(* Translate *)
val assert_v_thm = assert_def |> m_translate;
val decrease_v_thm = decrease_def |> m_translate;
val handle_decrease = handle_decrease_def |> m_translate;

(* ... *)

val _ = export_theory();
