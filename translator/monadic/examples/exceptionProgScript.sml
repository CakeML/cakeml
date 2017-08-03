(*
 * An example showing how to use the monadic translator to translate monadic functions
 * using exceptions (no references, no arrays).
 *)

open ml_monadBaseLib ml_monadBaseTheory
open ml_monadStoreLib ml_monad_translatorTheory ml_monad_translatorLib

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

(* Register the types used for the translation *)
(* In the future: will be performed automatically *)
val _ = register_type ``:'a # 'b``;
val _ = register_type ``:'a list``;
val _ = register_type ``:'a option``;
val _ = register_type ``:unit``;

(* No references/arays, so use unit for the state type *)
val state_type = ``:unit``;

(* Data type for the exceptions *)
val _ = Hol_datatype`
  state_exn = Fail1 of string | Fail2 of int`;

(* It is necessary to register that type for the CakeML program to be able to use it*)
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
val decrease_def = Define `decrease n = monad_ignore_bind (assert (n > 0)) (return (n-1))`;
val handle_decrease_def = Define `handle_decrease n = handle_fail (decrease n) (\e. return 0)`;

(* ... *)

(* TRANSLATION: initialisation *)
(* No references *)
val refs_init_list = [] : (string * thm * thm * thm) list;

(* No arrays *)
val arrays_init_list = [] : (string * thm * thm * thm * thm * thm * thm * thm) list;

(* Name for the store invariant *)
val store_hprop_name = "STATE_STORE";

(* The parameter for the exceptions *)
val exn_ri_def = STATE_EXN_TYPE_def;

(* Create the store *)
val (monad_parameters, store_translation) = translate_static_init_fixed_store refs_init_list arrays_init_list store_hprop_name state_type exn_ri_def;

(* Begin the translation *)
val store_exists_thm = SOME(#store_pred_exists_thm store_translation);
val type_theories = [] : string list;
val _ = init_translation monad_parameters store_exists_thm exn_ri_def type_theories;

(* Give the exceptions manipulating functions to the monadic translator *)
val (raise_functions, handle_functions) = unzip exn_functions;
val exn_thms = add_raise_handle_functions raise_functions handle_functions exn_ri_def;

(* Translate *)
val assert_v_thm = assert_def |> m_translate;
val decrease_v_thm = decrease_def |> m_translate;
val handle_decrease = handle_decrease_def |> m_translate;

(* ... *)

val _ = export_theory();
