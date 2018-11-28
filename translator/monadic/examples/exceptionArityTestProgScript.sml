(*
  A test file for the support of exceptions
*)

open preamble ml_monadBaseLib
open ml_monad_translatorTheory ml_monad_translatorLib

val _ = new_theory "exceptionArityTestProg"

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

(* No references/arays, so use unit for the state type *)
val state_type = ``:unit``;
val _ = register_type ``:unit``;

(* Data type for the exceptions *)
val _ = Hol_datatype`
  state_exn = Fail1
	    | Fail2 of int
            | Fail3 of string => bool
            | Fail4 of int => num => string`;

(* It is necessary to register that type for the CakeML program to be able to use it*)
val _ = register_type ``:tvarN``;
val _ = register_exn_type ``:state_exn``;
val STATE_EXN_TYPE_def = theorem"EXCEPTIONARITYTESTPROG_STATE_EXN_TYPE_def";

(* Generate the monadic functions to handle the exceptions *)
val exn_type = ``:state_exn``;
val exn_functions = define_monad_exception_functions ``:state_exn`` state_type;
val _ = temp_overload_on("failwith", ``raise_Fail1``);
val _ = temp_overload_on("handle_fail", ``handle_Fail1``);

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
