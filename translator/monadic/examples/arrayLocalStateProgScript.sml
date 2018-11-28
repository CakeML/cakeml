(*
  An example showing how to use the monadic translator with
  references, arrays and exceptions.
*)

open preamble ml_monadBaseLib
open ml_monad_translatorTheory ml_monad_translatorLib

val _ = new_theory "arrayLocalStateProg"
val _ = ParseExtras.temp_loose_equality();
val _ = patternMatchesLib.ENABLE_PMATCH_CASES();
val _ = monadsyntax.temp_add_monadsyntax()

val _ = temp_overload_on ("monad_bind", ``st_ex_bind``);
val _ = temp_overload_on ("monad_unitbind", ``\x y. st_ex_bind x (\z. y)``);
val _ = temp_overload_on ("monad_ignore_bind", ``\x y. st_ex_bind x (\z. y)``);
val _ = temp_overload_on ("return", ``st_ex_return``);

val _ = hide "state";

val _ = (use_full_type_names := false);

(* Create the data type to handle the references *)
val _ = Hol_datatype `
  state_refs = <|
		   ref1 : num ;
                   ref2 : int;
		   rarray1 : num list ;
		   rarray2 : int list;
                   farray1 : num list;
		   farray2 : int list;
		   |>`;

(* Data type for the exceptions *)
val _ = Hol_datatype`
  state_exn = Fail of string | Subscript`;

val _ = register_type ``:tvarN``;
val _ = register_exn_type ``:state_exn``;
val STATE_EXN_TYPE_def = theorem"STATE_EXN_TYPE_def";

(* Monadic functions to handle the exceptions *)
val exn_functions = define_monad_exception_functions ``:state_exn`` ``:state_refs``;
val _ = temp_overload_on ("failwith", ``raise_Fail``);

(* Define the functions used to access the elements of the state_refs data_type *)
val access_funs = define_monad_access_funs (``:state_refs``);
val [(ref1_name, get_ref1_def, set_ref1_def),
     (ref2_name, get_ref2_def, set_ref2_def),
     (rarray1_name, get_rarry1_def, set_rarray1_def),
     (rarray2_name, get_rarry2_def, set_rarray2_def),
     (farray1_name, get_farry1_def, set_farray1_def),
     (farray2_name, get_farry2_def, set_farray2_def)] = access_funs;

val sub_exn = ``Subscript``;
val update_exn = ``Subscript``;

val arrays_access_funs = List.drop (access_funs, 2);
val farrays_manip_list = List.drop (arrays_access_funs, 2);
val rarrays_manip_list = List.take (arrays_access_funs, 2);
val refs_manip_list = List.take (access_funs, 2);
val rarrays_manip_list = define_MRarray_manip_funs rarrays_manip_list sub_exn update_exn;
val farrays_manip_list = define_MFarray_manip_funs farrays_manip_list sub_exn update_exn;

(* Prepare the translation *)
val store_hprop_name = "STATE_STORE";
val state_type = ``:state_refs``;
val exn_ri_def = STATE_EXN_TYPE_def;
val store_pinv_def_opt = NONE : thm option;

(* translate_dynamic_init_fixed_store refs_manip_list rarrays_manip_list farrays_manip_list store_hprop_name state_type exn_ri_def store_pinv_def_opt *)

(* Initialize the translation *)
val (monad_parameters, exn_specs) =
    start_dynamic_init_fixed_store_translation refs_manip_list
					      rarrays_manip_list
					      farrays_manip_list
					      store_hprop_name
					      state_type
					      exn_ri_def
					      exn_functions
					      []
                                              store_pinv_def_opt;

(* Monadic translations *)

val test1_def = Define `test1 x =
  do
      y <- get_ref1;
      return (x + y)
  od`;
val test1_v_thm = test1_def |> m_translate;

val test2_def = Define `test2 n =
  do
      x <- rarray1_sub n;
      return x
  od`;
val test2_v_thm = test2_def |> m_translate;

val test3_def = Define `test3 n =
  do
      x <- farray1_sub n;
      return x
  od`;
val test3_v_thm = test3_def |> m_translate;

val test4_def = Define `test4 n x = update_rarray1 n x`;
val test4_v_thm = test4_def |> m_translate;

val test5_def = Define `test5 n x = update_farray1 n x`;
val test5_v_thm = test5_def |> m_translate;

val test6_def = Define `test6 n x = alloc_rarray1 n x`;
val test6_v_thm = test6_def |> m_translate;

(* run translations *)
(* test 1 *)
val run_init_state_def = define_run ``:state_refs``
                                    ["farray1", "farray2"]
				    "init_state"

val run_test1_def = Define `run_test1 x state = run_init_state (test1 x) state`;
val run_test1_v_thm = m_translate_run run_test1_def;

val crun_test1_def = Define `crun_test1 x = run_init_state (test1 x) (init_state 0 0 [] [] (10, 0) (11, 0))`;
val crun_test1_v_thm = m_translate_run crun_test1_def;

(* test 2 *)
val run_test2_def = Define `run_test2 x state = run_init_state (test2 x) state`;
val run_test2_v_thm = m_translate_run run_test2_def;

val crun_test2_def = Define `crun_test2 x = run_init_state (test2 x) (init_state 0 0 [] [] (10, 0) (11, 0))`;
val crun_test2_v_thm = m_translate_run crun_test2_def;

(* test 3 *)
val run_test3_def = Define `run_test3 x state = run_init_state (test3 x) state`;
val run_test3_v_thm = m_translate_run run_test3_def;

val crun_test3_def = Define `crun_test3 x = run_init_state (test3 x) (init_state 0 0 [] [] (10, 0) (11, 0))`;
val crun_test3_v_thm = m_translate_run crun_test3_def;

(* test 4 *)
val run_test4_def = Define `run_test4 n x state = run_init_state (test4 n x) state`;
val run_test4_v_thm = m_translate_run run_test4_def;

val crun_test4_def = Define `crun_test4 n x = run_init_state (test4 n x) (init_state 0 0 [] [] (10, 0) (11, 0))`;
val crun_test4_v_thm = m_translate_run crun_test4_def;

(* test 5 *)
val run_test5_def = Define `run_test5 n x state = run_init_state (test5 n x) state`;
val run_test5_v_thm = m_translate_run run_test5_def;

val crun_test5_def = Define `crun_test5 n x = run_init_state (test5 n x) (init_state 0 0 [] [] (10, 0) (11, 0))`;
val crun_test5_v_thm = m_translate_run crun_test5_def;

(* test 6 *)
val run_test6_def = Define `run_test6 n x state = run_init_state (test6 n x) state`;
val run_test6_v_thm = m_translate_run run_test6_def;

val crun_test6_def = Define `crun_test6 n x = run_init_state (test6 n x) (init_state 0 0 [] [] (10, 0) (11, 0))`;
val crun_test6_v_thm = m_translate_run crun_test6_def;

(* ... *)

val _ = export_theory ();
