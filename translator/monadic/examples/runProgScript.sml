open preamble ml_monadBaseLib ml_monadBaseTheory
open ml_monad_translatorTheory ml_monad_translatorLib

val _ = new_theory "arrayStateProg"
val _ = ParseExtras.temp_loose_equality();
val _ = patternMatchesLib.ENABLE_PMATCH_CASES();
val _ = monadsyntax.temp_add_monadsyntax()

val _ = temp_overload_on ("monad_bind", ``st_ex_bind``);
val _ = temp_overload_on ("monad_unitbind", ``\x y. st_ex_bind x (\z. y)``);
val _ = temp_overload_on ("monad_ignore_bind", ``\x y. st_ex_bind x (\z. y)``);
val _ = temp_overload_on ("return", ``st_ex_return``);

val _ = hide "state";

val _ = (use_full_type_names := false);

(* Register the types used for the translation *)
val _ = register_type ``:'a # 'b``;
val _ = register_type ``:'a list``;
val _ = register_type ``:'a option``;
val _ = register_type ``:('a, 'b) exc``;
val _ = register_type ``:unit``;

(* Create the data type to handle the references *)
val _ = Hol_datatype `
  state_refs = <| the_num : num ;
	          the_num_array : num list ;
                  the_int_array : int list |>`;

(* Data type for the exceptions *)
val _ = Hol_datatype`
  state_exn = Fail of string | ReadError of unit | WriteError of unit`;

val _ = register_exn_type ``:state_exn``;
val STATE_EXN_TYPE_def = theorem"STATE_EXN_TYPE_def";

val _ = register_type ``:state_refs``;
val STATE_REFS_TYPE_def = theorem"STATE_REFS_TYPE_def";

(* Monadic functions to handle the exceptions *)
val exn_functions = define_monad_exception_functions ``:state_exn`` ``:state_refs``;
val _ = temp_overload_on ("failwith", ``raise_Fail``);

(* Define the functions used to access the elements of the state_refs data_type *)
val access_funs = define_monad_access_funs (``:state_refs``);
val [(the_num_name, get_the_num_def, set_the_num_def),
     (the_num_array_name, get_the_num_array_def, set_the_num_array_def),
     (the_int_array_name, get_the_int_array_def, set_the_int_array_def)] = access_funs;

val sub_exn = ``ReadError ()``;
val update_exn = ``WriteError ()``;
val array_access_funs = (List.tl access_funs);
val array_manip_funs = define_Marray_manip_funs array_access_funs sub_exn update_exn;

(* Prepare the translation *)
val init_num_def = Define `init_num = (0 : num)`;
val init_num_array_def = Define `init_num_array = [] : num list`;
val init_int_array_def = Define `init_int_array = [] : int list`;
val refs_init_list = [(the_num_name, init_num_def, get_the_num_def, set_the_num_def),
		     (the_num_array_name, init_num_array_def, get_the_num_array_def, set_the_num_array_def),
		     (the_int_array_name, init_int_array_def, get_the_int_array_def, set_the_int_array_def)];
(* val refs_init_list = [(the_num_name, init_num_def, get_the_num_def, set_the_num_def)]; *)

(* val init_num_array_def = Define `init_num_array = [] : num list`;
val init_int_array_def = Define `init_int_array = [] : int list`;
val arrays_init_values = [init_num_array_def, init_int_array_def];
val arrays_init_list = List.map (fn ((x1, x2, x3, x4, x5, x6, x7), x) => (x1, x, x2, x3, x4, x5, x6, x7)) (zip array_manip_funs arrays_init_values); *)

val infer_init_state = ``<|the_num := 0; the_num_array := []; the_int_array := []|>``;

val store_hprop_name = "STATE_STORE";
val state_type = ``:state_refs``;
val EXN_RI = ``STATE_EXN_TYPE``;
val exn_ri_def = STATE_EXN_TYPE_def;

val refs_manip_list = List.map (fn (x, _, y, z) => (x, y, z)) refs_init_list;
(* val arrays_manip_list = List.map (fn (x1, _, x2, x3, x4, x5, x6, x7) => (x1, x2, x3, x4, x5, x6, x7)) arrays_init_list; *)
val arrays_manip_list = [] : (string * thm * thm * thm * thm * thm * thm) list;

(* Initialize the translation *)
val (translation_parameters, exn_specs) =
    start_dynamic_init_fixed_store_translation refs_manip_list
					       arrays_manip_list
					       store_hprop_name
					       state_type
					       exn_ri_def
					       exn_functions
                                               [];

(* Monadic translations *)
(* val test2_def = Define `test2 n = the_num_array_sub n`;
val def = test2_def |> m_translate;

val test3_def = Define `test3 n x = update_the_num_array n x`;
val def = test2_def |> m_translate;

val test4_def = Define `test4 n x = alloc_the_num_array n x`;
val def = test3_def |> m_translate;

val test5_def = Define `
test5 n z =
    do
	alloc_the_num_array n z;
        return ()
    od`;
val def = test5_def |> m_translate;
val test5_trans_th = m_translate test5_def;

val test6_def = Define `
test6 n z = test5 n z`;
val def = test6_def;
val test6_trans_th = m_translate test6_def;

val test7_def = Define `
(test7 [] = return 0) /\ ((test7 (x::l)) = (do x <- test7 l; return (x+1) od))`;
val def = test7_def;
val test7_v_th = m_translate test7_def;

val test8_def = Define `
test8 l = test7 l`;
val test8_v_th = m_translate test8_def; *)

val test1_def = Define `test1 x = do y <- get_the_num; return (x + y) od`;
val test1_v_th = m_translate test1_def;

val test2_def = Define `test2 (x : num) y = return (x + y)`;
val test2_v_th = m_translate test2_def;

val test3_def = Define `
test3 n m z =
   do
       test2 n z;
       x <- test1 m;
       return x
   od`;
val test3_v_th = m_translate test3_def;

(* Run *)
val run_test_def = Define `run_test n m z refs = run (test3 n m z) refs`;
val def = run_test_def;
val run_test_v_th = m_translate_run run_test_def;

val _ = export_theory ();
