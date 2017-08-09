(*
 * An example showing how to use the monadic translator with references, arrays and exceptions.
 *)

open preamble ml_monadBaseLib
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
val refs_init_list = [(the_num_name, init_num_def, get_the_num_def, set_the_num_def)];

val init_num_array_def = Define `init_num_array = [] : num list`;
val init_int_array_def = Define `init_int_array = [] : int list`;
val arrays_init_values = [init_num_array_def, init_int_array_def];
val arrays_init_list = List.map (fn ((x1, x2, x3, x4, x5, x6, x7), x) => (x1, x, x2, x3, x4, x5, x6, x7)) (zip array_manip_funs arrays_init_values);

val store_hprop_name = "STATE_STORE";
val state_type = ``:state_refs``;
val exn_ri_def = STATE_EXN_TYPE_def;

(* Initialize the translation *)
val (monad_parameters, store_translation, exn_specs) =
    start_static_init_fixed_store_translation refs_init_list
					      arrays_init_list
					      store_hprop_name
					      state_type
					      exn_ri_def
					      exn_functions
					      [];

(* Monadic translations *)
val test1_def = Define `test1 n =
  do
      x <- the_num_array_sub n;
      return x
  od`;
val def = test1_def |> m_translate;

val test2_def = Define `test2 n = the_num_array_sub n`;
val def = test2_def |> m_translate;

val test3_def = Define `test3 n x = update_the_num_array n x`;
val def = test2_def |> m_translate;

val test4_def = Define `test4 n x = alloc_the_num_array n x`;
val def = test3_def |> m_translate;

(* ... *)

val _ = export_theory ();
