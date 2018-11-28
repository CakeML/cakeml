(*
  An example showing how to use the monadic translator with
  references, arrays and exceptions.
*)
open preamble ml_monadBaseLib
open ml_monad_translatorTheory ml_monad_translatorLib

val _ = new_theory "arrayGlobalStateProg"
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

val rarray_access_funs = List.drop (access_funs, 2);
val farray_access_funs = List.drop (rarray_access_funs, 2);
val rarray_access_funs = List.take (rarray_access_funs, 2);
val rarray_manip_funs = define_MRarray_manip_funs rarray_access_funs sub_exn update_exn;
val farray_manip_funs = define_MFarray_manip_funs farray_access_funs sub_exn update_exn;

(* Prepare the translation *)
val ref_access_funs = List.take (access_funs, 2);
val init_ref1_def = Define `init_ref1 = (36 : num)`;
val init_ref2_def = Define `init_ref2 = (42 : int)`;
val refs_init_values = [init_ref1_def, init_ref2_def];
val refs_init_list = List.map (fn ((x1, x2, x3), x) => (x1, x, x2, x3)) (zip ref_access_funs refs_init_values)

val init_rarray1_def = Define `init_rarray1 = [] : num list`;
val init_rarray2_def = Define `init_rarray2 = [] : int list`;
val rarrays_init_values = [init_rarray1_def, init_rarray2_def];
val rarrays_init_list = List.map (fn ((x1, x2, x3, x4, x5, x6, x7), x) => (x1, x, x2, x3, x4, x5, x6, x7)) (zip rarray_manip_funs rarrays_init_values);

val init_farray1_def = Define `init_farray1 = 0 : num`;
val init_farray1_info = (12, init_farray1_def);
val init_farray2_def = Define `init_farray2 = 0 : int`;
val init_farray2_info = (7, init_farray2_def);
val farrays_init_values = [init_farray1_info, init_farray2_info];
val farrays_init_list = List.map (fn ((x1, x2, x3, x4, x5, x6), x) => (x1, x, x2, x3, x4, x5, x6)) (zip farray_manip_funs farrays_init_values);

val store_hprop_name = "STATE_STORE";
val state_type = ``:state_refs``;
val exn_ri_def = STATE_EXN_TYPE_def;
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
					      []
                                              store_pinv_opt extra_hprop;

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

(* ... *)

val _ = export_theory ();
