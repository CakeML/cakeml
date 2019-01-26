(*
  An example of how to translate `run`
*)
open preamble ml_monadBaseLib ml_monadBaseTheory
open ml_monad_translatorTheory ml_monad_translatorLib

val _ = new_theory "runProg"
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
  state_refs = <| the_num : num ;
                  the_num_array : num list ;
                  the_int_array : int list |>`;

(* Data type for the exceptions *)
val _ = Hol_datatype`
  state_exn = Fail of string | Subscript`;

val _ = register_type ``:tvarN``;
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

val sub_exn = ``Subscript``;
val update_exn = ``Subscript``;
val array_access_funs = (List.tl access_funs);
val array_manip_funs = define_MRarray_manip_funs array_access_funs sub_exn update_exn;

(* Prepare the translation *)
val init_num_def = Define `init_num = (0 : num)`;
val init_num_array_def = Define `init_num_array = [] : num list`;
val init_int_array_def = Define `init_int_array = [] : int list`;
val refs_init_list = [(the_num_name, init_num_def, get_the_num_def, set_the_num_def),
                     (the_num_array_name, init_num_array_def, get_the_num_array_def, set_the_num_array_def),
                     (the_int_array_name, init_int_array_def, get_the_int_array_def, set_the_int_array_def)];

val infer_init_state = ``<|the_num := 0; the_num_array := []; the_int_array := []|>``;

val store_hprop_name = "STATE_STORE";
val state_type = ``:state_refs``;
val EXN_RI = ``STATE_EXN_TYPE``;
val exn_ri_def = STATE_EXN_TYPE_def;
(*
val EXN_TYPE_def = STATE_EXN_TYPE_def;
*)

val refs_manip_list = List.map (fn (x, _, y, z) => (x, y, z)) refs_init_list;
val rarrays_manip_list = [] : (string * thm * thm * thm * thm * thm * thm) list;
val farrays_manip_list = [] : (string * thm * thm * thm * thm * thm) list;

val add_type_theories = [] : string list;
val store_pinv_def_opt = NONE : thm option;

(* Initialize the translation *)
val (translation_parameters, exn_specs) =
    start_dynamic_init_fixed_store_translation refs_manip_list
                                               rarrays_manip_list
                                               farrays_manip_list
                                               store_hprop_name
                                               state_type
                                               exn_ri_def
                                               exn_functions
                                               [] NONE;

(* Monadic translations *)
val _ = temp_tight_equality ();

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

(* Several non recursive functions *)
val run_test3_def = Define `run_test3 n m z refs = run (test3 n m z) refs`;
val run_test3_v_th = m_translate_run run_test3_def;
val test3'_def = Define `test3' (n, m, z, refs) = run_test3 n m z refs :(num, state_exn) exc`;
val res = translate test3'_def;

(* Recursive function *)
val test4_def = Define `
test4 (x::l) = do y <- test4 l; return (x + y) od /\
test4 [] = return (0 : num)`;
val def = test4_def;
val test4_v_th = m_translate test4_def;
val run_test4_def = Define `run_test4 l state = run (test4 l) state`;
val run_test4_v_thm = m_translate_run run_test4_def;

(* Mutual recursion *)
val _ = Hol_datatype `
data = C1 of num | C2 of data list`;

val data_length_def = Define `data_length1 (C1 x) = return x /\
        data_length1 (C2 x) = data_length2 x /\
data_length2 (x::xl) = do y1 <- data_length1 x; y2 <- data_length2 xl; return (y1 + y2) od /\
        data_length2 [] = return 0`;
val def = data_length_def;
val data_length_v_th = m_translate def;
val run_data_length1_def = Define `run_data_length d state = run (data_length1 d) state`;
val run_data_length1_v_thm = m_translate_run run_data_length1_def;

(* Other test *)
val test6_def = Define `
test6 (x::l) = do y <- test6 l; z <- test1 x; return (x + y + z) od /\
test6 [] = return (0 : num)`;
val def = test6_def;
val test6_v_th = m_translate test6_def;

val run_test6_def = Define `run_test6 l state = run (test6 l) state`;
val def = run_test6_def;
val run_test6_v_th = m_translate_run def;

(* Mix standard and monadic functions *)
val LENGTH_v_thm = translate LENGTH;
val test7_def = Define `test7 x l = do y <- test1 x; return (y + (LENGTH l)) od`
val test7_v_thm = m_translate test7_def;
val run_test7_def = Define `run_test7 x l state = run (test7 x l) state`;
val run_test7_v_thm = m_translate_run run_test7_def;

val _ = export_theory ();
