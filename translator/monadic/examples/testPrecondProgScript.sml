(*
  An example showing how to use the monadic translator with
  references, arrays and exceptions.
*)

open preamble ml_monadBaseLib
open ml_monad_translatorTheory ml_monad_translatorLib

val _ = new_theory "testPrecondProg"
val _ = ParseExtras.temp_loose_equality();
(* val _ = ParseExtras.temp_tight_equality(); *)

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
val rarray_access_funs = (List.tl access_funs);
val rarray_manip_funs = define_MRarray_manip_funs rarray_access_funs sub_exn update_exn;

(* Prepare the translation *)
val init_num_def = Define `init_num = (0 : num)`;
val refs_init_list = [(the_num_name, init_num_def, get_the_num_def, set_the_num_def)];

val init_num_array_def = Define `init_num_array = [] : num list`;
val init_int_array_def = Define `init_int_array = [] : int list`;
val rarrays_init_values = [init_num_array_def, init_int_array_def];
val rarrays_init_list = List.map (fn ((x1, x2, x3, x4, x5, x6, x7), x) => (x1, x, x2, x3, x4, x5, x6, x7)) (zip rarray_manip_funs rarrays_init_values);
val farrays_init_list = [] : (string * (int * thm) * thm * thm * thm * thm * thm) list;


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
                                              store_pinv_opt
                                              extra_hprop;

val hd_v_thm = translate HD;
val tl_v_thm = translate TL;
val el_v_thm = translate EL;

(* Some tests *)
val f1_def = Define `f1 x y (z : num) = return (x + y + z)`;
val f1_v_thm = m_translate f1_def;

val f2_def = Define `f2 x y (z : num) = return ((HD x) + y + z)`;
val f2_v_thm = m_translate f2_def;

val f3_def = Define `f3 x = return (HD x)`;
val f3_v_thm = m_translate f3_def;

val f4_def = Define `f4 x = do y <- return x; return y od`;
val f4_v_thm = m_translate f4_def;

val f5_def = Define `f5 l n1 = do n2 <- get_the_num; return (EL (n1 + n2) l) od`;
val f5_v_thm = m_translate f5_def;

val f6_def = Define `f6 l n = f5 l n`;
val f6_v_thm = m_translate f6_def;

val f7_def = Define `f7 x y z = f1 x y z`;
val f7_v_thm = m_translate f7_def;

val f8_def = Define `(f8 (x::xs) n = (do l <- f8 xs n; return (1+l) od)) /\
(f8 [] n = return (n : num))`;
val f8_v_thm = m_translate f8_def;

val f9_def = Define `
(f9 (x::xs) n = (do l <- f9 xs n; return (1+l) od)) /\
(f9 [] n = return ((HD n) : num))`;
val f9_v_thm = m_translate f9_def;

val f10_def = Define `
f10 y = handle_Fail (do x <- (raise_Fail "fail"); return x od) (\e. return e)`;
val f10_v_thm = m_translate f10_def;

val f11_def = Define `
f11 x = case x of [] => return (0 : num)
                | x::xs => (do l <- f11 xs; return (1 + l) od)`;
val f11_v_thm = m_translate f11_def;
val f11_side_def = fetch "testPrecondProg" "f11_side_def"
val f11_side_true = Q.prove(`!xs st. f11_side st xs`,
                            Induct \\ rw[Once f11_side_def]);

val f12_def = Define`
f12 x = ((return (1:num)) otherwise (return 0))`;
val f12_v_thm = m_translate f12_def;

(* Mutually recursive function with preconditions *)
val _ = Hol_datatype`
  tree = T1 of num list | T2 of tree list`;
val _ = register_type ``:tree``;
val TREE_TYPE_def = theorem"TREE_TYPE_def";

val _ = ParseExtras.temp_tight_equality();

val tree_sum_def = Define `
tree_sum (T1 l) = return (HD l) /\
tree_sum (T2 x) = tree_suml x /\
tree_suml [] = return 0 /\
tree_suml (t::l) = do x1 <- tree_sum t; x2 <- tree_suml l; return (x1 + x2) od`;
val tree_sum_v_thm = m_translate tree_sum_def;

(* No precondition *)
val tree_sum2_def = Define `
tree_sum2 (T1 l) = return (1 : num) /\
tree_sum2 (T2 x) = tree_suml2 x /\
tree_suml2 [] = return 0 /\
tree_suml2 (t::l) = do x1 <- tree_sum2 t; x2 <- tree_suml2 l; return (x1 + x2) od`
val tree_sum2_v_thm = m_translate tree_sum2_def;

(* pattern matching *)
(* val tree_sum3_def = Define `
tree_sum3 (T1 l) = return (HD l) /\
tree_sum3 (T2 x) = tree_suml3 x /\
tree_suml3 [] = return 0 /\
tree_suml3 (t::l) = do x1 <- tree_sum3 t; x2 <- tree_suml3 l; return (x1 + x2) od`;
val tree_sum_v_thm = m_translate tree_sum_def; *)

val _ = export_theory ();
