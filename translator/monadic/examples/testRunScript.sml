(*
  An example showing how to make use of m_translate_run
*)

open preamble ml_monadBaseLib
open ml_monad_translatorTheory ml_monad_translatorLib

val _ = new_theory "testRun"
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
val refs_manip_list = [(the_num_name, get_the_num_def, set_the_num_def)];
val rarrays_manip_list = rarray_manip_funs;
val farrays_manip_list = [] : (string * thm * thm * thm * thm * thm) list;

val store_hprop_name = "STATE_STORE";
val state_type = ``:state_refs``;
val exn_ri_def = STATE_EXN_TYPE_def;
val store_pinv_def_opt = NONE : thm option;

(**)
val add_type_theories = [] : string list;
(**)

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
val f11_side_def = fetch "testRun" "f11_side_def"
val f11_side_true = Q.prove(`!xs st. f11_side st xs`,
                            Induct \\ rw[Once f11_side_def]);

val f12_def = Define`
f12 x = ((return (1:num)) otherwise (return 0))`;
val f12_v_thm = m_translate f12_def;

val f13_def = Define `f13 l1 n1 l2 n2 = do x1 <- f5 l1 n1; f5 l2 n2 od`;
val f13_v_thm = m_translate f13_def;

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

(* m_translate_run *)
val r1_def = Define `r1 x y z st = run (f1 x y z) st`;
val r1_v_thm = m_translate_run r1_def;

val r2_def = Define `r2 x y z st = run (f2 x y z) st`;
val r2_v_thm = m_translate_run r2_def;

val r3_def = Define `r3 x st = run (f3 x) st`;
val r3_v_thm = m_translate_run r3_def;

val r4_def = Define `r4 x st = run (f4 x) st`;
val r4_v_thm = m_translate_run r4_def;

val r5_def = Define `r5 l n1 st = run (f5 l n1) st`;
val r5_v_thm = m_translate_run r5_def;

val r6_def = Define `r6 l n1 st = run (f6 l n1) st`;
val r6_v_thm = m_translate_run r6_def;

val r7_def = Define `r7 x y z st = run (f7 x y z) st`;
val r7_v_thm = m_translate_run r7_def;

val r8_def = Define `r8 xs n st = run (f8 xs n) st`;
val r8_v_thm = m_translate_run r8_def;

val r9_def = Define `r9 xs n st = run (f9 xs n) st`;
val r9_v_thm = m_translate_run r9_def;

val r10_def = Define `r10 x st = run (f10 x) st`;
val r10_v_thm = m_translate_run r10_def;

val r11_def = Define `r11 x st = run (f11 x) st`;
val r11_v_thm = m_translate_run r11_def;

val r12_def = Define `r12 x st = run (f12 x) st`;
val r12_v_thm = m_translate_run r12_def;

val r13_def = Define `r13 w x y z st = run (f13 w x y z) st`;
val r13_v_thm = m_translate_run r13_def;

val r14_def = Define `r14 l n1 = run (f5 l n1) <| the_num := 0; the_num_array := []; the_int_array := [] |>`;
val def = r14_def;
val r14_v_thm = m_translate_run r14_def;

val _ = export_theory ();
