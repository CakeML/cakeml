(*
  Test the monadic translator's handling of assumptions
*)
open preamble ml_translatorLib ml_translatorTheory
open ml_monadBaseLib ml_monadBaseTheory
open ml_monad_translatorLib ml_monad_translatorTheory

(***********************)
val _ = new_theory "testAssum";

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
  state_refs = <| the_num : num ; the_string : string|>`;

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
     (the_string_name, get_the_string_def, set_the_string_def)] = access_funs;

(* Prepare the translation *)
val init_num_def = Define `init_num = (0 : num)`;
val init_string_def = Define `init_string = ""`;
val refs_init_list = [(the_num_name, init_num_def, get_the_num_def, set_the_num_def),
		      (the_string_name, init_string_def, get_the_string_def, set_the_string_def)];

val rarrays_init_list = [] : (string * thm * thm * thm * thm * thm * thm * thm) list;
val farrays_init_list = [] : (string * (int * thm) * thm * thm * thm * thm * thm) list;


val store_hprop_name = "STATE_STORE";
val state_type = ``:state_refs``;
val exn_ri_def = STATE_EXN_TYPE_def;

val STATE_PINV_def = Define `STATE_PINV = \state. EVEN state.the_num /\ (state.the_string = "")`;
val STATE_PINV_VALID = Q.prove(`(state.the_num = 0) /\ (state.the_string = "") ==> STATE_PINV state`,
rw[STATE_PINV_def]);

val store_pinv_opt = SOME(STATE_PINV_def, STATE_PINV_VALID);

val add_type_theories = [] : string list;

(* val store_pinv_def = STATE_PINV_def *)

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
					      add_type_theories
                                              store_pinv_opt
                                              extra_hprop;

(* TESTS *)
val _ = set_trace "assumptions" 1;
val _ = Globals.max_print_depth := 40;

val pf_def = Define `pf x = (if EVEN x then x else ARB)`;
val res = translate arithmeticTheory.EVEN;
val pf_v_thm = translate pf_def;
val pf_side_def = definition"pf_side_def"

val mf_def = Define `mf () = do x <- get_the_num; return(pf x) od`;
val def = mf_def;
val res = m_translate mf_def;
val mf_side_def = definition"mf_side_def";

val mf2_def = Define `mf2 () = do x <- get_the_num; set_the_num x; return (); od`;
val def = mf2_def;
val res = m_translate mf2_def;

val mf3_def = Define `mf3 x = set_the_num x`;
val def = mf3_def;
val mf3_v_thm = m_translate mf3_def;
val mf3_side_def = definition"mf3_side_def";

val mf4_def = Define `mf4 () = get_the_num`;
val def = mf4_def;
val mf4_v_thm = m_translate mf4_def;

val mf5_def = Define `mf5 x = do y <- get_the_num; return (x+y) od`;
val def = mf5_def;
val mf5_v_thm = m_translate mf5_def;

(**)
val mf6_def = Define `mf6 l = dtcase l of [] => return 0 | x::l => return 1`;
val def = mf6_def;

val length_v_thm = translate listTheory.LENGTH;
val ZIP_def2 = Q.prove(`ZIP (l1,l2) = dtcase (l1,l2) of
    (x::l1,y::l2) => (x,y)::(ZIP (l1,l2))
 |  ([],[]) => []
 | other => []`,
Cases_on `l1`
\\ Cases_on `l2`
\\ fs[ZIP_def]);

val zip_v_thm = translate ZIP_def2;

val mf7_def = Define `mf7 l1 l2 = do z <- if LENGTH l1 = LENGTH l2 then return () else failwith ""; return (ZIP (l1, l2)) od`;
val def = mf7_def;
val mf7_v_thm = m_translate def;

val _ = export_theory ();
