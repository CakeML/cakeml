(*
 * An example showing how to use the monadic translator to translate monadic
 * array search functions, including exceptions.
 *)
open preamble ml_monad_translatorLib
open ml_monadBaseLib ml_monadStoreLib
open ml_monad_translatorTheory ml_monad_translatorLib ml_monadStoreLib

val _ = new_theory "polyTest"

val _ = ParseExtras.temp_loose_equality();
val _ = patternMatchesLib.ENABLE_PMATCH_CASES();
val _ = monadsyntax.temp_add_monadsyntax()

(* Need to hide "state" because of semanticPrimitives *)
val _ = hide "state";
val _ = (use_full_type_names := false);

val _ = temp_overload_on ("monad_bind", ``st_ex_bind``);
val _ = temp_overload_on ("monad_unitbind", ``\x y. st_ex_bind x (\z. y)``);
val _ = temp_overload_on ("monad_ignore_bind", ``\x y. st_ex_bind x (\z. y)``);
val _ = temp_overload_on ("return", ``st_ex_return``);


(* Create the data type to handle the array. *)
val _ = Datatype `
  state_refs = <| arr : 'a list; farr : unit list |>`;
  (* single resizeable array *)

val gen_var = ``:'state``
val state_type = ``:^(gen_var) state_refs``
(*
val _ = Datatype `
  state_refs = <| arr : num list |>`;
val state_type = ``:state_refs``;
*)
(* Generate the monadic functions to manipulate the reference(s). *)
val access_funs = define_monad_access_funs (state_type);

(* Data type for the exceptions *)
val _ = Hol_datatype`
  state_exn = Fail of string | Subscript`;

val _ = register_type ``:tvarN``;
val _ = register_exn_type ``:state_exn``;
val STATE_EXN_TYPE_def = theorem"STATE_EXN_TYPE_def";

(* Monadic functions to handle the exceptions *)
val exn_functions =
  define_monad_exception_functions ``:state_exn`` state_type;
val _ = temp_overload_on ("failwith", ``raise_Fail``);

val sub_exn = ``Subscript``;
val update_exn = ``Subscript``;

val _ = register_type ``:unit``;
val rarrays_manip_list =
  define_MRarray_manip_funs [hd access_funs] sub_exn update_exn;
val farrays_manip_list =
  define_MFarray_manip_funs (tl access_funs) sub_exn update_exn;

val store_hprop_name = "STATE_STORE";

val exn_ri_def = STATE_EXN_TYPE_def;
val refs_manip_list = [];
val store_pinv_def_opt = NONE : thm option;
val add_type_theories = [];

val (monad_translation_params, exn_specs)  =
  start_dynamic_init_fixed_store_translation
    refs_manip_list
    rarrays_manip_list
    farrays_manip_list
    store_hprop_name
    state_type
    exn_ri_def
    exn_functions
    add_type_theories
    store_pinv_def_opt;
(*  TODO this example doesn't work with the new interface - why?
open preamble ml_monad_translator_interfaceLib

val _ = new_theory "polyTest"

val _ = patternMatchesLib.ENABLE_PMATCH_CASES();

(* Create the data type to handle the references *)
val _ = Hol_datatype `
  state_refs = <|
                 arr : 'state list ;
                 farr : unit list
                |>`;

(* Data type for the exceptions *)
val _ = Hol_datatype`
  state_exn = Fail of string | Subscript`;

val config =  local_state_config |>
              with_state ``:'state state_refs`` |>
              with_exception ``:state_exn`` |>
              with_resizeable_arrays [
                ("arr", ``[] : 'state list``, ``Subscript``, ``Subscript``)
              ] |>
              with_fixed_arrays [
                ("farr", ``() : unit``, 0, ``Subscript``, ``Subscript``)
              ];

val _ = start_translation config;
*)
val _ = temp_overload_on ("failwith", ``raise_Fail``);

val array_set_aux_def = Define `
  (array_set_aux _ [] = return ()) ∧
  (array_set_aux n (x::xs) = do
    update_arr n x;
    array_set_aux (n + 1) xs
  od)
`;

val array_set_def = Define `
  array_set l = array_set_aux 0 l
`;

val array_set_aux_v_thm = m_translate array_set_aux_def;
val array_set_v_thm = m_translate array_set_def;

val array_get_aux_def = Define `
  (array_get_aux 0 = return []) ∧
  (array_get_aux n = do
    rest <- array_get_aux (n - 1);
    elem <- arr_sub n;
    return (rest ++ [elem])
  od)
`;

val array_get_def = Define `
  array_get () = do
    len <- arr_length;
    array_get_aux len
  od
`
val array_get_aux_v_thm = m_translate array_get_aux_def;
val array_get_v_thm = m_translate array_get_def;

val binary_search_aux_def = tDefine "binary_search_aux" `
  binary_search_aux cmp value start finish =
    do
      len <- arr_length;
      if start ≥ finish ∨ finish > len then return NONE else
          let mid = (finish + start) DIV 2n in
            do
              elem <- arr_sub mid;
              if value = elem then return (SOME mid)
              else if (cmp value elem) then
                binary_search_aux cmp value start mid
              else
                binary_search_aux cmp value (mid + 1n) finish
            od
  od
`
  (
    WF_REL_TAC `measure (λ (_, _, start, finish) . finish - start)` >>
    rw[] >>
    fs[NOT_GREATER_EQ, NOT_GREATER, ADD1] >>
    `start <= (finish + start) DIV 2` by fs[X_LE_DIV]
    >- DECIDE_TAC
    >- fs[DIV_LT_X]
  );

val binary_search_def = Define `
  binary_search cmp value =
    do len <- arr_length; binary_search_aux cmp value 0 len od`;

val binary_search_aux_v_thm = m_translate binary_search_aux_def;
val binary_search_v_thm = m_translate binary_search_def;

val fast_binary_search_def = Define `
  (fast_binary_search [] _ _ = return []) ∧
  (fast_binary_search (x::xs) cmp value = do
      alloc_arr (LENGTH (x::xs)) x;
      array_set (x::xs);
      binary_search cmp value;
      array_get ()
    od)
`;

val LENGTH_v_thm = translate LENGTH;
val fast_binary_search_v_thm = m_translate fast_binary_search_def;

val run_init_state_def =
  ml_monadBaseLib.define_run state_type ["farr"] "init_state";

val run_fast_binary_search_def = Define `
  run_fast_binary_search l cmp value =
    run_init_state (fast_binary_search l cmp value) (init_state [] (0, ()))
`;

val run_fast_binary_search_v_thm = m_translate_run run_fast_binary_search_def;

val final_thm = run_fast_binary_search_v_thm |> DISCH_ALL |>
                REWRITE_RULE [definition "run_fast_binary_search_side_def"] |>
                REWRITE_RULE [ml_translatorTheory.PRECONDITION_def]
(*
   ⊢ EqualityType a ⇒
     (Eq (LIST_TYPE a) v2 --> Eq (a --> a --> BOOL) v1 --> Eq a value -->
      EXC_TYPE (LIST_TYPE a) STATE_EXN_TYPE) run_fast_binary_search
       run_fast_binary_search_v: thm
*)

(************************************)
(*
val test_case_def = Define `
  (test_case [] = return []) ∧
  (test_case (x::xs) = return (x::xs))
`
val test_case_v_thm = m_translate test_case_def

val test_def = Define `
  test x = do v <- (arr_sub x); return v od
`
val test_v_thm = m_translate test_def;
(*
   ⊢ (nsLookup $var$(%env1).v (Short "arr") = SOME init_arr) ⇒
     (lookup_cons (Short "Subscript") $var$(%env1) = SOME (0,ExnStamp 3)) ⇒
     ArrowP ro (STATE_STORE a init_arr,p) (PURE NUM) (MONAD a STATE_EXN_TYPE)
       test
       (Closure $var$(%env1) "v2"
          (Let (SOME "v1")
             (App Asub [App Opderef [Var (Short "arr")]; Var (Short "v2")])
             (Var (Short "v1")))): thm
*)
val _ = save_thm("test_v_thm", test_v_thm)

val test_alloc_def = Define `
  test_alloc n x = alloc_arr n x
`

val test_update_def = Define `
  test_update n x = update_arr n x
`
val test_update_v_thm = m_translate test_update_def
val test_alloc_def = test_alloc_def |> INST_TYPE [gamma |-> alpha]
val test_alloc_v_thm = m_translate test_alloc_def

val run_init_state_def = define_run state_type ["farr"] "init_state"

val run_test_def = Define `
  run_test x state = run_init_state (test x) state`;
val run_test_v_thm = m_translate_run run_test_def;
val _ = save_thm("run_test_v_thm", run_test_v_thm);

val crun_test_def = Define `
  crun_test x =
    run_init_state (test x) (init_state [] (0, ()))`;
val crun_test_v_thm = m_translate_run crun_test_def;
val _ = save_thm("crun_test_v_thm", crun_test_v_thm);
*)
val _ = export_theory ();
