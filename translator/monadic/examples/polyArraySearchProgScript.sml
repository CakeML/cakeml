(*
 An example showing how to use the monadic translator to translate polymorphic
 monadic array search functions, including exceptions.
*)

open preamble ml_monad_translator_interfaceLib

val _ = new_theory "polyArraySearchProg"

val _ = patternMatchesLib.ENABLE_PMATCH_CASES();
(* TODO still some problems with type variables - if 'a not used below,
   some translations fail *)

(* Create the data type to handle the references *)
val _ = Hol_datatype `
  state_refs = <|
                 arr : 'a list ;
                 farr : unit list
                |>`;

val state_type = ``:'state state_refs``;

(* Data type for the exceptions *)
val _ = Hol_datatype`
  state_exn = Fail of string | Subscript`;

val config =  local_state_config |>
              with_state state_type |>
              with_exception ``:state_exn`` |>
              with_resizeable_arrays [
                ("arr", ``[] : 'a list``, ``Subscript``, ``Subscript``)
              ] |>
              with_fixed_arrays [
                ("farr", ``() : unit``, 0, ``Subscript``, ``Subscript``)
              ];

val _ = start_translation config;

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
  define_run state_type ["farr"] "init_state";

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

val _ = export_theory ();
