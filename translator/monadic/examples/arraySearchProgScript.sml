(*
  An example showing how to use the monadic translator to translate monadic
  array search functions, including exceptions.
 *)

open preamble ml_monad_translator_interfaceLib

val _ = new_theory "arraySearchProg"

(* Create the data type to handle the array. *)
val _ = Datatype `
  state_array = <| arr : num list |>`; (* single resizeable array *)

(* Data type for the exceptions *)
val _ = Hol_datatype`
  state_exn = Subscript`;

val config =  global_state_config |>
              with_state ``:state_array`` |>
              with_exception ``:state_exn`` |>
              with_resizeable_arrays
                [("arr", ``[] : num list``,
                  ``Subscript``, ``Subscript``)];

(* Initialize the translation *)
val _ = start_translation config;

(* Monadic definitions *)

val linear_search_aux_def = tDefine "linear_search_aux" `
  linear_search_aux (value:num) (start_index:num) s =
    do
      len <- arr_length;
      (λ s1 .
        if start_index ≥ len then return NONE s1
        else do
          elem <- arr_sub start_index;
          (λ s2 .
            if elem = value then return (SOME start_index) s2
            else linear_search_aux value (start_index + 1) s2)
        od s1)
    od s`
(
  rw[fetch "-" "arr_length_def"] >>
  rw[ml_monadBaseTheory.Marray_length_def] >>
  rw[fetch "-" "arr_sub_def"] >>
  rw[ml_monadBaseTheory.Marray_sub_def] >>
  WF_REL_TAC `measure (λ (value, start, state) . LENGTH state.arr - start)`
);

val linear_search_def = Define `
  linear_search value = linear_search_aux value 0n`


val binary_search_aux_def = tDefine "binary_search_aux" `
  binary_search_aux value start finish =
    do
      len <- arr_length;
      if start ≥ finish ∨ finish > len then return NONE else
          let mid = (finish + start) DIV 2n in
            do
              elem <- arr_sub mid;
              if value = elem then return (SOME mid)
              else if value < elem then
                binary_search_aux value start mid
              else
                binary_search_aux value (mid + 1n) finish
            od
  od
`
  (
    WF_REL_TAC `measure (λ (_, start, finish) . finish - start)` >>
    rw[] >>
    fs[NOT_GREATER_EQ, NOT_GREATER, ADD1] >>
    `start <= (finish + start) DIV 2` by fs[X_LE_DIV]
    >- DECIDE_TAC
    >- fs[DIV_LT_X]
  );

val binary_search_def = Define `
  binary_search value =
    do len <- arr_length; binary_search_aux value 0 len od`;

(* Monadic translation *)

Theorem pull_monad_state_if[simp]:
  ∀ b f g x . (λ s . if b then f s else g s) = (λ s . (if b then f else g) s)
Proof
  fs[Once COND_RATOR]
QED

Theorem remove_state_arg[simp]:
  ∀ f g . (∀ s . (f s = g s)) ⇔ (f = λ a . g a)
Proof
  rw[] >>
  EQ_TAC >>
  rw[] >>
  fs[ETA_THM, EQ_EXT]
QED

val linear_search_aux_def = linear_search_aux_def |>
                            REWRITE_RULE [pull_monad_state_if] |>
                            CONV_RULE (DEPTH_CONV ETA_CONV) |>
                            REWRITE_RULE [remove_state_arg] |>
                            REWRITE_RULE [ETA_THM]

val linear_search_aux_v_thm = m_translate linear_search_aux_def

val linear_search_aux_helper = theorem "linear_search_aux_helper_0"
val linear_search_aux_ind = theorem "linear_search_aux_ind"

val linear_search_precond = Q.prove (
  `^(first is_forall (hyp linear_search_aux_v_thm))`,
  ho_match_mp_tac linear_search_aux_ind >>
  rw[] >>
  match_mp_tac linear_search_aux_helper >>
  rpt strip_tac >>
  last_x_assum match_mp_tac >>
  fs[definition "arr_length_def", definition "arr_sub_def"] >>
  fs[fetch "ml_monadBase" "Marray_length_def"] >>
  fs[fetch "ml_monadBase" "Marray_sub_def"]
);

val _ = linear_search_precond |> update_precondition
val _ = (fetch "ml_translator" "EqualityType_NUM_BOOL") |> update_precondition

val linear_search_aux_v_thm = theorem "linear_search_aux_v_thm"
val linear_search_v_thm = m_translate linear_search_def;

val binary_search_aux_v_thm = m_translate binary_search_aux_def;
val binary_search_v_thm = m_translate binary_search_def;

val _ = export_theory ();
