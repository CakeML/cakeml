(*
  An example showing how to use the monadic translator to translate monadic
  array search functions, including exceptions.
 *)

open preamble ml_monad_translator_interfaceLib

val _ = new_theory "array_searchProg"

fun allowing_rebind f = Feedback.trace ("Theory.allow_rebinds", 1) f

(* Create the data type to handle the array. *)
Datatype:
  state_array = <| arr : num list |> (* single resizeable array *)
End

(* Data type for the exceptions *)
Datatype:
  state_exn = Subscript
End

val config =  global_state_config |>
              with_state ``:state_array`` |>
              with_exception ``:state_exn`` |>
              with_resizeable_arrays
                [("arr", ``[] : num list``,
                  ``Subscript``, ``Subscript``)];

(* Initialize the translation *)
val _ = start_translation config;

(* Monadic definitions *)

val linear_search_aux_def = allowing_rebind (mtDefine "linear_search_aux" `
  linear_search_aux (value:num) (start_index:num) =
    do
      len <- arr_length;
      if start_index ≥ len then
        return NONE
      else
        do
          elem <- (arr_sub start_index);
          if elem = value then
            return (SOME start_index)
          else
            linear_search_aux value (start_index + 1)
        od
    od`)
(
  rw[fetch "-" "arr_length_def"] >>
  rw[ml_monadBaseTheory.Marray_length_def] >>
  rw[fetch "-" "arr_sub_def"] >>
  rw[ml_monadBaseTheory.Marray_sub_def] >>
  WF_REL_TAC `measure (λ (value, start, state) . LENGTH state.arr - start)`
);

Definition linear_search_def:
  linear_search value = linear_search_aux value 0n
End


Definition binary_search_aux_def:
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
Termination
  simp[]>>
  WF_REL_TAC `measure (λ (value, start, finish) . finish - start)`>>
  rw[]>>
  intLib.ARITH_TAC
End

Definition binary_search_def:
  binary_search value =
    do len <- arr_length; binary_search_aux value 0 len od
End

(* Monadic translation *)

val linear_search_aux_v_thm = m_translate linear_search_aux_def
val linear_search_v_thm = m_translate linear_search_def;

val binary_search_aux_v_thm = m_translate binary_search_aux_def;
val binary_search_v_thm = m_translate binary_search_def;

val _ = export_theory ();
