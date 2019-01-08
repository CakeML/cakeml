(*
 * An example showing how to use the monadic translator to translate monadic
 * array search functions, including exceptions.
 *)

open preamble basisProgTheory
open ml_monadBaseLib ml_monadStoreLib
open ml_monad_translatorTheory ml_monad_translatorLib
open TextIOProofTheory cfMonadLib

val _ = new_theory "array_searchProg"
val _ = translation_extends "basisProg";

val _ = ParseExtras.temp_loose_equality();
val _ = patternMatchesLib.ENABLE_PMATCH_CASES();
val _ = monadsyntax.temp_add_monadsyntax()

val _ = temp_overload_on ("monad_bind", ``st_ex_bind``);
val _ = temp_overload_on ("monad_unitbind", ``\x y. st_ex_bind x (\z. y)``);
val _ = temp_overload_on ("monad_ignore_bind", ``\x y. st_ex_bind x (\z. y)``);
val _ = temp_overload_on ("return", ``st_ex_return``);

(* Need to hide "state" because of semanticPrimitives *)
val _ = hide "state";

val _ = (use_full_type_names := false);

(* Create the data type to handle the array. *)
val _ = Datatype `
  state_refs = <| arr : num list |>`; (* single resizeable array *)

(* Generate the monadic functions to manipulate the reference(s). *)
val access_funs = define_monad_access_funs (``:state_refs``);
val [(arr_name, get_arr_def, set_arr_def)] = access_funs;

(* Data type for the exceptions *)
val _ = Hol_datatype`
  state_exn = Fail of string | Subscript`;

val _ = register_type ``:tvarN``;
val _ = register_exn_type ``:state_exn``;
val STATE_EXN_TYPE_def = theorem"STATE_EXN_TYPE_def";

(* Monadic functions to handle the exceptions *)
val exn_functions =
  define_monad_exception_functions ``:state_exn`` ``:state_refs``;
val _ = temp_overload_on ("failwith", ``raise_Fail``);

val sub_exn = ``Subscript``;
val update_exn = ``Subscript``;

val rarray_manip_funs =
  define_MRarray_manip_funs access_funs sub_exn update_exn;
fun mk_rarr_init (name,get,set,len,sub,upd,alloc) init =
  (name,init,get,set,len,sub,upd,alloc);

(* Prepare the translation *)
val init_arr_def = Define `init_arr = [] : num list`;
val rarrays_init_values = [init_arr_def];
val rarrays_init_list =
  List.map
  (fn ((x1, x2, x3, x4, x5, x6, x7), x) => (x1, x, x2, x3, x4, x5, x6, x7))
  (zip rarray_manip_funs rarrays_init_values);

val store_hprop_name = "STATE_STORE";
val state_type = ``:state_refs``;

val exn_ri_def = STATE_EXN_TYPE_def;
val store_pinv_opt = NONE : (thm * thm) option;
val extra_hprop = NONE : term option;

val refs_init_list = [];
val farrays_init_list = [];

(* Initialize the translation *)
val (monad_parameters, store_translation, exn_specs) =
    start_static_init_fixed_store_translation
                refs_init_list
                rarrays_init_list
                farrays_init_list
                store_hprop_name
                state_type
                exn_ri_def
                exn_functions
                []
                store_pinv_opt extra_hprop;

(* Monadic translations *)

(* HOW TO PROVE TERMINATION? *)
(*
val linear_search_aux_def = Define `
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
    od
`
*)

val linear_search_aux_def = Define `
  linear_search_aux (value:num) (start_index:num) =
    do
      if start_index = 0n then
        return NONE
      else
        do
          elem <- (arr_sub (start_index - 1));
          if elem = value then
            return (SOME start_index)
          else
            linear_search_aux value (start_index - 1)
        od
    od
`

val linear_search_def = Define `
  linear_search value = do len <- arr_length; linear_search_aux value len od
`

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

val linear_search_aux_v = m_translate linear_search_aux_def;
val linear_search_v = m_translate linear_search_def;

val binary_search_aux_v = m_translate binary_search_aux_def;
val binary_search_v = m_translate binary_search_def;

val _ = export_theory ();
