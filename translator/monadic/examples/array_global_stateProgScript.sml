(*
  An example showing how to use the monadic translator with
  references, arrays and exceptions.
*)
open preamble ml_monad_translator_interfaceLib

val _ = new_theory "array_global_stateProg"

(* Create the data type to handle the references *)
Datatype:
  state_references = <|
                   ref1 : num ;
                   ref2 : int;
                   rarray1 : num list ;
                   rarray2 : int list;
                   farray1 : num list;
                   farray2 : int list;
                   |>
End

(* Data type for the exceptions *)
Datatype:
  state_exn = Fail string | Subscript
End

val config =  global_state_config |>
              with_state ``:state_references`` |>
              with_exception ``:state_exn`` |>
              with_refs [("ref1", ``36 : num``),
                         ("ref2", ``42 : int``)] |>
              with_fixed_arrays [
                ("farray1", ``0 : num``, 12,
                  ``Subscript``, ``Subscript``),
                ("farray2", ``0 : int``, 7,
                  ``Subscript``, ``Subscript``)
              ] |>
              with_resizeable_arrays [
                ("rarray1", ``[] : num list``,
                  ``Subscript``, ``Subscript``),
                ("rarray2", ``[] : int list``,
                  ``Subscript``, ``Subscript``)
              ];

Overload failwith = ``raise_Fail``

val _ = start_translation config;

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
