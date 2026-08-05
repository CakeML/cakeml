(*
  An example showing how to use the monadic translator with
  references, arrays and exceptions.
*)
Theory array_global_stateProg
Libs
  preamble ml_monad_translator_interfaceLib
Ancestors
  ml_monad_translator

val _ = set_up_monadic_translator ();

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

Definition test1_def:
  test1 x =
  do
      y <- get_ref1;
      return (x + y)
  od
End
val test1_v_thm = test1_def |> m_translate;

Definition test2_def:
  test2 n =
  do
      x <- rarray1_sub n;
      return x
  od
End
val test2_v_thm = test2_def |> m_translate;

Definition test3_def:
  test3 n =
  do
      x <- farray1_sub n;
      return x
  od
End
val test3_v_thm = test3_def |> m_translate;

Definition test4_def:
  test4 n x = update_rarray1 n x
End
val test4_v_thm = test4_def |> m_translate;

Definition test5_def:
  test5 n x = update_farray1 n x
End
val test5_v_thm = test5_def |> m_translate;

Definition test6_def:
  test6 n x = alloc_rarray1 n x
End
val test6_v_thm = test6_def |> m_translate;

(* ... *)
