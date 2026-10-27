(*
  An example showing how to use the monadic translator with
  references, arrays and exceptions.
*)
Theory array_local_stateProg
Libs
  preamble ml_monad_translator_interfaceLib
Ancestors
  ml_monad_translator

val _ = set_up_monadic_translator ();

val _ = patternMatchesSyntax.temp_enable_pmatch();

(* Create the data type to handle the references *)
Datatype:
  state_refs = <|
                 ref1    : num ;
                 ref2    : int;
                 rarray1 : num list ;
                 rarray2 : int list;
                 farray1 : num list;
                 farray2 : int list;
                 fbarray : word8 list;
                 rbarray : word8 list;
                 fbits : bool list;
                 rbits : bool list;
                |>
End

(* Data type for the exceptions *)
Datatype:
  state_exn = Fail string | Subscript
End

val config =  local_state_config |>
              with_state ``:state_refs`` |>
              with_exception ``:state_exn`` |>
              with_refs [
                ("ref1", ``0 : num``),
                ("ref2", ``0 : int``)
              ] |>
              with_resizeable_arrays [
                ("rarray1", ``[] : num list``, ``Subscript``, ``Subscript``),
                ("rarray2", ``[] : int list``, ``Subscript``, ``Subscript``),
                ("rbarray", ``[] : word8 list``, ``Subscript``, ``Subscript``)
              ] |>
              with_fixed_arrays [
                ("farray1", ``0 : num``, 0, ``Subscript``, ``Subscript``),
                ("farray2", ``0 : num``, 0, ``Subscript``, ``Subscript``),
                ("fbarray", ``0w : word8``, 0, ``Subscript``, ``Subscript``)
              ] |>
              (* bool list arrays stored as byte arrays, 8 bools per byte *)
              with_fixed_bool_arrays [
                ("fbits", 0, ``Subscript``, ``Subscript``)
              ] |>
              with_resizeable_bool_arrays [
                ("rbits", ``Subscript``, ``Subscript``)
              ];

val _ = start_translation config;

Overload failwith = ``raise_Fail``


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

(* word8 list arrays are stored as CakeML byte arrays *)
Definition test7_def:
  test7 n =
  do
      x <- fbarray_sub n;
      update_fbarray n (x + 1w);
      fbarray_length
  od
End
val test7_v_thm = test7_def |> m_translate;

Definition test8_def:
  test8 n =
  do
      alloc_rbarray n 0w;
      x <- rbarray_sub 0;
      update_rbarray 0 (x + 1w);
      rbarray_length
  od
End
val test8_v_thm = test8_def |> m_translate;

(* bool list arrays are stored as CakeML byte arrays, 8 bools per byte *)
Definition test9_def:
  test9 n =
  do
      x <- fbits_sub n;
      update_fbits n (~x);
      fbits_length
  od
End
val test9_v_thm = test9_def |> m_translate;

(* alloc_rbits n allocates 8 * n bools, all F *)
Definition test10_def:
  test10 n =
  do
      alloc_rbits n;
      x <- rbits_sub 0;
      update_rbits 0 (~x);
      rbits_length
  od
End
val test10_v_thm = test10_def |> m_translate;

(* run translations *)
(* test 1 *)
val run_init_state_def =
  define_run ``:state_refs`` ["farray1", "farray2", "fbarray", "fbits"]
             "init_state"

Definition run_test1_def:
  run_test1 (x: num) (state: init_state) = run_init_state (test1 x) (state: init_state)
End
val run_test1_v_thm = m_translate_run run_test1_def;

Definition crun_test1_def:
  crun_test1 x =
    run_init_state (test1 x) (init_state 0 0 [] [] (10, 0) (11, 0) (12, 0w) [] 2 [])
End
val crun_test1_v_thm = m_translate_run crun_test1_def;

(* test 2 *)
Definition run_test2_def:
  run_test2 x state = run_init_state (test2 x) state
End
val run_test2_v_thm = m_translate_run run_test2_def;

Definition crun_test2_def:
  crun_test2 x =
    run_init_state (test2 x) (init_state 0 0 [] [] (10, 0) (11, 0) (12, 0w) [] 2 [])
End
val crun_test2_v_thm = m_translate_run crun_test2_def;

(* test 3 *)
Definition run_test3_def:
  run_test3 x state = run_init_state (test3 x) state
End
val run_test3_v_thm = m_translate_run run_test3_def;

Definition crun_test3_def:
  crun_test3 x =
    run_init_state (test3 x) (init_state 0 0 [] [] (10, 0) (11, 0) (12, 0w) [] 2 [])
End
val crun_test3_v_thm = m_translate_run crun_test3_def;

(* test 4 *)
Definition run_test4_def:
  run_test4 n x state = run_init_state (test4 n x) state
End
val run_test4_v_thm = m_translate_run run_test4_def;

Definition crun_test4_def:
  crun_test4 n x =
    run_init_state (test4 n x) (init_state 0 0 [] [] (10, 0) (11, 0) (12, 0w) [] 2 [])
End
val crun_test4_v_thm = m_translate_run crun_test4_def;

(* test 5 *)
Definition run_test5_def:
  run_test5 n x state = run_init_state (test5 n x) state
End
val run_test5_v_thm = m_translate_run run_test5_def;

Definition crun_test5_def:
  crun_test5 n x =
    run_init_state (test5 n x) (init_state 0 0 [] [] (10, 0) (11, 0) (12, 0w) [] 2 [])
End
val crun_test5_v_thm = m_translate_run crun_test5_def;

(* test 6 *)
Definition run_test6_def:
  run_test6 n x state = run_init_state (test6 n x) state
End
val run_test6_v_thm = m_translate_run run_test6_def;

Definition crun_test6_def:
  crun_test6 n x =
    run_init_state (test6 n x) (init_state 0 0 [] [] (10, 0) (11, 0) (12, 0w) [] 2 [])
End
val crun_test6_v_thm = m_translate_run crun_test6_def;

(* test 7 *)
Definition run_test7_def:
  run_test7 n state = run_init_state (test7 n) state
End
val run_test7_v_thm = m_translate_run run_test7_def;

Definition crun_test7_def:
  crun_test7 n =
    run_init_state (test7 n) (init_state 0 0 [] [] (10, 0) (11, 0) (12, 0w) [] 2 [])
End
val crun_test7_v_thm = m_translate_run crun_test7_def;

(* test 8 *)
Definition run_test8_def:
  run_test8 n state = run_init_state (test8 n) state
End
val run_test8_v_thm = m_translate_run run_test8_def;

Definition crun_test8_def:
  crun_test8 n =
    run_init_state (test8 n) (init_state 0 0 [] [] (10, 0) (11, 0) (12, 0w) [] 2 [])
End
val crun_test8_v_thm = m_translate_run crun_test8_def;

(* test 9 *)
Definition run_test9_def:
  run_test9 n state = run_init_state (test9 n) state
End
val run_test9_v_thm = m_translate_run run_test9_def;

(* fbits starts as 2 bytes, i.e. 16 bools that are all F *)
Definition crun_test9_def:
  crun_test9 n =
    run_init_state (test9 n) (init_state 0 0 [] [] (10, 0) (11, 0) (12, 0w) [] 2 [])
End
val crun_test9_v_thm = m_translate_run crun_test9_def;

(* test 10 *)
Definition run_test10_def:
  run_test10 n state = run_init_state (test10 n) state
End
val run_test10_v_thm = m_translate_run run_test10_def;

Definition crun_test10_def:
  crun_test10 n =
    run_init_state (test10 n) (init_state 0 0 [] [] (10, 0) (11, 0) (12, 0w) [] 2 [])
End
val crun_test10_v_thm = m_translate_run crun_test10_def;

(* ... *)
