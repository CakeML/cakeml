(*
  An example showing how to use the monadic translator with
  references, arrays and exceptions.
*)

open preamble ml_monad_translator_interfaceLib

val _ = new_theory "array_local_stateProg"

val _ = patternMatchesLib.ENABLE_PMATCH_CASES();

(* Create the data type to handle the references *)
val _ = Hol_datatype `
  state_refs = <|
                 ref1    : num ;
                 ref2    : int;
                 rarray1 : num list ;
                 rarray2 : int list;
                 farray1 : num list;
                 farray2 : int list;
                |>`;

(* Data type for the exceptions *)
val _ = Hol_datatype`
  state_exn = Fail of string | Subscript`;

val config =  local_state_config |>
              with_state ``:state_refs`` |>
              with_exception ``:state_exn`` |>
              with_refs [
                ("ref1", ``0 : num``),
                ("ref2", ``0 : int``)
              ] |>
              with_resizeable_arrays [
                ("rarray1", ``[] : num list``, ``Subscript``, ``Subscript``),
                ("rarray2", ``[] : int list``, ``Subscript``, ``Subscript``)
              ] |>
              with_fixed_arrays [
                ("farray1", ``0 : num``, 0, ``Subscript``, ``Subscript``),
                ("farray2", ``0 : num``, 0, ``Subscript``, ``Subscript``)
              ];

val _ = start_translation config;

val _ = temp_overload_on ("failwith", ``raise_Fail``);

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

val test4_def = Define `
  test4 n x = update_rarray1 n x`;
val test4_v_thm = test4_def |> m_translate;

val test5_def = Define `
  test5 n x = update_farray1 n x`;
val test5_v_thm = test5_def |> m_translate;

val test6_def = Define `
  test6 n x = alloc_rarray1 n x`;
val test6_v_thm = test6_def |> m_translate;

(* run translations *)
(* test 1 *)
val run_init_state_def =
  define_run ``:state_refs`` ["farray1", "farray2"] "init_state"

val run_test1_def = Define `
  run_test1 x state = run_init_state (test1 x) state`;
val run_test1_v_thm = m_translate_run run_test1_def;

val crun_test1_def = Define `
  crun_test1 x =
    run_init_state (test1 x) (init_state 0 0 [] [] (10, 0) (11, 0))`;
val crun_test1_v_thm = m_translate_run crun_test1_def;

(* test 2 *)
val run_test2_def = Define `
  run_test2 x state = run_init_state (test2 x) state`;
val run_test2_v_thm = m_translate_run run_test2_def;

val crun_test2_def = Define `
  crun_test2 x =
    run_init_state (test2 x) (init_state 0 0 [] [] (10, 0) (11, 0))`;
val crun_test2_v_thm = m_translate_run crun_test2_def;

(* test 3 *)
val run_test3_def = Define `
  run_test3 x state = run_init_state (test3 x) state`;
val run_test3_v_thm = m_translate_run run_test3_def;

val crun_test3_def = Define `
  crun_test3 x =
    run_init_state (test3 x) (init_state 0 0 [] [] (10, 0) (11, 0))`;
val crun_test3_v_thm = m_translate_run crun_test3_def;

(* test 4 *)
val run_test4_def = Define `
  run_test4 n x state = run_init_state (test4 n x) state`;
val run_test4_v_thm = m_translate_run run_test4_def;

val crun_test4_def = Define `
  crun_test4 n x =
    run_init_state (test4 n x) (init_state 0 0 [] [] (10, 0) (11, 0))`;
val crun_test4_v_thm = m_translate_run crun_test4_def;

(* test 5 *)
val run_test5_def = Define `
  run_test5 n x state = run_init_state (test5 n x) state`;
val run_test5_v_thm = m_translate_run run_test5_def;

val crun_test5_def = Define `
  crun_test5 n x =
    run_init_state (test5 n x) (init_state 0 0 [] [] (10, 0) (11, 0))`;
val crun_test5_v_thm = m_translate_run crun_test5_def;

(* test 6 *)
val run_test6_def = Define `
  run_test6 n x state = run_init_state (test6 n x) state`;
val run_test6_v_thm = m_translate_run run_test6_def;

val crun_test6_def = Define `
  crun_test6 n x =
    run_init_state (test6 n x) (init_state 0 0 [] [] (10, 0) (11, 0))`;
val crun_test6_v_thm = m_translate_run crun_test6_def;

(* ... *)

val _ = export_theory ();
