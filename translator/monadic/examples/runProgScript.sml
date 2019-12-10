(*
  An example of how to translate `run`
*)
open preamble ml_monad_translator_interfaceLib

val _ = new_theory "runProg"

val _ = patternMatchesLib.ENABLE_PMATCH_CASES();

(* Create the data type to handle the references *)
Datatype:
  state_references = <| the_num : num |>
End

val config =  local_state_config |>
              with_state ``:state_references`` |>
              with_refs [
                ("the_num", ``0 : num``)
              ];

val _ = start_translation config;

(* Monadic translations *)
val _ = temp_tight_equality ();

val test1_def = Define `
  test1 x = do y <- get_the_num; return (x + y) od`;
val test1_v_th = m_translate test1_def;

val test2_def = Define `
  test2 (x : num) y = return (x + y)`;
val test2_v_th = m_translate test2_def;

val test3_def = Define `
test3 n m z =
   do
       test2 n z;
       x <- test1 m;
       return x
   od`;
val test3_v_th = m_translate test3_def;

(* Several non recursive functions *)
val run_test3_def = Define `
  run_test3 n m z refs = run (test3 n m z) refs`;

val run_test3_v_th = m_translate_run run_test3_def;
val test3'_def = Define `
  test3' (n, m, z, refs) = run_test3 n m z refs :(num, unit) exc`;
val res = translate test3'_def;

(* Recursive function *)
val test4_def = Define `
  test4 (x::l) = do y <- test4 l; return (x + y) od /\
  test4 []     = return (0 : num)`;
val test4_v_th = m_translate test4_def;

val run_test4_def = Define `
  run_test4 l state = run (test4 l) state`;
val run_test4_v_thm = m_translate_run run_test4_def;

(* Mutual recursion *)
Datatype:
  data = C1 num | C2 (data list)
End

val _ = register_type ``:data``;

val data_length_def = Define `
  data_length1 (C1 x)  = return x /\
  data_length1 (C2 x)  = data_length2 x /\
  data_length2 []      = return 0 /\
  data_length2 (x::xl) = do
      y1 <- data_length1 x;
      y2 <- data_length2 xl;
      return (y1 + y2)
    od`;
val data_length_v_th = m_translate data_length_def;

val run_data_length1_def = Define `
  run_data_length d state = run (data_length1 d) state`;
val run_data_length1_v_thm = m_translate_run run_data_length1_def;

(* Other test *)
val test6_def = Define `
  test6 (x::l) = do y <- test6 l; z <- test1 x; return (x + y + z) od /\
  test6 []     = return (0 : num)`;
val test6_v_th = m_translate test6_def;

val run_test6_def = Define `
  run_test6 l state = run (test6 l) state`;
val run_test6_v_th = m_translate_run run_test6_def;

(* Mix standard and monadic functions *)
val LENGTH_v_thm = translate LENGTH;

val test7_def = Define `
  test7 x l = do y <- test1 x; return (y + (LENGTH l)) od`
val test7_v_thm = m_translate test7_def;

val run_test7_def = Define `
  run_test7 x l state = run (test7 x l) state`;
val run_test7_v_thm = m_translate_run run_test7_def;

val _ = export_theory ();
