(*
  Test the monadic translator's handling of assumptions
*)
open preamble ml_monad_translator_interfaceLib

val _ = new_theory "test_assumProg";

val _ = patternMatchesLib.ENABLE_PMATCH_CASES();

(* Create the data type to handle the references *)
val _ = Hol_datatype `
  state_refs = <| the_num : num ; the_string : string|>`;

(* Extra state invariant *)
val STATE_PINV_def = Define `
  STATE_PINV = \state. EVEN state.the_num /\ (state.the_string = "")`;

val STATE_PINV_VALID = Q.prove (
  `(state.the_num = 0) /\ (state.the_string = "") ==> STATE_PINV state`,
  rw[STATE_PINV_def]
);

(* Data type for the exceptions *)
val _ = Hol_datatype`
  state_exn = Fail of string | Subscript`;

val config =  global_state_config |>
              with_state ``:state_refs`` |>
              with_exception ``:state_exn`` |>
              with_refs [
                ("the_num", ``0 : num``),
                ("the_string", ``""``)
              ] |>
              with_state_invariant STATE_PINV_def STATE_PINV_VALID;

val _ = temp_overload_on ("failwith", ``raise_Fail``);

val _ = start_translation config;

(* TESTS *)
val _ = set_trace "assumptions" 1;
val _ = Globals.max_print_depth := 40;

val pf_def = Define `
  pf x = (if EVEN x then x else ARB)`;
val _ = translate arithmeticTheory.EVEN;
val pf_v_thm = translate pf_def;
val pf_side_def = definition "pf_side_def";

val mf_def = Define `
  mf () = do x <- get_the_num; return(pf x) od`;
val mf_v_thm = m_translate mf_def;
val mf_side_def = definition "mf_side_def";

val mf2_def = Define `
  mf2 () = do x <- get_the_num; set_the_num x; return (); od`;
val mf2_v_thm = m_translate mf2_def;

val mf3_def = Define `
  mf3 x = set_the_num x`;
val mf3_v_thm = m_translate mf3_def;
val mf3_side_def = definition"mf3_side_def";

val mf4_def = Define `
  mf4 () = get_the_num`;
val mf4_v_thm = m_translate mf4_def;

val mf5_def = Define `
  mf5 x = do y <- get_the_num; return (x+y) od`;
val mf5_v_thm = m_translate mf5_def;

val mf6_def = Define `
  mf6 l = dtcase l of []   => return (0:num)
                    | x::l => return (1:num)`;
val mf6_v_thm = m_translate mf6_def;

val length_v_thm = translate listTheory.LENGTH;
val ZIP_def2 = Q.prove(
  `ZIP (l1,l2) = dtcase (l1,l2) of
      (x::l1, y::l2) => (x, y) :: ( ZIP (l1,l2) )
    | ([], [])       => []
    | _              => []`,
Cases_on `l1`
\\ Cases_on `l2`
\\ fs[ZIP_def]);

val zip_v_thm = translate ZIP_def2;

val mf7_def = Define `
  mf7 l1 l2 = do
    z <- if LENGTH l1 = LENGTH l2 then return () else failwith "";
    return (ZIP (l1, l2)) od`;
val mf7_v_thm = m_translate mf7_def;

val _ = export_theory ();
