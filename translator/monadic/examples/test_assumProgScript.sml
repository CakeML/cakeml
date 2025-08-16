(*
  Test the monadic translator's handling of assumptions
*)
Theory test_assumProg
Libs
  preamble ml_monad_translator_interfaceLib
Ancestors
  ml_monad_translator

val _ = set_up_monadic_translator ();

val _ = patternMatchesLib.ENABLE_PMATCH_CASES();

(* Create the data type to handle the references *)
Datatype:
  state_refs = <| the_num : num ; the_string : string|>
End

(* Extra state invariant *)
Definition STATE_PINV_def:
  STATE_PINV = \state. EVEN state.the_num /\ (state.the_string = "")
End

Triviality STATE_PINV_VALID:
  (state.the_num = 0) /\ (state.the_string = "") ==> STATE_PINV state
Proof
  rw[STATE_PINV_def]
QED

(* Data type for the exceptions *)
Datatype:
  state_exn = Fail string | Subscript
End

val config =  global_state_config |>
              with_state ``:state_refs`` |>
              with_exception ``:state_exn`` |>
              with_refs [
                ("the_num", ``0 : num``),
                ("the_string", ``""``)
              ] |>
              with_state_invariant STATE_PINV_def STATE_PINV_VALID;

Overload failwith = ``raise_Fail``

val _ = start_translation config;

(* TESTS *)
val _ = set_trace "assumptions" 1;
val _ = Globals.max_print_depth := 40;

Definition pf_def:
  pf x = (if EVEN x then x else ARB)
End
val _ = translate arithmeticTheory.EVEN;
val pf_v_thm = translate pf_def;
val pf_side_def = definition "pf_side_def";

Definition mf_def:
  mf () = do x <- get_the_num; return(pf x) od
End
val mf_v_thm = m_translate mf_def;
val mf_side_def = definition "mf_side_def";

Definition mf2_def:
  mf2 () = do x <- get_the_num; set_the_num x; return (); od
End
val mf2_v_thm = m_translate mf2_def;

Definition mf3_def:
  mf3 x = set_the_num x
End
val mf3_v_thm = m_translate mf3_def;
val mf3_side_def = definition"mf3_side_def";

Definition mf4_def:
  mf4 () = get_the_num
End
val mf4_v_thm = m_translate mf4_def;

Definition mf5_def:
  mf5 x = do y <- get_the_num; return (x+y) od
End
val mf5_v_thm = m_translate mf5_def;

Definition mf6_def:
  mf6 l = dtcase l of []   => return (0:num)
                    | x::l => return (1:num)
End
val mf6_v_thm = m_translate mf6_def;

val length_v_thm = translate listTheory.LENGTH;
Triviality ZIP_def2:
  ZIP x = dtcase x of
      (x::l1, y::l2) => (x, y) :: ( ZIP (l1,l2) )
    | ([], [])       => []
    | _              => []
Proof
  PairCases_on ‘x’ \\ Cases_on `x0`
\\ Cases_on `x1`
\\ fs[ZIP_def]
QED

val zip_v_thm = translate ZIP_def2;

Definition mf7_def:
  mf7 l1 l2 = do
    z <- if LENGTH l1 = LENGTH l2 then return () else failwith "";
    return (ZIP (l1, l2)) od
End
val mf7_v_thm = m_translate mf7_def;
