(*
  An example showing how to use the monadic translator to translate monadic
  doubling functions, including using references (no arrays, no exceptions).
 *)
Theory doubleArgProg
Libs
  preamble ml_monad_translator_interfaceLib
Ancestors
  ml_monad_translator

val _ = set_up_monadic_translator ();

val _ = patternMatchesSyntax.temp_enable_pmatch();

(* Create the data type to handle the references and I/O. *)
Datatype:
  state_num_refs = <| the_num_ref : num |>
End

val config =  global_state_config |>
              with_state ``:state_num_refs`` |>
              with_refs [("the_num_ref", ``0 : num``)]

val _ = start_translation config;

(* A basic double function *)
Definition double_def:
  double x = if x = 0n then 0 else
                            double (x - 1) + 2n
End

Definition double_tail_rec_aux_def:
  double_tail_rec_aux n carry = if n = 0n then carry else
                                  double_tail_rec_aux (n - 1) (carry + 2n)
End

Definition double_tail_rec_def:
  (double_tail_rec x = if x = 0n then 0n else double_tail_rec_aux x 0)
End

(* TODO update this A basic monadic double function using references *)
Definition double_ref_def:
  double_ref x = case x of 0n    => return 0n
                           | SUC v => do
                                        result <- double_ref v;
                                        return (result + 2)
                                      od
End

val double_v = double_def |> translate;

val double_tail_rec_aux_v = double_tail_rec_aux_def |> translate;
val double_tail_rec_v = double_tail_rec_def |> translate;

val double_ref_v = double_ref_def |> m_translate;

Theorem double_ref_thm =
  cfMonadLib.mk_app_of_ArrowP double_ref_v |> SPEC_ALL
