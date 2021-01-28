(*
  Tactic library specific to Icing
*)
structure icingTacticsLib =
struct
  open fpOptTheory fpOptPropsTheory
       fpSemPropsTheory semanticPrimitivesTheory evaluateTheory
       semanticsTheory semanticsPropsTheory
       evaluatePropsTheory terminationTheory fpSemPropsTheory mllistTheory;
  local open ml_progTheory in end;
  open preamble;

val prep = fn thm => SIMP_RULE std_ss [] thm;

val optUntil_tac =
  fn t1 => fn t2 =>
    qpat_x_assum t1 (mp_then Any mp_tac (CONJUNCT1 optUntil_evaluate_ok))
    \\ disch_then (qspec_then t2 assume_tac) \\ fs[];

val optUntil_match_tac =
  fn t1 => fn t2 =>
    qpat_x_assum t1 (mp_then Any mp_tac (CONJUNCT2 optUntil_evaluate_ok))
  \\ disch_then (qspec_then t2 assume_tac) \\ fs[];

val semState_comp_eq = semanticPrimitivesTheory.state_component_equality;

end
