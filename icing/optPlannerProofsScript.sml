(**
  Correctness proof for optimization planner
**)
open semanticPrimitivesTheory evaluateTheory terminationTheory
     icing_rewriterTheory icing_optimisationsTheory fpOptTheory fpValTreeTheory
     optPlannerTheory source_to_sourceTheory source_to_sourceProofsTheory;

open preamble;

val _ = new_theory "optPlannerProofs";

Theorem canonicalize_correct:
  ∀ cfg exp.
  (λ cfg e. ∀ st1 st2 env rws path exp r.
    MEM (Apply (path, rws)) (SND (canonicalize cfg e)) ⇒
    is_perform_rewrites_correct rws st1 st2 env cfg exp r path) cfg exp
Proof
  rpt strip_tac
  >> qspec_then ‘λ cfg e. ∀ st1 st2 env rws path exp r. MEM (Apply (path, rws)) (SND (canonicalize cfg e)) ⇒
    is_perform_rewrites_correct rws st1 st2 env cfg exp r path’
             mp_tac canonicalize_ind
  >> impl_tac
  >- (
    rpt conj_tac >> gs[]
    >- (
      rpt strip_tac >> gs[Once canonicalize_def]
  >> strip_tac >> gs[]
  >> disch_then drule
  ho_match_mp_tac canonicalize_ind


Theorem optPlanner_correct_single:
  is_optimise_with_plan_correct (generate_plan_exp cfg e) st1 st2 env cfg [e] r
Proof
  irule is_optimise_with_plan_correct_lift
  gs[generate_plan_exp_def, compose_plan_generation_def]

Theorem optPlanner_correct:
  is_optimise_with_plan_correct (generate_plan_exps cfg es) st1 st2 env cfg exps r
Proof
  irule is_optimise_with_plan_correct_lift
QED


val _ = export_theory();
