(*
  Calculus for VCG for Dafny
*)

open preamble
open dafny_evaluateTheory

val _ = new_theory "dafny_wp_calc";

(*
  TODO:
    - add ‘Let [(n,e1);(m,e2)] rest’ to expressions
    - exp needs to take two states
    - and Old switches to old state
*)

Overload False = “Lit (BoolL F)”;

Inductive sspec:
  T ⇒
  sspec m (reqs:exp list) (body:statement) (post:exp list) (ens:exp list)
End

Inductive adjust_calls:
  T ⇒
  adjust_calls decreases mutrec body adjusted_body
End

Inductive mspec:
[~empty:]
  mspec {}
[~nonrec:]
  mspec m ∧
  sspec m reqs body [False] ens
  ⇒
  mspec ((Method name ins reqs ens reads decreases outs mods body) INSERT m)
[~mutrec:]
  mspec m ∧
  (∀name ins reqs ens reads outs decreases mods body.
     Method name ins reqs ens reads decreases outs mods body ∈ mutrec ⇒
     ∃adjusted_body.
       adjust_calls decreases mutrec body adjusted_body ∧
       sspec (mutrec ∪ m) reqs adjusted_body [False] ens)
  ⇒
  mspec (mutrec ∪ m)
End

Definition eval_true_def:
  eval_true st env e ⇔
    ∃ck1 ck2.
      evaluate_exp (st with clock := ck1) env e =
        (st with clock := ck2, Rval (BoolV T))
End

Definition eval_stmt_def:
  eval_stmt st env body st' ret =
    ∃ck1 ck2.
      evaluate_stmt (st with clock := ck1) env body =
        (st' with clock := ck2, ret)
End

Definition conditions_hold_def:
  conditions_hold st env ⇔ EVERY (eval_true st env)
End

Definition compatible_env_def:
  compatible_env env m = T
End

Theorem sspec_sound:
  ∀m stmt post ens.
    sspec m reqs stmt post ens ⇒
    ∀st env.
      conditions_hold st env reqs ∧ compatible_env env m ⇒
      ∃st' ret.
        eval_stmt st env stmt st' ret ∧
        case ret of
        | Rstop Sret => conditions_hold st' env ens
        | Rcont => conditions_hold st' env post
        | _ => F
Proof
  cheat
QED

Theorem False_thm:
  conditions_hold st env [False] = F
Proof
  simp [conditions_hold_def,eval_true_def,evaluate_exp_def]
QED

Theorem mspec_sound:
  ∀m. mspec m ⇒
      ∀name ins reqs ens reads decreases outs mods body env.
        Method name ins reqs ens reads decreases outs mods body ∈ m ⇒
        ∀st. conditions_hold st env reqs ∧ compatible_env env m ⇒
             ∃st'. eval_stmt st env body st' (Rstop Sret) ∧
                   conditions_hold st' env ens
Proof
  ho_match_mp_tac mspec_ind
  \\ rpt conj_tac
  >- (* empty *) simp []
  >- (* nonrec *)
   (rpt strip_tac
    \\ reverse $ gvs [IN_INSERT]
    >-
     (last_x_assum drule
      \\ disch_then irule
      \\ gvs [compatible_env_def])
    \\ drule sspec_sound
    \\ disch_then drule
    \\ impl_tac
    >- gvs [compatible_env_def]
    \\ strip_tac
    \\ gvs [False_thm]
    \\ Cases_on ‘ret’ \\ gvs []
    \\ rename [‘eval_stmt _ _ _ _ (Rstop ret)’] \\ Cases_on ‘ret’ \\ gvs []
    \\ first_x_assum $ irule_at $ Pos hd \\ asm_rewrite_tac [])
  (*mutrec *)
  \\ rpt strip_tac
  \\ reverse $ gvs [IN_UNION]
  >-
   (last_x_assum drule
    \\ disch_then irule
    \\ gvs [compatible_env_def])
  \\ cheat
QED

val _ = export_theory ();
