(*
  Useful predicates on the CakeML ast.
 *)
open preamble astTheory semanticPrimitivesPropsTheory;

val _ = new_theory "ast_extras";

Definition every_exp_def[simp]:
  (every_exp f (Raise e) <=>
     f (Raise e) /\ every_exp f e) /\
  (every_exp f (Handle e pes) <=>
     f (Handle e pes) /\
     every_exp f e /\
     EVERY (every_exp f) (MAP SND pes)) /\
  (every_exp f (Con ts es) <=>
     f (Con ts es) /\
     EVERY (every_exp f) es) /\
  (every_exp f (Fun n e) <=>
     f (Fun n e) /\
     every_exp f e) /\
  (every_exp f (App op es) <=>
     f (App op es) /\
     EVERY (every_exp f) es) /\
  (every_exp f (Log lop e1 e2) <=>
     f (Log lop e1 e2) /\
     every_exp f e1 /\
     every_exp f e2) /\
  (every_exp f (If e1 e2 e3) <=>
    f (If e1 e2 e3) /\
    every_exp f e1 /\
    every_exp f e2 /\
    every_exp f e3) /\
  (every_exp f (Mat e pes) <=>
    f (Mat e pes) /\
    every_exp f e /\
    EVERY (every_exp f) (MAP SND pes)) /\
  (every_exp f (Let n x e) <=>
    f (Let n x e) /\
    every_exp f x /\
    every_exp f e) /\
  (every_exp f (Letrec funs e) <=>
    f (Letrec funs e) /\
    every_exp f e /\
    EVERY (every_exp f) (MAP (SND o SND) funs)) /\
  (every_exp f (Tannot e t) <=>
    f (Tannot e t) /\
    every_exp f e) /\
  (every_exp f (Lannot e l) <=>
    f (Lannot e l) /\
    every_exp f e) /\
  (every_exp f e <=> f e)
Termination
  WF_REL_TAC `measure (exp_size o SND)`
  \\ rw [list_size_pair_size_MAP_FST_SND]
  \\ drule MEM_list_size
  \\ disch_then(qspec_then `exp_size` mp_tac)
  \\ simp[]
End

Theorem every_exp_the[simp]:
  !P e. every_exp P e ==> P e
Proof
  gen_tac \\ Induct \\ rw []
QED

Theorem every_exp_mono:
  !P e P'.
    (!e. P e ==> P' e) ==> every_exp P e ==> every_exp P' e
Proof
  ho_match_mp_tac every_exp_ind
  \\ fsrw_tac [SATISFY_ss] [EVERY_MEM]
QED

Definition every_pat_def[simp]:
  every_pat f (Pcon opt ps) = (f (Pcon opt ps) ∧ EVERY (every_pat f) ps) ∧
  every_pat f (Pref p) = (f (Pref p) ∧ every_pat f p) ∧
  every_pat f (Pas p s) = (f (Pas p s) ∧ every_pat f p) ∧
  every_pat f (Ptannot p t) = (f (Ptannot p t) ∧ every_pat f p) ∧
  every_pat f p = f p
End

Theorem every_pat_the[simp]:
  ∀P p. every_pat P p ⇒ P p
Proof
  gen_tac \\ Induct \\ rw []
QED

Theorem every_pat_mono:
  ∀P p P'.
    (∀p. P p ⇒ P' p) ⇒ every_pat P p ⇒ every_pat P' p
Proof
  ho_match_mp_tac every_pat_ind
  \\ rw [] \\ gs [EVERY_MEM]
QED

Definition every_dec_def[simp]:
  (every_dec f (Dmod n ds) <=>
     f (Dmod n ds) /\
     EVERY (every_dec f) ds) /\
  (every_dec f (Dlocal ds1 ds2) <=>
     f (Dlocal ds1 ds2) /\
     EVERY (every_dec f) ds1 /\
     EVERY (every_dec f) ds2) /\
  (every_dec f d <=>
     f d)
End

Definition freevars_def[simp]:
  freevars (Lit l) = {} ∧
  freevars (Raise e) = freevars e ∧
  freevars (Handle e pes) =
      (freevars e ∪ BIGUNION (set (MAP (λ(p,e). freevars e DIFF
                                   set (MAP Short (pat_bindings p []))) pes))) ∧
  freevars (Con cn es) = BIGUNION (set (MAP freevars es)) ∧
  freevars (Var n) = {n} ∧
  freevars (Fun n e) = freevars e DIFF {Short n} ∧
  freevars (App op xs) = BIGUNION (set (MAP freevars xs)) ∧
  freevars (Log lop x y) = (freevars x ∪ freevars y) ∧
  freevars (If x y z) = (freevars x ∪ freevars y ∪ freevars z) ∧
  freevars (Mat e pes) =
      (freevars e ∪ BIGUNION (set (MAP (λ(p,e). freevars e DIFF
                                   set (MAP Short (pat_bindings p []))) pes))) ∧
  freevars (Let opt x y) =
      (freevars x ∪
       (freevars y DIFF (case opt of SOME n => {Short n} | _ => {}))) ∧
  freevars (Letrec f x) =
      (BIGUNION (set (MAP (λ(fn,vn,x). freevars x DIFF
                                       {Short fn; Short vn}) f)) ∪
       (freevars x DIFF set (MAP (Short o FST) f))) ∧
  freevars (Tannot x t) = freevars x ∧
  freevars (Lannot x l) = freevars x
End

(* Partial applications of closures.
 *)

Definition do_partial_app_def:
  do_partial_app f v =
    case f of
      Closure env n (Fun n' e) =>
        SOME (Closure (env with v := nsBind n v env.v) n' e)
    | _ => NONE
End

val _ = export_theory ();
