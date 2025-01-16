(*
  Semantics of Scheme
*)
open preamble;
open prim_recTheory;
open mlstringTheory;
open scheme_astTheory;

val _ = new_theory "scheme_semantics";

Datatype:
  cont = ApplyK ((val # val list) option) (exp list)
End

Definition sadd_def:
  sadd [] n = SNum n ∧
  sadd (SNum m :: xs) n = sadd xs (m + n) ∧
  sadd (_ :: xs) _ = Wrong "Arguments to + must be numbers"
End

Definition smul_def:
  smul [] n = SNum n ∧
  smul (SNum m :: xs) n = smul xs (m * n) ∧
  smul (_ :: xs) _ = Wrong "Arguments to * must be numbers"
End

Definition strict_def:
  strict (Prim SAdd) xs = sadd xs 0 ∧
  strict (Prim SMul) xs = smul xs 1 ∧
  strict _ _ = Wrong "Not supported"
End

Definition semantics_def:
  semantics (Val v) = v ∧
  semantics (Apply fn args) = strict (semantics fn) (MAP semantics args) ∧
  semantics (Print _) = Wrong "Not supported"
Termination
  WF_REL_TAC ‘measure exp_size’
End

Definition return_def:
  return ([], v) = ([], Val v) ∧
  return (ApplyK NONE [] :: ks, v) = (ks, Val $ strict v []) ∧
  return (ApplyK NONE (e::es) :: ks, v) = (ApplyK (SOME (v, [])) es :: ks, e) ∧
  return (ApplyK (SOME (vfn, vargs)) [] :: ks, v) =
    (ks, Val $ strict vfn (REVERSE $ v::vargs)) ∧
  return (ApplyK (SOME (vfn, vargs)) (e::es) :: ks, v) =
    (ApplyK (SOME (vfn, v::vargs)) es ::ks, e)
End

Definition step_def:
  step (ks, Val v) = return (ks, v) ∧
  step (ks, Apply fn args) = (ApplyK NONE args :: ks, fn) ∧
  step (_, Print _) = ([], Val $ Wrong "Not supported")
End

Definition big_step_def:
  big_step _ ([], Val v) = v ∧
  big_step (n:num) t = if n > 0
    then big_step (n - 1) $ step t
    else Wrong "Diverged"
End

Theorem big_small_equiv:
  ∀ e . ∃ n . big_step n ([], e) = semantics e
Proof
  rw[]
QED

(*EVAL “semantics (Val (SNum 3))”*)
(*EVAL “semantics (Apply (Val (Prim SMul)) [Val (SNum 2); Val (SNum 4)])”*)
(*EVAL “big_step 10 ([], Apply (Val (Prim SMul)) [Val (SNum 2); Val (SNum 4)])”*)

val _ = export_theory();