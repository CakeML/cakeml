(*
  Semantics of Scheme
*)
open preamble;
open prim_recTheory;
open mesonLib;
open arithmeticTheory;
open numTheory;
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
  strict _ _ = Wrong "Not a procedure"
End

Theorem wrong_strict:
  ∀ args n w . strict (SNum n) args = Wrong "Not a procedure" ∧
               strict (Wrong w) args = Wrong "Not a procedure"
Proof
  rw[strict_def]
QED

Definition semantics_def:
  semantics (Val v) = v ∧
  semantics (Apply fn args) = strict (semantics fn) (MAP semantics args)
Termination
  WF_REL_TAC ‘measure exp_size’
End

Definition return_def:
  return [] v = ([], Val v) ∧
  return (ApplyK NONE eargs :: ks) v = (case eargs of
  | [] => (ks, Val $ strict v [])
  | (e::es) => (ApplyK (SOME (v, [])) es :: ks, e)) ∧
  return (ApplyK (SOME (vfn, vargs)) eargs :: ks) v = (case eargs of
  | [] => (ks, Val $ strict vfn (REVERSE $ v::vargs))
  | (e::es) => (ApplyK (SOME (vfn, v::vargs)) es ::ks, e))
End

Definition step_def:
  step (ks, (Val v)) = return ks v ∧
  step (ks, (Apply fn args)) = (ApplyK NONE args :: ks, fn)
End

Definition steps_def:
  steps (n:num) t = if n = 0 then t
    else steps (n - 1) $ step t
End

Theorem steps_suc:
  ∀ n m t .
    steps (SUC n) t = steps n (step t)
Proof
  Induct >- (
    rpt (strip_tac >> simp [Once steps_def])
  )
  >> simp [Once steps_def]
QED

Theorem steps_add:
  ∀ n m t .
    steps (n + m) t = steps m (steps n t)
Proof
  Induct >- (
    rpt strip_tac
    >> ‘steps 0 t = t’ by simp[Once steps_def]
    >> rw[]
  )
  >> rewrite_tac [ADD_CLAUSES]
  >> simp [steps_suc]
QED

Theorem big_small_equiv:
  ∀ e ks . ∃ n . steps n ks e = (ks, Val (semantics e))
Proof
  ho_match_mp_tac semantics_ind
  >> rpt strip_tac
  >~ [‘semantics (Val _)’]
  >- (rpt strip_tac >> qexists_tac ‘0’ >> simp[Once steps_def, semantics_def])
  >> simp[semantics_def, SF ETA_ss]
  >> simp[Once steps_def]
  >> simp[step_def(*, AllCaseEqs()*)]
  >> qrefine ‘n+1’
  >> simp[]
  >> first_x_assum $ qspec_then ‘ApplyK NONE args::ks’ mp_tac
  >> strip_tac
  >> qrefine ‘k+m’
  >> simp[steps_add]
  >> pop_assum $ irule_at Any

  >> qrefine ‘n+m’
  >> rewrite_tac[steps_add]
  >> simp[]

  Induct_on ‘ks’ >> Induct_on ‘e’ >| [
    simp[semantics_def] >> Induct_on ‘l’ >| [
      rw[] >> Cases_on ‘semantics e’ >| [
        Cases_on ‘p’ >> simp[strict_def, sadd_def, smul_def]
          >> simp[Once steps_def, step_def]
        ,
      ]
      ,
    ]
    ,
    simp[semantics_def] >> rw[] >> qexists_tac ‘0’
      >> simp[Once steps_def]
  ]
QED

(*EVAL “semantics (Val (SNum 3))”*)
(*EVAL “semantics (Apply (Val (Prim SMul)) [Val (SNum 2); Val (SNum 4)])”*)
(*EVAL “big_step 10 ([], Apply (Val (Prim SMul)) [Val (SNum 2); Val (SNum 4)])”*)

val _ = export_theory();
