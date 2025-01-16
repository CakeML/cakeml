(*
  Semantics of Scheme
*)
open preamble;
open prim_recTheory;
open mesonLib;
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
  strict (Prim SMul) xs = smul xs 1
End

Definition semantics_def:
  semantics (Val v) = v ∧
  semantics (Apply fn args) = strict (semantics fn) (MAP semantics args)
Termination
  WF_REL_TAC ‘measure exp_size’
End

Definition return_def:
  return [] v = ([], Val v) ∧
  return (ApplyK NONE [] :: ks) v = (ks, Val $ strict v []) ∧
  return (ApplyK NONE (e::es) :: ks) v = (ApplyK (SOME (v, [])) es :: ks, e) ∧
  return (ApplyK (SOME (vfn, vargs)) [] :: ks) v =
    (ks, Val $ strict vfn (REVERSE $ v::vargs)) ∧
  return (ApplyK (SOME (vfn, vargs)) (e::es) :: ks) v =
    (ApplyK (SOME (vfn, v::vargs)) es ::ks, e)
End

Definition step_def:
  step ks (Val v) = return ks v ∧
  step ks (Apply fn args) = (ApplyK NONE args :: ks, fn)
End

Definition big_step_def:
  big_step _ ([], Val v) = v ∧
  big_step (n:num) t = if n > 0
    then big_step (n - 1) $ step t
    else Wrong "Diverged"
End

Definition steps_def:
  steps _ [] (Val v) = ([], Val v) ∧
  steps (n:num) ks e = if n > 0
    then let (ks', e') = (step ks e) in (steps (n - 1) ks' e')
    else (ks, e)
End

Theorem steps_return:
  ∀ e v n ks . steps n [] e = ([], Val v) ⇒ steps n ks e = return ks v
Proof
  Induct_on ‘ks’
  Induct_on ‘l’
  Induct_on ‘n’
  fs[return_def]
  fs[steps_def]
  rw[steps_def]
  rw[step_def]
  rw[return_def]
  rw[]
  simp[steps_def]
  ‘return ks' v'' = steps n'' ks' (Val v'')’ by rw[]
  pop_assum(SUBST1_TAC o SYM o SPEC ``0:num`` o SPEC ``SNum 0``)
  gs[]
  first_x_assum $ qspecl_then [‘SNum 0’,‘0’] SUBST1_TAC
  last_x_assum $ assume_tac o SRULE [Once EQ_SYM_EQ]
  qexists_tac ‘n’
  qexists_tac ‘n + 1’
  Cases_on ‘o'’
  Cases_on ‘v’
  Cases_on ‘v'’
  Cases_on ‘l’
  Cases_on ‘ks’
  Cases_on ‘n - 1 > 0’
  MESON_TAC[steps_def]

Theorem big_small_equiv:
  ∀ e v . semantics e = v ⇒ ∃ n . steps n ([], e) = ([], Val v)
Proof
  rw[]
  Induct
  simp[]
  fs[]
  Induct_on ‘l’
  Induct_on ‘e’
  asm_simp_tac bool_ss []
  SUBST1_TAC(ASSUME “return ks (SNum 0) = steps 0 ks (Val (SNum 0))”)
  fs[steps_def, step_def, semantics_def,
    return_def, strict_def, sadd_def, smul_def]
  DISCH_TAC
  rw[steps_def, step_def, semantics_def,
    return_def, strict_def, sadd_def, smul_def]
  metis_tac[steps_def, step_def, semantics_def,
    return_def, strict_def, sadd_def, smul_def]
  qexists_tac ‘n’
  Cases_on ‘e’
  Cases_on ‘p’
  Cases_on ‘v’
  Cases_on ‘h’
  qexists_tac ‘n+99’
  qexists_tac ‘1’
  full_simp_tac bool_ss [steps_def]
  full_simp_tac pure_ss []
QED

(*EVAL “semantics (Val (SNum 3))”*)
(*EVAL “semantics (Apply (Val (Prim SMul)) [Val (SNum 2); Val (SNum 4)])”*)
(*EVAL “big_step 10 ([], Apply (Val (Prim SMul)) [Val (SNum 2); Val (SNum 4)])”*)

val _ = export_theory();