(*
  Semantics of Scheme
*)
open preamble;
open mlstringTheory;
open scheme_astTheory;

val _ = new_theory "scheme_semantics";

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

(*EVAL “semantics (Val (SNum 3))”*)
(*EVAL “semantics (Apply (Val (Prim SMul)) [Val (SNum 2); Val (SNum 4)])”*)
(*EVAL “measure”*)

val _ = export_theory();