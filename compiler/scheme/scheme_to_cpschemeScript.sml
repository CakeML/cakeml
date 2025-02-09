(*
  CPS transform on Scheme
*)
open preamble;
open mlstringTheory;
open scheme_astTheory;
open cpscheme_astTheory;

val _ = new_theory "scheme_to_cpscheme";

Definition cps_transform_def:
  cps_transform (Val v) = CVal v ∧
  cps_transform (Cond c t f) = Call (cps_transform c) (CondK (cps_transform t) (cps_transform f)) ∧
  cps_transform (Apply fn args) = Call (cps_transform fn) (ApplyK NONE $ MAP cps_transform args)
Termination
  WF_REL_TAC ‘measure exp_size’
End

(*
  EVAL “cps_transform (Cond (Val $ SBool F) (Val $ SNum 2) (Val $ SNum 4))”
  EVAL “cps_transform (Apply (Val $ Prim SAdd) [Val $ SNum 4])”
*)

val _ = export_theory();