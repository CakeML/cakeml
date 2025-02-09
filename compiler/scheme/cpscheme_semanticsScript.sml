(*
  Semantics of CPScheme
*)
open preamble;
open mlstringTheory;
open scheme_astTheory;
open cpscheme_astTheory;

val _ = new_theory "cpscheme_semantics";

Definition reduce_def:
  reduce (env, ks, (CVal v)) = return CVal CException ([], ks, v) ∧
  reduce (env, ks, (Call c k)) = (env, (k::ks), c)
End

Definition many_reduce_def:
  many_reduce (n:num) c = if n = 0 then c
    else many_reduce (n - 1) $ reduce c
End

(*
  EVAL “many_reduce 4 ([], [], (cps_transform (Cond (Cond (Val $ SBool F) (Val $ SBool T) (Val $ SBool F)) (Val $ SNum 2) (Val $ SNum 4))))”
  EVAL “many_reduce 2 ([], [], (cps_transform (Apply (Val $ Prim SAdd) [Val $ SNum 4])))”
*)

val _ = export_theory();