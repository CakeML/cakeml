(*
  Call optimisation for loopLang
*)
open preamble loopLangTheory

val _ = new_theory "loop_call"

Definition last_def:
  (last [] = 0:num) /\
  (last xs = EL (LENGTH xs - 1) xs)
End

Definition butlast_def:
  (butlast [] = []) /\
  (butlast xs = TAKE (LENGTH xs - 1) xs)
End


Definition comp_def:
  (comp l (Call ret NONE args handler) =
   if args = [] then loopLang$Skip
   else
   case lookup (last args) l of
    | NONE => (Call ret NONE args handler)
    | SOME n => (Call ret (SOME n) (butlast args) handler)) /\
  (comp l p = p)
End


val _ = export_theory();
