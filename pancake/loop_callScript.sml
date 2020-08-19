(*
  Call optimisation for loopLang.
*)
open preamble loopLangTheory

val _ = new_theory "loop_call"



Definition find_label_def:
  find_label fm n =
  case FLOOKUP fm n of
    | SOME m => SOME (m:num)
    | NONE => SOME 0
End

Definition last_def:
  (last [] = 0:num) /\
  (last xs = EL (LENGTH xs - 1) xs)
End

Definition butlast_def:
  (butlast [] = []) /\
  (butlast xs = TAKE (LENGTH xs - 1) xs)
End


Definition comp_def:
  (comp fm (Call ret NONE args handler) =
   if args = [] then loopLang$Skip
   else (Call ret
              (find_label fm (last args))
              (butlast args)
              handler)) /\
  (comp fm p = p)
End

val _ = export_theory();
