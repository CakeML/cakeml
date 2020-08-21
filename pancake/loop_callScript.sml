(*
  Call optimisation for loopLang
*)
open preamble loopLangTheory

val _ = new_theory "loop_call"
(*
Definition last_def:
  (last [] = 0:num) /\
  (last xs = EL (LENGTH xs - 1) xs)
End

Definition butlast_def:
  (butlast [] = []) /\
  (butlast xs = TAKE (LENGTH xs - 1) xs)
End
*)

Definition comp_def:
  (comp l (Call ret NONE args handler) =
   if args = [] then loopLang$Skip
   else
   case lookup (LAST args) l of
    | NONE => (Call ret NONE args handler)
    | SOME n => (Call ret (SOME n) (BUTLAST args) handler)) /\
  (comp l p = p)
End


Definition comp_def:
  (comp l Skip = (Skip, l)) /\
  (comp l (Call ret NONE args handler) =
    if args = [] then (Skip, l)
    else
    case lookup (LAST args) l of
     | NONE => (Call ret NONE args handler, l)
     | SOME n => (Call ret (SOME n) (BUTLAST args) handler, l)) /\
  (comp l (LocValue n m) = (LocValue n m, insert n m l)) /\
  (comp l (Assign n e) = (Assign n e,
                          if lookup n l = NONE then l
                          else delete n l)) /\
  (comp l (LoadByte m n) = (LoadByte m n,
                            case lookup n l of
                             | NONE => l
                             | _ => delete n l)) /\
  (comp l (Seq p q) =
    let (np, nl) = comp l p;
        (nq, nl) = comp nl q in
     (Seq np nq, nl)) /\
  (comp l (If c n ri p q ns) =
    let (np, nl) = comp l p;
        (nq, ml) = comp l q in
     (If c n ri np nq ns, LN)) /\
  (comp l (Loop ns p ms) =
    let (np, nl) = comp l p in
     (Loop ns np ms, nl)) /\
  (comp l (Mark p) =
    let (np, nl) = comp l p in
     (Mark np, nl)) /\
  (comp l (FFI str n m n' m' nl) =
     (FFI str n m n' m' nl, LN)) /\
  (comp l p = (p, l))
End

val _ = export_theory();
