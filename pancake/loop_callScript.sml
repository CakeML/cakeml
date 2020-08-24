(*
  Call optimisation for loopLang
*)
open preamble loopLangTheory

val _ = new_theory "loop_call"

Definition comp_def:
  (comp l Skip = (Skip, l)) /\
  (comp l (Call ret dest args handler) =
   ((case dest of
     | SOME _  => Call ret dest args handler
     | NONE => (
       case args of
        | [] => Skip
        | _ => (
          case lookup (LAST args) l of
           | NONE => Call ret NONE args handler
           | SOME n => Call ret (SOME n) (BUTLAST args) handler))), LN)) /\
  (comp l (LocValue n m) = (LocValue n m, insert n m l)) /\
  (comp l (Assign n (Var m)) = (Assign n (Var m),
                                case lookup m l of
                                 | NONE => delete n l
                                 | SOME loc => insert n loc l)) /\
  (comp l (Assign n e) = (Assign n e,
                          case lookup n l of
                           | NONE => l
                           | _ => delete n l)) /\
  (comp l (LoadByte m n) = (LoadByte m n,
                            case lookup n l of
                             | NONE => l
                             | _ => delete n l)) /\
  (comp l (Seq p q) =
    let (np, nl) = comp l p;
        (nq, nl) = comp nl q in
     (Seq np nq, LN)) /\
  (comp l (If c n ri p q ns) =
    let (np, nl) = comp l p;
        (nq, ml) = comp l q in
     (If c n ri np nq ns, LN)) /\
  (comp l (Loop ns p ms) =
    let (np, nl) = comp LN p in
     (Loop ns np ms, LN)) /\
  (comp l (Mark p) =
    let (np, nl) = comp l p in
     (Mark np, nl)) /\
  (comp l (FFI str n m n' m' nl) =
    (FFI str n m n' m' nl, LN)) /\
  (comp l Tick = (Tick, LN)) /\
  (comp l (Raise n) = (Raise n, LN)) /\
  (comp l (Return n) = (Return n, LN)) /\
  (comp l p = (p, l))
End

val _ = export_theory();
