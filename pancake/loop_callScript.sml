(*
  Call optimisation for loopLang
*)
Theory loop_call
Ancestors
  loopLang
Libs
  preamble

Definition is_load_def:
  (is_load Load = T) ∧
  (is_load Load8 = T) ∧
  (is_load Load16 = T) ∧
  (is_load Load32 = T) ∧
  (is_load _ = F)
End

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
                                case (lookup n l, lookup m l) of
                                 | NONE, NONE => l
                                 | SOME _ , NONE => delete n l
                                 | _, SOME loc => insert n loc l)) /\
  (comp l (Assign n e) = (Assign n e,
                          case lookup n l of
                           | NONE => l
                           | _ => delete n l)) /\
  (comp l (ShMem op n e) = (ShMem op n e, LN)) /\
  (comp l (Load32 m n) = (Load32 m n,
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
  (comp l (Arith arith) =
   (Arith arith,
    case arith of
      LLongMul r1 r2 r3 r4 =>
        (case (lookup r1 l, lookup r2 l) of
           (NONE, NONE) => l
         | (SOME _ , NONE) => delete r1 l
         | (NONE, SOME loc) => delete r2 l
         | _ => delete r1 $ delete r2 l
        )
    | LLongDiv r1 r2 r3 r4 r5 =>
        (case (lookup r1 l, lookup r2 l) of
           (NONE, NONE) => l
         | (SOME _ , NONE) => delete r1 l
         | (NONE, SOME loc) => delete r2 l
         | _ => delete r1 $ delete r2 l
        )
    | LDiv r1 r2 r3 =>
        (case lookup r1 l of
           NONE => l
         | _ => delete r1 l)
    | _ => l)) ∧
  (comp l p = (p, l))
End


(*
EVAL “comp LN (LocValue 1 3)”;

EVAL “comp LN
       (Seq (LocValue 1 3)
        (Assign 2 (Var 1)))”;

EVAL “comp LN
       (Seq (LocValue 1 3)
        (Seq (Assign 2 (Var 1))
         (Seq (Call NONE NONE [2] NONE) Skip)))”




EVAL “(comp
       (Seq (LocValue 1 3)
        (Seq (Assign 2 (Var 1))
         (Seq (Call NONE NONE [2] NONE) Skip))), s)”

*)


