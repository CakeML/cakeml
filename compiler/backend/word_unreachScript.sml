(*
  This compilation pass removes trivially unreachable code.
*)
open preamble wordLangTheory;

val _ = new_theory "word_unreach";

(* function that makes all Seq associate to the right *)

Definition dest_Seq_Move_def:
  dest_Seq_Move (wordLang$Move n l) = SOME (n,l,Skip) ∧
  dest_Seq_Move (Seq (Move n l) rest) = SOME (n,l,rest) ∧
  dest_Seq_Move _ = NONE
End

Definition merge_moves_def:
  merge_moves l1 l2 =
    let l2' = MAP (λ(x,y). case ALOOKUP l1 y of
                           | NONE => (x,y)
                           | SOME v => (x,v)) l2 in
      anub (l2' ++ l1) ([]:num list)
End

Definition SimpSeq_def:
  SimpSeq p1 (p2:'a wordLang$prog) =
    let default = Seq p1 p2 in
      if p2 = Skip then p1 else
        case p1 of
        | Skip => p2
        | Raise _ => p1
        | Return _ _ => p1
        | Move n1 l1 =>
            (case dest_Seq_Move p2 of
             | NONE => default
             | SOME (n2,l2,rest) =>
                 (* if n1 ≠ n2 then default else *)
                   let l = merge_moves l1 l2 in
                     if rest = Skip
                     then Move (MAX n1 n2) l
                     else Seq (Move (MAX n1 n2) l) rest)
        | _ => default
End

Definition Seq_assoc_right_def:
  (Seq_assoc_right Skip acc = acc) ∧
  (Seq_assoc_right (Seq q1 q2) acc  =
     Seq_assoc_right q1 (Seq_assoc_right q2 acc)) ∧
  (Seq_assoc_right (If v n r q1 q2) acc =
     SimpSeq (If v n r (Seq_assoc_right q1 Skip) (Seq_assoc_right q2 Skip)) acc) ∧
  (Seq_assoc_right (MustTerminate q) acc =
     SimpSeq (MustTerminate (Seq_assoc_right q Skip)) acc) ∧
  (Seq_assoc_right (Call ret_prog dest args handler) acc =
     case ret_prog of
     | NONE => Call ret_prog dest args handler
     | SOME (x1,x2,q1,x3,x4) =>
         SimpSeq (Call (SOME (x1,x2,Seq_assoc_right q1 Skip,x3,x4))
           dest args
              (case handler of
               | NONE => NONE
               | SOME (y1,q2,y2,y3) => SOME (y1,Seq_assoc_right q2 Skip,y2,y3))) acc) ∧
  (Seq_assoc_right p1 acc = SimpSeq p1 acc)
End

Definition remove_unreach_def:
  remove_unreach (e:'a wordLang$prog) =
    Seq_assoc_right e Skip
End

Triviality remove_unreach_test:
  remove_unreach (Seq (Move 1 [(1,11);(2,22);(3,33)])
                      (Move 1 [(3,1);(2,99)]))
  =
  Move 1 [(3,11); (2,99); (1,11)]
Proof
  EVAL_TAC
QED

val _ = export_theory();
