open preamble wordLangTheory

val _ = new_theory "word_simp";

(* function that makes all Seq associate to the left *)

val SmartSeq_def = Define `
  SmartSeq p1 (p2:'a wordLang$prog) =
    if p1 = Skip then p2 else Seq p1 p2`

val Seq_assoc_def = Define `
  (Seq_assoc p1 Skip = p1) /\
  (Seq_assoc p1 (Seq q1 q2) = Seq_assoc (Seq_assoc p1 q1) q2) /\
  (Seq_assoc p1 (If v n r q1 q2) =
     SmartSeq p1 (If v n r (Seq_assoc Skip q1) (Seq_assoc Skip q2))) /\
  (Seq_assoc p1 (MustTerminate n q) =
     SmartSeq p1 (MustTerminate n (Seq_assoc Skip q))) /\
  (Seq_assoc p1 (Call ret_prog dest args handler) =
     SmartSeq p1 (Call (case ret_prog of
           | NONE => NONE
           | SOME (x1,x2,q1,x3,x4) => SOME (x1,x2,Seq_assoc Skip q1,x3,x4))
       dest args
          (case handler of
           | NONE => NONE
           | SOME (y1,q2,y2,y3) => SOME (y1,Seq_assoc Skip q2,y2,y3)))) /\
  (Seq_assoc p1 other = SmartSeq p1 other)`;

val Seq_assoc_ind = fetch "-" "Seq_assoc_ind";

(* optimise certain consequtive If statements that arise from data-to-word

   If something (q1 ; n := X) (q2 ; n := Y) ;
   If (n == Z) p1 p2

   --> (in case X <> Y and Z == X)

   If something (q1 ; n := X ; p1) (q2 ; n := Y ; p2) ;

   similarly if Z == Y and X <> Y

*)

val dest_Seq_def = Define `
  (dest_Seq (Seq p1 p2) = (p1,p2:'a wordLang$prog)) /\
  (dest_Seq p = (Skip,p))`

val dest_If_def = Define `
  (dest_If (If x1 x2 x3 p1 p2) = SOME (x1,x2,x3,p1,p2:'a wordLang$prog)) /\
  (dest_If _ = NONE)`

val dest_If_Eq_Imm_def = Define `
  dest_If_Eq_Imm p =
    case dest_If p of
    | SOME (Equal,n,Imm w,p1,p2) => SOME (n,w,p1,p2)
    | _ => NONE`

val dest_Seq_Assign_Const_def = Define `
  dest_Seq_Assign_Const n p =
    let (p1,p2) = dest_Seq p in
      case p2 of
      | Assign m (Const w) => if m = n then SOME (p1,w) else NONE
      | _ => NONE`

val apply_if_opt_def = Define `
  apply_if_opt x1 x2 =
    case dest_If_Eq_Imm x2 of
    | NONE => NONE
    | SOME (v,w,p1,p2) =>
       let (x0,x1) = dest_Seq x1 in
         case dest_If x1 of
         | NONE => NONE
         | SOME (x1,x2,x3,q1,q2) =>
         case dest_Seq_Assign_Const v q1 of
         | NONE => NONE
         | SOME (_,w1) =>
         case dest_Seq_Assign_Const v q2 of
         | NONE => NONE
         | SOME (_,w2) =>
            if w1 = w2 then NONE
            else if w1 = w then
              SOME (SmartSeq x0 (If x1 x2 x3 (Seq q1 p1) (Seq q2 p2)))
            else if w2 = w then
              SOME (SmartSeq x0 (If x1 x2 x3 (Seq q1 p2) (Seq q2 p1)))
            else NONE`

val simp_if_def = tDefine "simp_if" `
  (simp_if (Seq x1 x2) =
     let y1 = simp_if x1 in
     let y2 = simp_if x2 in
       case apply_if_opt y1 y2 of
       | NONE => Seq y1 y2
       | SOME p => p) /\
  (simp_if (If v n r q1 q2) = If v n r (simp_if q1) (simp_if q2)) /\
  (simp_if (MustTerminate n q) = MustTerminate n (simp_if q)) /\
  (simp_if (Call ret_prog dest args handler) =
     Call (case ret_prog of
           | NONE => NONE
           | SOME (x1,x2,q1,x3,x4) => SOME (x1,x2,simp_if q1,x3,x4))
       dest args
          (case handler of
           | NONE => NONE
           | SOME (y1,q2,y2,y3) => SOME (y1,simp_if q2,y2,y3))) /\
  (simp_if x = x)`
  (WF_REL_TAC `measure (wordLang$prog_size (K 0))` \\ rw [])

val simp_if_ind = fetch "-" "simp_if_ind"

(* all of them together *)

val compile_exp_def = Define `
  compile_exp (e:'a wordLang$prog) =
    let e = Seq_assoc Skip e in
    let e = simp_if e in
      e`;

val _ = export_theory();
