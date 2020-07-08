(*
  Correctness proof for loop_remove
*)

open preamble loopLangTheory

val _ = new_theory"loop_to_loopremove";

Definition mark_all_def:
  (mark_all (Seq p1 p2) =
     let (p1,t1) = mark_all p1 in
     let (p2,t2) = mark_all p2 in
     let t3 = (t1 /\ t2) in
       (if t3 then Mark (Seq p1 p2) else Seq p1 p2, t3)) /\
  (mark_all (Loop l1 body l2) =
     let (body,t1) = mark_all body in
       (Loop l1 body l2, F)) /\
  (mark_all (If x1 x2 x3 p1 p2 l1) =
     let (p1,t1) = mark_all p1 in
     let (p2,t2) = mark_all p2 in
     let p3 = If x1 x2 x3 p1 p2 l1 in
     let t3 = (t1 /\ t2) in
       (if t3 then Mark p3 else p3, t3)) /\
  (mark_all (Mark p1) = mark_all p1) /\
  (mark_all (Call ret dest args handler) =
     case handler of
     | NONE => (Mark (Call ret dest args handler), T)
     | SOME (n,p1,p2,l) =>
         let (p1,t1) = mark_all p1 in
         let (p2,t2) = mark_all p2 in
         let t3 = (t1 ∧ t2) in
         let p3 = Call ret dest args (SOME (n,p1,p2,l)) in
           (if t3 then Mark p3 else p3, t3)) /\
  (mark_all prog = (Mark prog,T))
End

Definition comp_no_loop_def:
  (comp_no_loop p (Seq p1 p2) =
    Seq (comp_no_loop p p1) (comp_no_loop p p2)) /\
  (comp_no_loop p (If x1 x2 x3 p1 p2 l1) =
    If x1 x2 x3 (comp_no_loop p p1) (comp_no_loop p p2) l1) /\
  (comp_no_loop p (Call ret dest args handler) =
    Call ret dest args
      (case handler of
       | SOME (n,q,r,l) => SOME (n, comp_no_loop p q, comp_no_loop p r, l)
       | NONE => NONE)) /\
  (comp_no_loop p Break = FST p) /\
  (comp_no_loop p Continue = SND p) /\
  (comp_no_loop p (Mark prog) = comp_no_loop p prog) /\
  (comp_no_loop p (Loop l1 b l2) = Fail) /\
  (comp_no_loop p prog = prog)
End

Definition store_cont_def:
  store_cont live code (n,funs) =
    let params = MAP FST (toSortedAList live) in
    let funs = (n,params,code) :: funs in
    let cont = Call NONE (SOME n) params NONE in
      (cont:'a loopLang$prog, (n+1,funs))
End

Definition comp_with_loop_def:
  (comp_with_loop p (Seq p1 p2) cont s =
     let (q2,s) = comp_with_loop p p2 cont s in
       comp_with_loop p p1 q2 s) ∧
  (comp_with_loop p (If x1 x2 x3 p1 p2 l1) cont s =
     let (cont,s) = store_cont l1 cont s in
     let (q1,s) = comp_with_loop p p1 cont s in
     let (q2,s) = comp_with_loop p p2 cont s in
       (If x1 x2 x3 q1 q2 LN,s)) /\
  (comp_with_loop p (Call ret dest args handler) cont s =
     case handler of
     | NONE => (Seq (Call ret dest args NONE) cont,s)
     | SOME (n,q,r,l) =>
         let (cont,s) = store_cont l cont s in
         let (q,s) = comp_with_loop p q cont s in
         let (r,s) = comp_with_loop p r cont s in
           (Call ret dest args (SOME (n,q,r,l)),s)) /\
  (comp_with_loop p Break cont s = (FST p,s)) /\
  (comp_with_loop p Continue cons s = (SND p,s)) /\
  (comp_with_loop p (Mark prog) cont s = (Seq (comp_no_loop p prog) cont,s)) /\
  (comp_with_loop p (Loop live_in body live_out) cont s =
     let (cont,s) = store_cont live_out cont s in
     let params = MAP FST (toSortedAList live_in) in
     let (n,funs) = s in
     let enter = Call NONE (SOME n) params NONE in
     let (body,m,funs) = comp_with_loop (cont,enter) body Fail (n+1,funs) in
     let funs = (n,params,body) :: funs in
       (enter,(m,funs))) ∧
  (comp_with_loop p prog cont s = (Fail,s)) (* impossible case *)
End

Definition comp_def:
  comp (name,params,prog) s =
    let (body,n,funs) = comp_with_loop (Fail,Fail) prog Fail s in
      (n,(name,params,body)::funs)
End

Definition comp_all_def:
  comp_all code =
    let n = FOLDR MAX 0 (MAP FST code) + 1 in
      SND (FOLDR comp (n,[]) code)
End

val _ = export_theory();
