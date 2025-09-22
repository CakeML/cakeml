(*
  Correctness proof for loop_remove
*)
Theory loop_remove
Ancestors
  loopLang
Libs
  preamble


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
    let params = MAP FST (toAList live) in
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
     let params = MAP FST (toAList live_in) in
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

Definition comp_prog_def:
  comp_prog code =
    let n = FOLDR MAX 0 (MAP FST code) + 1 in
      SND (FOLDR comp (n,[]) code)
End


