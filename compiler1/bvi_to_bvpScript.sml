open preamble bviTheory bvpTheory;

val _ = new_theory "bvi_to_bvp";

(* compilation from BVI to BVP *)

val op_space_reset_def = Define `
  (op_space_reset Add = T) /\
  (op_space_reset Sub = T) /\
  (op_space_reset _ = F)`;

val op_space_req_def = Define `
  (op_space_req (Cons k) = (k+1)) /\
  (op_space_req Ref = 2) /\
  (op_space_req x = 0)`;

val iAssign_def = Define `
  iAssign n1 op vs live env =
    if op_space_reset op then
      Assign n1 op vs (SOME (list_to_num_set (vs++live++env)))
    else
      let k = op_space_req op in
        if k = 0 then Assign n1 op vs NONE
          else Seq (MakeSpace k (list_to_num_set (vs++live++env)))
                   (Assign n1 op vs NONE)`;

val compile_def = tDefine "compile" `
  (compile (n:num) (env:num list) tail live [] =
    (Skip,[]:num list,n)) /\
  (compile n env tail live (x::y::xs) =
     let (c1,v1,n1) = compile n env F live [x] in
     let (c2,vs,n2) = compile n1 env F (HD v1::live) (y::xs) in
       (Seq c1 c2, HD v1 :: vs, n2)) /\
  (compile n env tail live [(Var v):bvi$exp] =
     if tail
     then (Return (EL v env), [n], n+1)
     else (Move n (EL v env), [n], n+1)) /\
  (compile n env tail live [If x1 x2 x3] =
     let (c1,v1,n1) = compile n env F live [x1] in
     let (c2,v2,n2) = compile n1 env tail live [x2] in
     let (c3,v3,n3) = compile n2 env tail live [x3] in
       if tail then
         (If c1 (HD v1) c2 c3,[n3],n3+1)
       else
         (If c1 (HD v1) (Seq c2 (Move n3 (HD v2)))
                        (Seq c3 (Move n3 (HD v3))),[n3],n3+1)) /\
  (compile n env tail live [Let xs x2] =
     let (c1,vs,n1) = compile n env F live xs in
     let (c2,v2,n2) = compile n1 (vs ++ env) tail live [x2] in
       (Seq c1 c2, v2, n2)) /\
  (compile n env tail live [Raise x1] =
     let (c1,v1,n1) = compile n env F live [x1] in
       (Seq c1 (Raise (HD v1)), v1, n1)) /\
  (compile n env tail live [Op op xs] =
     let (c1,vs,n1) = compile n env F live xs in
     let c2 = Seq c1 (iAssign n1 op (REVERSE vs) live env) in
       (if tail then Seq c2 (Return n1) else c2, [n1], n1+1)) /\
  (compile n env tail live [Tick x1] =
     let (c1,v1,n1) = compile n env tail live [x1] in
       (Seq Tick c1, v1, n1)) /\
  (compile n env tail live [Call ticks dest xs NONE] =
     let (c1,vs,n1) = compile n env F live xs in
     let ret = (if tail then NONE
                else SOME (n1, list_to_num_set (live ++ env))) in
       (Seq c1 (mk_ticks ticks (Call ret dest vs NONE)), [n1], n1+1)) /\
  (compile n env tail live [Call ticks dest xs (SOME handler)] =
     let (c1,vs,n1) = compile n env F live xs in
     let (c2,v,n2) = compile (n1+1) (n1::env) F live [handler] in
     let ret = SOME (HD v, list_to_num_set (live ++ env)) in
     let c3 = (if tail then Return (HD v) else Skip) in
       (Seq c1 (mk_ticks ticks (Seq (Call ret dest vs (SOME (n1,c2))) c3)), v, n2))`
 (WF_REL_TAC `measure (exp2_size o SND o SND o SND o SND)`);

val _ = export_theory();
