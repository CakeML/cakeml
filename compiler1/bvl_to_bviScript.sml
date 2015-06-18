open preamble bvlTheory bviTheory;

val _ = new_theory "bvl_to_bvi";

val destLet_def = Define `
  (destLet ((Let xs b):bvl$exp) = (xs,b)) /\
  (destLet _ = ([],Var 0))`;

val large_int = ``1000000000:int``

val compile_int_def = tDefine "compile_int" `
  compile_int (i:int) =
    if 0 <= i then
      if i <= ^large_int then
        (Op (Const i) []:bvi$exp)
      else
        let x = compile_int (i / ^large_int) in
        let y = Op (Const (i % ^large_int)) [] in
        let n = Op (Const ^large_int) [] in
          Op Add [Op Mult [x; n]; y]
    else
      if -^large_int <= i then
        Op (Const i) []
      else
        let i = 0 - i in
        let x = compile_int (i / ^large_int) in
        let y = Op (Const (0 - (i % ^large_int))) [] in
        let n = Op (Const (0 - ^large_int)) [] in
          Op Add [Op Mult [x; n]; y]`
 (WF_REL_TAC `measure (Num o ABS)`
  \\ REPEAT STRIP_TAC \\ intLib.COOPER_TAC)

val compile_op_def = Define `
  compile_op op c1 =
    case op of
    | Const i => (case c1 of [] => compile_int i
                  | _ => Let [Op (Const 0) c1] (compile_int i))
    | _ => Op op c1`

val compile_def = tDefine "compile" `
  (compile n [] = ([],[],n)) /\
  (compile n ((x:bvl$exp)::y::xs) =
     let (c1,aux1,n1) = compile n [x] in
     let (c2,aux2,n2) = compile n1 (y::xs) in
       (c1 ++ c2, aux1 ++ aux2, n2)) /\
  (compile n [Var v] = ([(Var v):bvi$exp], [], n)) /\
  (compile n [If x1 x2 x3] =
     let (c1,aux1,n1) = compile n [x1] in
     let (c2,aux2,n2) = compile n1 [x2] in
     let (c3,aux3,n3) = compile n2 [x3] in
       ([If (HD c1) (HD c2) (HD c3)],aux1++aux2++aux3,n3)) /\
  (compile n [Let xs x2] =
     let (c1,aux1,n1) = compile n xs in
     let (c2,aux2,n2) = compile n1 [x2] in
       ([Let c1 (HD c2)], aux1++aux2, n2)) /\
  (compile n [Raise x1] =
     let (c1,aux1,n1) = compile n [x1] in
       ([Raise (HD c1)], aux1, n1)) /\
  (compile n [Tick x1] =
     let (c1,aux1,n1) = compile n [x1] in
       ([Tick (HD c1)], aux1, n1)) /\
  (compile n [Op op xs] =
     let (c1,aux1,n1) = compile n xs in
       ([compile_op op c1],aux1,n1)) /\
  (compile n [Handle x1 x2] =
     let (args,x0) = destLet x1 in
     let (c1,aux1,n1) = compile n args in
     let (c2,aux2,n2) = compile n1 [x0] in
     let (c3,aux3,n3) = compile n2 [x2] in
     let aux4 = [(n3,LENGTH args,HD c2)] in
     let n4 = n3 + 1 in
       ([Call 0 (SOME (2 * n3 + 1)) c1 (SOME (HD c3))],
        aux1++aux2++aux3++aux4, n4)) /\
  (compile n [Call ticks dest xs] =
     let (c1,aux1,n1) = compile n xs in
       ([Call ticks
              (case dest of
               | NONE => NONE
               | SOME n => SOME (2 * n)) c1 NONE],aux1,n1))`
 (WF_REL_TAC `measure (exp1_size o SND)`
  \\ REPEAT STRIP_TAC \\ TRY DECIDE_TAC
  \\ Cases_on `x1` \\ fs [destLet_def]
  \\ SRW_TAC [] [bvlTheory.exp_size_def] \\ DECIDE_TAC);

val _ = export_theory();
