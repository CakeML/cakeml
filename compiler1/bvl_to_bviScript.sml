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

val get_globals_ptr_def = Define`
  get_globals_ptr = Op Deref [Op (Const 0) []; Op GlobalsPtr []]`;
val set_globals_ptr_def = Define`
  set_globals_ptr e = Op Update [e; Op(Const 0)[]; Op GlobalsPtr []]`;
val get_globals_count_def = Define`
  get_globals_count = Op Deref [Op (Const 1) []; Op GlobalsPtr []]`;
val set_globals_count_def = Define`
  set_globals_count e = Op Update [e; Op(Const 1)[]; Op GlobalsPtr []]`;

val AllocGlobal_location_def = Define`
  AllocGlobal_location = 0:num`;
val CopyGlobals_location_def = Define`
  CopyGlobals_location = 1:num`;
val num_stubs_def = Define`
  num_stubs = 2:num`;

val AllocGlobal_code_def = Define`
  AllocGlobal_code = (0:num,
    Let [get_globals_ptr; get_globals_count]
      (If (Op Less [Op Length [Var 0]; Var 1])
          (set_globals_count (Op Add [Var 1; Op(Const 1)[]]))
          (Let [Op RefArray [Op(Const 0)[];Op Mult [Op Length [Var 0]; Op(Const 2)[]]]]
            (Let [set_globals_ptr (Var 0)]
               (If (Op Equal [Op(Const 0)[]; Var 3]) (Var 0)
                 (Call 0 (SOME CopyGlobals_location) [Var 1; Var 2; Op Sub [Op(Const 1)[];Var 3]] NONE))))))`;

val CopyGlobals_code_def = Define`
  CopyGlobals_code = (3:num, (* ptr to new array, ptr to old array, index to copy *)
    Let [Op Update [Op Deref [Var 2; Var 1]; Var 2; Var 0]]
      (If (Op Equal [Op(Const 0)[]; Var 3]) (Var 0)
        (Call 0 (SOME CopyGlobals_location) [Var 1; Var 2; Op Sub [Op(Const 1)[];Var 3]] NONE)))`;

val compile_op_def = Define `
  compile_op op c1 =
    case op of
    | Const i => (case c1 of [] => compile_int i
                  | _ => Let [Op (Const 0) c1] (compile_int i))
    | Global n => Op Deref [Op(Const(&n))[]; get_globals_ptr]
    | SetGlobal n => Op Update (c1++[Op(Const(&n))[]; get_globals_ptr])
    | AllocGlobal => Call 0 (SOME AllocGlobal_location) [] NONE
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
       ([Call 0 (SOME (num_stubs + 2 * n3 + 1)) c1 (SOME (HD c3))],
        aux1++aux2++aux3++aux4, n4)) /\
  (compile n [Call ticks dest xs] =
     let (c1,aux1,n1) = compile n xs in
       ([Call ticks
              (case dest of
               | NONE => NONE
               | SOME n => SOME (num_stubs + 2 * n)) c1 NONE],aux1,n1))`
 (WF_REL_TAC `measure (exp1_size o SND)`
  \\ REPEAT STRIP_TAC \\ TRY DECIDE_TAC
  \\ Cases_on `x1` \\ fs [destLet_def]
  \\ SRW_TAC [] [bvlTheory.exp_size_def] \\ DECIDE_TAC);

val compile_ind = theorem"compile_ind";

val compile_LENGTH_lemma = prove(
  ``!n xs. (LENGTH (FST (compile n xs)) = LENGTH xs)``,
  HO_MATCH_MP_TAC compile_ind \\ REPEAT STRIP_TAC
  \\ SIMP_TAC std_ss [compile_def] \\ SRW_TAC [] []
  \\ FULL_SIMP_TAC (srw_ss()) [] \\ SRW_TAC [] [] \\ DECIDE_TAC);

val compile_LENGTH = store_thm("compile_LENGTH",
  ``(compile n xs = (ys,aux,n1)) ==> (LENGTH ys = LENGTH xs)``,
  REPEAT STRIP_TAC \\ MP_TAC (SPEC_ALL compile_LENGTH_lemma) \\ fs [])

val compile_SING = store_thm("compile_SING",
  ``(compile n [x] = (c,aux,n1)) ==> ?y. c = [y]``,
  REPEAT STRIP_TAC \\ IMP_RES_TAC compile_LENGTH
  \\ Cases_on `c` \\ fs [LENGTH_NIL]);

val _ = export_theory();
