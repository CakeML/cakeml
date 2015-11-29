open preamble bvlTheory bviTheory;
local open bvl_inlineTheory bvl_constTheory bvl_handleTheory in end;

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

val AllocGlobal_location_def = Define`
  AllocGlobal_location = 100:num`;
val CopyGlobals_location_def = Define`
  CopyGlobals_location = 101:num`;
val InitGlobals_location_def = Define`
  InitGlobals_location = 102:num`;
val num_stubs_def = Define`
  num_stubs = 103:num`;

val AllocGlobal_code_def = Define`
  AllocGlobal_code = (0:num,
    Let [Op GlobalsPtr []]
     (Let [Op Deref [Op (Const 0) []; Var 0]]
       (Let [Op Update [Op Add [Var 0; Op(Const 1)[]]; Op (Const 0) []; Var 1]]
         (Let [Op Length [Var 2]]
           (If (Op Less [Var 0; Var 2]) (Var 1)
               (Let [Op RefArray [Op (Const 0) []; Op Mult [Var 0; Op (Const 2) []]]]
                 (Let [Op SetGlobalsPtr [Var 0]]
                   (Call 0 (SOME CopyGlobals_location) [Var 1; Var 5; Op Sub [Op (Const 1) []; Var 4]] NONE))))))))`;

val CopyGlobals_code_def = Define`
  CopyGlobals_code = (3:num, (* ptr to new array, ptr to old array, index to copy *)
    Let [Op Update [Op Deref [Var 2; Var 1]; Var 2; Var 0]]
      (If (Op Equal [Op(Const 0)[]; Var 3]) (Var 0)
        (Call 0 (SOME CopyGlobals_location) [Var 1; Var 2; Op Sub [Op(Const 1)[];Var 3]] NONE)))`;

val InitGlobals_code_def = Define`
  InitGlobals_code start = (0:num,
    Let [Op SetGlobalsPtr [Op RefArray [Op (Const 1) []; Op (Const 1) []]]]
     (Call 0 (SOME start) [] NONE))`;

val bvi_stubs_def = Define `
  bvi_stubs start = [(AllocGlobal_location, AllocGlobal_code);
                     (CopyGlobals_location, CopyGlobals_code);
                     (InitGlobals_location, InitGlobals_code start)]`;

val compile_op_def = Define `
  compile_op op c1 =
    case op of
    | Const i => (case c1 of [] => compile_int i
                  | _ => Let [Op (Const 0) c1] (compile_int i))
    | Global n => Op Deref (c1++[compile_int(&(n+1)); Op GlobalsPtr []])
    | SetGlobal n => Op Update (c1++[compile_int(&(n+1)); Op GlobalsPtr []])
    | AllocGlobal =>
        (case c1 of [] => Call 0 (SOME AllocGlobal_location) [] NONE
         | _ => Let [Op (Const 0) c1] (Call 0 (SOME AllocGlobal_location) [] NONE))
    | _ => Op op c1`

val compile_exp_def = tDefine "compile_exp" `
  (compile_exp n [] = ([],[],n)) /\
  (compile_exp n ((x:bvl$exp)::y::xs) =
     let (c1,aux1,n1) = compile_exp n [x] in
     let (c2,aux2,n2) = compile_exp n1 (y::xs) in
       (c1 ++ c2, aux1 ++ aux2, n2)) /\
  (compile_exp n [Var v] = ([(Var v):bvi$exp], [], n)) /\
  (compile_exp n [If x1 x2 x3] =
     let (c1,aux1,n1) = compile_exp n [x1] in
     let (c2,aux2,n2) = compile_exp n1 [x2] in
     let (c3,aux3,n3) = compile_exp n2 [x3] in
       ([If (HD c1) (HD c2) (HD c3)],aux1++aux2++aux3,n3)) /\
  (compile_exp n [Let xs x2] =
     let (c1,aux1,n1) = compile_exp n xs in
     let (c2,aux2,n2) = compile_exp n1 [x2] in
       ([Let c1 (HD c2)], aux1++aux2, n2)) /\
  (compile_exp n [Raise x1] =
     let (c1,aux1,n1) = compile_exp n [x1] in
       ([Raise (HD c1)], aux1, n1)) /\
  (compile_exp n [Tick x1] =
     let (c1,aux1,n1) = compile_exp n [x1] in
       ([Tick (HD c1)], aux1, n1)) /\
  (compile_exp n [Op op xs] =
     let (c1,aux1,n1) = compile_exp n xs in
       ([compile_op op c1],aux1,n1)) /\
  (compile_exp n [Handle x1 x2] =
     let (args,x0) = destLet x1 in
     let (c1,aux1,n1) = compile_exp n args in
     let (c2,aux2,n2) = compile_exp n1 [x0] in
     let (c3,aux3,n3) = compile_exp n2 [x2] in
     let aux4 = [(n3,LENGTH args,HD c2)] in
     let n4 = n3 + 1 in
       ([Call 0 (SOME (num_stubs + 2 * n3 + 1)) c1 (SOME (HD c3))],
        aux1++aux2++aux3++aux4, n4)) /\
  (compile_exp n [Call ticks dest xs] =
     let (c1,aux1,n1) = compile_exp n xs in
       ([Call ticks
              (case dest of
               | NONE => NONE
               | SOME n => SOME (num_stubs + 2 * n)) c1 NONE],aux1,n1))`
 (WF_REL_TAC `measure (exp1_size o SND)`
  \\ REPEAT STRIP_TAC \\ TRY DECIDE_TAC
  \\ Cases_on `x1` \\ fs [destLet_def]
  \\ SRW_TAC [] [bvlTheory.exp_size_def] \\ DECIDE_TAC);

val compile_exp_ind = theorem"compile_exp_ind";

val compile_exp_LENGTH_lemma = prove(
  ``!n xs. (LENGTH (FST (compile_exp n xs)) = LENGTH xs)``,
  HO_MATCH_MP_TAC compile_exp_ind \\ REPEAT STRIP_TAC
  \\ SIMP_TAC std_ss [compile_exp_def] \\ SRW_TAC [] []
  \\ FULL_SIMP_TAC (srw_ss()) [] \\ SRW_TAC [] [] \\ DECIDE_TAC);

val compile_exp_LENGTH = store_thm("compile_exp_LENGTH",
  ``(compile_exp n xs = (ys,aux,n1)) ==> (LENGTH ys = LENGTH xs)``,
  REPEAT STRIP_TAC \\ MP_TAC (SPEC_ALL compile_exp_LENGTH_lemma) \\ fs [])

val compile_exp_SING = store_thm("compile_exp_SING",
  ``(compile_exp n [x] = (c,aux,n1)) ==> ?y. c = [y]``,
  REPEAT STRIP_TAC \\ IMP_RES_TAC compile_exp_LENGTH
  \\ Cases_on `c` \\ fs [LENGTH_NIL]);

val compile_single_def = Define `
  compile_single n (name,arg_count,exp) =
    let (c,aux,n1) = compile_exp n [exp] in
      (MAP (\(k,args,p). (num_stubs + 2 * k + 1,args,p)) aux ++
       [(num_stubs + 2 * name,arg_count,HD c)],n1)`

val compile_list_def = Define `
  (compile_list n [] = ([],n)) /\
  (compile_list n (p::progs) =
     let (code1,n1) = compile_single n p in
     let (code2,n2) = compile_list n1 progs in
       (code1 ++ code2,n2))`

val compile_prog_def = Define `
  compile_prog start n prog =
    let (code,n1) = compile_list n prog in
      (InitGlobals_location, bvi_stubs (num_stubs + 2 * start) ++ code, n1)`;

val compile_def = Define`
  compile start n prog =
    (* TODO: inline, #51 *)
    let prog = MAP (λ(name,arity,exp).
      (name,arity,
       HD (bvl_handle$compile 0
             [bvl_const$compile_exp exp]))) prog in
    (* TODO: let-optimisation, #50 *)
    compile_prog start n prog`;

val _ = export_theory();
