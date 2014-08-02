open HolKernel Parse boolLib bossLib; val _ = new_theory "bvl_const";

open pred_setTheory arithmeticTheory pairTheory listTheory combinTheory;
open finite_mapTheory sumTheory relationTheory stringTheory optionTheory;
open bytecodeTheory sptreeTheory lcsymtacs bvlTheory;

infix \\ val op \\ = op THEN;

val isConst_def = Define `
  (isConst (Op (Const _) []) = T) /\
  (isConst _ = F)`;

val getConst_def = Define `
  (getConst (Op (Const i) []) = i) /\
  (getConst _ = 0)`;

val bConstOp_def = Define `
  bConstOp op xs =
    if EVERY isConst xs then
      let ys = MAP getConst xs in
        (case op of
         | Add => Op (Const (EL 0 ys + EL 1 ys)) []
         | Sub => Op (Const (EL 0 ys - EL 1 ys)) []
         | Mult => Op (Const (EL 0 ys * EL 1 ys)) []
         | Div => Op (Const (EL 0 ys / EL 1 ys)) []
         | Mod => Op (Const (EL 0 ys % EL 1 ys)) []
         | Less => Op (Cons (bool_to_tag (EL 0 ys < EL 1 ys))) []
         | _ => Op op xs)
    else Op op xs`

val true_exp_def = Define `true_exp = Op (Cons (bool_to_tag T)) []`
val false_exp_def = Define `false_exp = Op (Cons (bool_to_tag F)) []`

val bConsts_def = tDefine "bConsts" `
  (bConsts [] = []) /\
  (bConsts (x::xs) = bConst x :: bConsts xs) /\
  (bConst (Var n) = (Var n)) /\
  (bConst (If x1 x2 x3) =
     let y1 = bConst x1 in
       if y1 = true_exp then bConst x2 else
       if y1 = false_exp then bConst x3 else
         If y1 (bConst x2) (bConst x3)) /\
  (bConst (Let xs x2) = Let (bConsts xs) (bConst x2)) /\
  (bConst (Raise x1) = Raise (bConst x1)) /\
  (bConst (Handle x1 x2) = Handle (bConst x1) (bConst x2)) /\
  (bConst (Op op xs) = bConstOp op (bConsts xs)) /\
  (bConst (Tick x) = Tick (bConst x)) /\
  (bConst (Call dest xs) = Call dest (bConsts xs))`
 (WF_REL_TAC `measure (\y. case y of INL xs => bvl_exp1_size xs
                                   | INR x => bvl_exp_size x)`)

val bEval_LENGTH = prove(
  ``!xs s env. (\(xs,s,env).
      (case bEval (xs,s,env) of (Result res,s1) => (LENGTH xs = LENGTH res)
            | _ => T))
      (xs,s,env)``,
  HO_MATCH_MP_TAC bEval_ind \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC (srw_ss()) [bEval_def]
  \\ SRW_TAC [] [] \\ SRW_TAC [] []
  \\ REPEAT BasicProvers.FULL_CASE_TAC \\ FULL_SIMP_TAC (srw_ss()) []
  \\ REV_FULL_SIMP_TAC std_ss [] \\ FULL_SIMP_TAC (srw_ss()) [])
  |> SIMP_RULE std_ss [];

val bEval_cons = prove(
  ``bEval (x::xs,env,s) =
     (case bEval ([x],env,s) of
        (Result v1,s1) =>
          (case bEval (xs,env,s1) of
             (Result vs,s2) => (Result (HD v1::vs),s2)
           | (res,s2) => (res,s2))
      | (res,s1) => (res,s1))``,
  Cases_on `xs` \\ FULL_SIMP_TAC (srw_ss()) [bEval_def]
  \\ Cases_on `bEval ([x],env,s)` \\ Cases_on `q`
  \\ FULL_SIMP_TAC (srw_ss()) []
  \\ MP_TAC (Q.SPECL [`[x]`,`env`,`s`] bEval_LENGTH)
  \\ FULL_SIMP_TAC (srw_ss()) []
  \\ Cases_on `a` \\ SRW_TAC [] [LENGTH_NIL]
  \\ FULL_SIMP_TAC std_ss [LENGTH_NIL]);

val bConst_SING = store_thm("bConst_SING",
  ``!x. [bConst x] = bConsts [x]``,
  Cases \\ SIMP_TAC std_ss [bConsts_def])

val ind = bEval_ind
  |> Q.SPECL [`\(xs,env,s). (FST (bEval (xs,env,s)) <> Error) ==>
                            bEval (bConsts xs,env,s) = bEval (xs,env,s)`]
  |> SIMP_RULE std_ss []

val bEval_isConst = prove(
  ``!xs. EVERY isConst xs ==>
         (bEval (xs,env,s) = (Result (MAP (Number o getConst) xs),s))``,
  Induct \\ fs [bEval_def]
  \\ ONCE_REWRITE_TAC [bEval_cons]
  \\ Cases \\ fs [isConst_def]
  \\ Cases_on `b` \\ fs [isConst_def]
  \\ Cases_on `l` \\ fs [isConst_def,bEval_def,bEvalOp_def,getConst_def]);

val bConsts_thm = store_thm("bConsts_thm",
  ``!xs env s.
      (FST (bEval (xs,env,s)) <> Error) ==>
      (bEval (bConsts xs,env,s) = bEval (xs,env,s))``,
  HO_MATCH_MP_TAC ind \\ REPEAT STRIP_TAC
  \\ SIMP_TAC std_ss [bConsts_def,LET_DEF]
  \\ POP_ASSUM MP_TAC
  THEN1
   (SIMP_TAC std_ss [Once bEval_cons]
    \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
    \\ SIMP_TAC std_ss [Once bEval_cons]
    \\ FULL_SIMP_TAC std_ss [bConst_SING]
    \\ REPEAT BasicProvers.FULL_CASE_TAC
    \\ FULL_SIMP_TAC (srw_ss()) [bConsts_def,bEval_def]
    \\ REV_FULL_SIMP_TAC (srw_ss()) [bConsts_def])
  THEN1
   (SRW_TAC [] [] \\ POP_ASSUM MP_TAC \\ fs [bEval_def]
    \\ Cases_on `bEval ([x1],env,s)` \\ fs []
    \\ REVERSE (Cases_on `q`) \\ fs []
    \\ fs [GSYM bConst_SING,EVAL ``true_exp``,EVAL ``false_exp``]
    \\ fs [bEval_def,bEvalOp_def] \\ SRW_TAC [] []
    \\ fs [EVAL ``bool_to_val T``,EVAL ``bool_to_val F``])
  \\ TRY
   (ASM_SIMP_TAC std_ss [bEval_def]
    \\ REPEAT BasicProvers.FULL_CASE_TAC
    \\ FULL_SIMP_TAC (srw_ss()) [GSYM bConst_SING]
    \\ REV_FULL_SIMP_TAC (srw_ss()) [] \\ NO_TAC)
  \\ SIMP_TAC std_ss [bEval_def,bConstOp_def]
  \\ REVERSE (Cases_on `EVERY isConst (bConsts xs)`)
  THEN1 (FULL_SIMP_TAC std_ss [bEval_def]
         \\ Cases_on `bEval (xs,env,s)` \\ FULL_SIMP_TAC (srw_ss()) []
         \\ Cases_on `q` \\ FULL_SIMP_TAC (srw_ss()) [])
  \\ Cases_on `?s1. bEval (xs,env,s) = (Error,s1)` \\ fs [LET_DEF]
  \\ Cases_on `bEval (xs,env,s)` \\ fs []
  \\ IMP_RES_TAC bEval_isConst
  \\ FULL_SIMP_TAC std_ss []
  \\ SRW_TAC [] []
  \\ Cases_on `op` \\ FULL_SIMP_TAC (srw_ss()) [bEval_def]
  \\ Cases_on `xs` \\ fs [bConsts_def,bEvalOp_def]
  \\ Cases_on `t` \\ fs [bConsts_def,bEvalOp_def,getConst_def]
  \\ Cases_on `t'` \\ fs [bConsts_def,bEvalOp_def,getConst_def]
  \\ Cases_on `getConst (bConst h') = 0` \\ fs [bool_to_val_def])

val _ = export_theory();
