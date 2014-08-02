open HolKernel Parse boolLib bossLib; val _ = new_theory "bvp_const";

open pred_setTheory arithmeticTheory pairTheory listTheory combinTheory;
open finite_mapTheory sumTheory relationTheory stringTheory optionTheory;
open bytecodeTheory sptreeTheory lcsymtacs bvlTheory bvpTheory;
open bvp_lemmasTheory bvp_simpTheory alistTheory;

infix \\ val op \\ = op THEN;

(* This file defines an optimisation that attempts to push constant
   assignments as far forward as possible. It pushes them past GC
   points so that known constants aren't stored on the stack past
   subroutine calls. Pushing the constants as far forward as possible
   also make the work of the lower-level constant folding
   optimisations more likely to be effective. *)

val pSeq2_def = Define `
  pSeq2 c1 c2 =
    if isSkip c1 then c2 else
    if isSkip c2 then c1 else Seq c1 c2`;

val ConstAssign_def = Define `
  ConstAssign v i = Assign v (Const i) [] NONE`;

(*

val toAList_def = Define `
  toAList = foldi (\(key:num) (val:'a) acc. (key,val)::acc) 0 []`


val set_foldi_values = prove(
  ``!t a i. foldi (\k v a. k INSERT a) i a t =
            a UNION IMAGE (\n. i + sptree$lrnext i * n) (domain t)``,
  Induct_on `t` >> simp[foldi_def, GSYM pred_setTheory.IMAGE_COMPOSE,
                        combinTheory.o_ABS_R]
  THEN1 simp[Once pred_setTheory.INSERT_SING_UNION, pred_setTheory.UNION_COMM]
  THEN1 (simp[pred_setTheory.EXTENSION] >> rpt gen_tac >>
      Cases_on `x IN a` >> simp[lrlemma1, lrlemma2, LEFT_ADD_DISTRIB]) >>
  simp[pred_setTheory.EXTENSION] >> rpt gen_tac >>
  Cases_on `x IN a'` >> simp[lrlemma1, lrlemma2, LEFT_ADD_DISTRIB])


  ``!f v i acc.
      ALOOKUP (foldi (\key val acc. (key,val)::acc) i acc f) v =
      case lookup (v - i) f of
      | SOME x => SOME x
      | NONE => ALOOKUP acc v``
  Induct
  THEN1 cheat
  THEN1 cheat
  THEN1 cheat

    fs [lookup_def,foldi_def,LET_DEF]





  ``!f v. ALOOKUP (toAList f) v = lookup v f``
  SIMP_TAC std_ss [toAList_def]






  foldi_def

  toListA_def

  type_of ``foldi``

combine_known k2 k3

val pConst_def = Define `
  (pConst Skip (known:int num_map) = (Skip,known)) /\
  (pConst Tick known = (Tick,known)) /\
  (pConst (Return v) known =
     case lookup v known of
     | NONE => (Return v,known)
     | SOME i => (Seq (ConstAssign v i) (Return v),known)) /\
  (pConst (Raise v) known =
     case lookup v known of
     | NONE => (Raise v,known)
     | SOME i => (Seq (ConstAssign v i) (Raise v),known)) /\
  (pConst (Seq c1 c2) known =
     let (d1,k1) = pConst c1 known in
     let (d2,k2) = pConst c2 k1 in
       (pSeq2 d1 d2,k2)) /\
  (pConst (Move v1 v2) known =
     case lookup v2 known of
     | NONE => (Move v1 v2, delete v1 known)
     | SOME i => (Skip, insert v1 i known)) /\
(*
  (pConst (If c1 c2 c3) known =
     let (d1,k1) = pConst c1 known in
     let (d2,k2) = pConst c2 k1 in
     let (d3,k3) = pConst c3 k1 in
     let (e2,e3,known) = combine_known k2 k3 in
       (If d1 (pSeq2 d2 e2) (pSeq2 d3 e3), known)) /\
*)
  (pConst (Assign v op args cut_set) known =
     (Assign v op args cut_set,delete v known))` (* todo *)

           | Call ((num # num_set) option) (num option) (num list)
           | MakeSpace num num_set
           | Handle num_set bvp_prog num num num_set bvp_prog



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

*)

val _ = export_theory();
