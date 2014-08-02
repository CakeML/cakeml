open HolKernel Parse boolLib bossLib; val _ = new_theory "bvl_handle";

open pred_setTheory arithmeticTheory pairTheory listTheory combinTheory;
open finite_mapTheory sumTheory relationTheory stringTheory optionTheory;
open bytecodeTheory bvlTheory sptreeTheory lcsymtacs;

(* BVL transformation that introduces a Let into each Handle
   body. This is preparation for BVL --> BVI compilation. *)

val bHandle_def = tDefine "bHandle" `
  (bHandle n [] = []) /\
  (bHandle n (x::y::xs) = bHandle n [x] ++ bHandle n (y::xs)) /\
  (bHandle n [Var v] = if v < n then [Var v]
                       else [Op (Const 0) []]) /\
  (bHandle n [If x1 x2 x3] =
     [If (HD (bHandle n [x1])) (HD (bHandle n [x2])) (HD (bHandle n [x3]))]) /\
  (bHandle n [Let xs x2] =
     [Let (bHandle n xs) (HD (bHandle (n + LENGTH xs) [x2]))]) /\
  (bHandle n [Raise x1] =
     [Raise (HD (bHandle n [x1]))]) /\
  (bHandle n [Handle x1 x2] =
     let y1 = HD (bHandle n [x1]) in
     let y2 = HD (bHandle (n+1) [x2]) in
       [Handle (Let (GENLIST Var n) y1) y2]) /\
  (bHandle n [Op op xs] = [Op op (bHandle n xs)]) /\
  (bHandle n [Tick x] = [Tick (HD (bHandle n [x]))]) /\
  (bHandle n [Call dest xs] = [Call dest (bHandle n xs)])`
 (WF_REL_TAC `measure (bvl_exp1_size o SND)`);

(* proof of semantics preservation *)

val bHandle_LENGTH = prove(
  ``!n xs. LENGTH (bHandle n xs) = LENGTH xs``,
  HO_MATCH_MP_TAC (fetch "-" "bHandle_ind") \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC (srw_ss()) [bHandle_def,ADD1,LET_DEF]
  \\ SRW_TAC [] [] \\ DECIDE_TAC);

val SING_HD_bHandle = prove(
  ``[HD (bHandle n [x])] = bHandle n [x]``,
  MP_TAC (Q.SPECL [`n`,`[x]`] bHandle_LENGTH)
  \\ Cases_on `bHandle n [x]` \\ fs [LENGTH_NIL]);

val bEval_GENLIST = prove(
  ``!env ys s.
       bEval (GENLIST Var (LENGTH env),env ++ ys,s) = (Result env,s)``,
  HO_MATCH_MP_TAC SNOC_INDUCT \\ REPEAT STRIP_TAC
  THEN1 (EVAL_TAC \\ SIMP_TAC std_ss [])
  \\ SRW_TAC [] [GENLIST,REVERSE_SNOC]
  \\ fs [bEval_SNOC] \\ FULL_SIMP_TAC std_ss [SNOC_APPEND,GSYM APPEND_ASSOC]
  \\ fs [bEval_def] \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND]
  \\ fs [DECIDE ``0 < 1 + n:num``]
  \\ fs [rich_listTheory.EL_APPEND2])

val bHandle_thm = prove(
  ``!xs env s1 res s2 ys.
      (bEval (xs,env,s1) = (res,s2)) /\ res <> Error ==>
      (bEval (bHandle (LENGTH env) xs,env ++ ys,s1) = (res,s2))``,
  SIMP_TAC std_ss [Once EQ_SYM_EQ]
  \\ recInduct bEval_ind \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [bHandle_def,bEval_def,SING_HD_bHandle]
  THEN1 (* Cons *)
   (ONCE_REWRITE_TAC [GSYM SING_HD_bHandle] \\ fs []
    \\ SIMP_TAC std_ss [Once bEval_CONS]
    \\ fs [SING_HD_bHandle]
    \\ Cases_on `bEval ([x],env,s)` \\ Cases_on `q` \\ fs []
    \\ Cases_on `bEval (y::xs,env,r)` \\ Cases_on `q` \\ fs [])
  THEN1 (* Var *)
   (Cases_on `n < LENGTH env` \\ fs []
    \\ `n < LENGTH env + LENGTH ys` by DECIDE_TAC
    \\ fs [bHandle_def,bEval_def,rich_listTheory.EL_APPEND1])
  THEN1 (* If *)
   (Cases_on `bEval ([x1],env,s)` \\ Cases_on `q` \\ fs []
    \\ SRW_TAC [] [] \\ fs []
    \\ FIRST_X_ASSUM MATCH_MP_TAC \\ METIS_TAC [])
  THEN1 (* Let *)
   (Cases_on `bEval (xs,env,s)` \\ Cases_on `q` \\ fs []
    \\ ONCE_REWRITE_TAC [ADD_COMM]
    \\ `LENGTH xs = LENGTH a` by (IMP_RES_TAC bEval_IMP_LENGTH \\ fs [])
    \\ fs [] \\ FIRST_X_ASSUM MATCH_MP_TAC \\ METIS_TAC [])
  THEN1 (* Raise *)
   (Cases_on `bEval ([x1],env,s)` \\ Cases_on `q` \\ fs [])
  THEN1 (* Handle *)
   (fs [LET_DEF,bEval_def,SING_HD_bHandle,bEval_GENLIST]
    \\ Cases_on `bEval ([x1],env,s1)` \\ fs []
    \\ `q <> Error` by (REPEAT STRIP_TAC \\ fs []) \\ fs []
    \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC] \\ fs []
    \\ Cases_on `q` \\ fs [ADD1]
    \\ FIRST_X_ASSUM MATCH_MP_TAC \\ METIS_TAC [])
  THEN1 (* Op *)
   (Cases_on `bEval (xs,env,s)` \\ Cases_on `q` \\ fs [])
  THEN1 (* Tick *)
   (Cases_on `s.clock = 0` \\ fs [SING_HD_bHandle]
    \\ FIRST_X_ASSUM MATCH_MP_TAC \\ METIS_TAC [])
  THEN1 (* Call *)
   (Cases_on `bEval (xs,env,s1)` \\ Cases_on `q` \\ fs []))
  |> Q.SPECL [`xs`,`env`,`s1`,`res`,`s2`,`[]`]
  |> SIMP_RULE std_ss [APPEND_NIL];

val _ = save_thm("bHandle_thm",bHandle_thm);

val _ = export_theory();
