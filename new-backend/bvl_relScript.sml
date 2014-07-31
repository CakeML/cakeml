open HolKernel Parse boolLib bossLib; val _ = new_theory "bvl_rel";

open pred_setTheory arithmeticTheory pairTheory listTheory combinTheory;
open finite_mapTheory sumTheory relationTheory stringTheory optionTheory;
open bytecodeTheory bvlTheory;

infix \\ val op \\ = op THEN;

(* The evaluation is defined as a big-step operational semantics. *)

val isResult_def = Define `
  (isResult (Result _) = T) /\
  (isResult _ = F)`;

val isException_def = Define `
  (isException (Exception _) = T) /\
  (isException _ = F)`;

val isError_def = Define `
  (isError (Error) = T) /\
  (isError _ = F)`;

val _ = computeLib.add_persistent_funs
  ["isResult_def","isException_def","isError_def"];

val (bEvalRel_rules, bEvalRel_ind_raw, bEvalRel_cases) = Hol_reln `
  (!env s.
     bEvalRel ([],env,s) (Result [],s))
  /\
  (!x y xs env s s1 res.
     bEvalRel ([x],env,s) (res,s1) /\ ~(isResult res) ==>
     bEvalRel (x::y::xs,env,s) (res,s1))
  /\
  (!x y xs env s res.
     bEvalRel ([x],env,s) (Result [v1],s1) /\
     bEvalRel (y::xs,env,s1) (res,s2) ==>
     bEvalRel (x::y::xs,env,s)
       ((case res of
         | Result vs => Result (v1::vs)
         | z => z), s2))
  /\
  (!n env s.
     bEvalRel ([Var n],env,s)
       (if n < LENGTH env then (Result [EL n env],s) else (Error,s)))
  /\
  (!x1 x2 x3 env s s2 res.
     bEvalRel ([x1],env,s) (res,s2) /\ ~(isResult res) ==>
     bEvalRel ([If x1 x2 x3],env,s) (res,s2))
  /\
  (!x1 x2 x3 env s s1 v1.
     bEvalRel ([x1],env,s) (Result [v1],s1) /\
     ~(v1 = bool_to_val T) /\
     ~(v1 = bool_to_val F) ==>
     bEvalRel ([If x1 x2 x3],env,s) (Error,s1))
  /\
  (!x1 x2 x3 env s s1 res v1.
     bEvalRel ([x1],env,s) (Result [v1],s1) /\
     (v1 = bool_to_val T) /\
     bEvalRel ([x2],env,s1) (res,s2) ==>
     bEvalRel ([If x1 x2 x3],env,s) (res,s2))
  /\
  (!x1 x2 x3 env s s1 res v1.
     bEvalRel ([x1],env,s) (Result [v1],s1) /\
     (v1 = bool_to_val F) /\
     bEvalRel ([x3],env,s1) (res,s2) ==>
     bEvalRel ([If x1 x2 x3],env,s) (res,s2))
  /\
  (!xs env s s2 res.
     bEvalRel (xs,env,s) (res,s2) /\ ~(isResult res) ==>
     bEvalRel ([Let xs x2],env,s) (res,s2))
  /\
  (!xs env s s1 res.
     bEvalRel (xs,env,s) (Result vs,s1) /\
     bEvalRel ([x2],vs ++ env,s1) (res,s2) ==>
     bEvalRel ([Let xs x2],env,s) (res,s2))
  /\
  (!x1 env s s2 res.
     bEvalRel ([x1],env,s) (res,s2) /\ ~(isResult res) ==>
     bEvalRel ([Raise x1],env,s) (res,s2))
  /\
  (!x1 env s s1 v1.
     bEvalRel ([x1],env,s) (Result [v1],s1) ==>
     bEvalRel ([Raise x1],env,s) (Exception v1,s1))
  /\
  (!x1 env s s1 res.
     bEvalRel ([x1],env,s) (res,s1) /\ ~isException res ==>
     bEvalRel ([Handle x1 x2],env,s) (res,s1))
  /\
  (!x1 env s s1 res v.
     bEvalRel ([x1],env,s) (Exception v,s1) /\
     bEvalRel ([x2],v::env,s1) (res,s2) ==>
     bEvalRel ([Handle x1 x2],env,s) (res,s2))
  /\
  (!op xs env s res s1.
     bEvalRel (xs,env,s) (res,s1) /\ ~isResult res ==>
     bEvalRel ([Op op xs],env,s) (res,s1))
  /\
  (!op xs env s vs s1.
     bEvalRel (xs,env,s) (Result vs,s1) ==>
     bEvalRel ([Op op xs],env,s)
           (case bEvalOp op vs s1 of
            | NONE => (Error,s1)
            | SOME (v,s2) => (Result [v],s2)))
  /\
  (!x env s.
     (s.clock = 0) ==>
     bEvalRel ([Tick x],env,s) (TimeOut,s))
  /\
  (!x env s res.
     (s.clock <> 0) /\
     bEvalRel ([x],env,dec_clock s) (res,s2) ==>
     bEvalRel ([Tick x],env,s) (res,s2))
  /\
  (!dest xs env s res s1.
     bEvalRel (xs,env,s) (res,s1) /\ ~isResult res ==>
     bEvalRel ([Call dest xs],env,s) (res,s1))
  /\
  (!dest xs env s vs s1.
     bEvalRel (xs,env,s) (Result vs,s1) /\
     (find_code dest vs s1.code = NONE) ==>
     bEvalRel ([Call dest xs],env,s) (Error,s1))
  /\
  (!dest xs env s vs s1 args exp.
     bEvalRel (xs,env,s) (Result vs,s1) /\
     (find_code dest vs s1.code = SOME (args,exp)) /\
     (s1.clock = 0) ==>
     bEvalRel ([Call dest xs],env,s) (TimeOut,s1))
  /\
  (!dest xs env s vs s1 res args exp.
     bEvalRel (xs,env,s) (Result vs,s1) /\
     (find_code dest vs s1.code = SOME (args,exp)) /\
     (s1.clock <> 0) /\
     bEvalRel ([exp],args,dec_clock s1) (res,s2) ==>
     bEvalRel ([Call dest xs],env,s) (res,s2))`;

(* Improve ind thm *)

val bEvalRel_ind = save_thm("bEvalRel_ind",
  IndDefLib.derive_strong_induction(bEvalRel_rules,bEvalRel_ind_raw)
  |> CONV_RULE (QUANT_CONV (RAND_CONV (SIMP_CONV std_ss [FORALL_PROD])))
  |> Q.SPEC `\(x1,x2,x3) (y1,y2). P x1 x2 x3 y1 y2`
  |> SIMP_RULE std_ss [] |> Q.GEN `P`);

(* Improve cases thm *)

val bEvalRel_case0 =
  ``bEvalRel ([],env,s) res``
  |> ONCE_REWRITE_CONV [bEvalRel_cases]
  |> SIMP_RULE (srw_ss()) []

val bEvalRel_case1 =
  ([],``!x. T = bEvalRel ([x],env,s) res``)
  |> Cases |> fst |> map (rand o snd)
  |> map (SIMP_RULE (srw_ss()) [] o ONCE_REWRITE_CONV [bEvalRel_cases])

val bEvalRel_case2 =
  ``bEvalRel (x::y::xs,env,s) res``
  |> ONCE_REWRITE_CONV [bEvalRel_cases]
  |> SIMP_RULE (srw_ss()) []

val bEvalRel_cases = save_thm("bEvalRel_cases",
  LIST_CONJ ([bEvalRel_case0,bEvalRel_case2] @ bEvalRel_case1));

(* LENGTH lemma *)

val bEvalRel_LENGTH_LEMMA = prove(
  ``!xs env s res s1.
      bEvalRel (xs,env,s) (res,s1) ==>
        case res of
        | Result vs => (LENGTH xs = LENGTH vs)
        | _ => T``,
  HO_MATCH_MP_TAC bEvalRel_ind \\ SRW_TAC [] []
  \\ TRY (Cases_on `res`) \\ FULL_SIMP_TAC (srw_ss()) [isResult_def]
  \\ Cases_on `bEvalOp op vs s1` \\ SRW_TAC [] []
  \\ Cases_on `x` \\ FULL_SIMP_TAC (srw_ss()) []);

val bEvalRel_LENGTH = store_thm("bEvalRel_LENGTH",
  ``!xs env s1 vs s2.
       bEvalRel (xs,env,s1) (Result vs,s2) ==> (LENGTH vs = LENGTH xs)``,
  REPEAT STRIP_TAC
  \\ IMP_RES_TAC bEvalRel_LENGTH_LEMMA
  \\ FULL_SIMP_TAC (srw_ss()) []);

(* code stays unchanged *)

val bEvalRel_code = store_thm("bEvalRel_code",
  ``!xs env s res s1.
      bEvalRel (xs,env,s) (res,s1) ==> (s1.code = s.code)``,
  HO_MATCH_MP_TAC bEvalRel_ind \\ SRW_TAC [] [dec_clock_def]
  \\ BasicProvers.FULL_CASE_TAC \\ FULL_SIMP_TAC (srw_ss()) []
  \\ BasicProvers.FULL_CASE_TAC \\ FULL_SIMP_TAC (srw_ss()) []
  \\ IMP_RES_TAC bEvalOp_const \\ FULL_SIMP_TAC (srw_ss()) []);

(* Equivalence between functional and relation definitions *)

val bEvalRel_bEval = store_thm("bEvalRel_bEval",
  ``!xs env s1 res s2.
      bEvalRel (xs,env,s1) (res,s2) ==>
      (bEval (xs,env,s1) = (res,s2))``,
  HO_MATCH_MP_TAC bEvalRel_ind \\ REPEAT STRIP_TAC
  \\ ASM_SIMP_TAC (srw_ss()) [bEval_def]
  \\ TRY (Cases_on `res`
          \\ FULL_SIMP_TAC (srw_ss()) [isResult_def,isException_def] \\ NO_TAC)
  \\ SRW_TAC [] [] \\ FULL_SIMP_TAC std_ss []
  \\ REPEAT (BasicProvers.FULL_CASE_TAC)
  \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC (srw_ss()) []
  \\ POP_ASSUM MP_TAC \\ EVAL_TAC);

val _ = export_theory();
