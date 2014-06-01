open HolKernel Parse boolLib bossLib; val _ = new_theory "bvp_live";

open pred_setTheory arithmeticTheory pairTheory listTheory combinTheory;
open finite_mapTheory sumTheory relationTheory stringTheory optionTheory;
open bytecodeTheory bvlTheory bvpTheory bvp_lemmasTheory;
open sptreeTheory lcsymtacs;

(* This script defines an optimisation that minimises the live var
   annotations that are attached to MakeSpace, Assign, Call, Handle
   etc. in BVP programs. *)

val list_insert_def = Define `
  (list_insert [] t = t) /\
  (list_insert (n::ns) t = list_insert ns (insert n () t))`;

val pLive_def = Define `
  (pLive Skip live = (Skip,live)) /\
  (pLive (Return n) live = (Return n, insert n () LN)) /\
  (pLive (Raise n) live = (Raise n, insert n () LN)) /\
  (pLive (Move n1 n2) live =
    (Move n1 n2, insert n2 () (delete n1 live))) /\
  (pLive (Seq c1 c2) live =
     let (d2,l2) = pLive c2 live in
     let (d1,l1) = pLive c1 l2 in
       (Seq d1 d2, l1)) /\
  (pLive Tick live = (Tick,live)) /\
  (pLive (Cut names) live =
     let l1 = inter names live in (Cut l1,l1)) /\
  (pLive (MakeSpace k names) live =
     let l1 = inter names live in (MakeSpace k l1,l1)) /\
  (pLive (Assign v op vs NONE) live =
     let l1 = list_insert vs (delete v live) in
       (Assign v op vs NONE,l1)) /\
  (pLive (Assign v op vs (SOME names)) live =
     let l1 = inter names (list_insert vs (delete v live)) in
       (Assign v op vs (SOME l1),l1)) /\
  (pLive (If c1 n c2 c3) live =
     let (d3,l3) = pLive c3 live in
     let (d2,l2) = pLive c2 live in
     let (d1,l1) = pLive c1 (union l2 l3) in
       (If d1 n d2 d3, l1)) /\
  (pLive (Call NONE dest vs) live =
     (Call NONE dest vs,list_to_num_set vs)) /\
  (pLive (Call (SOME (n,names)) dest vs) live =
     let l1 = inter names (list_insert vs (delete n live)) in
       (Call (SOME (n,l1)) dest vs,l1)) /\
  (pLive (Handle ns1 c1 n1 n2 ns2 c2) live =
     let (d1,l1) = pLive c1 (insert n1 () LN) in
     let (d2,l2) = pLive c2 live in
     let ns1' = inter ns1 l1 in
     let ns2' = inter ns2 (delete n2 l2) in
       (Handle ns1' d1 n1 n2 ns2' d2, union ns1' ns2'))`;

val state_rel_def = Define `
  state_rel (s1:bvp_state) (t1:bvp_state) (live:num_set) <=>
    s1.code = t1.code /\ s1.clock = t1.clock /\
    s1.globals = t1.globals /\ s1.space = t1.space /\
    s1.output = t1.output /\ s1.refs = t1.refs /\
    s1.handler = t1.handler /\
    (!x. x IN domain live ==> (lookup x s1.locals = lookup x t1.locals))`;

val state_rel_ID = prove(
  ``!s live. state_rel s s live``,
  fs [state_rel_def]);

val lookup_inter_assoc = prove(
  ``lookup x (inter t1 (inter t2 t3)) =
    lookup x (inter (inter t1 t2) t3)``,
  fs [lookup_inter] \\ REPEAT BasicProvers.CASE_TAC);

val lookup_inter_domain = prove(
  ``x IN domain t2 ==> (lookup x (inter t1 t2) = lookup x t1)``,
  fs [lookup_inter,domain_lookup] \\ REPEAT BasicProvers.CASE_TAC);

val pEval_pLive = prove(
  ``!c s1 res s2 l2 t1 l1 d.
      (pEval (c,s1) = (res,s2)) /\ state_rel s1 t1 l1 /\
      (pLive c l2 = (d,l1)) /\ (res <> SOME Error) ==>
      ?t2. (pEval (d,t1) = (res,t2)) /\
           state_rel s2 t2 (case res of
                            | NONE => l2
                            | _ => LN)``,
  ONCE_REWRITE_TAC [EQ_SYM_EQ]
  \\ recInduct pEval_ind \\ REPEAT STRIP_TAC
  THEN1 (* Skip *)
    (fs [pEval_def,pLive_def])
  THEN1 (* Move *)
    (fs [pEval_def,pLive_def,get_var_def,state_rel_def]
     \\ Cases_on `lookup src t1.locals`
     \\ fs [set_var_def,lookup_insert])
  THEN1 (* Assign *) cheat
  THEN1 (* Tick *)
    (fs [pEval_def,pLive_def,state_rel_def] \\ SRW_TAC [] []
     \\ fs [call_env_def,dec_clock_def]
     \\ BasicProvers.FULL_CASE_TAC \\ fs [])
  THEN1 (* MakeSpace *)
   (fs [pEval_def,pLive_def,get_var_def,state_rel_def,LET_DEF,cut_env_def]
    \\ Cases_on `domain names SUBSET domain s.locals` \\ fs []
    \\ SRW_TAC [] [add_space_def]
    \\ fs [domain_inter,lookup_inter_assoc,lookup_inter_domain]
    \\ fs [domain_lookup,PULL_EXISTS,lookup_inter_EQ,SUBSET_DEF]
    \\ Cases_on `lookup x names` \\ fs [lookup_inter,oneTheory.one]
    \\ REPEAT BasicProvers.CASE_TAC \\ METIS_TAC [])
  THEN1 (* Cut *)
   (fs [pEval_def,pLive_def,get_var_def,state_rel_def,LET_DEF,cut_env_def]
    \\ Cases_on `domain names SUBSET domain s.locals` \\ fs []
    \\ SRW_TAC [] []
    \\ fs [domain_inter,lookup_inter_assoc,lookup_inter_domain]
    \\ fs [domain_lookup,PULL_EXISTS,lookup_inter_EQ,SUBSET_DEF]
    \\ Cases_on `lookup x names` \\ fs [lookup_inter,oneTheory.one]
    \\ REPEAT BasicProvers.CASE_TAC \\ METIS_TAC [])
  THEN1 (* Raise *)
   (fs [pEval_def,pLive_def] \\ Cases_on `get_var n s` \\ fs []
    \\ fs [state_rel_def]
    \\ Q.PAT_ASSUM `lookup n s.locals = lookup n t1.locals`
         (ASSUME_TAC o GSYM) \\ fs [get_var_def]
    \\ SRW_TAC [] [call_env_def]
    \\ fs [jump_exc_def] \\ Cases_on `t1.handler < LENGTH t1.stack` \\ fs []
    \\ cheat)
  THEN1 (* Return *)
   (fs [pEval_def,pLive_def] \\ Cases_on `get_var n s` \\ fs []
    \\ fs [state_rel_def]
    \\ Q.PAT_ASSUM `lookup n s.locals = lookup n t1.locals`
         (ASSUME_TAC o GSYM) \\ fs [get_var_def]
    \\ SRW_TAC [] [call_env_def])
  THEN1 (* Seq *)
   (fs [pEval_def]
    \\ `?res1 u1. pEval (c1,s) = (res1,u1)` by METIS_TAC [PAIR]
    \\ `?res2 u2. pEval (c2,u1) = (res2,u2)` by METIS_TAC [PAIR]
    \\ `?x2 l5. pLive c2 l2 = (x2,l5)` by METIS_TAC [PAIR]
    \\ `?x1 l6. pLive c1 l5 = (x1,l6)` by METIS_TAC [PAIR]
    \\ fs [LET_DEF,pLive_def,pEval_def,PULL_FORALL,AND_IMP_INTRO]
    \\ FIRST_X_ASSUM (MP_TAC o GSYM o Q.SPECL [`l5`,`t1`]) \\ fs []
    \\ FIRST_X_ASSUM (MP_TAC o GSYM o Q.SPECL [`l2`]) \\ fs []
    \\ REPEAT STRIP_TAC
    \\ Cases_on `res1 = SOME Error` \\ fs []
    \\ Cases_on `res1 = NONE` \\ fs [] \\ SRW_TAC [] []
    THEN1 (FIRST_X_ASSUM (MP_TAC o GSYM o Q.SPECL [`t2`]) \\ fs [])
    \\ fs [state_rel_def] \\ IMP_RES_TAC pEval_locals_LN \\ fs [])
  THEN1 (* Handle *) cheat
  THEN1 (* If *) cheat
  THEN1 (* Call *) cheat);

val SPLIT_PAIR = prove(
  ``!x y z. (x = (y,z)) <=> (y = FST x) /\ (z = SND x)``,
  Cases \\ SRW_TAC [] [] \\ METIS_TAC []);

val pLive_correct = prove(
  ``!c s. FST (pEval (c,s)) <> SOME Error /\
          FST (pEval (c,s)) <> NONE ==>
          (pEval (FST (pLive c LN),s) = pEval (c,s))``,
  REPEAT STRIP_TAC
  \\ (pEval_pLive |> ONCE_REWRITE_RULE [SPLIT_PAIR]
       |> SIMP_RULE std_ss [] |> Q.SPECL [`c`,`s`,`LN`,`s`]
       |> SIMP_RULE std_ss [state_rel_ID] |> MP_TAC)
  \\ fs [] \\ REPEAT STRIP_TAC
  \\ Cases_on `pEval (c,s)` \\ fs []
  \\ Cases_on `pEval (FST (pLive c LN),s)` \\ fs []
  \\ SRW_TAC [] []
  \\ IMP_RES_TAC pEval_locals_LN
  \\ fs [state_rel_def,bvp_state_explode]
  \\ MP_TAC (Q.SPECL [`c`,`s`] pEval_stack)
  \\ MP_TAC (Q.SPECL [`FST (pLive c LN)`,`s`] pEval_stack)
  \\ fs [] \\ Cases_on `q` \\ fs [] \\ Cases_on `x` \\ fs []
  \\ REPEAT STRIP_TAC \\ fs [] \\ SRW_TAC [] [] \\ fs [] \\ cheat);

val _ = export_theory();
