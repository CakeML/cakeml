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
     let ns2' = inter ns2 (union (delete n1 live) (delete n2 l2)) in
       (Handle ns1' d1 n1 n2 ns2' d2, union ns1' ns2'))`;

val state_rel_def = Define `
  state_rel (s1:bvp_state) (t1:bvp_state) (live:num_set) <=>
    s1.code = t1.code /\ s1.clock = t1.clock /\
    s1.globals = t1.globals /\ s1.space = t1.space /\
    s1.output = t1.output /\ s1.refs = t1.refs /\
    s1.handler = t1.handler /\ (LENGTH s1.stack = LENGTH t1.stack) /\
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

val pEval_NONE_jump_exc = prove(
  ``(pEval (c,s) = (NONE,u1)) /\ (jump_exc u1 = SOME x) ==>
    (jump_exc s = SOME (s with <| stack := x.stack ;
                                  handler := x.handler ;
                                  locals := x.locals |>))``,
  REPEAT STRIP_TAC \\ MP_TAC (Q.SPECL [`c`,`s`] pEval_stack) \\ fs []
  \\ fs [jump_exc_def] \\ REPEAT STRIP_TAC \\ fs []
  \\ REPEAT (BasicProvers.FULL_CASE_TAC \\ fs [])
  \\ SRW_TAC [] []);

val pEval_NONE_jump_exc_ALT = prove(
  ``(pEval (c,s) = (NONE,u1)) /\ (jump_exc s = SOME x) ==>
    (jump_exc u1 = SOME (u1 with <| stack := x.stack ;
                                  handler := x.handler ;
                                  locals := x.locals |>))``,
  REPEAT STRIP_TAC \\ MP_TAC (Q.SPECL [`c`,`s`] pEval_stack) \\ fs []
  \\ fs [jump_exc_def] \\ REPEAT STRIP_TAC \\ fs []
  \\ REPEAT (BasicProvers.FULL_CASE_TAC \\ fs [])
  \\ SRW_TAC [] []);

val jump_exc_IMP_state_rel = prove(
  ``!s1 t1 s2 t2.
      (jump_exc s1 = SOME s2) /\ (jump_exc t1 = SOME t2) /\
      state_rel s1 t1 LN /\ (LENGTH s2.stack = LENGTH t2.stack) ==>
      state_rel (s2 with handler := s1.handler)
                (t2 with handler := t1.handler) LN``,
  REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [jump_exc_def]
  \\ REPEAT (BasicProvers.FULL_CASE_TAC \\ fs [])
  \\ SRW_TAC [] [] \\ fs [state_rel_def]);

val LAST_N_LEMMA = prove(
  ``(LAST_N (LENGTH xs + 1 + 1) (x::y::xs) = x::y::xs) /\
    (LAST_N (LENGTH xs + 1) (x::xs) = x::xs)``,
  MP_TAC (Q.SPEC `x::y::xs` LAST_N_LENGTH)
  \\ MP_TAC (Q.SPEC `x::xs` LAST_N_LENGTH) \\ fs [ADD1]);

val pEval_pLive = prove(
  ``!c s1 res s2 l2 t1 l1 d.
      (pEval (c,s1) = (res,s2)) /\ state_rel s1 t1 l1 /\
      (pLive c l2 = (d,l1)) /\ (res <> SOME Error) /\
      (!s3. (jump_exc s1 = SOME s3) ==>
            ?t3. (jump_exc t1 = SOME t3) /\ state_rel s3 t3 LN /\
                 (t3.handler = s3.handler) /\
                 (LENGTH t3.stack = LENGTH s3.stack)) ==>
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
    \\ Cases_on `jump_exc s` \\ fs [] \\ SRW_TAC [] []
    \\ Cases_on `jump_exc t1` \\ fs [] \\ SRW_TAC [] [])
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
    \\ fs [LET_DEF,pLive_def,pEval_def]
    \\ FIRST_X_ASSUM (MP_TAC o GSYM o Q.SPECL [`l5`,`t1`]) \\ fs []
    \\ Cases_on `res1 = SOME Error` \\ fs []
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1 (METIS_TAC [])
    \\ REPEAT STRIP_TAC
    \\ REVERSE (Cases_on `res1 = NONE`) \\ fs []
    THEN1 (SRW_TAC [] [] \\ Cases_on `res` \\ fs [])
    \\ Q.PAT_ASSUM `!x y. bb` (MP_TAC o GSYM o Q.SPECL [`l2`,`t2`]) \\ fs []
    \\ REV_FULL_SIMP_TAC std_ss []
    \\ MATCH_MP_TAC IMP_IMP \\ REPEAT STRIP_TAC \\ fs []
    \\ Q.PAT_ASSUM `!x.bbb` (ASSUME_TAC o GSYM)
    \\ IMP_RES_TAC pEval_NONE_jump_exc \\ Q.PAT_ASSUM `!x.bbb` (K ALL_TAC)
    \\ RES_TAC
    \\ IMP_RES_TAC pEval_NONE_jump_exc_ALT \\ POP_ASSUM (K ALL_TAC)
    \\ POP_ASSUM (K ALL_TAC) \\ fs []
    \\ `state_rel u1 t2 LN` by fs [state_rel_def]
    \\ MP_TAC (Q.SPECL [`u1`,`t2`] jump_exc_IMP_state_rel) \\ fs []
    \\ ASM_SIMP_TAC (srw_ss()) [state_rel_def])
  THEN1 (* Handle *)
   (fs [pEval_def]
    \\ Cases_on `cut_env ns1 s.locals` \\ fs []
    \\ Q.MATCH_ASSUM_RENAME_TAC `cut_env ns1 s.locals = SOME env1` []
    \\ Cases_on `cut_env ns2 s.locals` \\ fs []
    \\ Q.MATCH_ASSUM_RENAME_TAC `cut_env ns2 s.locals = SOME env2` []
    \\ Cases_on `pEval (c1,push_exc env1 env2 s)` \\ fs []
    \\ Cases_on `pLive c1 (insert v () LN)` \\ fs [LET_DEF]
    \\ Cases_on `pLive c2 l2` \\ fs []
    \\ Q.MATCH_ASSUM_RENAME_TAC `pLive c2 l2 = (q2,r2)` []
    \\ Q.MATCH_ASSUM_RENAME_TAC `pLive c1 (insert v () LN) = (q1,r1)` []
    \\ fs [pLive_def,LET_DEF,pEval_def]
    \\ `domain (inter ns1 r1) SUBSET domain t1.locals /\
        domain (inter ns2 (delete n r2)) SUBSET domain t1.locals /\
        domain (inter ns2 (union (delete v l2) (delete n r2))) SUBSET
          domain t1.locals`
           by ALL_TAC THEN1
     (fs [domain_inter,SUBSET_DEF,cut_env_def,state_rel_def,
          domain_union,domain_delete] \\ REPEAT STRIP_TAC
      \\ RES_TAC \\ fs [domain_lookup])
    \\ fs [cut_env_def]
    \\ Q.ABBREV_TAC `ns3 = (inter ns1 r1)`
    \\ Q.ABBREV_TAC `ns4 = (inter ns2 (union (delete v l2) (delete n r2)))`
    \\ FIRST_X_ASSUM (MP_TAC o GSYM o Q.SPECL [`(insert v () LN)`,
          `push_exc (inter t1.locals (ns3:num_set))
                    (inter t1.locals (ns4:num_set)) t1`])
    \\ fs [] \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
     (REPEAT STRIP_TAC \\ UNABBREV_ALL_TAC \\ fs [] THEN1
       (fs[state_rel_def,push_exc_def] \\ SRW_TAC [] []
        \\ fs [lookup_inter_assoc,lookup_inter_domain]
        \\ fs [domain_union,domain_inter,domain_delete]
        \\ fs[lookup_inter]
        \\ Cases_on `lookup x ns1` \\ fs []
        THEN1 (REPEAT BasicProvers.CASE_TAC \\ fs [])
        \\ fs [domain_lookup])
      \\ fs [jump_exc_def,push_exc_def,LAST_N_LEMMA]
      \\ SRW_TAC [] [] \\ fs [state_rel_def] \\ DECIDE_TAC)
    \\ REPEAT STRIP_TAC \\ fs []
    \\ Cases_on `q` \\ fs [] THEN1
     (Cases_on `get_var v r` \\ Cases_on `pop_exc r` \\ fs []
      \\ `get_var v t2 = SOME x` by (fs [state_rel_def,get_var_def] \\ NO_TAC)
      \\ fs [] \\ (Q.SPECL [`q1`,`push_exc
            (inter t1.locals (ns3:num_set))
            (inter t1.locals (ns4:num_set)) t1`] pEval_stack |> MP_TAC) \\ fs []
      \\ REPEAT STRIP_TAC
      \\ ASM_SIMP_TAC (srw_ss()) [pop_exc_def,push_exc_def]
      \\ fs [] \\ (Q.SPECL [`c1`,`push_exc env1 env2 s`]
                     pEval_stack |> MP_TAC) \\ fs []
      \\ REPEAT STRIP_TAC \\ fs [pop_exc_def,push_exc_def] \\ SRW_TAC [] []
      \\ fs [state_rel_def,set_var_def,lookup_insert]
      \\ REPEAT STRIP_TAC
      \\ Q.MATCH_ASSUM_RENAME_TAC `x6 IN domain l2` []
      \\ Cases_on `x6 = v` \\ fs []
      \\ UNABBREV_ALL_TAC
      \\ ASM_SIMP_TAC std_ss [lookup_inter,lookup_delete,lookup_union]
      \\ `lookup x6 l2 = SOME ()` by fs [domain_lookup,oneTheory.one]
      \\ fs [] \\ Cases_on `lookup x6 ns2` \\ fs []
      THEN1 (REPEAT BasicProvers.CASE_TAC \\ fs [])
      \\ fs [oneTheory.one]
      \\ fs [domain_union,domain_inter,domain_delete]
      \\ `x6 IN domain ns2` by METIS_TAC [domain_lookup]
      \\ RES_TAC \\ fs [])
    \\ Cases_on `x` \\ fs []
    \\ Q.PAT_ASSUM `(res,s2) = xxx` (ASSUME_TAC o GSYM) \\ fs []
    \\ FIRST_X_ASSUM MATCH_MP_TAC \\ fs [] \\ REPEAT STRIP_TAC
    \\ (Q.SPECL [`q1`,`push_exc
              (inter t1.locals (ns3:num_set))
              (inter t1.locals (ns4:num_set)) t1`] pEval_stack |> MP_TAC) \\ fs []
    \\ ASM_SIMP_TAC (srw_ss()) [Once jump_exc_def,push_exc_def,LAST_N_LEMMA]
    \\ ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ REPEAT STRIP_TAC
    \\ fs [] \\ (Q.SPECL [`c1`,`push_exc env1 env2 s`]
                    pEval_stack |> MP_TAC) \\ fs []
    \\ ASM_SIMP_TAC (srw_ss()) [Once jump_exc_def,push_exc_def,LAST_N_LEMMA]
    \\ ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ REPEAT STRIP_TAC THEN1
     (SRW_TAC [] [] \\ fs [state_rel_def,set_var_def,lookup_insert]
      \\ REPEAT STRIP_TAC \\ Cases_on `x = n` \\ fs []
      \\ Q.PAT_ASSUM `inter s.locals ns2 = r.locals` (ASSUME_TAC o GSYM)
      \\ UNABBREV_ALL_TAC
      \\ fs [] \\ ASM_SIMP_TAC std_ss [lookup_inter,lookup_delete,lookup_union]
      \\ fs [domain_union,domain_inter,domain_delete]
      \\ Cases_on `lookup x ns2` \\ fs []
      THEN1 (REPEAT BasicProvers.CASE_TAC \\ fs [])
      \\ `x IN domain ns2` by METIS_TAC [domain_lookup]
      \\ `lookup x s.locals = lookup x t1.locals` by METIS_TAC []
      \\ fs [] \\ fs [domain_lookup]
      \\ REPEAT BasicProvers.CASE_TAC \\ fs [])
    \\ fs [jump_exc_def,set_var_def]
    \\ Cases_on `LAST_N (s.handler + 1) s.stack` \\ fs []
    \\ Cases_on `t` \\ fs []
    \\ Cases_on `h'` \\ fs []
    \\ Cases_on `h` \\ fs [] \\ SRW_TAC [] []
    \\ Cases_on `LAST_N (t1.handler + 1) t1.stack` \\ fs []
    \\ Cases_on `t` \\ fs []
    \\ Cases_on `h'` \\ fs []
    \\ Cases_on `h` \\ fs [] \\ SRW_TAC [] []
    \\ fs [state_rel_def])
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
  \\ SRW_TAC [] [] \\ Cases_on `q` \\ fs []
  \\ IMP_RES_TAC pEval_locals_LN
  \\ fs [state_rel_def,bvp_state_explode]
  \\ MP_TAC (Q.SPECL [`c`,`s`] pEval_stack)
  \\ MP_TAC (Q.SPECL [`FST (pLive c LN)`,`s`] pEval_stack)
  \\ fs [] \\ Cases_on `x` \\ fs []
  \\ REPEAT STRIP_TAC \\ fs [] \\ SRW_TAC [] [] \\ fs []);

val _ = export_theory();
