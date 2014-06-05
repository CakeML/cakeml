open HolKernel Parse boolLib bossLib; val _ = new_theory "bvp_space";

open pred_setTheory arithmeticTheory pairTheory listTheory combinTheory;
open finite_mapTheory sumTheory relationTheory stringTheory optionTheory;
open bytecodeTheory bvlTheory bvpTheory bvp_lemmasTheory;
open sptreeTheory lcsymtacs;

(* BVP optimisation that lumps together MakeSpace operations. *)

val pMakeSpace_def = Define `
  (pMakeSpace (INL c) = c) /\
  (pMakeSpace (INR (k,names,c)) = Seq (MakeSpace k names) c)`;

val pSpace_def = Define `
  (pSpace (MakeSpace k names) = INR (k,names,Skip)) /\
  (pSpace (Seq c1 c2) =
     let d1 = pMakeSpace (pSpace c1) in
     let x2 = pSpace c2 in
       case x2 of
       | INL c4 =>
          (case c1 of
           | MakeSpace k names => INR (k,names,c4)
           | Skip => INL c4
           | _ => INL (Seq d1 c4))
       | INR (k,names,c4) =>
          (case c1 of
           | Skip => INR (k,names,c4)
           | MakeSpace k2 names2 => INR (k+k2,inter names names2,c4)
           | Move dest src =>
               INR (k,insert src () (delete dest names),
                    Seq (Move dest src) c4)
           | Assign dest op args NONE =>
               INR (k,list_insert args (delete dest names),
                    Seq (Assign dest op args NONE) c4)
           | Cut names2 => INR (k,inter names names2,c4)
           | _ => INL (Seq d1 (pMakeSpace x2)))) /\
  (pSpace (Handle ns1 c1 n1 n2 ns2 c2) =
     INL (Handle ns1 (pMakeSpace (pSpace c1)) n1 n2 ns2
                     (pMakeSpace (pSpace c2)))) /\
  (pSpace (If c1 n c2 c3) =
     INL (If (pMakeSpace (pSpace c1)) n (pMakeSpace (pSpace c2))
                                        (pMakeSpace (pSpace c3)))) /\
  (pSpace c = INL c)`;

val pSpaceOpt_def = Define `
  pSpaceOpt c = pMakeSpace (pSpace c)`;

val union_assoc = prove(
  ``!t1 t2 t3. union t1 (union t2 t3) = union (union t1 t2) t3``,
  Induct \\ Cases_on `t2` \\ Cases_on `t3` \\ fs [union_def]);

val pEvalOp_SOME_IMP = prove(
  ``(pEvalOp op x s = SOME (q,r)) ==>
    (pEvalOp op x (s with locals := extra) =
       SOME (q,r with locals := extra))``,
  fs [pEvalOp_def,pEvalOpSpace_def,consume_space_def,bvp_to_bvl_def]
  \\ REPEAT (BasicProvers.CASE_TAC \\ fs []) \\ SRW_TAC [] []
  \\ fs [bvl_to_bvp_def,bvp_state_explode]);

(*
val union_inter_inter = prove(
  ``union (inter t1 x) (inter t2 x) = inter (union t1 t2) x``,
  cheat);
*)

val push_exc_with_locals = prove(
  ``((push_exc env1 env2 (s with locals := xs)) = push_exc env1 env2 s) /\
    ((s with locals := s.locals) = s)``,
  fs [push_exc_def,bvp_state_explode]);

val Seq_Skip = prove(
  ``pEval (Seq c Skip,s) = pEval (c,s)``,
  fs [pEval_def] \\ Cases_on `pEval (c,s)` \\ fs [LET_DEF] \\ SRW_TAC [] []);

val locals_ok_def = Define `
  locals_ok l1 l2 =
    !v x. (lookup v l1 = SOME x) ==> (lookup v l2 = SOME x)`;

val locals_ok_IMP = prove(
  ``locals_ok l1 l2 ==> domain l1 SUBSET domain l2``,
  cheat);

val pEval_pSpaceOpt = prove(
  ``!c s res s2 vars l.
      res <> SOME Error /\ (pEval (c,s) = (res,s2)) /\
      locals_ok s.locals l ==>
      ?w. (pEval (pSpaceOpt c, s with locals := l) =
             (res,if res = NONE then s2 with locals := w
                                else s2)) /\
          locals_ok s2.locals w``,

  SIMP_TAC std_ss [pSpaceOpt_def]
  \\ recInduct pEval_ind \\ REPEAT STRIP_TAC
  \\ fs [pEval_def,pSpace_def,pMakeSpace_def]
  THEN1 (* Skip *)
   (fs [pEval_def] \\ METIS_TAC [])
  THEN1 (* Move *)
   (Cases_on `get_var src s` \\ fs [] \\ SRW_TAC [] []
    \\ fs [get_var_def,lookup_union,set_var_def,locals_ok_def]
    \\ RES_TAC \\ fs []
    \\ Q.EXISTS_TAC `insert dest x l` \\ fs [lookup_insert]
    \\ METIS_TAC [])

  THEN1 (* Assign *)
   (Cases_on `names_opt` \\ fs []
    \\ Cases_on `op_space_reset op` \\ fs [cut_state_opt_def] THEN1
     (Cases_on `get_vars args s` \\ fs [cut_state_opt_def]
      \\ `get_vars args (s with locals := l) =
          get_vars args s` by
       (MATCH_MP_TAC EVERY_get_vars
        \\ fs [EVERY_MEM,locals_ok_def]
        \\ REPEAT STRIP_TAC \\ IMP_RES_TAC get_vars_IMP_domain
        \\ fs [domain_lookup])
      \\ fs [] \\ Cases_on `pEvalOp op x s` \\ fs []
      \\ Cases_on `x'` \\ fs [] \\ SRW_TAC [] []
      \\ IMP_RES_TAC pEvalOp_SOME_IMP \\ fs [set_var_def]
      \\ Q.EXISTS_TAC `insert dest q l`
      \\ fs [set_var_def,locals_ok_def,lookup_insert]
      \\ METIS_TAC [pEvalOp_IMP])

    \\ `cut_state x (s with locals := l) = cut_state x s` by ALL_TAC

      fs [cut_state_def,cut_env_def]
      \\ Cases_on `domain x SUBSET domain s.locals` \\ fs []
      \\ IMP_RES_TAC locals_ok_IMP \\ IMP_RES_TAC SUBSET_TRANS
      \\ fs [bvp_state_explode] \\ cheat

    \\ fs [] \\ POP_ASSUM (K ALL_TAC)
    \\ fs [cut_state_def,cut_env_def]
    \\ Cases_on `domain x SUBSET domain s.locals` \\ fs []
    \\ Q.EXISTS_TAC `s2.locals` \\ fs [locals_ok_def]
    \\ SRW_TAC [] [bvp_state_explode])
  \\ cheat
(*
  THEN1 (* Tick *)
   (Cases_on `s.clock = 0` \\ fs [] \\ SRW_TAC [] []
    \\ fs [dec_clock_def,call_env_def,locals_ok_def] \\ METIS_TAC [])
  THEN1 (* MakeSpace *)
   (fs [cut_state_def,cut_env_def]
    \\ Cases_on `domain names SUBSET domain s.locals` \\ fs []
    \\ `domain names SUBSET domain (union s.locals vars)` by
         fs [SUBSET_DEF,domain_union] \\ fs [LET_DEF]
    \\ SRW_TAC [] [] \\ fs [bvp_state_explode,add_space_def]
    \\ Q.EXISTS_TAC `inter vars names`
    \\ fs [union_inter_inter])
  THEN1 (* Cut *)
   (fs [cut_state_def,cut_env_def]
    \\ Cases_on `domain names SUBSET domain s.locals` \\ fs []
    \\ `domain names SUBSET domain (union s.locals vars)` by
         fs [SUBSET_DEF,domain_union] \\ fs [LET_DEF]
    \\ SRW_TAC [] [] \\ fs [bvp_state_explode,add_space_def]
    \\ Q.EXISTS_TAC `inter vars names`
    \\ fs [union_inter_inter])
  THEN1 (* Raise *)
   (Cases_on `get_var n s` \\ fs [] \\ SRW_TAC [] []
    \\ `jump_exc (s with locals := union s.locals vars) = jump_exc s` by
         fs [jump_exc_def] \\ Cases_on `jump_exc s` \\ fs []
    \\ fs [get_var_def,lookup_union] \\ SRW_TAC [] [])
  THEN1 (* Return *)
   (Cases_on `get_var n s` \\ fs [] \\ SRW_TAC [] []
    \\ `jump_exc (s with locals := union s.locals vars) = jump_exc s` by
         fs [jump_exc_def] \\ Cases_on `jump_exc s` \\ fs []
    \\ fs [get_var_def,lookup_union] \\ SRW_TAC [] [call_env_def])
  THEN1 (* Seq *)
   (fs [LET_DEF] \\ Cases_on `pSpace c2` \\ fs [] THEN1
     (Cases_on `pEval (c1,s)` \\ fs []
      \\ Cases_on `c1` \\ fs [pMakeSpace_def]
      THEN1 (fs [pEval_def])
      \\ Cases_on `q = SOME Error` \\ fs []
      \\ SIMP_TAC std_ss [Once pEval_def] \\ fs [pSpace_def,pMakeSpace_def]
      \\ FIRST_X_ASSUM (STRIP_ASSUME_TAC o Q.SPEC `vars`)
      \\ fs [LET_DEF,Seq_Skip] \\ Cases_on `q` \\ fs [] \\ SRW_TAC [] [])
    \\ PairCases_on `y` \\ fs []
    \\ Cases_on `pEval (c1,s)` \\ fs []
    \\ REVERSE (Cases_on `c1`) \\ fs []
    \\ TRY (fs [pMakeSpace_def,pSpace_def]
      \\ SIMP_TAC std_ss [Once pEval_def,LET_DEF]
      \\ fs [] \\ SRW_TAC [] []
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `vars`) \\ fs []
      \\ Cases_on `q = SOME Error` \\ fs [] \\ REPEAT STRIP_TAC
      \\ fs [] \\ Cases_on `q` \\ fs [] \\ SRW_TAC [] [] \\ NO_TAC)
    \\ TRY (fs [pEval_def] \\ NO_TAC)
    THEN1 (* Cut *) cheat
    THEN1 (* MakeSpace *) cheat
    THEN1 (* Seq *)
     (fs [pMakeSpace_def]
      \\ SIMP_TAC std_ss [Once pEval_def,LET_DEF]
      \\ fs [] \\ SRW_TAC [] []
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `vars`) \\ fs []
      \\ Cases_on `q = SOME Error` \\ fs [] \\ REPEAT STRIP_TAC
      \\ fs [] \\ Cases_on `q` \\ fs [] \\ SRW_TAC [] [])
    THEN1 (* Assign *) cheat
    THEN1 (* Move *) cheat)
  THEN1 (* Handle *)
   (Cases_on `cut_env ns1 s.locals` \\ fs []
    \\ Cases_on `cut_env ns2 s.locals` \\ fs []
    \\ `cut_env ns1 (union s.locals vars) = SOME x` by cheat
    \\ `cut_env ns2 (union s.locals vars) = SOME x'` by cheat
    \\ fs [] \\ `push_exc x x' (s with locals := union s.locals vars) =
                 push_exc x x' s` by fs [push_exc_def] \\ fs []
    \\ Cases_on `pEval (c1,push_exc x x' s)` \\ fs []
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `LN`) \\ fs [union_LN]
    \\ Cases_on `q` \\ fs [] \\ REPEAT STRIP_TAC
    \\ fs [push_exc_with_locals] THEN1
     (Cases_on `lookup v r.locals`
      \\ fs [get_var_def,lookup_union]
      \\ Cases_on `pop_exc r` \\ fs [] \\ SRW_TAC [] []
      \\ fs [pop_exc_def,set_var_def]
      \\ ONCE_REWRITE_TAC [insert_union]
      \\ SIMP_TAC std_ss [GSYM union_assoc]
      \\ Q.EXISTS_TAC `LN` \\ fs [union_LN])
    \\ Cases_on `x''` \\ fs [push_exc_with_locals]
    \\ SRW_TAC [] [] \\ fs []
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `LN`) \\ fs [union_LN]
    \\ fs [push_exc_with_locals])
  THEN1 (* If *)
   (Cases_on `pEval (g,s)` \\ fs []
    \\ REVERSE (Cases_on `q`) \\ fs []
    \\ SRW_TAC [] [] \\ fs []
    \\ FIRST_X_ASSUM (STRIP_ASSUME_TAC o Q.SPEC `vars`) \\ fs []
    \\ Cases_on `get_var n r` \\ fs []
    \\ fs [get_var_def,lookup_union]
    \\ Cases_on `x = bool_to_val T` \\ fs []
    \\ Cases_on `x = bool_to_val F` \\ fs [])
  THEN1 (* Call *)
   (Cases_on `s.clock = 0` \\ fs [] \\ SRW_TAC [] []
    THEN1 (fs [dec_clock_def,call_env_def] \\ METIS_TAC [])
    \\ Cases_on `get_vars args s` \\ fs []
    \\ `get_vars args (s with locals := union s.locals vars) =
        get_vars args s` by ALL_TAC THEN1
     (MATCH_MP_TAC EVERY_get_vars
      \\ fs [EVERY_MEM,lookup_inter_alt,lookup_union]
      \\ REPEAT STRIP_TAC \\ IMP_RES_TAC get_vars_IMP_domain
      \\ fs [domain_lookup])
    \\ Cases_on `find_code dest x s.code` \\ fs []
    \\ Cases_on `x'` \\ fs []
    \\ Cases_on `ret` \\ fs [] THEN1
     (fs [call_env_def,dec_clock_def]
      \\ REPEAT (BasicProvers.FULL_CASE_TAC \\ fs []))
    \\ Cases_on `x'` \\ fs [cut_env_def]
    \\ Cases_on `domain r' SUBSET domain s.locals` \\ fs []
    \\ `domain r' SUBSET domain (union s.locals vars)` by
         fs [SUBSET_DEF,domain_union] \\ fs []
    \\ `inter (union s.locals vars) r' = inter s.locals r'` by cheat \\ fs []
    \\ `call_env q (push_env (inter s.locals r')
          (dec_clock (s with locals := union s.locals vars))) =
        call_env q (push_env (inter s.locals r') (dec_clock s))` by
         (fs [call_env_def,dec_clock_def,push_env_def] \\ NO_TAC) \\ fs []
    \\ Cases_on `res` \\ fs [] \\ Q.EXISTS_TAC `LN`
    \\ fs [union_LN,bvp_state_explode])
*)
);

val pSpaceOpt = store_thm("pSpaceOpt_correct",
  ``!c s.
      FST (pEval (c,s)) <> NONE /\
      FST (pEval (c,s)) <> SOME Error ==>
      (pEval (pSpaceOpt c, s) = pEval (c,s))``,
  REPEAT STRIP_TAC \\ Cases_on `pEval (c,s)` \\ fs []
  \\ MP_TAC (Q.SPECL [`c`,`s`] pEval_pSpaceOpt)
  \\ fs [] \\ REPEAT STRIP_TAC
  \\ POP_ASSUM (MP_TAC o Q.SPECL [`LN`]) \\ fs [union_LN]
  \\ `(s with locals := s.locals) = s` by fs [bvp_state_explode]
  \\ fs [] \\ REPEAT STRIP_TAC \\ fs []);

val _ = export_theory();
