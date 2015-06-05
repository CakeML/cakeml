open preamble
     db_varsTheory
     closSemTheory closPropsTheory
     clos_freeTheory clos_freeProofTheory
     clos_annotateTheory;

val _ = new_theory"clos_annotateProof";

val EVERY2_EL = LIST_REL_EL_EQN |> SPEC_ALL |> EQ_IMP_RULE |> fst
                |> UNDISCH |> CONJUNCT2 |> DISCH_ALL;

(* TODO: move, or delete *)
val fv_EL_IMP = prove(
  ``!fns n index.
      fv n [EL index fns] /\ index < LENGTH fns ==>
      fv n fns``,
  Induct \\ fs [] \\ REPEAT STRIP_TAC
  \\ Cases_on `index` \\ fs [EL]
  \\ Cases_on `fns` \\ fs [fv_def] \\ RES_TAC \\ fs []);
(* -- *)

(* value relation *)

val _ = overload_on("fv_set",``λx y. fv y x``);

val (v_rel_rules,v_rel_ind,v_rel_cases) = Hol_reln `
  (v_rel (Number j) (Number j))
  /\
  (EVERY2 v_rel (xs:closSem$v list) (ys:closSem$v list) ==>
   v_rel (Block t xs) (Block t ys))
  /\
  (v_rel (RefPtr r1) (RefPtr r1))
  /\
  ((shift (FST (free [c])) m num_args i = [c']) /\
   (!n. fv_set [c] n /\ num_args <= n ==>
        env_ok m 0 i env env' (n - num_args)) /\
   (LENGTH env = m) /\ EVERY2 v_rel vals vals' ==>
   v_rel (Closure p vals env num_args c) (Closure p vals' env' num_args c'))
  /\
  (EVERY2 ( \ (num_args,c1) (num_args',c1').
     ?m i.
       (num_args' = num_args) /\
       (shift (FST (free [c1])) m (LENGTH cs + num_args) i = [c1']) /\
       (!n. fv_set [c1] n /\ num_args + LENGTH cs <= n ==>
          env_ok m 0 i env env' (n - (num_args + LENGTH cs))) /\
       (LENGTH env = m)) cs cs' /\
   EVERY2 v_rel vals vals' /\ index < LENGTH cs ==>
   v_rel (Recclosure p vals env cs index) (Recclosure p vals' env' cs' index))
  /\
  (l + m <= n ==>
   env_ok m l i (env2:closSem$v list) (env2':closSem$v list) n)
  /\
  (n < l /\ v_rel (EL n env2) (EL n env2') /\
   n < LENGTH env2 /\ n < LENGTH env2' ==>
   env_ok m l i env2 env2' n)
  /\
  (l <= n /\ n < l + m /\
   n < l + m /\ (lookup (n - l) i = SOME v) /\
   n < LENGTH env2 /\
   l + v < LENGTH env2' /\
   v_rel (EL n env2) (EL (l + v) env2') ==>
   env_ok m l i env2 env2' n)`

val v_rel_simp = let
  val f = SIMP_CONV (srw_ss()) [Once v_rel_cases]
  in map f [``v_rel (Number x) y``,
            ``v_rel (Block n l) y``,
            ``v_rel (RefPtr x) y``,
            ``v_rel (Closure n l v x w) y``,
            ``v_rel (Recclosure x1 x2 x3 x4 x5) y``,
            ``v_rel y (Number x)``,
            ``v_rel y (Block n l)``,
            ``v_rel y (RefPtr x)``,
            ``v_rel y (Closure n l v x w)``,
            ``v_rel y (Recclosure x1 x2 x3 x4 x5)``] |> LIST_CONJ end
  |> curry save_thm "v_rel_simp";

val v_rel_Boolv = store_thm("v_rel_Boolv[simp]",
  ``(v_rel x (Boolv b) ⇔ (x = Boolv b)) ∧
    (v_rel (Boolv b) x ⇔ (x = Boolv b))``,
  Cases_on`b`>>EVAL_TAC>>ntac 2(simp[Once v_rel_cases]))

val v_rel_Unit = store_thm("v_rel_Unit[simp]",
  ``(v_rel x Unit ⇔ (x = Unit)) ∧
    (v_rel Unit x ⇔ (x = Unit))``,
  EVAL_TAC>>ntac 2(simp[Once v_rel_cases]))

val env_ok_def = v_rel_cases |> CONJUNCT2

val env_ok_EXTEND = prove(
  ``EVERY2 v_rel env1 env2 /\ (l1 = LENGTH env1) /\
    (l1 <= n ==> env_ok m l i env1' env2' (n - l1)) ==>
    env_ok m (l + l1) i (env1 ++ env1') (env2 ++ env2') n``,
  SRW_TAC [] [] \\ SIMP_TAC std_ss [env_ok_def]
  \\ Cases_on `n < LENGTH env1` \\ fs [] THEN1
   (DISJ2_TAC \\ DISJ1_TAC \\ REPEAT STRIP_TAC
    \\ IMP_RES_TAC EVERY2_LENGTH
    \\ fs [rich_listTheory.EL_APPEND1]
    \\ IMP_RES_TAC EVERY2_EL \\ fs [] \\ DECIDE_TAC)
  \\ fs [NOT_LESS]
  \\ fs [env_ok_def]
  THEN1 (DISJ1_TAC \\ DECIDE_TAC)
  THEN1
   (DISJ2_TAC \\ DISJ1_TAC
    \\ IMP_RES_TAC EVERY2_LENGTH
    \\ fs [rich_listTheory.EL_APPEND2]
    \\ DECIDE_TAC)
  \\ DISJ2_TAC \\ DISJ2_TAC \\ Q.EXISTS_TAC `v` \\ fs []
  \\ IMP_RES_TAC EVERY2_LENGTH
  \\ fs [rich_listTheory.EL_APPEND2]
  \\ `n - (l + LENGTH env2) = n - LENGTH env2 - l` by DECIDE_TAC \\ fs []
  \\ `LENGTH env2 <= l + LENGTH env2 + v` by DECIDE_TAC
  \\ fs [rich_listTheory.EL_APPEND2]
  \\ `l + LENGTH env2 + v - LENGTH env2 = l + v` by DECIDE_TAC \\ fs []
  \\ DECIDE_TAC);

val env_ok_cons = env_ok_EXTEND
  |> Q.INST [`env1`|->`[v1]`,`env2`|->`[v2]`] |> Q.GEN `l1`
  |> SIMP_RULE (srw_ss()) []

val env_ok_1 = env_ok_EXTEND
  |> Q.INST [`env1`|->`[v1]`,`env2`|->`[v2]`,`l`|->`0`] |> Q.GEN `l1`
  |> SIMP_RULE (srw_ss()) []

val env_ok_some = env_ok_EXTEND
  |> DISCH ``l + LENGTH (env1:closSem$v list) = k``
  |> Q.GEN `l1` |> SIMP_RULE std_ss []
  |> REWRITE_RULE [AND_IMP_INTRO] |> GEN_ALL

val env_ok_append = env_ok_EXTEND
  |> GSYM |> Q.INST [`l`|->`0`]
  |> SIMP_RULE (srw_ss()) []

val state_rel_def = Define `
  state_rel (s:closSem$state) (t:closSem$state) <=>
    (s.clock = t.clock) /\
    (s.io = t.io) /\
    ~s.restrict_envs /\ t.restrict_envs /\
    EVERY2 (OPTREL v_rel) s.globals t.globals /\
    (FDOM s.refs = FDOM t.refs) /\
    (!n r1.
      (FLOOKUP s.refs n = SOME r1) ==>
      ?r2. (FLOOKUP t.refs n = SOME r2) /\ ref_rel v_rel r1 r2) /\
    (!name arity c.
      (FLOOKUP s.code name = SOME (arity,c)) ==>
      ?c2.
        (shift (FST (free [c])) 0 arity LN = [c2]) /\
        (FLOOKUP t.code name = SOME (arity,c2)))`

(* semantic functions respect relation *)

val list_to_v = prove(
  ``!l' l. LIST_REL v_rel l' l ==>
           v_rel (list_to_v l') (list_to_v l)``,
  Induct \\ Cases_on `l` \\ fs [list_to_v_def,v_rel_simp]);

val v_to_list = prove(
  ``!h h'.
      v_rel h h' ==>
      (v_to_list h = NONE /\
       v_to_list h' = NONE) \/
      ?x x'. (v_to_list h = SOME x) /\
             (v_to_list h' = SOME x') /\
             EVERY2 v_rel x x'``,
  HO_MATCH_MP_TAC v_to_list_ind
  \\ fs [v_rel_simp]
  \\ fs [v_to_list_def]
  \\ REPEAT STRIP_TAC \\ SRW_TAC [] []
  \\ fs [v_to_list_def]
  \\ Cases_on `v_to_list h'` \\ fs []
  \\ Cases_on `v_to_list y'` \\ fs []
  \\ CCONTR_TAC \\ RES_TAC \\ fs []
  \\ RES_TAC \\ fs [] \\ SRW_TAC [] [] \\ fs []);

val do_eq = prove(
  ``(!h1 u1 h2 u2.
       v_rel h1 h2 /\ v_rel u1 u2 ==>
       (do_eq h1 u1 = do_eq h2 u2)) /\
    (!h1 u1 h2 u2.
      EVERY2 v_rel h1 h2 /\ EVERY2 v_rel u1 u2 ==>
      (do_eq_list h1 u1 = do_eq_list h2 u2))``,
  HO_MATCH_MP_TAC do_eq_ind
  \\ REPEAT STRIP_TAC \\ fs []
  \\ ONCE_REWRITE_TAC [do_eq_def]
  \\ BasicProvers.EVERY_CASE_TAC \\ fs [v_rel_simp]
  \\ RES_TAC \\ SRW_TAC [] []
  \\ IMP_RES_TAC EVERY2_LENGTH \\ fs []
  \\ Q.PAT_ASSUM `xx = do_eq y y'` (ASSUME_TAC o GSYM)
  \\ fs []) |> CONJUNCT1 ;

val do_app_IMP_case = prove(
  ``(do_app UpdateByte xs s1 = Rval x) ==>
    ?x1 x2 x3. xs = [RefPtr x1; Number x2; Number x3]``,
  fs [do_app_def]
  \\ BasicProvers.EVERY_CASE_TAC \\ fs []);

val do_app_thm = prove(
  ``state_rel s1 t1 /\ EVERY2 v_rel xs ys /\
    (do_app op xs s1 = Rval (v,s2)) ==>
    ?w t2. (do_app op ys t1 = Rval (w,t2)) /\
           v_rel v w /\ state_rel s2 t2``,
  REVERSE (Cases_on `op`) \\ rpt STRIP_TAC
  THEN1 (* GreaterEq *)
   (fs [do_app_def] \\ BasicProvers.EVERY_CASE_TAC \\ fs []
    \\ SRW_TAC [] [] \\ fs [v_rel_simp] \\ SRW_TAC [] [])
  THEN1 (* Greater *)
   (fs [do_app_def] \\ BasicProvers.EVERY_CASE_TAC \\ fs []
    \\ SRW_TAC [] [] \\ fs [v_rel_simp] \\ SRW_TAC [] [])
  THEN1 (* LessEq *)
   (fs [do_app_def] \\ BasicProvers.EVERY_CASE_TAC \\ fs []
    \\ SRW_TAC [] [] \\ fs [v_rel_simp] \\ SRW_TAC [] [])
  THEN1 (* Less *)
   (fs [do_app_def] \\ BasicProvers.EVERY_CASE_TAC \\ fs []
    \\ SRW_TAC [] [] \\ fs [v_rel_simp] \\ SRW_TAC [] [])
  THEN1 (* Mod *)
   (fs [do_app_def] \\ BasicProvers.EVERY_CASE_TAC \\ fs []
    \\ SRW_TAC [] [] \\ fs [v_rel_simp] \\ SRW_TAC [] [])
  THEN1 (* Div *)
   (fs [do_app_def] \\ BasicProvers.EVERY_CASE_TAC \\ fs []
    \\ SRW_TAC [] [] \\ fs [v_rel_simp] \\ SRW_TAC [] [])
  THEN1 (* Mult *)
   (fs [do_app_def] \\ BasicProvers.EVERY_CASE_TAC \\ fs []
    \\ SRW_TAC [] [] \\ fs [v_rel_simp] \\ SRW_TAC [] [])
  THEN1 (* Sub *)
   (fs [do_app_def] \\ BasicProvers.EVERY_CASE_TAC \\ fs []
    \\ SRW_TAC [] [] \\ fs [v_rel_simp] \\ SRW_TAC [] [])
  THEN1 (* Add *)
   (fs [do_app_def] \\ BasicProvers.EVERY_CASE_TAC \\ fs []
    \\ SRW_TAC [] [] \\ fs [v_rel_simp] \\ SRW_TAC [] [])
  THEN1 (* Const *)
   (fs [do_app_def] \\ BasicProvers.EVERY_CASE_TAC
    \\ SRW_TAC [] [v_rel_simp] \\ fs [] \\ fs[v_rel_simp])
  THEN1 (* Equal *)
   (fs [do_app_def] \\ BasicProvers.EVERY_CASE_TAC \\ fs []
    \\ fs [v_rel_simp] \\ SRW_TAC [] []
    \\ IMP_RES_TAC do_eq \\ fs []
    \\ SRW_TAC [] [] \\ fs []
    \\ TRY (Cases_on `b`) \\ EVAL_TAC \\ fs [v_rel_simp])
  THEN1 (* FFI *)
   (fs [do_app_def] \\ BasicProvers.EVERY_CASE_TAC \\ fs []
    \\ fs [v_rel_simp] \\ SRW_TAC [] []
    \\ rfs[state_rel_def]
    \\ res_tac >> fs[FLOOKUP_UPDATE] >> rw[] >> fs[] >>
    fs[FLOOKUP_DEF] >> rfs[])
  THEN1 (* Label *)
   (fs [do_app_def] \\ BasicProvers.EVERY_CASE_TAC \\ fs [] \\
    rw[] >> rw[])
  THEN1 (* Update *)
   (fs [do_app_def] \\ BasicProvers.EVERY_CASE_TAC \\ fs []
    \\ fs [v_rel_simp] \\ SRW_TAC [] []
    \\ fs [state_rel_def,FLOOKUP_DEF]
    \\ rfs [] \\ fs []
    \\ TRY (Q.PAT_ASSUM `!x. bb ==> bbb` IMP_RES_TAC
            \\ rfs [] \\ POP_ASSUM MP_TAC
            \\ fs []
            \\ REPEAT STRIP_TAC
            \\ IMP_RES_TAC EVERY2_LENGTH \\ fs [] \\ NO_TAC)
    \\ STRIP_TAC \\ Cases_on `n' = n` \\ fs []
    \\ fs [FAPPLY_FUPDATE_THM] \\ fs []
    \\ MATCH_MP_TAC EVERY2_LUPDATE_same \\ fs [] >>
    first_x_assum(fn th => first_x_assum(mp_tac o MATCH_MP th)) >>
    simp[])
  THEN1 (* Deref *)
   (fs [do_app_def] \\ BasicProvers.EVERY_CASE_TAC \\ fs []
    \\ fs [v_rel_simp] \\ SRW_TAC [] []
    \\ fs [state_rel_def,FLOOKUP_DEF]
    \\ rfs [] \\ fs []
    \\ TRY (Q.PAT_ASSUM `!x. bb ==> bbb` IMP_RES_TAC
            \\ rfs [] \\ POP_ASSUM MP_TAC
            \\ fs []
            \\ REPEAT STRIP_TAC
            \\ IMP_RES_TAC EVERY2_LENGTH \\ fs [] \\ NO_TAC)
    \\ Q.PAT_ASSUM `!x. bb ==> bbb` IMP_RES_TAC
    \\ rfs [] \\ POP_ASSUM MP_TAC
    \\ fs [] \\ REPEAT STRIP_TAC
    \\ IMP_RES_TAC EVERY2_EL
    \\ IMP_RES_TAC EVERY2_LENGTH \\ fs []
    \\ `Num i < LENGTH l` by intLib.COOPER_TAC
    \\ RES_TAC >>
    fs[LIST_REL_EL_EQN] >> METIS_TAC[])
  THEN1 (* Ref *)
   (fs [do_app_def] \\ BasicProvers.EVERY_CASE_TAC \\ fs []
    \\ fs [v_rel_simp,LET_DEF] \\ SRW_TAC [] []
    \\ fs [state_rel_def]
    \\ fs [FLOOKUP_DEF,FAPPLY_FUPDATE_THM] \\ STRIP_TAC
    \\ Cases_on `n = (LEAST ptr. ptr NOTIN FDOM t1.refs)` \\ fs []
    \\ fs [])
  THEN1 (* IsBlock *)
   (fs [do_app_def] \\ BasicProvers.EVERY_CASE_TAC \\ fs []
    \\ fs [v_rel_simp] \\ SRW_TAC [] [] \\ fs[v_rel_simp])
  THEN1 (* TagEq *)
   (fs [do_app_def] \\ BasicProvers.EVERY_CASE_TAC \\ fs []
    \\ fs [v_rel_simp] \\ SRW_TAC [] [] \\ fs[v_rel_simp]
    \\ METIS_TAC[LIST_REL_LENGTH])
  THEN1 (* ToList *)
   (fs [do_app_def] \\ BasicProvers.EVERY_CASE_TAC
    \\ fs [v_rel_simp] \\ rw[] \\ SRW_TAC [] [list_to_v])
  THEN1 (* FromList *)
   (fs [do_app_def] \\ BasicProvers.EVERY_CASE_TAC
    \\ fs [v_rel_simp] \\ SRW_TAC [] []
    \\ IMP_RES_TAC v_to_list \\ fs []
    \\ SRW_TAC [] [])
  THEN1 (* UpdateByte *)
   (rpt strip_tac >>IMP_RES_TAC do_app_IMP_case
    \\ fs [v_rel_simp] \\ SRW_TAC [] []
    \\ fs [do_app_def] \\ BasicProvers.EVERY_CASE_TAC
    \\ fs [] \\ SRW_TAC [] []
    \\ fs [state_rel_def] \\ RES_TAC \\ fs []
    \\ SRW_TAC [] [] \\ fs []
    \\ fs [v_rel_simp]
    \\ fs [FLOOKUP_DEF,FAPPLY_FUPDATE_THM]
    \\ SRW_TAC [] [] \\ fs []
    \\ RES_TAC \\ fs [] \\ rfs [])
  THEN1 (* DerefByte *)
   (fs [do_app_def] \\ BasicProvers.EVERY_CASE_TAC \\ fs []
    \\ fs [v_rel_simp,LET_DEF] \\ SRW_TAC [] []
    \\ fs [state_rel_def] \\ RES_TAC \\ fs []
    \\ SRW_TAC [] [] \\ fs []
    \\ IMP_RES_TAC EVERY2_LENGTH \\ fs [])
  THEN1 (* RefArray *)
   (fs [do_app_def] \\ BasicProvers.EVERY_CASE_TAC \\ fs []
    \\ fs [v_rel_simp,LET_DEF] \\ SRW_TAC [] []
    \\ fs [state_rel_def]
    \\ fs [FLOOKUP_DEF,FAPPLY_FUPDATE_THM] \\ STRIP_TAC
    \\ Cases_on `n = (LEAST ptr. ptr NOTIN FDOM t1.refs)` \\ fs []
    \\ fs [LIST_REL_REPLICATE_same])
  THEN1 (* RefByte *)
   (fs [do_app_def] \\ BasicProvers.EVERY_CASE_TAC \\ fs []
    \\ fs [v_rel_simp,LET_DEF] \\ SRW_TAC [] []
    \\ fs [state_rel_def]
    \\ fs [FLOOKUP_DEF,FAPPLY_FUPDATE_THM] \\ STRIP_TAC
    \\ Cases_on `n = (LEAST ptr. ptr NOTIN FDOM t1.refs)` \\ fs []
    \\ fs [])
  THEN1 (* LengthByte *)
   (fs [do_app_def] \\ BasicProvers.EVERY_CASE_TAC
    \\ fs [v_rel_simp] \\ SRW_TAC [] []
    \\ fs [state_rel_def] \\ RES_TAC \\ fs []
    \\ SRW_TAC [] [] \\ fs []
    \\ IMP_RES_TAC EVERY2_LENGTH \\ fs [])
  THEN1 (* Length *)
   (fs [do_app_def] \\ BasicProvers.EVERY_CASE_TAC
    \\ fs [v_rel_simp] \\ SRW_TAC [] []
    \\ fs [state_rel_def] \\ RES_TAC \\ fs []
    \\ SRW_TAC [] [] \\ fs []
    \\ IMP_RES_TAC EVERY2_LENGTH \\ fs [])
  THEN1 (* LengthBlock *)
   (fs [do_app_def] \\ BasicProvers.EVERY_CASE_TAC
    \\ SRW_TAC [] [v_rel_simp] \\ fs []
    \\ fs [v_rel_simp] \\ fs [] \\ SRW_TAC [] []
    \\ IMP_RES_TAC EVERY2_LENGTH \\ fs [])
  THEN1 (* El *)
   (fs [do_app_def] \\ BasicProvers.EVERY_CASE_TAC
    \\ SRW_TAC [] [v_rel_simp] \\ fs []
    \\ fs [v_rel_simp] \\ fs [] \\ SRW_TAC [] []
    \\ IMP_RES_TAC EVERY2_EL
    \\ IMP_RES_TAC EVERY2_LENGTH \\ fs [])
  THEN1 (* Cons *)
   (fs [do_app_def] \\ BasicProvers.EVERY_CASE_TAC
    \\ SRW_TAC [] [v_rel_simp] \\ fs [])
  THEN1 (* AllocGlobal *)
   (fs [do_app_def] \\ BasicProvers.EVERY_CASE_TAC
    \\ SRW_TAC [] [v_rel_simp] \\ fs []
    \\ fs [state_rel_def,get_global_def] \\ RES_TAC
    \\ fs [quotient_optionTheory.OPTION_REL_def])
  THEN1 (* SetGlobal *)
   (fs [do_app_def] \\ BasicProvers.EVERY_CASE_TAC
    \\ SRW_TAC [] [v_rel_simp] \\ fs []
    \\ fs [state_rel_def,get_global_def] \\ RES_TAC
    \\ IMP_RES_TAC EVERY2_LENGTH \\ fs []
    \\ IMP_RES_TAC EVERY2_EL
    \\ rfs [] \\ POP_ASSUM IMP_RES_TAC
    \\ rfs [quotient_optionTheory.OPTION_REL_def]
    \\ MATCH_MP_TAC EVERY2_LUPDATE_same
    \\ fs [quotient_optionTheory.OPTION_REL_def])
  THEN1 (* Global *)
   (fs [do_app_def] \\ BasicProvers.EVERY_CASE_TAC
    \\ SRW_TAC [] [v_rel_simp] \\ fs []
    \\ fs [state_rel_def,get_global_def] \\ RES_TAC
    \\ IMP_RES_TAC EVERY2_LENGTH \\ fs []
    \\ IMP_RES_TAC EVERY2_EL
    \\ rfs [] \\ POP_ASSUM IMP_RES_TAC
    \\ rfs [quotient_optionTheory.OPTION_REL_def]));

val do_app_err_thm = Q.prove(
  `state_rel s1 t1 /\ EVERY2 v_rel xs ys /\
   do_app op xs s1 = Rerr err /\ (err <> Rabort Rtype_error) ==>
     ?w. (do_app op ys t1 = Rerr w) /\
          exc_rel v_rel err w`,
  rw[] >>
  imp_res_tac do_app_err >> fs[] >>
  Cases_on`op`>>fs[do_app_def]
  >- (every_case_tac >> fs[])
  >- (every_case_tac >> fs[])
  >- (every_case_tac >> fs[])
  >- (Cases_on`xs`>>fs[]>>every_case_tac >> fs[])
  >- (Cases_on`xs`>>fs[]>>every_case_tac >> fs[])
  >- (Cases_on`xs`>>fs[]>>every_case_tac >> fs[])
  >- (Cases_on`xs`>>fs[]>>every_case_tac >> fs[])
  >- (Cases_on`xs`>>fs[LET_THM]>>every_case_tac >> fs[])
  >- (Cases_on`xs`>>fs[LET_THM]>>every_case_tac >> fs[])
  >- (Cases_on`xs`>>fs[LET_THM]>>
      Cases_on`t`>>fs[]>>
      Cases_on`h'`>>fs[]>>
      Cases_on`h`>>fs[]>>
      Cases_on`t'`>>fs[]>>
      every_case_tac >> fs[])
  >- (Cases_on`xs`>>fs[LET_THM]>>
      Cases_on`t`>>fs[]>>
      Cases_on`t'`>>fs[]>>
      Cases_on`h''`>>fs[]>>
      Cases_on`h'`>>fs[]>>
      Cases_on`h`>>fs[]>>
      Cases_on`t`>>fs[]>>
      every_case_tac >> fs[])
  >- (Cases_on`xs`>>fs[]>>every_case_tac >> fs[])
  >- (Cases_on`xs`>>fs[]>>every_case_tac >> fs[])
  >- (Cases_on`xs`>>fs[]>>every_case_tac >> fs[])
  >- (Cases_on`xs`>>fs[]>>every_case_tac >> fs[])
  >- (fs[LET_THM]>>every_case_tac >> fs[])
  >- (Cases_on`xs`>>fs[]>>
      Cases_on`t`>>fs[]>>
      Cases_on`h'`>>fs[]>>
      Cases_on`h`>>fs[]>>
      Cases_on`t'`>>fs[]>>
      every_case_tac >> fs[])
  >- (Cases_on`xs`>>fs[]>>
      Cases_on`t`>>fs[]>>
      Cases_on`t'`>>fs[]>>
      Cases_on`h'`>>fs[]>>
      Cases_on`h`>>fs[]>>
      Cases_on`t`>>fs[]>>
      every_case_tac >> fs[])
  >- (Cases_on`xs`>>fs[]>>every_case_tac >> fs[v_rel_simp] >>
      rw[] >> fs[state_rel_def] >> res_tac >> fs[] >>
      rw[] >> rfs[])
  >- (Cases_on`xs`>>fs[]>>every_case_tac >> fs[])
  >- (Cases_on`xs`>>fs[]>>every_case_tac >> fs[])
  >- (Cases_on`xs`>>fs[]>>
      Cases_on`t`>>fs[]>>
      Cases_on`h'`>>fs[]>>
      Cases_on`h`>>fs[]>>
      Cases_on`t'`>>fs[])
  >- (Cases_on`xs`>>fs[]>>
      Cases_on`t`>>fs[]>>
      Cases_on`h'`>>fs[]>>
      Cases_on`h`>>fs[]>>
      Cases_on`t'`>>fs[])
  >- (Cases_on`xs`>>fs[]>>
      Cases_on`t`>>fs[]>>
      Cases_on`h'`>>fs[]>>
      Cases_on`h`>>fs[]>>
      Cases_on`t'`>>fs[])
  >- (Cases_on`xs`>>fs[]>>
      Cases_on`t`>>fs[]>>
      Cases_on`h'`>>fs[]>>
      Cases_on`h`>>fs[]>>
      Cases_on`t'`>>fs[]>>
      every_case_tac >>fs[])
  >- (Cases_on`xs`>>fs[]>>
      Cases_on`t`>>fs[]>>
      Cases_on`h'`>>fs[]>>
      Cases_on`h`>>fs[]>>
      Cases_on`t'`>>fs[]>>
      every_case_tac >>fs[])
  >- (Cases_on`xs`>>fs[]>>
      Cases_on`t`>>fs[]>>
      Cases_on`h'`>>fs[]>>
      Cases_on`h`>>fs[]>>
      Cases_on`t'`>>fs[]>>
      every_case_tac >>fs[])
  >- (Cases_on`xs`>>fs[]>>
      Cases_on`t`>>fs[]>>
      Cases_on`h'`>>fs[]>>
      Cases_on`h`>>fs[]>>
      Cases_on`t'`>>fs[]>>
      every_case_tac >>fs[])
  >- (Cases_on`xs`>>fs[]>>
      Cases_on`t`>>fs[]>>
      Cases_on`h'`>>fs[]>>
      Cases_on`h`>>fs[]>>
      Cases_on`t'`>>fs[]>>
      every_case_tac >>fs[])
  >- (Cases_on`xs`>>fs[]>>
      Cases_on`t`>>fs[]>>
      Cases_on`h'`>>fs[]>>
      Cases_on`h`>>fs[]>>
      Cases_on`t'`>>fs[]>>
      every_case_tac >>fs[]));

(* compiler correctness *)

val lookup_EL_new_env = prove(
  ``!y n k. n < LENGTH y /\ ALL_DISTINCT y ==>
            (lookup (EL n y) (new_env k y) = SOME (k + n))``,
  Induct \\ fs [] \\ Cases_on `n` \\ fs [new_env_def,lookup_insert]
  \\ SRW_TAC [] [ADD1,AC ADD_COMM ADD_ASSOC]
  \\ fs [MEM_EL] \\ METIS_TAC []);

val env_ok_new_env = prove(
  ``env_ok m l i env env2 k /\ MEM k live /\ ALL_DISTINCT live /\
    (lookup_vars (MAP (get_var m l i) (FILTER (\n. n < m + l) live)) env2 =
      SOME x) ==>
    env_ok (m + l) 0 (new_env 0 (FILTER (\n. n < m + l) live)) env x k``,
  REPEAT STRIP_TAC
  \\ Q.ABBREV_TAC `y = FILTER (\n. n < m + l) live`
  \\ `ALL_DISTINCT y` by
       (UNABBREV_ALL_TAC \\ MATCH_MP_TAC FILTER_ALL_DISTINCT \\ fs [])
  \\ Cases_on `~(k < m + l)` THEN1 (fs [env_ok_def,NOT_LESS] \\ DECIDE_TAC)
  \\ fs []
  \\ `MEM k y` by (UNABBREV_ALL_TAC \\ fs [MEM_FILTER])
  \\ POP_ASSUM MP_TAC
  \\ simp [MEM_EL] \\ STRIP_TAC
  \\ POP_ASSUM (ASSUME_TAC o GSYM)
  \\ Q.PAT_ASSUM `MEM k live` (K ALL_TAC)
  \\ Q.PAT_ASSUM `Abbrev vvv` (K ALL_TAC)
  \\ `(EL n (MAP (get_var m l i) y) = get_var m l i k) /\
      n < LENGTH (MAP (get_var m l i) y)` by fs [EL_MAP]
  \\ Q.ABBREV_TAC `ys = (MAP (get_var m l i) y)`
  \\ MP_TAC lookup_vars_MEM \\ fs [] \\ STRIP_TAC
  \\ `v_rel (EL k env) (EL (get_var m l i k) env2)` by
   (fs [env_ok_def] THEN1 (`F` by DECIDE_TAC) \\ fs [get_var_def]
    \\ `~(k < l)` by DECIDE_TAC \\ fs [tlookup_def])
  \\ Q.PAT_ASSUM `EL n x = yy` (ASSUME_TAC o GSYM) \\ fs []
  \\ fs [env_ok_def] \\ DISJ2_TAC
  \\ TRY (`k < l + m` by DECIDE_TAC) \\ fs []
  \\ SRW_TAC [] [] \\ fs [lookup_EL_new_env]
  \\ IMP_RES_TAC lookup_vars_SOME \\ fs []);

val EL_shift_free = prove(
  ``!fns index.
     index < LENGTH fns ==>
     ([EL index (shift (FST (free fns)) l m i)] =
      (shift (FST (free [EL index fns])) l m i))``,
  Induct \\ fs [] \\ REPEAT STRIP_TAC
  \\ ONCE_REWRITE_TAC [free_CONS]
  \\ SIMP_TAC std_ss [Once shift_CONS]
  \\ Cases_on `index` \\ fs []
  \\ fs [LET_DEF,free_def]
  \\ REPEAT (AP_TERM_TAC ORELSE AP_THM_TAC)
  \\ fs [SING_HD,LENGTH_FST_free]);

val shift_correct = prove(
  ``(!xs env s1 env' t1 res s2 m l i.
      (evaluate (xs,env,s1) = (res,s2)) /\ res <> Rerr (Rabort Rtype_error) /\
      (LENGTH env = m + l) /\
      fv_set xs SUBSET env_ok m l i env env' /\
      state_rel s1 t1 ==>
      ?res' t2.
         (evaluate (shift (FST (free xs)) m l i,env',t1) = (res',t2)) /\
         result_rel (LIST_REL v_rel) v_rel res res' /\
         state_rel s2 t2) /\
    (!loc_opt f args s1 res s2 f' args' s1'.
      (evaluate_app loc_opt f args s1 = (res,s2)) /\
      v_rel f f' /\ EVERY2 v_rel args args' /\
      state_rel s1 s1' /\ res <> Rerr (Rabort Rtype_error) ==>
      ?res' s2'.
        (evaluate_app loc_opt f' args' s1' = (res',s2')) /\
        result_rel (LIST_REL v_rel) v_rel res res' /\
        state_rel s2 s2')``,
  HO_MATCH_MP_TAC (evaluate_ind |> Q.SPEC `\(x1,x2,x3). P0 x1 x2 x3` |> Q.GEN `P0`
                             |> SIMP_RULE std_ss [FORALL_PROD])
  \\ REPEAT STRIP_TAC
  THEN1 (* NIL *)
   (fs [free_def,shift_def,evaluate_def]
    \\ SRW_TAC [] [])
  THEN1 (* CONS *)
   (fs [free_def,evaluate_def]
    \\ `?y1 l1. free [x] = ([y1],l1)` by METIS_TAC [PAIR,free_SING]
    \\ `?y2 l2. free (y::xs) = (y2,l2)` by METIS_TAC [PAIR] \\ fs []
    \\ fs [LET_DEF]
    \\ `?r1 s2. evaluate ([x],env,s1) = (r1,s2)` by METIS_TAC [PAIR] \\ fs []
    \\ `?y3 y4. y2 = y3::y4` by
     (IMP_RES_TAC free_LENGTH
      \\ Cases_on `y2` \\ fs [has_var_def,fv_def])
    \\ fs [shift_def]
    \\ Cases_on `r1` \\ fs []
    \\ SRW_TAC [] [markerTheory.Abbrev_def]
    \\ SRW_TAC [] [markerTheory.Abbrev_def]
    \\ `?t. shift [y1] m l i = [t]` by METIS_TAC [shift_SING]
    \\ fs [] \\ ONCE_REWRITE_TAC [evaluate_CONS]
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`env'`,`t1`])
    \\ REPEAT STRIP_TAC \\ POP_ASSUM (MP_TAC o Q.SPECL [`m`,`l`,`i`])
    \\ `fv_set [x] SUBSET env_ok m l i env env' /\
        fv_set (y::xs) SUBSET env_ok m l i env env'` by
      (fs [SUBSET_DEF,IN_DEF,fv_def])
    \\ fs [] \\ REPEAT STRIP_TAC \\ fs []
    \\ `?r2 s3. evaluate (y::xs,env,s2') = (r2,s3)` by METIS_TAC [PAIR] \\ fs []
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`env'`,`t2`])
    \\ Cases_on `r2` \\ fs []
    \\ REPEAT STRIP_TAC \\ POP_ASSUM (MP_TAC o Q.SPECL [`m`,`l`,`i`]) \\ fs []
    \\ REPEAT STRIP_TAC \\ fs [] \\ SRW_TAC [] [] \\ fs []
    \\ IMP_RES_TAC evaluate_SING \\ fs [])
  THEN1 (* Var *)
   (Cases_on `n < LENGTH env`
    \\ fs [free_def,evaluate_def,shift_def]
    \\ fs [SUBSET_DEF,IN_DEF,fv_def]
    \\ Cases_on `l + m <= n`
    THEN1 (fs [env_ok_def] \\ rfs [] \\ `F` by DECIDE_TAC)
    \\ REVERSE (`get_var m l i n < LENGTH env' /\
        v_rel (EL n env) (EL (get_var m l i n) env')` by ALL_TAC)
    THEN1 (fs [] \\ SRW_TAC [] [] \\ fs [])
    \\ fs [get_var_def,env_ok_def]
    \\ Cases_on `n < l` \\ fs [tlookup_def]
    \\ `F` by DECIDE_TAC)
  THEN1 (* If *)
   (fs [free_def]
    \\ `?y1 l1. free [x1] = ([y1],l1)` by METIS_TAC [PAIR,free_SING]
    \\ `?y2 l2. free [x2] = ([y2],l2)` by METIS_TAC [PAIR,free_SING]
    \\ `?y3 l3. free [x3] = ([y3],l3)` by METIS_TAC [PAIR,free_SING]
    \\ fs [LET_DEF,shift_def,evaluate_def]
    \\ `?r1 s2. evaluate ([x1],env,s1) = (r1,s2)` by METIS_TAC [PAIR] \\ fs []
    \\ `fv_set [x1] SUBSET env_ok m l i env env' /\
        fv_set [x2] SUBSET env_ok m l i env env' /\
        fv_set [x3] SUBSET env_ok m l i env env'` by
      (fs [SUBSET_DEF,IN_DEF,fv_def])
    \\ `r1 <> Rerr(Rabort Rtype_error)` by (REPEAT STRIP_TAC \\ fs [])
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`env'`,`t1`,`m`,`l`,`i`]) \\ fs []
    \\ REPEAT STRIP_TAC \\ fs []
    \\ Cases_on `r1` \\ fs [] \\ SRW_TAC [] []
    \\ fs [] \\ SRW_TAC [] []
    \\ IMP_RES_TAC evaluate_SING \\ fs [] \\ SRW_TAC [] []
    \\ fs [] \\ SRW_TAC [] []
    \\ fs [v_rel_simp] \\ SRW_TAC [] []
    \\ Cases_on `r1 = Boolv T` \\ fs [v_rel_simp]
    \\ Cases_on `r1 = Boolv F` \\ fs [v_rel_simp])
  THEN1 (* Let *)
   (fs [free_def]
    \\ `?y1 l1. free xs = (y1,l1)` by METIS_TAC [PAIR,free_SING]
    \\ `?y2 l2. free [x2] = ([y2],l2)` by METIS_TAC [PAIR,free_SING]
    \\ fs [LET_DEF,shift_def,evaluate_def]
    \\ `?r1 s2. evaluate (xs,env,s1) = (r1,s2)` by METIS_TAC [PAIR] \\ fs []
    \\ `fv_set xs SUBSET env_ok m l i env env'` by
      (fs [SUBSET_DEF,IN_DEF,fv_def])
    \\ `r1 <> Rerr(Rabort Rtype_error)` by (REPEAT STRIP_TAC \\ fs [])
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`env'`,`t1`,`m`,`l`,`i`]) \\ fs []
    \\ REPEAT STRIP_TAC \\ fs []
    \\ Cases_on `r1` \\ fs [] \\ SRW_TAC [] []
    \\ fs [] \\ SRW_TAC [] []
    \\ FIRST_X_ASSUM (qspecl_then[`v'++env'`,`t2`,
         `m`,`l + LENGTH y1`,`i`]mp_tac)
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
    \\ REPEAT STRIP_TAC \\ fs []
    \\ fs [] \\ fs [SUBSET_DEF,IN_DEF] \\ REPEAT STRIP_TAC
    \\ IMP_RES_TAC free_LENGTH
    \\ IMP_RES_TAC EVERY2_LENGTH
    \\ IMP_RES_TAC evaluate_IMP_LENGTH
    \\ fs [shift_LENGTH_LEMMA,AC ADD_COMM ADD_ASSOC]
    \\ MATCH_MP_TAC env_ok_EXTEND \\ fs []
    \\ fs [fv_def]
    \\ REPEAT STRIP_TAC
    \\ Q.PAT_ASSUM `!x.bbb` (K ALL_TAC)
    \\ FIRST_X_ASSUM MATCH_MP_TAC
    \\ `x - LENGTH v' + LENGTH v' = x` by DECIDE_TAC \\ fs [])
  THEN1 (* Raise *)
   (fs [free_def]
    \\ `?y1 l1. free [x1] = ([y1],l1)` by METIS_TAC [PAIR,free_SING]
    \\ fs [LET_DEF,shift_def,evaluate_def]
    \\ `?r1 s2. evaluate ([x1],env,s1) = (r1,s2)` by METIS_TAC [PAIR] \\ fs []
    \\ `fv_set [x1] SUBSET env_ok m l i env env'` by
      (fs [SUBSET_DEF,IN_DEF,fv_def])
    \\ `r1 <> Rerr(Rabort Rtype_error)` by (REPEAT STRIP_TAC \\ fs [])
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`env'`,`t1`,`m`,`l`,`i`]) \\ fs []
    \\ REPEAT STRIP_TAC \\ fs []
    \\ Cases_on `r1` \\ fs [] \\ SRW_TAC [] []
    \\ fs [] \\ SRW_TAC [] []
    \\ IMP_RES_TAC evaluate_SING \\ fs [])
  THEN1 (* Handle *)
   (fs [free_def]
    \\ `?y1 l1. free [x1] = ([y1],l1)` by METIS_TAC [PAIR,free_SING]
    \\ `?y2 l2. free [x2] = ([y2],l2)` by METIS_TAC [PAIR,free_SING]
    \\ fs [LET_DEF,shift_def,evaluate_def]
    \\ `?r1 s2. evaluate ([x1],env,s1) = (r1,s2)` by METIS_TAC [PAIR] \\ fs []
    \\ `fv_set [x1] SUBSET env_ok m l i env env'` by
      (fs [SUBSET_DEF,IN_DEF,fv_def])
    \\ `r1 <> Rerr(Rabort Rtype_error)` by (REPEAT STRIP_TAC \\ fs [])
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`env'`,`t1`,`m`,`l`,`i`]) \\ fs []
    \\ REPEAT STRIP_TAC \\ fs []
    \\ Cases_on `r1` \\ fs [] \\ SRW_TAC [] []
    \\ fs [] \\ SRW_TAC [] []
    \\ Cases_on `e` \\ fs [] \\ SRW_TAC [] []
    \\ fs [] \\ SRW_TAC [] []
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`v'::env'`,`t2`,`m`,`l+1`,`i`]) \\ fs []
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC \\ fs []
    \\ fs [AC ADD_ASSOC ADD_COMM,ADD1]
    \\ fs [SUBSET_DEF,IN_DEF] \\ REPEAT STRIP_TAC
    \\ MATCH_MP_TAC env_ok_cons \\ fs []
    \\ RES_TAC \\ REPEAT STRIP_TAC
    \\ fs [fv_def]
    \\ Cases_on `x` \\ fs []
    \\ Q.PAT_ASSUM `!x.bbb` (K ALL_TAC)
    \\ FIRST_X_ASSUM MATCH_MP_TAC \\ fs [ADD1])
  THEN1 (* Op *)
   (fs [free_def]
    \\ `?y1 l1. free xs = (y1,l1)` by METIS_TAC [PAIR,free_SING]
    \\ fs [LET_DEF,shift_def,evaluate_def]
    \\ `?r1 s2. evaluate (xs,env,s1) = (r1,s2)` by METIS_TAC [PAIR] \\ fs []
    \\ `fv_set xs SUBSET env_ok m l i env env'` by
      (fs [SUBSET_DEF,IN_DEF,fv_def])
    \\ `r1 <> Rerr(Rabort Rtype_error)` by (REPEAT STRIP_TAC \\ fs [])
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`env'`,`t1`,`m`,`l`,`i`]) \\ fs []
    \\ REPEAT STRIP_TAC \\ fs []
    \\ Cases_on `r1` \\ fs [] \\ SRW_TAC [] []
    \\ fs [] \\ SRW_TAC [] [] >>
    last_x_assum mp_tac >>
    reverse BasicProvers.CASE_TAC >- (
      rw[] >>
      IMP_RES_TAC do_app_err >> fs[] >> rw[] >>
      imp_res_tac EVERY2_REVERSE >>
      IMP_RES_TAC do_app_err_thm >> rfs[] ) >>
    BasicProvers.CASE_TAC >> rw[] >>
    IMP_RES_TAC EVERY2_REVERSE
    \\ IMP_RES_TAC do_app_thm \\ fs [])
  THEN1 (* Fn *)
   (fs [free_def,evaluate_def]
    \\ `~s1.restrict_envs /\ t1.restrict_envs` by fs [state_rel_def]
    \\ fs [clos_env_def]
    \\ SRW_TAC [] [] \\ SRW_TAC [] [markerTheory.Abbrev_def]
    \\ `?y1 l1. free [exp] = ([y1],l1)` by METIS_TAC [PAIR,free_SING]
    \\ Cases_on `num_args <= max_app` \\ fs []
    \\ Cases_on `num_args <> 0` \\ fs [] \\ SRW_TAC [] []
    \\ fs [shift_def,LET_DEF,evaluate_def,clos_env_def,
           PULL_EXISTS,v_rel_simp]
    \\ Q.ABBREV_TAC `live =
          FILTER (\n. n < m + l) (vars_to_list (Shift num_args l1))`
    \\ fs [MAP_MAP_o,o_DEF]
    \\ Cases_on `lookup_vars (MAP (get_var m l i) live) env'`
    \\ fs [] THEN1
     (fs [SUBSET_DEF,IN_DEF,fv_def]
      \\ fs [lookup_vars_NONE] \\ UNABBREV_ALL_TAC
      \\ fs [MEM_FILTER,MEM_vars_to_list,MEM_MAP]
      \\ MP_TAC (Q.SPEC`[exp]` free_thm)
      \\ fs [LET_DEF] \\ CCONTR_TAC \\ fs [] \\ RES_TAC
      \\ SRW_TAC [] []
      \\ fs [env_ok_def] \\ rfs []
      \\ fs [get_var_def,tlookup_def]
      \\ DECIDE_TAC)
    \\ Q.EXISTS_TAC `new_env 0 live` \\ fs []
    \\ REPEAT STRIP_TAC \\ Cases_on `n` \\ fs []
    \\ MP_TAC (Q.SPEC `[exp]` free_thm)
    \\ fs [LET_DEF] \\ STRIP_TAC
    \\ fs [SUBSET_DEF,IN_DEF,fv_def]
    \\ fs [ADD1] \\ RES_TAC \\ UNABBREV_ALL_TAC
    \\ Q.ABBREV_TAC `live = vars_to_list (Shift num_args l1)`
    \\ MATCH_MP_TAC (GEN_ALL env_ok_new_env)
    \\ Q.LIST_EXISTS_TAC [`i`,`env'`] \\ fs []
    \\ `n' + 1 = (n' + 1 - num_args) + num_args` by DECIDE_TAC
    \\ STRIP_TAC THEN1 METIS_TAC []
    \\ STRIP_TAC THEN1 (UNABBREV_ALL_TAC \\ fs [MEM_vars_to_list] \\ METIS_TAC [])
    \\ UNABBREV_ALL_TAC \\ fs [ALL_DISTINCT_vars_to_list])
  THEN1 (* Letrec *)
   (fs [free_def,evaluate_def]
    \\ `~s1.restrict_envs /\ t1.restrict_envs` by fs [state_rel_def]
    \\ fs [clos_env_def]
    \\ SRW_TAC [] [] \\ SRW_TAC [] [markerTheory.Abbrev_def]
    \\ `EVERY (\(num_args,e). num_args <= max_app /\
                              num_args <> 0) fns` by
      (CCONTR_TAC \\ FULL_SIMP_TAC std_ss [])
    \\ Cases_on `build_recc F loc env names fns` \\ fs []
    \\ Q.ABBREV_TAC `rec_res = MAP
                        (\(n,x).
                           (let (c,l) = free [x] in
                              ((n,HD c),Shift (n + LENGTH fns) l))) fns`
    \\ `?y2 l2. free [exp] = ([y2],l2)` by METIS_TAC [PAIR,free_SING]
    \\ fs [shift_def,LET_DEF,evaluate_def,build_recc_def,clos_env_def,
           shift_LENGTH_LEMMA]
    \\ Q.PAT_ABBREV_TAC `ev = EVERY PP xx`
    \\ `ev` by
     (UNABBREV_ALL_TAC \\ fs [MAP_MAP_o,o_DEF]
      \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) \\ fs [EVERY_MAP]
      \\ fs [EVERY_MEM,FORALL_PROD] \\ REPEAT STRIP_TAC \\ RES_TAC)
    \\ fs [] \\ POP_ASSUM (K ALL_TAC) \\ POP_ASSUM (K ALL_TAC)
    \\ Q.ABBREV_TAC `live = FILTER (\n. n < m + l)
          (vars_to_list (list_mk_Union (MAP SND rec_res)))`
    \\ Cases_on `lookup_vars (MAP (get_var m l i) live) env'`
    \\ fs [] THEN1
     (fs [SUBSET_DEF,IN_DEF,fv_def]
      \\ fs [lookup_vars_NONE] \\ UNABBREV_ALL_TAC
      \\ fs [MEM_FILTER,MEM_vars_to_list,MEM_MAP]
      \\ fs [EXISTS_MEM,PULL_EXISTS,EXISTS_PROD]
      \\ NTAC 3 (POP_ASSUM MP_TAC)
      \\ fs [MAP_MAP_o,o_DEF,MEM_MAP,EXISTS_PROD]
      \\ REPEAT STRIP_TAC
      \\ Q.MATCH_ASSUM_RENAME_TAC `MEM (p_11,p_21) fns`
      \\ Cases_on `free [p_21]` \\ fs [] \\ SRW_TAC [] [] \\ fs []
      \\ MP_TAC (Q.SPEC`[p_21]` free_thm)
      \\ fs [LET_DEF] \\ CCONTR_TAC
      \\ fs [AC ADD_ASSOC ADD_COMM] \\ RES_TAC
      \\ SRW_TAC [] [] \\ fs []
      \\ fs [env_ok_def] \\ rfs []
      \\ fs [get_var_def,tlookup_def]
      \\ DECIDE_TAC)
    \\ FIRST_X_ASSUM MATCH_MP_TAC
    \\ IMP_RES_TAC free_LENGTH \\ fs []
    \\ `LENGTH rec_res = LENGTH x` by ALL_TAC THEN1
      (UNABBREV_ALL_TAC \\ fs [] \\ SRW_TAC [] [] \\ fs [])
    \\ STRIP_TAC THEN1 (fs [AC ADD_COMM ADD_ASSOC])
    \\ fs [SUBSET_DEF,IN_DEF,fv_def]
    \\ REPEAT STRIP_TAC
    \\ MATCH_MP_TAC (env_ok_EXTEND |> GEN_ALL) \\ fs []
    \\ REVERSE (REPEAT STRIP_TAC) THEN1
     (FIRST_X_ASSUM MATCH_MP_TAC \\ DISJ2_TAC
      \\ UNABBREV_ALL_TAC \\ fs [] \\ SRW_TAC [] [] \\ fs []
      \\ IMP_RES_TAC (DECIDE ``n <= m:num <=> (m - n + n = m)``) \\ fs [])
    \\ SRW_TAC [] []
    \\ fs [LIST_REL_GENLIST] \\ REPEAT STRIP_TAC
    \\ fs [v_rel_simp]
    \\ Q.UNABBREV_TAC `rec_res`
    \\ fs [EVERY2_MAP]
    \\ MATCH_MP_TAC listTheory.EVERY2_refl
    \\ REPEAT STRIP_TAC
    \\ PairCases_on `x` \\ fs []
    \\ `?y1 y2. free [x1] = ([y1],y2)` by METIS_TAC [free_SING,PAIR]
    \\ fs [] \\ Q.EXISTS_TAC `new_env 0 live`
    \\ STRIP_TAC THEN1 SIMP_TAC std_ss [AC ADD_COMM ADD_ASSOC]
    \\ REPEAT STRIP_TAC
    \\ UNABBREV_ALL_TAC
    \\ MATCH_MP_TAC (GEN_ALL env_ok_new_env)
    \\ Q.LIST_EXISTS_TAC [`i`,`env'`] \\ fs []
    \\ fs [AC ADD_COMM ADD_ASSOC,ALL_DISTINCT_vars_to_list]
    \\ fs [MEM_vars_to_list]
    \\ STRIP_TAC THEN1
     (FIRST_X_ASSUM MATCH_MP_TAC \\ DISJ1_TAC
      \\ fs [EXISTS_MEM,EXISTS_PROD]
      \\ Q.LIST_EXISTS_TAC [`x0`,`x1`] \\ fs []
      \\ fs [MEM_EL,PULL_EXISTS]
      \\ `x0 + (n - (x0 + LENGTH fns) + LENGTH fns) = n` by DECIDE_TAC
      \\ METIS_TAC [])
    \\ fs [EXISTS_MEM,EXISTS_PROD,PULL_EXISTS]
    \\ fs [MEM_MAP,EXISTS_PROD,PULL_EXISTS]
    \\ CONV_TAC (DEPTH_CONV (PairRules.PBETA_CONV)) \\ fs []
    \\ Q.LIST_EXISTS_TAC [`x0`,`x1`] \\ fs []
    \\ MP_TAC (Q.SPEC `[x1]` free_thm)
    \\ IMP_RES_TAC (DECIDE ``n <= m:num <=> (m - n + n = m)``)
    \\ fs [LET_DEF] \\ STRIP_TAC \\ fs [])
  THEN1 (* App *)
   (fs [free_def]
    \\ `?y1 l1. free xs = (y1,l1)` by METIS_TAC [PAIR]
    \\ `?y2 l2. free [x1] = ([y2],l2)` by METIS_TAC [PAIR,free_SING]
    \\ fs [LET_DEF,shift_def,evaluate_def]
    \\ `?r1 s2. evaluate (xs,env,s1) = (r1,s2)` by METIS_TAC [PAIR] \\ fs []
    \\ `?r2 s3. evaluate ([x1],env,s2') = (r2,s3)` by METIS_TAC [PAIR] \\ fs []
    \\ fs [shift_LENGTH_LEMMA]
    \\ IMP_RES_TAC free_LENGTH
    \\ Cases_on `LENGTH xs > 0` \\ fs []
    \\ `fv_set xs SUBSET env_ok m l i env env' /\
        fv_set [x1] SUBSET env_ok m l i env env'` by
      (fs [SUBSET_DEF,IN_DEF,fv_def])
    \\ `r1 <> Rerr(Rabort Rtype_error)` by (REPEAT STRIP_TAC \\ fs [])
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`env'`,`t1`,`m`,`l`,`i`]) \\ fs []
    \\ REPEAT STRIP_TAC \\ fs []
    \\ Cases_on `r1` \\ fs [] \\ SRW_TAC [] []
    \\ fs [] \\ SRW_TAC [] []
    \\ `?r2 s2. evaluate ([x1],env,s1) = (r2,s2)` by METIS_TAC [PAIR] \\ fs []
    \\ `r2 <> Rerr(Rabort Rtype_error)` by (REPEAT STRIP_TAC \\ fs [])
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`env'`,`t2`,`m`,`l`,`i`]) \\ fs []
    \\ REPEAT STRIP_TAC \\ fs []
    \\ Cases_on `r2` \\ fs [] \\ SRW_TAC [] []
    \\ fs [] \\ SRW_TAC [] []
    \\ IMP_RES_TAC evaluate_SING \\ fs [] \\ SRW_TAC [] [])
  THEN1 (* Tick *)
   (fs [free_def,evaluate_def]
    \\ `?y1 l1. free [x] = ([y1],l1)` by METIS_TAC [PAIR,free_SING]
    \\ fs [LET_DEF,shift_def,evaluate_def]
    \\ `t1.clock = s1.clock` by fs [state_rel_def] \\ fs []
    \\ Cases_on `s1.clock = 0` \\ fs []
    \\ SRW_TAC [] []
    \\ `fv_set [x] SUBSET env_ok m l i env env'` by
      (fs [SUBSET_DEF,IN_DEF,fv_def])
    \\ `state_rel (dec_clock 1 s1) (dec_clock 1 t1)` by
          fs [state_rel_def,dec_clock_def] \\ RES_TAC
    \\ STRIP_ASSUME_TAC (shift_SING |> Q.INST [`x`|->`y1`]) \\ fs [])
  THEN1 (* Call *)
   (fs [free_def]
    \\ `?y1 l1. free xs = (y1,l1)` by METIS_TAC [PAIR,free_SING]
    \\ fs [LET_DEF,shift_def,evaluate_def]
    \\ `?r1 s2. evaluate (xs,env,s1) = (r1,s2)` by METIS_TAC [PAIR] \\ fs []
    \\ `fv_set xs SUBSET env_ok m l i env env'` by
      (fs [SUBSET_DEF,IN_DEF,fv_def])
    \\ `r1 <> Rerr(Rabort Rtype_error)` by (REPEAT STRIP_TAC \\ fs [])
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`env'`,`t1`,`m`,`l`,`i`]) \\ fs []
    \\ REPEAT STRIP_TAC \\ fs []
    \\ Cases_on `r1` \\ fs [] \\ SRW_TAC [] []
    \\ fs [] \\ SRW_TAC [] []
    \\ Cases_on `find_code dest a s2'.code` \\ fs []
    \\ Cases_on `x` \\ fs []
    \\ fs [find_code_def]
    \\ Cases_on `FLOOKUP s2'.code dest` \\ fs []
    \\ Cases_on `x` \\ fs [] \\ SRW_TAC [] []
    \\ `?c2. shift (FST (free [r])) 0 (LENGTH a) LN = [c2] /\
             FLOOKUP t2.code dest = SOME (LENGTH a,c2)` by
         (fs [state_rel_def] \\ RES_TAC \\ NO_TAC)
    \\ fs [] \\ IMP_RES_TAC EVERY2_LENGTH \\ fs []
    \\ `s2'.clock = t2.clock` by fs [state_rel_def] \\ fs []
    \\ Cases_on `t2.clock = 0` \\ fs []
    THEN1 (SRW_TAC [] [])
    \\ FIRST_X_ASSUM (qspecl_then[`v'`,`dec_clock 1 t2`,`0`,
         `LENGTH v'`,`LN`]mp_tac)
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
     (fs [] \\ REVERSE (REPEAT STRIP_TAC)
      THEN1 (fs [state_rel_def,dec_clock_def])
      \\ fs [SUBSET_DEF,IN_DEF] \\ REPEAT STRIP_TAC
      \\ SIMP_TAC std_ss [env_ok_def]
      \\ REVERSE (Cases_on `x < LENGTH v'`) \\ fs [] THEN1 DECIDE_TAC
      \\ IMP_RES_TAC EVERY2_EL \\ METIS_TAC [])
    \\ REPEAT STRIP_TAC \\ fs [] \\ rfs [])
  THEN1 (* evaluate_app NIL *)
   (fs [] \\ SRW_TAC [] []
    \\ fs [evaluate_def] \\ SRW_TAC [] [])
  THEN1 (* evaluate_app CONS *)
   (fs [evaluate_def]
    \\ Cases_on `dest_closure loc_opt f (v41::v42)` \\ fs []
    \\ Cases_on `x` \\ fs []
    THEN1 (* Partial_app *)
     (REVERSE (`?z. (dest_closure loc_opt f' (y::ys) = SOME (Partial_app z)) /\
           v_rel v z` by ALL_TAC) THEN1
       (fs [] \\ IMP_RES_TAC EVERY2_LENGTH \\ fs []
        \\ `s1'.clock = s1.clock` by fs [state_rel_def] \\ fs []
        \\ SRW_TAC [] [] \\ fs [] \\ SRW_TAC [] []
        \\ fs [state_rel_def,dec_clock_def])
      \\ fs [dest_closure_def]
      \\ Cases_on `f` \\ fs []
      \\ TRY (Cases_on `EL n l1`) \\ fs [LET_DEF]
      \\ fs [METIS_PROVE [] ``((if b then x1 else x2) = SOME y) <=>
              (b /\ (x1 = SOME y)) \/ (~b /\ (x2 = SOME y))``]
      \\ SRW_TAC [] [] \\ fs [v_rel_simp]
      \\ IMP_RES_TAC EVERY2_LENGTH \\ fs []
      THEN1
       (fs [PULL_EXISTS] \\ Q.EXISTS_TAC `i` \\ fs []
        \\ REPEAT STRIP_TAC
        \\ TRY (MATCH_MP_TAC rich_listTheory.EVERY2_APPEND_suff \\ fs [])
        \\ rfs [] \\ DECIDE_TAC)
      \\ Cases_on `EL n cs'` \\ fs []
      \\ fs [METIS_PROVE [] ``((if b then x1 else x2) = SOME y) <=>
              (b /\ (x1 = SOME y)) \/ (~b /\ (x2 = SOME y))``]
      \\ `n < LENGTH l1` by fs []
      \\ IMP_RES_TAC EVERY2_EL \\ rfs[]
      \\ MATCH_MP_TAC rich_listTheory.EVERY2_APPEND_suff \\ fs [])
    (* Full_app *)
    \\ Cases_on `f` \\ fs [dest_closure_def]
    \\ TRY (Cases_on `EL n l1`) \\ fs [LET_DEF]
    \\ TRY (Cases_on `EL n cs'`) \\ fs [LET_DEF]
    \\ fs [METIS_PROVE [] ``((if b then x1 else x2) = SOME y) <=>
            (b /\ (x1 = SOME y)) \/ (~b /\ (x2 = SOME y))``]
    THEN1
     (SRW_TAC [] [] \\ fs [v_rel_simp]
      \\ IMP_RES_TAC EVERY2_LENGTH \\ fs []
      \\ `s1'.clock = s1.clock` by fs [state_rel_def] \\ fs []
      \\ fs [METIS_PROVE [] ``((if b then x1 else x2) = y) <=>
              (b /\ (x1 = y)) \/ (~b /\ (x2 = y))``]
      \\ SRW_TAC [] [] \\ fs []
      \\ TRY (fs [state_rel_def] \\ NO_TAC) \\ rfs []
      \\ Q.ABBREV_TAC `env3 =
         REVERSE (TAKE (n - LENGTH vals') (REVERSE v42 ++ [v41])) ++
            l' ++ l0'`
      \\ Q.ABBREV_TAC `n3 =
           (SUC (LENGTH ys) - (LENGTH ys + 1 - (n - LENGTH vals')))`
      \\ Cases_on `evaluate ([e],env3,dec_clock n3 s1)` \\ fs []
      \\ `q <> Rerr(Rabort Rtype_error)` by (REPEAT STRIP_TAC \\ fs [])
      \\ Q.ABBREV_TAC `env3' =
           REVERSE (TAKE (n - LENGTH vals') (REVERSE ys ++ [y])) ++
           vals' ++ env'`
      \\ FIRST_X_ASSUM (qspecl_then [`env3'`,`dec_clock n3 s1'`,
           `LENGTH (l0':closSem$v list)`,`n`,`i`]mp_tac)
      \\ fs [] \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
      THEN1
       (REPEAT STRIP_TAC
        \\ TRY (fs [state_rel_def,dec_clock_def] \\ NO_TAC)
        THEN1 (fs [LENGTH_TAKE_EQ] \\ SRW_TAC [] [] \\ DECIDE_TAC)
        \\ fs [SUBSET_DEF,IN_DEF] \\ REPEAT STRIP_TAC
        \\ Q.UNABBREV_TAC `env3`
        \\ Q.UNABBREV_TAC `env3'`
        \\ MATCH_MP_TAC env_ok_some
        \\ Q.EXISTS_TAC `0` \\ fs []
        \\ MATCH_MP_TAC (METIS_PROVE []
             ``b1 /\ (b1 ==> b2) ==> b1 /\ b2``)
        \\ fs [] \\ REPEAT STRIP_TAC
        THEN1 (fs [LENGTH_TAKE_EQ] \\ SRW_TAC [] [] \\ DECIDE_TAC)
        \\ MATCH_MP_TAC rich_listTheory.EVERY2_APPEND_suff \\ fs []
        \\ MATCH_MP_TAC EVERY2_REVERSE
        \\ MATCH_MP_TAC EVERY2_TAKE
        \\ MATCH_MP_TAC rich_listTheory.EVERY2_APPEND_suff \\ fs []
        \\ MATCH_MP_TAC EVERY2_REVERSE \\ fs [])
      \\ REPEAT STRIP_TAC \\ fs []
      \\ REVERSE (Cases_on `q`) \\ fs []
      \\ SRW_TAC [] [] \\ fs []
      \\ REVERSE (Cases_on `a`) \\ fs []
      \\ SRW_TAC [] [] \\ fs []
      \\ REVERSE (Cases_on `t`) \\ fs []
      \\ SRW_TAC [] [] \\ fs []
      \\ Q.MATCH_ASSUM_RENAME_TAC `v_rel h h'`
      \\ FIRST_X_ASSUM MATCH_MP_TAC \\ fs []
      \\ MATCH_MP_TAC EVERY2_REVERSE
      \\ MATCH_MP_TAC EVERY2_DROP
      \\ MATCH_MP_TAC rich_listTheory.EVERY2_APPEND_suff \\ fs []
      \\ MATCH_MP_TAC EVERY2_REVERSE \\ fs [])
    \\ SRW_TAC [] [] \\ fs [v_rel_simp]
    \\ Cases_on `EL n cs'` \\ fs []
    \\ IMP_RES_TAC EVERY2_LENGTH \\ fs []
    \\ `q' = q` by
     (`n < LENGTH l1` by fs []
      \\ IMP_RES_TAC EVERY2_EL \\ rfs []) \\ fs []
    \\ fs [METIS_PROVE [] ``((if b then x1 else x2) = y) <=>
              (b /\ (x1 = y)) \/ (~b /\ (x2 = y))``]
    \\ `s1'.clock = s1.clock` by fs [state_rel_def] \\ fs []
    THEN1 (SRW_TAC [] [] \\ fs [state_rel_def])
    \\ Q.ABBREV_TAC `env3 =
         REVERSE (TAKE (q - LENGTH vals') (REVERSE v42 ++ [v41])) ++
            l' ++ GENLIST (Recclosure n0 [] l0' l1) (LENGTH cs') ++ l0'`
    \\ Q.ABBREV_TAC `n3 =
           (SUC (LENGTH ys) - (LENGTH ys + 1 - (q - LENGTH vals')))`
    \\ Cases_on `evaluate ([e],env3,dec_clock n3 s1)` \\ fs []
    \\ `q'' <> Rerr(Rabort Rtype_error)` by (REPEAT STRIP_TAC \\ fs [])
    \\ Q.ABBREV_TAC `env3' =
           REVERSE (TAKE (q - LENGTH vals') (REVERSE ys ++ [y])) ++ vals' ++
           GENLIST (Recclosure n0 [] env' cs') (LENGTH cs') ++ env'`
    \\ `n < LENGTH l1` by fs []
    \\ IMP_RES_TAC EVERY2_EL
    \\ rfs []
    \\ FIRST_X_ASSUM (qspecl_then [`env3'`,`dec_clock n3 s1'`,
           `LENGTH (l0':closSem$v list)`,
           `LENGTH (cs') + q`,`i`]mp_tac)
    \\ fs [] \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
    THEN1
     (REPEAT STRIP_TAC
      \\ TRY (fs [state_rel_def,dec_clock_def] \\ NO_TAC)
      THEN1 (fs [LENGTH_TAKE_EQ] \\ SRW_TAC [] [] \\ DECIDE_TAC)
      \\ fs [SUBSET_DEF,IN_DEF] \\ REPEAT STRIP_TAC
      \\ Q.UNABBREV_TAC `env3`
      \\ Q.UNABBREV_TAC `env3'`
      \\ MATCH_MP_TAC env_ok_some
      \\ Q.EXISTS_TAC `0` \\ fs []
      \\ MATCH_MP_TAC (METIS_PROVE []
           ``b1 /\ (b1 ==> b2) ==> b1 /\ b2``)
      \\ fs [] \\ REPEAT STRIP_TAC
      THEN1 (fs [LENGTH_TAKE_EQ] \\ SRW_TAC [] [] \\ DECIDE_TAC)
      \\ TRY (fs [AC ADD_COMM ADD_ASSOC]
        \\ FIRST_X_ASSUM MATCH_MP_TAC \\ fs []
        \\ fs [AC ADD_COMM ADD_ASSOC] \\ NO_TAC)
      \\ MATCH_MP_TAC rich_listTheory.EVERY2_APPEND_suff \\ fs []
      \\ REPEAT STRIP_TAC THEN1
       (MATCH_MP_TAC rich_listTheory.EVERY2_APPEND_suff \\ fs []
        \\ MATCH_MP_TAC EVERY2_REVERSE
        \\ MATCH_MP_TAC EVERY2_TAKE
        \\ MATCH_MP_TAC rich_listTheory.EVERY2_APPEND_suff \\ fs []
        \\ MATCH_MP_TAC EVERY2_REVERSE \\ fs [])
      \\ fs [LIST_REL_GENLIST]
      \\ fs [v_rel_simp] \\ REPEAT STRIP_TAC
      \\ fs [])
    \\ REPEAT STRIP_TAC \\ fs []
    \\ REVERSE (Cases_on `q''`) \\ fs []
    \\ SRW_TAC [] [] \\ fs []
    \\ REVERSE (Cases_on `a`) \\ fs []
    \\ SRW_TAC [] [] \\ fs []
    \\ REVERSE (Cases_on `t`) \\ fs []
    \\ SRW_TAC [] [] \\ fs []
    \\ Q.MATCH_ASSUM_RENAME_TAC `v_rel h h'`
    \\ FIRST_X_ASSUM MATCH_MP_TAC \\ fs []
    \\ MATCH_MP_TAC EVERY2_REVERSE
    \\ MATCH_MP_TAC EVERY2_DROP
    \\ MATCH_MP_TAC rich_listTheory.EVERY2_APPEND_suff \\ fs []
    \\ MATCH_MP_TAC EVERY2_REVERSE \\ fs []));

val env_set_default = prove(
  ``x SUBSET env_ok 0 0 LN [] env'``,
  fs [SUBSET_DEF,IN_DEF,env_ok_def]);

val annotate_correct = save_thm("annotate_correct",
  shift_correct |> CONJUNCT1
  |> SPEC_ALL |> Q.INST [`m`|->`0`,`l`|->`0`,`i`|->`LN`,`env`|->`[]`]
  |> REWRITE_RULE [GSYM annotate_def,env_set_default,LENGTH,ADD_0]);

val _ = export_theory()
