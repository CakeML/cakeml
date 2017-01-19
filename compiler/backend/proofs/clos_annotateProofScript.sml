open preamble
     db_varsTheory
     closSemTheory closPropsTheory
     clos_freeTheory clos_freeProofTheory
     clos_annotateTheory;

val _ = new_theory"clos_annotateProof";

val _ = temp_bring_to_front_overload"do_app"{Name="do_app",Thy="closSem"};

val EVERY2_EL = LIST_REL_EL_EQN |> SPEC_ALL |> EQ_IMP_RULE |> fst
                |> UNDISCH |> CONJUNCT2 |> DISCH_ALL;

(* value relation *)

val _ = overload_on("fv_set",``λx y. fv y x``);

val (v_rel_rules,v_rel_ind,v_rel_cases) = Hol_reln `
  (v_rel (Number j) (Number j))
  /\
  (v_rel (Word64 w) (Word64 w))
  /\
  (EVERY2 v_rel (xs:closSem$v list) (ys:closSem$v list) ==>
   v_rel (Block t xs) (Block t ys))
  /\
  (v_rel (ByteVector ws) (ByteVector ws))
  /\
  (v_rel (RefPtr r1) (RefPtr r1))
  /\
  ((shift (FST (free [c])) m num_args i = [c']) /\
   (!n. fv_set [c] n /\ num_args <= n ==>
        env_ok m 0 i env env' (n - num_args)) /\
   every_Fn_vs_NONE [c] ∧
   (LENGTH env = m) /\ EVERY2 v_rel vals vals' ==>
   v_rel (Closure p vals env num_args c) (Closure p vals' env' num_args c'))
  /\
  (EVERY2 ( \ (num_args,c1) (num_args',c1').
     ?m i.
       (num_args' = num_args) /\
       (shift (FST (free [c1])) m (LENGTH cs + num_args) i = [c1']) /\
       (!n. fv_set [c1] n /\ num_args + LENGTH cs <= n ==>
          env_ok m 0 i env env' (n - (num_args + LENGTH cs))) /\
       every_Fn_vs_NONE [c1] ∧
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
            ``v_rel (Word64 n) y``,
            ``v_rel (Block n l) y``,
            ``v_rel (ByteVector ws) y``,
            ``v_rel (RefPtr x) y``,
            ``v_rel (Closure n l v x w) y``,
            ``v_rel (Recclosure x1 x2 x3 x4 x5) y``,
            ``v_rel y (Number x)``,
            ``v_rel y (Block n l)``,
            ``v_rel y (ByteVector ws)``,
            ``v_rel y (RefPtr x)``,
            ``v_rel y (Closure n l v x w)``,
            ``v_rel y (Recclosure x1 x2 x3 x4 x5)``] |> LIST_CONJ end
  |> curry save_thm "v_rel_simp";

val v_rel_Boolv = Q.store_thm("v_rel_Boolv[simp]",
  `(v_rel x (Boolv b) ⇔ (x = Boolv b)) ∧
    (v_rel (Boolv b) x ⇔ (x = Boolv b))`,
  Cases_on`b`>>EVAL_TAC>>ntac 2(simp[Once v_rel_cases]))

val v_rel_Unit = Q.store_thm("v_rel_Unit[simp]",
  `(v_rel x Unit ⇔ (x = Unit)) ∧
    (v_rel Unit x ⇔ (x = Unit))`,
  EVAL_TAC>>ntac 2(simp[Once v_rel_cases]))

val env_ok_def = v_rel_cases |> CONJUNCT2

val env_ok_EXTEND = Q.prove(
  `EVERY2 v_rel env1 env2 /\ (l1 = LENGTH env1) /\
    (l1 <= n ==> env_ok m l i env1' env2' (n - l1)) ==>
    env_ok m (l + l1) i (env1 ++ env1') (env2 ++ env2') n`,
  SRW_TAC [] [] \\ SIMP_TAC std_ss [env_ok_def]
  \\ Cases_on `n < LENGTH env1` \\ full_simp_tac(srw_ss())[] THEN1
   (DISJ2_TAC \\ DISJ1_TAC \\ REPEAT STRIP_TAC
    \\ IMP_RES_TAC EVERY2_LENGTH
    \\ full_simp_tac(srw_ss())[rich_listTheory.EL_APPEND1]
    \\ IMP_RES_TAC EVERY2_EL \\ full_simp_tac(srw_ss())[] \\ DECIDE_TAC)
  \\ full_simp_tac(srw_ss())[NOT_LESS]
  \\ full_simp_tac(srw_ss())[env_ok_def]
  THEN1 (DISJ1_TAC \\ DECIDE_TAC)
  THEN1
   (DISJ2_TAC \\ DISJ1_TAC
    \\ IMP_RES_TAC EVERY2_LENGTH
    \\ full_simp_tac(srw_ss())[rich_listTheory.EL_APPEND2]
    \\ DECIDE_TAC)
  \\ DISJ2_TAC \\ DISJ2_TAC \\ Q.EXISTS_TAC `v` \\ full_simp_tac(srw_ss())[]
  \\ IMP_RES_TAC EVERY2_LENGTH
  \\ full_simp_tac(srw_ss())[rich_listTheory.EL_APPEND2]
  \\ `n - (l + LENGTH env2) = n - LENGTH env2 - l` by DECIDE_TAC \\ full_simp_tac(srw_ss())[]
  \\ `LENGTH env2 <= l + LENGTH env2 + v` by DECIDE_TAC
  \\ full_simp_tac(srw_ss())[rich_listTheory.EL_APPEND2]
  \\ `l + LENGTH env2 + v - LENGTH env2 = l + v` by DECIDE_TAC \\ full_simp_tac(srw_ss())[]
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
  state_rel (s:'ffi closSem$state) (t:'ffi closSem$state) <=>
    (s.clock = t.clock) /\
    (s.ffi = t.ffi) /\
    (s.max_app = t.max_app) /\
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

val state_rel_max_app = Q.store_thm("state_rel_max_app",
  `state_rel s t ⇒ s.max_app = t.max_app`,
  rw[state_rel_def]);

(* semantic functions respect relation *)

val v_to_list = Q.prove(
  `!h h'.
      v_rel h h' ==>
      (v_to_list h = NONE /\
       v_to_list h' = NONE) \/
      ?x x'. (v_to_list h = SOME x) /\
             (v_to_list h' = SOME x') /\
             EVERY2 v_rel x x'`,
  HO_MATCH_MP_TAC v_to_list_ind
  \\ full_simp_tac(srw_ss())[v_rel_simp]
  \\ full_simp_tac(srw_ss())[v_to_list_def]
  \\ REPEAT STRIP_TAC \\ SRW_TAC [] []
  \\ full_simp_tac(srw_ss())[v_to_list_def]
  \\ Cases_on `v_to_list h'` \\ full_simp_tac(srw_ss())[]
  \\ Cases_on `v_to_list y'` \\ full_simp_tac(srw_ss())[]
  \\ CCONTR_TAC \\ RES_TAC \\ full_simp_tac(srw_ss())[]
  \\ RES_TAC \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[]);

val do_eq = Q.prove(
  `(!h1 u1 h2 u2.
       v_rel h1 h2 /\ v_rel u1 u2 ==>
       (do_eq h1 u1 = do_eq h2 u2)) /\
    (!h1 u1 h2 u2.
      EVERY2 v_rel h1 h2 /\ EVERY2 v_rel u1 u2 ==>
      (do_eq_list h1 u1 = do_eq_list h2 u2))`,
  HO_MATCH_MP_TAC do_eq_ind
  \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[]
  \\ ONCE_REWRITE_TAC [do_eq_def]
  \\ BasicProvers.EVERY_CASE_TAC \\ full_simp_tac(srw_ss())[v_rel_simp]
  \\ RES_TAC \\ SRW_TAC [] []
  \\ IMP_RES_TAC EVERY2_LENGTH \\ full_simp_tac(srw_ss())[]
  \\ Q.PAT_X_ASSUM `xx = do_eq y y'` (ASSUME_TAC o GSYM)
  \\ full_simp_tac(srw_ss())[]) |> CONJUNCT1 ;

val do_app_IMP_case = Q.prove(
  `(do_app UpdateByte xs s1 = Rval x) ==>
    ?x1 x2 x3. xs = [RefPtr x1; Number x2; Number x3]`,
  full_simp_tac(srw_ss())[do_app_def]
  \\ BasicProvers.EVERY_CASE_TAC \\ full_simp_tac(srw_ss())[]);

val do_app_thm = Q.prove(
  `state_rel s1 t1 /\ EVERY2 v_rel xs ys /\
   (do_app op xs s1 = Rval (v,s2)) ==>
   ?w t2. (do_app op ys t1 = Rval (w,t2)) /\
          v_rel v w /\ state_rel s2 t2`,
  Cases_on `?i. op = EqualInt i`
  THEN1 (fs [] \\ fs [do_app_def] \\ every_case_tac \\ fs [])
  \\ reverse (Cases_on `op`) \\ rpt STRIP_TAC
  \\ TRY (full_simp_tac(srw_ss())[do_app_def] >> NO_TAC)
  THEN1 (* WordToInt *)
   (full_simp_tac(srw_ss())[do_app_def] \\ BasicProvers.EVERY_CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[v_rel_simp] \\ SRW_TAC [] [])
  THEN1 (* WordFromInt *)
   (full_simp_tac(srw_ss())[do_app_def] \\ BasicProvers.EVERY_CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[v_rel_simp] \\ SRW_TAC [] [])
  THEN1 (* WordShift *)
   (full_simp_tac(srw_ss())[do_app_def] \\ BasicProvers.EVERY_CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[v_rel_simp] \\ SRW_TAC [] [])
  THEN1 (* WordOp *)
   (full_simp_tac(srw_ss())[do_app_def] \\ BasicProvers.EVERY_CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[v_rel_simp] \\ SRW_TAC [] [])
  THEN1 (* GreaterEq *)
   (full_simp_tac(srw_ss())[do_app_def] \\ BasicProvers.EVERY_CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[v_rel_simp] \\ SRW_TAC [] [])
  THEN1 (* Greater *)
   (full_simp_tac(srw_ss())[do_app_def] \\ BasicProvers.EVERY_CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[v_rel_simp] \\ SRW_TAC [] [])
  THEN1 (* LessEq *)
   (full_simp_tac(srw_ss())[do_app_def] \\ BasicProvers.EVERY_CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[v_rel_simp] \\ SRW_TAC [] [])
  THEN1 (* Less *)
   (full_simp_tac(srw_ss())[do_app_def] \\ BasicProvers.EVERY_CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[v_rel_simp] \\ SRW_TAC [] [])
  THEN1 (* Mod *)
   (full_simp_tac(srw_ss())[do_app_def] \\ BasicProvers.EVERY_CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[v_rel_simp] \\ SRW_TAC [] [])
  THEN1 (* Div *)
   (full_simp_tac(srw_ss())[do_app_def] \\ BasicProvers.EVERY_CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[v_rel_simp] \\ SRW_TAC [] [])
  THEN1 (* Mult *)
   (full_simp_tac(srw_ss())[do_app_def] \\ BasicProvers.EVERY_CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[v_rel_simp] \\ SRW_TAC [] [])
  THEN1 (* Sub *)
   (full_simp_tac(srw_ss())[do_app_def] \\ BasicProvers.EVERY_CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[v_rel_simp] \\ SRW_TAC [] [])
  THEN1 (* Add *)
   (full_simp_tac(srw_ss())[do_app_def] \\ BasicProvers.EVERY_CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[v_rel_simp] \\ SRW_TAC [] [])
  THEN1 (* Const *)
   (full_simp_tac(srw_ss())[do_app_def] \\ BasicProvers.EVERY_CASE_TAC
    \\ SRW_TAC [] [v_rel_simp] \\ full_simp_tac(srw_ss())[] \\ full_simp_tac(srw_ss())[v_rel_simp])
  THEN1 (* Equal *)
   (full_simp_tac(srw_ss())[do_app_def] \\ BasicProvers.EVERY_CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[v_rel_simp] \\ SRW_TAC [] []
    \\ IMP_RES_TAC do_eq \\ full_simp_tac(srw_ss())[]
    \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[]
    \\ TRY (Cases_on `b`) \\ EVAL_TAC \\ full_simp_tac(srw_ss())[v_rel_simp])
  THEN1 (* FFI *)
   (full_simp_tac(srw_ss())[do_app_def] \\ BasicProvers.EVERY_CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[v_rel_simp] \\ SRW_TAC [] []
    \\ rev_full_simp_tac(srw_ss())[state_rel_def]
    \\ res_tac >> full_simp_tac(srw_ss())[FLOOKUP_UPDATE] >> srw_tac[][] >> full_simp_tac(srw_ss())[] >>
    full_simp_tac(srw_ss())[FLOOKUP_DEF] >> rev_full_simp_tac(srw_ss())[])
  THEN1 (* Label *)
   (full_simp_tac(srw_ss())[do_app_def] \\ BasicProvers.EVERY_CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[v_rel_simp] \\ SRW_TAC [] []
    \\ full_simp_tac(srw_ss())[state_rel_def,FLOOKUP_DEF]
    \\ rev_full_simp_tac(srw_ss())[] \\ full_simp_tac(srw_ss())[]
    \\ TRY (Q.PAT_X_ASSUM `!x. bb ==> bbb` IMP_RES_TAC
            \\ rev_full_simp_tac(srw_ss())[] \\ POP_ASSUM MP_TAC
            \\ full_simp_tac(srw_ss())[]
            \\ REPEAT STRIP_TAC
            \\ IMP_RES_TAC EVERY2_LENGTH \\ full_simp_tac(srw_ss())[] \\ NO_TAC)
    \\ STRIP_TAC \\ Cases_on `n' = n` \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[FAPPLY_FUPDATE_THM] \\ full_simp_tac(srw_ss())[]
    \\ MATCH_MP_TAC EVERY2_LUPDATE_same \\ full_simp_tac(srw_ss())[] >>
    first_x_assum(fn th => first_x_assum(mp_tac o MATCH_MP th)) >>
    simp[])
  THEN1 (* Update *) (
     fs[do_app_def]
     \\ Cases_on`xs`\\fs[]
     \\ Cases_on`t`\\fs[]
     \\ Cases_on`h`\\fs[]
     \\ Cases_on`t'`\\fs[]
     \\ Cases_on`h'`\\fs[]
     \\ Cases_on`t`\\fs[]
     \\ rveq \\ fs[v_rel_simp] \\ rveq
     \\ every_case_tac \\ fs[] \\ rveq
     \\ rfs[state_rel_def]
     \\ res_tac \\ fs[FLOOKUP_UPDATE]
     \\ rw[v_rel_simp]
     \\ imp_res_tac EVERY2_LENGTH \\ fs[]
     \\ MATCH_MP_TAC EVERY2_LUPDATE_same \\ full_simp_tac(srw_ss())[])
  THEN1 (* Deref *) (
    fs[do_app_def]
    \\ Cases_on`xs`\\fs[]
    \\ Cases_on`t`\\fs[]
    \\ Cases_on`h`\\fs[]
    \\ Cases_on`t'`\\fs[]
    \\ Cases_on`h'`\\fs[]
    \\ rveq \\ fs[v_rel_simp] \\ rveq
    \\ every_case_tac \\ fs[] \\ rveq
    \\ rfs[state_rel_def]
    \\ res_tac \\ fs[]
    \\ fs[LIST_REL_EL_EQN] \\ rveq \\ fs[]
    \\ first_x_assum match_mp_tac
    \\ intLib.COOPER_TAC)
  THEN1 (* Ref *)
   (full_simp_tac(srw_ss())[do_app_def] \\ BasicProvers.EVERY_CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[v_rel_simp,LET_DEF] \\ SRW_TAC [] []
    \\ full_simp_tac(srw_ss())[state_rel_def]
    \\ full_simp_tac(srw_ss())[FLOOKUP_DEF,FAPPLY_FUPDATE_THM] \\ STRIP_TAC
    \\ Cases_on `n = (LEAST ptr. ptr NOTIN FDOM t1.refs)` \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[])
  THEN1 (* TagEq *)
   (full_simp_tac(srw_ss())[do_app_def] \\ BasicProvers.EVERY_CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[v_rel_simp] \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[v_rel_simp]
    \\ METIS_TAC[LIST_REL_LENGTH])
  THEN1 (* TagLenEq *)
   (full_simp_tac(srw_ss())[do_app_def] \\ BasicProvers.EVERY_CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[v_rel_simp] \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[v_rel_simp]
    \\ METIS_TAC[LIST_REL_LENGTH])
  THEN1 (* DerefByteVec *)
   (full_simp_tac(srw_ss())[do_app_def] \\ BasicProvers.EVERY_CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[v_rel_simp] \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[v_rel_simp]
    \\ METIS_TAC[LIST_REL_LENGTH])
  THEN1 (* LengthByteVec *)
   (full_simp_tac(srw_ss())[do_app_def] \\ BasicProvers.EVERY_CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[v_rel_simp] \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[v_rel_simp]
    \\ METIS_TAC[LIST_REL_LENGTH])
  THEN1 (* FromListByte *)
   (fs[do_app_def] \\ every_case_tac \\ fs[]
    \\ rpt (qpat_x_assum`$some _ = _`mp_tac)
    \\ rpt (DEEP_INTRO_TAC some_intro) \\ fs[] \\ rw[]
    \\ IMP_RES_TAC v_to_list \\ fs[] \\ rw[]
    \\ fs[LIST_REL_EL_EQN,LIST_EQ_REWRITE,EL_MAP,v_rel_simp]
    \\ rfs[EL_MAP] \\ qexists_tac`x` \\ rw[EL_MAP])
  THEN1 (* FromList *)
   (full_simp_tac(srw_ss())[do_app_def] \\ BasicProvers.EVERY_CASE_TAC
    \\ full_simp_tac(srw_ss())[v_rel_simp] \\ SRW_TAC [] []
    \\ IMP_RES_TAC v_to_list \\ full_simp_tac(srw_ss())[]
    \\ SRW_TAC [] [])
  THEN1 (* UpdateByte *)
   (rpt strip_tac >>IMP_RES_TAC do_app_IMP_case
    \\ full_simp_tac(srw_ss())[v_rel_simp] \\ SRW_TAC [] []
    \\ full_simp_tac(srw_ss())[do_app_def] \\ BasicProvers.EVERY_CASE_TAC
    \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
    \\ full_simp_tac(srw_ss())[state_rel_def] \\ RES_TAC \\ full_simp_tac(srw_ss())[]
    \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[v_rel_simp]
    \\ full_simp_tac(srw_ss())[FLOOKUP_DEF,FAPPLY_FUPDATE_THM]
    \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[]
    \\ RES_TAC \\ full_simp_tac(srw_ss())[] \\ rev_full_simp_tac(srw_ss())[])
  THEN1 (* DerefByte *)
   (full_simp_tac(srw_ss())[do_app_def] \\ BasicProvers.EVERY_CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[v_rel_simp,LET_DEF] \\ SRW_TAC [] []
    \\ full_simp_tac(srw_ss())[state_rel_def] \\ RES_TAC \\ full_simp_tac(srw_ss())[]
    \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[]
    \\ IMP_RES_TAC EVERY2_LENGTH \\ full_simp_tac(srw_ss())[])
  THEN1 (* RefArray *)
   (full_simp_tac(srw_ss())[do_app_def] \\ BasicProvers.EVERY_CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[v_rel_simp,LET_DEF] \\ SRW_TAC [] []
    \\ full_simp_tac(srw_ss())[state_rel_def]
    \\ full_simp_tac(srw_ss())[FLOOKUP_DEF,FAPPLY_FUPDATE_THM] \\ STRIP_TAC
    \\ Cases_on `n = (LEAST ptr. ptr NOTIN FDOM t1.refs)` \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[LIST_REL_REPLICATE_same])
  THEN1 (* RefByte *)
   (full_simp_tac(srw_ss())[do_app_def] \\ BasicProvers.EVERY_CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[v_rel_simp,LET_DEF] \\ SRW_TAC [] []
    \\ full_simp_tac(srw_ss())[state_rel_def]
    \\ full_simp_tac(srw_ss())[FLOOKUP_DEF,FAPPLY_FUPDATE_THM] \\ STRIP_TAC
    \\ Cases_on `n = (LEAST ptr. ptr NOTIN FDOM t1.refs)` \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[])
  THEN1 (* LengthByte *)
   (full_simp_tac(srw_ss())[do_app_def] \\ BasicProvers.EVERY_CASE_TAC
    \\ full_simp_tac(srw_ss())[v_rel_simp] \\ SRW_TAC [] []
    \\ full_simp_tac(srw_ss())[state_rel_def] \\ RES_TAC \\ full_simp_tac(srw_ss())[]
    \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[]
    \\ IMP_RES_TAC EVERY2_LENGTH \\ full_simp_tac(srw_ss())[])
  THEN1 (* Length *)
   (full_simp_tac(srw_ss())[do_app_def] \\ BasicProvers.EVERY_CASE_TAC
    \\ full_simp_tac(srw_ss())[v_rel_simp] \\ SRW_TAC [] []
    \\ full_simp_tac(srw_ss())[state_rel_def] \\ RES_TAC \\ full_simp_tac(srw_ss())[]
    \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[]
    \\ IMP_RES_TAC EVERY2_LENGTH \\ full_simp_tac(srw_ss())[])
  THEN1 (* LengthBlock *)
   (full_simp_tac(srw_ss())[do_app_def] \\ BasicProvers.EVERY_CASE_TAC
    \\ SRW_TAC [] [v_rel_simp] \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[v_rel_simp] \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
    \\ IMP_RES_TAC EVERY2_LENGTH \\ full_simp_tac(srw_ss())[])
  THEN1 (* El *)
   (full_simp_tac(srw_ss())[do_app_def]
    \\ Cases_on`xs`\\fs[]
    \\ Cases_on`t`\\fs[]
    \\ Cases_on`h`\\fs[]
    \\ Cases_on`t'`\\fs[]
    \\ Cases_on`h'`\\fs[]
    \\ BasicProvers.EVERY_CASE_TAC
    \\ SRW_TAC [] [v_rel_simp] \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[v_rel_simp] \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
    \\ IMP_RES_TAC EVERY2_EL
    \\ IMP_RES_TAC EVERY2_LENGTH \\ full_simp_tac(srw_ss())[])
  THEN1 (* Cons *)
   (full_simp_tac(srw_ss())[do_app_def] \\ BasicProvers.EVERY_CASE_TAC
    \\ SRW_TAC [] [v_rel_simp] \\ full_simp_tac(srw_ss())[])
  THEN1 (* SetGlobalsPtr *)
   (full_simp_tac(srw_ss())[do_app_def] \\ BasicProvers.EVERY_CASE_TAC
    \\ SRW_TAC [] [v_rel_simp] \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[state_rel_def,get_global_def] \\ RES_TAC
    \\ full_simp_tac(srw_ss())[quotient_optionTheory.OPTION_REL_def])
  THEN1 (* GlobalsPtr *)
   (full_simp_tac(srw_ss())[do_app_def] \\ BasicProvers.EVERY_CASE_TAC
    \\ SRW_TAC [] [v_rel_simp] \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[state_rel_def,get_global_def] \\ RES_TAC
    \\ full_simp_tac(srw_ss())[quotient_optionTheory.OPTION_REL_def])
  THEN1 (* AllocGlobal *)
   (full_simp_tac(srw_ss())[do_app_def] \\ BasicProvers.EVERY_CASE_TAC
    \\ SRW_TAC [] [v_rel_simp] \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[state_rel_def,get_global_def] \\ RES_TAC
    \\ full_simp_tac(srw_ss())[quotient_optionTheory.OPTION_REL_def])
  THEN1 (* SetGlobal *)
   (full_simp_tac(srw_ss())[do_app_def] \\ BasicProvers.EVERY_CASE_TAC
    \\ SRW_TAC [] [v_rel_simp] \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[state_rel_def,get_global_def] \\ RES_TAC
    \\ IMP_RES_TAC EVERY2_LENGTH \\ full_simp_tac(srw_ss())[]
    \\ IMP_RES_TAC EVERY2_EL
    \\ rev_full_simp_tac(srw_ss())[] \\ POP_ASSUM IMP_RES_TAC
    \\ rev_full_simp_tac(srw_ss())[quotient_optionTheory.OPTION_REL_def]
    \\ MATCH_MP_TAC EVERY2_LUPDATE_same
    \\ full_simp_tac(srw_ss())[quotient_optionTheory.OPTION_REL_def])
  THEN1 (* Global *)
   (full_simp_tac(srw_ss())[do_app_def] \\ BasicProvers.EVERY_CASE_TAC
    \\ SRW_TAC [] [v_rel_simp] \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[state_rel_def,get_global_def] \\ RES_TAC
    \\ IMP_RES_TAC EVERY2_LENGTH \\ full_simp_tac(srw_ss())[]
    \\ IMP_RES_TAC EVERY2_EL
    \\ rev_full_simp_tac(srw_ss())[] \\ POP_ASSUM IMP_RES_TAC
    \\ rev_full_simp_tac(srw_ss())[quotient_optionTheory.OPTION_REL_def]));

val v_rel_Number = prove(
  ``(v_rel x (Number i) <=> (x = Number i)) /\
    (v_rel (Number i) x <=> (x = Number i)) /\
    (v_rel (ByteVector ws) x <=> (x = ByteVector ws)) /\
    (v_rel x (Word64 w) <=> (x = Word64 w)) /\
    (v_rel (Word64 w) x <=> (x = Word64 w))``,
  once_rewrite_tac [v_rel_cases] \\ fs []);

val do_app_err_thm = Q.prove(
  `state_rel s1 t1 /\ EVERY2 v_rel xs ys /\
   do_app op xs s1 = Rerr err /\ (err <> Rabort Rtype_error) ==>
     ?w. (do_app op ys t1 = Rerr w) /\
          exc_rel v_rel err w`,
  srw_tac[][] >>
  imp_res_tac do_app_err >> fsrw_tac[][] >>
  Cases_on `?i. op = EqualInt i`
  THEN1 (rw [] \\ fsrw_tac[][do_app_def] \\ every_case_tac >> fs[])
  \\ Cases_on `op = UpdateByte \/ op = Update` THEN1
   (fs [do_app_def]
    \\ rpt (TOP_CASE_TAC \\ fs [])
    \\ every_case_tac \\ fs[])
  \\ Cases_on `op = DerefByte \/ op = Deref` THEN1
   (fs [do_app_def]
    \\ rpt (TOP_CASE_TAC \\ fs [v_rel_Number])
    \\ every_case_tac \\ fs[])
  \\ Cases_on `op = Add \/ op = Sub \/ op = Mult \/ op = Div \/
               op = Mod \/ op = Less \/ op = LessEq \/
               op = Greater \/ op = GreaterEq` THEN1
   (fs [] \\ fs [do_app_def]
    \\ Cases_on `ys` \\ fs [v_rel_Number] \\ rveq \\ fs []
    \\ Cases_on `t` \\ fs [v_rel_Number] \\ rveq \\ fs []
    \\ Cases_on `h` \\ fs [v_rel_Number] \\ rveq \\ fs []
    \\ Cases_on `t'` \\ fs [v_rel_Number] \\ rveq \\ fs []
    \\ Cases_on `h'` \\ fs [v_rel_Number] \\ rveq \\ fs []
    \\ every_case_tac \\ fs[])
  \\ `?f. f op = ARB` by (qexists_tac `K ARB` \\ fs [])
  \\ Cases_on`op`>>fsrw_tac[][do_app_def]
  \\ every_case_tac >> fs[]);

(* compiler correctness *)

val lookup_EL_shifted_env = Q.prove(
  `!y n k. n < LENGTH y /\ ALL_DISTINCT y ==>
            (lookup (EL n y) (shifted_env k y) = SOME (k + n))`,
  Induct \\ full_simp_tac(srw_ss())[] \\ Cases_on `n` \\ full_simp_tac(srw_ss())[shifted_env_def,lookup_insert]
  \\ SRW_TAC [] [ADD1,AC ADD_COMM ADD_ASSOC]
  \\ full_simp_tac(srw_ss())[MEM_EL] \\ METIS_TAC []);

val env_ok_shifted_env = Q.prove(
  `env_ok m l i env env2 k /\ MEM k live /\ ALL_DISTINCT live /\
    (lookup_vars (MAP (get_var m l i) (FILTER (\n. n < m + l) live)) env2 =
      SOME x) ==>
    env_ok (m + l) 0 (shifted_env 0 (FILTER (\n. n < m + l) live)) env x k`,
  REPEAT STRIP_TAC
  \\ Q.ABBREV_TAC `y = FILTER (\n. n < m + l) live`
  \\ `ALL_DISTINCT y` by
       (UNABBREV_ALL_TAC \\ MATCH_MP_TAC FILTER_ALL_DISTINCT \\ full_simp_tac(srw_ss())[])
  \\ Cases_on `~(k < m + l)` THEN1 (full_simp_tac(srw_ss())[env_ok_def,NOT_LESS] \\ DECIDE_TAC)
  \\ full_simp_tac(srw_ss())[]
  \\ `MEM k y` by (UNABBREV_ALL_TAC \\ full_simp_tac(srw_ss())[MEM_FILTER])
  \\ POP_ASSUM MP_TAC
  \\ simp [MEM_EL] \\ STRIP_TAC
  \\ POP_ASSUM (ASSUME_TAC o GSYM)
  \\ Q.PAT_X_ASSUM `MEM k live` (K ALL_TAC)
  \\ Q.PAT_X_ASSUM `Abbrev vvv` (K ALL_TAC)
  \\ `(EL n (MAP (get_var m l i) y) = get_var m l i k) /\
      n < LENGTH (MAP (get_var m l i) y)` by full_simp_tac(srw_ss())[EL_MAP]
  \\ Q.ABBREV_TAC `ys = (MAP (get_var m l i) y)`
  \\ MP_TAC lookup_vars_MEM \\ full_simp_tac(srw_ss())[] \\ STRIP_TAC
  \\ `v_rel (EL k env) (EL (get_var m l i k) env2)` by
   (full_simp_tac(srw_ss())[env_ok_def] THEN1 (`F` by DECIDE_TAC) \\ full_simp_tac(srw_ss())[get_var_def]
    \\ `~(k < l)` by DECIDE_TAC \\ full_simp_tac(srw_ss())[tlookup_def])
  \\ Q.PAT_X_ASSUM `EL n x = yy` (ASSUME_TAC o GSYM) \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[env_ok_def] \\ DISJ2_TAC
  \\ TRY (`k < l + m` by DECIDE_TAC) \\ full_simp_tac(srw_ss())[]
  \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[lookup_EL_shifted_env]
  \\ IMP_RES_TAC lookup_vars_SOME \\ full_simp_tac(srw_ss())[]);

val EL_shift_free = Q.prove(
  `!fns index.
     index < LENGTH fns ==>
     ([EL index (shift (FST (free fns)) l m i)] =
      (shift (FST (free [EL index fns])) l m i))`,
  Induct \\ full_simp_tac(srw_ss())[] \\ REPEAT STRIP_TAC
  \\ ONCE_REWRITE_TAC [free_CONS]
  \\ SIMP_TAC std_ss [Once shift_CONS]
  \\ Cases_on `index` \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[LET_DEF,free_def]
  \\ REPEAT (AP_TERM_TAC ORELSE AP_THM_TAC)
  \\ full_simp_tac(srw_ss())[SING_HD,LENGTH_FST_free]);

val shift_correct = Q.prove(
  `(!xs env (s1:'ffi closSem$state) env' t1 res s2 m l i.
     (evaluate (xs,env,s1) = (res,s2)) /\ res <> Rerr (Rabort Rtype_error) /\
     (LENGTH env = m + l) /\
     fv_set xs SUBSET env_ok m l i env env' /\
     every_Fn_vs_NONE xs ∧ FEVERY (λp. every_Fn_vs_NONE [SND (SND p)]) s1.code ∧
     state_rel s1 t1 ==>
     ?res' t2.
        (evaluate (shift (FST (free xs)) m l i,env',t1) = (res',t2)) /\
        result_rel (LIST_REL v_rel) v_rel res res' /\
        state_rel s2 t2) /\
   (!loc_opt f args (s1:'ffi closSem$state) res s2 f' args' s1'.
     (evaluate_app loc_opt f args s1 = (res,s2)) /\
     v_rel f f' /\ EVERY2 v_rel args args' /\
     FEVERY (λp. every_Fn_vs_NONE [SND (SND p)]) s1.code ∧
     state_rel s1 s1' /\ res <> Rerr (Rabort Rtype_error) ==>
     ?res' s2'.
       (evaluate_app loc_opt f' args' s1' = (res',s2')) /\
       result_rel (LIST_REL v_rel) v_rel res res' /\
       state_rel s2 s2')`,
  HO_MATCH_MP_TAC (evaluate_ind |> Q.SPEC `λ(x1,x2,x3). P0 x1 x2 x3` |> Q.GEN `P0`
                             |> SIMP_RULE std_ss [FORALL_PROD])
  \\ REPEAT STRIP_TAC
  THEN1 (* NIL *)
   (full_simp_tac(srw_ss())[free_def,shift_def,evaluate_def]
    \\ SRW_TAC [] [])
  THEN1 (* CONS *)
   (full_simp_tac(srw_ss())[free_def,evaluate_def]
    \\ `?y1 l1. free [x] = ([y1],l1)` by METIS_TAC [PAIR,free_SING]
    \\ `?y2 l2. free (y::xs) = (y2,l2)` by METIS_TAC [PAIR] \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[LET_DEF]
    \\ `?r1 s2. evaluate ([x],env,s1) = (r1,s2)` by METIS_TAC [PAIR] \\ full_simp_tac(srw_ss())[]
    \\ `?y3 y4. y2 = y3::y4` by
     (IMP_RES_TAC free_LENGTH
      \\ Cases_on `y2` \\ full_simp_tac(srw_ss())[has_var_def,fv_def,fv1_thm])
    \\ full_simp_tac(srw_ss())[shift_def]
    \\ Cases_on `r1` \\ full_simp_tac(srw_ss())[]
    \\ SRW_TAC [] [markerTheory.Abbrev_def]
    \\ SRW_TAC [] [markerTheory.Abbrev_def]
    \\ `?t. shift [y1] m l i = [t]` by METIS_TAC [shift_SING]
    \\ full_simp_tac(srw_ss())[] \\ ONCE_REWRITE_TAC [evaluate_CONS]
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`env'`,`t1`])
    \\ REPEAT STRIP_TAC \\ POP_ASSUM (MP_TAC o Q.SPECL [`m`,`l`,`i`])
    \\ `fv_set [x] SUBSET env_ok m l i env env' /\
        fv_set (y::xs) SUBSET env_ok m l i env env'` by
      (full_simp_tac(srw_ss())[SUBSET_DEF,IN_DEF,fv_def,fv1_thm])
    \\ full_simp_tac(srw_ss())[] \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[]
    \\ `?r2 s3. evaluate (y::xs,env,s2') = (r2,s3)` by METIS_TAC [PAIR] \\ full_simp_tac(srw_ss())[]
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`env'`,`t2`])
    \\ imp_res_tac evaluate_const
    \\ Cases_on `r2` \\ full_simp_tac(srw_ss())[]
    \\ REPEAT STRIP_TAC \\ POP_ASSUM (MP_TAC o Q.SPECL [`m`,`l`,`i`]) \\ full_simp_tac(srw_ss())[]
    \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[]
    \\ IMP_RES_TAC evaluate_SING \\ full_simp_tac(srw_ss())[])
  THEN1 (* Var *)
   (Cases_on `n < LENGTH env`
    \\ full_simp_tac(srw_ss())[free_def,evaluate_def,shift_def]
    \\ full_simp_tac(srw_ss())[SUBSET_DEF,IN_DEF,fv_def,fv1_thm]
    \\ Cases_on `l + m <= n`
    THEN1 (full_simp_tac(srw_ss())[env_ok_def] \\ rev_full_simp_tac(srw_ss())[] \\ `F` by DECIDE_TAC)
    \\ reverse (`get_var m l i n < LENGTH env' /\
        v_rel (EL n env) (EL (get_var m l i n) env')` by ALL_TAC)
    THEN1 (full_simp_tac(srw_ss())[] \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[])
    \\ full_simp_tac(srw_ss())[get_var_def,env_ok_def]
    \\ Cases_on `n < l` \\ full_simp_tac(srw_ss())[tlookup_def]
    \\ `F` by DECIDE_TAC)
  THEN1 (* If *)
   (full_simp_tac(srw_ss())[free_def]
    \\ `?y1 l1. free [x1] = ([y1],l1)` by METIS_TAC [PAIR,free_SING]
    \\ `?y2 l2. free [x2] = ([y2],l2)` by METIS_TAC [PAIR,free_SING]
    \\ `?y3 l3. free [x3] = ([y3],l3)` by METIS_TAC [PAIR,free_SING]
    \\ full_simp_tac(srw_ss())[LET_DEF,shift_def,evaluate_def]
    \\ `?r1 s2. evaluate ([x1],env,s1) = (r1,s2)` by METIS_TAC [PAIR] \\ full_simp_tac(srw_ss())[]
    \\ `fv_set [x1] SUBSET env_ok m l i env env' /\
        fv_set [x2] SUBSET env_ok m l i env env' /\
        fv_set [x3] SUBSET env_ok m l i env env'` by
      (full_simp_tac(srw_ss())[SUBSET_DEF,IN_DEF,fv_def,fv1_thm])
    \\ `r1 <> Rerr(Rabort Rtype_error)` by (REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[])
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`env'`,`t1`,`m`,`l`,`i`]) \\ full_simp_tac(srw_ss())[]
    \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `r1` \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
    \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
    \\ IMP_RES_TAC evaluate_SING \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
    \\ imp_res_tac evaluate_const
    \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
    \\ full_simp_tac(srw_ss())[v_rel_simp] \\ SRW_TAC [] []
    \\ Cases_on `r1 = Boolv T` \\ full_simp_tac(srw_ss())[v_rel_simp]
    \\ Cases_on `r1 = Boolv F` \\ full_simp_tac(srw_ss())[v_rel_simp])
  THEN1 (* Let *)
   (full_simp_tac(srw_ss())[free_def]
    \\ `?y1 l1. free xs = (y1,l1)` by METIS_TAC [PAIR,free_SING]
    \\ `?y2 l2. free [x2] = ([y2],l2)` by METIS_TAC [PAIR,free_SING]
    \\ full_simp_tac(srw_ss())[LET_DEF,shift_def,evaluate_def]
    \\ `?r1 s2. evaluate (xs,env,s1) = (r1,s2)` by METIS_TAC [PAIR] \\ full_simp_tac(srw_ss())[]
    \\ `fv_set xs SUBSET env_ok m l i env env'` by
      (full_simp_tac(srw_ss())[SUBSET_DEF,IN_DEF,fv_def,fv1_thm])
    \\ `r1 <> Rerr(Rabort Rtype_error)` by (REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[])
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`env'`,`t1`,`m`,`l`,`i`]) \\ full_simp_tac(srw_ss())[]
    \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `r1` \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
    \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
    \\ FIRST_X_ASSUM (qspecl_then[`v'++env'`,`t2`,
         `m`,`l + LENGTH y1`,`i`]mp_tac)
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
    \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[] \\ full_simp_tac(srw_ss())[SUBSET_DEF,IN_DEF] \\ REPEAT STRIP_TAC
    \\ IMP_RES_TAC free_LENGTH
    \\ IMP_RES_TAC EVERY2_LENGTH
    \\ IMP_RES_TAC evaluate_IMP_LENGTH
    \\ IMP_RES_TAC evaluate_const
    \\ full_simp_tac(srw_ss())[shift_LENGTH_LEMMA,AC ADD_COMM ADD_ASSOC]
    \\ MATCH_MP_TAC env_ok_EXTEND \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[fv_def,fv1_thm]
    \\ REPEAT STRIP_TAC
    \\ Q.PAT_X_ASSUM `!x.bbb` (K ALL_TAC)
    \\ FIRST_X_ASSUM MATCH_MP_TAC
    \\ `x - LENGTH v' + LENGTH v' = x` by DECIDE_TAC \\ full_simp_tac(srw_ss())[])
  THEN1 (* Raise *)
   (full_simp_tac(srw_ss())[free_def]
    \\ `?y1 l1. free [x1] = ([y1],l1)` by METIS_TAC [PAIR,free_SING]
    \\ full_simp_tac(srw_ss())[LET_DEF,shift_def,evaluate_def]
    \\ `?r1 s2. evaluate ([x1],env,s1) = (r1,s2)` by METIS_TAC [PAIR] \\ full_simp_tac(srw_ss())[]
    \\ `fv_set [x1] SUBSET env_ok m l i env env'` by
      (full_simp_tac(srw_ss())[SUBSET_DEF,IN_DEF,fv_def,fv1_thm])
    \\ `r1 <> Rerr(Rabort Rtype_error)` by (REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[])
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`env'`,`t1`,`m`,`l`,`i`]) \\ full_simp_tac(srw_ss())[]
    \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `r1` \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
    \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
    \\ IMP_RES_TAC evaluate_SING \\ full_simp_tac(srw_ss())[])
  THEN1 (* Handle *)
   (full_simp_tac(srw_ss())[free_def]
    \\ `?y1 l1. free [x1] = ([y1],l1)` by METIS_TAC [PAIR,free_SING]
    \\ `?y2 l2. free [x2] = ([y2],l2)` by METIS_TAC [PAIR,free_SING]
    \\ full_simp_tac(srw_ss())[LET_DEF,shift_def,evaluate_def]
    \\ `?r1 s2. evaluate ([x1],env,s1) = (r1,s2)` by METIS_TAC [PAIR] \\ full_simp_tac(srw_ss())[]
    \\ `fv_set [x1] SUBSET env_ok m l i env env'` by
      (full_simp_tac(srw_ss())[SUBSET_DEF,IN_DEF,fv_def,fv1_thm])
    \\ `r1 <> Rerr(Rabort Rtype_error)` by (REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[])
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`env'`,`t1`,`m`,`l`,`i`]) \\ full_simp_tac(srw_ss())[]
    \\ imp_res_tac evaluate_const
    \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `r1` \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
    \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
    \\ Cases_on `e` \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
    \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`v'::env'`,`t2`,`m`,`l+1`,`i`]) \\ full_simp_tac(srw_ss())[]
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[AC ADD_ASSOC ADD_COMM,ADD1]
    \\ full_simp_tac(srw_ss())[SUBSET_DEF,IN_DEF] \\ REPEAT STRIP_TAC
    \\ MATCH_MP_TAC env_ok_cons \\ full_simp_tac(srw_ss())[]
    \\ RES_TAC \\ REPEAT STRIP_TAC
    \\ full_simp_tac(srw_ss())[fv_def,fv1_thm]
    \\ Cases_on `x` \\ full_simp_tac(srw_ss())[]
    \\ Q.PAT_X_ASSUM `!x.bbb` (K ALL_TAC)
    \\ FIRST_X_ASSUM MATCH_MP_TAC \\ full_simp_tac(srw_ss())[ADD1])
  THEN1 (* Op *)
   (full_simp_tac(srw_ss())[free_def]
    \\ `?y1 l1. free xs = (y1,l1)` by METIS_TAC [PAIR,free_SING]
    \\ full_simp_tac(srw_ss())[LET_DEF,shift_def,evaluate_def]
    \\ `?r1 s2. evaluate (xs,env,s1) = (r1,s2)` by METIS_TAC [PAIR] \\ full_simp_tac(srw_ss())[]
    \\ `fv_set xs SUBSET env_ok m l i env env'` by
      (full_simp_tac(srw_ss())[SUBSET_DEF,IN_DEF,fv_def,fv1_thm])
    \\ `r1 <> Rerr(Rabort Rtype_error)` by (REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[])
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`env'`,`t1`,`m`,`l`,`i`]) \\ full_simp_tac(srw_ss())[]
    \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `r1` \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
    \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] [] >>
    last_x_assum mp_tac >>
    reverse BasicProvers.CASE_TAC >- (
      srw_tac[][] >>
      IMP_RES_TAC do_app_err >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
      imp_res_tac EVERY2_REVERSE >>
      IMP_RES_TAC do_app_err_thm >> rev_full_simp_tac(srw_ss())[] ) >>
    BasicProvers.CASE_TAC >> srw_tac[][] >>
    IMP_RES_TAC EVERY2_REVERSE
    \\ IMP_RES_TAC do_app_thm \\ full_simp_tac(srw_ss())[])
  THEN1 (* Fn *)
   (full_simp_tac(srw_ss())[free_def,evaluate_def]
    \\ full_simp_tac(srw_ss())[clos_env_def]
    \\ SRW_TAC [] [] \\ SRW_TAC [] [markerTheory.Abbrev_def]
    \\ `?y1 l1. free [exp] = ([y1],l1)` by METIS_TAC [PAIR,free_SING]
    \\ Cases_on `num_args <= s1.max_app` \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `num_args <> 0` \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
    \\ full_simp_tac(srw_ss())[shift_def,LET_DEF,evaluate_def,clos_env_def,
           PULL_EXISTS,v_rel_simp]
    \\ Q.ABBREV_TAC `live =
          FILTER (\n. n < m + l) (vars_to_list (Shift num_args l1))`
    \\ full_simp_tac(srw_ss())[MAP_MAP_o,o_DEF]
    \\ Cases_on `lookup_vars (MAP (get_var m l i) live) env'`
    \\ full_simp_tac(srw_ss())[] THEN1
     (full_simp_tac(srw_ss())[SUBSET_DEF,IN_DEF,fv_def,fv1_thm]
      \\ full_simp_tac(srw_ss())[lookup_vars_NONE] \\ UNABBREV_ALL_TAC
      \\ full_simp_tac(srw_ss())[MEM_FILTER,MEM_vars_to_list,MEM_MAP]
      \\ MP_TAC (Q.SPEC`[exp]` free_thm)
      \\ full_simp_tac(srw_ss())[LET_DEF] \\ CCONTR_TAC \\ full_simp_tac(srw_ss())[] \\ RES_TAC
      \\ SRW_TAC [] []
      \\ full_simp_tac(srw_ss())[env_ok_def] \\ rev_full_simp_tac(srw_ss())[]
      \\ full_simp_tac(srw_ss())[get_var_def,tlookup_def]
      \\ DECIDE_TAC)
    \\ reverse IF_CASES_TAC >- (
      imp_res_tac state_rel_max_app \\ fs[])
    \\ simp_tac (srw_ss())[]
    \\ Q.EXISTS_TAC `shifted_env 0 live` \\ full_simp_tac(srw_ss())[]
    \\ REPEAT STRIP_TAC \\ Cases_on `n` \\ full_simp_tac(srw_ss())[]
    \\ MP_TAC (Q.SPEC `[exp]` free_thm)
    \\ full_simp_tac(srw_ss())[LET_DEF] \\ STRIP_TAC
    \\ full_simp_tac(srw_ss())[SUBSET_DEF,IN_DEF,fv_def,fv1_thm]
    \\ full_simp_tac(srw_ss())[ADD1] \\ RES_TAC \\ UNABBREV_ALL_TAC
    \\ Q.ABBREV_TAC `live = vars_to_list (Shift num_args l1)`
    \\ MATCH_MP_TAC (GEN_ALL env_ok_shifted_env)
    \\ Q.LIST_EXISTS_TAC [`i`,`env'`] \\ full_simp_tac(srw_ss())[]
    \\ `n' + 1 = (n' + 1 - num_args) + num_args` by DECIDE_TAC
    \\ STRIP_TAC THEN1 METIS_TAC []
    \\ STRIP_TAC THEN1 (UNABBREV_ALL_TAC \\ full_simp_tac(srw_ss())[MEM_vars_to_list] \\ METIS_TAC [])
    \\ UNABBREV_ALL_TAC \\ full_simp_tac(srw_ss())[ALL_DISTINCT_vars_to_list])
  THEN1 (* Letrec *)
   (full_simp_tac(srw_ss())[free_def,evaluate_def]
    \\ full_simp_tac(srw_ss())[clos_env_def]
    \\ SRW_TAC [] [] \\ SRW_TAC [] [markerTheory.Abbrev_def]
    \\ `EVERY (\(num_args,e). num_args <= s1.max_app /\
                              num_args <> 0) fns` by
      (CCONTR_TAC \\ FULL_SIMP_TAC std_ss [])
    \\ Cases_on `build_recc F loc env names fns` \\ full_simp_tac(srw_ss())[]
    \\ Q.ABBREV_TAC `rec_res = MAP
                        (\(n,x).
                           (let (c,l) = free [x] in
                              ((n,HD c),Shift (n + LENGTH fns) l))) fns`
    \\ `?y2 l2. free [exp] = ([y2],l2)` by METIS_TAC [PAIR,free_SING]
    \\ full_simp_tac(srw_ss())[shift_def,LET_DEF,evaluate_def,build_recc_def,clos_env_def,
           shift_LENGTH_LEMMA]
    \\ Q.PAT_ABBREV_TAC `ev = EVERY PP xx`
    \\ `ev` by
     (UNABBREV_ALL_TAC \\ full_simp_tac(srw_ss())[MAP_MAP_o,o_DEF]
      \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) \\ full_simp_tac(srw_ss())[EVERY_MAP]
      \\ full_simp_tac(srw_ss())[EVERY_MEM,FORALL_PROD] \\ REPEAT STRIP_TAC \\ RES_TAC
      \\ imp_res_tac state_rel_max_app \\ fs[])
    \\ full_simp_tac(srw_ss())[] \\ POP_ASSUM (K ALL_TAC) \\ POP_ASSUM (K ALL_TAC)
    \\ Q.ABBREV_TAC `live = FILTER (\n. n < m + l)
          (vars_to_list (list_mk_Union (MAP SND rec_res)))`
    \\ Cases_on `lookup_vars (MAP (get_var m l i) live) env'`
    \\ full_simp_tac(srw_ss())[] THEN1
     (full_simp_tac(srw_ss())[SUBSET_DEF,IN_DEF,fv_def,fv1_thm]
      \\ full_simp_tac(srw_ss())[lookup_vars_NONE] \\ UNABBREV_ALL_TAC
      \\ full_simp_tac(srw_ss())[MEM_FILTER,MEM_vars_to_list,MEM_MAP]
      \\ full_simp_tac(srw_ss())[EXISTS_MEM,PULL_EXISTS,EXISTS_PROD]
      \\ NTAC 3 (POP_ASSUM MP_TAC)
      \\ full_simp_tac(srw_ss())[MAP_MAP_o,o_DEF,MEM_MAP,EXISTS_PROD]
      \\ REPEAT STRIP_TAC
      \\ Q.MATCH_ASSUM_RENAME_TAC `MEM (p_11,p_21) fns`
      \\ Cases_on `free [p_21]` \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[]
      \\ MP_TAC (Q.SPEC`[p_21]` free_thm)
      \\ full_simp_tac(srw_ss())[LET_DEF] \\ CCONTR_TAC
      \\ full_simp_tac(srw_ss())[AC ADD_ASSOC ADD_COMM] \\ RES_TAC
      \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[]
      \\ full_simp_tac(srw_ss())[env_ok_def] \\ rev_full_simp_tac(srw_ss())[]
      \\ full_simp_tac(srw_ss())[get_var_def,tlookup_def]
      \\ DECIDE_TAC)
    \\ FIRST_X_ASSUM MATCH_MP_TAC
    \\ IMP_RES_TAC free_LENGTH \\ full_simp_tac(srw_ss())[]
    \\ `LENGTH rec_res = LENGTH x` by ALL_TAC THEN1
      (UNABBREV_ALL_TAC \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[])
    \\ STRIP_TAC THEN1 (full_simp_tac(srw_ss())[AC ADD_COMM ADD_ASSOC,Abbr`rec_res`])
    \\ full_simp_tac(srw_ss())[SUBSET_DEF,IN_DEF,fv_def,fv1_thm]
    \\ REPEAT STRIP_TAC
    \\ MATCH_MP_TAC (env_ok_EXTEND |> GEN_ALL) \\ full_simp_tac(srw_ss())[]
    \\ reverse (REPEAT STRIP_TAC) THEN1
     (FIRST_X_ASSUM MATCH_MP_TAC \\ DISJ2_TAC
      \\ UNABBREV_ALL_TAC \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[]
      \\ IMP_RES_TAC (DECIDE ``n <= m:num <=> (m - n + n = m)``) \\ full_simp_tac(srw_ss())[])
    \\ SRW_TAC [] []
    \\ full_simp_tac(srw_ss())[LIST_REL_GENLIST] \\ REPEAT STRIP_TAC
    \\ full_simp_tac(srw_ss())[v_rel_simp]
    \\ Q.UNABBREV_TAC `rec_res`
    \\ full_simp_tac(srw_ss())[EVERY2_MAP]
    \\ MATCH_MP_TAC listTheory.EVERY2_refl
    \\ REPEAT STRIP_TAC
    \\ PairCases_on `x` \\ full_simp_tac(srw_ss())[]
    \\ `?y1 y2. free [x1] = ([y1],y2)` by METIS_TAC [free_SING,PAIR]
    \\ full_simp_tac(srw_ss())[] \\ Q.EXISTS_TAC `shifted_env 0 live`
    \\ STRIP_TAC THEN1 SIMP_TAC std_ss [AC ADD_COMM ADD_ASSOC]
    \\ reverse strip_tac >- (
         full_simp_tac(srw_ss())[Once every_Fn_vs_NONE_EVERY,EVERY_MAP,EVERY_MEM] >>
         res_tac >> full_simp_tac(srw_ss())[] )
    \\ REPEAT STRIP_TAC
    \\ UNABBREV_ALL_TAC
    \\ MATCH_MP_TAC (GEN_ALL env_ok_shifted_env)
    \\ Q.LIST_EXISTS_TAC [`i`,`env'`] \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[AC ADD_COMM ADD_ASSOC,ALL_DISTINCT_vars_to_list]
    \\ full_simp_tac(srw_ss())[MEM_vars_to_list]
    \\ STRIP_TAC THEN1
     (FIRST_X_ASSUM MATCH_MP_TAC \\ DISJ1_TAC
      \\ full_simp_tac(srw_ss())[EXISTS_MEM,EXISTS_PROD]
      \\ Q.LIST_EXISTS_TAC [`x0`,`x1`] \\ full_simp_tac(srw_ss())[]
      \\ full_simp_tac(srw_ss())[MEM_EL,PULL_EXISTS]
      \\ `x0 + (n - (x0 + LENGTH fns) + LENGTH fns) = n` by DECIDE_TAC
      \\ METIS_TAC [])
    \\ full_simp_tac(srw_ss())[EXISTS_MEM,EXISTS_PROD,PULL_EXISTS]
    \\ full_simp_tac(srw_ss())[MEM_MAP,EXISTS_PROD,PULL_EXISTS]
    \\ CONV_TAC (DEPTH_CONV (PairRules.PBETA_CONV)) \\ full_simp_tac(srw_ss())[]
    \\ Q.LIST_EXISTS_TAC [`x0`,`x1`] \\ full_simp_tac(srw_ss())[]
    \\ MP_TAC (Q.SPEC `[x1]` free_thm)
    \\ IMP_RES_TAC (DECIDE ``n <= m:num <=> (m - n + n = m)``)
    \\ full_simp_tac(srw_ss())[LET_DEF] \\ STRIP_TAC \\ full_simp_tac(srw_ss())[])
  THEN1 (* App *)
   (full_simp_tac(srw_ss())[free_def]
    \\ `?y1 l1. free xs = (y1,l1)` by METIS_TAC [PAIR]
    \\ `?y2 l2. free [x1] = ([y2],l2)` by METIS_TAC [PAIR,free_SING]
    \\ full_simp_tac(srw_ss())[LET_DEF,shift_def,evaluate_def]
    \\ `?r1 s2. evaluate (xs,env,s1) = (r1,s2)` by METIS_TAC [PAIR] \\ full_simp_tac(srw_ss())[]
    \\ `?r2 s3. evaluate ([x1],env,s2') = (r2,s3)` by METIS_TAC [PAIR] \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[shift_LENGTH_LEMMA]
    \\ IMP_RES_TAC free_LENGTH
    \\ Cases_on `LENGTH xs > 0` \\ full_simp_tac(srw_ss())[]
    \\ `fv_set xs SUBSET env_ok m l i env env' /\
        fv_set [x1] SUBSET env_ok m l i env env'` by
      (full_simp_tac(srw_ss())[SUBSET_DEF,IN_DEF,fv_def,fv1_thm])
    \\ `r1 <> Rerr(Rabort Rtype_error)` by (REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[])
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`env'`,`t1`,`m`,`l`,`i`]) \\ full_simp_tac(srw_ss())[]
    \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `r1` \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
    \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
    \\ `?r2 s2. evaluate ([x1],env,s1) = (r2,s2)` by METIS_TAC [PAIR] \\ full_simp_tac(srw_ss())[]
    \\ `r2 <> Rerr(Rabort Rtype_error)` by (REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[])
    \\ imp_res_tac evaluate_const
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`env'`,`t2`,`m`,`l`,`i`]) \\ full_simp_tac(srw_ss())[]
    \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `r2` \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
    \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
    \\ IMP_RES_TAC evaluate_SING \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] [])
  THEN1 (* Tick *)
   (full_simp_tac(srw_ss())[free_def,evaluate_def]
    \\ `?y1 l1. free [x] = ([y1],l1)` by METIS_TAC [PAIR,free_SING]
    \\ full_simp_tac(srw_ss())[LET_DEF,shift_def,evaluate_def]
    \\ `t1.clock = s1.clock` by full_simp_tac(srw_ss())[state_rel_def] \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `s1.clock = 0` \\ full_simp_tac(srw_ss())[]
    \\ SRW_TAC [] []
    \\ `fv_set [x] SUBSET env_ok m l i env env'` by
      (full_simp_tac(srw_ss())[SUBSET_DEF,IN_DEF,fv_def,fv1_thm])
    \\ imp_res_tac evaluate_const \\ full_simp_tac(srw_ss())[Once dec_clock_def]
    \\ `state_rel (dec_clock 1 s1) (dec_clock 1 t1)` by
          full_simp_tac(srw_ss())[state_rel_def,dec_clock_def] \\ RES_TAC
    \\ STRIP_ASSUME_TAC (shift_SING |> Q.INST [`x`|->`y1`]) \\ full_simp_tac(srw_ss())[])
  THEN1 (* Call *)
   (full_simp_tac(srw_ss())[free_def]
    \\ `?y1 l1. free xs = (y1,l1)` by METIS_TAC [PAIR,free_SING]
    \\ full_simp_tac(srw_ss())[LET_DEF,shift_def,evaluate_def]
    \\ `?r1 s2. evaluate (xs,env,s1) = (r1,s2)` by METIS_TAC [PAIR] \\ full_simp_tac(srw_ss())[]
    \\ `fv_set xs SUBSET env_ok m l i env env'` by
      (full_simp_tac(srw_ss())[SUBSET_DEF,IN_DEF,fv_def,fv1_thm])
    \\ `r1 <> Rerr(Rabort Rtype_error)` by (REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[])
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`env'`,`t1`,`m`,`l`,`i`]) \\ full_simp_tac(srw_ss())[]
    \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `r1` \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
    \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
    \\ Cases_on `find_code dest a s2'.code` \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `x` \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[find_code_def]
    \\ Cases_on `FLOOKUP s2'.code dest` \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `x` \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
    \\ `?c2. shift (FST (free [r])) 0 (LENGTH a) LN = [c2] /\
             FLOOKUP t2.code dest = SOME (LENGTH a,c2)` by
         (full_simp_tac(srw_ss())[state_rel_def] \\ RES_TAC \\ NO_TAC)
    \\ full_simp_tac(srw_ss())[] \\ IMP_RES_TAC EVERY2_LENGTH \\ full_simp_tac(srw_ss())[]
    \\ `s2'.clock = t2.clock` by full_simp_tac(srw_ss())[state_rel_def] \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `t2.clock < ticks+1` \\ full_simp_tac(srw_ss())[]
    THEN1 (SRW_TAC [] [] \\ fs[state_rel_def])
    \\ FIRST_X_ASSUM (qspecl_then[`v'`,`dec_clock (ticks+1) t2`,`0`,
         `LENGTH v'`,`LN`]mp_tac)
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
     (imp_res_tac evaluate_const
      \\ full_simp_tac(srw_ss())[] \\ reverse (REPEAT STRIP_TAC)
      THEN1 (full_simp_tac(srw_ss())[state_rel_def,dec_clock_def])
      THEN1 (full_simp_tac(srw_ss())[state_rel_def,dec_clock_def])
      THEN1 ( full_simp_tac(srw_ss())[FEVERY_ALL_FLOOKUP] >> res_tac >> full_simp_tac(srw_ss())[] )
      \\ full_simp_tac(srw_ss())[SUBSET_DEF,IN_DEF] \\ REPEAT STRIP_TAC
      \\ SIMP_TAC std_ss [env_ok_def]
      \\ reverse (Cases_on `x < LENGTH v'`) \\ full_simp_tac(srw_ss())[] THEN1 DECIDE_TAC
      \\ IMP_RES_TAC EVERY2_EL \\ METIS_TAC [])
    \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[] \\ rev_full_simp_tac(srw_ss())[])
  THEN1 (* evaluate_app NIL *)
   (full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
    \\ full_simp_tac(srw_ss())[evaluate_def] \\ SRW_TAC [] [])
  THEN1 (* evaluate_app CONS *)
   (full_simp_tac(srw_ss())[evaluate_def]
    \\ Cases_on `dest_closure s1.max_app loc_opt f (v42::v43)` \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `x` \\ full_simp_tac(srw_ss())[]
    THEN1 (* Partial_app *)
     (reverse (`?z. (dest_closure s1'.max_app loc_opt f' (y::ys) = SOME (Partial_app z)) /\
           v_rel v z` by ALL_TAC) THEN1
       (full_simp_tac(srw_ss())[] \\ IMP_RES_TAC EVERY2_LENGTH \\ full_simp_tac(srw_ss())[]
        \\ `s1'.clock = s1.clock` by full_simp_tac(srw_ss())[state_rel_def] \\ full_simp_tac(srw_ss())[]
        \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
        \\ full_simp_tac(srw_ss())[state_rel_def,dec_clock_def])
      \\ full_simp_tac(srw_ss())[dest_closure_def]
      \\ Cases_on `f` \\ full_simp_tac(srw_ss())[]
      \\ TRY (Cases_on `EL n l1`) \\ full_simp_tac(srw_ss())[LET_DEF]
      \\ full_simp_tac(srw_ss())[METIS_PROVE [] ``((if b then x1 else x2) = SOME y) <=>
              (b /\ (x1 = SOME y)) \/ (~b /\ (x2 = SOME y))``]
      \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[v_rel_simp]
      \\ IMP_RES_TAC EVERY2_LENGTH \\ full_simp_tac(srw_ss())[]
      THEN1
       (full_simp_tac(srw_ss())[PULL_EXISTS] \\ Q.EXISTS_TAC `i` \\ full_simp_tac(srw_ss())[]
        \\ REPEAT STRIP_TAC
        \\ TRY (MATCH_MP_TAC rich_listTheory.EVERY2_APPEND_suff \\ full_simp_tac(srw_ss())[])
        \\ imp_res_tac state_rel_max_app
        \\ rev_full_simp_tac(srw_ss())[] \\ fs[])
      \\ Cases_on `EL n cs'` \\ full_simp_tac(srw_ss())[]
      \\ full_simp_tac(srw_ss())[METIS_PROVE [] ``((if b then x1 else x2) = SOME y) <=>
              (b /\ (x1 = SOME y)) \/ (~b /\ (x2 = SOME y))``]
      \\ `n < LENGTH l1` by full_simp_tac(srw_ss())[]
      \\ IMP_RES_TAC EVERY2_EL \\ rev_full_simp_tac(srw_ss())[]
      \\ imp_res_tac state_rel_max_app \\ fs[]
      \\ MATCH_MP_TAC rich_listTheory.EVERY2_APPEND_suff \\ full_simp_tac(srw_ss())[])
    (* Full_app *)
    \\ Cases_on `f` \\ full_simp_tac(srw_ss())[dest_closure_def]
    \\ TRY (Cases_on `EL n l1`) \\ full_simp_tac(srw_ss())[LET_DEF]
    \\ TRY (Cases_on `EL n cs'`) \\ full_simp_tac(srw_ss())[LET_DEF]
    \\ full_simp_tac(srw_ss())[METIS_PROVE [] ``((if b then x1 else x2) = SOME y) <=>
            (b /\ (x1 = SOME y)) \/ (~b /\ (x2 = SOME y))``]
    THEN1
     (SRW_TAC [] [] \\ full_simp_tac(srw_ss())[v_rel_simp]
      \\ IMP_RES_TAC EVERY2_LENGTH \\ full_simp_tac(srw_ss())[]
      \\ `s1'.clock = s1.clock` by full_simp_tac(srw_ss())[state_rel_def] \\ full_simp_tac(srw_ss())[]
      \\ `s1'.max_app = s1.max_app` by fs[state_rel_def]
      \\ full_simp_tac(srw_ss())[METIS_PROVE [] ``((if b then x1 else x2) = y) <=>
              (b /\ (x1 = y)) \/ (~b /\ (x2 = y))``]
      \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[]
      \\ TRY (full_simp_tac(srw_ss())[state_rel_def] \\ NO_TAC) \\ rev_full_simp_tac(srw_ss())[]
      \\ qpat_x_assum`_ = (res,_)`mp_tac
      \\ Q.PAT_ABBREV_TAC `env3 =
         REVERSE (TAKE (n - LENGTH vals') (REVERSE _ ++ [_])) ++
            l' ++ l0'`
      \\ Q.PAT_ABBREV_TAC `n3 =
           (SUC (LENGTH ys) - (LENGTH ys + 1 - (n - LENGTH vals')))`
      \\ strip_tac
      \\ Cases_on `evaluate ([e],env3,dec_clock n3 s1)` \\ full_simp_tac(srw_ss())[]
      \\ `q <> Rerr(Rabort Rtype_error)` by (REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[])
      \\ Q.PAT_ABBREV_TAC `env3' =
           REVERSE (TAKE (n - LENGTH vals') (REVERSE ys ++ [y])) ++
           vals' ++ env'`
      \\ FIRST_X_ASSUM (qspecl_then [`env3'`,`dec_clock n3 s1'`,
           `LENGTH (l0':closSem$v list)`,`n`,`i`]mp_tac)
      \\ imp_res_tac evaluate_const \\ full_simp_tac(srw_ss())[Once dec_clock_def]
      \\ full_simp_tac(srw_ss())[] \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
      THEN1
       (REPEAT STRIP_TAC
        \\ TRY (full_simp_tac(srw_ss())[state_rel_def,dec_clock_def] \\ NO_TAC)
        THEN1 (full_simp_tac(srw_ss())[LENGTH_TAKE_EQ] \\ SRW_TAC [] [] \\ DECIDE_TAC)
        \\ full_simp_tac(srw_ss())[SUBSET_DEF,IN_DEF] \\ REPEAT STRIP_TAC
        \\ Q.UNABBREV_TAC `env3`
        \\ Q.UNABBREV_TAC `env3'`
        \\ MATCH_MP_TAC env_ok_some
        \\ Q.EXISTS_TAC `0` \\ full_simp_tac(srw_ss())[]
        \\ MATCH_MP_TAC (METIS_PROVE []
             ``b1 /\ (b1 ==> b2) ==> b1 /\ b2``)
        \\ full_simp_tac(srw_ss())[] \\ REPEAT STRIP_TAC
        THEN1 (full_simp_tac(srw_ss())[LENGTH_TAKE_EQ] \\ SRW_TAC [] [] \\ DECIDE_TAC)
        \\ MATCH_MP_TAC rich_listTheory.EVERY2_APPEND_suff \\ full_simp_tac(srw_ss())[]
        \\ MATCH_MP_TAC EVERY2_REVERSE
        \\ MATCH_MP_TAC EVERY2_TAKE
        \\ MATCH_MP_TAC rich_listTheory.EVERY2_APPEND_suff \\ full_simp_tac(srw_ss())[]
        \\ MATCH_MP_TAC EVERY2_REVERSE \\ full_simp_tac(srw_ss())[])
      \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[]
      \\ reverse (Cases_on `q`) \\ full_simp_tac(srw_ss())[]
      \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[]
      \\ reverse (Cases_on `a`) \\ full_simp_tac(srw_ss())[]
      \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[]
      \\ reverse (Cases_on `t`) \\ full_simp_tac(srw_ss())[]
      \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[]
      \\ Q.MATCH_ASSUM_RENAME_TAC `v_rel h h'`
      \\ FIRST_X_ASSUM MATCH_MP_TAC \\ full_simp_tac(srw_ss())[]
      \\ MATCH_MP_TAC EVERY2_REVERSE
      \\ MATCH_MP_TAC EVERY2_DROP
      \\ MATCH_MP_TAC rich_listTheory.EVERY2_APPEND_suff \\ full_simp_tac(srw_ss())[]
      \\ MATCH_MP_TAC EVERY2_REVERSE \\ full_simp_tac(srw_ss())[])
    \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[v_rel_simp]
    \\ Cases_on `EL n cs'` \\ full_simp_tac(srw_ss())[]
    \\ IMP_RES_TAC EVERY2_LENGTH \\ full_simp_tac(srw_ss())[]
    \\ `q' = q` by
     (`n < LENGTH l1` by full_simp_tac(srw_ss())[]
      \\ IMP_RES_TAC EVERY2_EL \\ rev_full_simp_tac(srw_ss())[]) \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[METIS_PROVE [] ``((if b then x1 else x2) = y) <=>
              (b /\ (x1 = y)) \/ (~b /\ (x2 = y))``]
    \\ `s1'.clock = s1.clock` by full_simp_tac(srw_ss())[state_rel_def] \\ full_simp_tac(srw_ss())[]
    \\ `s1'.max_app = s1.max_app` by full_simp_tac(srw_ss())[state_rel_def] \\ full_simp_tac(srw_ss())[]
    THEN1 (SRW_TAC [] [] \\ full_simp_tac(srw_ss())[state_rel_def])
    \\ qpat_x_assum`_ = (res,_)`mp_tac
    \\ Q.PAT_ABBREV_TAC `env3 =
         REVERSE (TAKE (q - LENGTH vals') (REVERSE _ ++ [_])) ++
            l' ++ GENLIST (Recclosure o' [] l0' l1) (LENGTH cs') ++ l0'`
    \\ Q.PAT_ABBREV_TAC `n3 =
           (SUC (LENGTH ys) - (LENGTH ys + 1 - (q - LENGTH vals')))`
    \\ strip_tac
    \\ Cases_on `evaluate ([e],env3,dec_clock n3 s1)` \\ full_simp_tac(srw_ss())[]
    \\ `q'' <> Rerr(Rabort Rtype_error)` by (REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[])
    \\ Q.ABBREV_TAC `env3' =
           REVERSE (TAKE (q - LENGTH vals') (REVERSE ys ++ [y])) ++ vals' ++
           GENLIST (Recclosure o' [] env' cs') (LENGTH cs') ++ env'`
    \\ `n < LENGTH l1` by full_simp_tac(srw_ss())[]
    \\ IMP_RES_TAC EVERY2_EL
    \\ rev_full_simp_tac(srw_ss())[]
    \\ FIRST_X_ASSUM (qspecl_then [`env3'`,`dec_clock n3 s1'`,
           `LENGTH (l0':closSem$v list)`,
           `LENGTH (cs') + q`,`i`]mp_tac)
    \\ full_simp_tac(srw_ss())[] \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
    THEN1
     (REPEAT STRIP_TAC
      \\ TRY (full_simp_tac(srw_ss())[state_rel_def,dec_clock_def] \\ NO_TAC)
      THEN1 (full_simp_tac(srw_ss())[LENGTH_TAKE_EQ] \\ SRW_TAC [] [] \\ DECIDE_TAC)
      \\ full_simp_tac(srw_ss())[SUBSET_DEF,IN_DEF] \\ REPEAT STRIP_TAC
      \\ Q.UNABBREV_TAC `env3`
      \\ Q.UNABBREV_TAC `env3'`
      \\ MATCH_MP_TAC env_ok_some
      \\ Q.EXISTS_TAC `0` \\ full_simp_tac(srw_ss())[]
      \\ MATCH_MP_TAC (METIS_PROVE []
           ``b1 /\ (b1 ==> b2) ==> b1 /\ b2``)
      \\ full_simp_tac(srw_ss())[] \\ REPEAT STRIP_TAC
      THEN1 (full_simp_tac(srw_ss())[LENGTH_TAKE_EQ] \\ SRW_TAC [] [] \\ DECIDE_TAC)
      \\ TRY (full_simp_tac(srw_ss())[AC ADD_COMM ADD_ASSOC]
        \\ FIRST_X_ASSUM MATCH_MP_TAC \\ full_simp_tac(srw_ss())[]
        \\ full_simp_tac(srw_ss())[AC ADD_COMM ADD_ASSOC] \\ NO_TAC)
      \\ MATCH_MP_TAC rich_listTheory.EVERY2_APPEND_suff \\ full_simp_tac(srw_ss())[]
      \\ REPEAT STRIP_TAC THEN1
       (MATCH_MP_TAC rich_listTheory.EVERY2_APPEND_suff \\ full_simp_tac(srw_ss())[]
        \\ MATCH_MP_TAC EVERY2_REVERSE
        \\ MATCH_MP_TAC EVERY2_TAKE
        \\ MATCH_MP_TAC rich_listTheory.EVERY2_APPEND_suff \\ full_simp_tac(srw_ss())[]
        \\ MATCH_MP_TAC EVERY2_REVERSE \\ full_simp_tac(srw_ss())[])
      \\ full_simp_tac(srw_ss())[LIST_REL_GENLIST]
      \\ full_simp_tac(srw_ss())[v_rel_simp] \\ REPEAT STRIP_TAC
      \\ full_simp_tac(srw_ss())[])
    \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[]
    \\ reverse (Cases_on `q''`) \\ full_simp_tac(srw_ss())[]
    \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[]
    \\ reverse (Cases_on `a`) \\ full_simp_tac(srw_ss())[]
    \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[]
    \\ reverse (Cases_on `t`) \\ full_simp_tac(srw_ss())[]
    \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[]
    \\ Q.MATCH_ASSUM_RENAME_TAC `v_rel h h'`
    \\ FIRST_X_ASSUM MATCH_MP_TAC \\ full_simp_tac(srw_ss())[]
    \\ imp_res_tac evaluate_const \\ full_simp_tac(srw_ss())[dec_clock_def]
    \\ MATCH_MP_TAC EVERY2_REVERSE
    \\ MATCH_MP_TAC EVERY2_DROP
    \\ MATCH_MP_TAC rich_listTheory.EVERY2_APPEND_suff \\ full_simp_tac(srw_ss())[]
    \\ MATCH_MP_TAC EVERY2_REVERSE \\ full_simp_tac(srw_ss())[]));

val env_set_default = Q.prove(
  `x SUBSET env_ok 0 0 LN [] env'`,
  full_simp_tac(srw_ss())[SUBSET_DEF,IN_DEF,env_ok_def]);

val annotate_correct = save_thm("annotate_correct",
  shift_correct |> CONJUNCT1
  |> SPEC_ALL |> Q.INST [`m`|->`0`,`l`|->`0`,`i`|->`LN`,`env`|->`[]`]
  |> REWRITE_RULE [GSYM annotate_def,env_set_default,LENGTH,ADD_0]);

(* more correctness properties *)

val every_Fn_vs_SOME_shift = Q.store_thm("every_Fn_vs_SOME_shift[simp]",
  `∀a b c d. every_Fn_vs_SOME (shift a b c d)`,
  ho_match_mp_tac shift_ind >> srw_tac[][shift_def] >> srw_tac[][] >>
  rpt(qpat_x_assum`Abbrev _`(strip_assume_tac o SYM o REWRITE_RULE[markerTheory.Abbrev_def])) >>
  imp_res_tac shift_SING >>
  full_simp_tac(srw_ss())[Once every_Fn_vs_SOME_EVERY] >>
  srw_tac[][] >>
  simp[MAP_MAP_o,o_DEF,UNCURRY,EVERY_MAP] >>
  simp[EVERY_MEM,FORALL_PROD] >>
  simp[Once every_Fn_vs_SOME_EVERY]);

val every_Fn_vs_SOME_annotate = Q.store_thm("every_Fn_vs_SOME_annotate[simp]",
  `every_Fn_vs_SOME (annotate n es)`, srw_tac[][annotate_def]);

val every_Fn_SOME_shift = Q.store_thm("every_Fn_SOME_shift[simp]",
  `∀a b c d. every_Fn_SOME (shift a b c d) ⇔ every_Fn_SOME a`,
  ho_match_mp_tac shift_ind >> srw_tac[][shift_def] >> srw_tac[][] >>
  rpt(qpat_x_assum`Abbrev _`(strip_assume_tac o SYM o REWRITE_RULE[markerTheory.Abbrev_def])) >>
  imp_res_tac shift_SING >>
  full_simp_tac(srw_ss())[Once every_Fn_SOME_EVERY] >>
  srw_tac[][] >>
  simp[MAP_MAP_o,o_DEF,UNCURRY,EVERY_MAP] >>
  simp[EVERY_MEM,FORALL_PROD] >>
  simp[Once every_Fn_SOME_EVERY] >>
  ONCE_REWRITE_TAC[every_Fn_SOME_EVERY] >>
  simp[EVERY_MAP,EVERY_MEM,FORALL_PROD]);

val every_Fn_SOME_free = Q.store_thm("every_Fn_SOME_free[simp]",
  `∀es. every_Fn_SOME (FST (free es)) = every_Fn_SOME es`,
  ho_match_mp_tac free_ind >>
  srw_tac[][free_def] >> full_simp_tac(srw_ss())[] >>
  imp_res_tac free_SING >> full_simp_tac(srw_ss())[] >>
  unabbrev_all_tac >> full_simp_tac(srw_ss())[] >>
  simp[MAP_MAP_o,UNCURRY,o_DEF] >>
  rpt (pop_assum mp_tac) >>
  ONCE_REWRITE_TAC[every_Fn_SOME_EVERY] >>
  srw_tac[][EVERY_MAP] >>
  srw_tac[][EVERY_MEM] >>
  rpt(AP_TERM_TAC ORELSE AP_THM_TAC) >>
  simp[FUN_EQ_THM] >>
  full_simp_tac(srw_ss())[GSYM every_Fn_SOME_EVERY] >>
  metis_tac[free_SING,HD,FST,PAIR]);

val every_Fn_SOME_annotate = Q.store_thm("every_Fn_SOME_annotate[simp]",
  `every_Fn_SOME (annotate n es) ⇔ every_Fn_SOME es`, srw_tac[][annotate_def]);

val IF_MAP_EQ = MAP_EQ_f |> SPEC_ALL |> EQ_IMP_RULE |> snd;

val shift_code_locs = Q.prove(
  `!xs env s1 env'. code_locs (shift xs env s1 env') = code_locs xs`,
  ho_match_mp_tac shift_ind
  \\ simp[shift_def,code_locs_def,shift_LENGTH_LEMMA]
  \\ srw_tac[][code_locs_append]
  \\ full_simp_tac(srw_ss())[MAP_MAP_o,o_DEF]
  \\ ONCE_REWRITE_TAC [code_locs_map]
  \\ AP_TERM_TAC \\ MATCH_MP_TAC IF_MAP_EQ \\ full_simp_tac(srw_ss())[FORALL_PROD])

val free_code_locs = Q.prove(
  `!xs. code_locs (FST (free xs)) = code_locs xs`,
  ho_match_mp_tac free_ind >>
  simp[free_def,code_locs_def,UNCURRY] >> srw_tac[][]
  \\ Cases_on `free [x]` \\ full_simp_tac(srw_ss())[code_locs_append,HD_FST_free]
  \\ Cases_on `free [x1]` \\ full_simp_tac(srw_ss())[code_locs_append,HD_FST_free]
  \\ Cases_on `free [x2]` \\ full_simp_tac(srw_ss())[code_locs_append,HD_FST_free]
  \\ Cases_on `free xs` \\ full_simp_tac(srw_ss())[code_locs_append,HD_FST_free]
  \\ full_simp_tac(srw_ss())[MAP_MAP_o,o_DEF]
  \\ ONCE_REWRITE_TAC [code_locs_map] \\ AP_TERM_TAC
  \\ MATCH_MP_TAC IF_MAP_EQ \\ full_simp_tac(srw_ss())[FORALL_PROD,HD_FST_free]
  \\ REPEAT STRIP_TAC \\ RES_TAC \\ full_simp_tac(srw_ss())[])

val annotate_code_locs = Q.store_thm("annotate_code_locs",
  `!n ls. code_locs (annotate n ls) = code_locs ls`,
  srw_tac[][annotate_def,shift_code_locs,free_code_locs])

val _ = export_theory()
