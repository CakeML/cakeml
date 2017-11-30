open preamble
     db_varsTheory
     closSemTheory closPropsTheory
     clos_annotateTheory;

val _ = new_theory"clos_annotateProof";

val _ = temp_bring_to_front_overload"do_app"{Name="do_app",Thy="closSem"};

val EVERY2_EL = LIST_REL_EL_EQN |> SPEC_ALL |> EQ_IMP_RULE |> fst
                |> UNDISCH |> CONJUNCT2 |> DISCH_ALL;

(* alternative definition of free_vars (fv) function *)

val alt_fv_def = Define `
  alt_fv n xs = has_var n (SND (alt_free xs))`;

val alt_free_thm = Q.store_thm("alt_free_thm",
  `!xs.
     let (ys,l) = alt_free xs in
       !n. (alt_fv n xs = has_var n l)`,
  fs [alt_fv_def,UNCURRY]);

val alt_fv = store_thm("alt_fv",
  ``(∀n. alt_fv n [] ⇔ F) ∧
    (∀y xs x n. alt_fv n (x::y::xs) ⇔ alt_fv n [x] ∨ alt_fv n (y::xs)) ∧
    (∀v0 v n. alt_fv n [Var v0 v] ⇔ n = v) ∧
    (∀x3 x2 x1 v1 n.
      alt_fv n [If v1 x1 x2 x3] ⇔ alt_fv n [x1] ∨ alt_fv n [x2] ∨ alt_fv n [x3]) ∧
    (∀xs x2 v2 n.
      alt_fv n [Let v2 xs x2] ⇔
        if clos_annotate$no_overlap (LENGTH xs) (SND (alt_free [x2])) /\ EVERY pure xs then
          alt_fv (n + LENGTH xs) [x2]
        else
          alt_fv n xs ∨ alt_fv (n + LENGTH xs) [x2]) ∧
    (∀x1 v3 n. alt_fv n [Raise v3 x1] ⇔ alt_fv n [x1]) ∧
    (∀x1 v4 n. alt_fv n [Tick v4 x1] ⇔ alt_fv n [x1]) ∧
    (∀xs v5 op n. alt_fv n [Op v5 op xs] ⇔ alt_fv n xs) ∧
    (∀x2 x1 v6 n loc_opt.
       alt_fv n [App v6 loc_opt x1 x2] ⇔ alt_fv n [x1] ∨ alt_fv n x2) ∧
    (∀x1 vs v7 num_args n loc.
       alt_fv n [Fn v7 loc vs num_args x1] ⇔ alt_fv (n + num_args) [x1]) ∧
    (∀x1 vs v8 n loc fns.
       alt_fv n [Letrec v8 loc vs fns x1] ⇔
       if clos_annotate$no_overlap (LENGTH fns) (SND (alt_free [x1])) then
         alt_fv (n + LENGTH fns) [x1]
       else
         EXISTS (λ(num_args,x). alt_fv (n + num_args + LENGTH fns) [x]) fns ∨
         alt_fv (n + LENGTH fns) [x1]) ∧
    (∀x2 x1 v9 n. alt_fv n [Handle v9 x1 x2] ⇔ alt_fv n [x1] ∨ alt_fv (n + 1) [x2]) ∧
    ∀xs v10 ticks n dest. alt_fv n [Call v10 ticks dest xs] ⇔ alt_fv n xs``,
  rw [alt_fv_def,alt_free_def]
  \\ rpt (pairarg_tac \\ fs [])
  \\ Cases_on `has_var (n + LENGTH fns) l2` \\ fs []
  \\ fs [EXISTS_MAP,UNCURRY] \\ fs []
  \\ TRY (rw [] \\ fs [EXISTS_MEM,EVERY_MEM] \\ res_tac \\ fs [] \\ NO_TAC)
  \\ AP_THM_TAC \\ AP_TERM_TAC
  \\ fs [FUN_EQ_THM,FORALL_PROD]);

val alt_fv_nil = Q.store_thm("alt_fv_nil[simp]",
  `alt_fv v [] ⇔ F`, rw[alt_fv])

val alt_fv1_def = Define`alt_fv1 v e = alt_fv v [e]`;
val alt_fv1_intro = save_thm("alt_fv1_intro[simp]",GSYM alt_fv1_def)
val alt_fv1_thm =
  alt_fv |> SIMP_RULE (srw_ss())[]
  |> curry save_thm "alt_fv1_thm"

val alt_fv_cons = Q.store_thm("alt_fv_cons[simp]",
  `alt_fv v (x::xs) ⇔ alt_fv1 v x ∨ alt_fv v xs`,
  Cases_on `xs` \\ fs [alt_fv]);

val alt_fv_REPLICATE = Q.store_thm(
  "alt_fv_REPLICATE[simp]",
  `alt_fv n (REPLICATE m e) ⇔ 0 < m ∧ alt_fv1 n e`,
  Induct_on `m` >> simp[REPLICATE, alt_fv,alt_fv1_thm] >>
  simp[] >> metis_tac[]);

(* value relation *)

val _ = overload_on("alt_fv_set",``λx y. alt_fv y x``);

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
  ((shift (FST (alt_free [c])) m num_args i = [c']) /\
   (!n. alt_fv_set [c] n /\ num_args <= n ==>
        env_ok m 0 i env env' (n - num_args)) /\
   every_Fn_vs_NONE [c] ∧
   (LENGTH env = m) /\ EVERY2 v_rel vals vals' ==>
   v_rel (Closure p vals env num_args c) (Closure p vals' env' num_args c'))
  /\
  (EVERY2 ( \ (num_args,c1) (num_args',c1').
     ?m i.
       (num_args' = num_args) /\
       (shift (FST (alt_free [c1])) m (LENGTH cs + num_args) i = [c1']) /\
       (!n. alt_fv_set [c1] n /\ num_args + LENGTH cs <= n ==>
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

val env_ok_EXTEND_IGNORE = Q.prove(
  `(LENGTH env2 = LENGTH env1) /\ LENGTH env1 <= n /\ l1 = LENGTH env1 /\
   env_ok m l i env1' env2' (n - l1) ==>
   env_ok m (l + l1) i (env1 ++ env1') (env2 ++ env2') n`,
  SRW_TAC [] [] \\ SIMP_TAC std_ss [env_ok_def] \\ fs []
  \\ Cases_on `n < LENGTH env1` \\ fs []
  \\ full_simp_tac(srw_ss())[NOT_LESS]
  \\ full_simp_tac(srw_ss())[env_ok_def]
  \\ fs [rich_listTheory.EL_APPEND2]);

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
        (shift (FST (alt_free [c])) 0 arity LN = [c2]) /\
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
  Cases_on `op = ConfigGC`
  THEN1 (fs [do_app_cases_val] \\ rw [] \\ fs [v_rel_simp])
  \\ Cases_on `?i. op = EqualInt i`
  THEN1 (fs [] \\ fs [do_app_def] \\ every_case_tac \\ fs [])
  \\ reverse (Cases_on `op`) \\ rpt STRIP_TAC
  \\ TRY (full_simp_tac(srw_ss())[do_app_def] >> NO_TAC)
  THEN1 (* LessConstSmall *)
   (fs [do_app_cases_val] \\ rveq \\ fs [PULL_EXISTS]
    \\ BasicProvers.EVERY_CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ rveq \\ fs [v_rel_simp] \\ SRW_TAC [] [])
  THEN1 (* BoundsCheckByte *)
   (fs [do_app_cases_val] \\ rveq \\ fs [PULL_EXISTS]
    \\ rveq \\ fs [v_rel_simp] \\ SRW_TAC [] []
    \\ rfs[state_rel_def]
    \\ res_tac \\ fs[])
  THEN1 (* BoundsCheckArray *)
   (fs [do_app_cases_val] \\ rveq \\ fs [PULL_EXISTS]
    \\ rveq \\ fs [v_rel_simp] \\ SRW_TAC [] []
    \\ rfs[state_rel_def]
    \\ res_tac \\ fs[]
    \\ imp_res_tac LIST_REL_LENGTH \\ fs [])
  THEN1 (* BoundsCheckBlock *)
   (fs [do_app_cases_val] \\ rveq \\ fs [PULL_EXISTS]
    \\ rveq \\ fs [v_rel_simp] \\ SRW_TAC [] []
    \\ imp_res_tac LIST_REL_LENGTH \\ fs [])
  THEN1 (* FP_bop *)
   (fs [do_app_cases_val] \\ rveq \\ fs [PULL_EXISTS]
    \\ rveq \\ fs [v_rel_simp] \\ SRW_TAC [] [])
  THEN1 (* FP_uop *)
   (fs [do_app_cases_val] \\ rveq \\ fs [PULL_EXISTS]
    \\ rveq \\ fs [v_rel_simp] \\ SRW_TAC [] [])
  THEN1 (* FP_cmp *)
   (fs [do_app_cases_val] \\ rveq \\ fs [PULL_EXISTS]
    \\ rveq \\ fs [v_rel_simp] \\ SRW_TAC [] [])
  THEN1 (* WordFromWord *)
   (full_simp_tac(srw_ss())[do_app_def] \\ BasicProvers.EVERY_CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[v_rel_simp] \\ SRW_TAC [] [])
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
   (fs [do_app_cases_val] \\ rveq \\ fs [PULL_EXISTS]
    \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[v_rel_simp] \\ SRW_TAC [] [])
  THEN1 (* GreaterEq *)
   (fs [do_app_cases_val] \\ rveq \\ fs [PULL_EXISTS]
    \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[v_rel_simp] \\ SRW_TAC [] [])
  THEN1 (* Greater *)
   (fs [do_app_cases_val] \\ rveq \\ fs [PULL_EXISTS]
    \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[v_rel_simp] \\ SRW_TAC [] [])
  THEN1 (* LessEq *)
   (fs [do_app_cases_val] \\ rveq \\ fs [PULL_EXISTS]
    \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[v_rel_simp] \\ SRW_TAC [] [])
  THEN1 (* Less *)
   (fs [do_app_cases_val] \\ rveq \\ fs [PULL_EXISTS]
    \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[v_rel_simp] \\ SRW_TAC [] [])
  THEN1 (* Mod *)
   (fs [do_app_cases_val] \\ rveq \\ fs [PULL_EXISTS]
    \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[v_rel_simp] \\ SRW_TAC [] [])
  THEN1 (* Div *)
   (fs [do_app_cases_val] \\ rveq \\ fs [PULL_EXISTS]
    \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[v_rel_simp] \\ SRW_TAC [] [])
  THEN1 (* Mult *)
   (fs [do_app_cases_val] \\ rveq \\ fs [PULL_EXISTS]
    \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[v_rel_simp] \\ SRW_TAC [] [])
  THEN1 (* Sub *)
   (fs [do_app_cases_val] \\ rveq \\ fs [PULL_EXISTS]
    \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[v_rel_simp] \\ SRW_TAC [] [])
  THEN1 (* Add *)
   (fs [do_app_cases_val] \\ rveq \\ fs [PULL_EXISTS]
    \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[v_rel_simp] \\ SRW_TAC [] [])
  THEN1 (* Const *)
   (fs [do_app_cases_val] \\ rveq \\ fs [PULL_EXISTS]
    \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[v_rel_simp] \\ SRW_TAC [] [])
  THEN1 (* Equal *)
   (fs [do_app_cases_val] \\ rveq \\ fs [PULL_EXISTS]
    \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[v_rel_simp] \\ SRW_TAC [] []
    \\ IMP_RES_TAC do_eq \\ full_simp_tac(srw_ss())[])
  THEN1 (* FFI *)
   (full_simp_tac(srw_ss())[do_app_def] \\ BasicProvers.EVERY_CASE_TAC
    \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[v_rel_simp] \\ SRW_TAC [] []
    \\ rev_full_simp_tac(srw_ss())[state_rel_def]
    \\ res_tac \\ full_simp_tac(srw_ss())[FLOOKUP_UPDATE] \\ srw_tac[][]
    \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[FLOOKUP_DEF] \\ rev_full_simp_tac(srw_ss())[])
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
    \\ rfs[EL_MAP,EVERY_MEM] \\ qexists_tac`x` \\ rw[EL_MAP])
  THEN1 (* String *)
    (fs[do_app_def] \\ every_case_tac \\ fs[] \\ rw[v_rel_simp])
  THEN1 (* FromList *)
   (full_simp_tac(srw_ss())[do_app_def] \\ BasicProvers.EVERY_CASE_TAC
    \\ full_simp_tac(srw_ss())[v_rel_simp] \\ SRW_TAC [] []
    \\ IMP_RES_TAC v_to_list \\ full_simp_tac(srw_ss())[]
    \\ SRW_TAC [] [])
  THEN1 (* CopyByte *)
    (fs[do_app_def,case_eq_thms,bool_case_eq]
     \\ rw[] \\ fs[v_rel_simp,PULL_EXISTS]
     \\ fs[state_rel_def]
     \\ res_tac \\ fs[v_rel_simp]
     \\ fs[FLOOKUP_UPDATE]
     \\ rw[] \\ rw[v_rel_simp] )
  THEN1 (* ConcatByteVec *)
   (fs[do_app_def] \\
    TOP_CASE_TAC \\ fs[] \\ rveq \\ fs[] \\
    TOP_CASE_TAC \\ fs[] \\ rveq \\ fs[] \\
    imp_res_tac v_to_list \\ fs[] \\ rw[v_rel_simp] \\
    qpat_x_assum`_ = Rval _ `mp_tac \\
    DEEP_INTRO_TAC some_intro \\ fs[] \\
    ntac 3 strip_tac \\ rveq \\ fs[] \\
    fs[EVERY2_MAP,v_rel_simp] \\
    DEEP_INTRO_TAC some_intro \\ fs[PULL_EXISTS] \\
    rename1`LIST_REL _ l1 l2` \\
    map_every qexists_tac[`l1`] \\
    reverse conj_asm2_tac >- (
      fs[LIST_EQ_REWRITE,EL_MAP,LIST_REL_EL_EQN,state_rel_def] ) \\
    simp[] \\ fs[state_rel_def,FLOOKUP_UPDATE] \\ rw[] \\
    rw[] \\ fs[] \\
    imp_res_tac INJ_MAP_EQ \\ fs[INJ_DEF])
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
    \\ full_simp_tac(srw_ss())[v_rel_simp]
    \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
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
    \\ full_simp_tac(srw_ss())[v_rel_simp]
    \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
    \\ IMP_RES_TAC EVERY2_EL
    \\ IMP_RES_TAC EVERY2_LENGTH \\ full_simp_tac(srw_ss())[])
  THEN1 (* ConsExtend *)
   (
    fs [do_app_cases_val] >>
    fs [] >>
    rw [] >>
    fs [v_rel_simp] >>
    rw [PULL_EXISTS] >>
    metis_tac [EVERY2_APPEND_suff, EVERY2_TAKE, EVERY2_DROP, LIST_REL_LENGTH])
  THEN1 (* Cons *)
   (full_simp_tac(srw_ss())[do_app_def] \\ BasicProvers.EVERY_CASE_TAC
    \\ SRW_TAC [] [v_rel_simp] \\ full_simp_tac(srw_ss())[])
  THEN1 (* SetGlobalsPtr *)
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
  \\ Cases_on `err` \\ fs []
  \\ fs [do_app_cases_err]
  \\ Cases_on `a` \\ fs []);

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
    \\ `~(k < l)` by DECIDE_TAC \\ full_simp_tac(srw_ss())[zlookup_def])
  \\ Q.PAT_X_ASSUM `EL n x = yy` (ASSUME_TAC o GSYM) \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[env_ok_def] \\ DISJ2_TAC
  \\ TRY (`k < l + m` by DECIDE_TAC) \\ full_simp_tac(srw_ss())[]
  \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[lookup_EL_shifted_env]
  \\ IMP_RES_TAC lookup_vars_SOME \\ full_simp_tac(srw_ss())[]);

val EL_shift_alt_free = Q.prove(
  `!fns index.
     index < LENGTH fns ==>
     ([EL index (shift (FST (alt_free fns)) l m i)] =
      (shift (FST (alt_free [EL index fns])) l m i))`,
  Induct \\ full_simp_tac(srw_ss())[] \\ REPEAT STRIP_TAC
  \\ ONCE_REWRITE_TAC [alt_free_CONS]
  \\ SIMP_TAC std_ss [Once shift_CONS]
  \\ Cases_on `index` \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[LET_DEF,alt_free_def]
  \\ REPEAT (AP_TERM_TAC ORELSE AP_THM_TAC)
  \\ full_simp_tac(srw_ss())[SING_HD,LENGTH_FST_alt_free]);

val FOLDR_mk_Union = prove(
  ``!ys aux l.
      FOLDR (λ(x,l) (ts,alt_frees). (x::ts,mk_Union l alt_frees)) (aux,l) ys =
      (MAP FST ys ++ aux, FOLDR mk_Union l (MAP SND ys))``,
  Induct \\ fs [FORALL_PROD]);

(*
val MAPi_MAPi = store_thm("MAPi_MAPi",
  ``!xs. MAPi f (MAPi g xs) = MAPi (\i x. f i (g i x)) xs``,
  ...);
*)

val evaluate_shift_REPLICATE_const_0 =
  store_thm("evaluate_shift_REPLICATE_const_0[simp]",
  ``evaluate (shift (REPLICATE n (clos_annotate$const_0 v8)) m l i,env,t1) =
      (Rval (REPLICATE n (Number 0)),t1)``,
  Induct_on `n` \\ fs [REPLICATE,shift_def]
  \\ once_rewrite_tac [shift_CONS]
  \\ fs [EVAL ``shift [clos_annotate$const_0 t] a2 a3 a4``]
  \\ once_rewrite_tac [evaluate_CONS]
  \\ fs [EVAL ``evaluate ([Op v8 (Const 0) []],env,t1)``]);

val no_overlap_has_var_IMP = prove(
  ``!n l2 x. clos_annotate$no_overlap n l2 /\ has_var x l2 ==> n <= x``,
  Induct \\ fs [no_overlap_def] \\ rw [] \\ res_tac
  \\ Cases_on `x = n` \\ fs []);

val evaluate_pure_IMP = prove(
  ``evaluate (xs,env,s) = (q,r) /\ EVERY pure xs /\
    q <> Rerr (Rabort Rtype_error) ==>
    ?vs. q = Rval vs /\ r = s /\ LENGTH vs = LENGTH xs``,
  rw[]
  \\ imp_res_tac (EVERY_pure_correct |> INST_TYPE[``:'ffi``|->alpha]) \\ fs[]
  \\ first_x_assum(qspecl_then[`s`,`env`]mp_tac)
  \\ simp[case_eq_thms]
  \\ CASE_TAC \\ simp[]
  \\ CASE_TAC \\ simp[]
  \\ strip_tac \\ fs[]);

val shift_correct = Q.prove(
  `(!xs env (s1:'ffi closSem$state) env' t1 res s2 m l i.
     (evaluate (xs,env,s1) = (res,s2)) /\ res <> Rerr (Rabort Rtype_error) /\
     (LENGTH env = m + l) /\
     alt_fv_set xs SUBSET env_ok m l i env env' /\
     every_Fn_vs_NONE xs ∧ FEVERY (λp. every_Fn_vs_NONE [SND (SND p)]) s1.code ∧
     state_rel s1 t1 ==>
     ?res' t2.
        (evaluate (shift (FST (alt_free xs)) m l i,env',t1) = (res',t2)) /\
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
   (full_simp_tac(srw_ss())[alt_free_def,shift_def,evaluate_def]
    \\ SRW_TAC [] [])
  THEN1 (* CONS *)
   (full_simp_tac(srw_ss())[alt_free_def,evaluate_def]
    \\ `?y1 l1. alt_free [x] = ([y1],l1)` by METIS_TAC [PAIR,alt_free_SING]
    \\ `?y2 l2. alt_free (y::xs) = (y2,l2)` by METIS_TAC [PAIR] \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[LET_DEF]
    \\ `?r1 s2. evaluate ([x],env,s1) = (r1,s2)` by METIS_TAC [PAIR]
    \\ full_simp_tac(srw_ss())[]
    \\ `?y3 y4. y2 = y3::y4` by
     (IMP_RES_TAC alt_free_LENGTH
      \\ Cases_on `y2` \\ full_simp_tac(srw_ss())[has_var_def,alt_fv,alt_fv1_thm])
    \\ full_simp_tac(srw_ss())[shift_def]
    \\ Cases_on `r1` \\ full_simp_tac(srw_ss())[]
    \\ SRW_TAC [] [markerTheory.Abbrev_def]
    \\ SRW_TAC [] [markerTheory.Abbrev_def]
    \\ `?t. shift [y1] m l i = [t]` by METIS_TAC [shift_SING]
    \\ full_simp_tac(srw_ss())[] \\ ONCE_REWRITE_TAC [evaluate_CONS]
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`env'`,`t1`])
    \\ REPEAT STRIP_TAC \\ POP_ASSUM (MP_TAC o Q.SPECL [`m`,`l`,`i`])
    \\ `alt_fv_set [x] SUBSET env_ok m l i env env' /\
        alt_fv_set (y::xs) SUBSET env_ok m l i env env'` by
      (full_simp_tac(srw_ss())[SUBSET_DEF,IN_DEF,alt_fv,alt_fv1_thm]
       \\ full_simp_tac(srw_ss())[] \\ REPEAT STRIP_TAC
       \\ full_simp_tac(srw_ss())[])
    \\ fs[] \\ rpt strip_tac
    \\ `?r2 s3. evaluate (y::xs,env,s2') = (r2,s3)` by METIS_TAC [PAIR] \\ full_simp_tac(srw_ss())[]
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`env'`,`t2`])
    \\ imp_res_tac evaluate_const
    \\ Cases_on `r2` \\ full_simp_tac(srw_ss())[]
    \\ REPEAT STRIP_TAC \\ POP_ASSUM (MP_TAC o Q.SPECL [`m`,`l`,`i`]) \\ full_simp_tac(srw_ss())[]
    \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[]
    \\ IMP_RES_TAC evaluate_SING \\ full_simp_tac(srw_ss())[])
  THEN1 (* Var *)
   (Cases_on `n < LENGTH env`
    \\ full_simp_tac(srw_ss())[alt_free_def,evaluate_def,shift_def]
    \\ full_simp_tac(srw_ss())[SUBSET_DEF,IN_DEF,alt_fv,alt_fv1_thm]
    \\ Cases_on `l + m <= n`
    THEN1 (full_simp_tac(srw_ss())[env_ok_def] \\ rev_full_simp_tac(srw_ss())[] \\ `F` by DECIDE_TAC)
    \\ reverse (sg `get_var m l i n < LENGTH env' /\
        v_rel (EL n env) (EL (get_var m l i n) env')`)
    THEN1 (full_simp_tac(srw_ss())[] \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[])
    \\ full_simp_tac(srw_ss())[get_var_def,env_ok_def]
    \\ Cases_on `n < l` \\ full_simp_tac(srw_ss())[zlookup_def]
    \\ `F` by DECIDE_TAC)
  THEN1 (* If *)
   (full_simp_tac(srw_ss())[alt_free_def]
    \\ `?y1 l1. alt_free [x1] = ([y1],l1)` by METIS_TAC [PAIR,alt_free_SING]
    \\ `?y2 l2. alt_free [x2] = ([y2],l2)` by METIS_TAC [PAIR,alt_free_SING]
    \\ `?y3 l3. alt_free [x3] = ([y3],l3)` by METIS_TAC [PAIR,alt_free_SING]
    \\ full_simp_tac(srw_ss())[LET_DEF,shift_def,evaluate_def]
    \\ `?r1 s2. evaluate ([x1],env,s1) = (r1,s2)` by METIS_TAC [PAIR] \\ full_simp_tac(srw_ss())[]
    \\ `alt_fv_set [x1] SUBSET env_ok m l i env env' /\
        alt_fv_set [x2] SUBSET env_ok m l i env env' /\
        alt_fv_set [x3] SUBSET env_ok m l i env env'` by
      (full_simp_tac(srw_ss())[SUBSET_DEF,IN_DEF,alt_fv,alt_fv1_thm])
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
   (full_simp_tac std_ss [alt_free_def]
    \\ `?y2 l2. alt_free [x2] = ([y2],l2)` by METIS_TAC [PAIR,alt_free_SING]
    \\ full_simp_tac std_ss [LET_DEF]
    \\ IF_CASES_TAC
    THEN1
     (fs [shift_def]
      \\ full_simp_tac(srw_ss())[alt_free_def,evaluate_def,case_eq_thms]
      \\ Cases_on `evaluate (xs,env,s1')` \\ fs []
      \\ Cases_on `q = Rerr (Rabort Rtype_error)` \\ fs []
      \\ drule (GEN_ALL evaluate_pure_IMP) \\ fs [] \\ strip_tac \\ fs []
      \\ rveq \\ fs []
      \\ first_x_assum match_mp_tac \\ fs []
      \\ asm_rewrite_tac [alt_fv1_def,alt_fv_def]
      \\ fs [SUBSET_DEF,IN_DEF]
      \\ rpt strip_tac
      \\ match_mp_tac (GEN_ALL env_ok_EXTEND_IGNORE)
      \\ fs [] \\ rveq \\ fs []
      \\ imp_res_tac no_overlap_has_var_IMP \\ fs []
      \\ first_x_assum match_mp_tac
      \\ asm_rewrite_tac [alt_fv1_def,alt_fv_def]
      \\ fs [alt_free_def])
    \\ full_simp_tac(srw_ss())[alt_free_def]
    \\ `?y1 l1. alt_free xs = (y1,l1)` by METIS_TAC [PAIR,alt_free_SING]
    \\ full_simp_tac(srw_ss())[LET_DEF,shift_def,evaluate_def]
    \\ rename1`Let tra xs x2` \\ rename1`evaluate(xs,env,s1)`
    \\ `?r1 s2. evaluate (xs,env,s1) = (r1,s2)` by METIS_TAC [PAIR]
    \\ full_simp_tac(srw_ss())[]
    \\ `alt_fv_set xs SUBSET env_ok m l i env env'` by
      (fs[SUBSET_DEF,IN_DEF,alt_fv_def,alt_fv1_thm]
       \\ `~(EVERY pure xs)` by fs []
       \\ full_simp_tac std_ss [SUBSET_DEF,IN_DEF,alt_fv_def,alt_fv1_thm])
    \\ `r1 <> Rerr(Rabort Rtype_error)` by (REPEAT STRIP_TAC \\ fs[])
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`env'`,`t1`,`m`,`l`,`i`])
    \\ full_simp_tac(srw_ss())[]
    \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `r1` \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
    \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
    \\ FIRST_X_ASSUM (qspecl_then[`v'++env'`,`t2`,
         `m`,`l + LENGTH y1`,`i`]mp_tac)
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
    \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[] \\ full_simp_tac(srw_ss())[SUBSET_DEF,IN_DEF]
    \\ REPEAT STRIP_TAC
    \\ IMP_RES_TAC alt_free_LENGTH
    \\ IMP_RES_TAC EVERY2_LENGTH
    \\ IMP_RES_TAC evaluate_IMP_LENGTH
    \\ IMP_RES_TAC evaluate_const
    \\ full_simp_tac(srw_ss())[shift_LENGTH_LEMMA,AC ADD_COMM ADD_ASSOC]
    \\ MATCH_MP_TAC env_ok_EXTEND \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[alt_fv_def,alt_fv1_thm]
    \\ REPEAT STRIP_TAC
    \\ Q.PAT_X_ASSUM `!x.bbb` (K ALL_TAC)
    \\ FIRST_X_ASSUM MATCH_MP_TAC
    \\ `x - LENGTH v' + LENGTH v' = x` by DECIDE_TAC \\ full_simp_tac(srw_ss())[])
  THEN1 (* Raise *)
   (full_simp_tac(srw_ss())[alt_free_def]
    \\ `?y1 l1. alt_free [x1] = ([y1],l1)` by METIS_TAC [PAIR,alt_free_SING]
    \\ full_simp_tac(srw_ss())[LET_DEF,shift_def,evaluate_def]
    \\ `?r1 s2. evaluate ([x1],env,s1) = (r1,s2)` by METIS_TAC [PAIR] \\ full_simp_tac(srw_ss())[]
    \\ `alt_fv_set [x1] SUBSET env_ok m l i env env'` by
      (full_simp_tac(srw_ss())[SUBSET_DEF,IN_DEF,alt_fv,alt_fv1_thm])
    \\ `r1 <> Rerr(Rabort Rtype_error)` by (REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[])
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`env'`,`t1`,`m`,`l`,`i`]) \\ full_simp_tac(srw_ss())[]
    \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `r1` \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
    \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
    \\ IMP_RES_TAC evaluate_SING \\ full_simp_tac(srw_ss())[])
  THEN1 (* Handle *)
   (full_simp_tac(srw_ss())[alt_free_def]
    \\ `?y1 l1. alt_free [x1] = ([y1],l1)` by METIS_TAC [PAIR,alt_free_SING]
    \\ `?y2 l2. alt_free [x2] = ([y2],l2)` by METIS_TAC [PAIR,alt_free_SING]
    \\ full_simp_tac(srw_ss())[LET_DEF,shift_def,evaluate_def]
    \\ `?r1 s2. evaluate ([x1],env,s1) = (r1,s2)` by METIS_TAC [PAIR] \\ full_simp_tac(srw_ss())[]
    \\ `alt_fv_set [x1] SUBSET env_ok m l i env env'` by
      (full_simp_tac(srw_ss())[SUBSET_DEF,IN_DEF,alt_fv,alt_fv1_thm])
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
    \\ full_simp_tac(srw_ss())[alt_fv,alt_fv1_thm]
    \\ Cases_on `x` \\ full_simp_tac(srw_ss())[]
    \\ Q.PAT_X_ASSUM `!x.bbb` (K ALL_TAC)
    \\ FIRST_X_ASSUM MATCH_MP_TAC \\ full_simp_tac(srw_ss())[ADD1])
  THEN1 (* Op *)
   (full_simp_tac(srw_ss())[alt_free_def]
    \\ `?y1 l1. alt_free xs = (y1,l1)` by METIS_TAC [PAIR,alt_free_SING]
    \\ full_simp_tac(srw_ss())[LET_DEF,shift_def,evaluate_def]
    \\ `?r1 s2. evaluate (xs,env,s1) = (r1,s2)` by METIS_TAC [PAIR] \\ full_simp_tac(srw_ss())[]
    \\ `alt_fv_set xs SUBSET env_ok m l i env env'` by
      (full_simp_tac(srw_ss())[SUBSET_DEF,IN_DEF,alt_fv,alt_fv1_thm])
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
   (full_simp_tac(srw_ss())[alt_free_def,evaluate_def]
    \\ full_simp_tac(srw_ss())[clos_env_def]
    \\ SRW_TAC [] [] \\ SRW_TAC [] [markerTheory.Abbrev_def]
    \\ `?y1 l1. alt_free [exp] = ([y1],l1)` by METIS_TAC [PAIR,alt_free_SING]
    \\ Cases_on `num_args <= s1.max_app` \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `num_args <> 0` \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
    \\ full_simp_tac(srw_ss())[shift_def,LET_DEF,evaluate_def,clos_env_def,
           PULL_EXISTS,v_rel_simp]
    \\ Q.ABBREV_TAC `live =
          FILTER (\n. n < m + l) (vars_to_list (Shift num_args l1))`
    \\ full_simp_tac(srw_ss())[MAP_MAP_o,o_DEF]
    \\ Cases_on `lookup_vars (MAP (get_var m l i) live) env'`
    \\ full_simp_tac(srw_ss())[] THEN1
     (full_simp_tac(srw_ss())[SUBSET_DEF,IN_DEF,alt_fv,alt_fv1_thm]
      \\ full_simp_tac(srw_ss())[lookup_vars_NONE] \\ UNABBREV_ALL_TAC
      \\ full_simp_tac(srw_ss())[MEM_FILTER,MEM_vars_to_list,MEM_MAP]
      \\ MP_TAC (Q.SPEC`[exp]` alt_free_thm)
      \\ full_simp_tac(srw_ss())[LET_DEF] \\ CCONTR_TAC \\ full_simp_tac(srw_ss())[] \\ RES_TAC
      \\ SRW_TAC [] []
      \\ full_simp_tac(srw_ss())[env_ok_def] \\ rev_full_simp_tac(srw_ss())[]
      \\ full_simp_tac(srw_ss())[get_var_def,zlookup_def]
      \\ DECIDE_TAC)
    \\ reverse IF_CASES_TAC >- (
      imp_res_tac state_rel_max_app \\ fs[])
    \\ simp_tac (srw_ss())[]
    \\ Q.EXISTS_TAC `shifted_env 0 live` \\ full_simp_tac(srw_ss())[]
    \\ REPEAT STRIP_TAC \\ Cases_on `n` \\ full_simp_tac(srw_ss())[]
    \\ MP_TAC (Q.SPEC `[exp]` alt_free_thm)
    \\ full_simp_tac(srw_ss())[LET_DEF] \\ STRIP_TAC
    \\ full_simp_tac(srw_ss())[SUBSET_DEF,IN_DEF,alt_fv,alt_fv1_thm]
    \\ full_simp_tac(srw_ss())[ADD1] \\ RES_TAC \\ UNABBREV_ALL_TAC
    \\ Q.ABBREV_TAC `live = vars_to_list (Shift num_args l1)`
    \\ MATCH_MP_TAC (GEN_ALL env_ok_shifted_env)
    \\ Q.LIST_EXISTS_TAC [`i`,`env'`] \\ full_simp_tac(srw_ss())[]
    \\ `n' + 1 = (n' + 1 - num_args) + num_args` by DECIDE_TAC
    \\ STRIP_TAC THEN1 METIS_TAC []
    \\ STRIP_TAC THEN1 (UNABBREV_ALL_TAC \\ full_simp_tac(srw_ss())[MEM_vars_to_list] \\ METIS_TAC [])
    \\ UNABBREV_ALL_TAC \\ full_simp_tac(srw_ss())[ALL_DISTINCT_vars_to_list])
  THEN1 (* Letrec *)
   (full_simp_tac std_ss [alt_free_def]
    \\ `?y2 l2. alt_free [exp] = ([y2],l2)` by METIS_TAC [PAIR,alt_free_SING]
    \\ full_simp_tac std_ss [LET_DEF]
    \\ IF_CASES_TAC
    THEN1
     (fs [shift_def]
      \\ full_simp_tac(srw_ss())[alt_free_def,evaluate_def,case_eq_thms]
      \\ qpat_x_assum `_ = (res,_)` mp_tac \\ IF_CASES_TAC \\ fs []
      \\ strip_tac \\ fs []
      \\ first_x_assum match_mp_tac \\ fs []
      \\ asm_rewrite_tac [alt_fv1_def,alt_fv_def]
      \\ fs [SUBSET_DEF,IN_DEF]
      \\ rpt strip_tac
      \\ match_mp_tac (GEN_ALL env_ok_EXTEND_IGNORE)
      \\ fs [] \\ rveq \\ fs []
      \\ imp_res_tac no_overlap_has_var_IMP \\ fs []
      \\ first_x_assum match_mp_tac
      \\ asm_rewrite_tac [alt_fv1_def,alt_fv_def]
      \\ fs [alt_free_def])
    \\ full_simp_tac(srw_ss())[alt_free_def,evaluate_def]
    \\ full_simp_tac(srw_ss())[clos_env_def]
    \\ SRW_TAC [] [] \\ SRW_TAC [] [markerTheory.Abbrev_def]
    \\ `EVERY (\(num_args,e). num_args <= s1.max_app /\
                              num_args <> 0) fns` by
      (CCONTR_TAC \\ FULL_SIMP_TAC std_ss [])
    \\ Cases_on `build_recc F loc env names fns` \\ full_simp_tac(srw_ss())[]
    \\ Q.ABBREV_TAC `rec_res = MAP
                        (\(n,x).
                           (let (c,l) = alt_free [x] in
                              ((n,HD c),Shift (n + LENGTH fns) l))) fns`
    \\ full_simp_tac(srw_ss())[shift_def,LET_DEF,evaluate_def,
           build_recc_def,clos_env_def,shift_LENGTH_LEMMA]
    \\ Q.PAT_ABBREV_TAC `ev = EVERY PP xx`
    \\ `ev` by
     (UNABBREV_ALL_TAC \\ full_simp_tac(srw_ss())[MAP_MAP_o,o_DEF]
      \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV)
      \\ full_simp_tac(srw_ss())[EVERY_MAP]
      \\ full_simp_tac(srw_ss())[EVERY_MEM,FORALL_PROD] \\ rpt strip_tac \\ RES_TAC
      \\ imp_res_tac state_rel_max_app \\ fs[])
    \\ full_simp_tac(srw_ss())[] \\ POP_ASSUM (K ALL_TAC) \\ POP_ASSUM (K ALL_TAC)
    \\ Q.ABBREV_TAC `live = FILTER (\n. n < m + l)
          (vars_to_list (list_mk_Union (MAP SND rec_res)))`
    \\ Cases_on `lookup_vars (MAP (get_var m l i) live) env'`
    \\ full_simp_tac(srw_ss())[] THEN1
     (full_simp_tac(srw_ss())[SUBSET_DEF,IN_DEF,alt_fv,alt_fv1_thm]
      \\ full_simp_tac(srw_ss())[lookup_vars_NONE] \\ UNABBREV_ALL_TAC
      \\ full_simp_tac(srw_ss())[MEM_FILTER,MEM_vars_to_list,MEM_MAP]
      \\ full_simp_tac(srw_ss())[EXISTS_MEM,PULL_EXISTS,EXISTS_PROD]
      \\ NTAC 3 (POP_ASSUM MP_TAC)
      \\ full_simp_tac(srw_ss())[MAP_MAP_o,o_DEF,MEM_MAP,EXISTS_PROD]
      \\ REPEAT STRIP_TAC
      \\ Q.MATCH_ASSUM_RENAME_TAC `MEM (p_11,p_21) fns`
      \\ Cases_on `alt_free [p_21]` \\ full_simp_tac(srw_ss())[]
      \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[]
      \\ MP_TAC (Q.SPEC`[p_21]` alt_free_thm)
      \\ full_simp_tac(srw_ss())[LET_DEF] \\ CCONTR_TAC
      \\ full_simp_tac(srw_ss())[AC ADD_ASSOC ADD_COMM] \\ RES_TAC
      \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[]
      \\ full_simp_tac(srw_ss())[env_ok_def] \\ rev_full_simp_tac(srw_ss())[]
      \\ full_simp_tac(srw_ss())[get_var_def,zlookup_def]
      \\ DECIDE_TAC)
    \\ FIRST_X_ASSUM MATCH_MP_TAC
    \\ IMP_RES_TAC alt_free_LENGTH \\ full_simp_tac(srw_ss())[]
    \\ `LENGTH rec_res = LENGTH x` by
      (UNABBREV_ALL_TAC \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[])
    \\ STRIP_TAC THEN1 (full_simp_tac(srw_ss())[AC ADD_COMM ADD_ASSOC,Abbr`rec_res`])
    \\ full_simp_tac(srw_ss())[SUBSET_DEF,IN_DEF,alt_fv,alt_fv1_thm]
    \\ REPEAT STRIP_TAC
    \\ MATCH_MP_TAC (env_ok_EXTEND |> GEN_ALL) \\ full_simp_tac(srw_ss())[]
    \\ reverse (REPEAT STRIP_TAC) THEN1
     (FIRST_X_ASSUM MATCH_MP_TAC \\ DISJ2_TAC
      \\ UNABBREV_ALL_TAC \\ full_simp_tac(srw_ss())[]
      \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[]
      \\ IMP_RES_TAC (DECIDE ``n <= m:num <=> (m - n + n = m)``)
      \\ full_simp_tac(srw_ss())[] \\ rfs [])
    \\ SRW_TAC [] []
    \\ full_simp_tac(srw_ss())[LIST_REL_GENLIST] \\ REPEAT STRIP_TAC
    \\ full_simp_tac(srw_ss())[v_rel_simp]
    \\ Q.UNABBREV_TAC `rec_res`
    \\ full_simp_tac(srw_ss())[EVERY2_MAP]
    \\ MATCH_MP_TAC listTheory.EVERY2_refl
    \\ REPEAT STRIP_TAC
    \\ PairCases_on `x` \\ full_simp_tac(srw_ss())[]
    \\ `?y1 y2. alt_free [x1] = ([y1],y2)` by METIS_TAC [alt_free_SING,PAIR]
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
    \\ MP_TAC (Q.SPEC `[x1]` alt_free_thm)
    \\ IMP_RES_TAC (DECIDE ``n <= m:num <=> (m - n + n = m)``)
    \\ full_simp_tac(srw_ss())[LET_DEF] \\ STRIP_TAC \\ full_simp_tac(srw_ss())[])
  THEN1 (* App *)
   (full_simp_tac(srw_ss())[alt_free_def]
    \\ `?y1 l1. alt_free xs = (y1,l1)` by METIS_TAC [PAIR]
    \\ `?y2 l2. alt_free [x1] = ([y2],l2)` by METIS_TAC [PAIR,alt_free_SING]
    \\ full_simp_tac(srw_ss())[LET_DEF,shift_def,evaluate_def]
    \\ `?r1 s2. evaluate (xs,env,s1) = (r1,s2)` by METIS_TAC [PAIR] \\ full_simp_tac(srw_ss())[]
    \\ `?r2 s3. evaluate ([x1],env,s2') = (r2,s3)` by METIS_TAC [PAIR] \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[shift_LENGTH_LEMMA]
    \\ IMP_RES_TAC alt_free_LENGTH
    \\ Cases_on `LENGTH xs > 0` \\ full_simp_tac(srw_ss())[]
    \\ `alt_fv_set xs SUBSET env_ok m l i env env' /\
        alt_fv_set [x1] SUBSET env_ok m l i env env'` by
      (full_simp_tac(srw_ss())[SUBSET_DEF,IN_DEF,alt_fv,alt_fv1_thm])
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
   (full_simp_tac(srw_ss())[alt_free_def,evaluate_def]
    \\ `?y1 l1. alt_free [x] = ([y1],l1)` by METIS_TAC [PAIR,alt_free_SING]
    \\ full_simp_tac(srw_ss())[LET_DEF,shift_def,evaluate_def]
    \\ `t1.clock = s1.clock` by full_simp_tac(srw_ss())[state_rel_def] \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `s1.clock = 0` \\ full_simp_tac(srw_ss())[]
    \\ SRW_TAC [] []
    \\ `alt_fv_set [x] SUBSET env_ok m l i env env'` by
      (full_simp_tac(srw_ss())[SUBSET_DEF,IN_DEF,alt_fv,alt_fv1_thm])
    \\ imp_res_tac evaluate_const \\ full_simp_tac(srw_ss())[Once dec_clock_def]
    \\ `state_rel (dec_clock 1 s1) (dec_clock 1 t1)` by
          full_simp_tac(srw_ss())[state_rel_def,dec_clock_def] \\ RES_TAC
    \\ STRIP_ASSUME_TAC (shift_SING |> Q.INST [`x`|->`y1`]) \\ full_simp_tac(srw_ss())[])
  THEN1 (* Call *)
   (full_simp_tac(srw_ss())[alt_free_def]
    \\ `?y1 l1. alt_free xs = (y1,l1)` by METIS_TAC [PAIR,alt_free_SING]
    \\ full_simp_tac(srw_ss())[LET_DEF,shift_def,evaluate_def]
    \\ `?r1 s2. evaluate (xs,env,s1) = (r1,s2)` by METIS_TAC [PAIR] \\ full_simp_tac(srw_ss())[]
    \\ `alt_fv_set xs SUBSET env_ok m l i env env'` by
      (full_simp_tac(srw_ss())[SUBSET_DEF,IN_DEF,alt_fv,alt_fv1_thm])
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
    \\ `?c2. shift (FST (alt_free [r])) 0 (LENGTH a) LN = [c2] /\
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
    \\ rename1 `dest_closure s1.max_app loc_opt f (l::ls)`
    \\ Cases_on `dest_closure s1.max_app loc_opt f (l::ls)` \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `x` \\ full_simp_tac(srw_ss())[]
    THEN1 (* Partial_app *)
     (reverse (sg `?z. (dest_closure s1'.max_app loc_opt f' (y::ys) = SOME (Partial_app z)) /\
           v_rel v z`) THEN1
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
        \\ MATCH_MP_TAC rich_listTheory.EVERY2_APPEND_suff \\ fs[]
        \\ MATCH_MP_TAC EVERY2_TAKE
        \\ MATCH_MP_TAC rich_listTheory.EVERY2_APPEND_suff \\ fs[])
      \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[]
      \\ reverse (Cases_on `q`) \\ full_simp_tac(srw_ss())[]
      \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[]
      \\ reverse (Cases_on `a`) \\ full_simp_tac(srw_ss())[]
      \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[]
      \\ reverse (Cases_on `t`) \\ full_simp_tac(srw_ss())[]
      \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[]
      \\ Q.MATCH_ASSUM_RENAME_TAC `v_rel h h'`
      \\ FIRST_X_ASSUM MATCH_MP_TAC \\ full_simp_tac(srw_ss())[]
      \\ MATCH_MP_TAC EVERY2_DROP
      \\ MATCH_MP_TAC rich_listTheory.EVERY2_APPEND_suff \\ full_simp_tac(srw_ss())[])
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
        \\ MATCH_MP_TAC EVERY2_TAKE
        \\ MATCH_MP_TAC rich_listTheory.EVERY2_APPEND_suff \\ full_simp_tac(srw_ss())[])
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
    \\ MATCH_MP_TAC EVERY2_DROP
    \\ MATCH_MP_TAC rich_listTheory.EVERY2_APPEND_suff \\ full_simp_tac(srw_ss())[]));

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

val every_Fn_SOME_const_0 = Q.store_thm("every_Fn_SOME_const_0[simp]",
  `every_Fn_SOME [clos_annotate$const_0 t]`,
  EVAL_TAC );

val every_Fn_SOME_alt_free = Q.store_thm("every_Fn_SOME_alt_free",
  `∀es. every_Fn_SOME es ⇒ every_Fn_SOME (FST (alt_free es))`,
  ho_match_mp_tac alt_free_ind >>
  rw[alt_free_def] \\ rpt(pairarg_tac \\ fs[]) \\
  imp_res_tac alt_free_SING >> fs[] \\
  simp[MAP_MAP_o,UNCURRY,o_DEF] >> rveq >>
  TRY IF_CASES_TAC >> fs[] >>
  rpt (pop_assum mp_tac) >>
  fs[REPLICATE_GENLIST] >>
  ONCE_REWRITE_TAC[every_Fn_SOME_EVERY] >>
  fs[EVERY_MAP,EVERY_GENLIST] >>
  rw[EVERY_MEM,FORALL_PROD] >> res_tac
  \\ metis_tac[alt_free_SING,HD,FST,PAIR,MEM]);

val every_Fn_SOME_annotate = Q.store_thm("every_Fn_SOME_annotate",
  `every_Fn_SOME es ⇒ every_Fn_SOME (annotate n es)`, rw[annotate_def,every_Fn_SOME_alt_free]);

val IF_MAP_EQ = MAP_EQ_f |> SPEC_ALL |> EQ_IMP_RULE |> snd;

val shift_code_locs = Q.prove(
  `!xs env s1 env'. code_locs (shift xs env s1 env') = code_locs xs`,
  ho_match_mp_tac shift_ind
  \\ simp[shift_def,code_locs_def,shift_LENGTH_LEMMA]
  \\ srw_tac[][code_locs_append]
  \\ full_simp_tac(srw_ss())[MAP_MAP_o,o_DEF]
  \\ ONCE_REWRITE_TAC [code_locs_map]
  \\ AP_TERM_TAC \\ MATCH_MP_TAC IF_MAP_EQ \\ full_simp_tac(srw_ss())[FORALL_PROD]);

val code_locs_const_0 = Q.store_thm("code_locs_const_0[simp]",
  `code_locs [clos_annotate$const_0 t] = []`, EVAL_TAC);

val alt_free_code_locs = Q.prove(
  `!xs. set (code_locs (FST (alt_free xs))) ⊆ set (code_locs xs)`,
  ho_match_mp_tac alt_free_ind
  \\ simp[alt_free_def,code_locs_def,UNCURRY] >> rw[]
  \\ Cases_on `alt_free [x]` \\ full_simp_tac(srw_ss())[code_locs_append,HD_FST_alt_free]
  \\ Cases_on `alt_free [x1]` \\ full_simp_tac(srw_ss())[code_locs_append,HD_FST_alt_free]
  \\ Cases_on `alt_free [x2]` \\ full_simp_tac(srw_ss())[code_locs_append,HD_FST_alt_free]
  \\ Cases_on `alt_free xs` \\ full_simp_tac(srw_ss())[code_locs_append,HD_FST_alt_free]
  \\ fs[MAP_MAP_o,o_DEF,SUBSET_DEF,code_locs_def,GSYM MAP_K_REPLICATE]
  \\ ONCE_REWRITE_TAC [code_locs_map]
  \\ simp[MEM_FLAT,MEM_GENLIST,MEM_MAP,PULL_EXISTS,UNCURRY,HD_FST_alt_free]
  \\ metis_tac[HD_FST_alt_free,FST,PAIR]);

val alt_free_code_locs_distinct = Q.prove(
  `∀xs. ALL_DISTINCT (code_locs xs) ⇒ ALL_DISTINCT (code_locs (FST (alt_free xs)))`,
  recInduct alt_free_ind
  \\ rw[alt_free_def,code_locs_def]
  \\ rpt(pairarg_tac \\ fs[])
  \\ fs[code_locs_append,ALL_DISTINCT_APPEND,code_locs_def] \\ rw[]
  \\ fs[code_locs_append,ALL_DISTINCT_APPEND,code_locs_def,GSYM MAP_K_REPLICATE,code_locs_map,FLAT_MAP_NIL]
  \\ TRY (
    rename1`GENLIST`
    \\ fs[MEM_GENLIST,MAP_MAP_o,o_DEF,UNCURRY,HD_FST_alt_free,PULL_EXISTS]
    \\ imp_res_tac alt_free_SING \\ fs[] \\ rveq
    \\ reverse conj_tac
    >- (
      fs[MEM_FLAT,MEM_MAP,PULL_EXISTS,EXISTS_PROD] \\ rw[]
      \\ metis_tac[SUBSET_DEF,alt_free_code_locs,FST] )
    \\ reverse conj_tac
    >- (
      fs[MEM_FLAT,MEM_MAP,PULL_EXISTS,EXISTS_PROD] \\ rw[]
      \\ metis_tac[SUBSET_DEF,alt_free_code_locs,FST] )
    \\ fs[ALL_DISTINCT_FLAT,EL_MAP]
    \\ fs[MEM_FLAT,MEM_MAP,PULL_EXISTS,EXISTS_PROD] \\ rw[]
    \\ metis_tac[SUBSET_DEF,alt_free_code_locs,FST] )
  \\ metis_tac[SUBSET_DEF,alt_free_code_locs,FST,alt_free_SING,HD]);

val annotate_code_locs = Q.store_thm("annotate_code_locs",
  `!n ls. set (code_locs (annotate n ls)) ⊆ set (code_locs ls) ∧
          (ALL_DISTINCT (code_locs ls) ⇒ ALL_DISTINCT (code_locs (annotate n ls)))`,
  srw_tac[][annotate_def,shift_code_locs,alt_free_code_locs,alt_free_code_locs_distinct]);

val _ = export_theory()
