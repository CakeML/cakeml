open preamble
     bvlSemTheory bvlPropsTheory
     bvl_inlineTheory;

val _ = new_theory"bvl_inlineProof";

val code_rel_def = Define `
  code_rel (:'ffi) c1 c2 <=>
    !n arity e1.
      lookup n c1 = SOME (arity,e1) ==>
      ?e2. lookup n c2 = SOME (arity,e2) /\
           !(s:'ffi bvlSem$state) env res t.
             LENGTH env = arity /\ res <> Rerr (Rabort Rtype_error) /\
             evaluate ([e1],env,s with code := c1) = (res,t with code := c1) ==>
             evaluate ([e2],env,s with code := c2) = (res,t with code := c2)`

val code_rel_refl = store_thm("code_rel_refl",
  ``!c. code_rel (:'ffi) c c``,
  fs [code_rel_def]);

val code_rel_trans = store_thm("code_rel_trans",
  ``!c1 c2 c3.
      code_rel (:'ffi) c1 c2 /\ code_rel (:'ffi) c2 c3 ==>
      code_rel (:'ffi) c1 c3``,
  fs [code_rel_def] \\ rw [] \\ res_tac
  \\ first_x_assum drule \\ rw [] \\ fs []);

val exp_rel_def = Define `
  exp_rel (:'ffi) c e1 e2 <=>
    !(s:'ffi bvlSem$state) env res t.
      evaluate ([e1],env,s) = (res,t) /\ s.code = c /\
      res <> Rerr (Rabort Rtype_error) ==>
      evaluate ([e2],env,s) = (res,t)`

val evaluate_code_insert = store_thm("evaluate_code_insert",
  ``!xs env (s:'ffi bvlSem$state) res t e1 e2 n arity c.
      evaluate (xs,env,s) = (res,t) /\
      exp_rel (:'ffi) (insert n (arity,e2) c) e1 e2 /\
      res ≠ Rerr (Rabort Rtype_error) /\
      lookup n c = SOME (arity,e1) /\
      s.code = c ==>
      evaluate (xs,env,s with code := insert n (arity,e2) c) =
                  (res,t with code := insert n (arity,e2) c)``,
  recInduct bvlSemTheory.evaluate_ind \\ reverse (rw [])
  \\ fs [bvlSemTheory.evaluate_def]
  THEN1 (* Call *)
   (Cases_on `evaluate (xs,env,s1)` \\ fs []
    \\ `q <> Rerr (Rabort Rtype_error)` by (rpt strip_tac \\ fs [])
    \\ fs [] \\ first_x_assum drule
    \\ disch_then drule \\ fs []
    \\ Cases_on `q` \\ fs [] \\ rw []
    \\ Cases_on `find_code dest a (insert n (arity,e2) s1.code) =
                 find_code dest a r.code` \\ fs []
    THEN1
     (BasicProvers.TOP_CASE_TAC \\ fs []
      \\ PairCases_on `x` \\ fs [] \\ IF_CASES_TAC \\ fs [] \\ rw [] \\ fs []
      \\ rfs [] \\ imp_res_tac evaluate_code \\ fs [])
    \\ reverse (Cases_on `dest`) \\ fs [] THEN1
     (fs [find_code_def,lookup_insert]
      \\ Cases_on `lookup x r.code` \\ fs []
      \\ Cases_on `x'` \\ fs []
      \\ Cases_on `LENGTH a = q` \\ fs []
      \\ Cases_on `x = n` \\ fs []
      \\ rveq \\ fs [] \\ imp_res_tac evaluate_code \\ fs []
      \\ IF_CASES_TAC \\ fs [] \\ rveq \\ fs []
      \\ first_x_assum drule
      \\ disch_then drule
      \\ fs [exp_rel_def] \\ rw [])
    \\ fs [find_code_def,lookup_insert] \\ IF_CASES_TAC \\ fs []
    \\ Cases_on `LAST a` \\ fs []
    \\ Cases_on `lookup n' r.code` \\ fs []
    \\ PairCases_on `x` \\ fs []
    \\ Cases_on `LENGTH a = x0 + 1` \\ fs []
    \\ Cases_on `n' = n` \\ fs []
    \\ fs [] \\ rveq \\ fs [] \\ imp_res_tac evaluate_code \\ fs []
    \\ IF_CASES_TAC \\ fs [] \\ rveq \\ fs []
    \\ first_x_assum drule
    \\ disch_then drule
    \\ fs [exp_rel_def] \\ rw [])
  \\ TRY (IF_CASES_TAC \\ fs [] \\ NO_TAC)
  THEN1
   (Cases_on `evaluate (xs,env,s)` \\ fs []
    \\ `q <> Rerr (Rabort Rtype_error)` by (rpt strip_tac \\ fs [])
    \\ fs [] \\ imp_res_tac evaluate_code \\ fs []
    \\ first_x_assum drule
    \\ disch_then drule \\ fs []
    \\ Cases_on `q` \\ fs []
    \\ Cases_on `do_app op (REVERSE a) r` \\ fs []
    \\ TRY (Cases_on `a'` \\ fs [] \\ rveq \\ fs []) \\ rveq \\ fs []
    \\ TRY (drule (GEN_ALL bvlPropsTheory.do_app_with_code) ORELSE
            drule (GEN_ALL bvlPropsTheory.do_app_with_code_err))
    \\ disch_then (qspec_then `insert n (arity,e2) s.code` mp_tac)
    \\ (impl_tac THEN1 fs [domain_insert,SUBSET_DEF])
    \\ rw [] \\ fs [])
  \\ TRY
   (Cases_on `evaluate ([x1],env,s)` \\ fs []
    \\ `q <> Rerr (Rabort Rtype_error)` by (rpt strip_tac \\ fs [])
    \\ Cases_on `q` \\ fs [] \\ rveq \\ fs [] \\ NO_TAC)
  \\ TRY
   (Cases_on `evaluate ([x1],env,s1)` \\ fs []
    \\ `q <> Rerr (Rabort Rtype_error)` by (rpt strip_tac \\ fs [])
    \\ Cases_on `q` \\ fs [] \\ rveq \\ fs [] \\ NO_TAC)
  THEN1
   (Cases_on `evaluate ([x1],env,s1)` \\ fs []
    \\ `q <> Rerr (Rabort Rtype_error)` by (rpt strip_tac \\ fs [])
    \\ Cases_on `q` \\ fs [] \\ rveq \\ fs []
    \\ every_case_tac \\ fs [] \\ rfs []
    \\ first_x_assum drule \\ fs []
    \\ imp_res_tac evaluate_code \\ fs [])
  THEN1
   (Cases_on `evaluate (xs,env,s)` \\ fs []
    \\ `q <> Rerr (Rabort Rtype_error)` by (rpt strip_tac \\ fs [])
    \\ Cases_on `q` \\ fs [] \\ rveq \\ fs []
    \\ first_x_assum drule \\ fs []
    \\ imp_res_tac evaluate_code \\ fs [])
  THEN1
   (Cases_on `evaluate ([x1],env,s)` \\ fs []
    \\ `q <> Rerr (Rabort Rtype_error)` by (rpt strip_tac \\ fs [])
    \\ Cases_on `q` \\ fs [] \\ rveq \\ fs []
    \\ rpt (IF_CASES_TAC \\ fs [])
    \\ first_x_assum drule \\ fs []
    \\ imp_res_tac evaluate_code \\ fs [])
  THEN1
   (Cases_on `evaluate ([x],env,s)` \\ fs []
    \\ `q <> Rerr (Rabort Rtype_error)` by (rpt strip_tac \\ fs [])
    \\ Cases_on `q` \\ fs [] \\ rveq \\ fs []
    \\ Cases_on `evaluate (y::xs,env,r)` \\ fs []
    \\ first_x_assum drule \\ fs []
    \\ imp_res_tac evaluate_code \\ fs []
    \\ Cases_on `q` \\ fs [] \\ rveq \\ fs []));

val code_rel_insert = store_thm("code_rel_insert",
  ``lookup n c = SOME (arity,e1) /\
    exp_rel (:'ffi) (insert n (arity,e2) c) e1 e2 ==>
    code_rel (:'ffi) c (insert n (arity,e2) c)``,
  fs [code_rel_def] \\ rw [lookup_insert] \\ rw [] \\ fs [] \\ rw []
  \\ TRY (drule evaluate_code_insert \\ fs [] \\ NO_TAC)
  \\ drule evaluate_code_insert \\ fs []
  \\ disch_then drule \\ fs [] \\ rw []
  \\ qpat_assum `exp_rel (:'ffi) _ e1 e2` (fn th => mp_tac th \\ assume_tac th)
  \\ simp_tac std_ss [exp_rel_def]
  \\ disch_then drule \\ fs []);

fun split_tac q = Cases_on q \\ Cases_on `q` \\ FULL_SIMP_TAC (srw_ss()) [];

val evaluate_inline = Q.store_thm("evaluate_inline",
  `!cs xs s env.
     subspt cs s.code /\
     FST (evaluate (xs,env,s)) <> Rerr(Rabort Rtype_error) ==>
     (evaluate (inline cs xs,env,s) = evaluate (xs,env,s))`,
  recInduct inline_ind \\ reverse (REPEAT STRIP_TAC)
  \\ POP_ASSUM MP_TAC \\ SIMP_TAC std_ss [Once inline_def,LET_DEF] \\ RES_TAC
  THEN1
   (Cases_on `dest` \\ fs [] THEN1
     (ONCE_REWRITE_TAC [evaluate_def] \\ ASM_SIMP_TAC std_ss [HD_inline]
      \\ Cases_on `evaluate (xs,env,s)` \\ FULL_SIMP_TAC std_ss []
      \\ Cases_on `q` \\ FULL_SIMP_TAC (srw_ss()) [LET_DEF])
    \\ Cases_on `lookup x cs` \\ fs [] THEN1
     (ONCE_REWRITE_TAC [evaluate_def] \\ ASM_SIMP_TAC std_ss [HD_inline]
      \\ Cases_on `evaluate (xs,env,s)` \\ FULL_SIMP_TAC std_ss []
      \\ Cases_on `q` \\ FULL_SIMP_TAC (srw_ss()) [LET_DEF])
    \\ rename1 `lookup x cs = SOME args`
    \\ PairCases_on `args` \\ fs []
    \\ ONCE_REWRITE_TAC [evaluate_def] \\ ASM_SIMP_TAC std_ss [HD_inline]
    \\ Cases_on `evaluate (xs,env,s)` \\ FULL_SIMP_TAC std_ss []
    \\ Cases_on `q` \\ FULL_SIMP_TAC (srw_ss()) [LET_DEF]
    \\ IMP_RES_TAC evaluate_code
    \\ `lookup x s.code = SOME (args0,args1)` by fs [subspt_def,domain_lookup]
    \\ fs [find_code_def]
    \\ IMP_RES_TAC evaluate_IMP_LENGTH \\ fs []
    \\ IF_CASES_TAC \\ fs []
    \\ SIMP_TAC std_ss [evaluate_mk_tick] \\ SRW_TAC [] [] \\ fs [ADD1]
    \\ MATCH_MP_TAC evaluate_expand_env \\ FULL_SIMP_TAC std_ss [])
  \\ ONCE_REWRITE_TAC [evaluate_def] \\ ASM_SIMP_TAC std_ss [HD_inline]
  \\ TRY (SRW_TAC [] [] \\ FIRST_X_ASSUM MATCH_MP_TAC
          \\ FULL_SIMP_TAC (srw_ss()) [dec_clock_def] \\ NO_TAC)
  \\ TRY (split_tac `evaluate (xs,env,s)`
     \\ IMP_RES_TAC evaluate_code \\ FULL_SIMP_TAC (srw_ss()) [] \\ NO_TAC)
  \\ TRY (split_tac `evaluate ([x1],env,s)` \\ SRW_TAC [] []
     \\ IMP_RES_TAC evaluate_code \\ FULL_SIMP_TAC (srw_ss()) []
     \\ Cases_on`e`>>fs[]>>NO_TAC)
  THEN1 (Cases_on `inline cs (y::xs)` THEN1
      (`LENGTH (inline cs (y::xs)) = 0` by METIS_TAC [LENGTH]
       \\ FULL_SIMP_TAC std_ss [LENGTH_inline,LENGTH] \\ `F` by DECIDE_TAC)
     \\ SIMP_TAC std_ss [Once evaluate_def,HD_inline]
     \\ POP_ASSUM (fn th => FULL_SIMP_TAC std_ss [GSYM th])
     \\ split_tac `evaluate ([x],env,s)` \\ split_tac `evaluate (y::xs,env,r)`
     \\ IMP_RES_TAC evaluate_code \\ FULL_SIMP_TAC (srw_ss()) []));

val exp_rel_inline = store_thm("exp_rel_inline",
  ``subspt cs c ==> exp_rel (:'ffi) c e (HD (inline cs [e]))``,
  fs [exp_rel_def] \\ rw []
  \\ qpat_assum `_ = (_,_)` (fn th => assume_tac th THEN
        once_rewrite_tac [GSYM th])
  \\ match_mp_tac evaluate_inline \\ fs []);

val code_rel_insert_inline = store_thm("code_rel_insert_inline",
  ``lookup n c = SOME (arity,e1) /\ subspt cs c /\ ~(n IN domain cs) ==>
    code_rel (:'ffi) c (insert n (arity,(HD (inline cs [e1]))) c)``,
  rw [] \\ match_mp_tac code_rel_insert \\ fs []
  \\ match_mp_tac exp_rel_inline
  \\ fs [subspt_def,domain_lookup,PULL_EXISTS,lookup_insert]
  \\ rw [] \\ res_tac \\ fs []);

val _ = export_theory();
