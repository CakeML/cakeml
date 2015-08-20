open preamble
     bvlSemTheory bvlPropsTheory
     bvl_inlineTheory;

val _ = new_theory"bvl_inlineProof";

fun split_tac q = Cases_on q \\ Cases_on `q` \\ FULL_SIMP_TAC (srw_ss()) [];

val evaluate_inline = Q.store_thm("evaluate_inline",
  `!n code arity xs s env.
     (lookup n s.code = SOME (arity,code)) /\
     FST (evaluate (xs,env,s)) <> Rerr(Rabort Rtype_error) ==>
     (evaluate (inline n code arity xs,env,s) = evaluate (xs,env,s))`,
  recInduct inline_ind \\ reverse (REPEAT STRIP_TAC)
  \\ POP_ASSUM MP_TAC \\ SIMP_TAC std_ss [Once inline_def,LET_DEF] \\ RES_TAC
  THEN1 (reverse (Cases_on `(dest = SOME n) /\ (LENGTH xs = arity)`)
    \\ ASM_SIMP_TAC std_ss []
    \\ ONCE_REWRITE_TAC [evaluate_def] \\ ASM_SIMP_TAC std_ss [HD_inline]
    \\ Cases_on `evaluate (xs,env,s)` \\ FULL_SIMP_TAC std_ss []
    \\ Cases_on `q` \\ FULL_SIMP_TAC (srw_ss()) [LET_DEF]
    \\ FULL_SIMP_TAC std_ss [find_code_def]
    \\ IMP_RES_TAC evaluate_code
    \\ IMP_RES_TAC evaluate_IMP_LENGTH
    \\ FULL_SIMP_TAC (srw_ss()) []
    \\ SIMP_TAC std_ss [Once evaluate_def, evaluate_mk_tick] \\ SRW_TAC [] []
    \\ FULL_SIMP_TAC (srw_ss()) [ADD1]
    \\ MATCH_MP_TAC evaluate_expand_env \\ FULL_SIMP_TAC std_ss [])
  \\ ONCE_REWRITE_TAC [evaluate_def] \\ ASM_SIMP_TAC std_ss [HD_inline]
  \\ TRY (SRW_TAC [] [] \\ FIRST_X_ASSUM MATCH_MP_TAC
          \\ FULL_SIMP_TAC (srw_ss()) [dec_clock_def] \\ NO_TAC)
  \\ TRY (split_tac `evaluate (xs,env,s)`
     \\ IMP_RES_TAC evaluate_code \\ FULL_SIMP_TAC (srw_ss()) [] \\ NO_TAC)
  \\ TRY (split_tac `evaluate ([x1],env,s)` \\ SRW_TAC [] []
     \\ IMP_RES_TAC evaluate_code \\ FULL_SIMP_TAC (srw_ss()) []
     \\ Cases_on`e`>>fs[]>>NO_TAC)
  THEN1 (Cases_on `inline n code arity (y::xs)` THEN1
      (`LENGTH (inline n code arity (y::xs)) = 0` by METIS_TAC [LENGTH]
       \\ FULL_SIMP_TAC std_ss [LENGTH_inline,LENGTH] \\ `F` by DECIDE_TAC)
     \\ SIMP_TAC std_ss [Once evaluate_def,HD_inline]
     \\ POP_ASSUM (fn th => FULL_SIMP_TAC std_ss [GSYM th])
     \\ split_tac `evaluate ([x],env,s)` \\ split_tac `evaluate (y::xs,env,r)`
     \\ IMP_RES_TAC evaluate_code \\ FULL_SIMP_TAC (srw_ss()) []));

val _ = export_theory();
