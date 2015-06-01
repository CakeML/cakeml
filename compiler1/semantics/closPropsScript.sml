open preamble closSemTheory

val _ = new_theory"closProps"

val Boolv_11 = store_thm("Boolv_11[simp]",``closSem$Boolv b1 = Boolv b2 ⇔ b1 = b2``,EVAL_TAC>>rw[]);

val evaluate_LENGTH_ind =
  evaluate_ind
  |> Q.SPEC `\(xs,s,env).
       (case evaluate (xs,s,env) of (Rval res,s1) => (LENGTH xs = LENGTH res)
            | _ => T)`
  |> Q.SPEC `\x1 x2 x3 x4.
       (case evaluate_app x1 x2 x3 x4 of (Rval res,s1) => (LENGTH res = 1)
            | _ => T)`

val evaluate_LENGTH = prove(evaluate_LENGTH_ind |> concl |> rand,
  MATCH_MP_TAC evaluate_LENGTH_ind
  \\ REPEAT STRIP_TAC \\ fs []
  \\ ONCE_REWRITE_TAC [evaluate_def] \\ fs []
  \\ BasicProvers.EVERY_CASE_TAC \\ fs [] \\ rfs [] \\ fs [])
  |> SIMP_RULE std_ss [FORALL_PROD]

val _ = save_thm("evaluate_LENGTH", evaluate_LENGTH);

val evaluate_IMP_LENGTH = store_thm("evaluate_IMP_LENGTH",
  ``(evaluate (xs,s,env) = (Rval res,s1)) ==> (LENGTH xs = LENGTH res)``,
  REPEAT STRIP_TAC
  \\ MP_TAC (evaluate_LENGTH |> CONJUNCT1 |> Q.SPECL [`xs`,`s`,`env`])
  \\ fs []);

val evaluate_app_IMP_LENGTH = store_thm("evaluate_app_IMP_LENGTH",
  ``(evaluate_app x1 x2 x3 x4 = (Rval res,s1)) ==> (LENGTH res = 1)``,
  REPEAT STRIP_TAC
  \\ MP_TAC (evaluate_LENGTH |> CONJUNCT2 |> Q.SPECL [`x1`,`x2`,`x3`,`x4`])
  \\ fs []);

val evaluate_SING = store_thm("evaluate_SING",
  ``(evaluate ([x],s,env) = (Rval r,s2)) ==> ?r1. r = [r1]``,
  REPEAT STRIP_TAC \\ IMP_RES_TAC evaluate_IMP_LENGTH
  \\ Cases_on `r` \\ fs [] \\ Cases_on `t` \\ fs []);

val evaluate_CONS = store_thm("evaluate_CONS",
  ``evaluate (x::xs,env,s) =
      case evaluate ([x],env,s) of
      | (Rval v,s2) =>
         (case evaluate (xs,env,s2) of
          | (Rval vs,s1) => (Rval (HD v::vs),s1)
          | t => t)
      | t => t``,
  Cases_on `xs` \\ fs [evaluate_def]
  \\ Cases_on `evaluate ([x],env,s)` \\ fs [evaluate_def]
  \\ Cases_on `q` \\ fs [evaluate_def]
  \\ IMP_RES_TAC evaluate_IMP_LENGTH
  \\ Cases_on `a` \\ fs []
  \\ Cases_on `t` \\ fs []);

val evaluate_SNOC = store_thm("evaluate_SNOC",
  ``!xs env s x.
      evaluate (SNOC x xs,env,s) =
      case evaluate (xs,env,s) of
      | (Rval vs,s2) =>
         (case evaluate ([x],env,s2) of
          | (Rval v,s1) => (Rval (vs ++ v),s1)
          | t => t)
      | t => t``,
  Induct THEN1
   (fs [SNOC_APPEND,evaluate_def] \\ REPEAT STRIP_TAC
    \\ Cases_on `evaluate ([x],env,s)` \\ Cases_on `q` \\ fs [])
  \\ fs [SNOC_APPEND,APPEND]
  \\ ONCE_REWRITE_TAC [evaluate_CONS]
  \\ REPEAT STRIP_TAC
  \\ Cases_on `evaluate ([h],env,s)` \\ Cases_on `q` \\ fs []
  \\ Cases_on `evaluate (xs,env,r)` \\ Cases_on `q` \\ fs []
  \\ Cases_on `evaluate ([x],env,r')` \\ Cases_on `q` \\ fs [evaluate_def]
  \\ IMP_RES_TAC evaluate_IMP_LENGTH
  \\ Cases_on `a''` \\ fs [LENGTH]
  \\ REV_FULL_SIMP_TAC std_ss [LENGTH_NIL] \\ fs []);

val evaluate_const_ind =
  evaluate_ind
  |> Q.SPEC `\(xs,env,s).
       (case evaluate (xs,env,s) of (_,s1) =>
          (s1.restrict_envs = s.restrict_envs) /\
          (s1.code = s.code))`
  |> Q.SPEC `\x1 x2 x3 x4.
       (case evaluate_app x1 x2 x3 x4 of (_,s1) =>
          (s1.restrict_envs = x4.restrict_envs) /\
          (s1.code = x4.code))`

val evaluate_const_lemma = prove(
  evaluate_const_ind |> concl |> rand,
  MATCH_MP_TAC evaluate_const_ind
  \\ REPEAT STRIP_TAC \\ fs []
  \\ ONCE_REWRITE_TAC [evaluate_def] \\ fs []
  \\ BasicProvers.EVERY_CASE_TAC \\ fs [] \\ rfs []
  \\ BasicProvers.EVERY_CASE_TAC \\ fs [] \\ rfs []
  \\ IMP_RES_TAC do_app_const \\ fs [dec_clock_def])
  |> SIMP_RULE std_ss [FORALL_PROD]

val evaluate_const = store_thm("evaluate_const",
  ``(evaluate (xs,env,s) = (res,s1)) ==>
      (s1.restrict_envs = s.restrict_envs) /\
      (s1.code = s.code)``,
  REPEAT STRIP_TAC
  \\ MP_TAC (evaluate_const_lemma |> CONJUNCT1 |> Q.SPECL [`xs`,`env`,`s`])
  \\ fs []);

val evaluate_app_const = store_thm("evaluate_app_const",
  ``(evaluate_app x1 x2 x3 x4 = (res,s1)) ==>
      (s1.restrict_envs = x4.restrict_envs) /\
      (s1.code = x4.code)``,
  REPEAT STRIP_TAC
  \\ MP_TAC (evaluate_const_lemma |> CONJUNCT2 |> Q.SPECL [`x1`,`x2`,`x3`,`x4`])
  \\ fs []);

val evaluate_MAP_Op_Const = store_thm("evaluate_MAP_Op_Const",
  ``∀f env s ls.
      evaluate (MAP (λx. Op (Const (f x)) []) ls,env,s) =
      (Rval (MAP (Number o f) ls),s)``,
  ntac 3 gen_tac >> Induct >>
  simp[evaluate_def] >>
  simp[Once evaluate_CONS] >>
  simp[evaluate_def,do_app_def])

val evaluate_REPLICATE_Op_AllocGlobal = store_thm("evaluate_REPLICATE_Op_AllocGlobal",
  ``∀n env s. evaluate (REPLICATE n (Op AllocGlobal []),env,s) =
              (Rval (GENLIST (K Unit) n),s with globals := s.globals ++ GENLIST (K NONE) n)``,
  Induct >> simp[evaluate_def,REPLICATE] >- (
    simp[state_component_equality] ) >>
  simp[Once evaluate_CONS,evaluate_def,do_app_def,GENLIST_CONS] >>
  simp[state_component_equality])

val _ = export_theory();
