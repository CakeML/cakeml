open preamble closLangTheory closSemTheory

val _ = new_theory"closProps"

val dec_clock_code = Q.store_thm("dec_clock_code",
  `(dec_clock x y).code = y.code`,
  EVAL_TAC);

val ref_rel_def = Define`
  (ref_rel R (ValueArray vs) (ValueArray ws) ⇔ LIST_REL R vs ws) ∧
  (ref_rel R (ByteArray as) (ByteArray bs) ⇔ as = bs) ∧
  (ref_rel _ _ _ = F)`
val _ = export_rewrites["ref_rel_def"];

val ref_rel_simp = Q.store_thm("ref_rel_simp[simp]",
  `(ref_rel R (ValueArray vs) y ⇔ ∃ws. y = ValueArray ws ∧ LIST_REL R vs ws) ∧
   (ref_rel R (ByteArray bs) y ⇔ y = ByteArray bs)`,
  Cases_on`y`>>simp[ref_rel_def] >> rw[EQ_IMP_THM])

val code_locs_def = tDefine "code_locs" `
  (code_locs [] = []) /\
  (code_locs (x::y::xs) =
     let c1 = code_locs [x] in
     let c2 = code_locs (y::xs) in
       c1 ++ c2) /\
  (code_locs [Var v] = []) /\
  (code_locs [If x1 x2 x3] =
     let c1 = code_locs [x1] in
     let c2 = code_locs [x2] in
     let c3 = code_locs [x3] in
       c1 ++ c2 ++ c3) /\
  (code_locs [Let xs x2] =
     let c1 = code_locs xs in
     let c2 = code_locs [x2] in
       c1 ++ c2) /\
  (code_locs [Raise x1] =
     code_locs [x1]) /\
  (code_locs [Tick x1] =
     code_locs [x1]) /\
  (code_locs [Op op xs] =
     code_locs xs) /\
  (code_locs [App loc_opt x1 xs] =
     let c1 = code_locs [x1] in
     let c2 = code_locs xs in
         c1++c2) /\
  (code_locs [Fn loc_opt vs num_args x1] =
     let loc = case loc_opt of NONE => 0 | SOME n => n in
     let c1 = code_locs [x1] in
       c1 ++ [loc]) /\
  (code_locs [Letrec loc_opt vs fns x1] =
     let loc = case loc_opt of NONE => 0 | SOME n => n in
     let c1 = code_locs (MAP SND fns) in
     let c2 = code_locs [x1] in
     c1 ++ GENLIST ($+ loc) (LENGTH fns) ++ c2) /\
  (code_locs [Handle x1 x2] =
     let c1 = code_locs [x1] in
     let c2 = code_locs [x2] in
       c1 ++ c2) /\
  (code_locs [Call dest xs] =
     code_locs xs)`
  (WF_REL_TAC `measure (exp3_size)`
   \\ REPEAT STRIP_TAC \\ TRY DECIDE_TAC >>
   Induct_on `fns` >>
   srw_tac [ARITH_ss] [exp_size_def] >>
   Cases_on `h` >>
   fs [exp_size_def] >>
   decide_tac);

val code_locs_cons = store_thm("code_locs_cons",
  ``∀x xs. code_locs (x::xs) = code_locs [x] ++ code_locs xs``,
  gen_tac >> Cases >> simp[code_locs_def]);

val code_locs_append = store_thm("code_locs_append",
  ``!l1 l2. code_locs (l1 ++ l2) = code_locs l1 ++ code_locs l2``,
  Induct >> simp[code_locs_def] >>
  simp[Once code_locs_cons] >>
  simp[Once code_locs_cons,SimpRHS]);

val code_locs_map = store_thm("code_locs_map",
  ``!xs f. code_locs (MAP f xs) = FLAT (MAP (\x. code_locs [f x]) xs)``,
  Induct \\ fs [code_locs_def]
  \\ ONCE_REWRITE_TAC [code_locs_cons] \\ fs [code_locs_def]);

val contains_App_SOME_def = tDefine "contains_App_SOME" `
  (contains_App_SOME [] ⇔ F) /\
  (contains_App_SOME (x::y::xs) ⇔
     contains_App_SOME [x] ∨
     contains_App_SOME (y::xs)) /\
  (contains_App_SOME [Var v] ⇔ F) /\
  (contains_App_SOME [If x1 x2 x3] ⇔
     contains_App_SOME [x1] ∨
     contains_App_SOME [x2] ∨
     contains_App_SOME [x3]) /\
  (contains_App_SOME [Let xs x2] ⇔
     contains_App_SOME [x2] ∨
     contains_App_SOME xs) /\
  (contains_App_SOME [Raise x1] ⇔
     contains_App_SOME [x1]) /\
  (contains_App_SOME [Tick x1] ⇔
     contains_App_SOME [x1]) /\
  (contains_App_SOME [Op op xs] ⇔
     contains_App_SOME xs) /\
  (contains_App_SOME [App loc_opt x1 x2] ⇔
     IS_SOME loc_opt ∨ max_app < LENGTH x2 ∨
     contains_App_SOME [x1] ∨
     contains_App_SOME x2) /\
  (contains_App_SOME [Fn loc vs num_args x1] ⇔
     contains_App_SOME [x1]) /\
  (contains_App_SOME [Letrec loc vs fns x1] ⇔
     contains_App_SOME (MAP SND fns) ∨
     contains_App_SOME [x1]) /\
  (contains_App_SOME [Handle x1 x2] ⇔
     contains_App_SOME [x1] ∨
     contains_App_SOME [x2]) /\
  (contains_App_SOME [Call dest xs] ⇔
     contains_App_SOME xs)`
  (WF_REL_TAC `measure (exp3_size)`
   \\ REPEAT STRIP_TAC \\ TRY DECIDE_TAC >>
   Induct_on `fns` >>
   srw_tac [ARITH_ss] [exp_size_def] >>
   Cases_on `h` >>
   fs [exp_size_def] >>
   decide_tac);

val contains_App_SOME_EXISTS = store_thm("contains_App_SOME_EXISTS",
  ``∀ls. contains_App_SOME ls ⇔ EXISTS (λx. contains_App_SOME [x]) ls``,
  Induct >> simp[contains_App_SOME_def] >>
  Cases_on`ls`>>fs[contains_App_SOME_def])

val every_Fn_SOME_def = tDefine "every_Fn_SOME" `
  (every_Fn_SOME [] ⇔ T) ∧
  (every_Fn_SOME (x::y::xs) ⇔
     every_Fn_SOME [x] ∧
     every_Fn_SOME (y::xs)) ∧
  (every_Fn_SOME [Var v] ⇔ T) ∧
  (every_Fn_SOME [If x1 x2 x3] ⇔
     every_Fn_SOME [x1] ∧
     every_Fn_SOME [x2] ∧
     every_Fn_SOME [x3]) ∧
  (every_Fn_SOME [Let xs x2] ⇔
     every_Fn_SOME [x2] ∧
     every_Fn_SOME xs) ∧
  (every_Fn_SOME [Raise x1] ⇔
     every_Fn_SOME [x1]) ∧
  (every_Fn_SOME [Tick x1] ⇔
     every_Fn_SOME [x1]) ∧
  (every_Fn_SOME [Op op xs] ⇔
     every_Fn_SOME xs) ∧
  (every_Fn_SOME [App loc_opt x1 x2] ⇔
     every_Fn_SOME [x1] ∧
     every_Fn_SOME x2) ∧
  (every_Fn_SOME [Fn loc_opt vs num_args x1] ⇔
     IS_SOME loc_opt ∧
     every_Fn_SOME [x1]) ∧
  (every_Fn_SOME [Letrec loc_opt vs fns x1] ⇔
     IS_SOME loc_opt ∧
     every_Fn_SOME (MAP SND fns) ∧
     every_Fn_SOME [x1]) ∧
  (every_Fn_SOME [Handle x1 x2] ⇔
     every_Fn_SOME [x1] ∧
     every_Fn_SOME [x2]) ∧
  (every_Fn_SOME [Call dest xs] ⇔
     every_Fn_SOME xs)`
  (WF_REL_TAC `measure (exp3_size)`
   \\ REPEAT STRIP_TAC \\ TRY DECIDE_TAC >>
   Induct_on `fns` >>
   srw_tac [ARITH_ss] [exp_size_def] >>
   Cases_on `h` >>
   fs [exp_size_def] >>
   decide_tac);
val _ = export_rewrites["every_Fn_SOME_def"];

val every_Fn_SOME_EVERY = store_thm("every_Fn_SOME_EVERY",
  ``∀ls. every_Fn_SOME ls ⇔ EVERY (λx. every_Fn_SOME [x]) ls``,
  Induct >> simp[every_Fn_SOME_def] >>
  Cases_on`ls`>>fs[every_Fn_SOME_def])

val fv_def = tDefine "fv" `
  (fv n [] <=> F) /\
  (fv n ((x:closLang$exp)::y::xs) <=>
     fv n [x] \/ fv n (y::xs)) /\
  (fv n [Var v] <=> (n = v)) /\
  (fv n [If x1 x2 x3] <=>
     fv n [x1] \/ fv n [x2] \/ fv n [x3]) /\
  (fv n [Let xs x2] <=>
     fv n xs \/ fv (n + LENGTH xs) [x2]) /\
  (fv n [Raise x1] <=> fv n [x1]) /\
  (fv n [Tick x1] <=> fv n [x1]) /\
  (fv n [Op op xs] <=> fv n xs) /\
  (fv n [App loc_opt x1 x2] <=>
     fv n [x1] \/ fv n x2) /\
  (fv n [Fn loc vs num_args x1] <=>
     fv (n + num_args) [x1]) /\
  (fv n [Letrec loc vs fns x1] <=>
     EXISTS (\(num_args, x). fv (n + num_args + LENGTH fns) [x]) fns \/ fv (n + LENGTH fns) [x1]) /\
  (fv n [Handle x1 x2] <=>
     fv n [x1] \/ fv (n+1) [x2]) /\
  (fv n [Call dest xs] <=> fv n xs)`
 (WF_REL_TAC `measure (exp3_size o SND)`
  \\ REPEAT STRIP_TAC \\ TRY DECIDE_TAC \\
  Induct_on `fns` >>
  srw_tac [ARITH_ss] [exp_size_def] >>
  res_tac >>
  srw_tac [ARITH_ss] [exp_size_def]);

val v_ind =
  TypeBase.induction_of``:closSem$v``
  |> Q.SPECL[`P`,`EVERY P`]
  |> SIMP_RULE(srw_ss())[]
  |> UNDISCH_ALL
  |> CONJUNCT1
  |> DISCH_ALL
  |> Q.GEN`P`
  |> curry save_thm "v_ind";

val do_app_err = Q.store_thm("do_app_err",
  `∀op ls s e.
     do_app op ls s = Rerr e ⇒
     (op ≠ Equal ⇒ ∃a. e = Rabort a)`,
  Cases >>
  rw[do_app_def] >>
  every_case_tac >> fs[LET_THM] >> rw[])

val Boolv_11 = store_thm("Boolv_11[simp]",``closSem$Boolv b1 = Boolv b2 ⇔ b1 = b2``,EVAL_TAC>>rw[]);

val do_eq_list_rel = store_thm("do_eq_list_rel",
  ``∀l1 l2 l3 l4.
     LENGTH l1 = LENGTH l2 ∧ LENGTH l3 = LENGTH l4 ∧
     LIST_REL (λp1 p2. UNCURRY do_eq p1 = UNCURRY do_eq p2) (ZIP(l1,l2)) (ZIP(l3,l4)) ⇒
     closSem$do_eq_list l1 l2 = do_eq_list l3 l4``,
   Induct >> simp[LENGTH_NIL_SYM] >- (
     simp[GSYM AND_IMP_INTRO, ZIP_EQ_NIL] ) >>
   gen_tac >> Cases >> simp[PULL_EXISTS] >>
   Cases >> simp[LENGTH_NIL_SYM] >>
   Cases >> simp[CONJUNCT2 do_eq_def] >>
   strip_tac >> BasicProvers.CASE_TAC >> rw[]);

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
  \\ ONCE_REWRITE_TAC [evaluate_def] \\ fs [LET_THM]
  \\ BasicProvers.EVERY_CASE_TAC \\ fs [] \\ rfs [] \\ fs [])
  |> SIMP_RULE std_ss [FORALL_PROD]

val _ = save_thm("evaluate_LENGTH", evaluate_LENGTH);

val evaluate_IMP_LENGTH = store_thm("evaluate_IMP_LENGTH",
  ``(evaluate (xs,s,env) = (Rval res,s1)) ==> (LENGTH xs = LENGTH res)``,
  REPEAT STRIP_TAC
  \\ (evaluate_LENGTH |> CONJUNCT1 |> Q.ISPECL_THEN [`xs`,`s`,`env`] MP_TAC)
  \\ fs []);

val evaluate_app_IMP_LENGTH = store_thm("evaluate_app_IMP_LENGTH",
  ``(evaluate_app x1 x2 x3 x4 = (Rval res,s1)) ==> (LENGTH res = 1)``,
  REPEAT STRIP_TAC
  \\ (evaluate_LENGTH |> CONJUNCT2 |> Q.ISPECL_THEN [`x1`,`x2`,`x3`,`x4`] MP_TAC)
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
  \\ ONCE_REWRITE_TAC [evaluate_def] \\ fs [LET_THM]
  \\ BasicProvers.EVERY_CASE_TAC \\ fs [] \\ rfs []
  \\ BasicProvers.EVERY_CASE_TAC \\ fs [] \\ rfs []
  \\ IMP_RES_TAC do_app_const \\ fs [dec_clock_def])
  |> SIMP_RULE std_ss [FORALL_PROD]

val evaluate_const = store_thm("evaluate_const",
  ``(evaluate (xs,env,s) = (res,s1)) ==>
      (s1.restrict_envs = s.restrict_envs) /\
      (s1.code = s.code)``,
  REPEAT STRIP_TAC
  \\ (evaluate_const_lemma |> CONJUNCT1 |> Q.ISPECL_THEN [`xs`,`env`,`s`] mp_tac)
  \\ fs []);

val evaluate_app_const = store_thm("evaluate_app_const",
  ``(evaluate_app x1 x2 x3 x4 = (res,s1)) ==>
      (s1.restrict_envs = x4.restrict_envs) /\
      (s1.code = x4.code)``,
  REPEAT STRIP_TAC
  \\ (evaluate_const_lemma |> CONJUNCT2 |> Q.ISPECL_THEN [`x1`,`x2`,`x3`,`x4`] mp_tac)
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

val lookup_vars_NONE = store_thm("lookup_vars_NONE",
  ``!vs. (lookup_vars vs env = NONE) <=> ?v. MEM v vs /\ LENGTH env <= v``,
  Induct \\ fs [lookup_vars_def]
  \\ REPEAT STRIP_TAC \\ fs []
  \\ Cases_on `h < LENGTH env` \\ fs [NOT_LESS]
  \\ Cases_on `lookup_vars vs env` \\ fs []
  THEN1 METIS_TAC []
  \\ CCONTR_TAC \\ fs [] \\ METIS_TAC [NOT_LESS]);

val lookup_vars_SOME = store_thm("lookup_vars_SOME",
  ``!vs env xs.
      (lookup_vars vs env = SOME xs) ==>
      (LENGTH vs = LENGTH xs)``,
  Induct \\ fs [lookup_vars_def] \\ REPEAT STRIP_TAC
  \\ Cases_on `lookup_vars vs env` \\ fs [] \\ SRW_TAC [] [] \\ RES_TAC);

val lookup_vars_MEM = prove(
  ``!ys n x (env2:closSem$v list).
      (lookup_vars ys env2 = SOME x) /\ n < LENGTH ys ==>
      (EL n ys) < LENGTH env2 /\
      (EL n x = EL (EL n ys) env2)``,
  Induct \\ fs [lookup_vars_def] \\ NTAC 5 STRIP_TAC
  \\ Cases_on `lookup_vars ys env2` \\ fs []
  \\ Cases_on `n` \\ fs [] \\ SRW_TAC [] [] \\ fs []) |> SPEC_ALL
  |> curry save_thm "lookup_vars_MEM";

val _ = export_theory();
