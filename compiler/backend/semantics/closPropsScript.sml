open preamble closLangTheory closSemTheory

val _ = new_theory"closProps"

(* TODO: move *)

val bool_case_eq = Q.store_thm("bool_case_eq",
  `COND b t f = v ⇔ b /\ v = t ∨ ¬b ∧ v = f`,
  srw_tac[][] >> metis_tac[]);

val pair_case_eq = Q.store_thm("pair_case_eq",
`pair_CASE x f = v ⇔ ?x1 x2. x = (x1,x2) ∧ f x1 x2 = v`,
 Cases_on `x` >>
 srw_tac[][]);

(* -- *)

val with_same_clock = Q.store_thm("with_same_clock[simp]",
  `(s:'ffi closSem$state) with clock := s.clock = s`,
  srw_tac[][closSemTheory.state_component_equality])

val dec_clock_code = Q.store_thm("dec_clock_code",
  `(dec_clock x y).code = y.code`,
  EVAL_TAC);

val dec_clock_ffi = Q.store_thm("dec_clock_ffi",
  `(dec_clock x y).ffi = y.ffi`,
  EVAL_TAC);

val ref_rel_def = Define`
  (ref_rel R (ValueArray vs) (ValueArray ws) ⇔ LIST_REL R vs ws) ∧
  (ref_rel R (ByteArray as) (ByteArray bs) ⇔ as = bs) ∧
  (ref_rel _ _ _ = F)`
val _ = export_rewrites["ref_rel_def"];

val ref_rel_simp = Q.store_thm("ref_rel_simp[simp]",
  `(ref_rel R (ValueArray vs) y ⇔ ∃ws. y = ValueArray ws ∧ LIST_REL R vs ws) ∧
   (ref_rel R (ByteArray bs) y ⇔ y = ByteArray bs)`,
  Cases_on`y`>>simp[ref_rel_def] >> srw_tac[][EQ_IMP_THM])

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
     c1 ++ GENLIST (λn. loc + 2*n) (LENGTH fns) ++ c2) /\
  (code_locs [Handle x1 x2] =
     let c1 = code_locs [x1] in
     let c2 = code_locs [x2] in
       c1 ++ c2) /\
  (code_locs [Call ticks dest xs] =
     code_locs xs)`
  (WF_REL_TAC `measure (exp3_size)`
   \\ REPEAT STRIP_TAC \\ TRY DECIDE_TAC >>
   Induct_on `fns` >>
   srw_tac [ARITH_ss] [exp_size_def] >>
   Cases_on `h` >>
   full_simp_tac(srw_ss())[exp_size_def] >>
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
  Induct \\ full_simp_tac(srw_ss())[code_locs_def]
  \\ ONCE_REWRITE_TAC [code_locs_cons] \\ full_simp_tac(srw_ss())[code_locs_def]);

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
  (contains_App_SOME [Call ticks dest xs] ⇔
     contains_App_SOME xs)`
  (WF_REL_TAC `measure (exp3_size)`
   \\ REPEAT STRIP_TAC \\ TRY DECIDE_TAC >>
   Induct_on `fns` >>
   srw_tac [ARITH_ss] [exp_size_def] >>
   Cases_on `h` >>
   full_simp_tac(srw_ss())[exp_size_def] >>
   decide_tac);

val contains_App_SOME_EXISTS = store_thm("contains_App_SOME_EXISTS",
  ``∀ls. contains_App_SOME ls ⇔ EXISTS (λx. contains_App_SOME [x]) ls``,
  Induct >> simp[contains_App_SOME_def] >>
  Cases_on`ls`>>full_simp_tac(srw_ss())[contains_App_SOME_def])

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
  (every_Fn_SOME [Call ticks dest xs] ⇔
     every_Fn_SOME xs)`
  (WF_REL_TAC `measure (exp3_size)`
   \\ REPEAT STRIP_TAC \\ TRY DECIDE_TAC >>
   Induct_on `fns` >>
   srw_tac [ARITH_ss] [exp_size_def] >>
   Cases_on `h` >>
   full_simp_tac(srw_ss())[exp_size_def] >>
   decide_tac);
val _ = export_rewrites["every_Fn_SOME_def"];

val every_Fn_SOME_EVERY = store_thm("every_Fn_SOME_EVERY",
  ``∀ls. every_Fn_SOME ls ⇔ EVERY (λx. every_Fn_SOME [x]) ls``,
  Induct >> simp[every_Fn_SOME_def] >>
  Cases_on`ls`>>full_simp_tac(srw_ss())[every_Fn_SOME_def])

val every_Fn_vs_NONE_def = tDefine "every_Fn_vs_NONE" `
  (every_Fn_vs_NONE [] ⇔ T) ∧
  (every_Fn_vs_NONE (x::y::xs) ⇔
     every_Fn_vs_NONE [x] ∧
     every_Fn_vs_NONE (y::xs)) ∧
  (every_Fn_vs_NONE [Var v] ⇔ T) ∧
  (every_Fn_vs_NONE [If x1 x2 x3] ⇔
     every_Fn_vs_NONE [x1] ∧
     every_Fn_vs_NONE [x2] ∧
     every_Fn_vs_NONE [x3]) ∧
  (every_Fn_vs_NONE [Let xs x2] ⇔
     every_Fn_vs_NONE [x2] ∧
     every_Fn_vs_NONE xs) ∧
  (every_Fn_vs_NONE [Raise x1] ⇔
     every_Fn_vs_NONE [x1]) ∧
  (every_Fn_vs_NONE [Tick x1] ⇔
     every_Fn_vs_NONE [x1]) ∧
  (every_Fn_vs_NONE [Op op xs] ⇔
     every_Fn_vs_NONE xs) ∧
  (every_Fn_vs_NONE [App loc_opt x1 x2] ⇔
     every_Fn_vs_NONE [x1] ∧
     every_Fn_vs_NONE x2) ∧
  (every_Fn_vs_NONE [Fn loc vs_opt num_args x1] ⇔
     IS_NONE vs_opt ∧
     every_Fn_vs_NONE [x1]) ∧
  (every_Fn_vs_NONE [Letrec loc vs_opt fns x1] ⇔
     IS_NONE vs_opt ∧
     every_Fn_vs_NONE (MAP SND fns) ∧
     every_Fn_vs_NONE [x1]) ∧
  (every_Fn_vs_NONE [Handle x1 x2] ⇔
     every_Fn_vs_NONE [x1] ∧
     every_Fn_vs_NONE [x2]) ∧
  (every_Fn_vs_NONE [Call ticks dest xs] ⇔
     every_Fn_vs_NONE xs)`
  (WF_REL_TAC `measure (exp3_size)`
   \\ REPEAT STRIP_TAC \\ TRY DECIDE_TAC >>
   Induct_on `fns` >>
   srw_tac [ARITH_ss] [exp_size_def] >>
   Cases_on `h` >>
   full_simp_tac(srw_ss())[exp_size_def] >>
   decide_tac);
val _ = export_rewrites["every_Fn_vs_NONE_def"];

val every_Fn_vs_NONE_EVERY = store_thm("every_Fn_vs_NONE_EVERY",
  ``∀ls. every_Fn_vs_NONE ls ⇔ EVERY (λx. every_Fn_vs_NONE [x]) ls``,
  Induct >> simp[every_Fn_vs_NONE_def] >>
  Cases_on`ls`>>full_simp_tac(srw_ss())[every_Fn_vs_NONE_def])

val every_Fn_vs_SOME_def = tDefine "every_Fn_vs_SOME" `
  (every_Fn_vs_SOME [] ⇔ T) ∧
  (every_Fn_vs_SOME (x::y::xs) ⇔
     every_Fn_vs_SOME [x] ∧
     every_Fn_vs_SOME (y::xs)) ∧
  (every_Fn_vs_SOME [Var v] ⇔ T) ∧
  (every_Fn_vs_SOME [If x1 x2 x3] ⇔
     every_Fn_vs_SOME [x1] ∧
     every_Fn_vs_SOME [x2] ∧
     every_Fn_vs_SOME [x3]) ∧
  (every_Fn_vs_SOME [Let xs x2] ⇔
     every_Fn_vs_SOME [x2] ∧
     every_Fn_vs_SOME xs) ∧
  (every_Fn_vs_SOME [Raise x1] ⇔
     every_Fn_vs_SOME [x1]) ∧
  (every_Fn_vs_SOME [Tick x1] ⇔
     every_Fn_vs_SOME [x1]) ∧
  (every_Fn_vs_SOME [Op op xs] ⇔
     every_Fn_vs_SOME xs) ∧
  (every_Fn_vs_SOME [App loc_opt x1 x2] ⇔
     every_Fn_vs_SOME [x1] ∧
     every_Fn_vs_SOME x2) ∧
  (every_Fn_vs_SOME [Fn loc vs_opt num_args x1] ⇔
     IS_SOME vs_opt ∧
     every_Fn_vs_SOME [x1]) ∧
  (every_Fn_vs_SOME [Letrec loc vs_opt fns x1] ⇔
     IS_SOME vs_opt ∧
     every_Fn_vs_SOME (MAP SND fns) ∧
     every_Fn_vs_SOME [x1]) ∧
  (every_Fn_vs_SOME [Handle x1 x2] ⇔
     every_Fn_vs_SOME [x1] ∧
     every_Fn_vs_SOME [x2]) ∧
  (every_Fn_vs_SOME [Call ticks dest xs] ⇔
     every_Fn_vs_SOME xs)`
  (WF_REL_TAC `measure (exp3_size)`
   \\ REPEAT STRIP_TAC \\ TRY DECIDE_TAC >>
   Induct_on `fns` >>
   srw_tac [ARITH_ss] [exp_size_def] >>
   Cases_on `h` >>
   full_simp_tac(srw_ss())[exp_size_def] >>
   decide_tac);
val _ = export_rewrites["every_Fn_vs_SOME_def"];

val every_Fn_vs_SOME_EVERY = store_thm("every_Fn_vs_SOME_EVERY",
  ``∀ls. every_Fn_vs_SOME ls ⇔ EVERY (λx. every_Fn_vs_SOME [x]) ls``,
  Induct >> simp[every_Fn_vs_SOME_def] >>
  Cases_on`ls`>>full_simp_tac(srw_ss())[every_Fn_vs_SOME_def])

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
  (fv n [Call ticks dest xs] <=> fv n xs)`
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
  srw_tac[][do_app_def] >>
  every_case_tac >> full_simp_tac(srw_ss())[LET_THM] >> srw_tac[][])

val Boolv_11 = store_thm("Boolv_11[simp]",``closSem$Boolv b1 = Boolv b2 ⇔ b1 = b2``,EVAL_TAC>>srw_tac[][]);

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
   strip_tac >> BasicProvers.CASE_TAC >> srw_tac[][]);

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
  \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[]
  \\ ONCE_REWRITE_TAC [evaluate_def] \\ full_simp_tac(srw_ss())[LET_THM]
  \\ BasicProvers.EVERY_CASE_TAC \\ full_simp_tac(srw_ss())[] \\ rev_full_simp_tac(srw_ss())[] \\ full_simp_tac(srw_ss())[])
  |> SIMP_RULE std_ss [FORALL_PROD]

val _ = save_thm("evaluate_LENGTH", evaluate_LENGTH);

val evaluate_IMP_LENGTH = store_thm("evaluate_IMP_LENGTH",
  ``(evaluate (xs,s,env) = (Rval res,s1)) ==> (LENGTH xs = LENGTH res)``,
  REPEAT STRIP_TAC
  \\ (evaluate_LENGTH |> CONJUNCT1 |> Q.ISPECL_THEN [`xs`,`s`,`env`] MP_TAC)
  \\ full_simp_tac(srw_ss())[]);

val evaluate_app_IMP_LENGTH = store_thm("evaluate_app_IMP_LENGTH",
  ``(evaluate_app x1 x2 x3 x4 = (Rval res,s1)) ==> (LENGTH res = 1)``,
  REPEAT STRIP_TAC
  \\ (evaluate_LENGTH |> CONJUNCT2 |> Q.ISPECL_THEN [`x1`,`x2`,`x3`,`x4`] MP_TAC)
  \\ full_simp_tac(srw_ss())[]);

val evaluate_SING = store_thm("evaluate_SING",
  ``(evaluate ([x],s,env) = (Rval r,s2)) ==> ?r1. r = [r1]``,
  REPEAT STRIP_TAC \\ IMP_RES_TAC evaluate_IMP_LENGTH
  \\ Cases_on `r` \\ full_simp_tac(srw_ss())[] \\ Cases_on `t` \\ full_simp_tac(srw_ss())[]);

val evaluate_CONS = store_thm("evaluate_CONS",
  ``evaluate (x::xs,env,s) =
      case evaluate ([x],env,s) of
      | (Rval v,s2) =>
         (case evaluate (xs,env,s2) of
          | (Rval vs,s1) => (Rval (HD v::vs),s1)
          | t => t)
      | t => t``,
  Cases_on `xs` \\ full_simp_tac(srw_ss())[evaluate_def]
  \\ Cases_on `evaluate ([x],env,s)` \\ full_simp_tac(srw_ss())[evaluate_def]
  \\ Cases_on `q` \\ full_simp_tac(srw_ss())[evaluate_def]
  \\ IMP_RES_TAC evaluate_IMP_LENGTH
  \\ Cases_on `a` \\ full_simp_tac(srw_ss())[]
  \\ Cases_on `t` \\ full_simp_tac(srw_ss())[]);

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
   (full_simp_tac(srw_ss())[SNOC_APPEND,evaluate_def] \\ REPEAT STRIP_TAC
    \\ Cases_on `evaluate ([x],env,s)` \\ Cases_on `q` \\ full_simp_tac(srw_ss())[])
  \\ full_simp_tac(srw_ss())[SNOC_APPEND,APPEND]
  \\ ONCE_REWRITE_TAC [evaluate_CONS]
  \\ REPEAT STRIP_TAC
  \\ Cases_on `evaluate ([h],env,s)` \\ Cases_on `q` \\ full_simp_tac(srw_ss())[]
  \\ Cases_on `evaluate (xs,env,r)` \\ Cases_on `q` \\ full_simp_tac(srw_ss())[]
  \\ Cases_on `evaluate ([x],env,r')` \\ Cases_on `q` \\ full_simp_tac(srw_ss())[evaluate_def]
  \\ IMP_RES_TAC evaluate_IMP_LENGTH
  \\ Cases_on `a''` \\ full_simp_tac(srw_ss())[LENGTH]
  \\ REV_FULL_SIMP_TAC std_ss [LENGTH_NIL] \\ full_simp_tac(srw_ss())[]);

val evaluate_const_ind =
  evaluate_ind
  |> Q.SPEC `\(xs,env,s).
       (case evaluate (xs,env,s) of (_,s1) =>
          (s1.code = s.code))`
  |> Q.SPEC `\x1 x2 x3 x4.
       (case evaluate_app x1 x2 x3 x4 of (_,s1) =>
          (s1.code = x4.code))`

val evaluate_const_lemma = prove(
  evaluate_const_ind |> concl |> rand,
  MATCH_MP_TAC evaluate_const_ind
  \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[]
  \\ ONCE_REWRITE_TAC [evaluate_def] \\ full_simp_tac(srw_ss())[LET_THM]
  \\ BasicProvers.EVERY_CASE_TAC \\ full_simp_tac(srw_ss())[] \\ rev_full_simp_tac(srw_ss())[]
  \\ BasicProvers.EVERY_CASE_TAC \\ full_simp_tac(srw_ss())[] \\ rev_full_simp_tac(srw_ss())[]
  \\ IMP_RES_TAC do_app_const \\ full_simp_tac(srw_ss())[dec_clock_def])
  |> SIMP_RULE std_ss [FORALL_PROD]

val evaluate_const = store_thm("evaluate_const",
  ``(evaluate (xs,env,s) = (res,s1)) ==>
      (s1.code = s.code)``,
  REPEAT STRIP_TAC
  \\ (evaluate_const_lemma |> CONJUNCT1 |> Q.ISPECL_THEN [`xs`,`env`,`s`] mp_tac)
  \\ full_simp_tac(srw_ss())[]);

val evaluate_app_const = store_thm("evaluate_app_const",
  ``(evaluate_app x1 x2 x3 x4 = (res,s1)) ==>
      (s1.code = x4.code)``,
  REPEAT STRIP_TAC
  \\ (evaluate_const_lemma |> CONJUNCT2 |> Q.ISPECL_THEN [`x1`,`x2`,`x3`,`x4`] mp_tac)
  \\ full_simp_tac(srw_ss())[]);

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
  Induct \\ full_simp_tac(srw_ss())[lookup_vars_def]
  \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[]
  \\ Cases_on `h < LENGTH env` \\ full_simp_tac(srw_ss())[NOT_LESS]
  \\ Cases_on `lookup_vars vs env` \\ full_simp_tac(srw_ss())[]
  THEN1 METIS_TAC []
  \\ CCONTR_TAC \\ full_simp_tac(srw_ss())[] \\ METIS_TAC [NOT_LESS]);

val lookup_vars_SOME = store_thm("lookup_vars_SOME",
  ``!vs env xs.
      (lookup_vars vs env = SOME xs) ==>
      (LENGTH vs = LENGTH xs)``,
  Induct \\ full_simp_tac(srw_ss())[lookup_vars_def] \\ REPEAT STRIP_TAC
  \\ Cases_on `lookup_vars vs env` \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] [] \\ RES_TAC);

val lookup_vars_MEM = prove(
  ``!ys n x (env2:closSem$v list).
      (lookup_vars ys env2 = SOME x) /\ n < LENGTH ys ==>
      (EL n ys) < LENGTH env2 /\
      (EL n x = EL (EL n ys) env2)``,
  Induct \\ full_simp_tac(srw_ss())[lookup_vars_def] \\ NTAC 5 STRIP_TAC
  \\ Cases_on `lookup_vars ys env2` \\ full_simp_tac(srw_ss())[]
  \\ Cases_on `n` \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[]) |> SPEC_ALL
  |> curry save_thm "lookup_vars_MEM";

val clock_lemmas = Q.store_thm ("clock_lemmas",
`!s. (s with clock := s.clock) = s`,
 srw_tac[][state_component_equality]);

val evaluate_app_rw = Q.store_thm ("evaluate_app_rw",
`(!args loc_opt f s.
  args ≠ [] ⇒
  evaluate_app loc_opt f args s =
    case dest_closure loc_opt f args of
       | NONE => (Rerr(Rabort Rtype_error),s)
       | SOME (Partial_app v) =>
           if s.clock < LENGTH args then
             (Rerr(Rabort Rtimeout_error),s with clock := 0)
           else (Rval [v], dec_clock (LENGTH args) s)
       | SOME (Full_app exp env rest_args) =>
           if s.clock < (LENGTH args - LENGTH rest_args) then
             (Rerr(Rabort Rtimeout_error),s with clock := 0)
           else
             case evaluate ([exp],env,dec_clock (LENGTH args - LENGTH rest_args) s) of
                | (Rval [v], s1) =>
                    evaluate_app loc_opt v rest_args s1
                | res => res)`,
 Cases_on `args` >>
 full_simp_tac(srw_ss())[evaluate_def]);

val op_thms = { nchotomy = op_nchotomy, case_def = op_case_def}
val list_thms = { nchotomy = list_nchotomy, case_def = list_case_def}
val option_thms = { nchotomy = option_nchotomy, case_def = option_case_def}
val v_thms = { nchotomy = v_nchotomy, case_def = v_case_def}
val ref_thms = { nchotomy = ref_nchotomy, case_def = ref_case_def}
val result_thms = { nchotomy = TypeBase.nchotomy_of ``:('a,'b)result``,
                    case_def = TypeBase.case_def_of ``:('a,'b)result`` }
val error_result_thms = { nchotomy = TypeBase.nchotomy_of ``:'a error_result``,
                          case_def = TypeBase.case_def_of ``:'a error_result`` }
val eq_result_thms = { nchotomy = TypeBase.nchotomy_of ``:eq_result``,
                       case_def = TypeBase.case_def_of ``:eq_result`` }
val appkind_thms = { nchotomy = TypeBase.nchotomy_of ``:app_kind``,
                     case_def = TypeBase.case_def_of ``:app_kind`` }
val word_size_thms = { nchotomy = TypeBase.nchotomy_of ``:word_size``,
                     case_def = TypeBase.case_def_of ``:word_size`` }
val eqs = LIST_CONJ (map prove_case_eq_thm [
  op_thms, list_thms, option_thms, v_thms, ref_thms, result_thms,
  eq_result_thms, error_result_thms, appkind_thms, word_size_thms])

val _ = save_thm ("eqs", eqs);

val EVERY_pure_correct = Q.store_thm("EVERY_pure_correct",
  `(∀t es E (s:'ffi closSem$state). t = (es,E,s) ∧ EVERY closLang$pure es ⇒
               case evaluate(es, E, s) of
                 (Rval vs, s') => s' = s ∧ LENGTH vs = LENGTH es
               | (Rerr (Rraise a), _) => F
               | (Rerr (Rabort a), _) => a = Rtype_error) ∧
   (∀(n: num option) (v:closSem$v)
     (vl : closSem$v list) (s : 'ffi closSem$state). T)`,
  ho_match_mp_tac evaluate_ind >> simp[pure_def] >>
  rpt strip_tac >> simp[evaluate_def]
  >- (every_case_tac >> full_simp_tac(srw_ss())[] >>
      rpt (qpat_assum `_ ==> _` mp_tac) >> simp[] >> full_simp_tac(srw_ss())[] >>
      full_simp_tac(srw_ss())[EVERY_MEM, EXISTS_MEM] >> metis_tac[])
  >- srw_tac[][]
  >- (full_simp_tac(srw_ss())[] >> every_case_tac >> full_simp_tac(srw_ss())[])
  >- (full_simp_tac (srw_ss() ++ ETA_ss) [] >> every_case_tac >> full_simp_tac(srw_ss())[])
  >- (full_simp_tac(srw_ss())[] >> every_case_tac >> full_simp_tac(srw_ss())[])
  >- (every_case_tac >> full_simp_tac(srw_ss())[] >>
      rename1 `pure_op opn` >> Cases_on `opn` >>
      full_simp_tac(srw_ss())[pure_op_def, do_app_def, eqs, bool_case_eq] >>
      srw_tac[][] >>
      rev_full_simp_tac(srw_ss() ++ ETA_ss) [] >>
      every_case_tac \\ fs[] >>
      full_simp_tac(srw_ss())[EVERY_MEM, EXISTS_MEM] >> metis_tac[])
  >- (every_case_tac >> simp[])
  >- (every_case_tac >> full_simp_tac(srw_ss())[])) |> SIMP_RULE (srw_ss()) []

val pure_correct = save_thm(
  "pure_correct",
  EVERY_pure_correct |> Q.SPECL [`[e]`, `env`, `s`]
                     |> SIMP_RULE (srw_ss()) [])

val pair_lam_lem = Q.prove (
`!f v z. (let (x,y) = z in f x y) = v ⇔ ∃x1 x2. z = (x1,x2) ∧ (f x1 x2 = v)`,
 srw_tac[][]);

val do_app_cases_val = save_thm ("do_app_cases_val",
``do_app op vs s = Rval (v,s')`` |>
  (SIMP_CONV (srw_ss()++COND_elim_ss) [PULL_EXISTS, do_app_def, eqs, pair_case_eq, pair_lam_lem] THENC
   SIMP_CONV (srw_ss()++COND_elim_ss) [LET_THM, eqs] THENC
   ALL_CONV));

val do_app_cases_err = save_thm ("do_app_cases_err",
``do_app op vs s = Rerr (Rraise v)`` |>
  (SIMP_CONV (srw_ss()++COND_elim_ss) [PULL_EXISTS, do_app_def, eqs, pair_case_eq, pair_lam_lem] THENC
   SIMP_CONV (srw_ss()++COND_elim_ss) [LET_THM, eqs] THENC
   ALL_CONV));

val do_app_cases_timeout = save_thm ("do_app_cases_timeout",
``do_app op vs s = Rerr (Rabort Rtimeout_error)`` |>
  (SIMP_CONV (srw_ss()++COND_elim_ss) [PULL_EXISTS, do_app_def, eqs, pair_case_eq, pair_lam_lem] THENC
   SIMP_CONV (srw_ss()++COND_elim_ss) [LET_THM, eqs] THENC
   ALL_CONV));

val do_app_cases_type_error = save_thm ("do_app_cases_type_error",
``do_app op vs s = Rerr (Rabort Rtype_error)`` |>
  (SIMP_CONV (srw_ss()++COND_elim_ss) [PULL_EXISTS, do_app_def, eqs, pair_case_eq, pair_lam_lem] THENC
   SIMP_CONV (srw_ss()++COND_elim_ss++boolSimps.DNF_ss) [LET_THM, eqs] THENC
   ALL_CONV));

val dest_closure_none_loc = Q.store_thm ("dest_closure_none_loc",
`!l cl vs v e env rest.
  (dest_closure l cl vs = SOME (Partial_app v) ⇒ l = NONE) ∧
  (dest_closure l cl vs = SOME (Full_app e env rest) ∧ rest ≠ [] ⇒ l = NONE)`,
 rpt gen_tac >>
 simp [dest_closure_def] >>
 Cases_on `cl` >>
 simp [] >>
 srw_tac[][] >>
 Cases_on `l` >>
 full_simp_tac(srw_ss())[check_loc_def] >>
 srw_tac[][] >>
 rev_full_simp_tac(srw_ss())[DROP_NIL] >>
 Cases_on `EL n l1` >>
 full_simp_tac(srw_ss())[] >>
 srw_tac[][] >>
 rev_full_simp_tac(srw_ss())[DROP_NIL]);

val is_closure_def = Define `
(is_closure (Closure _ _ _ _ _) ⇔ T) ∧
(is_closure (Recclosure _ _ _ _ _) ⇔ T) ∧
(is_closure _ ⇔ F)`;
val _ = export_rewrites ["is_closure_def"]

val clo_to_loc_def = Define `
(clo_to_loc (Closure l _ _ _ _) = l) ∧
(clo_to_loc (Recclosure l _ _ _ i) = OPTION_MAP ((+) (2 * i)) l)`;
val _ = export_rewrites ["clo_to_loc_def"]

val clo_to_env_def = Define `
(clo_to_env (Closure _ _ env _ _) = env) ∧
(clo_to_env (Recclosure loc _ env fns _) =
  GENLIST (Recclosure loc [] env fns) (LENGTH fns) ++ env)`;
val _ = export_rewrites ["clo_to_env_def"]

val clo_to_partial_args_def = Define `
(clo_to_partial_args (Closure _ args _ _ _) = args) ∧
(clo_to_partial_args (Recclosure _ args _ _ _) = args)`;
val _ = export_rewrites ["clo_to_partial_args_def"]

val clo_add_partial_args_def = Define `
(clo_add_partial_args args (Closure x1 args' x2 x3 x4) =
  Closure x1 (args ++ args') x2 x3 x4) ∧
(clo_add_partial_args args (Recclosure x1 args' x2 x3 x4) =
  Recclosure x1 (args ++ args') x2 x3 x4)`;
val _ = export_rewrites ["clo_add_partial_args_def"]

val clo_to_num_params_def = Define `
(clo_to_num_params (Closure _ _ _ n _) = n) ∧
(clo_to_num_params (Recclosure _ _ _ fns i) = FST (EL i fns))`;
val _ = export_rewrites ["clo_to_num_params_def"]

val rec_clo_ok_def = Define `
(rec_clo_ok (Recclosure _ _ _ fns i) ⇔ i < LENGTH fns) ∧
(rec_clo_ok (Closure _ _ _ _ _) ⇔ T)`;
val _ = export_rewrites ["rec_clo_ok_def"]

val dest_closure_full_length = Q.store_thm ("dest_closure_full_length",
`!l v vs e args rest.
  dest_closure l v vs = SOME (Full_app e args rest)
  ⇒
  LENGTH (clo_to_partial_args v) < clo_to_num_params v ∧
  LENGTH vs + LENGTH (clo_to_partial_args v) = clo_to_num_params v + LENGTH rest ∧
  LENGTH args = clo_to_num_params v + LENGTH (clo_to_env v)`,
 rpt gen_tac >>
 simp [dest_closure_def] >>
 BasicProvers.EVERY_CASE_TAC >>
 full_simp_tac(srw_ss())[is_closure_def, clo_to_partial_args_def, clo_to_num_params_def, clo_to_env_def]
 >- (`n - LENGTH l' ≤ LENGTH vs` by decide_tac >>
     srw_tac[][] >>
     simp [LENGTH_TAKE]) >>
 Cases_on `EL n l1` >>
 full_simp_tac(srw_ss())[] >>
 srw_tac[][] >>
 simp []);

val evaluate_app_clock_less = Q.store_thm ("evaluate_app_clock_less",
`!loc_opt f args s1 vs s2.
  args ≠ [] ∧
  evaluate_app loc_opt f args s1 = (Rval vs, s2)
  ⇒
  s2.clock < s1.clock`,
 srw_tac[][] >>
 rev_full_simp_tac(srw_ss())[evaluate_app_rw] >>
 BasicProvers.EVERY_CASE_TAC >>
 full_simp_tac(srw_ss())[] >>
 srw_tac[][] >>
 TRY decide_tac >>
 imp_res_tac evaluate_SING >>
 full_simp_tac(srw_ss())[] >>
 imp_res_tac evaluate_clock >>
 full_simp_tac(srw_ss())[dec_clock_def] >>
 imp_res_tac dest_closure_full_length >>
 TRY decide_tac >>
 Cases_on `args` >>
 full_simp_tac(srw_ss())[] >>
 decide_tac);

val clo_add_partial_args_nil = Q.store_thm ("clo_add_partial_args_nil[simp]",
`!x. is_closure x ⇒ clo_add_partial_args [] x = x`,
 Cases_on `x` >>
 srw_tac[][is_closure_def, clo_add_partial_args_def]);

val clo_can_apply_def = Define `
clo_can_apply loc cl num_args ⇔
  LENGTH (clo_to_partial_args cl) < clo_to_num_params cl ∧
  rec_clo_ok cl ∧
  (loc ≠ NONE ⇒
   loc = clo_to_loc cl ∧
   num_args = clo_to_num_params cl ∧
   clo_to_partial_args cl = [])`;

val check_closures_def = Define `
check_closures cl cl' ⇔
  !loc num_args.
    clo_can_apply loc cl num_args ⇒ clo_can_apply loc cl' num_args`;

val dest_closure_partial_is_closure = Q.store_thm(
  "dest_closure_partial_is_closure",
  `dest_closure l v vs = SOME (Partial_app v') ⇒
   is_closure v'`,
  dsimp[dest_closure_def, eqs, bool_case_eq, is_closure_def, UNCURRY]);

val is_closure_add_partial_args_nil = Q.store_thm(
  "is_closure_add_partial_args_nil",
  `is_closure v ⇒ (clo_add_partial_args [] v = v)`,
  Cases_on `v` >> simp[]);

val evaluate_app_clock0 = Q.store_thm(
  "evaluate_app_clock0",
  `s0.clock = 0 ∧ args ≠ [] ⇒
   evaluate_app lopt r args s0 ≠ (Rval vs, s)`,
  strip_tac >> `∃a1 args0. args = a1::args0` by (Cases_on `args` >> full_simp_tac(srw_ss())[]) >>
  simp[evaluate_def] >>
  Cases_on `dest_closure lopt r (a1::args0)` >> simp[] >>
  rename1 `dest_closure lopt r (a1::args0) = SOME c` >>
  Cases_on `c` >> simp[] >>
  rename1 `dest_closure lopt r (a1::args0) = SOME (Full_app b env rest)` >>
  srw_tac[][] >>
  `SUC (LENGTH args0) ≤ LENGTH rest` by simp[] >>
  imp_res_tac dest_closure_full_length >> lfs[])

val evaluate_app_clock_drop = Q.store_thm(
  "evaluate_app_clock_drop",
  `∀args f lopt s0 s vs.
     evaluate_app lopt f args s0 = (Rval vs, s) ⇒
     s.clock + LENGTH args ≤ s0.clock`,
  gen_tac >> completeInduct_on `LENGTH args` >>
  full_simp_tac (srw_ss() ++ DNF_ss) [] >> qx_gen_tac `args` >>
  `args = [] ∨ ∃a1 as. args = a1::as` by (Cases_on `args` >> simp[]) >>
  dsimp[evaluate_def, eqs, bool_case_eq, pair_case_eq, dec_clock_def] >>
  rpt strip_tac >> imp_res_tac evaluate_SING >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
  rename1 `evaluate_app lopt r1 args' s1` >>
  Cases_on `args' = []`
  >- (full_simp_tac(srw_ss())[evaluate_def] >> srw_tac[][] >> imp_res_tac evaluate_clock >> full_simp_tac(srw_ss())[] >> simp[])
  >- (`SUC (LENGTH as) ≤ LENGTH args' + s0.clock` by simp[] >>
      `LENGTH args' < SUC (LENGTH as)`
        by (imp_res_tac dest_closure_full_length >> lfs[]) >>
      `s.clock + LENGTH args' ≤ s1.clock` by metis_tac[] >>
      imp_res_tac evaluate_clock  >> full_simp_tac(srw_ss())[] >> simp[]))

val dest_closure_is_closure = Q.store_thm(
  "dest_closure_is_closure",
  `dest_closure lopt f vs = SOME r ⇒ is_closure f`,
  Cases_on `f` >> simp[is_closure_def, dest_closure_def]);

val stage_partial_app = Q.store_thm(
  "stage_partial_app",
  `is_closure c ∧
   dest_closure NONE v (rest ++ used) =
     SOME (Partial_app (clo_add_partial_args rest c)) ⇒
   dest_closure NONE c rest =
     SOME (Partial_app (clo_add_partial_args rest c))`,
  Cases_on `v` >> simp[dest_closure_def, eqs, bool_case_eq, UNCURRY] >>
  Cases_on `c` >>
  simp[clo_add_partial_args_def, is_closure_def, check_loc_def]);

val dest_closure_full_addargs = Q.store_thm(
  "dest_closure_full_addargs",
  `dest_closure NONE c vs = SOME (Full_app b env r) ∧
   LENGTH more + LENGTH vs ≤ max_app ⇒
   dest_closure NONE c (more ++ vs) = SOME (Full_app b env (more ++ r))`,
  Cases_on `c` >> csimp[dest_closure_def, bool_case_eq, revdroprev, UNCURRY] >>
  simp[DROP_APPEND1, revdroprev, TAKE_APPEND1, TAKE_APPEND2] >>
  simp[check_loc_def]);

val evaluate_append = Q.store_thm  ("evaluate_append",
`!es1 es2 env s.
  evaluate (es1 ++ es2, env, s) =
    case evaluate (es1, env, s) of
    | (Rval vs1, s') =>
        (case evaluate (es2, env, s') of
         | (Rval vs2, s'') => (Rval (vs1++vs2), s'')
         | x => x)
    | x => x`,
 Induct_on `es1` >>
 srw_tac[][evaluate_def]
 >- (
   every_case_tac >>
   srw_tac[][]) >>
 ONCE_REWRITE_TAC [evaluate_CONS] >>
 every_case_tac >>
 srw_tac[][]);

val evaluate_GENLIST_Var = Q.store_thm("evaluate_GENLIST_Var",
  `∀n env s.
   evaluate (GENLIST Var n, env, s) =
   if n ≤ LENGTH env then
     (Rval (TAKE n env),s)
   else
     (Rerr (Rabort Rtype_error),s)`,
  Induct \\ simp[evaluate_def,GENLIST,SNOC_APPEND,evaluate_append]
  \\ rw[]
  \\ REWRITE_TAC[GSYM SNOC_APPEND]
  \\ match_mp_tac SNOC_EL_TAKE
  \\ simp[]);

val evaluate_length_imp = Q.store_thm ("evaluate_length_imp",
`evaluate (es,env,s1) = (Rval vs, s2) ⇒ LENGTH es = LENGTH vs`,
 srw_tac[][] >>
 Q.ISPECL_THEN [`es`, `env`, `s1`] mp_tac (hd (CONJUNCTS evaluate_LENGTH)) >>
 srw_tac[][]);

val evaluate_app_length_imp = Q.store_thm ("evaluate_app_length_imp",
`evaluate_app l f args s = (Rval vs, s2) ⇒ LENGTH vs = 1`,
 srw_tac[][] >>
 Q.ISPECL_THEN [`l`, `f`, `args`, `s`] mp_tac (hd (tl (CONJUNCTS evaluate_LENGTH))) >>
 srw_tac[][]);

val dest_closure_none_append = Q.store_thm ("dest_closure_none_append",
`!l f args1 args2.
  dest_closure NONE f args2 = NONE ⇒
  dest_closure NONE f (args1 ++ args2) = NONE`,
 srw_tac[][dest_closure_def] >>
 Cases_on `f` >>
 full_simp_tac(srw_ss())[check_loc_def] >>
 srw_tac[][] >>
 full_simp_tac(srw_ss())[LET_THM] >>
 every_case_tac >>
 full_simp_tac(srw_ss())[] >>
 simp []);

val dest_closure_none_append2 = Q.store_thm ("dest_closure_none_append2",
`!l f args1 args2.
  LENGTH args1 + LENGTH args2 ≤ max_app ∧
  dest_closure NONE f (args1 ++ args2) = NONE ⇒
  dest_closure NONE f args2 = NONE`,
 srw_tac[][dest_closure_def] >>
 Cases_on `f` >>
 full_simp_tac(srw_ss())[check_loc_def] >>
 srw_tac[][] >>
 full_simp_tac(srw_ss())[LET_THM] >>
 every_case_tac >>
 full_simp_tac(srw_ss())[] >>
 simp []);

val dest_closure_rest_length = Q.store_thm ("dest_closure_rest_length",
`dest_closure NONE f args = SOME (Full_app e l rest) ⇒ LENGTH rest < LENGTH args`,
 simp [dest_closure_def] >>
 Cases_on `f` >>
 simp [check_loc_def]
 >- (srw_tac[][] >> simp []) >>
 Cases_on `EL n l1`
 >- (srw_tac[][] >> simp []));

val dest_closure_partial_twice = Q.store_thm ("dest_closure_partial_twice",
`∀f args1 args2 cl res.
  LENGTH args1 + LENGTH args2 ≤ max_app ∧
  dest_closure NONE f (args1 ++ args2) = res ∧
  dest_closure NONE f args2 = SOME (Partial_app cl)
  ⇒
  dest_closure NONE cl args1 = res`,
 simp [dest_closure_def] >>
 Cases_on `f` >>
 simp [check_loc_def]
 >- (
   Cases_on `cl` >>
   simp [] >>
   TRY (srw_tac[][] >> NO_TAC) >>
   srw_tac[][] >>
   simp [TAKE_APPEND, DROP_APPEND] >>
   full_simp_tac (srw_ss()++ARITH_ss) [NOT_LESS, NOT_LESS_EQUAL]
   >- (
     Q.ISPECL_THEN [`REVERSE args2`, `n - LENGTH l`] mp_tac TAKE_LENGTH_TOO_LONG >>
     srw_tac[][] >>
     full_simp_tac (srw_ss()++ARITH_ss) [])
   >- (
     Q.ISPECL_THEN [`REVERSE args2`, `n - LENGTH l`] mp_tac DROP_LENGTH_TOO_LONG >>
     srw_tac[][] >>
     full_simp_tac (srw_ss()++ARITH_ss) []) >>
   CCONTR_TAC >>
   full_simp_tac(srw_ss())[] >>
   srw_tac[][] >>
   full_simp_tac (srw_ss()++ARITH_ss) []) >>
 Cases_on `EL n l1` >>
 full_simp_tac(srw_ss())[] >>
 Cases_on `cl` >>
 simp [] >>
 TRY (srw_tac[][] >> NO_TAC) >>
 srw_tac[][] >>
 simp [TAKE_APPEND, DROP_APPEND] >>
 full_simp_tac (srw_ss()++ARITH_ss) [NOT_LESS, NOT_LESS_EQUAL] >>
 srw_tac[][]
 >- (
   Q.ISPECL_THEN [`REVERSE args2`, `q - LENGTH l`] mp_tac TAKE_LENGTH_TOO_LONG >>
   srw_tac[][] >>
   full_simp_tac (srw_ss()++ARITH_ss) [])
 >- (
   Q.ISPECL_THEN [`REVERSE args2`, `q - LENGTH l`] mp_tac DROP_LENGTH_TOO_LONG >>
   srw_tac[][] >>
   full_simp_tac (srw_ss()++ARITH_ss) []));

val evaluate_app_append = Q.store_thm ("evaluate_app_append",
`!args2 f args1 s.
  LENGTH (args1 ++ args2) ≤ max_app ⇒
  evaluate_app NONE f (args1 ++ args2) s =
    case evaluate_app NONE f args2 s of
    | (Rval vs1, s1) => evaluate_app NONE (HD vs1) args1 s1
    | err => err`,
 gen_tac >>
 completeInduct_on `LENGTH args2` >>
 srw_tac[][] >>
 Cases_on `args1++args2 = []`
 >- full_simp_tac(srw_ss())[evaluate_def, APPEND_eq_NIL] >>
 Cases_on `args2 = []`
 >- full_simp_tac(srw_ss())[evaluate_def, APPEND_eq_NIL] >>
 srw_tac[][evaluate_app_rw] >>
 `dest_closure NONE f args2 = NONE ∨ ?x. dest_closure NONE f args2 = SOME x` by metis_tac [option_nchotomy] >>
 full_simp_tac(srw_ss())[]
 >- (
   imp_res_tac dest_closure_none_append >>
   srw_tac[][]) >>
 Cases_on `x` >>
 full_simp_tac(srw_ss())[]
 >- ( (* args2 partial app *)
   `dest_closure NONE f (args1++args2) = NONE ∨
    ?x. dest_closure NONE f (args1++args2) = SOME x` by metis_tac [option_nchotomy] >>
   simp []
   >- (imp_res_tac dest_closure_none_append2 >> full_simp_tac(srw_ss())[]) >>
   imp_res_tac dest_closure_partial_twice >>
   srw_tac[][] >>
   simp [] >>
   Cases_on `x` >>
   simp [] >>
   full_simp_tac (srw_ss()++ARITH_ss) [NOT_LESS] >>
   imp_res_tac dest_closure_rest_length >>
   full_simp_tac (srw_ss()++ARITH_ss) [NOT_LESS] >>
   Cases_on `args1 = []` >>
   full_simp_tac (srw_ss()++ARITH_ss) [] >>
   full_simp_tac(srw_ss())[evaluate_app_rw, dec_clock_def] >>
   simp [evaluate_def] >>
   srw_tac[][] >>
   full_simp_tac (srw_ss()++ARITH_ss) [NOT_LESS])
 >- ( (* args2 full app *)
   imp_res_tac dest_closure_full_addargs >>
   simp [] >>
   srw_tac[][] >>
   every_case_tac >>
   imp_res_tac evaluate_SING >>
   full_simp_tac(srw_ss())[] >>
   srw_tac[][] >>
   first_x_assum (qspec_then `LENGTH l0` mp_tac) >>
   srw_tac[][] >>
   `LENGTH l0 < LENGTH args2` by metis_tac [dest_closure_rest_length] >>
   full_simp_tac(srw_ss())[] >>
   first_x_assum (qspec_then `l0` mp_tac) >>
   srw_tac[][] >>
   pop_assum (qspecl_then [`h`, `args1`, `r`] mp_tac) >>
   simp []));

val revnil = Q.prove(`[] = REVERSE l ⇔ l = []`,
  CONV_TAC (LAND_CONV (REWR_CONV EQ_SYM_EQ)) >> simp[])

val dest_closure_full_maxapp = Q.store_thm(
  "dest_closure_full_maxapp",
  `dest_closure NONE c vs = SOME (Full_app b env r) ∧ r ≠ [] ⇒
   LENGTH vs ≤ max_app`,
  Cases_on `c` >> simp[dest_closure_def, check_loc_def, UNCURRY]);

val dest_closure_full_split' = Q.store_thm(
  "dest_closure_full_split'",
  `dest_closure loc v vs = SOME (Full_app e env rest) ⇒
   ∃used.
    vs = rest ++ used ∧ dest_closure loc v used = SOME (Full_app e env [])`,
  simp[dest_closure_def] >> Cases_on `v` >>
  simp[bool_case_eq, revnil, DROP_NIL, DECIDE ``0n >= x ⇔ x = 0``, UNCURRY,
       NOT_LESS, DECIDE ``x:num >= y ⇔ y ≤ x``, DECIDE ``¬(x:num ≤ y) ⇔ y < x``]
  >- (strip_tac >> rename1 `TAKE (n - LENGTH l) (REVERSE vs)` >>
      dsimp[LENGTH_NIL] >> rveq >>
      simp[revdroprev] >>
      qexists_tac `DROP (LENGTH l + LENGTH vs - n) vs` >> simp[] >>
      reverse conj_tac
      >- (`vs = TAKE (LENGTH l + LENGTH vs - n) vs ++
                DROP (LENGTH l + LENGTH vs - n) vs`
             by simp[] >>
          pop_assum (fn th => CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV[th]))) >>
          simp[TAKE_APPEND1]) >>
      Cases_on `loc` >> lfs[check_loc_def]) >>
  simp[revdroprev] >> dsimp[LENGTH_NIL] >> rpt strip_tac >> rveq >>
  rename1 `vs = TAKE (LENGTH l + LENGTH vs - N) vs ++ _` >>
  qexists_tac `DROP (LENGTH l + LENGTH vs - N) vs` >> simp[] >>
  reverse conj_tac
  >- (`vs = TAKE (LENGTH l + LENGTH vs - N) vs ++
            DROP (LENGTH l + LENGTH vs - N) vs`
         by simp[] >>
      pop_assum (fn th => CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV[th]))) >>
      simp[TAKE_APPEND1]) >>
  Cases_on `loc` >> lfs[check_loc_def])

val dest_closure_partial_split = Q.store_thm (
  "dest_closure_partial_split",
`!v1 vs v2 n.
  dest_closure NONE v1 vs = SOME (Partial_app v2) ∧
  n ≤ LENGTH vs
  ⇒
  ?v3.
    dest_closure NONE v1 (DROP n vs) = SOME (Partial_app v3) ∧
    v2 = clo_add_partial_args (TAKE n vs) v3`,
 srw_tac[][dest_closure_def] >>
 Cases_on `v1` >>
 simp [] >>
 full_simp_tac(srw_ss())[check_loc_def]
 >- (Cases_on `LENGTH vs + LENGTH l < n'` >>
     full_simp_tac(srw_ss())[] >>
     srw_tac[][clo_add_partial_args_def] >>
     decide_tac) >>
 full_simp_tac(srw_ss())[LET_THM] >>
 Cases_on `EL n' l1` >>
 full_simp_tac(srw_ss())[] >>
 srw_tac[][clo_add_partial_args_def] >>
 full_simp_tac(srw_ss())[] >>
 simp [] >>
 Cases_on `LENGTH vs + LENGTH l < q` >>
 full_simp_tac(srw_ss())[] >>
 decide_tac);

val dest_closure_partial_split' = Q.store_thm(
  "dest_closure_partial_split'",
  `∀n v vs cl.
      dest_closure NONE v vs = SOME (Partial_app cl) ∧ n ≤ LENGTH vs ⇒
      ∃cl0 used rest.
         vs = rest ++ used ∧ LENGTH rest = n ∧
         dest_closure NONE v used = SOME (Partial_app cl0) ∧
         cl = clo_add_partial_args rest cl0`,
  rpt strip_tac >>
  IMP_RES_THEN
    (IMP_RES_THEN (qx_choose_then `cl0` strip_assume_tac))
    (REWRITE_RULE [GSYM AND_IMP_INTRO] dest_closure_partial_split) >>
  map_every qexists_tac [`cl0`, `DROP n vs`, `TAKE n vs`] >> simp[]);

val dest_closure_NONE_Full_to_Partial = Q.store_thm(
  "dest_closure_NONE_Full_to_Partial",
  `dest_closure NONE v (l1 ++ l2) = SOME (Full_app b env []) ∧ l1 ≠ [] ⇒
   ∃cl. dest_closure NONE v l2 = SOME (Partial_app cl) ∧
        dest_closure NONE cl l1 = SOME (Full_app b env [])`,
  Cases_on `v` >>
  dsimp[dest_closure_def, bool_case_eq, revnil, DROP_NIL, GREATER_EQ,
        check_loc_def, UNCURRY] >> srw_tac[][] >>
  `0 < LENGTH l1` by (Cases_on `l1` >> full_simp_tac(srw_ss())[]) >> simp[] >>
  simp[TAKE_APPEND2] >> Cases_on `l2` >> full_simp_tac(srw_ss())[]);

val dec_clock_with_clock = Q.store_thm("dec_clock_with_clock[simp]",
  `dec_clock s with clock := y = s with clock := y`,
  EVAL_TAC)

val do_app_add_to_clock = Q.store_thm("do_app_add_to_clock",
  `(do_app op vs (s with clock := s.clock + extra) =
    map_result (λ(v,s). (v,s with clock := s.clock + extra)) I (do_app op vs s))`,
  Cases_on`do_app op vs s` >>
  TRY(rename1`Rerr e`>>Cases_on`e`)>>
  TRY(rename1`Rval a`>>Cases_on`a`)>>
  TRY(rename1`Rabort a`>>Cases_on`a`)>>
  full_simp_tac(srw_ss())[do_app_cases_val,do_app_cases_err,do_app_cases_timeout] >>
  full_simp_tac(srw_ss())[LET_THM,
     semanticPrimitivesTheory.store_alloc_def,
     semanticPrimitivesTheory.store_lookup_def,
     semanticPrimitivesTheory.store_assign_def] >>
  srw_tac[][] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >>
  pop_assum(fn th => strip_assume_tac(CONV_RULE(REWR_CONV do_app_cases_type_error)th)) >>
  fsrw_tac[][do_app_def] >>
  every_case_tac >> fsrw_tac[][] >> srw_tac[][] >> fsrw_tac[][]);

val s = ``s:'ffi closSem$state``

val evaluate_add_to_clock = Q.store_thm("evaluate_add_to_clock",
  `(∀p es env ^s r s'.
       p = (es,env,s) ∧
       evaluate (es,env,s) = (r,s') ∧
       r ≠ Rerr (Rabort Rtimeout_error) ⇒
       evaluate (es,env,s with clock := s.clock + extra) =
         (r,s' with clock := s'.clock + extra)) ∧
   (∀loc_opt v rest_args ^s r s'.
       evaluate_app loc_opt v rest_args s = (r,s') ∧
       r ≠ Rerr (Rabort Rtimeout_error) ⇒
       evaluate_app loc_opt v rest_args (s with clock := s.clock + extra) =
         (r,s' with clock := s'.clock + extra))`,
  ho_match_mp_tac evaluate_ind >>
  srw_tac[][evaluate_def] >> full_simp_tac(srw_ss())[evaluate_def] >>
  TRY (
    rename1`Boolv T` >>
    first_assum(split_pair_case0_tac o lhs o concl) >> full_simp_tac(srw_ss())[] >>
    BasicProvers.CASE_TAC >> full_simp_tac(srw_ss())[] >>
    reverse(BasicProvers.CASE_TAC) >> full_simp_tac(srw_ss())[] >- (
      every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >> full_simp_tac(srw_ss())[] ) >>
    srw_tac[][] >> full_simp_tac(srw_ss())[] >- (
      every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] )
    >- (
      qpat_assum`_ = (r,_)`mp_tac >>
      BasicProvers.CASE_TAC >> full_simp_tac(srw_ss())[] )
    >> ( every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] )) >>
  TRY (
    rename1`dest_closure` >>
    BasicProvers.CASE_TAC >> full_simp_tac(srw_ss())[] >>
    BasicProvers.CASE_TAC >> full_simp_tac(srw_ss())[] >>
    BasicProvers.CASE_TAC >> full_simp_tac(srw_ss())[] >>
    every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
    imp_res_tac evaluate_length_imp >>
    fsrw_tac[ARITH_ss][] >> rev_full_simp_tac(srw_ss())[] >>
    full_simp_tac(srw_ss())[dec_clock_def] >>
    simp[state_component_equality] >>
    rename1`extra + (s.clock - (SUC n - m))` >>
    `extra + (s.clock - (SUC n - m)) = extra + s.clock - (SUC n - m)` by DECIDE_TAC >>
    full_simp_tac(srw_ss())[] >> srw_tac[][] ) >>
  unabbrev_all_tac >>
  every_case_tac >> full_simp_tac(srw_ss())[do_app_add_to_clock,LET_THM] >> srw_tac[][] >> rev_full_simp_tac(srw_ss())[] >>
  every_case_tac >> full_simp_tac(srw_ss())[do_app_add_to_clock,LET_THM] >> srw_tac[][] >> rev_full_simp_tac(srw_ss())[] >>
  rev_full_simp_tac(srw_ss()++ARITH_ss)[dec_clock_def]);

val do_app_io_events_mono = Q.prove(
  `do_app op vs s = Rval(v,s') ⇒
   s.ffi.io_events ≼ s'.ffi.io_events ∧
   (IS_SOME s.ffi.final_event ⇒ s'.ffi = s.ffi)`,
  srw_tac[][do_app_cases_val] >>
  full_simp_tac(srw_ss())[LET_THM,
     semanticPrimitivesTheory.store_alloc_def,
     semanticPrimitivesTheory.store_lookup_def,
     semanticPrimitivesTheory.store_assign_def] >> srw_tac[][] >>
  full_simp_tac(srw_ss())[ffiTheory.call_FFI_def] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][]);

val evaluate_io_events_mono = Q.store_thm("evaluate_io_events_mono",
  `(∀p. ((SND(SND p)):'ffi closSem$state).ffi.io_events ≼ (SND (evaluate p)).ffi.io_events ∧
    (IS_SOME (SND(SND p)).ffi.final_event ⇒ (SND (evaluate p)).ffi = (SND(SND p)).ffi)) ∧
   (∀loc_opt v rest ^s.
     s.ffi.io_events ≼ (SND(evaluate_app loc_opt v rest s)).ffi.io_events ∧
     (IS_SOME s.ffi.final_event ⇒ (SND(evaluate_app loc_opt v rest s)).ffi = s.ffi))`,
  ho_match_mp_tac evaluate_ind >> srw_tac[][evaluate_def] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >> rev_full_simp_tac(srw_ss())[] >> full_simp_tac(srw_ss())[dec_clock_def] >>
  metis_tac[IS_PREFIX_TRANS,do_app_io_events_mono]);

val evaluate_io_events_mono_imp = Q.prove(
  `evaluate (es,env,s) = (r,s') ⇒
    s.ffi.io_events ≼ s'.ffi.io_events ∧
    (IS_SOME s.ffi.final_event ⇒ s'.ffi = s.ffi)`,
  metis_tac[evaluate_io_events_mono,FST,SND,PAIR])

val with_clock_ffi = Q.prove(
  `(s with clock := k).ffi = s.ffi`,EVAL_TAC)
val lemma = DECIDE``¬(x < y - z) ⇒ ((a:num) + x - (y - z) = x - (y - z) + a)``
val lemma2 = DECIDE``x ≠ 0n ⇒ a + (x - 1) = a + x - 1``
val lemma3 = DECIDE``¬(x:num < t+1) ⇒ a + (x - (t+1)) = a + x - (t+1)``

val tac =
  imp_res_tac evaluate_add_to_clock >> rev_full_simp_tac(srw_ss())[] >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
  imp_res_tac evaluate_io_events_mono_imp >> full_simp_tac(srw_ss())[] >> srw_tac[][] >> rev_full_simp_tac(srw_ss())[] >>
  full_simp_tac(srw_ss())[dec_clock_def] >> full_simp_tac(srw_ss())[do_app_add_to_clock] >>
  TRY(first_assum(split_uncurry_arg_tac o rhs o concl) >> full_simp_tac(srw_ss())[]) >>
  imp_res_tac do_app_io_events_mono >>
  fsrw_tac[ARITH_ss][AC ADD_ASSOC ADD_COMM] >>
  metis_tac[evaluate_io_events_mono,with_clock_ffi,FST,SND,IS_PREFIX_TRANS,lemma,Boolv_11,lemma2,lemma3]

val evaluate_add_to_clock_io_events_mono = Q.store_thm("evaluate_add_to_clock_io_events_mono",
  `(∀p es env ^s.
     p = (es,env,s) ⇒
     (SND(evaluate p)).ffi.io_events ≼
     (SND(evaluate (es,env,s with clock := s.clock + extra))).ffi.io_events ∧
     (IS_SOME((SND(evaluate p)).ffi.final_event) ⇒
      (SND(evaluate (es,env,s with clock := s.clock + extra))).ffi
      = ((SND(evaluate p)).ffi))) ∧
   (∀l v r ^s.
     (SND(evaluate_app l v r s)).ffi.io_events ≼
     (SND(evaluate_app l v r (s with clock := s.clock + extra))).ffi.io_events ∧
     (IS_SOME((SND(evaluate_app l v r s)).ffi.final_event) ⇒
       (SND(evaluate_app l v r (s with clock := s.clock + extra))).ffi
       = (SND(evaluate_app l v r s)).ffi))`,
  ho_match_mp_tac evaluate_ind >> srw_tac[][evaluate_def] >>
  TRY (
    rename1`Boolv T` >>
    qmatch_assum_rename_tac`IS_SOME _.ffi.final_event` >>
    ntac 6 (BasicProvers.CASE_TAC >> full_simp_tac(srw_ss())[] >> rev_full_simp_tac(srw_ss())[]) >>
    srw_tac[][] >> full_simp_tac(srw_ss())[] >> rev_full_simp_tac(srw_ss())[] >> tac) >>
  TRY (
    rename1`dest_closure` >>
    ntac 4 (BasicProvers.CASE_TAC >> full_simp_tac(srw_ss())[] >> rev_full_simp_tac(srw_ss())[dec_clock_ffi]) >>
    every_case_tac >> full_simp_tac(srw_ss())[] >> rev_full_simp_tac(srw_ss())[] >> full_simp_tac(srw_ss())[dec_clock_def] >>
    imp_res_tac lemma >> full_simp_tac(srw_ss())[] >>
    fsrw_tac[ARITH_ss][] >> tac) >>
  unabbrev_all_tac >> full_simp_tac(srw_ss())[LET_THM] >>
  every_case_tac >> full_simp_tac(srw_ss())[evaluate_def] >>
  tac)

val do_app_never_timesout = Q.store_thm(
  "do_app_never_timesout[simp]",
  `do_app op args s ≠ Rerr (Rabort Rtimeout_error)`,
  Cases_on `op` >> Cases_on `args` >>
  simp[do_app_def, eqs, bool_case_eq, pair_case_eq]);

val evaluate_timeout_clocks0 = Q.store_thm(
  "evaluate_timeout_clocks0",
  `(∀v (s:α closSem$state).
      evaluate v = (Rerr (Rabort Rtimeout_error), s) ⇒ s.clock = 0) ∧
   (∀locopt v env (s:α closSem$state) s'.
       evaluate_app locopt v env s = (Rerr (Rabort Rtimeout_error), s') ⇒
       s'.clock = 0)`,
  ho_match_mp_tac evaluate_ind >> rpt conj_tac >>
  dsimp[evaluate_def, eqs, pair_case_eq, bool_case_eq])

val _ = export_theory();
