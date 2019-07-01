(*
  Properties about BVL and its semantics
*)
open preamble bvlTheory bvlSemTheory bvl_constTheory;
open closPropsTheory backend_commonTheory;

val _ = new_theory"bvlProps";

val s = ``(s:('c,'ffi) bvlSem$state)``

Theorem with_same_code[simp]:
   ^s with code := s.code = s
Proof
  srw_tac[][bvlSemTheory.state_component_equality]
QED

Theorem with_same_clock[simp]:
   (st:('a,'b) bvlSem$state) with clock := st.clock = st
Proof
  rw[bvlSemTheory.state_component_equality]
QED

Theorem dec_clock_with_code[simp]:
   bvlSem$dec_clock n (s with code := c) = dec_clock n s with code := c
Proof
  EVAL_TAC
QED

fun get_thms ty = { case_def = TypeBase.case_def_of ty, nchotomy = TypeBase.nchotomy_of ty }
val case_eq_thms = LIST_CONJ (closSemTheory.case_eq_thms::
                              map (prove_case_eq_thm o get_thms)
  [``:v``,``:'a ffi_result``])
val case_eq_thms = CONJ bool_case_eq (CONJ pair_case_eq case_eq_thms)

val _ = save_thm ("case_eq_thms", case_eq_thms);

val do_app_split_list = prove(
  ``do_app op vs s = res
    <=>
    vs = [] /\ do_app op [] s = res \/
    ?v vs1. vs = v::vs1 /\ do_app op (v::vs1) s = res``,
  Cases_on `vs` \\ fs []);

val pair_lam_lem = Q.prove (
`!f v z. (let (x,y) = z in f x y) = v ⇔ ∃x1 x2. z = (x1,x2) ∧ (f x1 x2 = v)`,
 srw_tac[][]);

val do_app_cases_val = save_thm ("do_app_cases_val",
  ``do_app op vs s = Rval (v,s')`` |>
  (ONCE_REWRITE_CONV [do_app_split_list] THENC
   SIMP_CONV (srw_ss()++COND_elim_ss) [PULL_EXISTS, do_app_def, case_eq_thms, pair_case_eq, pair_lam_lem] THENC
   SIMP_CONV (srw_ss()++COND_elim_ss) [LET_THM, case_eq_thms] THENC
   ALL_CONV));

val do_app_cases_err = save_thm ("do_app_cases_err",
``do_app op vs s = Rerr err`` |>
  (ONCE_REWRITE_CONV [do_app_split_list] THENC
   SIMP_CONV (srw_ss()++COND_elim_ss) [PULL_EXISTS, do_app_def, case_eq_thms, pair_case_eq, pair_lam_lem] THENC
   SIMP_CONV (srw_ss()++COND_elim_ss) [LET_THM, case_eq_thms] THENC
   ALL_CONV));

Theorem do_app_Rval_swap:
   do_app op a (s1:('a,'b) bvlSem$state) = Rval (x0,x1) /\ op <> Install /\
    (domain s1.code) SUBSET (domain t1.code) ==>
    do_app op a
      ((t1:('c,'d) bvlSem$state) with
       <| globals := s1.globals; refs := s1.refs;
          clock := s1.clock; ffi := s1.ffi |>) = Rval
      (x0,t1 with
       <| globals := x1.globals; refs := x1.refs;
          clock := x1.clock; ffi := x1.ffi |>)
Proof
  rw[do_app_cases_val] \\ rfs[SUBSET_DEF] \\ fs []
  \\ strip_tac \\ res_tac \\ fs []
QED

Theorem do_app_with_code:
   bvlSem$do_app op vs s = Rval (r,s') /\ op <> Install ⇒
   domain s.code ⊆ domain c ⇒
   do_app op vs (s with <| code := c
                         ; compile := cc
                         ; compile_oracle := co |>) =
        Rval (r,s' with <| code := c
                         ; compile := cc
                         ; compile_oracle := co |>)
Proof
  rpt strip_tac
  \\ qmatch_goalsub_abbrev_tac `do_app _ _ s4`
  \\ drule (do_app_Rval_swap |> INST_TYPE [delta|->beta,gamma|->alpha] |> GEN_ALL)
  \\ disch_then (qspec_then `s4` mp_tac)
  \\ unabbrev_all_tac \\ fs []
  \\ qmatch_goalsub_abbrev_tac `do_app _ _ s1 = Rval (_,s2) ==>
                                do_app _ _ t1 = Rval (_,t2)`
  \\ qsuff_tac `t1 = s1 /\ t2 = s2` \\ rw []
  \\ unabbrev_all_tac \\ fs [state_component_equality]
QED

val do_app_Rerr_swap = time store_thm("do_app_Rerr_swap",
  ``do_app op a (s1:('a,'b) bvlSem$state) = Rerr e /\ op <> Install /\
    (domain t1.code) SUBSET (domain s1.code) ==>
    do_app op a
     ((t1:('c,'d) bvlSem$state) with
       <| globals := s1.globals; refs := s1.refs; clock := s1.clock;
          ffi := s1.ffi|> ) = Rerr e``,
  Cases_on `op` \\ rw[do_app_cases_err] \\ rfs[SUBSET_DEF] \\ fs []
  \\ strip_tac \\ res_tac \\ fs []);

Theorem do_app_with_code_err_not_Install:
   bvlSem$do_app op vs s = Rerr e /\ op <> Install ⇒
   (domain c ⊆ domain s.code ∨ e ≠ Rabort Rtype_error) ⇒
   do_app op vs (s with <| code := c
                         ; compile := cc
                         ; compile_oracle := co |>) = Rerr e
Proof
  rw [Once do_app_cases_err] >> rw [do_app_def] >> fs [SUBSET_DEF] >>
  fs [do_install_def,case_eq_thms,UNCURRY]
QED

Theorem do_app_with_code_err:
   bvlSem$do_app op vs s = Rerr e ⇒
   (domain c = domain s.code ∨ e ≠ Rabort Rtype_error) ⇒
   do_app op vs (s with code := c) = Rerr e
Proof
  rw [Once do_app_cases_err] >> rw [do_app_def] >> fs [SUBSET_DEF] >>
  fs [do_install_def,case_eq_thms,UNCURRY] >>
  rveq \\ fs [PULL_EXISTS]
  \\ CCONTR_TAC \\ fs []
  \\ rename1 `s.compile _ args = _`
  \\ qpat_x_assum `args = _` (fn th => fs [GSYM th])
  \\ Cases_on `s.compile (FST (s.compile_oracle 0)) args` \\ fs []
  \\ PairCases_on `x` \\ fs []
  \\ Cases_on `v6` \\ fs []
  \\ rveq \\ fs [] \\ rfs []
QED

Theorem initial_state_simp[simp]:
   (initial_state f c co cc k).code = c ∧
   (initial_state f c co cc k).ffi = f ∧
   (initial_state f c co cc k).clock = k ∧
   (initial_state f c co cc k).compile = cc ∧
   (initial_state f c co cc k).compile_oracle = co ∧
   (initial_state f c co cc k).refs = FEMPTY ∧
   (initial_state f c co cc k).globals = []
Proof
   srw_tac[][initial_state_def]
QED

Theorem initial_state_with_simp[simp]:
   initial_state f c co cc k with clock := k1 = initial_state f c co cc k1 ∧
   initial_state f c co cc k with code := c1 = initial_state f c1 co cc k
Proof
  EVAL_TAC
QED

Theorem bool_to_tag_11[simp]:
   bool_to_tag b1 = bool_to_tag b2 ⇔ (b1 = b2)
Proof
  srw_tac[][bool_to_tag_def] >> EVAL_TAC >> simp[]
QED

Theorem Boolv_11[simp]:
  bvlSem$Boolv b1 = Boolv b2 ⇔ b1 = b2
Proof
EVAL_TAC>>srw_tac[][]
QED

Theorem find_code_EVERY_IMP:
   (find_code dest a (r:('c,'ffi) bvlSem$state).code = SOME (q,t)) ==>
    EVERY P a ==> EVERY P q
Proof
  Cases_on `dest` \\ full_simp_tac(srw_ss())[find_code_def] \\ REPEAT STRIP_TAC
  \\ BasicProvers.EVERY_CASE_TAC \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[]
  \\ BasicProvers.EVERY_CASE_TAC \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[]
  \\ `?x1 l1. a = SNOC x1 l1` by METIS_TAC [SNOC_CASES] \\ full_simp_tac(srw_ss())[]
  \\ BasicProvers.EVERY_CASE_TAC \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[]
  \\ BasicProvers.EVERY_CASE_TAC \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[]
  \\ BasicProvers.EVERY_CASE_TAC \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[]
  \\ BasicProvers.EVERY_CASE_TAC \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[]
  \\ FULL_SIMP_TAC std_ss [GSYM SNOC_APPEND,FRONT_SNOC]
QED

Theorem do_app_err:
   do_app op vs s = Rerr e ⇒ (e = Rabort Rtype_error)
                             \/
                             (?i x. op = FFI i /\ e = Rabort (Rffi_error x))
Proof
  rw [do_app_cases_err,do_install_def,UNCURRY] >> fs []
  \\ every_case_tac \\ fs []
QED

val evaluate_LENGTH = Q.prove(
  `!xs s env. (\(xs,s,env).
      (case evaluate (xs,s,env) of (Rval res,s1) => (LENGTH xs = LENGTH res)
            | _ => T))
      (xs,s,env)`,
  HO_MATCH_MP_TAC evaluate_ind \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC (srw_ss()) [evaluate_def]
  \\ SRW_TAC [] [] \\ SRW_TAC [] []
  \\ BasicProvers.EVERY_CASE_TAC \\ FULL_SIMP_TAC (srw_ss()) []
  \\ REV_FULL_SIMP_TAC std_ss [] \\ FULL_SIMP_TAC (srw_ss()) [])
  |> SIMP_RULE std_ss [];

val _ = save_thm("evaluate_LENGTH", evaluate_LENGTH);

Theorem evaluate_IMP_LENGTH:
   (evaluate (xs,s,env) = (Rval res,s1)) ==> (LENGTH xs = LENGTH res)
Proof
  REPEAT STRIP_TAC \\ MP_TAC (SPEC_ALL evaluate_LENGTH) \\ full_simp_tac(srw_ss())[]
QED

Theorem evaluate_CONS:
   evaluate (x::xs,env,s) =
      case evaluate ([x],env,s) of
      | (Rval v,s2) =>
         (case evaluate (xs,env,s2) of
          | (Rval vs,s1) => (Rval (HD v::vs),s1)
          | t => t)
      | t => t
Proof
  Cases_on `xs` \\ full_simp_tac(srw_ss())[evaluate_def]
  \\ Cases_on `evaluate ([x],env,s)` \\ full_simp_tac(srw_ss())[evaluate_def]
  \\ Cases_on `q` \\ full_simp_tac(srw_ss())[evaluate_def]
  \\ IMP_RES_TAC evaluate_IMP_LENGTH
  \\ Cases_on `a` \\ full_simp_tac(srw_ss())[]
  \\ Cases_on `t` \\ full_simp_tac(srw_ss())[]
QED

Theorem evaluate_SNOC:
   !xs env s x.
      evaluate (SNOC x xs,env,s) =
      case evaluate (xs,env,s) of
      | (Rval vs,s2) =>
         (case evaluate ([x],env,s2) of
          | (Rval v,s1) => (Rval (vs ++ v),s1)
          | t => t)
      | t => t
Proof
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
  \\ REV_FULL_SIMP_TAC std_ss [LENGTH_NIL] \\ full_simp_tac(srw_ss())[]
QED

Theorem evaluate_APPEND:
   !xs env s ys.
      evaluate (xs ++ ys,env,s) =
      case evaluate (xs,env,s) of
        (Rval vs,s2) =>
          (case evaluate (ys,env,s2) of
             (Rval ws,s1) => (Rval (vs ++ ws),s1)
           | res => res)
      | res => res
Proof
  Induct \\ full_simp_tac(srw_ss())[APPEND,evaluate_def] \\ REPEAT STRIP_TAC
  THEN1 REPEAT BasicProvers.CASE_TAC
  \\ ONCE_REWRITE_TAC [evaluate_CONS]
  \\ REPEAT BasicProvers.CASE_TAC \\ full_simp_tac(srw_ss())[]
QED

Theorem evaluate_SING:
   (evaluate ([x],env,s) = (Rval a,p1)) ==> ?d1. a = [d1]
Proof
  REPEAT STRIP_TAC \\ IMP_RES_TAC evaluate_IMP_LENGTH
  \\ Cases_on `a` \\ full_simp_tac(srw_ss())[LENGTH_NIL]
QED

Theorem evaluate_code:
   !xs env s1 vs s2.
     (evaluate (xs,env,s1) = (vs,s2)) ==>
     ∃n.
       s2.compile_oracle = shift_seq n s1.compile_oracle ∧
       s2.code = FOLDL union s1.code (MAP (fromAList o SND)
         (GENLIST s1.compile_oracle n))
Proof
  recInduct evaluate_ind \\ rw []
  \\ pop_assum (mp_tac o SIMP_RULE std_ss[evaluate_def])
  THEN1
   (rw [] \\ qexists_tac `0` \\ fs [shift_seq_def,FUN_EQ_THM])
  THEN1
   (reverse (fs [case_eq_thms] \\ rw [] \\ fs []) THEN1 metis_tac []
    \\ qexists_tac `n+n'` \\ fs [shift_seq_def]
    \\ rewrite_tac [GENLIST_APPEND,FOLDL_APPEND,MAP_APPEND])
  THEN1 (rw [] \\ qexists_tac `0` \\ fs [shift_seq_def,FUN_EQ_THM])
  THEN1
   (reverse (fs [case_eq_thms] \\ rw [] \\ fs [])
    THEN1 metis_tac []
    THEN1 metis_tac []
    \\ pop_assum (assume_tac o GSYM) \\ fs []
    \\ qexists_tac `n'+n`
    \\ rewrite_tac [GENLIST_APPEND,FOLDL_APPEND,MAP_APPEND]
    \\ fs [shift_seq_def]
    \\ simp_tac std_ss [Once ADD_COMM] \\ fs [])
  THEN1
   (reverse (fs [case_eq_thms] \\ rw [] \\ fs []) THEN1 metis_tac []
    \\ qexists_tac `n+n'` \\ fs [shift_seq_def]
    \\ rewrite_tac [GENLIST_APPEND,FOLDL_APPEND,MAP_APPEND])
  THEN1
   (reverse (fs [case_eq_thms] \\ rw [] \\ fs [])
    THEN1 metis_tac []
    THEN1 metis_tac []
    \\ pop_assum (assume_tac o GSYM) \\ fs []
    \\ qexists_tac `n'+n`
    \\ rewrite_tac [GENLIST_APPEND,FOLDL_APPEND,MAP_APPEND]
    \\ fs [shift_seq_def]
    \\ simp_tac std_ss [Once ADD_COMM] \\ fs [])
  THEN1
   (reverse (fs [case_eq_thms] \\ rw [] \\ fs [])
    THEN1 metis_tac []
    THEN1
     (qexists_tac `n+n'` \\ fs [shift_seq_def]
      \\ rewrite_tac [GENLIST_APPEND,FOLDL_APPEND,MAP_APPEND])
    \\ metis_tac [])
  THEN1
   (reverse (fs [case_eq_thms] \\ rw [] \\ fs [])
    THEN1 metis_tac [] THEN1 metis_tac []
    \\ reverse (Cases_on `op = Install`)
    THEN1 (imp_res_tac do_app_const \\ qexists_tac `n` \\ fs [])
    \\ fs [do_app_def,do_install_def,case_eq_thms,UNCURRY] \\ rveq \\ fs []
    \\ qexists_tac `SUC n`
    \\ fs [shift_seq_def,FUN_EQ_THM,ADD1]
    \\ once_rewrite_tac [ADD_COMM]
    \\ rewrite_tac [GENLIST_APPEND,MAP_APPEND,EVAL ``GENLIST f 1``]
    \\ fs [FOLDL_APPEND] \\ rfs [])
  THEN1
   (fs [case_eq_thms] \\ rw [] \\ fs []
    THEN1 (qexists_tac `0` \\ fs [shift_seq_def,FUN_EQ_THM])
    \\ pop_assum (assume_tac o GSYM) \\ fs []
    \\ qexists_tac `n` \\ fs [dec_clock_def])
  \\ fs [case_eq_thms] \\ rw [] \\ fs []
  \\ TRY (qexists_tac `n` \\ fs [] \\ NO_TAC)
  \\ pop_assum (assume_tac o GSYM) \\ fs []
  \\ fs [dec_clock_def]
  \\ qexists_tac `n'+n`
  \\ rewrite_tac [GENLIST_APPEND,FOLDL_APPEND,MAP_APPEND]
  \\ fs [dec_clock_def,shift_seq_def,FUN_EQ_THM]
  \\ simp_tac std_ss [Once ADD_COMM] \\ fs []
QED

Theorem evaluate_mono:
   !xs env s1 vs s2.
     (evaluate (xs,env,s1) = (vs,s2)) ==>
     subspt s1.code s2.code
Proof
  rw[] \\ imp_res_tac evaluate_code
  \\ rw[] \\ metis_tac[subspt_FOLDL_union]
QED

Theorem evaluate_mk_tick:
   !exp env s n.
    evaluate ([mk_tick n exp], env, s) =
      if s.clock < n then
        (Rerr(Rabort Rtimeout_error), s with clock := 0)
      else
        evaluate ([exp], env, dec_clock n s)
Proof
  Induct_on `n` >>
  srw_tac[][mk_tick_def, evaluate_def, dec_clock_def, FUNPOW] >>
  full_simp_tac(srw_ss())[mk_tick_def, evaluate_def, dec_clock_def] >>
  srw_tac[][] >>
  full_simp_tac (srw_ss()++ARITH_ss) [dec_clock_def, ADD1]
  >- (`s.clock = n` by decide_tac >>
      full_simp_tac(srw_ss())[])
QED

Theorem evaluate_MAP_Const:
   !exps.
      evaluate (MAP (K (Op (Const i) [])) (exps:'a list),env,t1) =
        (Rval (MAP (K (Number i)) exps),t1)
Proof
  Induct \\ full_simp_tac(srw_ss())[evaluate_def,evaluate_CONS,do_app_def]
QED

Theorem evaluate_Bool[simp]:
   evaluate ([Bool b],env,s) = (Rval [Boolv b],s)
Proof
  EVAL_TAC
QED

fun split_tac q = Cases_on q \\ Cases_on `q` \\ FULL_SIMP_TAC (srw_ss()) []

Theorem evaluate_expand_env:
   !xs a s env.
     FST (evaluate (xs,a,s)) <> Rerr(Rabort Rtype_error) ==>
     (evaluate (xs,a ++ env,s) = evaluate (xs,a,s))
Proof
  recInduct evaluate_ind \\ REPEAT STRIP_TAC \\ POP_ASSUM MP_TAC
  \\ ONCE_REWRITE_TAC [evaluate_def] \\ ASM_SIMP_TAC std_ss []
  THEN1 (split_tac `evaluate ([x],env,s)` \\ split_tac `evaluate (y::xs,env,r)`)
  THEN1 (Cases_on `n < LENGTH env` \\ FULL_SIMP_TAC (srw_ss()) []
         \\ SRW_TAC [] [rich_listTheory.EL_APPEND1] \\ DECIDE_TAC)
  THEN1 (split_tac `evaluate ([x1],env,s)` \\ SRW_TAC [] [])
  THEN1 (split_tac `evaluate (xs,env,s)`)
  THEN1 (split_tac `evaluate ([x1],env,s)`)
  THEN1 (split_tac `evaluate ([x1],env,s1)` \\ BasicProvers.CASE_TAC >> simp[])
  THEN1 (split_tac `evaluate (xs,env,s)`)
  THEN1 (SRW_TAC [] [])
  THEN1 (split_tac `evaluate (xs,env,s1)`)
QED

val inc_clock_def = Define `
  inc_clock ck s = s with clock := s.clock + ck`;

Theorem inc_clock_code:
   !n ^s. (inc_clock n s).code = s.code
Proof
  srw_tac[][inc_clock_def]
QED

Theorem inc_clock_refs:
   !n ^s. (inc_clock n s).refs = s.refs
Proof
  srw_tac[][inc_clock_def]
QED

Theorem inc_clock_ffi[simp]:
   !n ^s. (inc_clock n s).ffi = s.ffi
Proof
  srw_tac[][inc_clock_def]
QED

Theorem inc_clock_clock[simp]:
   !n ^s. (inc_clock n s).clock = s.clock + n
Proof
  srw_tac[][inc_clock_def]
QED

Theorem inc_clock0:
   !n ^s. inc_clock 0 s = s
Proof
  simp [inc_clock_def, state_component_equality]
QED

val _ = export_rewrites ["inc_clock_refs", "inc_clock_code", "inc_clock0"];

Theorem inc_clock_add:
   inc_clock k1 (inc_clock k2 s) = inc_clock (k1 + k2) s
Proof
  simp[inc_clock_def,state_component_equality]
QED

Theorem dec_clock_code:
   !n ^s. (dec_clock n s).code = s.code
Proof
  srw_tac[][dec_clock_def]
QED

Theorem dec_clock_refs:
   !n ^s. (dec_clock n s).refs = s.refs
Proof
  srw_tac[][dec_clock_def]
QED

Theorem dec_clock_ffi[simp]:
   !n ^s. (dec_clock n s).ffi = s.ffi
Proof
  srw_tac[][dec_clock_def]
QED

Theorem dec_clock0:
   !n ^s. dec_clock 0 s = s
Proof
  simp [dec_clock_def, state_component_equality]
QED

val _ = export_rewrites ["dec_clock_refs", "dec_clock_code", "dec_clock0"];

Theorem do_app_change_clock:
   (do_app op args s1 = Rval (res,s2)) ==>
   (do_app op args (s1 with clock := ck) = Rval (res,s2 with clock := ck))
Proof
  rw [do_app_cases_val,UNCURRY,do_install_def]
  \\ every_case_tac \\ fs []
QED

Theorem do_app_change_clock_err:
   (do_app op args s1 = Rerr e) ==>
   (do_app op args (s1 with clock := ck) = Rerr e)
Proof
  disch_then (strip_assume_tac o SIMP_RULE (srw_ss()) [do_app_cases_err])
  \\ rveq \\ asm_simp_tac (srw_ss()) [do_app_def]
  \\ fs [] \\ every_case_tac \\ fs [] \\ rveq \\ fs []
  \\ fs [do_install_def,UNCURRY] \\ every_case_tac \\ fs [] \\ rw [] \\ fs []
QED

Theorem evaluate_add_clock:
   !exps env s1 res s2.
    evaluate (exps,env,s1) = (res, s2) ∧
    res ≠ Rerr(Rabort Rtimeout_error)
    ⇒
    !ck. evaluate (exps,env,inc_clock ck s1) = (res, inc_clock ck s2)
Proof
  recInduct evaluate_ind >>
  srw_tac[][evaluate_def]
  >- (Cases_on `evaluate ([x], env,s)` >> full_simp_tac(srw_ss())[] >>
      Cases_on `q` >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
      Cases_on `evaluate (y::xs,env,r)` >> full_simp_tac(srw_ss())[] >>
      Cases_on `q` >> full_simp_tac(srw_ss())[] >> srw_tac[][] >> full_simp_tac(srw_ss())[])
  >- (Cases_on `evaluate ([x1],env,s)` >> full_simp_tac(srw_ss())[] >>
      Cases_on `q` >> full_simp_tac(srw_ss())[] >> srw_tac[][] >> full_simp_tac(srw_ss())[])
  >- (Cases_on `evaluate (xs,env,s)` >>
      full_simp_tac(srw_ss())[] >>
      Cases_on `q` >>
      full_simp_tac(srw_ss())[] >>
      srw_tac[][] >> full_simp_tac(srw_ss())[])
  >- (Cases_on `evaluate (xs,env,s)` >> full_simp_tac(srw_ss())[] >>
      Cases_on `q` >> full_simp_tac(srw_ss())[] >> srw_tac[][] >> full_simp_tac(srw_ss())[] >>
      BasicProvers.EVERY_CASE_TAC >>
      full_simp_tac(srw_ss())[] >> srw_tac[][] >> full_simp_tac(srw_ss())[])
  >- (Cases_on `evaluate ([x1],env,s1)` >> full_simp_tac(srw_ss())[] >>
      Cases_on `q` >> full_simp_tac(srw_ss())[] >> srw_tac[][] >> full_simp_tac(srw_ss())[] >>
      Cases_on`e`>>full_simp_tac(srw_ss())[]>>srw_tac[][]>>full_simp_tac(srw_ss())[])
  >- (Cases_on `evaluate (xs,env,s)` >> full_simp_tac(srw_ss())[] >>
      Cases_on `q` >> full_simp_tac(srw_ss())[] >> srw_tac[][] >> full_simp_tac(srw_ss())[] >>
      srw_tac[][inc_clock_def] >>
      BasicProvers.EVERY_CASE_TAC >>
      full_simp_tac(srw_ss())[] >>
      imp_res_tac do_app_const >>
      imp_res_tac do_app_change_clock >>
      imp_res_tac do_app_change_clock_err >>
      full_simp_tac(srw_ss())[] >>
      srw_tac[][])
  >- (srw_tac[][] >>
      full_simp_tac(srw_ss())[inc_clock_def, dec_clock_def] >>
      srw_tac[][] >>
      `s.clock + ck - 1 = s.clock - 1 + ck` by (srw_tac [ARITH_ss] [ADD1]) >>
      metis_tac [])
  >- (Cases_on `evaluate (xs,env,s1)` >>
      full_simp_tac(srw_ss())[] >>
      Cases_on `q` >>
      full_simp_tac(srw_ss())[] >>
      srw_tac[][] >>
      BasicProvers.EVERY_CASE_TAC >>
      full_simp_tac(srw_ss())[] >>
      srw_tac[][] >>
      rev_full_simp_tac(srw_ss())[inc_clock_def, dec_clock_def] >>
      srw_tac[][]
      >- decide_tac >>
      `r.clock + ck - (ticks + 1) = r.clock - (ticks + 1) + ck` by srw_tac [ARITH_ss] [ADD1] >>
      metis_tac [])
QED

Theorem evaluate_add_clock_initial_state:
   evaluate (es,env,initial_state ffi code co cc k) = (r,s') ∧
    r ≠ Rerr (Rabort Rtimeout_error) ⇒
    ∀extra.
      evaluate (es,env,initial_state ffi code co cc (k + extra)) =
      (r,s' with clock := s'.clock + extra)
Proof
  rpt strip_tac
  \\ drule (GEN_ALL evaluate_add_clock) \\ fs []
  \\ fs [bvlSemTheory.initial_state_def,inc_clock_def]
QED

Theorem do_app_io_events_mono:
   do_app op vs s1 = Rval (x,s2) ⇒
   s1.ffi.io_events ≼ s2.ffi.io_events
Proof
  rw [do_app_cases_val] >>
  fs[ffiTheory.call_FFI_def,case_eq_thms] >>
  every_case_tac \\ fs[] \\ rw[] \\ rfs[do_install_def,UNCURRY] >>
  every_case_tac \\ fs[] \\ rw[] \\ rfs[do_install_def,UNCURRY]
QED

Theorem evaluate_io_events_mono:
   !exps env s1 res s2.
    evaluate (exps,env,s1) = (res, s2)
    ⇒
    s1.ffi.io_events ≼ s2.ffi.io_events
Proof
  recInduct evaluate_ind >>
  srw_tac[][evaluate_def] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >>
  srw_tac[][] >> rev_full_simp_tac(srw_ss())[] >>
  metis_tac[IS_PREFIX_TRANS,do_app_io_events_mono]
QED

Theorem Boolv_11[simp]:
  bvlSem$Boolv b1 = Boolv b2 ⇔ b1 = b2
Proof
EVAL_TAC>>srw_tac[][]
QED

val do_app_inc_clock = Q.prove(
  `do_app op vs (inc_clock x y) =
   map_result (λ(v,s). (v,s with clock := x + y.clock)) I (do_app op vs y)`,
  Cases_on`do_app op vs y` >>
  imp_res_tac do_app_change_clock_err >>
  TRY(Cases_on`a`>>imp_res_tac do_app_change_clock) >>
  full_simp_tac(srw_ss())[inc_clock_def] >> simp[])

val dec_clock_1_inc_clock = Q.prove(
  `x ≠ 0 ⇒ dec_clock 1 (inc_clock x s) = inc_clock (x-1) s`,
  simp[state_component_equality,inc_clock_def,dec_clock_def])

val dec_clock_1_inc_clock2 = Q.prove(
  `s.clock ≠ 0 ⇒ dec_clock 1 (inc_clock x s) = inc_clock x (dec_clock 1 s)`,
  simp[state_component_equality,inc_clock_def,dec_clock_def])

val dec_clock_inc_clock = Q.prove(
  `¬(s.clock < n) ⇒ dec_clock n (inc_clock x s) = inc_clock x (dec_clock n s)`,
  simp[state_component_equality,inc_clock_def,dec_clock_def])

Theorem evaluate_add_to_clock_io_events_mono:
   ∀exps env s extra.
    (SND(evaluate(exps,env,s))).ffi.io_events ≼
    (SND(evaluate(exps,env,inc_clock extra s))).ffi.io_events
Proof
  recInduct evaluate_ind >>
  srw_tac[][evaluate_def] >>
  TRY (
    rename1`Boolv T` >>
    ntac 4 (BasicProvers.CASE_TAC >> full_simp_tac(srw_ss())[] >> rev_full_simp_tac(srw_ss())[]) >>
    ntac 2 (TRY (BasicProvers.CASE_TAC >> full_simp_tac(srw_ss())[] >> rev_full_simp_tac(srw_ss())[])) >>
    srw_tac[][] >> full_simp_tac(srw_ss())[] >> rev_full_simp_tac(srw_ss())[]) >>
  every_case_tac >> full_simp_tac(srw_ss())[] >> rev_full_simp_tac(srw_ss())[] >>
  full_simp_tac(srw_ss())[dec_clock_1_inc_clock,dec_clock_1_inc_clock2] >>
  imp_res_tac evaluate_add_clock >> rev_full_simp_tac(srw_ss())[] >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
  imp_res_tac evaluate_io_events_mono >> rev_full_simp_tac(srw_ss())[] >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
  rev_full_simp_tac(srw_ss())[do_app_inc_clock] >> full_simp_tac(srw_ss())[] >> srw_tac[][] >> full_simp_tac(srw_ss())[] >>
  imp_res_tac do_app_io_events_mono >>
  TRY(fsrw_tac[ARITH_ss][] >>NO_TAC) >>
  full_simp_tac(srw_ss())[dec_clock_inc_clock] >>
  metis_tac[evaluate_io_events_mono,SND,IS_PREFIX_TRANS,Boolv_11,PAIR,
            inc_clock_ffi,dec_clock_ffi]
QED

val take_drop_lem = Q.prove (
  `!skip env.
    skip < LENGTH env ∧
    skip + SUC n ≤ LENGTH env ∧
    DROP skip env ≠ [] ⇒
    EL skip env::TAKE n (DROP (1 + skip) env) = TAKE (n + 1) (DROP skip env)`,
  Induct_on `n` >>
  srw_tac[][TAKE1, HD_DROP] >>
  `skip + SUC n ≤ LENGTH env` by decide_tac >>
  res_tac >>
  `LENGTH (DROP skip env) = LENGTH env - skip` by srw_tac[][LENGTH_DROP] >>
  `SUC n < LENGTH (DROP skip env)` by decide_tac >>
  `LENGTH (DROP (1 + skip) env) = LENGTH env - (1 + skip)` by srw_tac[][LENGTH_DROP] >>
  `n < LENGTH (DROP (1 + skip) env)` by decide_tac >>
  srw_tac[][TAKE_EL_SNOC, ADD1] >>
  `n + (1 + skip) < LENGTH env` by decide_tac >>
  `(n+1) + skip < LENGTH env` by decide_tac >>
  srw_tac[][EL_DROP] >>
  srw_tac [ARITH_ss] []);

Theorem evaluate_genlist_vars:
   !skip env n st.
    n + skip ≤ LENGTH env ⇒
    evaluate (GENLIST (λarg. Var (arg + skip)) n, env, st)
    =
    (Rval (TAKE n (DROP skip env)), st)
Proof
  Induct_on `n` >>
  srw_tac[][evaluate_def, DROP_LENGTH_NIL, GSYM ADD1] >>
  srw_tac[][Once GENLIST_CONS] >>
  srw_tac[][Once evaluate_CONS, evaluate_def] >>
  full_simp_tac (srw_ss()++ARITH_ss) [] >>
  first_x_assum (qspecl_then [`skip + 1`, `env`] mp_tac) >>
  srw_tac[][] >>
  `n + (skip + 1) ≤ LENGTH env` by decide_tac >>
  full_simp_tac(srw_ss())[] >>
  srw_tac[][combinTheory.o_DEF, ADD1, GSYM ADD_ASSOC] >>
  `skip + 1 = 1 + skip ` by decide_tac >>
  full_simp_tac(srw_ss())[] >>
  `LENGTH (DROP skip env) = LENGTH env - skip` by srw_tac[][LENGTH_DROP] >>
  `n < LENGTH env - skip` by decide_tac >>
  `DROP skip env ≠ []`
        by (Cases_on `DROP skip env` >>
            full_simp_tac(srw_ss())[] >>
            decide_tac) >>
  metis_tac [take_drop_lem]
QED

Theorem evaluate_var_reverse:
   !xs env ys (st:('c,'ffi) bvlSem$state).
   evaluate (MAP Var xs, env, st) = (Rval ys, st)
   ⇒
   evaluate (REVERSE (MAP Var xs), env, st) = (Rval (REVERSE ys), st)
Proof
  Induct_on `xs` >>
  srw_tac[][evaluate_def] >>
  full_simp_tac(srw_ss())[evaluate_APPEND] >>
  pop_assum (mp_tac o SIMP_RULE (srw_ss()) [Once evaluate_CONS]) >>
  srw_tac[][] >>
  BasicProvers.EVERY_CASE_TAC >>
  full_simp_tac(srw_ss())[evaluate_def] >>
  BasicProvers.EVERY_CASE_TAC >>
  srw_tac[][] >>
  res_tac >>
  full_simp_tac(srw_ss())[]
QED

Theorem evaluate_genlist_vars_rev:
   !skip env n st.
    n + skip ≤ LENGTH env ⇒
    evaluate (REVERSE (GENLIST (λarg. Var (arg + skip)) n), env, st) =
    (Rval (REVERSE (TAKE n (DROP skip env))), st)
Proof
  srw_tac[][] >>
  imp_res_tac evaluate_genlist_vars >>
  pop_assum (qspec_then `st` assume_tac) >>
  `GENLIST (λarg. Var (arg + skip):bvl$exp) n = MAP Var (GENLIST (\arg. arg + skip) n)`
           by srw_tac[][MAP_GENLIST, combinTheory.o_DEF] >>
  full_simp_tac(srw_ss())[] >>
  metis_tac [evaluate_var_reverse]
QED

Theorem do_app_refs_SUBSET:
   (do_app op a r = Rval (q,t)) ==> FDOM r.refs SUBSET FDOM t.refs
Proof
  rw [do_app_cases_val] >>
  fs [SUBSET_DEF,IN_INSERT,dec_clock_def,do_install_def] >>
  fs [UNCURRY] >> every_case_tac >> fs [] \\ rw [] \\ fs []
QED

val evaluate_refs_SUBSET_lemma = Q.prove(
  `!xs env s. FDOM s.refs SUBSET FDOM (SND (evaluate (xs,env,s))).refs`,
  recInduct evaluate_ind \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[evaluate_def]
  \\ BasicProvers.EVERY_CASE_TAC \\ full_simp_tac(srw_ss())[]
  \\ REV_FULL_SIMP_TAC std_ss []
  \\ IMP_RES_TAC SUBSET_TRANS
  \\ full_simp_tac(srw_ss())[dec_clock_def] \\ full_simp_tac(srw_ss())[]
  \\ IMP_RES_TAC do_app_refs_SUBSET \\ full_simp_tac(srw_ss())[SUBSET_DEF]);

Theorem evaluate_refs_SUBSET:
   (evaluate (xs,env,s) = (res,t)) ==> FDOM s.refs SUBSET FDOM t.refs
Proof
  REPEAT STRIP_TAC \\ MP_TAC (SPEC_ALL evaluate_refs_SUBSET_lemma) \\ full_simp_tac(srw_ss())[]
QED

val get_vars_def = Define `
  (get_vars [] env = SOME []) /\
  (get_vars (n::ns) env =
     if n < LENGTH env then
       (case get_vars ns env of
        | NONE => NONE
        | SOME vs => SOME (EL n env :: vs))
     else NONE)`

val isVar_def = Define `
  (isVar ((Var n):bvl$exp) = T) /\ (isVar _ = F)`;

val destVar_def = Define `
  (destVar ((Var n):bvl$exp) = n)`;

Theorem evaluate_Var_list:
   !l. EVERY isVar l ==>
       (evaluate (l,env,s) = (Rerr(Rabort Rtype_error),s)) \/
       ?vs. (evaluate (l,env,s) = (Rval vs,s)) /\
            (get_vars (MAP destVar l) env = SOME vs) /\
            (LENGTH vs = LENGTH l)
Proof
  Induct \\ full_simp_tac(srw_ss())[evaluate_def,get_vars_def] \\ Cases \\ full_simp_tac(srw_ss())[isVar_def]
  \\ ONCE_REWRITE_TAC [evaluate_CONS] \\ full_simp_tac(srw_ss())[evaluate_def]
  \\ Cases_on `n < LENGTH env` \\ full_simp_tac(srw_ss())[]
  \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[destVar_def]
QED

val bVarBound_def = tDefine "bVarBound" `
  (bVarBound n [] <=> T) /\
  (bVarBound n ((x:bvl$exp)::y::xs) <=>
     bVarBound n [x] /\ bVarBound n (y::xs)) /\
  (bVarBound n [Var v] <=> v < n) /\
  (bVarBound n [If x1 x2 x3] <=>
     bVarBound n [x1] /\ bVarBound n [x2] /\ bVarBound n [x3]) /\
  (bVarBound n [Let xs x2] <=>
     bVarBound n xs /\ bVarBound (n + LENGTH xs) [x2]) /\
  (bVarBound n [Raise x1] <=> bVarBound n [x1]) /\
  (bVarBound n [Tick x1] <=>  bVarBound n [x1]) /\
  (bVarBound n [Op op xs] <=> bVarBound n xs) /\
  (bVarBound n [Handle x1 x2] <=>
     bVarBound n [x1] /\ bVarBound (n + 1) [x2]) /\
  (bVarBound n [Call ticks dest xs] <=> bVarBound n xs)`
  (WF_REL_TAC `measure (exp1_size o SND)`
   \\ REPEAT STRIP_TAC \\ TRY DECIDE_TAC
   \\ SRW_TAC [] [bvlTheory.exp_size_def] \\ DECIDE_TAC);

val bEvery_def = tDefine "bEvery" `
  (bEvery P [] <=> T) /\
  (bEvery P ((x:bvl$exp)::y::xs) <=>
     bEvery P [x] /\ bEvery P (y::xs)) /\
  (bEvery P [Var v] <=> P (Var v)) /\
  (bEvery P [If x1 x2 x3] <=> P (If x1 x2 x3) /\
     bEvery P [x1] /\ bEvery P [x2] /\ bEvery P [x3]) /\
  (bEvery P [Let xs x2] <=> P (Let xs x2) /\
     bEvery P xs /\ bEvery P [x2]) /\
  (bEvery P [Raise x1] <=> P (Raise x1) /\ bEvery P [x1]) /\
  (bEvery P [Tick x1] <=> P (Tick x1) /\ bEvery P [x1]) /\
  (bEvery P [Op op xs] <=> P (Op op xs) /\ bEvery P xs) /\
  (bEvery P [Handle x1 x2] <=> P (Handle x1 x2) /\
     bEvery P [x1] /\ bEvery P [x2]) /\
  (bEvery P [Call ticks dest xs] <=> P (Call ticks dest xs) /\ bEvery P xs)`
  (WF_REL_TAC `measure (exp1_size o SND)`
   \\ REPEAT STRIP_TAC \\ TRY DECIDE_TAC
   \\ SRW_TAC [] [bvlTheory.exp_size_def] \\ DECIDE_TAC);

val _ = export_rewrites["bEvery_def","bVarBound_def"];

Theorem bVarBound_EVERY:
   ∀ls. bVarBound P ls ⇔ EVERY (λe. bVarBound P [e]) ls
Proof
  Induct >> simp[] >> Cases >> simp[] >>
  Cases_on`ls`>>simp[]
QED

Theorem bEvery_EVERY:
   ∀ls. bEvery P ls ⇔ EVERY (λe. bEvery P [e]) ls
Proof
  Induct >> simp[] >> Cases >> simp[] >>
  Cases_on`ls`>>simp[]
QED

val get_code_labels_def = tDefine"get_code_labels"
  `(get_code_labels (bvl$Var _) = {}) ∧
   (get_code_labels (If e1 e2 e3) = get_code_labels e1 ∪ get_code_labels e2 ∪ get_code_labels e3) ∧
   (get_code_labels (Let es e) = BIGUNION (set (MAP get_code_labels es)) ∪ get_code_labels e) ∧
   (get_code_labels (Raise e) = get_code_labels e) ∧
   (get_code_labels (Handle e1 e2) = get_code_labels e1 ∪ get_code_labels e2) ∧
   (get_code_labels (Tick e) = get_code_labels e) ∧
   (get_code_labels (Call _ d es) = (case d of NONE => {} | SOME n => {n}) ∪ BIGUNION (set (MAP get_code_labels es))) ∧
   (get_code_labels (Op op es) = closLang$assign_get_code_label op ∪ BIGUNION (set (MAP get_code_labels es)))`
  (wf_rel_tac`measure exp_size`
   \\ simp[bvlTheory.exp_size_def]
   \\ rpt conj_tac \\ rpt gen_tac
   \\ Induct_on`es`
   \\ rw[bvlTheory.exp_size_def]
   \\ simp[] \\ res_tac \\ simp[]);
val get_code_labels_def = get_code_labels_def |> SIMP_RULE (srw_ss()++ETA_ss)[] |> curry save_thm "get_code_labels_def[simp,compute]"

Theorem mk_tick_code_labels[simp]:
   !n x. get_code_labels (mk_tick n x) = get_code_labels x
Proof
  Induct \\ rw [] \\ fs [bvlTheory.mk_tick_def, FUNPOW_SUC]
QED

val _ = export_theory();
