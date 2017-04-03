open preamble
open bviSemTheory
open bviPropsTheory
open bvi_tailrecTheory

val _ = new_theory "bvi_tailrecProof";

val find_code_def = bvlSemTheory.find_code_def;
val eqs           = closPropsTheory.eqs;
val pure_op_def   = closLangTheory.pure_op_def;

val op_id_val_def = Define `
  (op_id_val (IntOp Plus) = Number 0) ∧
  (op_id_val (IntOp Times) = Number 1)
  `;

val Associative_def = Define `
  Associative (:'ffi) op ⇔
    ∀x1 x2 x3 env (s: 'ffi bviSem$state).
      evaluate ([apply_op op x1 (apply_op op x2 x3)], env, s) =
      evaluate ([apply_op op (apply_op op x1 x2) x3], env, s)`;

val Commutative_def = Define `
  Commutative (:'ffi) op ⇔
    ∀x1 x2 env (s: 'ffi bviSem$state).
      (is_pure x1 ∨ is_pure x2) ⇒
        evaluate ([apply_op op x1 x2], env, s) =
        evaluate ([apply_op op x2 x1], env, s)`;

val Associative_IntOp = Q.store_thm ("Associative_IntOp",
  `∀op. Associative (:'ffi) (IntOp op)`,
  cheat (* TODO *)
  );

val Commutative_IntOp = Q.store_thm ("Commutative_Arith",
  `∀op. Commutative (:'ffi) (IntOp op)`,
  cheat (* TODO *)
  );

val op_identity_evaluate_lemma = Q.prove (
  `∀iop.
    let op_exp = apply_op (IntOp iop) exp (id_from_op (IntOp iop)) in
     evaluate ([op_exp], env, s) = (r, t) ∧
     r ≠ Rerr (Rabort Rtype_error) ⇒
       evaluate ([exp], env, s) = (r, t)`,
  Cases
  \\ simp [apply_op_def, id_from_op_def, to_op_def]
  \\ simp [evaluate_def]
  \\ CASE_TAC
  \\ Cases_on `q` \\ fs []
  \\ simp [do_app_def, do_app_aux_def, small_enough_int_def]
  \\ simp [bvlSemTheory.do_app_def]
  \\ imp_res_tac evaluate_IMP_LENGTH
  \\ `a = [HD a]` by (Cases_on `a` \\ fs [LENGTH_NIL])
  \\ fs []
  \\ strip_tac
  \\ every_case_tac \\ fs [] \\ rveq \\ fs [bvl_to_bvi_id]);

val op_identity_evaluate = 
  SIMP_RULE std_ss [LET_THM] op_identity_evaluate_lemma;

val op_identity_pure = Q.prove (
  `∀iop.
     evaluate ([id_from_op (IntOp iop)], env, s) = (r, t) ⇒
       s = t ∧ ∃v. r = Rval v`,
  Cases
  \\ simp [id_from_op_def, 
           evaluate_def, 
           do_app_def, 
           do_app_aux_def,
           small_enough_int_def]
  \\ rw []);

val tail_check_IntOp = Q.store_thm ("tail_check_IntOp",
  `∀x. tail_check name x = SOME op ⇒ ∃op'. op = IntOp op'`,
  Induct \\ fs [tail_check_def]
  >- (TOP_CASE_TAC\\ fs [])
  \\ rpt strip_tac \\ rveq
  \\ every_case_tac \\ fs [from_op_def] \\ rveq \\ simp []);

val optimize_check_IntOp = Q.store_thm ("optimize_check_IntOp",
  `∀x. optimize_check name x = SOME op ⇒ ∃op'. op = IntOp op'`,
  rpt strip_tac \\ fs [optimize_check_def]
  \\ drule (GEN_ALL tail_check_IntOp) \\ fs []);

val op_binargs_SOME = Q.store_thm ("op_binargs_SOME[simp]",
  `∀exp.
     IS_SOME (op_binargs exp) ⇔
       ∃e1 e2 op.
         exp = Op op [e1; e2]`,
  Cases \\ simp [op_binargs_def]
  \\ rename1 `op_binargs (Op _ xs)`
  \\ Cases_on `xs` \\ simp [op_binargs_def]
  \\ rename1 `op_binargs (Op _ (_::xs))`
  \\ Cases_on `xs` \\ simp [op_binargs_def]
  \\ rename1 `op_binargs (Op _ (_::_::xs))`
  \\ Cases_on `xs` \\ simp [op_binargs_def])

val op_eq_to_op = Q.store_thm ("op_eq_to_op",
  `∀op xs. op_eq (IntOp op) (Op (to_op op) xs)`,
  Cases \\ fs [op_eq_def, to_op_def]);

(* Need something like the theorem(s) in clos_to_bvl *)
val is_pure_state = Q.prove (
  `∀x env s r t.
     evaluate ([x], env, s) = (r, t) ∧
     is_pure x ⇒
       s = t ∧ ∀err. r = Rerr err ⇒ err = Rabort Rtype_error`,
  cheat (* TODO *)
  );

val evaluate_op_rewrite = Q.store_thm ("evaluate_op_rewrite",
  `∀op name exp env (s: 'ffi bviSem$state) r t p exp2.
     op_rewrite op name exp = (p, exp2) /\
     Associative (:'ffi) op ∧
     Commutative (:'ffi) op ∧
     evaluate ([exp], env, s) = (r, t) ==>
       if ¬p then exp2 = exp else
         evaluate ([exp2], env, s) = (r, t) ∧
         (is_pure exp ⇒ is_pure exp2)`,

  ho_match_mp_tac op_rewrite_ind
  \\ rpt gen_tac \\ strip_tac \\ rpt gen_tac
  \\ once_rewrite_tac [op_rewrite_def]
  \\ cheat (* TODO *)
  );

(* optimize_check tells us something about the operation *)
val optimize_check_IMP_to_op = Q.store_thm ("optimize_check_IMP_to_op",
  `∀op nm xs iop.
    optimize_check nm (Op op xs) = SOME (IntOp iop) ⇒
      op = to_op iop`,
  cheat
  );

(* should hold for all input expressions *)
val op_rewrite_correct = Q.store_thm ("op_rewrite_correct",
  `∀iop name op xs exp.
     op_rewrite iop name (Op op xs) = (T, exp) ⇒
       IS_SOME (op_binargs exp)`,
  Cases
  \\ once_rewrite_tac [op_rewrite_def]
  \\ simp [op_eq_def]
  \\ rpt gen_tac
  \\ IF_CASES_TAC \\ fs []
  \\ TOP_CASE_TAC
  \\ TOP_CASE_TAC \\ fs []
  \\ rpt (pairarg_tac \\ fs [])
  \\ IF_CASES_TAC
  \\ IF_CASES_TAC \\ fs []
  \\ IF_CASES_TAC \\ fs []
  \\ fs [ac_swap_def, apply_op_def]
  \\ every_case_tac \\ rw []);

val op_rewrite_is_rec = Q.store_thm ("op_rewrite_is_rec",
  `∀iop name op xs e1 e2.
     op_rewrite iop name (Op op xs) = (T, Op op [e1; e2]) ⇒
       is_rec name e1`,
  Cases
  \\ rpt gen_tac
  \\ once_rewrite_tac [op_rewrite_def]
  \\ simp [op_eq_def]
  \\ IF_CASES_TAC \\ fs []
  \\ TOP_CASE_TAC
  \\ TOP_CASE_TAC
  \\ rpt (pairarg_tac \\ fs[])
  \\ IF_CASES_TAC
  >-
    (IF_CASES_TAC \\ fs []
    \\ IF_CASES_TAC \\ fs []
    \\ fs [ac_swap_def, apply_op_def]
    \\ qpat_x_assum `binop_has_rec _ _ y1` mp_tac
    \\ simp [binop_has_rec_def]
    \\ strip_tac
    >-
      (TOP_CASE_TAC
      >- (strip_tac \\ rveq \\ fs [])
      \\ TOP_CASE_TAC
      \\ Cases_on `y1` \\ fs [is_rec_def, op_binargs_def])
    \\ TOP_CASE_TAC \\ fs []
    \\ TOP_CASE_TAC
    \\ strip_tac
    \\ rveq
    \\ fs [])
  \\ IF_CASES_TAC \\ fs []
  \\ IF_CASES_TAC \\ fs []
  \\ simp [ac_swap_def, apply_op_def]
  \\ TOP_CASE_TAC
  >- (strip_tac \\ rveq \\ fs [binop_has_rec_def])
  \\ TOP_CASE_TAC
  \\ strip_tac \\ rveq
  \\ Cases_on `y2`
  \\ fs [binop_has_rec_def, op_binargs_def, is_rec_def]);

val op_rewrite_preserves_op = Q.store_thm ("op_rewrite_preserves_op",
  `∀iop name op xs exp2.
      op_rewrite (IntOp iop) name (Op op xs) = (T, exp2) ⇒
        ∃e1 e2. exp2 = Op op [e1;e2]`,
  rpt gen_tac
  \\ once_rewrite_tac [op_rewrite_def]
  \\ Cases_on `iop` \\ Cases_on `op` \\ fs [op_eq_def]
  \\ TOP_CASE_TAC
  \\ TOP_CASE_TAC
  \\ rpt (pairarg_tac \\ fs [])
  \\ every_case_tac \\ fs [ac_swap_def, apply_op_def, to_op_def]
  \\ every_case_tac \\ rw []);

val op_rewrite_is_pure = Q.store_thm ("op_rewrite_is_pure",
  `∀iop name op xs exp2 e1 e2.
     op_rewrite iop name (Op op xs) = (T, exp2) ∧
     op_binargs exp2 = SOME (e1, e2) ⇒
       is_pure e2`,
  cheat (* TODO *)
  );

val evaluate_push_call_LEMMA = Q.prove (
  `∀e2 iop n nm ticks args hdl env (s: 'ffi bviSem$state) r t.
   let new_call = Call ticks (SOME n) (e2 :: args) hdl in
   let old_call = Call ticks (SOME nm) args hdl in
     evaluate ([e2], env, s) = (r, t) ∧
     r ≠ Rerr (Rabort Rtype_error) ⇒
       evaluate ([new_call], env, s) =
       evaluate ([apply_op (IntOp iop) old_call e2], env, inc_clock 1 s)`,
  cheat (* TODO *)
  );

val evaluate_push_call_lemma =
  SIMP_RULE std_ss [LET_THM] evaluate_push_call_LEMMA

val env_rel_def = Define `
  env_rel opt_here acc env1 env2 ⇔
    isPREFIX env1 env2 ∧
    (opt_here ⇒ LENGTH env1 = acc ∧ LENGTH env2 > acc)
  `;

val env_rel_noopt_refl = Q.prove (
  `∀env acc. env_rel F acc env env`,
  fs [env_rel_def]);

val env_rel_simp = Q.store_thm ("env_rel_simp[simp]",
  `∀env1 env2 acc.
    env_rel F acc env1 env2 ∧
    env_rel T acc env1 env2 ⇔
      (∀p. env_rel p acc env1 env2)`,
  metis_tac [env_rel_def]);

val evaluate_env_extra = Q.store_thm ("evaluate_env_extra",
  `∀xs env s r t extra.
  evaluate (xs, env, s) = (r, t) ∧
  r ≠ Rerr (Rabort Rtype_error) ⇒
    evaluate (xs, env ++ extra, s) = (r, t)`,
  recInduct evaluate_ind
  \\ rpt conj_tac \\ rpt gen_tac \\ rpt strip_tac
  \\ qhdtm_x_assum `evaluate` mp_tac \\ simp [evaluate_def]
  \\ TRY (IF_CASES_TAC \\ fs [] \\ NO_TAC)
  \\ TRY (IF_CASES_TAC \\ strip_tac \\ rveq \\ fs [EL_APPEND1] \\ NO_TAC)
  \\ TRY (every_case_tac \\ strip_tac \\ rfs [] \\ rveq \\ rfs [] \\ NO_TAC)
  \\ every_case_tac \\ strip_tac \\ rfs [] \\ rveq \\ rfs [] \\ fs []);

val code_rel_def = Define `
  code_rel c1 c2 ⇔
    ∀name args exp op.
      lookup name c1 = SOME (args, exp) ⇒
      (optimize_check name exp = NONE ⇒
        lookup name c2 = SOME (args, exp)) ∧
      (optimize_check name exp = SOME op ⇒
        ∃n. ∀exp_aux exp_opt.
        optimize_single n name args exp = SOME (exp_aux, exp_opt) ⇒
          lookup name c2 = SOME (args, exp_aux) ∧
          lookup n c2 = SOME (args + 1, exp_opt))`;

val code_rel_find_code_noopt = Q.store_thm ("code_rel_find_code_noopt",
  `∀c1 c2 n (args: v list) exp.
     code_rel c1 c2 ∧
     find_code (SOME n) args c1 = SOME (args, exp) ∧
     optimize_check n exp = NONE ⇒
       find_code (SOME n) args c2 = SOME (args, exp)`,
  rpt strip_tac
  \\ fs [find_code_def, code_rel_def]
  \\ every_case_tac \\ fs []
  \\ first_x_assum (qspecl_then [`n`,`LENGTH args`,`exp`] strip_assume_tac)
  \\ rfs []);

val find_code_args_simp = Q.store_thm ("find_code_args_simp[simp]",
  `∀c n (args: v list) x y.
     find_code (SOME n) args c = SOME (x, y) ⇔
     x = args ∧ lookup n c = SOME (LENGTH args, y)`,
  rpt gen_tac
  \\ fs [find_code_def]
  \\ every_case_tac
  \\ metis_tac [find_code_def]);

val code_rel_find_code_no_delete = Q.store_thm ("code_rel_find_code_no_delete",
  `∀c1 c2 x (args: v list) exp.
     code_rel c1 c2 ∧
     find_code (SOME n) args c1 = SOME (args, exp) ⇒
       find_code (SOME n) args c2 ≠ NONE`,
  rpt gen_tac \\ strip_tac
  \\ qhdtm_x_assum `find_code` mp_tac \\ simp [find_code_def]
  \\ fs [code_rel_def]
  \\ TOP_CASE_TAC
  >-
    (CCONTR_TAC \\ fs []
    \\ first_x_assum drule
    \\ Cases_on `optimize_check n exp`  \\ fs []
    \\ fs [optimize_single_def])
  \\ strip_tac \\ CASE_TAC \\ simp []
  \\ first_x_assum drule
  \\ Cases_on `optimize_check n exp`
  \\ fs [optimize_single_def, optimize_check_def]
  \\ strip_tac \\ rveq \\ fs []);

val code_rel_find_code_SOME = Q.store_thm ("code_rel_find_code_SOME",
  `∀c1 c2 x (args: v list) exp.
     code_rel c1 c2 ∧
     find_code (SOME n) args c1 = SOME (args, exp) ⇒
       ∃exp2.
       find_code (SOME n) args c2 = SOME (args, exp2)`,
  rpt strip_tac
  \\ fs [find_code_def, code_rel_def]
  \\ every_case_tac \\ fs []
  \\ first_x_assum (qspecl_then [`n`,`LENGTH args`,`exp`] strip_assume_tac)
  \\ rfs []
  \\ Cases_on `optimize_check n exp` \\ fs []
  \\ Cases_on `optimize_single n' n q exp` \\ fs []
  \\ fs [optimize_single_def]
  \\ rfs []);

val state_rel_def = Define `
  state_rel (s: 'ffi bviSem$state) (t: 'ffi bviSem$state) ⇔
    s.ffi = t.ffi ∧
    s.clock = t.clock ∧
    code_rel s.code t.code
  `;

(* TODO *)
val code_rel_domain = Q.store_thm ("code_rel_domain",
  `∀c1 c2.
     code_rel c1 c2 ⇒ domain c1 ⊆ domain c2`,
  cheat);

val take_drop_lem = Q.prove (
  `!skip env.
    skip < LENGTH env ∧
    skip + SUC n ≤ LENGTH env ∧
    DROP skip env ≠ [] ⇒
    EL skip env::TAKE n (DROP (1 + skip) env) = TAKE (n + 1) (DROP skip env)`,
  Induct_on `n` >>
  srw_tac[][take1, hd_drop] >>
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

val evaluate_genlist_vars = Q.store_thm ("evaluate_genlist_vars",
  `!skip env n (st: 'ffi bviSem$state).
    n + skip ≤ LENGTH env ⇒
    evaluate (GENLIST (λarg. Var (arg + skip)) n, env, st)
    =
    (Rval (TAKE n (DROP skip env)), st)`,
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
  metis_tac [take_drop_lem]);

(* TODO: Make stronger by dropping ::vs in the RHS *)
val evaluate_let_wrap = Q.store_thm ("evaluate_let_wrap",
  `∀x v vs (s: 'ffi bviSem$state) r t num_args.
   num_args = LENGTH vs ∧
   evaluate ([let_wrap num_args x], v::vs, s) = (r, t) ∧
   r ≠ Rerr (Rabort Rtype_error) ⇒
     evaluate ([x], vs ++ (v::vs), s) = (r, t)`,
  rpt gen_tac \\ strip_tac
  \\ `num_args + 1 ≤ LENGTH (v::vs)` by fs []
  \\ qhdtm_x_assum `evaluate` mp_tac
  \\ drule evaluate_genlist_vars
  \\ disch_then (qspec_then `s` assume_tac)
  \\ simp [let_wrap_def, evaluate_def]
  \\ TOP_CASE_TAC
  \\ reverse TOP_CASE_TAC
  >- (strip_tac \\ rveq \\ fs [])
  \\ rfs []);

val evaluate_complete_ind = Q.store_thm ("evaluate_complete_ind",
  `∀P.
    (∀xs s.
      (∀ys t.
        exp2_size ys < exp2_size xs ∧ t.clock ≤ s.clock ∨ t.clock < s.clock ⇒
        P ys t) ⇒
      P xs s) ⇒
    ∀(xs: bvi$exp list) (s: 'ffi bviSem$state). P xs s`,
  rpt strip_tac
  \\ `∃sz. exp2_size xs = sz` by fs []
  \\ `∃ck0. s.clock = ck0` by fs []
  \\ ntac 2 (pop_assum mp_tac)
  \\ qspec_tac (`xs`,`xs`)
  \\ qspec_tac (`s`,`s`)
  \\ qspec_tac (`sz`,`sz`)
  \\ completeInduct_on `ck0`
  \\ strip_tac
  \\ completeInduct_on `sz`
  \\ fs [PULL_FORALL, AND_IMP_INTRO, GSYM CONJ_ASSOC]
  \\ rpt strip_tac \\ rveq
  \\ last_x_assum match_mp_tac
  \\ rpt strip_tac
  \\ simp []
  \\ fs [LESS_OR_EQ]);

val evaluate_optimized_WF = Q.store_thm ("evaluate_optimized_WF",
  `∀xs (s: 'ffi bviSem$state) env1 r opt_here t c acc env2 n nm.
    evaluate (xs, env1, s) = (r, t) ∧
    env_rel opt_here acc env1 env2 ∧
    code_rel s.code c ∧
    (LENGTH xs ≠ 1 ⇒ ¬opt_here) ∧
    (opt_here ⇒ IS_SOME (optimize_check nm (HD xs))) ∧
    r ≠ Rerr (Rabort Rtype_error) ⇒
      ∃ck ck'.
        if opt_here then
          ∀op.
            optimize_check nm (HD xs) = SOME op ⇒
            evaluate ([tail_rewrite n op nm acc (HD xs)],
              env2, inc_clock ck (s with code := c)) =
            evaluate ([apply_op op (HD xs) (Var acc)],
              env2, inc_clock ck' (s with code := c))
        else
          evaluate (xs, env2, inc_clock ck (s with code := c)) =
            (r, t with code := c)`,

  ho_match_mp_tac evaluate_complete_ind
  \\ rpt strip_tac \\ rveq
  \\ Cases_on `xs` \\ fs []
  >- (qexists_tac `0` \\ fs [evaluate_def, inc_clock_ZERO])
  \\ reverse (Cases_on `t'`)
  >-
    (rfs []
    \\ qpat_x_assum `evaluate _ = _` mp_tac \\ simp [evaluate_def]
    \\ TOP_CASE_TAC
    \\ reverse TOP_CASE_TAC \\ fs []
    >-
      (strip_tac \\ rveq \\ fs []
      \\ first_assum (qspecl_then [`[h]`,`s`] assume_tac)
      \\ fs [bviTheory.exp_size_def]
      \\ first_x_assum drule
      \\ disch_then (qspec_then `F` mp_tac) \\ fs []
      \\ ntac 2 (disch_then drule)
      \\ strip_tac
      \\ qexists_tac `ck`
      \\ rw [])
    \\ qmatch_goalsub_rename_tac `evaluate (y::ys, env1, s2)`
    \\ first_assum (qspecl_then [`[h]`,`s`] assume_tac)
    \\ fs [bviTheory.exp_size_def]
    \\ first_x_assum drule
    \\ disch_then (qspec_then `F` mp_tac) \\ fs []
    \\ ntac 2 (disch_then drule)
    \\ strip_tac
    \\ ntac 2 TOP_CASE_TAC
    \\ strip_tac \\ rveq \\ fs []
    \\ first_assum (qspecl_then [`y::ys`,`s2`] assume_tac)
    \\ imp_res_tac evaluate_clock \\ fs [bviTheory.exp_size_def]
    \\ first_x_assum drule
    \\ disch_then (qspec_then `F` mp_tac) \\ fs []
    \\ imp_res_tac evaluate_code_const
    \\ `code_rel s2.code c` by fs []
    \\ ntac 2 (disch_then drule)
    \\ strip_tac
    \\ qexists_tac `ck + ck'`
    \\ imp_res_tac evaluate_add_clock \\ fs []
    \\ pop_assum kall_tac
    \\ first_x_assum (qspec_then `ck'` assume_tac)
    \\ fs [inc_clock_ADD])
  \\ fs [bviTheory.exp_size_def]
  \\ Cases_on `∃ticks dest xs hdl. h = Call ticks dest xs hdl` \\ rw [] \\ fs [] (* TODO *)
  >-
    (
    qhdtm_x_assum `evaluate` mp_tac 
    \\ simp [Once evaluate_def]
    \\ `¬opt_here` by fs [optimize_check_def, tail_check_def] \\ fs []
    \\ IF_CASES_TAC >- fs []
    \\ `dest = NONE ⇒ ¬IS_SOME hdl` by metis_tac []
    \\ qpat_x_assum `¬(_)` kall_tac
    \\ first_assum (qspecl_then [`xs`,`s`] assume_tac)
    \\ fs [bviTheory.exp_size_def]
    \\ Cases_on `dest` \\ fs []
    >-
      (
      cheat (* TODO *)
      )
    \\ TOP_CASE_TAC
    \\ reverse TOP_CASE_TAC
    >-
      (fs [] \\ strip_tac \\ rveq
      \\ first_x_assum drule
      \\ disch_then (qspec_then `F` mp_tac)
      \\ ntac 2 (disch_then drule) \\ rw []
      \\ qexists_tac `ck`
      \\ fs [evaluate_def])
    \\ TOP_CASE_TAC >- fs []
    \\ TOP_CASE_TAC
    \\ IF_CASES_TAC
    >-
      (strip_tac \\ fs [] \\ rveq
      \\ first_x_assum drule
      \\ disch_then (qspec_then `F` mp_tac)
      \\ imp_res_tac evaluate_code_const
      \\ `code_rel r'.code c` by fs []
      \\ ntac 2 (disch_then drule) \\ rw []
      \\ qexists_tac `ck`
      \\ imp_res_tac code_rel_find_code_no_delete
      \\ fs [evaluate_def]
      \\ TOP_CASE_TAC >- rfs []
      \\ TOP_CASE_TAC)
    \\ qmatch_assum_rename_tac `_ = SOME (args, exp)`
    \\ qmatch_assum_rename_tac `evaluate (_,_,s1) = (_, s2)`
    \\ qpat_x_assum `∀x. ∀y. ∀z. _` kall_tac
    \\ `s2.clock ≥ ticks + 1` by fs [] \\ fs []
    \\ qmatch_goalsub_abbrev_tac `evaluate ([exp],_,s3)`
    \\ first_assum (qspecl_then [`[exp]`, `s3`] assume_tac)
    \\ `s3.clock < s1.clock` by
      (fs [Abbr`s3`, dec_clock_def] \\ imp_res_tac evaluate_clock \\ fs [])
    \\ fs []
    \\ TOP_CASE_TAC
    \\ TOP_CASE_TAC
    >-
      (
      strip_tac \\ fs [] \\ rveq
      \\ imp_res_tac evaluate_code_const
      \\ qhdtm_assum `code_rel` mp_tac
      \\ SIMP_TAC std_ss [code_rel_def]
      \\ fs []
      \\ disch_then drule
      \\ Cases_on `optimize_check x exp` \\ fs [] \\ strip_tac
      >- (* not optimized; exp points to same thing *)
        (first_x_assum drule
        \\ disch_then (qspec_then `F` mp_tac)
        \\ `env_rel F 0 a a` by fs [env_rel_def]
        \\ `code_rel s3.code c` by fs [Abbr`s3`]
        \\ ntac 2 (disch_then drule) \\ rw []
        \\ first_assum (qspecl_then [`xs`,`s1`] assume_tac)
        \\ fs [bviTheory.exp_size_def]
        \\ first_x_assum drule
        \\ disch_then (qspec_then `F` mp_tac)
        \\ ntac 2 (disch_then drule) \\ rw []
        \\ qexists_tac `ck + ck'`
        \\ drule evaluate_add_clock
        \\ impl_tac >- fs []
        \\ disch_then (qspec_then `ck` assume_tac)
        \\ fs [inc_clock_ADD]
        \\ imp_res_tac code_rel_find_code_no_delete
        \\ simp [evaluate_def]
        \\ TOP_CASE_TAC \\ fs []
        >- (first_x_assum drule \\ fs [])
        \\ TOP_CASE_TAC
        \\ qmatch_goalsub_abbrev_tac `dec_clock z s4`
        \\ fs [inc_clock_def, dec_clock_def]
        \\ full_simp_tac bool_ss [AC ADD_COMM ADD_ASSOC, Abbr`s4`]
        \\ rfs [Abbr`s3`])
      \\ Cases_on `optimize_single n x (LENGTH a) exp`
      >- rfs [optimize_single_def]
      \\ fs []
      \\ qmatch_assum_rename_tac `_ = SOME exp_`
      \\ PairCases_on `exp_` \\ fs []
      \\ qpat_x_assum `∀x.∀y.∀z._` kall_tac
      \\ first_assum (qspecl_then [`xs`,`s1`] assume_tac)
      \\ fs [bviTheory.exp_size_def]
      \\ first_x_assum drule
      \\ disch_then (qspec_then `F` mp_tac)
      \\ ntac 2 (disch_then drule) \\ rw []
      \\ unabbrev_all_tac
      \\ qmatch_assum_abbrev_tac `evaluate ([exp],_,_) = (_ res,s3)`
      (* Ensure Call finds the 'right' expression (auxilliary) *)
      \\ Cases_on `find_code (SOME x) a c`
      >- (rfs [find_code_def])
      \\ rename1 `find_code _ a c = SOME call_exp`
      \\ PairCases_on `call_exp`
      \\ `call_exp0 = a ∧ call_exp1 = exp_0` by rfs [find_code_def] \\ rveq
      (* What happens when we evaluate the auxilliary? *)
      \\ rfs [optimize_single_def]
      \\ imp_res_tac optimize_check_IntOp \\ rveq
      (* Need specific clocks from IH on [exp] with opt_here T *)
      \\ qmatch_asmsub_abbrev_tac `([exp],a,st)`
      \\ first_assum (qspecl_then [`[exp]`,`st`] assume_tac) \\ rfs []
      \\ first_x_assum drule \\ disch_then (qspec_then `T` mp_tac) \\ fs []
      \\ imp_res_tac evaluate_code_const \\ fs []
      \\ `∀xtra. env_rel T (LENGTH a) a (a ++ [xtra] ++ a)` by 
        (fs [env_rel_def] \\ fs [IS_PREFIX_APPEND])
      \\ rename1 `IntOp iop`
      \\ `env_rel T (LENGTH a) a (a ++ [op_id_val (IntOp iop)] ++ a)` by fs []
      \\ ntac 2 (disch_then drule) \\ fs []
      \\ disch_then (qspecl_then [`n`,`x`] strip_assume_tac)
      \\ rfs []
      \\ qexists_tac `1 + ck + ck'`
      \\ simp [evaluate_def]
      \\ drule evaluate_add_clock \\ fs []
      \\ disch_then (qspec_then `1 + ck'` mp_tac)
      \\ simp [inc_clock_ADD]
      \\ strip_tac
      \\ TOP_CASE_TAC
      >- rfs [find_code_def]
      \\ TOP_CASE_TAC
      \\ fs [find_code_def] \\ rveq
      \\ simp [mk_aux_call_def]
      (* Get rid of the GENLIST *)
      \\ simp [dec_clock_inv_clock]
      \\ simp [evaluate_def]
      \\ once_rewrite_tac [evaluate_CONS]
      \\ ntac 2 CASE_TAC
      \\ `LENGTH a + 0 ≤ LENGTH a` by decide_tac
      \\ drule evaluate_genlist_vars
      \\ fs []
      \\ strip_tac \\ fs [] \\ rveq
      \\ pop_assum kall_tac \\ rw []
      \\ simp [find_code_def]
      \\ drule (GEN_ALL op_identity_pure)
      \\ strip_tac \\ rveq \\ fs []
      \\ simp [evaluate_def]
      (* Get rid of let_wrap *)
      \\ simp [let_wrap_def]
      \\ simp [evaluate_def]
      \\ CASE_TAC
      \\ `LENGTH a + 1 ≤ LENGTH (HD v::a)` by fs []
      \\ drule evaluate_genlist_vars \\ fs []
      \\ strip_tac \\ fs [] \\ rveq
      \\ pop_assum kall_tac \\ rw []
      \\ fs [inc_clock_def, dec_clock_def]
      \\ `op_id_val (IntOp iop) = HD v` by
        (rw []
        \\ pop_assum mp_tac
        \\ Cases_on `iop`
        \\ simp [evaluate_def, id_from_op_def, op_id_val_def]
        \\ simp [do_app_def, do_app_aux_def, small_enough_int_def]
        \\ strip_tac \\ rveq \\ fs [])
      \\ pop_assum (fn th => fs [th])
      \\ `a ++ HD v::a = a ++ [HD v] ++ a` by fs []
      \\ pop_assum (fn th => fs [th])
      \\ qpat_x_assum `evaluate _ = evaluate _` (fn th => fs [th])
      \\ simp [apply_op_def]
      (* I know nothing about exp in the new code at this point and to do *)
      (* I need to ``create`` another clock using the IH, which I cannot  *)
      (* relate to ck''                                                   *)
      \\ cheat
      )
    \\ cheat (* TODO *)
    )
  \\ Cases_on `∃x1 x2 x3. h = If x1 x2 x3` \\ rw [] \\ fs []
  >-
    (
    qhdtm_x_assum `evaluate` mp_tac \\ simp [Once evaluate_def]
    \\ first_assum (qspecl_then [`[x1]`, `s`] assume_tac)
    \\ fs [bviTheory.exp_size_def]
    \\ TOP_CASE_TAC
    \\ reverse TOP_CASE_TAC
    >-
      (strip_tac \\ rveq \\ fs []
      \\ `env_rel F acc env1 env2` by fs [env_rel_def]
      \\ first_x_assum drule
      \\ disch_then (qspec_then `F` drule) \\ fs []
      \\ disch_then drule
      \\ strip_tac
      \\ ntac 2 (qexists_tac `ck`)
      \\ reverse IF_CASES_TAC \\ fs []
      >- simp [evaluate_def]
      \\ rpt strip_tac
      \\ imp_res_tac optimize_check_IntOp \\ rveq
      \\ simp [evaluate_def, tail_rewrite_def, apply_op_def])
    \\ reverse (Cases_on `opt_here`) \\ fs []
    >-
      (IF_CASES_TAC
      >-
        (strip_tac
        \\ `env_rel F acc env1 env2` by fs [env_rel_def]
        \\ first_x_assum drule
        \\ disch_then (qspec_then `F` drule) \\ fs []
        \\ disch_then drule
        \\ strip_tac
        \\ rename1 `([x2],env1,st)`
        \\ first_x_assum (qspecl_then [`[x2]`,`st`] assume_tac)
        \\ imp_res_tac evaluate_clock
        \\ fs [bviTheory.exp_size_def]
        \\ first_x_assum drule
        \\ disch_then (qspec_then `F` drule) \\ fs []
        \\ imp_res_tac evaluate_code_const \\ fs []
        \\ disch_then drule
        \\ strip_tac
        \\ pop_assum mp_tac
        \\ drule evaluate_add_clock \\ fs []
        \\ disch_then (qspec_then `ck'` assume_tac)
        \\ fs [inc_clock_ADD]
        \\ strip_tac
        \\ qexists_tac `ck + ck'`
        \\ simp [evaluate_def])
      \\ IF_CASES_TAC \\ fs []
      \\ strip_tac
      \\ `env_rel F acc env1 env2` by fs [env_rel_def]
      \\ first_x_assum drule
      \\ disch_then (qspec_then `F` drule) \\ fs []
      \\ disch_then drule
      \\ strip_tac
      \\ rename1 `([x3],env1,st)`
      \\ first_x_assum (qspecl_then [`[x3]`,`st`] assume_tac)
      \\ imp_res_tac evaluate_clock
      \\ fs [bviTheory.exp_size_def]
      \\ first_x_assum drule
      \\ disch_then (qspec_then `F` drule) \\ fs []
      \\ imp_res_tac evaluate_code_const \\ fs []
      \\ disch_then drule
      \\ strip_tac
      \\ pop_assum mp_tac
      \\ drule evaluate_add_clock \\ fs []
      \\ disch_then (qspec_then `ck'` assume_tac)
      \\ fs [inc_clock_ADD]
      \\ strip_tac
      \\ qexists_tac `ck + ck'`
      \\ simp [evaluate_def])
    \\ IF_CASES_TAC
    \\ cheat (* TODO *)
    )
  \\ Cases_on `∃xs x1. h = Let xs x1` \\ rw [] \\ fs []
  >-
    (qpat_x_assum `evaluate _ = _` mp_tac \\ simp [evaluate_def]
    \\ TOP_CASE_TAC
    \\ reverse TOP_CASE_TAC
    \\ first_assum (qspecl_then [`xs`,`s`] assume_tac)
    \\ strip_tac \\ rveq \\ fs []
    \\ fs [bviTheory.exp_size_def]
    \\ first_x_assum drule
    \\ disch_then (qspec_then `F` mp_tac) \\ fs []
    \\ `env_rel F acc env1 env2` by fs [env_rel_def]
    \\ ntac 2 (disch_then drule)
    \\ strip_tac
    >-
      (ntac 2 (qexists_tac `ck`)
      \\ IF_CASES_TAC \\ fs []
      \\ rpt strip_tac
      \\ imp_res_tac optimize_check_IntOp \\ rveq
      \\ fs [tail_rewrite_def, apply_op_def, evaluate_def])
    \\ rename1 `evaluate (_,_,s) = (_,s2)`
    \\ first_x_assum (qspecl_then [`[x1]`,`s2`] assume_tac)
    \\ imp_res_tac evaluate_clock
    \\ imp_res_tac evaluate_code_const
    \\ `code_rel s2.code c` by fs []
    \\ fs [bviTheory.exp_size_def]
    \\ first_x_assum drule
    \\ disch_then (qspec_then `opt_here` mp_tac) \\ fs []
    \\ `env_rel opt_here (acc+LENGTH a) (a++env1) (a++env2)` by
      (fs [env_rel_def, IS_PREFIX_LENGTH] \\ CCONTR_TAC \\ fs [])
    \\ ntac 2 (disch_then drule)
    \\ disch_then (qspecl_then [`n`,`nm`] assume_tac) \\ fs []
    \\ reverse (Cases_on `opt_here`) \\ fs []
    >-
      (qexists_tac `ck + ck'`
      \\ imp_res_tac evaluate_add_clock \\ fs []
      \\ ntac 2 (pop_assum kall_tac)
      \\ first_x_assum (qspec_then `ck'` assume_tac)
      \\ fs [inc_clock_ADD])
    \\ `IS_SOME (optimize_check nm x1)` by
       fs [optimize_check_def, tail_check_def, ok_tail_type_def]
    \\ rfs [] \\ fs []
    \\ Cases_on `optimize_check nm (Let xs x1)` \\ fs []
    \\ Cases_on `optimize_check nm x1` \\ fs []
    \\ `x = x'` by fs [optimize_check_def, tail_check_def] \\ rveq
    \\ `acc < LENGTH env2` by fs [env_rel_def]
    \\ imp_res_tac optimize_check_IntOp \\ fs [] \\ rveq
    \\ fs [tail_rewrite_def, apply_op_def]
    \\ qexists_tac `ck + ck'`
    \\ imp_res_tac evaluate_add_clock \\ fs []
    \\ ntac 2 (pop_assum kall_tac)
    \\ first_assum (qspec_then `ck'` assume_tac)
    \\ first_x_assum (qspec_then `ck''` assume_tac)
    \\ fs [inc_clock_ADD]
    \\ `LENGTH a = LENGTH xs` by metis_tac [evaluate_IMP_LENGTH]
    \\ simp [evaluate_def]
    \\ `EL (acc+LENGTH xs) (a++env2) = EL acc env2` by
       fs [EL_APPEND2, env_rel_def]
    \\ qexists_tac `ck + ck''`
    \\ fs [evaluate_def])
  \\ Cases_on `∃x1. h = Tick x1` \\ rw [] \\ fs []
  >-
    (
    qpat_x_assum `evaluate _ = _` mp_tac \\ simp [evaluate_def]
    \\ IF_CASES_TAC \\ fs []
    \\ strip_tac \\ rveq \\ fs []
    >-
      (ntac 2 (qexists_tac `0`)
      \\ simp [inc_clock_ZERO]
      \\ Cases_on `opt_here` \\ fs []
      \\ rpt strip_tac
      \\ imp_res_tac optimize_check_IntOp \\ rveq
      \\ fs [tail_rewrite_def, apply_op_def, evaluate_def])
    \\ first_x_assum (qspecl_then [`[x1]`, `dec_clock 1 s`] assume_tac)
    \\ `(dec_clock 1 s).clock < s.clock` by fs [dec_clock_def]
    \\ fs [bviTheory.exp_size_def]
    \\ first_x_assum drule \\ fs []
    \\ ntac 2 (disch_then drule)
    \\ disch_then (qspecl_then [`n`,`nm`] assume_tac) \\ rfs []
    \\ reverse (Cases_on `opt_here`) \\ fs []
    >-
      (qexists_tac `ck` \\ rfs [] \\ rveq
      \\ fs [dec_clock_inv_clock1])
    \\ Cases_on `optimize_check nm x1` \\ fs []
    >-
      (fs [optimize_check_def, tail_check_def, ok_tail_type_def]
      \\ every_case_tac \\ fs [])
    \\ qexists_tac `ck`
    \\ qexists_tac `ck'`
    \\ rpt strip_tac
    \\ imp_res_tac optimize_check_IntOp \\ rveq
    \\ rename1 `IntOp op`
    \\ rename1 `_ _ x1 = _ (_ op1)`
    \\ `op = op1` by fs [optimize_check_def, tail_check_def] \\ rveq
    \\ `acc < LENGTH env2` by fs [env_rel_def]
    \\ fs [tail_rewrite_def, apply_op_def]
    \\ simp [Once evaluate_def]
    \\ fs [dec_clock_inv_clock1]
    \\ fs [evaluate_def, inc_clock_def, dec_clock_def])
  \\ Cases_on `∃v. h = Var v` \\ rw [] \\ fs []
  >-
    (qpat_x_assum `evaluate _ = _` mp_tac \\ simp [evaluate_def]
    \\ IF_CASES_TAC
    \\ strip_tac \\ fs [] \\rveq
    \\ Cases_on `opt_here` \\ fs [] \\ rveq
    >- (fs [optimize_check_def, tail_check_def])
    \\ qexists_tac `0`
    \\ fs [env_rel_def]
    \\ drule IS_PREFIX_LENGTH
    \\ fs [inc_clock_ZERO, env_rel_def, is_prefix_el])
  \\ Cases_on `∃x1. h = Raise x1` \\ rw [] \\ fs []
  >-
    (qpat_x_assum `evaluate _ = _` mp_tac \\ simp [evaluate_def]
    \\ `¬opt_here` by fs [optimize_check_def, tail_check_def] \\ fs []
    \\ TOP_CASE_TAC
    \\ strip_tac
    \\ first_x_assum (qspecl_then [`[x1]`,`s`] assume_tac) \\ rfs []
    \\ fs [bviTheory.exp_size_def]
    \\ first_x_assum drule \\ fs []
    \\ ntac 2 (disch_then drule) \\ fs []
    \\ impl_tac
    >- (every_case_tac \\ fs [] \\ rveq \\ fs [])
    \\ strip_tac
    \\ qexists_tac `ck`
    \\ every_case_tac \\ fs [])
  \\ Cases_on `∃xs op. h = Op op xs` \\ rw [] \\ fs []

  >-
    (
    qhdtm_x_assum `evaluate` mp_tac \\ simp [evaluate_def]
    \\ reverse (Cases_on `opt_here`) \\ fs []
    >- (* no optimization *)
      (TOP_CASE_TAC
      \\ strip_tac
      \\ first_x_assum (qspecl_then [`xs`,`s`] assume_tac) \\ rfs []
      \\ fs [bviTheory.exp_size_def]
      \\ first_x_assum drule
      \\ ntac 2 (disch_then drule) \\ fs []
      \\ impl_tac
      >- (every_case_tac \\ fs [] \\ rveq \\ fs [])
      \\ strip_tac
      \\ qexists_tac `ck` \\ fs []
      \\ TOP_CASE_TAC \\ fs []
      \\ qpat_x_assum `_ = (r, t)` mp_tac
      \\ TOP_CASE_TAC
      >-
        (TOP_CASE_TAC \\ strip_tac \\ rveq
        \\ imp_res_tac do_app_with_code
        \\ pop_assum (qspec_then `c` mp_tac)
        \\ imp_res_tac evaluate_code_const
        \\ fs [code_rel_domain])
      \\ strip_tac \\ rveq
      \\ imp_res_tac do_app_with_code_err \\ fs [])
    \\ TOP_CASE_TAC
    \\ strip_tac
    \\ first_assum (qspecl_then [`xs`,`s`] assume_tac) \\ rfs []
    \\ fs [bviTheory.exp_size_def]
    \\ first_x_assum drule
    \\ `env_rel F acc env1 env2` by fs [env_rel_def]
    \\ ntac 2 (disch_then drule) \\ fs []
    \\ impl_tac
    >- (every_case_tac \\ fs [] \\ rveq \\ fs [])
    \\ strip_tac
    \\ Cases_on `optimize_check nm (Op op xs)` \\ fs []
    \\ imp_res_tac optimize_check_IntOp \\ rveq
    \\ qexists_tac `ck`
    \\ fs [tail_rewrite_def, mk_tailcall_def] \\ rveq
    \\ rename1 `IntOp iop`
    \\ TOP_CASE_TAC
    \\ reverse TOP_CASE_TAC
    >-
      (drule evaluate_op_rewrite
      \\ simp [Associative_IntOp, Commutative_IntOp, apply_op_def]
      \\ rename1 `evaluate (xs,env1,s) = (res, s2)`
      \\ disch_then (qspecl_then [`env1`,`s`,`r`,`t`] mp_tac)
      \\ simp [Once evaluate_def]
      \\ strip_tac \\ rveq
      \\ qexists_tac `ck`
      \\ fs [])
    \\ imp_res_tac op_rewrite_correct \\ fs [] \\ rveq
    \\ simp [op_binargs_def]
    \\ imp_res_tac op_rewrite_preserves_op \\ fs [] \\ rveq
    \\ imp_res_tac op_rewrite_is_rec
    \\ Cases_on `e1` \\ fs [is_rec_def, args_from_def]
    \\ rename1 `SOME (ticks,_,args,hdl)`
    \\ rveq
    \\ simp [push_call_def]
    \\ `acc < LENGTH env2` by fs [env_rel_def]
    \\ qexists_tac `ck + 1`
    \\ qmatch_asmsub_abbrev_tac `op_rewrite _ _ _ = (_, op_exp)`
    \\ qmatch_goalsub_abbrev_tac `([apply_op _ _ _],_,st)`
    \\ `evaluate ([apply_op (IntOp iop) (Op op xs) (Var acc)], env2, st) =
        evaluate ([apply_op (IntOp iop) op_exp (Var acc)], env2, st)` by
      (drule evaluate_op_rewrite
      \\ fs [Associative_IntOp, Commutative_IntOp]
      \\ qmatch_goalsub_abbrev_tac `(_,_,st)`
      \\ disch_then (qspecl_then [`env2`,`st`] mp_tac)
      \\ imp_res_tac optimize_check_IMP_to_op \\ rveq
      \\ fs [apply_op_def]
      \\ Cases_on `evaluate ([Op (to_op iop) xs], env2, st)` \\ fs []
      \\ strip_tac
      \\ simp [evaluate_def])
    \\ simp [apply_op_def, Abbr`op_exp`, Abbr`st`]
    \\ imp_res_tac optimize_check_IMP_to_op \\ rveq
    \\ pop_assum kall_tac
    \\ assume_tac Associative_IntOp
    \\ fs [Associative_def, apply_op_def]
    \\ first_x_assum (qspec_then `iop` assume_tac)
    \\ pop_assum (fn th => fs [GSYM th])
    \\ qmatch_goalsub_abbrev_tac `evaluate (_,_,st) = _`
    \\ Cases_on `evaluate ([Op (to_op iop) [e2; Var acc]], env2, st)`
    \\ fs [Abbr`st`]
    \\ rename1 `_ = (op_acc_res, _)`
    \\ reverse (Cases_on `op_acc_res`)

    >- (* TODO show that e2 + var acc is not an error. solution: purity of e2 *)
      (
      drule op_rewrite_is_pure 
      \\ fs [op_binargs_def]
      \\ strip_tac
      \\ drule is_pure_state 
      \\ impl_tac
      >- (Cases_on `iop` \\ fs [to_op_def, is_pure_def, pure_op_def])
      \\ strip_tac \\ fs [] \\ rveq
      
      \\ drule evaluate_op_rewrite 
      \\ simp [Associative_IntOp, Commutative_IntOp]
      \\ disch_then (qspecl_then [`env2`,`inc_clock ck (s with code := c)`,`r`,`r' with code := c`] mp_tac)
      \\ impl_tac
      >- 
        (simp [evaluate_def]
        \\ imp_res_tac code_rel_domain
        \\ TOP_CASE_TAC \\ fs []
        \\ Cases_on `iop` \\ fs [to_op_def, do_app_def, do_app_aux_def]
        \\ fs [bvlSemTheory.do_app_def]
        \\ every_case_tac \\ fs [] \\ rveq \\ fs [bvl_to_bvi_id])
      \\ strip_tac
      \\ pop_assum kall_tac
      \\ CCONTR_TAC
      \\ qhdtm_x_assum `evaluate` kall_tac
      \\ qhdtm_x_assum `evaluate` mp_tac
      \\ Cases_on `evaluate ([e2], env2, inc_clock ck (s with code := c))`
      \\ drule is_pure_state
      \\ strip_tac \\ rfs [] \\ rveq
      \\ simp [evaluate_def]

      \\ cheat
      )
    \\ drule evaluate_push_call_lemma \\ fs [apply_op_def]
    \\ fs [inc_clock_ADD]
  )
  \\ Cases_on `h` \\ fs []
  );

val optimize_prog_LENGTH = Q.store_thm ("optimize_prog_LENGTH",
  `∀n prog. LENGTH (optimize_prog n prog) ≥ LENGTH prog`,
  recInduct optimize_prog_ind
  \\ conj_tac
  >- fs [optimize_prog_def]
  \\ rpt gen_tac \\ strip_tac
  \\ Cases_on `optimize_single n nm args exp` \\ fs []
  >- fs [optimize_prog_def]
  \\ Cases_on `x` \\ fs []
  \\ fs [optimize_prog_def]);

val free_names_def = Define `
  free_names n (name: num) ⇔ ∀k. n + 2*k ≠ name
  `;

val more_free_names = Q.prove (
  `free_names n name ⇒ free_names (n + 2) name`,
  fs [free_names_def] \\ rpt strip_tac
  \\ first_x_assum (qspec_then `k + 1` mp_tac) \\ strip_tac
  \\ rw []);

val is_free_name = Q.prove (
  `free_names n name ⇒ n ≠ name`,
  fs [free_names_def] \\ strip_tac
  \\ first_x_assum (qspec_then `0` mp_tac) \\ strip_tac \\ rw []);

val optimize_next_name = Q.prove (
  `optimize_single n name args exp = NONE ⇒
     optimize_single (n + 2) name args exp = NONE`,
  fs [optimize_single_def] \\ every_case_tac);

val optimize_all_untouched = Q.store_thm ("optimize_all_untouched",
  `∀n prog prog2 name exp args.
     free_names n name ∧
     lookup name (fromAList prog) = SOME (args, exp) ∧
     optimize_check name exp = NONE ∧
     optimize_single n name args exp = NONE ∧
     optimize_prog n prog = prog2 ⇒
       lookup name (fromAList prog2) = SOME (args, exp)`,
  recInduct optimize_prog_ind
  \\ rpt conj_tac \\ rpt gen_tac \\ strip_tac
  \\ fs [fromAList_def, lookup_def]
  \\ rpt gen_tac \\ strip_tac
  \\ Cases_on `nm = name` \\ fs [] \\ rveq
  >-
    (Cases_on `lookup name (fromAList xs)`
    \\ fs [optimize_prog_def, fromAList_def])
  \\ fs [lookup_insert]
  \\ Cases_on `optimize_single n nm args exp` \\ fs []
  >- rfs [optimize_prog_def, fromAList_def, lookup_insert]
  \\ Cases_on `x` \\ rw []
  \\ imp_res_tac more_free_names
  \\ imp_res_tac optimize_next_name
  \\ first_x_assum drule
  \\ disch_then drule \\ rfs []
  \\ strip_tac
  \\ fs [optimize_prog_def, fromAList_def, lookup_insert, is_free_name]);

val EVERY_free_names_SUCSUC = Q.prove (
  `∀xs. EVERY (free_names n o FST) xs ⇒ EVERY (free_names (n + 2) o FST) xs`,
  Induct \\ strip_tac \\ fs []
  \\ strip_tac \\ imp_res_tac more_free_names);

val optimize_all_touched = Q.store_thm ("optimize_all_touched",
  `∀n prog prog2 name exp args.
     ALL_DISTINCT (MAP FST prog) ∧
     EVERY (free_names n o FST) prog ∧
     free_names n name ∧
     lookup name (fromAList prog) = SOME (args, exp) ∧
     optimize_check name exp = SOME op ∧
     optimize_prog n prog = prog2 ⇒
      ∃k. ∀exp_aux exp_opt.
        optimize_single (n + 2 * k) name args exp = SOME (exp_aux, exp_opt) ⇒
          lookup name (fromAList prog2) = SOME (args, exp_aux) ∧
          lookup (n + 2 * k) (fromAList prog2) = SOME (args + 1, exp_opt)`,
  recInduct optimize_prog_ind
  \\ conj_tac \\ rpt gen_tac \\ strip_tac
  >- fs [fromAList_def, lookup_def]
  \\ rpt gen_tac \\ strip_tac
  \\ fs [ALL_DISTINCT_APPEND]
  \\ qhdtm_x_assum `optimize_prog` mp_tac \\ simp [optimize_prog_def]
  \\ TOP_CASE_TAC \\ fs []
  >-
    (qhdtm_x_assum `optimize_single` mp_tac \\ simp [Once optimize_single_def]
    \\ qpat_x_assum `_ = SOME (_,_)` mp_tac
    \\ simp [lookup_insert, fromAList_def]
    \\ IF_CASES_TAC
    \\ strip_tac \\ rveq \\ fs []
    \\ first_x_assum drule
    \\ disch_then drule
    \\ strip_tac \\ rveq \\ rfs []
    \\ TOP_CASE_TAC \\ strip_tac \\ rveq
    \\ qexists_tac `k`
    \\ simp [lookup_insert, fromAList_def]
    \\ fs [free_names_def])
  \\ TOP_CASE_TAC
  \\ strip_tac
  \\ qhdtm_x_assum `lookup` mp_tac
  \\ simp [lookup_insert, fromAList_def]
  \\ reverse IF_CASES_TAC
  >-
    (strip_tac \\ rveq \\ fs []
    \\ imp_res_tac more_free_names
    \\ rfs [EVERY_free_names_SUCSUC]
    \\ fs [lookup_insert, fromAList_def]
    \\ IF_CASES_TAC >- fs [free_names_def]
    \\ first_x_assum (qspec_then `name` assume_tac)
    \\ first_x_assum drule
    \\ disch_then drule \\ fs []
    \\ strip_tac
    \\ fs [free_names_def]
    \\ qexists_tac `k + 1` \\ fs []
    \\ simp [LEFT_ADD_DISTRIB])
  \\ strip_tac \\ fs [] \\ rveq
  \\ imp_res_tac more_free_names
  \\ rfs [EVERY_free_names_SUCSUC]
  \\ fs [lookup_insert, fromAList_def, free_names_def]
  \\ qexists_tac `0` \\ fs []);

val optimize_check_no_single = Q.prove (
  `optimize_check name exp = NONE ⇒ optimize_single n name args exp = NONE`,
  fs [optimize_single_def]);

val optimize_check_SOME_single = Q.prove (
  `optimize_check name exp = SOME op ⇒
     ∃q. optimize_single n name args exp = SOME q`,
  fs [optimize_single_def]);

val EVERY_free_names_IMP_free_names = Q.prove (
  `EVERY (free_names n o FST) prog ∧
   lookup name (fromAList prog) = SOME x ⇒
     free_names n name`,
  strip_tac
  \\ fs [lookup_fromAList, EVERY_MEM]
  \\ imp_res_tac ALOOKUP_MEM
  \\ first_x_assum (qspec_then `(name, x)` mp_tac) \\ rw []);

val optimize_prog_code_rel = Q.store_thm ("optimize_prog_code_rel",
  `ALL_DISTINCT (MAP FST prog) ∧
   EVERY (free_names n o FST) prog ∧
   optimize_prog n prog = prog2 ⇒
   code_rel (fromAList prog)
            (fromAList prog2)`,
  simp [GSYM AND_IMP_INTRO]
  \\ fs [code_rel_def]
  \\ rpt strip_tac
  \\ imp_res_tac EVERY_free_names_IMP_free_names
  >- (* No optimize_single *)
    (imp_res_tac optimize_check_no_single
     \\ drule optimize_check_no_single
     \\ imp_res_tac optimize_all_untouched)
  \\ drule optimize_all_touched
  \\ disch_then drule
  \\ strip_tac \\ rfs []
  \\ first_x_assum (qspecl_then [`name`,`exp`,`args`] strip_assume_tac)
  \\ rfs []
  \\ imp_res_tac (GEN_ALL optimize_check_SOME_single)
  \\ first_x_assum (qspecl_then [`2 * k + n`, `args`] strip_assume_tac)
  \\ Cases_on `q` \\ fs []
  \\ qexists_tac `2 * k + n` \\ rw []
  );

val optimize_prog_evaluate = Q.store_thm ("optimize_prog_evaluate",
  `EVERY (free_names n o FST) prog ∧
   ALL_DISTINCT (MAP FST prog) ∧
   evaluate ([Call 0 (SOME start) [] NONE], [],
             initial_state ffi0 (fromAList prog) k) = (r, s) ∧
   0 < k ∧
   r ≠ Rerr (Rabort Rtype_error) ⇒
   ∃ck s2.
     evaluate ([Call 0 (SOME start) [] NONE], [],
               initial_state ffi0 (fromAList (optimize_prog n prog)) (k + ck))
               = (r, s2) ∧
     state_rel s s2`,
  simp [GSYM AND_IMP_INTRO]
  \\ rpt strip_tac
  \\ qmatch_assum_abbrev_tac `evaluate (es,env,st1) = _`
  \\ `env_rel F 0 env env` by fs [env_rel_def]
  \\ drule (GEN_ALL optimize_prog_code_rel) \\ disch_then drule
  \\ disch_then (qspec_then `optimize_prog n prog` assume_tac) \\ fs []
  \\ qmatch_assum_abbrev_tac `code_rel _ c`
  \\ drule evaluate_optimized_WF
  \\ disch_then drule \\ rfs [Abbr`st1`]
  \\ disch_then drule \\ strip_tac
  \\ qexists_tac `ck` \\ fs [inc_clock_def]
  \\ imp_res_tac evaluate_code_const
  \\ fs [state_rel_def, initial_state_def]);

val optimize_prog_semantics = Q.store_thm ("optimize_prog_semantics",
  `EVERY (free_names n o FST) prog ∧
   ALL_DISTINCT (MAP FST prog) ∧
   optimize_prog n prog = prog2 ∧
   semantics ffi (fromAList prog) start ≠ Fail ⇒
   semantics ffi (fromAList prog) start =
   semantics ffi (fromAList prog2) start`,
   simp [GSYM AND_IMP_INTRO]
   \\ ntac 3 strip_tac
   \\ simp [Ntimes semantics_def 2]
   \\ IF_CASES_TAC \\ fs []
   \\ DEEP_INTRO_TAC some_intro \\ simp []
   \\ conj_tac
   >-
     (gen_tac \\ strip_tac \\ rveq \\ simp []
     \\ simp [semantics_def]
     \\ IF_CASES_TAC \\ fs []
     >-
       (first_assum (subterm (fn tm => Cases_on`^(assert(has_pair_type)tm)`) o concl)
       \\ drule evaluate_add_clock
       \\ impl_tac >- fs []
       \\ strip_tac
       \\ qpat_x_assum `evaluate (_,_,_ _ (_ prog) _) = _` kall_tac
       \\ last_assum (qspec_then `SUC k'` mp_tac)
       \\ (fn g => subterm (fn tm => Cases_on`^(assert(has_pair_type)tm)`) (#2 g) g )
       \\ drule (GEN_ALL optimize_prog_evaluate) \\ simp []
       \\ disch_then drule
       \\ impl_tac
       >-
         (fs [] \\ last_x_assum (qspec_then `SUC k'` strip_assume_tac)
         \\ rfs [] \\ spose_not_then strip_assume_tac \\ fs [])
       \\ strip_tac
       \\ first_x_assum (qspec_then `SUC ck` mp_tac)
       \\ simp [inc_clock_def]
       \\ fs [ADD1])
     \\ DEEP_INTRO_TAC some_intro \\ simp []
     \\ conj_tac
     >-
       (gen_tac \\ strip_tac \\ rveq \\ fs []
       \\ qmatch_assum_abbrev_tac `evaluate (opts,[],sopt) = _`
       \\ qmatch_assum_abbrev_tac `evaluate (exps,[],st) = (r,s)`
       \\ qspecl_then [`opts`,`[]`,`sopt`] mp_tac evaluate_add_to_clock_io_events_mono
       \\ qspecl_then [`exps`,`[]`,`st`] mp_tac evaluate_add_to_clock_io_events_mono
       \\ simp [inc_clock_def, Abbr`sopt`, Abbr`st`]
       \\ ntac 2 strip_tac
       \\ Cases_on `s.ffi.final_event` \\ fs []
       >-
         (Cases_on `s'.ffi.final_event` \\ fs []
         >-
           (unabbrev_all_tac
           \\ drule (GEN_ALL optimize_prog_evaluate) \\ simp []
           \\ disch_then drule
           \\ impl_tac
           >- (spose_not_then strip_assume_tac \\ fs []
               \\ fs [evaluate_def] \\ every_case_tac \\ fs [] \\ rveq \\ fs [])
           \\ strip_tac
           \\ drule evaluate_add_clock
           \\ impl_tac
           >- (every_case_tac \\ fs [])
           \\ disch_then (qspec_then `k'` mp_tac) \\ simp [inc_clock_def]
           \\ qpat_x_assum `evaluate (_,_,_ _ (_ prog2) _) = _` mp_tac
           \\ drule evaluate_add_clock
           \\ impl_tac
           >- (spose_not_then strip_assume_tac \\ fs [evaluate_def])
           \\ disch_then (qspec_then `ck+k` mp_tac) \\ simp [inc_clock_def]
           \\ ntac 2 strip_tac \\ rveq \\ fs []
           \\ fs [state_component_equality]
           \\ fs [state_rel_def]
           \\ every_case_tac \\ fs [])
         \\ qpat_x_assum `∀extra._` mp_tac
         \\ first_x_assum (qspec_then `k'` assume_tac)
         \\ first_assum (subterm (fn tm => Cases_on`^(assert has_pair_type tm)`) o concl)
         \\ strip_tac \\ fs []
         \\ unabbrev_all_tac
         \\ drule (GEN_ALL optimize_prog_evaluate)
         \\ ntac 2 (disch_then drule)
         \\ impl_tac
         >-
          (last_x_assum (qspec_then `k + k'` mp_tac) \\ fs [] \\ strip_tac
          \\ spose_not_then assume_tac \\ fs [] \\ rveq
          \\ qpat_x_assum `_ = (q,_)` mp_tac
          \\ qpat_x_assum `_ = (r,_)` mp_tac
          \\ simp [evaluate_def]
          \\ every_case_tac \\ fs [] \\ rveq \\ fs [])
         \\ strip_tac
         \\ qhdtm_x_assum `evaluate` mp_tac
         \\ imp_res_tac evaluate_add_clock
         \\ pop_assum mp_tac
         \\ ntac 2 (pop_assum kall_tac)
         \\ impl_tac
         >- (strip_tac \\ fs [])
         \\ disch_then (qspec_then `k'` mp_tac) \\ simp [inc_clock_def]
         \\ first_x_assum (qspec_then `ck + k` mp_tac) \\ fs []
         \\ ntac 3 strip_tac
         \\ fs [state_rel_def] \\ rveq)
       \\ qpat_x_assum `∀extra._` mp_tac
       \\ first_x_assum (qspec_then `SUC k'` assume_tac)
       \\ first_assum (subterm (fn tm => Cases_on`^(assert has_pair_type tm)`) o concl)
       \\ fs []
       \\ unabbrev_all_tac
       \\ strip_tac
       \\ drule (GEN_ALL optimize_prog_evaluate)
       \\ ntac 2 (disch_then drule)
       \\ impl_tac
       >-
         (last_x_assum (qspec_then `k + SUC k'` mp_tac) \\ fs [] \\ strip_tac
         \\ spose_not_then assume_tac \\ rveq \\ fs [])
       \\ strip_tac \\ rveq \\ fs []
       \\ reverse (Cases_on `s'.ffi.final_event`) \\ fs [] \\ rfs []
       >-
         (first_x_assum (qspec_then `ck + SUC k` mp_tac) \\ fs [ADD1]
         \\ strip_tac \\ fs [state_rel_def] \\ rfs [])
       \\ qhdtm_x_assum `evaluate` mp_tac
       \\ imp_res_tac evaluate_add_clock
       \\ pop_assum kall_tac
       \\ pop_assum mp_tac
       \\ impl_tac
       >- (strip_tac \\ fs [])
       \\ disch_then (qspec_then `ck + SUC k` mp_tac) \\ simp [inc_clock_def]
       \\ fs [ADD1]
       \\ ntac 2 strip_tac \\ rveq
       \\ fs [state_rel_def] \\ rfs [])
     \\ qmatch_assum_abbrev_tac `evaluate (exps,[],st) = _`
     \\ qspecl_then [`exps`,`[]`,`st`] mp_tac evaluate_add_to_clock_io_events_mono
     \\ simp [inc_clock_def, Abbr`st`]
     \\ disch_then (qspec_then `1` strip_assume_tac)
     \\ first_assum (subterm (fn tm => Cases_on`^(assert(has_pair_type)tm)`) o concl)
     \\ unabbrev_all_tac
     \\ drule (GEN_ALL optimize_prog_evaluate)
     \\ ntac 2 (disch_then drule) \\ simp []
     \\ impl_tac
     >-
       (spose_not_then assume_tac
       \\ last_x_assum (qspec_then `k + 1` mp_tac) \\ fs [])
     \\ strip_tac
     \\ asm_exists_tac
     \\ every_case_tac \\ fs [] \\ rveq \\ fs []
     >-
       (qpat_x_assum `evaluate _ = (Rerr e,_)` mp_tac
       \\ imp_res_tac evaluate_add_clock
       \\ pop_assum kall_tac
       \\ pop_assum mp_tac
       \\ impl_tac >- fs []
       \\ disch_then (qspec_then `1` mp_tac) \\ simp [inc_clock_def])
     \\ rfs [state_rel_def] \\ fs [])
   \\ strip_tac
   \\ simp [semantics_def]
   \\ IF_CASES_TAC \\ fs []
   >-
     (last_x_assum (qspec_then `k` assume_tac) \\ rfs []
     \\ first_assum (qspec_then `e` assume_tac)
     \\ fs [] \\ rfs []
     \\ qmatch_assum_abbrev_tac `FST q ≠ _`
     \\ Cases_on `q` \\ fs [markerTheory.Abbrev_def]
     \\ pop_assum (assume_tac o SYM)
     \\ drule (GEN_ALL optimize_prog_evaluate)
     \\ ntac 2 (disch_then drule)
     \\ impl_tac
     >-
       (reverse conj_tac \\ CCONTR_TAC \\ fs []
       \\ fs [] \\ rveq
       \\ qhdtm_x_assum `evaluate` mp_tac
       \\ simp [evaluate_def]
       \\ every_case_tac \\ fs []
       \\ CCONTR_TAC \\ fs [] \\ rveq \\ fs []
       \\ qpat_x_assum `FST _ = _` mp_tac
       \\ simp [evaluate_def]
       \\ drule (GEN_ALL optimize_prog_code_rel) \\ fs []
       \\ disch_then drule
       \\ strip_tac
       (* Automatic simplification de-simplified this part *)
       \\ Cases_on `find_code (SOME start) ([]: v list) (fromAList prog)`
       >- rfs [find_code_def]
       \\ rename1 `_ = SOME exps`
       \\ PairCases_on `exps`
       \\ imp_res_tac code_rel_find_code_no_delete
       \\ first_x_assum (qspec_then `start` mp_tac)
       \\ CASE_TAC >- (fs [] \\ strip_tac \\ rveq \\ fs [])
       \\ CASE_TAC \\ fs [])
     \\ simp []
     \\ spose_not_then strip_assume_tac
     \\ qmatch_assum_abbrev_tac `FST q = _`
     \\ Cases_on `q` \\ fs [markerTheory.Abbrev_def]
     \\ pop_assum (assume_tac o SYM)
     \\ imp_res_tac evaluate_add_clock \\ rfs []
     \\ first_x_assum (qspec_then `ck` mp_tac)
     \\ simp [inc_clock_def])
   \\ DEEP_INTRO_TAC some_intro \\ simp []
   \\ conj_tac
   >-
    (spose_not_then assume_tac \\ rw []
    \\ fsrw_tac [QUANT_INST_ss[pair_default_qp]] []
    \\ last_assum (qspec_then `SUC k` mp_tac)
    \\ (fn g => subterm (fn tm => Cases_on`^(assert (can dest_prod o type_of) tm)` g) (#2 g))
    \\ strip_tac
    \\ drule (GEN_ALL optimize_prog_evaluate)
    \\ ntac 2 (disch_then drule)
    \\ impl_tac
    >- (spose_not_then assume_tac \\ fs [])
    \\ strip_tac
    \\ qmatch_assum_rename_tac `evaluate (_,[],_ (SUC k)) = (_,rr)`
    \\ reverse (Cases_on `rr.ffi.final_event`)
    >-
      (first_x_assum (qspecl_then
        [`SUC k`, `FFI_outcome(THE rr.ffi.final_event)`] mp_tac)
      \\ simp [])
    \\ qpat_x_assum `∀x y. ¬z` mp_tac \\ simp []
    \\ qexists_tac `SUC k` \\ simp []
    \\ reverse (Cases_on `s.ffi.final_event`) \\ fs []
    >-
      (qhdtm_x_assum `evaluate` mp_tac
      \\ qmatch_assum_abbrev_tac `evaluate (opts,[],os) = (r,_)`
      \\ qspecl_then [`opts`,`[]`,`os`] mp_tac evaluate_add_to_clock_io_events_mono
      \\ disch_then (qspec_then `SUC ck` mp_tac)
      \\ fs [ADD1, inc_clock_def, Abbr`os`]
      \\ rpt strip_tac \\ fs []
      \\ fs [state_rel_def] \\ rfs [])
    \\ qhdtm_x_assum `evaluate` mp_tac
    \\ imp_res_tac evaluate_add_clock
    \\ pop_assum mp_tac
    \\ impl_tac >- (strip_tac \\ fs [])
    \\ disch_then (qspec_then `SUC ck` mp_tac)
    \\ simp [inc_clock_def] \\ fs [ADD1]
    \\ rpt strip_tac \\ rveq
    \\ qexists_tac `outcome` \\ rw [])
  \\ strip_tac
  \\ qmatch_abbrev_tac `build_lprefix_lub l1 = build_lprefix_lub l2`
  \\ `(lprefix_chain l1 ∧ lprefix_chain l2) ∧ equiv_lprefix_chain l1 l2`
     suffices_by metis_tac [build_lprefix_lub_thm,
                            lprefix_lub_new_chain,
                            unique_lprefix_lub]
  \\ conj_asm1_tac
  >-
    (unabbrev_all_tac
    \\ conj_tac
    \\ Ho_Rewrite.ONCE_REWRITE_TAC [GSYM o_DEF]
    \\ REWRITE_TAC [IMAGE_COMPOSE]
    \\ match_mp_tac prefix_chain_lprefix_chain
    \\ simp [prefix_chain_def, PULL_EXISTS]
    \\ qx_genl_tac [`k1`,`k2`]
    \\ qspecl_then [`k1`,`k2`] mp_tac LESS_EQ_CASES
    \\ metis_tac [
         LESS_EQ_EXISTS,
         bviPropsTheory.initial_state_with_simp,
         bvlPropsTheory.initial_state_with_simp,
         bviPropsTheory.evaluate_add_to_clock_io_events_mono
           |> CONV_RULE(RESORT_FORALL_CONV(sort_vars["s"]))
           |> Q.SPEC`s with clock := k`
           |> SIMP_RULE (srw_ss())[bviPropsTheory.inc_clock_def],
         bvlPropsTheory.evaluate_add_to_clock_io_events_mono
           |> CONV_RULE(RESORT_FORALL_CONV(sort_vars["s"]))
           |> Q.SPEC`s with clock := k`
           |> SIMP_RULE (srw_ss())[bvlPropsTheory.inc_clock_def]])
  \\ simp [equiv_lprefix_chain_thm]
  \\ unabbrev_all_tac \\ simp [PULL_EXISTS]
  \\ ntac 2 (pop_assum kall_tac)
  \\ simp [LNTH_fromList, PULL_EXISTS, GSYM FORALL_AND_THM]
  \\ rpt gen_tac
  \\ drule (GEN_ALL optimize_prog_evaluate)
  \\ fsrw_tac [QUANT_INST_ss [pair_default_qp]] []
  \\ disch_then (qspecl_then [`start`,`k`,`ffi`] mp_tac) \\ simp []
  \\ Cases_on `k = 0` \\ simp []
  >-
    (fs [evaluate_def]
    \\ every_case_tac \\ fs []
    \\ simp [GSYM IMP_CONJ_THM]
    \\ rpt strip_tac
    \\ qexists_tac `0` \\ simp [])
  \\ impl_tac
  >-
    (spose_not_then assume_tac
    \\ last_x_assum (qspec_then `k` mp_tac) \\ fs [])
  \\ strip_tac
  \\ qmatch_asmsub_abbrev_tac `state_rel (SND p1) (SND p2)`
  \\ Cases_on `p1` \\ Cases_on `p2` \\ fs [markerTheory.Abbrev_def]
  \\ ntac 2 (pop_assum (mp_tac o SYM)) \\ fs []
  \\ ntac 2 strip_tac
  \\ qmatch_assum_rename_tac `state_rel p1 p2`
  \\ `p1.ffi = p2.ffi` by fs [state_rel_def]
  \\ rveq
  \\ conj_tac \\ rw []
  >- (qexists_tac `ck + k` \\ fs [])
  \\ qexists_tac `k` \\ fs []
  \\ qmatch_assum_abbrev_tac `_ < (LENGTH (_ ffi1))`
  \\ `ffi1.io_events ≼ p2.ffi.io_events` by
    (qunabbrev_tac `ffi1`
    \\ metis_tac [
       initial_state_with_simp, evaluate_add_to_clock_io_events_mono
         |> CONV_RULE(RESORT_FORALL_CONV(sort_vars["s"]))
         |> Q.SPEC`s with clock := k`
         |> SIMP_RULE(srw_ss())[inc_clock_def],
       SND,ADD_SYM])
  \\ fs [IS_PREFIX_APPEND]
  \\ simp [EL_APPEND1]);

val _ = export_theory();

