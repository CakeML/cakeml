open preamble
open bviSemTheory
open bviPropsTheory
open bvi_tailrecTheory

(* TODO Might want to get rid of the Commutative/Associative predicates *)

val _ = new_theory "bvi_tailrecProof";

val find_code_def = bvlSemTheory.find_code_def;
val eqs           = closPropsTheory.eqs;
val pure_op_def   = closLangTheory.pure_op_def;

val case_SOME = Q.store_thm ("case_SOME[simp]",
  `(case x of
    | NONE => NONE
    | SOME y => SOME (f y)) = SOME res
    ⇔
    ∃y. x = SOME y ∧ res = f y`,
  Cases_on `x` \\ fs [EQ_SYM_EQ]);

val op_id_val_def = Define `
  (op_id_val Plus  = Number 0) ∧
  (op_id_val Times = Number 1) ∧
  (op_id_val Noop  = Number 0)
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

val AC_Arith = Q.store_thm ("AC_Arith",
  `∀a.
    Associative a Plus  ∧ Commutative a Plus ∧
    Associative a Times ∧ Commutative a Times`,
  cheat (* TODO *)
  );

val op_identity_op_id_val = Q.store_thm ("op_identity_op_id_val",
  `∀iop env s.
    iop ≠ Noop ⇒
      evaluate ([id_from_op iop], env, s) =
        (Rval [op_id_val iop], s)`,
   Cases
   \\ rpt gen_tac
   \\ simp [id_from_op_def, op_id_val_def, evaluate_def]
   \\ simp [do_app_def, do_app_aux_def, small_enough_int_def]);

val tail_check_Arith = Q.store_thm ("tail_check_Arith",
  `∀exp name.
     tail_check name exp = SOME op ⇒
       op ≠ Noop`,
  Induct \\ rpt gen_tac
  \\ TRY (simp [tail_check_def] \\ NO_TAC)
  \\ TRY
    (simp [tail_check_def]
    \\ strip_tac
    \\ first_x_assum drule \\ rw []
    \\ NO_TAC)
  >-
    (simp [tail_check_def]
    \\ TOP_CASE_TAC
    >- (strip_tac \\ first_x_assum drule \\ rw [])
    \\ strip_tac \\ rveq
    \\ first_x_assum drule \\ rw [])
  \\ simp [tail_check_def]
  \\ TOP_CASE_TAC
  \\ IF_CASES_TAC
  \\ strip_tac \\ rveq
  \\ fs [from_op_def] \\ rveq
  \\ rw []);

val optimize_check_Arith = Q.store_thm ("optimize_check_Arith",
  `∀exp name.
    optimize_check name exp = SOME op ⇒
      op ≠ Noop`,
  rpt strip_tac \\ fs [optimize_check_def]
  \\ drule tail_check_Arith \\ fs []);

val tail_check_NONE_op_rewrite = Q.prove (
  `∀exp.
     tail_check name exp = NONE ⇒
       op_rewrite op name exp = (F, exp)`,
  Cases
  \\ once_rewrite_tac [op_rewrite_def]
  \\ fs [tail_check_def]
  \\ IF_CASES_TAC \\ fs []
  \\ TRY (fs [op_eq_def])
  \\ rename1 `Op op1 xs: bvi$exp`
  \\ TOP_CASE_TAC
  \\ IF_CASES_TAC \\ fs []
  >-
    (strip_tac
    \\ Cases_on `op` \\ Cases_on `op1` \\ fs [op_eq_def])
  \\ `from_op op1 = op` by
    (rveq
    \\ pop_assum mp_tac
    \\ once_rewrite_tac [op_rewrite_def]
    \\ Cases_on `op1` \\ Cases_on `op` \\ fs [from_op_def, op_eq_def])
  \\ rveq
  \\ pop_assum mp_tac
  \\ simp [Once op_rewrite_def]
  \\ ntac 2 TOP_CASE_TAC
  \\ rpt (pairarg_tac \\ fs []) \\ rveq
  \\ strip_tac
  \\ every_case_tac \\ fs [] \\ rveq \\ fs [])

val tail_check_NONE_mk_tailcall = Q.prove (
  `tail_check name exp = NONE ⇒
     mk_tailcall n op name acc exp = apply_op op exp (Var acc)`,
  simp [mk_tailcall_def, tail_check_NONE_op_rewrite]
);

val op_binargs_SOME = Q.store_thm ("op_binargs_SOME[simp]",
  `∀exp q. op_binargs exp = SOME q
    ⇔
    ∃e1 e2 op. q = (e1, e2) ∧ exp = Op op [e1; e2]`,
  Cases \\ simp [op_binargs_def]
  \\ rename1 `op_binargs (Op _ xs)`
  \\ Cases_on `xs` \\ simp [op_binargs_def]
  \\ rename1 `op_binargs (Op _ (_::xs))`
  \\ Cases_on `xs` \\ simp [op_binargs_def]
  \\ rename1 `op_binargs (Op _ (_::_::xs))`
  \\ Cases_on `xs` \\ simp [op_binargs_def]
  \\ metis_tac []);

val op_eq_to_op = Q.store_thm ("op_eq_to_op[simp]",
  `∀iop op xs.
      op_eq iop (Op op xs) ∧ iop ≠ Noop
      ⇔
      op = to_op iop ∧ iop ≠ Noop`,
  Cases \\ Cases \\ fs [op_eq_def, to_op_def]);

(* Need something like the theorem(s) in clos_to_bvl *)
val is_pure_state = Q.prove (
  `∀x env s r t.
     evaluate ([x], env, s) = (r, t) ∧
     is_pure x ⇒
       s = t ∧ ∀err. r = Rerr err ⇒ err = Rabort Rtype_error`,
  cheat (* TODO *)
  );

(* TODO restate for all expressions *)
val op_rewrite_is_pure = Q.store_thm ("op_rewrite_is_pure",
  `∀iop name op xs exp2 e1 e2.
     op_rewrite iop name (Op op xs) = (T, exp2) ∧
     op_binargs exp2 = SOME (e1, e2) ⇒
       is_pure e2`,
  cheat (* TODO *)
  );

val evaluate_assoc_swap = Q.store_thm ("evaluate_assoc_swap",
  `is_pure from ∧
   iop ≠ Noop ⇒
     evaluate ([apply_op   iop into from], env, s) =
     evaluate ([assoc_swap iop from into], env, s)`,
  strip_tac
  \\ `Associative (:'a) iop ∧ Commutative (:'a) iop` by
    (assume_tac AC_Arith
    \\ Cases_on `iop` \\ fs [])
  \\ fs [Associative_def, Commutative_def]
  \\ simp [assoc_swap_def]
  \\ TOP_CASE_TAC \\ fs [] \\ rveq
  \\ `to_op iop = op` by cheat (* TODO fix *)
  \\ rveq
  \\ fs [apply_op_def, evaluate_def]);

(* TODO It works but is in serious need of cleanup *)
val evaluate_op_rewrite = Q.store_thm ("evaluate_op_rewrite",
  `∀op name exp env s r t p exp2.
     op_rewrite op name exp = (p, exp2) ∧
     op ≠ Noop ∧
     evaluate ([exp], env, s) = (r, t) ==>
       if ¬p then exp2 = exp else
         evaluate ([exp2], env, s) = (r, t)`,
  ho_match_mp_tac op_rewrite_ind
  \\ rpt gen_tac \\ strip_tac \\ rpt gen_tac
  \\ strip_tac
  \\ qhdtm_x_assum `op_rewrite` mp_tac
  \\ once_rewrite_tac [op_rewrite_def]
  \\ `Associative (:'a) op ∧ Commutative (:'a) op` by
    (assume_tac AC_Arith
    \\ Cases_on `op` \\ fs [])
  \\ IF_CASES_TAC \\ fs []
  \\ ntac 2 TOP_CASE_TAC
  \\ rpt (pairarg_tac \\ fs []) \\ rveq
  \\ reverse (Cases_on `p`) \\ fs []
  >- (every_case_tac \\ fs [])
  \\ `op' = to_op op` by
    (Cases_on `op` \\ Cases_on `op'` \\ fs [to_op_def, op_eq_def])
  \\ rveq
  \\ IF_CASES_TAC \\ fs []
  >-
    (ntac 2 (IF_CASES_TAC \\ fs [])
    \\ strip_tac \\ fs [] \\ rveq
    \\ rw [op_binargs_def, op_eq_to_op]
    \\ drule (GEN_ALL evaluate_assoc_swap)
    \\ fs [apply_op_def]
    \\ strip_tac
    \\ pop_assum (fn th => fs [GSYM th])
    \\ qhdtm_x_assum `evaluate` mp_tac
    \\ simp [Ntimes evaluate_def 2]
    \\ ntac 2 CASE_TAC
    \\ ntac 2 (first_x_assum drule)
    \\ rpt strip_tac \\ fs [] \\ rveq
    \\ every_case_tac \\ fs [] \\ rveq \\ fs [evaluate_def])
  \\ ntac 2 (IF_CASES_TAC \\ fs [])
  \\ strip_tac \\ rveq
  \\ drule (GEN_ALL evaluate_assoc_swap) \\ strip_tac
  \\ fs [apply_op_def]
  \\ pop_assum (fn th => fs [GSYM th])
  \\ qhdtm_x_assum `evaluate` mp_tac
  \\ simp [Ntimes evaluate_def 2]
  \\ ntac 2 CASE_TAC
  \\ ntac 2 (first_x_assum drule)
  \\ fs [Commutative_def, apply_op_def]
  \\ IF_CASES_TAC \\ fs []
  >-
    (strip_tac \\ rveq
    \\ IF_CASES_TAC \\ fs []
    >- (strip_tac \\ rveq \\ rfs [evaluate_def])
    \\ strip_tac \\ rveq
    \\ rename1 `evaluate ([q],_,_) = (_,s2)`
    \\ rename1 `evaluate ([e1],_,s2) = _`
    \\ first_x_assum (qspecl_then [`y1`,`e1`,`env`,`s`] assume_tac)
    \\ rfs [evaluate_def])
  \\ strip_tac \\ rveq
  \\ IF_CASES_TAC \\ fs []
  \\ strip_tac \\ rveq
  \\ rfs [apply_op_def, evaluate_def]);

val optimize_check_IMP_to_op = Q.store_thm ("optimize_check_IMP_to_op",
  `∀op nm xs iop.
      optimize_check nm (Op op xs) = SOME iop ⇒
        op = to_op iop`,
  Cases
  \\ fs [optimize_check_def, ok_tail_type_def,
         is_arithmetic_def, tail_check_def]
  \\ ntac 2 gen_tac
  \\ Cases \\ fs [from_op_def, to_op_def]
  \\ TOP_CASE_TAC \\ fs []);

(* should hold for all input expressions *)
val op_rewrite_correct = Q.store_thm ("op_rewrite_correct",
  `∀iop name op xs exp.
     op_rewrite iop name (Op op xs) = (T, exp) ⇒
       ∃e1 e2. op_binargs exp = SOME (e1, e2)`,
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
  \\ fs [assoc_swap_def, apply_op_def]
  \\ every_case_tac \\ rw []);

val op_rewrite_is_rec = Q.store_thm ("op_rewrite_is_rec",
  `∀iop name op xs e1 e2.
     iop ≠ Noop ∧
     op_rewrite iop name (Op op xs) = (T, Op op [e1; e2]) ⇒
       is_rec name e1`,
  Cases
  \\ rpt gen_tac
  \\ once_rewrite_tac [op_rewrite_def]
  \\ simp [op_eq_def]
  \\ IF_CASES_TAC \\ fs []
  \\ ntac 2 TOP_CASE_TAC
  \\ rpt (pairarg_tac \\ fs []) \\ rveq
  \\ IF_CASES_TAC \\ fs []
  >-
    (ntac 2 (IF_CASES_TAC \\ fs [])
    \\ fs [assoc_swap_def, apply_op_def]
    \\ qpat_x_assum `binop_has_rec _ _ y1` mp_tac
    \\ simp [binop_has_rec_def]
    \\ strip_tac
    >- (strip_tac \\ every_case_tac \\ fs [] \\ rveq \\ fs [is_rec_def])
    \\ Cases_on `y1` \\ fs [is_rec_def, op_binargs_def]
    \\ rpt strip_tac \\ rveq \\ fs []
    \\ every_case_tac \\ fs [] \\ rveq \\ fs [op_binargs_def])
  \\ ntac 2 (IF_CASES_TAC \\ fs [])
  \\ simp [assoc_swap_def, apply_op_def]
  \\ strip_tac
  \\ Cases_on `y2` \\ fs [binop_has_rec_def, is_rec_def, op_binargs_def]
  \\ rveq
  \\ every_case_tac \\ fs [] \\ rveq \\ fs [is_rec_def]);

val op_rewrite_preserves_op = Q.store_thm ("op_rewrite_preserves_op",
  `∀iop name op xs exp2.
      op_rewrite iop name (Op op xs) = (T, exp2) ⇒
        ∃e1 e2. exp2 = Op op [e1;e2]`,
  rpt gen_tac
  \\ once_rewrite_tac [op_rewrite_def]
  \\ Cases_on `iop` \\ Cases_on `op` \\ fs [op_eq_def]
  \\ TOP_CASE_TAC
  \\ TOP_CASE_TAC
  \\ rpt (pairarg_tac \\ fs [])
  \\ every_case_tac \\ fs [assoc_swap_def, apply_op_def, to_op_def]
  \\ every_case_tac \\ rw []);

val env_rel_def = Define `
  env_rel opt_here acc env1 env2 ⇔
    isPREFIX env1 env2 ∧
    (opt_here ⇒
      LENGTH env1 = acc ∧
      LENGTH env2 > acc ∧
      ∃k. EL acc env2 = Number k)
  `;

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

(* TODO Might not be needed *)
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

val state_rel_def = Define `
  state_rel s t ⇔
    s.ffi = t.ffi ∧
    s.clock = t.clock ∧
    code_rel s.code t.code
  `;

val code_rel_domain = Q.store_thm ("code_rel_domain",
  `∀c1 c2.
     code_rel c1 c2 ⇒ domain c1 ⊆ domain c2`,
  simp [code_rel_def, SUBSET_DEF]
  \\ CCONTR_TAC
  \\ fs []
  \\ Cases_on `lookup x c1`
  >- fs [lookup_NONE_domain]
  \\ fs [GSYM lookup_NONE_domain]
  \\ rename1 `SOME exp`
  \\ PairCases_on `exp`
  \\ first_x_assum drule \\ fs []
  \\ Cases_on `optimize_check x exp1` \\ fs []
  \\ simp [optimize_single_def]);

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
  `!skip env n st.
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

val evaluate_let_wrap = Q.store_thm ("evaluate_let_wrap",
  `∀x v vs s r t.
     evaluate ([let_wrap (LENGTH vs) x], v::vs, s) =
     evaluate ([x], vs ++ (v::vs), s)`,
  rpt gen_tac
  \\ `LENGTH vs + 1 ≤ LENGTH (v::vs)` by fs []
  \\ drule evaluate_genlist_vars
  \\ disch_then (qspec_then `s` assume_tac)
  \\ simp [let_wrap_def, evaluate_def])

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

val op_rewrite_IMP_op_eq = Q.prove (
  `∀op name exp p exp2.
     op_rewrite op name exp = (p, exp2) ∧
     op_eq op exp ⇒
       op_eq op exp2`,
  ho_match_mp_tac op_rewrite_ind
  \\ rpt strip_tac
  \\ qhdtm_x_assum `op_rewrite` mp_tac
  \\ once_rewrite_tac [op_rewrite_def]
  \\ IF_CASES_TAC \\ fs []
  \\ TOP_CASE_TAC \\ fs []
  >- (strip_tac \\ rveq \\ fs [])
  \\ rpt (pairarg_tac \\ fs []) \\ rveq
  \\ rename1 `Op op1 _: bvi$exp`
  \\ `op ≠ Noop` by (Cases_on `op` \\ Cases_on `op1` \\ fs [op_eq_def])
  \\ IF_CASES_TAC \\ fs []
  >-
    (IF_CASES_TAC \\ fs []
    >- (strip_tac \\ rveq \\ fs [])
    \\ reverse IF_CASES_TAC \\ fs []
    >- (strip_tac \\ rveq \\ fs [])
    \\ strip_tac \\ rveq
    \\ simp [assoc_swap_def, apply_op_def]
    \\ every_case_tac
    \\ Cases_on `op` \\ fs [op_eq_def, to_op_def])
  \\ reverse IF_CASES_TAC \\ fs []
  >- (strip_tac \\ rveq \\ fs [])
  \\ reverse IF_CASES_TAC \\ fs []
  >- (strip_tac \\ rveq \\ fs [])
  \\ strip_tac \\ rveq
  \\ simp [assoc_swap_def, apply_op_def]
  \\ every_case_tac \\ fs []
  \\ Cases_on `op` \\ fs [op_eq_def, to_op_def]);

val tail_rewrite_rec_or_typed = Q.prove (
  `∀n op name acc exp exp2.
     optimize_check name exp = SOME op ∧
     tail_rewrite n op name acc exp = exp2 ⇒
       (∃ticks args. exp2 = Call ticks (SOME n) args NONE) ∨
       ok_tail_type name exp`,
  ho_match_mp_tac tail_rewrite_ind
  \\ rpt strip_tac \\ rveq
  \\ fs [tail_rewrite_def, ok_tail_type_def, optimize_check_def,
         tail_check_def]);

val ok_tail_type_IMP_Number = Q.store_thm ("ok_tail_type_IMP_Number",
  `∀name exp env (s: 'a bviSem$state) r t.
     ok_tail_type name exp ∧
     evaluate ([exp], env, s) = (Rval r, t) ⇒
       ∃n. r = [Number n]`,
  gen_tac
  \\ Induct
  \\ fs [ok_tail_type_def]
  \\ rpt strip_tac
  \\ pop_assum mp_tac
  \\ simp [evaluate_def]
  >-
    (TOP_CASE_TAC
    \\ TOP_CASE_TAC \\ fs []
    \\ IF_CASES_TAC \\ fs []
    >-
      (strip_tac
      \\ first_x_assum drule
      \\ fs [])
    \\ IF_CASES_TAC \\ fs []
    \\ strip_tac
    \\ first_x_assum drule
    \\ fs [])
  >-
    (TOP_CASE_TAC
    \\ TOP_CASE_TAC \\ fs []
    \\ strip_tac
    \\ first_x_assum (qspec_then `a++env` drule)
    \\ fs [])
  >-
    (IF_CASES_TAC \\ fs []
    \\ strip_tac
    \\ first_x_assum drule
    \\ fs [])
  \\ TOP_CASE_TAC
  \\ TOP_CASE_TAC \\ fs []
  \\ rename1 `is_arithmetic op`
  \\ Cases_on `op`
  \\ fs [is_arithmetic_def]
  \\ simp [do_app_def, do_app_aux_def, small_enough_int_def]
  >- (CASE_TAC \\ strip_tac \\ rveq \\ fs [])
  \\ CASE_TAC
  \\ CASE_TAC
  \\ strip_tac \\ rveq
  \\ fs [bvlSemTheory.do_app_def]
  \\ every_case_tac \\ fs [] \\ rveq \\ fs []);

val is_arithmetic_to_op = Q.store_thm ("is_arithmetic_to_op[simp]",
  `∀iop. is_arithmetic (to_op iop)`,
  Cases \\ fs [is_arithmetic_def, to_op_def]);

val op_rewrite_exp_size = Q.store_thm ("op_rewrite_exp_size",
  `∀op nm exp p exp2.
    op_rewrite op nm exp = (p, exp2) ⇒
      exp_size exp = exp_size exp2`,
  ho_match_mp_tac op_rewrite_ind
  \\ rpt strip_tac
  \\ pop_assum mp_tac
  \\ once_rewrite_tac [op_rewrite_def]
  \\ IF_CASES_TAC \\ fs []
  \\ TOP_CASE_TAC \\ fs []
  \\ rpt (pairarg_tac \\ fs []) \\ rveq
  \\ rename1 `Op op1 _: bvi$exp`
  \\ `op ≠ Noop` by
     (Cases_on `op` \\ Cases_on `op1` \\ fs [op_eq_def])
  \\ `op1 = to_op op` by
    (Cases_on `op` \\ Cases_on `op1` \\ fs [op_eq_def, to_op_def])
  \\ rveq
  \\ IF_CASES_TAC \\ fs []
  >-
    (ntac 2 (IF_CASES_TAC \\ fs [])
    \\ strip_tac \\ rveq
    \\ simp [assoc_swap_def, apply_op_def]
    \\ TOP_CASE_TAC \\ fs []
    >- fs [bviTheory.exp_size_def]
    \\ rveq
    \\ Cases_on `r1` \\ fs []
    \\ `op' = to_op op` by cheat (* TODO fix *)
    \\ rveq
    \\ fs [bviTheory.exp_size_def])
  \\ ntac 2 (IF_CASES_TAC \\ fs [])
  \\ strip_tac \\ rveq
  \\ simp [assoc_swap_def, apply_op_def]
  \\ TOP_CASE_TAC \\ fs []
  >- fs [bviTheory.exp_size_def]
  \\ rveq
  \\ `op' = to_op op` by cheat (* TODO fix *)
  \\ rveq
  \\ fs [bviTheory.exp_size_def]);

val optimized_code_def = Define `
  optimized_code name arity exp n c op =
    ∃exp_aux exp_opt.
        optimize_single n name arity exp = SOME (exp_aux, exp_opt) ∧
        optimize_check name exp = SOME op ∧
        lookup name c = SOME (arity, exp_aux) ∧
        lookup n c    = SOME (arity + 1, exp_opt)
  `;

(* TODO

   - Should try to `place` e2 in such a place that it always evaluates in
     the `same` state, if possible?

   - When e2 evaluates to a value and the args in Call (SOME nm) args NONE
     evaluates to an error I get F in the goal. Solving this simplifies the
     proof of |- ∃n. evaluate ([e2], env, s) = (Rval [Number n], s)

   - The entire expression optimized may still raise an exception as far
     as we know.

   - Remove the name on ok_tail_type
*)

(* TODO perhaps shuffle env_rel and optimized code around a bit *)
val evaluate_optimized_WF = Q.store_thm ("evaluate_optimized_WF",
  `∀xs s env1 r t opt_here c acc env2 nm.
    evaluate (xs, env1, s) = (r, t) ∧
    env_rel opt_here acc env1 env2 ∧
    code_rel s.code c ∧
    (opt_here ⇒ LENGTH xs = 1) ∧
    r ≠ Rerr (Rabort Rtype_error) ⇒
          evaluate (xs, env2, s with code := c) =
            (r, t with code := c) ∧
          (opt_here ⇒
            ∀op n exp arity.
              lookup nm s.code = SOME (arity, exp) ∧
              optimized_code nm arity exp n c op ∧
              optimize_check nm (HD xs) = SOME op ⇒
                evaluate ([tail_rewrite n op nm acc (HD xs)],
                  env2, s with code := c) =
                evaluate ([apply_op op (HD xs) (Var acc)],
                  env2, s with code := c))`,

  ho_match_mp_tac evaluate_complete_ind
  \\ ntac 2 (rpt gen_tac \\ strip_tac)
  \\ Cases_on `xs` \\ fs []
  >- fs [evaluate_def]
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
      \\ ntac 2 (disch_then drule) \\ fs [])
    \\ qmatch_goalsub_rename_tac `evaluate (y::ys, env1, s2)`
    \\ first_assum (qspecl_then [`[h]`,`s`] assume_tac)
    \\ fs [bviTheory.exp_size_def]
    \\ first_x_assum drule
    \\ ntac 2 (disch_then drule) \\ fs []
    \\ strip_tac
    \\ ntac 2 TOP_CASE_TAC
    \\ strip_tac \\ rveq \\ fs []
    \\ first_assum (qspecl_then [`y::ys`,`s2`] assume_tac)
    \\ imp_res_tac evaluate_clock \\ fs [bviTheory.exp_size_def]
    \\ imp_res_tac evaluate_code_const \\ fs []
    \\ first_x_assum drule
    \\ ntac 2 (disch_then drule) \\ fs [])
  \\ fs [bviTheory.exp_size_def]
  \\ Cases_on `∃xs op. h = Op op xs` \\ fs [] \\ rveq
  >-
    (
    conj_tac
    >-
      (qhdtm_x_assum `evaluate` mp_tac \\ simp [evaluate_def]
      \\ TOP_CASE_TAC
      \\ strip_tac
      \\ `env_rel F acc env1 env2` by fs [env_rel_def]
      \\ first_x_assum (qspecl_then [`xs`,`s`] assume_tac)
      \\ fs [bviTheory.exp_size_def]
      \\ first_x_assum drule
      \\ disch_then (qspec_then `F` drule)
      \\ disch_then drule \\ fs []
      \\ impl_tac
      >- (every_case_tac \\ fs [] \\ rveq \\ fs [])
      \\ strip_tac \\ fs []
      \\ every_case_tac \\ fs [] \\ rveq \\ fs []
      \\ imp_res_tac code_rel_domain
      \\ imp_res_tac evaluate_code_const \\ fs []
      \\ imp_res_tac (GEN_ALL do_app_with_code_err)
      \\ imp_res_tac (GEN_ALL do_app_with_code)
      \\ imp_res_tac (GEN_ALL do_app_err) \\ fs []
      \\ first_assum drule \\ fs [])
    \\ rpt strip_tac
    \\ imp_res_tac optimize_check_Arith \\ rveq
    \\ rename1 `iop ≠ Noop`
    \\ imp_res_tac optimize_check_IMP_to_op \\ rveq
    \\ qhdtm_x_assum `evaluate` mp_tac \\ simp [evaluate_def]
    \\ TOP_CASE_TAC
    \\ strip_tac
    \\ simp [tail_rewrite_def, mk_tailcall_def]
    \\ CASE_TAC
    \\ reverse IF_CASES_TAC \\ fs []
    >-
      (drule evaluate_op_rewrite \\ simp []
      \\ disch_then (qspecl_then [`env1`,`s`,`r`,`t`] mp_tac)
      \\ simp [evaluate_def])
    \\ drule op_rewrite_correct
    \\ strip_tac \\ fs [] \\ rveq
    \\ simp [op_binargs_def]
    \\ imp_res_tac op_rewrite_preserves_op \\ fs [] \\ rveq
    \\ imp_res_tac op_rewrite_is_rec
    \\ Cases_on `e1` \\ fs [is_rec_def]
    \\ rename1 `Call ticks dest args hdl: bvi$exp`
    \\ Cases_on `hdl` \\ fs [is_rec_def] \\ rveq
    \\ simp [args_from_def, push_call_def]
    \\ qmatch_asmsub_abbrev_tac `op_rewrite _ _ _ = (_, op_exp)`
    \\ `∀st.
          evaluate ([apply_op iop (Op (to_op iop) xs) (Var acc)],
            env2, st) =
          evaluate ([apply_op iop op_exp (Var acc)],
            env2, st)` by
      (gen_tac
      \\ drule evaluate_op_rewrite \\ simp []
      \\ disch_then (qspecl_then [`env2`,`st`] mp_tac)
      \\ simp [apply_op_def]
      \\ Cases_on `evaluate ([Op (to_op iop) xs], env2, st)` \\ fs []
      \\ strip_tac
      \\ simp [evaluate_def])
    \\ pop_assum (fn th => fs [th])
    \\ unabbrev_all_tac
    \\ qhdtm_assum `optimized_code` mp_tac
    \\ simp_tac std_ss [optimized_code_def]
    \\ strip_tac
    \\ simp [GSYM apply_op_def]
    \\ `ok_tail_type nm (Op (to_op iop) xs)` by fs [optimize_check_def]
    \\ imp_res_tac ok_tail_type_IMP_Number
    \\ `env_rel F acc env1 env2` by fs [env_rel_def]
    \\ `acc < LENGTH env2` by fs [env_rel_def]
    \\ `∃k. EL acc env2 = Number k` by fs [env_rel_def]
    \\ drule evaluate_op_rewrite
    \\ disch_then (qspecl_then [`env1`,`s`,`r`,`t`] mp_tac) \\ simp []
    \\ simp [Once evaluate_def]
    \\ strip_tac
    \\ `∀t r.
          evaluate ([Op (to_op iop) [Call ticks (SOME nm) args NONE; e2]],
            env1, s) = (Rval r, t) ⇒
            ∃j. r = [Number j]` by
      (fs [optimize_check_def]
      \\ drule ok_tail_type_IMP_Number
      \\ simp [evaluate_def]
      \\ disch_then (qspecl_then [`env1`,`s`] mp_tac)
      \\ TOP_CASE_TAC
      \\ fs [])
    \\ first_assum (qspecl_then [`xs`,`s`] mp_tac)
    \\ simp [bviTheory.exp_size_def]
    \\ disch_then drule
    \\ disch_then (qspec_then `F` drule)
    \\ disch_then drule \\ simp []
    \\ impl_tac
    >- (every_case_tac \\ fs [] \\ rveq \\ fs [])
    \\ strip_tac
    (* Easier to evaluate the call in the pre-state *)
    \\ Cases_on `evaluate ([Call ticks (SOME nm) args NONE], env1, s)`
    \\ pop_assum mp_tac
    \\ simp [Once evaluate_def]
    \\ CASE_TAC
    \\ rename1 `_ = (res_args, st_args)`
    \\ first_assum (qspecl_then [`args`,`s`] mp_tac)
    \\ imp_res_tac op_rewrite_exp_size
    \\ fs [bviTheory.exp_size_def]
    \\ pop_assum kall_tac
    \\ disch_then drule
    \\ disch_then (qspec_then `F` drule)
    \\ disch_then drule \\ fs []
    \\ impl_tac
    >-
      (qpat_x_assum `_ = (r, t)` mp_tac
      \\ simp [evaluate_def]
      \\ strip_tac
      \\ every_case_tac \\ fs [] \\ rveq \\ fs [])
    \\ strip_tac
    \\ cheat (* TODO *)
    )
  \\ Cases_on `∃ticks dest xs hdl. h = Call ticks dest xs hdl` \\ fs [] \\ rveq
  >-
    (
    simp [optimize_check_def, tail_check_def]
    \\ `env_rel F acc env1 env2` by fs [env_rel_def]
    \\ qhdtm_x_assum `evaluate` mp_tac
    \\ simp [Once evaluate_def]
    \\ IF_CASES_TAC >- fs []
    \\ `dest = NONE ⇒ ¬IS_SOME hdl` by metis_tac []
    \\ qpat_x_assum `¬(_)` kall_tac
    \\ first_assum (qspecl_then [`xs`,`s`] assume_tac)
    \\ fs [bviTheory.exp_size_def]
    \\ Cases_on `dest` \\ fs []
    >-
      (TOP_CASE_TAC
      \\ first_x_assum drule
      \\ disch_then (qspec_then `F` drule)
      \\ disch_then drule \\ fs []
      \\ reverse TOP_CASE_TAC
      >- (rpt strip_tac \\ rveq \\ rfs [evaluate_def])
      \\ strip_tac
      \\ TOP_CASE_TAC
      >-
        (strip_tac \\ rveq
        \\ simp [evaluate_def]
        \\ TOP_CASE_TAC \\ fs [])
      \\ TOP_CASE_TAC
      \\ IF_CASES_TAC \\ fs []
      >-
        (strip_tac \\ rveq \\ simp [evaluate_def]
        \\ TOP_CASE_TAC \\ fs []
        >-
          (imp_res_tac evaluate_code_const \\ fs []
          \\ ntac 2 (qhdtm_x_assum `find_code` mp_tac)
          \\ simp [find_code_def]
          \\ ntac 3 (CASE_TAC \\ fs [])
          \\ strip_tac \\ rveq
          \\ reverse TOP_CASE_TAC
          >-
            (CASE_TAC
            \\ IF_CASES_TAC \\ fs []
            \\ fs [code_rel_def]
            \\ first_x_assum drule
            \\ Cases_on `optimize_check n r` \\ fs []
            \\ fs [optimize_single_def])
          \\ fs [code_rel_def]
          \\ first_x_assum drule
          \\ Cases_on `optimize_check n r` \\ fs []
          \\ fs [optimize_single_def])
        \\ CASE_TAC \\ fs [])
      \\ rename1 `evaluate ([exp],q,dec_clock (ticks+1) s2)`
      \\ TOP_CASE_TAC
      \\ strip_tac
      \\ first_assum
        (qspecl_then [`[exp]`,`dec_clock (ticks+1) s2`] assume_tac)
      \\ `(dec_clock (ticks+1) s2).clock < s.clock` by
        (fs [dec_clock_def]
        \\ imp_res_tac evaluate_clock \\ fs [])
      \\ fs []
      \\ Cases_on `optimize_check nm exp` \\ fs []
      >-
        (first_x_assum drule
        \\ `env_rel F acc q q` by fs [env_rel_def]
        \\ imp_res_tac evaluate_code_const \\ fs []
        \\ disch_then (qspec_then `F` drule)
        \\ disch_then drule \\ fs []
        \\ impl_tac
        >- (every_case_tac \\ fs [] \\ rveq \\ fs [])
        \\ strip_tac
        \\ simp [evaluate_def]
        \\ TOP_CASE_TAC \\ fs []
        >-
          (ntac 2 (qhdtm_x_assum `find_code` mp_tac)
          \\ simp [find_code_def]
          \\ ntac 3 CASE_TAC
          \\ IF_CASES_TAC \\ fs []
          \\ strip_tac \\ rveq \\ fs []
          \\ TOP_CASE_TAC
          >-
            (fs [code_rel_def]
            \\ first_x_assum drule
            \\ Cases_on `optimize_check n exp` \\ fs []
            \\ simp [optimize_single_def])
          \\ CASE_TAC \\ fs []
          \\ fs [code_rel_def]
          \\ first_x_assum drule
          \\ Cases_on `optimize_check n exp` \\ fs []
          \\ simp [optimize_single_def]
          \\ strip_tac \\ rveq \\ fs [])
        \\ CASE_TAC \\ fs []
        \\ ntac 2 (qhdtm_x_assum `find_code` mp_tac)
        \\ simp [find_code_def]
        \\ ntac 3 CASE_TAC \\ fs []
        \\ strip_tac \\ rveq
        \\ ntac 2 CASE_TAC \\ fs []
        \\ strip_tac \\ rveq
        \\ qhdtm_assum `code_rel` mp_tac
        \\ simp_tac std_ss [code_rel_def]
        \\ disch_then drule
        \\ Cases_on `optimize_check n exp` \\ fs []
        >-
          (strip_tac \\ rveq
          \\ every_case_tac \\ fs [] \\ rveq \\ fs [])
        \\ simp [optimize_single_def]
        \\ strip_tac \\ rveq
        \\ simp [evaluate_def]
        \\ imp_res_tac optimize_check_Arith
        \\ fs [op_identity_op_id_val]
        \\ `q = LENGTH (FRONT a)` by (Cases_on `a` \\ fs [])
        \\ simp [evaluate_let_wrap]
        \\ first_x_assum
          (qspecl_then [`[exp]`,`dec_clock (ticks+1) s2`] assume_tac)
        \\ rfs []
        \\ `env_rel T (LENGTH (FRONT a))
                      (FRONT a)
                      (FRONT a ++ op_id_val x::FRONT a)` by
          (fs [env_rel_def]
          \\ fs [EL_LENGTH_APPEND]
          \\ Cases_on `x` \\ fs [op_id_val_def])
        \\ imp_res_tac evaluate_code_const \\ fs []
        \\ first_x_assum drule
        \\ disch_then (qspec_then `T` drule)
        \\ disch_then drule
        \\ disch_then (qspec_then `n` mp_tac)
        \\ impl_tac
        >- (every_case_tac \\ fs [] \\ rveq \\ fs [])
        \\ fs []
        \\ strip_tac
        \\ rename1 `tail_rewrite m x n _ exp`
        \\ first_x_assum (qspec_then `m` mp_tac)
        \\ fs [optimized_code_def, optimize_single_def]
        \\ simp [apply_op_def]
        \\ strip_tac \\ pop_assum kall_tac
        \\ simp [evaluate_def]
        \\ fs [EL_LENGTH_APPEND]
        \\ rename1 `evaluate _ = (res_exp, s3 with code := c)`
        \\ reverse (Cases_on `res_exp`) \\ fs []
        >- (every_case_tac \\ fs [] \\ rveq \\ fs [])
        \\ fs [optimize_check_def]
        \\ imp_res_tac ok_tail_type_IMP_Number \\ rveq \\ fs []
        \\ Cases_on `x` \\ fs [op_id_val_def, to_op_def]
        \\ fs [do_app_def, do_app_aux_def, bvlSemTheory.do_app_def]
        \\ fs [bvl_to_bvi_id])
      \\ imp_res_tac optimize_check_Arith
      \\ simp [evaluate_def]
      \\ TOP_CASE_TAC \\ fs []
      >-
        (ntac 2 (qhdtm_x_assum `find_code` mp_tac)
        \\ simp [find_code_def]
        \\ ntac 3 CASE_TAC \\ fs []
        \\ strip_tac \\ rveq
        \\ qhdtm_assum `code_rel` mp_tac
        \\ simp_tac std_ss [code_rel_def] \\ strip_tac
        \\ TOP_CASE_TAC \\ fs []
        >-
          (imp_res_tac evaluate_code_const \\ fs []
          \\ first_x_assum drule
          \\ Cases_on `optimize_check n exp` \\ fs []
          \\ simp [optimize_single_def])
        \\ CASE_TAC \\ fs []
        \\ imp_res_tac evaluate_code_const \\ fs []
        \\ first_x_assum drule
        \\ Cases_on `optimize_check n exp` \\ fs []
        \\ simp [optimize_single_def]
        \\ strip_tac \\ rveq \\ fs [])
      \\ CASE_TAC
      \\ ntac 2 (qhdtm_x_assum `find_code` mp_tac)
      \\ simp [find_code_def]
      \\ ntac 3 CASE_TAC \\ fs []
      \\ strip_tac \\ rveq
      \\ qhdtm_assum `code_rel` mp_tac
      \\ simp_tac std_ss [code_rel_def]
      \\ strip_tac
      \\ ntac 3 CASE_TAC \\ fs []
      \\ strip_tac \\ rveq
      \\ imp_res_tac evaluate_code_const \\ fs []
      \\ first_x_assum drule
      \\ Cases_on `optimize_check n exp` \\ fs []
      >-
        (strip_tac \\ rveq
        \\ `env_rel F acc (FRONT a) (FRONT a)` by fs [env_rel_def]
        \\ imp_res_tac evaluate_code_const \\ fs []
        \\ first_x_assum drule
        \\ disch_then (qspec_then `F` drule)
        \\ disch_then drule
        \\ disch_then (qspec_then `n` mp_tac) \\ fs []
        \\ impl_tac
        >- (every_case_tac \\ fs [] \\ rveq \\ fs [])
        \\ strip_tac
        \\ every_case_tac \\ fs [] \\ rveq \\ fs [])
      \\ imp_res_tac optimize_check_Arith
      \\ simp [optimize_single_def]
      \\ strip_tac \\ rveq
      \\ simp [evaluate_def]
      \\ imp_res_tac op_identity_op_id_val \\ fs []
      \\ `q = LENGTH (FRONT a)` by (Cases_on `a` \\ fs [FRONT_DEF])
      \\ simp [evaluate_let_wrap]
      \\ first_x_assum
        (qspecl_then [`[exp]`,`dec_clock (ticks+1) s2`] assume_tac)
      \\ rfs []
      \\ rename1 `tail_rewrite m x1 n _ exp`
      \\ `env_rel T (LENGTH (FRONT a))
                    (FRONT a)
                    (FRONT a ++ op_id_val x1::FRONT a)` by
        (fs [env_rel_def]
        \\ fs [EL_LENGTH_APPEND]
        \\ Cases_on `x1` \\ fs [op_id_val_def])
      \\ first_x_assum drule
      \\ disch_then (qspec_then `T` drule)
      \\ disch_then drule \\ fs []
      \\ disch_then (qspec_then `n` mp_tac)
      \\ impl_tac
      >- (every_case_tac \\ fs [] \\ rveq \\ fs [])
      \\ strip_tac
      \\ first_x_assum drule
      \\ fs [optimized_code_def, optimize_single_def]
      \\ disch_then (qspec_then `m` mp_tac) \\ simp []
      \\ strip_tac
      \\ simp [apply_op_def, evaluate_def]
      \\ rename1 `evaluate _ = (res_exp, s3 with code := c)`
      \\ reverse (Cases_on `res_exp`) \\ fs []
      >- (every_case_tac \\ fs [] \\ rveq \\ fs [])
      \\ simp [EL_LENGTH_APPEND]
      \\ fs [optimize_check_def]
      \\ imp_res_tac ok_tail_type_IMP_Number \\ fs [] \\ rveq
      \\ Cases_on `x1` \\ fs [to_op_def, op_id_val_def]
      \\ simp [do_app_def, do_app_aux_def, bvlSemTheory.do_app_def]
      \\ simp [bvl_to_bvi_id])
    \\ TOP_CASE_TAC
    \\ reverse TOP_CASE_TAC
    >-
      (fs [] \\ strip_tac \\ rveq
      \\ first_x_assum drule
      \\ disch_then (qspec_then `F` mp_tac)
      \\ ntac 2 (disch_then drule)
      \\ fs [evaluate_def])
    \\ TOP_CASE_TAC >- fs []
    \\ TOP_CASE_TAC
    \\ IF_CASES_TAC
    >-
      (strip_tac \\ fs [] \\ rveq
      \\ first_x_assum drule
      \\ disch_then (qspec_then `F` mp_tac) \\ fs []
      \\ ntac 2 (disch_then drule)
      \\ imp_res_tac code_rel_find_code_no_delete
      \\ strip_tac
      \\ simp [evaluate_def]
      \\ imp_res_tac evaluate_code_const \\ fs []
      \\ TOP_CASE_TAC >- rfs []
      \\ TOP_CASE_TAC)
    \\ qmatch_assum_rename_tac `_ = SOME (args, exp)`
    \\ qmatch_assum_rename_tac `evaluate (_,_,s1) = (_, s2)`
    \\ first_x_assum drule
    \\ disch_then (qspec_then `F` drule) \\ fs []
    \\ disch_then drule
    \\ strip_tac
    \\ TOP_CASE_TAC
    \\ strip_tac \\ fs [] \\ rveq
    \\ imp_res_tac evaluate_code_const \\ fs []
    \\ qhdtm_assum `code_rel` mp_tac
    \\ SIMP_TAC std_ss [code_rel_def] \\ fs []
    \\ disch_then drule
    \\ Cases_on `optimize_check x exp` \\ fs [] \\ strip_tac
    >-
      (simp [evaluate_def, find_code_def]
      \\ first_assum
        (qspecl_then [`[exp]`,`dec_clock (ticks+1) s2`] mp_tac)
      \\ `(dec_clock (ticks+1) s2).clock < s1.clock` by
        (simp [dec_clock_def]
        \\ imp_res_tac evaluate_clock \\ fs [])
      \\ fs []
      \\ pop_assum kall_tac
      \\ `env_rel F acc a a` by fs [env_rel_def]
      \\ imp_res_tac evaluate_code_const
      \\ disch_then drule
      \\ disch_then (qspec_then `F` drule)
      \\ disch_then drule
      \\ disch_then (qspec_then `nm` mp_tac)
      \\ impl_tac
      >- (every_case_tac \\ fs [] \\ rveq \\ fs [])
      \\ fs []
      \\ strip_tac
      \\ every_case_tac \\ fs [] \\ rveq \\ fs []
      \\ rename1 `evaluate ([exc],throw::env1, s3) = (r, t)`
      \\ first_assum (qspecl_then [`[exc]`,`s3`] mp_tac)
      \\ `s3.clock < s1.clock` by
        (imp_res_tac evaluate_clock
        \\ fs [dec_clock_def])
      \\ fs []
      \\ `env_rel F acc (throw::env1) (throw::env2)` by fs [env_rel_def]
      \\ disch_then drule
      \\ disch_then (qspec_then `F` drule)
      \\ disch_then drule
      \\ disch_then (qspec_then `nm` mp_tac)
      \\ fs [])
    \\ Cases_on `optimize_single n x (LENGTH a) exp`
    >- rfs [optimize_single_def]
    \\ fs []
    \\ qmatch_assum_rename_tac `_ = SOME exp_`
    \\ PairCases_on `exp_` \\ fs []
    \\ imp_res_tac optimize_check_Arith \\ rveq
    \\ rename1 `iop ≠ Noop`
    \\ simp [evaluate_def, find_code_def]
    \\ fs [optimize_single_def] \\ rveq
    \\ fs [] \\ rveq
    \\ simp [evaluate_def, op_identity_op_id_val, evaluate_let_wrap]
    \\ first_assum (qspecl_then [`[exp]`, `dec_clock (ticks+1) s2`] mp_tac)
    \\ `(dec_clock (ticks+1) s2).clock < s1.clock` by
      (fs [dec_clock_def]
      \\ imp_res_tac evaluate_clock \\ fs [])
    \\ simp []
    \\ `env_rel T (LENGTH a) a (a ++ op_id_val iop::a)` by
      (fs [env_rel_def]
      \\ fs [EL_LENGTH_APPEND]
      \\ Cases_on `iop` \\ fs [op_id_val_def])
    \\ disch_then drule
    \\ disch_then (qspec_then `T` drule)
    \\ disch_then drule
    \\ disch_then (qspec_then `x` mp_tac)
    \\ impl_tac
    >- (every_case_tac \\ fs [] \\ rveq \\ fs [])
    \\ simp []
    \\ strip_tac
    \\ first_x_assum (qspec_then `n` mp_tac)
    \\ simp [optimized_code_def, optimize_single_def]
    \\ strip_tac
    \\ pop_assum kall_tac
    \\ simp [apply_op_def, evaluate_def, EL_LENGTH_APPEND]
    \\ `ok_tail_type x exp` by fs [optimize_check_def]
    \\ imp_res_tac ok_tail_type_IMP_Number \\ rfs []
    \\ rename1 `evaluate ([exp], _, _) = (res_exp, st_exp with code := c)`
    \\ reverse (Cases_on `res_exp`) \\ fs []
    >-
      (every_case_tac \\ fs [] \\ rveq \\ fs []
      \\ rename1 `evaluate ([exc], throw::env1, st_exp) = (r, t)`
      \\ first_x_assum (qspecl_then [`[exc]`,`st_exp`] mp_tac)
      \\ `st_exp.clock < s1.clock` by
        (imp_res_tac evaluate_clock
        \\ fs [dec_clock_def])
      \\ simp []
      \\ `env_rel F acc (throw::env1) (throw::env2)` by fs [env_rel_def]
      \\ disch_then drule
      \\ disch_then (qspec_then `F` drule)
      \\ disch_then drule
      \\ disch_then (qspec_then `nm` mp_tac)
      \\ fs [])
    \\ first_x_assum drule \\ strip_tac \\ rveq \\ fs []
    \\ Cases_on `iop` \\ fs [to_op_def, op_id_val_def]
    \\ simp [do_app_def, do_app_aux_def, bvlSemTheory.do_app_def]
    \\ fs [bvl_to_bvi_id])
  \\ Cases_on `∃x1 x2 x3. h = If x1 x2 x3` \\ fs [] \\ rveq
  >-
    (
    qhdtm_x_assum `evaluate` mp_tac \\ simp [evaluate_def]
    \\ `env_rel F acc env1 env2` by fs [env_rel_def]
    \\ TOP_CASE_TAC
    \\ reverse TOP_CASE_TAC \\ fs []
    >-
      (strip_tac \\ rveq \\ fs []
      \\ first_assum (qspecl_then [`[x1]`,`s`] assume_tac)
      \\ fs [bviTheory.exp_size_def]
      \\ first_x_assum drule
      \\ disch_then (qspec_then `F` drule)
      \\ disch_then drule \\ fs []
      \\ rpt strip_tac
      \\ imp_res_tac optimize_check_Arith
      \\ imp_res_tac optimize_check_IMP_to_op
      \\ simp [tail_rewrite_def, evaluate_def, apply_op_def])
    \\ first_assum (qspecl_then [`[x1]`,`s`] assume_tac)
    \\ fs [bviTheory.exp_size_def]
    \\ first_x_assum drule
    \\ disch_then (qspec_then `F` drule)
    \\ disch_then drule \\ fs []
    \\ strip_tac
    \\ reverse (Cases_on `opt_here`) \\ fs []
    >-
      (rename1 `evaluate ([x1],_,s) = (_,s2)`
      \\ IF_CASES_TAC \\ fs []
      >-
        (strip_tac
        \\ first_assum (qspecl_then [`[x2]`,`s2`] assume_tac)
        \\ imp_res_tac evaluate_clock
        \\ imp_res_tac evaluate_code_const
        \\ fs [bviTheory.exp_size_def]
        \\ first_x_assum drule
        \\ disch_then (qspec_then `F` drule) \\ fs [])
      \\ IF_CASES_TAC \\ fs []
      \\ strip_tac
      \\ first_assum (qspecl_then [`[x3]`,`s2`] assume_tac)
      \\ imp_res_tac evaluate_clock
      \\ imp_res_tac evaluate_code_const
      \\ fs [bviTheory.exp_size_def]
      \\ first_x_assum drule
      \\ disch_then (qspec_then `F` drule) \\ fs [])
    \\ rename1 `evaluate ([x1],_,s) = (_,s2)`
    \\ IF_CASES_TAC \\ fs []
    >-
      (
      strip_tac
      \\ first_assum (qspecl_then [`[x2]`,`s2`] assume_tac)
      \\ imp_res_tac evaluate_clock
      \\ imp_res_tac evaluate_code_const
      \\ fs [bviTheory.exp_size_def]
      \\ first_x_assum drule
      \\ disch_then (qspec_then `T` drule) \\ fs []
      \\ disch_then drule
      \\ disch_then (qspec_then `nm` strip_assume_tac)
      \\ rpt strip_tac
      \\ first_x_assum drule
      \\ disch_then drule
      \\ cheat (* TODO *)
      )
    \\ cheat (* TODO *)
    )
  \\ Cases_on `∃xs x1. h = Let xs x1` \\ fs [] \\ rveq
  >-
    (
    qpat_x_assum `evaluate _ = _` mp_tac \\ simp [evaluate_def]
    \\ `env_rel F acc env1 env2` by fs [env_rel_def]
    \\ TOP_CASE_TAC
    \\ reverse TOP_CASE_TAC
    >-
      (strip_tac \\ rveq \\ fs []
      \\ first_assum (qspecl_then [`xs`,`s`] assume_tac)
      \\ fs [bviTheory.exp_size_def]
      \\ first_x_assum drule
      \\ disch_then (qspec_then `F` mp_tac) \\ fs []
      \\ ntac 2 (disch_then drule)
      \\ strip_tac \\ fs []
      \\ rpt strip_tac
      \\ imp_res_tac optimize_check_Arith \\ rveq
      \\ fs [tail_rewrite_def, apply_op_def, evaluate_def])
    \\ strip_tac
    \\ first_assum (qspecl_then [`xs`,`s`] assume_tac)
    \\ fs [bviTheory.exp_size_def]
    \\ first_x_assum drule
    \\ disch_then (qspec_then `F` drule)
    \\ disch_then drule \\ fs []
    \\ strip_tac
    \\ imp_res_tac evaluate_clock
    \\ imp_res_tac evaluate_code_const
    \\ `env_rel opt_here (acc+LENGTH a) (a++env1) (a++env2)` by
      (Cases_on `opt_here`
      \\ fs [env_rel_def, IS_PREFIX_LENGTH]
      \\ fs [EL_APPEND2])
    \\ rename1 `evaluate (xs,_,s) = (_, s2)`
    \\ first_x_assum (qspecl_then [`[x1]`,`s2`] assume_tac)
    \\ fs [bviTheory.exp_size_def]
    \\ `s2.clock ≤ s.clock` by (imp_res_tac evaluate_clock \\ fs [])
    \\ rfs []
    \\ first_x_assum drule
    \\ ntac 2 (disch_then drule)
    \\ disch_then (qspec_then `nm` assume_tac) \\ rfs []
    \\ rpt strip_tac
    \\ fs []
    \\ first_x_assum drule
    \\ rpt strip_tac
    \\ Cases_on `optimize_check nm x1`
    >- rfs [optimize_check_def, tail_check_def, ok_tail_type_def]
    \\ `acc < LENGTH env2` by fs [env_rel_def]
    \\ imp_res_tac optimize_check_Arith \\ fs [] \\ rveq
    \\ fs [tail_rewrite_def, apply_op_def]
    \\ rename1 `op1 = op2 ⇒ _`
    \\ `op1 = op2` by fs [optimize_check_def, tail_check_def]
    \\ rveq \\ fs []
    \\ imp_res_tac evaluate_IMP_LENGTH \\ fs []
    \\ simp [evaluate_def, EL_APPEND2])
  \\ Cases_on `∃x1. h = Tick x1` \\ fs [] \\ rveq
  >-
    (qpat_x_assum `evaluate _ = _` mp_tac \\ simp [evaluate_def]
    \\ IF_CASES_TAC \\ fs []
    \\ strip_tac \\ rveq \\ fs []
    >-
      (rpt strip_tac
      \\ imp_res_tac optimize_check_Arith \\ rveq
      \\ fs [tail_rewrite_def, apply_op_def, evaluate_def])
    \\ first_x_assum (qspecl_then [`[x1]`, `dec_clock 1 s`] assume_tac)
    \\ `(dec_clock 1 s).clock < s.clock` by fs [dec_clock_def]
    \\ fs [bviTheory.exp_size_def]
    \\ pop_assum kall_tac
    \\ first_x_assum drule \\ fs []
    \\ ntac 2 (disch_then drule)
    \\ disch_then (qspec_then `nm` assume_tac) \\ rfs []
    \\ rpt strip_tac \\ fs []
    \\ first_x_assum drule
    \\ `optimize_check nm x1 = SOME op` by
      rfs [optimize_check_def, tail_check_def, ok_tail_type_def]
    \\ fs []
    \\ strip_tac
    \\ imp_res_tac optimize_check_Arith \\ fs [] \\ rveq
    \\ `acc < LENGTH env2` by fs [env_rel_def]
    \\ fs [tail_rewrite_def, evaluate_def, apply_op_def]
    \\ IF_CASES_TAC \\ fs [])
  \\ Cases_on `∃v. h = Var v` \\ fs [] \\ rveq
  >-
    (qpat_x_assum `evaluate _ = _` mp_tac \\ simp [evaluate_def]
    \\ IF_CASES_TAC \\ fs []
    \\ strip_tac \\ fs [] \\ rveq
    \\ reverse IF_CASES_TAC
    >-
      (fs [env_rel_def]
      \\ pop_assum mp_tac \\ fs []
      \\ `LENGTH env1 ≤ LENGTH env2` by fs [IS_PREFIX_LENGTH]
      \\ fs [])
    \\ conj_tac
    >- (fs [env_rel_def] \\ imp_res_tac is_prefix_el \\ fs [])
    \\ rpt strip_tac
    \\ fs [tail_rewrite_def, mk_tailcall_def]
    \\ imp_res_tac optimize_check_Arith \\ rveq
    \\ once_rewrite_tac [op_rewrite_def]
    \\ simp [op_eq_def])
  \\ Cases_on `∃x1. h = Raise x1` \\ fs [] \\ rveq
  >-
    (simp [optimize_check_def, tail_check_def]
    \\ qpat_x_assum `evaluate _ = _` mp_tac \\ simp [evaluate_def]
    \\ TOP_CASE_TAC
    \\ strip_tac
    \\ first_x_assum (qspecl_then [`[x1]`,`s`] assume_tac) \\ rfs []
    \\ fs [bviTheory.exp_size_def]
    \\ first_x_assum drule \\ fs []
    \\ `env_rel F acc env1 env2` by
      (Cases_on `opt_here` \\ fs [env_rel_def])
    \\ disch_then (qspec_then `F` drule)
    \\ disch_then drule \\ fs []
    \\ impl_tac
    >- (every_case_tac \\ fs [] \\ rveq \\ fs [])
    \\ strip_tac
    \\ every_case_tac \\ fs [] \\ rveq \\ fs [])
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
    \\ IF_CASES_TAC \\ fs []
    \\ strip_tac \\ rveq \\ fs []
    \\ first_x_assum drule
    \\ disch_then drule
    \\ rpt strip_tac \\ rveq \\ rfs []
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
    \\ disch_then drule \\ rw []
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
  \\ drule (GEN_ALL optimize_prog_code_rel)
  \\ disch_then drule
  \\ disch_then (qspec_then `optimize_prog n prog` assume_tac) \\ fs []
  \\ qmatch_assum_abbrev_tac `code_rel _ c`
  \\ `fromAList prog = st1.code` by fs [Abbr`st1`]
  \\ pop_assum (fn th => fs [th])
  \\ drule evaluate_optimized_WF
  \\ disch_then (qspec_then `F` drule)
  \\ disch_then drule \\ fs []
  \\ strip_tac
  \\ qexists_tac `0` \\ fs [inc_clock_ZERO]
  \\ fs [Abbr`st1`]
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

