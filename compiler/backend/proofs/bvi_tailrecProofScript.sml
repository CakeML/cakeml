open preamble bviSemTheory
open bviPropsTheory bvi_tailrecTheory

(* TODO

   - It should be possible to prove that we can replace the simplified
     compile_exp by the old compile_exp without touching the evaluate-
     theorem. Benefits:
       * Less code duplication
       * Can inline auxiliary calls more easily
*)

val _ = new_theory "bvi_tailrecProof";

val find_code_def = bvlSemTheory.find_code_def;

val case_SOME = Q.store_thm ("case_SOME",
  `(case x of
    | NONE => NONE
    | SOME y => SOME (f y)) = SOME res
    ⇔
    ∃y. x = SOME y ∧ res = f y`,
  Cases_on `x` \\ fs [EQ_SYM_EQ]);

val _ = bossLib.augment_srw_ss [rewrites [case_SOME]];

val get_bin_args_SOME = Q.store_thm ("get_bin_args_SOME[simp]",
  `∀exp q. get_bin_args exp = SOME q
    ⇔
    ∃e1 e2 op. q = (e1, e2) ∧ exp = Op op [e1; e2]`,
  Cases \\ simp [get_bin_args_def]
  \\ rename1 `get_bin_args (Op _ xs)`
  \\ Cases_on `xs` \\ simp [get_bin_args_def]
  \\ rename1 `get_bin_args (Op _ (_::xs))`
  \\ Cases_on `xs` \\ simp [get_bin_args_def]
  \\ rename1 `get_bin_args (Op _ (_::_::xs))`
  \\ Cases_on `xs` \\ simp [get_bin_args_def]
  \\ metis_tac []);

val op_eq_to_op = Q.store_thm ("op_eq_to_op[simp]",
  `∀iop op xs.
      op_eq iop (Op op xs)
      ⇔
      op = to_op iop ∧ iop ≠ Noop`,
  Cases \\ Cases \\ fs [op_eq_def, to_op_def]);

val ty_rel_def = Define `
  ty_rel = LIST_REL (λv t. t = Int ⇒ ∃k. v = Number k)
  `;

val is_arith_op_to_op = Q.store_thm ("is_arith_op_to_op[simp]",
  `∀iop. is_arith_op (to_op iop)`,
  Cases \\ fs [is_arith_op_def, to_op_def]);

val scan_expr_eq_aux = Q.store_thm ("scan_expr_eq_aux",
  `∀ts exp loc. scan_aux ts exp = FST (scan_expr ts loc exp)`,
  ho_match_mp_tac scan_aux_ind
  \\ rw [scan_aux_def, scan_expr_def]
  \\ rpt (pairarg_tac \\ fs [])
  \\ metis_tac [FST]);

val MAP2_LENGTH = Q.store_thm ("MAP2_LENGTH",
  `∀xs ys.
     LENGTH (MAP2 f xs ys) = MIN (LENGTH xs) (LENGTH ys)`,
  Induct \\ rw []
  \\ Cases_on `ys` \\ fs [MIN_DEF] \\ EVAL_TAC);

val MAP2_K = Q.store_thm ("MAP2_K",
  `∀xs ys.
     MAP2 K xs ys = TAKE (MIN (LENGTH xs) (LENGTH ys)) xs`,
  Induct \\ rw []
  \\ Cases_on `ys` \\ fs [MIN_DEF] \\ EVAL_TAC
  \\ IF_CASES_TAC \\ fs []);

val MAP2_EL = Q.store_thm ("MAP2_HD",
  `∀xs ys n.
     n < MIN (LENGTH xs) (LENGTH ys) ⇒
       EL n (MAP2 f xs ys) = f (EL n xs) (EL n ys)`,
  Induct \\ rw []
  \\ Cases_on `ys` \\ Cases_on `n` \\ fs []);

val try_update_LENGTH = Q.store_thm ("try_update_LENGTH",
  `LENGTH (try_update ty idx ts) = LENGTH ts`,
  Cases_on `idx` \\ fs [try_update_def]
  \\ PURE_CASE_TAC \\ fs []);

(* TODO surely there is a less contrived way to do this *)
val try_update_mono = Q.store_thm ("try_update_mono",
  `∀ts n idx.
     n < LENGTH ts ∧
     EL n ts = Int ⇒
       EL n (try_update Int idx ts) = Int`,
  Induct \\ rw []
  \\ Cases_on `idx` \\ rw [try_update_def]
  \\ Cases_on `x < n` \\ fs []
  \\ Cases_on `n`
  \\ fs [EL_APPEND1, EL_APPEND2, ADD1, EL_TAKE, EL_DROP]
  \\ Cases_on `x` \\ fs []
  \\ simp [EL_CONS, prim_recTheory.PRE, GSYM ADD1]
  \\ fs [ADD1]
  \\ Cases_on `n' = n` \\ rw []
  \\ fs [EL_APPEND1, EL_APPEND2, EL_TAKE]);

val scan_aux_LENGTH = Q.store_thm ("scan_aux_LENGTH",
  `∀ts exp.
     LENGTH (scan_aux ts exp) = LENGTH ts`,
  ho_match_mp_tac scan_aux_ind
  \\ rw [scan_aux_def, MAP2_K]
  \\ TRY
   (PURE_TOP_CASE_TAC
   \\ fs [try_update_LENGTH, MAP2_LENGTH])
  \\ qmatch_goalsub_abbrev_tac `FOLDL (λt e. Any::f t e) ts xs`
  \\ `LENGTH (FOLDL (λt e. Any::f t e) ts xs) = LENGTH xs + LENGTH ts`
    suffices_by fs []
  \\ qpat_x_assum `∀x. ∀y. _` mp_tac
  \\ qspec_tac (`ts`,`ts`)
  \\ qspec_tac (`xs`,`xs`)
  \\ Induct \\ rw []);

val scan_aux_mono = Q.store_thm ("scan_aux_mono",
  `∀ts exp n.
     n < LENGTH ts ∧
     EL n ts = Int ⇒
       EL n (scan_aux ts exp) = Int`,
  ho_match_mp_tac scan_aux_ind
  \\ rw [scan_aux_def, MAP2_K, scan_aux_LENGTH, EL_TAKE]
  >-
   (
    qmatch_goalsub_abbrev_tac `scan_aux zs exp`
    \\ `LENGTH (scan_aux zs exp) = LENGTH zs` by fs [scan_aux_LENGTH]
    \\ `LENGTH zs = LENGTH xs + LENGTH ts` by
      (
       qunabbrev_tac `zs`
       \\ qpat_x_assum `∀n. _ ⇒ _` mp_tac
       \\ rpt (pop_assum kall_tac)
       \\ qspec_tac (`ts`,`ts`)
       \\ qspec_tac (`xs`,`xs`)
       \\ Induct \\ rw []
       \\ simp [scan_aux_LENGTH])
    \\ `n + LENGTH xs < LENGTH ts + LENGTH xs` by fs []
    \\ rw [EL_DROP]
    \\ fs [PULL_FORALL]
    \\ cheat (* Wrong induction? *)
   )
  \\ PURE_TOP_CASE_TAC \\ fs [] \\ rw []
  \\ simp [MAP2_EL, try_update_LENGTH]
  \\ PURE_CASE_TAC \\ fs []
  \\ metis_tac [try_update_mono]);

val ty_rel_extend = Q.store_thm ("ty_rel_extend",
  `∀xs env s vs t ts.
     LENGTH vs = LENGTH xs ∧
     ty_rel env ts ⇒
       ty_rel (vs ++ env) (FOLDL (λt e. Any::scan_aux t e) ts xs)`,
  Induct
  \\ rw []
  \\ Cases_on `vs` \\ fs []
  \\ fs [ty_rel_def, LIST_REL_EL_EQN]
  \\ cheat (* TODO *)
  );

val EVERY_no_err_correct = Q.store_thm ("EVERY_no_err_correct",
  `∀xs env (s: 'ffi bviSem$state) r t ts.
     EVERY (no_err ts) xs ∧
     ty_rel env ts ∧
     evaluate (xs, env, s) = (r, t) ⇒
       s = t ∧
       ∃vs.
         r = Rval vs ∧
         LENGTH vs = LENGTH xs ∧
         EVERY (λv. ∃k. v = Number k) vs ∧
       (∀(s': 'ffi bviSem$state). evaluate (xs, env, s') = (r, s')) `,
  recInduct evaluate_ind
  \\ rw [no_err_def]
  \\ pop_assum mp_tac
  \\ simp [evaluate_def]
  >-
    (rpt (PURE_TOP_CASE_TAC \\ fs []) \\ rw []
    \\ res_tac \\ fs []
    \\ metis_tac [EVERY_NOT_EXISTS])
  >-
    (rpt (PURE_TOP_CASE_TAC \\ fs []) \\ rw []
    \\ rpt (PURE_TOP_CASE_TAC \\ fs []) \\ rw []
    \\ res_tac \\ fs []
    \\ TRY (metis_tac [EVERY_NOT_EXISTS])
    \\ `∃v. a = [v]` by (Cases_on `a` \\ fs [])
    \\ fs [])
  >- (PURE_CASE_TAC \\ fs [])
  >-
    (PURE_CASE_TAC \\ fs [] \\ rw []
    \\ fs [ty_rel_def, LIST_REL_EL_EQN])
  \\ TRY
    (Cases_on `op` \\ fs []
    >- (rw [evaluate_def, do_app_def, do_app_aux_def]
       \\ rfs [small_int_def, small_enough_int_def])
    \\ rpt (PURE_TOP_CASE_TAC \\ fs []) \\ rw []
    \\ TRY (metis_tac [EVERY_NOT_EXISTS])
    \\ `∃x y. xs = [x; y]` by
      (Cases_on `xs` \\ fs []
      \\ Cases_on `t` \\ fs [])
    \\ fs []
    \\ imp_res_tac evaluate_IMP_LENGTH
    \\ Cases_on `a` \\ fs []
    \\ Cases_on `t` \\ fs []
    \\ res_tac \\ fs [] \\ rveq
    \\ fs [do_app_def, do_app_aux_def,
           bvlSemTheory.do_app_def, bvl_to_bvi_id])
  \\ rw []);

val no_err_correct = Q.store_thm ("no_err_correct",
  `no_err ts x ∧
   ty_rel env ts ∧
   evaluate ([x], env, (s: 'ffi bviSem$state)) = (r, t) ⇒
     ∃k. r = Rval [Number k] ∧
         ∀(s': 'ffi bviSem$state). evaluate ([x], env, s') = (r, s')`,
  rw []
  \\ drule (Q.SPEC `[x]` EVERY_no_err_correct |> SIMP_RULE (srw_ss()) [])
  \\ rpt (disch_then drule) \\ rw []
  \\ imp_res_tac evaluate_SING_IMP \\ fs []);

val op_id_val_def = Define `
  (op_id_val Plus  = Number 0) ∧
  (op_id_val Times = Number 1) ∧
  (op_id_val Noop  = Number 6333)
  `;

val op_identity_op_id_val = Q.store_thm ("op_identity_op_id_val",
  `∀iop env s.
    iop ≠ Noop ⇒
      evaluate ([id_from_op iop], env, s) =
        (Rval [op_id_val iop], s)`,
   Cases
   \\ rpt gen_tac
   \\ simp [id_from_op_def, op_id_val_def, evaluate_def]
   \\ simp [do_app_def, do_app_aux_def, small_enough_int_def]);

val scan_expr_not_Noop = Q.store_thm ("scan_expr_not_Noop",
  `∀exp ts loc tt r ok op.
     scan_expr ts loc exp = (tt, r, ok, SOME op) ⇒
       op ≠ Noop`,
  Induct
  \\ rw [scan_expr_def]
  \\ rpt (pairarg_tac \\ fs [])
  \\ rpt (PURE_FULL_CASE_TAC \\ fs [])
  \\ fs [from_op_def]
  \\ metis_tac []);

val check_exp_not_Noop = Q.store_thm ("check_exp_not_Noop",
  `∀loc arity exp op.
     check_exp loc arity exp = SOME op ⇒ op ≠ Noop`,
  rw [check_exp_def]
  \\ pairarg_tac \\ fs [] \\ rveq
  \\ imp_res_tac scan_expr_not_Noop);

val evaluate_rewrite_op = Q.store_thm ("evaluate_rewrite_op",
  `∀ts op loc exp env (s: 'ffi bviSem$state) r t p exp2.
     evaluate ([exp], env, s) = (r, t) ∧
     r ≠ Rerr (Rabort Rtype_error) ∧
     ty_rel env ts ∧
     rewrite_op ts op loc exp = (p, exp2) ∧
     evaluate ([exp], env, s) = (r, t) ⇒
       if ¬p then exp2 = exp else
         evaluate ([exp2], env, s) = (r, t)`,
  ho_match_mp_tac rewrite_op_ind \\ rw []
  \\ IF_CASES_TAC \\ rw []
  \\ pop_assum mp_tac
  \\ once_rewrite_tac [rewrite_op_def]
  \\ rpt (PURE_CASE_TAC \\ fs [])
  \\ rpt (pairarg_tac \\ fs [])
  >- rpt (PURE_FULL_CASE_TAC \\ fs [])
  \\ rpt (IF_CASES_TAC \\ fs [])
  \\ rw []
  \\ qpat_x_assum `_ = (r, t)` mp_tac
  \\ Cases_on `r1` \\ Cases_on `r2` \\ fs []
  \\ simp [evaluate_def]
  \\ TRY
   (PURE_CASE_TAC \\ fs [] \\ first_x_assum drule \\ strip_tac
    \\ PURE_CASE_TAC \\ fs [] \\ first_x_assum drule \\ strip_tac
    \\ rename1 `_ ([e1],_,_) = (r1,_)`
    \\ rename1 `_ ([e2],_,_) = (r2,_)`
    \\ Cases_on `r1 = Rerr (Rabort Rtype_error)` \\ rfs []
    \\ Cases_on `r2 = Rerr (Rabort Rtype_error)` \\ fs []
    >-
     (PURE_CASE_TAC \\ fs [] \\ rw []
      \\ simp [assoc_swap_def, apply_op_def]
      \\ IF_CASES_TAC
      \\ simp [evaluate_def]
      \\ rpt (PURE_CASE_TAC \\ fs [])
      \\ rw [evaluate_def]
      \\ fs [op_eq_to_op] \\ rveq
      \\ qpat_x_assum `_ = (Rerr e, _)` mp_tac
      \\ simp [evaluate_def]
      \\ rpt (PURE_FULL_CASE_TAC \\ fs [])
      \\ imp_res_tac evaluate_SING_IMP \\ rw [] \\ fs []
      \\ imp_res_tac do_app_err \\ fs []
      \\ imp_res_tac no_err_correct \\ fs [])
    \\ drule (GEN_ALL no_err_correct)
    \\ rpt (disch_then drule)
    \\ strip_tac \\ fs [] \\ rveq
    \\ simp [assoc_swap_def, apply_op_def]
    \\ IF_CASES_TAC \\ simp [evaluate_def]
    \\ rpt (PURE_FULL_CASE_TAC \\ fs [])
    \\ rw [evaluate_def]
    \\ fs [evaluate_def]
    \\ rpt (PURE_FULL_CASE_TAC \\ fs []) \\ rw []
    \\ imp_res_tac evaluate_SING_IMP \\ rw [] \\ fs []
    \\ Cases_on `op` \\ fs [to_op_def]
    \\ fs [do_app_def, do_app_aux_def, bvlSemTheory.do_app_def, bvl_to_bvi_id]
    \\ rpt (PURE_FULL_CASE_TAC \\ fs [])
    \\ fs [bvl_to_bvi_id] \\ rw []
    \\ intLib.COOPER_TAC));

val rewrite_op_preserves_op = Q.store_thm ("rewrite_op_preserves_op",
  `∀ts op loc op1 xs exp.
     rewrite_op ts op loc (Op op1 xs) = (T, exp) ⇒
       ∃x y. exp = Op op1 [x; y]`,
  rpt gen_tac
  \\ once_rewrite_tac [rewrite_op_def]
  \\ Cases_on `op1` \\ Cases_on `op` \\ fs [op_eq_def]
  \\ rpt (PURE_TOP_CASE_TAC \\ fs [])
  \\ rpt (pairarg_tac \\ fs [])
  \\ rpt (PURE_FULL_CASE_TAC \\ fs [])
  \\ fs [assoc_swap_def, apply_op_def, to_op_def]
  \\ rpt (PURE_FULL_CASE_TAC \\ fs []) \\ rw []);

val rewrite_op_no_err = Q.store_thm ("rewrite_op_no_err",
  `∀ts op loc exp p exp2 x y.
      rewrite_op ts op loc exp = (p, exp2) ⇒
        if p then (get_bin_args exp2 = SOME (x, y) ⇒ no_err ts y)
        else exp = exp2`,
  ho_match_mp_tac rewrite_op_ind
  \\ rpt strip_tac
  \\ pop_assum mp_tac
  \\ once_rewrite_tac [rewrite_op_def]
  \\ PURE_CASE_TAC \\ fs [] \\ rveq
  \\ rpt (pairarg_tac \\ fs [])
  \\ rpt (IF_CASES_TAC \\ fs [])
  \\ rw [assoc_swap_def, apply_op_def]
  \\ rpt (PURE_FULL_CASE_TAC \\ fs [] \\ rw [])
  \\ fs [is_rec_or_rec_binop_def, no_err_def, is_rec_def]
  \\ Cases_on `op` \\ fs [to_op_def, get_bin_args_def]);

val rewrite_op_noopt = Q.prove (
  `rewrite_op ts op loc exp  = (F, exp2) ⇒ exp = exp2`,
  once_rewrite_tac [rewrite_op_def]
  \\ rpt (PURE_CASE_TAC \\ fs [])
  \\ rpt (pairarg_tac \\ fs [])
  \\ rpt (PURE_CASE_TAC \\ fs []));

val check_exp_IMP_to_op = Q.store_thm ("check_exp_IMP_to_op",
  `check_exp loc arity (Op op xs) = SOME iop ⇒
     op = to_op iop`,
  rw [check_exp_def]
  \\ pairarg_tac \\ fs [] \\ rw []
  \\ Cases_on `op` \\ Cases_on `iop`
  \\ fs [to_op_def, scan_expr_def, from_op_def]);

val rewrite_op_binargs = Q.store_thm ("rewrite_op_binargs",
  `rewrite_op ts op loc (Op op1 xs) = (T, exp) ⇒
     ∃x y. get_bin_args exp = SOME (x, y)`,
  Cases_on `op`
  \\ once_rewrite_tac [rewrite_op_def]
  \\ simp [op_eq_def, assoc_swap_def, apply_op_def, to_op_def]
  \\ rpt (PURE_CASE_TAC \\ fs [])
  \\ rpt (pairarg_tac \\ fs [])
  \\ rpt (PURE_CASE_TAC \\ fs [])
  \\ rw []);

val rewrite_op_is_rec = Q.store_thm ("rewrite_op_is_rec",
  `op ≠ Noop ∧
   rewrite_op ts op loc (Op op1 xs) = (T, Op op1 [x; y]) ⇒
     is_rec loc x`,
  Cases_on `op`
  \\ once_rewrite_tac [rewrite_op_def]
  \\ simp [op_eq_def]
  \\ rpt (PURE_CASE_TAC \\ fs [])
  \\ rpt (pairarg_tac \\ fs [])
  \\ rpt (PURE_CASE_TAC \\ fs [])
  \\ rw [assoc_swap_def, apply_op_def]
  \\ fs [is_rec_or_rec_binop_def] \\ rw []
  \\ rpt (PURE_FULL_CASE_TAC \\ fs []) \\ rw []
  \\ fs [is_rec_def, no_err_def]);

(* TODO for append, parametrise on op *)
val env_rel_def = Define `
  env_rel opt acc env1 env2 ⇔
    isPREFIX env1 env2 ∧
    (opt ⇒
      LENGTH env1 = acc ∧
      LENGTH env2 > acc ∧
      ∃k. EL acc env2 = Number k)`;

val evaluate_env_extra = Q.store_thm ("evaluate_env_extra",
  `∀xs env s r t extra.
     evaluate (xs, env, s) = (r, t) ∧
     r ≠ Rerr (Rabort Rtype_error) ⇒
       evaluate (xs, env ++ extra, s) = (r, t)`,
  recInduct evaluate_ind \\ rw []
  \\ qpat_x_assum `evaluate _ = _` mp_tac
  \\ simp [evaluate_def]
  \\ rpt (PURE_TOP_CASE_TAC \\ fs []) \\ rw []
  \\ res_tac
  \\ fs [EL_APPEND1]
  \\ CCONTR_TAC \\ fs []
  \\ rveq \\ fs []
  \\ rfs []);

val code_rel_def = Define `
  code_rel c1 c2 ⇔
    ∀loc arity exp op.
      lookup loc c1 = SOME (arity, exp) ⇒
      (check_exp loc arity exp = NONE ⇒
        lookup loc c2 = SOME (arity, exp)) ∧
      (check_exp loc arity exp = SOME op ⇒
        ∃n. ∀exp_aux exp_opt.
        compile_exp loc n arity exp = SOME (exp_aux, exp_opt) ⇒
          lookup loc c2 = SOME (arity, exp_aux) ∧
          lookup n c2 = SOME (arity + 1, exp_opt))`;

val code_rel_find_code_SOME = Q.prove (
  `∀c1 c2 x (args: v list) exp.
     code_rel c1 c2 ∧
     find_code (SOME n) args c1 = SOME (args, exp) ⇒
       find_code (SOME n) args c2 ≠ NONE`,
  rw []
  \\ pop_assum mp_tac
  \\ simp [find_code_def]
  \\ rpt (PURE_TOP_CASE_TAC \\ fs [])
  \\ fs [code_rel_def]
  \\ first_x_assum drule
  \\ Cases_on `check_exp n q r`
  \\ rw [compile_exp_def]
  \\ pairarg_tac \\ fs []);

val code_rel_find_code_NONE = Q.prove (
  `∀c1 c2 x (args: v list) exp.
     code_rel c1 c2 ∧
     find_code NONE args c1 = SOME (FRONT args, exp) ⇒
       find_code NONE args c2 ≠ NONE`,
  rw []
  \\ pop_assum mp_tac
  \\ simp [find_code_def]
  \\ rpt (PURE_TOP_CASE_TAC \\ fs [])
  \\ fs [code_rel_def]
  \\ first_x_assum drule
  \\ Cases_on `check_exp n q r`
  \\ rw [compile_exp_def]
  \\ pairarg_tac \\ fs []);

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
  \\ CCONTR_TAC \\ fs []
  \\ Cases_on `lookup x c1`
  >- fs [lookup_NONE_domain]
  \\ fs [GSYM lookup_NONE_domain]
  \\ rename1 `SOME z`
  \\ PairCases_on `z`
  \\ first_x_assum drule
  \\ Cases_on `check_exp x z0 z1`
  \\ rw [compile_exp_def]
  \\ pairarg_tac \\ fs []);

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
  `!skip env n (st:'ffi bviSem$state).
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
  `∀x op vs (s:'ffi bviSem$state) r t.
     op ≠ Noop ⇒
     evaluate ([let_wrap (LENGTH vs) (id_from_op op) x], vs, s) =
     evaluate ([x], vs ++ [op_id_val op] ++ vs, s)`,
  rpt gen_tac
  \\ `LENGTH vs + 0 ≤ LENGTH vs` by fs []
  \\ drule evaluate_genlist_vars
  \\ disch_then (qspec_then `s` assume_tac)
  \\ simp [let_wrap_def, evaluate_def]
  \\ once_rewrite_tac [evaluate_APPEND] \\ fs []
  \\ simp [op_identity_op_id_val]
  \\ rw []);

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

val rewrite_op_IMP_op_eq = Q.prove (
  `∀ts op loc exp p exp2.
     rewrite_op ts op loc exp = (p, exp2) ∧
     op_eq op exp ⇒
       op_eq op exp2`,
  ho_match_mp_tac rewrite_op_ind \\ rw []
  \\ qpat_x_assum `rewrite_op _ _ _ _ = _` mp_tac
  \\ once_rewrite_tac [rewrite_op_def]
  \\ rpt (PURE_CASE_TAC \\ fs [])
  \\ rpt (pairarg_tac \\ fs [])
  \\ TRY (rw [] \\ fs [] \\ NO_TAC)
  \\ rpt (PURE_CASE_TAC \\ fs [])
  \\ TRY (rw [] \\ fs [] \\ NO_TAC)
  \\ rw [assoc_swap_def, apply_op_def] \\ fs []
  \\ PURE_FULL_CASE_TAC \\ fs []);

val rewrite_op_exp_size = Q.store_thm ("rewrite_op_exp_size",
  `∀ts op loc exp p exp2.
    rewrite_op ts op loc exp = (p, exp2) ⇒
      exp_size exp = exp_size exp2`,
  ho_match_mp_tac rewrite_op_ind
  \\ rw []
  \\ pop_assum mp_tac
  \\ once_rewrite_tac [rewrite_op_def]
  \\ rpt (PURE_CASE_TAC \\ fs [])
  \\ rpt (pairarg_tac \\ fs [])
  \\ rpt (PURE_CASE_TAC \\ fs [])
  \\ rw [assoc_swap_def]
  \\ fs [apply_op_def, bviTheory.exp_size_def]
  \\ PURE_CASE_TAC \\ fs [op_eq_to_op, bviTheory.exp_size_def]
  \\ rw [] \\ fs []);

val optimized_code_def = Define `
  optimized_code loc arity exp n c op =
    ∃exp_aux exp_opt.
        compile_exp loc n arity exp = SOME (exp_aux, exp_opt) ∧
        check_exp loc arity exp     = SOME op ∧
        lookup loc c                = SOME (arity, exp_aux) ∧
        lookup n c                  = SOME (arity + 1, exp_opt)`;

val env_rel_extra = Q.prove (
  `∀env1 env2 acc.
     env_rel F acc env1 env2 ⇒
       ∃extra. env1 ++ extra = env2`,
  rw [env_rel_def]
  \\ fs [IS_PREFIX_APPEND]);

val evaluate_env_rel_err = Q.prove (
  `∀xs env1 (s:'ffi bviSem$state) vs t acc env2.
     evaluate (xs, env1, s) = (Rval vs, t) ∧
     env_rel F acc env1 env2 ⇒
       evaluate (xs, env2, s) = (Rval vs, t)`,
  rpt strip_tac
  \\ imp_res_tac env_rel_extra \\ rveq
  \\ imp_res_tac evaluate_env_extra \\ fs []);

(* TODO:

   For non-arithmetic operations, (∃op' check_exp ... ⇒ ...) will have
   to include some op_rel op op' which says that op and op' operate on
   the same type. *)
val evaluate_rewrite_tail = Q.store_thm ("evaluate_rewrite_tail",
  `∀xs (s:'ffi bviSem$state) env1 r t opt c acc env2 loc ts.
     evaluate (xs, env1, s) = (r, t) ∧
     env_rel opt acc env1 env2 ∧
     code_rel s.code c ∧
     ty_rel env1 ts ∧
     (opt ⇒ LENGTH xs = 1) ∧
     r ≠ Rerr (Rabort Rtype_error) ⇒
       evaluate (xs, env2, s with code := c) = (r, t with code := c) ∧
       (opt ⇒
         ∀op n exp arity.
           lookup loc s.code = SOME (arity, exp) ∧
           optimized_code loc arity exp n c op ∧
           (∃op'. ∀tt r ok.
             scan_expr ts loc (HD xs) = (tt, r, ok, SOME op') ∧
             op' ≠ Noop ∧ ok) ⇒
               let (tu, lr, x) = rewrite (loc, n, op, acc, ts) (HD xs) in
                 evaluate ([x], env2, s with code := c) =
                 evaluate ([apply_op op (HD xs) (Var acc)],
                   env2, s with code := c))`,

  ho_match_mp_tac evaluate_complete_ind
  \\ ntac 2 (rpt gen_tac \\ strip_tac)
  \\ Cases_on `xs` \\ fs []
  >- fs [evaluate_def]
  \\ reverse (Cases_on `t'`)
  >-
   (rfs []
    \\ qhdtm_x_assum `evaluate` mp_tac
    \\ simp [evaluate_def]
    \\ PURE_TOP_CASE_TAC \\ fs []
    \\ reverse PURE_TOP_CASE_TAC \\ fs []
    >-
     (rw []
      \\ first_assum (qspecl_then [`[h]`,`s`] mp_tac)
      \\ simp [bviTheory.exp_size_def]
      \\ rpt (disch_then drule) \\ fs [])
    \\ qmatch_goalsub_rename_tac `evaluate (y::ys, env1, s2)`
    \\ first_assum (qspecl_then [`[h]`,`s`] mp_tac)
    \\ simp [bviTheory.exp_size_def]
    \\ rpt (disch_then drule) \\ fs []
    \\ strip_tac
    \\ ntac 2 PURE_TOP_CASE_TAC \\ fs [] \\ rveq
    \\ PURE_TOP_CASE_TAC \\ fs [] \\ rw []
    \\ first_assum (qspecl_then [`y::ys`,`s2`] mp_tac)
    \\ imp_res_tac evaluate_clock
    \\ imp_res_tac evaluate_code_const
    \\ simp [bviTheory.exp_size_def]
    \\ rpt (disch_then drule) \\ fs [])
  \\ fs [bviTheory.exp_size_def]
  \\ Cases_on `∃v. h = Var v` \\ fs [] \\ rveq
  >-
   (qhdtm_x_assum `evaluate` mp_tac \\ simp [evaluate_def]
    \\ IF_CASES_TAC \\ fs []
    \\ strip_tac \\ fs [] \\ rveq
    \\ reverse IF_CASES_TAC
    >-
     (fs [env_rel_def]
      \\ `LENGTH env1 ≤ LENGTH env2` by fs [IS_PREFIX_LENGTH]
      \\ fs [])
    \\ conj_tac
    >- (fs [env_rel_def] \\ imp_res_tac is_prefix_el \\ fs [])
    \\ rw []
    \\ pairarg_tac \\ fs [] \\ rveq
    \\ pop_assum mp_tac
    \\ simp [rewrite_def]
    \\ once_rewrite_tac [rewrite_op_def]
    \\ simp [op_eq_def])
  \\ Cases_on `∃x1. h = Tick x1` \\ fs [] \\ rveq
  >-
   (qhdtm_x_assum `evaluate` mp_tac \\ simp [evaluate_def]
    \\ IF_CASES_TAC \\ fs []
    \\ strip_tac \\ rveq \\ fs []
    >-
     (rw []
      \\ pairarg_tac \\ fs [])
      (*\\ pop_assum mp_tac*)
      (*\\ simp [rewrite_def]*)
      (*\\ once_rewrite_tac [rewrite_op_def]*)
      (*\\ simp [op_eq_def])*)
    \\ first_x_assum (qspecl_then [`[x1]`, `dec_clock 1 s`] mp_tac)
    \\ `(dec_clock 1 s).clock < s.clock` by fs [dec_clock_def]
    \\ simp [bviTheory.exp_size_def]
    \\ rpt (disch_then drule)
    \\ disch_then (qspec_then `loc` mp_tac) \\ rw []
    \\ pairarg_tac \\ fs [])
    (*\\ first_x_assum drule*)
    (*\\ impl_tac*)
    (*>-*)
     (*(rfs [scan_expr_def]*)
      (*\\ asm_exists_tac \\ fs [])*)
    (*\\ pairarg_tac \\ fs []*)
    (*\\ rw []*)
    (*\\ rpt (qhdtm_x_assum `rewrite` mp_tac)*)
    (*\\ simp [rewrite_def]*)
    (*\\ once_rewrite_tac [rewrite_op_def]*)
    (*\\ simp [op_eq_def])*)
  \\ Cases_on `∃x1. h = Raise x1` \\ fs [] \\ rveq
  >-
   (simp [scan_expr_def]
    \\ qpat_x_assum `evaluate _ = _` mp_tac
    \\ simp [evaluate_def]
    \\ PURE_TOP_CASE_TAC \\ fs []
    \\ strip_tac
    \\ `env_rel F acc env1 env2` by fs [env_rel_def]
    \\ first_x_assum (qspecl_then [`[x1]`,`s`] mp_tac)
    \\ simp [bviTheory.exp_size_def]
    \\ rpt (disch_then drule) \\ fs []
    \\ rpt (PURE_FULL_CASE_TAC \\ fs []) \\ rw [] \\ fs [])
  \\ Cases_on `∃xs x1. h = Let xs x1` \\ fs [] \\ rveq
  >-
   (qpat_x_assum `evaluate _ = _` mp_tac
    \\ simp [evaluate_def]
    \\ `env_rel F acc env1 env2` by fs [env_rel_def]
    \\ PURE_TOP_CASE_TAC \\ fs []
    \\ reverse PURE_TOP_CASE_TAC \\ fs []
    \\ strip_tac
    >-
     (rveq \\ fs []
      \\ first_assum (qspecl_then [`xs`,`s`] mp_tac)
      \\ simp [bviTheory.exp_size_def]
      \\ rpt (disch_then drule) \\ fs [] \\ rw []
      \\ pairarg_tac \\ fs [])
      (*\\ fs [rewrite_def, scan_expr_def]*)
      (*\\ pairarg_tac \\ fs []*)
      (*\\ rw [evaluate_def, apply_op_def])*)
    \\ first_assum (qspecl_then [`xs`,`s`] mp_tac)
    \\ simp [bviTheory.exp_size_def]
    \\ rpt (disch_then drule) \\ fs []
    \\ strip_tac
    \\ imp_res_tac evaluate_clock
    \\ imp_res_tac evaluate_code_const
    \\ `env_rel opt (acc+LENGTH a) (a++env1) (a++env2)` by
      (Cases_on `opt`
      \\ fs [env_rel_def, IS_PREFIX_LENGTH]
      \\ fs [EL_APPEND2])
    \\ rename1 `evaluate (xs,env,s) = (Rval a, s2)`
    \\ `ty_rel (a ++ env) (FOLDL (λt e. Any::scan_aux t e) ts xs)` by
      metis_tac [ty_rel_extend, evaluate_IMP_LENGTH]
    \\ first_x_assum (qspecl_then [`[x1]`,`s2`] mp_tac)
    \\ simp [bviTheory.exp_size_def]
    \\ rpt (disch_then drule)
    \\ disch_then (qspec_then `loc` mp_tac) \\ rw []
    \\ pairarg_tac \\ fs [])
    (*\\ first_x_assum drule*)
    (*\\ impl_tac*)
    (*>-*)
     (*(fs [scan_expr_def]*)
      (*\\ pairarg_tac \\ fs [])*)
    (*\\ fs [scan_expr_def]*)
    (*\\ rpt (pairarg_tac \\ fs []))*)
  \\ Cases_on `∃x1 x2 x3. h = If x1 x2 x3` \\ fs [] \\ rveq
  >-
   (
    qpat_x_assum `evaluate _ = _` mp_tac
    \\ simp [evaluate_def]
    \\ `env_rel F acc env1 env2` by fs [env_rel_def]
    \\ PURE_TOP_CASE_TAC \\ fs []
    \\ reverse PURE_TOP_CASE_TAC \\ fs []
    >-
      (strip_tac \\ rveq \\ fs []
      \\ first_assum (qspecl_then [`[x1]`,`s`] mp_tac)
      \\ simp [bviTheory.exp_size_def]
      \\ rpt (disch_then drule) \\ fs [] \\ rw []
      \\ pairarg_tac \\ fs [])
      (*\\ fs [rewrite_def]*)
      (*\\ pairarg_tac \\ fs []*)
      (*\\ rw [evaluate_def, apply_op_def])*)
    \\ first_assum (qspecl_then [`[x1]`,`s`] mp_tac)
    \\ simp [bviTheory.exp_size_def]
    \\ rpt (disch_then drule) \\ fs []
    \\ strip_tac
    \\ reverse (Cases_on `opt`) \\ fs []
    \\ rename1 `evaluate ([x1],_,s) = (_,s2)`
    >-
     (IF_CASES_TAC \\ fs []
      >-
       (strip_tac
        \\ first_assum (qspecl_then [`[x2]`,`s2`] mp_tac)
        \\ imp_res_tac evaluate_clock
        \\ imp_res_tac evaluate_code_const
        \\ simp [bviTheory.exp_size_def]
        \\ rpt (disch_then drule) \\ fs [])
      \\ IF_CASES_TAC \\ fs []
      \\ strip_tac
      \\ first_assum (qspecl_then [`[x3]`,`s2`] mp_tac)
      \\ imp_res_tac evaluate_clock
      \\ imp_res_tac evaluate_code_const
      \\ simp [bviTheory.exp_size_def]
      \\ rpt (disch_then drule) \\ fs [])
    \\ strip_tac
    \\ conj_tac
    >-
     (IF_CASES_TAC \\ fs []
      >-
       (first_x_assum (qspecl_then [`[x2]`,`s2`] mp_tac)
        \\ imp_res_tac evaluate_clock \\ fs []
        \\ imp_res_tac evaluate_code_const \\ fs []
        \\ simp [bviTheory.exp_size_def]
        \\ rpt (disch_then drule) \\ fs [])
      \\ IF_CASES_TAC \\ fs []
      \\ first_x_assum (qspecl_then [`[x3]`,`s2`] mp_tac)
      \\ imp_res_tac evaluate_clock \\ fs []
      \\ imp_res_tac evaluate_code_const \\ fs []
      \\ simp [bviTheory.exp_size_def]
      \\ rpt (disch_then drule) \\ fs [])
    \\ rw []
    \\ fs [rewrite_def, evaluate_def, scan_expr_def])
  \\ Cases_on `∃xs op. h = Op op xs` \\ fs [] \\ rveq
  >-
    (conj_tac
    >-
     (qhdtm_x_assum `evaluate` mp_tac \\ simp [evaluate_def]
      \\ PURE_TOP_CASE_TAC \\ fs []
      \\ strip_tac
      \\ `env_rel F acc env1 env2` by fs [env_rel_def]
      \\ first_x_assum (qspecl_then [`xs`,`s`] assume_tac)
      \\ fs [bviTheory.exp_size_def]
      \\ first_x_assum drule
      \\ rpt (disch_then drule) \\ fs []
      \\ impl_tac
      >- (PURE_FULL_CASE_TAC \\ fs [] \\ rw [])
      \\ strip_tac \\ fs []
      \\ rpt (PURE_FULL_CASE_TAC \\ fs [])
      \\ imp_res_tac code_rel_domain
      \\ imp_res_tac evaluate_code_const \\ fs []
      \\ imp_res_tac do_app_with_code_err
      \\ imp_res_tac do_app_with_code
      \\ imp_res_tac do_app_err \\ fs [] \\ rw []
      \\ res_tac \\ rfs [])
    \\ rw []
    \\ fs [rewrite_def])
    \\ rpt (pairarg_tac \\ fs [])
  \\ Cases_on `∃ticks dest xs hdl. h = Call ticks dest xs hdl` \\ fs [] \\ rveq
  >-
   (cheat (* TODO *)
   )
  \\ Cases_on `h` \\ fs []);

  \\ Cases_on `∃ticks dest xs hdl. h = Call ticks dest xs hdl` \\ fs [] \\ rveq
  >-
    (simp [check_exp_def, tail_is_ok_def]
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
        \\ reverse TOP_CASE_TAC \\ fs []
        >- CASE_TAC
        \\ imp_res_tac evaluate_code_const \\ fs []
        \\ `q = FRONT a` by
          (fs [find_code_def]
          \\ every_case_tac \\ fs [] \\ rveq \\ fs [])
        \\ rveq
        \\ imp_res_tac code_rel_find_code_NONE)
      \\ rename1 `evaluate ([exp],q,dec_clock (ticks+1) s2)`
      \\ TOP_CASE_TAC
      \\ strip_tac
      \\ first_assum
        (qspecl_then [`[exp]`,`dec_clock (ticks+1) s2`] assume_tac)
      \\ `(dec_clock (ticks+1) s2).clock < s.clock` by
        (fs [dec_clock_def]
        \\ imp_res_tac evaluate_clock \\ fs [])
      \\ fs []
      \\ Cases_on `check_exp nm exp` \\ fs []
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
          (`q = FRONT a` by
            (fs [find_code_def]
            \\ every_case_tac \\ fs [] \\ rveq \\ fs [])
          \\ rveq
          \\ imp_res_tac code_rel_find_code_NONE)
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
        \\ Cases_on `check_exp n exp` \\ fs []
        >-
          (strip_tac \\ rveq
          \\ every_case_tac \\ fs [] \\ rveq \\ fs [])
        \\ simp [compile_exp_def]
        \\ CASE_TAC
        \\ strip_tac \\ rveq
        \\ pairarg_tac \\ fs [] \\ rveq
        \\ simp [evaluate_def]
        \\ imp_res_tac check_exp_Arith
        \\ fs [op_identity_op_id_val]
        \\ `q = LENGTH (FRONT a)` by (Cases_on `a` \\ fs [])
        \\ simp [evaluate_let_wrap]
        \\ qmatch_goalsub_abbrev_tac `zs ++ [_] ++ zs`
        \\ first_x_assum
          (qspecl_then [`[exp]`,`dec_clock (ticks+1) s2`] assume_tac)
        \\ rfs []
        \\ rename1 `check_exp n exp = SOME (_, opr)`
        \\ `env_rel T (LENGTH zs) zs (zs ++ [op_id_val opr] ++ zs)` by
          (simp [env_rel_def, IS_PREFIX_APPEND, EL_APPEND1, EL_LENGTH_APPEND]
          \\ Cases_on `opr` \\ fs [op_id_val_def])
        \\ imp_res_tac evaluate_code_const \\ fs []
        \\ first_x_assum drule
        \\ disch_then (qspec_then `T` drule)
        \\ disch_then drule
        \\ disch_then (qspec_then `n` mp_tac)
        \\ impl_tac
        >- (every_case_tac \\ fs [] \\ rveq \\ fs [])
        \\ fs []
        \\ strip_tac
        \\ first_x_assum (qspecl_then [`opr`,`n'`] assume_tac)
        \\ pairarg_tac \\ fs []
        \\ rveq
        \\ rename1 `rewrite_tail m opr n _ exp`
        \\ rfs [optimized_code_def, compile_exp_def]
        \\ pairarg_tac \\ fs [] \\ rveq
        \\ simp [apply_op_def, evaluate_def, EL_APPEND1, EL_LENGTH_APPEND]
        \\ rename1 `evaluate _ = (_, s3 with code := c)`
        \\ reverse CASE_TAC \\ fs []
        >- (every_case_tac \\ fs [] \\ rveq \\ fs [])
        \\ fs [check_exp_def]
        \\ imp_res_tac is_ok_type_IMP_Number \\ fs [] \\ rveq
        \\ Cases_on `opr` \\ fs [op_id_val_def, to_op_def]
        \\ fs [do_app_def, do_app_aux_def, bvlSemTheory.do_app_def]
        \\ fs [bvl_to_bvi_id])
      \\ Cases_on `x`
      \\ imp_res_tac check_exp_Arith
      \\ rename1 `check_exp nm exp = SOME (_, opr)`
      \\ simp [evaluate_def]
      \\ TOP_CASE_TAC \\ fs []
      >-
        (`q = FRONT a` by
          (fs [find_code_def]
          \\ every_case_tac \\ fs [] \\ rveq \\ fs [])
        \\ rveq
        \\ imp_res_tac evaluate_code_const \\ fs []
        \\ imp_res_tac code_rel_find_code_NONE)
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
      \\ Cases_on `check_exp n exp` \\ fs []
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
      \\ Cases_on `x`
      \\ rename1 `check_exp n exp = SOME (_, opr2)`
      \\ imp_res_tac check_exp_Arith
      \\ simp [compile_exp_def]
      \\ strip_tac \\ rveq
      \\ pairarg_tac \\ fs [] \\ rveq
      (*\\ simp [evaluate_def]*)
      \\ `q = LENGTH (FRONT a)` by (Cases_on `a` \\ fs [FRONT_DEF])
      \\ simp [evaluate_let_wrap]
      \\ first_x_assum
        (qspecl_then [`[exp]`,`dec_clock (ticks+1) s2`] assume_tac)
      \\ rfs []
      \\ rename1 `rewrite_tail m x1 n _ exp`
      \\ `env_rel T (LENGTH (FRONT a))
                    (FRONT a)
                    (FRONT a ++ [op_id_val x1] ++ FRONT a)` by
        (simp [env_rel_def, IS_PREFIX_APPEND, EL_LENGTH_APPEND, EL_APPEND1]
        \\ Cases_on `x1` \\ simp [op_id_val_def])
      \\ first_x_assum drule
      \\ disch_then (qspec_then `T` drule)
      \\ disch_then drule \\ fs []
      \\ disch_then (qspec_then `n` mp_tac)
      \\ impl_tac
      >- (every_case_tac \\ fs [] \\ rveq \\ fs [])
      \\ strip_tac
      \\ first_x_assum drule
      \\ fs [optimized_code_def, compile_exp_def]
      \\ disch_then (qspecl_then [`x1`,`m`] mp_tac) \\ simp []
      \\ strip_tac
      \\ simp [apply_op_def, evaluate_def]
      \\ reverse CASE_TAC \\ fs []
      >- (every_case_tac \\ fs [] \\ rveq \\ fs [])
      \\ simp [EL_LENGTH_APPEND, EL_APPEND1]
      \\ fs [check_exp_def]
      \\ imp_res_tac is_ok_type_IMP_Number \\ fs [] \\ rveq
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
    \\ `a = q` by (fs [find_code_def] \\ every_case_tac \\ fs []) \\ rveq
    \\ IF_CASES_TAC
    >-
      (strip_tac \\ fs [] \\ rveq
      \\ first_x_assum drule
      \\ disch_then (qspec_then `F` mp_tac) \\ fs []
      \\ ntac 2 (disch_then drule)
      \\ imp_res_tac code_rel_find_code_SOME
      \\ strip_tac
      \\ simp [evaluate_def]
      \\ imp_res_tac evaluate_code_const \\ fs []
      \\ TOP_CASE_TAC >- rfs []
      \\ TOP_CASE_TAC)
    \\ imp_res_tac evaluate_code_const \\ fs []
    \\ qmatch_assum_rename_tac `_ = SOME (args, exp)`
    \\ qmatch_assum_rename_tac `evaluate (_,_,s1) = (_, s2)`
    \\ first_x_assum drule
    \\ disch_then (qspec_then `F` drule) \\ fs []
    \\ disch_then drule
    \\ strip_tac
    \\ TOP_CASE_TAC
    \\ strip_tac \\ fs [] \\ rveq
    \\ qhdtm_assum `code_rel` mp_tac
    \\ SIMP_TAC std_ss [code_rel_def] \\ fs []
    \\ qhdtm_x_assum `find_code` mp_tac
    \\ simp [find_code_def]
    \\ ntac 2 TOP_CASE_TAC \\ fs []
    \\ strip_tac \\ rveq
    \\ disch_then drule
    \\ Cases_on `check_exp x exp` \\ fs [] \\ strip_tac
    >-
      (simp [evaluate_def, find_code_def]
      \\ first_assum
        (qspecl_then [`[exp]`,`dec_clock (ticks+1) s2`] mp_tac)
      \\ `(dec_clock (ticks+1) s2).clock < s1.clock` by
        (simp [dec_clock_def]
        \\ imp_res_tac evaluate_clock \\ fs [])
      \\ fs []
      \\ pop_assum kall_tac
      \\ `env_rel F acc args args` by fs [env_rel_def]
      \\ imp_res_tac evaluate_code_const \\ fs []
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
      \\ fs [])
    \\ Cases_on `compile_exp n x (LENGTH args) exp`
    >-
      (rfs [compile_exp_def]
      \\ Cases_on `x'` \\ fs []
      \\ pairarg_tac \\ fs [])
    \\ fs []
    \\ qmatch_assum_rename_tac `_ = SOME exp_`
    \\ PairCases_on `exp_` \\ fs []
    \\ Cases_on `x'`
    \\ imp_res_tac check_exp_Arith \\ rveq
    \\ rename1 `iop ≠ Noop`
    \\ simp [evaluate_def, find_code_def]
    \\ rfs [compile_exp_def] \\ rveq
    \\ pairarg_tac \\ fs [] \\ rveq
    \\ simp [evaluate_let_wrap]
    \\ first_assum (qspecl_then [`[exp]`, `dec_clock (ticks+1) s2`] mp_tac)
    \\ `(dec_clock (ticks+1) s2).clock < s1.clock` by
      (fs [dec_clock_def]
      \\ imp_res_tac evaluate_clock \\ fs [])
    \\ simp []
    \\ `env_rel T (LENGTH args) args (args ++ [op_id_val iop] ++ args)` by
      (simp [env_rel_def, IS_PREFIX_APPEND, EL_APPEND1, EL_LENGTH_APPEND]
      \\ Cases_on `iop` \\ simp [op_id_val_def])
    \\ disch_then drule
    \\ disch_then (qspec_then `T` drule)
    \\ disch_then drule
    \\ disch_then (qspec_then `x` mp_tac)
    \\ impl_tac
    >- (every_case_tac \\ fs [] \\ rveq \\ fs [])
    \\ simp []
    \\ strip_tac
    \\ first_x_assum (qspecl_then [`iop`,`n`] mp_tac)
    \\ pairarg_tac \\ fs [] \\ rveq
    \\ simp [optimized_code_def, compile_exp_def]
    \\ strip_tac
    \\ simp [apply_op_def, evaluate_def, EL_LENGTH_APPEND, EL_APPEND1]
    \\ `is_ok_type exp` by fs [check_exp_def]
    \\ imp_res_tac is_ok_type_IMP_Number \\ rfs []
    \\ rename1 `evaluate ([exp], _, _) = (_, st_exp with code := c)`
    \\ reverse CASE_TAC \\ fs []
    >-
      (every_case_tac \\ fs [] \\ rveq \\ fs []
      \\ rename1 `evaluate ([exc], throw::env1, st_exp) = (r, t)`
      \\ first_x_assum (qspecl_then [`[exc]`,`st_exp`] mp_tac)
      \\ `st_exp.clock < s1.clock` by
        (imp_res_tac evaluate_clock
        \\ fs [dec_clock_def])
      \\ simp []
      \\ imp_res_tac evaluate_code_const \\ fs []
      \\ `env_rel F acc (throw::env1) (throw::env2)` by fs [env_rel_def]
      \\ disch_then drule
      \\ disch_then (qspec_then `F` drule) \\ fs [])
    \\ first_x_assum drule
    \\ strip_tac \\ rveq \\ fs []
    \\ Cases_on `iop` \\ fs [to_op_def, op_id_val_def]
    \\ simp [do_app_def, do_app_aux_def, bvlSemTheory.do_app_def]
    \\ fs [bvl_to_bvi_id])
  \\ Cases_on `h` \\ fs []);

val compile_prog_LENGTH = Q.store_thm ("compile_prog_LENGTH",
  `∀n prog. LENGTH (SND (bvi_tailrec$compile_prog n prog)) ≥ LENGTH prog`,
  recInduct compile_prog_ind
  \\ conj_tac
  >- fs [compile_prog_def]
  \\ rw []
  \\ Cases_on `compile_exp loc next arity exp` \\ fs []
  >-
   (fs [compile_prog_def]
    \\ pairarg_tac \\ fs [])
  \\ PairCases_on `x`
  \\ fs [compile_prog_def]
  \\ pairarg_tac \\ fs []);

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

val compile_exp_next_addr = Q.prove (
  `compile_exp loc next args exp = NONE ⇒
     compile_exp loc (next + 2) args exp = NONE`,
  fs [compile_exp_def]
  \\ every_case_tac
  \\ pairarg_tac \\ fs []);

val compile_prog_untouched = Q.store_thm ("compile_prog_untouched",
  `∀next prog prog2 loc exp arity.
     free_names next loc ∧
     lookup loc (fromAList prog) = SOME (arity, exp) ∧
     check_exp loc arity exp = NONE ∧
     compile_exp loc next arity exp = NONE ∧
     compile_prog next prog = (next1, prog2) ⇒
       lookup loc (fromAList prog2) = SOME (arity, exp)`,
  ho_match_mp_tac compile_prog_ind \\ rw []
  \\ fs [fromAList_def, lookup_def]
  \\ Cases_on `loc' = loc` \\ rw []
  >-
   (Cases_on `lookup loc (fromAList xs)`
    \\ fs [compile_prog_def]
    \\ rpt (pairarg_tac \\ fs [])
    \\ rfs [] \\ rw []
    \\ simp [fromAList_def])
  \\ fs [lookup_insert]
  \\ Cases_on `compile_exp loc next arity exp` \\ fs []
  >-
   (fs [compile_prog_def]
    \\ pairarg_tac \\ fs [] \\ rw []
    \\ fs [fromAList_def, lookup_insert])
  \\ PairCases_on `x`
  \\ imp_res_tac more_free_names
  \\ imp_res_tac compile_exp_next_addr
  \\ fs [compile_prog_def]
  \\ pairarg_tac \\ fs [] \\ rw []
  \\ fs [fromAList_def, lookup_insert]
  \\ first_x_assum drule
  \\ disch_then drule
  \\ rw [fromAList_def, lookup_insert, is_free_name]);

val EVERY_free_names_SUCSUC = Q.prove (
  `∀xs.
     EVERY (free_names n o FST) xs ⇒
       EVERY (free_names (n + 2) o FST) xs`,
  Induct
  \\ strip_tac \\ fs []
  \\ strip_tac
  \\ imp_res_tac more_free_names);

val compile_prog_touched = Q.store_thm ("compile_prog_touched",
  `∀next prog prog2 loc exp arity.
     ALL_DISTINCT (MAP FST prog) ∧
     EVERY (free_names next o FST) prog ∧
     free_names next loc ∧
     lookup loc (fromAList prog) = SOME (arity, exp) ∧
     check_exp loc arity exp = SOME op ∧
     compile_prog next prog = (next1, prog2) ⇒
       ∃k. ∀exp_aux exp_opt.
         compile_exp loc (next + 2 * k) arity exp = SOME (exp_aux, exp_opt) ⇒
           lookup loc (fromAList prog2) = SOME (arity, exp_aux) ∧
           lookup (next + 2 * k) (fromAList prog2) = SOME (arity + 1, exp_opt)`,
  ho_match_mp_tac compile_prog_ind \\ rw []
  \\ fs [fromAList_def, lookup_def]
  \\ pop_assum mp_tac
  \\ simp [compile_prog_def]
  \\ rpt (pairarg_tac \\ fs [])
  \\ PURE_TOP_CASE_TAC \\ fs []
  >-
   (rw []
    \\ qpat_x_assum `compile_exp _ _ _ _ = _` mp_tac
    \\ simp [Once compile_exp_def]
    \\ qpat_x_assum `_ = SOME (_, _)` mp_tac
    \\ simp [lookup_insert, fromAList_def]
    \\ IF_CASES_TAC \\ fs []
    \\ TRY (PURE_CASE_TAC \\ fs [])
    \\ TRY (pairarg_tac \\ fs [])
    \\ strip_tac
    \\ first_x_assum drule
    \\ disch_then drule \\ rw []
    \\ fs [lookup_insert, fromAList_def]
    \\ qexists_tac `k` \\ rw []
    \\ fs [free_names_def])
  \\ PURE_CASE_TAC \\ rw []
  \\ qpat_x_assum `lookup _ _ = SOME (_,_)` mp_tac
  \\ fs [lookup_insert, fromAList_def]
  \\ IF_CASES_TAC \\ fs [] \\ rw []
  \\ imp_res_tac more_free_names
  \\ rfs [EVERY_free_names_SUCSUC]
  \\ fs [lookup_insert, fromAList_def, free_names_def]
  \\ TRY (qexists_tac `0` \\ fs [] \\ NO_TAC)
  \\ first_x_assum (qspec_then `loc'` assume_tac)
  \\ first_x_assum drule
  \\ disch_then drule \\ rw []
  \\ qexists_tac `k + 1` \\ fs []
  \\ simp [LEFT_ADD_DISTRIB]);

val check_exp_NONE_compile_exp = Q.prove (
  `check_exp loc arity exp = NONE ⇒ compile_exp loc next arity exp = NONE`,
  fs [compile_exp_def]);

val check_exp_SOME_compile_exp = Q.prove (
  `check_exp loc arity exp = SOME p ⇒
     ∃q. compile_exp loc next arity exp = SOME q`,
  fs [compile_exp_def]
  \\ pairarg_tac \\ fs []);

val EVERY_free_names_thm = Q.prove (
  `EVERY (free_names next o FST) prog ∧
   lookup loc (fromAList prog) = SOME x ⇒
     free_names next loc`,
  rw [lookup_fromAList, EVERY_MEM]
  \\ imp_res_tac ALOOKUP_MEM
  \\ first_x_assum (qspec_then `(loc, x)` mp_tac) \\ rw []);

val compile_prog_code_rel = Q.store_thm ("compile_prog_code_rel",
  `ALL_DISTINCT (MAP FST prog) ∧
   EVERY (free_names next o FST) prog ∧
   compile_prog next prog = (next1, prog2) ⇒
     code_rel (fromAList prog) (fromAList prog2)`,
  rw [code_rel_def]
  \\ imp_res_tac EVERY_free_names_thm
  >- metis_tac [check_exp_NONE_compile_exp, compile_prog_untouched]
  \\ drule compile_prog_touched
  \\ rpt (disch_then drule) \\ rw []
  \\ qexists_tac `2 * k + next` \\ fs []);

val evaluate_compile_prog = Q.store_thm ("evaluate_compile_prog",
  `EVERY (free_names next o FST) prog ∧
   ALL_DISTINCT (MAP FST prog) ∧
   evaluate ([Call 0 (SOME start) [] NONE], [],
             initial_state ffi0 (fromAList prog) k) = (r, s) ∧
   0 < k ∧
   r ≠ Rerr (Rabort Rtype_error) ⇒
   ∃ck s2.
     evaluate
      ([Call 0 (SOME start) [] NONE], [],
        initial_state ffi0 (fromAList (SND (compile_prog next prog))) (k + ck))
      = (r, s2) ∧
     state_rel s s2`,
  rw []
  \\ qmatch_asmsub_abbrev_tac `(es,env,st1)`
  \\ `env_rel F 0 env env` by fs [env_rel_def]
  \\ qabbrev_tac `ts: v_ty list = []`
  \\ `ty_rel env ts` by fs [ty_rel_def, Abbr`ts`]
  \\ drule (GEN_ALL compile_prog_code_rel)
  \\ disch_then drule
  \\ Cases_on `compile_prog next prog` \\ fs []
  \\ strip_tac
  \\ qmatch_assum_abbrev_tac `code_rel _ c`
  \\ `fromAList prog = st1.code` by fs [Abbr`st1`]
  \\ pop_assum (fn th => fs [th])
  \\ drule evaluate_rewrite_tail
  \\ disch_then (qspec_then `F` drule)
  \\ rpt (disch_then drule) \\ fs []
  \\ strip_tac
  \\ qexists_tac `0` \\ fs [inc_clock_ZERO]
  \\ qunabbrev_tac `st1`
  \\ imp_res_tac evaluate_code_const
  \\ fs [state_rel_def, initial_state_def]);

val compile_prog_semantics = Q.store_thm ("compile_prog_semantics",
  `EVERY (free_names n o FST) prog ∧
   ALL_DISTINCT (MAP FST prog) ∧
   SND (compile_prog n prog) = prog2 ∧
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
       \\ drule (GEN_ALL evaluate_compile_prog) \\ simp []
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
           \\ drule (GEN_ALL evaluate_compile_prog) \\ simp []
           \\ disch_then drule
           \\ impl_tac
           >- (spose_not_then strip_assume_tac \\ fs []
               \\ fs [evaluate_def]
               \\ every_case_tac \\ fs [] \\ rveq \\ fs [])
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
           \\ fs [state_component_equality, state_rel_def]
           \\ every_case_tac \\ fs [])
         \\ qpat_x_assum `∀extra._` mp_tac
         \\ first_x_assum (qspec_then `k'` assume_tac)
         \\ first_assum (subterm (fn tm => Cases_on`^(assert has_pair_type tm)`) o concl)
         \\ strip_tac \\ fs []
         \\ unabbrev_all_tac
         \\ drule (GEN_ALL evaluate_compile_prog)
         \\ ntac 2 (disch_then drule)
         \\ impl_tac
         >-
          (last_x_assum (qspec_then `k + k'` mp_tac)
          \\ fs [] \\ strip_tac
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
       \\ drule (GEN_ALL evaluate_compile_prog)
       \\ ntac 2 (disch_then drule)
       \\ impl_tac
       >-
         (last_x_assum (qspec_then `k + SUC k'` mp_tac)
         \\ fs [] \\ strip_tac
         \\ spose_not_then assume_tac \\ rveq \\ fs [])
       \\ strip_tac \\ rveq \\ fs []
       \\ reverse (Cases_on `s'.ffi.final_event`) \\ fs [] \\ rfs []
       >-
         (first_x_assum (qspec_then `ck + SUC k` mp_tac)
         \\ fs [ADD1]
         \\ strip_tac \\ fs [state_rel_def] \\ rfs [])
       \\ qhdtm_x_assum `evaluate` mp_tac
       \\ imp_res_tac evaluate_add_clock
       \\ pop_assum kall_tac
       \\ pop_assum mp_tac
       \\ impl_tac
       >- (strip_tac \\ fs [])
       \\ disch_then (qspec_then `ck + SUC k` mp_tac)
       \\ simp [inc_clock_def]
       \\ fs [ADD1]
       \\ ntac 2 strip_tac \\ rveq
       \\ fs [state_rel_def] \\ rfs [])
     \\ qmatch_assum_abbrev_tac `evaluate (exps,[],st) = _`
     \\ qspecl_then [`exps`,`[]`,`st`] mp_tac evaluate_add_to_clock_io_events_mono
     \\ simp [inc_clock_def, Abbr`st`]
     \\ disch_then (qspec_then `1` strip_assume_tac)
     \\ first_assum (subterm (fn tm => Cases_on`^(assert(has_pair_type)tm)`) o concl)
     \\ unabbrev_all_tac
     \\ drule (GEN_ALL evaluate_compile_prog)
     \\ ntac 2 (disch_then drule) \\ simp []
     \\ impl_tac
     >-
       (spose_not_then assume_tac
       \\ last_x_assum (qspec_then `k + 1` mp_tac)
       \\ fs [])
     \\ strip_tac
     \\ asm_exists_tac
     \\ every_case_tac \\ fs [] \\ rveq \\ fs []
     >-
       (qpat_x_assum `evaluate _ = (Rerr e,_)` mp_tac
       \\ imp_res_tac evaluate_add_clock
       \\ pop_assum kall_tac
       \\ pop_assum mp_tac
       \\ impl_tac >- fs []
       \\ disch_then (qspec_then `1` mp_tac)
       \\ simp [inc_clock_def])
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
     \\ drule (GEN_ALL evaluate_compile_prog)
     \\ ntac 2 (disch_then drule)
     \\ impl_tac
     >-
       (reverse conj_tac
       \\ CCONTR_TAC \\ fs []
       \\ fs [] \\ rveq
       \\ qhdtm_x_assum `evaluate` mp_tac
       \\ simp [evaluate_def]
       \\ every_case_tac \\ fs []
       \\ CCONTR_TAC \\ fs []
       \\ rveq \\ fs []
       \\ qpat_x_assum `FST _ = _` mp_tac
       \\ simp [evaluate_def]
       \\ drule (GEN_ALL compile_prog_code_rel) \\ fs []
       \\ disch_then drule
       \\ Cases_on `compile_prog n prog` \\ fs []
       \\ strip_tac
       \\ Cases_on `find_code (SOME start) ([]: v list) (fromAList prog)`
       >- rfs [find_code_def]
       \\ fs [] \\ rveq
       \\ rename1 `_ = SOME (q1, q2)`
       \\ imp_res_tac code_rel_find_code_SOME
       \\ `q1 = []` by (fs [find_code_def] \\ every_case_tac \\ fs [])
       \\ rveq
       \\ first_x_assum drule \\ strip_tac
       \\ every_case_tac \\ fs [])
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
    \\ drule (GEN_ALL evaluate_compile_prog)
    \\ ntac 2 (disch_then drule)
    \\ impl_tac
    >- (spose_not_then assume_tac \\ fs [])
    \\ strip_tac
    \\ qmatch_assum_rename_tac `evaluate (_,[],_ (SUC k)) = (_,rr)`
    \\ reverse (Cases_on `rr.ffi.final_event`)
    >-
      (first_x_assum
        (qspecl_then
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
    \\ impl_tac
    >- (strip_tac \\ fs [])
    \\ disch_then (qspec_then `SUC ck` mp_tac)
    \\ simp [inc_clock_def]
    \\ fs [ADD1]
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
  \\ drule (GEN_ALL evaluate_compile_prog)
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
    \\ last_x_assum (qspec_then `k` mp_tac)
    \\ fs [])
  \\ strip_tac
  \\ qmatch_asmsub_abbrev_tac `state_rel (SND p1) (SND p2)`
  \\ Cases_on `p1` \\ Cases_on `p2` \\ fs [markerTheory.Abbrev_def]
  \\ ntac 2 (pop_assum (mp_tac o SYM)) \\ fs []
  \\ ntac 2 strip_tac
  \\ qmatch_assum_rename_tac `state_rel p1 p2`
  \\ `p1.ffi = p2.ffi` by fs [state_rel_def]
  \\ rveq
  \\ conj_tac \\ rw []
  >- (qexists_tac `ck + k`
     \\ fs [])
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

val compile_prog_MEM = Q.store_thm("compile_prog_MEM",
  `compile_prog n xs = (n1,ys) /\ MEM e (MAP FST ys) ==>
   MEM e (MAP FST xs) \/ n <= e`,
  qspec_tac (`e`,`e`)
  \\ qspec_tac (`n1`,`n1`)
  \\ qspec_tac (`ys`,`ys`)
  \\ qspec_tac (`n`,`n`)
  \\ qspec_tac (`xs`,`xs`)
  \\ Induct
  >- fs [compile_prog_def]
  \\ gen_tac
  \\ PairCases_on `h`
  \\ rename1 `(name, arity, exp)`
  \\ simp [compile_prog_def]
  \\ rpt gen_tac
  \\ rpt (pairarg_tac \\ fs [])
  \\ PURE_CASE_TAC \\ fs []
  \\ TRY (PURE_CASE_TAC \\ fs [])
  \\ fs [MEM_MAP, PULL_EXISTS, FORALL_PROD]
  \\ rpt strip_tac \\ rveq \\ fs []
  \\ TRY (metis_tac [])
  \\ first_x_assum drule
  \\ disch_then drule
  \\ strip_tac
  >- metis_tac []
  \\ fs []);

val compile_prog_intro = Q.prove (
  `∀xs n ys n1 name.
    ¬MEM name (MAP FST xs) ∧
    free_names n name ∧
    compile_prog n xs = (n1, ys) ⇒
      ¬MEM name (MAP FST ys)`,
  Induct
  >- fs [compile_prog_def]
  \\ gen_tac
  \\ PairCases_on `h`
  \\ rpt gen_tac
  \\ simp [compile_prog_def]
  \\ rpt (pairarg_tac \\ fs [])
  \\ PURE_TOP_CASE_TAC \\ fs []
  >-
    (rpt strip_tac \\ rveq \\ fs []
    \\ metis_tac [])
  \\ PURE_CASE_TAC \\ fs []
  \\ rpt strip_tac \\ rveq \\ fs []
  \\ TRY (metis_tac [is_free_name])
  \\ metis_tac [more_free_names]);

val compile_prog_ALL_DISTINCT = Q.store_thm("compile_prog_ALL_DISTINCT",
  `compile_prog n xs = (n1,ys) /\ ALL_DISTINCT (MAP FST xs) /\
   EVERY (free_names n o FST) xs ==>
   ALL_DISTINCT (MAP FST ys)`,
  qspec_tac (`n1`,`n1`)
  \\ qspec_tac (`ys`,`ys`)
  \\ qspec_tac (`n`,`n`)
  \\ qspec_tac (`xs`,`xs`)
  \\ Induct
  >- fs [compile_prog_def]
  \\ gen_tac
  \\ PairCases_on `h`
  \\ rename1 `(name, arity, exp)`
  \\ simp [compile_prog_def]
  \\ rpt gen_tac
  \\ rpt (pairarg_tac \\ fs [])
  \\ PURE_CASE_TAC \\ fs []
  >-
    (rpt strip_tac \\ fs [] \\ rveq
    \\ qpat_x_assum `_ = (_, ys'')` kall_tac
    \\ res_tac
    \\ simp [MAP]
    \\ metis_tac [more_free_names, compile_prog_intro])
  \\ PURE_CASE_TAC \\ fs []
  \\ rpt strip_tac
  \\ rveq
  \\ fs [is_free_name]
  \\ imp_res_tac EVERY_free_names_SUCSUC
  \\ res_tac
  \\ simp []
  \\ reverse conj_tac
  >-
    (CCONTR_TAC \\ fs []
    \\ drule (GEN_ALL compile_prog_MEM)
    \\ disch_then drule
    \\ simp [MEM_MAP]
    \\ fs [EVERY_MEM]
    \\ gen_tac
    \\ Cases_on `MEM y xs` \\ fs []
    \\ res_tac
    \\ fs [is_free_name])
  \\ CCONTR_TAC \\ fs []
  \\ drule (GEN_ALL compile_prog_MEM)
  \\ disch_then drule
  \\ simp [MEM_MAP]
  \\ metis_tac [compile_prog_intro, more_free_names]);

val _ = export_theory();
