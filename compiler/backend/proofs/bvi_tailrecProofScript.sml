open preamble bviSemTheory bviPropsTheory bvi_tailrecTheory

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
  Cases \\ rw[get_bin_args_def]
  \\ rw[bvlPropsTheory.case_eq_thms]
  \\ rw[EQ_IMP_THM]);

val decide_ty_simp = Q.store_thm ("decide_ty_simp[simp]",
  `decide_ty ty1 ty2 = Int ⇔ ty1 = Int ∧ ty2 = Int`,
  Cases_on `ty1` \\ Cases_on `ty2` \\ fs [decide_ty_def]);

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

val try_update_LENGTH = Q.store_thm ("try_update_LENGTH",
  `LENGTH (try_update ty idx ts) = LENGTH ts`,
  Cases_on `idx` \\ rw [try_update_def]);

val EVERY_no_err_correct = Q.store_thm ("EVERY_no_err_correct",
  `∀xs env (s: ('c,'ffi) bviSem$state) r t ts.
     EVERY (no_err ts) xs ∧
     ty_rel env ts ∧
     evaluate (xs, env, s) = (r, t) ⇒
       s = t ∧
       ∃vs.
         r = Rval vs ∧
         LENGTH vs = LENGTH xs ∧
         EVERY (λv. ∃k. v = Number k) vs ∧
       (∀(s': ('c,'ffi) bviSem$state). evaluate (xs, env, s') = (r, s')) `,
  recInduct evaluate_ind
  \\ rw [no_err_def]
  \\ pop_assum mp_tac
  \\ simp [evaluate_def]
  \\ fs[pair_case_eq,bvlPropsTheory.case_eq_thms]
  \\ TRY (
    Cases_on `op` \\ fs []
    \\ strip_tac \\ rveq \\ fs[]
    \\ fs[evaluate_def, do_app_def, do_app_aux_def, bvlPropsTheory.case_eq_thms, pair_case_eq, bvlSemTheory.do_app_def]
    \\ rfs [small_int_def, small_enough_int_def] \\ rw[]
    \\ imp_res_tac evaluate_IMP_LENGTH
    \\ fs[LENGTH_EQ_NUM_compute,ADD1,bvl_to_bvi_id]
    \\ rw[] \\ fs[LENGTH_EQ_NUM_compute] \\ rw[] \\ fs[] \\ fs[] \\ fs[] \\ fs[] \\ rw[] \\ fs[]
    \\ res_tac \\ rw[bvl_to_bvi_id]
    \\ metis_tac[] )
  \\ (
    strip_tac \\ rveq \\ fs[]
    \\ fsrw_tac[DNF_ss][EVERY_MEM,EXISTS_MEM,bool_case_eq]
    \\ imp_res_tac evaluate_IMP_LENGTH
    \\ fs[LENGTH_EQ_NUM_compute,ADD1] \\ rw[]
    \\ fs[]
    \\ TRY (
      qmatch_assum_rename_tac`EL n ts = Int`
      \\ fs[ty_rel_def,LIST_REL_EL_EQN]
      \\ NO_TAC)
    \\ metis_tac[HD] ));

val no_err_correct = Q.store_thm ("no_err_correct",
  `no_err ts x ∧
   ty_rel env ts ∧
   evaluate ([x], env, (s: ('c,'ffi) bviSem$state)) = (r, t) ⇒
     ∃k. r = Rval [Number k] ∧ s = t ∧
         ∀(s': ('c,'ffi) bviSem$state). evaluate ([x], env, s') = (r, s')`,
  rw []
  \\ drule (Q.SPEC `[x]` EVERY_no_err_correct |> SIMP_RULE (srw_ss()) [])
  \\ rpt (disch_then drule) \\ rw []
  \\ imp_res_tac evaluate_SING_IMP \\ fs []);

val op_id_val_def = Define `
  (op_id_val Plus  = Number 0) ∧
  (op_id_val Times = Number 1) ∧
  (op_id_val Noop  = Number 6333)
  `;

val scan_expr_not_Noop = Q.store_thm ("scan_expr_not_Noop",
  `∀exp ts loc tt ty r ok op.
     scan_expr ts loc [exp] = [(tt, ty, r, SOME op)] ⇒
       op ≠ Noop`,
  Induct
  \\ rw [scan_expr_def]
  \\ rpt (pairarg_tac \\ fs []) \\ rw []
  \\ fs[bvlPropsTheory.case_eq_thms]
  \\ fs [from_op_def]
  \\ metis_tac []);

val check_exp_not_Noop = Q.store_thm ("check_exp_not_Noop",
  `∀loc arity exp op.
     check_exp loc arity exp = SOME op ⇒ op ≠ Noop`,
  rw [check_exp_def] \\ imp_res_tac scan_expr_not_Noop);

val to_op_eq_simp = Q.store_thm("to_op_eq_simp[simp]",
  `(to_op x = Add ⇔ (x = Plus)) ∧
   (to_op x = Mult ⇔ (x = Times)) ∧
   (to_op x = Mod ⇔ (x = Noop)) ∧
   (Add = to_op x ⇔ (x = Plus)) ∧
   (Mult = to_op x ⇔ (x = Times)) ∧
   (Mod = to_op x ⇔ (x = Noop))`,
   Cases_on`x` \\ rw[to_op_def]);

val op_eq_simp = Q.store_thm("op_eq_simp[simp]",
  `(op_eq Plus x ⇔ (∃xs. x = Op Add xs)) ∧
   (op_eq Times x ⇔ (∃xs. x = Op Mult xs))`,
  Cases_on`x` \\ rw[op_eq_def]);

val scan_expr_Op = Q.store_thm ("scan_expr_Op",
  `scan_expr ts loc [Op op xs] = [(tt, ty, r, SOME iop1)] ∧
   iop1 ≠ Noop ∧ ty = Int ∧
   rewrite_op ts iop2 loc (Op op xs) = (T, exp) ⇒
     ∃x y.
       exp = Op (to_op iop2) [x; y] ∧
       is_rec loc x ∧
       no_err ts y ∧
       op = to_op iop1 ∧
       iop1 = iop2`,
  rw [scan_expr_def]
  \\ fs [is_arith_op_def, is_const_def] \\ rw []
  \\ pop_assum mp_tac
  \\ once_rewrite_tac [rewrite_op_def]
  \\ simp [op_eq_def, to_op_def, from_op_def]
  \\ fs[case_eq_thms,bool_case_eq,pair_case_eq,case_elim_thms]
  \\ rw[]
  \\ rpt (pairarg_tac \\ fs []) \\ rveq
  \\ fs[case_eq_thms,bool_case_eq,case_elim_thms]
  \\ rw [assoc_swap_def, apply_op_def, to_op_def]
  \\ fs [is_rec_or_rec_binop_def, is_rec_def, get_bin_args_def, no_err_def]
  \\ fs[case_eq_thms,case_elim_thms,pair_case_eq,PULL_EXISTS,is_rec_def,no_err_def]);

val evaluate_rewrite_op = Q.store_thm ("evaluate_rewrite_op",
  `∀ts op loc exp env (s: ('c,'ffi) bviSem$state) r t p exp2.
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

(* TODO for append, parametrise on op *)
val env_rel_def = Define `
  env_rel opt acc env1 env2 ⇔
    isPREFIX env1 env2 ∧
    (opt ⇒
      LENGTH env1 = acc ∧
      LENGTH env2 > acc ∧
      ∃k. EL acc env2 = Number k)`;

val _ = temp_overload_on("in_ns_2",``λn. n MOD bvl_to_bvi_namespaces = 2``);

val code_rel_def = Define `
  code_rel c1 c2 ⇔
    ∀loc arity exp op.
      lookup loc c1 = SOME (arity, exp) ⇒
      (check_exp loc arity exp = NONE ⇒
        lookup loc c2 = SOME (arity, exp)) ∧
      (check_exp loc arity exp = SOME op ⇒
        ∃n.
          ∀exp_aux exp_opt.
          compile_exp loc n arity exp = SOME (exp_aux, exp_opt) ⇒
            lookup loc c2 = SOME (arity, exp_aux) ∧
            lookup n c2 = SOME (arity + 1, exp_opt))`;

val code_rel_find_code_SOME = Q.prove (
  `∀c1 c2 x (args: v list) a exp.
     code_rel c1 c2 ∧
     find_code (SOME n) args c1 = SOME (a, exp) ⇒
       find_code (SOME n) args c2 ≠ NONE`,
  rw [find_code_def, code_rel_def]
  \\ pop_assum mp_tac
  \\ rpt (PURE_TOP_CASE_TAC \\ fs [])
  \\ first_x_assum drule
  \\ fs [compile_exp_def]
  \\ CASE_TAC \\ fs [] \\ rw []
  \\ pairarg_tac \\ fs []);

val code_rel_find_code_NONE = Q.prove (
  `∀c1 c2 x (args: v list) a exp.
     code_rel c1 c2 ∧
     find_code NONE args c1 = SOME (a, exp) ⇒
       find_code NONE args c2 ≠ NONE`,
  rw [find_code_def, code_rel_def]
  \\ pop_assum mp_tac
  \\ rpt (PURE_TOP_CASE_TAC \\ fs []) \\ rw []
  >-
   (first_x_assum drule
    \\ fs [compile_exp_def]
    \\ CASE_TAC \\ fs [] \\ rw []
    \\ pairarg_tac \\ fs [])
  \\ first_x_assum drule
  \\ fs [compile_exp_def]
  \\ CASE_TAC \\ fs [] \\ rw []
  \\ pairarg_tac \\ fs []);

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
  \\ fs [compile_exp_def]
  \\ CASE_TAC \\ fs [] \\ rw []
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
  `!skip env n (st:('c,'ffi) bviSem$state).
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
  `∀x op vs (s:('c,'ffi) bviSem$state) r t.
     op ≠ Noop ⇒
     evaluate ([let_wrap (LENGTH vs) (id_from_op op) x], vs, s) =
     evaluate ([x], vs ++ [op_id_val op] ++ vs, s)`,
  rpt gen_tac
  \\ `LENGTH vs + 0 ≤ LENGTH vs` by fs []
  \\ drule evaluate_genlist_vars
  \\ disch_then (qspec_then `s` assume_tac)
  \\ simp [let_wrap_def, evaluate_def]
  \\ once_rewrite_tac [evaluate_APPEND]
  \\ Cases_on `op` \\ rw [id_from_op_def, evaluate_def]
  \\ simp [do_app_def, do_app_aux_def, small_enough_int_def, op_id_val_def]
  \\ pop_assum mp_tac
  \\ EVAL_TAC \\ rw []);

val evaluate_complete_ind = Q.store_thm ("evaluate_complete_ind",
  `∀P.
    (∀xs s.
      (∀ys t.
        exp2_size ys < exp2_size xs ∧ t.clock ≤ s.clock ∨ t.clock < s.clock ⇒
        P ys t) ⇒
      P xs s) ⇒
    ∀(xs: bvi$exp list) (s: ('c,'ffi) bviSem$state). P xs s`,
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

val no_err_extra = Q.prove (
  `∀ts exp extra.
     no_err ts exp ⇒ no_err (ts ++ extra) exp`,
  ho_match_mp_tac no_err_ind
  \\ rw [no_err_def, EL_APPEND1]
  \\ PURE_CASE_TAC \\ fs [EVERY_MEM]);

val is_rec_or_rec_binop_extra = Q.prove (
  `∀ts loc op exp extra.
    is_rec_or_rec_binop ts loc op exp ⇒
      is_rec_or_rec_binop (ts ++ extra) loc op exp`,
  rw [is_rec_or_rec_binop_def] \\ fs []
  \\ rpt (PURE_FULL_CASE_TAC \\ fs []) \\ rw []
  \\ metis_tac [no_err_extra]);

val rewrite_op_is_op = Q.prove (
  `∀ts op loc exp exp2 p.
     rewrite_op ts op loc exp = (p, exp2) ⇒
       if p then ∃x y. exp2 = Op (to_op op) [x; y] else exp = exp2`,
  ho_match_mp_tac rewrite_op_ind \\ rw []
  \\ pop_assum mp_tac
  \\ once_rewrite_tac [rewrite_op_def]
  \\ IF_CASES_TAC \\ fs []
  \\ PURE_TOP_CASE_TAC \\ fs []
  \\ rpt (pairarg_tac \\ fs []) \\ rw []
  \\ simp [assoc_swap_def, apply_op_def]
  \\ IF_CASES_TAC \\ fs []
  \\ PURE_TOP_CASE_TAC \\ fs []);

val no_err_is_rec_thm = Q.store_thm ("no_err_is_rec_thm",
  `(∀ts loc op exp. is_rec_or_rec_binop ts loc op exp ⇒ ¬no_err ts exp) ∧
   (∀ts loc exp. is_rec loc exp ⇒ ¬no_err ts exp)`,
  rw [is_rec_or_rec_binop_def, no_err_def]
  \\ Cases_on `exp`
  \\ fs [is_rec_def, get_bin_args_def, op_eq_def, no_err_def]
  \\ Cases_on `op` \\ fs [to_op_def,case_eq_thms,case_elim_thms]
  \\ rw[]
  \\ Cases_on `e1` \\ fs [is_rec_def, no_err_def]);

val no_err_rewrite_op_thm = Q.store_thm ("no_err_rewrite_op_thm",
  `∀ts op loc exp.
     no_err ts exp ⇒ rewrite_op ts op loc exp = (F, exp)`,
  ho_match_mp_tac rewrite_op_ind \\ rw []
  \\ once_rewrite_tac [rewrite_op_def]
  \\ IF_CASES_TAC \\ fs []
  \\ Cases_on `∃x y op. exp = Op op [x; y]` \\ fs []
  >-
   (res_tac \\ rveq
    \\ fs [op_eq_to_op] \\ rveq
    \\ sg `no_err ts x`
    >-
     (fs [no_err_def]
      \\ Cases_on `op` \\ fs [to_op_def])
    \\ fs [] \\ rfs []
    \\ sg `no_err ts y`
    >-
     (fs [no_err_def]
      \\ Cases_on `op` \\ fs [to_op_def])
    \\ fs []
    \\ simp [get_bin_args_def] \\ rw []
    \\ qpat_x_assum `is_rec_or_rec_binop _ _ _ _` mp_tac
    \\ simp [is_rec_or_rec_binop_def]
    \\ conj_tac
    \\ TRY
     (Cases_on `x` \\ Cases_on `y`
      \\ fs [no_err_def, is_rec_def]
      \\ NO_TAC)
    \\ PURE_CASE_TAC \\ fs [] \\ rveq
    \\ Cases_on `e1` \\ fs [is_rec_def, no_err_def]
    \\ PURE_FULL_CASE_TAC \\ fs [])
  \\ `get_bin_args exp = NONE` suffices_by fs []
  \\ Cases_on `exp` \\ fs [get_bin_args_def]
  \\ Cases_on `l` \\ fs [get_bin_args_def]
  \\ Cases_on `t` \\ fs [get_bin_args_def]
  \\ Cases_on `t'` \\ fs [get_bin_args_def]);

val is_rec_rewrite_op_thm = Q.store_thm ("is_rec_rewrite_op_thm",
  `∀ts op loc exp.
     is_rec loc exp ⇒ rewrite_op ts op loc exp = (F, exp)`,
  rw []
  \\ Cases_on `exp` \\ fs [is_rec_def]
  \\ once_rewrite_tac [rewrite_op_def]
  \\ simp [op_eq_def, get_bin_args_def]);

val is_rec_or_rec_binop_Op = Q.store_thm("is_rec_or_rec_binop_Op",
  `is_rec_or_rec_binop ts loc op (Op (to_op op) [e1;e2]) ⇔ op ≠ Noop ∧ is_rec loc e1 ∧ no_err ts e2`,
  rw[is_rec_or_rec_binop_def,is_rec_def,case_elim_thms,PULL_EXISTS]);

val assoc_swap_is_apply_op = Q.store_thm("assoc_swap_is_apply_op",
  `∃x y. assoc_swap op y2 y1 = Op (to_op op) [x;y]`,
  rw[assoc_swap_def,apply_op_def,case_eq_thms,PULL_EXISTS]
  \\ Cases_on`get_bin_args y1` \\ fs[]
  \\ metis_tac[]);

val no_err_Op = Q.store_thm("no_err_Op",
  `no_err ts (Op (to_op op) xs) ⇔
    op ≠ Noop ∧ EVERY (no_err ts) xs ∧ LENGTH xs = 2`,
  rw[no_err_def]
  \\ Cases_on`op` \\ simp[to_op_def]
  \\ srw_tac[ETA_ss][EQ_IMP_THM]);

val rewrite_op_T_imp = Q.store_thm("rewrite_op_T_imp",
  `∀ts op loc exp exp2.
   rewrite_op ts op loc exp = (T,exp2) ⇒
         (∃x y.
           exp2 = Op (to_op op) [x; y] ∧
           is_rec loc x ∧
           no_err ts y ∧
           is_rec_or_rec_binop ts loc op exp2)`,
  recInduct rewrite_op_ind \\ rw[]
  \\ pop_assum mp_tac
  \\ rw[Once rewrite_op_def]
  \\ fs[case_eq_thms,pair_case_eq]
  \\ pairarg_tac \\ fs[]
  \\ pairarg_tac \\ fs[]
  \\ rveq \\ fs[] \\ rveq
  \\ imp_res_tac rewrite_op_is_op
  \\ Cases_on`r1` \\ fs[] \\ rveq \\ fs[is_rec_or_rec_binop_Op] \\ rveq \\ fs[] \\ rfs[]
  >- (
    fs[bool_case_eq]
    \\ simp[assoc_swap_def,get_bin_args_def,apply_op_def,is_rec_or_rec_binop_Op,no_err_Op] )
  \\ Cases_on`r2` \\ fs[] \\ rveq \\ fs[is_rec_or_rec_binop_Op] \\ rveq \\ fs[] \\ rfs[]
  >- (
    fs[bool_case_eq]
    \\ simp[assoc_swap_def,get_bin_args_def,apply_op_def,is_rec_or_rec_binop_Op,no_err_Op] )
  \\ ntac 2 (pop_assum mp_tac)
  \\ simp[Once rewrite_op_def] \\ strip_tac
  \\ simp[Once rewrite_op_def] \\ strip_tac
  \\ fs[case_eq_thms,bool_case_eq,pair_case_eq] \\ rveq
  \\ simp[assoc_swap_def,get_bin_args_def,apply_op_def,is_rec_or_rec_binop_Op,no_err_Op]
  \\ imp_res_tac no_err_is_rec_thm \\ rveq
  \\ fs[is_rec_or_rec_binop_def,no_err_Op,is_rec_def,get_bin_args_def]);

val imp_these = [
   rewrite_op_T_imp
  ,rewrite_op_is_op
  ,no_err_extra
  ,is_rec_or_rec_binop_extra
  ,no_err_is_rec_thm
  ,CONTRAPOS (SPEC_ALL(CONJUNCT2 no_err_is_rec_thm)) |> SIMP_RULE std_ss []
  ,no_err_rewrite_op_thm
  ,is_rec_rewrite_op_thm]

val rewrite_op_extra = Q.store_thm ("rewrite_op_extra",
  `∀ts op loc exp exp2.
     rewrite_op ts op loc exp = (T, exp2) ⇒
       (∀ws. rewrite_op (ts ++ ws) op loc exp = (T, exp2))`,
  ho_match_mp_tac rewrite_op_ind \\ rw []
  \\ pop_assum mp_tac
  \\ simp[Once rewrite_op_def]
  \\ simp[bool_case_eq,case_eq_thms,pair_case_eq,PULL_EXISTS]
  \\ rpt gen_tac \\ strip_tac
  \\ pairarg_tac \\ fs[]
  \\ pairarg_tac \\ fs[]
  \\ rveq
  \\ simp[Once rewrite_op_def,get_bin_args_def]
  \\ rpt(pairarg_tac \\ fs[])
  \\ fs[case_eq_thms,bool_case_eq]
  \\ Cases_on`r1` \\ rfs[] \\ rveq
  \\ fs[] \\ rveq \\ fs[is_rec_or_rec_binop_Op,no_err_Op]
  \\ rveq \\ fs[]
  \\ map_every imp_res_tac imp_these
  \\ fs[] \\ rveq \\ fs[is_rec_or_rec_binop_Op,no_err_Op]
  \\ fs[] \\ rveq \\ fs[is_rec_or_rec_binop_Op,no_err_Op]
  \\ Cases_on`r2` \\ rfs[] \\ rveq
  \\ fs[] \\ rveq \\ fs[is_rec_or_rec_binop_Op,no_err_Op]
  \\ rveq \\ fs[]
  \\ map_every imp_res_tac imp_these
  \\ fs[] \\ rveq \\ fs[is_rec_or_rec_binop_Op,no_err_Op]
  \\ fs[] \\ rveq \\ fs[is_rec_or_rec_binop_Op,no_err_Op]
  \\ map_every TRY [Cases_on`r1'`,Cases_on`r2'`]
  \\ fs[is_rec_or_rec_binop_Op,no_err_Op] \\ rveq
  \\ map_every imp_res_tac imp_these
  \\ fs[is_rec_or_rec_binop_Op,no_err_Op] \\ rveq
  \\ rfs[] \\ rw[] \\ fs[]
  \\ TRY strip_tac
  \\ TRY (
    rpt(first_x_assum(qspec_then`ws`strip_assume_tac))
    \\ map_every imp_res_tac imp_these \\ fs[] \\ NO_TAC)
  \\ qhdtm_x_assum`is_rec_or_rec_binop`mp_tac
  \\ simp[is_rec_or_rec_binop_def,case_elim_thms,PULL_EXISTS]
  \\ strip_tac \\ map_every imp_res_tac imp_these \\ fs[]
  \\ rveq \\ simp[assoc_swap_def,get_bin_args_def,apply_op_def]
  \\ fs[is_rec_or_rec_binop_Op,no_err_Op]
  \\ qpat_x_assum`rewrite_op (ts++ws) _ _ _ = (T,_)`mp_tac
  \\ simp[Once rewrite_op_def,get_bin_args_def]
  \\ simp[Once is_rec_or_rec_binop_def]
  \\ pairarg_tac \\ fs[]
  \\ rpt(first_x_assum(qspec_then`ws`strip_assume_tac))
  \\ map_every imp_res_tac imp_these \\ fs[] \\ rveq \\ fs[]
  \\ rpt(qpat_x_assum`T`kall_tac)
  \\ IF_CASES_TAC \\ fs[]
  \\ simp[assoc_swap_def,apply_op_def]
  \\ IF_CASES_TAC \\ fs[]
  \\ simp[case_eq_thms,PULL_EXISTS]
  \\ strip_tac \\ rveq \\ fs[]
  \\ strip_tac \\ rveq \\ fs[is_rec_def]);

val scan_expr_EVERY_SING = Q.store_thm ("scan_expr_EVERY_SING[simp]",
  `EVERY P (scan_expr ts loc [x]) ⇔ P (HD (scan_expr ts loc [x]))`,
  `LENGTH (scan_expr ts loc [x]) = 1` by fs []
  \\ Cases_on `scan_expr ts loc [x]` \\ fs []);

val scan_expr_LENGTH = Q.store_thm ("scan_expr_LENGTH",
  `∀ts loc xs ys.
     scan_expr ts loc xs = ys ⇒
       EVERY (λy. LENGTH (FST y) = LENGTH ts) ys`,
  ho_match_mp_tac scan_expr_ind
  \\ rw [scan_expr_def] \\ fs []
  \\ rpt (pairarg_tac \\ fs [])
  \\ TRY (PURE_TOP_CASE_TAC \\ fs [])
  \\ rw [LENGTH_MAP2_MIN, try_update_LENGTH]);

val ty_rel_decide_ty = Q.store_thm ("ty_rel_decide_ty",
  `∀ts tt env.
     (ty_rel env ts ∨ ty_rel env tt) ∧ LENGTH ts = LENGTH tt ⇒
       ty_rel env (MAP2 decide_ty ts tt)`,
  Induct \\ rw [] \\ fs []
  \\ Cases_on `tt` \\ rfs [ty_rel_def]
  \\ EVAL_TAC \\ fs [] \\ rveq
  \\ Cases_on `h`  \\ fs [] \\ Cases_on `h'` \\ simp [decide_ty_def]);

val MAP2_if_mono = Q.store_thm ("MAP2_if_mono[simp]",
  `∀ts. MAP2 (λa b. if a = Int ∨ b = Int then Int else Any) ts ts = ts`,
  Induct \\ rw [] \\ Cases_on `h` \\ fs []);

val ty_rel_APPEND = Q.prove (
  `∀env ts ws vs.
     ty_rel env ts ∧ ty_rel vs ws ⇒ ty_rel (vs ++ env) (ws ++ ts)`,
  rw []
  \\ sg `LENGTH ws = LENGTH vs`
  >- (fs [ty_rel_def, LIST_REL_EL_EQN])
  \\ fs [ty_rel_def, LIST_REL_APPEND_EQ]);

val try_update_mono = Q.prove (
  `∀ts n m.
   EL n ts = Int ⇒
     EL n (try_update Int (SOME m) ts) = Int`,
  Induct \\ rw [try_update_def]
  \\ Cases_on `m`
  >-
   (fs []
    \\ Cases_on `n` \\ fs [])
  \\ fs [EL_TAKE]
  \\ first_x_assum (qspec_then `n - 1` mp_tac)
  \\ disch_then (qspec_then `n'` assume_tac)
  \\ Cases_on `n` \\ fs []
  \\ rfs [try_update_def, ADD1]);

val scan_expr_ty_rel = Q.store_thm ("scan_expr_ty_rel",
  `∀ts loc xs env ys (s: (num#'c,'ffi) bviSem$state) vs (t: (num#'c,'ffi) bviSem$state).
     ty_rel env ts ∧
     scan_expr ts loc xs = ys ∧
     evaluate (xs, env, s) = (Rval vs, t) ⇒
       EVERY (ty_rel env o FST) ys ∧
       LIST_REL (λv y. y = Int ⇒ ∃k. v = Number k) vs (MAP (FST o SND) ys)`,
  ho_match_mp_tac scan_expr_ind
  \\ fs [scan_expr_def]
  \\ rpt conj_tac
  \\ rpt gen_tac
  \\ simp [evaluate_def]
  >- (* Cons *)
   (strip_tac
    \\ rpt gen_tac
    \\ rpt (PURE_TOP_CASE_TAC \\ fs [])
    \\ strip_tac \\ rveq
    \\ res_tac \\ fs [] \\ rw []
    \\ imp_res_tac evaluate_SING_IMP \\ fs [] \\ rveq
    \\ PairCases_on `x0` \\ rfs [])
  >- (* Var *)
   (rw []
    \\ fs [ty_rel_def, LIST_REL_EL_EQN])
  \\ strip_tac
  \\ rpt gen_tac
  \\ rpt (pairarg_tac \\ fs [])
  >- (* If *)
   (rpt (PURE_TOP_CASE_TAC \\ fs [])
    \\ strip_tac \\ rveq
    \\ res_tac \\ fs [] \\ rveq
    \\ imp_res_tac scan_expr_LENGTH \\ fs []
    \\ metis_tac [ty_rel_decide_ty])
  >- (* Let *)
   (rpt (PURE_TOP_CASE_TAC \\ fs [])
    \\ strip_tac \\ rveq
    \\ sg `ty_rel (a++env) (MAP (FST o SND) (scan_expr ts loc xs) ++ ts)`
    >- metis_tac [ty_rel_def, EVERY2_APPEND]
    \\ last_x_assum drule
    \\ disch_then drule \\ rw []
    \\ sg `LENGTH xs + LENGTH ts = LENGTH tu`
    >- (imp_res_tac scan_expr_LENGTH \\ rfs [])
    \\ simp [ty_rel_def, LIST_REL_EL_EQN, EL_DROP]
    \\ conj_tac
    >- fs [ty_rel_def, LIST_REL_EL_EQN]
    \\ rw []
    \\ `n + LENGTH xs < LENGTH tu` by fs [ty_rel_def, LIST_REL_EL_EQN]
    \\ fs [EL_DROP]
    \\ fs [ty_rel_def, LIST_REL_EL_EQN]
    \\ `n + LENGTH xs < LENGTH a + LENGTH env` by fs []
    \\ first_x_assum drule \\ rw []
    \\ `LENGTH a = LENGTH xs` by fs []
    \\ fs [EL_APPEND2])
  >- (* Raise *)
   (rpt (PURE_FULL_CASE_TAC
    \\ fs []))
  >- (* Tick *)
   (IF_CASES_TAC \\ fs []
    \\ strip_tac \\ rveq
    \\ metis_tac [])
  >- (* Call *)
   (rpt (PURE_FULL_CASE_TAC \\ fs []) \\ rw []
    \\ imp_res_tac evaluate_SING_IMP \\ fs [])
     (* Op *)
  \\ pop_assum mp_tac
  \\ ntac 4 (PURE_TOP_CASE_TAC \\ fs [])
  \\ strip_tac \\ rveq
  \\ reverse conj_tac \\ fs []
  >-
   (pop_assum mp_tac
    \\ Cases_on `op` \\ fs [is_arith_op_def, is_const_def]
    \\ fs [do_app_def, do_app_aux_def, bvlSemTheory.do_app_def]
    \\ rpt (PURE_CASE_TAC \\ fs []) \\ rw [])
  \\ IF_CASES_TAC >- fs []
  \\ `¬is_arith_op op ⇒ is_num_rel op` by fs []
  \\ qpat_x_assum `¬(_)` kall_tac
  \\ PURE_TOP_CASE_TAC \\ fs [] \\ rveq
  \\ Cases_on `∃n. e1 = Var n` \\ fs [] \\ rveq
  >-
   (Cases_on `∃m. e2 = Var m` \\ fs [] \\ rveq
    >-
     (sg `∃k. EL n env = Number k ∧ ∃j. EL m env = Number j`
      >-
       (qpat_x_assum `evaluate _ = _` mp_tac
        \\ simp [evaluate_def]
        \\ IF_CASES_TAC \\ fs []
        \\ IF_CASES_TAC \\ fs []
        \\ rw []
        \\ qpat_x_assum `do_app _ _ _ = _` mp_tac
        \\ Cases_on `op` \\ fs [is_arith_op_def, is_num_rel_def]
        \\ simp [do_app_def, do_app_aux_def, bvlSemTheory.do_app_def]
        \\ rpt (PURE_CASE_TAC \\ fs []) \\ rw [])
      \\ fs [ty_rel_def, LIST_REL_EL_EQN, LENGTH_MAP2_MIN, index_of_def,
             try_update_LENGTH, EL_MAP2]
      \\ rw []
      \\ pop_assum mp_tac
      \\ simp [try_update_def]
      \\ TRY (IF_CASES_TAC \\ fs [])
      \\ TRY
       (Cases_on `n' < n` \\ fs [EL_TAKE, EL_APPEND1, EL_APPEND2]
        \\ Cases_on `n' > n` \\ fs [EL_APPEND1, EL_APPEND2, EL_DROP]
        \\ `n' = n` by fs [] \\ fs []
        \\ NO_TAC)
      \\ Cases_on `n' < m` \\ fs [EL_TAKE, EL_APPEND1, EL_APPEND2]
      \\ Cases_on `n' > m` \\ fs [EL_APPEND1, EL_APPEND2, EL_DROP]
      \\ `n' = m` by fs [] \\ fs [])
    \\ sg `∃k. EL n env = Number k`
    >-
     (qpat_x_assum `evaluate _ = _` mp_tac
      \\ simp [evaluate_def]
      \\ IF_CASES_TAC \\ fs []
      \\ PURE_TOP_CASE_TAC \\ fs []
      \\ PURE_TOP_CASE_TAC \\ fs []
      \\ rw []
      \\ qpat_x_assum `do_app _ _ _ = _` mp_tac
      \\ Cases_on `op` \\ fs [is_arith_op_def, is_num_rel_def]
      \\ simp [do_app_def, do_app_aux_def, bvlSemTheory.do_app_def]
      \\ rpt (PURE_CASE_TAC \\ fs []) \\ rw [])
    \\ fs [ty_rel_def, LIST_REL_EL_EQN, LENGTH_MAP2_MIN, index_of_def,
           try_update_LENGTH, EL_MAP2]
    \\ rw []
    \\ pop_assum mp_tac
    \\ TRY (Cases_on `e2` \\ fs [index_of_def])
    \\ simp [try_update_def]
    \\ TRY (IF_CASES_TAC \\ fs [])
    \\ Cases_on `n' < n` \\ fs [EL_TAKE, EL_APPEND1, EL_APPEND2]
    \\ Cases_on `n' > n` \\ fs [EL_APPEND1, EL_APPEND2, EL_DROP]
    \\ `n' = n` by fs [] \\ fs [])
  \\ reverse (Cases_on `∃m. e2 = Var m`) \\ fs [] \\ rveq
  >-
   (fs [EL_MAP2, try_update_LENGTH, ty_rel_def, LIST_REL_EL_EQN]
    \\ Cases_on `e1` \\ Cases_on `e2`
    \\ fs [try_update_def, index_of_def] \\ rw [])
  \\ sg `∃k. EL m env = Number k`
  >-
   (qpat_x_assum `evaluate _ = _` mp_tac
    \\ simp [evaluate_def]
    \\ PURE_TOP_CASE_TAC \\ fs []
    \\ PURE_TOP_CASE_TAC \\ fs []
    \\ IF_CASES_TAC \\ fs []
    \\ rw []
    \\ qpat_x_assum `do_app _ _ _ = _` mp_tac
    \\ Cases_on `op` \\ fs [is_arith_op_def, is_num_rel_def]
    \\ simp [do_app_def, do_app_aux_def, bvlSemTheory.do_app_def]
    \\ rpt (PURE_CASE_TAC \\ fs []) \\ rw [])
  \\ fs [ty_rel_def, LIST_REL_EL_EQN, LENGTH_MAP2_MIN, index_of_def,
         try_update_LENGTH, EL_MAP2]
  \\ rw []
  \\ pop_assum mp_tac
  \\ TRY (Cases_on `e1` \\ fs [index_of_def])
  \\ simp [try_update_def]
  \\ TRY (IF_CASES_TAC \\ fs [])
  \\ Cases_on `n < m` \\ fs [EL_TAKE, EL_APPEND1, EL_APPEND2]
  \\ Cases_on `n > m` \\ fs [EL_APPEND1, EL_APPEND2, EL_DROP]
  \\ `n = m` by fs [] \\ fs []);

(* TODO: move? *)
val from_op_thm = save_thm("from_op_thm[simp]",
  map (fn tm => EVAL ``from_op ^tm``)
  (TypeBase.case_def_of ``:closLang$op``
   |> CONJUNCTS |> map (el 1 o #2 o strip_comb o lhs o concl o SPEC_ALL))
  |> LIST_CONJ)
(* -- *)

val rewrite_scan_expr = Q.store_thm ("rewrite_scan_expr",
  `∀loc next op acc ts exp tt ty p exp2 tt' ty' r opr.
   rewrite (loc,next,op,acc,ts) exp = (tt,ty,p,exp2) ∧
   op ≠ Noop ∧
   scan_expr ts loc [exp] = [(tt', ty', r, opr)] ⇒
     case opr of
       SOME op' => op = op' ⇒ p
     | NONE     => ¬p`,
  recInduct rewrite_ind
  \\ rw [rewrite_def, scan_expr_def] \\ fs []
  \\ rpt (pairarg_tac \\ fs []) \\ rveq
  \\ fs[case_eq_thms,case_elim_thms,pair_case_eq,bool_case_eq]
  \\ rw[] \\ fs[]
  \\ fs[Once rewrite_op_def,op_eq_def]
  \\ Cases_on`op` \\ fs[to_op_def] \\ rfs[]
  \\ fs[get_bin_args_def,case_eq_thms] \\ rfs[]
  \\ rpt(pairarg_tac \\ fs[]) \\ rveq
  \\ fs[is_rec_or_rec_binop_def,assoc_swap_def,apply_op_def,case_eq_thms,pair_case_eq,bool_case_eq]);

val optimized_code_def = Define `
  optimized_code loc arity exp n c op =
    ∃exp_aux exp_opt.
        compile_exp loc n arity exp = SOME (exp_aux, exp_opt) ∧
        check_exp loc arity exp     = SOME op ∧
        lookup loc c                = SOME (arity, exp_aux) ∧
        lookup n c                  = SOME (arity + 1, exp_opt)`;

val code_rel_subspt = Q.store_thm("code_rel_subspt",
  `code_rel c1 x1 ∧ subspt x1 x2 ⇒ code_rel c1 x2`,
  rw[code_rel_def]
  \\ fs[subspt_lookup]
  \\ first_x_assum drule
  \\ disch_then(qspec_then`op`mp_tac)
  \\ rw[] \\ qexists_tac`n` \\ rw[]);

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
  free_names n (name: num) ⇔ ∀k. n + bvl_to_bvi_namespaces*k ≠ name
  `;

val more_free_names = Q.prove (
  `free_names n name ⇒ free_names (n + bvl_to_bvi_namespaces) name`,
  fs [free_names_def] \\ rpt strip_tac
  \\ first_x_assum (qspec_then `k + 1` mp_tac) \\ strip_tac
  \\ rw []);

val is_free_name = Q.prove (
  `free_names n name ⇒ n ≠ name`,
  fs [free_names_def] \\ strip_tac
  \\ first_x_assum (qspec_then `0` mp_tac) \\ strip_tac \\ rw []);

val compile_exp_next_addr = Q.prove (
  `compile_exp loc next args exp = NONE ⇒
     compile_exp loc (next + bvl_to_bvi_namespaces) args exp = NONE`,
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
       EVERY (free_names (n + bvl_to_bvi_namespaces) o FST) xs`,
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
         compile_exp loc (next + bvl_to_bvi_namespaces * k) arity exp = SOME (exp_aux, exp_opt) ⇒
           lookup loc (fromAList prog2) = SOME (arity, exp_aux) ∧
           lookup (next + bvl_to_bvi_namespaces * k) (fromAList prog2) = SOME (arity + 1, exp_opt)`,
  ho_match_mp_tac compile_prog_ind \\ rw []
  \\ fs [fromAList_def, lookup_def]
  \\ pop_assum mp_tac
  \\ simp [compile_prog_def]
  \\ rpt (pairarg_tac \\ fs [])
  \\ PURE_TOP_CASE_TAC \\ fs []
  >-
   (rw []
    \\ qpat_x_assum `compile_exp _ _ _ _ = _` mp_tac
    \\ simp [Once compile_exp_def, check_exp_def]
    \\ `LENGTH (scan_expr (REPLICATE arity Any) loc [exp]) = LENGTH [exp]` by fs []
    \\ CASE_TAC \\ fs []
    \\ PairCases_on `h` \\ fs [] \\ rveq
    \\ qpat_x_assum `_ = SOME (_, _)` mp_tac
    \\ simp [lookup_insert, fromAList_def]
    \\ IF_CASES_TAC \\ strip_tac
    \\ rw [] \\ rfs []
    \\ rveq \\ fs []
    \\ TRY (pairarg_tac \\ fs [])
    \\ first_x_assum drule
    \\ disch_then drule \\ rw []
    \\ fs [lookup_insert, fromAList_def]
    \\ qexists_tac `k` \\ rw []
    \\ fs [free_names_def,backend_commonTheory.bvl_to_bvi_namespaces_def])
  \\ PURE_CASE_TAC \\ rw []
  \\ qpat_x_assum `lookup _ _ = SOME (_,_)` mp_tac
  \\ fs [lookup_insert, fromAList_def]
  \\ IF_CASES_TAC \\ fs [] \\ rw []
  \\ imp_res_tac more_free_names
  \\ rfs [EVERY_free_names_SUCSUC]
  \\ fs [lookup_insert, fromAList_def, free_names_def]
  \\ TRY (qexists_tac `0` \\ fs [backend_commonTheory.bvl_to_bvi_namespaces_def] \\ NO_TAC)
  \\ first_x_assum (qspec_then `loc'` assume_tac)
  \\ first_x_assum drule
  \\ disch_then drule \\ rw []
  \\ qexists_tac `k + 1` \\ fs []
  \\ simp [LEFT_ADD_DISTRIB]
  \\ fs[backend_commonTheory.bvl_to_bvi_namespaces_def]);

val check_exp_NONE_compile_exp = Q.prove (
  `check_exp loc arity exp = NONE ⇒ compile_exp loc next arity exp = NONE`,
  fs [compile_exp_def]);

val check_exp_SOME_compile_exp = Q.prove (
  `check_exp loc arity exp = SOME p ⇒
     ∃q. compile_exp loc next arity exp = SOME q`,
  fs [compile_exp_def, check_exp_def]
  \\ rw [] \\ rw []
  \\ pairarg_tac \\ fs []);

val EVERY_free_names_thm = Q.prove (
  `EVERY (free_names next o FST) prog ∧
   lookup loc (fromAList prog) = SOME x ⇒
     free_names next loc`,
  rw [lookup_fromAList, EVERY_MEM]
  \\ imp_res_tac ALOOKUP_MEM
  \\ first_x_assum (qspec_then `(loc, x)` mp_tac) \\ rw []);

val compile_prog_code_rel = Q.store_thm ("compile_prog_code_rel",
  `compile_prog next prog = (next1, prog2) ∧
   ALL_DISTINCT (MAP FST prog) ∧
   EVERY (free_names next o FST) prog ⇒
     code_rel (fromAList prog) (fromAList prog2)`,
  rw [code_rel_def]
  \\ imp_res_tac EVERY_free_names_thm
  >- metis_tac [check_exp_NONE_compile_exp, compile_prog_untouched]
  \\ drule compile_prog_touched
  \\ rpt (disch_then drule) \\ rw []
  \\ qexists_tac `bvl_to_bvi_namespaces * k + next` \\ fs []
  \\ `0 < bvl_to_bvi_namespaces` by EVAL_TAC
  \\ simp[ADD_MODULUS]);

val compile_prog_next_mono = Q.store_thm("compile_prog_next_mono",
  `∀n xs n1 ys. compile_prog n xs = (n1,ys) ⇒ ∃k. n1 = n + bvl_to_bvi_namespaces * k`,
  recInduct compile_prog_ind
  \\ rw[compile_prog_def]
  \\ rpt(pairarg_tac \\ fs[bvlPropsTheory.case_eq_thms])
  \\ rveq \\ fs[]
  \\ TRY(qexists_tac`0` \\ simp[] \\ NO_TAC)
  \\ TRY(qexists_tac`k` \\ simp[] \\ NO_TAC)
  \\ TRY(qexists_tac`k+1` \\ simp[] \\ NO_TAC));

val compile_prog_MEM = Q.store_thm("compile_prog_MEM",
  `compile_prog n xs = (n1,ys) /\ MEM e (MAP FST ys) ==>
   MEM e (MAP FST xs) \/ (n <= e /\ e < n1 /\ (∃k. e = n + k * bvl_to_bvi_namespaces))`,
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
  \\ rveq
  \\ imp_res_tac compile_prog_next_mono \\ fs[]
  \\ first_x_assum drule
  \\ TRY (simp[backend_commonTheory.bvl_to_bvi_namespaces_def] \\
    rw[] \\ rpt disj2_tac \\ qexists_tac`0` \\ simp[] \\ NO_TAC)
  \\ disch_then drule
  \\ strip_tac
  >- metis_tac []
  \\ fs []
  \\ rpt disj2_tac
  \\ qexists_tac`k'' + 1` \\ simp[]);

val compile_prog_intro = Q.prove (
  `∀xs n ys n1 name.
    ¬MEM name (MAP FST xs) ∧
    free_names n name ∧
    compile_prog n xs = (n1, ys) ⇒
      ¬MEM name (MAP FST ys) ∧
      free_names n1 name
      `,
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
  \\ metis_tac [is_free_name,more_free_names]);

val compile_prog_ALL_DISTINCT = Q.store_thm("compile_prog_ALL_DISTINCT",
  `compile_prog n xs = (n1,ys) /\ ALL_DISTINCT (MAP FST xs) /\
   EVERY (free_names n o FST) xs ==>
   ALL_DISTINCT (MAP FST ys) /\
   EVERY (free_names n1 o FST) ys`,
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
  \\ reverse(rpt strip_tac) \\ rveq
  \\ fs [is_free_name]
  \\ imp_res_tac EVERY_free_names_SUCSUC
  \\ res_tac
  \\ simp []
  >- (
    fs[free_names_def]
    \\ imp_res_tac compile_prog_next_mono
    \\ rveq \\ fs[]
    \\ `bvl_to_bvi_namespaces ≠ 0` by EVAL_TAC
    \\ CCONTR_TAC \\ fs[] \\ rveq \\ fs[]
    \\ first_x_assum(qspec_then`k+k''+1`mp_tac)
    \\ simp[] )
  \\ reverse conj_tac
  >-
    (CCONTR_TAC \\ fs []
    \\ drule (GEN_ALL compile_prog_MEM)
    \\ disch_then drule
    \\ simp [MEM_MAP]
    \\ fs [EVERY_MEM]
    \\ `0 < bvl_to_bvi_namespaces` by EVAL_TAC \\ fs[]
    \\ gen_tac
    \\ Cases_on `MEM y xs` \\ fs []
    \\ res_tac
    \\ fs [is_free_name])
  \\ CCONTR_TAC \\ fs []
  \\ drule (GEN_ALL compile_prog_MEM)
  \\ disch_then drule
  \\ simp [MEM_MAP]
  \\ metis_tac [compile_prog_intro, more_free_names]);

val namespace_rel_def = Define`
  namespace_rel c1 c2 ⇔
    (∀n. n ∈ domain c2 ⇒ if in_ns_2 n then n ∉ domain c1 else n ∈ domain c1) ∧
    (∀n. n ∈ domain c1 ⇒ ¬(in_ns_2 n))`;

val mk_co_def = Define`
  mk_co co = λn.
   let
     ((next,cfg),prog) = co n;
     (next,prog) = compile_prog next prog
   in
     (cfg,prog)`;

val mk_cc_def = Define`
  mk_cc cc = λ(next,cfg) prog.
    let (next,prog) = compile_prog next prog in
      OPTION_MAP (λ(code,data,cfg). (code,data,(next,cfg))) (cc cfg prog)`;

val state_rel_def = Define`
  state_rel s t ⇔
    t.refs = s.refs ∧
    t.clock = s.clock ∧
    t.global = s.global ∧
    t.ffi = s.ffi ∧
    t.compile_oracle = mk_co s.compile_oracle ∧
    s.compile = mk_cc t.compile ∧
    code_rel s.code t.code ∧
    namespace_rel s.code t.code ∧
    (∀n. let ((next,cfg),prog) = s.compile_oracle n in
            ALL_DISTINCT (MAP FST prog) ∧
            EVERY (free_names next o FST) prog ∧
            EVERY ($~ o in_ns_2 o FST) prog ∧
            in_ns_2 next) ∧
    (∀n. n ∈ domain t.code ∧ in_ns_2 n ⇒ n < FST(FST(s.compile_oracle 0)))`;

val state_rel_const = Q.store_thm("state_rel_const",
  `state_rel s t ⇒
    t.refs = s.refs ∧
    t.clock = s.clock ∧
    t.global = s.global ∧
    t.ffi = s.ffi`, rw[state_rel_def]);

val state_rel_with_clock = Q.store_thm("state_rel_with_clock",
  `state_rel s t ⇒ state_rel (s with clock := k) (t with clock := k)`,
  rw[state_rel_def]);

val state_rel_code_rel = Q.store_thm("state_rel_code_rel",
  `state_rel s t ⇒ code_rel s.code t.code`,
  rw[state_rel_def]);

val code_rel_union = Q.store_thm("code_rel_union",
  `code_rel x y ∧ code_rel t s ∧
   (*
   (∀a. a ∉ domain x ∧ a ∈ domain s ⇒ a ∉ domain y) ∧
   (∀a. a ∉ domain x ∧ a ∈ domain y ⇒ a ∉ domain s)
   *)
   DISJOINT (domain s) (domain y)
   (* DISJOINT (domain s DIFF domain t) (domain y DIFF domain x) *)
   ⇒
    code_rel (union x t) (union y s)`,
  rw[code_rel_def,lookup_union]
  \\ fs[bvlPropsTheory.case_eq_thms]
  \\ fs[IN_DISJOINT,IN_DIFF,domain_lookup]
  \\ res_tac
  \\ TRY(qexists_tac`n` \\ simp[])
  \\ metis_tac[option_nchotomy,NOT_SOME_NONE]);

val namespace_rel_union = Q.store_thm("namespace_rel_union",
  `namespace_rel x y ∧ namespace_rel t s ∧
   DISJOINT (domain s) (domain y)
  ⇒
   namespace_rel (union x t) (union y s)`,
  rw[namespace_rel_def,domain_union,IN_DISJOINT]
  \\ metis_tac[]);

val compile_prog_namespace_rel = Q.store_thm("compile_prog_namespace_rel",
  `compile_prog next prog = (next1,prog2) ∧ in_ns_2 next ∧ EVERY ($~ o in_ns_2 o FST) prog ⇒
   namespace_rel (fromAList prog) (fromAList prog2)`,
  rw[namespace_rel_def,EVERY_MEM,domain_fromAList,MEM_MAP,PULL_EXISTS] \\
  imp_res_tac compile_prog_MEM \\
  fs[MEM_MAP,PULL_EXISTS]
  \\ res_tac \\ fs[]
  \\ fs[backend_commonTheory.bvl_to_bvi_namespaces_def]
  \\ CCONTR_TAC \\ fs[] >- metis_tac[]
  \\ last_x_assum drule
  \\ qpat_x_assum`_ = FST _`(assume_tac o SYM)
  \\ simp[]);

val state_rel_do_app_aux = Q.store_thm("state_rel_do_app_aux",
  `do_app_aux op vs s = res ∧
   state_rel s t ∧ op ≠ Install ∧ (∀n. op ≠ Label n)
   ⇒
   ∃res'.
     do_app_aux op vs t = res' ∧
     OPTREL (OPTREL ($= ### state_rel)) res res'`,
  simp[do_app_aux_def] \\ strip_tac
  \\ Cases_on`res` \\ fs[]
  >- (
    fs[case_eq_thms,OPTREL_def]
    \\ fs[state_rel_def] )
  \\ imp_res_tac state_rel_const
  \\ fs[case_eq_thms]
  \\ rveq \\ fs[OPTREL_def,quotient_pairTheory.PAIR_REL_THM]
  \\ fs[state_rel_def]);

val state_rel_do_app = Q.store_thm("state_rel_do_app",
  `bviSem$do_app op vs s = Rval (r,s') ∧
   state_rel s t ∧ op ≠ Install ∧ (∀n. op ≠ Label n)
   ⇒
   ∃t'.
     bviSem$do_app op vs t = Rval (r,t') ∧
     state_rel s' t'`,
  rw[do_app_def]
  \\ imp_res_tac state_rel_do_app_aux \\ fs[]
  \\ first_x_assum(qspec_then`vs`strip_assume_tac)
  \\ fs[case_eq_thms,OPTREL_def] \\ rw[] \\ rfs[]
  \\ fs[PULL_EXISTS]
  \\ rveq \\ fs[quotient_pairTheory.PAIR_REL]
  \\ TRY(pairarg_tac \\ fs[])
  \\ imp_res_tac state_rel_const
  \\ fs[bvlSemTheory.do_app_def,case_eq_thms,bvl_to_bvi_id]
  \\ rveq \\ fs[bvl_to_bvi_id]
  \\ fs[do_app_aux_def]
  \\ fs[state_rel_def,bvl_to_bvi_def,bvi_to_bvl_def]);

val state_rel_do_app_err = Q.store_thm("state_rel_do_app_err",
  `bviSem$do_app op vs s = Rerr e ∧
   state_rel s t ∧ op ≠ Install ∧ (∀n. op ≠ Label n)
   ⇒
   bviSem$do_app op vs t = Rerr e`,
  rw[do_app_def]
  \\ imp_res_tac state_rel_do_app_aux \\ fs[]
  \\ first_x_assum(qspec_then`vs`strip_assume_tac)
  \\ fs[case_eq_thms,OPTREL_def] \\ rw[] \\ rfs[]
  \\ imp_res_tac state_rel_const \\ rw[]
  \\ fs[bvi_to_bvl_def]
  \\ fs[bvlSemTheory.do_app_def]
  \\ TOP_CASE_TAC \\ fs[]
  \\ fs[case_eq_thms,do_app_aux_def]);

val do_app_to_op_state = Q.store_thm("do_app_to_op_state",
  `bviSem$do_app (to_op op) vs s = Rval (r,t) ⇒ t = s`,
  rw[]
  \\ Cases_on`op` \\ fs[to_op_def,do_app_def,do_app_aux_def,bvlSemTheory.do_app_def]
  \\ fs[case_eq_thms] \\ rw[bvl_to_bvi_id]
  \\ rw[bvl_to_bvi_id]);

(* TODO:

   For non-arithmetic operations, (∃op' check_exp ... ⇒ ...) will have
   to include some op_rel op op' which says that op and op' operate on
   the same type. *)
val evaluate_rewrite_tail = Q.store_thm ("evaluate_rewrite_tail",
  `∀xs (s:((num#'c),'ffi) bviSem$state) env1 r t opt s' acc env2 loc ts.
     evaluate (xs, env1, s) = (r, t) ∧
     env_rel opt acc env1 env2 ∧
     state_rel s s' ∧
     ty_rel env1 ts ∧
     (opt ⇒ LENGTH xs = 1) ∧
     r ≠ Rerr (Rabort Rtype_error) ⇒
       ∃t'.
       evaluate (xs, env2, s') = (r, t') ∧
       state_rel t t' ∧
       (opt ⇒
         ∀op n exp arity.
           lookup loc s.code = SOME (arity, exp) ∧
           optimized_code loc arity exp n s'.code op ∧
           (∃op' tt ty rr.
             scan_expr ts loc [HD xs] = [(tt, ty, rr, SOME op')] ∧
             op' ≠ Noop ∧ ty = Int) ⇒
               let (tu, tz, lr, x) = rewrite (loc, n, op, acc, ts) (HD xs) in
                 ∃rrr t1 t2.
                 evaluate ([x], env2, s') = (rrr,t1) ∧
                 evaluate ([apply_op op (HD xs) (Var acc)],
                   env2, s') = (rrr,t2) ∧
                 state_rel t t1 ∧
                 state_rel t t2)`,
  ho_match_mp_tac evaluate_complete_ind
  \\ ntac 2 (rpt gen_tac \\ strip_tac)
  \\ Cases_on `xs` \\ fs []
  >- (fs [evaluate_def] \\ rw[] \\ metis_tac[])
  \\ qpat_x_assum `evaluate _ = _` mp_tac
  \\ reverse (Cases_on `t'`) \\ fs []
  >-
   (simp [evaluate_def]
    \\ PURE_TOP_CASE_TAC \\ fs []
    \\ reverse PURE_TOP_CASE_TAC \\ fs []
    >-
     (rw []
      \\ first_assum (qspecl_then [`[h]`,`s`] mp_tac)
      \\ simp [bviTheory.exp_size_def]
      \\ rpt (disch_then drule) \\ fs []
      \\ strip_tac \\ fs[]
      \\ metis_tac[])
    \\ qmatch_goalsub_rename_tac `evaluate (y::ys, env1, s2)`
    \\ first_assum (qspecl_then [`[h]`,`s`] mp_tac)
    \\ simp [bviTheory.exp_size_def]
    \\ rpt (disch_then drule) \\ fs []
    \\ strip_tac
    \\ ntac 2 PURE_TOP_CASE_TAC \\ fs [] \\ rveq
    \\ strip_tac
    \\ first_assum (qspecl_then [`y::ys`,`s2`] mp_tac)
    \\ imp_res_tac evaluate_clock
    \\ simp [bviTheory.exp_size_def]
    \\ rpt (disch_then drule) \\ fs []
    \\ impl_tac >- (strip_tac \\ fs[])
    \\ strip_tac \\ fs[]
    \\ PURE_TOP_CASE_TAC \\ fs [] \\ rw []
    \\ metis_tac[] )
  \\ fs [bviTheory.exp_size_def]
  \\ Cases_on `∃v. h = Var v` \\ fs [] \\ rveq
  >-
   (simp [evaluate_def]
    \\ `LENGTH env1 ≤ LENGTH env2` by metis_tac [env_rel_def, IS_PREFIX_LENGTH]
    \\ IF_CASES_TAC \\ fs []
    \\ strip_tac \\ fs [] \\ rveq
    \\ conj_tac
    >- fs [env_rel_def, is_prefix_el]
    \\ rw [scan_expr_def])
  \\ Cases_on `∃x1. h = Tick x1` \\ fs [] \\ rveq
  >-
   (simp [evaluate_def]
    \\ imp_res_tac state_rel_const
    \\ IF_CASES_TAC \\ fs [] \\ rw [] \\ rw[]
    >-
     (rw [rewrite_def, evaluate_def, apply_op_def]
      \\ rpt (pairarg_tac \\ fs [])
      \\ rw [evaluate_def])
    \\ first_x_assum (qspecl_then [`[x1]`,`dec_clock 1 s`] mp_tac)
    \\ impl_tac
    >- fs [bviTheory.exp_size_def, evaluate_clock, dec_clock_def]
    \\ `state_rel (dec_clock 1 s) (dec_clock 1 s')` by fs [dec_clock_def,state_rel_def]
    \\ rpt (disch_then drule) \\ fs []
    \\ disch_then (qspec_then `loc` mp_tac) \\ rw []
    \\ rw[] \\ fs[]
    \\ simp [rewrite_def]
    \\ rpt (pairarg_tac \\ fs []) \\ rw []
    \\ first_x_assum drule
    \\ fs [scan_expr_def]
    \\ rw [evaluate_def, apply_op_def])
  \\ Cases_on `∃x1. h = Raise x1` \\ fs [] \\ rveq
  >-
   (simp [scan_expr_def, evaluate_def]
    \\ `env_rel F acc env1 env2` by fs [env_rel_def]
    \\ PURE_TOP_CASE_TAC \\ rw []
    \\ first_x_assum (qspecl_then [`[x1]`,`s`] mp_tac)
    \\ simp [bviTheory.exp_size_def]
    \\ rpt (disch_then drule) \\ rw []
    \\ rpt (PURE_FULL_CASE_TAC \\ fs [])
    \\ rw [] \\ fs []
    \\ metis_tac[])
  \\ Cases_on `∃xs x1. h = Let xs x1` \\ fs [] \\ rveq
  >-
   (simp [evaluate_def]
    \\ PURE_TOP_CASE_TAC \\ fs []
    \\ strip_tac
    \\ first_assum (qspecl_then [`xs`,`s`] mp_tac)
    \\ impl_tac >- simp [bviTheory.exp_size_def]
    \\ disch_then drule
    \\ `env_rel F acc env1 env2` by fs[env_rel_def]
    \\ rpt(disch_then drule) \\ fs[]
    \\ impl_tac >- (strip_tac \\ fs[])
    \\ strip_tac \\ fs[]
    \\ reverse(PURE_TOP_CASE_TAC) \\ fs[] \\ rveq \\ fs[]
    >-
     (rpt strip_tac
      \\ pairarg_tac \\ fs []
      \\ fs [rewrite_def, scan_expr_def]
      \\ rpt (pairarg_tac \\ fs [])
      \\ rw [evaluate_def, apply_op_def])
    \\ `env_rel opt (acc+LENGTH a) (a++env1) (a++env2)` by
      (Cases_on `opt`
      \\ fs [env_rel_def, IS_PREFIX_LENGTH]
      \\ fs [EL_APPEND2])
    \\ rename1 `evaluate (xs,env,s) = (Rval a, s2)`
    \\ sg `ty_rel (a++env) (MAP (FST o SND) (scan_expr ts loc xs) ++ ts)`
    >-
     (drule scan_expr_ty_rel
      \\ disch_then (qspecl_then [`loc`,`xs`,`scan_expr ts loc xs`,`s`] mp_tac)
      \\ simp [] \\ rw []
      \\ metis_tac [ty_rel_def, EVERY2_APPEND])
    \\ imp_res_tac evaluate_clock
    \\ first_x_assum (qspecl_then [`[x1]`,`s2`] mp_tac)
    \\ impl_tac >- simp [bviTheory.exp_size_def]
    \\ rpt (disch_then drule)
    \\ disch_then (qspec_then `loc` mp_tac)
    \\ simp[] \\ strip_tac \\ fs[]
    \\ imp_res_tac evaluate_code_mono
    \\ rpt strip_tac
    \\ rpt (pairarg_tac \\ fs []) \\ rveq
    \\ `lookup loc s2.code = lookup loc s.code` by fs[subspt_lookup]
    \\ fs[]
    \\ `optimized_code loc arity exp n t'.code op`
    by ( fs[optimized_code_def,subspt_lookup] )
    \\ first_x_assum drule
    \\ fs [scan_expr_def]
    \\ qpat_x_assum `rewrite _ (Let _ _) = _` mp_tac
    \\ simp [rewrite_def]
    \\ pairarg_tac \\ fs [] \\ rw []
    \\ `acc < LENGTH env2` by fs [env_rel_def]
    \\ `LENGTH xs = LENGTH a` by metis_tac [evaluate_IMP_LENGTH]
    \\ pop_assum (fn th => fs [th]) \\ rw []
    \\ rpt(pairarg_tac \\ fs[]) \\ rveq \\ rfs[]
    \\ simp [apply_op_def, evaluate_def, EL_LENGTH_APPEND, EL_APPEND2]
    \\ CASE_TAC \\ simp[]
    \\ rfs[apply_op_def, evaluate_def] \\ fs[EL_APPEND2])
  \\ Cases_on `∃x1 x2 x3. h = If x1 x2 x3` \\ fs [] \\ rveq
  >-
   (simp [evaluate_def]
    \\ `env_rel F acc env1 env2` by fs [env_rel_def]
    \\ PURE_TOP_CASE_TAC \\ fs []
    \\ reverse PURE_TOP_CASE_TAC \\ fs []
    >-
     (strip_tac \\ rveq \\ fs []
      \\ first_assum (qspecl_then [`[x1]`,`s`] mp_tac)
      \\ simp [bviTheory.exp_size_def]
      \\ rpt (disch_then drule) \\ fs [] \\ rw [] \\ rw[]
      \\ pairarg_tac \\ fs []
      \\ fs [rewrite_def]
      \\ rpt (pairarg_tac \\ fs [])
      \\ rw [evaluate_def, apply_op_def])
    \\ first_assum (qspecl_then [`[x1]`,`s`] mp_tac)
    \\ simp [bviTheory.exp_size_def]
    \\ rpt (disch_then drule) \\ fs []
    \\ strip_tac
    \\ rename1 `evaluate ([x1],_,s) = (_,s2)`
    \\ reverse (Cases_on `opt`) \\ fs []
    >-
     (IF_CASES_TAC \\ fs []
      >-
       (strip_tac
        \\ first_assum (qspecl_then [`[x2]`,`s2`] mp_tac)
        \\ imp_res_tac evaluate_clock
        \\ simp [bviTheory.exp_size_def]
        \\ rpt (disch_then drule)
        \\ rw[])
      \\ IF_CASES_TAC \\ fs []
      \\ strip_tac
      \\ first_assum (qspecl_then [`[x3]`,`s2`] mp_tac)
      \\ imp_res_tac evaluate_clock
      \\ simp [bviTheory.exp_size_def]
      \\ rpt (disch_then drule) \\ rw [])
    \\ strip_tac
    \\ simp[LEFT_EXISTS_AND_THM,CONJ_ASSOC]
    \\ conj_tac
    >-
     (IF_CASES_TAC \\ fs []
      >-
       (first_x_assum (qspecl_then [`[x2]`,`s2`] mp_tac)
        \\ imp_res_tac evaluate_clock \\ fs []
        \\ simp [bviTheory.exp_size_def]
        \\ rpt (disch_then drule) \\ rw [])
      \\ IF_CASES_TAC \\ fs []
      \\ first_x_assum (qspecl_then [`[x3]`,`s2`] mp_tac)
      \\ imp_res_tac evaluate_clock \\ fs []
      \\ simp [bviTheory.exp_size_def]
      \\ rpt (disch_then drule) \\ rw [])
    \\ rw []
    \\ fs [rewrite_def, evaluate_def, scan_expr_def]
    \\ rpt (pairarg_tac \\ fs [])
    \\ sg `ty_rel env1 ti`
    >-
     (drule scan_expr_ty_rel
      \\ rpt (disch_then drule)
      \\ rw [])
    \\ rw []
    >- (* xt ∧ xe optimized *)
     (qpat_x_assum `_ = (r, t)` mp_tac
      \\ IF_CASES_TAC \\ fs []
      >-
       (strip_tac
       \\ first_assum (qspecl_then [`[x2]`,`s2`] mp_tac)
       \\ impl_tac
       >-
        (imp_res_tac evaluate_clock
         \\ simp [bviTheory.exp_size_def])
       \\ disch_then drule
       \\ disch_then (qspec_then `T` drule)
       \\ rpt (disch_then drule)
       \\ disch_then (qspec_then `loc` mp_tac) \\ rw []
       \\ `lookup loc s2.code = lookup loc s.code`
       by ( imp_res_tac evaluate_code_mono \\ fs[subspt_lookup] )
       \\ rfs[]
       \\ `optimized_code loc arity exp n t'.code op`
       by (
         imp_res_tac evaluate_code_mono
         \\ fs[optimized_code_def]
         \\ fs[subspt_lookup] )
       \\ first_x_assum drule
       \\ disch_then drule
       \\ impl_tac
       >-
        (fs [optimized_code_def]
         \\ imp_res_tac scan_expr_not_Noop
         \\ drule rewrite_scan_expr
         \\ rpt (disch_then drule)
         \\ PURE_CASE_TAC \\ fs []
         \\ qpat_x_assum `rewrite _ x3 = _` kall_tac
         \\ drule rewrite_scan_expr
         \\ rpt (disch_then drule)
         \\ PURE_TOP_CASE_TAC \\ fs [])
       \\ pairarg_tac \\ fs []
       \\ rw [evaluate_def, apply_op_def] \\ rw[])
     \\ IF_CASES_TAC \\ fs [] \\ rw []
     \\ first_assum (qspecl_then [`[x3]`,`s2`] mp_tac)
     \\ impl_tac
     >-
      (imp_res_tac evaluate_clock
       \\ simp [bviTheory.exp_size_def])
     \\ disch_then drule
     \\ disch_then (qspec_then `T` drule)
     \\ rpt (disch_then drule)
     \\ disch_then (qspec_then `loc` mp_tac) \\ rw []
     \\ `lookup loc s2.code = lookup loc s.code`
     by ( imp_res_tac evaluate_code_mono \\ fs[subspt_lookup] )
     \\ rfs[]
     \\ `optimized_code loc arity exp n t'.code op`
     by (
       imp_res_tac evaluate_code_mono
       \\ fs[optimized_code_def]
       \\ fs[subspt_lookup] )
     \\ first_x_assum drule
     \\ disch_then drule
     \\ impl_tac
     >-
      (fs [optimized_code_def]
       \\ imp_res_tac scan_expr_not_Noop
       \\ drule rewrite_scan_expr
       \\ rpt (disch_then drule)
       \\ PURE_CASE_TAC \\ fs []
       \\ imp_res_tac scan_expr_not_Noop)
     \\ pairarg_tac \\ fs []
     \\ rw [evaluate_def, apply_op_def]
     \\ rw[])
    >- (* xt optimized, xe untouched *)
     (qpat_x_assum `_ = (r, t)` mp_tac
      \\ IF_CASES_TAC \\ fs []
      >-
       (strip_tac
        \\ first_assum (qspecl_then [`[x2]`,`s2`] mp_tac)
        \\ impl_tac
        >-
         (imp_res_tac evaluate_clock
          \\ simp [bviTheory.exp_size_def])
        \\ disch_then drule
        \\ disch_then (qspec_then `T` drule)
        \\ rpt (disch_then drule)
        \\ disch_then (qspec_then `loc` mp_tac) \\ rw []
         \\ `lookup loc s2.code = lookup loc s.code`
         by ( imp_res_tac evaluate_code_mono \\ fs[subspt_lookup] )
         \\ rfs[]
         \\ `optimized_code loc arity exp n t'.code op`
         by (
           imp_res_tac evaluate_code_mono
           \\ fs[optimized_code_def]
           \\ fs[subspt_lookup] )
        \\ first_x_assum drule
        \\ disch_then drule
        \\ impl_tac
        >-
         (fs [optimized_code_def]
          \\ imp_res_tac scan_expr_not_Noop
          \\ qpat_x_assum `rewrite _ x3 = _` kall_tac
          \\ drule rewrite_scan_expr
          \\ rpt (disch_then drule)
          \\ PURE_CASE_TAC \\ fs [])
        \\ pairarg_tac \\ fs []
        \\ rw [evaluate_def, apply_op_def]
        \\ rw[])
      \\ IF_CASES_TAC \\ fs [] \\ rw []
      \\ first_assum (qspecl_then [`[x3]`,`s2`] mp_tac)
      \\ impl_tac
      >-
       (imp_res_tac evaluate_clock
        \\ simp [bviTheory.exp_size_def])
      \\ rpt (disch_then drule)
      \\ rw [evaluate_def, apply_op_def]
      \\ `acc < LENGTH env2` by fs[env_rel_def]
      \\ rw[]
      \\ CASE_TAC \\ rw[]
      \\ CASE_TAC \\ rw[]
      \\ CASE_TAC \\ simp[]
      \\ imp_res_tac do_app_to_op_state \\ fs[])
    >- (* xe optimized, xt untouched *)
     (qpat_x_assum `_ = (r, t)` mp_tac
      \\ IF_CASES_TAC \\ fs []
      >-
       (strip_tac
        \\ first_assum (qspecl_then [`[x2]`,`s2`] mp_tac)
        \\ impl_tac
        >-
         (imp_res_tac evaluate_clock
          \\ simp [bviTheory.exp_size_def])
        \\ rpt (disch_then drule)
        \\ rw [evaluate_def, apply_op_def]
        \\ `acc < LENGTH env2` by fs[env_rel_def]
        \\ rw[]
        \\ CASE_TAC \\ rw[]
        \\ CASE_TAC \\ rw[]
        \\ CASE_TAC \\ rw[]
        \\ imp_res_tac do_app_to_op_state \\ fs[])
      \\ IF_CASES_TAC \\ fs [] \\ rw []
      \\ first_assum (qspecl_then [`[x3]`,`s2`] mp_tac)
      \\ impl_tac
      >-
       (imp_res_tac evaluate_clock
        \\ simp [bviTheory.exp_size_def])
      \\ disch_then drule
      \\ disch_then (qspec_then `T` drule)
      \\ rpt (disch_then drule)
      \\ disch_then (qspec_then `loc` mp_tac) \\ rw []
       \\ `lookup loc s2.code = lookup loc s.code`
       by ( imp_res_tac evaluate_code_mono \\ fs[subspt_lookup] )
       \\ rfs[]
       \\ `optimized_code loc arity exp n t'.code op`
       by (
         imp_res_tac evaluate_code_mono
         \\ fs[optimized_code_def]
         \\ fs[subspt_lookup] )
      \\ first_x_assum drule
      \\ disch_then drule
      \\ impl_tac
      >-
       (fs [optimized_code_def]
        \\ imp_res_tac scan_expr_not_Noop
        \\ drule rewrite_scan_expr
        \\ rpt (disch_then drule)
        \\ PURE_CASE_TAC \\ fs []
        \\ imp_res_tac scan_expr_not_Noop)
      \\ pairarg_tac \\ fs []
      \\ rw [evaluate_def, apply_op_def]
      \\ rw[])
    \\ qpat_x_assum `_ = (r, t)` mp_tac
    \\ IF_CASES_TAC \\ fs []
    >-
     (strip_tac
      \\ first_assum (qspecl_then [`[x2]`,`s2`] mp_tac)
      \\ impl_tac
      >-
       (imp_res_tac evaluate_clock
        \\ simp [bviTheory.exp_size_def])
      \\ rpt (disch_then drule)
      \\ rw [evaluate_def, apply_op_def]
      \\ `acc < LENGTH env2` by fs[env_rel_def]
      \\ rw[]
      \\ CASE_TAC \\ rw[]
      \\ CASE_TAC \\ rw[]
      \\ CASE_TAC \\ rw[]
      \\ imp_res_tac do_app_to_op_state \\ fs[])
    \\ IF_CASES_TAC \\ fs [] \\ rw []
    \\ first_assum (qspecl_then [`[x3]`,`s2`] mp_tac)
    \\ impl_tac
    >-
     (imp_res_tac evaluate_clock
      \\ simp [bviTheory.exp_size_def])
    \\ rpt (disch_then drule)
    \\ rw [evaluate_def, apply_op_def]
    \\ `acc < LENGTH env2` by fs[env_rel_def]
    \\ rw[]
    \\ CASE_TAC \\ rw[]
    \\ CASE_TAC \\ rw[]
    \\ CASE_TAC \\ rw[]
    \\ imp_res_tac do_app_to_op_state \\ fs[])
  \\ Cases_on `∃xs op. h = Op op xs` \\ fs [] \\ rveq
  >-
   (simp [evaluate_def]
    \\ PURE_TOP_CASE_TAC \\ fs []
    \\ strip_tac
    \\ simp[CONJ_ASSOC,LEFT_EXISTS_AND_THM]
    \\ conj_tac
    >-
     (first_x_assum (qspecl_then [`xs`, `s`] mp_tac)
      \\ simp [bviTheory.exp_size_def]
      \\ `env_rel F acc env1 env2` by fs [env_rel_def]
      \\ rpt (disch_then drule) \\ fs[]
      (*
      \\ disch_then (qspec_then `loc` mp_tac) \\ fs []
      *)
      \\ impl_tac >- (strip_tac \\ fs[]) \\ rw[] \\ fs[]
      \\ Cases_on`op=Install`
      >- (
        reverse(fs[bvlPropsTheory.case_eq_thms] \\ rveq \\ fs[do_app_def])
        >- (
          fs[do_install_def,bvlPropsTheory.case_eq_thms]
          \\ rveq \\ fs[]
          \\ rpt(pairarg_tac \\ fs[bvlPropsTheory.case_eq_thms])
          \\ rveq \\ fs[] )
        \\ fs[do_install_def,bvlPropsTheory.case_eq_thms] \\ rveq \\ fs[]
        \\ rpt(pairarg_tac \\ fs[]) \\ rveq \\ fs[]
        \\ qhdtm_x_assum`state_rel`mp_tac
        \\ simp[state_rel_def,mk_cc_def,mk_co_def]
        \\ strip_tac \\ fs[]
        \\ rpt(pairarg_tac \\ fs[]) \\ rveq
        \\ rename1`compile_prog next1 prog1 = (next2, prog2)`
        \\ `LENGTH prog1 ≤ LENGTH prog2` by metis_tac[compile_prog_LENGTH,SND,GREATER_EQ]
        \\ `prog1 ≠ []` by (strip_tac \\ fs[])
        \\ `prog2 ≠ []` by (strip_tac \\ fs[])
        \\ fs[bvlPropsTheory.case_eq_thms,pair_case_eq,PULL_EXISTS]
        \\ pairarg_tac \\ fs[] \\ rveq
        \\ fs[shift_seq_def]
        \\ qpat_x_assum`_ = FST _`(assume_tac o SYM) \\ fs[]
        \\ pairarg_tac \\ fs[]
        \\ pairarg_tac \\ fs[] \\ rveq
        \\ simp[RIGHT_EXISTS_AND_THM]
        \\ simp[LEFT_EXISTS_AND_THM]
        \\ qmatch_assum_rename_tac`code_rel src.code tgt.code`
        \\ qmatch_assum_abbrev_tac`compile_prog next1 prog1 = (next2, prog2)`
        \\ `DISJOINT (domain src.code) (set (MAP FST prog1))` by simp[Abbr`prog1`]
        \\ `in_ns_2 next1` by (rpt(first_x_assum(qspec_then`0`mp_tac) \\ simp[]))
        \\ qpat_x_assum`compile_prog next1 prog1 = _`assume_tac
        \\ drule (GEN_ALL compile_prog_code_rel)
        \\ impl_tac
        >- (
          simp[Abbr`prog1`]
          \\ rpt(first_x_assum(qspec_then`0`mp_tac) \\ simp[] ))
        \\ strip_tac
        \\ `∀n. in_ns_2 n ⇒ ¬MEM n (MAP FST prog1)`
        by (
          rw[] \\
          qpat_x_assum`∀n. _ (src.compile_oracle n)`(qspec_then`0`mp_tac) \\
          simp[] \\
          strip_tac \\ fs[EVERY_MEM,MEM_MAP,PULL_EXISTS]
          \\ metis_tac[] )
        \\ conj_asm1_tac
        >- (
          fs[IN_DISJOINT]
          \\ qx_gen_tac`n`
          \\ spose_not_then strip_assume_tac
          \\ qpat_x_assum`∀n. _ (src.compile_oracle n)`(qspec_then`0`mp_tac)
          \\ simp[]
          \\ CCONTR_TAC \\ fs[]
          \\ Cases_on`in_ns_2 n`
          >- (
            `¬MEM n (MAP FST prog1)` by ( metis_tac[] )
            \\ drule (GEN_ALL compile_prog_MEM)
            \\ disch_then drule \\ simp[]
            \\ CCONTR_TAC \\ fs[]
            \\ res_tac \\ fs[] )
          \\ fs[namespace_rel_def]
          \\ `n ∈ domain src.code` by metis_tac[]
          \\ drule (GEN_ALL compile_prog_MEM)
          \\ disch_then drule
          \\ strip_tac >- metis_tac[]
          \\ fs[backend_commonTheory.bvl_to_bvi_namespaces_def] )
        \\ qpat_x_assum`∀n. _ (src.compile_oracle n)`(qspec_then`0`mp_tac)
        \\ simp[] \\ strip_tac
        \\ conj_asm1_tac
        >- ( drule compile_prog_ALL_DISTINCT \\ simp[] )
        \\ conj_tac >- (
          Cases_on`prog2` \\ fs[compile_prog_def,Abbr`prog1`]
          \\ Cases_on`prog` \\ fs[compile_prog_def,case_eq_thms]
          \\ pairarg_tac \\ fs[] \\ rw[] )
        \\ conj_asm1_tac
        >- (
          match_mp_tac code_rel_union
          \\ fs[domain_fromAList,DISJOINT_SYM] )
        \\ conj_asm1_tac
        >- (
          match_mp_tac namespace_rel_union
          \\ fs[domain_fromAList,DISJOINT_SYM]
          \\ match_mp_tac (GEN_ALL compile_prog_namespace_rel)
          \\ asm_exists_tac \\ fs[])
        \\ simp[domain_union]
        \\ imp_res_tac compile_prog_next_mono
        \\ rveq \\ rw[]
        >- ( res_tac \\ simp[] )
        \\ fs[domain_fromAList]
        \\ drule (GEN_ALL compile_prog_MEM)
        \\ disch_then drule
        \\ simp[] )
      \\ Cases_on`∃n. op = Label n`
      >- (
        fs[] \\ rveq \\
        fs[do_app_def,do_app_aux_def] \\
        imp_res_tac state_rel_code_rel \\
        imp_res_tac code_rel_domain \\
        fs[SUBSET_DEF] \\
        fs[case_eq_thms] \\ rveq \\ fs[] ) \\ fs[]
      \\ fs[case_eq_thms] \\ rveq \\ fs[]
      \\ imp_res_tac state_rel_do_app \\ fs[]
      \\ imp_res_tac state_rel_do_app_err \\ fs[])
    \\ rw []
    \\ pairarg_tac \\ fs []
    \\ pop_assum mp_tac
    \\ simp [rewrite_def]
    \\ PURE_TOP_CASE_TAC \\ fs []
    \\ `op ≠ Install ∧ (∀n. op ≠ Label n)` by ( fs[scan_expr_def] )
    \\ reverse PURE_TOP_CASE_TAC \\ fs []
    >- (
      rw[] \\
      first_assum(qspecl_then[`xs`,`s`]mp_tac) \\
      simp[bviTheory.exp_size_def] \\
      `env_rel F acc env1 env2` by fs [env_rel_def] \\
      rpt (disch_then drule) \\ fs [] \\
      impl_tac >- (strip_tac \\ fs[]) \\
      strip_tac \\
      reverse(fs[case_eq_thms] \\ rveq \\ fs[])
      >- ( rw[apply_op_def,evaluate_def] \\ rw[] )
      >- (
        imp_res_tac state_rel_do_app_err \\
        rw[apply_op_def,evaluate_def] )
      >- (
        drule state_rel_do_app
        \\ simp[] \\ strip_tac
        \\ simp[apply_op_def,evaluate_def]
        \\ `acc < LENGTH env2` by fs[env_rel_def]
        \\ simp[]
        \\ CASE_TAC \\ fs[]
        \\ CASE_TAC \\ fs[]
        \\ imp_res_tac do_app_to_op_state \\ fs[]))
    \\ drule (GEN_ALL scan_expr_Op) \\ fs []
    \\ disch_then drule
    \\ strip_tac \\ rveq
    \\ rw [get_bin_args_def]
    \\ sg `∃ticks args. x' = Call ticks (SOME loc) args NONE`
    >-
     (Cases_on `x'` \\ fs [is_rec_def]
      \\ Cases_on `o'` \\ fs [is_rec_def])
    \\ rw [args_from_def, push_call_def]
    \\ rename1 `to_op op`
    \\ simp [apply_op_def]
    \\ `env_rel F acc env1 env2` by fs [env_rel_def]
    \\ `acc < LENGTH env2` by fs [env_rel_def]
    \\ first_assum (qspecl_then [`xs`,`s`] mp_tac)
    \\ simp [bviTheory.exp_size_def]
    \\ rpt (disch_then drule) \\ fs []
    \\ impl_tac >- (strip_tac \\ fs[])
    \\ rw []
    \\ qmatch_asmsub_abbrev_tac `(T, expr)`
    \\ Cases_on `evaluate ([Op (to_op op) xs], env1, s)`
    \\ drule (INST_TYPE[gamma|->``:num#'c``]evaluate_rewrite_op)
    \\ disch_then (qspecl_then [`ts`,`op`,`loc`,`T`,`expr`] mp_tac)
    \\ impl_tac
    >-
      (fs [evaluate_def]
      \\ rpt (PURE_FULL_CASE_TAC \\ fs []) \\ rw []
      \\ imp_res_tac do_app_err \\ fs [])
    \\ fs []
    \\ qunabbrev_tac `expr`
    \\ pop_assum mp_tac
    \\ qmatch_goalsub_abbrev_tac `_ ⇒ _ ⇒ goal`
    \\ simp [evaluate_def]
    \\ strip_tac \\ rveq
    \\ PURE_CASE_TAC \\ fs []
    \\ rename1 `_ = (r_args, s_args)`
    \\ Cases_on `r_args = Rerr (Rabort Rtype_error)` \\ fs []
    \\ first_assum (qspecl_then [`args`,`s`] mp_tac)
    \\ `exp2_size args < exp2_size xs` by
     (imp_res_tac rewrite_op_exp_size
      \\ fs [bviTheory.exp_size_def])
    \\ simp [bviTheory.exp_size_def]
    \\ rpt (disch_then drule) \\ fs []
    \\ strip_tac
    \\ reverse (Cases_on `r_args`) \\ fs []
    >-
     (qunabbrev_tac `goal`
      \\ rw [evaluate_def]
      \\ once_rewrite_tac [evaluate_APPEND]
      \\ fs []
      \\ `to_op op ≠ Install ∧ (∀n. to_op op ≠ Label n)` by (Cases_on`op` \\ fs[to_op_def])
      \\ qpat_x_assum`_ _ _ = (Rerr _ ,_)`mp_tac
      \\ simp[Once case_eq_thms]
      \\ simp[Once case_eq_thms]
      \\ simp[Once case_eq_thms]
      \\ reverse strip_tac \\ rveq \\ fs[]
      \\ imp_res_tac state_rel_do_app_err \\ fs[])
    \\ Cases_on `find_code (SOME loc) a s_args.code` \\ fs []
    \\ Cases_on `x` \\ fs []
    \\ Cases_on `evaluate ([y], env1, s_args)`
    \\ drule (GEN_ALL (INST_TYPE[gamma|->``:num#'c``]no_err_correct))
    \\ rpt (disch_then drule)
    \\ strip_tac \\ rveq
    \\ rename1 `s_args.clock`
    \\ first_assum (qspecl_then [`[y]`,`s_args`] mp_tac)
    \\ impl_tac
    >-
     (imp_res_tac evaluate_clock
     \\ imp_res_tac rewrite_op_exp_size
     \\ fs [bviTheory.exp_size_def])
    \\ rpt (disch_then drule) \\ fs []
    \\ strip_tac \\ fs [] \\ rveq
    \\ qabbrev_tac `ts' = REPLICATE (LENGTH env2 - LENGTH env1) Any`
    \\ `ty_rel env2 (ts++ts')`
    by (
      fs[env_rel_def,IS_PREFIX_APPEND,Abbr`ts'`]
      \\ match_mp_tac ty_rel_APPEND
      \\ simp[ty_rel_def,LIST_REL_EL_EQN,EL_REPLICATE] )
    \\ `no_err (ts ++ ts') y` by metis_tac[no_err_extra]
    \\ drule (GEN_ALL no_err_correct)
    \\ disch_then drule
    \\ disch_then drule
    \\ strip_tac \\ rveq \\ fs[] \\ rveq
    \\ IF_CASES_TAC \\ fs []
    >-
     (rw [Abbr `goal`, evaluate_def]
      \\ once_rewrite_tac [evaluate_APPEND]
      \\ simp [evaluate_def]
      \\ `∃j. EL acc env2 = Number j` by fs [env_rel_def] \\ fs []
      \\ reverse CASE_TAC
      >- (
        Cases_on`op` \\ fs[to_op_def,do_app_def,do_app_aux_def,bvlSemTheory.do_app_def] )
      \\ CASE_TAC \\ fs[]
      \\ imp_res_tac do_app_code
      \\ imp_res_tac state_rel_code_rel
      \\ `s_args.code = r'.code` by ( fs[case_eq_thms] )
      \\ fs[]
      \\ qhdtm_x_assum`optimized_code`mp_tac
      \\ rw[optimized_code_def]
      \\ imp_res_tac evaluate_code_mono
      \\ fs[subspt_lookup]
      \\ simp[find_code_def]
      \\ res_tac \\ fs[]
      \\ res_tac \\ fs[]
      \\ imp_res_tac evaluate_IMP_LENGTH \\ fs[]
      \\ fs[find_code_def]
      \\ imp_res_tac state_rel_const \\ fs[]
      \\ imp_res_tac do_app_const \\ fs[]
      \\ rveq
      \\ reverse(fs[case_eq_thms] \\ rveq \\ fs[])
      >- (
        match_mp_tac state_rel_with_clock
        \\ imp_res_tac do_app_to_op_state \\ fs[] )
      \\ imp_res_tac do_app_err \\ fs[] )
    \\ PURE_CASE_TAC \\ fs []
    \\ strip_tac
    \\ qunabbrev_tac `goal`
    \\ qmatch_asmsub_abbrev_tac `(T, expr)`
    \\ sg `∃rrr t1 t2.
           evaluate ([Op (to_op op) [Op (to_op op) xs; Var acc]],
                      env2, s') = (rrr,t1) ∧
           evaluate ([Op (to_op op) [expr; Var acc]],
                      env2, s') = (rrr,t2) ∧
           state_rel r' t1 ∧ state_rel r' t2`
    >-
     (
      Cases_on `evaluate ([Op (to_op op) xs], env2, s')`
      \\ drule rewrite_op_T_imp \\ fs []
      \\ drule rewrite_op_extra \\ fs []
      \\ ntac 2 strip_tac \\ rveq
      \\ drule evaluate_rewrite_op
      \\ disch_then
        (qspecl_then [`ts ++ ts'`,`op`,`loc`,`T`,`Op (to_op op) [x;y']`] mp_tac)
      \\ simp []
      \\ impl_tac
      >-
        (unabbrev_all_tac
        \\ last_x_assum kall_tac
        \\ fs [evaluate_def] \\ rfs[]
        \\ strip_tac \\ fs[]
        \\ qpat_x_assum`_ = (Rerr _,_)`mp_tac
        \\ simp[case_eq_thms]
        \\ CCONTR_TAC \\ fs[] \\ fs[]
        \\ rveq \\ fs[]
        \\ qpat_x_assum`result_CASE _ _ _  = _`mp_tac
        \\ reverse CASE_TAC
        >- ( imp_res_tac do_app_err \\ fs[] )
        \\ simp[pair_case_eq]
        \\ CCONTR_TAC \\ fs[] \\ rveq
        \\ imp_res_tac state_rel_do_app \\ fs[])
      \\ strip_tac
      \\ simp[evaluate_def]
      \\ reverse CASE_TAC
      >- (
        pop_assum mp_tac
        \\ simp[evaluate_def]
        \\ reverse CASE_TAC \\ fs[]
        >- ( rw[] \\ rw[] )
        \\ reverse CASE_TAC \\ fs[]
        >- ( rw[] \\ rw[] )
        \\ reverse CASE_TAC \\ fs[] )
      \\ reverse CASE_TAC \\ fs[]
      >- (
        imp_res_tac evaluate_IMP_LENGTH \\ fs[LENGTH_EQ_NUM_compute]
        \\ `∃j. EL acc env2 = Number j` by fs [env_rel_def] \\ fs []
        \\ qpat_x_assum`_ = (Rval[h],_)`mp_tac
        \\ simp[evaluate_def]
        \\ simp[case_eq_thms]
        \\ strip_tac
        \\ `∃j. h = Number j`
        by (
          pop_assum mp_tac \\
          Cases_on`op` \\ simp[do_app_def,to_op_def,do_app_aux_def,bvlSemTheory.do_app_def,case_eq_thms] \\
          rw[] )
        \\ qpat_x_assum`_ = Rerr _`mp_tac
        \\ Cases_on`op` \\ simp[do_app_def,to_op_def,do_app_aux_def,bvlSemTheory.do_app_def,case_eq_thms]
        \\ fs[is_rec_or_rec_binop_def] )
      \\ simp[case_eq_thms,PULL_EXISTS]
      \\ Cases_on`a''` \\ fs[]
      \\ imp_res_tac do_app_to_op_state \\ fs[]
      \\ qhdtm_x_assum`evaluate`mp_tac
      \\ simp[evaluate_def,case_eq_thms,PULL_EXISTS] \\ rw[]
      \\ imp_res_tac do_app_to_op_state \\ fs[])
    \\ fs[]
    \\ `r'' = r'`
    by (
      qpat_x_assum`result_CASE q _ _  = _ `mp_tac
      \\ simp[case_eq_thms] \\ rw[]
      \\ imp_res_tac do_app_to_op_state \\ fs[] )
    \\ rveq \\ fs[]
    \\ `r''' = r'`
    by (
      qpat_x_assum`_ = (_,r') `mp_tac
      \\ simp[case_eq_thms] \\ rw[]
      \\ imp_res_tac do_app_to_op_state \\ fs[] )
    \\ rveq \\ fs[]
    \\ qunabbrev_tac `expr`
    \\ simp [evaluate_def]
    \\ once_rewrite_tac [evaluate_APPEND]
    \\ simp [evaluate_def]
    \\ `∃j. EL acc env2 = Number j` by fs [env_rel_def] \\ fs []
    \\ `∃m. do_app (to_op op) [Number j; Number k] t'' =
              Rval (Number m, t'')` by
     (Cases_on `op`
      \\ fs [to_op_def, do_app_def, do_app_aux_def,
             bvlSemTheory.do_app_def, bvl_to_bvi_id])
    \\ simp []
    \\ PURE_TOP_CASE_TAC \\ fs []
    >-
     (rpt (qpat_x_assum `find_code _ _ _ = _` mp_tac)
      \\ fs [find_code_def, optimized_code_def]
      \\ imp_res_tac evaluate_code_mono
      \\ fs[subspt_lookup]
      \\ res_tac \\ fs[]
      \\ res_tac \\ fs[])
    \\ PURE_TOP_CASE_TAC \\ fs []
    \\ IF_CASES_TAC
    >- ( imp_res_tac state_rel_const \\ fs[] )
    \\ fs[optimized_code_def,compile_exp_def,check_exp_def] \\ fs[]
    \\ pairarg_tac \\ fs[] \\ rw[]
    \\ rpt(qhdtm_x_assum`find_code`mp_tac)
    \\ `subspt s.code s_args.code ∧ subspt s'.code t''.code`
    by (
      imp_res_tac evaluate_code_mono
      \\ metis_tac[subspt_trans] )
    \\ fs[subspt_lookup]
    \\ simp[find_code_def]
    \\ res_tac \\ simp[]
    \\ strip_tac \\ rveq
    \\ strip_tac \\ rveq
    \\ qhdtm_x_assum`evaluate`mp_tac
    \\ simp[evaluate_def,find_code_def]
    \\ simp[evaluate_let_wrap]
    \\ `env_rel T (LENGTH a) a (a ++ [op_id_val op] ++ a)` by
     (fs [env_rel_def, EL_LENGTH_APPEND, EL_APPEND1, IS_PREFIX_APPEND]
      \\ Cases_on `op` \\ fs [op_id_val_def])
    \\ first_assum (qspecl_then [`[exp]`, `dec_clock (ticks+1) s_args`] mp_tac)
    \\ impl_tac
    >-
     (imp_res_tac evaluate_clock
      \\ simp [dec_clock_def])
    \\ sg `state_rel (dec_clock (ticks+1) s_args) (dec_clock (ticks+1) t'')`
    >- (imp_res_tac state_rel_const \\ fs [state_rel_with_clock,dec_clock_def])
    \\ sg `ty_rel a (REPLICATE (LENGTH a) Any)`
    >- simp [ty_rel_def, LIST_REL_EL_EQN, EL_REPLICATE]
    \\ rpt (disch_then drule)
    \\ disch_then (qspec_then `loc` mp_tac) \\ fs []
    \\ impl_tac >- (strip_tac \\ fs[])
    \\ rw []
    \\ first_x_assum (qspecl_then [`op`,`n`] mp_tac)
    \\ impl_tac
    \\ pairarg_tac \\ fs [] \\ rw []
    \\ qpat_x_assum `env_rel_ (LENGTH a) _ _` kall_tac
    \\ qpat_x_assum `ty_rel a _` kall_tac
    \\ sg `env_rel T (LENGTH a) a (a ++ [Number m])`
    >- fs [env_rel_def, EL_LENGTH_APPEND, EL_APPEND1, IS_PREFIX_APPEND]
    \\ first_assum (qspecl_then [`[exp]`, `dec_clock (ticks+1) s_args`] mp_tac)
    \\ impl_tac
    >-
     (imp_res_tac evaluate_clock
     \\ simp [dec_clock_def])
    \\ sg `ty_rel a (REPLICATE (LENGTH a) Any)`
    >- simp [ty_rel_def, LIST_REL_EL_EQN, EL_REPLICATE]
    \\ rpt (disch_then drule)
    \\ disch_then (qspec_then `loc` mp_tac) \\ fs []
    \\ impl_tac >- (strip_tac \\ fs[])
    \\ rw []
    \\ first_x_assum (qspecl_then [`op`,`n`] mp_tac)
    \\ impl_tac
    \\ pairarg_tac \\ fs [] \\ rw []
    \\ simp[]
    \\ qhdtm_x_assum`evaluate`mp_tac
    \\ qpat_x_assum`evaluate _ = (rrr',_)`mp_tac
    \\ simp [apply_op_def, to_op_def, evaluate_def,
             EL_LENGTH_APPEND, EL_APPEND1]
    \\ reverse PURE_CASE_TAC \\ fs []
    >- (
      rw[] \\ fs[] \\ rw[]
      \\ CASE_TAC \\ fs[] \\ rveq \\ fs[] )
    \\ sg `∃k. a' = [Number k]`
    >-
     (drule scan_expr_ty_rel
      \\ rpt (disch_then drule)
      \\ rw [])
    \\ fs []
    \\ sg `∀k (s: ('c,'ffi) bviSem$state).
             do_app (to_op op) [op_id_val op; Number k] s = Rval (Number k, s)`
    >-
     (rw []
      \\ Cases_on `op`
      \\ rw [op_id_val_def, to_op_def, do_app_def, do_app_aux_def,
             bvlSemTheory.do_app_def, bvl_to_bvi_id, small_enough_int_def])
    \\ simp[]
    \\ strip_tac \\ rveq \\ fs[]
    \\ Cases_on `op`
    \\ fs [evaluate_def, to_op_def, op_id_val_def, do_app_def,
           do_app_aux_def, bvlSemTheory.do_app_def, bvl_to_bvi_id,
           small_enough_int_def]
    \\ rw [bvl_to_bvi_id] \\ rfs[]
    \\ intLib.COOPER_TAC)
  \\ Cases_on `∃ticks dest xs hdl. h = Call ticks dest xs hdl` \\ fs [] \\ rveq
  >-
   (simp [scan_expr_def, evaluate_def]
   \\ IF_CASES_TAC
   >- fs []
   \\ `dest = NONE ⇒ ¬IS_SOME hdl` by fs []
   \\ qpat_x_assum `¬(_)` kall_tac
   \\ TOP_CASE_TAC
   \\ first_assum (qspecl_then [`xs`, `s`] mp_tac)
   \\ simp [bviTheory.exp_size_def]
   \\ sg `env_rel F acc env1 env2`
   >- fs [env_rel_def]
   \\ rpt (disch_then drule) \\ fs []
   \\ strip_tac
   \\ reverse PURE_TOP_CASE_TAC \\ fs []
   >- (rw [] \\ rfs [] \\ fs[] \\ metis_tac[])
   \\ PURE_TOP_CASE_TAC \\ fs []
   \\ PURE_TOP_CASE_TAC \\ fs []
   \\ IF_CASES_TAC \\ fs []
   >-
    (rw []
     \\ imp_res_tac state_rel_code_rel
     \\ imp_res_tac state_rel_const \\ fs[]
     \\ PURE_TOP_CASE_TAC \\ fs []
     \\ TRY (PURE_CASE_TAC \\ fs [])
     \\ Cases_on `dest` \\ fs []
     \\ metis_tac [code_rel_find_code_NONE, code_rel_find_code_SOME,subspt_refl, state_rel_with_clock])
   \\ rename1 `([exp],args, _ _ s1)`
   \\ Cases_on `dest` \\ fs []
   >-
    (strip_tac
     \\ PURE_TOP_CASE_TAC \\ fs []
     >-
      (imp_res_tac state_rel_code_rel
       \\ metis_tac [code_rel_find_code_NONE])
     \\ PURE_TOP_CASE_TAC \\ fs []
     \\ rpt (qpat_x_assum `find_code _ _ _ = _` mp_tac)
     \\ simp [find_code_def]
     \\ simp[case_eq_thms]
     \\ ntac 2 strip_tac
     \\ rveq
     \\ qpat_x_assum `_ = (r, t)` mp_tac
     \\ PURE_TOP_CASE_TAC \\ fs [] \\ rveq
     \\ imp_res_tac state_rel_code_rel
     \\ qpat_assum`code_rel s1.code _`mp_tac
     \\ simp_tac (srw_ss()) [Once code_rel_def]
     \\ disch_then drule
     \\ simp [compile_exp_def]
     \\ CASE_TAC \\ fs []
     >-
      (rw []
       \\ `env_rel F (LENGTH (FRONT a)) (FRONT a) (FRONT a)` by fs [env_rel_def]
       \\ sg `ty_rel (FRONT a) (REPLICATE (LENGTH (FRONT a)) Any)`
       >- fs [ty_rel_def, LIST_REL_EL_EQN, EL_REPLICATE]
       \\ first_assum (qspecl_then [`[exp]`,`dec_clock (ticks+1) s1`] mp_tac)
       \\ impl_tac
       >-
        (imp_res_tac evaluate_clock
         \\ simp [dec_clock_def])
       \\ rpt (disch_then drule) \\ fs []
       \\ disch_then(qspec_then`dec_clock (ticks+1) t'`mp_tac)
       \\ imp_res_tac state_rel_const
       \\ simp[dec_clock_def,state_rel_with_clock]
       \\ rpt (disch_then drule) \\ fs []
       \\ impl_tac >- (strip_tac \\ fs[])
       \\ rw[] \\ rw[]
       \\ fs[case_eq_thms] \\ rveq \\ fs[])
     \\ rw []
     \\ pairarg_tac \\ fs [] \\ rw []
     \\ imp_res_tac scan_expr_not_Noop
     \\ `arity = LENGTH (FRONT a)` by simp[LENGTH_FRONT]
     \\ pop_assum SUBST_ALL_TAC
     \\ simp [evaluate_let_wrap]
     \\ sg
       `env_rel T (LENGTH (FRONT a)) (FRONT a)
         (FRONT a ++ [op_id_val x] ++ FRONT a)`
     >-
       (fs [env_rel_def, EL_LENGTH_APPEND, EL_APPEND1, IS_PREFIX_APPEND]
        \\ Cases_on `x` \\ fs [op_id_val_def])
     \\ sg `ty_rel (FRONT a) (REPLICATE (LENGTH (FRONT a)) Any)`
     >- fs [ty_rel_def, LIST_REL_EL_EQN, EL_REPLICATE]
     \\ first_x_assum (qspecl_then [`[exp]`,`dec_clock (ticks+1) s1`] mp_tac)
     \\ impl_tac
     >-
      (imp_res_tac evaluate_clock
       \\ simp [dec_clock_def])
     \\ `state_rel (dec_clock (ticks+1) s1) (dec_clock (ticks+1) t')`
     by (
       imp_res_tac state_rel_const \\ fs[state_rel_with_clock, dec_clock_def])
     \\ rpt (disch_then drule) \\ fs[]
     \\ disch_then (qspec_then `loc` mp_tac) \\ fs []
     \\ impl_tac >- (strip_tac \\ fs[])
     \\ rw []
     \\ first_x_assum (qspecl_then [`x`,`n`] mp_tac)
     \\ simp [optimized_code_def, compile_exp_def]
     \\ fs [check_exp_def]
     \\ simp [apply_op_def, evaluate_def]
     \\ simp [EL_LENGTH_APPEND, EL_APPEND1]
     \\ reverse PURE_CASE_TAC \\ fs []
     >- (
       rw[] \\ rw[]
       \\ fs[case_eq_thms]
       \\ rveq \\ fs[]
       \\ imp_res_tac state_rel_const \\ fs[] )
     \\ rw[]
     \\ imp_res_tac state_rel_const \\ fs[]
     \\ imp_res_tac evaluate_IMP_LENGTH \\ fs[LENGTH_EQ_NUM_compute]
     \\ rveq \\ fs[]
     \\ imp_res_tac scan_expr_ty_rel \\ fs[]
     \\ Cases_on`x` \\ fs[to_op_def,op_id_val_def,do_app_def,bvlSemTheory.do_app_def,do_app_aux_def]
     \\ rw[bvl_to_bvi_id])
   \\ PURE_TOP_CASE_TAC \\ fs [] \\ rw []
   \\ PURE_TOP_CASE_TAC \\ fs []
   >- (metis_tac [state_rel_code_rel,code_rel_find_code_SOME])
   \\ PURE_TOP_CASE_TAC \\ fs []
   \\ IF_CASES_TAC
   >- ( imp_res_tac state_rel_const \\ fs[] )
   \\ first_assum (qspecl_then [`[exp]`, `dec_clock (ticks+1) s1`] mp_tac)
   \\ impl_tac
   >-
    (imp_res_tac evaluate_clock
     \\ simp [dec_clock_def])
   \\ `env_rel F acc args args` by fs [env_rel_def]
   \\ sg `ty_rel args (REPLICATE (LENGTH args) Any)`
   >- fs [ty_rel_def, LIST_REL_EL_EQN, EL_REPLICATE]
   \\ rpt (disch_then drule) \\ fs []
   \\ `state_rel (dec_clock (ticks+1) s1) (dec_clock (ticks+1) t')` by (
     imp_res_tac state_rel_const \\
     fs[dec_clock_def,state_rel_with_clock])
   \\ rpt (disch_then drule) \\ fs []
   \\ impl_tac >- (strip_tac \\ fs[])
   \\ rw[]
   \\ rpt (qpat_x_assum `find_code _ _ _ = _` mp_tac)
   \\ simp [find_code_def]
   \\ ntac 4 (PURE_TOP_CASE_TAC \\ fs []) \\ rw []
   \\ imp_res_tac state_rel_code_rel
   \\ qpat_assum `code_rel s1.code _` mp_tac
   \\ simp_tac std_ss [Once code_rel_def]
   \\ disch_then drule \\ fs []
   \\ simp [compile_exp_def]
   \\ CASE_TAC \\ fs []
   >-
    (rw[]
     \\ fs[case_eq_thms] \\ rveq \\ fs[]
     \\ rename1 `([z], aa::env1, s2)`
     \\ first_x_assum (qspecl_then [`[z]`,`s2`] mp_tac)
     \\ impl_tac
     >-
      (imp_res_tac evaluate_clock
       \\ fs [dec_clock_def])
     \\ `env_rel F (LENGTH env1 + 1) (aa::env1) (aa::env2)` by fs [env_rel_def]
     \\ sg `ty_rel (aa::env1) (Any::ts)`
     >- fs [ty_rel_def, LIST_REL_EL_EQN]
     \\ rpt (disch_then drule) \\ rw [])
   \\ rw []
   \\ pairarg_tac \\ fs [] \\ rw []
   \\ imp_res_tac scan_expr_not_Noop
   \\ simp [evaluate_let_wrap]
   \\ first_assum (qspecl_then [`[exp]`,`dec_clock (ticks+1) s1`] mp_tac)
   \\ impl_tac
   >-
    (imp_res_tac evaluate_clock
     \\ fs [dec_clock_def])
   \\ sg `env_rel T (LENGTH a) a (a ++ [op_id_val x'] ++ a)`
   >-
    (Cases_on `x'`
     \\ fs [op_id_val_def, env_rel_def, EL_LENGTH_APPEND,
            EL_APPEND1, IS_PREFIX_APPEND])
   \\ sg `ty_rel a (REPLICATE (LENGTH a) Any)`
   >- fs [ty_rel_def, LIST_REL_EL_EQN, EL_REPLICATE]
   \\ rpt (disch_then drule) \\ fs []
   \\ disch_then (qspec_then `x` mp_tac)
   \\ impl_tac >- (strip_tac \\ fs[])
   \\ rw []
   \\ first_x_assum (qspecl_then [`x'`,`n`] mp_tac)
   \\ simp [optimized_code_def, compile_exp_def, check_exp_def]
   \\ simp [apply_op_def, evaluate_def]
   \\ reverse (PURE_CASE_TAC \\ fs [])
   >-
    (fs[case_eq_thms]
     >- metis_tac[]
     >- (
       rename1 `([z], aa::env1, s2)`
       \\ strip_tac
       \\ first_x_assum (qspecl_then [`[z]`,`s2`] mp_tac)
       \\ impl_tac
       >-
        (imp_res_tac evaluate_clock
         \\ fs [dec_clock_def])
       \\ `env_rel F (LENGTH env1 + 1) (aa::env1) (aa::env2)` by fs [env_rel_def]
       \\ `ty_rel (aa::env1) (Any::ts)` by fs [ty_rel_def]
       \\ rpt (disch_then drule)
       \\ rw [])
     >- metis_tac[])
   \\ simp [EL_LENGTH_APPEND, EL_APPEND1]
   \\ rw[]
   \\ sg `∃k. a' = [Number k]`
   >-
    (drule scan_expr_ty_rel
     \\ rpt (disch_then drule)
     \\ rw [])
   \\ rw []
   \\ rename1`to_op op`
   \\ Cases_on`op` \\ fs[to_op_def,op_id_val_def,do_app_def,do_app_aux_def,bvlSemTheory.do_app_def]
   \\ rw[bvl_to_bvi_id])
  \\ Cases_on `h` \\ fs []);

val input_condition_def = Define`
  input_condition next prog ⇔
    EVERY (free_names next o FST) prog ∧
   ALL_DISTINCT (MAP FST prog) ∧
   EVERY ($~ o in_ns_2 o FST) prog ∧
   in_ns_2 next`;

val evaluate_compile_prog = Q.store_thm ("evaluate_compile_prog",
  `input_condition next prog ∧
   (∀n next cfg prog. co n = ((next,cfg),prog) ⇒ input_condition next prog) ∧
   (∀n. MEM n (MAP FST (SND (compile_prog next prog))) ∧ in_ns_2 n ⇒ n < FST (FST (co 0))) ∧
   evaluate ([Call 0 (SOME start) [] NONE], [],
             initial_state ffi0 (fromAList prog) co (mk_cc cc) k) = (r, s) ∧
   r ≠ Rerr (Rabort Rtype_error) ⇒
   ∃s2.
     evaluate
      ([Call 0 (SOME start) [] NONE], [],
        initial_state ffi0 (fromAList (SND (compile_prog next prog))) (mk_co co) cc k)
      = (r, s2) ∧
     state_rel s s2`,
  rw [input_condition_def]
  \\ qmatch_asmsub_abbrev_tac `(es,env,st1)`
  \\ `env_rel F 0 env env` by fs [env_rel_def]
  \\ qabbrev_tac `ts: v_ty list = []`
  \\ `ty_rel env ts` by fs [ty_rel_def, Abbr`ts`]
  \\ Cases_on `compile_prog next prog` \\ fs []
  \\ drule (GEN_ALL compile_prog_code_rel)
  \\ simp[]
  \\ strip_tac
  \\ qmatch_goalsub_abbrev_tac`(es,env,st2)`
  \\ `state_rel st1 st2`
  by (
    simp[state_rel_def,Abbr`st1`,Abbr`st2`,domain_fromAList]
    \\ reverse conj_tac >- (
      rw[] \\
      last_x_assum(qspec_then`n`mp_tac)
      \\ pairarg_tac \\ fs[] )
    \\ match_mp_tac (GEN_ALL compile_prog_namespace_rel)
    \\ asm_exists_tac \\ fs[] )
  \\ drule evaluate_rewrite_tail
  \\ disch_then (qspec_then `F` drule)
  \\ rpt (disch_then drule) \\ fs []);

val compile_prog_semantics = Q.store_thm ("compile_prog_semantics",
  `input_condition n prog ∧
   (∀k n cfg prog. co k = ((n,cfg),prog) ⇒ input_condition n prog) ∧
   (∀k. MEM k (MAP FST prog2) ∧ in_ns_2 k ⇒ k < FST(FST (co 0))) ∧
   SND (compile_prog n prog) = prog2 ∧
   semantics ffi (fromAList prog) co (mk_cc cc) start ≠ Fail ⇒
   semantics ffi (fromAList prog) co (mk_cc cc) start =
   semantics ffi (fromAList prog2) (mk_co co) cc start`,
   simp [GSYM AND_IMP_INTRO]
   \\ ntac 4 strip_tac
   \\ fs[AND_IMP_INTRO]
   \\ simp [Ntimes semantics_def 2]
   \\ IF_CASES_TAC \\ fs []
   \\ DEEP_INTRO_TAC some_intro \\ simp []
   \\ conj_tac >- (
     gen_tac \\ strip_tac \\ rveq \\ simp []
     \\ simp [semantics_def]
     \\ IF_CASES_TAC \\ fs [] >- (
       qpat_x_assum`_ = (r,s)`kall_tac
       \\ first_assum(qspec_then`k'`mp_tac)
       \\ disch_then(subterm (fn tm => Cases_on`^(assert(has_pair_type)tm)`) o concl)
       \\ drule (GEN_ALL evaluate_compile_prog)
       \\ rpt(disch_then drule)
       \\ first_x_assum (qspec_then `k'` strip_assume_tac)
       \\ rfs [] \\ CCONTR_TAC \\ fs [] \\ rfs[] \\ fs[] \\ rfs[])
     \\ DEEP_INTRO_TAC some_intro \\ simp []
     \\ conj_tac >- (
       gen_tac \\ strip_tac \\ rveq \\ fs []
       \\ qmatch_assum_abbrev_tac `evaluate (opts,[],sopt) = _`
       \\ qmatch_assum_abbrev_tac `evaluate (exps,[],st) = (r,s)`
       \\ qspecl_then [`opts`,`[]`,`sopt`] mp_tac evaluate_add_to_clock_io_events_mono
       \\ qspecl_then [`exps`,`[]`,`st`] mp_tac (INST_TYPE[alpha|->``:num#'a``]evaluate_add_to_clock_io_events_mono)
       \\ simp [inc_clock_def, Abbr`sopt`, Abbr`st`]
       \\ ntac 2 strip_tac
       \\ Cases_on `s.ffi.final_event` \\ fs [] >- (
         Cases_on `s'.ffi.final_event` \\ fs [] >- (
           unabbrev_all_tac
           \\ drule (GEN_ALL evaluate_compile_prog) \\ simp []
           \\ rpt(disch_then drule)
           \\ impl_tac
           >- (spose_not_then strip_assume_tac \\ fs []
               \\ fs [evaluate_def]
               \\ every_case_tac \\ fs [] \\ rveq \\ fs [])
           \\ strip_tac
           \\ drule evaluate_add_clock
           \\ impl_tac
           >- (every_case_tac \\ fs [])
           \\ disch_then (qspec_then `k'` mp_tac) \\ simp [inc_clock_def]
           \\ qpat_x_assum`_ = (r',s')`assume_tac
           \\ drule evaluate_add_clock
           \\ impl_tac
           >- (spose_not_then strip_assume_tac \\ fs [evaluate_def])
           \\ disch_then (qspec_then `k` mp_tac) \\ simp [inc_clock_def]
           \\ ntac 2 strip_tac \\ rveq \\ fs []
           \\ imp_res_tac state_rel_const
           \\ fs [state_component_equality]
           \\ every_case_tac \\ fs [])
         \\ qpat_x_assum `∀extra._` mp_tac
         \\ first_x_assum (qspec_then `k'` assume_tac)
         \\ first_assum (subterm (fn tm => Cases_on`^(assert has_pair_type tm)`) o concl)
         \\ strip_tac \\ fs []
         \\ unabbrev_all_tac
         \\ drule (GEN_ALL evaluate_compile_prog)
         \\ ntac 3 (disch_then drule)
         \\ impl_tac >- (
          rpt(first_x_assum(qspec_then`k+k'`mp_tac))
          \\ rw[] \\ strip_tac \\ fs[])
         \\ strip_tac \\ fs[]
         \\ first_x_assum(qspec_then`k`mp_tac)
         \\ simp[] \\ strip_tac
         \\ Cases_on`r` \\ fs[]
         \\ ntac 3 (qhdtm_x_assum `evaluate` mp_tac)
         \\ drule evaluate_add_clock
         \\ simp[]
         \\ disch_then(qspec_then`k'`mp_tac)
         \\ simp[inc_clock_def] \\ rw[]
         \\ imp_res_tac state_rel_const \\ fs[])
       \\ qpat_x_assum `∀extra._` mp_tac
       \\ first_x_assum (qspec_then `k'` assume_tac)
       \\ first_assum (subterm (fn tm => Cases_on`^(assert has_pair_type tm)`) o concl)
       \\ fs []
       \\ unabbrev_all_tac
       \\ strip_tac
       \\ drule (GEN_ALL evaluate_compile_prog)
       \\ ntac 3 (disch_then drule)
       \\ impl_tac
       >-
         (rpt(last_x_assum (qspec_then `k + k'` mp_tac))
         \\ fs [] \\ strip_tac
         \\ spose_not_then assume_tac \\ rveq \\ fs []
         \\ fs[])
       \\ strip_tac \\ rveq \\ fs []
       \\ reverse (Cases_on `s'.ffi.final_event`) \\ fs [] \\ rfs []
       >-
         (first_x_assum (qspec_then `k` mp_tac)
         \\ fs [ADD1]
         \\ strip_tac
         \\ imp_res_tac state_rel_const
         \\ fs [] \\ rfs []
         \\ rw[] \\ fs[])
       \\ ntac 2 (qhdtm_x_assum `evaluate` mp_tac)
       \\ drule evaluate_add_clock
       \\ impl_tac >- (strip_tac \\ fs [])
       \\ disch_then (qspec_then `k` mp_tac)
       \\ simp [inc_clock_def]
       \\ ntac 3 strip_tac \\ rveq
       \\ imp_res_tac state_rel_const
       \\ fs[] \\ rfs[])
     \\ first_assum (subterm (fn tm => Cases_on`^(assert(has_pair_type)tm)`) o concl)
     \\ drule (GEN_ALL evaluate_compile_prog)
     \\ ntac 3 (disch_then drule) \\ simp []
     \\ impl_tac
     >-
       (spose_not_then assume_tac
       \\ rpt(last_x_assum (qspec_then `k` mp_tac))
       \\ fs [])
     \\ strip_tac
     \\ asm_exists_tac
     \\ imp_res_tac state_rel_const \\ fs[]
     \\ TOP_CASE_TAC \\ fs[]
     \\ TOP_CASE_TAC \\ fs[])
   \\ strip_tac
   \\ simp [semantics_def]
   \\ IF_CASES_TAC \\ fs [] >- (
     qpat_x_assum`∀k. _`mp_tac
     \\ first_x_assum (qspec_then `k` assume_tac)
     \\ strip_tac \\ rfs[]
     \\ drule (GEN_ALL evaluate_compile_prog)
     \\ rveq \\ disch_then drule
     \\ qmatch_asmsub_abbrev_tac`FST p ≠ Rerr _`
     \\ Cases_on`p` \\ pop_assum(assume_tac o SYM o SIMP_RULE std_ss [markerTheory.Abbrev_def])
     \\ disch_then drule
     \\ disch_then drule
     \\ impl_tac >- (strip_tac \\ fs[])
     \\ strip_tac \\ fs[] \\ rfs[])
   \\ DEEP_INTRO_TAC some_intro \\ simp []
   \\ conj_tac >- (
    spose_not_then assume_tac \\ rw []
    \\ qpat_x_assum`∀k. _`mp_tac
    \\ first_assum (qspec_then `k` mp_tac)
    \\ (fn g => subterm (fn tm => Cases_on`^(assert (can dest_prod o type_of) tm)` g) (#2 g))
    \\ strip_tac
    \\ drule (GEN_ALL evaluate_compile_prog)
    \\ rveq
    \\ (disch_then drule)
    \\ (disch_then drule)
    \\ (disch_then drule)
    \\ impl_tac >- (
      strip_tac \\ fs[]
      \\ rpt(first_x_assum(qspec_then`k`mp_tac))\\ simp[] )
    \\ strip_tac
    \\ qmatch_assum_rename_tac `state_rel rr _`
    \\ reverse (Cases_on `rr.ffi.final_event`) >- (
      first_x_assum(qspec_then`k`mp_tac) \\ simp[] )
    \\ disch_then(qspec_then`k`mp_tac)
    \\ strip_tac \\ rfs[] \\ rveq \\ fs[]
    \\ imp_res_tac state_rel_const \\ fs[])
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
  \\ rpt gen_tac \\ rveq
  \\ drule (GEN_ALL evaluate_compile_prog)
  \\ rpt(disch_then drule)
  \\ disch_then(mp_tac o CONV_RULE(RESORT_FORALL_CONV(sort_vars["start","k","ffi0","cc"])))
  \\ disch_then (qspecl_then [`start`,`k`,`ffi`,`cc`] mp_tac)
  \\ qmatch_goalsub_abbrev_tac`p = (_,_)`
  \\ Cases_on`p` \\ pop_assum(assume_tac o SYM o SIMP_RULE std_ss [markerTheory.Abbrev_def])
  \\ simp []
  \\ impl_tac >- (
    strip_tac
    \\ rpt(last_x_assum (qspec_then `k` mp_tac))
    \\ fs [])
  \\ strip_tac
  \\ imp_res_tac state_rel_const
  \\ conj_tac \\ rw []
  \\ qexists_tac `k` \\ fs []);

val _ = export_theory();
