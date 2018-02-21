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

val get_bin_args_SOME = Q.store_thm ("get_bin_args_SOME[simp]",
  `∀exp q. get_bin_args exp = SOME q
    ⇔
    ∃e1 e2 op. q = (e1, e2) ∧ exp = Op op [e1; e2]`,
  Cases \\ rw [get_bin_args_def]
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
   evaluate ([x], env, (s: 'ffi bviSem$state)) = (r, t) ⇒
     ∃k. r = Rval [Number k] ∧ s = t ∧
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
  `∀ts op loc exp env (s: 'ffi bviSem$state) r t p exp2.
     evaluate ([exp], env, s) = (r, t) ∧
     r ≠ Rerr (Rabort Rtype_error) ∧
     ty_rel env ts ∧
     rewrite_op ts op loc exp = (p, exp2) ==>
       if ¬p then exp2 = exp else
         evaluate ([exp2], env, s) = (r, t)`,
  ho_match_mp_tac rewrite_op_ind \\ rw [] \\ rw []
  \\ pop_assum mp_tac
  \\ once_rewrite_tac [rewrite_op_def]
  \\ rw [bool_case_eq, case_eq_thms, pair_case_eq]
  \\ rpt (pairarg_tac \\ fs []) \\ rfs []
  \\ fs [evaluate_def, assoc_swap_def, apply_op_def] \\ rveq
  \\ fs [bool_case_eq, case_eq_thms, case_elim_thms, pair_case_eq] \\ rveq
  \\ imp_res_tac evaluate_SING_IMP \\ fs [] \\ rveq
  \\ Cases_on `r1` \\ Cases_on `r2` \\ fs []
  \\ rpt (first_x_assum drule \\ fs []) \\ rw []
  \\ fs [evaluate_def, case_eq_thms, case_elim_thms, pair_case_eq] \\ rw []
  \\ imp_res_tac no_err_correct \\ fs [] \\ rveq
  \\ Cases_on `op` \\ fs [to_op_def]
  \\ fs [do_app_def, do_app_aux_def, bvlSemTheory.do_app_def]
  \\ fs [case_eq_thms, case_elim_thms, pair_case_eq]
  \\ rveq \\ fs [bvl_to_bvi_id]
  \\ rveq \\ fs [bvl_to_bvi_id]
  \\ TRY intLib.COOPER_TAC
  \\ fs [is_rec_or_rec_binop_def, no_err_def, is_rec_def, get_bin_args_def]);

(* TODO for append, parametrise on op *)
val env_rel_def = Define `
  env_rel opt acc env1 env2 ⇔
    isPREFIX env1 env2 ∧
    (opt ⇒
      LENGTH env1 = acc ∧
      LENGTH env2 > acc ∧
      ∃k. EL acc env2 = Number k)`;

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
  \\ fs [compile_exp_def]
  \\ CASE_TAC \\ fs [] \\ rw []
  \\ pairarg_tac \\ fs []);

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

val rewrite_op_exp_size = Q.store_thm ("rewrite_op_exp_size",
  `∀ts op loc exp p exp2.
    rewrite_op ts op loc exp = (p, exp2) ⇒
      exp_size exp = exp_size exp2`,
  ho_match_mp_tac rewrite_op_ind
  \\ rw []
  \\ pop_assum mp_tac
  \\ once_rewrite_tac [rewrite_op_def]
  \\ fs [case_eq_thms, pair_case_eq, case_elim_thms, bool_case_eq] \\ rw []
  \\ rpt (pairarg_tac \\ fs [])
  \\ rfs [] \\ rveq
  \\ fs [bool_case_eq, assoc_swap_def, apply_op_def, case_eq_thms]
  \\ fs [to_op_def, op_eq_to_op] \\ rveq
  \\ fs [bviTheory.exp_size_def]);

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
  `is_rec_or_rec_binop ts loc op (Op (to_op op) [e1;e2]) ⇔
   op ≠ Noop ∧ is_rec loc e1 ∧ no_err ts e2`,
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

val EVERY_LAST1 = Q.store_thm("EVERY_LAST1",
  `!xs y. EVERY P xs /\ LAST1 xs = SOME y ==> P y`,
  ho_match_mp_tac LAST1_ind \\ rw [LAST1_def] \\ fs []);

val scan_expr_LENGTH = Q.store_thm ("scan_expr_LENGTH",
  `∀ts loc xs ys.
     scan_expr ts loc xs = ys ⇒
       EVERY (λy. LENGTH (FST y) = LENGTH ts) ys`,
  ho_match_mp_tac scan_expr_ind
  \\ rw [scan_expr_def] \\ fs []
  \\ rpt (pairarg_tac \\ fs [])
  \\ TRY (PURE_CASE_TAC \\ fs [case_eq_thms, case_elim_thms, pair_case_eq])
  \\ rw [try_update_LENGTH]
  \\ fs [LAST1_def, case_eq_thms] \\ rw [] \\ fs []
  \\ imp_res_tac EVERY_LAST1 \\ fs []);

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

val LAST1_thm = Q.store_thm("LAST1_thm",
  `!xs. LAST1 xs = NONE <=> xs = []`,
  Induct \\ rw [LAST1_def]
  \\ Cases_on `xs` \\ fs [LAST1_def]);

val scan_expr_ty_rel = Q.store_thm ("scan_expr_ty_rel",
  `∀ts loc xs env ys (s: 'ffi bviSem$state) vs (t: 'ffi bviSem$state).
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
   (fs [case_eq_thms, pair_case_eq, case_elim_thms, PULL_EXISTS] \\ rw []
    \\ rpt (pairarg_tac \\ fs [])
    \\ res_tac \\ fs [] \\ rw [])
  >- (* Var *)
   (rw [] \\ fs [ty_rel_def, LIST_REL_EL_EQN])
  \\ strip_tac
  \\ rpt gen_tac
  \\ rpt (pairarg_tac \\ fs [])
  \\ TRY (* All but Let, Op *)
   (fs [case_eq_thms, pair_case_eq, case_elim_thms, bool_case_eq, PULL_EXISTS]
    \\ rw []
    \\ res_tac \\ fs [] \\ rw []
    \\ imp_res_tac evaluate_SING_IMP \\ fs []
    \\ imp_res_tac scan_expr_LENGTH \\ fs []
    \\ metis_tac [ty_rel_decide_ty])
  >- (* Let *)
   (fs [case_eq_thms, pair_case_eq, case_elim_thms, bool_case_eq]
    \\ fs [PULL_EXISTS] \\ rw []
    \\ imp_res_tac evaluate_SING_IMP \\ fs [] \\ rveq
    \\ imp_res_tac evaluate_IMP_LENGTH \\ fs [] \\ rveq
    \\ qpat_x_assum `scan_expr _ _ [x] = _` mp_tac
    \\ CASE_TAC
    >-
     (fs [LAST1_thm]
      \\ res_tac \\ rfs [] \\ rveq
      \\ fs [LENGTH_EQ_NUM_compute])
    \\ strip_tac
    \\ fs [case_eq_thms]
    \\ res_tac \\ fs []
    \\ sg `ty_rel vs' (MAP (FST o SND) (scan_expr ts loc xs))`
    >- fs [ty_rel_def]
    \\ sg `ty_rel env (FST x')`
    >-
     (fs [ty_rel_def]
      \\ imp_res_tac EVERY_LAST1 \\ fs [])
    \\ fs [ty_rel_APPEND]
    \\ fs [ty_rel_def, LIST_REL_EL_EQN] \\ rw []
    \\ rfs [EL_DROP]
    \\ `n + LENGTH xs < LENGTH tu` by fs []
    \\ res_tac \\ fs []
    \\ rfs [EL_APPEND1, EL_APPEND2, EL_LENGTH_APPEND])
  \\ fs [case_eq_thms, case_elim_thms, pair_case_eq, bool_case_eq, PULL_EXISTS]
  \\ rveq \\ fs []
  \\ reverse conj_tac \\ fs []
  >-
   (Cases_on `op`
    \\ fs [do_app_def, do_app_aux_def, bvlSemTheory.do_app_def,
           is_arith_op_def, is_const_def]
    \\ fs [case_eq_thms, case_elim_thms, bool_case_eq, pair_case_eq]
    \\ fs [small_enough_int_def, small_int_def] \\ rw [])
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
       (fs [evaluate_def, do_app_def, do_app_aux_def, bvlSemTheory.do_app_def]
        \\ Cases_on `op` \\ fs [is_arith_op_def, is_num_rel_def]
        \\ fs [case_eq_thms, case_elim_thms, pair_case_eq, bool_case_eq, PULL_EXISTS]
        \\ fs [bvl_to_bvi_id]
        \\ rw [] \\ fs [])
      \\ fs [ty_rel_def, LIST_REL_EL_EQN, index_of_def]
      \\ fs [try_update_LENGTH, EL_MAP2] \\ rw []
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
    \\ fs [ty_rel_def, LIST_REL_EL_EQN, index_of_def,
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
  \\ fs [ty_rel_def, LIST_REL_EL_EQN, index_of_def,
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
  `∀loc next op acc ts exp tt ty p exp2 r opr.
   rewrite (loc,next,op,acc,ts) exp = (p,exp2) ∧
   op ≠ Noop ∧
   scan_expr ts loc [exp] = [(tt, ty, r, opr)] ⇒
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
           (∃op' tt ty r.
             scan_expr ts loc [HD xs] = [(tt, ty, r, SOME op')] ∧
             op' ≠ Noop ∧ ty = Int) ⇒
               let (lr, x) = rewrite (loc, n, op, acc, ts) (HD xs) in
                 evaluate ([x], env2, s with code := c) =
                 evaluate ([apply_op op (HD xs) (Var acc)],
                   env2, s with code := c))`,
  ho_match_mp_tac evaluate_complete_ind
  \\ ntac 2 (rpt gen_tac \\ strip_tac)
  \\ Cases_on `xs` \\ fs []
  >- fs [evaluate_def]
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
    \\ IF_CASES_TAC \\ fs [] \\ rw []
    >-
     (simp [rewrite_def, evaluate_def, apply_op_def]
      \\ rpt (pairarg_tac \\ fs [])
      \\ rw [evaluate_def])
    >-
     (first_x_assum (qspecl_then [`[x1]`,`dec_clock 1 s`] mp_tac)
      \\ impl_tac
      >- fs [bviTheory.exp_size_def, evaluate_clock, dec_clock_def]
      \\ `env_rel F acc env1 env2` by fs [env_rel_def]
      \\ `code_rel (dec_clock 1 s).code c` by fs [dec_clock_def]
      \\ rpt (disch_then drule) \\ fs [])
    \\ simp [rewrite_def]
    \\ rpt (pairarg_tac \\ fs []) \\ rw []
    \\ first_x_assum (qspecl_then [`[x1]`,`dec_clock 1 s`] mp_tac)
    \\ impl_tac
    >- fs [bviTheory.exp_size_def, evaluate_clock, dec_clock_def]
    \\ `code_rel (dec_clock 1 s).code c` by fs [dec_clock_def]
    \\ rpt (disch_then drule) \\ fs []
    \\ disch_then (qspec_then `loc` mp_tac) \\ rw []
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
    \\ rw [] \\ fs [])
  \\ Cases_on `∃xs x1. h = Let xs x1` \\ fs [] \\ rveq
  >-
   (simp [evaluate_def]
    \\ `env_rel F acc env1 env2` by fs [env_rel_def]
    \\ PURE_TOP_CASE_TAC \\ fs []
    \\ reverse PURE_TOP_CASE_TAC \\ fs []
    \\ strip_tac
    >-
     (rveq \\ fs []
      \\ first_assum (qspecl_then [`xs`,`s`] mp_tac)
      \\ simp [bviTheory.exp_size_def]
      \\ rpt (disch_then drule) \\ fs [] \\ rw []
      \\ pairarg_tac \\ fs []
      \\ fs [rewrite_def, scan_expr_def]
      \\ rpt (pairarg_tac \\ fs [])
      \\ rw [evaluate_def, apply_op_def])
    \\ `env_rel opt (acc+LENGTH a) (a++env1) (a++env2)` by
      (Cases_on `opt`
      \\ fs [env_rel_def, IS_PREFIX_LENGTH]
      \\ fs [EL_APPEND2])
    \\ first_assum (qspecl_then [`xs`,`s`] mp_tac)
    \\ simp [bviTheory.exp_size_def]
    \\ rpt (disch_then drule) \\ fs []
    \\ strip_tac
    \\ imp_res_tac evaluate_clock
    \\ imp_res_tac evaluate_code_const
    \\ rename1 `evaluate (xs,env,s) = (Rval a, s2)`
    \\ qabbrev_tac `ttt = scan_expr ts loc xs`
    \\ sg `ty_rel (a ++ env) (MAP (FST o SND) ttt ++ (case LAST1 ttt of SOME z => FST z | NONE => ts))`
    >-
     (match_mp_tac ty_rel_APPEND
      \\ drule scan_expr_ty_rel
      \\ disch_then (qspecl_then [`loc`,`xs`,`ttt`,`s`] mp_tac)
      \\ qunabbrev_tac `ttt`
      \\ simp []
      \\ strip_tac
      \\ fs [ty_rel_def]
      \\ CASE_TAC \\ fs []
      \\ imp_res_tac EVERY_LAST1 \\ fs [])
    \\ qunabbrev_tac `ttt`
    \\ first_assum (qspecl_then [`[x1]`,`s2`] mp_tac)
    \\ impl_tac
    >- simp [bviTheory.exp_size_def]
    \\ imp_res_tac evaluate_code_const \\ fs []
    \\ rpt (disch_then drule)
    \\ disch_then (qspec_then `loc` mp_tac)
    \\ rw []
    \\ pairarg_tac \\ fs []
    \\ first_x_assum drule
    \\ fs [scan_expr_def]
    \\ rpt (pairarg_tac \\ fs []) \\ rveq
    \\ qpat_x_assum `rewrite _ (Let _ _) = _` mp_tac
    \\ simp [rewrite_def]
    \\ pairarg_tac \\ fs [] \\ rw []
    \\ `acc < LENGTH env2` by fs [env_rel_def]
    \\ `LENGTH xs = LENGTH a` by metis_tac [evaluate_IMP_LENGTH]
    \\ pop_assum (fn th => fs [th]) \\ rw []
    \\ simp [apply_op_def, evaluate_def, EL_LENGTH_APPEND, EL_APPEND2])
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
      \\ rpt (disch_then drule) \\ fs [] \\ rw []
      \\ pairarg_tac \\ fs []
      \\ fs [rewrite_def]
      \\ rpt (pairarg_tac \\ fs [])
      \\ rw [evaluate_def, apply_op_def])
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
       \\ imp_res_tac evaluate_code_const \\ fs []
       \\ disch_then drule
       \\ disch_then (qspec_then `T` drule)
       \\ rpt (disch_then drule)
       \\ disch_then (qspec_then `loc` mp_tac) \\ rw []
       \\ first_x_assum drule
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
       \\ rw [evaluate_def, apply_op_def])
     \\ IF_CASES_TAC \\ fs [] \\ rw []
     \\ first_assum (qspecl_then [`[x3]`,`s2`] mp_tac)
     \\ impl_tac
     >-
      (imp_res_tac evaluate_clock
       \\ simp [bviTheory.exp_size_def])
     \\ imp_res_tac evaluate_code_const \\ fs []
     \\ disch_then drule
     \\ disch_then (qspec_then `T` drule)
     \\ rpt (disch_then drule)
     \\ disch_then (qspec_then `loc` mp_tac) \\ rw []
     \\ first_x_assum drule
     \\ impl_tac
     >-
      (fs [optimized_code_def]
       \\ imp_res_tac scan_expr_not_Noop
       \\ drule rewrite_scan_expr
       \\ rpt (disch_then drule)
       \\ PURE_CASE_TAC \\ fs []
       \\ imp_res_tac scan_expr_not_Noop)
     \\ pairarg_tac \\ fs []
     \\ rw [evaluate_def, apply_op_def])
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
        \\ imp_res_tac evaluate_code_const \\ fs []
        \\ disch_then drule
        \\ disch_then (qspec_then `T` drule)
        \\ rpt (disch_then drule)
        \\ disch_then (qspec_then `loc` mp_tac) \\ rw []
        \\ first_x_assum drule
        \\ impl_tac
        >-
         (fs [optimized_code_def]
          \\ imp_res_tac scan_expr_not_Noop
          \\ qpat_x_assum `rewrite _ x3 = _` kall_tac
          \\ drule rewrite_scan_expr
          \\ rpt (disch_then drule)
          \\ PURE_CASE_TAC \\ fs [])
        \\ pairarg_tac \\ fs []
        \\ rw [evaluate_def, apply_op_def])
      \\ IF_CASES_TAC \\ fs [] \\ rw []
      \\ first_assum (qspecl_then [`[x3]`,`s2`] mp_tac)
      \\ impl_tac
      >-
       (imp_res_tac evaluate_clock
        \\ simp [bviTheory.exp_size_def])
      \\ imp_res_tac evaluate_code_const \\ fs []
      \\ rpt (disch_then drule)
      \\ rw [evaluate_def, apply_op_def])
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
        \\ imp_res_tac evaluate_code_const \\ fs []
        \\ rpt (disch_then drule)
        \\ rw [evaluate_def, apply_op_def])
      \\ IF_CASES_TAC \\ fs [] \\ rw []
      \\ first_assum (qspecl_then [`[x3]`,`s2`] mp_tac)
      \\ impl_tac
      >-
       (imp_res_tac evaluate_clock
        \\ simp [bviTheory.exp_size_def])
      \\ imp_res_tac evaluate_code_const \\ fs []
      \\ disch_then drule
      \\ disch_then (qspec_then `T` drule)
      \\ rpt (disch_then drule)
      \\ disch_then (qspec_then `loc` mp_tac) \\ rw []
      \\ first_x_assum drule
      \\ impl_tac
      >-
       (fs [optimized_code_def]
        \\ imp_res_tac scan_expr_not_Noop
        \\ drule rewrite_scan_expr
        \\ rpt (disch_then drule)
        \\ PURE_CASE_TAC \\ fs []
        \\ imp_res_tac scan_expr_not_Noop)
      \\ pairarg_tac \\ fs []
      \\ rw [evaluate_def, apply_op_def])
    \\ qpat_x_assum `_ = (r, t)` mp_tac
    \\ IF_CASES_TAC \\ fs []
    >-
     (strip_tac
      \\ first_assum (qspecl_then [`[x2]`,`s2`] mp_tac)
      \\ impl_tac
      >-
       (imp_res_tac evaluate_clock
        \\ simp [bviTheory.exp_size_def])
      \\ imp_res_tac evaluate_code_const \\ fs []
      \\ rpt (disch_then drule)
      \\ rw [evaluate_def, apply_op_def])
    \\ IF_CASES_TAC \\ fs [] \\ rw []
    \\ first_assum (qspecl_then [`[x3]`,`s2`] mp_tac)
    \\ impl_tac
    >-
     (imp_res_tac evaluate_clock
      \\ simp [bviTheory.exp_size_def])
    \\ imp_res_tac evaluate_code_const \\ fs []
    \\ rpt (disch_then drule)
    \\ rw [evaluate_def, apply_op_def])
  \\ Cases_on `∃xs op. h = Op op xs` \\ fs [] \\ rveq
  >-
   (simp [evaluate_def]
    \\ PURE_TOP_CASE_TAC \\ fs []
    \\ strip_tac
    \\ conj_tac
    >-
     (first_x_assum (qspecl_then [`xs`, `s`] mp_tac)
      \\ simp [bviTheory.exp_size_def]
      \\ `env_rel F acc env1 env2` by fs [env_rel_def]
      \\ rpt (disch_then drule)
      \\ disch_then (qspec_then `loc` mp_tac) \\ fs []
      \\ rw []
      \\ rpt (PURE_FULL_CASE_TAC \\ fs []) \\ rw []
      \\ imp_res_tac code_rel_domain
      \\ imp_res_tac evaluate_code_const
      \\ imp_res_tac do_app_with_code
      \\ imp_res_tac do_app_with_code_err
      \\ imp_res_tac do_app_err
      \\ fs [])
    \\ rw []
    \\ pairarg_tac \\ fs []
    \\ pop_assum mp_tac
    \\ simp [rewrite_def]
    \\ PURE_TOP_CASE_TAC \\ fs []
    \\ PURE_TOP_CASE_TAC \\ fs []
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
    \\ impl_tac
    >- (rpt (PURE_FULL_CASE_TAC \\ fs []) \\ rw [])
    \\ rw []
    \\ qmatch_asmsub_abbrev_tac `(T, expr)`
    \\ Cases_on `evaluate ([Op (to_op op) xs], env1, s)`
    \\ drule evaluate_rewrite_op
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
      \\ rpt (PURE_FULL_CASE_TAC \\ fs []) \\ rw []
      \\ imp_res_tac do_app_err)
    \\ Cases_on `find_code (SOME loc) a s_args.code` \\ fs []
    \\ Cases_on `x` \\ fs []
    \\ Cases_on `evaluate ([y], env1, s_args)`
    \\ drule (GEN_ALL no_err_correct)
    \\ rpt (disch_then drule)
    \\ strip_tac
    \\ sg `code_rel s_args.code c`
    >- (imp_res_tac evaluate_code_const \\ fs [])
    \\ first_assum (qspecl_then [`[y]`,`s_args`] mp_tac)
    \\ impl_tac
    >-
     (imp_res_tac evaluate_clock
     \\ imp_res_tac rewrite_op_exp_size
     \\ fs [bviTheory.exp_size_def])
    \\ rpt (disch_then drule) \\ fs []
    \\ strip_tac \\ fs [] \\ rveq
    \\ rename1 `s_args.clock`
    \\ IF_CASES_TAC \\ fs []
    >-
     (rw [Abbr `goal`, evaluate_def]
      \\ once_rewrite_tac [evaluate_APPEND]
      \\ simp [evaluate_def]
      \\ `∃j. EL acc env2 = Number j` by fs [env_rel_def] \\ fs []
      \\ `∃m. do_app (to_op op) [Number j; Number k] (s_args with code := c) =
                Rval (Number m, s_args with code := c)` by
       (Cases_on `op`
        \\ fs [to_op_def, do_app_def, do_app_aux_def,
               bvlSemTheory.do_app_def, bvl_to_bvi_id])
      \\ simp []
      \\ PURE_TOP_CASE_TAC \\ fs []
      >-
       (rpt (qpat_x_assum `find_code _ _ _ = _` mp_tac)
        \\ imp_res_tac evaluate_code_const
        \\ fs [find_code_def, optimized_code_def])
      \\ PURE_CASE_TAC \\ fs []
      \\ rpt (qpat_x_assum `find_code _ _ _ = _` mp_tac)
      \\ imp_res_tac evaluate_code_const
      \\ fs [optimized_code_def, find_code_def]
      \\ rw []
      \\ rpt (PURE_FULL_CASE_TAC \\ fs []) \\ rw []
      \\ imp_res_tac do_app_err \\ fs [])
    \\ PURE_CASE_TAC \\ fs []
    \\ strip_tac
    \\ qunabbrev_tac `goal`
    \\ qmatch_asmsub_abbrev_tac `(T, expr)`
    \\ sg `evaluate ([Op (to_op op) [Op (to_op op) xs; Var acc]],
                      env2, s with code := c) =
           evaluate ([Op (to_op op) [expr; Var acc]],
                      env2, s with code := c)`
    >-
     (qabbrev_tac `ts' = REPLICATE (LENGTH env2 - LENGTH env1) Any`
      \\ sg `ty_rel env2 (ts ++ ts')`
      >-
       (fs [ty_rel_def, LIST_REL_EL_EQN, Abbr`ts'`]
        \\ `LENGTH ts < LENGTH env2` by fs [env_rel_def, IS_PREFIX_LENGTH]
        \\ rw []
        \\ Cases_on `n' < LENGTH ts`
        >-
         (fs [EL_APPEND1, env_rel_def]
          \\ imp_res_tac is_prefix_el \\ fs []
          \\ metis_tac [])
        \\ fs [EL_APPEND2]
        \\ `n' - LENGTH ts < LENGTH env2 - LENGTH ts` by fs []
        \\ fs [EL_REPLICATE])
      \\ Cases_on `evaluate ([Op (to_op op) xs], env2, s with code := c)`
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
        \\ strip_tac \\ fs[]
        \\ fs [evaluate_def]
        \\ imp_res_tac evaluate_code_const
        \\ imp_res_tac code_rel_domain
        \\ imp_res_tac do_app_with_code
        \\ imp_res_tac do_app_err \\ fs []
        \\ rfs[]
        \\ qpat_x_assum`_ = (Rerr (Rabort _),_)`mp_tac
        \\ simp[case_eq_thms,pair_case_eq]
        \\ qpat_x_assum`result_CASE q _ _ = _`mp_tac
        \\ simp[case_eq_thms,pair_case_eq]
        \\ strip_tac \\ fs[] \\ rveq \\ fs[]
        \\ imp_res_tac do_app_with_code \\ fs[]
        \\ imp_res_tac do_app_err \\ fs [])
      \\ fs [evaluate_def])
    \\ pop_assum (fn th => fs [th])
    \\ qunabbrev_tac `expr`
    \\ simp [evaluate_def]
    \\ once_rewrite_tac [evaluate_APPEND]
    \\ simp [evaluate_def]
    \\ `∃j. EL acc env2 = Number j` by fs [env_rel_def] \\ fs []
    \\ `∃m. do_app (to_op op) [Number j; Number k] (s_args with code := c) =
              Rval (Number m, s_args with code := c)` by
     (Cases_on `op`
      \\ fs [to_op_def, do_app_def, do_app_aux_def,
             bvlSemTheory.do_app_def, bvl_to_bvi_id])
    \\ simp []
    \\ PURE_TOP_CASE_TAC \\ fs []
    >-
     (rpt (qpat_x_assum `find_code _ _ _ = _` mp_tac)
      \\ fs [find_code_def, optimized_code_def])
    \\ PURE_TOP_CASE_TAC \\ fs []
    \\ once_rewrite_tac [EQ_SYM_EQ]
    \\ PURE_CASE_TAC \\ fs []
    >-
     (rpt (qpat_x_assum `find_code _ _ _ = _` mp_tac)
      \\ fs [find_code_def, optimized_code_def])
    \\ PURE_CASE_TAC \\ fs []
    \\ rpt (qpat_x_assum `find_code _ _ _ = _` mp_tac)
    \\ qpat_x_assum `optimized_code _ _ _ _ _ _` mp_tac
    \\ fs [optimized_code_def, compile_exp_def, find_code_def]
    \\ simp [check_exp_def]
    \\ rw []
    \\ rpt (pairarg_tac \\ fs []) \\ rw []
    \\ rpt (qpat_x_assum `_ = SOME (_,_)` mp_tac)
    \\ imp_res_tac evaluate_code_const
    \\ rw []
    \\ pairarg_tac \\ fs [] \\ rveq
    \\ simp [evaluate_let_wrap]
    \\ `env_rel T (LENGTH a) a (a ++ [op_id_val op] ++ a)` by
     (fs [env_rel_def, EL_LENGTH_APPEND, EL_APPEND1, IS_PREFIX_APPEND]
      \\ Cases_on `op` \\ fs [op_id_val_def])
    \\ first_assum (qspecl_then [`[exp]`, `dec_clock (ticks+1) s_args`] mp_tac)
    \\ impl_tac
    >-
     (imp_res_tac evaluate_clock
      \\ simp [dec_clock_def])
    \\ sg `code_rel (dec_clock (ticks+1) s_args).code c`
    >- fs [evaluate_code_const]
    \\ sg `ty_rel a (REPLICATE (LENGTH a) Any)`
    >- simp [ty_rel_def, LIST_REL_EL_EQN, EL_REPLICATE]
    \\ rpt (disch_then drule)
    \\ disch_then (qspec_then `loc` mp_tac) \\ fs []
    \\ impl_tac
    >- (rpt (PURE_FULL_CASE_TAC \\ fs []) \\ rw [])
    \\ rw [check_exp_def]
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
    \\ sg `code_rel (dec_clock (ticks+1) s_args).code c`
    >- fs [evaluate_code_const]
    \\ rpt (disch_then drule)
    \\ disch_then (qspec_then `loc` mp_tac) \\ fs []
    \\ impl_tac
    >- (rpt (PURE_FULL_CASE_TAC \\ fs []) \\ rw [])
    \\ rw [check_exp_def]
    \\ first_x_assum (qspecl_then [`op`,`n`] mp_tac)
    \\ impl_tac
    \\ pairarg_tac \\ fs [] \\ rw []
    \\ simp [apply_op_def, to_op_def, evaluate_def,
             EL_LENGTH_APPEND, EL_APPEND1]
    \\ reverse PURE_CASE_TAC \\ fs []
    >- (rpt (PURE_CASE_TAC \\ fs []))
    \\ sg `∃k. a' = [Number k]`
    >-
     (drule scan_expr_ty_rel
      \\ rpt (disch_then drule)
      \\ rw [])
    \\ fs []
    \\ rename1 `do_app _ _ (st with code := c)`
    \\ Cases_on `evaluate ([y], env1, st)`
    \\ drule (GEN_ALL no_err_correct)
    \\ rpt (disch_then drule) \\ rw []
    \\ first_x_assum (qspecl_then [`[y]`,`r`] mp_tac)
    \\ impl_tac
    >-
      (imp_res_tac evaluate_clock
      \\ fs [dec_clock_def])
    \\ sg `code_rel r.code c`
    >- (imp_res_tac evaluate_code_const \\ fs [])
    \\ rpt (disch_then drule) \\ rw []
    \\ sg `∀k (s: 'ffi bviSem$state).
             do_app (to_op op) [op_id_val op; Number k] s = Rval (Number k, s)`
    >-
     (rw []
      \\ Cases_on `op`
      \\ rw [op_id_val_def, to_op_def, do_app_def, do_app_aux_def,
             bvlSemTheory.do_app_def, bvl_to_bvi_id, small_enough_int_def])
    \\ pop_assum (fn th => fs [th])
    \\ Cases_on `op`
    \\ fs [evaluate_def, to_op_def, op_id_val_def, do_app_def,
           do_app_aux_def, bvlSemTheory.do_app_def, bvl_to_bvi_id,
           small_enough_int_def]
    \\ rw [bvl_to_bvi_id]
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
   >- (rw [] \\ rfs [])
   \\ PURE_TOP_CASE_TAC \\ fs []
   \\ PURE_TOP_CASE_TAC \\ fs []
   \\ IF_CASES_TAC \\ fs []
   >-
    (rw []
     \\ PURE_TOP_CASE_TAC \\ fs []
     \\ TRY (PURE_CASE_TAC \\ fs [])
     \\ sg `code_rel r'.code c`
     >- (imp_res_tac evaluate_code_const \\ fs [])
     \\ Cases_on `dest` \\ fs []
     \\ metis_tac [code_rel_find_code_NONE, code_rel_find_code_SOME])
   \\ rename1 `([exp],args, _ _ s1)`
   \\ Cases_on `dest` \\ fs []
   >-
    (strip_tac
     \\ PURE_TOP_CASE_TAC \\ fs []
     >-
      (sg `code_rel s1.code c`
       >- (imp_res_tac evaluate_code_const \\ fs [])
       \\ metis_tac [code_rel_find_code_NONE])
     \\ PURE_TOP_CASE_TAC \\ fs []
     \\ rpt (qpat_x_assum `find_code _ _ _ = _` mp_tac)
     \\ simp [find_code_def]
     \\ ntac 5 (PURE_CASE_TAC \\ fs []) \\ rw []
     \\ qpat_x_assum `_ = (r, t)` mp_tac
     \\ PURE_TOP_CASE_TAC \\ fs []
     \\ sg `code_rel s1.code c`
     >- (imp_res_tac evaluate_code_const \\ fs [])
     \\ pop_assum mp_tac
     \\ simp [code_rel_def]
     \\ disch_then drule
     \\ simp [compile_exp_def]
     \\ CASE_TAC \\ fs []
     >-
      (rw []
       \\ `env_rel F (LENGTH (FRONT a)) (FRONT a) (FRONT a)` by fs [env_rel_def]
       \\ sg `ty_rel (FRONT a) (REPLICATE (LENGTH (FRONT a)) Any)`
       >- fs [ty_rel_def, LIST_REL_EL_EQN, EL_REPLICATE]
       \\ imp_res_tac evaluate_code_const
       \\ first_assum (qspecl_then [`[exp]`,`dec_clock (ticks+1) s1`] mp_tac)
       \\ impl_tac
       >-
        (imp_res_tac evaluate_clock
         \\ simp [dec_clock_def])
       \\ simp []
       \\ rpt (disch_then drule) \\ fs []
       \\ impl_tac
       >- (rpt (PURE_FULL_CASE_TAC \\ fs []) \\ rw [])
       \\ rw []
       \\ rpt (PURE_FULL_CASE_TAC \\ fs []))
     \\ rw []
     \\ pairarg_tac \\ fs [] \\ rw []
     \\ `q' = LENGTH (FRONT a)` by fs [LENGTH_FRONT]
     \\ pop_assum (fn th => fs [th])
     \\ imp_res_tac scan_expr_not_Noop
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
     \\ imp_res_tac evaluate_code_const
     \\ simp []
     \\ rpt (disch_then drule)
     \\ disch_then (qspec_then `n` mp_tac) \\ fs []
     \\ impl_tac
     >- (rpt (PURE_FULL_CASE_TAC \\ fs []) \\ rw [])
     \\ rw []
     \\ first_x_assum (qspecl_then [`x`,`n'`] mp_tac)
     \\ simp [optimized_code_def, compile_exp_def]
     \\ fs [check_exp_def]
     \\ simp [apply_op_def, evaluate_def]
     \\ reverse PURE_CASE_TAC \\ fs []
     >- (rpt (PURE_FULL_CASE_TAC \\ fs []))
     \\ rw [EL_LENGTH_APPEND, EL_APPEND1]
     \\ sg `∃m. a' = [Number m]`
     >-
      (drule scan_expr_ty_rel
       \\ rpt (disch_then drule)
       \\ rw [])
     \\ Cases_on `x`
     \\ fs [to_op_def, op_id_val_def, do_app_def, do_app_aux_def,
            bvlSemTheory.do_app_def, bvl_to_bvi_id])
   \\ PURE_TOP_CASE_TAC \\ fs [] \\ rw []
   \\ PURE_TOP_CASE_TAC \\ fs []
   >-
    (imp_res_tac evaluate_code_const
     \\ metis_tac [code_rel_find_code_SOME])
   \\ PURE_TOP_CASE_TAC \\ fs []
   \\ first_assum (qspecl_then [`[exp]`, `dec_clock (ticks+1) s1`] mp_tac)
   \\ impl_tac
   >-
    (imp_res_tac evaluate_clock
     \\ simp [dec_clock_def])
   \\ `env_rel F acc args args` by fs [env_rel_def]
   \\ sg `ty_rel args (REPLICATE (LENGTH args) Any)`
   >- fs [ty_rel_def, LIST_REL_EL_EQN, EL_REPLICATE]
   \\ imp_res_tac evaluate_code_const \\ fs []
   \\ rpt (disch_then drule) \\ fs []
   \\ impl_tac
   >- (rpt (PURE_FULL_CASE_TAC \\ fs []) \\ rw [])
   \\ rpt (qpat_x_assum `find_code _ _ _ = _` mp_tac)
   \\ simp [find_code_def]
   \\ ntac 4 (PURE_TOP_CASE_TAC \\ fs []) \\ rw []
   \\ qpat_assum `code_rel _ _` mp_tac
   \\ simp_tac std_ss [code_rel_def]
   \\ disch_then drule \\ fs []
   \\ simp [compile_exp_def]
   \\ CASE_TAC \\ fs []
   >-
    (rpt (PURE_CASE_TAC \\ fs [])
     \\ rename1 `([z], aa::env1, s2)`
     \\ first_x_assum (qspecl_then [`[z]`,`s2`] mp_tac)
     \\ impl_tac
     >-
      (imp_res_tac evaluate_clock
       \\ fs [dec_clock_def])
     \\ `env_rel F (LENGTH env1 + 1) (aa::env1) (aa::env2)` by fs [env_rel_def]
     \\ sg `ty_rel (aa::env1) (Any::ts)`
     >- fs [ty_rel_def, LIST_REL_EL_EQN]
     \\ imp_res_tac evaluate_code_const \\ fs []
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
   \\ imp_res_tac evaluate_code_const \\ fs []
   \\ rpt (disch_then drule) \\ fs []
   \\ disch_then (qspec_then `x` mp_tac)
   \\ impl_tac
   >- (rpt (PURE_FULL_CASE_TAC \\ fs []) \\ rw [])
   \\ rw []
   \\ first_x_assum (qspecl_then [`x'`,`n`] mp_tac)
   \\ simp [optimized_code_def, compile_exp_def, check_exp_def]
   \\ simp [apply_op_def, evaluate_def]
   \\ reverse (PURE_CASE_TAC \\ fs [])
   >-
    (rpt (PURE_TOP_CASE_TAC \\ fs [])
     \\ rename1 `([z], aa::env1, s2)`
     \\ first_x_assum (qspecl_then [`[z]`,`s2`] mp_tac)
     \\ impl_tac
     >-
      (imp_res_tac evaluate_clock
       \\ fs [dec_clock_def])
     \\ `env_rel F (LENGTH env1 + 1) (aa::env1) (aa::env2)` by fs [env_rel_def]
     \\ `ty_rel (aa::env1) (Any::ts)` by fs [ty_rel_def]
     \\ imp_res_tac evaluate_code_const \\ fs []
     \\ rpt (disch_then drule) \\ rw [])
   \\ simp [EL_LENGTH_APPEND, EL_APPEND1]
   \\ sg `∃k. a' = [Number k]`
   >-
    (drule scan_expr_ty_rel
     \\ rpt (disch_then drule)
     \\ rw [])
   \\ rw []
   \\ Cases_on `x'`
   \\ fs [to_op_def, do_app_def, do_app_aux_def, op_id_val_def,
          bvlSemTheory.do_app_def, bvl_to_bvi_id])
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
  `ALL_DISTINCT (MAP FST prog) ∧
   EVERY (free_names next o FST) prog ∧
   compile_prog next prog = (next1, prog2) ⇒
     code_rel (fromAList prog) (fromAList prog2)`,
  rw [code_rel_def]
  \\ imp_res_tac EVERY_free_names_thm
  >- metis_tac [check_exp_NONE_compile_exp, compile_prog_untouched]
  \\ drule compile_prog_touched
  \\ rpt (disch_then drule) \\ rw []
  \\ qexists_tac `bvl_to_bvi_namespaces * k + next` \\ fs []);

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
       \\ CONV_TAC(LAND_CONV (SIMP_CONV bool_ss [GSYM PULL_FORALL]))
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
           \\ CONV_TAC (LAND_CONV (SIMP_CONV bool_ss [GSYM PULL_FORALL]))
           \\ impl_tac
           >- (every_case_tac \\ fs [])
           \\ disch_then (qspec_then `k'` mp_tac) \\ simp [inc_clock_def]
           \\ qpat_x_assum `evaluate (_,_,_ _ (_ prog2) _) = _` mp_tac
           \\ drule evaluate_add_clock
           \\ CONV_TAC (LAND_CONV (SIMP_CONV bool_ss [GSYM PULL_FORALL]))
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
       \\ fs [] \\ rveq
       \\ rename1 `_ = SOME (q1, q2)`
       \\ imp_res_tac code_rel_find_code_SOME
       \\ PURE_TOP_CASE_TAC \\ fs []
       \\ PURE_TOP_CASE_TAC \\ fs [])
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
    \\ fs [EVERY_MEM,backend_commonTheory.bvl_to_bvi_namespaces_def]
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
