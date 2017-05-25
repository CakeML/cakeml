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

val is_ok_type_IMP_Number = Q.store_thm ("is_ok_type_IMP_Number[simp]",
  `∀exp env (s:'ffi bviSem$state) r t.
     is_ok_type exp ∧
     evaluate ([exp], env, s) = (Rval r, t) ⇒
       ∃n. r = [Number n]`,
  Induct
  \\ fs [is_ok_type_def]
  \\ rpt strip_tac
  \\ qhdtm_x_assum `evaluate` mp_tac
  \\ simp [evaluate_def]
  >-
    (ntac 2 TOP_CASE_TAC \\ fs []
    \\ IF_CASES_TAC \\ fs []
    >- (strip_tac \\ first_x_assum drule \\ fs [])
    \\ IF_CASES_TAC \\ fs []
    \\ strip_tac \\ first_x_assum drule \\ fs [])
  >-
    (ntac 2 TOP_CASE_TAC \\ fs []
    \\ strip_tac \\ first_x_assum (qspec_then `a++env` drule) \\ fs [])
  >-
    (IF_CASES_TAC \\ fs []
    \\ strip_tac \\ first_x_assum drule \\ fs [])
  \\ ntac 2 TOP_CASE_TAC \\ fs []
  \\ rename1 `is_arithmetic op`
  \\ Cases_on `op`
  \\ fs [is_arithmetic_def]
  \\ simp [do_app_def, do_app_aux_def, small_int_def]
  >- (CASE_TAC \\ strip_tac \\ rveq \\ fs [])
  \\ ntac 2 CASE_TAC
  \\ strip_tac \\ rveq
  \\ fs [bvlSemTheory.do_app_def]
  \\ every_case_tac \\ fs [] \\ rveq \\ fs []);

val is_arithmetic_to_op = Q.store_thm ("is_arithmetic_to_op[simp]",
  `∀iop. is_arithmetic (to_op iop)`,
  Cases \\ fs [is_arithmetic_def, to_op_def]);

val all_num_def = Define `
  all_num xs = EVERY (λv. ∃n. v = Number n) xs
  `;

val EVERY_no_err_correct = Q.store_thm ("EVERY_no_err_correct",
  `∀xs env (s: 'ffi bviSem$state) r t.
     EVERY no_err xs ∧
     evaluate (xs, env, s) = (r, t) ⇒
       s = t ∧
       ∃vs.
         r = Rval vs ∧
         LENGTH vs = LENGTH xs ∧
         all_num vs ∧
       (∀(s': 'ffi bviSem$state). evaluate (xs, env, s') = (r, s')) `,
  recInduct evaluate_ind
  \\ simp [no_err_def, all_num_def]
  \\ rpt strip_tac
  \\ qhdtm_x_assum `evaluate` mp_tac
  \\ TRY (simp [evaluate_def] \\ rw [] \\ NO_TAC)
  \\ TRY
    (simp [evaluate_def]
    \\ every_case_tac \\ fs [] \\ rveq \\ fs []
    \\ strip_tac \\ rveq \\ rfs []
    \\ NO_TAC)
  \\ TRY
    (simp [evaluate_def]
    \\ every_case_tac \\ fs [] \\ rveq \\ fs []
    \\ strip_tac \\ rveq
    \\ rfs [] \\ rveq
    \\ first_x_assum (qspec_then `s` assume_tac)
    \\ imp_res_tac evaluate_SING_IMP \\ fs []
    \\ NO_TAC)
  \\ Cases_on `op` \\ fs [no_err_def]
  \\ TRY
    (Cases_on `xs` \\ fs [no_err_def]
    \\ fs [evaluate_def, do_app_def, do_app_aux_def,
           bvlSemTheory.do_app_def, bvl_to_bvi_id, small_int_def,
           small_enough_int_def]
    \\ rw []
    \\ NO_TAC)
  \\ Cases_on `xs` \\ fs [no_err_def]
  \\ Cases_on `t'` \\ fs [no_err_def]
  \\ Cases_on `t''` \\ fs [no_err_def]
  \\ simp [Once evaluate_def]
  \\ CASE_TAC \\ fs []
  \\ rveq
  \\ first_assum (qspec_then `s` assume_tac)
  \\ imp_res_tac evaluate_IMP_LENGTH
  \\ Cases_on `vs` \\ fs [LENGTH_NIL]
  \\ Cases_on `t'` \\ fs [LENGTH_NIL] \\ rveq
  \\ fs [evaluate_def, do_app_def, do_app_aux_def,
         bvlSemTheory.do_app_def, bvl_to_bvi_id, small_int_def,
         small_enough_int_def]
  \\ rw []);

val no_err_correct = save_thm (
  "no_err_correct",
  Q.SPEC `[x]` EVERY_no_err_correct |> SIMP_RULE (srw_ss()) []
  );

val no_err_env = Q.store_thm ("no_err_env",
  `∀xs env (s: 'ffi bviSem$state) r t env'.
   EVERY no_err xs ∧
   evaluate (xs, env, s) = (r, t) ⇒
     evaluate (xs, env', s) = (r, t)`,
  recInduct evaluate_ind
  \\ simp [no_err_def]
  \\ rpt strip_tac
  \\ fs [evaluate_def]
  \\ pop_assum mp_tac
  >-
    (TOP_CASE_TAC \\ fs []
    \\ imp_res_tac no_err_correct
    \\ last_assum (qspec_then `env` assume_tac)
    \\ first_x_assum drule
    \\ strip_tac \\ rveq \\ fs []
    \\ rveq
    \\ TOP_CASE_TAC \\ fs [])
  \\ TOP_CASE_TAC \\ fs []
  \\ Cases_on `op` \\ fs [no_err_def]
  \\ Cases_on `xs` \\ fs [no_err_def]
  \\ Cases_on `t'` \\ fs [no_err_def]
  \\ Cases_on `t''` \\ fs [no_err_def]);

val no_err_type_correct = Q.store_thm ("no_err_type_correct",
  `∀x.
     no_err x ⇒
       ∃k. ∀env (s:'ffi bviSem$state).
         evaluate ([x], env, s) = (Rval [Number k], s)`,
  rpt strip_tac
  \\ drule no_err_correct
  \\ strip_tac
  \\ Cases_on `evaluate ([x],env,(s:'ffi bviSem$state))`
  \\ first_x_assum drule \\ rw []
  \\ imp_res_tac evaluate_SING_IMP
  \\ fs [all_num_def] \\ rveq
  \\ qexists_tac `n`
  \\ rw []
  \\ first_x_assum (qspec_then `s` assume_tac)
  \\ imp_res_tac no_err_env
  \\ rfs [EVERY_DEF]);

val comm_theorem = Q.store_thm ("comm_theorem",
  `∀(s:'ffi bviSem$state).
     op ≠ Noop ∧
     no_err x1 ∧
     evaluate ([apply_op op x1 x2], env, s) = (r, t) ∧
     r ≠ Rerr (Rabort Rtype_error) ⇒
       evaluate ([apply_op op x2 x1], env, s) = (r, t)`,
  simp [apply_op_def]
  \\ rpt strip_tac
  \\ qhdtm_x_assum `evaluate` mp_tac
  \\ simp [evaluate_def]
  \\ CASE_TAC
  \\ drule (GEN_ALL no_err_correct)
  \\ disch_then drule
  \\ strip_tac \\ rveq
  \\ imp_res_tac evaluate_SING_IMP \\ fs [] \\ rveq
  \\ CASE_TAC
  \\ reverse CASE_TAC \\ fs []
  >- (CASE_TAC \\ fs [])
  \\ imp_res_tac evaluate_SING_IMP \\ fs [] \\ rveq
  \\ Cases_on `op` \\ fs [to_op_def]
  \\ fs [do_app_def, do_app_aux_def, bvlSemTheory.do_app_def]
  \\ every_case_tac \\ fs [] \\ rveq
  \\ fs [integerTheory.INT_ADD_COMM, integerTheory.INT_MUL_COMM]);

val assoc_theorem = Q.store_thm ("assoc_theorem",
  `∀(s: 'ffi bviSem$state).
     op ≠ Noop ∧
     evaluate ([apply_op op (apply_op op x1 x2) x3], env, s) = (r, t) ∧
     r ≠ Rerr (Rabort Rtype_error) ⇒
       evaluate ([apply_op op x1 (apply_op op x2 x3)], env, s) = (r, t)`,
  simp [apply_op_def]
  \\ rpt strip_tac
  \\ qhdtm_x_assum `evaluate` mp_tac
  \\ simp [evaluate_def]
  \\ ntac 2 CASE_TAC
  \\ strip_tac
  \\ CASE_TAC
  \\ rename1 `evaluate ([x1],_,_) = (res_x1, st_x1)`
  \\ rename1 `evaluate ([x2],_,_) = (res_x2, st_x2)`
  \\ rename1 `evaluate ([x3],_,_) = (res_x3, st_x3)`
  \\ reverse (Cases_on `res_x1`) \\ fs []
  >- (rveq \\ fs [])
  \\ reverse (Cases_on `res_x2`) \\ fs []
  >- (rveq \\ fs [])
  \\ reverse (Cases_on `res_x3`) \\ fs []
  >-
    (imp_res_tac evaluate_SING_IMP \\ fs [] \\ rveq
    \\ every_case_tac \\ fs [] \\ rveq \\ fs []
    \\ imp_res_tac do_app_err
    \\ Cases_on `op` \\ fs [to_op_def]
    \\ Cases_on `w` \\ Cases_on `w'`
    \\ fs [do_app_def,
           do_app_aux_def,
           bvlSemTheory.do_app_def,
           bvl_to_bvi_id])
  \\ imp_res_tac evaluate_SING_IMP \\ fs [] \\ rveq
  \\ every_case_tac \\ fs [] \\ rveq \\ fs []
  \\ imp_res_tac do_app_err
  \\ Cases_on `op` \\ fs [to_op_def]
  \\ Cases_on `w` \\ Cases_on `w'` \\ Cases_on `w''`
  \\ fs [do_app_def,
             do_app_aux_def,
             bvlSemTheory.do_app_def,
             bvl_to_bvi_id]
  \\ rveq \\ rfs [] \\ rveq
  \\ fs [integerTheory.INT_ADD_ASSOC, integerTheory.INT_MUL_ASSOC]);

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

val tail_is_ok_Arith = Q.store_thm ("tail_is_ok_Arith",
  `∀exp name p.
     tail_is_ok name exp = SOME (p, op) ⇒
       op ≠ Noop`,
  Induct \\ rpt gen_tac
  \\ TRY (simp [tail_is_ok_def] \\ NO_TAC)
  \\ TRY
    (simp [tail_is_ok_def]
    \\ strip_tac
    \\ first_x_assum drule \\ rw []
    \\ NO_TAC)
  >-
    (simp [tail_is_ok_def]
    \\ TOP_CASE_TAC
    >-
      (ntac 2 (TOP_CASE_TAC \\ fs [])
      \\ strip_tac \\ rveq
      \\ first_x_assum drule
      \\ rw [])
    \\ ntac 2 (TOP_CASE_TAC \\ fs [])
    \\ strip_tac \\ rveq
    \\ first_x_assum drule
    \\ rw [])
  \\ simp [tail_is_ok_def]
  \\ TOP_CASE_TAC
  \\ IF_CASES_TAC \\ fs []
  \\ strip_tac \\ rveq
  \\ fs [from_op_def] \\ rveq);

val check_exp_Arith = Q.store_thm ("check_exp_Arith",
  `∀exp name p.
    check_exp name exp = SOME (p, op) ⇒
      op ≠ Noop`,
  rpt strip_tac \\ fs [check_exp_def]
  \\ drule tail_is_ok_Arith \\ fs []);

val assoc_swap_lemma = Q.store_thm ("assoc_swap_lemma",
  `∀(s: 'ffi bviSem$state).
     op ≠ Noop ∧
     no_err x3 ∧
     no_err x1 ∧
     evaluate ([apply_op op x1 (apply_op op x2 x3)], env, s) = (r, t) ∧
     r ≠ Rerr (Rabort Rtype_error) ⇒
       evaluate ([apply_op op x2 (apply_op op x1 x3)], env, s) = (r, t)`,
  rpt strip_tac
  \\ `evaluate ([apply_op op x1 (apply_op op x2 x3)], env, s) =
      evaluate ([apply_op op (apply_op op x1 x2) x3], env, s)` by
    (simp [apply_op_def, evaluate_def]
    \\ CASE_TAC
    \\ drule (GEN_ALL no_err_correct)
    \\ disch_then drule
    \\ strip_tac \\ rveq
    \\ imp_res_tac evaluate_SING_IMP
    \\ fs [all_num_def] \\ rveq
    \\ fs [evaluate_def, apply_op_def]
    \\ ntac 2 CASE_TAC \\ fs []
    \\ imp_res_tac evaluate_SING_IMP \\ fs [] \\ rveq
    \\ `∃m. w = Number m` by
      (every_case_tac \\ fs []
      \\ imp_res_tac evaluate_SING_IMP \\ fs [] \\ rveq
      \\ imp_res_tac do_app_err
      \\ Cases_on `op` \\ fs [to_op_def]
      \\ Cases_on `w` \\ TRY (Cases_on `w'`)
      \\ fs [do_app_def,
             do_app_aux_def,
             bvlSemTheory.do_app_def,
             bvl_to_bvi_id]
      \\ rveq \\ fs []
      \\ imp_res_tac no_err_correct \\ fs [])
    \\ rveq
    \\ rename1 `_ = (_, st_x2)`
    \\ `∃k.
          do_app (to_op op) [Number m; Number n] st_x2 =
            Rval (Number k, st_x2)` by
      (Cases_on `op`
      \\ simp [to_op_def,
               do_app_def,
               do_app_aux_def,
               bvlSemTheory.do_app_def,
               bvl_to_bvi_id,
               small_enough_int_def])
    \\ simp []
    \\ CASE_TAC
    \\ imp_res_tac no_err_type_correct
    \\ fs [] \\ rveq \\ fs []
    \\ Cases_on `op`
    \\ fs [to_op_def,
           do_app_def,
           do_app_aux_def,
           bvlSemTheory.do_app_def,
           bvl_to_bvi_id,
           small_enough_int_def]
    \\ rveq
    \\ fs [integerTheory.INT_ADD_ASSOC, integerTheory.INT_MUL_ASSOC])
  \\ fs []
  \\ pop_assum kall_tac
  \\ `evaluate ([apply_op op (apply_op op x1 x2) x3], env, s) =
      evaluate ([apply_op op (apply_op op x2 x1) x3], env, s)` by
    (simp_tac std_ss [Once apply_op_def, evaluate_def]
    \\ CASE_TAC
    \\ drule (GEN_ALL comm_theorem)
    \\ ntac 2 (disch_then drule)
    \\ simp []
    \\ strip_tac
    \\ reverse (Cases_on `q`) \\ fs []
    >-
      (fs [evaluate_def, apply_op_def]
      \\ every_case_tac \\ fs [] \\ rveq \\ fs []
      \\ imp_res_tac do_app_err
      \\ rveq \\ rfs [])
    \\ fs [apply_op_def, evaluate_def])
  \\ `evaluate ([apply_op op (apply_op op x2 x1) x3], env, s) =
      evaluate ([apply_op op x2 (apply_op op x1 x3)], env, s)` by
    (Cases_on `evaluate ([apply_op op (apply_op op x2 x1) x3], env, s)`
    \\ drule (GEN_ALL assoc_theorem)
    \\ disch_then drule
    \\ impl_tac
    >- fs [evaluate_def, apply_op_def]
    \\ fs [])
  \\ fs []);

val evaluate_assoc_swap = Q.store_thm ("evaluate_assoc_swap",
  `∀(s: 'ffi bviSem$state).
   no_err from ∧
   iop ≠ Noop ∧
   is_rec_or_rec_binop nm iop into ∧
   evaluate ([apply_op iop from into], env, s) = (r, t) ∧
   r ≠ Rerr (Rabort Rtype_error) ⇒
     evaluate ([assoc_swap iop from into], env, s) = (r, t)`,
  rpt strip_tac
  \\ simp [assoc_swap_def]
  \\ IF_CASES_TAC \\ fs []
  >- imp_res_tac comm_theorem
  \\ TOP_CASE_TAC \\ fs []
  >- imp_res_tac comm_theorem
  \\ fs [op_eq_to_op]
  \\ rveq
  \\ fs [GSYM apply_op_def]
  \\ simp [evaluate_def, apply_op_def]
  \\ `no_err e2` by
    fs [is_rec_or_rec_binop_def,
        apply_op_def,
        is_rec_def,
        get_bin_args_def]
  \\ ntac 3 CASE_TAC
  \\ drule (GEN_ALL no_err_correct)
  \\ disch_then drule
  \\ strip_tac \\ rveq \\ fs []
  \\ `∃k. vs = [Number k]` by
    (Cases_on `vs`
    \\ fs [LENGTH_NIL, all_num_def])
  \\ fs [] \\ rveq
  \\ rename1 `evaluate ([e1],_,_) = (res_e1, st_e1)`
  \\ reverse (Cases_on `res_e1`) \\ fs []
  >-
    (qpat_x_assum `_ = (r, t)` mp_tac
    \\ simp [evaluate_def, apply_op_def]
    \\ CASE_TAC
    \\ imp_res_tac (GEN_ALL no_err_correct) \\ fs [])
  \\ fs []
  \\ imp_res_tac (GEN_ALL no_err_correct) \\ fs [] \\ rveq
  \\ rpt (qpat_x_assum `no_err _ ⇒ _` kall_tac)
  \\ fs []
  \\ `∃n. vs = [Number n]` by
    (Cases_on `vs`
    \\ fs [LENGTH_NIL, all_num_def])
  \\ fs [] \\ rveq
  \\ imp_res_tac evaluate_SING_IMP \\ fs [] \\ rveq
  \\ `∃m. w = Number m` by
    (qpat_x_assum `_ = (r, t)` mp_tac
    \\ simp [evaluate_def, apply_op_def]
    \\ Cases_on `iop`
    \\ Cases_on `w`
    \\ fs [to_op_def,
           do_app_def,
           do_app_aux_def,
           bvlSemTheory.do_app_def,
           bvl_to_bvi_id])
  \\ fs [] \\ rveq
  \\ Cases_on `iop`
  \\ fs [evaluate_def,
         apply_op_def,
         to_op_def,
         do_app_def,
         do_app_aux_def,
         bvlSemTheory.do_app_def,
         bvl_to_bvi_id]
  \\ metis_tac [integerTheory.INT_MUL_ASSOC,
                integerTheory.INT_ADD_ASSOC,
                integerTheory.INT_MUL_COMM,
                integerTheory.INT_ADD_COMM]);

(* TODO: This repeats itself a lot except in a few cases. *)
val evaluate_rewrite_op = Q.store_thm ("evaluate_rewrite_op",
  `∀op name exp env (s: 'ffi bviSem$state) r t p exp2.
     evaluate ([exp], env, s) = (r, t) ∧
     r ≠ Rerr (Rabort Rtype_error) ∧
     rewrite_op op name exp = (p, exp2) ∧
     evaluate ([exp], env, s) = (r, t) ⇒
       if ¬p then exp2 = exp else
         evaluate ([exp2], env, s) = (r, t)`,
  ho_match_mp_tac rewrite_op_ind
  \\ rpt gen_tac \\ strip_tac \\ rpt gen_tac
  \\ strip_tac
  \\ reverse (Cases_on `p`)
  >-
    (pop_assum mp_tac
    \\ once_rewrite_tac [rewrite_op_def]
    \\ IF_CASES_TAC
    >- rw []
    \\ TOP_CASE_TAC
    \\ fs [] \\ rveq
    \\ rfs [] \\ rveq
    \\ rpt (pairarg_tac \\ fs [])
    \\ every_case_tac \\ fs [] \\ rveq \\ fs [])
  \\ IF_CASES_TAC >- fs []
  \\ pop_assum kall_tac
  \\ pop_assum mp_tac
  \\ once_rewrite_tac [rewrite_op_def]
  \\ IF_CASES_TAC
  >- rw []
  \\ TOP_CASE_TAC \\ fs []
  \\ rpt (pairarg_tac \\ fs []) \\ rveq
  \\ rfs []
  \\ Cases_on `r1`
  >-
    (Cases_on `r2`
    >-
      (fs []
      \\ qhdtm_x_assum `evaluate` mp_tac
      \\ simp [evaluate_def]
      \\ CASE_TAC \\ first_x_assum drule \\ strip_tac
      \\ CASE_TAC \\ first_x_assum drule \\ strip_tac
      \\ rename1 `evaluate ([e1],_,_) = (res_e1, st_e1)`
      \\ rename1 `evaluate ([e2],_,_) = (res_e2, st_e2)`
      \\ Cases_on `res_e1 = Rerr (Rabort Rtype_error)`
      \\ rfs []
      \\ reverse (Cases_on `res_e1`) \\ fs []
      >-
        (strip_tac \\ rveq
        \\ IF_CASES_TAC
        >-
          (IF_CASES_TAC \\ fs []
          \\ IF_CASES_TAC \\ fs []
          \\ strip_tac \\ rveq
          \\ drule (GEN_ALL evaluate_assoc_swap)
          \\ ntac 2 (disch_then drule)
          \\ Cases_on `evaluate ([apply_op op y2 y1], env, s)`
          \\ disch_then drule
          \\ impl_tac
          >-
            (pop_assum mp_tac
            \\ simp [evaluate_def, apply_op_def]
            \\ CASE_TAC
            \\ drule (GEN_ALL no_err_correct)
            \\ disch_then drule
            \\ strip_tac \\ rveq \\ fs []
            \\ strip_tac \\ rveq \\ fs [])
          \\ simp []
          \\ pop_assum mp_tac
          \\ fs [apply_op_def, evaluate_def]
          \\ CASE_TAC
          \\ drule (GEN_ALL no_err_correct)
          \\ disch_then drule
          \\ strip_tac \\ rveq \\ fs [])
        \\ IF_CASES_TAC
        >-
          (IF_CASES_TAC \\ fs []
          \\ strip_tac \\ rveq
          \\ drule (GEN_ALL evaluate_assoc_swap)
          \\ ntac 2 (disch_then drule)
          \\ Cases_on `evaluate ([apply_op op y1 y2], env, s)`
          \\ disch_then drule
          \\ impl_tac
          >-
            (pop_assum mp_tac
            \\ simp [evaluate_def, apply_op_def]
            \\ strip_tac \\ rveq \\ fs [])
          \\ simp []
          \\ pop_assum mp_tac
          \\ fs [apply_op_def, evaluate_def])
        \\ fs [])
      \\ reverse CASE_TAC
      >-
        (strip_tac \\ rveq \\ fs []
        \\ IF_CASES_TAC
        >-
          (ntac 2 (IF_CASES_TAC \\ fs [])
          \\ strip_tac \\ rveq
          \\ drule (GEN_ALL evaluate_assoc_swap)
          \\ ntac 2 (disch_then drule)
          \\ Cases_on `evaluate ([apply_op op y2 y1], env, s)`
          \\ disch_then drule
          \\ impl_tac
          >-
            (pop_assum mp_tac
            \\ simp [evaluate_def, apply_op_def]
            \\ CASE_TAC
            \\ drule (GEN_ALL no_err_correct)
            \\ disch_then drule
            \\ strip_tac \\ rveq \\ fs [])
          \\ rfs []
          \\ pop_assum mp_tac
          \\ simp [apply_op_def, evaluate_def]
          \\ CASE_TAC
          \\ drule (GEN_ALL no_err_correct)
          \\ disch_then drule
          \\ strip_tac \\ rveq \\ fs [])
        \\ IF_CASES_TAC
        >-
          (IF_CASES_TAC \\ fs []
          \\ strip_tac \\ rveq
          \\ drule (GEN_ALL evaluate_assoc_swap)
          \\ ntac 2 (disch_then drule)
          \\ Cases_on `evaluate ([apply_op op y1 y2], env, s)`
          \\ disch_then drule
          \\ impl_tac
          >-
            (pop_assum mp_tac
            \\ simp [apply_op_def, evaluate_def]
            \\ strip_tac \\ rveq \\ fs [])
          \\ pop_assum mp_tac
          \\ simp [apply_op_def, evaluate_def])
        \\ fs [])
      \\ fs []
      \\ imp_res_tac evaluate_SING_IMP \\ fs [] \\ rveq
      \\ strip_tac
      \\ `∃m n. w = Number m ∧ w'' = Number n` by
        (Cases_on `op`
        \\ Cases_on `w`
        \\ Cases_on `w''`
        \\ fs [to_op_def,
               do_app_def,
               do_app_aux_def,
               bvlSemTheory.do_app_def,
               bvl_to_bvi_id])
      \\ fs [] \\ rveq
      \\ IF_CASES_TAC
      >-
        (ntac 2 (IF_CASES_TAC \\ fs [])
        \\ strip_tac \\ rveq
        \\ drule (GEN_ALL evaluate_assoc_swap)
        \\ ntac 2 (disch_then drule)
        \\ Cases_on `evaluate ([apply_op op y2 y1], env, s)`
        \\ disch_then drule
        \\ impl_tac
        >-
          (pop_assum mp_tac
          \\ simp [apply_op_def, evaluate_def]
          \\ CASE_TAC
          \\ drule (GEN_ALL no_err_correct)
          \\ disch_then drule
          \\ strip_tac \\ rveq \\ fs []
          \\ strip_tac
          \\ Cases_on `op`
          \\ fs [to_op_def,
                 do_app_def,
                 do_app_aux_def,
                 bvlSemTheory.do_app_def,
                 bvl_to_bvi_id]
          \\ rveq \\ fs [])
        \\ pop_assum mp_tac
        \\ simp [apply_op_def, evaluate_def]
        \\ CASE_TAC
        \\ drule (GEN_ALL no_err_correct)
        \\ disch_then drule
        \\ strip_tac \\ rveq \\ fs []
        \\ ntac 2 strip_tac
        \\ Cases_on `op`
        \\ fs [to_op_def,
               do_app_def,
               do_app_aux_def,
               bvlSemTheory.do_app_def,
               bvl_to_bvi_id]
        \\ rveq
        \\ fs [integerTheory.INT_ADD_COMM, integerTheory.INT_MUL_COMM])
      \\ ntac 2 (IF_CASES_TAC \\ fs [])
      \\ strip_tac \\ rveq
      \\ drule (GEN_ALL evaluate_assoc_swap)
      \\ ntac 2 (disch_then drule)
      \\ Cases_on `evaluate ([apply_op op y1 y2], env, s)`
      \\ disch_then drule
      \\ impl_tac
      >-
        (pop_assum mp_tac
        \\ simp [evaluate_def, apply_op_def]
        \\ strip_tac \\ rveq \\ fs [])
      \\ pop_assum mp_tac
      \\ simp [evaluate_def, apply_op_def])
    \\ IF_CASES_TAC
    >-
      (ntac 2 (IF_CASES_TAC \\ fs [])
      \\ strip_tac \\ rveq
      \\ qhdtm_x_assum `evaluate` mp_tac
      \\ simp [evaluate_def]
      \\ CASE_TAC \\ first_x_assum drule \\ strip_tac
      \\ CASE_TAC \\ first_x_assum drule \\ strip_tac
      \\ rename1 `evaluate ([e1],_,_) = (res_e1, st_e1)`
      \\ rename1 `evaluate ([e2],_,_) = (res_e2, st_e2)`
      \\ reverse (Cases_on `res_e1`) \\ fs []
      >-
        (strip_tac \\ rveq \\ rfs []
        \\ drule (GEN_ALL evaluate_assoc_swap)
        \\ ntac 2 (disch_then drule)
        \\ Cases_on `evaluate ([apply_op op y2 y1], env, s)`
        \\ disch_then drule
        \\ pop_assum mp_tac
        \\ simp [evaluate_def, apply_op_def]
        \\ CASE_TAC
        \\ drule (GEN_ALL no_err_correct)
        \\ disch_then drule
        \\ ntac 2 (strip_tac \\ rveq \\ fs []))
      \\ reverse CASE_TAC
      >-
        (strip_tac \\ rveq \\ rfs []
        \\ fs [] \\ rveq
        \\ drule (GEN_ALL evaluate_assoc_swap)
        \\ ntac 2 (disch_then drule)
        \\ Cases_on `evaluate ([apply_op op e2 y1], env, s)`
        \\ disch_then drule
        \\ pop_assum mp_tac
        \\ simp [evaluate_def, apply_op_def]
        \\ ntac 2 CASE_TAC
        \\ drule (GEN_ALL no_err_correct)
        \\ disch_then drule
        \\ strip_tac \\ rveq \\ fs [])
      \\ fs [] \\ rveq \\ rfs []
      \\ drule (GEN_ALL evaluate_assoc_swap)
      \\ ntac 2 (disch_then drule)
      \\ Cases_on `evaluate ([apply_op op e2 y1], env, s)`
      \\ disch_then drule
      \\ pop_assum mp_tac
      \\ simp [evaluate_def, apply_op_def]
      \\ CASE_TAC
      \\ drule (GEN_ALL no_err_correct)
      \\ disch_then drule
      \\ strip_tac \\ rveq \\ fs []
      \\ rveq
      \\ imp_res_tac evaluate_SING_IMP \\ fs [] \\ rveq
      \\ rpt strip_tac
      \\ Cases_on `a'` \\ Cases_on `w`
      \\ Cases_on `op`
      \\ fs [LENGTH_NIL,
             all_num_def,
             to_op_def,
             do_app_def,
             do_app_aux_def,
             bvlSemTheory.do_app_def,
             bvl_to_bvi_id]
      \\ rveq \\ fs [bvl_to_bvi_id]
      \\ rveq \\ fs [integerTheory.INT_ADD_COMM, integerTheory.INT_MUL_COMM])
    \\ ntac 2 (IF_CASES_TAC \\ fs [])
    \\ strip_tac \\ rveq
    \\ qhdtm_x_assum `evaluate` mp_tac
    \\ simp [evaluate_def]
    \\ ntac 2 (CASE_TAC \\ first_x_assum drule \\ strip_tac)
    \\ rename1 `evaluate ([e1],_,_) = (res_e1, st_e1)`
    \\ rename1 `evaluate ([e2],_,_) = (res_e2, st_e2)`
    \\ reverse (Cases_on `res_e1`) \\ fs []
    >-
      (strip_tac \\ rveq \\ fs []
      \\ drule (GEN_ALL evaluate_assoc_swap)
      \\ ntac 2 (disch_then drule)
      \\ Cases_on `evaluate ([apply_op op y1 y2], env, s)`
      \\ disch_then drule
      \\ pop_assum mp_tac
      \\ simp [evaluate_def, apply_op_def]
      \\ strip_tac \\ rveq \\ fs [])
    \\ reverse CASE_TAC \\ fs []
    >-
      (strip_tac \\ rveq \\ rfs []
      \\ rveq
      \\ drule (GEN_ALL evaluate_assoc_swap)
      \\ ntac 2 (disch_then drule)
      \\ Cases_on `evaluate ([apply_op op y1 e2], env, s)`
      \\ disch_then drule
      \\ pop_assum mp_tac
      \\ simp [evaluate_def, apply_op_def]
      \\ strip_tac \\ rveq \\ fs [])
    \\ rveq \\ rfs []
    \\ drule (GEN_ALL evaluate_assoc_swap)
    \\ ntac 2 (disch_then drule)
    \\ Cases_on `evaluate ([apply_op op y1 e2], env, s)`
    \\ disch_then drule
    \\ pop_assum mp_tac
    \\ simp [evaluate_def, apply_op_def])
  \\ Cases_on `r2` \\ fs []
  >-
    (IF_CASES_TAC
    >-
      (ntac 2 (IF_CASES_TAC \\ fs [])
      \\ strip_tac \\ rveq
      \\ qhdtm_x_assum `evaluate` mp_tac
      \\ simp [evaluate_def]
      \\ ntac 2 (CASE_TAC \\ first_x_assum drule \\ strip_tac)
      \\ rename1 `evaluate ([e1],_,_) = (res_e1, st_e1)`
      \\ rename1 `evaluate ([e2],_,_) = (res_e2, st_e2)`
      \\ reverse (Cases_on `res_e1`) \\ fs []
      >-
        (strip_tac \\ rveq \\ rfs []
        \\ rveq
        \\ drule (GEN_ALL evaluate_assoc_swap)
        \\ ntac 2 (disch_then drule)
        \\ Cases_on `evaluate ([apply_op op y2 e1], env, s)`
        \\ disch_then drule
        \\ pop_assum mp_tac
        \\ simp [evaluate_def, apply_op_def]
        \\ CASE_TAC
        \\ drule (GEN_ALL no_err_correct)
        \\ disch_then drule
        \\ ntac 2 (strip_tac \\ rveq \\ fs []))
      \\ reverse CASE_TAC
      >-
        (strip_tac \\ rveq \\ fs []
        \\ rfs [] \\ rveq
        \\ drule (GEN_ALL evaluate_assoc_swap)
        \\ ntac 2 (disch_then drule)
        \\ Cases_on `evaluate ([apply_op op y2 e1], env, s)`
        \\ disch_then drule
        \\ pop_assum mp_tac
        \\ simp [evaluate_def, apply_op_def]
        \\ CASE_TAC
        \\ drule (GEN_ALL no_err_correct)
        \\ disch_then drule
        \\ strip_tac \\ rveq \\ fs [])
      \\ fs [] \\ rfs [] \\ rveq
      \\ drule (GEN_ALL evaluate_assoc_swap)
      \\ ntac 2 (disch_then drule)
      \\ Cases_on `evaluate ([apply_op op y2 e1], env, s)`
      \\ disch_then drule
      \\ pop_assum mp_tac
      \\ simp [evaluate_def, apply_op_def]
      \\ CASE_TAC
      \\ drule (GEN_ALL no_err_correct)
      \\ disch_then drule
      \\ strip_tac \\ rveq \\ fs []
      \\ imp_res_tac evaluate_SING_IMP \\ fs [] \\ rveq
      \\ rpt strip_tac
      \\ Cases_on `w` \\ Cases_on `w'`
      \\ Cases_on `op`
      \\ fs [to_op_def,
             all_num_def,
             LENGTH_NIL,
             do_app_def,
             do_app_aux_def,
             bvlSemTheory.do_app_def,
             bvl_to_bvi_id]
      \\ rveq \\ fs [integerTheory.INT_ADD_COMM, integerTheory.INT_MUL_COMM])
    \\ ntac 2 (IF_CASES_TAC \\ fs [])
    \\ strip_tac \\ rveq
    \\ qhdtm_x_assum `evaluate` mp_tac
    \\ simp [evaluate_def]
    \\ ntac 2 (CASE_TAC \\ first_x_assum drule \\ strip_tac)
    \\ rename1 `evaluate ([e1],_,_) = (res_e1, st_e1)`
    \\ rename1 `evaluate ([e2],_,_) = (res_e2, st_e2)`
    \\ reverse (Cases_on `res_e1`) \\ fs []
    >-
      (strip_tac \\ rveq \\ rfs []
      \\ rveq
      \\ drule (GEN_ALL evaluate_assoc_swap)
      \\ ntac 2 (disch_then drule)
      \\ Cases_on `evaluate ([apply_op op e1 y2], env, s)`
      \\ disch_then drule
      \\ pop_assum mp_tac
      \\ simp [evaluate_def, apply_op_def]
      \\ strip_tac \\ rveq \\ fs [])
    \\ reverse CASE_TAC
    >-
      (strip_tac \\ rveq \\ fs []
      \\ rfs [] \\ rveq
      \\ drule (GEN_ALL evaluate_assoc_swap)
      \\ ntac 2 (disch_then drule)
      \\ Cases_on `evaluate ([apply_op op e1 y2], env, s)`
      \\ disch_then drule
      \\ pop_assum mp_tac
      \\ simp [evaluate_def, apply_op_def]
      \\ strip_tac \\ rveq \\ fs [])
    \\ fs [] \\ rfs [] \\ rveq
    \\ drule (GEN_ALL evaluate_assoc_swap)
    \\ ntac 2 (disch_then drule)
    \\ Cases_on `evaluate ([apply_op op e1 y2], env, s)`
    \\ disch_then drule
    \\ pop_assum mp_tac
    \\ simp [evaluate_def, apply_op_def])
  \\ IF_CASES_TAC
  >-
    (ntac 2 (IF_CASES_TAC \\ fs [])
    \\ strip_tac \\ rveq
    \\ qhdtm_x_assum `evaluate` mp_tac
    \\ simp [evaluate_def]
    \\ ntac 2 (CASE_TAC \\ first_x_assum drule \\ strip_tac)
    \\ rename1 `evaluate ([e1],_,_) = (res_e1, st_e1)`
    \\ rename1 `evaluate ([e2],_,_) = (res_e2, st_e2)`
    \\ reverse (Cases_on `res_e1`) \\ fs []
    >-
      (strip_tac \\ rveq \\ rfs []
      \\ rveq
      \\ drule (GEN_ALL evaluate_assoc_swap)
      \\ ntac 2 (disch_then drule)
      \\ Cases_on `evaluate ([apply_op op y2 e1], env, s)`
      \\ disch_then drule
      \\ pop_assum mp_tac
      \\ simp [evaluate_def, apply_op_def]
      \\ CASE_TAC
      \\ drule (GEN_ALL no_err_correct)
      \\ disch_then drule
      \\ ntac 2 (strip_tac \\ rveq \\ fs []))
    \\ reverse CASE_TAC
    >-
      (strip_tac \\ rveq \\ rfs []
      \\ fs [] \\ rveq
      \\ drule (GEN_ALL evaluate_assoc_swap)
      \\ ntac 2 (disch_then drule)
      \\ Cases_on `evaluate ([apply_op op e2 e1], env, s)`
      \\ disch_then drule
      \\ pop_assum mp_tac
      \\ simp [evaluate_def, apply_op_def]
      \\ CASE_TAC
      \\ drule (GEN_ALL no_err_correct)
      \\ disch_then drule
      \\ strip_tac \\ rveq \\ fs [])
    \\ fs [] \\ rfs [] \\ rveq
    \\ drule (GEN_ALL evaluate_assoc_swap)
    \\ ntac 2 (disch_then drule)
    \\ Cases_on `evaluate ([apply_op op e2 e1], env, s)`
    \\ disch_then drule
    \\ pop_assum mp_tac
    \\ simp [evaluate_def, apply_op_def]
    \\ CASE_TAC
    \\ drule (GEN_ALL no_err_correct)
    \\ disch_then drule
    \\ strip_tac \\ rveq \\ fs []
    \\ rpt strip_tac
    \\ imp_res_tac evaluate_SING_IMP \\ fs [] \\ rveq
    \\ Cases_on `a'` \\ Cases_on `w`
    \\ Cases_on `op`
    \\ fs [to_op_def,
           all_num_def,
           LENGTH_NIL,
           do_app_def,
           do_app_aux_def,
           bvlSemTheory.do_app_def,
           bvl_to_bvi_id]
    \\ rveq \\ fs [integerTheory.INT_ADD_COMM, integerTheory.INT_MUL_COMM])
  \\ ntac 2 (IF_CASES_TAC \\ fs [])
  \\ strip_tac \\ rveq
  \\ qhdtm_x_assum `evaluate` mp_tac
  \\ simp [evaluate_def]
  \\ ntac 2 (CASE_TAC \\ first_x_assum drule \\ strip_tac)
  \\ rfs []
  \\ rename1 `evaluate ([e1],_,_) = (res_e1, st_e1)`
  \\ rename1 `evaluate ([e2],_,_) = (res_e2, st_e2)`
  \\ reverse (Cases_on `res_e1`) \\ fs []
  >-
    (strip_tac \\ rveq \\ rfs []
    \\ rveq
    \\ drule (GEN_ALL evaluate_assoc_swap)
    \\ ntac 2 (disch_then drule)
    \\ Cases_on `evaluate ([apply_op op e1 y2], env, s)`
    \\ disch_then drule
    \\ pop_assum mp_tac
    \\ simp [evaluate_def, apply_op_def]
    \\ strip_tac \\ rveq \\ fs [])
  \\ fs [] \\ rveq
  \\ reverse CASE_TAC
  >-
    (strip_tac \\ rveq \\ rfs []
    \\ rveq
    \\ drule (GEN_ALL evaluate_assoc_swap)
    \\ ntac 2 (disch_then drule)
    \\ Cases_on `evaluate ([apply_op op e1 e2], env, s)`
    \\ disch_then drule
    \\ pop_assum mp_tac
    \\ simp [evaluate_def, apply_op_def]
    \\ strip_tac \\ rveq \\ fs [])
  \\ rfs [] \\ rveq
  \\ drule (GEN_ALL evaluate_assoc_swap)
  \\ ntac 2 (disch_then drule)
  \\ Cases_on `evaluate ([apply_op op e1 e2], env, s)`
  \\ disch_then drule
  \\ pop_assum mp_tac
  \\ simp [evaluate_def, apply_op_def]);

val rewrite_op_preserves_op = Q.store_thm ("rewrite_op_preserves_op",
  `∀iop name op xs exp2.
      rewrite_op iop name (Op op xs) = (T, exp2) ⇒
        ∃e1 e2. exp2 = Op op [e1;e2]`,
  rpt gen_tac
  \\ once_rewrite_tac [rewrite_op_def]
  \\ Cases_on `iop` \\ Cases_on `op` \\ fs [op_eq_def]
  \\ TOP_CASE_TAC
  \\ TOP_CASE_TAC
  \\ rpt (pairarg_tac \\ fs [])
  \\ every_case_tac \\ fs [assoc_swap_def, apply_op_def, to_op_def]
  \\ every_case_tac \\ rw []);

val rewrite_op_no_err = Q.store_thm ("rewrite_op_no_err",
  `∀op name exp env (s:'ffi bviSem$state) r t p exp2 e1 e2.
      evaluate ([exp], env, s) = (r, t) ∧
      r ≠ Rerr (Rabort Rtype_error) ∧
      rewrite_op op name exp = (p, exp2) ⇒
        if p then
          (get_bin_args exp2 = SOME (e1, e2) ⇒ no_err e2)
        else
          exp = exp2`,
  ho_match_mp_tac rewrite_op_ind
  \\ rpt gen_tac \\ strip_tac \\ rpt gen_tac
  \\ strip_tac
  \\ reverse (Cases_on `p`)
  >-
    (simp_tac bool_ss []
    \\ drule (GEN_ALL evaluate_rewrite_op)
    \\ disch_then drule
    \\ disch_then drule
    \\ simp [])
  \\ simp_tac bool_ss []
  \\ strip_tac \\ fs [] \\ rveq
  \\ pop_assum mp_tac
  \\ once_rewrite_tac [rewrite_op_def]
  \\ IF_CASES_TAC \\ fs []
  \\ TOP_CASE_TAC \\ fs []
  \\ rpt (pairarg_tac \\ fs []) \\ rveq
  \\ IF_CASES_TAC
  >-
    (ntac 2 (IF_CASES_TAC \\ fs [])
    \\ simp [assoc_swap_def]
    \\ IF_CASES_TAC \\ fs []
    >-
      (simp [apply_op_def]
      \\ strip_tac \\ rveq \\ fs [])
    \\ TOP_CASE_TAC \\ fs []
    >-
      (simp [apply_op_def]
      \\ strip_tac \\ rveq \\ fs [])
    \\ simp [apply_op_def]
    \\ strip_tac \\ rveq \\ fs []
    \\ rveq
    \\ Cases_on `op`
    \\ fs [is_rec_or_rec_binop_def,
           no_err_def,
           to_op_def,
           is_rec_def,
           get_bin_args_def])
  \\ ntac 2 (IF_CASES_TAC \\ fs [])
  \\ simp [assoc_swap_def, apply_op_def]
  \\ IF_CASES_TAC \\ fs []
  >-
    (strip_tac \\ rveq
    \\ Cases_on `op`
    \\ fs [is_rec_or_rec_binop_def,
           no_err_def,
           to_op_def,
           is_rec_def,
           get_bin_args_def])
  \\ TOP_CASE_TAC \\ fs []
  >-
    (strip_tac \\ rveq
    \\ Cases_on `op`
    \\ fs [op_eq_def,
           get_bin_args_def])
  \\ rveq
  \\ fs [op_eq_to_op]
  \\ strip_tac \\ rveq
  \\ Cases_on `op`
  \\ fs [is_rec_or_rec_binop_def,
         no_err_def,
         to_op_def,
         is_rec_def,
         get_bin_args_def]);

val rewrite_op_no_err_spec = Q.store_thm ("rewrite_op_no_err_spec",
  `∀op name exp env (s:'ffi bviSem$state) r t e1 e2.
      evaluate ([exp], env, s) = (r, t) ∧
      r ≠ Rerr (Rabort Rtype_error) ∧
      rewrite_op op name exp = (T, exp2) ∧
      get_bin_args exp2 = SOME (e1, e2) ⇒
        no_err e2`,
  rpt strip_tac
  \\ imp_res_tac rewrite_op_no_err \\ fs []);

val rewrite_op_noopt = Q.prove (
  `rewrite_op op name exp = (F, exp2) ⇒ exp = exp2`,
  once_rewrite_tac [rewrite_op_def]
  \\ IF_CASES_TAC \\ fs []
  \\ TOP_CASE_TAC \\ fs []
  \\ rveq
  \\ rpt (pairarg_tac \\ fs []) \\ rveq
  \\ every_case_tac \\ fs [] \\ rveq \\ fs []);

val check_exp_IMP_to_op = Q.store_thm ("check_exp_IMP_to_op",
  `∀op nm xs p iop.
      check_exp nm (Op op xs) = SOME (p, iop) ⇒
        op = to_op iop`,
  Cases
  \\ fs [check_exp_def, is_ok_type_def,
         is_arithmetic_def, tail_is_ok_def]
  \\ ntac 3 gen_tac
  \\ Cases \\ fs [from_op_def, to_op_def]
  \\ TOP_CASE_TAC \\ fs []);

val rewrite_op_binargs = Q.store_thm ("rewrite_op_binargs",
  `∀iop name op xs exp.
     rewrite_op iop name (Op op xs) = (T, exp) ⇒
       ∃e1 e2. get_bin_args exp = SOME (e1, e2)`,
  Cases
  \\ once_rewrite_tac [rewrite_op_def]
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

val rewrite_op_is_rec = Q.store_thm ("rewrite_op_is_rec",
  `∀iop name op xs e1 e2.
     iop ≠ Noop ∧
     rewrite_op iop name (Op op xs) = (T, Op op [e1; e2]) ⇒
       is_rec name e1`,
  Cases
  \\ rpt gen_tac
  \\ once_rewrite_tac [rewrite_op_def]
  \\ simp [op_eq_def]
  \\ IF_CASES_TAC \\ fs []
  \\ ntac 2 TOP_CASE_TAC
  \\ rpt (pairarg_tac \\ fs []) \\ rveq
  \\ IF_CASES_TAC \\ fs []
  >-
    (ntac 2 (IF_CASES_TAC \\ fs [])
    \\ fs [assoc_swap_def, apply_op_def]
    \\ qpat_x_assum `is_rec_or_rec_binop _ _ y1` mp_tac
    \\ simp [is_rec_or_rec_binop_def]
    \\ strip_tac
    >- (strip_tac \\ every_case_tac \\ fs [] \\ rveq \\ fs [is_rec_def])
    \\ Cases_on `y1` \\ fs [is_rec_def, get_bin_args_def]
    \\ rpt strip_tac \\ rveq \\ fs []
    \\ every_case_tac \\ fs [] \\ rveq \\ fs [get_bin_args_def])
  \\ ntac 2 (IF_CASES_TAC \\ fs [])
  \\ simp [assoc_swap_def, apply_op_def]
  \\ strip_tac
  \\ Cases_on `y2` \\ fs [is_rec_or_rec_binop_def, is_rec_def, get_bin_args_def]
  \\ rveq
  \\ every_case_tac \\ fs [] \\ rveq \\ fs [is_rec_def]);

(* TODO for append, parametrise on op *)
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

val code_rel_def = Define `
  code_rel c1 c2 ⇔
    ∀name args exp op.
      lookup name c1 = SOME (args, exp) ⇒
      (check_exp name exp = NONE ⇒
        lookup name c2 = SOME (args, exp)) ∧
      (check_exp name exp = SOME op ⇒
        ∃n. ∀exp_aux exp_opt.
        compile_exp n name args exp = SOME (exp_aux, exp_opt) ⇒
          lookup name c2 = SOME (args, exp_aux) ∧
          lookup n c2 = SOME (args + 1, exp_opt))`;

val code_rel_find_code_SOME = Q.prove (
  `∀c1 c2 x (args: v list) exp.
     code_rel c1 c2 ∧
     find_code (SOME n) args c1 = SOME (args, exp) ⇒
       find_code (SOME n) args c2 ≠ NONE`,
  rpt gen_tac \\ strip_tac
  \\ qhdtm_x_assum `find_code` mp_tac \\ simp [find_code_def]
  \\ ntac 2 TOP_CASE_TAC \\ fs []
  \\ strip_tac \\ rveq
  \\ fs [code_rel_def]
  \\ TOP_CASE_TAC
  \\ TRY TOP_CASE_TAC \\ fs []
  \\ first_x_assum drule
  \\ Cases_on `check_exp n exp`
  \\ simp [compile_exp_def]
  \\ TRY CASE_TAC \\ fs []
  \\ rw []
  \\ pairarg_tac \\ fs []);

val code_rel_find_code_NONE = Q.prove (
  `∀c1 c2 x (args: v list) exp.
     code_rel c1 c2 ∧
     find_code NONE args c1 = SOME (FRONT args, exp) ⇒
       find_code NONE args c2 ≠ NONE`,
  rpt gen_tac \\ strip_tac
  \\ qhdtm_x_assum `find_code` mp_tac
  \\ simp [find_code_def]
  \\ ntac 3 TOP_CASE_TAC \\ fs []
  \\ strip_tac \\ rveq
  \\ TOP_CASE_TAC
  \\ TRY TOP_CASE_TAC
  \\ fs [code_rel_def]
  \\ first_x_assum drule
  \\ Cases_on `check_exp n exp` \\ fs []
  \\ simp [compile_exp_def]
  \\ TRY CASE_TAC \\ fs []
  \\ rw []
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
  \\ CCONTR_TAC
  \\ fs []
  \\ Cases_on `lookup x c1`
  >- fs [lookup_NONE_domain]
  \\ fs [GSYM lookup_NONE_domain]
  \\ rename1 `SOME exp`
  \\ PairCases_on `exp`
  \\ first_x_assum drule \\ fs []
  \\ Cases_on `check_exp x exp1` \\ fs []
  \\ simp [compile_exp_def]
  \\ CASE_TAC \\ fs []
  \\ rw []
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
  `∀op name exp p exp2.
     rewrite_op op name exp = (p, exp2) ∧
     op_eq op exp ⇒
       op_eq op exp2`,
  ho_match_mp_tac rewrite_op_ind
  \\ rpt strip_tac
  \\ qhdtm_x_assum `rewrite_op` mp_tac
  \\ once_rewrite_tac [rewrite_op_def]
  \\ IF_CASES_TAC \\ fs []
  \\ TOP_CASE_TAC \\ fs []
  >- (strip_tac \\ rveq \\ fs [])
  \\ rpt (pairarg_tac \\ fs []) \\ rveq
  \\ IF_CASES_TAC \\ fs []
  >-
    (IF_CASES_TAC \\ fs []
    >- (strip_tac \\ rveq \\ fs [])
    \\ reverse IF_CASES_TAC \\ fs []
    >- (strip_tac \\ rveq \\ fs [])
    \\ strip_tac \\ rveq
    \\ simp [assoc_swap_def, apply_op_def]
    \\ every_case_tac \\ fs [])
  \\ reverse IF_CASES_TAC \\ fs []
  >- (strip_tac \\ rveq \\ fs [])
  \\ reverse IF_CASES_TAC \\ fs []
  >- (strip_tac \\ rveq \\ fs [])
  \\ strip_tac \\ rveq
  \\ simp [assoc_swap_def, apply_op_def]
  \\ every_case_tac \\ fs []);

val rewrite_op_exp_size = Q.store_thm ("rewrite_op_exp_size",
  `∀op nm exp p exp2.
    rewrite_op op nm exp = (p, exp2) ⇒
      exp_size exp = exp_size exp2`,
  ho_match_mp_tac rewrite_op_ind
  \\ rpt strip_tac
  \\ pop_assum mp_tac
  \\ once_rewrite_tac [rewrite_op_def]
  \\ IF_CASES_TAC \\ fs []
  \\ TOP_CASE_TAC \\ fs []
  \\ rpt (pairarg_tac \\ fs []) \\ rveq
  \\ IF_CASES_TAC \\ fs []
  >-
    (ntac 2 (IF_CASES_TAC \\ fs [])
    \\ strip_tac \\ rveq
    \\ simp [assoc_swap_def, apply_op_def]
    \\ TOP_CASE_TAC \\ fs []
    >- fs [bviTheory.exp_size_def]
    \\ rveq
    \\ TOP_CASE_TAC \\ fs []
    >- fs [bviTheory.exp_size_def]
    \\ rveq
    \\ fs [op_eq_to_op] \\ rveq
    \\ fs [bviTheory.exp_size_def])
  \\ ntac 2 (IF_CASES_TAC \\ fs [])
  \\ strip_tac \\ rveq
  \\ simp [assoc_swap_def, apply_op_def]
  \\ TOP_CASE_TAC \\ fs []
  >- fs [bviTheory.exp_size_def]
  \\ TOP_CASE_TAC
  >- fs [bviTheory.exp_size_def]
  \\ fs [] \\ rveq
  \\ fs [op_eq_to_op] \\ rveq
  \\ fs [bviTheory.exp_size_def]);

val optimized_code_def = Define `
  optimized_code name arity exp n c op =
    ∃exp_aux exp_opt p.
        compile_exp n name arity exp = SOME (exp_aux, exp_opt) ∧
        check_exp name exp = SOME (p, op) ∧
        lookup name c = SOME (arity, exp_aux) ∧
        lookup n c    = SOME (arity + 1, exp_opt)
  `;

val env_rel_extra = Q.prove (
  `∀env1 env2 acc.
     env_rel F acc env1 env2 ⇒
       ∃extra. env1 ++ extra = env2`,
  simp [env_rel_def]
  \\ rpt strip_tac
  \\ imp_res_tac IS_PREFIX_APPEND
  \\ rw []);

val evaluate_env_rel_err = Q.prove (
  `∀xs env1 (s:'ffi bviSem$state) vs t acc env2.
     evaluate (xs, env1, s) = (Rval vs, t) ∧
     env_rel F acc env1 env2 ⇒
       evaluate (xs, env2, s) = (Rval vs, t)`,
  rpt strip_tac
  \\ imp_res_tac env_rel_extra \\ rveq
  \\ imp_res_tac evaluate_env_extra \\ fs []);

val tail_is_ok_SOME_rewrite_tail = Q.store_thm ("tail_is_ok_SOME_rewrite_tail",
  `∀n op nm acc exp exp2 q.
     tail_is_ok nm exp = SOME (q, op) ∧
     rewrite_tail n op nm acc exp = (p, exp2) ⇒ p`,
  ho_match_mp_tac rewrite_tail_ind
  \\ rpt conj_tac
  \\ TRY
    (rpt strip_tac
    \\ fs [tail_is_ok_def, rewrite_tail_def]
    \\ pairarg_tac \\ fs []
    \\ NO_TAC)
  \\ TRY
    (rpt strip_tac
    \\ fs [tail_is_ok_def, rewrite_tail_def]
    \\ rpt (pairarg_tac \\ fs [])
    \\ qpat_x_assum `_ = SOME _` mp_tac
    \\ reverse TOP_CASE_TAC \\ fs []
    >-
      (TOP_CASE_TAC \\ fs []
      \\ TOP_CASE_TAC \\ fs []
      \\ metis_tac [])
    \\ ntac 2 (TOP_CASE_TAC \\ fs [])
    \\ metis_tac []
    \\ NO_TAC)
  \\ rpt strip_tac
  \\ fs [tail_is_ok_def, rewrite_tail_def]
  \\ every_case_tac \\ fs [] \\ rveq \\ fs []
  \\ rveq
  \\ pop_assum mp_tac
  \\ fs [from_op_def]
  \\ once_rewrite_tac [rewrite_op_def]
  \\ IF_CASES_TAC \\ fs []
  \\ TOP_CASE_TAC \\ fs []
  \\ rpt (pairarg_tac \\ fs []) \\ rveq
  \\ every_case_tac \\ fs []
  \\ TRY
    (Cases_on `y2`
    \\ fs [no_err_def, is_rec_or_rec_binop_def, is_rec_def]
    \\ rveq
    >-
      (every_case_tac \\ fs [] \\ rveq
      \\ Cases_on `q` \\ fs [is_rec_def, no_err_def, to_op_def])
    \\ fs [to_op_def]
    \\ simp [assoc_swap_def, to_op_def]
    \\ TOP_CASE_TAC
    >-
      (simp [apply_op_def]
      \\ CCONTR_TAC \\ fs [])
    \\ fs [] \\ rveq
    \\ simp [apply_op_def, to_op_def]
    \\ CCONTR_TAC \\ fs []
    \\ rveq
    \\ fs [get_bin_args_def]
    \\ NO_TAC)
  \\ fs [assoc_swap_def, apply_op_def, to_op_def]
  \\ every_case_tac \\ fs [] \\ rveq \\ fs []
  \\ CCONTR_TAC \\ fs [] \\ rveq
  \\ fs [get_bin_args_def]);

val tail_is_ok_NONE_rewrite_tail = Q.store_thm ("tail_is_ok_NONE_rewrite_tail",
  `∀n op nm acc exp exp2.
     tail_is_ok nm exp = NONE ∧
     op ≠ Noop ∧
     rewrite_tail n op nm acc exp = (p, exp2) ⇒
       ¬p`,
  ho_match_mp_tac rewrite_tail_ind
  \\ rpt conj_tac
  \\ rpt strip_tac
  \\ TRY
    (fs [rewrite_tail_def, tail_is_ok_def]
    \\ pairarg_tac \\ fs [] \\ rveq
    \\ NO_TAC)
  \\ TRY
    (fs [rewrite_tail_def, tail_is_ok_def]
    \\ every_case_tac \\ fs []
    \\ rpt (pairarg_tac \\ fs [])
    \\ NO_TAC)
  \\ TRY
    (fs [rewrite_tail_def]
    \\ every_case_tac \\ fs [] \\ rveq
    \\ pop_assum mp_tac \\ simp []
    \\ once_rewrite_tac [rewrite_op_def]
    \\ IF_CASES_TAC \\ fs []
    \\ TOP_CASE_TAC \\ fs []
    \\ NO_TAC)
  \\ rename1 `Op iop xs: bvi$exp`
  \\ fs [tail_is_ok_def]
  \\ every_case_tac \\ fs []
  >-
    (pop_assum mp_tac \\ simp []
    \\ once_rewrite_tac [rewrite_op_def]
    \\ IF_CASES_TAC \\ fs []
    \\ Cases_on `iop` \\ fs [to_op_def, from_op_def])
  \\ fs [rewrite_tail_def]
  \\ qpat_x_assum `_ = (T,_)` mp_tac
  \\ simp [rewrite_tail_def]
  \\ TOP_CASE_TAC \\ fs []
  \\ IF_CASES_TAC \\ fs []
  \\ imp_res_tac rewrite_op_preserves_op \\ rveq
  \\ `from_op iop = op` by
    (pop_assum mp_tac
    \\ once_rewrite_tac [rewrite_op_def]
    \\ IF_CASES_TAC \\ fs []
    \\ Cases_on `iop` \\ Cases_on `op` \\ fs [to_op_def, from_op_def])
  \\ rveq
  \\ fs []);

val rewrite_tail_Noop = Q.store_thm ("rewrite_tail_Noop",
  `∀n op nm acc exp p exp2.
     rewrite_tail n op nm acc exp = (p, exp2) ⇒
       (op = Noop ⇒ ¬p)`,
  ho_match_mp_tac rewrite_tail_ind
  \\ rpt strip_tac
  \\ TRY
    (fs [rewrite_tail_def]
    \\ pairarg_tac \\ fs []
    \\ NO_TAC)
  >-
    (fs [rewrite_tail_def]
    \\ rpt (pairarg_tac \\ fs []) \\ rveq
    \\ fs [])
  \\ qhdtm_x_assum `rewrite_tail` mp_tac
  \\ simp [rewrite_tail_def]
  \\ once_rewrite_tac [rewrite_op_def]
  \\ fs [op_eq_def]);

(* TODO:

   For non-arithmetic operations, (∃op' check_exp ... ⇒ ...) will have
   to include some op_rel op op' which says that op and op' operate on
   the same type. *)
val evaluate_rewrite_tail = Q.store_thm ("evaluate_rewrite_tail",
  `∀xs (s:'ffi bviSem$state) env1 r t opt_here c acc env2 nm.
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
               (∃op' p. check_exp nm (HD xs) = SOME (p, op') ∧ op' ≠ Noop) ⇒
                 let (p, x) = rewrite_tail n op nm acc (HD xs) in
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
      \\ pairarg_tac \\ fs []
      \\ imp_res_tac check_exp_Arith
      \\ imp_res_tac check_exp_IMP_to_op
      \\ fs [rewrite_tail_def, evaluate_def, apply_op_def]
      \\ rpt (pairarg_tac \\ fs [])
      \\ rveq
      \\ simp [evaluate_def])
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
        \\ first_assum (qspecl_then [`[x2]`,`s2`] mp_tac)
        \\ imp_res_tac evaluate_clock
        \\ imp_res_tac evaluate_code_const
        \\ simp [bviTheory.exp_size_def]
        \\ disch_then drule
        \\ disch_then (qspec_then `F` drule) \\ fs [])
      \\ IF_CASES_TAC \\ fs []
      \\ strip_tac
      \\ first_assum (qspecl_then [`[x3]`,`s2`] mp_tac)
      \\ imp_res_tac evaluate_clock
      \\ imp_res_tac evaluate_code_const
      \\ simp [bviTheory.exp_size_def]
      \\ disch_then drule
      \\ disch_then (qspec_then `F` drule) \\ fs [])
    \\ rename1 `(Rval a, s2 with code := c)`
    \\ strip_tac
    \\ conj_tac
    >-
      (IF_CASES_TAC \\ fs []
      >-
        (first_x_assum (qspecl_then [`[x2]`,`s2`] mp_tac)
        \\ simp [bviTheory.exp_size_def]
        \\ imp_res_tac evaluate_clock \\ fs []
        \\ imp_res_tac evaluate_code_const \\ fs []
        \\ ntac 2 (disch_then drule) \\ fs [])
      \\ IF_CASES_TAC \\ fs []
      \\ first_x_assum (qspecl_then [`[x3]`,`s2`] mp_tac)
      \\ simp [bviTheory.exp_size_def]
      \\ imp_res_tac evaluate_clock \\ fs []
      \\ imp_res_tac evaluate_code_const \\ fs []
      \\ ntac 2 (disch_then drule) \\ fs [])
    \\ rpt strip_tac
    \\ pairarg_tac \\ fs []
    \\ fs [rewrite_tail_def]
    \\ rpt (pairarg_tac \\ fs []) \\ rveq
    \\ `acc < LENGTH env2` by fs [env_rel_def]
    \\ IF_CASES_TAC
    >- (* r2 *)
      (IF_CASES_TAC
      >- (* r3 *)
        (simp [evaluate_def, apply_op_def]
        \\ IF_CASES_TAC \\ fs []
        >-
          (first_x_assum (qspecl_then [`[x2]`,`s2`] mp_tac)
          \\ imp_res_tac evaluate_code_const
          \\ imp_res_tac evaluate_clock
          \\ simp [bviTheory.exp_size_def]
          \\ disch_then drule
          \\ disch_then (qspec_then `T` drule)
          \\ disch_then drule
          \\ disch_then (qspec_then `nm` drule)
          \\ strip_tac
          \\ first_x_assum drule
          \\ disch_then drule
          \\ pairarg_tac \\ fs [] \\ rveq
          \\ impl_tac
          >-
            (simp [check_exp_def]
            \\ `is_ok_type x2` by fs [check_exp_def, is_ok_type_def]
            \\ simp []
            \\ reverse (Cases_on `p`)
            >-
              (fs [check_exp_def, tail_is_ok_def]
              \\ Cases_on `tail_is_ok nm x2` \\ fs []
              >-
                (Cases_on `tail_is_ok nm x3` \\ fs []
                \\ every_case_tac \\ fs [])
              \\ every_case_tac \\ fs [])
            \\ fs [check_exp_def, tail_is_ok_def]
            \\ Cases_on `tail_is_ok nm x2` \\ fs []
            >-
              (Cases_on `tail_is_ok nm x3` \\ fs []
              \\ every_case_tac \\ fs []
              \\ rveq
              \\ imp_res_tac tail_is_ok_NONE_rewrite_tail \\ fs []
              \\ metis_tac [rewrite_tail_Noop])
            \\ every_case_tac \\ fs [])
          \\ fs [apply_op_def, evaluate_def])
        \\ IF_CASES_TAC \\ fs []
        \\ first_x_assum (qspecl_then [`[x3]`,`s2`] mp_tac)
        \\ imp_res_tac evaluate_code_const
        \\ imp_res_tac evaluate_clock
        \\ simp [bviTheory.exp_size_def]
        \\ disch_then drule
        \\ disch_then (qspec_then `T` drule)
        \\ disch_then drule
        \\ disch_then (qspec_then `nm` drule)
        \\ strip_tac
        \\ first_x_assum drule
        \\ disch_then drule
        \\ pairarg_tac \\ fs [] \\ rveq
        \\ impl_tac
        >-
          (Cases_on `check_exp nm x2` \\ fs []
          >-
            (fs [check_exp_def, tail_is_ok_def]
            \\ Cases_on `tail_is_ok nm x2` \\ fs []
            >-
              (
              Cases_on `tail_is_ok nm x3` \\ fs []
              \\ every_case_tac \\ fs [] \\ rveq
              \\ imp_res_tac tail_is_ok_NONE_rewrite_tail \\ fs []
              \\ metis_tac [rewrite_tail_Noop])
            \\ Cases_on `tail_is_ok nm x3` \\ fs []
            >-
              (every_case_tac \\ fs [] \\ rveq
              \\ imp_res_tac tail_is_ok_NONE_rewrite_tail \\ fs []
              \\ metis_tac [rewrite_tail_Noop])
            \\ every_case_tac \\ fs []
            \\ rveq
            \\ fs [is_ok_type_def])
          \\ reverse (Cases_on `p`) \\ fs []
          >-
            (fs [check_exp_def, tail_is_ok_def]
            \\ Cases_on `tail_is_ok nm x3` \\ fs []
            >-
              (every_case_tac \\ fs [] \\ rveq
              \\ imp_res_tac tail_is_ok_NONE_rewrite_tail \\ fs []
              \\ metis_tac [rewrite_tail_Noop])
            \\ every_case_tac \\ fs [])
          \\ Cases_on `check_exp nm x3` \\ fs []
          >-
            (fs [check_exp_def, tail_is_ok_def]
            \\ Cases_on `tail_is_ok nm x3` \\ fs []
            >- (every_case_tac \\ fs [])
            \\ fs [is_ok_type_def])
          \\ rename1 `_ = SOME opr`
          \\ PairCases_on `opr`
          \\ imp_res_tac check_exp_Arith
          \\ rw [])
        \\ simp [evaluate_def, apply_op_def])
      (* ¬r3 *)
      \\ rveq
      \\ qpat_x_assum `_ = (r, t)` mp_tac
      \\ IF_CASES_TAC
      >-
        (strip_tac
        \\ first_x_assum (qspecl_then [`[x2]`,`s2`] mp_tac)
        \\ imp_res_tac evaluate_code_const
        \\ imp_res_tac evaluate_clock
        \\ simp [bviTheory.exp_size_def]
        \\ disch_then drule
        \\ disch_then (qspec_then `T` drule)
        \\ disch_then drule
        \\ disch_then (qspec_then `nm` drule)
        \\ strip_tac
        \\ first_x_assum drule
        \\ disch_then drule
        \\ impl_tac
        >-
          (fs [check_exp_def, tail_is_ok_def, is_ok_type_def]
          \\ every_case_tac \\ fs [] \\ rveq
          \\ imp_res_tac tail_is_ok_NONE_rewrite_tail \\ fs []
          \\ metis_tac [rewrite_tail_Noop])
        \\ pairarg_tac \\ fs []
        \\ simp [apply_op_def, evaluate_def])
      \\ IF_CASES_TAC \\ fs []
      \\ strip_tac
      \\ first_x_assum (qspecl_then [`[x3]`,`s2`] mp_tac)
      \\ imp_res_tac evaluate_code_const
      \\ imp_res_tac evaluate_clock
      \\ simp [bviTheory.exp_size_def]
      \\ disch_then drule
      \\ disch_then (qspec_then `F` drule)
      \\ disch_then drule \\ fs []
      \\ simp [apply_op_def, evaluate_def])
    (* ¬r2 *)
    \\ IF_CASES_TAC
    >- (* r3 *)
      (qpat_x_assum `_ = (r, t)` mp_tac
      \\ IF_CASES_TAC
      >-
        (strip_tac
        \\ first_assum (qspecl_then [`[x2]`,`s2`] mp_tac)
        \\ imp_res_tac evaluate_code_const
        \\ imp_res_tac evaluate_clock
        \\ simp [bviTheory.exp_size_def]
        \\ disch_then drule
        \\ disch_then (qspec_then `F` drule)
        \\ disch_then drule \\ fs []
        \\ strip_tac
        \\ first_assum (qspecl_then [`[x3]`,`s2`] mp_tac)
        \\ simp [bviTheory.exp_size_def]
        \\ Cases_on `evaluate ([x3], env1, s2)`
        \\ disch_then drule
        \\ disch_then (qspec_then `T` drule)
        \\ disch_then drule
        \\ disch_then (qspec_then `nm` mp_tac)
        \\ Cases_on `q = Rerr (Rabort Rtype_error)`
        >- simp [evaluate_def, apply_op_def]
        \\ simp []
        \\ strip_tac
        \\ first_x_assum drule
        \\ impl_tac
        >-
          (fs [check_exp_def, tail_is_ok_def, is_ok_type_def]
          \\ Cases_on `tail_is_ok nm x2` \\ fs []
          >-
            (Cases_on `tail_is_ok nm x3` \\ fs []
            \\ Cases_on `x` \\ fs [])
          \\ Cases_on `x` \\ fs []
          \\ Cases_on `tail_is_ok nm x3` \\ fs []
          >-
            (rveq
            \\ imp_res_tac tail_is_ok_NONE_rewrite_tail \\ fs []
            \\ metis_tac [rewrite_tail_Noop])
          \\ rveq
          \\ Cases_on `x` \\ fs []
          \\ imp_res_tac tail_is_ok_Arith)
        \\ pairarg_tac \\ fs [] \\ rveq
        \\ simp [evaluate_def, apply_op_def])
      \\ IF_CASES_TAC \\ fs []
      \\ strip_tac
      \\ first_assum (qspecl_then [`[x3]`,`s2`] mp_tac)
      \\ imp_res_tac evaluate_code_const
      \\ imp_res_tac evaluate_clock
      \\ simp [bviTheory.exp_size_def]
      \\ disch_then drule
      \\ disch_then (qspec_then `T` drule)
      \\ disch_then drule
      \\ disch_then (qspec_then `nm` drule)
      \\ strip_tac
      \\ first_x_assum drule
      \\ disch_then drule
      \\ impl_tac
      >-
        (fs [check_exp_def, tail_is_ok_def, is_ok_type_def]
        \\ every_case_tac \\ fs []
        >-
          (rveq
          \\ imp_res_tac tail_is_ok_NONE_rewrite_tail
          \\ fs []
          \\ metis_tac [rewrite_tail_Noop])
        \\ rveq
        \\ imp_res_tac tail_is_ok_Arith)
      \\ pairarg_tac \\ fs [] \\ rveq
      \\ simp [evaluate_def, apply_op_def])
    (* ¬r2 ¬r3 *)
    \\ rveq
    \\ fs [check_exp_def, tail_is_ok_def, is_ok_type_def]
    \\ qpat_x_assum `_ = (r,t)` mp_tac
    \\ IF_CASES_TAC
    >-
      (strip_tac
      \\ first_assum (qspecl_then [`[x2]`,`s2`] mp_tac)
      \\ imp_res_tac evaluate_code_const
      \\ imp_res_tac evaluate_clock
      \\ simp [bviTheory.exp_size_def]
      \\ disch_then drule
      \\ disch_then (qspec_then `F` drule)
      \\ disch_then drule \\ fs []
      \\ simp [apply_op_def, evaluate_def])
    \\ IF_CASES_TAC \\ fs []
    \\ strip_tac
    \\ first_assum (qspecl_then [`[x3]`,`s2`] mp_tac)
    \\ imp_res_tac evaluate_code_const
    \\ imp_res_tac evaluate_clock
    \\ simp [bviTheory.exp_size_def]
    \\ disch_then drule
    \\ disch_then (qspec_then `F` drule)
    \\ disch_then drule \\ fs []
    \\ simp [apply_op_def, evaluate_def])
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
      \\ imp_res_tac do_app_with_code_err
      \\ imp_res_tac do_app_with_code
      \\ imp_res_tac do_app_err \\ fs []
      \\ first_assum drule \\ fs [])
    \\ rpt strip_tac
    \\ rpt (pairarg_tac \\ fs [])
    (*\\ imp_res_tac check_exp_Arith \\ rveq*)
    \\ imp_res_tac check_exp_IMP_to_op \\ rveq
    \\ rename1 `iop ≠ Noop`
    \\ qhdtm_x_assum `evaluate` mp_tac \\ simp [evaluate_def]
    \\ TOP_CASE_TAC
    \\ strip_tac
    \\ qhdtm_x_assum `rewrite_tail` mp_tac
    \\ simp [rewrite_tail_def]
    \\ CASE_TAC
    \\ IF_CASES_TAC \\ fs [] \\ rveq
    \\ drule rewrite_op_binargs
    \\ strip_tac \\ fs [] \\ rveq
    \\ simp [get_bin_args_def]
    \\ strip_tac \\ rveq
    \\ imp_res_tac rewrite_op_preserves_op \\ fs [] \\ rveq
    \\ `iop = op'` by
      (pop_assum mp_tac
      \\ once_rewrite_tac [rewrite_op_def]
      \\ IF_CASES_TAC \\ fs []
      \\ Cases_on `iop` \\ Cases_on `op'` \\ fs [to_op_def])
    \\ rveq
    \\ imp_res_tac rewrite_op_is_rec
    \\ Cases_on `e1` \\ fs [is_rec_def]
    \\ rename1 `Call ticks dest args hdl: bvi$exp`
    \\ Cases_on `hdl` \\ fs [is_rec_def] \\ rveq
    \\ simp [args_from_def, push_call_def]
    \\ first_assum (qspecl_then [`xs`,`s`] mp_tac)
    \\ simp [bviTheory.exp_size_def]
    \\ `env_rel F acc env1 env2` by fs [env_rel_def]
    \\ disch_then drule
    \\ disch_then (qspec_then `F` drule)
    \\ disch_then drule \\ fs []
    \\ impl_tac
    >- (every_case_tac \\ fs [] \\ rveq \\ fs [])
    \\ strip_tac
    (*\\ imp_res_tac rewrite_op_no_err_spec*)
    \\ `no_err e2` by
      (Cases_on `evaluate ([Op (to_op iop) xs], env1, s)`
      \\ drule (GEN_ALL rewrite_op_no_err_spec)
      \\ rfs [evaluate_def] \\ rveq
      \\ ntac 2 (disch_then drule) \\ fs [])
    (*\\ ntac 2 (pop_assum kall_tac)*)
    (*\\ fs [get_bin_args_def]*)
    (*\\ pop_assum mp_tac*)
    (*\\ simp [Once evaluate_def]*)
    (*\\ disch_then (qspecl_then [`t`,`s`,`env1`] mp_tac)*)
    (*\\ TOP_CASE_TAC*)
    (*\\ fs [] \\ rveq \\ strip_tac*)
    \\ imp_res_tac no_err_type_correct
    \\ Cases_on `evaluate ([Op (to_op iop) xs], env1, s)`
    \\ drule evaluate_rewrite_op
    \\ qmatch_asmsub_abbrev_tac `rewrite_op _ _ _ = (T, exp2)`
    \\ disch_then (qspecl_then [`iop`,`nm`,`T`, `exp2`] mp_tac)
    \\ unabbrev_all_tac \\ simp []
    \\ impl_tac
    >-
      (rfs [evaluate_def] \\ rveq
      \\ every_case_tac \\ fs [] \\ rveq \\ fs [])
    \\ `acc < LENGTH env2` by fs [env_rel_def]
    \\ qmatch_asmsub_abbrev_tac `rewrite_op _ _ _ = (T, exp2)`
    \\ `evaluate ([apply_op iop (Op (to_op iop) xs) (Var acc)],
          env2, s with code := c) =
        evaluate ([apply_op iop exp2 (Var acc)],
          env2, s with code := c)` by
      (Cases_on `evaluate ([Op (to_op iop) xs], env2, s with code := c)` \\ fs []
      \\ drule evaluate_rewrite_op
      \\ disch_then (qspecl_then [`iop`,`nm`,`T`,`exp2`] mp_tac)
      \\ simp [apply_op_def]
      \\ rfs [evaluate_def]
      \\ rveq
      \\ every_case_tac \\ fs [] \\ rveq \\ fs []
      \\ imp_res_tac evaluate_code_const \\ fs []
      \\ imp_res_tac code_rel_domain \\ fs []
      \\ imp_res_tac do_app_with_code \\ fs []
      \\ imp_res_tac do_app_err \\ fs [])
    \\ pop_assum (fn th => fs [th])
    \\ qunabbrev_tac `exp2`
    \\ simp [evaluate_def]
    \\ CASE_TAC
    \\ rename1 `_ = (res_args, st_args)`
    \\ first_assum (qspecl_then [`args`,`s`] mp_tac)
    \\ `exp2_size args < exp2_size xs` by
      (imp_res_tac rewrite_op_exp_size
      \\ fs [bviTheory.exp_size_def])
    \\ simp [bviTheory.exp_size_def]
    \\ disch_then drule
    \\ disch_then (qspec_then `F` drule)
    \\ disch_then drule \\ fs []
    \\ reverse (Cases_on `res_args`) \\ fs []
    >-
      (Cases_on `e = Rabort Rtype_error` \\ fs []
      >- (strip_tac \\ rveq \\ rfs [evaluate_def])
      \\ rpt strip_tac \\ rveq
      \\ once_rewrite_tac [evaluate_APPEND]
      \\ simp [apply_op_def, evaluate_def])
    \\ strip_tac
    \\ simp [find_code_def]
    \\ `lookup nm st_args.code = lookup nm s.code` by
      (imp_res_tac evaluate_code_const \\ fs [])
    \\ pop_assum (fn th => fs [th])
    \\ `∃l. EL acc env2 = Number l` by fs [env_rel_def]
    \\ reverse IF_CASES_TAC \\ fs []
    >-
      (strip_tac \\ rveq
      \\ once_rewrite_tac [evaluate_APPEND]
      \\ simp [evaluate_def, apply_op_def, find_code_def]
      \\ fs [optimized_code_def]
      \\ Cases_on `iop` \\ fs [to_op_def]
      \\ simp [do_app_def, do_app_aux_def, bvlSemTheory.do_app_def,
               bvl_to_bvi_id])
    \\ IF_CASES_TAC \\ fs []
    >-
      (strip_tac \\ rveq
      \\ simp [evaluate_APPEND]
      \\ fs [optimized_code_def, apply_op_def, evaluate_def, find_code_def]
      \\ Cases_on `iop` \\ fs [to_op_def]
      \\ simp [do_app_def, do_app_aux_def, bvlSemTheory.do_app_def,
               bvl_to_bvi_id])
    \\ CASE_TAC
    \\ rename1 `_ = (res_exp, st_exp)`
    \\ strip_tac
    \\ simp [evaluate_APPEND]
    \\ qhdtm_assum `optimized_code` mp_tac
    \\ simp_tac std_ss [optimized_code_def]
    \\ strip_tac \\ fs []
    \\ first_x_assum (qspecl_then [`[exp]`,`dec_clock (ticks+1) st_args`] mp_tac)
    \\ `(dec_clock (ticks+1) st_args).clock < s.clock` by
      (imp_res_tac evaluate_clock
      \\ fs [dec_clock_def])
    \\ simp []
    \\ disch_then drule
    \\ `code_rel st_args.code c` by (imp_res_tac evaluate_code_const \\ fs [])
    \\ disch_then (qspec_then `T` assume_tac) \\ fs []
    \\ simp [apply_op_def, evaluate_def]
    \\ `∃j.
          do_app (to_op iop) [Number l; Number k] (st_args with code := c) =
            Rval (Number j, st_args with code := c)` by
      (Cases_on `iop` \\ fs [to_op_def]
      \\ simp [do_app_def, do_app_aux_def, bvlSemTheory.do_app_def,
               bvl_to_bvi_id])
    \\ fs [find_code_def, compile_exp_def]
    \\ rveq
    \\ `env_rel T (LENGTH a) a (a ++ [Number j])` by
      fs [env_rel_def, EL_LENGTH_APPEND]
    \\ first_assum drule
    \\ disch_then drule
    \\ disch_then (qspec_then `nm` mp_tac)
    \\ impl_tac
    >-
      (rfs [evaluate_def]
      \\ every_case_tac \\ fs [] \\ rveq \\ fs [] )
    \\ strip_tac \\ fs []
    \\ imp_res_tac evaluate_code_const \\ fs []
    \\ first_x_assum drule
    \\ disch_then drule
    \\ impl_tac
    >- fs []
    (*\\ simp [optimized_code_def, compile_exp_def]*)
    (*\\ disch_then (qspec_then `n` mp_tac) \\ fs []*)
    \\ rpt (pairarg_tac \\ fs [])
    \\ rfs []
    \\ strip_tac \\ pop_assum kall_tac
    \\ qpat_x_assum `env_rel _ _ a _` kall_tac
    \\ `env_rel T (LENGTH a) a (a ++ [op_id_val iop] ++ a)` by
      (fs [env_rel_def, EL_LENGTH_APPEND, EL_APPEND1, IS_PREFIX_APPEND]
      \\ Cases_on `iop` \\ fs [op_id_val_def])
    \\ first_x_assum drule
    \\ disch_then drule
    \\ disch_then (qspec_then `nm` mp_tac)
    \\ impl_tac
    >-
      (rfs [evaluate_def]
      \\ every_case_tac \\ fs [] \\ rveq \\ fs [] )
    \\ strip_tac \\ fs []
    \\ first_x_assum drule
    \\ disch_then drule
    \\ impl_tac
    >- fs []
    (*\\ simp [optimized_code_def, compile_exp_def]*)
    (*\\ disch_then (qspec_then `n` mp_tac) \\ fs []*)
    (*\\ rfs [] \\ rveq*)
    \\ pairarg_tac \\ fs []
    \\ rveq
    \\ simp [evaluate_let_wrap]
    \\ strip_tac \\ pop_assum kall_tac
    \\ simp [evaluate_def, apply_op_def]
    \\ fs [EL_LENGTH_APPEND, EL_APPEND1]
    \\ reverse CASE_TAC \\ fs []
    >- (CASE_TAC \\ fs [])
    \\ fs [check_exp_def]
    \\ imp_res_tac is_ok_type_IMP_Number \\ fs [] \\ rveq
    \\ Cases_on `iop`
    \\ fs [to_op_def, op_id_val_def]
    \\ fs [do_app_def, do_app_aux_def, bvlSemTheory.do_app_def,
             bvl_to_bvi_id, small_int_def, small_enough_int_def]
    \\ rveq \\ fs [bvl_to_bvi_id]
    \\ fs [integerTheory.INT_ADD_ASSOC, integerTheory.INT_MUL_ASSOC])
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
  \\ Cases_on `∃xs x1. h = Let xs x1` \\ fs [] \\ rveq
  >-
    (qpat_x_assum `evaluate _ = _` mp_tac \\ simp [evaluate_def]
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
      \\ imp_res_tac check_exp_Arith \\ rveq
      \\ fs [rewrite_tail_def, apply_op_def, evaluate_def]
      \\ rpt (pairarg_tac \\ fs []) \\ rveq
      \\ simp [evaluate_def])
    \\ strip_tac
    \\ first_assum (qspecl_then [`xs`,`s`] mp_tac)
    \\ simp [bviTheory.exp_size_def]
    \\ disch_then drule
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
    \\ first_x_assum (qspecl_then [`[x1]`,`s2`] mp_tac)
    \\ simp [bviTheory.exp_size_def]
    \\ ntac 4 (disch_then drule)
    \\ disch_then (qspec_then `nm` mp_tac)
    \\ rpt strip_tac \\ fs []
    \\ pairarg_tac \\ fs [] \\ rveq
    \\ first_x_assum drule
    \\ impl_tac
    >- rfs [check_exp_def, tail_is_ok_def, is_ok_type_def]
    \\ pairarg_tac \\ fs [] \\ rveq
    \\ `acc < LENGTH env2` by fs [env_rel_def]
    \\ imp_res_tac check_exp_Arith \\ fs [] \\ rveq
    \\ fs [rewrite_tail_def, apply_op_def]
    \\ pairarg_tac \\ fs [] \\ rveq
    \\ imp_res_tac evaluate_IMP_LENGTH \\ fs []
    \\ simp [evaluate_def, EL_APPEND2])
  \\ Cases_on `∃x1. h = Tick x1` \\ fs [] \\ rveq
  >-
    (qhdtm_x_assum `evaluate` mp_tac \\ simp [evaluate_def]
    \\ IF_CASES_TAC \\ fs []
    \\ strip_tac \\ rveq \\ fs []
    >-
      (rpt strip_tac
      \\ imp_res_tac check_exp_Arith \\ rveq
      \\ fs [rewrite_tail_def, apply_op_def, evaluate_def]
      \\ rpt (pairarg_tac \\ fs []) \\ rveq
      \\ simp [evaluate_def])
    \\ first_x_assum (qspecl_then [`[x1]`, `dec_clock 1 s`] mp_tac)
    \\ `(dec_clock 1 s).clock < s.clock` by fs [dec_clock_def]
    \\ simp [bviTheory.exp_size_def]
    \\ ntac 4 (disch_then drule)
    \\ disch_then (qspec_then `nm` mp_tac)
    \\ rpt strip_tac \\ fs []
    \\ pairarg_tac \\ fs [] \\ rveq
    \\ first_x_assum drule
    \\ impl_tac
    >- rfs [check_exp_def, tail_is_ok_def, is_ok_type_def]
    \\ pairarg_tac \\ fs [] \\ rveq
    \\ strip_tac
    \\ imp_res_tac check_exp_Arith \\ fs [] \\ rveq
    \\ `acc < LENGTH env2` by fs [env_rel_def]
    \\ fs [rewrite_tail_def, evaluate_def, apply_op_def]
    \\ rveq
    \\ simp [evaluate_def])
  \\ Cases_on `∃v. h = Var v` \\ fs [] \\ rveq
  >-
    (qhdtm_x_assum `evaluate` mp_tac \\ simp [evaluate_def]
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
    \\ pairarg_tac \\ fs [] \\ rveq
    \\ pop_assum mp_tac
    \\ simp [rewrite_tail_def, mk_tailcall_def]
    \\ imp_res_tac check_exp_Arith \\ rveq
    \\ once_rewrite_tac [rewrite_op_def]
    \\ simp [op_eq_def])
  \\ Cases_on `∃x1. h = Raise x1` \\ fs [] \\ rveq
  >-
    (simp [check_exp_def, tail_is_ok_def]
    \\ qhdtm_x_assum `evaluate` mp_tac \\ simp [evaluate_def]
    \\ TOP_CASE_TAC
    \\ strip_tac
    \\ first_x_assum (qspecl_then [`[x1]`,`s`] mp_tac)
    \\ simp [bviTheory.exp_size_def]
    \\ disch_then drule
    \\ `env_rel F acc env1 env2` by fs [env_rel_def]
    \\ disch_then (qspec_then `F` drule)
    \\ disch_then drule \\ fs []
    \\ impl_tac
    >- (every_case_tac \\ fs [] \\ rveq \\ fs [])
    \\ strip_tac
    \\ every_case_tac \\ fs [] \\ rveq \\ fs [])
  \\ Cases_on `h` \\ fs []);

val compile_prog_LENGTH = Q.store_thm ("compile_prog_LENGTH",
  `∀n prog. LENGTH (SND (bvi_tailrec$compile_prog n prog)) ≥ LENGTH prog`,
  recInduct compile_prog_ind
  \\ conj_tac
  >- fs [compile_prog_def]
  \\ rpt gen_tac \\ strip_tac
  \\ Cases_on `compile_exp n nm args exp` \\ fs []
  >-
    (fs [compile_prog_def]
    \\ pairarg_tac \\ fs [])
  \\ PairCases_on `x` \\ fs []
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
  `compile_exp n name args exp = NONE ⇒
     compile_exp (n + 2) name args exp = NONE`,
  fs [compile_exp_def]
  \\ every_case_tac
  \\ pairarg_tac \\ fs []);

val compile_prog_untouched = Q.store_thm ("compile_prog_untouched",
  `∀n prog prog2 name exp args.
     free_names n name ∧
     lookup name (fromAList prog) = SOME (args, exp) ∧
     check_exp name exp = NONE ∧
     compile_exp n name args exp = NONE ∧
     compile_prog n prog = (n1, prog2) ⇒
       lookup name (fromAList prog2) = SOME (args, exp)`,
  recInduct compile_prog_ind
  \\ rpt conj_tac \\ rpt gen_tac \\ strip_tac
  \\ fs [fromAList_def, lookup_def]
  \\ rpt gen_tac \\ strip_tac
  \\ Cases_on `nm = name` \\ fs [] \\ rveq
  >-
    (Cases_on `lookup name (fromAList xs)`
    \\ rfs [compile_prog_def]
    \\ pairarg_tac \\ fs [] \\ rveq
    \\ fs [fromAList_def])
  \\ fs [lookup_insert]
  \\ Cases_on `compile_exp n nm args exp` \\ fs []
  >-
    (rfs [compile_prog_def]
    \\ pairarg_tac \\ fs [] \\ rveq
    \\ fs [fromAList_def, lookup_insert])
  \\ PairCases_on `x` \\ rw []
  \\ imp_res_tac more_free_names
  \\ imp_res_tac compile_exp_next_addr
  \\ first_x_assum drule
  \\ disch_then drule \\ rfs []
  \\ strip_tac
  \\ rfs [compile_prog_def]
  \\ rpt (pairarg_tac \\ fs []) \\ rveq
  \\ fs [fromAList_def, lookup_insert, is_free_name]);

val EVERY_free_names_SUCSUC = Q.prove (
  `∀xs.
     EVERY (free_names n o FST) xs ⇒
       EVERY (free_names (n + 2) o FST) xs`,
  Induct
  \\ strip_tac \\ fs []
  \\ strip_tac
  \\ imp_res_tac more_free_names);

val compile_prog_touched = Q.store_thm ("compile_prog_touched",
  `∀n prog prog2 name exp args.
     ALL_DISTINCT (MAP FST prog) ∧
     EVERY (free_names n o FST) prog ∧
     free_names n name ∧
     lookup name (fromAList prog) = SOME (args, exp) ∧
     check_exp name exp = SOME op ∧
     compile_prog n prog = (n1, prog2) ⇒
      ∃k. ∀exp_aux exp_opt.
        compile_exp (n + 2 * k) name args exp = SOME (exp_aux, exp_opt) ⇒
          lookup name (fromAList prog2) = SOME (args, exp_aux) ∧
          lookup (n + 2 * k) (fromAList prog2) = SOME (args + 1, exp_opt)`,
  recInduct compile_prog_ind
  \\ conj_tac \\ rpt gen_tac \\ strip_tac
  >- fs [fromAList_def, lookup_def]
  \\ rpt gen_tac \\ strip_tac
  \\ fs [ALL_DISTINCT_APPEND]
  \\ qhdtm_x_assum `compile_prog` mp_tac
  \\ simp [compile_prog_def]
  \\ TOP_CASE_TAC \\ fs []
  >-
    (pairarg_tac \\ fs []
    \\ strip_tac \\ rveq
    \\ qhdtm_x_assum `compile_exp` mp_tac
    \\ simp [Once compile_exp_def]
    \\ qpat_x_assum `_ = SOME (_,_)` mp_tac
    \\ simp [lookup_insert, fromAList_def]
    \\ IF_CASES_TAC \\ fs []
    \\ strip_tac \\ rveq \\ fs []
    \\ TRY
      (CASE_TAC
      \\ pairarg_tac \\ fs [])
    \\ first_x_assum drule
    \\ disch_then drule \\ fs []
    \\ rpt strip_tac \\ rveq
    \\ qexists_tac `k`
    \\ fs [lookup_insert, fromAList_def, free_names_def])
  \\ TOP_CASE_TAC
  \\ pairarg_tac \\ fs []
  \\ strip_tac \\ rveq
  \\ qhdtm_x_assum `lookup` mp_tac
  \\ simp [lookup_insert, fromAList_def]
  \\ reverse IF_CASES_TAC
  >-
    (strip_tac \\ rveq \\ fs []
    \\ imp_res_tac more_free_names
    \\ rfs [EVERY_free_names_SUCSUC]
    \\ fs [lookup_insert, fromAList_def]
    \\ IF_CASES_TAC
    >- fs [free_names_def]
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

val check_exp_NONE_compile_exp = Q.prove (
  `check_exp name exp = NONE ⇒ compile_exp n name args exp = NONE`,
  fs [compile_exp_def]);

val check_exp_SOME_compile_exp = Q.prove (
  `check_exp name exp = SOME p ⇒
     ∃q. compile_exp n name args exp = SOME q`,
  fs [compile_exp_def]
  \\ CASE_TAC
  \\ pairarg_tac \\ fs []);

val EVERY_free_names_thm = Q.prove (
  `EVERY (free_names n o FST) prog ∧
   lookup name (fromAList prog) = SOME x ⇒
     free_names n name`,
  strip_tac
  \\ fs [lookup_fromAList, EVERY_MEM]
  \\ imp_res_tac ALOOKUP_MEM
  \\ first_x_assum (qspec_then `(name, x)` mp_tac) \\ rw []);

val compile_prog_code_rel = Q.store_thm ("compile_prog_code_rel",
  `ALL_DISTINCT (MAP FST prog) ∧
   EVERY (free_names n o FST) prog ∧
   compile_prog n prog = (n1, prog2) ⇒
     code_rel (fromAList prog) (fromAList prog2)`,
  simp [GSYM AND_IMP_INTRO]
  \\ fs [code_rel_def]
  \\ rpt strip_tac
  \\ imp_res_tac EVERY_free_names_thm
  >-
    (drule check_exp_NONE_compile_exp
     \\ imp_res_tac compile_prog_untouched)
  \\ drule compile_prog_touched
  \\ disch_then drule
  \\ strip_tac \\ rfs []
  \\ first_x_assum drule
  \\ disch_then drule
  \\ simp []
  \\ strip_tac
  \\ imp_res_tac (GEN_ALL check_exp_SOME_compile_exp)
  \\ first_x_assum (qspecl_then [`2 * k + n`, `args`] strip_assume_tac)
  \\ PairCases_on `q` \\ fs []
  \\ qexists_tac `2 * k + n`
  \\ rw []);

val evaluate_compile_prog = Q.store_thm ("evaluate_compile_prog",
  `EVERY (free_names n o FST) prog ∧
   ALL_DISTINCT (MAP FST prog) ∧
   evaluate ([Call 0 (SOME start) [] NONE], [],
             initial_state ffi0 (fromAList prog) k) = (r, s) ∧
   0 < k ∧
   r ≠ Rerr (Rabort Rtype_error) ⇒
   ∃ck s2.
     evaluate
      ([Call 0 (SOME start) [] NONE], [],
        initial_state ffi0 (fromAList (SND (compile_prog n prog))) (k + ck))
      = (r, s2) ∧
     state_rel s s2`,
  simp [GSYM AND_IMP_INTRO]
  \\ rpt strip_tac
  \\ qmatch_assum_abbrev_tac `evaluate (es,env,st1) = _`
  \\ `env_rel F 0 env env` by fs [env_rel_def]
  \\ drule (GEN_ALL compile_prog_code_rel)
  \\ disch_then drule
  \\ Cases_on `compile_prog n prog` \\ fs []
  \\ strip_tac
  \\ qmatch_assum_abbrev_tac `code_rel _ c`
  \\ `fromAList prog = st1.code` by fs [Abbr`st1`]
  \\ pop_assum (fn th => fs [th])
  \\ drule evaluate_rewrite_tail
  \\ disch_then (qspec_then `F` drule)
  \\ disch_then drule \\ fs []
  \\ strip_tac
  \\ qexists_tac `0` \\ fs [inc_clock_ZERO]
  \\ fs [Abbr`st1`]
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

val _ = export_theory();

