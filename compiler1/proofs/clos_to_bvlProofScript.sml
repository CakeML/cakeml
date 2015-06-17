open preamble
     closLangTheory closSemTheory
     bvlSemTheory bvlPropsTheory
     bvl_jumpProofTheory
     clos_to_bvlTheory;

val _ = new_theory"clos_to_bvlProof";

(* TODO: move? *)

val ARITH_TAC = intLib.ARITH_TAC;

val SUBMAP_FDOM_SUBSET = Q.store_thm("SUBMAP_FDOM_SUBSET",
  `f1 ⊑ f2 ⇒ FDOM f1 ⊆ FDOM f2`,
  rw[SUBMAP_DEF,SUBSET_DEF])

val SUBMAP_FRANGE_SUBSET = Q.store_thm("SUBMAP_FRANGE_SUBSET",
  `f1 ⊑ f2 ⇒ FRANGE f1 ⊆ FRANGE f2`,
  rw[SUBMAP_DEF,SUBSET_DEF,IN_FRANGE] >> metis_tac[])

val FDIFF_def = Define `
  FDIFF f1 s = DRESTRICT f1 (COMPL s)`;

val FDOM_FDIFF = prove(
  ``x IN FDOM (FDIFF refs f2) <=> x IN FDOM refs /\ ~(x IN f2)``,
  fs [FDIFF_def,DRESTRICT_DEF]);

val NUM_NOT_IN_FDOM =
  MATCH_MP IN_INFINITE_NOT_FINITE (CONJ INFINITE_NUM_UNIV
    (Q.ISPEC `f:num|->'a` FDOM_FINITE))
  |> SIMP_RULE std_ss [IN_UNIV]

val EXISTS_NOT_IN_FDOM_LEMMA = prove(
  ``?x. ~(x IN FDOM (refs:num|->'a))``,
  METIS_TAC [NUM_NOT_IN_FDOM]);

val LEAST_NO_IN_FDOM = prove(
  ``(LEAST ptr. ptr NOTIN FDOM (refs:num|->'a)) NOTIN FDOM refs``,
  ASSUME_TAC (EXISTS_NOT_IN_FDOM_LEMMA |>
           SIMP_RULE std_ss [whileTheory.LEAST_EXISTS]) \\ fs []);

val EVERY2_GENLIST = LIST_REL_GENLIST |> EQ_IMP_RULE |> snd |> Q.GEN`l`

val EVERY_ZIP_GENLIST = prove(
  ``!xs.
      (!i. i < LENGTH xs ==> P (EL i xs,f i)) ==>
      EVERY P (ZIP (xs,GENLIST f (LENGTH xs)))``,
  HO_MATCH_MP_TAC SNOC_INDUCT \\ fs [GENLIST] \\ REPEAT STRIP_TAC
  \\ fs [ZIP_SNOC,EVERY_SNOC] \\ REPEAT STRIP_TAC
  THEN1
   (FIRST_X_ASSUM MATCH_MP_TAC \\ REPEAT STRIP_TAC
    \\ IMP_RES_TAC EL_SNOC \\ fs []
    \\ `i < SUC (LENGTH xs)` by DECIDE_TAC \\ RES_TAC \\ METIS_TAC [])
  \\ `LENGTH xs < SUC (LENGTH xs)` by DECIDE_TAC \\ RES_TAC
  \\ fs [SNOC_APPEND,EL_LENGTH_APPEND]);

val map2_snoc = Q.prove (
  `!l1 l2 f x y.
    LENGTH l1 = LENGTH l2 ⇒
    MAP2 f (SNOC x l1) (SNOC y l2) = MAP2 f l1 l2 ++ [f x y]`,
  Induct_on `l1` >>
  rw [] >>
  `l2 = [] ∨ ?h l2'. l2 = h::l2'` by (Cases_on `l2` >> rw []) >>
  Cases_on `l2` >>
  fs [] >>
  rw []);

val el_map2 = Q.prove (
  `!x f l1 l2.
    LENGTH l1 = LENGTH l2 ∧ x < LENGTH l1
    ⇒
    EL x (MAP2 f l1 l2) = f (EL x l1) (EL x l2)`,
  Induct_on `x` >>
  rw [] >>
  Cases_on `l2` >>
  fs [] >>
  Cases_on `l1` >>
  fs []);

val length_take2 = Q.prove (
  `!x l. ¬(x ≤ LENGTH l) ⇒ LENGTH (TAKE x l) = LENGTH l`,
  Induct_on `l` >>
  rw [TAKE_def] >>
  Cases_on `x` >>
  fs [] >>
  first_x_assum match_mp_tac >>
  decide_tac);

val el_take_append = Q.prove (
  `!n l x l2. n ≤ LENGTH l ⇒ EL n (TAKE n l ++ [x] ++ l2) = x`,
  Induct_on `l` >>
  rw [] >>
  `0 < n` by decide_tac >>
  rw [EL_CONS] >>
  Cases_on `n = SUC (LENGTH l)` >>
  fs [] >>
  rw [PRE_SUB1]
  >- (first_x_assum (qspec_then `LENGTH l` mp_tac) >>
      rw [])
  >- (first_x_assum (qspec_then `n-1` mp_tac) >>
      srw_tac [ARITH_ss] []));

val el_append2 = Q.prove (
  `∀l x. EL (LENGTH l) (l++[x]) = x`,
  Induct_on `l` >> rw []);

val el_append2_lemma = Q.prove (
  `!n args.
    n+1 = LENGTH args
    ⇒
    EL (SUC n) (args ++ [x]) = x`,
  Induct_on `args` >> rw [] >>
  full_simp_tac (srw_ss()++ARITH_ss) [ADD1, el_append2]);

val hd_append = Q.prove (
  `!l1 l2. 0 < LENGTH l1 ⇒ HD (l1 ++ l2) = HD l1`,
  Cases_on `l1` >> rw []);

val tl_append = Q.prove (
  `!l1 l2. 0 < LENGTH l1 ⇒ TL (l1 ++ l2) = TL l1 ++ l2`,
  Cases_on `l1` >> rw []);

val twod_table_lemma = Q.prove (
  `!x y z.
    z ≤ y ⇒
    GENLIST (λt. f ((t + x * y) DIV y) ((t + x * y) MOD y)) z
    =
    GENLIST (λt. f x t) z`,
  Induct_on `z` >>
  rw [GENLIST] >>
  `z < y ∧ z ≤ y` by decide_tac >>
  fs [] >>
  `z+x*y = x*y+z` by decide_tac >>
  rw_tac std_ss [MOD_MULT, DIV_MULT, LESS_DIV_EQ_ZERO]);

val twod_table = Q.prove (
  `!f x y.
    0 < y ⇒
    FLAT (GENLIST (\m. GENLIST (\n. f m n) y) x) =
    GENLIST (\n. f (n DIV y) (n MOD y)) (x * y)`,
  Induct_on `x` >>
  rw [GENLIST] >>
  `(x+1) * y = y + x * y` by decide_tac >>
  fs [ADD1, GENLIST_APPEND, twod_table_lemma]);

val less_rectangle = Q.prove (
  `!(x:num) y m n. m < x ∧ n < y ⇒ x * n +m < x * y`,
  REPEAT STRIP_TAC
  \\ `SUC n <= y` by fs [LESS_EQ]
  \\ `x * (SUC n) <= x * y` by fs []
  \\ FULL_SIMP_TAC bool_ss [MULT_CLAUSES]
  \\ DECIDE_TAC);

val less_rectangle2 = Q.prove (
  `!(x:num) y m n. m < x ∧ n < y ⇒ m + n * x< x * y`,
  metis_tac [less_rectangle, ADD_COMM, MULT_COMM]);

val sum_genlist_square = Q.prove (
  `!x z. SUM (GENLIST (\y. z) x) = x * z`,
  Induct >>
  rw [GENLIST, SUM_SNOC, ADD1] >>
  decide_tac);

val if_expand = Q.prove (
  `!w x y z. (if x then y else z) = w ⇔ x ∧ y = w ∨ ~x ∧ z = w`,
  metis_tac []);

val take_drop_lemma = Q.prove (
  `!rem_args arg_list.
   LENGTH arg_list > rem_args
   ⇒
   TAKE (rem_args + 1) (DROP (LENGTH arg_list − (rem_args + 1)) (arg_list ++ stuff)) =
   DROP (LENGTH arg_list − (rem_args + 1)) arg_list`,
  Induct_on `arg_list` >>
  rw [] >>
  full_simp_tac (srw_ss() ++ ARITH_ss) [ADD1, TAKE_LENGTH_APPEND] >>
  `LENGTH arg_list = rem_args` by decide_tac >>
  rw [] >>
  full_simp_tac (srw_ss() ++ ARITH_ss) [ADD1, TAKE_LENGTH_APPEND]);

val ETA2_THM = Q.prove (
  `(\x y. f a b c x y) = f a b c`,
  rw [FUN_EQ_THM]);

val p_genlist = Q.prove (
  `EL k exps_ps = ((n',e),p) ∧
   MAP SND exps_ps = GENLIST (λn. loc + num_stubs + n) (LENGTH exps_ps) ∧
   k < LENGTH exps_ps
   ⇒
   p = EL k (GENLIST (λn. loc + num_stubs + n) (LENGTH exps_ps))`,
  rw [] >>
  `EL k (MAP SND exps_ps) = EL k (GENLIST (λn. loc + num_stubs + n) (LENGTH exps_ps))` by metis_tac [] >>
  rfs [EL_MAP]);

(* -- *)

(* correctness of partial/over application *)

val evaluate_genlist_prev_args = Q.prove (
  `!prev_args z x tag p n cl arg_list st.
    evaluate (REVERSE (GENLIST (λprev_arg. Op El [Op (Const (&(prev_arg + LENGTH z))) []; Var (LENGTH x)]) (LENGTH prev_args)),
           x++(Block tag (z++prev_args))::arg_list,
           st)
    =
    (Rval (REVERSE prev_args),st)`,
  Induct_on `prev_args` >>
  rw [evaluate_def, GENLIST_CONS] >>
  rw [evaluate_APPEND, evaluate_def, do_app_def] >>
  full_simp_tac (srw_ss()++ARITH_ss) [] >>
  rw [] >>
  pop_assum (qspecl_then [`z++[h]`] mp_tac) >>
  srw_tac [ARITH_ss] [combinTheory.o_DEF, ADD1] >>
  `z ++ h :: prev_args = z ++ [h] ++ prev_args` by metis_tac [APPEND, APPEND_ASSOC] >>
  rw [el_append3] >>
  `x ++ Block tag (z ++ [h] ++ prev_args)::arg_list = x ++ [Block tag (z ++ [h] ++ prev_args)] ++ arg_list`
          by metis_tac [APPEND, APPEND_ASSOC] >>
  rw [el_append3] >>
  decide_tac);

val evaluate_genlist_prev_args1 = Q.prove (
  `!prev_args x y tag p n cl args st.
    evaluate (REVERSE (GENLIST (λprev_arg. Op El [Op (Const (&(prev_arg + 3))) []; Var (LENGTH args + 2)]) (LENGTH prev_args)),
           x::y::(args++[Block tag (p::n::cl::prev_args)]),
           st)
    =
    (Rval (REVERSE prev_args),st)`,
  rw [] >>
  assume_tac (Q.SPECL [`prev_args`, `[p;n;cl]`, `x::y::args`] evaluate_genlist_prev_args) >>
  full_simp_tac (srw_ss()++ARITH_ss) [ADD1]);

val evaluate_genlist_prev_args_no_rev = Q.prove (
  `!prev_args z x tag p n cl arg_list st.
    evaluate (GENLIST (λprev_arg. Op El [Op (Const (&(prev_arg + LENGTH z))) []; Var (LENGTH x)]) (LENGTH prev_args),
           x++(Block tag (z++prev_args))::arg_list,
           st)
    =
    (Rval prev_args,st)`,
  Induct_on `prev_args` >>
  rw [evaluate_def, GENLIST_CONS] >>
  rw [Once evaluate_CONS, evaluate_def, do_app_def] >>
  full_simp_tac (srw_ss()++ARITH_ss) [] >>
  rw [] >>
  pop_assum (qspecl_then [`z++[h]`] mp_tac) >>
  srw_tac [ARITH_ss] [combinTheory.o_DEF, ADD1] >>
  `z ++ h :: prev_args = z ++ [h] ++ prev_args` by metis_tac [APPEND, APPEND_ASSOC] >>
  rw [el_append3] >>
  `x ++ Block tag (z ++ [h] ++ prev_args)::arg_list = x ++ [Block tag (z ++ [h] ++ prev_args)] ++ arg_list`
          by metis_tac [APPEND, APPEND_ASSOC] >>
  rw [el_append3] >>
  decide_tac);

val evaluate_genlist_prev_args1_no_rev = Q.prove (
  `!prev_args x tag p n cl args st.
    evaluate (GENLIST (λprev_arg. Op El [Op (Const (&(prev_arg + 3))) []; Var (LENGTH args + 1)]) (LENGTH prev_args),
           x::(args++[Block tag (p::n::cl::prev_args)]),
           st)
    =
    (Rval prev_args,st)`,
  metis_tac [evaluate_genlist_prev_args_no_rev, APPEND, LENGTH, DECIDE ``SUC (SUC (SUC 0)) = 3``,
             DECIDE ``(SUC 0) = 1``, DECIDE ``SUC (SUC 0) = 2``, ADD1]);

val evaluate_generic_app1 = Q.prove (
  `!n args st total_args l fvs cl.
    partial_app_fn_location total_args n ∈ domain st.code ∧
    n < total_args ∧
    total_args < max_app ∧
    n + 1 = LENGTH args ∧
    cl = Block closure_tag (CodePtr l :: Number (&total_args) :: fvs)
    ⇒
    evaluate ([generate_generic_app n], args++[cl], st) =
      if st.clock < n then
        (Rerr(Rabort Rtimeout_error), st with clock := 0)
      else
        (Rval [Block partial_app_tag (CodePtr (partial_app_fn_location total_args n) ::
                                      Number (&(total_args - (n + 1))) ::
                                      cl::
                                      args)],
         dec_clock n st)`,
  rw [generate_generic_app_def] >>
  rw [evaluate_def, do_app_def] >>
  full_simp_tac (srw_ss() ++ ARITH_ss) [el_append2] >>
  `~(&total_args − &(n+1) < 0)` by intLib.ARITH_TAC >>
  rw [] >>
  rfs [evaluate_mk_tick, evaluate_def, do_app_def] >>
  full_simp_tac (srw_ss() ++ ARITH_ss) [el_append2] >>
  rw [DECIDE ``x + 2 = SUC (SUC x)``, el_append2_lemma, evaluate_APPEND] >>
  srw_tac [ARITH_ss] [ADD1, evaluate_genlist_vars_rev, evaluate_def] >>
  `evaluate ([Op El [Op (Const (1:int)) []; Var (LENGTH args + 1)]],
          Number (&total_args − &(LENGTH args))::(args++[Block closure_tag (CodePtr l::Number (&total_args)::fvs)]),
          dec_clock n st) =
    (Rval [Number (&total_args)], dec_clock n st)`
          by (srw_tac [ARITH_ss] [evaluate_def, do_app_def, int_arithTheory.INT_NUM_SUB] >>
              srw_tac [ARITH_ss][PRE_SUB1, EL_CONS, el_append2]) >>
  imp_res_tac evaluate_Jump >>
  rfs [] >>
  srw_tac [ARITH_ss] [LENGTH_GENLIST, evaluate_def, do_app_def, evaluate_APPEND] >>
  rw [evaluate_def, do_app_def, int_arithTheory.INT_NUM_SUB, el_append2,
      TAKE_LENGTH_APPEND] >>
  decide_tac);

val evaluate_generic_app2 = Q.prove (
  `!n args st rem_args prev_args l clo cl.
    partial_app_fn_location (rem_args + LENGTH prev_args) (n + LENGTH prev_args) ∈ domain st.code ∧
    n < rem_args ∧
    n + 1 = LENGTH args ∧
    LENGTH prev_args > 0 ∧
    rem_args + LENGTH prev_args < max_app ∧
    cl = Block partial_app_tag (CodePtr l :: Number (&rem_args) :: clo :: prev_args)
    ⇒
    evaluate ([generate_generic_app n], args++[cl], st) =
      if st.clock < n then
        (Rerr(Rabort Rtimeout_error), st with clock := 0)
      else
        (Rval [Block partial_app_tag (CodePtr (partial_app_fn_location (rem_args + LENGTH prev_args) (n + LENGTH prev_args)) ::
                                      Number (&rem_args - &(n+1)) ::
                                      clo ::
                                      args ++
                                      prev_args)],
         dec_clock n st)`,
  rw [generate_generic_app_def, mk_const_def] >>
  rw [evaluate_def, do_app_def] >>
  full_simp_tac (srw_ss() ++ ARITH_ss) [] >>
  `~(&rem_args − &(n+1) < 0)` by intLib.ARITH_TAC >>
  rw [el_append2] >>
  rfs [evaluate_mk_tick] >>
  full_simp_tac (srw_ss()++ARITH_ss) [] >>
  rw [evaluate_def, do_app_def] >>
  rw [DECIDE ``x + 2 = SUC (SUC x)``, el_append2_lemma, evaluate_APPEND] >>
  rw [ADD1] >>
  fs [] >>
  `evaluate ([Op Sub [Op (Const 4) []; Op LengthBlock [Var (LENGTH args + 1)]]],
          Number (&rem_args − &LENGTH args)::(args++[Block partial_app_tag (CodePtr l::Number (&rem_args)::clo::prev_args)]),dec_clock n st) =
    (Rval [Number (&(LENGTH prev_args - 1))], dec_clock n st)`
          by (srw_tac [ARITH_ss] [evaluate_def, do_app_def, int_arithTheory.INT_NUM_SUB] >>
              srw_tac [ARITH_ss] [EL_CONS, GSYM ADD1, el_append2] >>
              intLib.ARITH_TAC) >>
  imp_res_tac evaluate_Jump >>
  rfs [] >>
  srw_tac [ARITH_ss] [evaluate_APPEND, LENGTH_GENLIST, evaluate_def, do_app_def] >>
  rw [REVERSE_APPEND, evaluate_APPEND] >>
  `n + 3 = LENGTH args + 2` by decide_tac >>
  rw [evaluate_genlist_prev_args1] >>
  srw_tac [ARITH_ss] [evaluate_genlist_vars_rev, EL_CONS, PRE_SUB1, el_append2] >>
  `evaluate ([Op Add [Op (Const (&(n + (LENGTH prev_args + 1)))) []; Var 1]],
          Number (&(LENGTH prev_args − 1))::Number (&rem_args − &LENGTH args)::(args++[Block partial_app_tag (CodePtr l::Number (&rem_args)::clo::prev_args)]),
          dec_clock n st) =
    (Rval [Number (&(LENGTH prev_args + rem_args))], dec_clock n st)`
          by (srw_tac [ARITH_ss] [partial_app_tag_def, evaluate_def, do_app_def, int_arithTheory.INT_NUM_SUB] >>
              intLib.ARITH_TAC) >>
  imp_res_tac evaluate_Jump >>
  `LENGTH prev_args - 1 < max_app` by decide_tac >>
  fs [partial_app_tag_def] >>
  srw_tac [ARITH_ss] [evaluate_APPEND, REVERSE_APPEND, TAKE_LENGTH_APPEND, LENGTH_GENLIST, evaluate_def, do_app_def, mk_label_def]);

val (unpack_closure_rules, unpack_closure_ind, unpack_closure_cases) = Hol_reln `
  (total_args ≥ 0
   ⇒
   unpack_closure (Block closure_tag (CodePtr l :: Number total_args :: fvs))
         ([], Num total_args, Block closure_tag (CodePtr l :: Number total_args :: fvs))) ∧
  (prev_args ≠ [] ∧
   rem_args ≥ 0
   ⇒
   unpack_closure (Block partial_app_tag (CodePtr l :: Number rem_args :: clo :: prev_args))
         (prev_args, Num rem_args + LENGTH prev_args, clo))`;

val evaluate_generic_app_partial = Q.prove (
  `!total_args prev_args st args cl sub_cl.
    partial_app_fn_location total_args (LENGTH prev_args + (LENGTH args - 1)) ∈ domain st.code ∧
    total_args < max_app ∧
    LENGTH args < (total_args + 1) - LENGTH prev_args ∧
    LENGTH args ≠ 0 ∧
    unpack_closure cl (prev_args, total_args, sub_cl)
    ⇒
    evaluate ([generate_generic_app (LENGTH args - 1)], args++[cl], st) =
      if st.clock < LENGTH args - 1 then
        (Rerr(Rabort Rtimeout_error), st with clock := 0)
      else
        (Rval [Block partial_app_tag (CodePtr (partial_app_fn_location total_args (LENGTH prev_args + (LENGTH args - 1))) ::
                                      Number (&(total_args - (LENGTH prev_args + LENGTH args))) ::
                                      sub_cl::
                                      args++
                                      prev_args)],
         dec_clock (LENGTH args - 1) st)`,
  rpt GEN_TAC >>
  strip_tac >>
  fs [unpack_closure_cases]
  >- (qspecl_then [`LENGTH args - 1`, `args`, `st`, `total_args`] mp_tac evaluate_generic_app1 >>
      srw_tac [ARITH_ss] [] >>
      rfs [] >>
      `&Num total_args' = total_args'` by intLib.COOPER_TAC >>
      fs [] >>
      rw [])
  >- (qspecl_then [`LENGTH args - 1`, `args`, `st`, `Num rem_args`, `prev_args`] mp_tac evaluate_generic_app2 >>
      full_simp_tac (srw_ss()++ARITH_ss) [] >>
      srw_tac [ARITH_ss] [] >>
      Cases_on `prev_args` >>
      fs [] >>
      rw [] >>
      `&Num rem_args = rem_args` by intLib.ARITH_TAC >>
      fs [] >>
      rw [int_arithTheory.INT_NUM_SUB] >>
      intLib.ARITH_TAC));

val evaluate_generic_app_full = Q.prove (
  `!n args st rem_args vs l tag exp clo.
    lookup l st.code = SOME (rem_args + 2, exp) ∧
    n + 1 = LENGTH args ∧
    n > rem_args ∧
    rem_args < max_app
    ⇒
    evaluate ([generate_generic_app n], args++[Block tag (CodePtr l :: Number (&rem_args) :: vs)], st) =
    if st.clock < rem_args + 1 then (Rerr(Rabort Rtimeout_error), st with clock := 0) else
      case evaluate ([exp],
                     DROP (LENGTH args − (rem_args + 1)) args ++
                     [Block tag (CodePtr l::Number (&rem_args)::vs)],
                     dec_clock (rem_args + 1) st) of
        | (Rval [v], st') =>
            (case
               evaluate
                 ([mk_cl_call (Var 0) (GENLIST (λn. Var (n + 3)) (n − rem_args))],
                  v::Number (&rem_args)::Number (&rem_args − &LENGTH args)::
                      args++[Block tag (CodePtr l::Number (&rem_args)::vs)],
                  st')
             of
               (Rval v,s2) => (Rval [HD v],s2)
             | x => x)
        | x => x`,
  rw [generate_generic_app_def, mk_const_def] >>
  rw [evaluate_def, do_app_def, el_append2] >>
  full_simp_tac (srw_ss() ++ ARITH_ss) [partial_app_tag_def] >>
  `(&rem_args − &(LENGTH args) < 0)` by intLib.ARITH_TAC >>
  rw [] >>
  `evaluate ([Op El [Op (Const (1:int)) []; Var (LENGTH args + 1)]],
          Number (&rem_args − &LENGTH args):: (args ++ [Block tag (CodePtr l::Number (&rem_args)::vs)]),
          st) =
    (Rval [Number (&rem_args)], st)`
          by srw_tac [ARITH_ss] [evaluate_def, do_app_def, PRE_SUB1, EL_CONS, el_append2] >>
  `n + 2 = LENGTH args + 1` by decide_tac >>
  fs [] >>
  imp_res_tac evaluate_Jump >>
  srw_tac [ARITH_ss] [LENGTH_GENLIST, evaluate_def, do_app_def] >>
  srw_tac [ARITH_ss] [evaluate_APPEND, do_app_def, evaluate_def] >>
  srw_tac [ARITH_ss] [Once evaluate_CONS, evaluate_def, evaluate_APPEND] >>
  fs [] >>
  `(rem_args + 1) + ((LENGTH args + 1) - rem_args) ≤
     LENGTH (Number (&rem_args)::Number (&rem_args − &LENGTH args)::
                 (args ++
                  [Block tag (CodePtr l::Number (&rem_args)::vs)]))`
             by (rw [] >>
                 decide_tac) >>
  imp_res_tac evaluate_genlist_vars >>
  pop_assum (qspec_then `st` mp_tac) >>
  `LENGTH args + 1 - rem_args = (LENGTH args + 1) - rem_args` by decide_tac >>
  simp [] >>
  rw [] >>
  simp [EL_CONS, PRE_SUB1, el_append2, find_code_def, bvlSemTheory.state_component_equality, FRONT_APPEND] >>
  `LENGTH args > rem_args` by decide_tac >>
  rw [take_drop_lemma] >>
  qabbrev_tac `res1 =
    evaluate
      ([exp],
       DROP (LENGTH args − (rem_args + 1)) args ++ [Block tag (CodePtr l::Number (&rem_args)::vs)],
       dec_clock (rem_args + 1) st)` >>
  Cases_on `res1` >>
  fs [] >>
  Cases_on `q` >>
  fs [] >>
  `LENGTH a = 1` by metis_tac [bvlPropsTheory.evaluate_IMP_LENGTH, LENGTH, DECIDE ``SUC 0 = 1``] >>
  Cases_on `a` >>
  fs [] >>
  Cases_on `t` >>
  fs [] >>
  BasicProvers.FULL_CASE_TAC >>
  BasicProvers.FULL_CASE_TAC >>
  `LENGTH a = 1` by metis_tac [bvlPropsTheory.evaluate_IMP_LENGTH, LENGTH, DECIDE ``SUC 0 = 1``] >>
  Cases_on `a` >>
  fs [] >>
  Cases_on `t` >>
  fs []);

val mk_cl_lem = Q.prove (
  `l < LENGTH env
   ⇒
   evaluate (GENLIST (λn. Var (n + 3)) l, a::b::c::env, st) =
   evaluate (GENLIST (λn. Var (n + 1)) l, a::env, st)`,
  rw [] >>
  `l + 3 ≤ LENGTH (a::b::c::env)` by srw_tac [ARITH_ss] [ADD1] >>
  `l + 1 ≤ LENGTH (a::env)` by srw_tac [ARITH_ss] [ADD1] >>
  imp_res_tac evaluate_genlist_vars >>
  rw []);

val evaluate_mk_cl_simpl = Q.prove (
  `evaluate ([mk_cl_call (Var 0) (GENLIST (λn. Var (n + 3)) (LENGTH args' − (n + 1)))],
                               v::a::b::(args' ++ [Block tag (CodePtr p::Number (&n)::xs)]),
                               st')
   =
   evaluate ([mk_cl_call (Var 0) (GENLIST (λn. Var (n + 1)) (LENGTH args' − (n + 1)))],
                               v::(args' ++ [Block tag (CodePtr p::Number (&n)::xs)]),
                               st')`,
  rw [mk_cl_call_def, evaluate_def, do_app_def] >>
  Cases_on `v` >>
  rw [] >>
  BasicProvers.FULL_CASE_TAC >>
  rw [evaluate_APPEND] >>
  ntac 2 (pop_assum (mp_tac o GSYM)) >>
  rw [] >>
  full_simp_tac (srw_ss()++ARITH_ss) [evaluate_def, do_app_def] >>
  `LENGTH args' - (n + 1) < LENGTH (args' ++ [Block tag (CodePtr p::Number (&n)::xs)])`
              by srw_tac [ARITH_ss] [] >>
  srw_tac [ARITH_ss] [mk_cl_lem]);

val evaluate_mk_cl_call = Q.prove (
  `!cl env s tag p n args args' exp exp2 xs.
    evaluate ([cl],env,s) = (Rval [Block tag (CodePtr p::Number &n::xs)], s) ∧
    evaluate (args,env,s) = (Rval args', s) ∧
    lookup p s.code = SOME (n+2, exp) ∧
    lookup (LENGTH args' - 1) s.code = SOME (LENGTH args' + 1, generate_generic_app (LENGTH args' - 1)) ∧
    LENGTH args' - 1 ≥ n ∧
    n < max_app ∧
    LENGTH args ≠ 0
    ⇒
    evaluate ([mk_cl_call cl args],env,s) =
     if n = LENGTH args - 1 then
       if s.clock < LENGTH args
       then (Rerr(Rabort Rtimeout_error),s with clock := 0)
       else evaluate ([exp],
                   args' ++ [Block tag (CodePtr p::Number (&(LENGTH args − 1))::xs)],
                   dec_clock (LENGTH args) s)
     else
         if s.clock < n + 2
         then (Rerr(Rabort Rtimeout_error),s with clock := 0)
         else
         case evaluate ([exp],
                     DROP (LENGTH args' − (n + 1)) args' ++ [Block tag (CodePtr p::Number (&n)::xs)],
                     dec_clock (n + 2) s)
           of
            | (Rval [v],st') =>
                (case evaluate ([mk_cl_call (Var 0) (GENLIST (λn. Var (n + 1)) (LENGTH args' − (n + 1)))],
                              v::(args' ++ [Block tag (CodePtr p::Number (&n)::xs)]),
                              st') of
                    | (Rval v,s2) => (Rval [HD v],s2)
                    | x => x)
            | x => x`,
  rw [Once mk_cl_call_def, evaluate_def, do_app_def] >>
  fs [ADD1] >>
  Cases_on `n = &(LENGTH args − 1)` >>
  rw [evaluate_APPEND, evaluate_def, do_app_def, find_code_def, FRONT_APPEND] >>
  simp [] >>
  imp_res_tac bvlPropsTheory.evaluate_IMP_LENGTH >>
  rev_full_simp_tac (srw_ss()++ARITH_ss) [] >>
  `LENGTH args' - 1 + 1 = LENGTH args'` by decide_tac >>
  `lookup p (dec_clock 1 s).code = SOME (n+2,exp)` by rw [] >>
  imp_res_tac evaluate_generic_app_full >>
  rw [] >>
  full_simp_tac (srw_ss()++ARITH_ss) [dec_clock_def] >>
  simp [evaluate_mk_cl_simpl]);

val evaluate_partial_app_fn = Q.prove (
  `!num_args args' num_args' args prev_args tag num tag' num' l l' fvs exp code.
    lookup l code = SOME (LENGTH args' + LENGTH prev_args + 1,exp) /\
    LENGTH prev_args ≠ 0 ∧
    LENGTH prev_args < num_args ∧
    num_args = LENGTH prev_args + LENGTH args'
    ⇒
    !st. evaluate ([generate_partial_app_closure_fn (num_args - 1) (LENGTH prev_args - 1)],
           DROP (LENGTH args' + LENGTH prev_args − num_args) args' ++
           [Block tag (l'::num::Block tag' (CodePtr l::num_args'::fvs)::prev_args)],
           (st with code := code)) =
     if st.clock = 0 then
       (Rerr(Rabort Rtimeout_error), (st with code := code))
     else
       evaluate ([exp],
              DROP (LENGTH args' + LENGTH prev_args − num_args) args'++prev_args++[Block tag' (CodePtr l::num_args'::fvs)],
              dec_clock 1 (st with code := code))`,
  rw [evaluate_def, generate_partial_app_closure_fn_def, mk_const_def, do_app_def] >>
  full_simp_tac (srw_ss()++ARITH_ss) [el_append2, evaluate_APPEND] >>
  rw [evaluate_def] >>
  qabbrev_tac `cl = Block tag (l'::num::Block tag' (CodePtr l::num_args'::fvs):: prev_args)` >>
  qspecl_then [`1`, `Block tag' (CodePtr l::num_args'::fvs)::(args' ++ [cl])`,
                       `LENGTH (args')`, `st with code := code`] assume_tac evaluate_genlist_vars >>
  full_simp_tac (srw_ss()++ARITH_ss) [ADD1] >>
  rw [evaluate_genlist_prev_args1_no_rev, Abbr `cl`, evaluate_def, do_app_def, find_code_def] >>
  full_simp_tac (srw_ss()++ARITH_ss) [ADD1] >>
  rw [FRONT_APPEND, TAKE_LENGTH_APPEND, bvlSemTheory.state_component_equality]);

(* -- *)

(* value relation *)

val code_installed_def = Define `
  code_installed aux code =
    EVERY (\(n,num_args,exp). lookup n code = SOME (num_args,exp)) aux`;

val closure_code_installed_def = Define `
  closure_code_installed code exps_ps (env:closSem$v list) =
    EVERY (\((n,exp),p).
      n ≤ max_app ∧
      n ≠ 0 ∧
      ?aux c aux1.
        (compile [exp] aux = ([c],aux1)) /\
        (lookup p code = SOME (n+1,SND (code_for_recc_case (LENGTH env + LENGTH exps_ps) n c))) /\
        code_installed aux1 code) exps_ps`

val (cl_rel_rules,cl_rel_ind,cl_rel_cases) = Hol_reln `
  ( num_args ≤ max_app ∧
    num_args ≠ 0 ∧
    (compile [x] aux = ([c],aux1)) /\
    code_installed aux1 code /\
    (lookup (p + num_stubs) code =
      SOME (num_args + 1:num,Let (GENLIST Var num_args++free_let (Var num_args) (LENGTH env)) c))
   ⇒
   cl_rel fs refs code
          (env,ys)
          (Closure p [] env num_args x)
          (Block closure_tag (CodePtr (p + num_stubs) :: Number (&(num_args-1)) :: ys))) ∧
  ( num_args ≤ max_app ∧
    num_args ≠ 0 ∧
    compile [x] aux = ([c],aux1) /\
    code_installed aux1 code /\
    lookup (p + num_stubs) code =
      SOME (num_args + 1:num,Let (GENLIST Var (num_args+1)++free_let (Var num_args) (LENGTH env)) c)
    ⇒
    cl_rel fs refs code (env,ys)
           (Recclosure p [] env [(num_args, x)] 0)
           (Block closure_tag (CodePtr (p + num_stubs) :: Number (&(num_args-1)) :: ys)))
    /\
    ((exps = MAP FST exps_ps) /\
     (ps = MAP SND exps_ps) /\ (ps = GENLIST (\n. loc + num_stubs + n) (LENGTH exps_ps)) /\
     (rs = MAP (\((n,e),p). Block closure_tag [CodePtr p; Number (&(n-1)); RefPtr r]) exps_ps) /\
     ~(r IN fs) /\
     (FLOOKUP refs r = SOME (ValueArray (rs ++ ys))) /\
     1 < LENGTH exps /\ k < LENGTH exps /\
     closure_code_installed code exps_ps env ==>
     cl_rel fs refs code (env,ys) (Recclosure loc [] env exps k) (EL k rs))`;

val add_args_def = Define `
  (add_args (Closure loc_opt args env num_args exp : closSem$v) args' =
    SOME (Closure loc_opt (args'++args) env num_args exp)) ∧
  (add_args (Recclosure loc_opt args env funs i : closSem$v) args' =
    SOME (Recclosure loc_opt (args'++args) env funs i)) ∧
  (add_args _ _ = NONE)`;

val add_args_append = Q.prove (
  `add_args cl arg_env = SOME func
   ⇒
   add_args cl (args ++ arg_env) = add_args func args`,
  Cases_on `cl` >>
  rw [add_args_def] >>
  rw [add_args_def]);

val get_num_args_def = Define `
  (get_num_args (Closure loc_opt args env num_args exp : closSem$v) =
    SOME num_args) ∧
  (get_num_args (Recclosure loc_opt args env funs i : closSem$v) =
    SOME (FST (EL i funs))) ∧
  (get_num_args _ = NONE)`;

val (v_rel_rules,v_rel_ind,v_rel_cases) = Hol_reln `
  (v_rel f refs code (Number n) (Number n))
  /\
  (EVERY2 (v_rel f refs code) xs (ys:bvlSem$v list) ==>
   v_rel f refs code (Block t xs) (Block (t+clos_tag_shift) ys))
  /\
  ((FLOOKUP f r1 = SOME r2) ==>
   v_rel f refs code (RefPtr r1) (RefPtr r2))
  /\
  (EVERY2 (v_rel f refs code) env fvs ∧
   cl_rel (FRANGE f) refs code (env,fvs) cl (Block closure_tag (CodePtr p :: Number n :: ys))
   ⇒
   v_rel f refs code cl (Block closure_tag (CodePtr p :: Number n :: ys)))
  /\
  (EVERY2 (v_rel f refs code) env fvs /\
   EVERY2 (v_rel f refs code) arg_env ys ∧
   arg_env ≠ [] ∧
   LENGTH arg_env < num_args ∧
   (lookup (partial_app_fn_location (num_args - 1) (LENGTH ys - 1)) code =
     SOME (num_args - LENGTH arg_env + 1, generate_partial_app_closure_fn (num_args-1) (LENGTH ys - 1))) ∧
   add_args cl arg_env = SOME cl_app ∧
   get_num_args cl = SOME num_args ∧
   cl_rel (FRANGE f) refs code (env,fvs) cl cl'
   ⇒
   v_rel f refs code cl_app
                       (Block partial_app_tag
                              (CodePtr (partial_app_fn_location (num_args - 1) (LENGTH ys - 1)) ::
                               Number (&(num_args - 1 - LENGTH arg_env)) :: cl' :: ys)))`;

val cl_rel_F = Q.prove (
  `~cl_rel f refs code (env,ys) (Number i) cl ∧
   ~cl_rel f refs code (env,ys) (RefPtr p) cl ∧
   ~cl_rel f refs code (env,ys) (Block tag xs) cl`,
  rw [cl_rel_cases]);

val add_args_F = Q.prove (
  `!cl args p i tag xs.
   add_args cl args ≠ SOME (RefPtr p) ∧
   add_args cl args ≠ SOME (Number i) ∧
   add_args cl args ≠ SOME (Block tag xs)`,
  Cases_on `cl` >>
  rw [add_args_def]);

val v_rel_Unit = Q.store_thm("v_rel_Unit[simp]",
  `(v_rel f refs code Unit y ⇔ (y = Unit)) ∧
   (v_rel f refs code x Unit ⇔ (x = Unit))`,
  EVAL_TAC >> simp[v_rel_cases] >> EVAL_TAC >>
  rw[EQ_IMP_THM] >> fs[add_args_F,cl_rel_F] >>
  every_case_tac >> rw[] >> fsrw_tac[ARITH_ss][])

val v_rel_Boolv = Q.store_thm("v_rel_Boolv[simp]",
  `(v_rel f refs code (Boolv b) y ⇔ (y = Boolv b)) ∧
   (v_rel f refs code x (Boolv b) ⇔ (x = Boolv b))`,
  EVAL_TAC >> simp[v_rel_cases] >> EVAL_TAC >> simp[] >>
  rw[EQ_IMP_THM] >> fs[cl_rel_F,add_args_F] >>
  every_case_tac >> rw[] >> fsrw_tac[ARITH_ss][])

val v_rel_SIMP = LIST_CONJ
  [``v_rel f refs code (RefPtr p) y``
   |> SIMP_CONV (srw_ss()) [v_rel_cases, cl_rel_F, add_args_F],
   ``v_rel f refs code (Block tag xs) y``
   |> SIMP_CONV (srw_ss()) [v_rel_cases, cl_rel_F, add_args_F],
   ``v_rel f refs code (Number i) y``
   |> SIMP_CONV (srw_ss()) [v_rel_cases, cl_rel_F, add_args_F],
   ``v_rel f refs code (Closure loc args env num_args exp) y``
   |> SIMP_CONV (srw_ss()) [v_rel_cases, cl_rel_F, add_args_F],
   ``v_rel f refs code (Recclosure loc args env exp k) y``
   |> SIMP_CONV (srw_ss()) [v_rel_cases, cl_rel_F, add_args_F]]
  |> curry save_thm "v_rel_SIMP"

val env_rel_def = Define `
  (env_rel f refs code [] [] = T) /\
  (env_rel f refs code [] ys = T) /\   (* bvl env allowed to contain extra stuff *)
  (env_rel f refs code (x::xs) [] = F) /\
  (env_rel f refs code (x::xs) (y::ys) <=>
     v_rel f refs code x y /\ env_rel f refs code xs ys)`;

val env_rel_APPEND = prove(
  ``!xs1 xs2.
      EVERY2 (v_rel f1 refs code) xs1 xs2 /\
      env_rel f1 refs code ys1 ys2 ==>
      env_rel f1 refs code (xs1 ++ ys1) (xs2 ++ ys2)``,
  Induct \\ Cases_on `xs2` \\ fs [env_rel_def]);

val list_rel_IMP_env_rel = prove(
  ``!xs ys.
      LIST_REL (v_rel f refs code) xs ys ==>
      env_rel f refs code xs (ys ++ ts)``,
  Induct \\ Cases_on `ys` \\ fs [env_rel_def]
  \\ Cases_on `ts` \\ fs [env_rel_def]);

val env_rel_IMP_LENGTH = prove(
  ``!env1 env2.
      env_rel f refs code env1 env2 ==>
      LENGTH env1 <= LENGTH env2``,
  Induct \\ Cases_on `env2` \\ fs [env_rel_def]);

val LESS_LENGTH_env_rel_IMP = prove(
  ``!env env2 n.
      n < LENGTH env /\ env_rel f refs code env env2 ==>
      n < LENGTH env2 /\ v_rel f refs code (EL n env) (EL n env2)``,
  Induct \\ fs [LENGTH] \\ REPEAT STRIP_TAC
  \\ Cases_on `env2` \\ fs [env_rel_def]
  \\ Cases_on `n` \\ fs []);

val env_rel_IMP_EL =
  LESS_LENGTH_env_rel_IMP |> SPEC_ALL |> UNDISCH
  |> CONJUNCT2 |> DISCH_ALL |> GEN_ALL

val state_rel_def = Define `
  state_rel f (s:closSem$state) (t:bvlSem$state) <=>
    (s.io = t.io) /\
    s.restrict_envs /\
    LIST_REL (OPTREL (v_rel f t.refs t.code)) s.globals t.globals /\
    INJ ($' f) (FDOM f) (FRANGE f) /\
    (FDOM f = FDOM s.refs) /\
    (FRANGE f SUBSET FDOM t.refs) /\
    (!n x. (FLOOKUP s.refs n = SOME x) ==>
           ?y m. (FLOOKUP f n = SOME m) /\
                 (FLOOKUP t.refs m = SOME y) /\
                 ref_rel (v_rel f t.refs t.code) x y) /\
    (!n. n < max_app ⇒ lookup n t.code = SOME (n + 2, generate_generic_app n)) ∧
    (!m n. m < max_app ∧ n < max_app ⇒
      lookup (partial_app_fn_location m n) t.code = SOME (m - n + 1, generate_partial_app_closure_fn m n)) ∧
    (!name arity c.
      (FLOOKUP s.code name = SOME (arity,c)) ==>
      ?aux1 c2 aux2.
        (compile [c] aux1 = ([c2],aux2)) /\
        (lookup (name + num_stubs) t.code = SOME (arity,c2)) /\
        code_installed aux2 t.code)`;

val state_rel_globals = prove(
  ``state_rel f s t ⇒
    LIST_REL (OPTREL (v_rel f t.refs t.code)) s.globals t.globals``,
  rw[state_rel_def]);

val state_rel_clock = Q.store_thm ("state_rel_clock[simp]",
  `(!f s t. state_rel f s (t with clock := x) = state_rel f s t) ∧
   (!f s t. state_rel f (s with clock := x) t = state_rel f s t)`,
  rw [state_rel_def]);

val cl_rel_SUBMAP = Q.prove (
  `cl_rel f1 refs1 code (env,ys) x y ∧
   f1 ⊆ f2 /\ FDIFF refs1 f1 SUBMAP FDIFF refs2 f2 ==>
   cl_rel f2 refs2 code (env,ys) x y`,
  rw [cl_rel_cases]
  >- metis_tac []
  >- metis_tac []
  \\ DISJ2_TAC \\ Q.LIST_EXISTS_TAC [`exps_ps`,`r`] \\ fs []
  \\ rfs []
  \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ fs [] \\ STRIP_TAC
  \\ fs [FDIFF_def,SUBMAP_DEF,DRESTRICT_DEF,FLOOKUP_DEF]
  \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `r`) \\ fs []);

val v_rel_SUBMAP = prove(
  ``!x y. v_rel f1 refs1 code x y ==>
      f1 SUBMAP f2 /\ FDIFF refs1 (FRANGE f1) SUBMAP FDIFF refs2 (FRANGE f2) ==>
      v_rel f2 refs2 code x y``,
  HO_MATCH_MP_TAC v_rel_ind \\ REPEAT STRIP_TAC
  \\ ONCE_REWRITE_TAC [v_rel_cases] \\ fs []
  THEN1 (REPEAT (POP_ASSUM MP_TAC) \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ fs [])
  THEN1 (fs [SUBMAP_DEF,FLOOKUP_DEF])
  THEN1 (imp_res_tac SUBMAP_FRANGE_SUBSET >>
         imp_res_tac cl_rel_SUBMAP >>
         disj2_tac >>
         fs [ETA2_THM] >>
         metis_tac [])
  THEN1 (imp_res_tac cl_rel_SUBMAP >>
         disj2_tac >>
         fs [ETA2_THM] >>
         metis_tac [SUBMAP_FRANGE_SUBSET] ))
  |> SPEC_ALL |> MP_CANON;

val env_rel_SUBMAP = prove(
  ``!env1 env2.
      env_rel f1 refs1 code env1 env2 /\
      f1 SUBMAP f2 /\ FDIFF refs1 (FRANGE f1) SUBMAP FDIFF refs2 (FRANGE f2) ==>
      env_rel f2 refs2 code env1 env2``,
  Induct \\ Cases_on `env2` \\ fs [env_rel_def]
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC v_rel_SUBMAP) |> GEN_ALL;

val cl_rel_NEW_REF = Q.prove (
  `!x y. cl_rel f1 refs1 code (env,ys) x y ==> ~(r IN FDOM refs1) ==>
         cl_rel f1 (refs1 |+ (r,t)) code (env,ys) x y`,
  rw [cl_rel_cases]
  >- metis_tac []
  >- metis_tac []
  \\ DISJ2_TAC \\ Q.LIST_EXISTS_TAC [`exps_ps`,`r'`] \\ fs []
  \\ rfs []
  \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ fs []
  \\ fs [FDIFF_def,SUBMAP_DEF,DRESTRICT_DEF,FLOOKUP_DEF]
  \\ fs [FAPPLY_FUPDATE_THM] \\ SRW_TAC [] [] \\ fs []);

val v_rel_NEW_REF = prove(
  ``!x y. v_rel f1 refs1 code x y ==> ~(r IN FDOM refs1) ==>
          v_rel f1 (refs1 |+ (r,t)) code x y``,
  HO_MATCH_MP_TAC v_rel_ind \\ REPEAT STRIP_TAC
  \\ ONCE_REWRITE_TAC [v_rel_cases] \\ fs []
  THEN1 (REPEAT (POP_ASSUM MP_TAC) \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ fs [])
  THEN1 (imp_res_tac cl_rel_NEW_REF >>
         disj2_tac >>
         fs [ETA2_THM] >>
         metis_tac [])
  THEN1 (imp_res_tac cl_rel_NEW_REF >>
         disj2_tac >>
         fs [ETA2_THM] >>
         metis_tac [] ))
  |> SPEC_ALL |> MP_CANON;

val cl_rel_UPDATE_REF = prove(
  ``!x y. cl_rel f1 refs1 code (env,ys) x y ==>
          (r IN f1) ==>
          cl_rel f1 (refs1 |+ (r,t)) code (env,ys) x y``,
  rw [cl_rel_cases]
  >- metis_tac []
  >- metis_tac []
  \\ DISJ2_TAC \\ Q.LIST_EXISTS_TAC [`exps_ps`,`r'`] \\ fs []
  \\ rfs []
  \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ fs []
  \\ fs [FDIFF_def,SUBMAP_DEF,DRESTRICT_DEF,FLOOKUP_DEF]
  \\ fs [FAPPLY_FUPDATE_THM] \\ SRW_TAC [] []
  \\ fs [FRANGE_DEF] \\ METIS_TAC []);

val v_rel_UPDATE_REF = prove(
  ``!x y. v_rel f1 refs1 code x y ==>
          (r IN FRANGE f1) ==>
          v_rel f1 (refs1 |+ (r,t)) code x y``,
  HO_MATCH_MP_TAC v_rel_ind \\ REPEAT STRIP_TAC
  \\ ONCE_REWRITE_TAC [v_rel_cases] \\ fs []
  THEN1 (REPEAT (POP_ASSUM MP_TAC) \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ fs [])
  THEN1 (imp_res_tac cl_rel_UPDATE_REF >>
         disj2_tac >>
         fs [ETA2_THM] >>
         metis_tac [])
  THEN1 (imp_res_tac cl_rel_UPDATE_REF >>
         disj2_tac >>
         fs [ETA2_THM] >>
         metis_tac [] ))
  |> SPEC_ALL |> MP_CANON;

val OPTREL_v_rel_NEW_REF = prove(
  ``OPTREL (v_rel f1 refs1 code) x y /\ ~(r IN FDOM refs1) ==>
    OPTREL (v_rel f1 (refs1 |+ (r,t)) code) x y``,
  Cases_on `x` \\ Cases_on `y` \\ fs [OPTREL_def,v_rel_NEW_REF]);

val OPTREL_v_rel_UPDATE_REF = prove(
  ``OPTREL (v_rel f1 refs1 code) x y /\ r IN FRANGE f1 ==>
    OPTREL (v_rel f1 (refs1 |+ (r,t)) code) x y``,
  Cases_on `x` \\ Cases_on `y` \\ fs [OPTREL_def,v_rel_UPDATE_REF]);

val env_rel_NEW_REF = prove(
  ``!x y.
      env_rel f1 refs1 code x y /\ ~(r IN FDOM refs1) ==>
      env_rel f1 (refs1 |+ (r,t)) code x y``,
  Induct \\ Cases_on `y` \\ fs [env_rel_def] \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC v_rel_NEW_REF \\ fs []);

val cl_rel_NEW_F = prove(
  ``!x y.
      cl_rel f2 t2.refs t2.code (env,ys) x y ==>
      ~(qq IN FDOM t2.refs) ==>
      cl_rel (qq INSERT f2) t2.refs t2.code (env,ys) x y``,
  rw [cl_rel_cases]
  >- metis_tac []
  >- metis_tac []
  \\ DISJ2_TAC \\ Q.LIST_EXISTS_TAC [`exps_ps`,`r`] \\ fs []
  \\ strip_tac >> fs[FLOOKUP_DEF])

val v_rel_NEW_F = prove(
  ``!x y.
      v_rel f2 t2.refs t2.code x y ==>
      ~(pp IN FDOM f2) ==>
      ~(qq IN FDOM t2.refs) ==>
      v_rel (f2 |+ (pp,qq)) t2.refs t2.code x y``,
  HO_MATCH_MP_TAC v_rel_ind \\ REPEAT STRIP_TAC
  \\ ONCE_REWRITE_TAC [v_rel_cases] \\ fs []
  THEN1 (REPEAT (POP_ASSUM MP_TAC) \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ fs [])
  THEN1 (fs [FLOOKUP_UPDATE] \\ SRW_TAC [] [] \\ fs [FLOOKUP_DEF])
  THEN1 (imp_res_tac cl_rel_NEW_F >>
         disj2_tac >>
         fs [ETA2_THM,DOMSUB_NOT_IN_DOM] >>
         metis_tac [])
  THEN1 (imp_res_tac cl_rel_NEW_F >>
         disj2_tac >>
         fs [ETA2_THM,DOMSUB_NOT_IN_DOM] >>
         metis_tac [] ))
  |> SPEC_ALL |> MP_CANON;

val OPTREL_v_rel_NEW_F = prove(
  ``OPTREL (v_rel f2 t2.refs t2.code) x y ==>
    ~(pp IN FDOM f2) ==>
    ~(qq IN FDOM t2.refs) ==>
    OPTREL (v_rel (f2 |+ (pp,qq)) t2.refs t2.code) x y``,
  Cases_on `x` \\ Cases_on `y` \\ fs [OPTREL_def]
  \\ METIS_TAC [v_rel_NEW_F]) |> MP_CANON

(* semantic functions respect relation *)

val v_to_list = Q.prove(
  `∀v l v'.
   v_to_list v = SOME l ∧
   v_rel f r c v v'
   ⇒
   ∃l'. v_to_list v' = SOME l' ∧
        LIST_REL (v_rel f r c) l l'`,
  ho_match_mp_tac closSemTheory.v_to_list_ind >>
  rw[v_rel_SIMP,closSemTheory.v_to_list_def,bvlSemTheory.v_to_list_def] >>
  every_case_tac >> fs[] >> rw[] >>
  rw[bvlSemTheory.v_to_list_def] >> res_tac >> rw[])

val do_app = Q.prove(
  `(do_app op xs s1 = Rval (v,s2)) /\
   state_rel f s1 t1 /\
   LIST_REL (v_rel f t1.refs t1.code) xs ys /\
   (* store updates need special treatment *)
   (op <> Ref) /\ (op <> Update) ∧
   (op ≠ RefArray) ∧ (op ≠ RefByte) ∧ (op ≠ UpdateByte) ∧
   (∀n. op ≠ (FFI n)) ∧
   (* implemented in code table *)
   (op ≠ Equal) ∧ (op ≠ ToList) ==>
   ?w t2.
     (do_app (compile_op op) ys t1 = Rval (w,t2)) /\
     v_rel f t1.refs t1.code v w /\
     state_rel f s2 t2 /\
     (t1.refs = t2.refs) /\ (t1.code = t2.code)`,
  Cases_on`op`>>rw[closSemTheory.do_app_def,bvlSemTheory.do_app_def]
  >- (
    imp_res_tac state_rel_globals >>
    fs[LIST_REL_EL_EQN] >>
    BasicProvers.EVERY_CASE_TAC >> rfs[get_global_def]>>
    first_x_assum(fn th => first_x_assum(strip_assume_tac o MATCH_MP th))>> rw[] >>
    rfs[optionTheory.OPTREL_def] )
  >- (
    imp_res_tac state_rel_globals >>
    fs[LIST_REL_EL_EQN] >>
    BasicProvers.EVERY_CASE_TAC >> rfs[get_global_def]>>
    rw[v_rel_SIMP] >>
    first_x_assum(fn th => first_x_assum(strip_assume_tac o MATCH_MP th))>> rw[] >>
    rfs[OPTREL_def] >>
    fs[state_rel_def] >>
    MATCH_MP_TAC EVERY2_LUPDATE_same >>
    rfs[OPTREL_def] )
  >- (
    every_case_tac >> fs[] >> rw[] >>
    fs[state_rel_def,OPTREL_def] )
  >- simp[v_rel_SIMP]
  >- fs[]
  >- (
    Cases_on`xs`>>fs[v_rel_SIMP]>>
    Cases_on`h`>>fs[v_rel_SIMP]>>
    every_case_tac >> fs[v_rel_SIMP] >> rw[]>>
    fs[LIST_REL_EL_EQN] >> rfs[])
  >- (
    BasicProvers.EVERY_CASE_TAC >> fs[v_rel_SIMP] >>
    rw[v_rel_SIMP] >> fs[LIST_REL_EL_EQN])
  >- (
    BasicProvers.EVERY_CASE_TAC >> fs[v_rel_SIMP] >>
    rw[] >> fs[state_rel_def] >> res_tac >> fs[v_rel_SIMP] >>
    rw[] >> fs[LIST_REL_EL_EQN] )
  >- (
    every_case_tac >> fs[v_rel_SIMP] >>
    rw[] >> fs[state_rel_def] >> res_tac >> fs[v_rel_SIMP] >>
    rw[] >> fs[LIST_REL_EL_EQN] )
  >- (
    Cases_on`xs`>>fs[v_rel_SIMP]>>
    Cases_on`t`>>fs[v_rel_SIMP]>>
    Cases_on`h'`>>fs[v_rel_SIMP]>>
    Cases_on`h`>>fs[v_rel_SIMP]>>
    every_case_tac >> fs[v_rel_SIMP] >> rw[v_rel_SIMP] >>
    fs[state_rel_def] >> res_tac >> fs[v_rel_SIMP] >>
    rw[] >> fs[LIST_REL_EL_EQN] >>rw[]>>fs[])
  >- (
    every_case_tac >> fs[v_rel_SIMP] >> rw[v_rel_SIMP] >>
    imp_res_tac v_to_list >> fs[] >> rw[] )
  >- (
    every_case_tac >> fs[v_rel_SIMP] >> rw[v_rel_SIMP] >>
    fs[LIST_REL_EL_EQN])
  >- ( every_case_tac >> fs[v_rel_SIMP] >> rw[v_rel_SIMP] )
  >- ( every_case_tac >> fs[v_rel_SIMP] >> rw[v_rel_SIMP] )
  >- (
    Cases_on`xs`>>fs[v_rel_SIMP]>>
    Cases_on`t`>>fs[v_rel_SIMP]>>
    Cases_on`h'`>>fs[v_rel_SIMP]>>
    Cases_on`h`>>fs[v_rel_SIMP]>>
    every_case_tac >> fs[v_rel_SIMP] >> rw[v_rel_SIMP] >>
    fs[state_rel_def] >> res_tac >> fs[v_rel_SIMP] >>
    rw[] >> fs[LIST_REL_EL_EQN] >>rw[]>>fs[] >>
    first_x_assum match_mp_tac >> intLib.COOPER_TAC)
  >- ( every_case_tac >> fs[v_rel_SIMP] >> rw[v_rel_SIMP] )
  >> (
    Cases_on`xs`>>fs[v_rel_SIMP]>>
    Cases_on`t`>>fs[v_rel_SIMP]>>
    Cases_on`h'`>>fs[v_rel_SIMP]>>
    Cases_on`h`>>fs[v_rel_SIMP]>>
    Cases_on`t'`>>fs[v_rel_SIMP]>>
    rw[v_rel_SIMP] >>
    last_x_assum mp_tac >>
    rw[v_rel_SIMP] >>
    rw[v_rel_SIMP]))

(* compiler correctness *)

val EXISTS_NOT_IN_refs = prove(
  ``?x. ~(x IN FDOM (t1:bvlSem$state).refs)``,
  METIS_TAC [NUM_NOT_IN_FDOM])

val lookup_vars_IMP2 = prove(
  ``!vs env xs env2.
      (lookup_vars vs env = SOME xs) /\
      env_rel f refs code env env2 ==>
      ?ys. (!t1. (evaluate (MAP Var vs,env2,t1) = (Rval ys,t1))) /\
           EVERY2 (v_rel f refs code) xs ys /\
           (LENGTH vs = LENGTH xs)``,
  Induct \\ fs [lookup_vars_def,evaluate_def]
  \\ REPEAT STRIP_TAC
  \\ Cases_on `lookup_vars vs env` \\ fs [] \\ SRW_TAC [] []
  \\ ONCE_REWRITE_TAC [evaluate_CONS]
  \\ fs [evaluate_def]
  \\ RES_TAC \\ IMP_RES_TAC LESS_LENGTH_env_rel_IMP \\ fs []);

val lookup_vars_IMP = prove(
  ``!vs env xs env2.
      (lookup_vars vs env = SOME xs) /\
      env_rel f refs code env env2 ==>
      ?ys. (evaluate (MAP Var vs,env2,t1) = (Rval ys,t1)) /\
           EVERY2 (v_rel f refs code) xs ys /\
           (LENGTH vs = LENGTH xs)``,
  metis_tac[lookup_vars_IMP2])

val compile_IMP_code_installed = prove(
  ``(compile xs aux = (c,aux1)) /\
    code_installed aux1 code ==>
    code_installed aux code``,
  REPEAT STRIP_TAC
  \\ MP_TAC (SPEC_ALL compile_acc) \\ fs [LET_DEF]
  \\ REPEAT STRIP_TAC \\ fs [code_installed_def]);

val compile_LIST_IMP_compile_EL = prove(
  ``!exps aux1 c7 aux7 i n8 n4 aux5 num_args e.
      EL i exps = (num_args, e) ∧
      (compile (MAP SND exps) aux1 = (c7,aux7)) /\ i < LENGTH exps /\
      (build_aux n8 (MAP2 (code_for_recc_case k) (MAP FST exps) c7) aux7 = (n4,aux5)) /\
      code_installed aux5 t1.code ==>
      ?aux c aux1'.
        compile [e] aux = ([c],aux1') /\
        lookup (i + n8) t1.code = SOME (num_args + 1,SND (code_for_recc_case k num_args c)) /\
        code_installed aux1' t1.code``,
  HO_MATCH_MP_TAC SNOC_INDUCT \\ fs [] \\ REPEAT STRIP_TAC
  \\ Cases_on `i = LENGTH exps` \\ fs [] THEN1
   (fs [SNOC_APPEND,EL_LENGTH_APPEND]
    \\ fs [GSYM SNOC_APPEND,compile_SNOC]
    \\ `?c1 aux2. compile (MAP SND exps) aux1 = (c1,aux2)` by METIS_TAC [PAIR]
    \\ `?c3 aux3. compile [e] aux2 = (c3,aux3)` by METIS_TAC [PAIR]
    \\ fs [LET_DEF] \\ SRW_TAC [] []
    \\ Q.LIST_EXISTS_TAC [`aux2`] \\ fs []
    \\ IMP_RES_TAC compile_SING \\ fs []
    \\ fs [code_installed_def]
    \\ qpat_assum `xxx++[yyy]=zzz` (assume_tac o GSYM)
    \\ fs []
    \\ rpt BasicProvers.VAR_EQ_TAC
    \\ IMP_RES_TAC compile_LENGTH \\ fs []
    \\ fs [GSYM SNOC_APPEND, map2_snoc]
    \\ fs [SNOC_APPEND, build_aux_APPEND1]
    \\ Cases_on `build_aux n8 (MAP2 (code_for_recc_case k) (MAP FST exps) c1) aux3`
    \\ fs [LET_DEF]
    \\ IMP_RES_TAC build_aux_LENGTH
    \\ fs [AC ADD_COMM ADD_ASSOC]
    \\ rpt BasicProvers.VAR_EQ_TAC
    \\ fs [LENGTH_MAP2]
    \\ Cases_on `code_for_recc_case k num_args d`
    \\ fs []
    \\ (qspecl_then [`MAP2 (code_for_recc_case k) (MAP FST exps) c1`,`n8`,`aux3`]
           mp_tac build_aux_acc) \\ fs []
    \\ REPEAT STRIP_TAC \\ fs []
    \\ rfs []
    \\ fs [code_for_recc_case_def] )
  \\ `i < LENGTH exps` by DECIDE_TAC
  \\ fs [EL_SNOC]
  \\ fs [MAP_SNOC, compile_SNOC]
  \\ `?c1 aux2. compile (MAP SND exps) aux1 = (c1,aux2)` by METIS_TAC [PAIR]
  \\ `?c3 aux3. compile [SND x] aux2 = (c3,aux3)` by METIS_TAC [PAIR]
  \\ fs [LET_DEF]
  \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`aux1`]) \\ fs []
  \\ SRW_TAC [] [] \\ POP_ASSUM (MP_TAC o Q.SPECL [`i`,`n8`])
  \\ fs [] \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC compile_SING \\ SRW_TAC [] []
  \\ imp_res_tac compile_LENGTH
  \\ fs [GSYM SNOC_APPEND, map2_snoc]
  \\ fs [SNOC_APPEND, MAP,build_aux_APPEND1]
  \\ Cases_on `build_aux n8 (MAP2 (code_for_recc_case k) (MAP FST exps) c1) aux3`
  \\ fs [LET_DEF] \\ NTAC 4 (POP_ASSUM MP_TAC)
  \\ qspecl_then [`[SND x]`,`aux2`] mp_tac compile_acc
  \\ fs [LET_DEF] \\ REPEAT STRIP_TAC \\ SRW_TAC [] []
  \\ FIRST_X_ASSUM MATCH_MP_TAC
  \\ POP_ASSUM MP_TAC
  \\ ONCE_REWRITE_TAC [build_aux_MOVE]
  \\ REPEAT STRIP_TAC \\ fs []
  \\ fs [code_installed_def]);

val evaluate_recc_Lets = prove(
  ``!(ll:(num#'a) list) n7 rr env' t1 ys c8 (x:(num#'a)) (x':(num#'a)) ck.
     EVERY (\n. n7 + num_stubs + n IN domain t1.code) (GENLIST I (LENGTH ll)) ==>
     (evaluate
       ([recc_Lets (n7 + num_stubs) (REVERSE (MAP FST ll)) (LENGTH ll) (HD c8)],
        Block closure_tag [CodePtr (n7 + (num_stubs + LENGTH ll)); Number (&(FST x-1)); RefPtr rr]::env',
        t1 with <| refs := t1.refs |+ (rr,
               ValueArray
               (MAP (K (Number 0)) (MAP FST ll) ++
                [Block closure_tag [CodePtr (n7 + (num_stubs + LENGTH ll)); Number (&(FST x'-1)); RefPtr rr]]++ys));clock := ck |>) =
      evaluate
       ([HD c8],
        MAP2 (\n args. Block closure_tag [CodePtr (n7 + num_stubs + n); Number &(args-1); RefPtr rr])
                  (GENLIST I (LENGTH ll + 1)) (MAP FST ll ++ [FST x]) ++ env',
        t1 with <| refs := t1.refs |+ (rr,
               ValueArray
               (MAP2 (\n args. Block closure_tag [CodePtr (n7 + num_stubs + n); Number &(args-1); RefPtr rr])
                  (GENLIST I (LENGTH ll + 1)) (MAP FST ll ++ [FST x']) ++ ys)); clock := ck |>))``,
  recInduct SNOC_INDUCT \\ fs [] \\ REPEAT STRIP_TAC
  \\ ONCE_REWRITE_TAC [recc_Lets_def] \\ fs [LET_DEF]
  \\ fs [bvlSemTheory.evaluate_def,recc_Let_def,bvlSemTheory.do_app_def]
  \\ simp []
  \\ fs [DECIDE ``0 < k + SUC n:num``,EVERY_SNOC,GENLIST, ADD_ASSOC]
  \\ fs [FLOOKUP_UPDATE,DECIDE ``n < SUC n + m``,DECIDE ``0 < 1 + SUC n``,
         DECIDE ``0 < 1 + n:num``,DECIDE ``2 < 1 + (1 + (1 + n:num))``]
  \\ simp []
  \\ fs [SNOC_APPEND,MAP_APPEND,MAP, MAP_REVERSE, REVERSE_APPEND, tl_append]
  \\ `LENGTH l = LENGTH (MAP (K (Number 0:bvlSem$v)) (MAP FST (l:(num#'a) list)))` by rw []
  \\ ONCE_ASM_REWRITE_TAC []
  \\ pop_assum kall_tac
  \\ rw_tac std_ss [SIMP_RULE std_ss [GSYM APPEND_ASSOC] lupdate_append2, GSYM APPEND_ASSOC]
  \\ simp []
  \\ rw_tac std_ss [PROVE [APPEND_ASSOC] ``!(a:'a list) b c d. a ++ b ++ c ++ d = a ++ b ++ (c ++ d)``] >>
  first_x_assum (qspecl_then [`n7`, `rr`,
                   `Block closure_tag [CodePtr (n7 + (num_stubs + SUC (LENGTH l))); Number (&(FST x'-1)); RefPtr rr]::env'`,
                   `t1`,
                   `[Block closure_tag [CodePtr (n7 + (num_stubs + SUC (LENGTH l))); Number (&(FST x''-1)); RefPtr rr]] ++ ys`,
                   `c8`,
                    `x`,
                    `x`,
                    `ck`] assume_tac) >>
  rev_full_simp_tac std_ss [ADD_ASSOC] >>
  rw_tac std_ss [ADD_ASSOC] >>
  simp [GENLIST, GSYM ADD1, GSYM SNOC_APPEND, map2_snoc] >>
  simp [SNOC_APPEND, APPEND_ASSOC]
  \\ FULL_SIMP_TAC std_ss [DECIDE ``SUC n + 1 = SUC (n+1)``,GENLIST]
  \\ FULL_SIMP_TAC std_ss [ADD1,SNOC_APPEND]
  \\ SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND]);

val evaluate_app_helper = Q.prove (
  `(!x. r ≠ Rval x) ∧ evaluate (c8,env,s) = (r,s')
    ⇒
    evaluate
           ([case loc of
              NONE => Let (c8++[c7]) (mk_cl_call (Var (LENGTH c8)) (GENLIST Var (LENGTH c8)))
            | SOME loc => Call (LENGTH c8 - 1) (SOME (loc + num_stubs)) (c8++[c7])],env,s) = (r, s')`,
  rw [] >>
  Cases_on `loc` >>
  rw [bvlSemTheory.evaluate_def, bvlPropsTheory.evaluate_APPEND] >>
  Cases_on `r` >>
  rw []);

val evaluate_app_helper2 = Q.prove (
  `(!x. r ≠ Rval x) ∧ evaluate (c8,env,s) = (Rval x, s') ∧ evaluate ([c7],env,s') = (r,s'')
    ⇒
    evaluate ([case loc of
              NONE => Let (c8++[c7]) (mk_cl_call (Var (LENGTH c8)) (GENLIST Var (LENGTH c8)))
            | SOME loc => Call (LENGTH c8 - 1) (SOME (loc + num_stubs)) (c8++[c7])],env,s) = (r, s'')`,
  rw [] >>
  Cases_on `loc` >>
  rw [bvlSemTheory.evaluate_def, bvlPropsTheory.evaluate_APPEND] >>
  Cases_on `r` >>
  rw []);

val evaluate_simple_genlist_vars = Q.prove (
  `!env1 env2 s.
    0 < LENGTH env1
    ⇒
    evaluate (GENLIST Var (LENGTH env1), env1++env2, s) = (Rval env1, s)`,
  rw [] >>
  qspecl_then [`0`, `env1++env2`, `LENGTH env1`, `s`] assume_tac evaluate_genlist_vars >>
  rfs [] >>
  rpt (pop_assum mp_tac) >>
  srw_tac [ARITH_ss] [TAKE_LENGTH_APPEND] >>
  metis_tac []);

val num_remaining_args_def = Define `
  (num_remaining_args (Closure loc_opt args env num_args exp : closSem$v) =
    SOME (num_args - LENGTH args)) ∧
  (num_remaining_args (Recclosure loc_opt args env funs i : closSem$v) =
    SOME (FST (EL i funs) - LENGTH args)) ∧
  (num_remaining_args _ = NONE)`;

val dest_closure_part_app = Q.prove (
  `!loc_opt func args c f1 t1.
    LENGTH args ≠ 0 ∧
    dest_closure loc_opt func args = SOME (Partial_app c)
    ⇒
    loc_opt = NONE ∧
    SOME c = add_args func args ∧
    ?n. num_remaining_args func = SOME n ∧ LENGTH args < n ∧ LENGTH args ≤ max_app`,
  rw [dest_closure_def] >>
  BasicProvers.EVERY_CASE_TAC >>
  fs [add_args_def, LET_THM, num_remaining_args_def] >>
  TRY (Cases_on `EL n l1`) >>
  fs [] >>
  BasicProvers.EVERY_CASE_TAC >>
  fs [] >>
  Cases_on `loc_opt` >>
  fs [check_loc_def] >>
  decide_tac);

val get_loc_def = Define `
  (get_loc (Closure loc args env num_args exp) = SOME loc) ∧
  (get_loc (Recclosure loc args env fns i) = SOME (loc + i)) ∧
  (get_loc _ = NONE)`;

val get_old_args_def = Define `
  (get_old_args (Closure loc args env num_args exp) = SOME args) ∧
  (get_old_args (Recclosure loc args env fns i) = SOME args) ∧
  (get_old_args _ = NONE)`;

val get_cl_env_def = Define `
  (get_cl_env (Closure loc args env num_args exp) = SOME env) ∧
  (get_cl_env (Recclosure loc args env fns i) = SOME env) ∧
  (get_cl_env _ = NONE)`;

val dest_closure_full_app = Q.prove (
  `!loc_opt func args c f1 t1 exp args1 args2.
    dest_closure loc_opt func args = SOME (Full_app exp args1 args2)
    ⇒
    ?rem_args loc num_args old_args cl_env.
      get_loc func = SOME loc ∧
      num_remaining_args func = SOME rem_args ∧
      get_num_args func = SOME num_args ∧
      get_old_args func = SOME old_args ∧
      get_cl_env func = SOME cl_env ∧
      rem_args ≤ LENGTH args ∧
      rem_args ≤ num_args ∧
      num_args ≤ LENGTH old_args + LENGTH args ∧
      LENGTH args2 = LENGTH args - rem_args ∧
      check_loc loc_opt loc num_args (LENGTH args) (num_args - rem_args)`,
  rw [dest_closure_def] >>
  BasicProvers.EVERY_CASE_TAC >>
  fs [] >>
  TRY (Cases_on `EL n l1`) >>
  fs [LET_THM] >>
  BasicProvers.EVERY_CASE_TAC >>
  fs [get_cl_env_def, get_old_args_def, get_loc_def, num_remaining_args_def, get_num_args_def] >>
  full_simp_tac (srw_ss()++ARITH_ss) [] >>
  rw [] >>
  decide_tac);

val v_rel_num_rem_args = Q.prove (
  `!f refs code v1 v2 n.
    v_rel f refs code v1 v2 ∧
    num_remaining_args v1 = SOME n
    ⇒
    ?tag ptr rest exp.
      v2 = Block tag (CodePtr ptr::Number (&n-1)::rest) ∧
      n ≠ 0 ∧
      lookup ptr code = SOME (n+1, exp)`,
  rw [v_rel_cases] >>
  fs [num_remaining_args_def]
  >- (fs [cl_rel_cases] >>
      rw [] >>
      fs [num_remaining_args_def, int_arithTheory.INT_NUM_SUB,closure_code_installed_def,
          EVERY_EL, EL_MAP] >>
      pop_assum (mp_tac o GSYM) >>
      rw [] >>
      pop_assum (fn th => first_assum (mp_tac o MATCH_MP th)) >>
      Cases_on `EL k exps_ps` >>
      simp [] >>
      Cases_on `q` >>
      fs [] >>
      rw [] >>
      simp [EL_MAP])
  >- (fs [cl_rel_cases] >>
      rw [] >>
      fs [get_num_args_def, add_args_def] >>
      rw [] >>
      fs [num_remaining_args_def, int_arithTheory.INT_NUM_SUB] >>
      intLib.ARITH_TAC));

val unpack_closure_thm = Q.prove (
  `v_rel f1 t1.refs t1.code func (Block tag (ptr::Number (&n-1)::rest)) ∧
   num_remaining_args func = SOME n
   ⇒
   ?prev_args total_args clo.
     unpack_closure (Block tag (ptr::Number (&n-1)::rest)) (prev_args, total_args, clo) ∧
     total_args < max_app ∧
     n = total_args − LENGTH prev_args + 1  ∧
     (tag = closure_tag ⇒ prev_args = [] ∧ clo = Block tag (ptr::Number (&n-1)::rest))`,
  rw [unpack_closure_cases, v_rel_cases, cl_rel_cases, num_remaining_args_def] >>
  fs [num_remaining_args_def] >>
  rw_tac bool_ss [] >>
  TRY ARITH_TAC >>
  fs [EL_MAP] >>
  `?n e p. EL k exps_ps = ((n,e),p)` by metis_tac [pair_CASES] >>
  fs [closure_code_installed_def, EVERY_EL] >>
  res_tac >>
  rfs [] >>
  TRY ARITH_TAC >>
  srw_tac [boolSimps.DNF_ss] [partial_app_tag_def, int_arithTheory.INT_NUM_SUB] >>
  imp_res_tac EVERY2_LENGTH >>
  fs [add_args_def, get_num_args_def, EL_MAP] >>
  TRY ARITH_TAC >>
  srw_tac [boolSimps.DNF_ss] [partial_app_tag_def, int_arithTheory.INT_NUM_SUB] >>
  TRY decide_tac >>
  TRY (Cases_on `ys`) >>
  fs [ADD1, num_remaining_args_def] >>
  srw_tac [ARITH_ss] [integerTheory.int_ge, integerTheory.INT_LE_SUB_LADD, integerTheory.INT_LE_LT1] >>
  TRY(simp[closure_tag_def]>>NO_TAC) >>
  first_x_assum (fn th => first_assum (mp_tac o MATCH_MP th)) >>
  rw [EL_MAP] >>
  decide_tac);

val cl_rel_get_num_args = Q.prove (
  `cl_rel f1 refs code (env,ys) func (Block tag (p::Number (&(total_args) - 1)::fvs))
   ⇒
   get_num_args func = SOME total_args`,
  rw [cl_rel_cases] >>
  fs [get_num_args_def, int_arithTheory.INT_NUM_SUB, EL_MAP, closure_code_installed_def, EVERY_EL] >>
  `?n e p. EL k exps_ps = ((n,e),p)` by metis_tac [pair_CASES] >>
  fs [] >>
  rw [] >>
  pop_assum mp_tac >>
  res_tac >>
  rw [] >>
  fs [] >>
  ARITH_TAC);

val arith_helper_lem = Q.prove (
  `LENGTH args' ≠ 0 ⇒ x − 1 − (LENGTH args' − 1) = x − LENGTH args'`,
  decide_tac);

val arith_helper_lem3 = Q.prove (
  `LENGTH args' < total_args + 1 − LENGTH prev_args ∧
   LENGTH args' ≠ 0 ∧
   total_args − LENGTH prev_args + 1 = num_args − LENGTH prev_args
   ⇒
   total_args − (LENGTH args' + LENGTH prev_args − 1) = total_args + 1 − (LENGTH args' + LENGTH prev_args) ∧
   LENGTH args' + LENGTH prev_args < total_args + 1 ∧
   num_args = total_args+1`,
  rw [int_arithTheory.INT_NUM_SUB] >>
  ARITH_TAC);

val closure_tag_neq_1 = EVAL``closure_tag = 1``|>EQF_ELIM

val cEval_def = closSemTheory.evaluate_def;
val cEval_SING = closPropsTheory.evaluate_SING;
val bEval_def = bvlSemTheory.evaluate_def;
val bEval_CONS = bvlPropsTheory.evaluate_CONS;
val bEval_SING = bvlPropsTheory.evaluate_SING;
val bEval_APPEND = bvlPropsTheory.evaluate_APPEND;
val bEvalOp_def = bvlSemTheory.do_app_def;

val evaluate_mk_cl_call_spec = Q.prove (
  `!s env tag p n args exp xs.
    lookup p s.code = SOME (n+2, exp) ∧
    lookup (LENGTH args - 1) s.code = SOME (LENGTH args + 1, generate_generic_app (LENGTH args - 1)) ∧
    LENGTH args - 1 ≥ n ∧
    n < max_app ∧
    LENGTH args ≠ 0
    ⇒
    evaluate ([mk_cl_call (Var (LENGTH args)) (GENLIST Var (LENGTH args))],args ++ [Block tag (CodePtr p::Number (&n)::xs)] ++ env,s) =
     if n = LENGTH args - 1 then
       if s.clock < LENGTH args
       then (Rerr(Rabort Rtimeout_error),s with clock := 0)
       else evaluate ([exp],
                   args ++ [Block tag (CodePtr p::Number (&(LENGTH args − 1))::xs)],
                   dec_clock (LENGTH args) s)
     else
         if s.clock < n + 2
         then (Rerr(Rabort Rtimeout_error),s with clock := 0)
         else
         case evaluate ([exp],
                     DROP (LENGTH args − (n + 1)) args ++ [Block tag (CodePtr p::Number (&n)::xs)],
                     dec_clock (n + 2) s)
           of
            | (Rval [v],st') =>
                (case evaluate ([mk_cl_call (Var 0) (GENLIST (λn. Var (n + 1)) (LENGTH args − (n + 1)))],
                              v::(args ++ [Block tag (CodePtr p::Number (&n)::xs)]),
                              st') of
                    | (Rval v,s2) => (Rval [HD v],s2)
                    | x => x)
            | x => x`,
  rpt strip_tac >>
  `evaluate ([Var (LENGTH args)], args ++ [Block tag (CodePtr p::Number (&n)::xs)] ++ env,s) =
   (Rval [Block tag (CodePtr p::Number (&n)::xs)], s)`
           by simp [bEval_def, el_append3] >>
  `evaluate (GENLIST Var (LENGTH args), args ++ [Block tag (CodePtr p::Number (&n)::xs)] ++ env,s) =
    (Rval args, s)`
           by (qspecl_then [`0`, `args++[Block tag (CodePtr p::Number (&n)::xs)]++env`, `LENGTH args`]mp_tac evaluate_genlist_vars >>
               simp [ETA_THM] >>
               metis_tac [APPEND_ASSOC, TAKE_LENGTH_APPEND]) >>
  strip_assume_tac (SIMP_RULE (srw_ss()) [GSYM AND_IMP_INTRO] evaluate_mk_cl_call) >>
  rpt (pop_assum (fn th => first_assum (strip_assume_tac o MATCH_MP th))) >>
  rfs []);

val cl_rel_get_loc = Q.prove (
  `cl_rel f1 refs code (env,fvs) func (Block tag (CodePtr p::n::ys))
   ⇒
   num_stubs ≤ p ∧
   get_loc func = SOME (p-num_stubs)`,
  rw [cl_rel_cases] >>
  fs [get_loc_def, closure_code_installed_def, EVERY_EL] >>
  `?n e p. EL k exps_ps = ((n,e),p)` by metis_tac [pair_CASES] >>
  fs [] >>
  rw [] >>
  pop_assum mp_tac >>
  res_tac >>
  rw [] >>
  fs [EL_MAP] >>
  rw [] >>
  `p = EL k (GENLIST (λn. loc + num_stubs + n) (LENGTH exps_ps))` by metis_tac [p_genlist] >>
  rw [] >>
  ARITH_TAC);

(* Differs from check_loc and dest_closure by not checking that max_app *)
val check_loc'_def = Define `
  (check_loc' NONE loc num_params num_args so_far ⇔  T) ∧
  (check_loc' (SOME p) loc num_params num_args so_far ⇔
    (num_params = num_args) ∧ (so_far = 0:num) ∧ (p = loc))`;

val dest_closure'_def = Define `
  dest_closure' loc_opt f args =
    case f of
    | Closure loc arg_env clo_env num_args exp =>
        if check_loc' loc_opt loc num_args (LENGTH args) (LENGTH arg_env) ∧ LENGTH arg_env < num_args then
          if ¬(LENGTH args + LENGTH arg_env < num_args) then
            SOME (Full_app exp
                           (REVERSE (TAKE (num_args - LENGTH arg_env) (REVERSE args))++
                            arg_env++clo_env)
                           (REVERSE (DROP (num_args - LENGTH arg_env) (REVERSE args))))
          else
            SOME (Partial_app (Closure loc (args++arg_env) clo_env num_args exp))
        else
          NONE
    | Recclosure loc arg_env clo_env fns i =>
        let (num_args,exp) = EL i fns in
          if LENGTH fns <= i \/
             ~(check_loc' loc_opt (loc+i) num_args (LENGTH args) (LENGTH arg_env)) ∨
             ¬(LENGTH arg_env < num_args) then NONE else
            let rs = GENLIST (Recclosure loc [] clo_env fns) (LENGTH fns) in
              if ¬(LENGTH args + LENGTH arg_env < num_args) then
                SOME (Full_app exp
                               (REVERSE (TAKE (num_args - LENGTH arg_env) (REVERSE args))++
                                arg_env++rs++clo_env)
                               (REVERSE (DROP (num_args - LENGTH arg_env) (REVERSE args))))
              else
                SOME (Partial_app (Recclosure loc (args++arg_env) clo_env fns i))
    | _ => NONE`;

val dest_cl_imp_dest_cl' = Q.prove (
  `dest_closure l f a = SOME x ⇒ dest_closure' l f a = SOME x`,
  rw [dest_closure_def, dest_closure'_def] >>
  BasicProvers.EVERY_CASE_TAC >>
  fs [] >>
  Cases_on `l` >>
  fs [check_loc_def, check_loc'_def, LET_THM] >>
  Cases_on `EL n l1` >>
  fs []);

val cl_rel_run_lemma1 = Q.prove (
  `num_args ≤ LENGTH args'
   ⇒
   evaluate (GENLIST Var num_args, DROP (LENGTH args' - num_args) args' ++ stuff, t1) =
   (Rval (DROP (LENGTH args' - num_args) args'), t1)`,
  rw [] >>
  assume_tac (Q.SPECL [`0`, `DROP (LENGTH args' - num_args) args'++stuff`, `num_args`, `t1`] evaluate_genlist_vars) >>
  rfs [] >>
  rpt (pop_assum mp_tac) >>
  srw_tac [ARITH_ss] [ETA_THM] >>
  `LENGTH (DROP (LENGTH args' - num_args) args') = num_args` by srw_tac [ARITH_ss] [] >>
  metis_tac [TAKE_LENGTH_APPEND]);

val cl_rel_run_lemma2 = Q.prove (
  `num_args ≤ LENGTH args'
   ⇒
   evaluate (GENLIST Var (num_args + 1), DROP (LENGTH args' - num_args) args' ++ [f] ++ stuff, t1) =
   (Rval (DROP (LENGTH args' - num_args) args' ++ [f]), t1)`,
  rw [] >>
  assume_tac (Q.SPECL [`0`, `DROP (LENGTH args' - num_args) args'++[f]++stuff`, `num_args+1`, `t1`] evaluate_genlist_vars) >>
  rfs [] >>
  rpt (pop_assum mp_tac) >>
  srw_tac [ARITH_ss] [ETA_THM] >>
  `LENGTH (DROP (LENGTH args' - num_args) args'++[f]) = num_args+1` by srw_tac [ARITH_ss] [] >>
  metis_tac [TAKE_LENGTH_APPEND]) |> Q.INST [`stuff`|-> `[]`] |> SIMP_RULE (srw_ss()) [];

val cl_rel_run_lemma3 = Q.prove (
  `LIST_REL R args args' ⇒
   LIST_REL R (DROP (LENGTH args' − n) args) (DROP (LENGTH args' − n) args')`,
  fs [LIST_REL_EL_EQN] >>
  rw [] >>
  `n' + (LENGTH args' − n) < LENGTH args` by decide_tac >>
  `n' + (LENGTH args' − n) < LENGTH args'` by metis_tac [] >>
  rw [EL_DROP]);

val bEval_free_let_Block = Q.prove (
  `!ys zs.
    evaluate ([x],env,s) = (Rval [Block n (y::z::ys ++ zs)], s)
    ⇒
    evaluate (free_let x (LENGTH ys),env,s) = (Rval ys,s)`,
  ho_match_mp_tac SNOC_INDUCT >>
  rw [free_let_def, bEval_def] >>
  fs [SNOC_APPEND] \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC] >>
  res_tac >>
  fs [GENLIST, bvlPropsTheory.evaluate_SNOC, bEvalOp_def, bEval_def] >>
  simp [EL_CONS, PRE_SUB1, el_append3])
   |> Q.SPECL [`ys`,`[]`] |> SIMP_RULE std_ss [APPEND_NIL];

val cl_rel_run_tac =
  qexists_tac `c` >>
  qexists_tac `aux` >>
  qexists_tac `aux1` >>
  imp_res_tac EVERY2_LENGTH >>
  fs [] >>
  rw [bEval_def, bEval_APPEND] >>
  rw_tac (std_ss) [GSYM APPEND_ASSOC] >>
  simp [cl_rel_run_lemma1, cl_rel_run_lemma2] >>
  `LENGTH (DROP (LENGTH args' − num_args) args') = num_args`
             by (rw [] >> decide_tac) >>
  qexists_tac `witness` >>
  rw [] >>
  `evaluate ([Var num_args], DROP (LENGTH args' − num_args) args' ++ [func'],t1 with refs := refs) = (Rval [func'],t1 with refs := refs)`
          by (rw [bEval_def]
              >- metis_tac [EL_LENGTH_APPEND, NULL, HD]) >>
  simp [TAKE_REVERSE, LASTN_DROP] >>
  unabbrev_all_tac >>
  imp_res_tac bEval_free_let_Block >>
  rfs [] >>
  rw [] >>
  metis_tac [list_rel_IMP_env_rel, APPEND_ASSOC, LASTN_LENGTH_ID, env_rel_APPEND, LIST_REL_def, cl_rel_run_lemma3];

val genlist_deref = Q.prove (
  `!skip st r xs args p n env ys.
    FLOOKUP st.refs r = SOME (ValueArray (ys++xs)) ∧
    skip = LENGTH ys
    ⇒
    evaluate (GENLIST (λi. Op Deref [Op (Const (&(i + skip))) []; Var 0]) (LENGTH xs),
           RefPtr r:: (args ++ Block closure_tag [CodePtr p; Number (&n); RefPtr r]::env),
           st)
    =
    (Rval xs, st)`,
  Induct_on `xs` >>
  rw [evaluate_def, GENLIST_CONS] >>
  rw [Once evaluate_CONS, evaluate_def, do_app_def, combinTheory.o_DEF] >>
  `FLOOKUP st.refs r = SOME (ValueArray ((ys++[h])++xs))` by rw [] >>
  first_x_assum (fn th => first_assum (assume_tac o MATCH_MP (SIMP_RULE (srw_ss()) [GSYM AND_IMP_INTRO] th))) >>
  simp [ADD1] >>
  rw [] >>
  fs [ADD1] >>
  rw [EL_LENGTH_APPEND]);

val evaluate_code_for_recc_case = Q.prove (
  `!st r xs args c p n env.
    FLOOKUP st.refs r = SOME (ValueArray xs)
    ⇒
    evaluate ([SND (code_for_recc_case (LENGTH xs) (LENGTH args) c)],
              args ++ Block closure_tag [CodePtr p;Number &n;RefPtr r]::env,
              st) =
    evaluate ([c],
              args ++ xs ++ [RefPtr r] ++ args ++ Block closure_tag [CodePtr p; Number (&n); RefPtr r]::env,
              st)`,
  simp [code_for_recc_case_def, evaluate_def, do_app_def] >>
  simp [evaluate_APPEND, EL_LENGTH_APPEND] >>
  rpt strip_tac >>
  `LENGTH args + 1 ≤ LENGTH (RefPtr r::(args ++ Block closure_tag [CodePtr p; Number (&n); RefPtr r]::env))`
              by (rw [] >> intLib.ARITH_TAC) >>
  imp_res_tac evaluate_genlist_vars >>
  fs [] >>
  mp_tac (Q.SPEC `0` genlist_deref) >>
  simp [LENGTH_NIL_SYM] >>
  rw [TAKE_LENGTH_APPEND]);

val cl_rel_run = Q.prove (
  `!loc f1 refs code args args' env env' ptr body new_env func func' rest n fvs.
    func' = Block closure_tag (CodePtr ptr::Number (&n)::env') ∧
    dest_closure' loc func args = SOME (Full_app body new_env rest) ∧
    v_rel f1 refs code func func' ∧
    cl_rel (FRANGE f1) refs code (env,fvs) func func' ∧
    LIST_REL (v_rel f1 refs code) env fvs ∧
    LIST_REL (v_rel f1 refs code) args args'
    ⇒
    ∃body' aux1 aux2 new_env' exp'.
      lookup ptr code = SOME (n + 2,exp') ∧
      compile [body] aux1 = ([body'],aux2) ∧ code_installed aux2 code ∧
      env_rel f1 refs code new_env new_env' ∧
      !t1. evaluate ([exp'], DROP (LENGTH args' - (n + 1)) args'++[func'], t1 with refs := refs) =
           evaluate ([body'], new_env', t1 with refs := refs)`,
  rw [cl_rel_cases, dest_closure'_def] >>
  fs [int_arithTheory.INT_NUM_SUB, closure_code_installed_def] >>
  rfs [] >>
  simp [] >>
  fs [check_loc_def, LET_THM] >>
  BasicProvers.EVERY_CASE_TAC >>
  rw []
  >- (qabbrev_tac `func' = Block closure_tag (CodePtr (p + num_stubs)::Number (&num_args − 1):: env')` >>
      qabbrev_tac `witness = DROP (LENGTH args' − num_args) args'++env'++DROP (LENGTH args' − num_args) args' ++ [func']` >>
      cl_rel_run_tac)
  >- (qabbrev_tac `func' = Block closure_tag (CodePtr (p + num_stubs)::Number (&num_args − 1):: env')` >>
      qabbrev_tac `witness = DROP (LENGTH args' − num_args) args'++[func']++env'++DROP (LENGTH args' − num_args) args' ++ [func']` >>
      cl_rel_run_tac) >>
  fs [EL_MAP] >>
  `?n e p. EL k exps_ps = ((n,e),p)` by metis_tac [pair_CASES] >>
  fs [] >>
  rw [] >>
  Cases_on `LENGTH args < n'` >>
  fs [EVERY_EL, closure_code_installed_def] >>
  rw [] >>
  first_assum (fn th => first_assum (mp_tac o MATCH_MP th)) >>
  ASM_REWRITE_TAC [] >>
  simp [] >>
  rw [] >>
  simp [] >>
  MAP_EVERY qexists_tac [`c`, `aux`, `aux1`,
        `DROP (LENGTH args' − (n + 1)) args' ++
         MAP (λ((n,e),p). Block closure_tag [CodePtr p; Number (if n = 0 then 0 else &n − 1); RefPtr r])
             exps_ps ++
         fvs ++
         [RefPtr r] ++
         DROP (LENGTH args' − (n + 1)) args' ++
         [Block closure_tag [CodePtr p; Number (&n); RefPtr r]]`] >>
  rw []
  >- ARITH_TAC
  >- (simp [TAKE_REVERSE, LASTN_DROP] >>
      `LIST_REL (v_rel f1 refs code)
                (DROP (LENGTH args − n') args)
                (DROP (LENGTH args' − (n + 1)) args')`
              by (`n' = n+1` by ARITH_TAC >>
                  metis_tac [cl_rel_run_lemma3, EVERY2_LENGTH]) >>
      `LIST_REL (v_rel f1 refs code)
                (GENLIST (Recclosure loc' [] env (MAP FST exps_ps)) (LENGTH exps_ps))
                (MAP (λ((n,e),p).
                       Block closure_tag [CodePtr p; Number (if n = 0 then 0 else &n − 1); RefPtr r])
                     exps_ps)`
            by (rw [LIST_REL_EL_EQN] >>
                simp [v_rel_cases] >>
                simp [EL_MAP, cl_rel_cases] >>
                `?n e p. EL n'' exps_ps = ((n,e),p)` by metis_tac [pair_CASES] >>
                fs [] >>
                simp [] >>
                qexists_tac `env` >>
                simp [] >>
                qexists_tac `fvs` >>
                simp [] >>
                DISJ2_TAC >>
                qexists_tac `exps_ps` >>
                simp [EL_MAP] >>
                rw [int_arithTheory.INT_NUM_SUB] >>
                rw [closure_code_installed_def] >>
                rw [EVERY_EL]) >>
      metis_tac [list_rel_IMP_env_rel, APPEND_ASSOC, EVERY2_APPEND])
  >- (`FLOOKUP refs r = FLOOKUP (t1 with refs := refs).refs r` by rw [] >>
      full_simp_tac std_ss [] >>
      imp_res_tac evaluate_code_for_recc_case >>
      fs [LENGTH_MAP] >>
      pop_assum (qspecl_then [`p`, `n`, `[]`, `c`, `DROP (LENGTH args' − (n + 1)) args'`] mp_tac) >>
      rw [] >>
      imp_res_tac EVERY2_LENGTH >>
      `LENGTH args' − (LENGTH args' − (n + 1)) = n'` by ARITH_TAC >>
      fs [] >>
      rw [Once ADD_COMM]));

val cl_rel_dest = Q.prove (
  `!f refs code cl cl' fvs fvs'.
    cl_rel f refs code (fvs,fvs') cl cl'
    ⇒
    get_old_args cl = SOME [] ∧
    ?l num_args fvs.
      cl' = Block closure_tag (CodePtr l::Number (&num_args)::fvs)`,
  rw [cl_rel_cases] >>
  rw [get_old_args_def, EL_MAP] >>
  `?n e p. EL k exps_ps = ((n,e),p)` by metis_tac [pair_CASES] >>
  rw []);

val dest_closure_full_of_part = Q.prove (
  `dest_closure loc func args = SOME (Full_app body newenv rest) ∧
   LENGTH arg_env ≠ 0 ∧
   add_args cl arg_env = SOME func ∧
   get_num_args cl = SOME num_args ∧
   LENGTH arg_env < num_args
   ⇒
   dest_closure' loc cl (args++arg_env) = SOME (Full_app body newenv rest)`,
  rw [dest_closure_def, dest_closure'_def] >>
  BasicProvers.EVERY_CASE_TAC >>
  fs [add_args_def, check_loc_def, check_loc'_def, get_num_args_def] >>
  rw [] >>
  fs [] >>
  TRY decide_tac
  >- (`LENGTH (REVERSE arg_env) ≤ n - LENGTH l` by (srw_tac [ARITH_ss] []) >>
      rw [TAKE_APPEND2] >>
      srw_tac [ARITH_ss] [])
  >- (`LENGTH (REVERSE arg_env) ≤ n - LENGTH l` by (srw_tac [ARITH_ss] []) >>
      rw [DROP_APPEND2] >>
      srw_tac [ARITH_ss] [])
  >- (Cases_on `loc` >> fs [check_loc_def, check_loc'_def])
  >- (fs [LET_THM] >>
      BasicProvers.EVERY_CASE_TAC >>
      rw [] >>
      fs [] >>
      TRY decide_tac
      >- (Cases_on `loc` >> fs [check_loc_def, check_loc'_def])
      >- (`LENGTH (REVERSE arg_env) ≤ num_args' - LENGTH l` by (srw_tac [ARITH_ss] []) >>
          rw [TAKE_APPEND2] >>
          srw_tac [ARITH_ss] [])
      >- (`LENGTH (REVERSE arg_env) ≤ num_args' - LENGTH l` by (srw_tac [ARITH_ss] []) >>
          rw [DROP_APPEND2] >>
          srw_tac [ARITH_ss] [])));

val v_rel_run = Q.prove (
  `!f1 refs code args args' env' ptr body newenv func func' rest tag n loc.
    LENGTH args ≠ 0 ∧
    func' = Block tag (CodePtr ptr::Number (&n)::env') ∧
    dest_closure loc func args = SOME (Full_app body newenv rest) ∧
    v_rel f1 refs code func func' ∧
    LIST_REL (v_rel f1 refs code) args args'
    ⇒
    ∃ck' body' aux1 aux2 newenv' exp'.
      lookup ptr code = SOME (n + 2,exp') ∧
      compile [body] aux1 = ([body'],aux2) ∧ code_installed aux2 code ∧
      env_rel f1 refs code newenv newenv' ∧
      !t1.
        evaluate ([exp'], DROP (LENGTH args' - (n + 1)) args' ++ [func'], inc_clock ck' (t1 with <|refs := refs; code := code|>)) =
        evaluate ([body'], newenv', (t1 with <| refs := refs; code := code |>))`,
  rw [] >>
  qpat_assum `v_rel x0 x1 x2 x3 x4` (fn x => mp_tac x >> simp [v_rel_cases] >> assume_tac x) >>
  rw [] >>
  imp_res_tac EVERY2_LENGTH >>
  imp_res_tac cl_rel_get_loc
  >- (qexists_tac `0` >>
      rw [] >>
      imp_res_tac dest_cl_imp_dest_cl' >>
      metis_tac [cl_rel_run]) >>
  CONV_TAC (RESORT_EXISTS_CONV List.rev) >>
  qexists_tac `generate_partial_app_closure_fn (num_args − 1) (LENGTH ys − 1)` >>
  srw_tac [ARITH_ss] [] >>
  imp_res_tac cl_rel_dest >>
  rw [] >>
  `v_rel f1 refs code cl (Block closure_tag (CodePtr l::Number (&num_args')::fvs'))`
            by (rw [v_rel_cases, partial_app_tag_def] >>
                metis_tac [closure_tag_def]) >>
  `LENGTH arg_env ≠ 0 ∧ LENGTH ys ≠ 0 ∧ LENGTH ys < num_args` by metis_tac [LENGTH_EQ_NUM] >>
  `LIST_REL (v_rel f1 refs code) (args++arg_env) (args'++ys)`
             by metis_tac [EVERY2_APPEND] >>
  assume_tac (SIMP_RULE (srw_ss()) [GSYM AND_IMP_INTRO] dest_closure_full_of_part |> GEN_ALL) >>
  rpt (pop_assum (fn th => first_assum (assume_tac o MATCH_MP th))) >>
  strip_assume_tac (SIMP_RULE (srw_ss()) [GSYM AND_IMP_INTRO] cl_rel_run) >>
  fs [] >>
  rpt (pop_assum (fn x => first_assum (strip_assume_tac o MATCH_MP x))) >>
  MAP_EVERY qexists_tac [`new_env'`, `aux2`, `aux1`, `body'`] >>
  rw [] >>
  `?total_args. &num_args' = &total_args - 1`
        by (qexists_tac `&num_args' + 1` >>
            rw [] >>
            ARITH_TAC) >>
  fs [] >>
  imp_res_tac cl_rel_get_num_args >>
  fs [] >>
  rw [] >>
  qexists_tac `1` >>
  rw [] >>
  fs [] >>
  `num_args' + 2 = LENGTH (DROP (LENGTH args' + LENGTH ys − num_args) args') + (LENGTH ys +1) ∧
   0 < LENGTH (DROP (LENGTH args' + LENGTH ys − num_args) args')`
            by (rw [LENGTH_DROP, SUB_LEFT_SUB] >>
                fs [LESS_OR_EQ] >>
                TRY ARITH_TAC >>
                `num_args' = num_args -1`  by ARITH_TAC >>
                simp [] >>
                imp_res_tac dest_closure_full_app >>
                `num_args'' = num_args ∧ LENGTH old_args = LENGTH ys`
                         by (Cases_on `cl` >>
                             fs [add_args_def] >>
                             qpat_assum `X = func` (assume_tac o GSYM) >>
                             fs [get_old_args_def, get_num_args_def] >>
                             rw [] >>
                             simp []) >>
                decide_tac) >>
  full_simp_tac bool_ss [] >>
  assume_tac (SIMP_RULE (srw_ss()++ARITH_ss) [GSYM AND_IMP_INTRO] evaluate_partial_app_fn) >>
  pop_assum (fn th => first_assum (mp_tac o MATCH_MP th)) >>
  fs [] >>
  rw [] >>
  fs [] >>
  fs [inc_clock_def] >>
  rw [] >>
  rfs [] >>
  pop_assum (qspecl_then [`Number (&num_args − 1)`,
                          `partial_app_tag`,
                          `Number (&(num_args − (LENGTH ys + 1)))`,
                          `closure_tag`,
                          `CodePtr (partial_app_fn_location (num_args − 1) (LENGTH ys − 1))`,
                          `fvs'`,
                          `t1 with <|refs:=refs;clock := t1.clock + 1; code := code|>`] mp_tac) >>
  rw [partial_app_tag_def] >>
  rw [] >>
  rw [dec_clock_def] >>
  `t1 with <|clock := t1.clock; code := code|> = t1 with code := code`
         by rw [bvlSemTheory.state_component_equality] >>
  `LENGTH args' − (LENGTH args' + LENGTH ys − num_args) + LENGTH ys − 1 = num_args -1` by ARITH_TAC >>
  fs [] >>
  `num_args' + 1 = num_args` by ARITH_TAC >>
  `LENGTH args' + LENGTH ys − (num_args' + 1) ≤ LENGTH args'` by ARITH_TAC >>
  first_x_assum (qspec_then `t1 with <| clock := t1.clock; code := code |>` mp_tac) >>
  fs [DROP_APPEND1] >>
  rw [dec_clock_def]);

val list_rel_app = Q.prove (
  `!R args args' l0 c l func rem_args.
    dest_closure NONE func args = SOME (Full_app c l l0) ∧
    num_remaining_args func = SOME rem_args ∧
    LIST_REL R args args'
    ⇒
    LIST_REL R l0 (TAKE (LENGTH args' − rem_args) args')`,
  rw [dest_closure_def, LET_THM] >>
  BasicProvers.EVERY_CASE_TAC >>
  fs [] >>
  TRY (Cases_on `EL n l1`) >>
  fs [] >>
  rw [] >>
  BasicProvers.EVERY_CASE_TAC >>
  fs [] >>
  rw [] >>
  fs [LIST_REL_EL_EQN, check_loc_def, num_remaining_args_def] >>
  srw_tac [ARITH_ss] [EL_TAKE, EL_REVERSE, EL_DROP, PRE_SUB1]);

val mk_call_simp2 = Q.prove(
  `!n args stuff stuff' v t.
    n ≤ LENGTH args ∧ LENGTH stuff' ≠ 0
    ⇒
    evaluate ([mk_cl_call (Var n) (GENLIST Var n)], (TAKE n args) ++ [v] ++ stuff, t)
    =
    evaluate ([mk_cl_call (Var 0) (GENLIST (\n. Var (n+1)) n)], v::(args++stuff'), t)`,
  strip_tac >>
  simp [mk_cl_call_def, bEval_def, bEvalOp_def, el_take_append] >>
  Cases_on `v` >>
  simp [] >>
  rw [] >>
  Cases_on`EL 1 l`>>simp[]>>
  simp[bEval_APPEND] >>
  qspecl_then [`0`, `TAKE n args ++ [Block n' l] ++ stuff`, `n`]mp_tac evaluate_genlist_vars >>
  qspecl_then [`1`, `Block n' l::(args ++ stuff')`, `n`]mp_tac evaluate_genlist_vars >>
  srw_tac [ARITH_ss] [ETA_THM, bEval_def, bEvalOp_def, el_take_append] >>
  rw [] >>
  `n+1 ≤ SUC (LENGTH args + LENGTH stuff')` by decide_tac >>
  srw_tac [ARITH_ss] [TAKE_APPEND1, TAKE_TAKE, EL_CONS]);

val no_partial_args = Q.prove (
  `num_remaining_args func = SOME x ∧
   get_num_args func = SOME x ∧
   x ≠ 0 ∧
   add_args cl arg_env = SOME func
   ⇒
   arg_env = []`,
  Cases_on `cl` >>
  rw [add_args_def] >>
  fs [get_num_args_def, num_remaining_args_def] >>
  rw [] >>
  Cases_on `arg_env` >>
  fs [] >>
  decide_tac);

val compile_correct = Q.store_thm("compile_correct",
  `(!tmp xs env s1 aux1 t1 env' f1 res s2 ys aux2.
     (tmp = (xs,env,s1)) ∧
     (evaluate (xs,env,s1) = (res,s2)) /\ res <> Rerr(Rabort Rtype_error) /\
     (compile xs aux1 = (ys,aux2)) /\
     code_installed aux2 t1.code /\
     env_rel f1 t1.refs t1.code env env' /\
     state_rel f1 s1 t1 ==>
     ?ck res' t2 f2.
        (evaluate (ys,env',t1 with clock := s1.clock + ck) = (res',t2)) /\
        result_rel (LIST_REL (v_rel f2 t2.refs t2.code)) (v_rel f2 t2.refs t2.code) res res' /\
        state_rel f2 s2 t2 /\
        f1 SUBMAP f2 /\
        (FDIFF t1.refs (FRANGE f1)) SUBMAP (FDIFF t2.refs (FRANGE f2)) ∧
        s2.clock = t2.clock) ∧
   (!loc_opt func args s1 res s2 env t1 args' func' f1.
     evaluate_app loc_opt func args s1 = (res,s2) ∧
     res ≠ Rerr(Rabort Rtype_error) ∧
     v_rel f1 t1.refs t1.code func func' ∧
     LIST_REL (v_rel f1 t1.refs t1.code) args args' ∧
     state_rel f1 s1 t1
     ⇒
     ?ck res' t2 f2.
       (LENGTH args' ≠ 0 ⇒
         case loc_opt of
          | NONE =>
              evaluate
                    ([mk_cl_call (Var (LENGTH args')) (GENLIST Var (LENGTH args'))],
                      args' ++ [func'] ++ env,
                      t1 with clock := s1.clock + ck) =
                (res',t2)
           | SOME loc =>
               (case find_code (SOME (loc + num_stubs)) (args' ++ [func']) t1.code of
                     NONE => (Rerr(Rabort Rtype_error),t2)
                   | SOME (args,exp) =>
                       if s1.clock + ck < (LENGTH args') then (Rerr(Rabort Rtimeout_error),t1 with clock := 0)
                       else evaluate ([exp],args,t1 with clock := s1.clock + ck - LENGTH args')) =
                 (res',t2)) ∧
       result_rel (LIST_REL (v_rel f2 t2.refs t2.code)) (v_rel f2 t2.refs t2.code) res res' ∧
       state_rel f2 s2 t2 ∧
       f1 ⊑ f2 ∧
       FDIFF t1.refs (FRANGE f1) ⊑ FDIFF t2.refs (FRANGE f2) ∧
       s2.clock = t2.clock)`,
  ho_match_mp_tac closSemTheory.evaluate_ind \\ REPEAT STRIP_TAC
  THEN1 (* NIL *)
   (rw [] >> fs [cEval_def,compile_def] \\ SRW_TAC [] [bEval_def]
    \\ metis_tac [ADD_0, SUBMAP_REFL] )
  THEN1 (* CONS *)
   (rw [] >>
    fs [cEval_def,compile_def] \\ SRW_TAC [] [bEval_def]
    \\ first_assum(split_pair_case_tac o lhs o concl) >> fs[]
    \\ `?q. evaluate (y::xs,env,s1) = q` by fs [] \\ PairCases_on `q` \\ fs []
    \\ fs[LET_THM]
    \\ first_assum(split_applied_pair_tac o lhs o concl) >> fs[]
    \\ first_assum(split_applied_pair_tac o lhs o concl) >> fs[]
    \\ fs [PULL_FORALL]
    \\ FIRST_X_ASSUM (qspec_then`aux1`mp_tac)
    \\ SRW_TAC [] []
    \\ IMP_RES_TAC compile_IMP_code_installed
    \\ Q.PAT_ASSUM `!xx yy zz. bbb ==> b` (MP_TAC o Q.SPECL [`t1`,`env''`,`f1`])
    \\ IMP_RES_TAC compile_SING \\ fs [] \\ REPEAT STRIP_TAC
    \\ ONCE_REWRITE_TAC [bEval_CONS]
    \\ pop_assum mp_tac >> discharge_hyps >- (
         spose_not_then STRIP_ASSUME_TAC >> fs[] )
    \\ strip_tac
    \\ REVERSE (Cases_on `v3`) \\ fs [] \\ SRW_TAC [] []
    \\ TRY (fs [] \\ rw[] \\ qexists_tac`ck` >> simp[] >>
            first_assum(match_exists_tac o concl) >> simp[] >> NO_TAC)
    \\ FIRST_X_ASSUM (qspecl_then[`aux1'`,`t2`]mp_tac) >> simp[]
    \\ imp_res_tac evaluate_code >> fs[]
    \\ disch_then(qspecl_then[`env''`,`f2`]mp_tac)
    \\ discharge_hyps >- (
         imp_res_tac env_rel_SUBMAP >>
         simp[] >> spose_not_then strip_assume_tac >> fs[])
    \\ strip_tac
    \\ fs [] \\ IMP_RES_TAC bEval_SING \\ fs []
    \\ imp_res_tac evaluate_add_clock >> fs[]
    \\ qexists_tac `ck + ck'`
    \\ fsrw_tac[ARITH_ss][inc_clock_def]
    \\ Cases_on `q0` \\ fs [] \\ SRW_TAC [] []
    \\ IMP_RES_TAC evaluate_code
    \\ IMP_RES_TAC v_rel_SUBMAP \\ fs []
    \\ IMP_RES_TAC SUBMAP_TRANS \\ fs []
    \\ rw []
    \\ METIS_TAC [v_rel_SUBMAP, SUBMAP_REFL])
  THEN1 (* Var *)
   (rw [] >>
    Cases_on `n < LENGTH env` \\ fs [compile_def,cEval_def]
    \\ IMP_RES_TAC env_rel_IMP_LENGTH
    \\ `n < LENGTH env''` by DECIDE_TAC
    \\ SRW_TAC [] [bEval_def]
    \\ MAP_EVERY Q.EXISTS_TAC [`0`, `f1`] \\ fs [SUBMAP_REFL]
    \\ MATCH_MP_TAC env_rel_IMP_EL \\ fs [])
  THEN1 (* If *)
   (rw [] >>
    fs [compile_def,cEval_def,LET_THM]
    \\ first_assum(split_applied_pair_tac o lhs o concl) >> fs[]
    \\ first_assum(split_applied_pair_tac o lhs o concl) >> fs[]
    \\ first_assum(split_applied_pair_tac o lhs o concl) >> fs[]
    \\ SRW_TAC [] [] \\ fs [bEval_def]
    \\ first_assum(split_pair_case_tac o lhs o concl) >> fs[]
    \\ SRW_TAC [] [] \\ IMP_RES_TAC compile_IMP_code_installed
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`aux1`,`t1`])
    \\ fs []
    \\ disch_then (MP_TAC o Q.SPECL [`env''`,`f1`]) \\ fs []
    \\ discharge_hyps >- ( spose_not_then strip_assume_tac >> fs[] )
    \\ strip_tac
    \\ imp_res_tac compile_SING >> rw[]
    \\ REVERSE (Cases_on `v2`) \\ fs [] \\ SRW_TAC [] []
    \\ TRY (qexists_tac `ck` >> rw [] >> first_assum(match_exists_tac o concl) >> simp[] >> NO_TAC)
    \\ IMP_RES_TAC cEval_SING \\ SRW_TAC [] []
    \\ fs []
    \\ Cases_on `Boolv T = r1` \\ fs [] THEN1
     (rw[] >> fs [] >> rw[] >> rfs[]
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`aux1'`]) \\ fs []
      \\ disch_then (MP_TAC o Q.SPECL [`t2`,`env''`,`f2`]) \\ fs []
      \\ IMP_RES_TAC evaluate_code \\ fs []
      \\ IMP_RES_TAC env_rel_SUBMAP \\ fs []
      \\ REPEAT STRIP_TAC \\ fs []
      \\ qexists_tac `ck + ck'`
      \\ rw []
      \\ imp_res_tac evaluate_add_clock
      \\ fsrw_tac[ARITH_ss][inc_clock_def] >>
      first_assum(match_exists_tac o concl) >> simp[]
      \\ IMP_RES_TAC SUBMAP_TRANS \\ fs [])
    \\ Cases_on `Boolv F = r1` \\ fs [] THEN1
     (rw[] >> fs [] >> rw[] >> rfs[]
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`aux2'`]) \\ fs []
      \\ disch_then (MP_TAC o Q.SPECL [`t2`,`env''`,`f2`]) \\ fs []
      \\ IMP_RES_TAC evaluate_code \\ fs []
      \\ IMP_RES_TAC env_rel_SUBMAP \\ fs []
      \\ REPEAT STRIP_TAC \\ fs []
      \\ qexists_tac `ck + ck'`
      \\ rw []
      \\ imp_res_tac evaluate_add_clock
      \\ fsrw_tac[ARITH_ss][inc_clock_def] >>
      first_assum(match_exists_tac o concl) >> simp[]
      \\ IMP_RES_TAC SUBMAP_TRANS \\ fs []))
  THEN1 (* Let *)
   (rw [] >>
    fs [compile_def,cEval_def,LET_THM]
    \\ first_assum(split_applied_pair_tac o lhs o concl) >> fs[]
    \\ first_assum(split_applied_pair_tac o lhs o concl) >> fs[]
    \\ SRW_TAC [] [] \\ fs [bEval_def]
    \\ first_assum(split_pair_case_tac o lhs o concl) >> fs[]
    \\ SRW_TAC [] [] \\ IMP_RES_TAC compile_IMP_code_installed
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`aux1`,`t1`])
    \\ fs []
    \\ disch_then (MP_TAC o Q.SPECL [`env''`,`f1`]) \\ fs []
    \\ discharge_hyps >- ( spose_not_then strip_assume_tac >> fs[] )
    \\ strip_tac
    \\ imp_res_tac compile_SING >> rw[]
    \\ REVERSE (Cases_on `v2`) \\ fs [] \\ SRW_TAC [] []
    \\ TRY (qexists_tac `ck` >> rw [] >> first_assum(match_exists_tac o concl) >> simp[] >> NO_TAC)
    \\ rfs[]
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`aux1'`]) \\ fs []
    \\ disch_then (MP_TAC o Q.SPECL [`t2`,`v' ++ env''`,`f2`]) \\ fs []
    \\ IMP_RES_TAC evaluate_code \\ fs []
    \\ discharge_hyps >-
     (MATCH_MP_TAC env_rel_APPEND \\ fs []
      \\ IMP_RES_TAC env_rel_SUBMAP \\ fs [])
    \\ REPEAT STRIP_TAC \\ fs []
    \\ qexists_tac `ck + ck'`
    \\ imp_res_tac evaluate_add_clock
    \\ fsrw_tac[ARITH_ss][inc_clock_def]
    \\ first_assum(match_exists_tac o concl) >> simp[]
    \\ IMP_RES_TAC SUBMAP_TRANS \\ fs [])
  THEN1 (* Raise *)
   (rw [] >>
    fs [cEval_def,compile_def,LET_THM] \\ SRW_TAC [] [bEval_def]
    \\ first_assum(split_applied_pair_tac o lhs o concl) >> fs[]
    \\ first_assum(split_pair_case_tac o lhs o concl) >> fs[]
    \\ fs [PULL_FORALL] \\ SRW_TAC [] []
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`aux1`]) \\ fs []
    \\ IMP_RES_TAC compile_IMP_code_installed
    \\ disch_then (MP_TAC o Q.SPECL [`t1`,`env''`,`f1`])
    \\ IMP_RES_TAC compile_SING \\ fs []
    \\ discharge_hyps >- ( spose_not_then strip_assume_tac >> fs[] )
    \\ fs [bEval_def]
    \\ REVERSE (Cases_on `v2`) \\ fs [] \\ SRW_TAC [] []
    \\ TRY (qexists_tac `ck` >> rw [] >> first_assum(match_exists_tac o concl) >> simp[] >> NO_TAC)
    \\ IMP_RES_TAC cEval_SING \\ fs []
    \\ IMP_RES_TAC bEval_SING \\ fs [] \\ SRW_TAC [] []
    \\ qexists_tac `ck` >> rw []
    \\ Q.EXISTS_TAC `f2` \\ fs [])
  THEN1 (* Handle *)
   (rw [] >>
    fs [compile_def,cEval_def,LET_THM]
    \\ `?c3 aux3. compile [x1] aux1 = ([c3],aux3)` by METIS_TAC [PAIR,compile_SING]
    \\ `?c4 aux4. compile [x2] aux3 = ([c4],aux4)` by METIS_TAC [PAIR,compile_SING]
    \\ fs [LET_DEF] \\ SRW_TAC [] [] \\ fs [bEval_def]
    \\ `?p. evaluate ([x1],env,s1) = p` by fs [] \\ PairCases_on `p` \\ fs []
    \\ SRW_TAC [] [] \\ IMP_RES_TAC compile_IMP_code_installed
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`aux1`,`t1`])
    \\ fs []
    \\ disch_then (MP_TAC o Q.SPECL [`env''`,`f1`]) \\ fs []
    \\ discharge_hyps >- ( spose_not_then strip_assume_tac >> fs[] )
    \\ REVERSE (Cases_on `p0`) \\ fs [] \\ SRW_TAC [] []
    \\ TRY (qexists_tac `ck` >> rw [] >> first_assum(match_exists_tac o concl) >> simp[] >> NO_TAC)
    \\ REVERSE (Cases_on `e`) \\ fs [] \\ SRW_TAC [] []
    \\ TRY (qexists_tac `ck` >> rw [] >> first_assum(match_exists_tac o concl) >> simp[] >> NO_TAC)
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`aux3`]) \\ fs []
    \\ disch_then (MP_TAC o Q.SPECL [`t2`,`v'::env''`,`f2`]) \\ fs []
    \\ IMP_RES_TAC evaluate_code \\ fs []
    \\ discharge_hyps >-
      (fs [env_rel_def] \\ IMP_RES_TAC env_rel_SUBMAP \\ fs [])
    \\ REPEAT STRIP_TAC \\ fs []
    \\ qexists_tac `ck + ck'`
    \\ rw []
    \\ imp_res_tac evaluate_add_clock
    \\ fsrw_tac[ARITH_ss][inc_clock_def]
    \\ Q.EXISTS_TAC `f2'` \\ fs []
    \\ IMP_RES_TAC SUBMAP_TRANS \\ fs [])
  THEN1 (* Op *)
   (rw [] >>
    fs [cEval_def,compile_def] \\ SRW_TAC [] [bEval_def]
    \\ `?p. cEval (xs,env,s) = p` by fs [] \\ PairCases_on `p` \\ fs []
    \\ `?cc. compile xs aux1 = cc` by fs [] \\ PairCases_on `cc` \\ fs []
    \\ fs [LET_DEF,PULL_FORALL] \\ SRW_TAC [] []
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`aux1`]) \\ fs []
    \\ IMP_RES_TAC compile_IMP_code_installed \\ REPEAT STRIP_TAC
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`t1`,`env''`,`f1`])
    \\ IMP_RES_TAC compile_SING \\ fs [] \\ SRW_TAC [] []
    \\ fs [bEval_def]
    \\ REVERSE (Cases_on `p0`) \\ fs [] \\ SRW_TAC [] []
    \\ TRY (fs [res_rel_cases] \\ qexists_tac `ck` >> rw [] \\ Q.EXISTS_TAC `f2` \\ fs [] \\ NO_TAC)
    \\ fs [res_rel_Result1] \\ SRW_TAC [] []
    \\ Cases_on `cEvalOp op (REVERSE a) p1` \\ fs []
    \\ Cases_on `x` \\ fs [] \\ SRW_TAC [] []
    \\ qexists_tac `ck` >>
    rw []
    \\ Cases_on `op = Ref` \\ fs []
    THEN1
     (fs [cEvalOp_def,LET_DEF] \\ SRW_TAC [] [res_rel_Result1]
      \\ fs [PULL_EXISTS]
      \\ Q.ABBREV_TAC `pp = LEAST ptr. ptr NOTIN FDOM p1.refs`
      \\ Q.ABBREV_TAC `qq = LEAST ptr. ptr NOTIN FDOM t2.refs`
      \\ fs [bEvalOp_def,LET_DEF]
      \\ Q.EXISTS_TAC `f2 |+ (pp,qq)` \\ fs []
      \\ `~(pp IN FDOM p1.refs)` by
           (UNABBREV_ALL_TAC \\ fs [LEAST_NO_IN_FDOM] \\ NO_TAC)
      \\ `~(qq IN FDOM t2.refs)` by
           (UNABBREV_ALL_TAC \\ fs [LEAST_NO_IN_FDOM] \\ NO_TAC)
      \\ `~(pp IN FDOM f2)` by fs [state_rel_def]
      \\ `~(qq IN FRANGE f2)` by
        (REPEAT STRIP_TAC \\ fs [state_rel_def,SUBSET_DEF] \\ RES_TAC \\ NO_TAC)
      \\ `FRANGE (f2 \\ pp) = FRANGE f2` by ALL_TAC THEN1
       (fs [FRANGE_DEF,finite_mapTheory.DOMSUB_FAPPLY_THM,EXTENSION]
        \\ METIS_TAC []) \\ fs []
      \\ REPEAT STRIP_TAC
      THEN1 (fs [val_rel_cases,FLOOKUP_UPDATE])
      THEN1
       (fs [state_rel_def,FLOOKUP_UPDATE]
        \\ REPEAT STRIP_TAC THEN1
         (Q.PAT_ASSUM `LIST_REL ppp qqq rrr` MP_TAC
          \\ MATCH_MP_TAC listTheory.LIST_REL_mono
          \\ REPEAT STRIP_TAC
          \\ MATCH_MP_TAC opt_val_rel_NEW_REF \\ fs []
          \\ MATCH_MP_TAC opt_val_rel_NEW_F \\ fs [])
        THEN1
         (Q.PAT_ASSUM `INJ ($' f2) (FDOM f2) (FRANGE f2)` MP_TAC
          \\ REPEAT (Q.PAT_ASSUM `INJ xx yy zz` (K ALL_TAC))
          \\ fs [INJ_DEF,FAPPLY_FUPDATE_THM,FRANGE_DEF]
          \\ REPEAT STRIP_TAC \\ METIS_TAC [])
        \\ Cases_on `n = pp` \\ fs [] THEN1
         (SRW_TAC [] [ref_rel_cases] >>
          imp_res_tac EVERY2_REVERSE
          \\ Q.PAT_ASSUM `LIST_REL (val_rel f2 t2.refs t2.code) (REVERSE a) (REVERSE ys)` MP_TAC
          \\ MATCH_MP_TAC listTheory.LIST_REL_mono
          \\ REPEAT STRIP_TAC
          \\ MATCH_MP_TAC val_rel_NEW_REF \\ fs []
          \\ MATCH_MP_TAC val_rel_NEW_F \\ fs [])
        \\ RES_TAC \\ fs []
        \\ `qq <> m` by (REPEAT STRIP_TAC \\ fs [FLOOKUP_DEF] \\ SRW_TAC [] [])
        \\ fs [ref_rel_cases]
        \\ Q.PAT_ASSUM `LIST_REL (val_rel f2 t2.refs t2.code) xs' ys'` MP_TAC
        \\ MATCH_MP_TAC listTheory.LIST_REL_mono
        \\ REPEAT STRIP_TAC
        \\ MATCH_MP_TAC val_rel_NEW_REF \\ fs []
        \\ MATCH_MP_TAC val_rel_NEW_F \\ fs [])
      THEN1
       (fs [SUBMAP_DEF,FAPPLY_FUPDATE_THM] \\ SRW_TAC [] [] \\ METIS_TAC [])
      \\ MATCH_MP_TAC SUBMAP_TRANS
      \\ Q.EXISTS_TAC `FDIFF t2.refs f2` \\ fs []
      \\ fs [SUBMAP_DEF,FDOM_FDIFF]
      \\ REPEAT STRIP_TAC
      \\ fs [FDIFF_def,DRESTRICT_DEF]
      \\ SRW_TAC [] [] \\ fs [state_rel_def,SUBSET_DEF])
    \\ Cases_on `op = Update` \\ fs [] THEN1
     (fs [cEvalOp_def,bEvalOp_def]
      \\ Cases_on `REVERSE a` \\ fs []
      \\ Cases_on `t` \\ fs []
      \\ Cases_on `t'` \\ fs []
      \\ Cases_on `t` \\ fs []
      \\ Cases_on `h` \\ fs []
      \\ Cases_on `h'` \\ fs []
      \\ Cases_on `FLOOKUP p1.refs n` \\ fs []
      \\ Cases_on `x` \\ fs [] \\ SRW_TAC [] []
      \\ imp_res_tac EVERY2_REVERSE >>
      rfs [] >>
      rw []
      \\ fs [val_rel_SIMP] \\ SRW_TAC [] []
      \\ `?y m.
            FLOOKUP f2 n = SOME m /\ FLOOKUP t2.refs m = SOME y /\
            ref_rel f2 t2.refs t2.code (ValueArray l) y` by
              METIS_TAC [state_rel_def]
      \\ fs [] \\ SRW_TAC [] []
      \\ fs [ref_rel_cases] \\ SRW_TAC [] []
      \\ Q.EXISTS_TAC `f2` \\ fs [res_rel_cases] \\ REPEAT STRIP_TAC
      \\ IMP_RES_TAC EVERY2_LENGTH \\ fs []
      THEN1
       (MATCH_MP_TAC val_rel_UPDATE_REF \\ fs []
        \\ fs [FLOOKUP_DEF,FRANGE_DEF] \\ METIS_TAC [])
      THEN1
       (fs [state_rel_def,FLOOKUP_UPDATE] \\ REPEAT STRIP_TAC
        THEN1
         (Q.PAT_ASSUM `LIST_REL tt yy t2.globals` MP_TAC
          \\ MATCH_MP_TAC listTheory.LIST_REL_mono
          \\ REPEAT STRIP_TAC
          \\ MATCH_MP_TAC opt_val_rel_UPDATE_REF \\ fs []
          \\ fs [FLOOKUP_DEF,FRANGE_DEF] \\ METIS_TAC [])
        THEN1 (fs [EXTENSION,FLOOKUP_DEF] \\ METIS_TAC [])
        THEN1
         (`m IN FRANGE f2` by (fs [FLOOKUP_DEF,FRANGE_DEF] \\ METIS_TAC [])
          \\ fs [SUBSET_DEF] \\ METIS_TAC [])
        \\ SRW_TAC [] [] \\ Cases_on `n' = n` \\ fs [] \\ SRW_TAC [] []
        THEN1
         (fs [ref_rel_cases]
          \\ MATCH_MP_TAC EVERY2_LUPDATE_same
          \\ REPEAT STRIP_TAC THEN1
           (MATCH_MP_TAC val_rel_UPDATE_REF \\ fs []
            \\ fs [FLOOKUP_DEF,FRANGE_DEF] \\ METIS_TAC [])
          \\ Q.PAT_ASSUM `LIST_REL (val_rel f2 t2.refs t2.code) l ys'` MP_TAC
          \\ MATCH_MP_TAC listTheory.LIST_REL_mono
          \\ REPEAT STRIP_TAC
          \\ MATCH_MP_TAC val_rel_UPDATE_REF \\ fs []
          \\ fs [FLOOKUP_DEF,FRANGE_DEF] \\ METIS_TAC [])
        \\ RES_TAC \\ fs []
        \\ `m' <> m''` by
         (Q.PAT_ASSUM `INJ ($' f2) (FDOM p1.refs) (FRANGE f2)` MP_TAC
          \\ SIMP_TAC std_ss [INJ_DEF,FRANGE_DEF] \\ fs [FLOOKUP_DEF]
          \\ METIS_TAC [])
        \\ fs [] \\ SRW_TAC [] [] \\ fs [ref_rel_cases] \\ SRW_TAC [] []
        \\ Q.PAT_ASSUM `LIST_REL pp xs' ys''` MP_TAC
        \\ MATCH_MP_TAC listTheory.LIST_REL_mono
        \\ REPEAT STRIP_TAC
        \\ MATCH_MP_TAC val_rel_UPDATE_REF \\ fs []
        \\ fs [FLOOKUP_DEF,FRANGE_DEF] \\ METIS_TAC [])
      \\ `m IN FRANGE f2` by (fs [FLOOKUP_DEF,FRANGE_DEF] \\ METIS_TAC [])
      \\ fs [SUBMAP_DEF,FDIFF_def,DRESTRICT_DEF,FAPPLY_FUPDATE_THM, add_args_def])
    \\ Cases_on `op = RefArray` \\ fs[] THEN1 cheat
    \\ Cases_on `op = RefByte` \\ fs[] THEN1 cheat
    \\ Cases_on `op = UpdateByte` \\ fs[] THEN1 cheat
    \\ imp_res_tac cEvalOp_const
    \\ first_x_assum(mp_tac o MATCH_MP (GEN_ALL(REWRITE_RULE[GSYM AND_IMP_INTRO]cEvalOp_correct)))
    \\ first_x_assum(fn th => disch_then (mp_tac o C MATCH_MP th))
    \\ imp_res_tac EVERY2_REVERSE 
    \\ first_x_assum(fn th => disch_then (mp_tac o C MATCH_MP th)) \\ rw[] \\ rw[]
    \\ Q.EXISTS_TAC `f2` \\ fs [res_rel_Result] >>
    metis_tac [bEvalOp_const])
  THEN1 (* Fn *)
   (rw [] >>
    fs [cEval_def] \\ BasicProvers.FULL_CASE_TAC
    \\ fs [] \\ SRW_TAC [] []
    \\ fs [compile_def]
    \\ `?c2 aux3. compile [exp] aux1 = (c2,aux3)` by METIS_TAC [PAIR]
    \\ fs [LET_DEF] \\ SRW_TAC [] []
    \\ fs [code_installed_def]
    \\ fs [bEval_def,bvlPropsTheory.evaluate_APPEND,bvlSemTheory.do_app_def,domain_lookup]
    \\ `s.restrict_envs` by fs [state_rel_def]
    \\ fs [clos_env_def]
    \\ IMP_RES_TAC lookup_vars_IMP
    \\ POP_ASSUM (qspec_then `t1 with clock := s.clock` strip_assume_tac)
    \\ imp_res_tac bvlPropsTheory.evaluate_var_reverse
    \\ qexists_tac`0`>>simp[]
    \\ Cases_on `num_args ≤ max_app ∧ num_args ≠ 0`
    \\ fs []
    \\ rw []
    \\ fs [v_rel_cases, cl_rel_cases]
    \\ Q.EXISTS_TAC `f1` \\ fs [] >>
    simp[PULL_EXISTS] >>
    Q.LIST_EXISTS_TAC [`aux1`,`aux3`] \\ fs []
    \\ IMP_RES_TAC compile_SING \\ fs [code_installed_def])
  THEN1 (* Letrec *)
   (rw [] >>
    fs [cEval_def] \\ BasicProvers.FULL_CASE_TAC
    \\ fs [] \\ SRW_TAC [] []
    \\ fs [compile_def]
    \\ `s.restrict_envs` by fs [state_rel_def]
    \\ fs [build_recc_def,clos_env_def]
    \\ Cases_on `lookup_vars names env` \\ fs [] \\ SRW_TAC [] []
    \\ Cases_on `fns` \\ fs []
    THEN1 (rfs [] \\ FIRST_X_ASSUM MATCH_MP_TAC
           \\ Q.LIST_EXISTS_TAC [`aux1`] \\ fs [])
    \\ Cases_on `t` \\ fs [] \\ rfs []
    THEN1 (* special case for singly-recursive closure *)
     (`?num_args body. h = (num_args, body)` by metis_tac [pair_CASES] >>
      rw [] >>
      fs [] >>
      `?c2 aux3. compile [body] aux1 = ([c2],aux3)` by
              METIS_TAC [PAIR,compile_SING]
      \\ fs[LET_THM]
      \\ first_assum(split_applied_pair_tac o lhs o concl)
      \\ fs [] \\ SRW_TAC [] []
      \\ simp[bEval_def, bvlPropsTheory.evaluate_APPEND, bvlSemTheory.do_app_def]
      \\ IMP_RES_TAC lookup_vars_IMP
      \\ Cases_on `num_args ≤ max_app ∧ num_args ≠ 0` >>
      fs [] >> fs [] >>
      first_x_assum(qspec_then`t1 with clock := s.clock` STRIP_ASSUME_TAC) >>
      `env_rel f1 t1.refs t1.code (Recclosure loc [] x' [(num_args,body)] 0::env) (Block closure_tag (CodePtr (loc + num_stubs)::Number (&(num_args − 1))::ys)::env'')`
               by (rw [env_rel_def] >>
                   rw [v_rel_cases, EXISTS_OR_THM] >>
                   first_assum(match_exists_tac o concl) >>
                   rw [cl_rel_cases, PULL_EXISTS]
                   \\ IMP_RES_TAC compile_IMP_code_installed
                   \\ fs [code_installed_def] >>
                   simp [GSYM ADD1, GENLIST] >>
                   metis_tac []) >>
      simp [REVERSE_APPEND] >>
      rw [] >>
      first_x_assum (fn th => first_assum (assume_tac o MATCH_MP (SIMP_RULE (srw_ss()) [GSYM AND_IMP_INTRO] th))) >>
      rpt (pop_assum (fn th => first_assum (strip_assume_tac o MATCH_MP th))) >>
      fs[code_installed_def] >>
      imp_res_tac evaluate_var_reverse >>
      fs [domain_lookup] >>
      imp_res_tac evaluate_add_clock >>
      fsrw_tac[ARITH_ss] [inc_clock_def]
      \\ qmatch_assum_abbrev_tac`compile [exp] auxx = zz`
      \\ qspecl_then[`[exp]`,`auxx`]strip_assume_tac compile_acc
      \\ rfs[Abbr`zz`,LET_THM] >> fs[Abbr`auxx`]
      \\ rw [REVERSE_APPEND]
      \\ imp_res_tac compile_SING \\ fs[] \\ rw[]
      \\ qexists_tac`ck`>>simp[]
      \\ Q.LIST_EXISTS_TAC [`f2`] \\ fs [])
    (* general case for mutually recursive closures *)
    \\ `0 < LENGTH (h::h'::t') /\ 1 < LENGTH (h::h'::t')` by (fs [] \\ DECIDE_TAC)
    \\ `SUC (SUC (LENGTH t')) = LENGTH (h::h'::t')` by fs []
    \\ Q.ABBREV_TAC `exps = h::h'::t'` \\ fs []
    \\ `SND h::SND h'::MAP SND t' = MAP SND exps` by rw [Abbr `exps`]
    \\ `FST h::FST h'::MAP FST t' = MAP FST exps` by rw [Abbr `exps`]
    \\ fs [if_expand]
    \\ rw []
    \\ fs []
    \\ `EVERY (λ(num_args,e). num_args ≤ max_app ∧ num_args ≠ 0) exps` by rw [Abbr `exps`]
    \\ pop_assum mp_tac
    \\ NTAC 4 (POP_ASSUM (K ALL_TAC)) \\ fs [LET_DEF]
    \\ DISCH_TAC
    \\ `?c7 aux7. compile (MAP SND exps) aux1 = (c7,aux7)` by METIS_TAC [PAIR]
    \\ `?n4 aux5. build_aux (loc + num_stubs)
           (MAP2 (code_for_recc_case (LENGTH exps + LENGTH names)) (MAP FST exps) c7)
           aux7 = (n4,aux5)` by METIS_TAC [PAIR]
    \\ `?c8 aux8. compile [exp] aux5 = (c8,aux8)` by METIS_TAC [PAIR]
    \\ fs [] \\ SRW_TAC [] []
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`aux5`]) \\ fs []
    \\ REPEAT STRIP_TAC
    \\ fs [build_recc_lets_def]
    \\ fs [bvlSemTheory.do_app_def,bEval_def,LET_DEF]
    \\ fs [bvlPropsTheory.evaluate_APPEND,evaluate_MAP_Const, REVERSE_APPEND]
    \\ IMP_RES_TAC lookup_vars_IMP2
    \\ `!t1. evaluate (REVERSE (MAP Var names), env'', t1) = (Rval (REVERSE ys), t1)`
        by metis_tac [evaluate_var_reverse, REVERSE_REVERSE]
    \\ fs []
    \\ rw [GSYM MAP_REVERSE]
    \\ rw [evaluate_MAP_Const]
    \\ Q.ABBREV_TAC `rr = LEAST ptr. ptr NOTIN FDOM t1.refs`
    \\ fs [recc_Let0_def]
    \\ `loc + num_stubs + (LENGTH exps - 1) IN domain t1.code` by
     (IMP_RES_TAC compile_IMP_code_installed
      \\ IMP_RES_TAC compile_LENGTH
      \\ fs [domain_lookup,code_installed_def]
      \\ IMP_RES_TAC build_aux_MEM \\ fs []
      \\ rfs [LENGTH_MAP2]
      \\ `LENGTH exps - 1 < LENGTH exps` by DECIDE_TAC
      \\ RES_TAC
      \\ fs [code_installed_def,EVERY_MEM] \\ fs []
      \\ RES_TAC \\ fs [] \\ PairCases_on `d` \\ fs [])
    \\ fs [bEval_def,bvlSemTheory.do_app_def,DECIDE ``1 < m + 1 + SUC n``,
           DECIDE ``0 < 1 + SUC n``, DECIDE ``1 < n + (1 + SUC m)``,
           DECIDE ``m < 1 + (m + n):num``]
    \\ `0 < LENGTH exps + LENGTH ys` by DECIDE_TAC
    \\ ASM_SIMP_TAC (srw_ss()) [FLOOKUP_DEF, DECIDE ``n < 1 + (n + m):num``]
    \\ `exps <> []` by (fs [GSYM LENGTH_NIL] \\ DECIDE_TAC)
    \\ `?ll x. exps = SNOC x ll` by METIS_TAC [SNOC_CASES] \\ fs []
    \\ simp [REVERSE_APPEND, MAP_REVERSE, LENGTH_MAP]
    \\ `LENGTH ll = LENGTH ((MAP (K (Number 0)) (MAP FST ll)) : bvlSem$v list)`
         by fs [LENGTH_MAP]
    \\ POP_ASSUM (fn th => REWRITE_TAC [th])
    \\ rw [lupdate_append2]
    \\ `EVERY (\n. loc + num_stubs + n IN domain t1.code) (GENLIST I (LENGTH ll))` by
     (fs [EVERY_GENLIST]
      \\ IMP_RES_TAC compile_IMP_code_installed
      \\ IMP_RES_TAC compile_LENGTH
      \\ fs [domain_lookup,code_installed_def]
      \\ IMP_RES_TAC build_aux_MEM \\ fs []
      \\ rfs [LENGTH_MAP2]
      \\ REPEAT STRIP_TAC
      \\ `i < LENGTH ll + 1` by ALL_TAC THEN1
       (IMP_RES_TAC compile_LENGTH \\ fs [LENGTH_APPEND]
        \\ DECIDE_TAC)
      \\ RES_TAC
      \\ fs [code_installed_def,EVERY_MEM] \\ fs []
      \\ RES_TAC \\ fs [] \\ PairCases_on `d` \\ fs [])
    \\ fs [hd_append, tl_append]
    \\ simp [SIMP_RULE(srw_ss())[]evaluate_recc_Lets]
    \\ Q.PAT_ABBREV_TAC `t1_refs  = t1 with <| refs := t1.refs |+ xxx; clock := yyy |>`
    \\ `[HD c8] = c8` by (IMP_RES_TAC compile_SING \\ fs []) \\ fs []
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`t1_refs`,
       `MAP2 (\n args. Block closure_tag [CodePtr (loc + num_stubs + n); Number &(args-1); RefPtr rr])
          (GENLIST I (LENGTH (ll:(num#closLang$exp) list) + 1)) (MAP FST ll ++ [FST (x:(num#closLang$exp))]) ++ env''`,`f1`])
    \\ `~(rr IN FDOM t1.refs)` by ALL_TAC THEN1
     (UNABBREV_ALL_TAC
      \\ SIMP_TAC std_ss [FDIFF_def,SUBMAP_DEF]
      \\ fs [DRESTRICT_DEF,FAPPLY_FUPDATE_THM]
      \\ REPEAT STRIP_TAC \\ SRW_TAC [] []
      \\ ASSUME_TAC (EXISTS_NOT_IN_refs |>
           SIMP_RULE std_ss [whileTheory.LEAST_EXISTS]) \\ fs [])
    \\ MATCH_MP_TAC IMP_IMP \\ reverse STRIP_TAC
    >- (REPEAT STRIP_TAC
        \\ qexists_tac `ck'`
        \\ full_simp_tac (srw_ss()++ARITH_ss) [Abbr `t1_refs`]
        \\ rw []
        \\ Q.EXISTS_TAC `f2` \\ IMP_RES_TAC SUBMAP_TRANS
        \\ ASM_SIMP_TAC std_ss []
        \\ FIRST_X_ASSUM MATCH_MP_TAC
        \\ UNABBREV_ALL_TAC
        \\ SIMP_TAC std_ss [FDIFF_def,SUBMAP_DEF]
        \\ fs [DRESTRICT_DEF,FAPPLY_FUPDATE_THM]
        \\ REPEAT STRIP_TAC \\ SRW_TAC [] []
        \\ ASSUME_TAC (EXISTS_NOT_IN_refs |>
             SIMP_RULE std_ss [whileTheory.LEAST_EXISTS]) \\ fs [])
    THEN1
     (`t1_refs.code = t1.code` by fs [Abbr`t1_refs`] \\ fs []
      \\ REVERSE (REPEAT STRIP_TAC) THEN1
       (fs [state_rel_def,Abbr`t1_refs`] \\ STRIP_TAC THEN1
         (Q.PAT_ASSUM `LIST_REL ppp s.globals t1.globals` MP_TAC
          \\ MATCH_MP_TAC listTheory.LIST_REL_mono
          \\ METIS_TAC [OPTREL_v_rel_NEW_REF])
        \\ STRIP_TAC THEN1 fs [SUBSET_DEF]
        \\ REPEAT STRIP_TAC \\ RES_TAC \\ fs [FLOOKUP_UPDATE]
        \\ `m <> rr` by (REPEAT STRIP_TAC \\ fs [FLOOKUP_DEF]) \\ fs []
        \\ Cases_on`x''`>>fs []
        \\ Q.PAT_ASSUM `LIST_REL ppp xs ys'` MP_TAC
        \\ MATCH_MP_TAC listTheory.LIST_REL_mono
        \\ IMP_RES_TAC v_rel_NEW_REF \\ fs [])
      \\ MATCH_MP_TAC env_rel_APPEND
      \\ REVERSE STRIP_TAC THEN1
       (UNABBREV_ALL_TAC \\ fs []
        \\ MATCH_MP_TAC (env_rel_NEW_REF |> GEN_ALL) \\ fs [])
      \\ rw [LIST_REL_EL_EQN, LENGTH_GENLIST, LENGTH_MAP2, el_map2]
      \\ rw [v_rel_cases, cl_rel_cases]
      \\ fs []
      \\ srw_tac [boolSimps.DNF_ss] []
      \\ disj2_tac
      \\ qexists_tac `ys`
      \\ qabbrev_tac `exps = ll++[x]`
      \\ `LENGTH ll + 1 = LENGTH exps` by fs [Abbr `exps`]
      \\ Q.EXISTS_TAC `ZIP (exps,GENLIST (\i.loc+num_stubs+i) (LENGTH exps))`
      \\ fs [LENGTH_ZIP, EL_MAP, LENGTH_MAP, EL_ZIP, MAP_ZIP]
      \\ `?num e. EL n exps = (num, e)` by metis_tac [pair_CASES]
      \\ `1 < LENGTH exps` by (fs [] \\ DECIDE_TAC)
      \\ fs [Abbr `t1_refs`,FLOOKUP_UPDATE]
      \\ `MAP FST ll ++ [FST x] = MAP FST exps` by rw [Abbr `exps`]
      \\ simp [EL_MAP]
      \\ rw []
      THEN1
       (Q.PAT_ASSUM `LIST_REL (v_rel f1 t1.refs t1.code) x' ys` MP_TAC
        \\ MATCH_MP_TAC listTheory.LIST_REL_mono
        \\ METIS_TAC [v_rel_NEW_REF])
      THEN1
       (fs [state_rel_def, SUBSET_DEF] >> metis_tac [])
      THEN1
       (rpt (pop_assum kall_tac)
        \\ Q.SPEC_TAC (`exps`, `exps`)
        \\ recInduct SNOC_INDUCT
        \\ rw [GENLIST, GSYM ADD1]
        \\ rw_tac std_ss [GSYM SNOC_APPEND, map2_snoc, LENGTH_GENLIST, LENGTH_MAP]
        \\ rw [GSYM ZIP_APPEND]
        \\ PairCases_on `x`
        \\ simp [])
      \\ fs [closure_code_installed_def]
      \\ MATCH_MP_TAC EVERY_ZIP_GENLIST \\ fs [AC ADD_ASSOC ADD_COMM]
      \\ REPEAT STRIP_TAC
      \\ IMP_RES_TAC compile_IMP_code_installed
      \\ `EVERY (λ(num_args,e). num_args ≤ max_app ∧ num_args ≠ 0) exps` by fs [Abbr `exps`]
      \\ fs [EVERY_EL]
      \\ res_tac
      \\ `?num e. EL i exps = (num, e)` by metis_tac [pair_CASES]
      \\ fs []
      \\ MATCH_MP_TAC (compile_LIST_IMP_compile_EL |> SPEC_ALL)
      \\ fs [Abbr`exps`])
   )
  THEN1 (* App *)
   (rw [] >>
    fs [cEval_def, compile_def]
    \\ `?res6 s6. evaluate (args,env,s) = (res6,s6)` by METIS_TAC [PAIR]
    \\ `?res5 s5. evaluate ([x1],env,s6) = (res5,s5)` by METIS_TAC [PAIR]
    \\ `?c7 aux7. compile [x1] aux1 = ([c7],aux7)` by
          METIS_TAC [PAIR,compile_SING]
    \\ `?c8 aux8. compile args aux7 = (c8,aux8)` by
          METIS_TAC [PAIR,compile_SING]
    \\ fs [LET_DEF] \\ SRW_TAC [] []
    \\ Cases_on `LENGTH args > 0` >> fs []
    \\ REVERSE (Cases_on `res6`) \\ fs []
    >- (res_tac >> rw[] >> fs[] >> rw[] >>
        imp_res_tac evaluate_app_helper >> fs [] >>
        metis_tac [])
    \\ `code_installed aux1 t1.code` by IMP_RES_TAC compile_IMP_code_installed
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`aux7`,`t1`,`env''`,`f1`]) \\ fs []
    \\ REPEAT STRIP_TAC \\ fs []
    \\ `code_installed aux7 t1.code` by IMP_RES_TAC compile_IMP_code_installed
    \\ `t2.code = t1.code` by (IMP_RES_TAC evaluate_code >> fs [])
    \\ `code_installed aux7 t2.code` by metis_tac []
    \\ `env_rel f2 t2.refs t2.code env env''` by metis_tac [env_rel_SUBMAP]
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`aux1`,`t2`,`env''`,`f2`]) \\ fs []
    \\ discharge_hyps >- ( spose_not_then strip_assume_tac >> fs[] )
    \\ disch_then (strip_assume_tac o SIMP_RULE (srw_ss()) [GSYM RIGHT_EXISTS_IMP_THM]) >>
    `evaluate (c8,env'',t1 with clock := s.clock + ck + ck') = (Rval v',inc_clock ck' t2)`
                by (imp_res_tac evaluate_add_clock >>
                    fs [inc_clock_def])
    \\ REVERSE (Cases_on `res5`) \\ fs [inc_clock_def]
    >- (rw[] >>
        imp_res_tac evaluate_app_helper2 >>
        rfs [] >>
        metis_tac [SUBMAP_TRANS, ADD_ASSOC])
    \\ imp_res_tac cEval_SING
    \\ fs [] \\ rw []
    \\ imp_res_tac bvlPropsTheory.evaluate_IMP_LENGTH
    \\ imp_res_tac compile_LENGTH
    \\ `t2'.code = t1.code` by (imp_res_tac evaluate_code >> fs [])
    \\ `LIST_REL (v_rel f2' t2'.refs t2'.code) a v'`
              by metis_tac [LIST_REL_mono, v_rel_SUBMAP]
    \\ res_tac
    \\ pop_assum (qspec_then `env''` strip_assume_tac)
    \\ `LENGTH v' ≠ 0 ∧ 0 < LENGTH v' ∧ LENGTH args = LENGTH v'` by decide_tac
    \\ fs []
    \\ qexists_tac `ck+ck'+ck''` >>
    rw [] >>
    `evaluate (c8,env'',t1 with clock := ck + ck' + ck'' + s.clock) = (Rval v',inc_clock (ck'+ck'') t2)`
                by (imp_res_tac evaluate_add_clock >>
                    fsrw_tac[ARITH_ss][inc_clock_def]) >>
    `evaluate ([c7],env'',inc_clock (ck' + ck'') t2) = (Rval [y],inc_clock ck'' t2')`
                by (imp_res_tac evaluate_add_clock >>
                    fsrw_tac[ARITH_ss][inc_clock_def])
    \\ Cases_on `loc_opt`
    \\ simp [bEval_def, bvlPropsTheory.evaluate_APPEND]
    \\ fs [] >> rw [ADD_ASSOC] >> rw [] >- metis_tac [SUBMAP_TRANS, inc_clock_def]
    \\ rfs []
    \\ REVERSE (Cases_on `find_code (SOME (x + num_stubs)) (v' ++ [y]) t1.code`)
    \\ fs []
    >- (Cases_on `x'` >>
        rw [inc_clock_def] >>
        fs [] >>
        rw [] >>
        fs [dec_clock_def] >>
        rw [] >>
        metis_tac [SUBMAP_TRANS])
    \\ rw []
    \\ fs [])
  THEN1 (* Tick *)
   (rw [] >>
    fs [compile_def]
    \\ `?p. evaluate ([x],env,s) = p` by fs [] \\ PairCases_on `p` \\ fs []
    \\ `?cc. compile [x] aux1 = cc` by fs [] \\ PairCases_on `cc` \\ fs []
    \\ fs [LET_DEF] \\ SRW_TAC [] []
    \\ IMP_RES_TAC compile_SING \\ SRW_TAC [] [] \\ fs [bEval_def]
    \\ Cases_on `s.clock = 0` \\ fs [] THEN1
     (fs [cEval_def] \\ SRW_TAC [] []
      \\ qexists_tac `0`
      \\ rw []
      \\ Q.EXISTS_TAC `f1` \\ fs [SUBMAP_REFL])
    \\ fs [cEval_def]
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`aux1`]) \\ fs []
    \\ REPEAT STRIP_TAC
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`dec_clock 1 t1`,`env''`,`f1`])
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
      (fs [bvlSemTheory.dec_clock_def,closSemTheory.dec_clock_def,state_rel_def])
    \\ REPEAT STRIP_TAC \\ fs []
    \\ qexists_tac `ck`
    \\ `s.clock − 1 + ck = s.clock + ck - 1` by simp []
    \\ fs [bvlSemTheory.dec_clock_def, closSemTheory.dec_clock_def]
    \\ Q.EXISTS_TAC `f2` \\ fs [bvlSemTheory.dec_clock_def])
  THEN1 (* Call *)
   (rw [] >>
    fs [compile_def,cEval_def]
    \\ `?c3 aux3. compile xs aux1 = (c3,aux3)` by METIS_TAC [PAIR]
    \\ fs [LET_DEF] \\ SRW_TAC [] [] \\ fs [bEval_def]
    \\ `?p. evaluate (xs,env,s1) = p` by fs [] \\ PairCases_on `p` \\ fs []
    \\ SRW_TAC [] [] \\ IMP_RES_TAC compile_IMP_code_installed
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`aux1`,`t1`])
    \\ fs [] \\ REPEAT STRIP_TAC
    \\ POP_ASSUM (MP_TAC o Q.SPECL [`env''`,`f1`]) \\ fs []
    \\ REVERSE (Cases_on `p0`) \\ fs [] \\ SRW_TAC [] []
    \\ TRY (fs [] \\ qexists_tac `ck` >> rw [] >> Q.EXISTS_TAC `f2` \\ fs [] \\ NO_TAC)
    \\ fs [closSemTheory.find_code_def,bvlSemTheory.find_code_def]
    \\ Cases_on `FLOOKUP p1.code dest` \\ fs []
    \\ Cases_on `x` \\ fs []
    \\ Cases_on `q = LENGTH a` \\ fs []
    \\ `?aux1 c2 aux2.
          compile [r] aux1 = ([c2],aux2) /\
          lookup (dest + num_stubs) t2.code = SOME (LENGTH a,c2) /\
          code_installed aux2 t2.code` by METIS_TAC [state_rel_def]
    \\ IMP_RES_TAC EVERY2_LENGTH \\ fs []
    \\ Cases_on `t2.clock = 0` \\ fs []
    THEN1 (qexists_tac `ck` >> SRW_TAC [] [] \\ Q.EXISTS_TAC `f2` >> fs [])
    \\ fs [] \\ rfs [] \\ fs []
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`aux1'`]) \\ fs []
    \\ REPEAT STRIP_TAC
    \\ POP_ASSUM (MP_TAC o Q.SPECL [`t2`,`v'`,`f2`]) \\ fs []
    \\ IMP_RES_TAC evaluate_code \\ fs []
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
     (fs [closSemTheory.dec_clock_def,state_rel_def,bvlSemTheory.dec_clock_def]
      \\ IMP_RES_TAC list_rel_IMP_env_rel \\ METIS_TAC [APPEND_NIL])
    \\ REPEAT STRIP_TAC \\ fs []
    \\ qexists_tac `ck + ck'` >>
    rw [] >>
    `evaluate (c3,env'',t1 with clock := s1.clock + (ck + ck')) = (Rval v',inc_clock ck' t2)`
           by (imp_res_tac evaluate_add_clock >>
               fsrw_tac[ARITH_ss] [inc_clock_def])
    \\ rw [inc_clock_def]
    \\ `p1.clock − 1 + ck' = t2.clock + ck' - 1` by simp []
    \\ fs [closSemTheory.dec_clock_def, bvlSemTheory.dec_clock_def]
    \\ Q.EXISTS_TAC `f2'` \\ fs []
    \\ IMP_RES_TAC SUBMAP_TRANS \\ fs [])
  THEN1
   ((* cEvalApp [] *)
    fs [cEval_def] >>
    rw [] >>
    qexists_tac `Rval [func']` >>
    qexists_tac `t1 with clock := s1.clock` >>
    rw [] >>
    metis_tac [SUBMAP_REFL])
  THEN1
   ((* cEvalApp real app *)
    qpat_assum `evaluate_app x0 x1 x2 x3 = x4` mp_tac
    \\ simp [cEval_def]
    \\ qabbrev_tac `args = v41::v42`
    \\ DISCH_TAC
    \\ qabbrev_tac `args' = args''`
    \\ `LENGTH args' ≠ 0` by metis_tac [LIST_REL_LENGTH, LENGTH, DECIDE ``SUC x ≠ 0``]
    \\ fs []
    \\ Cases_on `dest_closure loc_opt func args`
    \\ fs []
    \\ Cases_on `x`
    \\ fs []
    \\ rw []
    >- ((* Partial application *)
        `LENGTH args = LENGTH args' ∧ LENGTH args ≠ 0` by metis_tac [LIST_REL_LENGTH] >>
        imp_res_tac dest_closure_part_app >>
        rw [PULL_EXISTS] >>
        imp_res_tac v_rel_num_rem_args >>
        rw [mk_cl_call_def, bEval_def, bEval_APPEND, bEvalOp_def] >>
        srw_tac [ARITH_ss] [el_append3] >>
        `&n' ≠ &(LENGTH args')` by srw_tac [ARITH_ss] [] >>
        `&n' - 1 ≠ &(LENGTH args' - 1)`
                   by (fs [int_arithTheory.INT_NUM_SUB] >>
                       CCONTR_TAC >>
                       fs [] >>
                       rw [] >>
                       ARITH_TAC) >>
        rw [] >>
        `0 < LENGTH args'` by decide_tac >>
        `evaluate (GENLIST Var (LENGTH args'),
                args' ++ [Block tag (CodePtr ptr::Number (&n'-1)::rest)] ++ env,
                t1 with clock := s1.clock) = (Rval args', t1 with clock := s1.clock)`
                    by metis_tac [evaluate_simple_genlist_vars, APPEND_ASSOC] >>
        qexists_tac `0` >>
        rw [] >>
        `LENGTH args' - 1 < max_app` by decide_tac >>
        `lookup (LENGTH args' - 1) t1.code = SOME (LENGTH args' + 1, generate_generic_app (LENGTH args' - 1))`
               by (fs [state_rel_def] >>
                   decide_tac) >>
        simp [find_code_def] >>
        `SUC (LENGTH v42) = LENGTH args` by metis_tac [LENGTH] >>
        fs [] >>
        rw []
        >- (`s1.clock < LENGTH args'` by decide_tac >>
            fs [] >>
            qexists_tac `f1` >>
            simp [SUBMAP_REFL] >>
            fs [] >>
            fs [closSemTheory.state_component_equality] >>
            `s1 = s2` by rw [closSemTheory.state_component_equality] >>
            metis_tac []) >>
        assume_tac (GEN_ALL (SIMP_RULE (srw_ss()) [GSYM AND_IMP_INTRO] unpack_closure_thm)) >>
        rpt (pop_assum (fn th => first_assum  (strip_assume_tac o MATCH_MP th))) >>
        `lookup (partial_app_fn_location total_args (LENGTH args' + LENGTH prev_args − 1)) t1.code =
             SOME (total_args - (LENGTH args' + LENGTH prev_args-1) + 1, generate_partial_app_closure_fn total_args (LENGTH args' + LENGTH prev_args − 1))`
                 by (fs [state_rel_def] >>
                     first_x_assum match_mp_tac >>
                     rw [] >>
                     decide_tac) >>
        `LENGTH args' + LENGTH prev_args − 1 = LENGTH prev_args + (LENGTH args − 1)` by simp [] >>
        `LENGTH args' < total_args + 1 − LENGTH prev_args` by simp [] >>
        fs [] >>
        qspecl_then [`total_args`, `prev_args`, `dec_clock 1 (t1 with clock := s1.clock)`, `args'`] assume_tac evaluate_generic_app_partial >>
        rfs [domain_lookup] >>
        pop_assum (fn th => first_assum (strip_assume_tac o MATCH_MP th)) >>
        rw []
        >- ((* A TimeOut *)
            full_simp_tac (srw_ss()++ARITH_ss) [dec_clock_def, int_arithTheory.INT_NUM_SUB] >>
            qexists_tac `f1` >>
            rw [SUBMAP_REFL] >>
            fs [state_rel_def])
        >- ((* Result *)
            `~((t1 with clock := s1.clock).clock < LENGTH args')` by (fs [dec_clock_def] >> decide_tac) >>
            fs [] >>
            rw [] >>
            qexists_tac `f1` >>
            REVERSE (rw [])
            >- (rw [bvlSemTheory.dec_clock_def, closSemTheory.dec_clock_def] >>
                metis_tac [arith_helper_lem])
            >- (fs [bvlSemTheory.dec_clock_def, closSemTheory.dec_clock_def] >>
                fs [state_rel_def]) >>
            `args ≠ []` by (Cases_on `args` >> fs []) >>
            fs [v_rel_cases, num_remaining_args_def,closure_tag_neq_1,partial_app_tag_neq_closure_tag] >>
            rw [] >>
            fs [num_remaining_args_def, add_args_def, partial_app_tag_neq_closure_tag]
            >- ((* Wrapping a normal closure *)
                MAP_EVERY qexists_tac [`args`, `func`, `env'`, `fvs`, `total_args + 1`] >>
                fs [] >>
                imp_res_tac cl_rel_get_num_args >>
                rw [SUB_LEFT_SUB, LESS_OR_EQ] >>
                fs [])
            >- ((* Wrapping a partially applied closure *)
                fs [unpack_closure_cases] >>
                rw [] >>
                MAP_EVERY qexists_tac [`args++arg_env`, `cl`, `env'`, `fvs`, `total_args+1`] >>
                fs [partial_app_tag_neq_closure_tag] >>
                imp_res_tac EVERY2_LENGTH >>
                rw [partial_app_tag_neq_closure_tag]
                >- simp [] >>
                metis_tac [arith_helper_lem3, add_args_append, EVERY2_APPEND])))
    >- ((* Enough arguments to do something *)
         `SUC (LENGTH v42) = LENGTH args` by metis_tac [LENGTH] >>
         fs [] >>
         imp_res_tac dest_closure_full_app >>
         assume_tac (SIMP_RULE (srw_ss()) [GSYM AND_IMP_INTRO] v_rel_num_rem_args) >>
         rpt (pop_assum (fn th => first_assum (strip_assume_tac o MATCH_MP th))) >>
         `loc_opt = NONE ∨ ?loc. loc_opt = SOME loc` by metis_tac [option_nchotomy] >>
         fs [check_loc_def] >>
         rw []
         >- ((* App NONE *)
             qabbrev_tac `n = rem_args - 1` >>
             imp_res_tac EVERY2_LENGTH >>
             `lookup (LENGTH args' − 1) t1.code =
                SOME ((LENGTH args' - 1) + 2,generate_generic_app (LENGTH args' − 1))`
                         by (fs [state_rel_def] >>
                             `LENGTH args' - 1 < max_app` by decide_tac >>
                             metis_tac []) >>
             `LENGTH args' - 1 + 2  = LENGTH args' + 1` by decide_tac >>
             fs [] >>
             `&rem_args - 1 = &n ∧ rem_args + 1 = n + 2`
                  by (srw_tac [ARITH_ss] [Abbr `n`,int_arithTheory.INT_NUM_SUB]) >>
             `LENGTH args' − (LENGTH args' − rem_args) = rem_args` by decide_tac >>
             fs [] >>
             Cases_on `s1.clock < rem_args` >>
             fs [] >>
             simp []
             >- ((* Timeout *)
                 qspec_then `t1 with clock := s1.clock` (assume_tac o (SIMP_RULE (srw_ss()) [GSYM AND_IMP_INTRO]))
                   evaluate_mk_cl_call_spec >>
                 rpt (pop_assum (fn x => first_assum (strip_assume_tac o MATCH_MP x))) >>
                 pop_assum mp_tac >>
                 simp [] >>
                 DISCH_TAC >>
                 qexists_tac `0` >>
                 simp [] >>
                 qexists_tac `f1` >>
                 rw []) >>
             `?res' s'. evaluate ([e],l,dec_clock rem_args s1) = (res', s')` by metis_tac [pair_CASES] >>
             fs [] >>
             `res' ≠ Rerr(Rabort Rtype_error)` by (spose_not_then strip_assume_tac >> fs[]) >>
             fs [] >>
             imp_res_tac v_rel_run >>
             `LENGTH args ≠ 0` by decide_tac >>
             fs [int_arithTheory.INT_NUM_SUB, closSemTheory.dec_clock_def] >>
             first_x_assum (fn th => first_assum (assume_tac o MATCH_MP (SIMP_RULE (srw_ss()) [GSYM AND_IMP_INTRO] th))) >>
             rpt (pop_assum (fn th => (first_assum (strip_assume_tac o MATCH_MP th)))) >>
             Cases_on `?func''. res' =  Rval [func'']` >>
             fs [] >>
             rw [] >>
             fs []
             >- ((* The first application succeeds *)
                 `?v'. v_rel f2 t2.refs t2.code func'' v' ∧ res'' = Rval [v']`
                        by (fs [] >> metis_tac []) >>
                 `LIST_REL (v_rel f2 t2.refs t2.code) l0 (TAKE (LENGTH args' − rem_args) args')`
                          by (match_mp_tac list_rel_app >>
                              MAP_EVERY qexists_tac [`args`, `e`, `l`, `func`] >>
                              rw [] >>
                              fs [LIST_REL_EL_EQN] >>
                              rw [] >>
                              match_mp_tac (GEN_ALL v_rel_SUBMAP) >>
                              rw [] >>
                              `t1.code = t2.code`
                                     by (imp_res_tac evaluate_code >>
                                         fs []) >>
                              metis_tac []) >>
                 first_x_assum (fn th => first_assum (assume_tac o MATCH_MP (SIMP_RULE (srw_ss()) [GSYM AND_IMP_INTRO] th))) >>
                 rfs [] >>
                 rpt (pop_assum (fn th => (first_assum (strip_assume_tac o MATCH_MP th)))) >>
                 fs [LENGTH_TAKE] >>
                 Cases_on `(LENGTH args' ≤ rem_args)` >>
                 fs []
                 >- ((* No remaining arguments *)
                     qspec_then `t1 with clock := ck + ck' + s1.clock`
                       (assume_tac o SIMP_RULE (srw_ss()) [GSYM AND_IMP_INTRO])evaluate_mk_cl_call_spec >>
                     rpt (pop_assum (fn x => first_assum (strip_assume_tac o MATCH_MP x))) >>
                     pop_assum mp_tac >>
                     simp [] >>
                     DISCH_TAC >>
                     qexists_tac `ck + ck'` >>
                     rw [] >>
                     `rem_args = LENGTH args' ∧ n + 1 = LENGTH args'` by decide_tac >>
                     fs [ADD_ASSOC] >>
                     first_x_assum (qspec_then `t1 with clock := ck + s1.clock - LENGTH args'` mp_tac) >>
                     simp [inc_clock_def, dec_clock_def] >>
                     `!ck. t1 with <| clock := ck; code := t1.code |> = t1 with clock := ck`
                              by rw [bvlSemTheory.state_component_equality] >>
                     rw [] >>
                     `ck + s1.clock − LENGTH args' = s1.clock − LENGTH args' + ck` by decide_tac >>
                     rw [] >>
                     fs [cEval_def] >>
                     `!ck. t1 with <| clock := ck; refs := t1.refs |> = t1 with clock := ck`
                              by rw [bvlSemTheory.state_component_equality] >>
                     fs [] >> rw[] >>
                     metis_tac [SUBMAP_TRANS])
                 >- ((* Extra arguments *)
                     rw [] >>
                     first_x_assum (qspec_then `SOMEENV` strip_assume_tac) >>
                     qspec_then `t1 with clock := ck + ck' + ck'' + 1 + s1.clock`
                       (assume_tac o SIMP_RULE (srw_ss()) [GSYM AND_IMP_INTRO]) evaluate_mk_cl_call_spec >>
                     rpt (pop_assum (fn x => first_assum (strip_assume_tac o MATCH_MP x))) >>
                     pop_assum mp_tac >>
                     simp [] >>
                     DISCH_TAC >>
                     qexists_tac `ck + ck' + ck'' + 1` >>
                     simp [] >>
                     rw [] >>
                     fs [ADD_ASSOC] >>
                     pop_assum kall_tac >>
                     first_x_assum (qspec_then `t1 with clock := ck + ck'' + s1.clock - rem_args` mp_tac) >>
                     rw [inc_clock_def, dec_clock_def, Abbr `n`] >>
                     `ck + ck'' + s1.clock − rem_args + ck' =
                      ck + ck' + ck'' + s1.clock + 1 − (rem_args − 1 + 2)`
                               by ARITH_TAC  >>
                     `!ck. t1 with <| clock := ck; code := t1.code |> = t1 with clock := ck`
                              by rw [bvlSemTheory.state_component_equality] >>
                     fs [] >>
                     rw [] >>
                     `s1.clock − rem_args + ck + ck'' = ck+ck''+s1.clock-rem_args` by ARITH_TAC >>
                     `evaluate ([body'],newenv',t1 with clock := ck + ck'' + s1.clock - rem_args) =
                         (Rval [v''], inc_clock ck'' t2)`
                               by (imp_res_tac evaluate_add_clock >>
                                   rw [] >>
                                   pop_assum (qspec_then `ck''` mp_tac) >>
                                   fs [inc_clock_def]) >>
                     rw [] >>
                     `LENGTH [Block tag (CodePtr ptr::Number (&(rem_args − 1))::rest)] ≠ 0` by rw [] >>
                     `LENGTH args' − rem_args ≤ LENGTH args'` by ARITH_TAC >>
                     first_x_assum (fn th => strip_assume_tac (MATCH_MP (SIMP_RULE (srw_ss()) [GSYM AND_IMP_INTRO] mk_call_simp2) th)) >>
                     pop_assum (fn th => first_x_assum (strip_assume_tac o MATCH_MP th)) >>
                     fs [] >>
                     `rem_args - 1 + 1 = rem_args` by ARITH_TAC >>
                     rw [inc_clock_def] >>
                     Cases_on `res''''` >>
                     fs [] >>
                     imp_res_tac bEval_SING >>
                     fs [] >>
                     `!ck. t1 with <| clock := ck; refs := t1.refs |> = t1 with clock := ck`
                              by rw [bvlSemTheory.state_component_equality] >>
                     fs [inc_clock_def] >>
                     metis_tac [SUBMAP_TRANS]))
             >- ((* The first application fails *)
                 `res' = res ∧ s' = s2`
                       by (Cases_on `res'` >>
                           fs [] >>
                           Cases_on `a` >>
                           fs [] >>
                           Cases_on `t` >>
                           fs []) >>
                 fs [] >>
                 `!ck. t1 with <| refs := t1.refs; clock := ck; code := t1.code |> = t1 with clock := ck`
                              by rw [bvlSemTheory.state_component_equality] >>
                 first_x_assum (qspec_then `t1 with clock := s1.clock - rem_args + ck` assume_tac) >>
                 rfs [] >>
                 Cases_on `n = LENGTH args' - 1` >>
                 fs []
                 >- (qspec_then `t1 with clock := ck+ck' + s1.clock`
                       (assume_tac o SIMP_RULE (srw_ss()) [GSYM AND_IMP_INTRO]) evaluate_mk_cl_call_spec >>
                     rpt (pop_assum (fn x => first_assum (strip_assume_tac o MATCH_MP x))) >>
                     pop_assum mp_tac >>
                     simp [] >>
                     DISCH_TAC >>
                     qexists_tac `ck+ck'` >>
                     rev_full_simp_tac (srw_ss()++ARITH_ss) [inc_clock_def, dec_clock_def] >>
                     qexists_tac `f2` >>
                     rw [])
                 >- (qspec_then `t1 with clock := ck+ck' +1+ s1.clock`
                       (assume_tac o SIMP_RULE (srw_ss()) [GSYM AND_IMP_INTRO]) evaluate_mk_cl_call_spec >>
                     rpt (pop_assum (fn x => first_assum (strip_assume_tac o MATCH_MP x))) >>
                     pop_assum mp_tac >>
                     simp [] >>
                     DISCH_TAC >>
                     qexists_tac `ck+ck'+1` >>
                     rev_full_simp_tac (srw_ss()++ARITH_ss) [inc_clock_def, dec_clock_def] >>
                     pop_assum kall_tac >>
                     `rem_args = n + 1` by decide_tac >>
                     fs [] >>
                     rw [] >>
                     MAP_EVERY qexists_tac [`res''`, `t2`, `f2`] >>
                     rw [] >>
                     BasicProvers.CASE_TAC >>
                     Cases_on`res`>>fs[] >>
                     imp_res_tac bEval_SING >>
                     fs[] >> rw[])))
         >- ((* App SOME *)
             `rem_args = LENGTH args` by ARITH_TAC >>
             fs [] >>
             rw [find_code_def] >>
             `&LENGTH args - 1 = &(LENGTH args - 1)` by rw [int_arithTheory.INT_NUM_SUB] >>
             fs [] >>
             `t1.code = (t1 with clock := s1.clock - LENGTH args').code` by rw [] >>
             full_simp_tac std_ss [] >>
             strip_assume_tac (SIMP_RULE (srw_ss()) [GSYM AND_IMP_INTRO] (v_rel_run)) >>
             rpt (pop_assum (fn x => first_assum (strip_assume_tac o MATCH_MP x))) >>
             fs [] >>
             rw [] >>
             `ptr = loc + num_stubs`
                     by (fs [v_rel_cases] >>
                         imp_res_tac cl_rel_get_loc >>
                         fs [] >>
                         srw_tac [ARITH_ss] [] >>
                         metis_tac [no_partial_args]) >>
             rw [] >>
             imp_res_tac EVERY2_LENGTH >>
             fs [] >>
             Cases_on `s1.clock < LENGTH args'` >>
             fs []
             >- ((* TimeOut *)
                 qexists_tac `0` >> rw [] >>
                 metis_tac [SUBMAP_REFL]) >>
             `?res' s2. evaluate ([e],l,dec_clock (LENGTH args') s1) = (res',s2)`
                          by metis_tac [pair_CASES]  >>
             fs [] >>
             `l0 = []` by (Cases_on `l0` >> fs []) >>
             rw [] >>
             `res' = res ∧ s2' = s2`
                     by (Cases_on `res'` >>
                         fs [] >>
                         Cases_on `a` >>
                         fs [] >>
                         Cases_on `t` >>
                         fs [cEval_def]) >>
             rw [] >>
             fs [] >>
             `t1.refs = (dec_clock (LENGTH args') t1).refs` by rw [dec_clock_def] >>
             fs [] >>
             rw [] >>
             `LENGTH args' − (LENGTH args' − 1 + 1) = 0` by decide_tac >>
             full_simp_tac bool_ss [] >>
             fs [inc_clock_def, dec_clock_def] >>
             full_simp_tac (srw_ss()++ARITH_ss) [] >>
             first_x_assum (fn x => first_assum (strip_assume_tac o MATCH_MP (SIMP_RULE (srw_ss()) [GSYM AND_IMP_INTRO] x))) >>
             `code_installed aux2 (dec_clock (LENGTH args') t1).code` by rw [] >>
             first_x_assum (fn x => first_assum (strip_assume_tac o MATCH_MP x)) >>
             fs [] >>
             pop_assum (fn x => first_assum (strip_assume_tac o MATCH_MP x)) >>
             fs [bvlSemTheory.dec_clock_def, closSemTheory.dec_clock_def] >>
             pop_assum (fn x => first_assum (strip_assume_tac o MATCH_MP x)) >>
             qexists_tac `ck+ck'` >>
             rw [] >>
             first_x_assum (qspec_then `t1 with clock := ck + (s1.clock - LENGTH args')` mp_tac) >>
             simp [] >>
             rw [] >>
             `!ck. t1 with <| refs:=t1.refs;code:=t1.code;clock := ck|> = t1 with clock := ck`
                   by rw [bvlSemTheory.state_component_equality] >>
             fs [] >>
             `ck + s1.clock − LENGTH args' = ck + (s1.clock − LENGTH args')` by decide_tac >>
             metis_tac []))));

(* TODO: below this line, needs cleanup *)

(*
val do_eq = prove(
  ``INJ ($' f) (FDOM f) (FRANGE f) ⇒
    (∀x y x1 y1.
           v_rel f r c x x1 ∧
           v_rel f r c y y1 ⇒
           do_eq x y = do_eq x1 y1) ∧
    (∀x y x1 y1.
           LIST_REL (v_rel f r c) x x1 ∧
           LIST_REL (v_rel f r c) y y1 ⇒
           do_eq_list x y = do_eq_list x1 y1)``,
   strip_tac >>
   HO_MATCH_MP_TAC closSemTheory.do_eq_ind >>
   rw []
   >- (rw [closSemTheory.do_eq_def] >>
       Cases_on `x` >>
       fs [v_rel_SIMP] >> fs [add_args_def] >> rw[] >>
       Cases_on `y` >>
       fs [v_rel_SIMP] >> fs [add_args_def] >> rw[] >>
       rfs [] >>
       imp_res_tac LIST_REL_LENGTH >>
       fs [closure_tag_def,partial_app_tag_def] >>
       BasicProvers.EVERY_CASE_TAC >>
       rev_full_simp_tac (srw_ss()++ARITH_ss) [] >>
       fs [INJ_DEF, FLOOKUP_DEF] >>
       metis_tac [])
  >- fs [closSemTheory.do_eq_def]
  >- (res_tac >>
      rw [closSemTheory.do_eq_def] >>
      Cases_on `do_eq x y` >>
      fs [] >>
      qpat_assum `X = do_eq y'' y'''` (mp_tac o GSYM) >>
      rw [])
  >- fs [closSemTheory.do_eq_def]
  >- fs [closSemTheory.do_eq_def]);
*)

val init_code_ok = Q.store_thm ("init_code_ok",
  `(!n.
      n < max_app ⇒ lookup n init_code = SOME (n + 2, generate_generic_app n)) ∧
   (!m n.
      m < max_app ∧ n < max_app ⇒
        lookup (partial_app_fn_location m n) init_code =
          SOME (m - n + 1, generate_partial_app_closure_fn m n))`,
  rw [init_code_def, lookup_fromList, EL_APPEND1, partial_app_fn_location_def]
  >- decide_tac
  >- (rw [LENGTH_FLAT, MAP_GENLIST, combinTheory.o_DEF, sum_genlist_square] >>
      rw [DECIDE ``!(x:num) y z n. x + y +n < x + z ⇔ y +n < z``] >>
      metis_tac [less_rectangle])
  >- (`max_app ≤ max_app + max_app * m + n` by decide_tac >>
      simp [EL_APPEND2, LENGTH_GENLIST] >>
      `0 < max_app` by rw [max_app_def] >>
      rw [twod_table] >>
      `n+m*max_app < max_app*max_app` by metis_tac [less_rectangle2] >>
      rw [EL_GENLIST] >>
      rw [DIV_MULT, Once ADD_COMM] >>
      ONCE_REWRITE_TAC [ADD_COMM] >>
      rw [MOD_MULT]));

val build_aux_thm = prove(
  ``∀c n aux n7 aux7.
    build_aux n c aux = (n7,aux7++aux) ⇒
    (MAP FST aux7) = (REVERSE (GENLIST ($+ n) (LENGTH c)))``,
  Induct >> simp[build_aux_def] >> rw[] >>
  qmatch_assum_abbrev_tac`build_aux nn kk auxx = Z` >>
  qspecl_then[`kk`,`nn`,`auxx`]strip_assume_tac build_aux_acc >>
  Cases_on`build_aux nn kk auxx`>>UNABBREV_ALL_TAC>>fs[]>> rw[] >>
  full_simp_tac std_ss [Once (CONS_APPEND)] >>
  full_simp_tac std_ss [Once (GSYM APPEND_ASSOC)] >> res_tac >>
  rw[GENLIST,REVERSE_APPEND,REVERSE_GENLIST,PRE_SUB1] >>
  simp[LIST_EQ_REWRITE])

val lemma =
  SIMP_RULE(std_ss++LET_ss)[UNCURRY]compile_acc

fun tac (g as (asl,w)) =
  let
    fun get tm =
      let
        val tm = tm |> strip_forall |> snd |> dest_imp |> fst
        fun a tm =
          let
            val (f,xs) = strip_comb tm
          in
            same_const``compile``f andalso
            length xs = 2
          end
      in
        first a [rhs tm, lhs tm]
      end
    val tm = tryfind get asl
    val args = snd(strip_comb tm)
  in
    Cases_on[ANTIQUOTE tm] >>
    strip_assume_tac(SPECL args lemma) >>
    rfs[]
  end g

val compile_code_locs = store_thm("compile_code_locs",
  ``∀xs aux ys aux2.
    compile xs aux = (ys,aux2++aux) ⇒
    MAP FST aux2 = MAP ((+) num_stubs) (REVERSE(code_locs xs))``,
  ho_match_mp_tac compile_ind >> rpt conj_tac >>
  TRY (
    rw[compile_def] >>
    Cases_on`fns`>>fs[code_locs_def]>-(
      fs[LET_THM] ) >>
    Cases_on`t`>>fs[code_locs_def]>-(
      Cases_on `h` >> fs [] >>
      rw[LET_THM] >> tac >> tac  >> rw[] >> fs[LET_THM] >> rw[] >> DECIDE_TAC) >>
    simp[] >> rw[] >>
    fs[compile_def,LET_THM,UNCURRY] >> rw[] >>
    qmatch_assum_abbrev_tac`SND (compile [x1] aux1) = aux2 ++ aux` >>
    qspecl_then[`[x1]`,`aux1`]strip_assume_tac lemma >>
    Cases_on`compile [x1] aux1`>>fs[Abbr`aux1`] >> rw[] >>
    qmatch_assum_abbrev_tac`ys++SND(build_aux (loc + num_stubs) aux1 z) = aux2 ++ aux` >>
    qspecl_then[`aux1`,`loc+num_stubs`,`z`]STRIP_ASSUME_TAC build_aux_acc >>
    Cases_on`build_aux (loc+num_stubs) aux1 z`>>fs[] >>
    qspecl_then[`[SND h]`,`aux`]strip_assume_tac lemma >>
    Cases_on`compile [SND h] aux`>>fs[] >> rw[] >>
    qspecl_then[`SND h'::MAP SND t'`,`ys'++aux`]strip_assume_tac lemma >>
    Cases_on`compile (SND h'::MAP SND t') (ys'++aux)`>>fs[] >> rw[] >>
    fs[Abbr`z`] >> rw[] >> fs[] >>
    full_simp_tac std_ss [GSYM APPEND_ASSOC]  >>
    imp_res_tac build_aux_thm >>
    simp[Abbr`aux1`,ADD1, MAP_REVERSE, LENGTH_MAP2, MAP_GENLIST] >>
    match_mp_tac (METIS_PROVE [] ``!f x y z. (!a. x a = y a) ⇒ f x z = f y z``) >>
    simp [combinTheory.o_DEF]) >>
  simp[compile_def,code_locs_def,UNCURRY] >> rw[] >>
  rpt tac >> rw[] >> fs[] >> rw[]);

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
  (code_locs [Handle x1 x2] =
     let c1 = code_locs [x1] in
     let c2 = code_locs [x2] in
       c1 ++ c2) /\
  (code_locs [Tick x1] =
     code_locs [x1]) /\
  (code_locs [Op op xs] =
     case op of
       Label loc => code_locs xs ++ [loc]
     | _ => code_locs xs) /\
  (code_locs [Call ticks dest xs] =
     case dest of NONE => code_locs xs
                | SOME loc => loc::code_locs xs)`
 (WF_REL_TAC `measure (bvl_exp1_size)`
  \\ REPEAT STRIP_TAC \\ DECIDE_TAC);

val code_locs_cons = store_thm("code_locs_cons",
  ``∀x xs. code_locs (x::xs) = code_locs [x] ++ code_locs xs``,
  gen_tac >> Cases >> simp[code_locs_def])

val code_locs_append = store_thm("code_locs_append",
  ``∀l1 l2. clos_to_bvl$code_locs (l1 ++ l2) = code_locs l1 ++ code_locs l2``,
  Induct >> simp[code_locs_def] >>
  simp[Once code_locs_cons] >>
  simp[Once code_locs_cons,SimpRHS])

val code_locs_MAP_Var = store_thm("code_locs_MAP_Var",
  ``code_locs (MAP Var xs) = []``,
  Induct_on`xs`>>simp[code_locs_def] >>
  simp[Once code_locs_cons] >>
  simp[code_locs_def])

val code_locs_MAP_K_Op_Const = store_thm("code_locs_MAP_K_Op_Const",
  ``∀ls. code_locs (MAP (K (Op (Const n) [])) ls) = []``,
  Induct >> simp[code_locs_def] >>
  simp[Once code_locs_cons] >>
  simp[code_locs_def])

val compile_sing_lemma = prove(
  ``[HD (FST (compile [x] y))] = (FST (compile [x] y))``,
  Cases_on`compile [x] y` >>
  imp_res_tac compile_SING >> rw[])

val contains_Op_Label_def = tDefine "contains_Op_Label" `
  (contains_Op_Label [] ⇔ F) /\
  (contains_Op_Label (x::y::xs) ⇔
     contains_Op_Label [x] ∨
     contains_Op_Label (y::xs)) /\
  (contains_Op_Label [Var v] ⇔ F) /\
  (contains_Op_Label [If x1 x2 x3] ⇔
     contains_Op_Label [x1] ∨
     contains_Op_Label [x2] ∨
     contains_Op_Label [x3]) /\
  (contains_Op_Label [Let xs x2] ⇔
     contains_Op_Label [x2] ∨
     contains_Op_Label xs) /\
  (contains_Op_Label [Raise x1] ⇔
     contains_Op_Label [x1]) /\
  (contains_Op_Label [Tick x1] ⇔
     contains_Op_Label [x1]) /\
  (contains_Op_Label [Op op xs] ⇔
     (∃n. op = Label n) ∨
     contains_Op_Label xs) /\
  (contains_Op_Label [App loc_opt x1 xs] ⇔
     contains_Op_Label [x1] ∨
     contains_Op_Label xs) /\
  (contains_Op_Label [Fn loc vs num_args x1] ⇔
     contains_Op_Label [x1]) /\
  (contains_Op_Label [Letrec loc vs fns x1] ⇔
     contains_Op_Label (MAP SND fns) ∨
     contains_Op_Label [x1]) /\
  (contains_Op_Label [Handle x1 x2] ⇔
     contains_Op_Label [x1] ∨
     contains_Op_Label [x2]) /\
  (contains_Op_Label [Call dest xs] ⇔
     contains_Op_Label xs)`
 (WF_REL_TAC `measure (clos_exp3_size)`
  \\ REPEAT STRIP_TAC \\ TRY DECIDE_TAC
  \\ Induct_on `fns` >>
  srw_tac [ARITH_ss] [clos_exp_size_def] >>
  Cases_on `h` >>
  srw_tac [ARITH_ss] [clos_exp_size_def]);

val contains_Op_Label_EXISTS = prove(
  ``∀ls. contains_Op_Label ls ⇔ EXISTS (λx. contains_Op_Label [x]) ls``,
  Induct >> simp[contains_Op_Label_def] >>
  Cases_on`ls`>>fs[contains_Op_Label_def])

val contains_Call_def = tDefine "contains_Call" `
  (contains_Call [] ⇔ F) /\
  (contains_Call (x::y::xs) ⇔
     contains_Call [x] ∨
     contains_Call (y::xs)) /\
  (contains_Call [Var v] ⇔ F) /\
  (contains_Call [If x1 x2 x3] ⇔
     contains_Call [x1] ∨
     contains_Call [x2] ∨
     contains_Call [x3]) /\
  (contains_Call [Let xs x2] ⇔
     contains_Call [x2] ∨
     contains_Call xs) /\
  (contains_Call [Raise x1] ⇔
     contains_Call [x1]) /\
  (contains_Call [Tick x1] ⇔
     contains_Call [x1]) /\
  (contains_Call [Op op xs] ⇔
     contains_Call xs) /\
  (contains_Call [App loc_opt x1 xs] ⇔
     contains_Call [x1] ∨
     contains_Call xs) /\
  (contains_Call [Fn loc vs num_args x1] ⇔
     contains_Call [x1]) /\
  (contains_Call [Letrec loc vs fns x1] ⇔
     contains_Call (MAP SND fns) ∨
     contains_Call [x1]) /\
  (contains_Call [Handle x1 x2] ⇔
     contains_Call [x1] ∨
     contains_Call [x2]) /\
  (contains_Call [Call dest xs] ⇔ T)`
 (WF_REL_TAC `measure (clos_exp3_size)`
  \\ REPEAT STRIP_TAC \\ TRY DECIDE_TAC
  \\ Induct_on `fns` >>
  srw_tac [ARITH_ss] [clos_exp_size_def] >>
  Cases_on `h` >>
  srw_tac [ARITH_ss] [clos_exp_size_def]);

val contains_Call_EXISTS = prove(
  ``∀ls. contains_Call ls ⇔ EXISTS (λx. contains_Call [x]) ls``,
  Induct >> simp[contains_Call_def] >>
  Cases_on`ls`>>fs[contains_Call_def])

val pComp_contains_Op_Label = store_thm("pComp_contains_Op_Label",
  ``∀e. ¬contains_Op_Label[pComp e]``,
  ho_match_mp_tac pComp_ind >>
  simp[pComp_def,contains_Op_Label_def] >>
  rw[] >> srw_tac[ETA_ss][] >>
  rw[Once contains_Op_Label_EXISTS,EVERY_MAP] >>
  rw[contains_Op_Label_def] >> rw[EVERY_MEM] >>
  rw[Once contains_Op_Label_EXISTS,EVERY_MAP] >>
  rw[contains_Op_Label_def] >> rw[EVERY_MEM] >>
  fs[REPLICATE_GENLIST,MEM_GENLIST, MEM_MAP] >>
  rw[contains_Op_Label_def])

val pComp_contains_Call = store_thm("pComp_contains_Call",
  ``∀e. ¬contains_Call[pComp e]``,
  ho_match_mp_tac pComp_ind >>
  simp[pComp_def,contains_Call_def] >>
  rw[] >> srw_tac[ETA_ss][] >>
  rw[Once contains_Call_EXISTS,EVERY_MAP] >>
  rw[contains_Call_def] >> rw[EVERY_MEM] >>
  rw[Once contains_Call_EXISTS,EVERY_MAP] >>
  rw[contains_Call_def] >> rw[EVERY_MEM] >>
  fs[REPLICATE_GENLIST,MEM_GENLIST, MEM_MAP] >>
  rw[contains_Call_def])

val code_locs_recc_Lets = store_thm("code_locs_recc_Lets",
  ``∀n loc nargs r. set (code_locs [recc_Lets loc nargs n r]) = IMAGE ($+ loc) (count n) ∪ set (code_locs [r])``,
  Induct >> simp[Once recc_Lets_def,code_locs_def,recc_Let_def,COUNT_SUC] >>
  simp[EXTENSION] >> METIS_TAC[]);

val code_locs_build_recc_lets = store_thm("code_locs_build_recc_lets",
  ``∀args vs loc n r.
      set (code_locs [build_recc_lets args vs loc (SUC n) r]) = IMAGE ($+ loc) (count (SUC n)) ∪ set (code_locs [r])``,
  REWRITE_TAC [build_recc_lets_def, GSYM MAP_REVERSE, REVERSE_APPEND] >>
  simp[code_locs_def,code_locs_MAP_Var,recc_Let0_def,code_locs_recc_Lets,COUNT_SUC] >>
  rw[Once code_locs_cons,code_locs_def,code_locs_append,code_locs_MAP_Var,code_locs_MAP_K_Op_Const] >>
  rw[EXTENSION] >> METIS_TAC[]);

val set_code_locs_reverse = store_thm("set_code_locs_reverse",
  ``∀ls. set(code_locs (REVERSE ls)) = set (code_locs ls)``,
  Induct >> simp[code_locs_def,code_locs_append] >>
  simp[Once code_locs_cons,SimpRHS] >>
  METIS_TAC[UNION_COMM])

val code_locs_GENLIST_var = Q.prove (
`!n m. code_locs (GENLIST (\a. Var (a + m)) n) = []`,
 Induct >>
 rw [code_locs_def, GENLIST, code_locs_append]);

val code_locs_GENLIST_var' = Q.prove (
`!n m. code_locs (GENLIST Var n) = []`,
 Induct >>
 rw [code_locs_def, GENLIST, code_locs_append]);

val code_locs_compile = store_thm("code_locs_compile",
  ``∀xs aux.
      ¬contains_Op_Label xs ∧ ¬contains_App_SOME xs ∧ ¬contains_Call xs ⇒
      set (code_locs (FST(compile xs aux))) ⊆ count num_stubs ∪ IMAGE ($+ num_stubs) (set (code_locs xs))``,
  ho_match_mp_tac compile_ind >> rpt conj_tac >>
  TRY ( (* all but Letrec *)
    simp[compile_def,clos_numberTheory.code_locs_def,code_locs_def,UNCURRY,
                   clos_annotateTheory.code_locs_append,code_locs_append,
                   compile_sing_lemma,contains_Op_Label_def,
                   clos_numberTheory.contains_App_SOME_def,
                   contains_Call_def,
                   mk_cl_call_def,
                   set_code_locs_reverse, code_locs_MAP_Var,
                   code_locs_GENLIST_var,code_locs_GENLIST_var'] >>
    rw[compile_sing_lemma] >>
    rpt tac >> rw[] >> fs[compile_sing_lemma] >>
    fs[SUBSET_DEF] >>
    fsrw_tac[ARITH_ss][PULL_EXISTS] >>
    TRY ( Cases_on`op`>>simp[compile_op_def]>>fs[] >> NO_TAC) >>
    TRY ( (* 1 of 3 subgoals in App case *)
      qmatch_abbrev_tac`na < num_stubs + 1 ∧ 0 < num_stubs ∨ b ∨ c` >>
      Cases_on`na < num_stubs + 1` >- simp[num_stubs_def,max_app_def] >>
      `na = LENGTH xs` by METIS_TAC[compile_LENGTH,FST,PAIR] >>
      fsrw_tac[ARITH_ss][max_app_def,num_stubs_def] >>
      NO_TAC) >>
    METIS_TAC[] ) >>
  simp[contains_Op_Label_def,clos_numberTheory.contains_App_SOME_def,contains_Call_def] >>
  simp[compile_def,clos_numberTheory.code_locs_def,code_locs_def] >> rw[] >> fs[] >>
  Cases_on`fns`>>fs[clos_numberTheory.code_locs_def] >>
  Cases_on`t`>>fs[] >- (
    PairCases_on`h`>>fs[] >>
    tac >>
    simp[UNCURRY,code_locs_def,compile_sing_lemma] >>
    simp[Once code_locs_cons,code_locs_def,code_locs_MAP_Var,set_code_locs_reverse,code_locs_append] >>
    fs[SUBSET_DEF] >>
    METIS_TAC[]) >>
  fs[compile_def,LET_THM] >>
  Cases_on`compile[SND h]aux`>>fs[]>>
  Cases_on`compile(SND h'::MAP SND t')r`>>fs[]>>
  Q.PAT_ABBREV_TAC`p = build_aux X Y Z` >>
  Cases_on`p`>>fs[]>>
  simp[UNCURRY] >>
  simp[code_locs_build_recc_lets,compile_sing_lemma] >>
  fs[contains_App_SOME_def,contains_Op_Label_def,contains_Call_def] >>
  fs[SUBSET_DEF,compile_sing_lemma] >>
  simp[MEM_GENLIST,PULL_EXISTS] >>
  fsrw_tac[ARITH_ss][PULL_EXISTS] >>
  METIS_TAC[]);

val code_locs_free_let = prove(
  ``∀n m. code_locs [m] = [] ⇒ code_locs (free_let m n) = []``,
  Induct >- simp[free_let_def,code_locs_def] >>
  fs[free_let_def,GENLIST] >>
  simp[code_locs_append,code_locs_def])

val build_aux_aux = prove(
  ``∀k loc s.
    MAP SND (SND (build_aux loc k s)) =
    REVERSE k ++ MAP SND s``,
  Induct >> simp[build_aux_def])

val code_locs_GENLIST_Op = prove(
  ``(∀loc. op ≠ Label loc) ∧
    (∀x. code_locs (f x) = [])
  ⇒ ∀ls. code_locs (GENLIST (λi. Op op (f i)) ls) = []``,
  strip_tac >>
  Induct_on`ls`>>simp[code_locs_def,GENLIST,code_locs_append] >>
  Cases_on`op`>>fs[])

val code_locs_MAP_code_for_recc_case = prove(
  ``∀ls ns. LENGTH ls = LENGTH ns ⇒ code_locs (MAP SND (MAP2 (code_for_recc_case n) ns ls)) = code_locs ls``,
  Induct >> simp [] >>
  Cases_on `ns` >> simp[code_locs_def,code_for_recc_case_def] >>
  simp[Once code_locs_cons,code_locs_def] >>
  simp[Once code_locs_cons,code_locs_def] >>
  simp[code_locs_append] >>
  simp[Once code_locs_cons,SimpRHS, code_locs_GENLIST_var] >>
  DISCH_TAC >>
  rw [code_locs_GENLIST_var] >>
  HO_MATCH_MP_TAC (MP_CANON code_locs_GENLIST_Op) >>
  simp[code_locs_def]);

val code_locs_compile_aux = store_thm("code_locs_compile_aux",
  ``∀xs aux.
      ¬contains_Op_Label xs ∧ ¬contains_App_SOME xs ∧ ¬contains_Call xs ⇒
      set (code_locs (MAP SND (MAP SND (SND(compile xs aux))))) ⊆
      count num_stubs ∪
      IMAGE ($+ num_stubs) (set (code_locs xs)) ∪
      set (code_locs (MAP SND (MAP SND aux)))``,
  ho_match_mp_tac compile_ind >> rpt conj_tac >>
  TRY (
    simp[contains_Op_Label_def,clos_numberTheory.contains_App_SOME_def,contains_Call_def] >>
    simp[compile_def,clos_numberTheory.code_locs_def] >> rw[] >> fs [] >>
    simp[UNCURRY] >> rpt tac >> rw[] >> fs[SUBSET_DEF] >>
    METIS_TAC[] )
  >- (
    simp[contains_Op_Label_def,clos_numberTheory.contains_App_SOME_def,contains_Call_def] >>
    simp[compile_def,clos_numberTheory.code_locs_def] >> rw[] >> fs [] >>
    simp[UNCURRY] >> rpt tac >> rw[] >> fs[SUBSET_DEF] >>
    simp[Once code_locs_cons,code_locs_def] >>
    simp[compile_sing_lemma] >>
    simp[Once code_locs_cons,code_locs_def, code_locs_append] >>
    `code_locs [Var num_args] = []` by rw [code_locs_def] >>
    simp[code_locs_free_let, code_locs_GENLIST_var'] >>
    rw[] >> imp_res_tac code_locs_compile >> fs[SUBSET_DEF] >>
    fsrw_tac[ARITH_ss][] >> METIS_TAC[])
  >- ( (* Letrec *)
    simp[contains_Op_Label_def,clos_numberTheory.contains_App_SOME_def,contains_Call_def] >>
    simp[compile_def,clos_numberTheory.code_locs_def] >> rw[] >> fs [] >>
    Cases_on`fns`>>fs[clos_numberTheory.code_locs_def] >>
    Cases_on`t`>>fs[] >- (
      PairCases_on`h`>>fs[] >>
      tac >>
      simp[UNCURRY,code_locs_def,compile_sing_lemma] >>
      fs[SUBSET_DEF] >> rw[] >>
      first_x_assum(fn th => first_x_assum(strip_assume_tac o MATCH_MP th)) >> rw[] >>
      pop_assum mp_tac >>
      simp[Once code_locs_cons,code_locs_def,code_locs_append,code_locs_GENLIST_var',code_locs_free_let] >>
      fs[code_locs_append] >> rw[] >>
      imp_res_tac code_locs_compile >> fs[SUBSET_DEF] >>
      fsrw_tac[ARITH_ss][] >>
      METIS_TAC[FST,compile_sing_lemma]) >>
    fs[contains_Call_def,contains_Op_Label_def,contains_App_SOME_def] >>
    fs[compile_def,LET_THM] >>
    Cases_on`compile[SND h]aux`>>fs[]>>
    Cases_on`compile(SND h'::MAP SND t')r`>>fs[]>>
    Q.PAT_ABBREV_TAC`p = build_aux X Y Z` >>
    Cases_on`p`>>fs[markerTheory.Abbrev_def]>>
    pop_assum(assume_tac o SYM) >>
    simp[UNCURRY] >>
    fs[SUBSET_DEF,clos_numberTheory.code_locs_def,LET_THM] >>
    rw[] >> res_tac >> rw[] >>
    qmatch_assum_abbrev_tac`build_aux (loc+num_stubs) k aux1 = X` >>
    qspecl_then[`k`,`loc+num_stubs`,`aux1`]strip_assume_tac build_aux_aux >>
    rfs[Abbr`X`] >> fs[] >>
    qpat_assum`MEM x Z`mp_tac >>
    simp[code_locs_append] >>
    strip_tac >> TRY ( res_tac >> rw[] >> fsrw_tac[ARITH_ss][] >> METIS_TAC[] ) >>
    (* 1 subgoal left *)
    fs[set_code_locs_reverse,MAP_REVERSE] >>
    imp_res_tac compile_LENGTH >>
    fsrw_tac[ARITH_ss][Abbr`k`,code_locs_append,code_locs_MAP_code_for_recc_case] >>
    imp_res_tac code_locs_compile >> fs[SUBSET_DEF] >> fsrw_tac[ARITH_ss][] >>
    METIS_TAC[FST,compile_sing_lemma]))

val HD_FST_cFree_sing = prove(
  ``[HD (FST (cFree [x]))] = FST(cFree [x])``,
  simp[SING_HD,LENGTH_FST_cFree])

val HD_cShift_sing = prove(
  ``[HD (cShift [x] y z w)] = cShift [x] y z w``,
  rw[SING_HD,cShift_LENGTH_LEMMA])

val contains_Call_append = store_thm("contains_Call_append",
  ``contains_Call (l1 ++ l2) = (contains_Call l1 ∨ contains_Call l2)``,
  METIS_TAC[contains_Call_EXISTS,EXISTS_APPEND])

val contains_Call_EXISTS = store_thm("contains_Call_EXISTS",
  ``∀ls. contains_Call ls ⇔ EXISTS (λx. contains_Call [x]) ls``,
  Induct >> simp[contains_Call_def] >>
  Cases_on`ls`>>simp[contains_Call_def])

val contains_Call_cFree = store_thm("contains_Call_cFree",
  ``∀v. contains_Call (FST (cFree v)) = contains_Call v``,
  ho_match_mp_tac cFree_ind >>
  simp[cFree_def,contains_Call_def,UNCURRY,HD_FST_cFree_sing,contains_Call_append] >>
  rw[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
  TRY(METIS_TAC[PAIR]) >> (* 1 subgoal left *)
  simp[Q.SPEC`MAP X Y`contains_Call_EXISTS,EQ_IMP_THM] >> rw[] >> rw[] >>
  fs[EXISTS_MAP,LAMBDA_PROD,HD_FST_cFree_sing] >>
  fs[EXISTS_MEM,EXISTS_PROD] >>
  METIS_TAC[]);

val contains_Call_cShift = store_thm("contains_Call_cShift",
  ``∀a b c d. contains_Call (cShift a b c d) ⇔ contains_Call a``,
  ho_match_mp_tac cShift_ind >>
  simp[cShift_def,contains_Call_def,HD_cShift_sing,contains_Call_append] >>
  rw[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
  simp[Q.SPEC`MAP X Y`contains_Call_EXISTS,EQ_IMP_THM] >> rw[] >> rw[] >>
  fs[EXISTS_MAP,LAMBDA_PROD,HD_cShift_sing] >>
  fs[EXISTS_MEM,EXISTS_PROD] >>
  METIS_TAC[]);

val contains_Call_cAnnotate = store_thm("contains_Call_cAnnotate",
  ``∀n e. contains_Call (cAnnotate n e) ⇔ contains_Call e``,
  rw[cAnnotate_def,contains_Call_cShift,contains_Call_cFree])

val contains_App_SOME_append = store_thm("contains_App_SOME_append",
  ``contains_App_SOME (l1 ++ l2) = (contains_App_SOME l1 ∨ contains_App_SOME l2)``,
  METIS_TAC[contains_App_SOME_EXISTS,EXISTS_APPEND])

val contains_App_SOME_cFree = store_thm("contains_App_SOME_cFree",
  ``∀v. contains_App_SOME (FST (cFree v)) = contains_App_SOME v``,
  ho_match_mp_tac cFree_ind >>
  simp[cFree_def,contains_App_SOME_def,UNCURRY,HD_FST_cFree_sing,contains_App_SOME_append] >>
  rw[] >>
  rw[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
  TRY(METIS_TAC[PAIR,FST,LENGTH_FST_cFree]) (* 1 subgoal left *) >>
  simp[Q.SPEC`MAP X Y`contains_App_SOME_EXISTS,EQ_IMP_THM] >> rw[] >> rw[] >>
  fs[EXISTS_MAP,LAMBDA_PROD,HD_FST_cFree_sing] >>
  fs[EXISTS_MEM,EXISTS_PROD] >> METIS_TAC[]);

val contains_App_SOME_cShift = store_thm("contains_App_SOME_cShift",
  ``∀a b c d. contains_App_SOME (cShift a b c d) ⇔ contains_App_SOME a``,
  ho_match_mp_tac cShift_ind >>
  simp[cShift_def,contains_App_SOME_def,HD_cShift_sing,contains_App_SOME_append,cShift_LENGTH_LEMMA] >>
  simp[MAP_MAP_o,combinTheory.o_DEF,UNCURRY] >>
  simp[Q.SPEC`MAP X Y`contains_App_SOME_EXISTS,EXISTS_MAP,HD_cShift_sing] >>
  simp[EXISTS_MEM,EXISTS_PROD,PULL_EXISTS] >>
  METIS_TAC[]);

val contains_App_SOME_cAnnotate = store_thm("contains_App_SOME_cAnnotate",
  ``∀n e. contains_App_SOME (cAnnotate n e) ⇔ contains_App_SOME e``,
  rw[cAnnotate_def,contains_App_SOME_cShift,contains_App_SOME_cFree])

val contains_Op_Label_append = store_thm("contains_Op_Label_append",
  ``contains_Op_Label (l1 ++ l2) = (contains_Op_Label l1 ∨ contains_Op_Label l2)``,
  METIS_TAC[contains_Op_Label_EXISTS,EXISTS_APPEND])

val contains_Op_Label_EXISTS = store_thm("contains_Op_Label_EXISTS",
  ``∀ls. contains_Op_Label ls ⇔ EXISTS (λx. contains_Op_Label [x]) ls``,
  Induct >> simp[contains_Op_Label_def] >>
  Cases_on`ls`>>simp[contains_Op_Label_def])

val contains_Op_Label_cFree = store_thm("contains_Op_Label_cFree",
  ``∀v. contains_Op_Label (FST (cFree v)) = contains_Op_Label v``,
  ho_match_mp_tac cFree_ind >>
  simp[cFree_def,contains_Op_Label_def,UNCURRY,HD_FST_cFree_sing,contains_Op_Label_append] >>
  rw[] >> TRY(METIS_TAC[PAIR]) >>
  simp[Q.SPEC`MAP X Y`contains_Op_Label_EXISTS,EQ_IMP_THM] >> rw[] >> rw[] >>
  fs[EXISTS_MAP,LAMBDA_PROD,HD_FST_cFree_sing] >>
  fs[EXISTS_MEM,EXISTS_PROD] >>
  METIS_TAC[]);

val contains_Op_Label_cShift = store_thm("contains_Op_Label_cShift",
  ``∀a b c d. contains_Op_Label (cShift a b c d) ⇔ contains_Op_Label a``,
  ho_match_mp_tac cShift_ind >>
  simp[cShift_def,contains_Op_Label_def,HD_cShift_sing,contains_Op_Label_append] >>
  rw[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
  simp[Q.SPEC`MAP X Y`contains_Op_Label_EXISTS,EQ_IMP_THM] >> rw[] >> rw[] >>
  fs[EXISTS_MAP,LAMBDA_PROD,HD_cShift_sing] >>
  fs[EXISTS_MEM,EXISTS_PROD] >>
  METIS_TAC[]);

val contains_Op_Label_cAnnotate = store_thm("contains_Op_Label_cAnnotate",
  ``∀n e. contains_Op_Label (cAnnotate n e) ⇔ contains_Op_Label e``,
  rw[cAnnotate_def,contains_Op_Label_cShift,contains_Op_Label_cFree])

fun tac (g as (asl,w)) =
  let
    fun finder tm =
      let
        val (f,args) = strip_comb tm
      in
        (same_const``renumber_code_locs`` f orelse
         same_const``renumber_code_locs_list`` f)
        andalso
         all is_var args
        andalso
         length args = 2
      end
    val tms = find_terms finder w
  in
    map_every (fn tm => Cases_on [ANTIQUOTE tm]) tms g
  end

val contains_Call_cons = store_thm("contains_Call_cons",
  ``contains_Call (e::x) ⇔ contains_Call [e] ∨ contains_Call x``,
  METIS_TAC[contains_Call_EXISTS,listTheory.EXISTS_DEF])

val contains_Call_renumber_code_locs = store_thm("contains_Call_renumber_code_locs",
  ``(∀n e m f. renumber_code_locs_list n e = (m,f) ⇒
      (contains_Call f ⇔ contains_Call e)) ∧
    (∀n e m f. renumber_code_locs n e = (m,f) ⇒
      (contains_Call [f] ⇔ contains_Call [e]))``,
  ho_match_mp_tac renumber_code_locs_ind >>
  simp[contains_Call_def,renumber_code_locs_def,UNCURRY] >> rw[] >>
  tac >> fs[] >> rw[] >>
  tac >> fs[] >> rw[] >>
  tac >> fs[] >> rw[] >-
  METIS_TAC[contains_Call_cons] >>
  cheat);
  (*
  Cases_on`renumber_code_locs (q + LENGTH r) e'`>>fs[])
  *)

val contains_App_SOME_cons = store_thm("contains_App_SOME_cons",
  ``contains_App_SOME (e::x) ⇔ contains_App_SOME [e] ∨ contains_App_SOME x``,
  METIS_TAC[contains_App_SOME_EXISTS,listTheory.EXISTS_DEF])

val renumber_code_locs_length = store_thm("renumber_code_locs_length",
  ``(∀x y. LENGTH (SND (renumber_code_locs_list x y)) = LENGTH y) ∧
    (∀(x:num)(y:clos_exp). T)``,
    ho_match_mp_tac renumber_code_locs_ind >>
    simp[renumber_code_locs_def,UNCURRY] >> rw[] >>
    tac >> fs[])

val contains_App_SOME_renumber_code_locs = store_thm("contains_App_SOME_renumber_code_locs",
  ``(∀n e m f. renumber_code_locs_list n e = (m,f) ⇒
      (contains_App_SOME f ⇔ contains_App_SOME e)) ∧
    (∀n e m f. renumber_code_locs n e = (m,f) ⇒
      (contains_App_SOME [f] ⇔ contains_App_SOME [e]))``,
  ho_match_mp_tac renumber_code_locs_ind >>
  simp[contains_App_SOME_def,renumber_code_locs_def,UNCURRY] >> rw[] >>
  tac >> fs[] >> rw[] >>
  tac >> fs[] >> rw[] >>
  tac >> fs[] >> rw[] >-
    METIS_TAC[contains_App_SOME_cons]
  >-
    METIS_TAC[renumber_code_locs_length,SND] >>
  Cases_on`renumber_code_locs_list n (MAP SND fns)`>>fs[]>>
  Cases_on`renumber_code_locs (q + LENGTH r) e`>>fs[]>>
  METIS_TAC[MAP_ZIP,renumber_code_locs_length,SND,LENGTH_MAP])

val contains_Op_Label_cons = store_thm("contains_Op_Label_cons",
  ``contains_Op_Label (e::x) ⇔ contains_Op_Label [e] ∨ contains_Op_Label x``,
  METIS_TAC[contains_Op_Label_EXISTS,listTheory.EXISTS_DEF])

val contains_Op_Label_renumber_code_locs = store_thm("contains_Op_Label_renumber_code_locs",
  ``(∀n e m f. renumber_code_locs_list n e = (m,f) ⇒
      (contains_Op_Label f ⇔ contains_Op_Label e)) ∧
    (∀n e m f. renumber_code_locs n e = (m,f) ⇒
      (contains_Op_Label [f] ⇔ contains_Op_Label [e]))``,
  ho_match_mp_tac renumber_code_locs_ind >>
  simp[contains_Op_Label_def,renumber_code_locs_def,UNCURRY] >> rw[] >>
  tac >> fs[] >> rw[] >>
  tac >> fs[] >> rw[] >>
  tac >> fs[] >> rw[] >-
  METIS_TAC[contains_Op_Label_cons] >>
  Cases_on`renumber_code_locs_list n (MAP SND fns)`>>fs[]>>
  Cases_on`renumber_code_locs (q + LENGTH r) e`>>fs[]>>
  METIS_TAC[MAP_ZIP,renumber_code_locs_length,SND,LENGTH_MAP])

val _ = export_theory();
