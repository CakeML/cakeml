open preamble
     closLangTheory closSemTheory closPropsTheory
     bvlSemTheory bvlPropsTheory
     bvl_jumpProofTheory
     clos_to_bvlTheory;
local open
  clos_mtiProofTheory
  clos_numberProofTheory
  clos_knownProofTheory
  clos_removeProofTheory
  clos_annotateProofTheory
  clos_callProofTheory
in end

val _ = new_theory"clos_to_bvlProof";

val _ = temp_bring_to_front_overload"evaluate"{Name="evaluate",Thy="bvlSem"};
val _ = temp_bring_to_front_overload"num_stubs"{Name="num_stubs",Thy="clos_to_bvl"};
val _ = temp_bring_to_front_overload"compile_exps"{Name="compile_exps",Thy="clos_to_bvl"};

val _ = temp_overload_on ("kcompile", ``clos_known$compile``)
val _ = temp_overload_on ("kvrel", ``clos_knownProof$val_rel``)
val _ = temp_overload_on ("kerel", ``clos_knownProof$exp_rel``)
val _ = temp_overload_on ("krrel", ``clos_knownProof$res_rel``)

val _ = temp_overload_on ("state_rel", ``clos_relation$state_rel``)

(* TODO: move? *)

val ARITH_TAC = intLib.ARITH_TAC;

val EVERY2_GENLIST = LIST_REL_GENLIST |> EQ_IMP_RULE |> snd |> Q.GEN`l`

val EVERY_ZIP_GENLIST = prove(
  ``!xs.
      (!i. i < LENGTH xs ==> P (EL i xs,f i)) ==>
      EVERY P (ZIP (xs,GENLIST f (LENGTH xs)))``,
  HO_MATCH_MP_TAC SNOC_INDUCT \\ full_simp_tac(srw_ss())[GENLIST] \\ REPEAT STRIP_TAC
  \\ full_simp_tac(srw_ss())[ZIP_SNOC,EVERY_SNOC] \\ REPEAT STRIP_TAC
  THEN1
   (FIRST_X_ASSUM MATCH_MP_TAC \\ REPEAT STRIP_TAC
    \\ IMP_RES_TAC EL_SNOC \\ full_simp_tac(srw_ss())[]
    \\ `i < SUC (LENGTH xs)` by DECIDE_TAC \\ RES_TAC \\ METIS_TAC [])
  \\ `LENGTH xs < SUC (LENGTH xs)` by DECIDE_TAC \\ RES_TAC
  \\ full_simp_tac(srw_ss())[SNOC_APPEND,EL_LENGTH_APPEND]);

val EVEN_SUB = Q.store_thm("EVEN_SUB",
  `∀m n. m ≤ n ⇒ (EVEN (n - m) ⇔ (EVEN n <=> EVEN m))`,
  Induct \\ simp[] \\ Cases \\ simp[EVEN]);

val ODD_SUB = Q.store_thm("ODD_SUB",
  `∀m n. m ≤ n ⇒ (ODD (n - m) ⇔ ¬(ODD n ⇔ ODD m))`,
  rw[ODD_EVEN,EVEN_SUB]);

val map2_snoc = Q.prove (
  `!l1 l2 f x y.
    LENGTH l1 = LENGTH l2 ⇒
    MAP2 f (SNOC x l1) (SNOC y l2) = MAP2 f l1 l2 ++ [f x y]`,
  Induct_on `l1` >>
  srw_tac[][] >>
  `l2 = [] ∨ ?h l2'. l2 = h::l2'` by (Cases_on `l2` >> srw_tac[][]) >>
  Cases_on `l2` >>
  full_simp_tac(srw_ss())[] >>
  srw_tac[][]);

val el_map2 = Q.prove (
  `!x f l1 l2.
    LENGTH l1 = LENGTH l2 ∧ x < LENGTH l1
    ⇒
    EL x (MAP2 f l1 l2) = f (EL x l1) (EL x l2)`,
  Induct_on `x` >>
  srw_tac[][] >>
  Cases_on `l2` >>
  full_simp_tac(srw_ss())[] >>
  Cases_on `l1` >>
  full_simp_tac(srw_ss())[]);

val length_take2 = Q.prove (
  `!x l. ¬(x ≤ LENGTH l) ⇒ LENGTH (TAKE x l) = LENGTH l`,
  Induct_on `l` >>
  srw_tac[][TAKE_def] >>
  Cases_on `x` >>
  full_simp_tac(srw_ss())[] >>
  first_x_assum match_mp_tac >>
  decide_tac);

val el_take_append = Q.prove (
  `!n l x l2. n ≤ LENGTH l ⇒ EL n (TAKE n l ++ [x] ++ l2) = x`,
  Induct_on `l` >>
  srw_tac[][] >>
  `0 < n` by decide_tac >>
  srw_tac[][EL_CONS] >>
  Cases_on `n = SUC (LENGTH l)` >>
  full_simp_tac(srw_ss())[] >>
  srw_tac[][PRE_SUB1]
  >- (first_x_assum (qspec_then `LENGTH l` mp_tac) >>
      srw_tac[][])
  >- (first_x_assum (qspec_then `n-1` mp_tac) >>
      srw_tac [ARITH_ss] []));

val el_append2 = Q.prove (
  `∀l x. EL (LENGTH l) (l++[x]) = x`,
  Induct_on `l` >> srw_tac[][]);

val el_append2_lemma = Q.prove (
  `!n args.
    n+1 = LENGTH args
    ⇒
    EL (SUC n) (args ++ [x]) = x`,
  Induct_on `args` >> srw_tac[][] >>
  full_simp_tac (srw_ss()++ARITH_ss) [ADD1, el_append2]);

val hd_append = Q.prove (
  `!l1 l2. 0 < LENGTH l1 ⇒ HD (l1 ++ l2) = HD l1`,
  Cases_on `l1` >> srw_tac[][]);

val tl_append = Q.prove (
  `!l1 l2. 0 < LENGTH l1 ⇒ TL (l1 ++ l2) = TL l1 ++ l2`,
  Cases_on `l1` >> srw_tac[][]);

val twod_table_lemma = Q.prove (
  `!x y z.
    z ≤ y ⇒
    GENLIST (λt. f ((t + x * y) DIV y) ((t + x * y) MOD y)) z
    =
    GENLIST (λt. f x t) z`,
  Induct_on `z` >>
  srw_tac[][GENLIST] >>
  `z < y ∧ z ≤ y` by decide_tac >>
  full_simp_tac(srw_ss())[] >>
  `z+x*y = x*y+z` by decide_tac >>
  rw_tac std_ss [MOD_MULT, DIV_MULT, LESS_DIV_EQ_ZERO]);

val twod_table = Q.prove (
  `!f x y.
    0 < y ⇒
    FLAT (GENLIST (\m. GENLIST (\n. f m n) y) x) =
    GENLIST (\n. f (n DIV y) (n MOD y)) (x * y)`,
  Induct_on `x` >>
  srw_tac[][GENLIST] >>
  `(x+1) * y = y + x * y` by decide_tac >>
  full_simp_tac(srw_ss())[ADD1, GENLIST_APPEND, twod_table_lemma]);

val less_rectangle = Q.prove (
  `!(x:num) y m n. m < x ∧ n < y ⇒ x * n +m < x * y`,
  REPEAT STRIP_TAC
  \\ `SUC n <= y` by full_simp_tac(srw_ss())[LESS_EQ]
  \\ `x * (SUC n) <= x * y` by full_simp_tac(srw_ss())[]
  \\ FULL_SIMP_TAC bool_ss [MULT_CLAUSES]
  \\ DECIDE_TAC);

val less_rectangle2 = Q.prove (
  `!(x:num) y m n. m < x ∧ n < y ⇒ m + n * x< x * y`,
  metis_tac [less_rectangle, ADD_COMM, MULT_COMM]);

val sum_genlist_square = Q.prove (
  `!x z. SUM (GENLIST (\y. z) x) = x * z`,
  Induct >>
  srw_tac[][GENLIST, SUM_SNOC, ADD1] >>
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
  srw_tac[][] >>
  full_simp_tac (srw_ss() ++ ARITH_ss) [ADD1, TAKE_LENGTH_APPEND] >>
  `LENGTH arg_list = rem_args` by decide_tac >>
  srw_tac[][] >>
  full_simp_tac (srw_ss() ++ ARITH_ss) [ADD1, TAKE_LENGTH_APPEND]);

val ETA2_THM = Q.prove (
  `(\x y. f a b c x y) = f a b c`,
  srw_tac[][FUN_EQ_THM]);

val p_genlist = Q.prove (
  `EL k exps_ps = ((n',e),p) ∧
   MAP SND exps_ps = GENLIST (λn. loc + num_stubs + 2*n) (LENGTH exps_ps) ∧
   k < LENGTH exps_ps
   ⇒
   p = EL k (GENLIST (λn. loc + num_stubs + 2*n) (LENGTH exps_ps))`,
  srw_tac[][] >>
  `EL k (MAP SND exps_ps) = EL k (GENLIST (λn. loc + num_stubs + 2*n) (LENGTH exps_ps))` by metis_tac [] >>
  rev_full_simp_tac(srw_ss())[EL_MAP]);

val list_CASE_same = Q.store_thm("list_CASE_same",
  `list_CASE ls (P []) (λx y. P (x::y)) = P ls`,
  Cases_on`ls` \\ simp[]);

(* -- *)

(* correctness of partial/over application *)

val evaluate_genlist_prev_args = Q.prove (
  `!prev_args z x tag arg_list st.
    evaluate (REVERSE (GENLIST (λprev_arg. Op El [Op (Const (&(prev_arg + LENGTH z))) []; Var (LENGTH x)]) (LENGTH prev_args)),
           x++(Block tag (z++prev_args))::arg_list,
           st)
    =
    (Rval (REVERSE prev_args),st)`,
  Induct_on `prev_args` >>
  srw_tac[][evaluate_def, GENLIST_CONS] >>
  srw_tac[][evaluate_APPEND, evaluate_def, do_app_def] >>
  full_simp_tac (srw_ss()++ARITH_ss) [] >>
  srw_tac[][] >>
  pop_assum (qspecl_then [`z++[h]`] mp_tac) >>
  srw_tac [ARITH_ss] [combinTheory.o_DEF, ADD1] >>
  `z ++ h :: prev_args = z ++ [h] ++ prev_args` by metis_tac [APPEND, APPEND_ASSOC] >>
  srw_tac[][el_append3] >>
  `x ++ Block tag (z ++ [h] ++ prev_args)::arg_list = x ++ [Block tag (z ++ [h] ++ prev_args)] ++ arg_list`
          by metis_tac [APPEND, APPEND_ASSOC] >>
  srw_tac[][el_append3] >>
  decide_tac);

val evaluate_genlist_prev_args1 = Q.prove (
  `!prev_args x y tag p n cl args st.
    evaluate (REVERSE (GENLIST (λprev_arg. Op El [Op (Const (&(prev_arg + 3))) []; Var (LENGTH args + 2)]) (LENGTH prev_args)),
           x::y::(args++[Block tag (p::n::cl::prev_args)]),
           st)
    =
    (Rval (REVERSE prev_args),st)`,
  srw_tac[][] >>
  (Q.SPECL_THEN [`prev_args`, `[p;n;cl]`, `x::y::args`]assume_tac evaluate_genlist_prev_args) >>
  full_simp_tac (srw_ss()++ARITH_ss) [ADD1]);

val evaluate_genlist_prev_args_no_rev = Q.prove (
  `!prev_args z x tag arg_list st.
    evaluate (GENLIST (λprev_arg. Op El [Op (Const (&(prev_arg + LENGTH z))) []; Var (LENGTH x)]) (LENGTH prev_args),
           x++(Block tag (z++prev_args))::arg_list,
           st)
    =
    (Rval prev_args,st)`,
  Induct_on `prev_args` >>
  srw_tac[][evaluate_def, GENLIST_CONS] >>
  srw_tac[][Once evaluate_CONS, evaluate_def, do_app_def] >>
  full_simp_tac (srw_ss()++ARITH_ss) [] >>
  srw_tac[][] >>
  pop_assum (qspecl_then [`z++[h]`] mp_tac) >>
  srw_tac [ARITH_ss] [combinTheory.o_DEF, ADD1] >>
  `z ++ h :: prev_args = z ++ [h] ++ prev_args` by metis_tac [APPEND, APPEND_ASSOC] >>
  srw_tac[][el_append3] >>
  `x ++ Block tag (z ++ [h] ++ prev_args)::arg_list = x ++ [Block tag (z ++ [h] ++ prev_args)] ++ arg_list`
          by metis_tac [APPEND, APPEND_ASSOC] >>
  srw_tac[][el_append3] >>
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
  srw_tac[][generate_generic_app_def] >>
  srw_tac[][evaluate_def, do_app_def] >>
  full_simp_tac (srw_ss() ++ ARITH_ss) [el_append2] >>
  `~(&total_args − &(n+1) < 0)` by intLib.ARITH_TAC >>
  srw_tac[][] >>
  rev_full_simp_tac(srw_ss())[evaluate_mk_tick, evaluate_def, do_app_def] >>
  full_simp_tac (srw_ss() ++ ARITH_ss) [el_append2] >>
  srw_tac[][DECIDE ``x + 2 = SUC (SUC x)``, el_append2_lemma, evaluate_APPEND] >>
  srw_tac [ARITH_ss] [ADD1, evaluate_genlist_vars_rev, evaluate_def] >>
  `evaluate ([Op El [Op (Const (1:int)) []; Var (LENGTH args + 1)]],
          Number (&total_args − &(LENGTH args))::(args++[Block closure_tag (CodePtr l::Number (&total_args)::fvs)]),
          dec_clock n st) =
    (Rval [Number (&total_args)], dec_clock n st)`
          by (srw_tac [ARITH_ss] [evaluate_def, do_app_def, int_arithTheory.INT_NUM_SUB] >>
              srw_tac [ARITH_ss][PRE_SUB1, EL_CONS, el_append2]) >>
  imp_res_tac evaluate_Jump >>
  rev_full_simp_tac(srw_ss())[] >>
  srw_tac [ARITH_ss] [LENGTH_GENLIST, evaluate_def, do_app_def, evaluate_APPEND] >>
  srw_tac[][evaluate_def, do_app_def, int_arithTheory.INT_NUM_SUB, el_append2,
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
  srw_tac[][generate_generic_app_def, mk_const_def] >>
  srw_tac[][evaluate_def, do_app_def] >>
  full_simp_tac (srw_ss() ++ ARITH_ss) [] >>
  `~(&rem_args − &(n+1) < 0)` by intLib.ARITH_TAC >>
  srw_tac[][el_append2] >>
  rev_full_simp_tac(srw_ss())[evaluate_mk_tick] >>
  full_simp_tac (srw_ss()++ARITH_ss) [] >>
  srw_tac[][evaluate_def, do_app_def] >>
  srw_tac[][DECIDE ``x + 2 = SUC (SUC x)``, el_append2_lemma, evaluate_APPEND] >>
  srw_tac[][ADD1] >>
  full_simp_tac(srw_ss())[] >>
  `evaluate ([Op Sub [Op (Const 4) []; Op LengthBlock [Var (LENGTH args + 1)]]],
          Number (&rem_args − &LENGTH args)::(args++[Block partial_app_tag (CodePtr l::Number (&rem_args)::clo::prev_args)]),dec_clock n st) =
    (Rval [Number (&(LENGTH prev_args - 1))], dec_clock n st)`
          by (srw_tac [ARITH_ss] [evaluate_def, do_app_def, int_arithTheory.INT_NUM_SUB] >>
              srw_tac [ARITH_ss] [EL_CONS, GSYM ADD1, el_append2] >>
              intLib.ARITH_TAC) >>
  imp_res_tac evaluate_Jump >>
  rev_full_simp_tac(srw_ss())[] >>
  srw_tac [ARITH_ss] [evaluate_APPEND, LENGTH_GENLIST, evaluate_def, do_app_def] >>
  srw_tac[][REVERSE_APPEND, evaluate_APPEND] >>
  `n + 3 = LENGTH args + 2` by decide_tac >>
  srw_tac[][evaluate_genlist_prev_args1] >>
  srw_tac [ARITH_ss] [evaluate_genlist_vars_rev, EL_CONS, PRE_SUB1, el_append2] >>
  `evaluate ([Op Add [Op (Const (&(n + (LENGTH prev_args + 1)))) []; Var 1]],
          Number (&(LENGTH prev_args − 1))::Number (&rem_args − &LENGTH args)::(args++[Block partial_app_tag (CodePtr l::Number (&rem_args)::clo::prev_args)]),
          dec_clock n st) =
    (Rval [Number (&(LENGTH prev_args + rem_args))], dec_clock n st)`
          by (srw_tac [ARITH_ss] [partial_app_tag_def, evaluate_def, do_app_def, int_arithTheory.INT_NUM_SUB] >>
              intLib.ARITH_TAC) >>
  imp_res_tac evaluate_Jump >>
  `LENGTH prev_args - 1 < max_app` by decide_tac >>
  full_simp_tac(srw_ss())[partial_app_tag_def] >>
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
  full_simp_tac(srw_ss())[unpack_closure_cases]
  >- (qspecl_then [`LENGTH args - 1`, `args`, `st`, `total_args`] mp_tac evaluate_generic_app1 >>
      srw_tac [ARITH_ss] [] >>
      rev_full_simp_tac(srw_ss())[] >>
      `&Num total_args' = total_args'` by intLib.COOPER_TAC >>
      full_simp_tac(srw_ss())[] >>
      srw_tac[][])
  >- (qspecl_then [`LENGTH args - 1`, `args`, `st`, `Num rem_args`, `prev_args`] mp_tac evaluate_generic_app2 >>
      full_simp_tac (srw_ss()++ARITH_ss) [] >>
      srw_tac [ARITH_ss] [] >>
      Cases_on `prev_args` >>
      full_simp_tac(srw_ss())[] >>
      srw_tac[][] >>
      `&Num rem_args = rem_args` by intLib.ARITH_TAC >>
      full_simp_tac(srw_ss())[] >>
      srw_tac[][int_arithTheory.INT_NUM_SUB] >>
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
  srw_tac[][generate_generic_app_def, mk_const_def] >>
  srw_tac[][evaluate_def, do_app_def, el_append2] >>
  full_simp_tac (srw_ss() ++ ARITH_ss) [partial_app_tag_def] >>
  `(&rem_args − &(LENGTH args) < 0)` by intLib.ARITH_TAC >>
  srw_tac[][] >>
  `evaluate ([Op El [Op (Const (1:int)) []; Var (LENGTH args + 1)]],
          Number (&rem_args − &LENGTH args):: (args ++ [Block tag (CodePtr l::Number (&rem_args)::vs)]),
          st) =
    (Rval [Number (&rem_args)], st)`
          by srw_tac [ARITH_ss] [evaluate_def, do_app_def, PRE_SUB1, EL_CONS, el_append2] >>
  `n + 2 = LENGTH args + 1` by decide_tac >>
  full_simp_tac(srw_ss())[] >>
  imp_res_tac evaluate_Jump >>
  srw_tac [ARITH_ss] [LENGTH_GENLIST, evaluate_def, do_app_def] >>
  srw_tac [ARITH_ss] [evaluate_APPEND, do_app_def, evaluate_def] >>
  srw_tac [ARITH_ss] [Once evaluate_CONS, evaluate_def, evaluate_APPEND] >>
  full_simp_tac(srw_ss())[] >>
  `(rem_args + 1) + ((LENGTH args + 1) - rem_args) ≤
     LENGTH (Number (&rem_args)::Number (&rem_args − &LENGTH args)::
                 (args ++
                  [Block tag (CodePtr l::Number (&rem_args)::vs)]))`
             by (srw_tac[][] >>
                 decide_tac) >>
  imp_res_tac evaluate_genlist_vars >>
  pop_assum (qspec_then `st` mp_tac) >>
  `LENGTH args + 1 - rem_args = (LENGTH args + 1) - rem_args` by decide_tac >>
  simp [] >>
  srw_tac[][] >>
  simp [EL_CONS, PRE_SUB1, el_append2, find_code_def, bvlSemTheory.state_component_equality, FRONT_APPEND] >>
  `LENGTH args > rem_args` by decide_tac >>
  srw_tac[][take_drop_lemma] >>
  qabbrev_tac `res1 =
    evaluate
      ([exp],
       DROP (LENGTH args − (rem_args + 1)) args ++ [Block tag (CodePtr l::Number (&rem_args)::vs)],
       dec_clock (rem_args + 1) st)` >>
  Cases_on `res1` >>
  full_simp_tac(srw_ss())[] >>
  Cases_on `q` >>
  full_simp_tac(srw_ss())[] >>
  `LENGTH a = 1` by metis_tac [bvlPropsTheory.evaluate_IMP_LENGTH, LENGTH, DECIDE ``SUC 0 = 1``] >>
  Cases_on `a` >>
  full_simp_tac(srw_ss())[] >>
  Cases_on `t` >>
  full_simp_tac(srw_ss())[] >>
  BasicProvers.FULL_CASE_TAC >>
  BasicProvers.FULL_CASE_TAC >>
  `LENGTH a = 1` by metis_tac [bvlPropsTheory.evaluate_IMP_LENGTH, LENGTH, DECIDE ``SUC 0 = 1``] >>
  Cases_on `a` >>
  full_simp_tac(srw_ss())[] >>
  Cases_on `t` >>
  full_simp_tac(srw_ss())[]);

val mk_cl_lem = Q.prove (
  `l < LENGTH env
   ⇒
   evaluate (GENLIST (λn. Var (n + 3)) l, a::b::c::env, st) =
   evaluate (GENLIST (λn. Var (n + 1)) l, a::env, st)`,
  srw_tac[][] >>
  `l + 3 ≤ LENGTH (a::b::c::env)` by srw_tac [ARITH_ss] [ADD1] >>
  `l + 1 ≤ LENGTH (a::env)` by srw_tac [ARITH_ss] [ADD1] >>
  imp_res_tac evaluate_genlist_vars >>
  srw_tac[][]);

val evaluate_mk_cl_simpl = Q.prove (
  `evaluate ([mk_cl_call (Var 0) (GENLIST (λn. Var (n + 3)) (LENGTH args' − (n + 1)))],
                               v::a::b::(args' ++ [Block tag (CodePtr p::Number (&n)::xs)]),
                               st')
   =
   evaluate ([mk_cl_call (Var 0) (GENLIST (λn. Var (n + 1)) (LENGTH args' − (n + 1)))],
                               v::(args' ++ [Block tag (CodePtr p::Number (&n)::xs)]),
                               st')`,
  srw_tac[][mk_cl_call_def, evaluate_def, do_app_def] >>
  Cases_on `v` >>
  srw_tac[][] >>
  BasicProvers.FULL_CASE_TAC >>
  srw_tac[][evaluate_APPEND] >>
  ntac 2 (pop_assum (mp_tac o GSYM)) >>
  srw_tac[][] >>
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
  srw_tac[][Once mk_cl_call_def, evaluate_def, do_app_def] >>
  full_simp_tac(srw_ss())[ADD1] >>
  Cases_on `n = &(LENGTH args − 1)` >>
  srw_tac[][evaluate_APPEND, evaluate_def, do_app_def, find_code_def, FRONT_APPEND] >>
  simp [] >>
  imp_res_tac bvlPropsTheory.evaluate_IMP_LENGTH >>
  rev_full_simp_tac (srw_ss()++ARITH_ss) [] >>
  `LENGTH args' - 1 + 1 = LENGTH args'` by decide_tac >>
  `lookup p (dec_clock 1 s).code = SOME (n+2,exp)` by srw_tac[][] >>
  imp_res_tac evaluate_generic_app_full >>
  srw_tac[][] >>
  full_simp_tac (srw_ss()++ARITH_ss) [dec_clock_def] >>
  simp [evaluate_mk_cl_simpl]);

val evaluate_partial_app_fn = Q.prove (
  `!num_args args' num_args' prev_args tag num tag' l l' fvs exp code.
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
  srw_tac[][evaluate_def, generate_partial_app_closure_fn_def, mk_const_def, do_app_def] >>
  full_simp_tac (srw_ss()++ARITH_ss) [el_append2, evaluate_APPEND] >>
  srw_tac[][evaluate_def] >>
  qabbrev_tac `cl = Block tag (l'::num::Block tag' (CodePtr l::num_args'::fvs):: prev_args)` >>
  qspecl_then [`1`, `Block tag' (CodePtr l::num_args'::fvs)::(args' ++ [cl])`,
                       `LENGTH (args')`, `st with code := code`] assume_tac evaluate_genlist_vars >>
  full_simp_tac (srw_ss()++ARITH_ss) [ADD1] >>
  srw_tac[][evaluate_genlist_prev_args1_no_rev, Abbr `cl`, evaluate_def, do_app_def, find_code_def] >>
  full_simp_tac (srw_ss()++ARITH_ss) [ADD1] >>
  srw_tac[][FRONT_APPEND, TAKE_LENGTH_APPEND, bvlSemTheory.state_component_equality]);

(* -- *)

(* value relation *)

val code_installed_def = Define `
  code_installed aux code =
    EVERY (\(n,num_args,exp). lookup n code = SOME (num_args,exp)) aux`;

val code_installed_fromAList = Q.store_thm("code_installed_fromAList",
  `ALL_DISTINCT (MAP FST ls) ⇒ code_installed ls (fromAList ls)`,
  srw_tac[][code_installed_def,EVERY_MEM,FORALL_PROD,lookup_fromAList] >>
  metis_tac[ALOOKUP_ALL_DISTINCT_MEM])

val closure_code_installed_def = Define `
  closure_code_installed code exps_ps (env:closSem$v list) =
    EVERY (\((n,exp),p).
      n ≤ max_app ∧
      n ≠ 0 ∧
      ?aux c aux1.
        (compile_exps [exp] aux = ([c],aux1)) /\
        (lookup p code = SOME (n+1,SND (code_for_recc_case (LENGTH env + LENGTH exps_ps) n c))) /\
        code_installed aux1 code) exps_ps`

val (cl_rel_rules,cl_rel_ind,cl_rel_cases) = Hol_reln `
  ( num_args ≤ max_app ∧
    num_args ≠ 0 ∧
    every_Fn_SOME [x] ∧
    every_Fn_vs_SOME [x] ∧
    (compile_exps [x] aux = ([c],aux1)) /\
    code_installed aux1 code /\
    (lookup (p + num_stubs) code =
      SOME (num_args + 1:num,Let (GENLIST Var num_args++free_let (Var num_args) (LENGTH env)) c))
   ⇒
   cl_rel fs refs code
          (env,ys)
          (Closure (SOME p) [] env num_args x)
          (Block closure_tag (CodePtr (p + num_stubs) :: Number (&(num_args-1)) :: ys))) ∧
  ( num_args ≤ max_app ∧
    num_args ≠ 0 ∧
    every_Fn_SOME [x] ∧
    every_Fn_vs_SOME [x] ∧
    compile_exps [x] aux = ([c],aux1) /\
    code_installed aux1 code /\
    lookup (p + num_stubs) code =
      SOME (num_args + 1:num,Let (GENLIST Var (num_args+1)++free_let (Var num_args) (LENGTH env)) c)
    ⇒
    cl_rel fs refs code (env,ys)
           (Recclosure (SOME p) [] env [(num_args, x)] 0)
           (Block closure_tag (CodePtr (p + num_stubs) :: Number (&(num_args-1)) :: ys)))
    /\
    ((exps = MAP FST exps_ps) /\
     (ps = MAP SND exps_ps) /\ (ps = GENLIST (\n. loc + num_stubs + 2*n) (LENGTH exps_ps)) /\
     (rs = MAP (\((n,e),p). Block closure_tag [CodePtr p; Number (&(n-1)); RefPtr r]) exps_ps) /\
     ~(r IN fs) /\
     (FLOOKUP refs r = SOME (ValueArray (rs ++ ys))) /\
     1 < LENGTH exps /\ k < LENGTH exps /\
     every_Fn_SOME (MAP SND exps) ∧
     every_Fn_vs_SOME (MAP SND exps) ∧
     closure_code_installed code exps_ps env ==>
     cl_rel fs refs code (env,ys) (Recclosure (SOME loc) [] env exps k) (EL k rs))`;

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
  srw_tac[][add_args_def] >>
  srw_tac[][add_args_def]);

val get_num_args_def = Define `
  (get_num_args (Closure loc_opt args env num_args exp : closSem$v) =
    SOME num_args) ∧
  (get_num_args (Recclosure loc_opt args env funs i : closSem$v) =
    SOME (FST (EL i funs))) ∧
  (get_num_args _ = NONE)`;

val (v_rel_rules,v_rel_ind,v_rel_cases) = Hol_reln `
  (v_rel f refs code (Number n) (Number n))
  /\
  (v_rel f refs code (Word64 w) (Word64 w))
  /\
  (EVERY2 (v_rel f refs code) xs (ys:bvlSem$v list) ==>
   v_rel f refs code (Block t xs) (Block (clos_tag_shift t) ys))
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
   ~cl_rel f refs code (env,ys) (Word64 w) cl ∧
   ~cl_rel f refs code (env,ys) (RefPtr p) cl ∧
   ~cl_rel f refs code (env,ys) (Block tag xs) cl`,
  srw_tac[][cl_rel_cases]);

val add_args_F = Q.prove (
  `!cl args p i tag xs.
   add_args cl args ≠ SOME (RefPtr p) ∧
   add_args cl args ≠ SOME (Number i) ∧
   add_args cl args ≠ SOME (Word64 w) ∧
   add_args cl args ≠ SOME (Block tag xs)`,
  Cases_on `cl` >>
  srw_tac[][add_args_def]);

val v_rel_Unit = Q.store_thm("v_rel_Unit[simp]",
  `(v_rel f refs code Unit y ⇔ (y = Unit)) ∧
   (v_rel f refs code x Unit ⇔ (x = Unit))`,
  EVAL_TAC >> simp[v_rel_cases] >> EVAL_TAC >>
  srw_tac[][EQ_IMP_THM] >> full_simp_tac(srw_ss())[add_args_F,cl_rel_F] >>
  every_case_tac >> srw_tac[][] >> fsrw_tac[ARITH_ss][])

val v_rel_Boolv = Q.store_thm("v_rel_Boolv[simp]",
  `(v_rel f refs code (Boolv b) y ⇔ (y = Boolv b)) ∧
   (v_rel f refs code x (Boolv b) ⇔ (x = Boolv b))`,
  EVAL_TAC >> simp[v_rel_cases] >> EVAL_TAC >> simp[] >>
  srw_tac[][EQ_IMP_THM] >> full_simp_tac(srw_ss())[cl_rel_F,add_args_F] >>
  every_case_tac >> srw_tac[][] >> fsrw_tac[ARITH_ss][])

val v_rel_SIMP = LIST_CONJ
  [``v_rel f refs code (RefPtr p) y``
   |> SIMP_CONV (srw_ss()) [v_rel_cases, cl_rel_F, add_args_F],
   ``v_rel f refs code (Block tag xs) y``
   |> SIMP_CONV (srw_ss()) [v_rel_cases, cl_rel_F, add_args_F],
   ``v_rel f refs code (Number i) y``
   |> SIMP_CONV (srw_ss()) [v_rel_cases, cl_rel_F, add_args_F],
   ``v_rel f refs code (Word64 i) y``
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
  Induct \\ Cases_on `xs2` \\ full_simp_tac(srw_ss())[env_rel_def]);

val list_rel_IMP_env_rel = prove(
  ``!xs ys.
      LIST_REL (v_rel f refs code) xs ys ==>
      env_rel f refs code xs (ys ++ ts)``,
  Induct \\ Cases_on `ys` \\ full_simp_tac(srw_ss())[env_rel_def]
  \\ Cases_on `ts` \\ full_simp_tac(srw_ss())[env_rel_def]);

val env_rel_IMP_LENGTH = prove(
  ``!env1 env2.
      env_rel f refs code env1 env2 ==>
      LENGTH env1 <= LENGTH env2``,
  Induct \\ Cases_on `env2` \\ full_simp_tac(srw_ss())[env_rel_def]);

val LESS_LENGTH_env_rel_IMP = prove(
  ``!env env2 n.
      n < LENGTH env /\ env_rel f refs code env env2 ==>
      n < LENGTH env2 /\ v_rel f refs code (EL n env) (EL n env2)``,
  Induct \\ full_simp_tac(srw_ss())[LENGTH] \\ REPEAT STRIP_TAC
  \\ Cases_on `env2` \\ full_simp_tac(srw_ss())[env_rel_def]
  \\ Cases_on `n` \\ full_simp_tac(srw_ss())[]);

val env_rel_IMP_EL =
  LESS_LENGTH_env_rel_IMP |> SPEC_ALL |> UNDISCH
  |> CONJUNCT2 |> DISCH_ALL |> GEN_ALL

val state_rel_def = Define `
  state_rel f (s:'ffi closSem$state) (t:'ffi bvlSem$state) <=>
    (s.ffi = t.ffi) /\
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
    (lookup equality_location t.code = SOME equality_code) ∧
    (lookup block_equality_location t.code = SOME block_equality_code) ∧
    (lookup ToList_location t.code = SOME ToList_code) ∧
    (!name arity c.
      (FLOOKUP s.code name = SOME (arity,c)) ==>
      ?aux1 c2 aux2.
        (compile_exps [c] aux1 = ([c2],aux2)) /\
        (lookup (name + num_stubs) t.code = SOME (arity,c2)) /\
        code_installed aux2 t.code)`;

(* workaround for overloading bug - otherwise, this could be kept at
   head of script file, and its effect wouldn't be disturbed by definition
   above
*)
val _ = temp_overload_on ("ksrel", ``clos_knownProof$state_rel``)


val state_rel_globals = prove(
  ``state_rel f s t ⇒
    LIST_REL (OPTREL (v_rel f t.refs t.code)) s.globals t.globals``,
  srw_tac[][state_rel_def]);

val state_rel_clock = Q.store_thm ("state_rel_clock[simp]",
  `(!f s t. state_rel f s (t with clock := x) = state_rel f s t) ∧
   (!f s t. state_rel f (s with clock := x) t = state_rel f s t)`,
  srw_tac[][state_rel_def]);

val cl_rel_SUBMAP = Q.prove (
  `cl_rel f1 refs1 code (env,ys) x y ∧
   f1 ⊆ f2 /\ FDIFF refs1 f1 SUBMAP FDIFF refs2 f2 ==>
   cl_rel f2 refs2 code (env,ys) x y`,
  srw_tac[][cl_rel_cases]
  >- metis_tac []
  >- metis_tac []
  \\ DISJ2_TAC \\ Q.LIST_EXISTS_TAC [`exps_ps`,`r`] \\ full_simp_tac(srw_ss())[]
  \\ rev_full_simp_tac(srw_ss())[]
  \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ full_simp_tac(srw_ss())[] \\ STRIP_TAC
  \\ full_simp_tac(srw_ss())[FDIFF_def,SUBMAP_DEF,DRESTRICT_DEF,FLOOKUP_DEF]
  \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `r`) \\ full_simp_tac(srw_ss())[]);

val v_rel_SUBMAP = prove(
  ``!x y. v_rel f1 refs1 code x y ==>
      f1 SUBMAP f2 /\ FDIFF refs1 (FRANGE f1) SUBMAP FDIFF refs2 (FRANGE f2) ==>
      v_rel f2 refs2 code x y``,
  HO_MATCH_MP_TAC v_rel_ind \\ REPEAT STRIP_TAC
  \\ ONCE_REWRITE_TAC [v_rel_cases] \\ full_simp_tac(srw_ss())[]
  THEN1 (REPEAT (POP_ASSUM MP_TAC) \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ full_simp_tac(srw_ss())[])
  THEN1 (full_simp_tac(srw_ss())[SUBMAP_DEF,FLOOKUP_DEF])
  THEN1 (imp_res_tac SUBMAP_FRANGE_SUBSET >>
         imp_res_tac cl_rel_SUBMAP >>
         disj2_tac >>
         full_simp_tac(srw_ss())[ETA2_THM] >>
         metis_tac [])
  THEN1 (imp_res_tac cl_rel_SUBMAP >>
         disj2_tac >>
         full_simp_tac(srw_ss())[ETA2_THM] >>
         metis_tac [SUBMAP_FRANGE_SUBSET] ))
  |> SPEC_ALL |> MP_CANON;

val env_rel_SUBMAP = prove(
  ``!env1 env2.
      env_rel f1 refs1 code env1 env2 /\
      f1 SUBMAP f2 /\ FDIFF refs1 (FRANGE f1) SUBMAP FDIFF refs2 (FRANGE f2) ==>
      env_rel f2 refs2 code env1 env2``,
  Induct \\ Cases_on `env2` \\ full_simp_tac(srw_ss())[env_rel_def]
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC v_rel_SUBMAP) |> GEN_ALL;

val cl_rel_NEW_REF = Q.prove (
  `!x y. cl_rel f1 refs1 code (env,ys) x y ==> ~(r IN FDOM refs1) ==>
         cl_rel f1 (refs1 |+ (r,t)) code (env,ys) x y`,
  srw_tac[][cl_rel_cases]
  >- metis_tac []
  >- metis_tac []
  \\ DISJ2_TAC \\ Q.LIST_EXISTS_TAC [`exps_ps`,`r'`] \\ full_simp_tac(srw_ss())[]
  \\ rev_full_simp_tac(srw_ss())[]
  \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[FDIFF_def,SUBMAP_DEF,DRESTRICT_DEF,FLOOKUP_DEF]
  \\ full_simp_tac(srw_ss())[FAPPLY_FUPDATE_THM] \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[]);

val v_rel_NEW_REF = prove(
  ``!x y. v_rel f1 refs1 code x y ==> ~(r IN FDOM refs1) ==>
          v_rel f1 (refs1 |+ (r,t)) code x y``,
  HO_MATCH_MP_TAC v_rel_ind \\ REPEAT STRIP_TAC
  \\ ONCE_REWRITE_TAC [v_rel_cases] \\ full_simp_tac(srw_ss())[]
  THEN1 (REPEAT (POP_ASSUM MP_TAC) \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ full_simp_tac(srw_ss())[])
  THEN1 (imp_res_tac cl_rel_NEW_REF >>
         disj2_tac >>
         full_simp_tac(srw_ss())[ETA2_THM] >>
         metis_tac [])
  THEN1 (imp_res_tac cl_rel_NEW_REF >>
         disj2_tac >>
         full_simp_tac(srw_ss())[ETA2_THM] >>
         metis_tac [] ))
  |> SPEC_ALL |> MP_CANON;

val cl_rel_UPDATE_REF = prove(
  ``!x y. cl_rel f1 refs1 code (env,ys) x y ==>
          (r IN f1) ==>
          cl_rel f1 (refs1 |+ (r,t)) code (env,ys) x y``,
  srw_tac[][cl_rel_cases]
  >- metis_tac []
  >- metis_tac []
  \\ DISJ2_TAC \\ Q.LIST_EXISTS_TAC [`exps_ps`,`r'`] \\ full_simp_tac(srw_ss())[]
  \\ rev_full_simp_tac(srw_ss())[]
  \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[FDIFF_def,SUBMAP_DEF,DRESTRICT_DEF,FLOOKUP_DEF]
  \\ full_simp_tac(srw_ss())[FAPPLY_FUPDATE_THM] \\ SRW_TAC [] []
  \\ full_simp_tac(srw_ss())[FRANGE_DEF] \\ METIS_TAC []);

val v_rel_UPDATE_REF = prove(
  ``!x y. v_rel f1 refs1 code x y ==>
          (r IN FRANGE f1) ==>
          v_rel f1 (refs1 |+ (r,t)) code x y``,
  HO_MATCH_MP_TAC v_rel_ind \\ REPEAT STRIP_TAC
  \\ ONCE_REWRITE_TAC [v_rel_cases] \\ full_simp_tac(srw_ss())[]
  THEN1 (REPEAT (POP_ASSUM MP_TAC) \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ full_simp_tac(srw_ss())[])
  THEN1 (imp_res_tac cl_rel_UPDATE_REF >>
         disj2_tac >>
         full_simp_tac(srw_ss())[ETA2_THM] >>
         metis_tac [])
  THEN1 (imp_res_tac cl_rel_UPDATE_REF >>
         disj2_tac >>
         full_simp_tac(srw_ss())[ETA2_THM] >>
         metis_tac [] ))
  |> SPEC_ALL |> MP_CANON;

val OPTREL_v_rel_NEW_REF = prove(
  ``OPTREL (v_rel f1 refs1 code) x y /\ ~(r IN FDOM refs1) ==>
    OPTREL (v_rel f1 (refs1 |+ (r,t)) code) x y``,
  Cases_on `x` \\ Cases_on `y` \\ full_simp_tac(srw_ss())[OPTREL_def,v_rel_NEW_REF]);

val OPTREL_v_rel_UPDATE_REF = prove(
  ``OPTREL (v_rel f1 refs1 code) x y /\ r IN FRANGE f1 ==>
    OPTREL (v_rel f1 (refs1 |+ (r,t)) code) x y``,
  Cases_on `x` \\ Cases_on `y` \\ full_simp_tac(srw_ss())[OPTREL_def,v_rel_UPDATE_REF]);

val env_rel_NEW_REF = prove(
  ``!x y.
      env_rel f1 refs1 code x y /\ ~(r IN FDOM refs1) ==>
      env_rel f1 (refs1 |+ (r,t)) code x y``,
  Induct \\ Cases_on `y` \\ full_simp_tac(srw_ss())[env_rel_def] \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC v_rel_NEW_REF \\ full_simp_tac(srw_ss())[]);

val cl_rel_NEW_F = prove(
  ``!x y.
      cl_rel f2 t2.refs t2.code (env,ys) x y ==>
      ~(qq IN FDOM t2.refs) ==>
      cl_rel (qq INSERT f2) t2.refs t2.code (env,ys) x y``,
  srw_tac[][cl_rel_cases]
  >- metis_tac []
  >- metis_tac []
  \\ DISJ2_TAC \\ Q.LIST_EXISTS_TAC [`exps_ps`,`r`] \\ full_simp_tac(srw_ss())[]
  \\ strip_tac >> full_simp_tac(srw_ss())[FLOOKUP_DEF])

val v_rel_NEW_F = prove(
  ``!x y.
      v_rel f2 t2.refs t2.code x y ==>
      ~(pp IN FDOM f2) ==>
      ~(qq IN FDOM t2.refs) ==>
      v_rel (f2 |+ (pp,qq)) t2.refs t2.code x y``,
  HO_MATCH_MP_TAC v_rel_ind \\ REPEAT STRIP_TAC
  \\ ONCE_REWRITE_TAC [v_rel_cases] \\ full_simp_tac(srw_ss())[]
  THEN1 (REPEAT (POP_ASSUM MP_TAC) \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ full_simp_tac(srw_ss())[])
  THEN1 (full_simp_tac(srw_ss())[FLOOKUP_UPDATE] \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[FLOOKUP_DEF])
  THEN1 (imp_res_tac cl_rel_NEW_F >>
         disj2_tac >>
         full_simp_tac(srw_ss())[ETA2_THM,DOMSUB_NOT_IN_DOM] >>
         metis_tac [])
  THEN1 (imp_res_tac cl_rel_NEW_F >>
         disj2_tac >>
         full_simp_tac(srw_ss())[ETA2_THM,DOMSUB_NOT_IN_DOM] >>
         metis_tac [] ))
  |> SPEC_ALL |> MP_CANON;

val OPTREL_v_rel_NEW_F = prove(
  ``OPTREL (v_rel f2 t2.refs t2.code) x y ==>
    ~(pp IN FDOM f2) ==>
    ~(qq IN FDOM t2.refs) ==>
    OPTREL (v_rel (f2 |+ (pp,qq)) t2.refs t2.code) x y``,
  Cases_on `x` \\ Cases_on `y` \\ full_simp_tac(srw_ss())[OPTREL_def]
  \\ METIS_TAC [v_rel_NEW_F]) |> MP_CANON;

(* semantic functions respect relation *)

val v_to_list = Q.prove(
  `∀v l v'.
   v_to_list v = SOME l ∧
   v_rel f r c v v'
   ⇒
   ∃l'. v_to_list v' = SOME l' ∧
        LIST_REL (v_rel f r c) l l'`,
  ho_match_mp_tac closSemTheory.v_to_list_ind >>
  srw_tac[][v_rel_SIMP,closSemTheory.v_to_list_def,bvlSemTheory.v_to_list_def] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
  srw_tac[][bvlSemTheory.v_to_list_def] >> res_tac >> srw_tac[][]);

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
  Cases_on`op`>>srw_tac[][closSemTheory.do_app_def,bvlSemTheory.do_app_def]
  >- (
    imp_res_tac state_rel_globals >>
    full_simp_tac(srw_ss())[LIST_REL_EL_EQN] >>
    BasicProvers.EVERY_CASE_TAC >> rev_full_simp_tac(srw_ss())[get_global_def]>>
    first_x_assum(fn th => first_x_assum(strip_assume_tac o MATCH_MP th))>> srw_tac[][] >>
    rev_full_simp_tac(srw_ss())[optionTheory.OPTREL_def] )
  >- (
    imp_res_tac state_rel_globals >>
    full_simp_tac(srw_ss())[LIST_REL_EL_EQN] >>
    BasicProvers.EVERY_CASE_TAC >> rev_full_simp_tac(srw_ss())[get_global_def]>>
    srw_tac[][v_rel_SIMP] >>
    first_x_assum(fn th => first_x_assum(strip_assume_tac o MATCH_MP th))>> srw_tac[][] >>
    rev_full_simp_tac(srw_ss())[OPTREL_def] >>
    full_simp_tac(srw_ss())[state_rel_def] >>
    MATCH_MP_TAC EVERY2_LUPDATE_same >>
    rev_full_simp_tac(srw_ss())[OPTREL_def] )
  >- (
    every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
    full_simp_tac(srw_ss())[state_rel_def,OPTREL_def] )
  >- (
    every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
    full_simp_tac(srw_ss())[state_rel_def,OPTREL_def] )
  >- (
    every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
    full_simp_tac(srw_ss())[state_rel_def,OPTREL_def] )
  >- (Cases_on`v` \\ every_case_tac \\ fs[v_rel_SIMP] \\ rw[])
  >- (every_case_tac \\ full_simp_tac(srw_ss())[])
  >- (
    Cases_on`xs`>>full_simp_tac(srw_ss())[v_rel_SIMP]>>
    Cases_on`t`>>full_simp_tac(srw_ss())[v_rel_SIMP]>>
    Cases_on`h`>>full_simp_tac(srw_ss())[v_rel_SIMP]>>
    Cases_on`t'`>>full_simp_tac(srw_ss())[v_rel_SIMP]>>
    Cases_on`h'`>>full_simp_tac(srw_ss())[v_rel_SIMP]>>
    every_case_tac >> full_simp_tac(srw_ss())[v_rel_SIMP] >> srw_tac[][]>>
    full_simp_tac(srw_ss())[LIST_REL_EL_EQN] >> rev_full_simp_tac(srw_ss())[])
  >- (
    Cases_on`xs`>>full_simp_tac(srw_ss())[v_rel_SIMP]>>
    Cases_on`t`>>full_simp_tac(srw_ss())[v_rel_SIMP]>>
    Cases_on`h`>>full_simp_tac(srw_ss())[v_rel_SIMP]>>
    rw[v_rel_SIMP] >> fs[LIST_REL_EL_EQN])
  >- (
    Cases_on`xs`>>full_simp_tac(srw_ss())[v_rel_SIMP]>>
    Cases_on`t`>>full_simp_tac(srw_ss())[v_rel_SIMP]>>
    Cases_on`h`>>full_simp_tac(srw_ss())[v_rel_SIMP]>>
    rw[v_rel_SIMP] >> fs[LIST_REL_EL_EQN]>>
    every_case_tac \\ fs[v_rel_SIMP] \\ rw[]
    \\ full_simp_tac(srw_ss())[state_rel_def] >> res_tac >> full_simp_tac(srw_ss())[v_rel_SIMP] >>
    rw[] \\ fs[LIST_REL_EL_EQN])
  >- (
    Cases_on`xs`>>full_simp_tac(srw_ss())[v_rel_SIMP]>>
    Cases_on`t`>>full_simp_tac(srw_ss())[v_rel_SIMP]>>
    Cases_on`h`>>full_simp_tac(srw_ss())[v_rel_SIMP]>>
    rw[v_rel_SIMP] >> fs[LIST_REL_EL_EQN]>>
    every_case_tac \\ fs[v_rel_SIMP] \\ rw[]
    \\ full_simp_tac(srw_ss())[state_rel_def] >> res_tac >> full_simp_tac(srw_ss())[v_rel_SIMP] >>
    rw[] \\ fs[LIST_REL_EL_EQN])
  >- (
    Cases_on`xs`>>full_simp_tac(srw_ss())[v_rel_SIMP]>>
    Cases_on`t`>>full_simp_tac(srw_ss())[v_rel_SIMP]>>
    Cases_on`h`>>full_simp_tac(srw_ss())[v_rel_SIMP]>>
    Cases_on`t'`>>full_simp_tac(srw_ss())[v_rel_SIMP]>>
    Cases_on`h'`>>full_simp_tac(srw_ss())[v_rel_SIMP]>>
    rw[v_rel_SIMP] >> fs[LIST_REL_EL_EQN]>>
    every_case_tac \\ fs[v_rel_SIMP] \\ rw[]
    \\ full_simp_tac(srw_ss())[state_rel_def] >> res_tac >> full_simp_tac(srw_ss())[v_rel_SIMP] >>
    rw[] \\ fs[LIST_REL_EL_EQN] >>
    rw[] \\ fs[])
  >- (
    every_case_tac >> full_simp_tac(srw_ss())[v_rel_SIMP] >> srw_tac[][v_rel_SIMP] >>
    imp_res_tac v_to_list >> full_simp_tac(srw_ss())[] >> srw_tac[][] )
  >- (
    Cases_on`xs`\\fs[]
    \\ Cases_on`t`\\fs[]
    \\ Cases_on`h`\\fs[]
    \\ rw[] \\ fs[v_rel_SIMP]
    \\ metis_tac[clos_tag_shift_inj,LIST_REL_LENGTH])
  >- (
    Cases_on`xs`\\fs[]
    \\ Cases_on`t`\\fs[]
    \\ Cases_on`h`\\fs[]
    \\ rw[] \\ fs[v_rel_SIMP]
    \\ metis_tac[clos_tag_shift_inj,LIST_REL_LENGTH])
  >- ( every_case_tac >> fsrw_tac[][v_rel_SIMP] >> srw_tac[][v_rel_SIMP] >>
       metis_tac[clos_tag_shift_inj])
  >- (
    Cases_on`xs`>>full_simp_tac(srw_ss())[v_rel_SIMP]>>
    Cases_on`h`>>full_simp_tac(srw_ss())[v_rel_SIMP]>>
    Cases_on`t`>>full_simp_tac(srw_ss())[v_rel_SIMP]>>
    Cases_on`h`>>full_simp_tac(srw_ss())[v_rel_SIMP]>>
    every_case_tac >> full_simp_tac(srw_ss())[v_rel_SIMP] >> srw_tac[][v_rel_SIMP] >>
    full_simp_tac(srw_ss())[state_rel_def] >> res_tac >> full_simp_tac(srw_ss())[v_rel_SIMP] >>
    srw_tac[][] >> full_simp_tac(srw_ss())[LIST_REL_EL_EQN] >>srw_tac[][]>>full_simp_tac(srw_ss())[] >>
    first_x_assum match_mp_tac >> intLib.COOPER_TAC)
  >- (
    Cases_on`xs`>>full_simp_tac(srw_ss())[v_rel_SIMP]>>
    Cases_on`t`>>full_simp_tac(srw_ss())[v_rel_SIMP]>>
    Cases_on`h`>>full_simp_tac(srw_ss())[v_rel_SIMP]>>
    Cases_on`t'`>>full_simp_tac(srw_ss())[v_rel_SIMP]>>
    Cases_on`h'`>>full_simp_tac(srw_ss())[v_rel_SIMP]>>
    every_case_tac >> full_simp_tac(srw_ss())[v_rel_SIMP] >> srw_tac[][v_rel_SIMP] >>
    full_simp_tac(srw_ss())[state_rel_def] >> res_tac >> full_simp_tac(srw_ss())[v_rel_SIMP] >>
    srw_tac[][] >> full_simp_tac(srw_ss())[LIST_REL_EL_EQN] >>srw_tac[][]>>full_simp_tac(srw_ss())[] >>
    first_x_assum match_mp_tac >> intLib.COOPER_TAC)
  >- ( every_case_tac >> full_simp_tac(srw_ss())[v_rel_SIMP] >> srw_tac[][v_rel_SIMP] )
  >- ( every_case_tac >> full_simp_tac(srw_ss())[v_rel_SIMP] >> srw_tac[][v_rel_SIMP] )
  >- ( every_case_tac >> full_simp_tac(srw_ss())[v_rel_SIMP] >> srw_tac[][v_rel_SIMP] )
  >> (
    TRY(Cases_on`w`)>>fs[v_rel_SIMP]>>
    Cases_on`xs`>>full_simp_tac(srw_ss())[v_rel_SIMP]>>
    Cases_on`h`>>full_simp_tac(srw_ss())[v_rel_SIMP]>>
    Cases_on`t`>>full_simp_tac(srw_ss())[v_rel_SIMP]>>
    TRY(Cases_on`h`>>full_simp_tac(srw_ss())[v_rel_SIMP])>>
    TRY(Cases_on`t'`>>full_simp_tac(srw_ss())[v_rel_SIMP])>>
    srw_tac[][v_rel_SIMP] >>
    last_x_assum mp_tac >>
    srw_tac[][v_rel_SIMP] >>
    srw_tac[][v_rel_SIMP] >>
    every_case_tac \\ fs[] \\ rw[] \\ fs[v_rel_SIMP]));

val do_app_err = Q.prove(
  `do_app op xs s1 = Rerr err ∧
   err ≠ Rabort Rtype_error ∧
   state_rel f s1 t1 ∧
   LIST_REL (v_rel f t1.refs t1.code) xs ys ∧
   op ≠ ToList ∧ op ≠ Equal
   ⇒
   ∃e. do_app (compile_op op) ys t1 = Rerr e ∧
       exc_rel (v_rel f t1.refs t1.code) err e`,
  Cases_on`op`>>srw_tac[][closSemTheory.do_app_def,bvlSemTheory.do_app_def]
  >- (
    imp_res_tac state_rel_globals >>
    every_case_tac >> full_simp_tac(srw_ss())[get_global_def,LIST_REL_EL_EQN] >>
    rev_full_simp_tac(srw_ss())[OPTREL_def] >> res_tac >> full_simp_tac(srw_ss())[])
  >- (
    imp_res_tac state_rel_globals >>
    every_case_tac >> full_simp_tac(srw_ss())[get_global_def,LIST_REL_EL_EQN] >>
    rev_full_simp_tac(srw_ss())[OPTREL_def] >> res_tac >> full_simp_tac(srw_ss())[])
  >- ( every_case_tac >> full_simp_tac(srw_ss())[] )
  >- (
    spose_not_then strip_assume_tac
    \\ every_case_tac >> full_simp_tac(srw_ss())[] )
  >- (
    spose_not_then strip_assume_tac
    \\ every_case_tac >> full_simp_tac(srw_ss())[] )
  >- (
    spose_not_then strip_assume_tac
    \\ every_case_tac >> full_simp_tac(srw_ss())[] )
  >- (
    Cases_on`xs`\\fs[]
    \\ Cases_on`t`\\fs[]
    \\ Cases_on`h`\\fs[]
    \\ Cases_on`t'`\\fs[]
    \\ Cases_on`h'`\\fs[]
    \\ rw[]
    \\ every_case_tac \\ fs[])
  >- (
    Cases_on`xs`>>full_simp_tac(srw_ss())[]>>srw_tac[][]>>
    Cases_on`t`>>full_simp_tac(srw_ss())[v_rel_SIMP]>>srw_tac[][]>-
    (Cases_on`h`>>full_simp_tac(srw_ss())[v_rel_SIMP]>>srw_tac[][])>>
    Cases_on`h`>>full_simp_tac(srw_ss())[v_rel_SIMP]>>srw_tac[][]>>
    Cases_on`h'`>>full_simp_tac(srw_ss())[v_rel_SIMP]>>srw_tac[][]>>
    Cases_on`t'`>>full_simp_tac(srw_ss())[v_rel_SIMP]>>srw_tac[][]>>
    every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][])
  >- ( every_case_tac >> full_simp_tac(srw_ss())[] )
  >- ( every_case_tac >> full_simp_tac(srw_ss())[] )
  >- ( every_case_tac >> fsrw_tac[][LET_THM])
  >- (
    Cases_on`xs`>>fsrw_tac[][]>>srw_tac[][]>>
    Cases_on`h`>>fsrw_tac[][]>>srw_tac[][]>>
    Cases_on`t`>>fsrw_tac[][]>>srw_tac[][]>>
    Cases_on`h`>>fsrw_tac[][]>>srw_tac[][]>>
    Cases_on`t'`>>fsrw_tac[][]>>srw_tac[][]>>
    every_case_tac >> fsrw_tac[][LET_THM])
  >- (
    Cases_on`xs`>>fsrw_tac[][]>>srw_tac[][]>>
    Cases_on`t`>>fsrw_tac[][]>>srw_tac[][]>>
    Cases_on`h`>>fsrw_tac[][]>>srw_tac[][]>>
    Cases_on`t'`>>fsrw_tac[][]>>srw_tac[][]>>
    Cases_on`h'`>>fsrw_tac[][]>>srw_tac[][]>>
    every_case_tac >> fsrw_tac[][LET_THM])
  >- (
    Cases_on`xs`>>fsrw_tac[][]>>srw_tac[][]>>
    Cases_on`t`>>fsrw_tac[][]>>srw_tac[][]>>
    Cases_on`h`>>fsrw_tac[][]>>srw_tac[][]>>
    Cases_on`t'`>>fsrw_tac[][]>>srw_tac[][]>>
    Cases_on`h'`>>fsrw_tac[][]>>srw_tac[][]>>
    Cases_on`t`>>fsrw_tac[][]>>srw_tac[][]>>
    Cases_on`h`>>fsrw_tac[][]>>srw_tac[][]>>
    every_case_tac >> fsrw_tac[][LET_THM])
  >- ( every_case_tac >> full_simp_tac(srw_ss())[] )
  >- ( every_case_tac >> full_simp_tac(srw_ss())[] )
  >- ( every_case_tac >> full_simp_tac(srw_ss())[] )
  >- ( every_case_tac >> full_simp_tac(srw_ss())[LET_THM] )
  >- (
    Cases_on`xs`>>fsrw_tac[][]>>srw_tac[][]>>
    Cases_on`t`>>fsrw_tac[][]>>srw_tac[][]>>
    Cases_on`h`>>fsrw_tac[][]>>srw_tac[][]>>
    Cases_on`t'`>>fsrw_tac[][]>>srw_tac[][]>>
    Cases_on`h'`>>fsrw_tac[][]>>srw_tac[][]>>
    every_case_tac >> fsrw_tac[][LET_THM])
  >- ( every_case_tac >> full_simp_tac(srw_ss())[LET_THM] )
  >- (
    Cases_on`xs`>>full_simp_tac(srw_ss())[]>>srw_tac[][]>>
    Cases_on`h`>>full_simp_tac(srw_ss())[]>>srw_tac[][]>>
    Cases_on`t`>>full_simp_tac(srw_ss())[]>>srw_tac[][]>>
    Cases_on`h`>>full_simp_tac(srw_ss())[]>>srw_tac[][]>>
    every_case_tac >> full_simp_tac(srw_ss())[])
  >- (
    Cases_on`xs`>>full_simp_tac(srw_ss())[]>>srw_tac[][]>>
    Cases_on`h`>>full_simp_tac(srw_ss())[]>>srw_tac[][]>>
    Cases_on`t`>>full_simp_tac(srw_ss())[]>>srw_tac[][]>>
    Cases_on`h`>>full_simp_tac(srw_ss())[]>>srw_tac[][]>>
    Cases_on`t'`>>full_simp_tac(srw_ss())[]>>srw_tac[][]>>
    every_case_tac >> full_simp_tac(srw_ss())[])
  >- (
    every_case_tac >> full_simp_tac(srw_ss())[v_rel_SIMP] >> srw_tac[][] >>
    rev_full_simp_tac(srw_ss())[state_rel_def] >> res_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >> full_simp_tac(srw_ss())[] >>
    srw_tac[][] >> full_simp_tac(srw_ss())[])
  >- ( every_case_tac >> full_simp_tac(srw_ss())[] )
  >> (
    TRY(Cases_on`w`\\fs[])>>
    Cases_on`xs`>>full_simp_tac(srw_ss())[]>>
    Cases_on`h`>>full_simp_tac(srw_ss())[]>>
    Cases_on`t`>>full_simp_tac(srw_ss())[]>>
    TRY(Cases_on`h`>>full_simp_tac(srw_ss())[])>>
    TRY(Cases_on`t'`>>full_simp_tac(srw_ss())[])>>
    every_case_tac >> full_simp_tac(srw_ss())[] ));

val list_to_v_def = Define`
  list_to_v [] = bvlSem$Block nil_tag [] ∧
  list_to_v (h::t) = Block cons_tag [h; list_to_v t]`;

val list_to_v = Q.prove(
  `∀vs ws.
     LIST_REL (v_rel f r c) vs ws ⇒
     v_rel f r c (list_to_v vs) (list_to_v ws)`,
  Induct >> simp[closSemTheory.list_to_v_def,list_to_v_def,v_rel_SIMP,PULL_EXISTS])

val do_eq_def = tDefine"do_eq"`
  (do_eq (CodePtr _) _ = Eq_type_error) ∧
  (do_eq _ (CodePtr _) = Eq_type_error) ∧
  (do_eq (Number n1) (Number n2) = (Eq_val (n1 = n2))) ∧
  (do_eq (Number _) _ = Eq_type_error) ∧
  (do_eq _ (Number _) = Eq_type_error) ∧
  (do_eq (Word64 w1) (Word64 w2) = (Eq_val (w1 = w2))) ∧
  (do_eq (Word64 _) _ = Eq_type_error) ∧
  (do_eq _ (Word64 _) = Eq_type_error) ∧
  (do_eq (RefPtr n1) (RefPtr n2) = (Eq_val (n1 = n2))) ∧
  (do_eq (RefPtr _) _ = Eq_type_error) ∧
  (do_eq _ (RefPtr _) = Eq_type_error) ∧
  (do_eq (Block t1 l1) (Block t2 l2) =
   if (t1 = closure_tag) ∨ (t2 = closure_tag) ∨ (t1 = partial_app_tag) ∨ (t2 = partial_app_tag)
   then Eq_val T
   else if (t1 = t2) ∧ (LENGTH l1 = LENGTH l2)
        then do_eq_list l1 l2
        else Eq_val F) ∧
  (do_eq_list [] [] = Eq_val T) ∧
  (do_eq_list (v1::vs1) (v2::vs2) =
   case do_eq v1 v2 of
   | Eq_val T => do_eq_list vs1 vs2
   | Eq_val F => Eq_val F
   | bad => bad) ∧
  (do_eq_list _ _ = Eq_val F)`
  (WF_REL_TAC `measure (\x. case x of INL (v1,v2) => v_size v1 | INR (vs1,vs2) => v1_size vs1)`);
val _ = export_rewrites["do_eq_def"];

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
   srw_tac[][]
   >- (srw_tac[][closSemTheory.do_eq_def] >>
       Cases_on `x` >>
       full_simp_tac(srw_ss())[v_rel_SIMP] >> full_simp_tac(srw_ss())[add_args_def] >> srw_tac[][] >>
       Cases_on `y` >>
       full_simp_tac(srw_ss())[v_rel_SIMP] >> full_simp_tac(srw_ss())[add_args_def] >> srw_tac[][] >>
       rev_full_simp_tac(srw_ss())[] >>
       imp_res_tac LIST_REL_LENGTH >>
       full_simp_tac(srw_ss())[closure_tag_def,partial_app_tag_def,clos_tag_shift_def] >>
       BasicProvers.EVERY_CASE_TAC >>
       rev_full_simp_tac (srw_ss()++ARITH_ss) [] >>
       full_simp_tac(srw_ss())[INJ_DEF, FLOOKUP_DEF] >>
       metis_tac [])
  >- full_simp_tac(srw_ss())[closSemTheory.do_eq_def]
  >- (res_tac >>
      srw_tac[][closSemTheory.do_eq_def] >>
      Cases_on `do_eq x y` >>
      full_simp_tac(srw_ss())[] >>
      qpat_assum `X = do_eq y'' y'''` (mp_tac o GSYM) >>
      srw_tac[][])
  >- full_simp_tac(srw_ss())[closSemTheory.do_eq_def]
  >- full_simp_tac(srw_ss())[closSemTheory.do_eq_def]);

val do_eq_ind = theorem"do_eq_ind";

val do_eq_sym = Q.prove(
  `(∀x y. do_eq x y = do_eq y x) ∧
   (∀x y. do_eq_list x y = do_eq_list y x)`,
  ho_match_mp_tac do_eq_ind >> simp[] >>
  conj_tac >- ( gen_tac >> Cases >> srw_tac[][] ) >>
  conj_tac >- METIS_TAC[] >>
  conj_tac >- METIS_TAC[] >>
  conj_tac >- (
    rpt gen_tac >> strip_tac >>
    IF_CASES_TAC >> full_simp_tac(srw_ss())[] >>
    srw_tac[][] >> full_simp_tac(srw_ss())[] ) >>
  srw_tac[][] >>
  every_case_tac >> full_simp_tac(srw_ss())[])

val do_eq_list_T_every = Q.store_thm("do_eq_list_T_every",
  `∀vs1 vs2. do_eq_list vs1 vs2 = Eq_val T ⇔ LIST_REL (λv1 v2. do_eq v1 v2 = Eq_val T) vs1 vs2`,
  Induct \\ simp[do_eq_def]
  \\ Cases_on`vs2`\\ simp[do_eq_def]
  \\ srw_tac[][]
  \\ every_case_tac \\  full_simp_tac(srw_ss())[]);

(* correctness of implemented primitives *)

val ToList = Q.prove(
  `∀vs ws s.
     lookup ToList_location s.code = SOME ToList_code ∧
     LENGTH vs ≤ s.clock ⇒
   evaluate ([SND ToList_code],
             [Block t (vs++ws); Number &(LENGTH vs); list_to_v ws],
              s)
     = (Rval [list_to_v (vs++ws)], dec_clock (LENGTH vs) s)`,
  ho_match_mp_tac SNOC_INDUCT >>
  conj_tac >- (
    simp[ToList_code_def,bvlSemTheory.evaluate_def,bvlSemTheory.do_app_def] ) >>
  srw_tac[][] >>
  simp[ToList_code_def,bvlSemTheory.evaluate_def,bvlSemTheory.do_app_def] >>
  `&SUC (LENGTH vs) - 1 = &LENGTH vs` by ARITH_TAC >> simp[] >>
  simp[bvlSemTheory.find_code_def] >>
  `ToList_code = (3,SND ToList_code)` by simp[ToList_code_def] >>
  pop_assum SUBST1_TAC >> simp[] >>
  simp[SNOC_APPEND] >>
  first_x_assum(qspecl_then[`[x] ++ ws`,`dec_clock 1 s`]mp_tac) >>
  impl_tac >- simp[dec_clock_def] >>
  simp[list_to_v_def,EL_APPEND1,EL_LENGTH_APPEND,dec_clock_def,ADD1]);

val eq_res_def = Define`
  eq_res (Eq_val b) = Rval [bvlSem$Boolv b] ∧
  eq_res _ = Rerr (Rabort Rtype_error)`;
val _ = export_rewrites["eq_res_def"];

val eq_res_not_timeout = Q.prove(
  `eq_res x ≠ Rerr (Rabort Rtimeout_error)`,
  Cases_on`x`>>simp[])

val evaluate_check_closure = Q.prove(
  `n < LENGTH env ∧
   EL n env = bvlSem$Block t vs
   ⇒
   evaluate ([check_closure n e],env,s) =
   if t = closure_tag ∨ t = partial_app_tag then
     (eq_res (Eq_val T),s)
   else
     evaluate ([e],env,s)`,
  srw_tac[][check_closure_def,bvlSemTheory.evaluate_def,bvlSemTheory.do_app_def] >>
  full_simp_tac(srw_ss())[])

val s = ``s:'ffi bvlSem$state``

val equality = Q.prove(
  `(∀v1 v2 ^s.
     lookup equality_location s.code = SOME equality_code ∧
     lookup block_equality_location s.code = SOME block_equality_code ∧
     (do_eq v1 v2 ≠ Eq_type_error) ⇒
     ∃ck.
     evaluate ([SND equality_code], [v1;v2], inc_clock ck s)
       = (eq_res (do_eq v1 v2),s)) ∧
   (∀v1 v2 t vs1 vs2 ^s.
     lookup equality_location s.code = SOME equality_code ∧
     lookup block_equality_location s.code = SOME block_equality_code ∧
     (do_eq_list vs1 vs2 = Eq_val T) ∧
     (do_eq_list v1 v2 ≠ Eq_type_error) ∧
     LENGTH v1 = LENGTH v2 ⇒
     ∃ck.
     evaluate ([SND block_equality_code],
               [Block t (vs1++v1);
                Block t (vs2++v2);
                Number(&LENGTH (vs1++v1));
                Number(&LENGTH vs2)],
               inc_clock ck s)
       = (eq_res (do_eq_list v1 v2),s))`,
  ho_match_mp_tac do_eq_ind >> simp[] >>
  conj_tac >- (
    srw_tac[][] >>
    simp[equality_code_def,bvlSemTheory.evaluate_def,bvlSemTheory.do_app_def] >>
    qexists_tac`0`>>simp[inc_clock_def]>>METIS_TAC[]) >>
  conj_tac >- (
    srw_tac[][] >>
    simp[equality_code_def,bvlSemTheory.evaluate_def,bvlSemTheory.do_app_def] >>
    qexists_tac`0`>>simp[inc_clock_def]>>METIS_TAC[]) >>
  conj_tac >- (
    srw_tac[][] >>
    simp[equality_code_def,bvlSemTheory.evaluate_def,bvlSemTheory.do_app_def] >>
    qexists_tac`0`>>simp[inc_clock_def]) >>
  conj_tac >- (
    rpt gen_tac >> strip_tac >>
    rpt gen_tac >> strip_tac >>
    simp[equality_code_def,bvlSemTheory.evaluate_def,bvlSemTheory.do_app_def] >>
    (* TODO: why does simp[evaluate_check_closure] not work? *)
    qpat_abbrev_tac`env = [Block t1 v1;x]` >>
    `0 < LENGTH env ∧ 1 < LENGTH env` by simp[Abbr`env`] >>
    `EL 0 env = Block t1 v1 ∧ EL 1 env = Block t2 v2` by simp[Abbr`env`] >>
    simp[evaluate_check_closure |> GEN_ALL
      |> Q.SPECL[`v1`,`t1`,`s`,`0`,`env`,`e`]
      |> ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]
      |> UNDISCH |> UNDISCH] >>
    simp[evaluate_check_closure |> GEN_ALL
      |> Q.SPECL[`v2`,`t2`,`s`,`1`,`env`,`e`]
      |> ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]
      |> UNDISCH |> UNDISCH] >>
    Cases_on`t1=closure_tag ∨ t1 = partial_app_tag` >- (
      simp[] >> qexists_tac`0`>>simp[] ) >> simp[] >>
    Cases_on`t2=closure_tag ∨ t2 = partial_app_tag` >- (
      simp[] >> qexists_tac`0`>>simp[] ) >> simp[] >> full_simp_tac(srw_ss())[] >>
    simp[equality_code_def,bvlSemTheory.evaluate_def,bvlSemTheory.do_app_def,Abbr`env`] >>
    reverse(Cases_on`t1=t2 ∧ LENGTH v1=LENGTH v2`)>>simp[]>-(
      qexists_tac`0`>>simp[]) >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
    simp[find_code_def] >>
    `block_equality_code = (4,SND block_equality_code)` by simp[block_equality_code_def] >>
    pop_assum SUBST1_TAC >> simp[] >>
    first_x_assum(qspecl_then[`t1`,`[]`,`[]`,`s`]mp_tac) >>
    impl_tac >- simp[] >> strip_tac >>
    qexists_tac`ck+1` >>
    full_simp_tac(srw_ss())[dec_clock_def,inc_clock_def]>>
    simp[] >> fsrw_tac[ARITH_ss][]) >>
  conj_tac >- (
    srw_tac[][] >>
    simp[block_equality_code_def,bvlSemTheory.evaluate_def,bvlSemTheory.do_app_def] >>
    qexists_tac`0`>>simp[]
    \\ imp_res_tac do_eq_list_T_every
    \\ full_simp_tac(srw_ss())[LIST_REL_EL_EQN]) >>
  srw_tac[][] >>
  simp[block_equality_code_def,bvlSemTheory.evaluate_def,bvlSemTheory.do_app_def] >>
  simp[find_code_def] >>
  `equality_code = (2,SND equality_code)` by simp[equality_code_def] >>
  pop_assum SUBST1_TAC >> simp[] >>
  simp[EL_LENGTH_APPEND] >>
  first_x_assum(qspec_then`s`mp_tac) >>
  impl_tac >- (
    simp[] >> spose_not_then strip_assume_tac >> full_simp_tac(srw_ss())[] ) >>
  strip_tac >>
  reverse(Cases_on`do_eq v1 v2`)>>full_simp_tac(srw_ss())[]>>
  reverse(Cases_on`b`) >> full_simp_tac(srw_ss())[] >- (
    qexists_tac`ck+1`>>simp[dec_clock_def,inc_clock_def] >>
    fsrw_tac[ARITH_ss][inc_clock_def]>>
    imp_res_tac do_eq_list_T_every >>
    fsrw_tac[ARITH_ss][LIST_REL_EL_EQN]
    \\ simp[EL_APPEND2]
    \\ `equality_code = (2,SND equality_code)` by simp[equality_code_def]
    \\ pop_assum SUBST1_TAC \\ simp[]) >>
  first_x_assum(qspecl_then[`t`,`vs1++[v1]`,`vs2++[v2]`,`s`]mp_tac) >>
  impl_tac >- (
    simp[inc_clock_def]
    \\ full_simp_tac(srw_ss())[do_eq_list_T_every]) >> strip_tac >>
  qexists_tac`ck+1+ck'+1` >>
  `LENGTH vs1 = LENGTH vs2` by metis_tac[do_eq_list_T_every,LIST_REL_LENGTH] >>
  simp[inc_clock_def,dec_clock_def] >>
  `equality_code = (2,SND equality_code)` by simp[equality_code_def] >>
  pop_assum SUBST1_TAC \\ simp[] >>
  simp[EL_APPEND2] >>
  imp_res_tac evaluate_add_clock >>full_simp_tac(srw_ss())[] >>
  first_x_assum(qspec_then`ck'+1`mp_tac) >>
  simp[inc_clock_def] >> disch_then kall_tac >>
  `block_equality_code = (4,SND block_equality_code)` by simp[block_equality_code_def] >>
  pop_assum SUBST1_TAC >> simp[] >> srw_tac[][] >>
  simp[ADD1] >>
  fsrw_tac[ARITH_ss][inc_clock_def] >>
  `1 + &LENGTH vs = &(LENGTH vs + 1)` by ARITH_TAC >>
  fsrw_tac[ARITH_ss][integerTheory.INT_ADD] >>
  metis_tac[CONS_APPEND,APPEND_ASSOC])

(* compiler correctness *)

val EXISTS_NOT_IN_refs = prove(
  ``?x. ~(x IN FDOM (t1:'ffi bvlSem$state).refs)``,
  METIS_TAC [NUM_NOT_IN_FDOM])

val lookup_vars_IMP2 = prove(
  ``!vs env xs env2.
      (lookup_vars vs env = SOME xs) /\
      env_rel f refs code env env2 ==>
      ?ys. (!t1. (evaluate (MAP Var vs,env2,t1) = (Rval ys,t1))) /\
           EVERY2 (v_rel f refs code) xs ys /\
           (LENGTH vs = LENGTH xs)``,
  Induct \\ full_simp_tac(srw_ss())[lookup_vars_def,evaluate_def]
  \\ REPEAT STRIP_TAC
  \\ Cases_on `lookup_vars vs env` \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
  \\ ONCE_REWRITE_TAC [evaluate_CONS]
  \\ full_simp_tac(srw_ss())[evaluate_def]
  \\ RES_TAC \\ IMP_RES_TAC LESS_LENGTH_env_rel_IMP \\ full_simp_tac(srw_ss())[])
  |> INST_TYPE[alpha|->``:'ffi``];

val lookup_vars_IMP = prove(
  ``!vs env xs env2.
      (lookup_vars vs env = SOME xs) /\
      env_rel f refs code env env2 ==>
      ?ys. (evaluate (MAP Var vs,env2,t1) = (Rval ys,t1)) /\
           EVERY2 (v_rel f refs code) xs ys /\
           (LENGTH vs = LENGTH xs)``,
  (* TODO: metis_tac is not VALID here *)
    PROVE_TAC[lookup_vars_IMP2])
  |> INST_TYPE[alpha|->``:'ffi``];

val compile_exps_IMP_code_installed = prove(
  ``(compile_exps xs aux = (c,aux1)) /\
    code_installed aux1 code ==>
    code_installed aux code``,
  REPEAT STRIP_TAC
  \\ MP_TAC (SPEC_ALL compile_exps_acc) \\ full_simp_tac(srw_ss())[LET_DEF]
  \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[code_installed_def]);

val compile_exps_LIST_IMP_compile_exps_EL = prove(
  ``!exps aux1 c7 aux7 i n8 n4 aux5 num_args e.
      EL i exps = (num_args, e) ∧
      (compile_exps (MAP SND exps) aux1 = (c7,aux7)) /\ i < LENGTH exps /\
      (build_aux n8 (MAP2 (code_for_recc_case k) (MAP FST exps) c7) aux7 = (n4,aux5)) /\
      code_installed aux5 t1.code ==>
      ?aux c aux1'.
        compile_exps [e] aux = ([c],aux1') /\
        lookup (n8 + 2*i) t1.code = SOME (num_args + 1,SND (code_for_recc_case k num_args c)) /\
        code_installed aux1' t1.code``,
  HO_MATCH_MP_TAC SNOC_INDUCT \\ full_simp_tac(srw_ss())[] \\ REPEAT STRIP_TAC
  \\ Cases_on `i = LENGTH exps` \\ full_simp_tac(srw_ss())[] THEN1
   (full_simp_tac(srw_ss())[SNOC_APPEND,EL_LENGTH_APPEND]
    \\ full_simp_tac(srw_ss())[GSYM SNOC_APPEND,compile_exps_SNOC]
    \\ `?c1 aux2. compile_exps (MAP SND exps) aux1 = (c1,aux2)` by METIS_TAC [PAIR]
    \\ `?c3 aux3. compile_exps [e] aux2 = (c3,aux3)` by METIS_TAC [PAIR]
    \\ full_simp_tac(srw_ss())[LET_DEF] \\ SRW_TAC [] []
    \\ Q.LIST_EXISTS_TAC [`aux2`] \\ full_simp_tac(srw_ss())[]
    \\ IMP_RES_TAC compile_exps_SING \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[code_installed_def]
    \\ qpat_assum `xxx++[yyy]=zzz` (assume_tac o GSYM)
    \\ full_simp_tac(srw_ss())[]
    \\ rpt BasicProvers.VAR_EQ_TAC
    \\ IMP_RES_TAC compile_exps_LENGTH \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[GSYM SNOC_APPEND, map2_snoc]
    \\ full_simp_tac(srw_ss())[SNOC_APPEND, build_aux_APPEND1]
    \\ Cases_on `build_aux n8 (MAP2 (code_for_recc_case k) (MAP FST exps) c1) aux3`
    \\ full_simp_tac(srw_ss())[LET_DEF]
    \\ IMP_RES_TAC build_aux_LENGTH
    \\ full_simp_tac(srw_ss())[AC ADD_COMM ADD_ASSOC]
    \\ rpt BasicProvers.VAR_EQ_TAC
    \\ full_simp_tac(srw_ss())[LENGTH_MAP2]
    \\ Cases_on `code_for_recc_case k num_args d`
    \\ full_simp_tac(srw_ss())[]
    \\ (qspecl_then [`MAP2 (code_for_recc_case k) (MAP FST exps) c1`,`n8`,`aux3`]
           mp_tac build_aux_acc) \\ full_simp_tac(srw_ss())[]
    \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[]
    \\ rev_full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[code_for_recc_case_def] )
  \\ `i < LENGTH exps` by DECIDE_TAC
  \\ full_simp_tac(srw_ss())[EL_SNOC]
  \\ full_simp_tac(srw_ss())[MAP_SNOC, compile_exps_SNOC]
  \\ `?c1 aux2. compile_exps (MAP SND exps) aux1 = (c1,aux2)` by METIS_TAC [PAIR]
  \\ `?c3 aux3. compile_exps [SND x] aux2 = (c3,aux3)` by METIS_TAC [PAIR]
  \\ full_simp_tac(srw_ss())[LET_DEF]
  \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`aux1`]) \\ full_simp_tac(srw_ss())[]
  \\ SRW_TAC [] [] \\ POP_ASSUM (MP_TAC o Q.SPECL [`i`,`n8`])
  \\ full_simp_tac(srw_ss())[] \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC compile_exps_SING \\ SRW_TAC [] []
  \\ imp_res_tac compile_exps_LENGTH
  \\ full_simp_tac(srw_ss())[GSYM SNOC_APPEND, map2_snoc]
  \\ full_simp_tac(srw_ss())[SNOC_APPEND, MAP,build_aux_APPEND1]
  \\ Cases_on `build_aux n8 (MAP2 (code_for_recc_case k) (MAP FST exps) c1) aux3`
  \\ full_simp_tac(srw_ss())[LET_DEF] \\ NTAC 4 (POP_ASSUM MP_TAC)
  \\ qspecl_then [`[SND x]`,`aux2`] mp_tac compile_exps_acc
  \\ full_simp_tac(srw_ss())[LET_DEF] \\ REPEAT STRIP_TAC \\ SRW_TAC [] []
  \\ FIRST_X_ASSUM MATCH_MP_TAC
  \\ POP_ASSUM MP_TAC
  \\ ONCE_REWRITE_TAC [build_aux_MOVE]
  \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[code_installed_def]);

val evaluate_recc_Lets = prove(
  ``!(ll:(num#'a) list) n7 rr env' t1 ys c8 (x:(num#'a)) (x':(num#'a)) ck.
     EVERY (\n. n7 + num_stubs + 2* n IN domain t1.code) (GENLIST I (LENGTH ll)) ==>
     (evaluate
       ([recc_Lets (n7 + num_stubs) (REVERSE (MAP FST ll)) (LENGTH ll) (HD c8)],
        Block closure_tag [CodePtr (n7 + (num_stubs + 2 * LENGTH ll)); Number (&(FST x-1)); RefPtr rr]::env',
        t1 with <| refs := t1.refs |+ (rr,
               ValueArray
               (MAP (K (Number 0)) (MAP FST ll) ++
                [Block closure_tag [CodePtr (n7 + (num_stubs + 2* LENGTH ll)); Number (&(FST x'-1)); RefPtr rr]]++ys));clock := ck |>) =
      evaluate
       ([HD c8],
        MAP2 (\n args. Block closure_tag [CodePtr (n7 + num_stubs + 2* n); Number &(args-1); RefPtr rr])
                  (GENLIST I (LENGTH ll + 1)) (MAP FST ll ++ [FST x]) ++ env',
        t1 with <| refs := t1.refs |+ (rr,
               ValueArray
               (MAP2 (\n args. Block closure_tag [CodePtr (n7 + num_stubs + 2* n); Number &(args-1); RefPtr rr])
                  (GENLIST I (LENGTH ll + 1)) (MAP FST ll ++ [FST x']) ++ ys)); clock := ck |>))``,
  recInduct SNOC_INDUCT \\ full_simp_tac(srw_ss())[] \\ REPEAT STRIP_TAC
  \\ ONCE_REWRITE_TAC [recc_Lets_def] \\ full_simp_tac(srw_ss())[LET_DEF]
  \\ full_simp_tac(srw_ss())[bvlSemTheory.evaluate_def,recc_Let_def,bvlSemTheory.do_app_def]
  \\ simp []
  \\ full_simp_tac(srw_ss())[DECIDE ``0 < k + SUC n:num``,EVERY_SNOC,GENLIST, ADD_ASSOC]
  \\ full_simp_tac(srw_ss())[FLOOKUP_UPDATE,DECIDE ``n < SUC n + m``,DECIDE ``0 < 1 + SUC n``,
         DECIDE ``0 < 1 + n:num``,DECIDE ``2 < 1 + (1 + (1 + n:num))``]
  \\ simp []
  \\ full_simp_tac(srw_ss())[SNOC_APPEND,MAP_APPEND,MAP, MAP_REVERSE, REVERSE_APPEND, tl_append]
  \\ `LENGTH l = LENGTH (MAP (K (Number 0:bvlSem$v)) (MAP FST (l:(num#'a) list)))` by srw_tac[][]
  \\ ONCE_ASM_REWRITE_TAC []
  \\ pop_assum kall_tac
  \\ rw_tac std_ss [SIMP_RULE std_ss [GSYM APPEND_ASSOC] lupdate_append2, GSYM APPEND_ASSOC]
  \\ simp []
  \\ rw_tac std_ss [PROVE [APPEND_ASSOC] ``!(a:'a list) b c d. a ++ b ++ c ++ d = a ++ b ++ (c ++ d)``] >>
  first_x_assum (qspecl_then [`n7`, `rr`,
                   `Block closure_tag [CodePtr (n7 + (num_stubs + 2 * SUC (LENGTH l))); Number (&(FST x'-1)); RefPtr rr]::env'`,
                   `t1`,
                   `[Block closure_tag [CodePtr (n7 + (num_stubs + 2 * SUC (LENGTH l))); Number (&(FST x''-1)); RefPtr rr]] ++ ys`,
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
  srw_tac[][] >>
  Cases_on `loc` >>
  srw_tac[][bvlSemTheory.evaluate_def, bvlPropsTheory.evaluate_APPEND] >>
  Cases_on `r` >>
  srw_tac[][]);

val evaluate_app_helper2 = Q.prove (
  `(!x. r ≠ Rval x) ∧ evaluate (c8,env,s) = (Rval x, s') ∧ evaluate ([c7],env,s') = (r,s'')
    ⇒
    evaluate ([case loc of
              NONE => Let (c8++[c7]) (mk_cl_call (Var (LENGTH c8)) (GENLIST Var (LENGTH c8)))
            | SOME loc => Call (LENGTH c8 - 1) (SOME (loc + num_stubs)) (c8++[c7])],env,s) = (r, s'')`,
  srw_tac[][] >>
  Cases_on `loc` >>
  srw_tac[][bvlSemTheory.evaluate_def, bvlPropsTheory.evaluate_APPEND] >>
  Cases_on `r` >>
  srw_tac[][]);

val evaluate_simple_genlist_vars = Q.prove (
  `!env1 env2 s.
    0 < LENGTH env1
    ⇒
    evaluate (GENLIST Var (LENGTH env1), env1++env2, s) = (Rval env1, s)`,
  srw_tac[][] >>
  qspecl_then [`0`, `env1++env2`, `LENGTH env1`, `s`] assume_tac evaluate_genlist_vars >>
  rev_full_simp_tac(srw_ss())[] >>
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
  srw_tac[][dest_closure_def] >>
  BasicProvers.EVERY_CASE_TAC >>
  full_simp_tac(srw_ss())[add_args_def, LET_THM, num_remaining_args_def] >>
  TRY (Cases_on `EL n l1`) >>
  full_simp_tac(srw_ss())[] >>
  BasicProvers.EVERY_CASE_TAC >>
  full_simp_tac(srw_ss())[] >>
  Cases_on `loc_opt` >>
  full_simp_tac(srw_ss())[check_loc_def] >>
  decide_tac);

val get_loc_def = Define `
  (get_loc (Closure (SOME loc) args env num_args exp) = SOME loc) ∧
  (get_loc (Recclosure (SOME loc) args env fns i) = SOME (loc + 2*i)) ∧
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
      get_loc func = loc ∧
      num_remaining_args func = SOME rem_args ∧
      get_num_args func = SOME num_args ∧
      get_old_args func = SOME old_args ∧
      get_cl_env func = SOME cl_env ∧
      rem_args ≤ LENGTH args ∧
      rem_args ≤ num_args ∧
      num_args ≤ LENGTH old_args + LENGTH args ∧
      LENGTH args2 = LENGTH args - rem_args ∧
      check_loc loc_opt loc num_args (LENGTH args) (num_args - rem_args)`,
  srw_tac[][dest_closure_def] >>
  BasicProvers.EVERY_CASE_TAC >>
  full_simp_tac(srw_ss())[] >>
  TRY (Cases_on `EL n l1`) >>
  full_simp_tac(srw_ss())[LET_THM] >>
  BasicProvers.EVERY_CASE_TAC >>
  full_simp_tac(srw_ss())[get_cl_env_def, get_old_args_def, get_loc_def, num_remaining_args_def, get_num_args_def] >>
  full_simp_tac (srw_ss()++ARITH_ss) [] >>
  srw_tac[][] >>
  TRY (Cases_on `o'`) >>
  full_simp_tac(srw_ss())[get_loc_def] >>
  simp [] >>
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
  srw_tac[][v_rel_cases] >>
  full_simp_tac(srw_ss())[num_remaining_args_def]
  >- (full_simp_tac(srw_ss())[cl_rel_cases] >>
      srw_tac[][] >>
      full_simp_tac(srw_ss())[num_remaining_args_def, int_arithTheory.INT_NUM_SUB,closure_code_installed_def,
          EVERY_EL, EL_MAP] >>
      pop_assum (mp_tac o GSYM) >>
      srw_tac[][] >>
      pop_assum (fn th => first_assum (mp_tac o MATCH_MP th)) >>
      Cases_on `EL k exps_ps` >>
      simp [] >>
      Cases_on `q` >>
      full_simp_tac(srw_ss())[] >>
      srw_tac[][] >>
      simp [EL_MAP])
  >- (full_simp_tac(srw_ss())[cl_rel_cases] >>
      srw_tac[][] >>
      full_simp_tac(srw_ss())[get_num_args_def, add_args_def] >>
      srw_tac[][] >>
      full_simp_tac(srw_ss())[num_remaining_args_def, int_arithTheory.INT_NUM_SUB] >>
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
  srw_tac[][unpack_closure_cases, v_rel_cases, cl_rel_cases, num_remaining_args_def] >>
  full_simp_tac(srw_ss())[num_remaining_args_def] >>
  rw_tac bool_ss [] >>
  TRY ARITH_TAC >>
  full_simp_tac(srw_ss())[EL_MAP] >>
  `?n e p. EL k exps_ps = ((n,e),p)` by metis_tac [pair_CASES] >>
  full_simp_tac(srw_ss())[closure_code_installed_def, EVERY_EL] >>
  res_tac >>
  rev_full_simp_tac(srw_ss())[] >>
  TRY ARITH_TAC >>
  srw_tac [boolSimps.DNF_ss] [partial_app_tag_def, int_arithTheory.INT_NUM_SUB] >>
  imp_res_tac EVERY2_LENGTH >>
  full_simp_tac(srw_ss())[add_args_def, get_num_args_def, EL_MAP] >>
  TRY ARITH_TAC >>
  srw_tac [boolSimps.DNF_ss] [partial_app_tag_def, int_arithTheory.INT_NUM_SUB] >>
  TRY decide_tac >>
  TRY (Cases_on `ys`) >>
  full_simp_tac(srw_ss())[ADD1, num_remaining_args_def] >>
  srw_tac [ARITH_ss] [integerTheory.int_ge, integerTheory.INT_LE_SUB_LADD, integerTheory.INT_LE_LT1] >>
  TRY(simp[closure_tag_def]>>NO_TAC) >>
  first_x_assum (fn th => first_assum (mp_tac o MATCH_MP th)) >>
  srw_tac[][EL_MAP] >>
  decide_tac) |> INST_TYPE[alpha|->``:'ffi``];

val cl_rel_get_num_args = Q.prove (
  `cl_rel f1 refs code (env,ys) func (Block tag (p::Number (&(total_args) - 1)::fvs))
   ⇒
   get_num_args func = SOME total_args`,
  srw_tac[][cl_rel_cases] >>
  full_simp_tac(srw_ss())[get_num_args_def, int_arithTheory.INT_NUM_SUB, EL_MAP, closure_code_installed_def, EVERY_EL] >>
  `?n e p. EL k exps_ps = ((n,e),p)` by metis_tac [pair_CASES] >>
  full_simp_tac(srw_ss())[] >>
  srw_tac[][] >>
  pop_assum mp_tac >>
  res_tac >>
  srw_tac[][] >>
  full_simp_tac(srw_ss())[] >>
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
  srw_tac[][int_arithTheory.INT_NUM_SUB] >>
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
  rev_full_simp_tac(srw_ss())[]);

val cl_rel_get_loc = Q.prove (
  `cl_rel f1 refs code (env,fvs) func (Block tag (CodePtr p::n::ys))
   ⇒
   num_stubs ≤ p ∧
   get_loc func = SOME (p-num_stubs)`,
  srw_tac[][cl_rel_cases] >>
  full_simp_tac(srw_ss())[get_loc_def, closure_code_installed_def, EVERY_EL] >>
  `?n e p. EL k exps_ps = ((n,e),p)` by metis_tac [pair_CASES] >>
  full_simp_tac(srw_ss())[] >>
  srw_tac[][] >>
  pop_assum mp_tac >>
  res_tac >>
  srw_tac[][] >>
  full_simp_tac(srw_ss())[EL_MAP] >>
  srw_tac[][] >>
  `p = EL k (GENLIST (λn. loc + num_stubs + 2*n) (LENGTH exps_ps))` by metis_tac [p_genlist] >>
  srw_tac[][] >>
  ARITH_TAC);

(* Differs from check_loc and dest_closure by not checking that max_app *)
val check_loc'_def = Define `
  (check_loc' NONE loc num_params num_args so_far ⇔  T) ∧
  (check_loc' (SOME p) loc num_params num_args so_far ⇔
    (num_params = num_args) ∧ (so_far = 0:num) ∧ (SOME p = loc))`;

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
             ~(check_loc' loc_opt (lift ($+ (2 *i)) loc) num_args (LENGTH args) (LENGTH arg_env)) ∨
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
  srw_tac[][dest_closure_def, dest_closure'_def] >>
  BasicProvers.EVERY_CASE_TAC >>
  full_simp_tac(srw_ss())[] >>
  Cases_on `l` >>
  full_simp_tac(srw_ss())[check_loc_def, check_loc'_def, LET_THM] >>
  Cases_on `EL n l1` >>
  full_simp_tac(srw_ss())[]);

val cl_rel_run_lemma1 = Q.prove (
  `num_args ≤ LENGTH args'
   ⇒
   evaluate (GENLIST Var num_args, DROP (LENGTH args' - num_args) args' ++ stuff, t1) =
   (Rval (DROP (LENGTH args' - num_args) args'), t1)`,
  srw_tac[][] >>
  assume_tac (Q.SPECL [`0`, `DROP (LENGTH args' - num_args) args'++stuff`, `num_args`, `t1`] evaluate_genlist_vars) >>
  rev_full_simp_tac(srw_ss())[] >>
  rpt (pop_assum mp_tac) >>
  srw_tac [ARITH_ss] [ETA_THM] >>
  `LENGTH (DROP (LENGTH args' - num_args) args') = num_args` by srw_tac [ARITH_ss] [] >>
  metis_tac [TAKE_LENGTH_APPEND]);

val cl_rel_run_lemma2 = Q.prove (
  `num_args ≤ LENGTH args'
   ⇒
   evaluate (GENLIST Var (num_args + 1), DROP (LENGTH args' - num_args) args' ++ [f] ++ stuff, t1) =
   (Rval (DROP (LENGTH args' - num_args) args' ++ [f]), t1)`,
  srw_tac[][] >>
  assume_tac (Q.SPECL [`0`, `DROP (LENGTH args' - num_args) args'++[f]++stuff`, `num_args+1`, `t1`] evaluate_genlist_vars) >>
  rev_full_simp_tac(srw_ss())[] >>
  rpt (pop_assum mp_tac) >>
  srw_tac [ARITH_ss] [ETA_THM] >>
  `LENGTH (DROP (LENGTH args' - num_args) args'++[f]) = num_args+1` by srw_tac [ARITH_ss] [] >>
  metis_tac [TAKE_LENGTH_APPEND]) |> Q.INST [`stuff`|-> `[]`] |> SIMP_RULE (srw_ss()) [];

val cl_rel_run_lemma3 = Q.prove (
  `LIST_REL R args args' ⇒
   LIST_REL R (DROP (LENGTH args' − n) args) (DROP (LENGTH args' − n) args')`,
  full_simp_tac(srw_ss())[LIST_REL_EL_EQN] >>
  srw_tac[][] >>
  `n' + (LENGTH args' − n) < LENGTH args` by decide_tac >>
  `n' + (LENGTH args' − n) < LENGTH args'` by metis_tac [] >>
  srw_tac[][EL_DROP]);

val bEval_free_let_Block = Q.prove (
  `!ys zs.
    evaluate ([x],env,s) = (Rval [Block n (y::z::ys ++ zs)], s)
    ⇒
    evaluate (free_let x (LENGTH ys),env,s) = (Rval ys,s)`,
  ho_match_mp_tac SNOC_INDUCT >>
  srw_tac[][free_let_def, bEval_def] >>
  full_simp_tac(srw_ss())[SNOC_APPEND] \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC] >>
  res_tac >>
  full_simp_tac(srw_ss())[GENLIST, bvlPropsTheory.evaluate_SNOC, bEvalOp_def, bEval_def] >>
  simp [EL_CONS, PRE_SUB1, el_append3])
   |> Q.SPECL [`ys`,`[]`] |> SIMP_RULE std_ss [APPEND_NIL];

val cl_rel_run_tac =
  qexists_tac `c` >>
  qexists_tac `aux` >>
  qexists_tac `aux1` >>
  imp_res_tac EVERY2_LENGTH >>
  full_simp_tac(srw_ss())[] >>
  srw_tac[][bEval_def, bEval_APPEND] >>
  rw_tac (std_ss) [GSYM APPEND_ASSOC] >>
  simp [cl_rel_run_lemma1, cl_rel_run_lemma2] >>
  `LENGTH (DROP (LENGTH args' − num_args) args') = num_args`
             by (srw_tac[][] >> decide_tac) >>
  qexists_tac `witness` >>
  srw_tac[][] >>
  `evaluate ([Var num_args], DROP (LENGTH args' − num_args) args' ++ [func'],t1 with <| refs := refs; code := code |>)
      = (Rval [func'],t1 with <| refs := refs; code := code |>)`
          by (srw_tac[][bEval_def]
              >- metis_tac [EL_LENGTH_APPEND, NULL, HD]) >>
  simp [TAKE_REVERSE, LASTN_DROP] >>
  unabbrev_all_tac >>
  imp_res_tac bEval_free_let_Block >>
  rev_full_simp_tac(srw_ss())[] >>
  srw_tac[][] >>
  metis_tac [list_rel_IMP_env_rel, APPEND_ASSOC, LASTN_LENGTH_ID, env_rel_APPEND, LIST_REL_def, cl_rel_run_lemma3];

val genlist_deref = Q.prove (
  `!skip st r xs args p n env ys.
    FLOOKUP st.refs r = SOME (ValueArray (ys++xs)) ∧
    skip = LENGTH ys
    ⇒
    bvlSem$evaluate (GENLIST (λi. Op Deref [Op (Const (&(i + skip))) []; Var 0]) (LENGTH xs),
           RefPtr r:: (args ++ Block closure_tag [CodePtr p; Number (&n); RefPtr r]::env),
           st)
    =
    (Rval xs, st)`,
  Induct_on `xs` >>
  srw_tac[][evaluate_def, GENLIST_CONS] >>
  srw_tac[][Once evaluate_CONS, evaluate_def, do_app_def, combinTheory.o_DEF] >>
  `FLOOKUP st.refs r = SOME (ValueArray ((ys++[h])++xs))` by srw_tac[][] >>
  first_x_assum (fn th => first_assum (assume_tac o MATCH_MP (SIMP_RULE (srw_ss()) [GSYM AND_IMP_INTRO] th))) >>
  simp [ADD1] >>
  srw_tac[][] >>
  full_simp_tac(srw_ss())[ADD1] >>
  srw_tac[][EL_LENGTH_APPEND]);

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
              by (srw_tac[][] >> intLib.ARITH_TAC) >>
  imp_res_tac evaluate_genlist_vars >>
  full_simp_tac(srw_ss())[] >>
  mp_tac (Q.SPEC `0` genlist_deref) >>
  simp [LENGTH_NIL_SYM] >>
  srw_tac[][TAKE_LENGTH_APPEND]);

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
      compile_exps [body] aux1 = ([body'],aux2) ∧ code_installed aux2 code ∧
      env_rel f1 refs code new_env new_env' ∧
      !t1. evaluate ([exp'], DROP (LENGTH args' - (n + 1)) args'++[func'], t1 with <| refs := refs; code := code |>) =
           evaluate ([body'], new_env', t1 with <| refs := refs; code := code |>)`,
  srw_tac[][cl_rel_cases, dest_closure'_def] >>
  full_simp_tac(srw_ss())[int_arithTheory.INT_NUM_SUB, closure_code_installed_def] >>
  rev_full_simp_tac(srw_ss())[] >>
  simp [] >>
  full_simp_tac(srw_ss())[check_loc_def, LET_THM] >>
  BasicProvers.EVERY_CASE_TAC >>
  srw_tac[][]
  >- (qabbrev_tac `func' = Block closure_tag (CodePtr (p + num_stubs)::Number (&num_args − 1):: env')` >>
      qabbrev_tac `witness = DROP (LENGTH args' − num_args) args'++env'++DROP (LENGTH args' − num_args) args' ++ [func']` >>
      cl_rel_run_tac)
  >- (qabbrev_tac `func' = Block closure_tag (CodePtr (p + num_stubs)::Number (&num_args − 1):: env')` >>
      qabbrev_tac `witness = DROP (LENGTH args' − num_args) args'++[func']++env'++DROP (LENGTH args' − num_args) args' ++ [func']` >>
      cl_rel_run_tac) >>
  full_simp_tac(srw_ss())[EL_MAP] >>
  `?n e p. EL k exps_ps = ((n,e),p)` by metis_tac [pair_CASES] >>
  full_simp_tac(srw_ss())[] >>
  srw_tac[][] >>
  Cases_on `LENGTH args < n'` >>
  full_simp_tac(srw_ss())[EVERY_EL, closure_code_installed_def] >>
  srw_tac[][] >>
  first_assum (fn th => first_assum (mp_tac o MATCH_MP th)) >>
  ASM_REWRITE_TAC [] >>
  simp [] >>
  srw_tac[][] >>
  simp [] >>
  MAP_EVERY qexists_tac [`c`, `aux`, `aux1`,
        `DROP (LENGTH args' − (n + 1)) args' ++
         MAP (λ((n,e),p). Block closure_tag [CodePtr p; Number (if n = 0 then 0 else &n − 1); RefPtr r])
             exps_ps ++
         fvs ++
         [RefPtr r] ++
         DROP (LENGTH args' − (n + 1)) args' ++
         [Block closure_tag [CodePtr p; Number (&n); RefPtr r]]`] >>
  srw_tac[][]
  >- ARITH_TAC
  >- (simp [TAKE_REVERSE, LASTN_DROP] >>
      `LIST_REL (v_rel f1 refs code)
                (DROP (LENGTH args − n') args)
                (DROP (LENGTH args' − (n + 1)) args')`
              by (`n' = n+1` by ARITH_TAC >>
                  metis_tac [cl_rel_run_lemma3, EVERY2_LENGTH]) >>
      `LIST_REL (v_rel f1 refs code)
                (GENLIST (Recclosure (SOME loc') [] env (MAP FST exps_ps)) (LENGTH exps_ps))
                (MAP (λ((n,e),p).
                       Block closure_tag [CodePtr p; Number (if n = 0 then 0 else &n − 1); RefPtr r])
                     exps_ps)`
            by (srw_tac[][LIST_REL_EL_EQN] >>
                simp [v_rel_cases] >>
                simp [EL_MAP, cl_rel_cases] >>
                `?n e p. EL n'' exps_ps = ((n,e),p)` by metis_tac [pair_CASES] >>
                full_simp_tac(srw_ss())[] >>
                simp [] >>
                qexists_tac `env` >>
                simp [] >>
                qexists_tac `fvs` >>
                simp [] >>
                DISJ2_TAC >>
                qexists_tac `exps_ps` >>
                simp [EL_MAP] >>
                srw_tac[][int_arithTheory.INT_NUM_SUB] >>
                srw_tac[][closure_code_installed_def] >>
                srw_tac[][EVERY_EL]) >>
      metis_tac [list_rel_IMP_env_rel, APPEND_ASSOC, EVERY2_APPEND])
  >- (`FLOOKUP refs r = FLOOKUP (t1 with <| refs := refs; code := code|>).refs r` by srw_tac[][] >>
      full_simp_tac std_ss [] >>
      imp_res_tac evaluate_code_for_recc_case >>
      full_simp_tac(srw_ss())[LENGTH_MAP] >>
      pop_assum (qspecl_then [`p`, `n`, `[]`, `c`, `DROP (LENGTH args' − (n + 1)) args'`] mp_tac) >>
      srw_tac[][] >>
      imp_res_tac EVERY2_LENGTH >>
      `LENGTH args' − (LENGTH args' − (n + 1)) = n'` by ARITH_TAC >>
      full_simp_tac(srw_ss())[] >>
      srw_tac[][Once ADD_COMM]));

val cl_rel_dest = Q.prove (
  `!f refs code cl cl' fvs fvs'.
    cl_rel f refs code (fvs,fvs') cl cl'
    ⇒
    get_old_args cl = SOME [] ∧
    ?l num_args fvs.
      cl' = Block closure_tag (CodePtr l::Number (&num_args)::fvs)`,
  srw_tac[][cl_rel_cases] >>
  srw_tac[][get_old_args_def, EL_MAP] >>
  `?n e p. EL k exps_ps = ((n,e),p)` by metis_tac [pair_CASES] >>
  srw_tac[][]);

val dest_closure_full_of_part = Q.prove (
  `dest_closure loc func args = SOME (Full_app body newenv rest) ∧
   LENGTH arg_env ≠ 0 ∧
   add_args cl arg_env = SOME func ∧
   get_num_args cl = SOME num_args ∧
   LENGTH arg_env < num_args
   ⇒
   dest_closure' loc cl (args++arg_env) = SOME (Full_app body newenv rest)`,
  srw_tac[][dest_closure_def, dest_closure'_def] >>
  BasicProvers.EVERY_CASE_TAC >>
  full_simp_tac(srw_ss())[add_args_def, check_loc_def, check_loc'_def, get_num_args_def] >>
  srw_tac[][] >>
  full_simp_tac(srw_ss())[] >>
  TRY decide_tac
  >- (`LENGTH (REVERSE arg_env) ≤ n - LENGTH l` by (srw_tac [ARITH_ss] []) >>
      srw_tac[][TAKE_APPEND2] >>
      srw_tac [ARITH_ss] [])
  >- (`LENGTH (REVERSE arg_env) ≤ n - LENGTH l` by (srw_tac [ARITH_ss] []) >>
      srw_tac[][DROP_APPEND2] >>
      srw_tac [ARITH_ss] [])
  >- (Cases_on `loc` >> full_simp_tac(srw_ss())[check_loc_def, check_loc'_def])
  >- (full_simp_tac(srw_ss())[LET_THM] >>
      BasicProvers.EVERY_CASE_TAC >>
      srw_tac[][] >>
      full_simp_tac(srw_ss())[] >>
      TRY decide_tac
      >- (Cases_on `loc` >> full_simp_tac(srw_ss())[check_loc_def, check_loc'_def])
      >- (`LENGTH (REVERSE arg_env) ≤ num_args' - LENGTH l` by (srw_tac [ARITH_ss] []) >>
          srw_tac[][TAKE_APPEND2] >>
          srw_tac [ARITH_ss] [])
      >- (`LENGTH (REVERSE arg_env) ≤ num_args' - LENGTH l` by (srw_tac [ARITH_ss] []) >>
          srw_tac[][DROP_APPEND2] >>
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
      compile_exps [body] aux1 = ([body'],aux2) ∧ code_installed aux2 code ∧
      env_rel f1 refs code newenv newenv' ∧
      !t1.
        evaluate ([exp'], DROP (LENGTH args' - (n + 1)) args' ++ [func'], inc_clock ck' (t1 with <|refs := refs; code := code|>)) =
        evaluate ([body'], newenv', (t1 with <| refs := refs; code := code |>))`,
  srw_tac[][] >>
  qpat_assum `v_rel x0 x1 x2 x3 x4` (fn x => mp_tac x >> simp [v_rel_cases] >> assume_tac x) >>
  srw_tac[][] >>
  imp_res_tac EVERY2_LENGTH >>
  imp_res_tac cl_rel_get_loc
  >- (qexists_tac `0` >>
      srw_tac[][] >>
      imp_res_tac dest_cl_imp_dest_cl' >>
      (* TODO: metis_tac[cl_rel_run] is not VALID here *)
      match_mp_tac cl_rel_run >> metis_tac[]) >>
  CONV_TAC (RESORT_EXISTS_CONV List.rev) >>
  qexists_tac `generate_partial_app_closure_fn (num_args − 1) (LENGTH ys − 1)` >>
  srw_tac [ARITH_ss] [] >>
  imp_res_tac cl_rel_dest >>
  srw_tac[][] >>
  `v_rel f1 refs code cl (Block closure_tag (CodePtr l::Number (&num_args')::fvs'))`
            by (srw_tac[][v_rel_cases, partial_app_tag_def] >>
                metis_tac [closure_tag_def]) >>
  `LENGTH arg_env ≠ 0 ∧ LENGTH ys ≠ 0 ∧ LENGTH ys < num_args` by metis_tac [LENGTH_EQ_NUM] >>
  `LIST_REL (v_rel f1 refs code) (args++arg_env) (args'++ys)`
             by metis_tac [EVERY2_APPEND] >>
  assume_tac (SIMP_RULE (srw_ss()) [GSYM AND_IMP_INTRO] dest_closure_full_of_part |> GEN_ALL) >>
  rpt (pop_assum (fn th => first_assum (assume_tac o MATCH_MP th))) >>
  strip_assume_tac (SIMP_RULE (srw_ss()) [GSYM AND_IMP_INTRO] cl_rel_run) >>
  full_simp_tac(srw_ss())[] >>
  rpt (pop_assum (fn x => first_assum (strip_assume_tac o MATCH_MP x))) >>
  MAP_EVERY qexists_tac [`new_env'`, `aux2`, `aux1`, `body'`] >>
  srw_tac[][] >>
  `?total_args. &num_args' = &total_args - 1`
        by (qexists_tac `&num_args' + 1` >>
            srw_tac[][] >>
            ARITH_TAC) >>
  full_simp_tac(srw_ss())[] >>
  imp_res_tac cl_rel_get_num_args >>
  full_simp_tac(srw_ss())[] >>
  srw_tac[][] >>
  qexists_tac `1` >>
  srw_tac[][] >>
  full_simp_tac(srw_ss())[] >>
  `num_args' + 2 = LENGTH (DROP (LENGTH args' + LENGTH ys − num_args) args') + (LENGTH ys +1) ∧
   0 < LENGTH (DROP (LENGTH args' + LENGTH ys − num_args) args')`
            by (srw_tac[][LENGTH_DROP, SUB_LEFT_SUB] >>
                full_simp_tac(srw_ss())[LESS_OR_EQ] >>
                TRY ARITH_TAC >>
                `num_args' = num_args -1`  by ARITH_TAC >>
                simp [] >>
                imp_res_tac dest_closure_full_app >>
                `num_args'' = num_args ∧ LENGTH old_args = LENGTH ys`
                         by (Cases_on `cl` >>
                             full_simp_tac(srw_ss())[add_args_def] >>
                             qpat_assum `X = func` (assume_tac o GSYM) >>
                             full_simp_tac(srw_ss())[get_old_args_def, get_num_args_def] >>
                             srw_tac[][] >>
                             simp []) >>
                decide_tac) >>
  full_simp_tac bool_ss [] >>
  assume_tac (SIMP_RULE (srw_ss()++ARITH_ss) [GSYM AND_IMP_INTRO] evaluate_partial_app_fn) >>
  pop_assum (fn th => first_assum (mp_tac o MATCH_MP th)) >>
  full_simp_tac(srw_ss())[] >>
  srw_tac[][] >>
  full_simp_tac(srw_ss())[] >>
  full_simp_tac(srw_ss())[inc_clock_def] >>
  srw_tac[][] >>
  rev_full_simp_tac(srw_ss())[] >>
  pop_assum (qspecl_then [`Number (&num_args − 1)`,
                          `partial_app_tag`,
                          `Number (&(num_args − (LENGTH ys + 1)))`,
                          `closure_tag`,
                          `CodePtr (partial_app_fn_location (num_args − 1) (LENGTH ys − 1))`,
                          `fvs'`,
                          `t1 with <|refs:=refs;clock := t1.clock + 1; code := code|>`] mp_tac) >>
  srw_tac[][partial_app_tag_def] >>
  srw_tac[][] >>
  srw_tac[][dec_clock_def] >>
  `t1 with <|clock := t1.clock; code := code|> = t1 with code := code`
         by srw_tac[][bvlSemTheory.state_component_equality] >>
  `LENGTH args' − (LENGTH args' + LENGTH ys − num_args) + LENGTH ys − 1 = num_args -1` by ARITH_TAC >>
  full_simp_tac(srw_ss())[] >>
  `num_args' + 1 = num_args` by ARITH_TAC >>
  `LENGTH args' + LENGTH ys − (num_args' + 1) ≤ LENGTH args'` by ARITH_TAC >>
  first_x_assum (qspec_then `t1 with <| clock := t1.clock; code := code |>` mp_tac) >>
  full_simp_tac(srw_ss())[DROP_APPEND1] >>
  srw_tac[][dec_clock_def]) |> INST_TYPE[alpha|->``:'ffi``];

val list_rel_app = Q.prove (
  `!R args args' l0 c l func rem_args.
    dest_closure NONE func args = SOME (Full_app c l l0) ∧
    num_remaining_args func = SOME rem_args ∧
    LIST_REL R args args'
    ⇒
    LIST_REL R l0 (TAKE (LENGTH args' − rem_args) args')`,
  srw_tac[][dest_closure_def, LET_THM] >>
  BasicProvers.EVERY_CASE_TAC >>
  full_simp_tac(srw_ss())[] >>
  TRY (Cases_on `EL n l1`) >>
  full_simp_tac(srw_ss())[] >>
  srw_tac[][] >>
  BasicProvers.EVERY_CASE_TAC >>
  full_simp_tac(srw_ss())[] >>
  srw_tac[][] >>
  full_simp_tac(srw_ss())[LIST_REL_EL_EQN, check_loc_def, num_remaining_args_def] >>
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
  srw_tac[][] >>
  Cases_on`EL 1 l`>>simp[]>>
  simp[bEval_APPEND] >>
  qspecl_then [`0`, `TAKE n args ++ [Block n' l] ++ stuff`, `n`]mp_tac evaluate_genlist_vars >>
  qspecl_then [`1`, `Block n' l::(args ++ stuff')`, `n`]mp_tac evaluate_genlist_vars >>
  srw_tac [ARITH_ss] [ETA_THM, bEval_def, bEvalOp_def, el_take_append] >>
  srw_tac[][] >>
  `n+1 ≤ SUC (LENGTH args + LENGTH stuff')` by decide_tac >>
  srw_tac [ARITH_ss] [TAKE_APPEND1, TAKE_TAKE, EL_CONS]) |> INST_TYPE[alpha|->``:'ffi``];

val no_partial_args = Q.prove (
  `num_remaining_args func = SOME x ∧
   get_num_args func = SOME x ∧
   x ≠ 0 ∧
   add_args cl arg_env = SOME func
   ⇒
   arg_env = []`,
  Cases_on `cl` >>
  srw_tac[][add_args_def] >>
  full_simp_tac(srw_ss())[get_num_args_def, num_remaining_args_def] >>
  srw_tac[][] >>
  Cases_on `arg_env` >>
  full_simp_tac(srw_ss())[] >>
  decide_tac);

val s1 = ``s1:'ffi closSem$state``;

val compile_exps_correct = Q.store_thm("compile_exps_correct",
  `(!tmp xs env ^s1 aux1 t1 env' f1 res s2 ys aux2.
     (tmp = (xs,env,s1)) ∧
     (evaluate (xs,env,s1) = (res,s2)) /\ res <> Rerr(Rabort Rtype_error) /\
     (compile_exps xs aux1 = (ys,aux2)) /\
     every_Fn_SOME xs ∧ FEVERY (λp. every_Fn_SOME [SND (SND p)]) s1.code ∧
     every_Fn_vs_SOME xs ∧ FEVERY (λp. every_Fn_vs_SOME [SND (SND p)]) s1.code ∧
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
   (!loc_opt func args ^s1 res s2 env t1 args' func' f1.
     evaluate_app loc_opt func args s1 = (res,s2) ∧
     res ≠ Rerr(Rabort Rtype_error) ∧
     FEVERY (λp. every_Fn_SOME [SND (SND p)]) s1.code ∧
     FEVERY (λp. every_Fn_vs_SOME [SND (SND p)]) s1.code ∧
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
   (srw_tac[][] >> full_simp_tac(srw_ss())[cEval_def,compile_exps_def] \\ SRW_TAC [] [bEval_def]
    \\ metis_tac [ADD_0, SUBMAP_REFL] )
  THEN1 (* CONS *)
   (srw_tac[][] >>
    full_simp_tac(srw_ss())[cEval_def,compile_exps_def] \\ SRW_TAC [] [bEval_def]
    \\ first_assum(split_pair_case0_tac o lhs o concl) >> full_simp_tac(srw_ss())[]
    \\ last_assum(valOf o bvk_find_term(K true)(split_pair_case0_tac) o concl) >> full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[LET_THM]
    \\ first_assum(split_uncurry_arg_tac o lhs o concl) >> full_simp_tac(srw_ss())[]
    \\ first_assum(split_uncurry_arg_tac o lhs o concl) >> full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[PULL_FORALL]
    \\ FIRST_X_ASSUM (qspec_then`aux1`mp_tac)
    \\ SRW_TAC [] []
    \\ IMP_RES_TAC compile_exps_IMP_code_installed
    \\ first_x_assum(fn th =>
           first_assum(mp_tac o MATCH_MP (REWRITE_RULE[GSYM AND_IMP_INTRO]
             (CONV_RULE(STRIP_QUANT_CONV(LAND_CONV(move_conj_left(same_const``env_rel`` o #1 o strip_comb))))th))))
    \\ simp[]
    \\ impl_tac >- (strip_tac >> full_simp_tac(srw_ss())[])
    \\ IMP_RES_TAC compile_exps_SING \\ full_simp_tac(srw_ss())[] \\ REPEAT STRIP_TAC
    \\ ONCE_REWRITE_TAC [bEval_CONS]
    \\ qmatch_assum_rename_tac`evaluate ([x],_) = (v3,_)`
    \\ reverse (Cases_on `v3`) \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
    >- (full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ qexists_tac`ck` >> simp[] >>
        first_assum(match_exists_tac o concl) >> simp[])
    \\ FIRST_X_ASSUM (qspecl_then[`aux1'`,`t2`]mp_tac) >> simp[]
    \\ imp_res_tac evaluate_code >> full_simp_tac(srw_ss())[]
    \\ disch_then(qspecl_then[`env''`,`f2`]mp_tac)
    \\ impl_tac >- (
         imp_res_tac env_rel_SUBMAP >>
         simp[] >>
         imp_res_tac evaluate_const >> full_simp_tac(srw_ss())[] >>
         spose_not_then strip_assume_tac >> full_simp_tac(srw_ss())[])
    \\ strip_tac
    \\ full_simp_tac(srw_ss())[] \\ IMP_RES_TAC bEval_SING \\ full_simp_tac(srw_ss())[]
    \\ imp_res_tac evaluate_add_clock >> full_simp_tac(srw_ss())[]
    \\ qexists_tac `ck + ck'`
    \\ fsrw_tac[ARITH_ss][inc_clock_def]
    \\ every_case_tac \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
    \\ IMP_RES_TAC evaluate_code
    \\ IMP_RES_TAC v_rel_SUBMAP \\ full_simp_tac(srw_ss())[]
    \\ IMP_RES_TAC SUBMAP_TRANS \\ full_simp_tac(srw_ss())[]
    \\ srw_tac[][]
    \\ METIS_TAC [v_rel_SUBMAP, SUBMAP_REFL])
  THEN1 (* Var *)
   (srw_tac[][] >>
    Cases_on `n < LENGTH env` \\ full_simp_tac(srw_ss())[compile_exps_def,cEval_def]
    \\ IMP_RES_TAC env_rel_IMP_LENGTH
    \\ `n < LENGTH env''` by DECIDE_TAC
    \\ SRW_TAC [] [bEval_def]
    \\ MAP_EVERY Q.EXISTS_TAC [`0`, `f1`] \\ full_simp_tac(srw_ss())[SUBMAP_REFL]
    \\ MATCH_MP_TAC env_rel_IMP_EL \\ full_simp_tac(srw_ss())[])
  THEN1 (* If *)
   (srw_tac[][] >>
    full_simp_tac(srw_ss())[compile_exps_def,cEval_def,LET_THM]
    \\ first_assum(split_uncurry_arg_tac o lhs o concl) >> full_simp_tac(srw_ss())[]
    \\ first_assum(split_uncurry_arg_tac o lhs o concl) >> full_simp_tac(srw_ss())[]
    \\ first_assum(split_uncurry_arg_tac o lhs o concl) >> full_simp_tac(srw_ss())[]
    \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[bEval_def]
    \\ first_assum(split_pair_case0_tac o lhs o concl) >> full_simp_tac(srw_ss())[]
    \\ SRW_TAC [] [] \\ IMP_RES_TAC compile_exps_IMP_code_installed
    \\ first_x_assum(fn th =>
           first_assum(mp_tac o MATCH_MP (REWRITE_RULE[GSYM AND_IMP_INTRO]
             (CONV_RULE(STRIP_QUANT_CONV(LAND_CONV(move_conj_left(is_eq))))th))))
    \\ full_simp_tac(srw_ss())[]
    \\ simp[AND_IMP_INTRO]
    \\ CONV_TAC(LAND_CONV(STRIP_QUANT_CONV(LAND_CONV(move_conj_left(same_const``code_installed`` o fst o strip_comb)))))
    \\ disch_then drule
    \\ CONV_TAC(LAND_CONV(STRIP_QUANT_CONV(LAND_CONV(move_conj_left(same_const``env_rel`` o fst o strip_comb)))))
    \\ disch_then drule
    \\ simp[GSYM AND_IMP_INTRO]
    \\ impl_tac >- ( spose_not_then strip_assume_tac >> full_simp_tac(srw_ss())[] )
    \\ strip_tac
    \\ imp_res_tac compile_exps_SING >> srw_tac[][]
    \\ qmatch_assum_rename_tac`result_rel _ _ v2 _`
    \\ reverse (Cases_on `v2`) \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
    \\ TRY (qexists_tac `ck` >> srw_tac[][] >> first_assum(match_exists_tac o concl) >> simp[] >> NO_TAC)
    \\ IMP_RES_TAC cEval_SING \\ SRW_TAC [] []
    \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `Boolv T = r1` \\ full_simp_tac(srw_ss())[] THEN1
     (srw_tac[][] >> full_simp_tac(srw_ss())[] >> srw_tac[][] >> rev_full_simp_tac(srw_ss())[]
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`aux1'`]) \\ full_simp_tac(srw_ss())[]
      \\ disch_then (MP_TAC o Q.SPECL [`t2`,`env''`,`f2`]) \\ full_simp_tac(srw_ss())[]
      \\ imp_res_tac evaluate_const \\ full_simp_tac(srw_ss())[]
      \\ IMP_RES_TAC evaluate_code \\ full_simp_tac(srw_ss())[]
      \\ IMP_RES_TAC env_rel_SUBMAP \\ full_simp_tac(srw_ss())[]
      \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[]
      \\ qexists_tac `ck + ck'`
      \\ srw_tac[][]
      \\ imp_res_tac evaluate_add_clock
      \\ fsrw_tac[ARITH_ss][inc_clock_def] >>
      first_assum(match_exists_tac o concl) >> simp[]
      \\ IMP_RES_TAC SUBMAP_TRANS \\ full_simp_tac(srw_ss())[])
    \\ Cases_on `Boolv F = r1` \\ full_simp_tac(srw_ss())[] THEN1
     (srw_tac[][] >> full_simp_tac(srw_ss())[] >> srw_tac[][] >> rev_full_simp_tac(srw_ss())[]
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`aux2'`]) \\ full_simp_tac(srw_ss())[]
      \\ disch_then (MP_TAC o Q.SPECL [`t2`,`env''`,`f2`]) \\ full_simp_tac(srw_ss())[]
      \\ imp_res_tac evaluate_const \\ full_simp_tac(srw_ss())[]
      \\ IMP_RES_TAC evaluate_code \\ full_simp_tac(srw_ss())[]
      \\ IMP_RES_TAC env_rel_SUBMAP \\ full_simp_tac(srw_ss())[]
      \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[]
      \\ qexists_tac `ck + ck'`
      \\ srw_tac[][]
      \\ imp_res_tac evaluate_add_clock
      \\ fsrw_tac[ARITH_ss][inc_clock_def] >>
      first_assum(match_exists_tac o concl) >> simp[]
      \\ IMP_RES_TAC SUBMAP_TRANS \\ full_simp_tac(srw_ss())[]))
  THEN1 (* Let *)
   (srw_tac[][] >>
    full_simp_tac(srw_ss())[compile_exps_def,cEval_def,LET_THM]
    \\ first_assum(split_uncurry_arg_tac o lhs o concl) >> full_simp_tac(srw_ss())[]
    \\ first_assum(split_uncurry_arg_tac o lhs o concl) >> full_simp_tac(srw_ss())[]
    \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[bEval_def]
    \\ first_assum(split_pair_case0_tac o lhs o concl) >> full_simp_tac(srw_ss())[]
    \\ SRW_TAC [] [] \\ IMP_RES_TAC compile_exps_IMP_code_installed
    \\ first_x_assum(fn th =>
           first_assum(mp_tac o MATCH_MP (REWRITE_RULE[GSYM AND_IMP_INTRO]
             (CONV_RULE(STRIP_QUANT_CONV(LAND_CONV(move_conj_left(is_eq))))th))))
    \\ full_simp_tac(srw_ss())[]
    \\ simp[AND_IMP_INTRO]
    \\ CONV_TAC(LAND_CONV(STRIP_QUANT_CONV(LAND_CONV(move_conj_left(same_const``code_installed`` o fst o strip_comb)))))
    \\ disch_then drule
    \\ CONV_TAC(LAND_CONV(STRIP_QUANT_CONV(LAND_CONV(move_conj_left(same_const``env_rel`` o fst o strip_comb)))))
    \\ disch_then drule
    \\ simp[GSYM AND_IMP_INTRO]
    \\ impl_tac >- ( spose_not_then strip_assume_tac >> full_simp_tac(srw_ss())[] )
    \\ strip_tac
    \\ imp_res_tac compile_exps_SING >> srw_tac[][]
    \\ qmatch_assum_rename_tac`result_rel _ _ v2 _`
    \\ reverse (Cases_on `v2`) \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
    \\ TRY (qexists_tac `ck` >> srw_tac[][] >> first_assum(match_exists_tac o concl) >> simp[] >> NO_TAC)
    \\ rev_full_simp_tac(srw_ss())[]
    \\ first_x_assum(fn th =>
           first_assum(mp_tac o MATCH_MP (REWRITE_RULE[GSYM AND_IMP_INTRO]
             (CONV_RULE(STRIP_QUANT_CONV(LAND_CONV(move_conj_left(is_eq))))th))))
    \\ IMP_RES_TAC evaluate_const \\ full_simp_tac(srw_ss())[]
    \\ IMP_RES_TAC evaluate_code \\ full_simp_tac(srw_ss())[]
    \\ CONV_TAC(LAND_CONV(STRIP_QUANT_CONV(REWRITE_CONV[AND_IMP_INTRO])))
    \\ disch_then(fn th =>
           first_assum(mp_tac o MATCH_MP (REWRITE_RULE[GSYM AND_IMP_INTRO]
             (CONV_RULE(STRIP_QUANT_CONV(LAND_CONV(move_conj_left(equal"state_rel" o #1 o dest_const o #1 o strip_comb))))th))))
    \\ qmatch_assum_rename_tac`LIST_REL _ v1 v2`
    \\ qmatch_assum_rename_tac`env_rel _ _ _ env1 env2`
    \\ disch_then(qspec_then`v2 ++ env2`mp_tac) >> full_simp_tac(srw_ss())[]
    \\ impl_tac >-
     (MATCH_MP_TAC env_rel_APPEND \\ full_simp_tac(srw_ss())[]
      \\ IMP_RES_TAC env_rel_SUBMAP \\ full_simp_tac(srw_ss())[])
    \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[]
    \\ qexists_tac `ck + ck'`
    \\ imp_res_tac evaluate_add_clock
    \\ fsrw_tac[ARITH_ss][inc_clock_def]
    \\ first_assum(match_exists_tac o concl) >> simp[]
    \\ IMP_RES_TAC SUBMAP_TRANS \\ full_simp_tac(srw_ss())[])
  THEN1 (* Raise *)
   (srw_tac[][] >>
    full_simp_tac(srw_ss())[cEval_def,compile_exps_def,LET_THM] \\ SRW_TAC [] [bEval_def]
    \\ first_assum(split_uncurry_arg_tac o lhs o concl) >> full_simp_tac(srw_ss())[]
    \\ first_assum(split_pair_case0_tac o lhs o concl) >> full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[PULL_FORALL] \\ SRW_TAC [] []
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`aux1`]) \\ full_simp_tac(srw_ss())[]
    \\ IMP_RES_TAC compile_exps_IMP_code_installed
    \\ disch_then (MP_TAC o Q.SPECL [`t1`,`env''`,`f1`])
    \\ IMP_RES_TAC compile_exps_SING \\ full_simp_tac(srw_ss())[]
    \\ impl_tac >- ( spose_not_then strip_assume_tac >> full_simp_tac(srw_ss())[] )
    \\ full_simp_tac(srw_ss())[bEval_def]
    \\ qmatch_assum_rename_tac`closSem$evaluate _ = (v2,_)`
    \\ reverse (Cases_on `v2`) \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
    \\ TRY (qexists_tac `ck` >> srw_tac[][] >> first_assum(match_exists_tac o concl) >> simp[] >> NO_TAC)
    \\ IMP_RES_TAC cEval_SING \\ full_simp_tac(srw_ss())[]
    \\ IMP_RES_TAC bEval_SING \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
    \\ qexists_tac `ck` >> srw_tac[][]
    \\ first_assum(match_exists_tac o concl)
    \\ full_simp_tac(srw_ss())[])
  THEN1 (* Handle *)
   (srw_tac[][] >>
    full_simp_tac(srw_ss())[compile_exps_def,cEval_def,LET_THM]
    \\ `?c3 aux3. compile_exps [x1] aux1 = ([c3],aux3)` by METIS_TAC [PAIR,compile_exps_SING]
    \\ `?c4 aux4. compile_exps [x2] aux3 = ([c4],aux4)` by METIS_TAC [PAIR,compile_exps_SING]
    \\ full_simp_tac(srw_ss())[LET_DEF] \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[bEval_def]
    \\ `?p. evaluate ([x1],env,s1) = p` by full_simp_tac(srw_ss())[] \\ PairCases_on `p` \\ full_simp_tac(srw_ss())[]
    \\ SRW_TAC [] [] \\ IMP_RES_TAC compile_exps_IMP_code_installed
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`aux1`,`t1`])
    \\ full_simp_tac(srw_ss())[]
    \\ disch_then (MP_TAC o Q.SPECL [`env''`,`f1`]) \\ full_simp_tac(srw_ss())[]
    \\ impl_tac >- ( spose_not_then strip_assume_tac >> full_simp_tac(srw_ss())[] )
    \\ reverse (Cases_on `p0`) \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
    \\ TRY (qexists_tac `ck` >> srw_tac[][] >> first_assum(match_exists_tac o concl) >> simp[] >> NO_TAC)
    \\ reverse (Cases_on `e`) \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
    \\ TRY (qexists_tac `ck` >> srw_tac[][] >> first_assum(match_exists_tac o concl) >> simp[] >> NO_TAC)
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`aux3`]) \\ full_simp_tac(srw_ss())[]
    \\ disch_then (MP_TAC o Q.SPECL [`t2`,`v'::env''`,`f2`]) \\ full_simp_tac(srw_ss())[]
    \\ IMP_RES_TAC evaluate_const \\ full_simp_tac(srw_ss())[]
    \\ IMP_RES_TAC evaluate_code \\ full_simp_tac(srw_ss())[]
    \\ impl_tac >-
      (full_simp_tac(srw_ss())[env_rel_def] \\ IMP_RES_TAC env_rel_SUBMAP \\ full_simp_tac(srw_ss())[])
    \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[]
    \\ qexists_tac `ck + ck'`
    \\ srw_tac[][]
    \\ imp_res_tac evaluate_add_clock
    \\ fsrw_tac[ARITH_ss][inc_clock_def]
    \\ Q.EXISTS_TAC `f2'` \\ full_simp_tac(srw_ss())[]
    \\ IMP_RES_TAC SUBMAP_TRANS \\ full_simp_tac(srw_ss())[])
  THEN1 (* Op *)
   (srw_tac[][] >>
    full_simp_tac(srw_ss())[cEval_def,compile_exps_def] \\ SRW_TAC [] [bEval_def]
    \\ `?p. evaluate (xs,env,s) = p` by full_simp_tac(srw_ss())[] \\ PairCases_on `p` \\ full_simp_tac(srw_ss())[]
    \\ `?cc. compile_exps xs aux1 = cc` by full_simp_tac(srw_ss())[] \\ PairCases_on `cc` \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[LET_DEF,PULL_FORALL] \\ SRW_TAC [] []
    THEN1 ( (* ToList *)
      first_x_assum(qspec_then`aux1`mp_tac) >> simp[] >>
      `p0 ≠ Rerr (Rabort Rtype_error)` by (spose_not_then strip_assume_tac >> full_simp_tac(srw_ss())[]) >>
      disch_then(qspecl_then[`t1`,`env''`,`f1`]mp_tac) >>
      simp[] >> strip_tac >>
      full_simp_tac(srw_ss())[closSemTheory.do_app_def] >>
      reverse(Cases_on`p0`)>>full_simp_tac(srw_ss())[]>>srw_tac[][]>-(
        qexists_tac`ck`>>simp[bEval_def]>>
        qexists_tac`f2`>>simp[]) >>
      Cases_on`REVERSE a`>>full_simp_tac(srw_ss())[]>>
      Cases_on`h`>>full_simp_tac(srw_ss())[]>>
      Cases_on`t`>>full_simp_tac(srw_ss())[]>> srw_tac[][]>>
      simp[PULL_EXISTS] >>
      imp_res_tac evaluate_add_clock >> full_simp_tac(srw_ss())[] >>
      pop_assum(qspec_then`LENGTH l+1`strip_assume_tac) >>
      qexists_tac`ck+LENGTH l+1`>> simp[bEval_def] >>
      fsrw_tac[ARITH_ss][inc_clock_def] >>
      simp[bvlSemTheory.do_app_def] >>
      full_simp_tac(srw_ss())[v_rel_SIMP] >> var_eq_tac >>
      simp[bvlSemTheory.find_code_def] >>
      `lookup ToList_location t2.code = SOME ToList_code` by full_simp_tac(srw_ss())[state_rel_def] >> simp[] >>
      `ToList_code = (3,SND ToList_code)` by simp[ToList_code_def] >>
      pop_assum SUBST1_TAC >> simp[] >>
      qspecl_then[`clos_tag_shift n`,`ys`,`[]`](Q.ISPEC_THEN`t2 with clock := LENGTH l + t2.clock`mp_tac)(GEN_ALL ToList) >>
      impl_tac >- (imp_res_tac LIST_REL_LENGTH >> simp[]) >>
      simp[list_to_v_def,dec_clock_def] >>
      disch_then kall_tac >>
      imp_res_tac list_to_v >>
      first_assum(match_exists_tac o concl) >> simp[] >>
      imp_res_tac LIST_REL_LENGTH >> simp[])
    THEN1 ( (* Equal *)
      first_x_assum(qspec_then`aux1`mp_tac) >> simp[] >>
      `p0 ≠ Rerr (Rabort Rtype_error)` by (spose_not_then strip_assume_tac >> full_simp_tac(srw_ss())[]) >>
      disch_then(qspecl_then[`t1`,`env''`,`f1`]mp_tac) >>
      simp[] >> strip_tac >>
      full_simp_tac(srw_ss())[closSemTheory.do_app_def] >>
      reverse(Cases_on`p0`)>>full_simp_tac(srw_ss())[]>>srw_tac[][]>-(
        qexists_tac`ck`>>simp[bEval_def]>>
        qexists_tac`f2`>>simp[]) >>
      Cases_on`REVERSE a`>>full_simp_tac(srw_ss())[]>>
      Cases_on`t`>>full_simp_tac(srw_ss())[]>>
      Cases_on`t'`>>full_simp_tac(srw_ss())[]>> srw_tac[][]>>
      simp[bEval_def,find_code_def] >>
      `lookup equality_location t2.code = SOME equality_code ∧
       lookup block_equality_location t2.code = SOME block_equality_code` by
         full_simp_tac(srw_ss())[state_rel_def] >>
      qmatch_assum_rename_tac`REVERSE a = [v1; v2]` >>
      Cases_on `do_eq v1 v2 = Eq_type_error` >>full_simp_tac(srw_ss())[] >>
      Cases_on`a`>>full_simp_tac(srw_ss())[] >> rpt var_eq_tac >>
      `INJ ($' f2) (FDOM f2) (FRANGE f2)` by ( full_simp_tac(srw_ss())[state_rel_def] ) >>
      qmatch_assum_rename_tac`do_eq v1 v2 ≠ Eq_type_error` >>
      qmatch_assum_rename_tac`v_rel _ _ _ v1 w1` >>
      qmatch_assum_rename_tac`v_rel _ _ _ v2 w2` >>
      `do_eq w1 w2 = do_eq v1 v2` by (imp_res_tac do_eq >> simp[]) >>
      `do_eq w2 w1 = do_eq w1 w2` by (METIS_TAC[do_eq_sym]) >>
      qspecl_then[`w2`,`w1`,`t2`]mp_tac (CONJUNCT1 equality) >>
      impl_tac >- simp[] >> strip_tac >>
      qexists_tac`ck+ck'+1` >>
      imp_res_tac evaluate_add_clock >> full_simp_tac(srw_ss())[] >>
      first_x_assum(qspec_then`ck'+1`mp_tac) >>
      simp[inc_clock_def] >> disch_then kall_tac >>
      `equality_code = (2,SND equality_code)` by simp[equality_code_def] >>
      pop_assum SUBST1_TAC >> simp[] >>
      simp[dec_clock_def] >>
      fsrw_tac[ARITH_ss][inc_clock_def] >>
      Cases_on`do_eq v1 v2`>>full_simp_tac(srw_ss())[]>>srw_tac[][v_rel_SIMP] >>
      METIS_TAC[])
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`aux1`]) \\ full_simp_tac(srw_ss())[]
    \\ IMP_RES_TAC compile_exps_IMP_code_installed \\ REPEAT STRIP_TAC
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`t1`,`env''`,`f1`])
    \\ IMP_RES_TAC compile_exps_SING \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
    \\ full_simp_tac(srw_ss())[bEval_def]
    \\ reverse (Cases_on `p0`) \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
    \\ TRY (full_simp_tac(srw_ss())[] \\ qexists_tac `ck` >> srw_tac[][] \\ Q.EXISTS_TAC `f2` \\ full_simp_tac(srw_ss())[] \\ NO_TAC)
    \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
    \\ qexists_tac `ck` >> simp[]
    \\ reverse(Cases_on `do_app op (REVERSE a) p1`) \\ full_simp_tac(srw_ss())[] >- (
      srw_tac[][] >>
      first_x_assum(mp_tac o MATCH_MP
        (do_app_err |> REWRITE_RULE [GSYM AND_IMP_INTRO] |> GEN_ALL)) >>
      simp[] >>
      imp_res_tac EVERY2_REVERSE >>
      rpt(disch_then(fn th => first_assum(mp_tac o MATCH_MP th))) >>
      strip_tac >> simp[] >>
      first_assum(match_exists_tac o concl) >> simp[])
    \\ (Cases_on `a'`) \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
    \\ Cases_on `op = Ref` \\ full_simp_tac(srw_ss())[]
    THEN1
     (full_simp_tac(srw_ss())[closSemTheory.do_app_def,LET_DEF] \\ SRW_TAC [] []
      \\ full_simp_tac(srw_ss())[PULL_EXISTS]
      \\ Q.ABBREV_TAC `pp = LEAST ptr. ptr NOTIN FDOM p1.refs`
      \\ Q.ABBREV_TAC `qq = LEAST ptr. ptr NOTIN FDOM t2.refs`
      \\ full_simp_tac(srw_ss())[bvlSemTheory.do_app_def,LET_DEF]
      \\ Q.EXISTS_TAC `f2 |+ (pp,qq)` \\ full_simp_tac(srw_ss())[]
      \\ `~(pp IN FDOM p1.refs)` by
           (UNABBREV_ALL_TAC \\ full_simp_tac(srw_ss())[LEAST_NOTIN_FDOM] \\ NO_TAC)
      \\ `~(qq IN FDOM t2.refs)` by
           (UNABBREV_ALL_TAC \\ full_simp_tac(srw_ss())[LEAST_NOTIN_FDOM] \\ NO_TAC)
      \\ `~(pp IN FDOM f2)` by full_simp_tac(srw_ss())[state_rel_def]
      \\ `~(qq IN FRANGE f2)` by
        (REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[state_rel_def,SUBSET_DEF] \\ RES_TAC \\ NO_TAC)
      \\ `FRANGE (f2 \\ pp) = FRANGE f2` by ALL_TAC THEN1
       (full_simp_tac(srw_ss())[FRANGE_DEF,finite_mapTheory.DOMSUB_FAPPLY_THM,EXTENSION]
        \\ METIS_TAC []) \\ full_simp_tac(srw_ss())[]
      \\ fs[list_CASE_same] \\ rveq
      \\ conj_tac >- (full_simp_tac(srw_ss())[v_rel_cases,FLOOKUP_UPDATE])
      \\ conj_tac THEN1
       (full_simp_tac(srw_ss())[state_rel_def,FLOOKUP_UPDATE]
        \\ REPEAT STRIP_TAC THEN1
         (Q.PAT_ASSUM `LIST_REL ppp qqq rrr` MP_TAC
          \\ MATCH_MP_TAC listTheory.LIST_REL_mono
          \\ REPEAT STRIP_TAC
          \\ MATCH_MP_TAC OPTREL_v_rel_NEW_REF \\ full_simp_tac(srw_ss())[]
          \\ MATCH_MP_TAC OPTREL_v_rel_NEW_F \\ full_simp_tac(srw_ss())[])
        THEN1
         (Q.PAT_ASSUM `INJ ($' f2) (FDOM f2) (FRANGE f2)` MP_TAC
          \\ REPEAT (Q.PAT_ASSUM `INJ xx yy zz` (K ALL_TAC))
          \\ full_simp_tac(srw_ss())[INJ_DEF,FAPPLY_FUPDATE_THM,FRANGE_DEF]
          \\ REPEAT STRIP_TAC \\ METIS_TAC [])
        \\ Cases_on `n = pp` \\ full_simp_tac(srw_ss())[] THEN1
         (SRW_TAC [] [] >>
          imp_res_tac EVERY2_REVERSE
          \\ Q.PAT_ASSUM `LIST_REL _ (REVERSE a) (REVERSE ys)` MP_TAC
          \\ MATCH_MP_TAC listTheory.LIST_REL_mono
          \\ REPEAT STRIP_TAC
          \\ MATCH_MP_TAC v_rel_NEW_REF \\ full_simp_tac(srw_ss())[]
          \\ MATCH_MP_TAC v_rel_NEW_F \\ full_simp_tac(srw_ss())[])
        \\ RES_TAC \\ full_simp_tac(srw_ss())[]
        \\ `qq <> m` by (REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[FLOOKUP_DEF] \\ SRW_TAC [] [])
        \\ Cases_on`x`>>full_simp_tac(srw_ss())[]
        \\ Q.PAT_ASSUM `LIST_REL (v_rel f2 t2.refs t2.code) xs' ys'` MP_TAC
        \\ MATCH_MP_TAC listTheory.LIST_REL_mono
        \\ REPEAT STRIP_TAC
        \\ MATCH_MP_TAC v_rel_NEW_REF \\ full_simp_tac(srw_ss())[]
        \\ MATCH_MP_TAC v_rel_NEW_F \\ full_simp_tac(srw_ss())[])
      \\ conj_tac >-
       (full_simp_tac(srw_ss())[SUBMAP_DEF,FAPPLY_FUPDATE_THM,FDOM_FDIFF] \\ SRW_TAC [][] \\ METIS_TAC [] ) >>
      full_simp_tac(srw_ss())[SUBMAP_DEF,FDOM_FDIFF,FAPPLY_FUPDATE_THM,FDIFF_def,DRESTRICT_DEF] >> srw_tac[][] >> METIS_TAC[])
    \\ Cases_on `op = Update` \\ full_simp_tac(srw_ss())[] THEN1
     (full_simp_tac(srw_ss())[closSemTheory.do_app_def,bvlSemTheory.do_app_def]
      \\ Cases_on `REVERSE a` \\ full_simp_tac(srw_ss())[]
      \\ Cases_on `h` \\ full_simp_tac(srw_ss())[]
      \\ Cases_on `t` \\ full_simp_tac(srw_ss())[]
      \\ Cases_on `h` \\ full_simp_tac(srw_ss())[]
      \\ Cases_on `t'` \\ full_simp_tac(srw_ss())[]
      \\ Cases_on `t` \\ full_simp_tac(srw_ss())[]
      \\ Cases_on `FLOOKUP p1.refs n` \\ full_simp_tac(srw_ss())[]
      \\ Cases_on `x` \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
      \\ imp_res_tac EVERY2_REVERSE >>
      rev_full_simp_tac(srw_ss())[] >>
      srw_tac[][]
      \\ full_simp_tac(srw_ss())[v_rel_SIMP] \\ SRW_TAC [] []
      \\ `?y m.
            FLOOKUP f2 n = SOME m /\ FLOOKUP t2.refs m = SOME y /\
            ref_rel (v_rel f2 t2.refs t2.code) (ValueArray l) y` by
              METIS_TAC [state_rel_def]
      \\ full_simp_tac(srw_ss())[] \\ rpt var_eq_tac
      \\ simp[PULL_EXISTS]
      \\ srw_tac[][] >> full_simp_tac(srw_ss())[]
      \\ IMP_RES_TAC EVERY2_LENGTH \\ full_simp_tac(srw_ss())[]
      \\ Q.EXISTS_TAC `f2` \\ full_simp_tac(srw_ss())[]
      \\ rpt var_eq_tac >> simp[]
      \\ conj_tac >-
       (full_simp_tac(srw_ss())[state_rel_def,FLOOKUP_UPDATE] \\ REPEAT STRIP_TAC
        THEN1
         (Q.PAT_ASSUM `LIST_REL tt yy t2.globals` MP_TAC
          \\ MATCH_MP_TAC listTheory.LIST_REL_mono
          \\ REPEAT STRIP_TAC
          \\ MATCH_MP_TAC OPTREL_v_rel_UPDATE_REF \\ full_simp_tac(srw_ss())[]
          \\ full_simp_tac(srw_ss())[FLOOKUP_DEF,FRANGE_DEF] \\ METIS_TAC [])
        THEN1 (full_simp_tac(srw_ss())[EXTENSION,FLOOKUP_DEF] \\ METIS_TAC [])
        THEN1
         (`m IN FRANGE f2` by (full_simp_tac(srw_ss())[FLOOKUP_DEF,FRANGE_DEF] \\ METIS_TAC [])
          \\ full_simp_tac(srw_ss())[SUBSET_DEF] \\ METIS_TAC [])
        \\ SRW_TAC [] [] \\ Cases_on `n' = n` \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
        THEN1
         (full_simp_tac(srw_ss())[]
          \\ MATCH_MP_TAC EVERY2_LUPDATE_same
          \\ REPEAT STRIP_TAC THEN1
           (MATCH_MP_TAC v_rel_UPDATE_REF \\ full_simp_tac(srw_ss())[]
            \\ full_simp_tac(srw_ss())[FLOOKUP_DEF,FRANGE_DEF] \\ METIS_TAC [])
          \\ Q.PAT_ASSUM `LIST_REL (v_rel f2 t2.refs t2.code) l ys'` MP_TAC
          \\ MATCH_MP_TAC listTheory.LIST_REL_mono
          \\ REPEAT STRIP_TAC
          \\ MATCH_MP_TAC v_rel_UPDATE_REF \\ full_simp_tac(srw_ss())[]
          \\ full_simp_tac(srw_ss())[FLOOKUP_DEF,FRANGE_DEF] \\ METIS_TAC [])
        \\ RES_TAC \\ full_simp_tac(srw_ss())[]
        \\ `m' <> m''` by
         (Q.PAT_ASSUM `INJ ($' f2) (FDOM p1.refs) (FRANGE f2)` MP_TAC
          \\ SIMP_TAC std_ss [INJ_DEF,FRANGE_DEF] \\ full_simp_tac(srw_ss())[FLOOKUP_DEF]
          \\ METIS_TAC [])
        \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] [] \\ Cases_on`x` >> full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
        \\ Q.PAT_ASSUM `LIST_REL pp xs' ws''` MP_TAC
        \\ MATCH_MP_TAC listTheory.LIST_REL_mono
        \\ REPEAT STRIP_TAC
        \\ MATCH_MP_TAC v_rel_UPDATE_REF \\ full_simp_tac(srw_ss())[]
        \\ full_simp_tac(srw_ss())[FLOOKUP_DEF,FRANGE_DEF] \\ METIS_TAC [])
      \\ `m IN FRANGE f2` by (full_simp_tac(srw_ss())[FLOOKUP_DEF,FRANGE_DEF] \\ METIS_TAC [])
      \\ full_simp_tac(srw_ss())[SUBMAP_DEF,FDIFF_def,DRESTRICT_DEF,FAPPLY_FUPDATE_THM, add_args_def])
    \\ Cases_on `op = RefArray` \\ full_simp_tac(srw_ss())[] THEN1 (
      full_simp_tac(srw_ss())[closSemTheory.do_app_def,bvlSemTheory.do_app_def] >>
      Cases_on`REVERSE a`>>full_simp_tac(srw_ss())[]>>
      Cases_on`h`>>full_simp_tac(srw_ss())[]>>
      Cases_on`t`>>full_simp_tac(srw_ss())[]>>
      Cases_on`t'`>>full_simp_tac(srw_ss())[]>>
      Cases_on`a`>>full_simp_tac(srw_ss())[]>> rpt var_eq_tac >>
      full_simp_tac(srw_ss())[v_rel_SIMP,LET_THM] >> rpt var_eq_tac >>
      simp[PULL_EXISTS] >>
      IF_CASES_TAC >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
      qpat_abbrev_tac`pp = $LEAST P` >>
      qpat_abbrev_tac`qq = $LEAST P` >>
      simp[v_rel_SIMP] >>
      qexists_tac`f2 |+ (qq,pp)` >>
      simp[FLOOKUP_UPDATE] >>
      `f2 \\ qq = f2` by (
        full_simp_tac(srw_ss())[state_rel_def] >>
        MATCH_MP_TAC DOMSUB_NOT_IN_DOM >>
        simp[Abbr`qq`,LEAST_NOTIN_FDOM]) >>
      conj_tac >- (
        full_simp_tac(srw_ss())[state_rel_def] >>
        conj_tac >- (
          match_mp_tac(MP_CANON(GEN_ALL LIST_REL_mono)) >>
          ONCE_REWRITE_TAC[CONJ_COMM] >>
          first_assum(match_exists_tac o concl) >> simp[] >>
          rpt strip_tac >>
          match_mp_tac OPTREL_v_rel_NEW_REF >>
          reverse conj_tac >- (
            simp[Abbr`pp`,LEAST_NOTIN_FDOM] ) >>
          match_mp_tac OPTREL_v_rel_NEW_F >>
          simp[Abbr`pp`,Abbr`qq`,LEAST_NOTIN_FDOM] ) >>
        conj_tac >- (
          match_mp_tac INJ_FAPPLY_FUPDATE >> simp[] >>
          spose_not_then strip_assume_tac >>
          full_simp_tac(srw_ss())[SUBSET_DEF] >> res_tac >>
          full_simp_tac(srw_ss())[Abbr`pp`,LEAST_NOTIN_FDOM] ) >>
        conj_tac >- ( full_simp_tac(srw_ss())[SUBSET_DEF] ) >>
        simp[FLOOKUP_UPDATE] >>
        rpt gen_tac >> reverse IF_CASES_TAC >> simp[] >- (
          strip_tac >> res_tac >> simp[] >>
          Cases_on`pp=m`>>simp[]>-(
            `pp ∈ FRANGE f2` by (full_simp_tac(srw_ss())[FRANGE_FLOOKUP] >>METIS_TAC[]) >>
            full_simp_tac(srw_ss())[SUBSET_DEF] >> res_tac >>
            var_eq_tac >>
            full_simp_tac(srw_ss())[Abbr`m`,LEAST_NOTIN_FDOM] ) >>
          Cases_on`x`>>full_simp_tac(srw_ss())[] >>
          match_mp_tac(MP_CANON(GEN_ALL LIST_REL_mono)) >>
          ONCE_REWRITE_TAC[CONJ_COMM] >>
          first_assum(match_exists_tac o concl) >> simp[] >>
          rpt strip_tac >>
          match_mp_tac v_rel_NEW_REF >>
          reverse conj_tac >- (
            simp[Abbr`pp`,LEAST_NOTIN_FDOM] ) >>
          match_mp_tac v_rel_NEW_F >>
          simp[Abbr`pp`,Abbr`qq`,LEAST_NOTIN_FDOM] ) >>
        strip_tac >> var_eq_tac >> simp[] >>
        simp[LIST_REL_REPLICATE_same] >> srw_tac[][] >>
        match_mp_tac v_rel_NEW_REF >>
        reverse conj_tac >- (
          simp[Abbr`pp`,LEAST_NOTIN_FDOM] ) >>
        match_mp_tac v_rel_NEW_F >>
        simp[Abbr`pp`,Abbr`n`,LEAST_NOTIN_FDOM] ) >>
      conj_tac >- (
        match_mp_tac SUBMAP_TRANS >>
        first_assum(match_exists_tac o concl) >> simp[] >>
        disj1_tac >>
        full_simp_tac(srw_ss())[state_rel_def] >>
        simp[Abbr`qq`,LEAST_NOTIN_FDOM]) >>
      match_mp_tac SUBMAP_TRANS >>
      first_assum(match_exists_tac o concl) >> simp[] >>
      simp[FDIFF_def] >>
      simp[SUBMAP_DEF,FDOM_DRESTRICT,DRESTRICT_DEF] >>
      srw_tac[][] >>
      simp[Abbr`pp`,LEAST_NOTIN_FDOM])
    \\ Cases_on `op = RefByte` \\ full_simp_tac(srw_ss())[] THEN1 (
      full_simp_tac(srw_ss())[closSemTheory.do_app_def,bvlSemTheory.do_app_def] >>
      Cases_on`REVERSE a`>>full_simp_tac(srw_ss())[]>>
      Cases_on`h`>>full_simp_tac(srw_ss())[]>>
      Cases_on`t`>>full_simp_tac(srw_ss())[]>>
      Cases_on`h`>>full_simp_tac(srw_ss())[]>>
      Cases_on`t'`>>full_simp_tac(srw_ss())[]>>
      Cases_on`a`>>full_simp_tac(srw_ss())[]>> rpt var_eq_tac >>
      full_simp_tac(srw_ss())[v_rel_SIMP,LET_THM] >> rpt var_eq_tac >>
      simp[PULL_EXISTS] >>
      qpat_assum`_ = Rval _`mp_tac >>
      IF_CASES_TAC >> fsrw_tac[][] >> fsrw_tac[][] >> srw_tac[][] >>
      qpat_abbrev_tac`pp = $LEAST P` >>
      qpat_abbrev_tac`qq = $LEAST P` >>
      simp[v_rel_SIMP] >>
      qexists_tac`f2 |+ (qq,pp)` >>
      simp[FLOOKUP_UPDATE] >>
      `f2 \\ qq = f2` by (
        full_simp_tac(srw_ss())[state_rel_def] >>
        MATCH_MP_TAC DOMSUB_NOT_IN_DOM >>
        simp[Abbr`qq`,LEAST_NOTIN_FDOM]) >>
      conj_tac >- (
        full_simp_tac(srw_ss())[state_rel_def] >>
        conj_tac >- (
          match_mp_tac(MP_CANON(GEN_ALL LIST_REL_mono)) >>
          ONCE_REWRITE_TAC[CONJ_COMM] >>
          first_assum(match_exists_tac o concl) >> simp[] >>
          rpt strip_tac >>
          match_mp_tac OPTREL_v_rel_NEW_REF >>
          reverse conj_tac >- (
            simp[Abbr`pp`,LEAST_NOTIN_FDOM] ) >>
          match_mp_tac OPTREL_v_rel_NEW_F >>
          simp[Abbr`pp`,Abbr`qq`,LEAST_NOTIN_FDOM] ) >>
        conj_tac >- (
          match_mp_tac INJ_FAPPLY_FUPDATE >> simp[] >>
          spose_not_then strip_assume_tac >>
          full_simp_tac(srw_ss())[SUBSET_DEF] >> res_tac >>
          full_simp_tac(srw_ss())[Abbr`pp`,LEAST_NOTIN_FDOM] ) >>
        conj_tac >- ( full_simp_tac(srw_ss())[SUBSET_DEF] ) >>
        simp[FLOOKUP_UPDATE] >>
        rpt gen_tac >> reverse IF_CASES_TAC >> simp[] >- (
          strip_tac >> res_tac >> simp[] >>
          Cases_on`pp=m`>>simp[]>-(
            `pp ∈ FRANGE f2` by (full_simp_tac(srw_ss())[FRANGE_FLOOKUP] >>METIS_TAC[]) >>
            full_simp_tac(srw_ss())[SUBSET_DEF] >> res_tac >>
            var_eq_tac >>
            full_simp_tac(srw_ss())[Abbr`m`,LEAST_NOTIN_FDOM] ) >>
          Cases_on`x`>>full_simp_tac(srw_ss())[] >>
          match_mp_tac(MP_CANON(GEN_ALL LIST_REL_mono)) >>
          ONCE_REWRITE_TAC[CONJ_COMM] >>
          first_assum(match_exists_tac o concl) >> simp[] >>
          rpt strip_tac >>
          match_mp_tac v_rel_NEW_REF >>
          reverse conj_tac >- (
            simp[Abbr`pp`,LEAST_NOTIN_FDOM] ) >>
          match_mp_tac v_rel_NEW_F >>
          simp[Abbr`pp`,Abbr`qq`,LEAST_NOTIN_FDOM] ) >>
        strip_tac >> var_eq_tac >> simp[]) >>
      conj_tac >- (
        match_mp_tac SUBMAP_TRANS >>
        first_assum(match_exists_tac o concl) >> simp[] >>
        disj1_tac >>
        full_simp_tac(srw_ss())[state_rel_def] >>
        simp[Abbr`qq`,LEAST_NOTIN_FDOM]) >>
      match_mp_tac SUBMAP_TRANS >>
      first_assum(match_exists_tac o concl) >> simp[] >>
      simp[FDIFF_def] >>
      simp[SUBMAP_DEF,FDOM_DRESTRICT,DRESTRICT_DEF] >>
      srw_tac[][] >>
      simp[Abbr`pp`,LEAST_NOTIN_FDOM])
    \\ Cases_on `op = UpdateByte` \\ full_simp_tac(srw_ss())[] THEN1 (
      full_simp_tac(srw_ss())[closSemTheory.do_app_def,bvlSemTheory.do_app_def]
      \\ Cases_on `REVERSE a` \\ full_simp_tac(srw_ss())[]
      \\ Cases_on `h` \\ full_simp_tac(srw_ss())[]
      \\ Cases_on `t` \\ full_simp_tac(srw_ss())[]
      \\ Cases_on `h` \\ full_simp_tac(srw_ss())[]
      \\ Cases_on `t'` \\ full_simp_tac(srw_ss())[]
      \\ Cases_on `h` \\ full_simp_tac(srw_ss())[]
      \\ Cases_on `t` \\ full_simp_tac(srw_ss())[]
      \\ Cases_on `FLOOKUP p1.refs n` \\ full_simp_tac(srw_ss())[]
      \\ Cases_on `x` \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
      \\ imp_res_tac EVERY2_REVERSE >>
      rev_full_simp_tac(srw_ss())[] >>
      srw_tac[][]
      \\ full_simp_tac(srw_ss())[v_rel_SIMP] \\ SRW_TAC [] []
      \\ `?y m.
            FLOOKUP f2 n = SOME m /\ FLOOKUP t2.refs m = SOME y /\
            ref_rel (v_rel f2 t2.refs t2.code) (ByteArray l) y` by
              METIS_TAC [state_rel_def]
      \\ full_simp_tac(srw_ss())[] \\ rpt var_eq_tac
      \\ simp[PULL_EXISTS]
      \\ qpat_assum`_ = Rval _`mp_tac
      \\ srw_tac[][] >> fsrw_tac[][]
      \\ IMP_RES_TAC EVERY2_LENGTH \\ fsrw_tac[][]
      \\ Q.EXISTS_TAC `f2` \\ fsrw_tac[][]
      \\ rpt var_eq_tac >> simp[]
      \\ conj_tac >-
       (full_simp_tac(srw_ss())[state_rel_def,FLOOKUP_UPDATE] \\ REPEAT STRIP_TAC
        THEN1
         (Q.PAT_ASSUM `LIST_REL tt yy t2.globals` MP_TAC
          \\ MATCH_MP_TAC listTheory.LIST_REL_mono
          \\ REPEAT STRIP_TAC
          \\ MATCH_MP_TAC OPTREL_v_rel_UPDATE_REF \\ full_simp_tac(srw_ss())[]
          \\ full_simp_tac(srw_ss())[FLOOKUP_DEF,FRANGE_DEF] \\ METIS_TAC [])
        THEN1 (full_simp_tac(srw_ss())[EXTENSION,FLOOKUP_DEF] \\ METIS_TAC [])
        THEN1
         (`m IN FRANGE f2` by (full_simp_tac(srw_ss())[FLOOKUP_DEF,FRANGE_DEF] \\ METIS_TAC [])
          \\ full_simp_tac(srw_ss())[SUBSET_DEF] \\ METIS_TAC [])
        \\ SRW_TAC [] [] \\ Cases_on `n' = n` \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
        \\ RES_TAC \\ full_simp_tac(srw_ss())[]
        \\ `m' <> m''` by
         (Q.PAT_ASSUM `INJ ($' f2) (FDOM p1.refs) (FRANGE f2)` MP_TAC
          \\ SIMP_TAC std_ss [INJ_DEF,FRANGE_DEF] \\ full_simp_tac(srw_ss())[FLOOKUP_DEF]
          \\ METIS_TAC [])
        \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] [] \\ Cases_on`x` >> full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
        \\ Q.PAT_ASSUM `LIST_REL pp xs' ws''` MP_TAC
        \\ MATCH_MP_TAC listTheory.LIST_REL_mono
        \\ REPEAT STRIP_TAC
        \\ MATCH_MP_TAC v_rel_UPDATE_REF \\ full_simp_tac(srw_ss())[]
        \\ full_simp_tac(srw_ss())[FLOOKUP_DEF,FRANGE_DEF] \\ METIS_TAC [])
      \\ `m IN FRANGE f2` by (full_simp_tac(srw_ss())[FLOOKUP_DEF,FRANGE_DEF] \\ METIS_TAC [])
      \\ full_simp_tac(srw_ss())[SUBMAP_DEF,FDIFF_def,DRESTRICT_DEF,FAPPLY_FUPDATE_THM, add_args_def])
    \\ Cases_on `∃n. op = FFI n` \\ full_simp_tac(srw_ss())[] THEN1 (
      full_simp_tac(srw_ss())[closSemTheory.do_app_def,bvlSemTheory.do_app_def]
      \\ Cases_on `REVERSE a` \\ full_simp_tac(srw_ss())[]
      \\ Cases_on `h` \\ full_simp_tac(srw_ss())[]
      \\ Cases_on `t` \\ full_simp_tac(srw_ss())[]
      \\ srw_tac[][]
      \\ simp[PULL_EXISTS]
      \\ full_simp_tac(srw_ss())[v_rel_SIMP] \\ srw_tac[][]
      \\ qmatch_assum_rename_tac`FLOOKUP f2 k = SOME r2`
      \\ Cases_on`FLOOKUP p1.refs k` \\ full_simp_tac(srw_ss())[]
      \\ Cases_on`x` \\ full_simp_tac(srw_ss())[]
      \\ Cases_on`call_FFI p1.ffi n l` \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
      \\ `?y m.
            FLOOKUP f2 k = SOME m /\ FLOOKUP t2.refs m = SOME y /\
            ref_rel (v_rel f2 t2.refs t2.code) (ByteArray l) y` by
              METIS_TAC [state_rel_def]
      \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
      \\ `t2.ffi = p1.ffi` by METIS_TAC[state_rel_def]
      \\ simp[]
      \\ qexists_tac`f2` \\ simp[]
      \\ conj_tac >-
       (full_simp_tac(srw_ss())[state_rel_def,FLOOKUP_UPDATE] \\ REPEAT STRIP_TAC
        THEN1
         (Q.PAT_ASSUM `LIST_REL tt yy t2.globals` MP_TAC
          \\ MATCH_MP_TAC listTheory.LIST_REL_mono
          \\ REPEAT STRIP_TAC
          \\ MATCH_MP_TAC OPTREL_v_rel_UPDATE_REF \\ full_simp_tac(srw_ss())[]
          \\ full_simp_tac(srw_ss())[FLOOKUP_DEF,FRANGE_DEF] \\ METIS_TAC [])
        THEN1 (full_simp_tac(srw_ss())[EXTENSION,FLOOKUP_DEF] \\ METIS_TAC [])
        THEN1
         (`m IN FRANGE f2` by (full_simp_tac(srw_ss())[FLOOKUP_DEF,FRANGE_DEF] \\ METIS_TAC [])
          \\ full_simp_tac(srw_ss())[SUBSET_DEF] \\ METIS_TAC [])
        \\ SRW_TAC [] [] \\ Cases_on `n' = k` \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
        \\ RES_TAC \\ full_simp_tac(srw_ss())[]
        \\ `m' <> m''` by
         (Q.PAT_ASSUM `INJ ($' f2) (FDOM p1.refs) (FRANGE f2)` MP_TAC
          \\ SIMP_TAC std_ss [INJ_DEF,FRANGE_DEF] \\ full_simp_tac(srw_ss())[FLOOKUP_DEF]
          \\ METIS_TAC [])
        \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] [] \\ Cases_on`x` >> full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
        \\ Q.PAT_ASSUM `LIST_REL pp xs' ws''` MP_TAC
        \\ MATCH_MP_TAC listTheory.LIST_REL_mono
        \\ REPEAT STRIP_TAC
        \\ MATCH_MP_TAC v_rel_UPDATE_REF \\ full_simp_tac(srw_ss())[]
        \\ full_simp_tac(srw_ss())[FLOOKUP_DEF,FRANGE_DEF] \\ METIS_TAC [])
      \\ `m IN FRANGE f2` by (full_simp_tac(srw_ss())[FLOOKUP_DEF,FRANGE_DEF] \\ METIS_TAC [])
      \\ full_simp_tac(srw_ss())[SUBMAP_DEF,FDIFF_def,DRESTRICT_DEF,FAPPLY_FUPDATE_THM, add_args_def])
    \\ imp_res_tac closSemTheory.do_app_const
    \\ first_x_assum(mp_tac o MATCH_MP
         (GEN_ALL(REWRITE_RULE[GSYM AND_IMP_INTRO]do_app)))
    \\ first_x_assum(fn th => disch_then (mp_tac o C MATCH_MP th))
    \\ imp_res_tac EVERY2_REVERSE
    \\ first_x_assum(fn th => disch_then (mp_tac o C MATCH_MP th)) \\ srw_tac[][] \\ srw_tac[][]
    \\ Q.EXISTS_TAC `f2` \\ full_simp_tac(srw_ss())[]
    \\ imp_res_tac bvlSemTheory.do_app_const
    \\ simp[])
  THEN1 (* Fn *)
   (srw_tac[][] >>
    full_simp_tac(srw_ss())[cEval_def]
    \\ every_case_tac
    \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
    \\ full_simp_tac(srw_ss())[compile_exps_def]
    \\ `?c2 aux3. compile_exps [exp] aux1 = (c2,aux3)` by METIS_TAC [PAIR]
    \\ full_simp_tac(srw_ss())[LET_DEF] \\ SRW_TAC [] []
    \\ full_simp_tac(srw_ss())[code_installed_def]
    \\ full_simp_tac(srw_ss())[bEval_def,bvlPropsTheory.evaluate_APPEND,bvlSemTheory.do_app_def,domain_lookup]
    \\ full_simp_tac(srw_ss())[clos_env_def]
    \\ IMP_RES_TAC lookup_vars_IMP
    \\ POP_ASSUM (qspec_then `t1 with clock := s.clock` strip_assume_tac)
    \\ imp_res_tac bvlPropsTheory.evaluate_var_reverse
    \\ qexists_tac`0`>>simp[]
    \\ Cases_on `num_args ≤ max_app ∧ num_args ≠ 0`
    \\ full_simp_tac(srw_ss())[]
    \\ srw_tac[][]
    \\ full_simp_tac(srw_ss())[v_rel_cases, cl_rel_cases]
    \\ fsrw_tac[ARITH_ss][] >> var_eq_tac
    \\ simp[PULL_EXISTS]
    \\ first_assum(match_exists_tac o concl) >> simp[]
    \\ Cases_on`loc`>>full_simp_tac(srw_ss())[]
    \\ fsrw_tac[ARITH_ss][]
    \\ IMP_RES_TAC compile_exps_SING \\ full_simp_tac(srw_ss())[code_installed_def]
    \\ first_assum(match_exists_tac o concl) >> simp[])
  THEN1 (* Letrec *)
   (srw_tac[][] >>
    full_simp_tac(srw_ss())[cEval_def]
    \\ `∃names. namesopt = SOME names` by (Cases_on`namesopt`>>full_simp_tac(srw_ss())[])
    \\ full_simp_tac(srw_ss())[] \\ BasicProvers.FULL_CASE_TAC
    \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
    \\ full_simp_tac(srw_ss())[compile_exps_def]
    \\ full_simp_tac(srw_ss())[build_recc_def,clos_env_def]
    \\ full_simp_tac(srw_ss())[IS_SOME_EXISTS] \\ var_eq_tac \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `lookup_vars names env` \\ full_simp_tac(srw_ss())[LET_THM] \\ SRW_TAC [] []
    \\ Cases_on `fns` \\ full_simp_tac(srw_ss())[]
    THEN1 (rev_full_simp_tac(srw_ss())[] \\ FIRST_X_ASSUM MATCH_MP_TAC
           \\ Q.LIST_EXISTS_TAC [`aux1`] \\ full_simp_tac(srw_ss())[]
           \\ Cases_on`loc`>>full_simp_tac(srw_ss())[LET_THM])
    \\ Cases_on `t` \\ full_simp_tac(srw_ss())[] \\ rev_full_simp_tac(srw_ss())[]
    THEN1 (* special case for singly-recursive closure *)
     (`?num_args body. h = (num_args, body)` by metis_tac [pair_CASES] >>
      srw_tac[][] >>
      full_simp_tac(srw_ss())[] >>
      `?c2 aux3. compile_exps [body] aux1 = ([c2],aux3)` by
              METIS_TAC [PAIR,compile_exps_SING]
      \\ full_simp_tac(srw_ss())[LET_THM]
      \\ first_assum(split_uncurry_arg_tac o lhs o concl)
      \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
      \\ simp[bEval_def, bvlPropsTheory.evaluate_APPEND, bvlSemTheory.do_app_def]
      \\ IMP_RES_TAC lookup_vars_IMP
      \\ Cases_on `num_args ≤ max_app ∧ num_args ≠ 0` >>
      full_simp_tac(srw_ss())[] >> full_simp_tac(srw_ss())[] >>
      first_x_assum(qspec_then`t1 with clock := s.clock` STRIP_ASSUME_TAC) >>
      `env_rel f1 t1.refs t1.code (Recclosure (SOME x) [] x' [(num_args,body)] 0::env) (Block closure_tag (CodePtr (x + num_stubs)::Number (&(num_args − 1))::ys)::env'')`
               by (srw_tac[][env_rel_def] >>
                   srw_tac[][v_rel_cases, EXISTS_OR_THM] >>
                   first_assum(match_exists_tac o concl) >>
                   srw_tac[][cl_rel_cases, PULL_EXISTS]
                   \\ IMP_RES_TAC compile_exps_IMP_code_installed
                   \\ full_simp_tac(srw_ss())[code_installed_def] >>
                   simp [GSYM ADD1, GENLIST] >>
                   metis_tac []) >>
      simp [REVERSE_APPEND] >>
      srw_tac[][] >>
      first_x_assum (fn th => first_assum (assume_tac o MATCH_MP (SIMP_RULE (srw_ss()) [GSYM AND_IMP_INTRO] th))) >>
      rpt (pop_assum (fn th => first_assum (strip_assume_tac o MATCH_MP th))) >>
      full_simp_tac(srw_ss())[code_installed_def] >>
      imp_res_tac evaluate_var_reverse >>
      full_simp_tac(srw_ss())[domain_lookup] >>
      imp_res_tac evaluate_add_clock >>
      fsrw_tac[ARITH_ss] [inc_clock_def]
      \\ qmatch_assum_abbrev_tac`compile_exps [exp] auxx = zz`
      \\ qspecl_then[`[exp]`,`auxx`]strip_assume_tac compile_exps_acc
      \\ rev_full_simp_tac(srw_ss())[Abbr`zz`,LET_THM] >> full_simp_tac(srw_ss())[Abbr`auxx`]
      \\ srw_tac[][REVERSE_APPEND]
      \\ imp_res_tac compile_exps_SING \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
      \\ qexists_tac`ck`>>simp[]
      \\ Q.LIST_EXISTS_TAC [`f2`] \\ full_simp_tac(srw_ss())[])
    (* general case for mutually recursive closures *)
    \\ `0 < LENGTH (h::h'::t') /\ 1 < LENGTH (h::h'::t')` by (full_simp_tac(srw_ss())[] \\ DECIDE_TAC)
    \\ `SUC (SUC (LENGTH t')) = LENGTH (h::h'::t')` by full_simp_tac(srw_ss())[]
    \\ Q.ABBREV_TAC `exps = h::h'::t'` \\ full_simp_tac(srw_ss())[]
    \\ `SND h::SND h'::MAP SND t' = MAP SND exps` by srw_tac[][Abbr `exps`]
    \\ `FST h::FST h'::MAP FST t' = MAP FST exps` by srw_tac[][Abbr `exps`]
    \\ full_simp_tac(srw_ss())[if_expand]
    \\ srw_tac[][]
    \\ full_simp_tac(srw_ss())[]
    \\ `EVERY (λ(num_args,e). num_args ≤ max_app ∧ num_args ≠ 0) exps` by srw_tac[][Abbr `exps`]
    \\ pop_assum mp_tac
    \\ `every_Fn_SOME (MAP SND exps)` by (full_simp_tac(srw_ss())[Abbr`exps`])
    \\ `every_Fn_vs_SOME (MAP SND exps)` by (full_simp_tac(srw_ss())[Abbr`exps`])
    \\ ntac 2 (pop_assum mp_tac)
    \\ NTAC 4 (POP_ASSUM (K ALL_TAC))
    \\ ntac 3 DISCH_TAC
    \\ `?c7 aux7. compile_exps (MAP SND exps) aux1 = (c7,aux7)` by METIS_TAC [PAIR]
    \\ `?n4 aux5. build_aux (x + num_stubs)
           (MAP2 (code_for_recc_case (LENGTH exps + LENGTH names)) (MAP FST exps) c7)
           aux7 = (n4,aux5)` by METIS_TAC [PAIR]
    \\ `?c8 aux8. compile_exps [exp] aux5 = (c8,aux8)` by METIS_TAC [PAIR]
    \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
    \\ FIRST_X_ASSUM (Q.SPECL_THEN [`aux5`]mp_tac) \\ full_simp_tac(srw_ss())[]
    \\ REPEAT STRIP_TAC
    \\ full_simp_tac(srw_ss())[build_recc_lets_def]
    \\ full_simp_tac(srw_ss())[bvlSemTheory.do_app_def,bEval_def,LET_DEF]
    \\ full_simp_tac(srw_ss())[bvlPropsTheory.evaluate_APPEND,evaluate_MAP_Const, REVERSE_APPEND]
    \\ IMP_RES_TAC lookup_vars_IMP2
    \\ `!t1:'ffi bvlSem$state. evaluate (REVERSE (MAP Var names), env'', t1) = (Rval (REVERSE ys), t1)`
        by metis_tac [evaluate_var_reverse, REVERSE_REVERSE]
    \\ full_simp_tac(srw_ss())[]
    \\ srw_tac[][GSYM MAP_REVERSE]
    \\ srw_tac[][evaluate_MAP_Const]
    \\ Q.ABBREV_TAC `rr = LEAST ptr. ptr NOTIN FDOM t1.refs`
    \\ full_simp_tac(srw_ss())[recc_Let0_def]
    \\ `x + num_stubs + 2* (LENGTH exps - 1) IN domain t1.code` by
     (IMP_RES_TAC compile_exps_IMP_code_installed
      \\ IMP_RES_TAC compile_exps_LENGTH
      \\ full_simp_tac(srw_ss())[domain_lookup,code_installed_def]
      \\ IMP_RES_TAC build_aux_MEM \\ full_simp_tac(srw_ss())[]
      \\ rev_full_simp_tac(srw_ss())[LENGTH_MAP2]
      \\ `LENGTH exps - 1 < LENGTH exps` by DECIDE_TAC
      \\ RES_TAC
      \\ full_simp_tac(srw_ss())[code_installed_def,EVERY_MEM] \\ full_simp_tac(srw_ss())[]
      \\ RES_TAC \\ full_simp_tac(srw_ss())[] \\ PairCases_on `d` \\ full_simp_tac(srw_ss())[])
    \\ full_simp_tac(srw_ss())[bEval_def,bvlSemTheory.do_app_def,DECIDE ``1 < m + 1 + SUC n``,
           DECIDE ``0 < 1 + SUC n``, DECIDE ``1 < n + (1 + SUC m)``,
           DECIDE ``m < 1 + (m + n):num``]
    \\ `0 < LENGTH exps + LENGTH ys` by DECIDE_TAC
    \\ ASM_SIMP_TAC (srw_ss()) [FLOOKUP_DEF, DECIDE ``n < 1 + (n + m):num``]
    \\ `exps <> []` by (full_simp_tac(srw_ss())[GSYM LENGTH_NIL] \\ DECIDE_TAC)
    \\ `?ll x. exps = SNOC x ll` by METIS_TAC [SNOC_CASES] \\ full_simp_tac(srw_ss())[]
    \\ simp [REVERSE_APPEND, MAP_REVERSE, LENGTH_MAP]
    \\ `LENGTH ll = LENGTH ((MAP (K (Number 0)) (MAP FST ll)) : bvlSem$v list)`
         by full_simp_tac(srw_ss())[LENGTH_MAP]
    \\ POP_ASSUM (fn th => REWRITE_TAC [th])
    \\ srw_tac[][lupdate_append2]
    \\ `EVERY (\n. x + num_stubs + 2*n IN domain t1.code) (GENLIST I (LENGTH ll))` by
     (full_simp_tac(srw_ss())[EVERY_GENLIST]
      \\ IMP_RES_TAC compile_exps_IMP_code_installed
      \\ IMP_RES_TAC compile_exps_LENGTH
      \\ full_simp_tac(srw_ss())[domain_lookup,code_installed_def]
      \\ IMP_RES_TAC build_aux_MEM \\ full_simp_tac(srw_ss())[]
      \\ rev_full_simp_tac(srw_ss())[LENGTH_MAP2]
      \\ REPEAT STRIP_TAC
      \\ `i < LENGTH ll + 1` by ALL_TAC THEN1
       (IMP_RES_TAC compile_exps_LENGTH \\ full_simp_tac(srw_ss())[LENGTH_APPEND]
        \\ DECIDE_TAC)
      \\ RES_TAC
      \\ full_simp_tac(srw_ss())[code_installed_def,EVERY_MEM] \\ full_simp_tac(srw_ss())[]
      \\ RES_TAC \\ full_simp_tac(srw_ss())[] \\ PairCases_on `d` \\ full_simp_tac(srw_ss())[])
    \\ full_simp_tac(srw_ss())[hd_append, tl_append]
    \\ simp [SIMP_RULE(srw_ss())[]evaluate_recc_Lets]
    \\ `[HD c8] = c8` by (IMP_RES_TAC compile_exps_SING \\ full_simp_tac(srw_ss())[]) \\ full_simp_tac(srw_ss())[]
    \\ qpat_abbrev_tac`t1refs = t1.refs |+ (rr,vv)`
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`t1 with <| refs := t1refs; clock := ck+s.clock|>`,
       `MAP2 (\n args. Block closure_tag [CodePtr (x + num_stubs + 2*n); Number &(args-1); RefPtr rr])
          (GENLIST I (LENGTH (ll:(num#closLang$exp) list) + 1)) (MAP FST ll ++ [FST (x'':(num#closLang$exp))]) ++ env''`,`f1`])
    \\ `~(rr IN FDOM t1.refs)` by ALL_TAC THEN1
     (UNABBREV_ALL_TAC
      \\ SIMP_TAC std_ss [FDIFF_def,SUBMAP_DEF]
      \\ full_simp_tac(srw_ss())[DRESTRICT_DEF,FAPPLY_FUPDATE_THM]
      \\ REPEAT STRIP_TAC \\ SRW_TAC [] []
      \\ ASSUME_TAC (EXISTS_NOT_IN_refs |>
           SIMP_RULE std_ss [whileTheory.LEAST_EXISTS]) \\ full_simp_tac(srw_ss())[])
    \\ MATCH_MP_TAC IMP_IMP \\ reverse STRIP_TAC
    >- (REPEAT STRIP_TAC
        \\ qexists_tac`ck'`
        \\ full_simp_tac (srw_ss()++ARITH_ss) [Abbr `t1refs`]
        \\ srw_tac[][]
        \\ Q.EXISTS_TAC `f2` \\ IMP_RES_TAC SUBMAP_TRANS
        \\ ASM_SIMP_TAC std_ss []
        \\ FIRST_X_ASSUM MATCH_MP_TAC
        \\ UNABBREV_ALL_TAC
        \\ SIMP_TAC std_ss [FDIFF_def,SUBMAP_DEF]
        \\ full_simp_tac(srw_ss())[DRESTRICT_DEF,FAPPLY_FUPDATE_THM]
        \\ REPEAT STRIP_TAC \\ SRW_TAC [] []
        \\ ASSUME_TAC (EXISTS_NOT_IN_refs |>
             SIMP_RULE std_ss [whileTheory.LEAST_EXISTS]) \\ full_simp_tac(srw_ss())[])
    THEN1
     (reverse (REPEAT STRIP_TAC) THEN1
       (full_simp_tac(srw_ss())[state_rel_def,Abbr`t1refs`] \\ STRIP_TAC THEN1
         (Q.PAT_ASSUM `LIST_REL ppp s.globals t1.globals` MP_TAC
          \\ MATCH_MP_TAC listTheory.LIST_REL_mono
          \\ METIS_TAC [OPTREL_v_rel_NEW_REF])
        \\ STRIP_TAC THEN1 full_simp_tac(srw_ss())[SUBSET_DEF]
        \\ REPEAT STRIP_TAC \\ RES_TAC \\ full_simp_tac(srw_ss())[FLOOKUP_UPDATE]
        \\ `m <> rr` by (REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[FLOOKUP_DEF]) \\ full_simp_tac(srw_ss())[]
        \\ Cases_on`x'''`>>full_simp_tac(srw_ss())[]
        \\ Q.PAT_ASSUM `LIST_REL ppp xs ys'` MP_TAC
        \\ MATCH_MP_TAC listTheory.LIST_REL_mono
        \\ IMP_RES_TAC v_rel_NEW_REF \\ full_simp_tac(srw_ss())[])
      \\ TRY (simp[] \\ NO_TAC)
      \\ MATCH_MP_TAC env_rel_APPEND
      \\ reverse STRIP_TAC THEN1
       (UNABBREV_ALL_TAC \\ full_simp_tac(srw_ss())[]
        \\ MATCH_MP_TAC (env_rel_NEW_REF |> GEN_ALL) \\ full_simp_tac(srw_ss())[])
      \\ srw_tac[][LIST_REL_EL_EQN, LENGTH_GENLIST, LENGTH_MAP2, el_map2]
      \\ srw_tac[][v_rel_cases, cl_rel_cases]
      \\ full_simp_tac(srw_ss())[]
      \\ srw_tac [boolSimps.DNF_ss] []
      \\ disj2_tac
      \\ qexists_tac `ys`
      \\ qabbrev_tac `exps = ll++[x'']`
      \\ `LENGTH ll + 1 = LENGTH exps` by full_simp_tac(srw_ss())[Abbr `exps`]
      \\ Q.EXISTS_TAC `ZIP (exps,GENLIST (\i.x+num_stubs+2*i) (LENGTH exps))`
      \\ full_simp_tac(srw_ss())[LENGTH_ZIP, EL_MAP, LENGTH_MAP, EL_ZIP, MAP_ZIP]
      \\ `?num e. EL n exps = (num, e)` by metis_tac [pair_CASES]
      \\ `1 < LENGTH exps` by (full_simp_tac(srw_ss())[] \\ DECIDE_TAC)
      \\ full_simp_tac(srw_ss())[Abbr `t1refs`,FLOOKUP_UPDATE]
      \\ `MAP FST ll ++ [FST x''] = MAP FST exps` by srw_tac[][Abbr `exps`]
      \\ simp [EL_MAP]
      \\ srw_tac[][]
      THEN1
       (Q.PAT_ASSUM `LIST_REL (v_rel f1 t1.refs t1.code) x' ys` MP_TAC
        \\ MATCH_MP_TAC listTheory.LIST_REL_mono
        \\ METIS_TAC [v_rel_NEW_REF])
      THEN1
       (full_simp_tac(srw_ss())[state_rel_def, SUBSET_DEF] >> metis_tac [])
      THEN1
       (rpt (pop_assum kall_tac)
        \\ Q.SPEC_TAC (`exps`, `exps`)
        \\ recInduct SNOC_INDUCT
        \\ srw_tac[][GENLIST, GSYM ADD1]
        \\ rw_tac std_ss [GSYM SNOC_APPEND, map2_snoc, LENGTH_GENLIST, LENGTH_MAP]
        \\ srw_tac[][GSYM ZIP_APPEND]
        \\ PairCases_on `x'`
        \\ simp [])
      THEN1 ( full_simp_tac(srw_ss())[Abbr`exps`])
      THEN1 ( full_simp_tac(srw_ss())[Abbr`exps`])
      \\ full_simp_tac(srw_ss())[closure_code_installed_def]
      \\ MATCH_MP_TAC EVERY_ZIP_GENLIST \\ full_simp_tac(srw_ss())[AC ADD_ASSOC ADD_COMM]
      \\ REPEAT STRIP_TAC
      \\ IMP_RES_TAC compile_exps_IMP_code_installed
      \\ `EVERY (λ(num_args,e). num_args ≤ max_app ∧ num_args ≠ 0) exps` by full_simp_tac(srw_ss())[Abbr `exps`]
      \\ full_simp_tac(srw_ss())[EVERY_EL]
      \\ res_tac
      \\ `?num e. EL i exps = (num, e)` by metis_tac [pair_CASES]
      \\ full_simp_tac(srw_ss())[]
      \\ REWRITE_TAC[ADD_ASSOC]
      \\ MATCH_MP_TAC (compile_exps_LIST_IMP_compile_exps_EL |> SPEC_ALL)
      \\ full_simp_tac(srw_ss())[Abbr`exps`]))
  THEN1 (* App *)
   (srw_tac[][] >>
    full_simp_tac(srw_ss())[cEval_def, compile_exps_def]
    \\ `?res6 s6. evaluate (args,env,s) = (res6,s6)` by METIS_TAC [PAIR]
    \\ `?res5 s5. evaluate ([x1],env,s6) = (res5,s5)` by METIS_TAC [PAIR]
    \\ `?c7 aux7. compile_exps [x1] aux1 = ([c7],aux7)` by
          METIS_TAC [PAIR,compile_exps_SING]
    \\ `?c8 aux8. compile_exps args aux7 = (c8,aux8)` by
          METIS_TAC [PAIR,compile_exps_SING]
    \\ full_simp_tac(srw_ss())[LET_DEF] \\ SRW_TAC [] []
    \\ Cases_on `LENGTH args > 0` >> full_simp_tac(srw_ss())[]
    \\ reverse (Cases_on `res6`) \\ full_simp_tac(srw_ss())[]
    >- (res_tac >> srw_tac[][] >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
        imp_res_tac evaluate_app_helper >> full_simp_tac(srw_ss())[] >>
        metis_tac [])
    \\ `code_installed aux1 t1.code` by IMP_RES_TAC compile_exps_IMP_code_installed
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`aux7`,`t1`,`env''`,`f1`]) \\ full_simp_tac(srw_ss())[]
    \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[]
    \\ `code_installed aux7 t1.code` by IMP_RES_TAC compile_exps_IMP_code_installed
    \\ `t2.code = t1.code` by (IMP_RES_TAC evaluate_code >> full_simp_tac(srw_ss())[])
    \\ `code_installed aux7 t2.code` by metis_tac []
    \\ `env_rel f2 t2.refs t2.code env env''` by metis_tac [env_rel_SUBMAP]
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`aux1`,`t2`,`env''`,`f2`]) \\ full_simp_tac(srw_ss())[]
    \\ impl_tac >- (
        imp_res_tac evaluate_const >> full_simp_tac(srw_ss())[] >>
        spose_not_then strip_assume_tac >> full_simp_tac(srw_ss())[] )
    \\ disch_then (strip_assume_tac o SIMP_RULE (srw_ss()) [GSYM RIGHT_EXISTS_IMP_THM]) >>
    `evaluate (c8,env'',t1 with clock := s.clock + ck + ck') = (Rval v',inc_clock ck' t2)`
                by (imp_res_tac evaluate_add_clock >>
                    full_simp_tac(srw_ss())[inc_clock_def])
    \\ reverse (Cases_on `res5`) \\ full_simp_tac(srw_ss())[inc_clock_def]
    >- (srw_tac[][] >>
        imp_res_tac evaluate_app_helper2 >>
        rev_full_simp_tac(srw_ss())[] >>
        metis_tac [SUBMAP_TRANS, ADD_ASSOC])
    \\ imp_res_tac cEval_SING
    \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
    \\ imp_res_tac bvlPropsTheory.evaluate_IMP_LENGTH
    \\ imp_res_tac compile_exps_LENGTH
    \\ `t2'.code = t1.code` by (imp_res_tac evaluate_code >> full_simp_tac(srw_ss())[])
    \\ `LIST_REL (v_rel f2' t2'.refs t2'.code) a v'`
              by metis_tac [LIST_REL_mono, v_rel_SUBMAP]
    \\ res_tac
    \\ pop_assum mp_tac
    \\ REWRITE_TAC[AND_IMP_INTRO]
    \\ impl_tac >- metis_tac[evaluate_const]
    \\ disch_then (qspec_then `env''` strip_assume_tac)
    \\ `LENGTH v' ≠ 0 ∧ 0 < LENGTH v' ∧ LENGTH args = LENGTH v'` by decide_tac
    \\ full_simp_tac(srw_ss())[]
    \\ qexists_tac `ck+ck'+ck''` >>
    srw_tac[][] >>
    `evaluate (c8,env'',t1 with clock := ck + ck' + ck'' + s.clock) = (Rval v',inc_clock (ck'+ck'') t2)`
                by (imp_res_tac evaluate_add_clock >>
                    fsrw_tac[ARITH_ss][inc_clock_def]) >>
    `evaluate ([c7],env'',inc_clock (ck' + ck'') t2) = (Rval [y],inc_clock ck'' t2')`
                by (imp_res_tac evaluate_add_clock >>
                    fsrw_tac[ARITH_ss][inc_clock_def])
    \\ Cases_on `loc_opt`
    \\ simp [bEval_def, bvlPropsTheory.evaluate_APPEND]
    \\ full_simp_tac(srw_ss())[] >> srw_tac[][ADD_ASSOC] >> srw_tac[][] >- metis_tac [SUBMAP_TRANS, inc_clock_def]
    \\ rev_full_simp_tac(srw_ss())[]
    \\ reverse (Cases_on `find_code (SOME (x + num_stubs)) (v' ++ [y]) t1.code`)
    \\ full_simp_tac(srw_ss())[]
    >- (Cases_on `x'` >>
        srw_tac[][inc_clock_def] >>
        full_simp_tac(srw_ss())[] >>
        srw_tac[][] >>
        full_simp_tac(srw_ss())[dec_clock_def] >>
        srw_tac[][] >>
        metis_tac [SUBMAP_TRANS])
    \\ srw_tac[][]
    \\ full_simp_tac(srw_ss())[])
  THEN1 (* Tick *)
   (srw_tac[][] >>
    full_simp_tac(srw_ss())[compile_exps_def]
    \\ `?p. evaluate ([x],env,s) = p` by full_simp_tac(srw_ss())[] \\ PairCases_on `p` \\ full_simp_tac(srw_ss())[]
    \\ `?cc. compile_exps [x] aux1 = cc` by full_simp_tac(srw_ss())[] \\ PairCases_on `cc` \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[LET_DEF] \\ SRW_TAC [] []
    \\ IMP_RES_TAC compile_exps_SING \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[bEval_def]
    \\ Cases_on `s.clock = 0` \\ full_simp_tac(srw_ss())[] THEN1
     (full_simp_tac(srw_ss())[cEval_def] \\ SRW_TAC [] []
      \\ qexists_tac `0`
      \\ srw_tac[][]
      \\ Q.EXISTS_TAC `f1` \\ full_simp_tac(srw_ss())[SUBMAP_REFL])
    \\ full_simp_tac(srw_ss())[cEval_def]
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`aux1`]) \\ full_simp_tac(srw_ss())[]
    \\ REPEAT STRIP_TAC
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`dec_clock 1 t1`,`env''`,`f1`])
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
      (full_simp_tac(srw_ss())[bvlSemTheory.dec_clock_def,closSemTheory.dec_clock_def,state_rel_def])
    \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[]
    \\ qexists_tac `ck`
    \\ `s.clock − 1 + ck = s.clock + ck - 1` by simp []
    \\ full_simp_tac(srw_ss())[bvlSemTheory.dec_clock_def, closSemTheory.dec_clock_def]
    \\ Q.EXISTS_TAC `f2` \\ full_simp_tac(srw_ss())[bvlSemTheory.dec_clock_def])
  THEN1 (* Call *)
   (srw_tac[][] >>
    full_simp_tac(srw_ss())[compile_exps_def,cEval_def]
    \\ `?c3 aux3. compile_exps xs aux1 = (c3,aux3)` by METIS_TAC [PAIR]
    \\ full_simp_tac(srw_ss())[LET_DEF] \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[bEval_def]
    \\ `?p. evaluate (xs,env,s1) = p` by full_simp_tac(srw_ss())[] \\ PairCases_on `p` \\ full_simp_tac(srw_ss())[]
    \\ SRW_TAC [] [] \\ IMP_RES_TAC compile_exps_IMP_code_installed
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`aux1`,`t1`])
    \\ full_simp_tac(srw_ss())[] \\ REPEAT STRIP_TAC
    \\ POP_ASSUM (MP_TAC o Q.SPECL [`env''`,`f1`]) \\ full_simp_tac(srw_ss())[]
    \\ reverse (Cases_on `p0`) \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
    \\ TRY (full_simp_tac(srw_ss())[] \\ qexists_tac `ck` >> srw_tac[][] >> Q.EXISTS_TAC `f2` \\ full_simp_tac(srw_ss())[] \\ NO_TAC)
    \\ full_simp_tac(srw_ss())[closSemTheory.find_code_def,bvlSemTheory.find_code_def]
    \\ Cases_on `FLOOKUP p1.code dest` \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `x` \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `q = LENGTH a` \\ full_simp_tac(srw_ss())[]
    \\ `?aux1 c2 aux2.
          compile_exps [r] aux1 = ([c2],aux2) /\
          lookup (dest + num_stubs) t2.code = SOME (LENGTH a,c2) /\
          code_installed aux2 t2.code` by METIS_TAC [state_rel_def]
    \\ IMP_RES_TAC EVERY2_LENGTH \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `t2.clock < ticks+1` \\ full_simp_tac(srw_ss())[]
    THEN1 (qexists_tac `ck` >> SRW_TAC [] [] \\ Q.EXISTS_TAC `f2` >> full_simp_tac(srw_ss())[])
    \\ full_simp_tac(srw_ss())[] \\ rev_full_simp_tac(srw_ss())[] \\ full_simp_tac(srw_ss())[]
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`aux1'`]) \\ full_simp_tac(srw_ss())[]
    \\ REPEAT STRIP_TAC
    \\ POP_ASSUM (MP_TAC o Q.SPECL [`t2`,`v'`,`f2`]) \\ full_simp_tac(srw_ss())[]
    \\ IMP_RES_TAC evaluate_code \\ full_simp_tac(srw_ss())[]
    \\ IMP_RES_TAC evaluate_const \\ full_simp_tac(srw_ss())[closPropsTheory.dec_clock_code]
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
     (full_simp_tac(srw_ss())[closSemTheory.dec_clock_def,state_rel_def,bvlSemTheory.dec_clock_def]
      \\ full_simp_tac(srw_ss())[FEVERY_ALL_FLOOKUP,FORALL_PROD]
      \\ IMP_RES_TAC list_rel_IMP_env_rel \\ METIS_TAC [APPEND_NIL])
    \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[]
    \\ qexists_tac `ck + ck'` >>
    srw_tac[][] >>
    `evaluate (c3,env'',t1 with clock := s1.clock + (ck + ck')) = (Rval v',inc_clock ck' t2)`
           by (imp_res_tac evaluate_add_clock >>
               fsrw_tac[ARITH_ss] [inc_clock_def])
    \\ srw_tac[][inc_clock_def]
    \\ `p1.clock − (ticks+1) + ck' = t2.clock + ck' - (ticks + 1)` by simp []
    \\ full_simp_tac(srw_ss())[closSemTheory.dec_clock_def, bvlSemTheory.dec_clock_def]
    \\ Q.EXISTS_TAC `f2'` \\ full_simp_tac(srw_ss())[]
    \\ IMP_RES_TAC SUBMAP_TRANS \\ full_simp_tac(srw_ss())[]
    \\ `F` by decide_tac)
  THEN1
   ((* cEvalApp [] *)
    full_simp_tac(srw_ss())[cEval_def] >>
    srw_tac[][] >>
    qexists_tac `Rval [func']` >>
    qexists_tac `t1 with clock := s1.clock` >>
    srw_tac[][] >>
    metis_tac [SUBMAP_REFL])
  THEN1
   ((* cEvalApp real app *)
    qpat_assum `evaluate_app x0 x1 x2 x3 = x4` mp_tac
    \\ simp [cEval_def]
    \\ qpat_abbrev_tac `args = _::_`
    \\ DISCH_TAC
    \\ qabbrev_tac `args' = args''`
    \\ `LENGTH args' ≠ 0` by metis_tac [LIST_REL_LENGTH, LENGTH, DECIDE ``SUC x ≠ 0``]
    \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `dest_closure loc_opt func args`
    \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `x`
    \\ full_simp_tac(srw_ss())[]
    \\ srw_tac[][]
    >- ((* Partial application *)
        `LENGTH args = LENGTH args' ∧ LENGTH args ≠ 0` by metis_tac [LIST_REL_LENGTH] >>
        imp_res_tac dest_closure_part_app >>
        srw_tac[][PULL_EXISTS] >>
        imp_res_tac v_rel_num_rem_args >>
        srw_tac[][mk_cl_call_def, bEval_def, bEval_APPEND, bEvalOp_def] >>
        srw_tac [ARITH_ss] [el_append3] >>
        `&n' ≠ &(LENGTH args')` by srw_tac [ARITH_ss] [] >>
        `&n' - 1 ≠ &(LENGTH args' - 1)`
                   by (full_simp_tac(srw_ss())[int_arithTheory.INT_NUM_SUB] >>
                       CCONTR_TAC >>
                       full_simp_tac(srw_ss())[] >>
                       srw_tac[][] >>
                       ARITH_TAC) >>
        srw_tac[][] >>
        `0 < LENGTH args'` by decide_tac >>
        `evaluate (GENLIST Var (LENGTH args'),
                args' ++ [Block tag (CodePtr ptr::Number (&n'-1)::rest)] ++ env,
                t1 with clock := s1.clock) = (Rval args', t1 with clock := s1.clock)`
                    by metis_tac [evaluate_simple_genlist_vars, APPEND_ASSOC] >>
        qexists_tac `0` >>
        srw_tac[][] >>
        `LENGTH args' - 1 < max_app` by decide_tac >>
        `lookup (LENGTH args' - 1) t1.code = SOME (LENGTH args' + 1, generate_generic_app (LENGTH args' - 1))`
               by (full_simp_tac(srw_ss())[state_rel_def] >>
                   decide_tac) >>
        simp [find_code_def] >>
        `SUC (LENGTH v43) = LENGTH args` by metis_tac [LENGTH] >>
        full_simp_tac(srw_ss())[] >>
        srw_tac[][]
        >- (`s1.clock < LENGTH args'` by decide_tac >>
            full_simp_tac(srw_ss())[] >>
            qexists_tac `f1` >>
            simp [SUBMAP_REFL] >>
            full_simp_tac(srw_ss())[] >>
            full_simp_tac(srw_ss())[closSemTheory.state_component_equality] >>
            `s1 = s2` by srw_tac[][closSemTheory.state_component_equality] >>
            metis_tac []) >>
        assume_tac (GEN_ALL (SIMP_RULE (srw_ss()) [GSYM AND_IMP_INTRO] unpack_closure_thm)) >>
        rpt (pop_assum (fn th => first_assum  (strip_assume_tac o MATCH_MP th))) >>
        `lookup (partial_app_fn_location total_args (LENGTH args' + LENGTH prev_args − 1)) t1.code =
             SOME (total_args - (LENGTH args' + LENGTH prev_args-1) + 1, generate_partial_app_closure_fn total_args (LENGTH args' + LENGTH prev_args − 1))`
                 by (full_simp_tac(srw_ss())[state_rel_def] >>
                     first_x_assum match_mp_tac >>
                     srw_tac[][] >>
                     decide_tac) >>
        `LENGTH args' + LENGTH prev_args − 1 = LENGTH prev_args + (LENGTH args − 1)` by simp [] >>
        `LENGTH args' < total_args + 1 − LENGTH prev_args` by simp [] >>
        full_simp_tac(srw_ss())[] >>
        Q.ISPECL_THEN [`total_args`, `prev_args`, `dec_clock 1 (t1 with clock := s1.clock)`, `args'`] assume_tac evaluate_generic_app_partial >>
        rev_full_simp_tac(srw_ss())[domain_lookup] >>
        pop_assum (fn th => first_assum (strip_assume_tac o MATCH_MP th)) >>
        srw_tac[][]
        >- ((* A TimeOut *)
            full_simp_tac (srw_ss()++ARITH_ss) [dec_clock_def, int_arithTheory.INT_NUM_SUB] >>
            qexists_tac `f1` >>
            srw_tac[][SUBMAP_REFL] >>
            full_simp_tac(srw_ss())[state_rel_def])
        >- ((* Result *)
            `~((t1 with clock := s1.clock).clock < LENGTH args')` by (full_simp_tac(srw_ss())[dec_clock_def] >> decide_tac) >>
            full_simp_tac(srw_ss())[] >>
            srw_tac[][] >>
            qexists_tac `f1` >>
            reverse (srw_tac[][])
            >- (srw_tac[][bvlSemTheory.dec_clock_def, closSemTheory.dec_clock_def] >>
                metis_tac [arith_helper_lem])
            >- (full_simp_tac(srw_ss())[bvlSemTheory.dec_clock_def, closSemTheory.dec_clock_def] >>
                full_simp_tac(srw_ss())[state_rel_def]) >>
            `args ≠ []` by (Cases_on `args` >> full_simp_tac(srw_ss())[]) >>
            full_simp_tac(srw_ss())[v_rel_cases, num_remaining_args_def,closure_tag_neq_1,partial_app_tag_neq_closure_tag] >>
            srw_tac[][] >>
            full_simp_tac(srw_ss())[num_remaining_args_def, add_args_def, partial_app_tag_neq_closure_tag]
            >- ((* Wrapping a normal closure *)
                MAP_EVERY qexists_tac [`args`, `func`, `env'`, `fvs`, `total_args + 1`] >>
                full_simp_tac(srw_ss())[] >>
                imp_res_tac cl_rel_get_num_args >>
                srw_tac[][SUB_LEFT_SUB, LESS_OR_EQ] >>
                full_simp_tac(srw_ss())[])
            >- ((* Wrapping a partially applied closure *)
                full_simp_tac(srw_ss())[unpack_closure_cases] >>
                srw_tac[][] >>
                MAP_EVERY qexists_tac [`args++arg_env`, `cl`, `env'`, `fvs`, `total_args+1`] >>
                full_simp_tac(srw_ss())[partial_app_tag_neq_closure_tag] >>
                imp_res_tac EVERY2_LENGTH >>
                srw_tac[][partial_app_tag_neq_closure_tag]
                >- simp [] >>
                metis_tac [arith_helper_lem3, add_args_append, EVERY2_APPEND])))
    >- ((* Enough arguments to do something *)
         `SUC (LENGTH v43) = LENGTH args` by metis_tac [LENGTH] >>
         `every_Fn_SOME [e] ∧ every_Fn_vs_SOME [e]` by (
           rator_x_assum`dest_closure`mp_tac >>
           simp[dest_closure_def] >>
           BasicProvers.CASE_TAC >> srw_tac[][] >>
           full_simp_tac(srw_ss())[v_rel_cases,cl_rel_cases] >>
           srw_tac[][] >> full_simp_tac(srw_ss())[add_args_def] >> srw_tac[][] >>
           pop_assum mp_tac >> srw_tac[][UNCURRY] >> full_simp_tac(srw_ss())[] >>
           full_simp_tac(srw_ss())[Once every_Fn_SOME_EVERY,Once every_Fn_vs_SOME_EVERY] >>
           full_simp_tac(srw_ss())[EVERY_MAP] >>
           full_simp_tac(srw_ss())[EVERY_MEM,MEM_EL,PULL_EXISTS,EL_MAP] ) >>
         full_simp_tac(srw_ss())[] >>
         imp_res_tac dest_closure_full_app >>
         assume_tac (SIMP_RULE (srw_ss()) [GSYM AND_IMP_INTRO] v_rel_num_rem_args) >>
         rpt (pop_assum (fn th => first_assum (strip_assume_tac o MATCH_MP th))) >>
         `loc_opt = NONE ∨ ?loc. loc_opt = SOME loc` by metis_tac [option_nchotomy] >>
         full_simp_tac(srw_ss())[check_loc_def] >>
         srw_tac[][]
         >- ((* App NONE *)
             qabbrev_tac `n = rem_args - 1` >>
             imp_res_tac EVERY2_LENGTH >>
             `lookup (LENGTH args' − 1) t1.code =
                SOME ((LENGTH args' - 1) + 2,generate_generic_app (LENGTH args' − 1))`
                         by (full_simp_tac(srw_ss())[state_rel_def] >>
                             `LENGTH args' - 1 < max_app` by decide_tac >>
                             metis_tac []) >>
             `LENGTH args' - 1 + 2  = LENGTH args' + 1` by decide_tac >>
             full_simp_tac(srw_ss())[] >>
             `&rem_args - 1 = &n ∧ rem_args + 1 = n + 2`
                  by (srw_tac [ARITH_ss] [Abbr `n`,int_arithTheory.INT_NUM_SUB]) >>
             `LENGTH args' − (LENGTH args' − rem_args) = rem_args` by decide_tac >>
             full_simp_tac(srw_ss())[] >>
             Cases_on `s1.clock < rem_args` >>
             full_simp_tac(srw_ss())[] >>
             simp []
             >- ((* Timeout *)
                 Q.ISPEC_THEN `t1 with clock := s1.clock` (assume_tac o (SIMP_RULE (srw_ss()) [GSYM AND_IMP_INTRO]))
                   evaluate_mk_cl_call_spec >>
                 rpt (pop_assum (fn x => first_assum (strip_assume_tac o MATCH_MP x))) >>
                 pop_assum mp_tac >>
                 simp [] >>
                 DISCH_TAC >>
                 qexists_tac `0` >>
                 simp [] >>
                 qexists_tac `f1` >>
                 srw_tac[][]) >>
             `?res' s'. evaluate ([e],l,dec_clock rem_args s1) = (res', s')` by metis_tac [pair_CASES] >>
             full_simp_tac(srw_ss())[] >>
             `res' ≠ Rerr(Rabort Rtype_error)` by (spose_not_then strip_assume_tac >> full_simp_tac(srw_ss())[]) >>
             full_simp_tac(srw_ss())[] >>
             imp_res_tac v_rel_run >>
             `LENGTH args ≠ 0` by decide_tac >>
             full_simp_tac(srw_ss())[int_arithTheory.INT_NUM_SUB, closSemTheory.dec_clock_def] >>
             first_x_assum (fn th => first_assum (assume_tac o MATCH_MP (SIMP_RULE (srw_ss()) [GSYM AND_IMP_INTRO] th))) >>
             rpt (pop_assum (fn th => (first_assum (strip_assume_tac o MATCH_MP th)))) >>
             Cases_on `?func''. res' =  Rval [func'']` >>
             full_simp_tac(srw_ss())[] >>
             srw_tac[][] >>
             full_simp_tac(srw_ss())[]
             >- ((* The first application succeeds *)
                 `?v'. v_rel f2 t2.refs t2.code func'' v' ∧ res'' = Rval [v']`
                        by (full_simp_tac(srw_ss())[] >> metis_tac []) >>
                 `LIST_REL (v_rel f2 t2.refs t2.code) l0 (TAKE (LENGTH args' − rem_args) args')`
                          by (match_mp_tac list_rel_app >>
                              MAP_EVERY qexists_tac [`args`, `e`, `l`, `func`] >>
                              srw_tac[][] >>
                              full_simp_tac(srw_ss())[LIST_REL_EL_EQN] >>
                              srw_tac[][] >>
                              match_mp_tac (GEN_ALL v_rel_SUBMAP) >>
                              srw_tac[][] >>
                              `t1.code = t2.code`
                                     by (imp_res_tac evaluate_code >>
                                         full_simp_tac(srw_ss())[]) >>
                              metis_tac []) >>
                 first_x_assum (fn th => first_assum (assume_tac o MATCH_MP (SIMP_RULE (srw_ss()) [GSYM AND_IMP_INTRO] th))) >>
                 rev_full_simp_tac(srw_ss())[] >>
                 rpt (pop_assum (fn th => (first_assum (strip_assume_tac o MATCH_MP th)))) >>
                 full_simp_tac(srw_ss())[LENGTH_TAKE] >>
                 Cases_on `(LENGTH args' ≤ rem_args)` >>
                 full_simp_tac(srw_ss())[]
                 >- ((* No remaining arguments *)
                     Q.ISPEC_THEN `t1 with clock := ck + ck' + s1.clock`
                       (assume_tac o SIMP_RULE (srw_ss()) [GSYM AND_IMP_INTRO])evaluate_mk_cl_call_spec >>
                     rpt (pop_assum (fn x => first_assum (strip_assume_tac o MATCH_MP x))) >>
                     pop_assum mp_tac >>
                     simp [] >>
                     DISCH_TAC >>
                     qexists_tac `ck + ck'` >>
                     srw_tac[][] >>
                     `rem_args = LENGTH args' ∧ n + 1 = LENGTH args'` by decide_tac >>
                     full_simp_tac(srw_ss())[ADD_ASSOC] >>
                     first_x_assum (qspec_then `t1 with clock := ck + s1.clock - LENGTH args'` mp_tac) >>
                     simp [inc_clock_def, dec_clock_def] >>
                     `!ck. t1 with <| clock := ck; code := t1.code |> = t1 with clock := ck`
                              by srw_tac[][bvlSemTheory.state_component_equality] >>
                     srw_tac[][] >>
                     `ck + s1.clock − LENGTH args' = s1.clock − LENGTH args' + ck` by decide_tac >>
                     srw_tac[][] >>
                     full_simp_tac(srw_ss())[cEval_def] >>
                     `!ck. t1 with <| clock := ck; refs := t1.refs |> = t1 with clock := ck`
                              by srw_tac[][bvlSemTheory.state_component_equality] >>
                     full_simp_tac(srw_ss())[] >> srw_tac[][] >>
                     metis_tac [SUBMAP_TRANS])
                 >- ((* Extra arguments *)
                     srw_tac[][] >>
                     `FEVERY (λp. every_Fn_SOME [SND (SND p)]) s'.code ∧
                      FEVERY (λp. every_Fn_vs_SOME [SND (SND p)]) s'.code` by (
                       `s'.code = s1.code` by (
                         imp_res_tac evaluate_const >> full_simp_tac(srw_ss())[] ) >>
                       full_simp_tac(srw_ss())[] ) >> full_simp_tac(srw_ss())[] >>
                     first_x_assum(fn th => first_x_assum (mp_tac o MATCH_MP th)) >>
                     disch_then(fn th => first_x_assum (mp_tac o MATCH_MP th)) >>
                     simp[] >>
                     disch_then (qspec_then `SOMEENV` strip_assume_tac) >>
                     Q.ISPEC_THEN `t1 with clock := ck + ck' + ck'' + 1 + s1.clock`
                       (assume_tac o SIMP_RULE (srw_ss()) [GSYM AND_IMP_INTRO]) evaluate_mk_cl_call_spec >>
                     rpt (pop_assum (fn x => first_assum (strip_assume_tac o MATCH_MP x))) >>
                     pop_assum mp_tac >>
                     simp [] >>
                     DISCH_TAC >>
                     qexists_tac `ck + ck' + ck'' + 1` >>
                     simp [] >>
                     pop_assum kall_tac >>
                     first_x_assum (qspec_then `t1 with clock := ck + ck'' + s1.clock - rem_args` mp_tac) >>
                     qpat_abbrev_tac`t11:'ffi bvlSem$state = inc_clock ck' Z` >>
                     qpat_abbrev_tac`t12:'ffi bvlSem$state = dec_clock X Y` >>
                     `t11 = t12` by (
                       simp[Abbr`t11`,Abbr`t12`] >>
                       srw_tac[][inc_clock_def,dec_clock_def,bvlSemTheory.state_component_equality] >>
                       fsrw_tac[ARITH_ss][]) >>
                     pop_assum SUBST1_TAC >>
                     disch_then SUBST1_TAC >>
                     map_every qunabbrev_tac[`t11`,`t12`] >>
                     qmatch_assum_abbrev_tac`evaluate (_,_,t11) = (_,t2)` >>
                     qpat_abbrev_tac`t12:'ffi bvlSem$state = X Y` >>
                     `t12 = inc_clock ck'' t11` by (
                       unabbrev_all_tac >>
                       srw_tac[][bvlSemTheory.state_component_equality,inc_clock_def] >>
                       fsrw_tac[ARITH_ss][]) >>
                     pop_assum SUBST1_TAC >>
                     imp_res_tac evaluate_add_clock >>
                     unabbrev_all_tac >> full_simp_tac(srw_ss())[] >>
                     ntac 2 (pop_assum kall_tac) >>
                     `SUC (LENGTH ys) - (rem_args - 1 + 1) = LENGTH args'' - rem_args` by (
                       fsrw_tac[ARITH_ss][ADD1] ) >>
                     pop_assum SUBST_ALL_TAC >>
                     `LENGTH [Block tag (CodePtr ptr::Number (&(rem_args − 1))::rest)] ≠ 0` by srw_tac[][] >>
                     `LENGTH args'' − rem_args ≤ LENGTH args''` by (rpt var_eq_tac >> ARITH_TAC) >>
                     first_x_assum (fn th => strip_assume_tac (MATCH_MP (SIMP_RULE (srw_ss()) [GSYM AND_IMP_INTRO] mk_call_simp2) th)) >>
                     pop_assum (fn th => first_x_assum (strip_assume_tac o MATCH_MP th)) >>
                     pop_assum(qspecl_then[`SOMEENV`,`v''`,`inc_clock ck'' t2`](mp_tac o GSYM)) >>
                     rpt var_eq_tac >>
                     simp_tac(srw_ss())[inc_clock_def] >>
                     disch_then kall_tac >>
                     rator_x_assum`evaluate`mp_tac >>
                     simp_tac(srw_ss()++ARITH_ss)[] >>
                     strip_tac >>
                     Cases_on`res''''`>> full_simp_tac(srw_ss())[] >>
                     imp_res_tac bEval_SING >> full_simp_tac(srw_ss())[] >>
                     metis_tac[SUBMAP_TRANS]))
             >- ((* The first application fails *)
                 `res' = res ∧ s' = s2`
                       by (Cases_on `res'` >>
                           full_simp_tac(srw_ss())[] >>
                           Cases_on `a` >>
                           full_simp_tac(srw_ss())[] >>
                           Cases_on `t` >>
                           full_simp_tac(srw_ss())[]) >>
                 full_simp_tac(srw_ss())[] >>
                 `!ck. t1 with <| refs := t1.refs; clock := ck; code := t1.code |> = t1 with clock := ck`
                              by srw_tac[][bvlSemTheory.state_component_equality] >>
                 first_x_assum (qspec_then `t1 with clock := s1.clock - rem_args + ck` assume_tac) >>
                 rev_full_simp_tac(srw_ss())[] >>
                 Cases_on `n = LENGTH args' - 1` >>
                 full_simp_tac(srw_ss())[]
                 >- (Q.ISPEC_THEN `t1 with clock := ck+ck' + s1.clock`
                       (assume_tac o SIMP_RULE (srw_ss()) [GSYM AND_IMP_INTRO]) evaluate_mk_cl_call_spec >>
                     rpt (pop_assum (fn x => first_assum (strip_assume_tac o MATCH_MP x))) >>
                     pop_assum mp_tac >>
                     simp [] >>
                     DISCH_TAC >>
                     qexists_tac `ck+ck'` >>
                     rev_full_simp_tac (srw_ss()++ARITH_ss) [inc_clock_def, dec_clock_def] >>
                     qexists_tac `f2` >>
                     srw_tac[][])
                 >- (Q.ISPEC_THEN `t1 with clock := ck+ck' +1+ s1.clock`
                       (assume_tac o SIMP_RULE (srw_ss()) [GSYM AND_IMP_INTRO]) evaluate_mk_cl_call_spec >>
                     rpt (pop_assum (fn x => first_assum (strip_assume_tac o MATCH_MP x))) >>
                     pop_assum mp_tac >>
                     simp [] >>
                     DISCH_TAC >>
                     qexists_tac `ck+ck'+1` >>
                     rev_full_simp_tac (srw_ss()++ARITH_ss) [inc_clock_def, dec_clock_def] >>
                     pop_assum kall_tac >>
                     `rem_args = n + 1` by decide_tac >>
                     full_simp_tac(srw_ss())[] >>
                     srw_tac[][] >>
                     MAP_EVERY qexists_tac [`res''`, `t2`, `f2`] >>
                     srw_tac[][] >>
                     BasicProvers.CASE_TAC >>
                     Cases_on`res`>>full_simp_tac(srw_ss())[] >>
                     imp_res_tac bEval_SING >>
                     full_simp_tac(srw_ss())[] >> srw_tac[][])))
         >- ((* App SOME *)
             `rem_args = LENGTH args` by ARITH_TAC >>
             full_simp_tac(srw_ss())[] >>
             srw_tac[][find_code_def] >>
             `&LENGTH args - 1 = &(LENGTH args - 1)` by srw_tac[][int_arithTheory.INT_NUM_SUB] >>
             full_simp_tac(srw_ss())[] >>
             `t1.code = (t1 with clock := s1.clock - LENGTH args').code` by srw_tac[][] >>
             full_simp_tac std_ss [] >>
             strip_assume_tac (SIMP_RULE (srw_ss()) [GSYM AND_IMP_INTRO] (v_rel_run)) >>
             rpt (pop_assum (fn x => first_assum (strip_assume_tac o MATCH_MP x))) >>
             full_simp_tac(srw_ss())[] >>
             srw_tac[][] >>
             `ptr = loc' + num_stubs`
                     by (full_simp_tac(srw_ss())[v_rel_cases] >>
                         imp_res_tac cl_rel_get_loc >>
                         full_simp_tac(srw_ss())[] >>
                         srw_tac [ARITH_ss] [] >>
                         metis_tac [no_partial_args]) >>
             srw_tac[][] >>
             imp_res_tac EVERY2_LENGTH >>
             full_simp_tac(srw_ss())[] >>
             Cases_on `s1.clock < LENGTH args'` >>
             full_simp_tac(srw_ss())[]
             >- ((* TimeOut *)
                 qexists_tac `0` >> srw_tac[][] >>
                 metis_tac [SUBMAP_REFL]) >>
             `?res' s2. evaluate ([e],l,dec_clock (LENGTH args') s1) = (res',s2)`
                          by metis_tac [pair_CASES]  >>
             full_simp_tac(srw_ss())[] >>
             `l0 = []` by (Cases_on `l0` >> full_simp_tac(srw_ss())[]) >>
             srw_tac[][] >>
             `res' = res ∧ s2' = s2`
                     by (Cases_on `res'` >>
                         full_simp_tac(srw_ss())[] >>
                         Cases_on `a` >>
                         full_simp_tac(srw_ss())[] >>
                         Cases_on `t` >>
                         full_simp_tac(srw_ss())[cEval_def]) >>
             srw_tac[][] >>
             full_simp_tac(srw_ss())[] >>
             `t1.refs = (dec_clock (LENGTH args') t1).refs` by srw_tac[][dec_clock_def] >>
             full_simp_tac(srw_ss())[] >>
             srw_tac[][] >>
             `LENGTH args' − (LENGTH args' − 1 + 1) = 0` by decide_tac >>
             full_simp_tac bool_ss [] >>
             full_simp_tac(srw_ss())[inc_clock_def, dec_clock_def] >>
             full_simp_tac (srw_ss()++ARITH_ss) [] >>
             first_x_assum (fn x => first_assum (strip_assume_tac o MATCH_MP (SIMP_RULE (srw_ss()) [GSYM AND_IMP_INTRO] x))) >>
             `code_installed aux2 (dec_clock (LENGTH args') t1).code` by srw_tac[][] >>
             `(dec_clock (LENGTH args') s1).code = s1.code` by EVAL_TAC >> full_simp_tac(srw_ss())[] >> rev_full_simp_tac(srw_ss())[] >>
             first_x_assum (fn x => first_assum (strip_assume_tac o MATCH_MP x)) >>
             full_simp_tac(srw_ss())[] >>
             pop_assum (fn x => first_assum (strip_assume_tac o MATCH_MP x)) >>
             full_simp_tac(srw_ss())[bvlSemTheory.dec_clock_def, closSemTheory.dec_clock_def] >>
             pop_assum (fn x => first_assum (strip_assume_tac o MATCH_MP x)) >>
             qexists_tac `ck+ck'` >>
             srw_tac[][] >>
             first_x_assum (qspec_then `t1 with clock := ck + (s1.clock - LENGTH args')` mp_tac) >>
             simp [] >>
             srw_tac[][] >>
             `!ck. t1 with <| refs:=t1.refs;code:=t1.code;clock := ck|> = t1 with clock := ck`
                   by srw_tac[][bvlSemTheory.state_component_equality] >>
             full_simp_tac(srw_ss())[] >>
             `ck + s1.clock − LENGTH args' = ck + (s1.clock − LENGTH args')` by decide_tac >>
             metis_tac []))));

(* more correctness properties *)

val build_aux_thm = prove(
  ``∀c n aux n7 aux7.
    build_aux n c aux = (n7,aux7++aux) ⇒
    (MAP FST aux7) = (REVERSE (GENLIST ($+ n o $* 2) (LENGTH c)))``,
  Induct >> simp[build_aux_def] >> srw_tac[][] >>
  qmatch_assum_abbrev_tac`build_aux nn kk auxx = Z` >>
  qspecl_then[`kk`,`nn`,`auxx`]strip_assume_tac build_aux_acc >>
  Cases_on`build_aux nn kk auxx`>>UNABBREV_ALL_TAC>>full_simp_tac(srw_ss())[]>> srw_tac[][] >>
  full_simp_tac std_ss [Once (CONS_APPEND)] >>
  full_simp_tac std_ss [Once (GSYM APPEND_ASSOC)] >> res_tac >>
  srw_tac[][GENLIST,REVERSE_APPEND,REVERSE_GENLIST,PRE_SUB1] >>
  simp[LIST_EQ_REWRITE])

val lemma =
  SIMP_RULE(std_ss++LET_ss)[UNCURRY]compile_exps_acc

fun tac (g as (asl,w)) =
  let
    fun get tm =
      let
        val tm = tm |> strip_forall |> snd |> dest_imp |> fst
        fun a tm =
          let
            val (f,xs) = strip_comb tm
          in
            same_const``clos_to_bvl$compile_exps``f andalso
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
    rev_full_simp_tac(srw_ss())[]
  end g

val compile_exps_code_locs = store_thm("compile_exps_code_locs",
  ``∀xs aux ys aux2.
    compile_exps xs aux = (ys,aux2++aux) ⇒
    MAP FST aux2 = MAP ((+) num_stubs) (REVERSE(code_locs xs))``,
  ho_match_mp_tac compile_exps_ind >> rpt conj_tac >>
  TRY (
    srw_tac[][compile_exps_def] >>
    Cases_on`fns`>>full_simp_tac(srw_ss())[code_locs_def]>-(
      full_simp_tac(srw_ss())[LET_THM] ) >>
    Cases_on`t`>>full_simp_tac(srw_ss())[code_locs_def]>-(
      Cases_on `h` >> full_simp_tac(srw_ss())[] >>
      srw_tac[][LET_THM] >> tac >> tac  >> srw_tac[][] >> full_simp_tac(srw_ss())[LET_THM] >> srw_tac[][] >> DECIDE_TAC) >>
    simp[] >> srw_tac[][] >>
    full_simp_tac(srw_ss())[compile_exps_def,LET_THM,UNCURRY] >> srw_tac[][] >>
    qmatch_assum_abbrev_tac`SND (compile_exps [x1] aux1) = aux2 ++ aux` >>
    qspecl_then[`[x1]`,`aux1`]strip_assume_tac lemma >>
    Cases_on`compile_exps [x1] aux1`>>full_simp_tac(srw_ss())[Abbr`aux1`] >> srw_tac[][] >>
    qmatch_assum_abbrev_tac`ys++SND(build_aux (loc + num_stubs) aux1 z) = aux2 ++ aux` >>
    qspecl_then[`aux1`,`loc+num_stubs`,`z`]STRIP_ASSUME_TAC build_aux_acc >>
    Cases_on`build_aux (loc+num_stubs) aux1 z`>>full_simp_tac(srw_ss())[] >>
    qspecl_then[`[SND h]`,`aux`]strip_assume_tac lemma >>
    Cases_on`compile_exps [SND h] aux`>>full_simp_tac(srw_ss())[] >> srw_tac[][] >>
    qspecl_then[`SND h'::MAP SND t'`,`ys'++aux`]strip_assume_tac lemma >>
    Cases_on`compile_exps (SND h'::MAP SND t') (ys'++aux)`>>full_simp_tac(srw_ss())[] >> srw_tac[][] >>
    full_simp_tac(srw_ss())[Abbr`z`] >> srw_tac[][] >> full_simp_tac(srw_ss())[] >>
    full_simp_tac std_ss [GSYM APPEND_ASSOC]  >>
    imp_res_tac build_aux_thm >>
    simp[Abbr`aux1`,ADD1, MAP_REVERSE, LENGTH_MAP2, MAP_GENLIST] >>
    match_mp_tac (METIS_PROVE [] ``!f x y z. (!a. x a = y a) ⇒ f x z = f y z``) >>
    simp [combinTheory.o_DEF]) >>
  simp[compile_exps_def,code_locs_def,UNCURRY] >> srw_tac[][] >>
  rpt tac >> srw_tac[][] >> full_simp_tac(srw_ss())[] >> srw_tac[][]);

val init_code_ok = Q.store_thm ("init_code_ok",
  `(!n.
      n < max_app ⇒ lookup n init_code = SOME (n + 2, generate_generic_app n)) ∧
   (!m n.
      m < max_app ∧ n < max_app ⇒
        lookup (partial_app_fn_location m n) init_code =
          SOME (m - n + 1, generate_partial_app_closure_fn m n)) ∧
   (lookup equality_location init_code = SOME equality_code) ∧
   (lookup block_equality_location init_code = SOME block_equality_code) ∧
   (lookup ToList_location init_code = SOME ToList_code)`,
  srw_tac[][init_code_def, lookup_fromList, EL_APPEND1, partial_app_fn_location_def]
  >- decide_tac
  >- simp[EL_APPEND1]
  >- (srw_tac[][LENGTH_FLAT, MAP_GENLIST, combinTheory.o_DEF, sum_genlist_square] >>
      srw_tac[][DECIDE ``!(x:num) y z n. x + y +n < x + z + a ⇔ y +n < z + a``] >>
      `max_app * m + n < max_app * max_app` by metis_tac[less_rectangle] >>
      DECIDE_TAC)
  >- (`max_app ≤ max_app + max_app * m + n` by decide_tac >>
      ONCE_REWRITE_TAC[GSYM APPEND_ASSOC] >>
      simp[EL_APPEND2] >>
      `n+m*max_app < max_app*max_app` by metis_tac [less_rectangle2] >>
      `0 < max_app` by srw_tac[][max_app_def] >>
      srw_tac[][twod_table] >>
      asm_simp_tac std_ss [EL_APPEND1,LENGTH_GENLIST] >>
      srw_tac[][EL_GENLIST] >>
      srw_tac[][DIV_MULT, Once ADD_COMM] >>
      ONCE_REWRITE_TAC [ADD_COMM] >>
      srw_tac[][MOD_MULT])
  >- (
    `0 < max_app` by srw_tac[][max_app_def] >>
    srw_tac[][twod_table] >>
    simp[equality_location_def] )
  >- (
    `0 < max_app` by srw_tac[][max_app_def] >>
    srw_tac[][twod_table] >>
    simp[EL_APPEND2,equality_location_def] )
  >- (
    `0 < max_app` by srw_tac[][max_app_def] >>
    srw_tac[][twod_table] >>
    simp[equality_location_def,block_equality_location_def] )
  >- (
    `0 < max_app` by srw_tac[][max_app_def] >>
    srw_tac[][twod_table] >>
    simp[EL_APPEND2,block_equality_location_def,equality_location_def] )
  >- (
    `0 < max_app` by srw_tac[][max_app_def] >>
    srw_tac[][twod_table] >>
    simp[ToList_location_def,equality_location_def,block_equality_location_def] )
  >- (
    `0 < max_app` by srw_tac[][max_app_def] >>
    srw_tac[][twod_table] >>
    simp[EL_APPEND2,ToList_location_def,block_equality_location_def,equality_location_def] ));

val domain_init_code =
  ``domain init_code`` |> EVAL

val domain_init_code_lt_num_stubs = Q.store_thm("domain_init_code_lt_num_stubs",
  `∀x. x ∈ domain init_code ⇒ x < num_stubs`,
  REWRITE_TAC[domain_init_code] >>
  srw_tac[][EVAL``num_stubs``] >> simp[]);

(*TODO: This rewrite might make it worse, not sure...*)
val compile_prog_code_locs = Q.store_thm("compile_prog_code_locs",
  `∀ls.
  MAP FST (compile_prog ls) =
  FLAT (
    MAP (λn,args,e. (n+num_stubs)::(MAP ($+ num_stubs) (REVERSE (code_locs [e])))) ls)`,
  Induct>>fs[compile_prog_def,FORALL_PROD]>>rw[]>>
  pairarg_tac>>fs[MAP_MAP_o]>>
  pop_assum mp_tac>>
  specl_args_of_then``compile_exps``compile_exps_code_locs mp_tac >> srw_tac[][] >>
  imp_res_tac compile_exps_LENGTH>>
  fs[quantHeuristicsTheory.LIST_LENGTH_1])

(* TODO: Gets rid of the annoying ZIP in clos_remove$compile,
  should probably be the definition instead, but this might translate worse
*)
val remove_compile_alt = prove(``
  ∀b prog.
  clos_remove$compile b prog =
  MAP (λ(n,args,exp). (n,args, if b then HD(FST(remove [exp])) else exp)) prog``,
  Cases>>
  Induct>>fs[clos_removeTheory.compile_def]>-EVAL_TAC>>
  simp[FORALL_PROD]>>rw[Once clos_removeTheory.remove_CONS]);

val remove_FST = prove(``
  ∀ls b.MAP FST (clos_remove$compile b ls) = MAP FST ls``,
  Induct>>Cases_on`b`>>fs[clos_removeTheory.compile_def,FORALL_PROD]
  >-
    EVAL_TAC>>
  first_x_assum(qspec_then`T` assume_tac)>>fs[clos_removeTheory.compile_def]>>
  rw[Once clos_removeTheory.remove_CONS])

val compile_all_distinct_locs = Q.store_thm("compile_all_distinct_locs",
  `num_stubs ≤ c.start ∧ c.start < c.next_loc ∧ EVEN c.start ∧ EVEN c.next_loc ∧
   compile c e = (c',p) ⇒ ALL_DISTINCT (MAP FST p)`,
  srw_tac[][compile_def] >>
  full_simp_tac(srw_ss())[compile_def,LET_THM] >>
  rpt(first_assum(split_uncurry_arg_tac o lhs o concl)>>full_simp_tac(srw_ss())[]) >>
  srw_tac[][]>>
  simp[compile_prog_code_locs]>>
  simp[ALL_DISTINCT_APPEND] >>
  `∃z. clos_mti$compile c.do_mti [e] = [z]` by (
    Cases_on`c.do_mti`>>fs[clos_mtiTheory.compile_def]>>
    metis_tac[clos_mtiTheory.intro_multi_sing]) >>
  `∃z. es = [z]` by (
    metis_tac
      [clos_numberTheory.renumber_code_locs_length, SING_HD, SND, LENGTH, ONE]) >>
  CONJ_TAC>-
    EVAL_TAC>>
  reverse CONJ_TAC>-
    (simp[ALL_DISTINCT_MAP_FST_toAList,toAList_domain] >>
    rpt strip_tac >>
    drule domain_init_code_lt_num_stubs >>
    fs[MEM_FLAT,MEM_MAP]>>
    pairarg_tac>>fs[]>>rfs[MEM_MAP])>>
  qmatch_goalsub_abbrev_tac`clos_remove$compile _ ls`>>
  qmatch_goalsub_abbrev_tac`MAP f (clos_annotate$compile ls')`>>
  (* annotate *)
  `MAP f (clos_annotate$compile ls') = MAP f ls'` by
    (simp[Abbr`f`]>>
    rpt (pop_assum kall_tac)>>
    Induct_on`ls'`>>fs[clos_annotateTheory.compile_def,FORALL_PROD]>>
    rw[]>>
    `∃z.annotate p_1' [p_2] = [z]` by
      (simp[clos_annotateTheory.annotate_def]>>
      metis_tac[clos_freeTheory.free_SING,clos_annotateTheory.shift_SING,FST,PAIR])>>
     fs[]>>
     metis_tac[clos_annotateProofTheory.annotate_code_locs,clos_removeProofTheory.code_loc'_def])>>
  fs[]>>
  (* rewrite away the nasty ordering of stubs and the +num_stubs *)
  qsuff_tac`ALL_DISTINCT (MAP FST ls' ++ FLAT (MAP (code_loc' o SND o SND) ls'))`>-
    (fs[Abbr`f`]>>rpt(pop_assum kall_tac)>>Induct_on`ls'`>- EVAL_TAC>>
    simp[FORALL_PROD]>>rw[]
    >-
      simp[MEM_MAP]
    >-
      (fs[MEM_FLAT,MEM_MAP,FORALL_PROD]>>CCONTR_TAC>>fs[]>>
      rfs[MEM_MAP]>>metis_tac[])
    >>
      fs[ALL_DISTINCT_APPEND]>>
      CONJ_TAC>-
        fs[ALL_DISTINCT_MAP_INJ]>>
      fs[MEM_FLAT,MEM_MAP,FORALL_PROD]>>CCONTR_TAC>>fs[]>>
      rfs[MEM_MAP]>>
      metis_tac[FST])>>
  (* Rewrite away FLAT *)
  `FLAT (MAP (code_loc' o SND o SND) ls') = code_locs (MAP (SND o SND) ls')` by
    (rpt (pop_assum kall_tac)>>Induct_on`ls'`>- EVAL_TAC>>
    fs[FORALL_PROD])>>
  pop_assum SUBST1_TAC>>
  (* remove *)
  qho_match_abbrev_tac`P ls'`>>
  qsuff_tac`P ls`>-
    (fs[Abbr`P`,Abbr`ls'`]>>
    simp[ALL_DISTINCT_APPEND,remove_FST,clos_removeProofTheory.compile_distinct_locs]>>rw[]>>
    specl_args_of_then ``clos_remove$compile`` clos_removeProofTheory.compile_distinct_locs mp_tac>>
    CCONTR_TAC>>fs[SUBSET_DEF]>>
    metis_tac[])>>
  fs[Abbr`ls`,Abbr`P`]>>
  qabbrev_tac`ls = kcompile c.do_known z'`>>
  (* call's syntactic preconds go here *)
  qsuff_tac`ALL_DISTINCT (code_loc' ls) ∧
            set (code_loc' ls) ⊆ EVEN ∧
            EVERY ($<= c.next_loc) (code_loc' ls)`
  >-
    (strip_tac>>
    (* This must be in HOL somewhere... *)
    `ODD (c.start - num_stubs)`
      by ( simp[ODD_SUB,ODD_EVEN] \\ EVAL_TAC ) >>
    `¬MEM (c.start-num_stubs) (code_loc' ls)` by
      (fs[SUBSET_DEF]>>
      fs[ODD_EVEN]>>
      metis_tac[IN_DEF])>>
    Cases_on`c.do_call`>>fs[clos_callTheory.compile_def]>>
    rpt var_eq_tac>>rfs[]>>
    pairarg_tac>>fs[]>>
    imp_res_tac clos_callProofTheory.calls_sing>>rpt var_eq_tac>>fs[]>>
    imp_res_tac clos_callProofTheory.calls_code_locs_ALL_DISTINCT>>rfs[]>>
    imp_res_tac clos_callProofTheory.calls_code_locs_MEM>>
    imp_res_tac clos_callProofTheory.calls_add_SUC_code_locs>>
    imp_res_tac clos_callProofTheory.calls_ALL_DISTINCT>>rfs[]>>
    rw[]
    >-
      (CCONTR_TAC>>fs[SUBSET_DEF,EVERY_MEM]>>res_tac>>
      res_tac>>
      DECIDE_TAC)
    >-
      metis_tac[]
    >-
      metis_tac[]
    >>
    fs[ALL_DISTINCT_APPEND]>>
    CCONTR_TAC>>fs[SUBSET_DEF,EVERY_MEM]>>res_tac>>
    res_tac>>
    rpt var_eq_tac>>fs[IN_DEF,EVEN]>>
    rfs[])>>
  (* known *)
  `code_loc' ls = code_loc' z'` by
    fs[Abbr`ls`,clos_knownProofTheory.compile_code_locs,Once clos_removeProofTheory.code_loc'_def]>>
  unabbrev_all_tac>>fs[]>>
  (* renumber *)
  qspecl_then[`c.next_loc`,`z`]assume_tac clos_numberProofTheory.renumber_code_locs_distinct>>
  fs[clos_numberTheory.renumber_code_locs_def]>>pairarg_tac>>fs[]>>
  rpt var_eq_tac>>fs[]>>
  Q.SPECL_THEN [`c.next_loc`,`z`] assume_tac (CONJUNCT2 clos_numberProofTheory.renumber_code_locs_EVEN)>>
  rfs[EVERY_MEM,SUBSET_DEF]>>
  metis_tac[IN_DEF]);

val full_result_rel_def = Define`
  full_result_rel c (r1,s1) (r2,s2) ⇔
    ∃ra rb rc kgmap rd re rf sa sb sc sd se sf f.
      (* MTI *)
      res_rel (r1,s1) (ra,sa) ∧
      (* Number *)
      clos_numberProof$state_rel sa sb ∧
      result_rel (LIST_REL clos_numberProof$v_rel) clos_numberProof$v_rel ra rb ∧
      (* Known *)
      clos_knownProof$opt_res_rel c.do_known kgmap (rb,sb) (rc,sc) ∧
      (* call *)
      clos_callProof$opt_result_rel c.do_call rc rd ∧
      clos_callProof$opt_state_rel c.do_call sc sd ∧
      (* remove *)
      res_rel (rd,sd) (re,se) ∧
      (* TODO:
       FEVERY (λp. every_Fn_vs_NONE [SND (SND p)]) se.code ∧
      ?*)
      (* annotate *)
      clos_annotateProof$state_rel se sf ∧
      result_rel (LIST_REL clos_annotateProof$v_rel) clos_annotateProof$v_rel re rf ∧
      (* TODO:
      FEVERY (λp. every_Fn_vs_SOME [SND (SND p)]) sf.code ∧
      FEVERY (λp. every_Fn_SOME [SND (SND p)]) sf.code ∧ *)
      state_rel f sf s2 ∧
      result_rel (LIST_REL (v_rel f s2.refs s2.code)) (v_rel f s2.refs s2.code) rf r2`;

(* Initial state *)
val clos_init_def = Define`
  clos_init s ⇔
  s.globals = [] ∧ s.refs = FEMPTY ∧ s.code = FEMPTY`

val clos_init_with_clock = Q.store_thm("clos_init_with_clock[simp]",
  `clos_init (s with clock := k) ⇔ clos_init s`,
  EVAL_TAC);

val compile_evaluate = Q.store_thm("compile_evaluate",
  `evaluate ([e],[],s:'ffi closSem$state) = (r,s') ∧
  clos_init s ∧
  ¬contains_App_SOME [e] ∧ every_Fn_vs_NONE [e] ∧ esgc_free e ∧
  BAG_ALL_DISTINCT (set_globals e) ∧
  r ≠ Rerr (Rabort Rtype_error) ∧
  num_stubs ≤ c.start ∧ EVEN c.next_loc ∧
  compile c e = (c',p) ⇒
  ∃r1 s'1 ck.
     let init_bvl = initial_state s.ffi (fromAList p) (s.clock+ck) in
     evaluate ([Call 0 (SOME c'.start) []],[], init_bvl) = (r1,s'1) ∧
     full_result_rel c (r,s') (r1,s'1)`,
  srw_tac[][compile_def,LET_THM,clos_init_def] >>
  rpt(first_assum(split_uncurry_arg_tac o lhs o concl) >>
      full_simp_tac(srw_ss())[]) >>
  `∃z. es = [z]` by (
    Cases_on`c.do_mti`>>fs[clos_mtiTheory.compile_def]>>
    metis_tac[clos_mtiTheory.intro_multi_sing, SING_HD, SND,
              clos_numberTheory.renumber_code_locs_length,
              LENGTH, ONE] ) >>
  (* intro_multi correct *)
  qspecl_then[`c.do_mti`,`[e]`]mp_tac clos_mtiProofTheory.compile_correct >>
  simp[clos_relationTheory.exp_rel_def,clos_relationTheory.exec_rel_rw,clos_relationTheory.evaluate_ev_def] >>
  disch_then(qspecl_then[`s.clock`,`[]`,`[]`,`s`,`s`] mp_tac)>>
  simp[clos_relationTheory.state_rel_refl]>>
  disch_then (qspec_then`s.clock` assume_tac)>>fs[]>>
  simp[full_result_rel_def,PULL_EXISTS] >>
  qmatch_assum_abbrev_tac`res_rel _ q` >>
  Cases_on`q`>>full_simp_tac(srw_ss())[markerTheory.Abbrev_def]>>
  pop_assum(assume_tac o SYM) >> full_simp_tac(srw_ss())[] >>
  CONV_TAC(STRIP_QUANT_CONV
    (move_conj_left(same_const``clos_relation$res_rel`` o fst o strip_comb))) >>
  rfs[]>>
  first_assum(match_exists_tac o concl) >> simp[] >>
  (* Stuff to carry along *)
  `q' ≠ Rerr (Rabort Rtype_error)` by
    (CCONTR_TAC>>fs[clos_relationTheory.res_rel_rw])>>

  (* renumber_correct *)
  (clos_numberProofTheory.renumber_code_locs_correct
   |> CONJUNCT1 |> SIMP_RULE std_ss []
   |> (fn th => first_assum (mp_tac o MATCH_MP th))) >>
  simp[] >>
  disch_then(qspecl_then[`s`,`c.next_loc`] mp_tac)>>simp[]>>
  impl_tac>-
    simp[clos_numberProofTheory.state_rel_def]>>
  strip_tac >>
  CONV_TAC(STRIP_QUANT_CONV
    (move_conj_left(same_const``clos_numberProof$state_rel`` o fst o
                    strip_comb))) >>
  first_assum(match_exists_tac o concl) >> simp[] >>
  (* Stuff to carry along *)
  rator_x_assum`renumber_code_locs_list`mp_tac >>
  specl_args_of_then``renumber_code_locs_list``
    (CONJUNCT1 clos_numberProofTheory.renumber_code_locs_every_Fn_vs_NONE)
    assume_tac >>
  specl_args_of_then``renumber_code_locs_list``
    (CONJUNCT1 clos_numberProofTheory.renumber_code_locs_every_Fn_SOME)
    assume_tac >>
  specl_args_of_then``renumber_code_locs_list``
    (CONJUNCT1 clos_numberProofTheory.renumber_code_locs_EVEN) assume_tac>>
  strip_tac>>
  fs[]>>rfs[]>>
  `res' ≠ Rerr (Rabort Rtype_error)` by
    (CCONTR_TAC>>fs[]>>metis_tac[evalPropsTheory.result_rel_Rerr1])>>
  `∃ime. clos_mti$compile c.do_mti [e] = [ime]` by
    (Cases_on`c.do_mti`>>fs[clos_mtiTheory.compile_def]>>
    metis_tac[clos_mtiTheory.intro_multi_sing]) >>
  `EVERY esgc_free [e]` by simp[] >>
  `EVERY esgc_free [ime]`
    by metis_tac[clos_mtiProofTheory.compile_preserves_esgc_free] >>
  `elist_globals [ime] = elist_globals [e]`
    by metis_tac[clos_mtiProofTheory.compile_preserves_elist_globals] >>
  rename1`renumber_code_locs_list _ (clos_mti$compile c.do_mti [e]) = (_, [ren_e])` >>
  `elist_globals [ren_e] = elist_globals [ime]`
    by metis_tac[clos_numberProofTheory.renumber_code_locs_elist_globals] >>
  `EVERY esgc_free [ren_e]`
    by metis_tac[clos_numberProofTheory.renumber_code_locs_esgc_free] >> fs[] >>
  fs[clos_numberTheory.renumber_code_locs_def] >> pairarg_tac>>fs[]>>
  pop_assum mp_tac>>
  specl_args_of_then``renumber_code_locs``
    clos_numberProofTheory.renumber_code_locs_distinct assume_tac>>
  strip_tac>>fs[]>>
  (* known correct *)
  `clos_knownProof$opt_state_rel c.do_known LN s s` by
    (Cases_on`c.do_known`>>
    fs[clos_knownProofTheory.opt_state_rel_def,
       clos_knownProofTheory.state_rel_def])>>
  mp_tac (clos_knownProofTheory.compile_correct
          |> INST_TYPE [alpha |-> ``:'ffi``]
          |> Q.INST [`e0` |-> `ren_e`,
                     `e` |->  `kcompile c.do_known ren_e`,
                     `s01` |-> `s`, `s1` |-> `t2`, `res1` |-> `res'`,
                     `s02` |-> `s`,`b` |-> `c.do_known`])>>
  simp[]>>
  impl_tac
  >-  (simp[ssgc_free_def,clos_knownProofTheory.state_globals_approx_def,
           closSemTheory.get_global_def] >> fs[EVERY_MEM] >>
      metis_tac[MEM_EL, NOT_SOME_NONE]) >>
  strip_tac>>
  CONV_TAC(STRIP_QUANT_CONV(move_conj_left(same_const``opt_res_rel`` o fst o strip_comb))) >>
  first_assum(match_exists_tac o concl) >> simp[] >>
  (* Stuff to carry along *)
  `res2 ≠ Rerr (Rabort Rtype_error)` by
    (Cases_on`c.do_known`>>fs[clos_knownProofTheory.opt_res_rel_def]>>
    CCONTR_TAC>>fs[])>>

  (* call *)
  drule clos_callProofTheory.compile_correct>>
  disch_then (qspecl_then [`c.do_call`,`s with code:= alist_to_fmap aux`,`e'`,`aux`] mp_tac)>>
  fs[clos_callProofTheory.code_includes_def]>>
  impl_keep_tac>-
    (rveq>>simp[CONJ_ASSOC]>>
    reverse CONJ_TAC (*Don't know where conj2_tac went??*)
    >-
      (simp[clos_callProofTheory.opt_init_state_rel_def]>>
      IF_CASES_TAC>>fs[clos_callProofTheory.state_rel_def,clos_callProofTheory.wfv_state_def,clos_callProofTheory.code_includes_def,FEVERY_FEMPTY,clos_callTheory.compile_def]>>
      rveq>>fs[closSemTheory.state_component_equality])
    >>
    reverse CONJ_TAC
    >-
      fs[clos_knownProofTheory.compile_code_locs,Once clos_removeProofTheory.code_loc'_def,SUBSET_DEF,EVERY_MEM,IN_DEF]
    >>
    Cases_on`c.do_known`>>fs[clos_knownTheory.compile_def]>>
    ntac 2 (pairarg_tac>>fs[])>>
    Q.ISPECL_THEN [`ren_e`,`[]:val_approx list`,`g'`] assume_tac clos_knownPropsTheory.known_sing>>
    Q.ISPECL_THEN [`[ren_e]`,`[]:val_approx list`,`g'`] assume_tac clos_knownProofTheory.known_code_locs>>
    rfs[]>>
    imp_res_tac clos_knownProofTheory.known_preserves_every_Fn_SOME>>
    imp_res_tac clos_knownProofTheory.known_preserves_every_Fn_NONE>>
    rfs[])>>
  strip_tac>>
  CONV_TAC(STRIP_QUANT_CONV(move_conj_left(same_const``opt_state_rel`` o fst o strip_comb))) >>
  first_assum(match_exists_tac o concl) >> simp[] >>
  CONV_TAC(STRIP_QUANT_CONV(move_conj_left(same_const``opt_result_rel`` o fst o strip_comb))) >>
  first_assum(match_exists_tac o concl) >> simp[] >>
  qpat_assum`A = (r2,t2')` mp_tac>>
  qpat_abbrev_tac`s_call = s with <|clock:=A;code:=B|>`>> strip_tac>>
  `r2 ≠ Rerr (Rabort Rtype_error)` by
    (Cases_on`c.do_call`>>fs[clos_callProofTheory.opt_result_rel_def]>>
    CCONTR_TAC>>fs[])>>
  (* remove *)
  qmatch_asmsub_abbrev_tac`compile c.do_remove ls`>>
  Q.ISPECL_THEN [`c.do_remove`,`ls`] mp_tac clos_removeProofTheory.compile_correct>>
  simp[]>>impl_keep_tac>-
    (* Property of call *)
    cheat
    (*Cases_on`c.do_remove`>>fs[clos_knownTheory.compile_def]>>
    pairarg_tac>>fs[]>>
    pairarg_tac>>fs[]>>
    imp_res_tac clos_knownProofTheory.known_preserves_every_Fn_NONE>>
    imp_res_tac clos_knownPropsTheory.known_sing_EQ_E>>
    fs[Once every_Fn_vs_NONE_EVERY,EVERY_MAP]*)>>
  fs[Abbr`ls`,remove_compile_alt]>>
  qpat_abbrev_tac`e'_remove = if A then B else C`>>
  qpat_abbrev_tac`aux_remove = MAP f aux`>>
  strip_tac>>
  (* Not true, but can be made true by splitting the remove steps *)
  qpat_assum`exp_rel _ [A] [B]` mp_tac>>
  simp[clos_relationTheory.exp_rel_def,clos_relationTheory.exec_rel_rw,clos_relationTheory.evaluate_ev_def] >>
  (* This is the reason full_state_rel can't be used *)
  disch_then(qspecl_then [`s_call.clock`,`[]`,`[]`,`s_call`,`s_call with code := alist_to_fmap aux_remove`] mp_tac)>>
  simp[Once clos_relationTheory.state_rel_rw]>>
  impl_tac>-
    (unabbrev_all_tac>>simp[]>>
    qpat_abbrev_tac`ls = MAP f aux`>>
    pop_assum kall_tac>>
    pop_assum mp_tac>>
    rpt(pop_assum kall_tac)>>
    qid_spec_tac`ls`>>
    Induct_on`aux`>>fs[alist_to_fmap_thm,FORALL_PROD]>>
    rw[]>>PairCases_on`y`>>fs[]>>
    match_mp_tac fmap_rel_FUPDATE_same>>rw[]>>
    fs[clos_relationTheory.exp_rel_def,clos_relationTheory.exec_rel_rw,clos_relationTheory.evaluate_ev_def] >>
    metis_tac[])>>
  disch_then(qspec_then`s_call.clock` assume_tac)>>rfs[]>>
  qmatch_assum_abbrev_tac`res_rel _ q` >>
  Cases_on`q`>>
  pop_assum mp_tac>> simp[Once markerTheory.Abbrev_def]>>
  disch_then (assume_tac o SYM)>>full_simp_tac(srw_ss())[] >>
  CONV_TAC(STRIP_QUANT_CONV(move_conj_left(same_const``clos_relation$res_rel`` o fst o strip_comb))) >>
  first_assum(match_exists_tac o concl) >> simp[] >>
  `q'' ≠ Rerr (Rabort Rtype_error)` by
    (CCONTR_TAC>>fs[])>>

  (* annotate *)
  (clos_annotateProofTheory.annotate_correct
   |> REWRITE_RULE[GSYM AND_IMP_INTRO]
   |> GEN_ALL
   |> (fn th => first_assum(mp_tac o MATCH_MP th))) >>
  simp[GSYM PULL_FORALL] >>
  impl_keep_tac >-
    (* chain with call properties *)
    cheat>>
  impl_keep_tac >-
   cheat>>
  qpat_abbrev_tac`s_remove = s_call with <|clock:=s_call.clock; code:=A|>`>>
  fs[clos_annotateTheory.compile_def]>>
  qmatch_asmsub_abbrev_tac`clos_to_bvl$compile_prog (_::aux_annot)`>>
  `∃z. annotate 0 [e'_remove] = [z]` by
    (simp[clos_annotateTheory.annotate_def]>>
    metis_tac[clos_freeTheory.free_SING,clos_annotateTheory.shift_SING,FST,PAIR])>>
  fs[PULL_FORALL]>>
  disch_then (qspecl_then [`s_remove with code := alist_to_fmap aux_annot`,`[]`] mp_tac)>>
  impl_tac>-
    (fs[Abbr`aux_annot`,Abbr`s_remove`,Abbr`s_call`,clos_annotateProofTheory.state_rel_def]>>
    rpt (pop_assum kall_tac)>>
    Induct_on`aux_remove`>>fs[FORALL_PROD]>>rw[]>>
    simp[clos_annotateTheory.annotate_def]>>
    metis_tac[clos_freeTheory.free_SING,clos_annotateTheory.shift_SING,FST,PAIR,HD])>>
  strip_tac>>
  simp[]>>
  CONV_TAC(STRIP_QUANT_CONV(move_conj_left(same_const``result_rel`` o fst o strip_comb))) >>
  first_assum(match_exists_tac o concl) >> simp[] >>
  CONV_TAC(STRIP_QUANT_CONV(move_conj_left(same_const``clos_annotateProof$state_rel`` o fst o strip_comb))) >>
  first_assum(match_exists_tac o concl) >> simp[] >>
  (* clos_to_bvl *)
  qmatch_assum_abbrev_tac`closSem$evaluate tmp = _` >>
  qspec_then`tmp`mp_tac(CONJUNCT1 compile_exps_correct) >>
  simp[Abbr`tmp`] >>
  fs[compile_prog_def]>>
  pairarg_tac>>fs[]>>
  disch_then(qspec_then`[]`mp_tac) >> simp[] >>
  qpat_abbrev_tac`s_annot = s_remove with code:=A`>>
  (* Constructed BVL state *)
  disch_then(qspecl_then [`initial_state s.ffi (fromAList p) (ck +s.clock)`,`[]`,`FEMPTY`] mp_tac)>>
  impl_tac>-
    (fs(map Abbr [`s_annot`,`s_remove`,`s_call`])>>
    rveq>>
    simp[env_rel_def,CONJ_ASSOC]>>
    reverse CONJ_TAC>-
      (simp[state_rel_def]>>
      simp[lookup_fromAList,ALOOKUP_APPEND,ALOOKUP_toAList,init_code_ok]>>
      cheat)>>
    (*TODO: a lot of these require syntactic properties which are also proved in
    the all_distinct proof...
    It might be possible to re use the ALL_DISTINCTNESS of the
    final code table *)
    cheat)>>
  `∃z. new_e = [z]` by
    metis_tac[compile_exps_SING]>>
  fs[]>>
  strip_tac>>
  srw_tac[][bvlSemTheory.evaluate_def] >>
  srw_tac[][bvlSemTheory.find_code_def] >>
  full_simp_tac(srw_ss())[code_installed_def] >>
  simp[lookup_fromAList,ALOOKUP_APPEND]>>
  `ALOOKUP (toAList init_code) c.start = NONE` by
    (simp[ALOOKUP_NONE,toAList_domain]>>
    CCONTR_TAC>>
    fs[]>>imp_res_tac domain_init_code_lt_num_stubs>>
    fs[])>>
  fs[]>>
  qexists_tac`res'''`>>
  qexists_tac`t2'''`>>
  qexists_tac`ck+ck'+1`>>
  qexists_tac`f2`>>
  unabbrev_all_tac>>fs[bvlSemTheory.dec_clock_def]>>
  rfs[]>>
  fs[])

(*
val compile_to_known_def = Define`
  compile_to_known c e =
     (let es = clos_mti$compile c.do_mti [e] in
      let (n,es) = renumber_code_locs_list c.next_loc es in
      let c = c with next_loc := n in
      let e = kcompile c.do_known (HD es) in e)`

(* composed compiler correctness
   s1 = initial clos state
   s2 = bvl state
   c = clos conf
   e = input expr to simulate compilation
*)
val full_state_rel_def = Define`
  full_state_rel c e s1 s2 ⇔
    ∃sa sb sc sd se sf f.
      state_rel s1.clock s1 sa ∧ s1.clock = sa.clock ∧         (* intro_multi *)
      clos_numberProof$state_rel sa sb ∧                   (* renumber *)
      EVERY ((=) NONE) sb.globals ∧ ssgc_free sb ∧
      clos_knownProof$opt_state_rel c.do_known LN sb sc ∧      (* known *)
      clos_callProof$opt_init_state_rel c.do_call sc sd ∧ (* call *)
      sd.code = alist_to_fmap (SND (clos_call$compile  c.do_call (compile_to_known c e))) ∧
      (* TODO: Not sure if this quantification will work... *)
      (∀k.
      state_rel (sd.clock+k) sd se) ∧            (* remove *)
      FEVERY (λp. every_Fn_vs_NONE [SND (SND p)]) se.code ∧
      clos_annotateProof$state_rel se sf ∧
      (* TODO: these FEVERYs need to be removed *)
      FEVERY (λp. every_Fn_vs_SOME [SND (SND p)]) sf.code ∧
      FEVERY (λp. every_Fn_SOME [SND (SND p)]) sf.code ∧
      clos_to_bvlProof$state_rel f sf s2`;

(* This is false if s2 has incremented clock...
val full_state_rel_with_clock = Q.store_thm("full_state_rel_with_clock",
  `full_state_rel c e s1 s2 ⇒
   full_state_rel c e(s1 with clock := k) (s2 with clock := k)`,
  srw_tac[][full_state_rel_def] >>
  qmatch_goalsub_rename_tac`clos_relation$state_rel ck` >>
  first_x_assum(qspec_then`ck`strip_assume_tac) >>
  qexists_tac`sa with clock := k` >> simp[] >>
  qexists_tac`sb with clock := k` >> simp[] >>
  qexists_tac`sc with clock := k` >> simp[]>>
  qexists_tac`sd with clock := k` >> simp[] >>
  qexists_tac`se with clock := k` >> simp[] >>
  qexists_tac`sf with clock := k` >> simp[] >>
  qexists_tac`f`>>simp[] >>
  fs[clos_numberProofTheory.state_rel_def,
     clos_knownProofTheory.state_rel_def,
     clos_knownProofTheory.opt_state_rel_def,
     clos_annotateProofTheory.state_rel_def,
     clos_callProofTheory.opt_init_state_rel_def]>>
  BasicProvers.EVERY_CASE_TAC>>
  fs[clos_callProofTheory.state_rel_def,clos_callProofTheory.wfv_state_def]);
*)

val full_result_rel_abort = Q.store_thm("full_result_rel_abort",
  `r ≠ Rerr(Rabort Rtype_error) ⇒ full_result_rel c (r,x) (Rerr (Rabort a),y) ⇒
   r = Rerr (Rabort a)`,cheat)
  (*srw_tac[][full_result_rel_def] >>
  Cases_on`rd`>> fs[clos_relationTheory.res_rel_rw]>>
  fs[clos_callProofTheory.opt_result_rel_def]>>
  Cases_on`rb` >>
  fs[clos_knownProofTheory.opt_res_rel_def]>>
  rename[`evalProps$exc_rel clos_numberProof$v_rel e1 e2`,
         `res_rel (Rerr e0,sb') (Rerr (Rabort a), sc)`] >>
  Cases_on`e0`>> fs[clos_relationTheory.res_rel_rw]>>
  fs[clos_knownProofTheory.krrel_err_rw] >>
  `e2 = Rabort Rtype_error ∨
   e2 = Rabort Rtimeout_error ∧ a' = Rtimeout_error` by
    (Cases_on`do_known`>>Cases_on`a'`>>fs[])>>
  rveq >>
  Cases_on`e1` >> fs[] >> rveq >>
  fs[clos_relationPropsTheory.res_rel_arg2_timeout] >> rveq >>
  fs[clos_relationTheory.res_rel_rw]);*)

val full_result_rel_timeout = Q.store_thm("full_result_rel_timeout",
  `full_result_rel c (Rerr(Rabort Rtimeout_error),x) (r,y) ⇒
   r = Rerr (Rabort Rtimeout_error)`,
  srw_tac[][full_result_rel_def,clos_knownProofTheory.opt_res_rel_def,clos_callProofTheory.opt_result_rel_def] >>
  BasicProvers.EVERY_CASE_TAC>>
  rpt (fs[clos_knownProofTheory.krrel_err_rw] >> rveq));

val full_result_rel_ffi = Q.store_thm("full_result_rel_ffi",
  `r ≠ Rerr (Rabort Rtype_error) ⇒
   full_result_rel c (r,s) (r1,s1) ⇒ s.ffi = s1.ffi`,cheat)
  (*
  srw_tac[][full_result_rel_def] >>
  imp_res_tac clos_relationPropsTheory.res_rel_ffi >>
  fs[clos_annotateProofTheory.state_rel_def,
     clos_numberProofTheory.state_rel_def,
     state_rel_def] >> rfs[] >>
  `sc.ffi = sd.ffi` by
    (Cases_on`c.do_call`>>fs[clos_callProofTheory.opt_state_rel_def,clos_callProofTheory.state_rel_def])>>
  rename1 `opt_res_rel _ _ (res1, _) (res2, _)` >>
  Cases_on`c.do_known`>>fs[clos_knownProofTheory.opt_res_rel_def]>>
  imp_res_tac clos_knownProofTheory.krrel_ffi >>
  Cases_on `rd ≠ Rerr (Rabort Rtype_error)` >> fs[]>>
  rfs[]
  rveq>>fs[]
   rveq>> fs[]
  rfs[]
   >- (rveq >> fs[]) >>
  Cases_on `res1 = Rerr (Rabort Rtype_error)` >> fs[])*)

val compile_evaluate = Q.store_thm("compile_evaluate",
  `evaluate ([e],[],s) = (r,s') ∧
   ¬contains_App_SOME [e] ∧ every_Fn_vs_NONE [e] ∧ esgc_free e ∧
   BAG_ALL_DISTINCT (set_globals e) ∧
   r ≠ Rerr (Rabort Rtype_error) ∧
   compile c e = (c',p)  ∧
   full_state_rel c e (s:'ffi closSem$state) s1 ∧
   code_installed p s1.code
   ⇒
   ∃r1 s'1 ck.
     evaluate ([Call 0 (SOME c'.start) []],[],s1 with clock := s.clock + ck) = (r1,s'1) ∧
     full_result_rel c (r,s') (r1,s'1)`,
  srw_tac[][compile_def,LET_THM,full_state_rel_def] >>
  rpt(first_assum(split_uncurry_arg_tac o lhs o concl) >>
      full_simp_tac(srw_ss())[]) >>
  `∃z. es = [z]` by (
    Cases_on`c.do_mti`>>fs[clos_mtiTheory.compile_def]>>
    metis_tac[clos_mtiTheory.intro_multi_sing, SING_HD, SND,
              clos_numberTheory.renumber_code_locs_length,
              LENGTH, ONE] ) >>
  (* intro_multi correct *)
  qspecl_then[`c.do_mti`,`[e]`]mp_tac clos_mtiProofTheory.compile_correct >>
  simp[clos_relationTheory.exp_rel_def,clos_relationTheory.exec_rel_rw,clos_relationTheory.evaluate_ev_def] >>
  disch_then(fn th => last_assum(mp_tac o MATCH_MP(REWRITE_RULE[GSYM AND_IMP_INTRO]th))) >>
  disch_then(qspec_then`[]`mp_tac) >> simp[] >>
  disch_then(qspec_then`s.clock`mp_tac) >> simp[] >>
  strip_tac >>
  simp[full_result_rel_def,PULL_EXISTS] >>
  qmatch_assum_abbrev_tac`res_rel _ q` >>
  Cases_on`q`>>full_simp_tac(srw_ss())[markerTheory.Abbrev_def]>>
  pop_assum(assume_tac o SYM) >> full_simp_tac(srw_ss())[] >>
  CONV_TAC(STRIP_QUANT_CONV
    (move_conj_left(same_const``clos_relation$res_rel`` o fst o strip_comb))) >>
  first_assum(match_exists_tac o concl) >> simp[] >>

  (* renumber_correct *)
  (clos_numberProofTheory.renumber_code_locs_correct
   |> CONJUNCT1 |> SIMP_RULE std_ss []
   |> (fn th => first_assum (mp_tac o MATCH_MP th))) >>
  simp[] >>
  disch_then(fn th => first_assum(mp_tac o MATCH_MP th)) >>
  disch_then(qspec_then`c.next_loc`mp_tac) >> simp[] >> strip_tac >>
  CONV_TAC(STRIP_QUANT_CONV
    (move_conj_left(same_const``clos_numberProof$state_rel`` o fst o
                    strip_comb))) >>
  first_assum(match_exists_tac o concl) >> simp[] >>
  rator_x_assum`renumber_code_locs_list`mp_tac >>
  specl_args_of_then``renumber_code_locs_list``
    (CONJUNCT1 clos_numberProofTheory.renumber_code_locs_every_Fn_vs_NONE)
    assume_tac >>
  specl_args_of_then``renumber_code_locs_list``
    (CONJUNCT1 clos_numberProofTheory.renumber_code_locs_every_Fn_SOME)
    assume_tac >>
  strip_tac >> full_simp_tac(srw_ss())[] >> rev_full_simp_tac(srw_ss())[] >>

  (* known correct *)
  `∃ime. clos_mti$compile c.do_mti [e] = [ime]` by
    (Cases_on`c.do_mti`>>fs[clos_mtiTheory.compile_def]>>
    metis_tac[clos_mtiTheory.intro_multi_sing]) >>
  `EVERY esgc_free [e]` by simp[] >>
  `EVERY esgc_free [ime]`
    by metis_tac[clos_mtiProofTheory.compile_preserves_esgc_free] >>
  `elist_globals [ime] = elist_globals [e]`
    by metis_tac[clos_mtiProofTheory.compile_preserves_elist_globals] >>
  rename1`renumber_code_locs_list _ (clos_mti$compile c.do_mti [e]) = (_, [ren_e])` >>
  `elist_globals [ren_e] = elist_globals [ime]`
    by metis_tac[clos_numberProofTheory.renumber_code_locs_elist_globals] >>
  `EVERY esgc_free [ren_e]`
    by metis_tac[clos_numberProofTheory.renumber_code_locs_esgc_free] >> fs[] >>
  rename[`kcompile _ kexp0`, `evaluate([kexp0],_,ks0) = (kres1, ks1)`,
         `opt_state_rel _ LN ks0 ks02`] >>

  mp_tac (clos_knownProofTheory.compile_correct
          |> INST_TYPE [alpha |-> ``:'ffi``]
          |> Q.INST [`e0` |-> `kexp0`, `e` |->  `kcompile c.do_known kexp0`,
                     `s01` |-> `ks0`, `s1` |-> `ks1`, `res1` |-> `kres1`,
                     `s02` |-> `ks02`,`b` |-> `c.do_known`])>>
  simp[]>>
  impl_tac
  >- (simp[clos_knownProofTheory.state_globals_approx_def,
           closSemTheory.get_global_def] >> fs[EVERY_MEM] >>
      metis_tac[MEM_EL, NOT_SOME_NONE]) >>
  strip_tac>>
  CONV_TAC(STRIP_QUANT_CONV(move_conj_left(same_const``opt_res_rel`` o fst o strip_comb))) >>
  first_assum(match_exists_tac o concl) >> simp[] >>

  (* call *)
  drule clos_callProofTheory.compile_correct>>
  disch_then (qspecl_then [`c.do_call`,`sd`,`e'`,`aux`] mp_tac)>>
  fs[clos_callProofTheory.code_includes_def,compile_to_known_def]>>
  impl_keep_tac>-
    (* These seem okay, except maybe some new assumptions are needed *)
    cheat>>
  strip_tac>>
  CONV_TAC(STRIP_QUANT_CONV(move_conj_left(same_const``opt_state_rel`` o fst o strip_comb))) >>
  first_assum(match_exists_tac o concl) >> simp[] >>
  CONV_TAC(STRIP_QUANT_CONV(move_conj_left(same_const``opt_result_rel`` o fst o strip_comb))) >>
  first_assum(match_exists_tac o concl) >> simp[] >>

  (* remove *)
  qmatch_asmsub_abbrev_tac`compile c.do_remove ls`>>
  `∃ls'. clos_remove$compile c.do_remove ls = ls'` by
    fs[]>>
  Q.ISPECL_THEN [`c.do_remove`,`ls`] mp_tac clos_removeProofTheory.compile_correct>>
  simp[]>>impl_keep_tac>-
    (* Property of call *)
    cheat
    (*Cases_on`c.do_remove`>>fs[clos_knownTheory.compile_def]>>
    pairarg_tac>>fs[]>>
    pairarg_tac>>fs[]>>
    imp_res_tac clos_knownProofTheory.known_preserves_every_Fn_NONE>>
    imp_res_tac clos_knownPropsTheory.known_sing_EQ_E>>
    fs[Once every_Fn_vs_NONE_EVERY,EVERY_MAP]*)>>
  simp[clos_relationTheory.exp_rel_def,clos_relationTheory.exec_rel_rw,clos_relationTheory.evaluate_ev_def] >>
  first_x_assum(qspec_then`ck` assume_tac)>>
  disch_then(fn th => first_assum(mp_tac o MATCH_MP(REWRITE_RULE[GSYM AND_IMP_INTRO]th))) >>
  disch_then(qspec_then`[]`mp_tac) >> simp[] >>
  disch_then(qspec_then`ck+sd.clock`mp_tac) >> simp[] >>
  strip_tac >>
  qmatch_assum_abbrev_tac`res_rel _ q` >>
  Cases_on`q`>>full_simp_tac(srw_ss())[markerTheory.Abbrev_def]>>pop_assum(assume_tac o SYM) >> full_simp_tac(srw_ss())[] >>
  rveq>>fs[]>>
  qpat_assum`res_rel A B` mp_tac>>
  simp[Once evaluate_CONS]
  CONV_TAC(STRIP_QUANT_CONV(move_conj_left(same_const``clos_relation$res_rel`` o fst o strip_comb))) >>
  first_assum(match_exists_tac o concl) >> simp[] >>
  (clos_annotateProofTheory.annotate_correct
   |> REWRITE_RULE[GSYM AND_IMP_INTRO]
   |> GEN_ALL
   |> (fn th => first_assum(mp_tac o MATCH_MP th))) >>
  simp[GSYM PULL_FORALL] >>
  impl_keep_tac >- (
    strip_tac >>
    Cases_on`r`>> full_simp_tac(srw_ss())[clos_relationTheory.res_rel_rw] >>
    srw_tac[][] >> full_simp_tac(srw_ss())[] >> srw_tac[][] >> full_simp_tac(srw_ss())[clos_relationTheory.res_rel_rw] >>
    Cases_on`b`>>fs[clos_knownProofTheory.opt_res_rel_def]
    (*Not sure why the proof got so much easier,
      hopefully due to automatic rewrites and not a bad contradiction...
    rename1`res_rel (Rerr err,_) _` >>
    Cases_on`err`>>full_simp_tac(srw_ss())[clos_relationTheory.res_rel_rw] >>
    srw_tac[][] >> full_simp_tac(srw_ss())[] >> srw_tac[][] >> full_simp_tac(srw_ss())[clos_relationTheory.res_rel_rw] >>
    rename1`Rabort a` >>
    Cases_on`a`>>full_simp_tac(srw_ss())[clos_relationTheory.res_rel_rw] >>
    srw_tac[][] >> full_simp_tac(srw_ss())[] >> srw_tac[][] >> full_simp_tac(srw_ss())[clos_relationTheory.res_rel_rw]*) )>>
  impl_tac >- metis_tac[clos_removeProofTheory.every_Fn_vs_NONE_compile] >>
  disch_then(fn th => first_assum(qspec_then`[]`strip_assume_tac o MATCH_MP th)) >>
  imp_res_tac evaluate_const >> simp[] >>
  CONV_TAC(STRIP_QUANT_CONV(move_conj_left(same_const``clos_annotateProof$state_rel`` o fst o strip_comb))) >>
  first_assum(match_exists_tac o concl) >> simp[] >>
  qmatch_assum_abbrev_tac`closSem$evaluate tmp = _` >>
  qspec_then`tmp`mp_tac(CONJUNCT1 compile_exps_correct) >>
  simp[Abbr`tmp`] >>
  disch_then(qspec_then`[]`mp_tac) >> simp[] >>
  CONV_TAC(LAND_CONV(STRIP_QUANT_CONV(LAND_CONV(move_conj_left(same_const``clos_to_bvlProof$state_rel`` o fst o strip_comb))))) >>
  disch_then(fn th => first_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]th))) >>
  disch_then(qspec_then`[]`mp_tac) >>
  simp[env_rel_def] >>
  impl_tac >- (
    rpt var_eq_tac >>
    full_simp_tac(srw_ss())[code_installed_def] >>
    CONJ_TAC>-
      (strip_tac >> full_simp_tac(srw_ss())[] )
    >>
      match_mp_tac (clos_removeProofTheory.every_Fn_SOME_compile|>REWRITE_RULE[AND_IMP_INTRO]) >> simp[] >>
      qexists_tac`c.do_remove`>>
      qexists_tac`[kcompile b kexp0]`>>
      Cases_on`b`>>
      fs[clos_knownTheory.compile_def]>>
      rpt (pairarg_tac>>fs[])>>
      imp_res_tac clos_knownProofTheory.known_preserves_every_Fn_SOME>>
      imp_res_tac clos_knownPropsTheory.known_sing_EQ_E>>
      fs[])>>
  strip_tac >>
  CONV_TAC(STRIP_QUANT_CONV(move_conj_left(same_const``result_rel`` o fst o strip_comb))) >>
  first_assum(match_exists_tac o concl) >> simp[] >>
  CONV_TAC(STRIP_QUANT_CONV(move_conj_left(same_const``result_rel`` o fst o strip_comb))) >>
  first_assum(match_exists_tac o concl) >> simp[] >>
  srw_tac[][bvlSemTheory.evaluate_def] >>
  srw_tac[][bvlSemTheory.find_code_def] >>
  full_simp_tac(srw_ss())[code_installed_def] >>
  `∃z. clos_remove$compile c.do_remove [kcompile b kexp0] = [z]` by
    (Cases_on`c.do_remove`>>fs[clos_removeTheory.compile_def]>>
    metis_tac[FST,PAIR,clos_removeTheory.remove_SING])>>
  qmatch_assum_rename_tac`compile_exps _ _ = (esl,_)` >>
  `∃z. esl = [z]` by (
    metis_tac[clos_annotateTheory.shift_SING,
              clos_annotateTheory.annotate_def,
              clos_freeTheory.free_SING, FST, PAIR,
              compile_exps_SING] ) >>
  full_simp_tac(srw_ss())[] >>
  qexists_tac`ck+1` >>
  simp[bvlSemTheory.dec_clock_def] >>
  fs[clos_knownProofTheory.opt_state_rel_def]>>
  Cases_on`b`>>fs[clos_knownProofTheory.state_rel_def]>>
  metis_tac[clos_numberProofTheory.state_rel_def,
            clos_annotateProofTheory.state_rel_def]);
*)

val full_result_rel_abort = Q.store_thm("full_result_rel_abort",
  `r ≠ Rerr(Rabort Rtype_error) ⇒ full_result_rel c (r,x) (Rerr (Rabort a),y) ⇒
   r = Rerr (Rabort a)`,
  srw_tac[][full_result_rel_def] >>
  Cases_on`rd`>> fs[clos_relationTheory.res_rel_rw]>>
  fs[clos_callProofTheory.opt_result_rel_def]>>
  Cases_on`rc` >> fs[] >>
  fs[clos_knownProofTheory.opt_res_rel_def]>>
  Cases_on`rb` >> fs[] >> rveq >>
  Cases_on`r` >> fs[] >>
  Cases_on`e` >> fs[clos_relationTheory.res_rel_rw] >>
  rename[`Rerr (Rabort a)`,`err = Rabort a`] >>
  Cases_on`err` \\ fs[clos_relationTheory.res_rel_rw] >>
  fs[clos_knownProofTheory.krrel_err_rw] >>
  qmatch_rename_tac`err = _` >>
  Cases_on`err` >> fs[clos_relationTheory.res_rel_rw]
  \\ rveq \\ fs[] \\ rveq \\ fs[]
  \\ qmatch_rename_tac`ab = _`
  \\ Cases_on`ab` >> fs[clos_relationTheory.res_rel_rw]
  \\ rveq \\ fs[] \\ rveq \\ fs[]
  \\ qmatch_rename_tac`_ = ab`
  \\ Cases_on`ab` >> fs[]
  \\ rveq \\ fs[] \\ every_case_tac \\ fs[] \\ rveq \\ fs[])

val full_result_rel_timeout = Q.store_thm("full_result_rel_timeout",
  `full_result_rel c (Rerr(Rabort Rtimeout_error),x) (r,y) ⇒
   r = Rerr (Rabort Rtimeout_error)`,
  srw_tac[][full_result_rel_def,clos_knownProofTheory.opt_res_rel_def,clos_callProofTheory.opt_result_rel_def] >>
  BasicProvers.EVERY_CASE_TAC>>
  rpt (fs[clos_knownProofTheory.krrel_err_rw] >> rveq));

val full_result_rel_ffi = Q.store_thm("full_result_rel_ffi",
  `r ≠ Rerr (Rabort Rtype_error) ⇒
   full_result_rel c (r,s) (r1,s1) ⇒ s.ffi = s1.ffi`,
  srw_tac[][full_result_rel_def] >>
  imp_res_tac clos_relationPropsTheory.res_rel_ffi >>
  fs[clos_annotateProofTheory.state_rel_def,
     clos_numberProofTheory.state_rel_def,
     state_rel_def] >> rfs[] >>
  `sd.ffi = sc.ffi` by
    (Cases_on`c.do_call`>>fs[clos_callProofTheory.opt_state_rel_def,clos_callProofTheory.state_rel_def])>>
  `sc.ffi = sb.ffi` by (
    fs[clos_knownProofTheory.opt_res_rel_def] >>
    Cases_on`c.do_known` >> fs[] >>
    match_mp_tac (GEN_ALL clos_knownProofTheory.krrel_ffi) >>
    asm_exists_tac \\ rw[]
    \\ spose_not_then strip_assume_tac \\ fs[]) >>
  fs[] >> match_mp_tac EQ_SYM >> first_x_assum match_mp_tac >>
  spose_not_then strip_assume_tac \\ fs[] >>
  `rc = Rerr (Rabort Rtype_error)` by (
    fs[clos_callProofTheory.opt_result_rel_def] >>
    Cases_on`c.do_call` >> fs[] ) >>
  `rb = Rerr (Rabort Rtype_error)` by (
    fs[clos_knownProofTheory.opt_res_rel_def]>>
    metis_tac[] ) >>
  fs[]);

val compile_semantics = Q.store_thm("compile_semantics",
  `¬contains_App_SOME [e] ∧ every_Fn_vs_NONE [e] ∧ esgc_free e ∧
   BAG_ALL_DISTINCT (set_globals e) ∧
   compile c e = (c',p) ∧ num_stubs ≤ c.start ∧ c.start < c.next_loc ∧ EVEN c.next_loc ∧
   clos_init (s:'ffi closSem$state) ∧
   semantics [] s [e] ≠ Fail
   ⇒
   semantics s.ffi (fromAList p) c'.start =
   semantics [] s [e]`,
  rpt strip_tac >> qpat_assum `closSem$semantics _ _ _ ≠ Fail` mp_tac >>
  simp[closSemTheory.semantics_def] >>
  IF_CASES_TAC >> full_simp_tac(srw_ss())[] >>
  DEEP_INTRO_TAC some_intro >> simp[] >>
  conj_tac >- (
    gen_tac >> strip_tac >> rveq >> full_simp_tac(srw_ss())[] >>
    simp[bvlSemTheory.semantics_def] >>
    IF_CASES_TAC >> full_simp_tac(srw_ss())[] >- (
      first_assum(subterm (fn tm => Cases_on`^(assert(has_pair_type)tm)`) o concl) >>
      drule bvlPropsTheory.evaluate_add_clock >>
      impl_tac >- full_simp_tac(srw_ss())[] >> strip_tac >>
      rator_x_assum`closSem$evaluate`kall_tac >>
      last_assum(qspec_then`k'`mp_tac)>>
      (fn g => subterm (fn tm => Cases_on`^(assert(has_pair_type)tm)`) (#2 g) g) >>
      drule (GEN_ALL compile_evaluate) >> fs[] >>
      simp[RIGHT_FORALL_IMP_THM,GSYM AND_IMP_INTRO] >>
      impl_tac >- ( strip_tac >> PROVE_TAC[FST] ) >>
      disch_then drule >> fs[] >>
      strip_tac >>
      first_x_assum(qspec_then`ck`mp_tac) >>
      simp[inc_clock_def] >>
      strip_tac >> rveq >>
      spose_not_then strip_assume_tac >>
      imp_res_tac full_result_rel_abort ) >>
    DEEP_INTRO_TAC some_intro >> simp[] >>
    conj_tac >- (
      gen_tac >> strip_tac >> rveq >> full_simp_tac(srw_ss())[] >>
      qmatch_assum_abbrev_tac`closSem$evaluate (bxps,[],bs) = _` >>
      qmatch_assum_abbrev_tac`bvlSem$evaluate (exps,[],ss) = _` >>
      qspecl_then[`(bxps,[],bs)`](mp_tac o Q.GEN`extra`) (CONJUNCT1 closPropsTheory.evaluate_add_to_clock_io_events_mono) >>
      qspecl_then[`exps`,`[]`,`ss`]mp_tac (INST_TYPE[alpha|->``:'ffi``]bvlPropsTheory.evaluate_add_to_clock_io_events_mono) >>
      simp[bvlPropsTheory.inc_clock_def,Abbr`ss`,Abbr`bs`] >>
      ntac 2 strip_tac >>
      Cases_on`s'.ffi.final_event`>>full_simp_tac(srw_ss())[] >- (
        Cases_on`s''.ffi.final_event`>>full_simp_tac(srw_ss())[]>-(
          unabbrev_all_tac >>
          drule (GEN_ALL compile_evaluate) >> fs[] >>
          rpt(disch_then drule) >>
          strip_tac >>
          drule bvlPropsTheory.evaluate_add_clock >>
          impl_tac >- (
            PROVE_TAC[FST,full_result_rel_abort] ) >>
          disch_then(qspec_then`k'`mp_tac)>>simp[bvlPropsTheory.inc_clock_def]>>
          rator_x_assum`bvlSem$evaluate`mp_tac >>
          drule bvlPropsTheory.evaluate_add_clock >>
          impl_tac >- ( strip_tac >> full_simp_tac(srw_ss())[] ) >>
          disch_then(qspec_then`ck+k`mp_tac)>>simp[bvlPropsTheory.inc_clock_def]>>
          ntac 3 strip_tac >> rveq >> full_simp_tac(srw_ss())[] >>
          full_simp_tac(srw_ss())[state_component_equality] >>
          metis_tac[full_result_rel_ffi]) >>
        first_x_assum(qspec_then`k'`strip_assume_tac) >>
        first_assum(subterm (fn tm => Cases_on`^(assert has_pair_type tm)`) o concl) >> full_simp_tac(srw_ss())[] >>
        unabbrev_all_tac >>
        drule (GEN_ALL compile_evaluate) >>
        CONV_TAC(LAND_CONV(SIMP_CONV(srw_ss())[RIGHT_FORALL_IMP_THM,GSYM AND_IMP_INTRO])) >>
        REWRITE_TAC[AND_IMP_INTRO] >>
        impl_tac >- ( strip_tac >> PROVE_TAC[FST] ) >>
        CONV_TAC(LAND_CONV(SIMP_CONV(srw_ss())[RIGHT_FORALL_IMP_THM,GSYM AND_IMP_INTRO])) >>
        disch_then drule >>
        disch_then drule >>
        disch_then drule >>
        CONV_TAC(LAND_CONV(SIMP_CONV(srw_ss())[LET_THM])) >> strip_tac >>
        rator_x_assum`closSem$evaluate`mp_tac >>
        drule (Q.GEN`extra`(SIMP_RULE std_ss [] (CONJUNCT1 closPropsTheory.evaluate_add_to_clock))) >>
        CONV_TAC(LAND_CONV(SIMP_CONV(srw_ss())[RIGHT_FORALL_IMP_THM])) >>
        impl_tac >- (strip_tac >> full_simp_tac(srw_ss())[]) >>
        disch_then(qspec_then`k'`mp_tac)>>
        first_x_assum(qspec_then`ck+k`mp_tac)>>simp[] >>
        fsrw_tac[ARITH_ss][] >>
        rpt strip_tac >> spose_not_then strip_assume_tac >>
        rveq >> fsrw_tac[ARITH_ss][state_rel_def] >>
        `q ≠ Rerr(Rabort Rtype_error)` by metis_tac[] >>
        imp_res_tac full_result_rel_ffi >> full_simp_tac(srw_ss())[]) >>
      first_x_assum(qspec_then`k'`strip_assume_tac) >>
      first_assum(subterm (fn tm => Cases_on`^(assert has_pair_type tm)`) o concl) >> full_simp_tac(srw_ss())[] >>
      unabbrev_all_tac >>
      drule (GEN_ALL compile_evaluate) >>
      simp[RIGHT_FORALL_IMP_THM,GSYM AND_IMP_INTRO] >>
      impl_keep_tac >- ( strip_tac >> PROVE_TAC[FST] ) >>
      rpt(disch_then drule) >>
      strip_tac >> rveq >>
      fsrw_tac[ARITH_ss][] >>
      reverse(Cases_on`s''.ffi.final_event`)>>full_simp_tac(srw_ss())[]>>rev_full_simp_tac(srw_ss())[]>- (
        first_x_assum(qspec_then`ck+k`mp_tac) >>
        fsrw_tac[ARITH_ss][ADD1] >> strip_tac >>
        full_simp_tac(srw_ss())[state_rel_def] >> rev_full_simp_tac(srw_ss())[] >>
        imp_res_tac full_result_rel_ffi >>
        full_simp_tac(srw_ss())[] >> rev_full_simp_tac(srw_ss())[]) >>
      rator_x_assum`bvlSem$evaluate`mp_tac >>
      drule bvlPropsTheory.evaluate_add_clock >>
      impl_tac >- (strip_tac >> full_simp_tac(srw_ss())[]) >>
      disch_then(qspec_then`ck+k`mp_tac)>>simp[bvlPropsTheory.inc_clock_def] >>
      fsrw_tac[ARITH_ss][ADD1] >>
      strip_tac >> spose_not_then strip_assume_tac >> rveq >>
      fsrw_tac[ARITH_ss][state_rel_def] >> rev_full_simp_tac(srw_ss())[] >>
      imp_res_tac full_result_rel_ffi >> full_simp_tac(srw_ss())[] >> rev_full_simp_tac(srw_ss())[]) >>
    simp_tac(srw_ss()++QUANT_INST_ss[pair_default_qp])[] >>
    drule (GEN_ALL compile_evaluate) >> fs[] >>
    simp[RIGHT_FORALL_IMP_THM,GSYM AND_IMP_INTRO] >>
    impl_keep_tac >- ( strip_tac >> PROVE_TAC[FST] ) >>
    rpt(disch_then drule) >>
    strip_tac >>
    qexists_tac`ck + k` >> simp[] >>
    imp_res_tac full_result_rel_ffi >>
    CASE_TAC >> full_simp_tac(srw_ss())[] >> rpt strip_tac >>
    PROVE_TAC[full_result_rel_abort]) >>
  strip_tac >>
  simp[bvlSemTheory.semantics_def] >>
  IF_CASES_TAC >> full_simp_tac(srw_ss())[] >- (
    last_x_assum(qspec_then`k`strip_assume_tac) >>
    qmatch_assum_abbrev_tac`FST q ≠ _` >>
    Cases_on`q`>>full_simp_tac(srw_ss())[markerTheory.Abbrev_def] >>
    pop_assum(assume_tac o SYM) >>
    first_assum(mp_tac o MATCH_MP (REWRITE_RULE[GSYM AND_IMP_INTRO](GEN_ALL compile_evaluate))) >>
    simp[GSYM PULL_FORALL] >>
    rpt(first_assum(match_exists_tac o concl)>>simp[]) >>
    spose_not_then strip_assume_tac >>
    qmatch_assum_abbrev_tac`FST q = _` >>
    Cases_on`q`>>full_simp_tac(srw_ss())[markerTheory.Abbrev_def] >>
    pop_assum(assume_tac o SYM) >>
    imp_res_tac evaluate_add_clock >> rev_full_simp_tac(srw_ss())[] >>
    first_x_assum(qspec_then`ck`mp_tac) >>
    simp[inc_clock_def] >>
    spose_not_then strip_assume_tac >> full_simp_tac(srw_ss())[] >>
    imp_res_tac full_result_rel_abort) >>
  DEEP_INTRO_TAC some_intro >> simp[] >>
  conj_tac >- (
    spose_not_then strip_assume_tac >>
    fsrw_tac[QUANT_INST_ss[pair_default_qp]][] >>
    last_x_assum(qspec_then`k`mp_tac) >>
    (fn g => subterm (fn tm => Cases_on`^(assert (can dest_prod o type_of) tm)` g) (#2 g)) >>
    strip_tac >>
    first_assum(mp_tac o MATCH_MP (REWRITE_RULE[GSYM AND_IMP_INTRO](GEN_ALL compile_evaluate))) >>
    simp[] >> fs[] >>
    rpt(first_assum(match_exists_tac o concl)>>simp[]) >>
    spose_not_then strip_assume_tac >>
    last_x_assum(qspec_then`k`strip_assume_tac) >> rev_full_simp_tac(srw_ss())[] >>
    reverse(Cases_on`s'.ffi.final_event`)>>full_simp_tac(srw_ss())[] >- (
      rator_x_assum`bvlSem$evaluate`mp_tac >>
      qmatch_assum_abbrev_tac`bvlSem$evaluate (exps,[],ss) = _` >>
      qspecl_then[`exps`,`[]`,`ss`]mp_tac (INST_TYPE[alpha|->``:'ffi``]bvlPropsTheory.evaluate_add_to_clock_io_events_mono) >>
      disch_then(qspec_then`ck`mp_tac)>>
      fsrw_tac[ARITH_ss][ADD1,bvlPropsTheory.inc_clock_def,Abbr`ss`] >>
      rpt strip_tac >> full_simp_tac(srw_ss())[] >>
      imp_res_tac full_result_rel_ffi >> full_simp_tac(srw_ss())[]) >>
    rator_x_assum`bvlSem$evaluate`mp_tac >>
    drule bvlPropsTheory.evaluate_add_clock >>
    impl_tac >- (strip_tac >> full_simp_tac(srw_ss())[]) >>
    disch_then(qspec_then`ck`mp_tac) >>
    simp[bvlPropsTheory.inc_clock_def] >>
    fsrw_tac[ARITH_ss][ADD1] >>
    rpt strip_tac >> full_simp_tac(srw_ss())[] >>
    imp_res_tac full_result_rel_ffi >>
    spose_not_then strip_assume_tac >>
    full_simp_tac(srw_ss())[state_component_equality] >> rveq >> full_simp_tac(srw_ss())[] >>
    Cases_on`a`>>full_simp_tac(srw_ss())[]>>
    imp_res_tac full_result_rel_timeout >> full_simp_tac(srw_ss())[]) >>
  strip_tac >>
  qmatch_abbrev_tac`build_lprefix_lub l1 = build_lprefix_lub l2` >>
  `(lprefix_chain l1 ∧ lprefix_chain l2) ∧ equiv_lprefix_chain l1 l2`
    suffices_by metis_tac[build_lprefix_lub_thm,lprefix_lub_new_chain,unique_lprefix_lub] >>
  conj_asm1_tac >- (
    UNABBREV_ALL_TAC >>
    conj_tac >>
    Ho_Rewrite.ONCE_REWRITE_TAC[GSYM o_DEF] >>
    REWRITE_TAC[IMAGE_COMPOSE] >>
    match_mp_tac prefix_chain_lprefix_chain >>
    simp[prefix_chain_def,PULL_EXISTS] >>
    qx_genl_tac[`k1`,`k2`] >>
    qspecl_then[`k1`,`k2`]mp_tac LESS_EQ_CASES >>
    metis_tac[
      LESS_EQ_EXISTS, initial_state_with_simp,
      closPropsTheory.evaluate_add_to_clock_io_events_mono
        |> CONJUNCT1 |> CONV_RULE(RESORT_FORALL_CONV List.rev)
        |> Q.SPEC`s with clock := k` |> SIMP_RULE (srw_ss())[],
      bvlPropsTheory.evaluate_add_to_clock_io_events_mono
        |> CONV_RULE(RESORT_FORALL_CONV(sort_vars["s"]))
        |> Q.SPEC`s with clock := k`
        |> SIMP_RULE (srw_ss())[bvlPropsTheory.inc_clock_def]]) >>
  simp[equiv_lprefix_chain_thm] >>
  unabbrev_all_tac >> simp[PULL_EXISTS] >>
  ntac 2 (pop_assum kall_tac) >>
  simp[LNTH_fromList,PULL_EXISTS] >>
  simp[GSYM FORALL_AND_THM] >>
  rpt gen_tac >>
  reverse conj_tac >>
  strip_tac >>
  fsrw_tac[QUANT_INST_ss[pair_default_qp]][] >> srw_tac[][] >>
  (compile_evaluate
   |> Q.GEN`s` |> Q.SPEC`s with clock := k`
   |> GEN_ALL |> SIMP_RULE(srw_ss()++QUANT_INST_ss[pair_default_qp])[]
   |> Q.SPECL[`s`,`k`,`e`,`c`] |> mp_tac) >>
  (impl_tac >- ( simp[] )) >>
  srw_tac[][] >> fs[] >>
  qmatch_assum_abbrev_tac`full_result_rel c p1 p2` >>
  Cases_on`p1`>>Cases_on`p2`>>full_simp_tac(srw_ss())[markerTheory.Abbrev_def] >> rveq >>
  pop_assum(mp_tac o SYM) >> strip_tac >> full_simp_tac(srw_ss())[] >>
  qmatch_assum_rename_tac`full_result_rel c (a1,b1) (a2,b2)` >>
  `b1.ffi = b2.ffi` by (
    metis_tac[FST,full_result_rel_abort,full_result_rel_ffi,
              semanticPrimitivesTheory.result_11,
              semanticPrimitivesTheory.error_result_11,
              semanticPrimitivesTheory.abort_distinct])
  >- ( qexists_tac`k+ck` >> fs[] ) >>
  qexists_tac`k` >> fs[] >>
  qmatch_assum_abbrev_tac`n < (LENGTH (_ ffi))` >>
  `ffi.io_events ≼ b2.ffi.io_events` by (
    qunabbrev_tac`ffi` >>
    metis_tac[
      initial_state_with_simp,
      bvlPropsTheory.evaluate_add_to_clock_io_events_mono
        |> CONV_RULE(RESORT_FORALL_CONV(sort_vars["s"]))
        |> Q.SPEC`s with clock := k`
        |> SIMP_RULE(srw_ss())[bvlPropsTheory.inc_clock_def],
      SND,ADD_SYM]) >>
  full_simp_tac(srw_ss())[IS_PREFIX_APPEND] >> simp[EL_APPEND1]);

val _ = export_theory();
