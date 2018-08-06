open preamble
     closLangTheory closSemTheory closPropsTheory
     bvlSemTheory bvlPropsTheory
     bvl_jumpProofTheory
     clos_to_bvlTheory
     backend_commonTheory;

local
open
  clos_mtiProofTheory
  clos_numberProofTheory
  clos_knownProofTheory
  clos_annotateProofTheory
  clos_callProofTheory
in end

val _ = new_theory"clos_to_bvlProof";

val _ = temp_bring_to_front_overload"evaluate"{Name="evaluate",Thy="bvlSem"};
val _ = temp_bring_to_front_overload"num_stubs"{Name="num_stubs",Thy="clos_to_bvl"};
val _ = temp_bring_to_front_overload"compile_exps"{Name="compile_exps",Thy="clos_to_bvl"};

val _ = temp_overload_on ("kcompile", ``clos_known$compile``)

(* TODO: move? *)

val SUM_MAP_COUNT_LIST = Q.store_thm("SUM_MAP_COUNT_LIST",
  `!n k. SUM (MAP ($+ k) (COUNT_LIST n)) = (n * (2 * k + n - 1)) DIV 2`,
  Induct \\ rw [COUNT_LIST_def]
  \\ `!xs. MAP SUC xs = MAP ($+ 1) xs` by (Induct \\ rw [])
  \\ pop_assum (qspec_then `COUNT_LIST n` SUBST1_TAC)
  \\ pop_assum (qspec_then `k + 1` mp_tac)
  \\ simp [MAP_MAP_o, o_DEF]
  \\ `$+ (k + 1) = \x. k + (x + 1)` by fs [FUN_EQ_THM]
  \\ pop_assum SUBST1_TAC \\ rw [ADD1]
  \\ fs [LEFT_ADD_DISTRIB, RIGHT_ADD_DISTRIB]
  \\ metis_tac [ADD_DIV_ADD_DIV, MULT_COMM, DECIDE ``0n < 2``]);

val SUM_COUNT_LIST = save_thm("SUM_COUNT_LIST",
  SUM_MAP_COUNT_LIST |> Q.SPECL [`n`,`0`] |> SIMP_RULE (srw_ss()) []);

val union_insert_LN = Q.store_thm("union_insert_LN",
  `∀x y t2. union (insert x y LN) t2 = insert x y t2`,
  recInduct insert_ind
  \\ rw[]
  \\ rw[Once insert_def]
  \\ rw[Once insert_def,SimpRHS]
  \\ rw[union_def]);

val fromAList_append = Q.store_thm("fromAList_append",
  `∀l1 l2. fromAList (l1 ++ l2) = union (fromAList l1) (fromAList l2)`,
  recInduct fromAList_ind
  \\ rw[fromAList_def]
  \\ rw[Once insert_union]
  \\ rw[union_assoc]
  \\ AP_THM_TAC
  \\ AP_TERM_TAC
  \\ rw[union_insert_LN]);

val SUBMAP_FLOOKUP_EQN = Q.store_thm("SUBMAP_FLOOKUP_EQN",
  `f ⊑ g ⇔ (∀x y. FLOOKUP f x = SOME y ⇒ FLOOKUP g x = SOME y)`,
  rw[SUBMAP_DEF,FLOOKUP_DEF] \\ METIS_TAC[]);

val SUBMAP_mono_FUPDATE_LIST = Q.store_thm("SUBMAP_mono_FUPDATE_LIST",
  `∀ls f g.
   DRESTRICT f (COMPL (set (MAP FST ls))) ⊑
   DRESTRICT g (COMPL (set (MAP FST ls)))
   ⇒ f |++ ls ⊑ g |++ ls`,
  Induct \\ rw[FUPDATE_LIST_THM, DRESTRICT_UNIV]
  \\ first_x_assum MATCH_MP_TAC
  \\ Cases_on`h`
  \\ fs[SUBMAP_FLOOKUP_EQN]
  \\ rw[] \\ fs[FLOOKUP_DRESTRICT, FLOOKUP_UPDATE]
  \\ rw[] \\ fs[]
  \\ METIS_TAC[]);

val MEM_ALOOKUP = store_thm("MEM_ALOOKUP",
  ``!xs x v.
      ALL_DISTINCT (MAP FST xs) ==>
      (MEM (x,v) xs <=> ALOOKUP xs x = SOME v)``,
  Induct \\ fs [FORALL_PROD] \\ rw []
  \\ res_tac \\ eq_tac \\ rw [] \\ rfs []
  \\ imp_res_tac ALOOKUP_MEM
  \\ fs [MEM_MAP,FORALL_PROD] \\ rfs []);

val ARITH_TAC = intLib.ARITH_TAC;

val drop_lupdate = Q.store_thm ("drop_lupdate",
  `!n x m l. n ≤ m ⇒ DROP n (LUPDATE x m l) = LUPDATE x (m - n) (DROP n l)`,
  rw [LIST_EQ_REWRITE, EL_DROP, EL_LUPDATE] >>
  rw [] >>
  fs []);

val SUM_REPLICATE = Q.store_thm("SUM_REPLICATE",
  `∀n m. SUM (REPLICATE n m) = n * m`,
  Induct \\ simp[REPLICATE,ADD1]);

val EVERY2_GENLIST = LIST_REL_GENLIST |> EQ_IMP_RULE |> snd |> Q.GEN`l`

val EVERY_ZIP_GENLIST = Q.prove(
  `!xs.
      (!i. i < LENGTH xs ==> P (EL i xs,f i)) ==>
      EVERY P (ZIP (xs,GENLIST f (LENGTH xs)))`,
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

val IS_SUBLIST_MEM = Q.prove(`
  ∀ls ls' x.
  MEM x ls ∧ IS_SUBLIST ls' ls ⇒
  MEM x ls'`,
  Induct>>Induct_on`ls'`>>rw[IS_SUBLIST]>>
  metis_tac[MEM,IS_PREFIX_IS_SUBLIST])

val IS_SUBLIST_APPEND1 = Q.prove(`
  ∀A B C.
  IS_SUBLIST A C ⇒
  IS_SUBLIST (A++B) C`,
  rw[]>>match_mp_tac (snd(EQ_IMP_RULE (SPEC_ALL IS_SUBLIST_APPEND)))>>
  fs[IS_SUBLIST_APPEND]>>
  metis_tac[APPEND_ASSOC])

val IS_SUBLIST_APPEND2 = Q.prove(`
  ∀A B C.
  IS_SUBLIST B C ⇒
  IS_SUBLIST (A++B) C`,
  Induct_on`A`>>Induct_on`B`>>Induct_on`C`>>fs[IS_SUBLIST])

val IS_SUBLIST_REFL = Q.prove(`
  ∀ls.
  IS_SUBLIST ls ls`,
  Induct>>fs[IS_SUBLIST])

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
  ONCE_REWRITE_TAC [GSYM APPEND_ASSOC]>>
  fs[EL_APPEND2,LENGTH_TAKE])

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

val sum_genlist_triangle_help = Q.prove (
  `!x. SUM (GENLIST (\y. y) (x+1)) = x * (x + 1) DIV 2`,
  Induct >>
  fs [GENLIST, SUM_SNOC, GSYM ADD1] >>
  simp [ADD1] >>
  ARITH_TAC);

val sum_genlist_triangle = Q.prove (
  `!x. SUM (GENLIST (\y. y) x) = x * (x - 1) DIV 2`,
  rw [] >>
  mp_tac (Q.SPEC `x-1` sum_genlist_triangle_help) >>
  Cases_on `x = 0` >>
  simp []);

val triangle_table_size = Q.prove (
  `!max f. LENGTH (FLAT (GENLIST (\x. (GENLIST (\y. f x y) x)) max)) =
    max * (max -1) DIV 2`,
  rw [LENGTH_FLAT, MAP_GENLIST, combinTheory.o_DEF, sum_genlist_triangle]);

val tri_lemma = Q.prove (
  `!tot max_app.
    tot < max_app ⇒
    tot + tot * (tot − 1) DIV 2 < max_app + (max_app − 1) * (max_app − 2) DIV 2`,
  Induct_on `max_app` >>
  rw [ADD1] >>
  `tot = max_app ∨ tot < max_app` by decide_tac >>
  rw [] >>
  res_tac >>
  `max_app + (max_app − 1) * (max_app − 2) DIV 2 < max_app + (max_app * (max_app − 1) DIV 2 + 1)`
  suffices_by decide_tac >>
  simp [] >>
  rpt (pop_assum kall_tac) >>
  Induct_on `max_app` >>
  rw [ADD1] >>
  ARITH_TAC);

val triangle_div_lemma = Q.prove (
  `!max_app n tot.
    tot < max_app ∧ n < tot
    ⇒
    n + tot * (tot − 1) DIV 2 < max_app * (max_app − 1) DIV 2`,
  rw [] >>
  `(tot - 1) + (tot * (tot − 1) DIV 2) < max_app * (max_app − 1) DIV 2`
  suffices_by decide_tac >>
  `((max_app - 1) - 1) + ((max_app - 1) * ((max_app - 1) − 1) DIV 2) < max_app * (max_app − 1) DIV 2`
  suffices_by (
    rw [] >>
    `tot + tot * (tot − 1) DIV 2 < max_app + (max_app − 1) * (max_app − 2) DIV 2`
    suffices_by rw [] >>
    simp [tri_lemma]) >>
  Cases_on `max_app` >>
  fs [] >>
  Cases_on `tot` >>
  fs [ADD1] >>
  Cases_on `n'` >>
  fs [ADD1] >>
  ARITH_TAC);

val triangle_el = Q.prove (
  `!n tot max_app stuff f g.
    n < tot ∧ tot < max_app
    ⇒
    EL (n + tot * (tot − 1) DIV 2)
      (FLAT
         (GENLIST
            (λtot.
               GENLIST
                 (λprev. f tot prev) tot)
            max_app) ++
       stuff) =
    f tot n`,
  Induct_on `max_app` >>
  rw [GENLIST, FLAT_SNOC] >>
  `tot = max_app ∨ tot < max_app` by decide_tac >>
  rw []
  >- simp [triangle_table_size, EL_APPEND_EQN] >>
  res_tac >>
  fs [] >>
  metis_tac [APPEND_ASSOC]);

val triangle_el_no_suff = Q.prove (
  `!n tot max_app f g.
    n < tot ∧ tot < max_app
    ⇒
    EL (n + tot * (tot − 1) DIV 2)
      (FLAT
         (GENLIST
            (λtot.
               GENLIST
                 (λprev. f tot prev) tot)
            max_app)) =
    f tot n`,
  metis_tac [triangle_el, APPEND_NIL]);

val if_expand = Q.prove (
  `!w x y z. (if x then y else z) = w ⇔ x ∧ y = w ∨ ~x ∧ z = w`,
  metis_tac []);

val take_drop_lemma = Q.prove (
  `!rem_args arg_list.
   LENGTH arg_list > rem_args
   ⇒
   TAKE (rem_args + 1) (DROP (LENGTH arg_list − (rem_args + 1)) (arg_list ++ stuff)) =
   DROP (LENGTH arg_list − (rem_args + 1)) arg_list`,
  Induct_on `arg_list` >>fs[ADD1]>>rw[]>>
  Cases_on`rem_args = LENGTH arg_list`>>fs[TAKE_LENGTH_APPEND])

val ETA2_THM = Q.prove (
  `(\x y. f a b c x y) = f a b c`,
  srw_tac[][FUN_EQ_THM]);

val p_genlist = Q.prove (
  `EL k exps_ps = ((n',e),p) ∧
   MAP SND exps_ps = GENLIST (λn. loc + (num_stubs max_app) + 2*n) (LENGTH exps_ps) ∧
   k < LENGTH exps_ps
   ⇒
   p = EL k (GENLIST (λn. loc + (num_stubs max_app) + 2*n) (LENGTH exps_ps))`,
  srw_tac[][] >>
  `EL k (MAP SND exps_ps) = EL k (GENLIST (λn. loc + (num_stubs max_app) + 2*n) (LENGTH exps_ps))` by metis_tac [] >>
  rev_full_simp_tac(srw_ss())[EL_MAP]);

val list_CASE_same = Q.store_thm("list_CASE_same",
  `list_CASE ls (P []) (λx y. P (x::y)) = P ls`,
  Cases_on`ls` \\ simp[]);

val with_same_clock = Q.store_thm("with_same_clock[simp]",
  `(st:('a,'b) bvlSem$state) with clock := st.clock = st`,
  rw[bvlSemTheory.state_component_equality]);

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

val evaluate_genlist_prev_args1_simpl = Q.prove (
  `!prev_args x y tag p n cl a st.
    evaluate (REVERSE (GENLIST (λprev_arg. Op El [Op (Const (&(prev_arg + 3))) []; Var 3]) (LENGTH prev_args)),
           [x;y;a; Block tag (p::n::cl::prev_args)],
           st)
    =
    (Rval (REVERSE prev_args),st)`,
  srw_tac[][] >>
  (Q.SPECL_THEN [`prev_args`, `[p;n;cl]`, `[x;y;a]`]assume_tac evaluate_genlist_prev_args) >>
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

val evaluate_partial_app_fn_location_code = Q.prove (
  `!max_app n total_args st args tag ptr x fvs.
     partial_app_fn_location max_app total_args n ∈ domain st.code ∧
     n < total_args ∧ total_args < max_app ⇒
     evaluate
       ([partial_app_fn_location_code max_app
               (Op El [Op (Const 1) []; Var (LENGTH args + 1)])
               (Op (Const (&n)) [])],
        (x::(args++[Block tag (ptr::Number(&total_args)::fvs)])),
        st)
     =
     (Rval [Number (&(total_args * (total_args - 1) DIV 2 + n))], st)`,
  rw [partial_app_fn_location_code_def, evaluate_def, do_app_def, EL_CONS,
      el_append2, PRE_SUB1, partial_app_fn_location_def] >>
  rw [integerTheory.INT_ADD, integerTheory.INT_MUL, integerTheory.INT_DIV,
      integerTheory.INT_SUB]);

val global_table_def = Define `
  global_table max_app =
    Block tuple_tag
      (FLAT (GENLIST (\tot. GENLIST
        (\prev. CodePtr (partial_app_fn_location max_app tot prev)) tot) max_app))`;

val evaluate_generic_app1 = Q.prove (
  `!n args st total_args l fvs cl.
    partial_app_fn_location max_app total_args n ∈ domain st.code ∧
    n < total_args ∧
    total_args < max_app ∧
    n + 1 = LENGTH args ∧
    get_global 0 st.globals = SOME (SOME (global_table max_app)) ∧
    cl = Block closure_tag (CodePtr l :: Number (&total_args) :: fvs)
    ⇒
    evaluate ([generate_generic_app max_app n], args++[cl], st) =
      if st.clock < n then
        (Rerr(Rabort Rtimeout_error), st with clock := 0)
      else
        (Rval [Block partial_app_tag (CodePtr (partial_app_fn_location max_app total_args n) ::
                                      Number (&(total_args - (n + 1))) ::
                                      cl::
                                      args)],
         dec_clock n st)`,
  srw_tac[][generate_generic_app_def] >>
  srw_tac[][evaluate_def, do_app_def] >>
  full_simp_tac (srw_ss() ++ ARITH_ss) [el_append2] >>
  `((&total_args):int − &(n+1) >= 0)` by intLib.ARITH_TAC >>
  srw_tac[][] >>
  TRY (rfs [] >> NO_TAC) >>
  rev_full_simp_tac(srw_ss())[evaluate_mk_tick, evaluate_def, do_app_def] >>
  full_simp_tac (srw_ss() ++ ARITH_ss) [el_append2] >>
  srw_tac[][DECIDE ``x + 2 = SUC (SUC x)``, el_append2_lemma, evaluate_APPEND] >>
  srw_tac [ARITH_ss] [ADD1, evaluate_genlist_vars_rev, evaluate_def] >>
  rw [LENGTH_GENLIST, evaluate_def, do_app_def, evaluate_APPEND, el_append2] >>
  TRY (fs [dec_clock_def, LESS_OR_EQ]) >>
  simp [evaluate_partial_app_fn_location_code, global_table_def] >>
  simp [triangle_table_size, partial_app_fn_location_def, triangle_el_no_suff,
        triangle_div_lemma] >>
  srw_tac[][evaluate_def, do_app_def, int_arithTheory.INT_NUM_SUB, el_append2, TAKE_LENGTH_APPEND] >>
  CCONTR_TAC >>
  intLib.ARITH_TAC);

val evaluate_generic_app2 = Q.prove (
  `!n args st rem_args prev_args l clo cl.
    partial_app_fn_location max_app (rem_args + LENGTH prev_args) (n + LENGTH prev_args) ∈ domain st.code ∧
    n < rem_args ∧
    n + 1 = LENGTH args ∧
    LENGTH prev_args > 0 ∧
    rem_args + LENGTH prev_args < max_app ∧
    get_global 0 st.globals = SOME (SOME (global_table max_app)) ∧
    cl = Block partial_app_tag (CodePtr l :: Number (&rem_args) :: clo :: prev_args)
    ⇒
    evaluate ([generate_generic_app max_app n], args++[cl], st) =
      if st.clock < n then
        (Rerr(Rabort Rtimeout_error), st with clock := 0)
      else
        (Rval [Block partial_app_tag (CodePtr (partial_app_fn_location max_app (rem_args + LENGTH prev_args) (n + LENGTH prev_args)) ::
                                      Number (&rem_args - &(n+1)) ::
                                      clo ::
                                      args ++
                                      prev_args)],
         dec_clock n st)`,
  srw_tac[][generate_generic_app_def, mk_const_def] >>
  srw_tac[][evaluate_def, do_app_def] >>
  full_simp_tac (srw_ss() ++ ARITH_ss) [] >>
  `~(&rem_args − &(n+1):int < 0)` by intLib.ARITH_TAC >>
  srw_tac[][el_append2] >>
  TRY (fs [dec_clock_def, LESS_OR_EQ] >> NO_TAC) >>
  rev_full_simp_tac(srw_ss())[evaluate_mk_tick] >>
  full_simp_tac (srw_ss()++ARITH_ss) [] >>
  srw_tac[][evaluate_def, do_app_def] >>
  srw_tac[][DECIDE ``x + 2 = SUC (SUC x)``, el_append2_lemma, evaluate_APPEND] >>
  srw_tac[][ADD1] >>
  full_simp_tac(srw_ss())[] >>
  TRY (fs [dec_clock_def, LESS_OR_EQ] >> NO_TAC) >>
  fs [] >>
  srw_tac [ARITH_ss] [evaluate_genlist_vars_rev, EL_CONS, PRE_SUB1, el_append2] >>
  simp [evaluate_def, do_app_def] >>
  srw_tac [ARITH_ss] [EL_CONS, PRE_SUB1, el_append2] >>
  simp [dec_clock_def] >>
  `&rem_args − &LENGTH args + &(n + (LENGTH prev_args + 1)):int = &(rem_args + LENGTH prev_args)` by intLib.ARITH_TAC >>
  fs [partial_app_fn_location_code_def, global_table_def] >>
  simp [evaluate_APPEND, REVERSE_APPEND, TAKE_LENGTH_APPEND, LENGTH_GENLIST, evaluate_def, do_app_def, mk_label_def] >>
  simp [integerTheory.INT_ADD, integerTheory.INT_MUL, integerTheory.INT_DIV, integerTheory.INT_SUB] >>
  rw [REVERSE_APPEND, ADD1] >>
  rw [] >>
  fs [ADD1]
  >- intLib.ARITH_TAC
  >- intLib.ARITH_TAC
  >- (
    REWRITE_TAC [ADD_ASSOC, triangle_el_no_suff] >>
    `n + LENGTH prev_args < rem_args + LENGTH prev_args` by decide_tac >>
    `rem_args + LENGTH prev_args < max_app` by decide_tac >>
    REWRITE_TAC [ADD_ASSOC] >>
    simp [triangle_el_no_suff, triangle_div_lemma])
  >- (
    fs [triangle_table_size] >>
    pop_assum mp_tac >>
    REWRITE_TAC [ADD_ASSOC, triangle_el_no_suff] >>
    `n + LENGTH prev_args < rem_args + LENGTH prev_args` by decide_tac >>
    `rem_args + LENGTH prev_args < max_app` by decide_tac >>
    REWRITE_TAC [ADD_ASSOC] >>
    simp [triangle_div_lemma]));

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
    partial_app_fn_location max_app total_args (LENGTH prev_args + (LENGTH args - 1)) ∈ domain st.code ∧
    total_args < max_app ∧
    LENGTH args < (total_args + 1) - LENGTH prev_args ∧
    LENGTH args ≠ 0 ∧
    get_global 0 st.globals = SOME (SOME (global_table max_app)) ∧
    unpack_closure cl (prev_args, total_args, sub_cl)
    ⇒
    evaluate ([generate_generic_app max_app (LENGTH args - 1)], args++[cl], st) =
      if st.clock < LENGTH args - 1 then
        (Rerr(Rabort Rtimeout_error), st with clock := 0)
      else
        (Rval [Block partial_app_tag (CodePtr (partial_app_fn_location max_app total_args (LENGTH prev_args + (LENGTH args - 1))) ::
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
      `LENGTH args <> 0` by simp[] >>
      full_simp_tac(std_ss++ARITH_ss)[])
  >- (qspecl_then [`LENGTH args - 1`, `args`, `st`, `Num rem_args`, `prev_args`] mp_tac evaluate_generic_app2 >>
      full_simp_tac (srw_ss()++ARITH_ss) [] >>
      srw_tac [ARITH_ss] [] >>
      `LENGTH args <> 0` by simp [] \\ full_simp_tac (std_ss++ARITH_ss)[] >>
      Cases_on `prev_args` >>
      full_simp_tac(srw_ss())[] >>
      srw_tac[][] >>
      rfs [] >>
      `&Num rem_args = rem_args` by intLib.ARITH_TAC >>
      full_simp_tac(srw_ss())[] >>
      srw_tac[][int_arithTheory.INT_NUM_SUB] >>
      `LENGTH args <> 0` by simp [] \\ full_simp_tac (std_ss++ARITH_ss)[]));

val evaluate_generic_app_full = Q.prove (
  `!n args st rem_args vs l tag exp clo.
    lookup l st.code = SOME (rem_args + 2, exp) ∧
    n + 1 = LENGTH args ∧
    n > rem_args ∧
    rem_args < max_app
    ⇒
    evaluate ([generate_generic_app max_app n], args++[Block tag (CodePtr l :: Number (&rem_args) :: vs)], st) =
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
  `(&rem_args − &(LENGTH args):int < 0)` by intLib.ARITH_TAC >>
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
    bvlSem$evaluate
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
    lookup (generic_app_fn_location (LENGTH args' - 1)) s.code =
      SOME (LENGTH args' + 1, generate_generic_app max_app (LENGTH args' - 1)) ∧
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
  srw_tac[][Once mk_cl_call_def, evaluate_def, do_app_def, do_eq_def, generic_app_fn_location_def] >>
  full_simp_tac(srw_ss())[ADD1] >>
  Cases_on `n = &(LENGTH args − 1)` >>
  srw_tac[][evaluate_APPEND, evaluate_def, do_app_def, do_eq_def, find_code_def, FRONT_APPEND] >>
  simp [] >>
  imp_res_tac bvlPropsTheory.evaluate_IMP_LENGTH >>
  rev_full_simp_tac (srw_ss()++ARITH_ss) [] >>
  `LENGTH args <> 0` by simp[] >>
  `LENGTH args' - 1 + 1 = LENGTH args'` by decide_tac >>
  TRY(fs[] \\ NO_TAC) \\
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
  `LENGTH prev_args <> 0` by simp[] >>
  full_simp_tac (srw_ss()++ARITH_ss) [el_append2, evaluate_APPEND] >>
  `LENGTH prev_args <> 0` by simp[] >>
  full_simp_tac (std_ss++ARITH_ss) [ADD1] >>
  srw_tac[][evaluate_def] >>
  qabbrev_tac `cl = Block tag (l'::num::Block tag' (CodePtr l::num_args'::fvs):: prev_args)` >>
  qspecl_then [`1`, `Block tag' (CodePtr l::num_args'::fvs)::(args' ++ [cl])`,
                       `LENGTH (args')`, `st with code := code`] assume_tac evaluate_genlist_vars >>
  full_simp_tac (srw_ss()++ARITH_ss) [ADD1] >>
  `LENGTH prev_args <> 0` by simp[] >>
  full_simp_tac (std_ss++ARITH_ss) [ADD1,EL_LENGTH_APPEND] >>
  srw_tac[][evaluate_genlist_prev_args1_no_rev, Abbr `cl`, evaluate_def, do_app_def, find_code_def] >>
  full_simp_tac (srw_ss()++ARITH_ss) [ADD1,EL_LENGTH_APPEND] >>
  srw_tac[][evaluate_genlist_prev_args1_no_rev, evaluate_def, do_app_def, find_code_def] >>
  srw_tac[][FRONT_APPEND, TAKE_LENGTH_APPEND, bvlSemTheory.state_component_equality] >> fs[]);

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
  closure_code_installed max_app code exps_ps (env:closSem$v list) =
    EVERY (\((n,exp),p).
      n ≤ max_app ∧
      n ≠ 0 ∧
      ?aux c aux1.
        (compile_exps max_app [exp] aux = ([c],aux1)) /\
        (lookup p code = SOME (n+1,SND (code_for_recc_case (LENGTH env + LENGTH exps_ps) n c))) /\
        code_installed aux1 code) exps_ps`

val (cl_rel_rules,cl_rel_ind,cl_rel_cases) = Hol_reln `
  ( num_args ≤ max_app ∧
    num_args ≠ 0 ∧
    every_Fn_SOME [x] ∧
    every_Fn_vs_SOME [x] ∧
    (compile_exps max_app [x] aux = ([c],aux1)) /\
    code_installed aux1 code /\
    (lookup (p + (num_stubs max_app)) code =
      SOME (num_args + 1:num,Let (GENLIST Var num_args++free_let (Var num_args) (LENGTH env)) c))
   ⇒
   cl_rel max_app fs refs code
          (env,ys)
          (Closure (SOME p) [] env num_args x)
          (Block closure_tag (CodePtr (p + (num_stubs max_app)) :: Number (&(num_args-1)) :: ys))) ∧
  ( num_args ≤ max_app ∧
    num_args ≠ 0 ∧
    every_Fn_SOME [x] ∧
    every_Fn_vs_SOME [x] ∧
    compile_exps max_app [x] aux = ([c],aux1) /\
    code_installed aux1 code /\
    lookup (p + (num_stubs max_app)) code =
      SOME (num_args + 1:num,Let (GENLIST Var (num_args+1)++free_let (Var num_args) (LENGTH env)) c)
    ⇒
    cl_rel max_app fs refs code (env,ys)
           (Recclosure (SOME p) [] env [(num_args, x)] 0)
           (Block closure_tag (CodePtr (p + (num_stubs max_app)) :: Number (&(num_args-1)) :: ys)))
    /\
    ((exps = MAP FST exps_ps) /\
     (ps = MAP SND exps_ps) /\ (ps = GENLIST (\n. loc + (num_stubs max_app) + 2*n) (LENGTH exps_ps)) /\
     (rs = MAP (\((n,e),p). Block closure_tag [CodePtr p; Number (&(n-1)); RefPtr r]) exps_ps) /\
     ~(r IN fs) /\
     (FLOOKUP refs r = SOME (ValueArray (rs ++ ys))) /\
     1 < LENGTH exps /\ k < LENGTH exps /\
     every_Fn_SOME (MAP SND exps) ∧
     every_Fn_vs_SOME (MAP SND exps) ∧
     closure_code_installed max_app code exps_ps env ==>
     cl_rel max_app fs refs code (env,ys) (Recclosure (SOME loc) [] env exps k) (EL k rs))`;

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
  (v_rel max_app f refs code (Number n) (Number n))
  /\
  (v_rel max_app f refs code (Word64 w) (Word64 w))
  /\
  (EVERY2 (v_rel max_app f refs code) xs (ys:bvlSem$v list) ==>
   v_rel max_app f refs code (Block t xs) (Block (clos_tag_shift t) ys))
  /\
  (FLOOKUP refs p = SOME (ByteArray T bs) /\ p ∉ FRANGE f ==>
   v_rel max_app f refs code (ByteVector bs) (RefPtr p))
  /\
  ((FLOOKUP f r1 = SOME r2) ==>
   v_rel max_app f refs code (RefPtr r1) (RefPtr r2))
  /\
  (EVERY2 (v_rel max_app f refs code) env fvs ∧
   cl_rel max_app (FRANGE f) refs code (env,fvs) cl (Block closure_tag (CodePtr p :: Number n :: ys))
   ⇒
   v_rel max_app f refs code cl (Block closure_tag (CodePtr p :: Number n :: ys)))
  /\
  (EVERY2 (v_rel max_app f refs code) env fvs /\
   EVERY2 (v_rel max_app f refs code) arg_env ys ∧
   arg_env ≠ [] ∧
   LENGTH arg_env < num_args ∧
   (lookup (partial_app_fn_location max_app (num_args - 1) (LENGTH ys - 1)) code =
     SOME (num_args - LENGTH arg_env + 1, generate_partial_app_closure_fn (num_args-1) (LENGTH ys - 1))) ∧
   add_args cl arg_env = SOME cl_app ∧
   get_num_args cl = SOME num_args ∧
   cl_rel max_app (FRANGE f) refs code (env,fvs) cl cl'
   ⇒
   v_rel max_app f refs code cl_app
                       (Block partial_app_tag
                              (CodePtr (partial_app_fn_location max_app (num_args - 1) (LENGTH ys - 1)) ::
                               Number (&(num_args - 1 - LENGTH arg_env)) :: cl' :: ys)))`;

val cl_rel_F = Q.prove (
  `~cl_rel max_app f refs code (env,ys) (Number i) cl ∧
   ~cl_rel max_app f refs code (env,ys) (Word64 w) cl ∧
   ~cl_rel max_app f refs code (env,ys) (RefPtr p) cl ∧
   ~cl_rel max_app f refs code (env,ys) (Block tag xs) cl ∧
   ~cl_rel max_app f refs code (env,ys) (ByteVector bs) cl`,
  srw_tac[][cl_rel_cases]);

val add_args_F = Q.prove (
  `!cl args p i tag xs.
   add_args cl args ≠ SOME (RefPtr p) ∧
   add_args cl args ≠ SOME (Number i) ∧
   add_args cl args ≠ SOME (Word64 w) ∧
   add_args cl args ≠ SOME (Block tag xs) ∧
   add_args cl args ≠ SOME (ByteVector bs)`,
  Cases_on `cl` >>
  srw_tac[][add_args_def]);

val v_rel_Unit = Q.store_thm("v_rel_Unit[simp]",
  `(v_rel max_app f refs code Unit y ⇔ (y = Unit)) ∧
   (v_rel max_app f refs code x Unit ⇔ (x = Unit))`,
  EVAL_TAC >> simp[v_rel_cases] >> EVAL_TAC >>
  srw_tac[][EQ_IMP_THM] >> full_simp_tac(srw_ss())[add_args_F,cl_rel_F] >>
  every_case_tac >> srw_tac[][] >> fsrw_tac[ARITH_ss][])

val v_rel_Boolv = Q.store_thm("v_rel_Boolv[simp]",
  `(v_rel max_app f refs code (Boolv b) y ⇔ (y = Boolv b)) ∧
   (v_rel max_app f refs code x (Boolv b) ⇔ (x = Boolv b))`,
  EVAL_TAC >> simp[v_rel_cases] >> EVAL_TAC >> simp[] >>
  srw_tac[][EQ_IMP_THM] >> full_simp_tac(srw_ss())[cl_rel_F,add_args_F] >>
  every_case_tac >> srw_tac[][] >> fsrw_tac[ARITH_ss][])

val v_rel_SIMP = LIST_CONJ
  [``v_rel max_app f refs code (RefPtr p) y``
   |> SIMP_CONV (srw_ss()) [v_rel_cases, cl_rel_F, add_args_F],
   ``v_rel max_app f refs code (Block tag xs) y``
   |> SIMP_CONV (srw_ss()) [v_rel_cases, cl_rel_F, add_args_F],
   ``v_rel max_app f refs code (ByteVector bs) y``
   |> SIMP_CONV (srw_ss()) [v_rel_cases, cl_rel_F, add_args_F],
   ``v_rel max_app f refs code (Number i) y``
   |> SIMP_CONV (srw_ss()) [v_rel_cases, cl_rel_F, add_args_F],
   ``v_rel max_app f refs code y (Number i)``
   |> SIMP_CONV (srw_ss()) [v_rel_cases, cl_rel_F, add_args_F],
   ``v_rel max_app f refs code (Word64 i) y``
   |> SIMP_CONV (srw_ss()) [v_rel_cases, cl_rel_F, add_args_F],
   ``v_rel max_app f refs code y (Word64 i)``
   |> SIMP_CONV (srw_ss()) [v_rel_cases, cl_rel_F, add_args_F],
   ``v_rel max_app f refs code (Closure loc args env num_args exp) y``
   |> SIMP_CONV (srw_ss()) [v_rel_cases, cl_rel_F, add_args_F],
   ``v_rel max_app f refs code (Recclosure loc args env exp k) y``
   |> SIMP_CONV (srw_ss()) [v_rel_cases, cl_rel_F, add_args_F]]
  |> curry save_thm "v_rel_SIMP"

val env_rel_def = Define `
  (env_rel max_app f refs code [] [] = T) /\
  (env_rel max_app f refs code [] ys = T) /\   (* bvl env allowed to contain extra stuff *)
  (env_rel max_app f refs code (x::xs) [] = F) /\
  (env_rel max_app f refs code (x::xs) (y::ys) <=>
     v_rel max_app f refs code x y /\ env_rel max_app f refs code xs ys)`;

val env_rel_APPEND = Q.prove(
  `!xs1 xs2.
      EVERY2 (v_rel max_app f1 refs code) xs1 xs2 /\
      env_rel max_app f1 refs code ys1 ys2 ==>
      env_rel max_app f1 refs code (xs1 ++ ys1) (xs2 ++ ys2)`,
  Induct \\ Cases_on `xs2` \\ full_simp_tac(srw_ss())[env_rel_def]);

val list_rel_IMP_env_rel = Q.prove(
  `!xs ys.
      LIST_REL (v_rel max_app f refs code) xs ys ==>
      env_rel max_app f refs code xs (ys ++ ts)`,
  Induct \\ Cases_on `ys` \\ full_simp_tac(srw_ss())[env_rel_def]
  \\ Cases_on `ts` \\ full_simp_tac(srw_ss())[env_rel_def]);

val env_rel_IMP_LENGTH = Q.prove(
  `!env1 env2.
      env_rel max_app f refs code env1 env2 ==>
      LENGTH env1 <= LENGTH env2`,
  Induct \\ Cases_on `env2` \\ full_simp_tac(srw_ss())[env_rel_def]);

val LESS_LENGTH_env_rel_IMP = Q.prove(
  `!env env2 n.
      n < LENGTH env /\ env_rel max_app f refs code env env2 ==>
      n < LENGTH env2 /\ v_rel max_app f refs code (EL n env) (EL n env2)`,
  Induct \\ full_simp_tac(srw_ss())[LENGTH] \\ REPEAT STRIP_TAC
  \\ Cases_on `env2` \\ full_simp_tac(srw_ss())[env_rel_def]
  \\ Cases_on `n` \\ full_simp_tac(srw_ss())[]);

val env_rel_IMP_EL =
  LESS_LENGTH_env_rel_IMP |> SPEC_ALL |> UNDISCH
  |> CONJUNCT2 |> DISCH_ALL |> GEN_ALL;

val extract_name_def = Define `
  extract_name e =
    case (some n. ?t1 t2 t3 x. e =
            Let t1 [Op t2 (Const (& n)) []; x] ((Var t3 1):closLang$exp)) of
    | NONE => 0:num
    | SOME n => n`;

val compile_inc_def = Define `
  compile_inc max_app (e,prog) =
    clos_to_bvl$compile_prog max_app ((extract_name e,0,e)::prog)`;

val nth_code_def = Define `
  nth_code t_co 0 = LN /\
  nth_code t_co (SUC n) =
    union (fromAList (SND (t_co 0))) (nth_code (shift_seq 1 t_co) n)`

val compile_oracle_inv_def = Define `
  compile_oracle_inv max_app s_code s_cc s_co t_code t_cc t_co ⇔
     s_cc = pure_cc (compile_inc max_app) t_cc ∧
     t_co = pure_co (compile_inc max_app) ∘ s_co ∧
     (!n cfg ps. t_co n = (cfg,ps) ==> ALL_DISTINCT (MAP FST ps)) /\
     (!n. DISJOINT (domain (union t_code (nth_code t_co n)))
            (set (MAP FST (SND (t_co n))))) /\
     !n cfg e ps.
       s_co n = (cfg,e,ps) ==>
       every_Fn_SOME [e] ∧ every_Fn_vs_SOME [e] /\
       EVERY (λp. every_Fn_SOME [SND (SND p)]) ps /\
       EVERY (λp. every_Fn_vs_SOME [SND (SND p)]) ps`;

val state_rel_def = Define `
  state_rel f (s:('c,'ffi) closSem$state) (t:('c,'ffi) bvlSem$state) <=>
    (s.ffi = t.ffi) /\
    LIST_REL (OPTREL (v_rel s.max_app f t.refs t.code)) s.globals (DROP num_added_globals t.globals) /\
    get_global 0 t.globals = SOME (SOME (global_table s.max_app)) ∧
    INJ ($' f) (FDOM f) (FRANGE f) /\
    (∀x y bs. FLOOKUP f x = SOME y ⇒ FLOOKUP t.refs y ≠ SOME (ByteArray T bs)) /\
    (FDOM f = FDOM s.refs) /\
    (FRANGE f SUBSET FDOM t.refs) /\
    (!n x. (FLOOKUP s.refs n = SOME x) ==>
           ?y m. (FLOOKUP f n = SOME m) /\
                 (FLOOKUP t.refs m = SOME y) /\
                 ref_rel (v_rel s.max_app f t.refs t.code) x y) /\
    (!n. n < s.max_app ⇒
         lookup (generic_app_fn_location n) t.code = SOME (n + 2, generate_generic_app s.max_app n)) ∧
    (!tot n. tot < s.max_app ∧ n < tot ⇒
      lookup (partial_app_fn_location s.max_app tot n) t.code = SOME (tot - n + 1, generate_partial_app_closure_fn tot n)) ∧
    compile_oracle_inv s.max_app s.code s.compile s.compile_oracle
                                 t.code t.compile t.compile_oracle ∧
    (!name arity c.
      (FLOOKUP s.code name = SOME (arity,c)) ==>
      ?aux1 c2 aux2.
        (compile_exps s.max_app [c] aux1 = ([c2],aux2)) /\
        (lookup (name + (num_stubs s.max_app)) t.code = SOME (arity,c2)) /\
        code_installed aux2 t.code)`;

val state_rel_globals = Q.prove(
  `state_rel f s t ⇒
    get_global 0 t.globals = SOME (SOME (global_table s.max_app)) ∧
    LIST_REL (OPTREL (v_rel s.max_app f t.refs t.code)) s.globals (DROP num_added_globals t.globals)`,
  srw_tac[][state_rel_def]);

val state_rel_clock = Q.store_thm ("state_rel_clock[simp]",
  `(!f s t. state_rel f s (t with clock := x) = state_rel f s t) ∧
   (!f s t. state_rel f (s with clock := x) t = state_rel f s t)`,
  srw_tac[][state_rel_def]);

val state_rel_refs_lookup = Q.store_thm("state_rel_refs_lookup",
  `state_rel f s1 s2 ∧
   FLOOKUP s1.refs p = SOME x ∧
   FLOOKUP f p = SOME p' ⇒
   ∃x'. FLOOKUP s2.refs p' = SOME x' ∧
     ref_rel (v_rel s1.max_app f s2.refs s2.code) x x'`,
  rw[state_rel_def]
  \\ res_tac \\ fs[] \\ rw[]);

val cl_rel_SUBMAP = Q.prove (
  `cl_rel max_app f1 refs1 code (env,ys) x y ∧
   f1 ⊆ f2 /\ FDIFF refs1 f1 SUBMAP FDIFF refs2 f2 ==>
   cl_rel max_app f2 refs2 code (env,ys) x y`,
  srw_tac[][cl_rel_cases]
  >- metis_tac []
  >- metis_tac []
  \\ DISJ2_TAC \\ Q.LIST_EXISTS_TAC [`exps_ps`,`r`] \\ full_simp_tac(srw_ss())[]
  \\ rev_full_simp_tac(srw_ss())[]
  \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ full_simp_tac(srw_ss())[] \\ STRIP_TAC
  \\ full_simp_tac(srw_ss())[FDIFF_def,SUBMAP_DEF,DRESTRICT_DEF,FLOOKUP_DEF]
  \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `r`) \\ full_simp_tac(srw_ss())[]);

val v_rel_SUBMAP = Q.prove(
  `!x y. v_rel max_app f1 refs1 code x y ==>
      f1 SUBMAP f2 /\ FDIFF refs1 (FRANGE f1) SUBMAP FDIFF refs2 (FRANGE f2) ==>
      v_rel max_app f2 refs2 code x y`,
  HO_MATCH_MP_TAC v_rel_ind \\ REPEAT STRIP_TAC
  \\ ONCE_REWRITE_TAC [v_rel_cases] \\ full_simp_tac(srw_ss())[]
  THEN1 (REPEAT (POP_ASSUM MP_TAC) \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ full_simp_tac(srw_ss())[])
  THEN1 ( fs[SUBMAP_DEF,FLOOKUP_DEF,FDIFF_def,DRESTRICT_DEF] )
  THEN1 (fs[SUBMAP_DEF,FLOOKUP_DEF] )
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

val env_rel_SUBMAP = Q.prove(
  `!env1 env2.
      env_rel max_app f1 refs1 code env1 env2 /\
      f1 SUBMAP f2 /\ FDIFF refs1 (FRANGE f1) SUBMAP FDIFF refs2 (FRANGE f2) ==>
      env_rel max_app f2 refs2 code env1 env2`,
  Induct \\ Cases_on `env2` \\ full_simp_tac(srw_ss())[env_rel_def]
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC v_rel_SUBMAP) |> GEN_ALL;

val cl_rel_NEW_REF = Q.prove (
  `!x y. cl_rel max_app f1 refs1 code (env,ys) x y ==> ~(r IN FDOM refs1) ==>
         cl_rel max_app f1 (refs1 |+ (r,t)) code (env,ys) x y`,
  srw_tac[][cl_rel_cases]
  >- metis_tac []
  >- metis_tac []
  \\ DISJ2_TAC \\ Q.LIST_EXISTS_TAC [`exps_ps`,`r'`] \\ full_simp_tac(srw_ss())[]
  \\ rev_full_simp_tac(srw_ss())[]
  \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[FDIFF_def,SUBMAP_DEF,DRESTRICT_DEF,FLOOKUP_DEF]
  \\ full_simp_tac(srw_ss())[FAPPLY_FUPDATE_THM] \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[]);

val v_rel_NEW_REF = Q.prove(
  `!x y. v_rel max_app f1 refs1 code x y ==> ~(r IN FDOM refs1) ==>
          v_rel max_app f1 (refs1 |+ (r,t)) code x y`,
  HO_MATCH_MP_TAC v_rel_ind \\ REPEAT STRIP_TAC
  \\ ONCE_REWRITE_TAC [v_rel_cases] \\ full_simp_tac(srw_ss())[]
  THEN1 (REPEAT (POP_ASSUM MP_TAC) \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ full_simp_tac(srw_ss())[])
  THEN1 (rw[FLOOKUP_UPDATE] \\ fs[FLOOKUP_DEF])
  THEN1 (imp_res_tac cl_rel_NEW_REF >>
         disj2_tac >>
         full_simp_tac(srw_ss())[ETA2_THM] >>
         metis_tac [])
  THEN1 (imp_res_tac cl_rel_NEW_REF >>
         disj2_tac >>
         full_simp_tac(srw_ss())[ETA2_THM] >>
         metis_tac [] ))
  |> SPEC_ALL |> MP_CANON;

val cl_rel_UPDATE_REF = Q.prove(
  `!x y. cl_rel max_app f1 refs1 code (env,ys) x y ==>
          (r IN f1) ==>
          cl_rel max_app f1 (refs1 |+ (r,t)) code (env,ys) x y`,
  srw_tac[][cl_rel_cases]
  >- metis_tac []
  >- metis_tac []
  \\ DISJ2_TAC \\ Q.LIST_EXISTS_TAC [`exps_ps`,`r'`] \\ full_simp_tac(srw_ss())[]
  \\ rev_full_simp_tac(srw_ss())[]
  \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[FDIFF_def,SUBMAP_DEF,DRESTRICT_DEF,FLOOKUP_DEF]
  \\ full_simp_tac(srw_ss())[FAPPLY_FUPDATE_THM] \\ SRW_TAC [] []
  \\ full_simp_tac(srw_ss())[FRANGE_DEF] \\ METIS_TAC []);

val v_rel_UPDATE_REF = Q.prove(
  `!x y. v_rel max_app f1 refs1 code x y ==>
          (r IN FRANGE f1) ==>
          v_rel max_app f1 (refs1 |+ (r,t)) code x y`,
  HO_MATCH_MP_TAC v_rel_ind \\ REPEAT STRIP_TAC
  \\ ONCE_REWRITE_TAC [v_rel_cases] \\ full_simp_tac(srw_ss())[]
  THEN1 (REPEAT (POP_ASSUM MP_TAC) \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ full_simp_tac(srw_ss())[])
  THEN1 ( rw[FLOOKUP_UPDATE] \\ fs[FLOOKUP_DEF] )
  THEN1 (imp_res_tac cl_rel_UPDATE_REF >>
         disj2_tac >>
         full_simp_tac(srw_ss())[ETA2_THM] >>
         metis_tac [])
  THEN1 (imp_res_tac cl_rel_UPDATE_REF >>
         disj2_tac >>
         full_simp_tac(srw_ss())[ETA2_THM] >>
         metis_tac [] ))
  |> SPEC_ALL |> MP_CANON;

val OPTREL_v_rel_NEW_REF = Q.prove(
  `OPTREL (v_rel max_app f1 refs1 code) x y /\ ~(r IN FDOM refs1) ==>
    OPTREL (v_rel max_app f1 (refs1 |+ (r,t)) code) x y`,
  Cases_on `x` \\ Cases_on `y` \\ full_simp_tac(srw_ss())[OPTREL_def,v_rel_NEW_REF]);

val OPTREL_v_rel_UPDATE_REF = Q.prove(
  `OPTREL (v_rel max_app f1 refs1 code) x y /\ r IN FRANGE f1 ==>
    OPTREL (v_rel max_app f1 (refs1 |+ (r,t)) code) x y`,
  Cases_on `x` \\ Cases_on `y` \\ full_simp_tac(srw_ss())[OPTREL_def,v_rel_UPDATE_REF]);

val env_rel_NEW_REF = Q.prove(
  `!x y.
      env_rel max_app f1 refs1 code x y /\ ~(r IN FDOM refs1) ==>
      env_rel max_app f1 (refs1 |+ (r,t)) code x y`,
  Induct \\ Cases_on `y` \\ full_simp_tac(srw_ss())[env_rel_def] \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC v_rel_NEW_REF \\ full_simp_tac(srw_ss())[]);

val cl_rel_NEW_F = Q.prove(
  `!x y.
      cl_rel max_app f2 t2.refs t2.code (env,ys) x y ==>
      ~(qq IN FDOM t2.refs) ==>
      cl_rel max_app (qq INSERT f2) t2.refs t2.code (env,ys) x y`,
  srw_tac[][cl_rel_cases]
  >- metis_tac []
  >- metis_tac []
  \\ DISJ2_TAC \\ Q.LIST_EXISTS_TAC [`exps_ps`,`r`] \\ full_simp_tac(srw_ss())[]
  \\ strip_tac >> full_simp_tac(srw_ss())[FLOOKUP_DEF])

val v_rel_NEW_F = Q.prove(
  `!x y.
      v_rel max_app f2 t2.refs t2.code x y ==>
      ~(pp IN FDOM f2) ==>
      ~(qq IN FDOM t2.refs) ==>
      v_rel max_app (f2 |+ (pp,qq)) t2.refs t2.code x y`,
  HO_MATCH_MP_TAC v_rel_ind \\ REPEAT STRIP_TAC
  \\ ONCE_REWRITE_TAC [v_rel_cases] \\ full_simp_tac(srw_ss())[]
  THEN1 (REPEAT (POP_ASSUM MP_TAC) \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ full_simp_tac(srw_ss())[])
  THEN1 ( fs[IN_FRANGE,FLOOKUP_DEF,DOMSUB_FAPPLY_THM] \\ metis_tac[] )
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

val OPTREL_v_rel_NEW_F = Q.prove(
  `OPTREL (v_rel max_app f2 t2.refs t2.code) x y ==>
    ~(pp IN FDOM f2) ==>
    ~(qq IN FDOM t2.refs) ==>
    OPTREL (v_rel max_app (f2 |+ (pp,qq)) t2.refs t2.code) x y`,
  Cases_on `x` \\ Cases_on `y` \\ full_simp_tac(srw_ss())[OPTREL_def]
  \\ METIS_TAC [v_rel_NEW_F]) |> MP_CANON;

val state_rel_UPDATE_REF = Q.store_thm("state_rel_UPDATE_REF",
  `state_rel f2 p1 t2 ∧
   FLOOKUP f2 dst = SOME r2 ∧
   FLOOKUP p1.refs dst = SOME v0 ∧
   ref_rel (v_rel p1.max_app f2 t2.refs t2.code) v v' ∧
   (∀bs. v' ≠ ByteArray T bs)
  ⇒
   state_rel f2 (p1 with refs := p1.refs |+ (dst,v))
     (t2 with refs := t2.refs |+ (r2,v'))`,
  rw[state_rel_def,FLOOKUP_UPDATE]
  >- (
    match_mp_tac(MP_CANON(GEN_ALL LIST_REL_mono)) \\
    ONCE_REWRITE_TAC[CONJ_COMM] >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    rpt strip_tac >>
    match_mp_tac OPTREL_v_rel_UPDATE_REF >>
    fs[IN_FRANGE_FLOOKUP]
    \\ asm_exists_tac \\ fs[] )
  >- (
    rw[] \\ spose_not_then strip_assume_tac
    \\ res_tac )
  >- (
    simp[EXTENSION]
    \\ fs[FLOOKUP_DEF]
    \\ metis_tac[] )
  >- ( fs[SUBSET_DEF] )
  >- (
    pop_assum mp_tac \\ rw[] \\ rw[]
    >- (
      Cases_on`v` \\ fs[ref_rel_def] \\
      match_mp_tac(MP_CANON(GEN_ALL LIST_REL_mono)) \\
      ONCE_REWRITE_TAC[CONJ_COMM] >>
      first_assum(match_exists_tac o concl) >> simp[] >>
      rpt strip_tac >>
      match_mp_tac v_rel_UPDATE_REF >>
      fs[IN_FRANGE_FLOOKUP]
      \\ asm_exists_tac \\ fs[] )
    \\ res_tac \\ fs[]
    \\ rw[] \\ fs[]
    >- (
      fs[INJ_DEF,FLOOKUP_DEF]
      \\ metis_tac[] )
    \\ Cases_on`x` \\ fs[ref_rel_def] \\ rw[] \\
    match_mp_tac(MP_CANON(GEN_ALL LIST_REL_mono)) \\
    ONCE_REWRITE_TAC[CONJ_COMM] >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    rpt strip_tac >>
    match_mp_tac v_rel_UPDATE_REF >>
    fs[IN_FRANGE_FLOOKUP]
    \\ asm_exists_tac \\ fs[] ));

val state_rel_NEW_REF = Q.store_thm("state_rel_NEW_REF",
  `state_rel f2 p1 t2 ∧ p ∉ FDOM t2.refs ⇒
   state_rel f2 p1 (t2 with refs := t2.refs |+ (p,v))`,
  rw[state_rel_def,FLOOKUP_UPDATE]
  >- (
    match_mp_tac(MP_CANON(GEN_ALL LIST_REL_mono)) \\
    ONCE_REWRITE_TAC[CONJ_COMM] >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    rpt strip_tac >>
    match_mp_tac OPTREL_v_rel_NEW_REF >>
    fs[IN_FRANGE_FLOOKUP])
  >- (
    rw[] \\ spose_not_then strip_assume_tac
    \\ res_tac
    \\ fs[SUBSET_DEF,IN_FRANGE_FLOOKUP,PULL_EXISTS]
    \\ metis_tac[])
  >- ( fs[SUBSET_DEF] )
  \\ res_tac \\ rw[]
  >- fs[FLOOKUP_DEF]
  \\ Cases_on`x` \\ fs[ref_rel_def] \\ rw[] \\
  match_mp_tac(MP_CANON(GEN_ALL LIST_REL_mono)) \\
  ONCE_REWRITE_TAC[CONJ_COMM] >>
  first_assum(match_exists_tac o concl) >> simp[] >>
  rpt strip_tac >>
  match_mp_tac v_rel_NEW_REF >>
  fs[IN_FRANGE_FLOOKUP]);

(* semantic functions respect relation *)

val v_to_list = Q.prove(
  `∀v l v'.
   v_to_list v = SOME l ∧
   v_rel max_app f r c v v'
   ⇒
   ∃l'. v_to_list v' = SOME l' ∧
        LIST_REL (v_rel max_app f r c) l l'`,
  ho_match_mp_tac closSemTheory.v_to_list_ind >>
  srw_tac[][v_rel_SIMP,closSemTheory.v_to_list_def,bvlSemTheory.v_to_list_def] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
  srw_tac[][bvlSemTheory.v_to_list_def] >> res_tac >> srw_tac[][]);

val not_isClos = Q.store_thm("not_isClos[simp]",
  `~isClos (if n < ^(closure_tag_def |> concl |> rand) then n else (n + 2)) ys`,
  EVAL_TAC \\ rw []);

val do_eq = Q.prove(
  `INJ ($' f) (FDOM f) (FRANGE f) ∧
   (∀x y bs. FLOOKUP f x = SOME y ⇒ FLOOKUP r y ≠ SOME (ByteArray T bs)) ⇒
    (∀x y x1 y1.
           v_rel max_app f r c x x1 ∧
           v_rel max_app f r c y y1 ⇒
           do_eq x y = do_eq r x1 y1) ∧
    (∀x y x1 y1.
           LIST_REL (v_rel max_app f r c) x x1 ∧
           LIST_REL (v_rel max_app f r c) y y1 ⇒
           do_eq_list x y = do_eq_list r x1 y1)`,
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
       fs [isClos_def,closure_tag_def,partial_app_tag_def] >>
       metis_tac [])
  >- full_simp_tac(srw_ss())[closSemTheory.do_eq_def]
  >- (res_tac >>
      srw_tac[][closSemTheory.do_eq_def] >>
      Cases_on `do_eq x y` >>
      full_simp_tac(srw_ss())[] >>
      qpat_x_assum `X = do_eq _ y'' y'''` (mp_tac o GSYM) >>
      srw_tac[][])
  >- full_simp_tac(srw_ss())[closSemTheory.do_eq_def]
  >- full_simp_tac(srw_ss())[closSemTheory.do_eq_def]);

val r = mk_var("r",``:num |-> 'a ref``);

val do_eq_sym = Q.prove(
  `(∀^r x y. do_eq r x y = do_eq r y x) ∧
   (∀^r x y. do_eq_list r x y = do_eq_list r y x)`,
  ho_match_mp_tac do_eq_ind >> simp[] >>
  conj_tac >- ( ntac 2 gen_tac >> Cases >> srw_tac[][] ) >>
  conj_tac >- METIS_TAC[] >>
  conj_tac >- METIS_TAC[] >>
  conj_tac >- ( rw[] \\ every_case_tac \\ fs[] \\ metis_tac[] ) \\
  conj_tac >- (
    rpt gen_tac >> strip_tac >>
    IF_CASES_TAC >> full_simp_tac(srw_ss())[] >>
    srw_tac[][] >> full_simp_tac(srw_ss())[] ) >>
  srw_tac[][] >> every_case_tac >> fs[]);

val do_eq_list_T_every = Q.store_thm("do_eq_list_T_every",
  `∀vs1 vs2. do_eq_list r vs1 vs2 = Eq_val T ⇔ LIST_REL (λv1 v2. do_eq r v1 v2 = Eq_val T) vs1 vs2`,
  Induct \\ simp[do_eq_def]
  \\ Cases_on`vs2`\\ simp[do_eq_def]
  \\ srw_tac[][]
  \\ every_case_tac \\  full_simp_tac(srw_ss())[]);

val list_to_v_v_rel = Q.store_thm("list_to_v_v_rel",
  `!xs ys.
     LIST_REL (v_rel app f refs code) xs ys ==>
       v_rel app f refs code (list_to_v xs) (list_to_v ys)`,
  Induct
  >- rw [LIST_REL_EL_EQN, v_rel_SIMP, closSemTheory.list_to_v_def, list_to_v_def]
  \\ rw [] \\ fs [v_rel_SIMP, closSemTheory.list_to_v_def, list_to_v_def]);

val do_app = Q.prove(
  `(do_app op xs s1 = Rval (v,s2)) /\
   state_rel f s1 t1 /\
   LIST_REL (v_rel s1.max_app f t1.refs t1.code) xs ys /\
   (* store updates need special treatment *)
   (op <> Ref) /\ (op <> Update) ∧
   (op ≠ RefArray) ∧ (∀f. op ≠ RefByte f) ∧ (op ≠ UpdateByte) ∧
   (∀s. op ≠ String s) ∧ (op ≠ FromListByte) ∧ op ≠ ConcatByteVec ∧
   (∀b. op ≠ CopyByte b) ∧
   (∀n. op ≠ (FFI n)) ==>
   ?w t2.
     (do_app (compile_op op) ys t1 = Rval (w,t2)) /\
     v_rel s1.max_app f t1.refs t1.code v w /\
     state_rel f s2 t2 /\
     (t1.refs = t2.refs) /\ (t1.code = t2.code)`,
  Cases_on `op = ListAppend`
  >-
   (rw []
    \\ fs [do_app_def, closSemTheory.do_app_def, case_eq_thms, PULL_EXISTS]
    \\ rw [] \\ fs [] \\ rw [] \\ fs []
    \\ imp_res_tac v_to_list \\ fs [] \\ rveq \\ rfs [] \\ rw []
    \\ match_mp_tac list_to_v_v_rel
    \\ fs [EVERY2_APPEND_suff])
  \\ Cases_on `?i. op = LessConstSmall i` THEN1
    (srw_tac[][closSemTheory.do_app_def] \\ fs [] \\ every_case_tac \\ fs []
     \\ fs[v_rel_SIMP] \\ rveq \\ fs [bvlSemTheory.do_app_def])
  \\ Cases_on `op = BoundsCheckBlock` THEN1
    (srw_tac[][closSemTheory.do_app_def] \\ fs [] \\ every_case_tac \\ fs []
     \\ fs[v_rel_SIMP] \\ rveq \\ fs [bvlSemTheory.do_app_def]
     \\ imp_res_tac LIST_REL_LENGTH \\ fs [])
  \\ Cases_on `∃b. op = BoundsCheckByte b` THEN1
    (srw_tac[][closSemTheory.do_app_def] \\ fs [] \\ every_case_tac \\ fs []
     \\ fs[v_rel_SIMP] \\ rveq \\ fs [bvlSemTheory.do_app_def]
     \\ imp_res_tac LIST_REL_LENGTH \\ fs [state_rel_def]
     \\ res_tac \\ fs [] \\ rveq \\ fs []
     \\ rw [] \\ res_tac \\ fs [])
  \\ Cases_on `op = BoundsCheckArray` THEN1
    (srw_tac[][closSemTheory.do_app_def] \\ fs [] \\ every_case_tac \\ fs []
     \\ fs[v_rel_SIMP] \\ rveq \\ fs [bvlSemTheory.do_app_def]
     \\ imp_res_tac LIST_REL_LENGTH \\ fs [state_rel_def]
     \\ res_tac \\ fs [] \\ rveq \\ fs []
     \\ rw [] \\ res_tac \\ fs []
     \\ imp_res_tac LIST_REL_LENGTH \\ fs [])
  \\ Cases_on `?i. op = EqualInt i` THEN1
    (srw_tac[][closSemTheory.do_app_def] \\ fs [] \\ every_case_tac \\ fs [])
  \\ Cases_on `op = Install` THEN1 fs[closSemTheory.do_app_def]
  \\ Cases_on `op = Equal` THEN1
   (srw_tac[][closSemTheory.do_app_def,bvlSemTheory.do_app_def,
                            bvlSemTheory.do_eq_def]
    \\ `?x1 x2 y1 y2. xs = [x1;x2] /\ ys = [y1;y2]` by
          (every_case_tac \\ fs [] \\ NO_TAC) \\ fs []
    \\ Cases_on `do_eq x1 x2` \\ fs [] \\ rveq
    \\ `INJ ($' f) (FDOM f) (FRANGE f) ∧
        (∀x y bs. FLOOKUP f x = SOME y ⇒ FLOOKUP t1.refs y ≠ SOME (ByteArray T bs))`
    by (fs [state_rel_def] \\ metis_tac[])
    \\ drule (do_eq |> UNDISCH |> CONJUNCT1 |> DISCH_ALL |> GEN_ALL)
    \\ disch_then drule
    \\ strip_tac
    \\ `do_eq t1.refs y1 y2 = Eq_val b` by metis_tac [] \\ fs []) >>
  Cases_on `?tag. op = Cons tag`
  >- (
    rw [closSemTheory.do_app_def] >>
    fs [] >>
    every_case_tac >>
    fs [] >>
    rw [do_app_def] >>
    fs [v_rel_SIMP] >>
    rw []) >>
  Cases_on `?tag. op = ConsExtend tag`
  >- (
    fs [closPropsTheory.do_app_cases_val] >>
    fs [] >>
    rw [do_app_def] >>
    fs [v_rel_SIMP] >>
    rw [] >>
    imp_res_tac LIST_REL_LENGTH
    >- intLib.ARITH_TAC >>
    irule EVERY2_APPEND_suff >>
    simp [] >>
    metis_tac [EVERY2_TAKE, EVERY2_DROP])
  >> Cases_on`op`>>fs[]>>srw_tac[][closSemTheory.do_app_def,bvlSemTheory.do_app_def,
                            bvlSemTheory.do_eq_def]
  >- (
    imp_res_tac state_rel_globals >>
    every_case_tac >>
    fs [get_global_def, num_added_globals_def] >>
    rw [] >>
    imp_res_tac LIST_REL_LENGTH
    >- fs [DROP_CONS_EL, ADD1] >>
    fs [LIST_REL_EL_EQN] >>
    rw [] >>
    first_x_assum drule >>
    simp [EL_DROP, optionTheory.OPTREL_def])
  >- (
    imp_res_tac state_rel_globals >>
    every_case_tac >>
    fs [get_global_def, num_added_globals_def] >>
    rw [] >>
    imp_res_tac LIST_REL_LENGTH
    >- fs [DROP_CONS_EL, ADD1] >>
    fs [LIST_REL_EL_EQN] >>
    rw [] >>
    first_x_assum drule >>
    simp [EL_DROP, optionTheory.OPTREL_def] >>
    full_simp_tac(srw_ss())[state_rel_def] >>
    rw []
    >- (
      fs [num_added_globals_def, drop_lupdate] >>
      MATCH_MP_TAC EVERY2_LUPDATE_same >>
      rev_full_simp_tac(srw_ss())[OPTREL_def] )
    >- fs [get_global_def, HD_LUPDATE]
    >- metis_tac [])
  >- (
    every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
    full_simp_tac(srw_ss())[state_rel_def,OPTREL_def] >>
    rw []
    >- (
      fs [num_added_globals_def, DROP_APPEND] >>
      irule EVERY2_APPEND_suff >>
      simp [optionTheory.OPTREL_def] >>
      fs [get_global_def] >>
      `1 - LENGTH t1.globals = 0` by decide_tac >>
      simp [])
    >- (
      fs [get_global_def] >>
      Cases_on `t1.globals` >>
      fs [])
    >- metis_tac[])
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
    Cases_on`xs`>>full_simp_tac(srw_ss())[v_rel_SIMP]>>
    Cases_on`h`>>full_simp_tac(srw_ss())[v_rel_SIMP]>>
    Cases_on`t`>>full_simp_tac(srw_ss())[v_rel_SIMP]>>
    Cases_on`h`>>full_simp_tac(srw_ss())[v_rel_SIMP]>>
    every_case_tac >> full_simp_tac(srw_ss())[v_rel_SIMP] >> srw_tac[][v_rel_SIMP] >>
    full_simp_tac(srw_ss())[state_rel_def] >> res_tac >> full_simp_tac(srw_ss())[v_rel_SIMP] >>
    srw_tac[][] >> full_simp_tac(srw_ss())[LIST_REL_EL_EQN] >>srw_tac[][]>>full_simp_tac(srw_ss())[] >>
    first_x_assum match_mp_tac >> intLib.COOPER_TAC)
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
  >- (
    Cases_on`xs`>>full_simp_tac(srw_ss())[v_rel_SIMP]>>
    Cases_on`t`>>full_simp_tac(srw_ss())[v_rel_SIMP]>>
    Cases_on`h`>>full_simp_tac(srw_ss())[v_rel_SIMP]>>
    Cases_on`t'`>>full_simp_tac(srw_ss())[v_rel_SIMP]>>
    Cases_on`h'`>>full_simp_tac(srw_ss())[v_rel_SIMP]>>
    every_case_tac >> full_simp_tac(srw_ss())[v_rel_SIMP] >> srw_tac[][v_rel_SIMP] >>
    full_simp_tac(srw_ss())[state_rel_def] >> res_tac >>
    full_simp_tac(srw_ss())[v_rel_SIMP] >>
    srw_tac[][] >> full_simp_tac(srw_ss())[LIST_REL_EL_EQN] >>
    srw_tac[][]>>full_simp_tac(srw_ss())[] >>
    first_x_assum match_mp_tac >> intLib.COOPER_TAC)
  \\ rpt (pop_assum mp_tac)
  \\ rpt (TOP_CASE_TAC \\ fs [])
  \\ full_simp_tac(srw_ss())[v_rel_SIMP] \\ srw_tac[][v_rel_SIMP]
  \\ full_simp_tac(srw_ss())[v_rel_SIMP] \\ srw_tac[][v_rel_SIMP]
  \\ CCONTR_TAC \\ fs []);

val v_case_eq_thms =
  LIST_CONJ [
    prove_case_eq_thm{nchotomy = closSemTheory.v_nchotomy, case_def = closSemTheory.v_case_def},
    prove_case_eq_thm{nchotomy = bvlSemTheory.v_nchotomy, case_def = bvlSemTheory.v_case_def}];

val do_app_err = Q.prove(
  `do_app op xs s1 = Rerr err ∧
   err ≠ Rabort Rtype_error ∧
   state_rel f s1 t1 ∧
   LIST_REL (v_rel s1.max_app f t1.refs t1.code) xs ys
   ⇒
   ∃e. do_app (compile_op op) ys t1 = Rerr e ∧
       exc_rel (v_rel s1.max_app f t1.refs t1.code) err e`,
  Cases_on `?i. op = EqualInt i` THEN1
    (srw_tac[][closSemTheory.do_app_def] \\ fs [] \\ every_case_tac \\ fs []) >>
  Cases_on `?tag. op = ConsExtend tag`
  >- (
    Cases_on `err` >>
    rw [closPropsTheory.do_app_cases_err] >>
    Cases_on `a` >>
    rw [closPropsTheory.do_app_cases_timeout] >>
    fs [closPropsTheory.do_app_cases_type_error] >>
    fs [closPropsTheory.do_app_cases_ffi_error] >> fs[])
  \\ Cases_on `?n. op = FFI n`
  >- (Cases_on `err`
      >> rw [closPropsTheory.do_app_cases_err]
      >- (PURE_FULL_CASE_TAC >> fs[])
      >> Cases_on `a`
      >> rw [closPropsTheory.do_app_cases_timeout]
      >> fs [closPropsTheory.do_app_cases_type_error]
      >> fs [closPropsTheory.do_app_cases_ffi_error] >> fs[]
      >> PURE_FULL_CASE_TAC >> fs[] >> rveq
      >> drule(GEN_ALL state_rel_refs_lookup) >> strip_tac
      >> simp[Once do_app_def] >> fs[v_rel_SIMP]
      >> first_x_assum drule >> disch_then drule
      >> strip_tac >> simp[]
      >> fs[ref_rel_simp]
      >> rfs[state_rel_def])
  \\ Cases_on`op`
  \\ srw_tac[][closSemTheory.do_app_def,bvlSemTheory.do_app_def]
  \\ TRY (fs[case_eq_thms,bool_case_eq,v_case_eq_thms] \\ NO_TAC)
  \\ spose_not_then strip_assume_tac \\ fs[]
  \\ rpt (pop_assum mp_tac)
  \\ rpt (PURE_CASE_TAC \\ fs []) \\ fs []
  \\ TRY(rpt strip_tac \\ fs[v_rel_cases] \\ fs[state_rel_def] \\ NO_TAC)
    );

(* correctness of implemented primitives *)

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

val s = ``s:('c,'ffi) bvlSem$state``

(* compiler correctness *)

val EXISTS_NOT_IN_refs = Q.prove(
  `?x. ~(x IN FDOM (t1:('c,'ffi) bvlSem$state).refs)`,
  METIS_TAC [NUM_NOT_IN_FDOM])

val lookup_vars_IMP2 = Q.prove(
  `!vs env xs env2.
      (lookup_vars vs env = SOME xs) /\
      env_rel max_app f refs code env env2 ==>
      ?ys. (!t1. (evaluate (MAP Var vs,env2,t1) = (Rval ys,t1))) /\
           EVERY2 (v_rel max_app f refs code) xs ys /\
           (LENGTH vs = LENGTH xs)`,
  Induct \\ full_simp_tac(srw_ss())[lookup_vars_def,evaluate_def]
  \\ REPEAT STRIP_TAC
  \\ Cases_on `lookup_vars vs env` \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
  \\ ONCE_REWRITE_TAC [evaluate_CONS]
  \\ full_simp_tac(srw_ss())[evaluate_def]
  \\ RES_TAC \\ IMP_RES_TAC LESS_LENGTH_env_rel_IMP \\ full_simp_tac(srw_ss())[])
  |> INST_TYPE[alpha|->``:'c``,beta|->``:'ffi``];

val lookup_vars_IMP = Q.prove(
  `!vs env xs env2.
      (lookup_vars vs env = SOME xs) /\
      env_rel max_app f refs code env env2 ==>
      ?ys. (evaluate (MAP Var vs,env2,t1) = (Rval ys,t1:('c, 'ffi) bvlSem$state)) /\
           EVERY2 (v_rel max_app f refs code) xs ys /\
           (LENGTH vs = LENGTH xs)`,
  (* TODO: metis_tac is not VALID here *)
    PROVE_TAC[lookup_vars_IMP2]);

val compile_exps_IMP_code_installed = Q.prove(
  `(compile_exps max_app xs aux = (c,aux1)) /\
    code_installed aux1 code ==>
    code_installed aux code`,
  REPEAT STRIP_TAC
  \\ MP_TAC (SPEC_ALL compile_exps_acc) \\ full_simp_tac(srw_ss())[LET_DEF]
  \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[code_installed_def]);

val compile_exps_LIST_IMP_compile_exps_EL = Q.prove(
  `!exps aux1 c7 aux7 i n8 n4 aux5 num_args e.
      EL i exps = (num_args, e) ∧
      (compile_exps max_app (MAP SND exps) aux1 = (c7,aux7)) /\ i < LENGTH exps /\
      (build_aux n8 (MAP2 (code_for_recc_case k) (MAP FST exps) c7) aux7 = (n4,aux5)) /\
      code_installed aux5 t1.code ==>
      ?aux c aux1'.
        compile_exps max_app [e] aux = ([c],aux1') /\
        lookup (n8 + 2*i) t1.code = SOME (num_args + 1,SND (code_for_recc_case k num_args c)) /\
        code_installed aux1' t1.code`,
  HO_MATCH_MP_TAC SNOC_INDUCT \\ full_simp_tac(srw_ss())[] \\ REPEAT STRIP_TAC
  \\ Cases_on `i = LENGTH exps` \\ full_simp_tac(srw_ss())[] THEN1
   (full_simp_tac(srw_ss())[SNOC_APPEND,EL_LENGTH_APPEND]
    \\ full_simp_tac(srw_ss())[GSYM SNOC_APPEND,compile_exps_SNOC]
    \\ fs[] \\ rpt (pairarg_tac \\ fs[])
    \\ qmatch_assum_rename_tac`_ = (c2,aux3)`
    \\ qmatch_assum_rename_tac`_ = (c1,aux2)`
    \\ SRW_TAC [] []
    \\ Q.LIST_EXISTS_TAC [`aux2`] \\ full_simp_tac(srw_ss())[]
    \\ IMP_RES_TAC compile_exps_SING \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[code_installed_def]
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
  \\ fs[] \\ rpt (pairarg_tac \\ fs[])
  \\ qmatch_assum_rename_tac`_ = (c2,aux3)`
  \\ qmatch_assum_rename_tac`_ = (c1,aux2)`
  \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`aux1`]) \\ full_simp_tac(srw_ss())[]
  \\ SRW_TAC [] [] \\ POP_ASSUM (MP_TAC o Q.SPECL [`i`,`n8`])
  \\ full_simp_tac(srw_ss())[] \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC compile_exps_SING \\ SRW_TAC [] []
  \\ imp_res_tac compile_exps_LENGTH
  \\ full_simp_tac(srw_ss())[GSYM SNOC_APPEND, map2_snoc]
  \\ full_simp_tac(srw_ss())[SNOC_APPEND, MAP,build_aux_APPEND1]
  \\ Cases_on `build_aux n8 (MAP2 (code_for_recc_case k) (MAP FST exps) c1) aux3`
  \\ full_simp_tac(srw_ss())[LET_DEF] \\ NTAC 4 (POP_ASSUM MP_TAC)
  \\ qspecl_then [`max_app`,`[SND x]`,`aux2`] mp_tac compile_exps_acc
  \\ full_simp_tac(srw_ss())[LET_DEF] \\ REPEAT STRIP_TAC \\ SRW_TAC [] []
  \\ FIRST_X_ASSUM MATCH_MP_TAC
  \\ POP_ASSUM MP_TAC
  \\ ONCE_REWRITE_TAC [build_aux_MOVE]
  \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[code_installed_def]);

val compile_exps_EL = Q.store_thm("compile_exps_EL",
  `∀ls aux l2 aux2 n. compile_exps ma ls aux = (l2, aux2) ∧
   n < LENGTH ls
  ⇒
  ∃auxn aux2n.
  compile_exps ma [EL n ls] auxn = ([EL n l2], aux2n) ∧
  IS_SUBLIST aux2 aux2n`,
  ho_match_mp_tac SNOC_INDUCT
  \\ fs[compile_exps_SNOC]
  \\ rw[]
  \\ pairarg_tac \\ fs[]
  \\ pairarg_tac \\ fs[]
  \\ rw[]
  \\ imp_res_tac compile_exps_LENGTH
  \\ Cases_on`n = LENGTH ls` \\ fs[ADD1,EL_SNOC,EL_APPEND1,EL_APPEND2,EL_LENGTH_SNOC]
  \\ fs[LENGTH_EQ_NUM_compute] \\ rw[]
  >- (asm_exists_tac \\ rw[IS_SUBLIST_REFL])
  \\ `n < LENGTH ls` by fs[]
  \\ first_x_assum drule
  \\ disch_then drule \\ rw[]
  \\ asm_exists_tac \\ rw[]
  \\ qspecl_then[`ma`,`[x]`,`aux1`]mp_tac compile_exps_acc
  \\ simp[] \\ rw[]
  \\ fs[IS_SUBLIST_APPEND]
  \\ metis_tac[APPEND_ASSOC]);

val evaluate_recc_Lets = Q.prove(
  `!(ll:(num#'a) list) n7 rr env' (t1:('c,'ffi) bvlSem$state) ys c8 (x:(num#'a)) (x':(num#'a)) ck.
     EVERY (\n. n7 + ns + 2* n IN domain t1.code) (GENLIST I (LENGTH ll)) ==>
     (evaluate
       ([recc_Lets (n7 + ns) (REVERSE (MAP FST ll)) (LENGTH ll) (HD c8)],
        Block closure_tag [CodePtr (n7 + (ns + 2 * LENGTH ll)); Number (&(FST x-1)); RefPtr rr]::env',
        t1 with <| refs := t1.refs |+ (rr,
               ValueArray
               (MAP (K (Number 0)) (MAP FST ll) ++
                [Block closure_tag [CodePtr (n7 + (ns + 2* LENGTH ll)); Number (&(FST x'-1)); RefPtr rr]]++ys));clock := ck |>) =
      evaluate
       ([HD c8],
        MAP2 (\n args. Block closure_tag [CodePtr (n7 + ns + 2* n); Number &(args-1); RefPtr rr])
                  (GENLIST I (LENGTH ll + 1)) (MAP FST ll ++ [FST x]) ++ env',
        t1 with <| refs := t1.refs |+ (rr,
               ValueArray
               (MAP2 (\n args. Block closure_tag [CodePtr (n7 + ns + 2* n); Number &(args-1); RefPtr rr])
                  (GENLIST I (LENGTH ll + 1)) (MAP FST ll ++ [FST x']) ++ ys)); clock := ck |>))`,
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
                   `Block closure_tag [CodePtr (n7 + (ns + 2 * SUC (LENGTH l))); Number (&(FST x'-1)); RefPtr rr]::env'`,
                   `t1`,
                   `[Block closure_tag [CodePtr (n7 + (ns + 2 * SUC (LENGTH l))); Number (&(FST x''-1)); RefPtr rr]] ++ ys`,
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
            | SOME loc => Call (LENGTH c8 - 1) (SOME (loc + num_stubs max_app)) (c8++[c7])],env,s) = (r, s')`,
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
            | SOME loc => Call (LENGTH c8 - 1) (SOME (loc + num_stubs max_app)) (c8++[c7])],env,s) = (r, s'')`,
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
    dest_closure max_app loc_opt func args = SOME (Partial_app c)
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
    dest_closure max_app loc_opt func args = SOME (Full_app exp args1 args2)
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
      check_loc max_app loc_opt loc num_args (LENGTH args) (num_args - rem_args)`,
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
    v_rel max_app f refs code v1 v2 ∧
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
  `v_rel max_app f1 t1.refs t1.code func (Block tag (ptr::Number (&n-1)::rest)) ∧
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
  `cl_rel max_app f1 refs code (env,ys) func (Block tag (p::Number (&(total_args) - 1)::fvs))
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
  simp_tac(std_ss++ARITH_ss)[int_arithTheory.INT_NUM_SUB]);

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
    lookup (generic_app_fn_location (LENGTH args - 1)) s.code =
      SOME (LENGTH args + 1, generate_generic_app max_app (LENGTH args - 1)) ∧
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
  rev_full_simp_tac(srw_ss())[] >>
  first_x_assum match_mp_tac >>
  Cases_on`LENGTH args` \\ fs[GENLIST_CONS]);

val cl_rel_get_loc = Q.prove (
  `cl_rel max_app f1 refs code (env,fvs) func (Block tag (CodePtr p::n::ys))
   ⇒
   num_stubs max_app ≤ p ∧
   get_loc func = SOME (p-(num_stubs max_app))`,
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
  `p = EL k (GENLIST (λn. loc + num_stubs max_app + 2*n) (LENGTH exps_ps))` by metis_tac [p_genlist] >>
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
  `dest_closure max_app l f a = SOME x ⇒ dest_closure' l f a = SOME x`,
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
    v_rel max_app f1 refs code func func' ∧
    cl_rel max_app (FRANGE f1) refs code (env,fvs) func func' ∧
    LIST_REL (v_rel max_app f1 refs code) env fvs ∧
    LIST_REL (v_rel max_app f1 refs code) args args'
    ⇒
    ∃body' aux1 aux2 new_env' exp'.
      lookup ptr code = SOME (n + 2,exp') ∧
      compile_exps max_app [body] aux1 = ([body'],aux2) ∧ code_installed aux2 code ∧
      env_rel max_app f1 refs code new_env new_env' ∧
      !t1. evaluate ([exp'], DROP (LENGTH args' - (n + 1)) args'++[func'], t1 with <| refs := refs; code := code |>) =
           evaluate ([body'], new_env', t1 with <| refs := refs; code := code |>)`,
  srw_tac[][cl_rel_cases, dest_closure'_def] >>
  full_simp_tac(srw_ss())[int_arithTheory.INT_NUM_SUB, closure_code_installed_def] >>
  rev_full_simp_tac(srw_ss())[] >>
  simp [] >>
  full_simp_tac(srw_ss())[check_loc_def, LET_THM] >>
  BasicProvers.EVERY_CASE_TAC >>
  srw_tac[][]
  >- (qabbrev_tac `func' = Block closure_tag (CodePtr (p + num_stubs max_app)::Number (&num_args − 1):: env')` >>
      qabbrev_tac `witness = DROP (LENGTH args' − num_args) args'++env'++DROP (LENGTH args' − num_args) args' ++ [func']` >>
      cl_rel_run_tac)
  >- (qabbrev_tac `func' = Block closure_tag (CodePtr (p + num_stubs max_app)::Number (&num_args − 1):: env')` >>
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
      `LIST_REL (v_rel max_app f1 refs code)
                (DROP (LENGTH args − n') args)
                (DROP (LENGTH args' − (n + 1)) args')`
              by (`n' = n+1` by ARITH_TAC >>
                  metis_tac [cl_rel_run_lemma3, EVERY2_LENGTH]) >>
      `LIST_REL (v_rel max_app f1 refs code)
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
    cl_rel max_app f refs code (fvs,fvs') cl cl'
    ⇒
    get_old_args cl = SOME [] ∧
    ?l num_args fvs.
      cl' = Block closure_tag (CodePtr l::Number (&num_args)::fvs)`,
  srw_tac[][cl_rel_cases] >>
  srw_tac[][get_old_args_def, EL_MAP] >>
  `?n e p. EL k exps_ps = ((n,e),p)` by metis_tac [pair_CASES] >>
  srw_tac[][]);

val dest_closure_full_of_part = Q.prove (
  `dest_closure max_app loc func args = SOME (Full_app body newenv rest) ∧
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
    dest_closure max_app loc func args = SOME (Full_app body newenv rest) ∧
    v_rel max_app f1 refs code func func' ∧
    LIST_REL (v_rel max_app f1 refs code) args args'
    ⇒
    ∃ck' body' aux1 aux2 newenv' exp'.
      lookup ptr code = SOME (n + 2,exp') ∧
      compile_exps max_app [body] aux1 = ([body'],aux2) ∧ code_installed aux2 code ∧
      env_rel max_app f1 refs code newenv newenv' ∧
      !t1.
        evaluate ([exp'], DROP (LENGTH args' - (n + 1)) args' ++ [func'], inc_clock ck' (t1 with <|refs := refs; code := code|>)) =
        evaluate ([body'], newenv', (t1 with <| refs := refs; code := code |>))`,
  srw_tac[][] >>
  qpat_x_assum `v_rel _ x0 x1 x2 x3 x4` (fn x => mp_tac x >> simp [v_rel_cases] >> assume_tac x) >>
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
  `v_rel max_app f1 refs code cl (Block closure_tag (CodePtr l::Number (&num_args')::fvs'))`
            by (srw_tac[][v_rel_cases, partial_app_tag_def] >>
                metis_tac [closure_tag_def]) >>
  `LENGTH arg_env ≠ 0 ∧ LENGTH ys ≠ 0 ∧ LENGTH ys < num_args` by metis_tac [LENGTH_EQ_NUM] >>
  `LIST_REL (v_rel max_app f1 refs code) (args++arg_env) (args'++ys)`
             by metis_tac [EVERY2_APPEND] >>
  assume_tac (SIMP_RULE (srw_ss()) [GSYM AND_IMP_INTRO] dest_closure_full_of_part |> GEN_ALL) >>
  rpt (pop_assum (fn th => first_assum (assume_tac o MATCH_MP th))) >>
  strip_assume_tac (SIMP_RULE (srw_ss()) [GSYM AND_IMP_INTRO] cl_rel_run) >>
  full_simp_tac(srw_ss())[] >>
  rpt (pop_assum (fn x => first_assum (strip_assume_tac o MATCH_MP x))) >>
  MAP_EVERY qexists_tac [`new_env'`, `aux2`, `aux1`, `body'`] >>
  srw_tac[][] >>
  `?total_args. (&num_args'):int = &total_args - 1`
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
                             qpat_x_assum `X = func` (assume_tac o GSYM) >>
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
                          `CodePtr (partial_app_fn_location max_app (num_args − 1) (LENGTH ys − 1))`,
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
  srw_tac[][dec_clock_def]) |> INST_TYPE[alpha|->``:'c``,beta|->``:'ffi``];

val list_rel_app = Q.prove (
  `!R args args' l0 c l func rem_args.
    dest_closure max_app NONE func args = SOME (Full_app c l l0) ∧
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
  srw_tac [ARITH_ss] [TAKE_APPEND1, TAKE_TAKE, EL_CONS])
  |> INST_TYPE[alpha|->``:'c``,beta|->``:'ffi``];

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

val s1 = ``s1:('c,'ffi) closSem$state``;


val env_rel_ind = theorem"env_rel_ind";

val code_installed_subspt = Q.store_thm("code_installed_subspt",
  `code_installed aux code1 /\ subspt code1 code2 ==> code_installed aux code2`,
  rw[code_installed_def,EVERY_MEM]
  \\ res_tac \\ rpt(pairarg_tac \\ fs[])
  \\ fs[subspt_lookup]);

val closure_code_installed_subspt = Q.store_thm("closure_code_installed_subspt",
  `closure_code_installed a code1 b c /\ subspt code1 code2 ==> closure_code_installed a code2 b c`,
  rw[closure_code_installed_def,EVERY_MEM]
  \\ res_tac \\ rpt(pairarg_tac \\ fs[])
  \\ metis_tac[subspt_lookup,code_installed_subspt]);

val cl_rel_subspt = Q.store_thm("cl_rel_subspt",
  `∀a b c.
     cl_rel x y z code1 a b c ⇒ subspt code1 code2 ⇒ cl_rel x y z code2 a b c`,
  ho_match_mp_tac cl_rel_ind \\ rw[]
  \\ rw[Once cl_rel_cases]
  >- metis_tac[code_installed_subspt,subspt_lookup]
  >- metis_tac[code_installed_subspt,subspt_lookup]
  \\ disj2_tac
  \\ map_every qexists_tac[`exps_ps`,`r`]
  \\ fs[]
  \\ metis_tac[closure_code_installed_subspt]);

val v_rel_subspt = Q.prove(
  `!x y. v_rel max_app f refs code1 x y ==>
      subspt code1 code2 ==>
      v_rel max_app f refs code2 x y`,
  ho_match_mp_tac v_rel_ind \\ rw[]
  \\ rw[Once v_rel_cases] \\ fsrw_tac[ETA_ss][]
  >- metis_tac[cl_rel_subspt]
  \\ disj2_tac
  \\ map_every qexists_tac[`arg_env`,`cl`]
  \\ qexists_tac`env` \\ qexists_tac`fvs`
  \\ qexists_tac`num_args`
  \\ fs[]
  \\ imp_res_tac subspt_lookup \\ fs[]
  \\ metis_tac[cl_rel_subspt])
  |> SPEC_ALL |> MP_CANON |> curry save_thm "v_rel_subspt";

val env_rel_subspt = Q.store_thm("env_rel_subspt",
  `∀x y z code e1 e2.
    env_rel x y z code e1 e2 ⇒
     ∀code'. subspt code code' ⇒ env_rel x y z code' e1 e2`,
  recInduct env_rel_ind
  \\ rw[env_rel_def]
  \\ metis_tac[v_rel_subspt]);

val clos_tag_shift_eq_nil_tag = store_thm("clos_tag_shift_eq_nil_tag[simp]",
  ``(clos_tag_shift tag = nil_tag <=> tag = nil_tag) /\
    (clos_tag_shift tag = cons_tag <=> tag = cons_tag)``,
  fs [clos_tag_shift_def] \\ rw [] \\ fs []
  \\ EVAL_TAC \\ decide_tac);

val v_rel_IMP_v_to_words_lemma = prove(
  ``!x y.
      v_rel max_app f refs code x y ==>
      !ns. (v_to_list x = SOME (MAP Word64 ns)) <=>
           (v_to_list y = SOME (MAP Word64 ns))``,
  ho_match_mp_tac closSemTheory.v_to_list_ind \\ rw []
  \\ fs [bvlSemTheory.v_to_list_def,closSemTheory.v_to_list_def,v_rel_SIMP]
  \\ Cases_on `tag = cons_tag` \\ fs [] \\ rveq \\ fs []
  \\ res_tac \\ fs [case_eq_thms,v_rel_SIMP]
  THEN1
   (Cases_on `ns` \\ fs [] \\ rveq \\ fs [v_rel_SIMP] \\ rveq \\ fs []
    \\ rw [] \\ fs [] \\ eq_tac \\ rw [] \\ fs [v_rel_SIMP])
  \\ Cases_on `ys` \\ fs [bvlSemTheory.v_to_list_def]);

val v_rel_IMP_v_to_words = prove(
  ``v_rel max_app f refs code x y ==> v_to_words y = v_to_words x``,
  rw [v_to_words_def,closSemTheory.v_to_words_def]
  \\ drule v_rel_IMP_v_to_words_lemma \\ fs []);

val v_rel_IMP_v_to_bytes_lemma = prove(
  ``!x y.
      v_rel max_app f refs code x y ==>
      !ns. (v_to_list x = SOME (MAP (Number o $& o (w2n:word8->num)) ns)) <=>
           (v_to_list y = SOME (MAP (Number o $& o (w2n:word8->num)) ns))``,
  ho_match_mp_tac closSemTheory.v_to_list_ind \\ rw []
  \\ fs [bvlSemTheory.v_to_list_def,closSemTheory.v_to_list_def,v_rel_SIMP]
  \\ Cases_on `tag = cons_tag` \\ fs [] \\ rveq \\ fs []
  \\ res_tac \\ fs [case_eq_thms,v_rel_SIMP]
  THEN1
   (Cases_on `ns` \\ fs [] \\ rveq \\ fs [v_rel_SIMP] \\ rveq \\ fs []
    \\ rw [] \\ fs [] \\ eq_tac \\ rw [] \\ fs [v_rel_SIMP])
  \\ Cases_on `ys` \\ fs [bvlSemTheory.v_to_list_def]);

val v_rel_IMP_v_to_bytes = prove(
  ``v_rel max_app f refs code x y ==> v_to_bytes y = v_to_bytes x``,
  rw [v_to_bytes_def,closSemTheory.v_to_bytes_def]
  \\ drule v_rel_IMP_v_to_bytes_lemma \\ fs []);

val not_domain_lookup = store_thm("not_domain_lookup",
  ``~(n IN domain x) <=> lookup n x = NONE``,
  fs [domain_lookup] \\ Cases_on `lookup n x` \\ fs []);

val cl_rel_union = prove(
  ``!a x y.
      cl_rel max_app f2 refs code a x y ==>
      cl_rel max_app f2 refs (union code c2) a x y``,
  ho_match_mp_tac cl_rel_ind \\ rw []
  THEN1
   (once_rewrite_tac [cl_rel_cases] \\ fs [lookup_union]
    \\ asm_exists_tac \\ fs []
    \\ fs [code_installed_def]
    \\ first_x_assum (fn th => mp_tac th THEN match_mp_tac MONO_EVERY)
    \\ fs [FORALL_PROD,lookup_union])
  THEN1
   (once_rewrite_tac [cl_rel_cases] \\ fs [lookup_union]
    \\ disj1_tac
    \\ asm_exists_tac \\ fs []
    \\ fs [code_installed_def]
    \\ first_x_assum (fn th => mp_tac th THEN match_mp_tac MONO_EVERY)
    \\ fs [FORALL_PROD,lookup_union])
  THEN1
   (once_rewrite_tac [cl_rel_cases] \\ fs [lookup_union]
    \\ rpt disj2_tac
    \\ qexists_tac `exps_ps` \\ fs []
    \\ qexists_tac `r` \\ fs []
    \\ fs [closure_code_installed_def]
    \\ first_x_assum (fn th => mp_tac th THEN match_mp_tac MONO_EVERY)
    \\ fs [FORALL_PROD,lookup_union]
    \\ rw []
    \\ asm_exists_tac \\ fs []
    \\ fs [code_installed_def]
    \\ first_x_assum (fn th => mp_tac th THEN match_mp_tac MONO_EVERY)
    \\ fs [FORALL_PROD,lookup_union]));

val v_rel_union = prove(
  ``!c2 x y.
      v_rel max_app f2 refs code x y ==>
      v_rel max_app f2 refs (union code c2) x y``,
  strip_tac \\ ho_match_mp_tac v_rel_ind \\ rw []
  \\ TRY (once_rewrite_tac [v_rel_cases] \\ fs [] \\ NO_TAC)
  THEN1
   (once_rewrite_tac [v_rel_cases] \\ fs []
    \\ pop_assum mp_tac
    \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ fs [])
  THEN1
   (once_rewrite_tac [v_rel_cases] \\ fs []
    \\ rpt (pop_assum mp_tac)
    \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ fs []
    \\ rpt strip_tac
    \\ disj2_tac
    \\ asm_exists_tac \\ fs []
    \\ match_mp_tac cl_rel_union \\ fs [])
  THEN1
   (once_rewrite_tac [v_rel_cases] \\ fs []
    \\ rpt (pop_assum mp_tac)
    \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ fs []
    \\ rpt strip_tac
    \\ disj2_tac
    \\ qexists_tac `arg_env`
    \\ qexists_tac `cl`
    \\ qexists_tac `env`
    \\ qexists_tac `fvs`
    \\ qexists_tac `num_args`
    \\ fs [lookup_union]
    \\ rpt strip_tac
    \\ match_mp_tac cl_rel_union \\ fs []));

val FEVERY_FUPDATE_LIST_SUFF = store_thm("FEVERY_FUPDATE_LIST_SUFF",
  ``!progs x p. FEVERY p x /\ EVERY p progs ==> FEVERY p (x |++ progs)``,
  Induct \\ fs [FUPDATE_LIST] \\ rw [] \\ fs []
  \\ first_x_assum match_mp_tac \\ fs []
  \\ Cases_on `h` \\ fs [FEVERY_FUPDATE]
  \\ fs [FEVERY_DEF,FDOM_DRESTRICT,DRESTRICT_DEF]);

val code_installed_union = store_thm("code_installed_union",
  ``code_installed aux y /\ DISJOINT (set (MAP FST aux)) (domain x) ==>
    code_installed aux (union x y)``,
  fs [code_installed_def,EVERY_MEM,FORALL_PROD] \\ rw []
  \\ first_x_assum drule
  \\ fs [lookup_union,case_eq_thms]
  \\ rw [] \\ disj1_tac
  \\ fs [DISJOINT_DEF,EXTENSION]
  \\ fs [METIS_PROVE [] ``~b\/c <=> b ==> c``,not_domain_lookup]
  \\ first_x_assum match_mp_tac
  \\ fs [MEM_MAP,EXISTS_PROD]
  \\ asm_exists_tac \\ fs []);

val code_installed_insert = store_thm("code_installed_insert",
  ``code_installed aux t /\ ~(MEM x (MAP FST aux)) ==>
    code_installed aux (insert x y t)``,
  fs [code_installed_def,EVERY_MEM,FORALL_PROD] \\ rw []
  \\ first_x_assum drule
  \\ fs [lookup_insert,case_eq_thms]
  \\ fs [MEM_MAP,EXISTS_PROD]
  \\ rpt strip_tac \\ fs []
  \\ CCONTR_TAC \\ fs []
  \\ rveq \\ fs [] \\ rfs []);

val code_installed_fromAList = store_thm("code_installed_fromAList",
  ``ALL_DISTINCT (MAP FST ls) ∧ IS_SUBLIST ls aux ==>
    code_installed aux (fromAList ls)``,
  fs [code_installed_def,EVERY_MEM,FORALL_PROD] \\ rw []
  \\ fs [lookup_fromAList]
  \\ fs [ALOOKUP_APPEND, IS_SUBLIST_APPEND]
  \\ fs [case_eq_thms, ALL_DISTINCT_APPEND, MEM_MAP, PULL_EXISTS, EXISTS_PROD]
  \\ imp_res_tac MEM_ALOOKUP \\ fs []
  \\ metis_tac[pair_CASES,option_CASES]);

val compile_exps_correct = Q.store_thm("compile_exps_correct",
  `(!tmp xs env ^s1 aux1 (t1:('c,'ffi) bvlSem$state) env' f1 res s2 ys aux2.
     (tmp = (xs,env,s1)) ∧
     (evaluate (xs,env,s1) = (res,s2)) /\ res <> Rerr(Rabort Rtype_error) /\
     (compile_exps s1.max_app xs aux1 = (ys,aux2)) /\
     every_Fn_SOME xs ∧ FEVERY (λp. every_Fn_SOME [SND (SND p)]) s1.code ∧
     every_Fn_vs_SOME xs ∧ FEVERY (λp. every_Fn_vs_SOME [SND (SND p)]) s1.code ∧
     code_installed aux2 t1.code /\
     env_rel s1.max_app f1 t1.refs t1.code env env' /\
     state_rel f1 s1 t1 ==>
     ?ck res' t2 f2.
        (evaluate (ys,env',t1 with clock := s1.clock + ck) = (res',t2)) /\
        result_rel (LIST_REL (v_rel s1.max_app f2 t2.refs t2.code)) (v_rel s1.max_app f2 t2.refs t2.code) res res' /\
        state_rel f2 s2 t2 /\
        f1 SUBMAP f2 /\
        (FDIFF t1.refs (FRANGE f1)) SUBMAP (FDIFF t2.refs (FRANGE f2)) ∧
        FEVERY (λp. every_Fn_SOME [SND (SND p)]) s2.code ∧
        FEVERY (λp. every_Fn_vs_SOME [SND (SND p)]) s2.code ∧
        s2.clock = t2.clock) ∧
   (!loc_opt func args ^s1 res s2 env (t1:('c,'ffi) bvlSem$state) args' func' f1.
     evaluate_app loc_opt func args s1 = (res,s2) ∧
     res ≠ Rerr(Rabort Rtype_error) ∧
     FEVERY (λp. every_Fn_SOME [SND (SND p)]) s1.code ∧
     FEVERY (λp. every_Fn_vs_SOME [SND (SND p)]) s1.code ∧
     v_rel s1.max_app f1 t1.refs t1.code func func' ∧
     LIST_REL (v_rel s1.max_app f1 t1.refs t1.code) args args' ∧
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
               (case find_code (SOME (loc + num_stubs s1.max_app)) (args' ++ [func']) t1.code of
                     NONE => (Rerr(Rabort Rtype_error),t2)
                   | SOME (args,exp) =>
                       if s1.clock + ck < (LENGTH args') then (Rerr(Rabort Rtimeout_error),t1 with clock := 0)
                       else evaluate ([exp],args,t1 with clock := s1.clock + ck - LENGTH args')) =
                 (res',t2)) ∧
       result_rel (LIST_REL (v_rel s1.max_app f2 t2.refs t2.code)) (v_rel s1.max_app f2 t2.refs t2.code) res res' ∧
       state_rel f2 s2 t2 ∧
       f1 ⊑ f2 ∧
       FDIFF t1.refs (FRANGE f1) ⊑ FDIFF t2.refs (FRANGE f2) ∧
       FEVERY (λp. every_Fn_SOME [SND (SND p)]) s2.code ∧
       FEVERY (λp. every_Fn_vs_SOME [SND (SND p)]) s2.code ∧
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
    \\ qmatch_assum_rename_tac`evaluate ([x],_) = (vv,_)`
    \\ reverse (Cases_on `vv`) \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
    >- (full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ qexists_tac`ck` >> simp[] >>
        first_assum(match_exists_tac o concl) >> simp[])
    \\ FIRST_X_ASSUM (qspecl_then[`aux1'`,`t2`]mp_tac) >> simp[]
    \\ imp_res_tac evaluate_mono >> full_simp_tac(srw_ss())[]
    \\ disch_then(qspecl_then[`env''`,`f2`]mp_tac)
    \\ imp_res_tac evaluate_const \\ fs[]
    \\ impl_tac >- (
         imp_res_tac env_rel_SUBMAP >>
         imp_res_tac env_rel_subspt >>
         imp_res_tac code_installed_subspt >>
         simp[] >>
         spose_not_then strip_assume_tac >> full_simp_tac(srw_ss())[])
    \\ strip_tac
    \\ full_simp_tac(srw_ss())[] \\ IMP_RES_TAC bEval_SING \\ full_simp_tac(srw_ss())[]
    \\ imp_res_tac evaluate_add_clock >> full_simp_tac(srw_ss())[]
    \\ qexists_tac `ck + ck'`
    \\ fsrw_tac[ARITH_ss][inc_clock_def]
    \\ every_case_tac \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
    \\ IMP_RES_TAC evaluate_mono
    \\ imp_res_tac v_rel_subspt
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
      \\ IMP_RES_TAC evaluate_mono \\ full_simp_tac(srw_ss())[]
      \\ IMP_RES_TAC env_rel_SUBMAP \\ full_simp_tac(srw_ss())[]
      \\ IMP_RES_TAC env_rel_subspt \\ full_simp_tac(srw_ss())[]
      \\ IMP_RES_TAC code_installed_subspt \\ full_simp_tac(srw_ss())[]
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
      \\ IMP_RES_TAC evaluate_mono \\ full_simp_tac(srw_ss())[]
      \\ IMP_RES_TAC env_rel_SUBMAP \\ full_simp_tac(srw_ss())[]
      \\ IMP_RES_TAC env_rel_subspt \\ full_simp_tac(srw_ss())[]
      \\ IMP_RES_TAC code_installed_subspt \\ full_simp_tac(srw_ss())[]
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
    \\ imp_res_tac evaluate_const \\ fs[]
    \\ first_x_assum(fn th =>
           first_assum(mp_tac o MATCH_MP (REWRITE_RULE[GSYM AND_IMP_INTRO]
             (CONV_RULE(STRIP_QUANT_CONV(LAND_CONV(move_conj_left(is_eq))))th))))
    \\ IMP_RES_TAC evaluate_mono \\ full_simp_tac(srw_ss())[]
    \\ CONV_TAC(LAND_CONV(STRIP_QUANT_CONV(REWRITE_CONV[AND_IMP_INTRO])))
    \\ disch_then(fn th =>
           first_assum(mp_tac o MATCH_MP (REWRITE_RULE[GSYM AND_IMP_INTRO]
             (CONV_RULE(STRIP_QUANT_CONV(LAND_CONV(move_conj_left(equal"state_rel" o #1 o dest_const o #1 o strip_comb))))th))))
    \\ qmatch_assum_rename_tac`LIST_REL _ v1 v2`
    \\ qmatch_assum_rename_tac`env_rel _ _ _ _ env1 env2`
    \\ disch_then(qspec_then`v2 ++ env2`mp_tac) >> full_simp_tac(srw_ss())[]
    \\ impl_tac >- metis_tac[code_installed_subspt]
    \\ impl_tac >-
     (MATCH_MP_TAC env_rel_APPEND \\ full_simp_tac(srw_ss())[]
      \\ IMP_RES_TAC env_rel_subspt \\ full_simp_tac(srw_ss())[]
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
    \\ `?c3 aux3. compile_exps s1.max_app [x1] aux1 = ([c3],aux3)` by METIS_TAC [PAIR,compile_exps_SING]
    \\ `?c4 aux4. compile_exps s1.max_app [x2] aux3 = ([c4],aux4)` by METIS_TAC [PAIR,compile_exps_SING]
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
    \\ IMP_RES_TAC evaluate_mono \\ full_simp_tac(srw_ss())[]
    \\ impl_tac >-
      (imp_res_tac code_installed_subspt \\
       full_simp_tac(srw_ss())[env_rel_def] \\
       IMP_RES_TAC env_rel_SUBMAP \\
       IMP_RES_TAC env_rel_subspt \\
       full_simp_tac(srw_ss())[])
    \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[]
    \\ qexists_tac `ck + ck'`
    \\ srw_tac[][]
    \\ imp_res_tac evaluate_add_clock
    \\ fsrw_tac[ARITH_ss][inc_clock_def]
    \\ Q.EXISTS_TAC `f2'` \\ full_simp_tac(srw_ss())[]
    \\ IMP_RES_TAC SUBMAP_TRANS \\ full_simp_tac(srw_ss())[])
  THEN1 (* Op *)
   (Cases_on `op = Install` THEN1
     (rveq \\ fs [] \\ rveq
      \\ fs [cEval_def,compile_exps_def] \\ SRW_TAC [] [bEval_def]
      \\ pairarg_tac \\ fs []
      \\ `?p. evaluate (xs,env,s) = p` by fs[] \\ PairCases_on `p` \\ fs[]
      \\ rveq \\ fs []
      \\ `p0 ≠ Rerr (Rabort Rtype_error)` by (strip_tac \\ fs []) \\ fs []
      \\ first_x_assum drule
      \\ rpt (disch_then drule)
      \\ strip_tac \\ fs []
      \\ reverse (Cases_on `p0`) \\ fs [] \\ rveq \\ fs []
      THEN1
       (qexists_tac `ck` \\ fs [bEval_def]
        \\ asm_exists_tac \\ fs [])
      \\ qabbrev_tac `a1 = REVERSE a`
      \\ `?xx. do_install a1 p1 = xx` by fs [] \\ fs []
      \\ pop_assum mp_tac
      \\ fs [closSemTheory.do_install_def]
      \\ strip_tac
      \\ `?a2 a3. a1 = [a2;a3]` by (fs [case_eq_thms] \\ rveq \\ fs [])
      \\ qunabbrev_tac `a1`
      \\ fs[SWAP_REVERSE_SYM]
      \\ pop_assum (fn th => fs [th])
      \\ Cases_on `v_to_bytes a2` \\ fs [] THEN1 (rveq \\ fs[])
      \\ Cases_on `v_to_words a3` \\ fs [] THEN1 (rveq \\ fs[])
      \\ pairarg_tac \\ reverse (fs [bool_case_eq])
      THEN1 (rveq \\ fs[])
      THEN1 (rveq \\ fs[])
      \\ Cases_on `p1.compile cfg progs` \\ fs []
      \\ rename1 `_ = SOME yy`
      \\ PairCases_on `yy` \\ fs []
      \\ PairCases_on `progs` \\ fs []
      \\ qpat_x_assum `xx = _` (assume_tac o GSYM) \\ fs []
      \\ PairCases_on `xx`
      \\ `xx0 <> Rerr (Rabort Rtype_error)` by
           (strip_tac \\ fs [] \\ rveq \\ fs [])
      \\ qpat_x_assum `_ = (xx0,xx1)` mp_tac \\ fs []
      \\ simp [Once bool_case_eq]
      \\ strip_tac \\ rveq \\ fs []
      \\ `xx0 = (if t2.clock = 0 then Rerr (Rabort Rtimeout_error)
                                 else Rval progs0) /\
          xx1 = p1 with
          <|clock := t2.clock − 1;
            compile_oracle := shift_seq 1 p1.compile_oracle;
            code := p1.code |++ progs1|>`
           by (IF_CASES_TAC \\ fs [])
      \\ rveq \\ fs []
      \\ pop_assum kall_tac \\ fs [EVAL ``shift_seq 1 f 0``]
      \\ fs [bEval_def]
      \\ fs [bvlSemTheory.do_install_def,do_app_def]
      \\ fs [EVAL ``shift_seq 1 f 0``]
      \\ drule (GEN_ALL v_rel_IMP_v_to_bytes) \\ strip_tac
      \\ `v_to_words y = v_to_words a3` by
        (imp_res_tac v_rel_IMP_v_to_words \\ fs [])
      \\ `p1.compile = pure_cc (compile_inc p1.max_app) t2.compile ∧
          t2.compile_oracle = pure_co (compile_inc p1.max_app) ∘ p1.compile_oracle`
            by fs [state_rel_def,compile_oracle_inv_def]
      \\ `?cfg loc1 prog1 progs. t2.compile_oracle 0 = (cfg,(loc1,0,prog1)::progs)`
          by (fs [backendPropsTheory.pure_co_def,compile_inc_def,compile_prog_def]
              \\ pairarg_tac \\ fs []
              \\ imp_res_tac compile_exps_LENGTH
              \\ Cases_on`new_exps` \\ fs[])
      \\ `t2.compile cfg' ((loc1,0,prog1)::progs) =
            SOME (x,x',FST (t2.compile_oracle 1))` by
           (fs [] \\ rfs []
            \\ fs [backendPropsTheory.pure_co_def,backendPropsTheory.pure_cc_def])
      \\ `DISJOINT (domain t2.code) (set (MAP FST progs)) ∧
          loc1 ∉ domain t2.code ∧ ¬MEM loc1 (MAP FST progs) ∧
          ALL_DISTINCT (MAP FST progs)` by
        (`ALL_DISTINCT (MAP FST ((loc1,0,prog1)::progs))` by
            metis_tac [compile_oracle_inv_def,state_rel_def] \\ fs []
         \\ fs [compile_oracle_inv_def,state_rel_def]
         \\ qpat_x_assum `!n. DISJOINT _ _` (qspec_then `0` mp_tac)
         \\ simp [nth_code_def] \\ rfs []
         \\ fs[backendPropsTheory.pure_co_def])
      \\ `state_rel f2 (p1 with
              <|clock := p1.clock − 1;
                compile_oracle := shift_seq 1 p1.compile_oracle;
                code := p1.code |++ progs1|>) (t2 with
           <|clock := t2.clock − 1;
             compile_oracle := shift_seq 1 t2.compile_oracle;
             code := union t2.code (fromAList ((loc1,0,prog1)::progs))|>)` by
       (qpat_x_assum `state_rel f2 p1 t2` mp_tac \\ simp [state_rel_def]
        \\ strip_tac \\ fs [lookup_union]
        \\ rpt strip_tac
        THEN1
         (first_x_assum (fn th => mp_tac th \\ match_mp_tac LIST_REL_mono)
          \\ Cases \\ Cases \\ fs [OPTREL_def]
          \\ strip_tac \\ match_mp_tac v_rel_union \\ fs [])
        THEN1 (res_tac \\ fs[])
        THEN1
         (first_x_assum drule \\ strip_tac \\ fs []
          \\ rename1 `_ x2 x3`
          \\ Cases_on `x3` \\ fs []
          \\ Cases_on `x2` \\ fs [ref_rel_def]
          \\ first_x_assum (fn th => mp_tac th \\ match_mp_tac LIST_REL_mono)
          \\ rpt strip_tac \\ match_mp_tac v_rel_union \\ fs [])
        THEN1
         (fs [compile_oracle_inv_def]
          \\ fs [FUN_EQ_THM,shift_seq_def]
          \\ rpt strip_tac \\ res_tac \\ fs []
          \\ qpat_x_assum `!n. DISJOINT _ _` (qspec_then `SUC n` mp_tac)
          \\ fs [nth_code_def]
          \\ rewrite_tac [ADD1]
          \\ match_mp_tac (METIS_PROVE [] ``(x = x1) ==> f x y ==> f x1 y``)
          \\ fs [shift_seq_def,backendPropsTheory.pure_co_def]
          \\ rfs [] \\ fs [union_assoc,compile_inc_def,compile_prog_def])
        \\ fs [alistTheory.flookup_fupdate_list]
        \\ Cases_on `ALOOKUP (REVERSE progs1) name` \\ fs []
        THEN1
         (first_x_assum drule
          \\ strip_tac \\ asm_exists_tac \\ fs []
          \\ fs [code_installed_def]
          \\ pop_assum mp_tac
          \\ match_mp_tac MONO_EVERY
          \\ fs [FORALL_PROD,lookup_union])
        \\ fs [] \\ rveq \\ fs []
        \\ qabbrev_tac `new_progs = (loc1,0,prog1)::progs`
        \\ qabbrev_tac `aa = name + num_stubs p1.max_app`
        \\ `ALL_DISTINCT (MAP FST new_progs)` by
         (fs [compile_oracle_inv_def]
          \\ ntac 4 (first_x_assum (qspec_then `0` mp_tac)) \\ rfs []
          \\ fs [backendPropsTheory.pure_co_def,compile_inc_def,compile_prog_def])
        \\ `?aux1 aux2 c2.
              lookup aa (fromAList new_progs) = SOME (arity,c2) /\
              compile_exps p1.max_app [c] aux1 = ([c2],aux2) /\
              set aux2 SUBSET set new_progs` by
           (rfs [] \\ fs [backendPropsTheory.pure_co_def]
            \\ rveq \\ fs [compile_inc_def,lookup_fromAList]
            \\ rfs [alookup_distinct_reverse]
            \\ qpat_x_assum `ALL_DISTINCT (MAP FST progs1)` assume_tac
            \\ qunabbrev_tac `aa`
            \\ drule ALOOKUP_MEM
            \\ ntac 2 (pop_assum mp_tac)
            \\ simp[compile_prog_def]
            \\ pairarg_tac \\ fs[]
            \\ rw[MEM_EL]
            \\ drule compile_exps_EL
            \\ disch_then(qspec_then`SUC n`mp_tac)
            \\ simp[EL_MAP]
            \\ pop_assum (assume_tac o SYM) \\ fs[]
            \\ strip_tac
            \\ goal_assum(first_assum o mp_then Any mp_tac)
            \\ conj_tac
            >- (
              irule ALOOKUP_ALL_DISTINCT_MEM
              \\ imp_res_tac compile_exps_LENGTH
              \\ simp[]
              \\ simp[MAP2_MAP,MEM_MAP,MEM_ZIP,PULL_EXISTS,EXISTS_PROD]
              \\ disj1_tac
              \\ CONV_TAC SWAP_EXISTS_CONV
              \\ qexists_tac`SUC n`
              \\ simp[] )
            \\ simp[SUBSET_DEF]
            \\ metis_tac[IS_SUBLIST_MEM] )
        \\ `lookup aa t2.code = NONE` by
           (fs [compile_oracle_inv_def]
            \\ qpat_x_assum `!n. DISJOINT _ _` (qspec_then `0` mp_tac)
            \\ fs [nth_code_def] \\ rfs []
            \\ fs [DISJOINT_DEF,EXTENSION,not_domain_lookup]
            \\ disch_then (qspec_then `aa` strip_assume_tac) \\ fs []
            \\ fs [lookup_fromAList]
            \\ drule ALOOKUP_MEM \\ simp []
            \\ pop_assum mp_tac \\ simp [MEM_MAP,FORALL_PROD,PULL_EXISTS]
            \\ fs[backendPropsTheory.pure_co_def])
        \\ fs [] \\ asm_exists_tac \\ fs []
        \\ match_mp_tac code_installed_union
        \\ reverse conj_tac
        THEN1
         (fs [Abbr `new_progs`,DISJOINT_DEF,SUBSET_DEF,EXTENSION]
          \\ CCONTR_TAC \\ fs []
          \\ fs [MEM_MAP] \\ fs []
          \\ first_x_assum drule
          \\ CCONTR_TAC \\ fs []
          \\ rveq \\ fs []
          \\ rename1 `MEM yy _` \\ PairCases_on `yy` \\ fs [FORALL_PROD]
          \\ metis_tac [])
        \\ simp [code_installed_def,EVERY_MEM,FORALL_PROD]
        \\ rpt strip_tac
        \\ fs [lookup_fromAList]
        \\ fs [GSYM MEM_ALOOKUP] \\ fs [SUBSET_DEF])
      \\ `FEVERY (λp. every_Fn_SOME [SND (SND p)]) (p1.code |++ progs1) ∧
          FEVERY (λp. every_Fn_vs_SOME [SND (SND p)]) (p1.code |++ progs1)` by
       (strip_tac \\ match_mp_tac FEVERY_FUPDATE_LIST_SUFF \\ fs []
        \\ fs [compile_oracle_inv_def,state_rel_def]
        \\ rpt (first_x_assum (qspec_then `0` mp_tac)) \\ fs [])
      \\ Cases_on `t2.clock = 0` \\ fs []
      THEN1
       (qexists_tac `ck` \\ fs []
        \\ fs [find_code_def,lookup_union]
        \\ fs [not_domain_lookup]
        \\ fs [lookup_fromAList] \\ rveq \\ fs []
        \\ qexists_tac `f2` \\ fs [] \\ rfs [])
      \\ imp_res_tac evaluate_const \\ fs []
      \\ fs [backendPropsTheory.pure_cc_def,compile_inc_def]
      \\ fs [clos_to_bvlTheory.compile_prog_def]
      \\ pairarg_tac \\ fs []
      \\ drule compile_exps_EL
      \\ disch_then(qspec_then`0`mp_tac)
      \\ simp[] \\ strip_tac
      \\ first_x_assum drule
      \\ imp_res_tac compile_exps_SING \\ fs [] \\ rveq \\ fs []
      \\ disch_then (qspecl_then [`t2 with
          <|compile_oracle := shift_seq 1 t2.compile_oracle;
            code := union t2.code (fromAList ((loc1,0,prog1)::progs))|>`,
         `[]`,`f2`] mp_tac)
      \\ fs [] \\ impl_tac
      THEN1 (fs [env_rel_def]
             \\ rewrite_tac [CONJ_ASSOC]
             \\ conj_tac THEN1
              (qpat_x_assum `state_rel f2 p1 t2` mp_tac
               \\ simp [state_rel_def,compile_oracle_inv_def]
               \\ strip_tac
               \\ rpt (first_x_assum (qspec_then `0` mp_tac)) \\ fs [])
             \\ rfs [backendPropsTheory.pure_co_def,compile_inc_def]
             \\ imp_res_tac compile_exps_LENGTH
             \\ Cases_on`new_exps` \\ fs[]
             \\ fs [compile_prog_def] \\ rveq \\ fs []
             \\ match_mp_tac code_installed_union \\ fs []
             \\ simp [fromAList_def]
             \\ reverse conj_tac
             >- (
               fs[IN_DISJOINT]
               \\ METIS_TAC[IS_SUBLIST_MEM, MEM_MAP] )
             \\ match_mp_tac code_installed_insert \\ fs []
             \\ reverse conj_tac
             >- ( METIS_TAC[IS_SUBLIST_MEM, MEM_MAP] )
             \\ simp[fromAList_append]
             \\ match_mp_tac code_installed_union \\ fs []
             \\ fs[domain_fromAList]
             \\ reverse conj_tac
             >- (
               fs[IN_DISJOINT, ALL_DISTINCT_APPEND]
               \\ METIS_TAC[IS_SUBLIST_MEM, MEM_MAP] )
             \\ simp[code_installed_def, lookup_fromAList]
             \\ simp[EVERY_MEM, FORALL_PROD] \\ rw[]
             \\ match_mp_tac ALOOKUP_ALL_DISTINCT_MEM
             \\ fs[ALL_DISTINCT_APPEND]
             \\ METIS_TAC[IS_SUBLIST_MEM])
      \\ strip_tac
      \\ qpat_x_assum `bvlSem$evaluate (c1,_) = _` assume_tac
      \\ drule bvlPropsTheory.evaluate_add_clock \\ simp []
      \\ disch_then (qspec_then `ck'` assume_tac)
      \\ qexists_tac `ck+ck'` \\ fs [inc_clock_def]
      \\ fs [backendPropsTheory.pure_cc_def]
      \\ fs [backendPropsTheory.pure_co_def]
      \\ rfs []
      \\ fs [find_code_def,lookup_union]
      \\ fs [not_domain_lookup]
      \\ fs [lookup_fromAList] \\ rveq \\ fs []
      \\ fs [compile_inc_def,compile_prog_def]
      \\ imp_res_tac compile_exps_LENGTH
      \\ Cases_on`new_exps` \\ fs[]
      \\ rveq \\ fs [dec_clock_def]
      \\ rename1 `state_rel f3 s3 t3`
      \\ qexists_tac `f3` \\ fs []
      \\ imp_res_tac SUBMAP_TRANS \\ fs [])
    \\ srw_tac[][]
    \\ full_simp_tac(srw_ss())[cEval_def,compile_exps_def] \\ SRW_TAC [] [bEval_def]
    \\ `?p. evaluate (xs,env,s) = p` by full_simp_tac(srw_ss())[] \\ PairCases_on `p` \\ full_simp_tac(srw_ss())[]
    \\ `?cc. compile_exps s.max_app xs aux1 = cc` by full_simp_tac(srw_ss())[] \\ PairCases_on `cc` \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[LET_DEF,PULL_FORALL] \\ SRW_TAC [] []
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`aux1`]) \\ full_simp_tac(srw_ss())[]
    \\ IMP_RES_TAC compile_exps_IMP_code_installed \\ REPEAT STRIP_TAC
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`t1`,`env''`,`f1`])
    \\ IMP_RES_TAC compile_exps_SING \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
    \\ full_simp_tac(srw_ss())[bEval_def]
    \\ reverse (Cases_on `p0`) \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
    \\ TRY (full_simp_tac(srw_ss())[] \\ qexists_tac `ck` >> srw_tac[][] \\ Q.EXISTS_TAC `f2` \\ full_simp_tac(srw_ss())[] \\ NO_TAC)
    \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
    \\ fs []
    \\ qexists_tac `ck` >> simp[]
    \\ reverse(Cases_on `do_app op (REVERSE a) p1`) \\ full_simp_tac(srw_ss())[] >- (
      srw_tac[][] >>
      first_x_assum(mp_tac o INST_TYPE[beta|->gamma] o MATCH_MP
        (do_app_err |> REWRITE_RULE [GSYM AND_IMP_INTRO] |> GEN_ALL)) >>
      simp[] >>
      imp_res_tac evaluate_const >> fs[] >>
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
      \\ `FRANGE (f2 \\ pp) = FRANGE f2` by
       (full_simp_tac(srw_ss())[FRANGE_DEF,finite_mapTheory.DOMSUB_FAPPLY_THM,EXTENSION]
        \\ METIS_TAC []) \\ full_simp_tac(srw_ss())[]
      \\ fs[list_CASE_same] \\ rveq
      \\ conj_tac >- (full_simp_tac(srw_ss())[v_rel_cases,FLOOKUP_UPDATE])
      \\ conj_tac THEN1
       (full_simp_tac(srw_ss())[state_rel_def,FLOOKUP_UPDATE]
        \\ REPEAT STRIP_TAC THEN1
         (Q.PAT_X_ASSUM `LIST_REL ppp qqq rrr` MP_TAC
          \\ MATCH_MP_TAC listTheory.LIST_REL_mono
          \\ REPEAT STRIP_TAC
          \\ MATCH_MP_TAC OPTREL_v_rel_NEW_REF \\ full_simp_tac(srw_ss())[]
          \\ MATCH_MP_TAC OPTREL_v_rel_NEW_F \\ full_simp_tac(srw_ss())[])
        THEN1
         (Q.PAT_X_ASSUM `INJ ($' f2) (FDOM f2) (FRANGE f2)` MP_TAC
          \\ REPEAT (Q.PAT_X_ASSUM `INJ xx yy zz` (K ALL_TAC))
          \\ full_simp_tac(srw_ss())[INJ_DEF,FAPPLY_FUPDATE_THM,FRANGE_DEF]
          \\ REPEAT STRIP_TAC \\ METIS_TAC [])
        THEN1 (
          ntac 2 (pop_assum mp_tac) \\ rw[] \\
          first_x_assum match_mp_tac \\ asm_exists_tac \\ rw[] )
        \\ Cases_on `n = pp` \\ full_simp_tac(srw_ss())[] THEN1
         (SRW_TAC [] []
          \\ imp_res_tac evaluate_const
          \\ qmatch_rename_tac`LIST_REL _ a _`
          \\ qpat_x_assum`LIST_REL _ a _`mp_tac
          \\ MATCH_MP_TAC listTheory.LIST_REL_mono
          \\ REPEAT STRIP_TAC
          \\ MATCH_MP_TAC v_rel_NEW_REF \\ full_simp_tac(srw_ss())[]
          \\ MATCH_MP_TAC v_rel_NEW_F \\ full_simp_tac(srw_ss())[])
        \\ RES_TAC \\ full_simp_tac(srw_ss())[]
        \\ `qq <> m` by (REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[FLOOKUP_DEF] \\ SRW_TAC [] [])
        \\ Cases_on`x`>>full_simp_tac(srw_ss())[]
        \\ Q.PAT_X_ASSUM `LIST_REL (v_rel _ f2 t2.refs t2.code) xs' ys'` MP_TAC
        \\ MATCH_MP_TAC listTheory.LIST_REL_mono
        \\ REPEAT STRIP_TAC
        \\ MATCH_MP_TAC v_rel_NEW_REF \\ full_simp_tac(srw_ss())[]
        \\ MATCH_MP_TAC v_rel_NEW_F \\ full_simp_tac(srw_ss())[])
      \\ conj_tac >-
       (full_simp_tac(srw_ss())[SUBMAP_DEF,FAPPLY_FUPDATE_THM,FDOM_FDIFF] \\ SRW_TAC [][] \\ METIS_TAC [] ) >>
      full_simp_tac(srw_ss())[SUBMAP_DEF,FDOM_FDIFF,FAPPLY_FUPDATE_THM,FDIFF_def,DRESTRICT_DEF] >> srw_tac[][] >> METIS_TAC[])
    \\ Cases_on `op = Update` \\ full_simp_tac(srw_ss())[] THEN1
     (full_simp_tac(srw_ss())[closSemTheory.do_app_def,bvlSemTheory.do_app_def]
      \\ fs[case_eq_thms,bool_case_eq] \\ rveq
      \\ fs[SWAP_REVERSE_SYM]
      \\ rveq \\ fs[v_rel_SIMP] \\ rveq
      \\ fs[SWAP_REVERSE,PULL_EXISTS]
      \\ imp_res_tac evaluate_const
      \\ qmatch_assum_rename_tac`FLOOKUP _ n = SOME (ValueArray l)`
      \\ `?y m.
            FLOOKUP f2 n = SOME m /\ FLOOKUP t2.refs m = SOME y /\
            ref_rel (v_rel s.max_app f2 t2.refs t2.code) (ValueArray l) y` by
              METIS_TAC [state_rel_def]
      \\ full_simp_tac(srw_ss())[] \\ rpt var_eq_tac
      \\ srw_tac[][] >> full_simp_tac(srw_ss())[]
      \\ IMP_RES_TAC EVERY2_LENGTH \\ full_simp_tac(srw_ss())[]
      \\ Q.EXISTS_TAC `f2` \\ full_simp_tac(srw_ss())[]
      \\ conj_tac >-
       (full_simp_tac(srw_ss())[state_rel_def,FLOOKUP_UPDATE] \\ REPEAT STRIP_TAC
        THEN1
         (Q.PAT_X_ASSUM `LIST_REL tt yy (DROP _ t2.globals)` MP_TAC
          \\ MATCH_MP_TAC listTheory.LIST_REL_mono
          \\ REPEAT STRIP_TAC
          \\ MATCH_MP_TAC OPTREL_v_rel_UPDATE_REF \\ full_simp_tac(srw_ss())[]
          \\ full_simp_tac(srw_ss())[FLOOKUP_DEF,FRANGE_DEF] \\ METIS_TAC [])
        THEN1 (
          pop_assum mp_tac \\ rw[]
          \\ first_x_assum MATCH_MP_TAC
          \\ asm_exists_tac \\ rw[] )
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
          \\ Q.PAT_X_ASSUM `LIST_REL (v_rel _ f2 t2.refs t2.code) l ys'` MP_TAC
          \\ MATCH_MP_TAC listTheory.LIST_REL_mono
          \\ REPEAT STRIP_TAC
          \\ MATCH_MP_TAC v_rel_UPDATE_REF \\ full_simp_tac(srw_ss())[]
          \\ full_simp_tac(srw_ss())[FLOOKUP_DEF,FRANGE_DEF] \\ METIS_TAC [])
        \\ RES_TAC \\ full_simp_tac(srw_ss())[]
        \\ `m' <> m''` by
         (Q.PAT_X_ASSUM `INJ ($' f2) (FDOM p1.refs) (FRANGE f2)` MP_TAC
          \\ SIMP_TAC std_ss [INJ_DEF,FRANGE_DEF] \\ full_simp_tac(srw_ss())[FLOOKUP_DEF]
          \\ METIS_TAC [])
        \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
        \\ qmatch_rename_tac`ref_rel _ ref _`
        \\ Cases_on`ref` >> full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
        \\ Q.PAT_X_ASSUM `LIST_REL pp xs' ws''` MP_TAC
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
        conj_tac >- (
          rw[FLOOKUP_UPDATE]
          \\ first_x_assum match_mp_tac
          \\ METIS_TAC[] ) \\
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
        imp_res_tac evaluate_const >>
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
    \\ Cases_on `∃flag. op = RefByte flag` \\ full_simp_tac(srw_ss())[] THEN1 (
      full_simp_tac(srw_ss())[closSemTheory.do_app_def,bvlSemTheory.do_app_def] >>
      Cases_on`REVERSE a`>>full_simp_tac(srw_ss())[]>>
      Cases_on`h`>>full_simp_tac(srw_ss())[]>>
      Cases_on`t`>>full_simp_tac(srw_ss())[]>>
      Cases_on`h`>>full_simp_tac(srw_ss())[]>>
      Cases_on`t'`>>full_simp_tac(srw_ss())[]>>
      Cases_on`a`>>full_simp_tac(srw_ss())[]>> rpt var_eq_tac >>
      full_simp_tac(srw_ss())[v_rel_SIMP,LET_THM] >> rpt var_eq_tac >>
      simp[PULL_EXISTS] >>
      qpat_x_assum`_ = Rval _`mp_tac >>
      IF_CASES_TAC >> fsrw_tac[][] >>
      IF_CASES_TAC \\ fsrw_tac[][] >> srw_tac[][] >>
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
        conj_tac >- (
          rw[FLOOKUP_UPDATE]
          \\ first_x_assum match_mp_tac
          \\ asm_exists_tac \\ rw[] ) \\
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
      \\ fs[case_eq_thms,PULL_EXISTS,bool_case_eq]
      \\ rw[] \\ fs[SWAP_REVERSE_SYM] \\ rw[]
      \\ fs[v_rel_SIMP] \\ rw[]
      \\ imp_res_tac evaluate_const
      \\ qmatch_assum_rename_tac`FLOOKUP _ n = SOME (ByteArray b l)`
      \\ `?y m.
            FLOOKUP f2 n = SOME m /\ FLOOKUP t2.refs m = SOME y /\
            ref_rel (v_rel s.max_app f2 t2.refs t2.code) (ByteArray b l) y` by
              METIS_TAC [state_rel_def]
      \\ full_simp_tac(srw_ss())[] \\ rpt var_eq_tac
      \\ Q.EXISTS_TAC `f2` \\ fsrw_tac[][]
      \\ conj_tac >-
       (full_simp_tac(srw_ss())[state_rel_def,FLOOKUP_UPDATE] \\ REPEAT STRIP_TAC
        THEN1
         (Q.PAT_X_ASSUM `LIST_REL tt yy (DROP _ t2.globals)` MP_TAC
          \\ MATCH_MP_TAC listTheory.LIST_REL_mono
          \\ REPEAT STRIP_TAC
          \\ MATCH_MP_TAC OPTREL_v_rel_UPDATE_REF \\ full_simp_tac(srw_ss())[]
          \\ full_simp_tac(srw_ss())[FLOOKUP_DEF,FRANGE_DEF] \\ METIS_TAC [])
        THEN1 (
          pop_assum mp_tac \\ rw[] \\
          TRY(disj1_tac \\ strip_tac \\ rw[] \\ qpat_x_assum`_ = SOME (ByteArray T _)`mp_tac \\ simp[]) \\
          first_x_assum MATCH_MP_TAC \\
          asm_exists_tac \\ rw[] )
        THEN1 (full_simp_tac(srw_ss())[EXTENSION,FLOOKUP_DEF] \\ METIS_TAC [])
        THEN1
         (`m IN FRANGE f2` by (full_simp_tac(srw_ss())[FLOOKUP_DEF,FRANGE_DEF] \\ METIS_TAC [])
          \\ full_simp_tac(srw_ss())[SUBSET_DEF] \\ METIS_TAC [])
        \\ SRW_TAC [] [] \\ Cases_on `n' = n` \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
        \\ RES_TAC \\ full_simp_tac(srw_ss())[]
        \\ `m' <> m''` by
         (Q.PAT_X_ASSUM `INJ ($' f2) (FDOM p1.refs) (FRANGE f2)` MP_TAC
          \\ SIMP_TAC std_ss [INJ_DEF,FRANGE_DEF] \\ full_simp_tac(srw_ss())[FLOOKUP_DEF]
          \\ METIS_TAC [])
        \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] [] \\ Cases_on`x` >> full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
        \\ Q.PAT_X_ASSUM `LIST_REL pp xs' ws''` MP_TAC
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
      \\ Cases_on `h` \\ full_simp_tac(srw_ss())[]
      \\ Cases_on `t'` \\ full_simp_tac(srw_ss())[]
      \\ fs[SWAP_REVERSE_SYM]
      \\ srw_tac[][]
      \\ simp[PULL_EXISTS]
      \\ full_simp_tac(srw_ss())[v_rel_SIMP] \\ srw_tac[][]
      \\ qmatch_assum_rename_tac`FLOOKUP f2 k = SOME r2`
      \\ Cases_on`FLOOKUP t2.refs r2` \\ full_simp_tac(srw_ss())[]
      \\ Cases_on`FLOOKUP p1.refs k` \\ full_simp_tac(srw_ss())[]
      >- (fs[state_rel_def] >> res_tac >> fs[] >> rfs[])
      \\ Cases_on`x` \\ full_simp_tac(srw_ss())[]
      \\ Cases_on`x'` \\ full_simp_tac(srw_ss())[]
      >- (fs[state_rel_def] >> res_tac >> fs[] >> rfs[] >> rveq)
      \\ Cases_on`call_FFI p1.ffi n l l''` \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
      \\ imp_res_tac evaluate_const
      >- (fs[state_rel_def] >> res_tac >> fs[] >> rfs[] >> rveq)
      \\ `?y m.
            FLOOKUP f2 k = SOME m /\ FLOOKUP t2.refs m = SOME y /\
            ref_rel (v_rel s.max_app f2 t2.refs t2.code) (ByteArray b' l'') y` by
              METIS_TAC [state_rel_def]
      \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
      \\ rfs[]
      \\ `t2.ffi = p1.ffi` by METIS_TAC[state_rel_def]
      \\ simp[]
      \\ TRY(qmatch_goalsub_abbrev_tac `F` >> fs[])
      \\ qexists_tac`f2` \\ simp[]
      \\ conj_tac >-
       (rveq \\ full_simp_tac(srw_ss())[state_rel_def,FLOOKUP_UPDATE] \\
        rveq \\ fs[] \\ REPEAT STRIP_TAC
        THEN1
         (Q.PAT_X_ASSUM `LIST_REL tt yy (DROP _ t2.globals)` MP_TAC
          \\ MATCH_MP_TAC listTheory.LIST_REL_mono
          \\ REPEAT STRIP_TAC
          \\ MATCH_MP_TAC OPTREL_v_rel_UPDATE_REF \\ full_simp_tac(srw_ss())[]
          \\ full_simp_tac(srw_ss())[FLOOKUP_DEF,FRANGE_DEF] \\ METIS_TAC [])
        THEN1 (
          pop_assum mp_tac \\ rw[] \\
          first_x_assum match_mp_tac \\
          asm_exists_tac \\ rw[] )
        THEN1 (full_simp_tac(srw_ss())[EXTENSION,FLOOKUP_DEF] \\ METIS_TAC [])
        THEN1
         (`m IN FRANGE f2` by (full_simp_tac(srw_ss())[FLOOKUP_DEF,FRANGE_DEF] \\ METIS_TAC [])
          \\ full_simp_tac(srw_ss())[SUBSET_DEF] \\ METIS_TAC [])
        \\ SRW_TAC [] [] \\ Cases_on `n' = k` \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
        \\ RES_TAC \\ full_simp_tac(srw_ss())[]
        \\ fs[FLOOKUP_UPDATE] >> rveq >> simp[ref_rel_simp]
        \\ `m <> m'` by
         (Q.PAT_X_ASSUM `INJ ($' f2) (FDOM p1.refs) (FRANGE f2)` MP_TAC
          \\ SIMP_TAC std_ss [INJ_DEF,FRANGE_DEF] \\ full_simp_tac(srw_ss())[FLOOKUP_DEF]
          \\ rveq \\ METIS_TAC [])
        \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] [] \\ Cases_on`x` >> full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
        \\ Q.PAT_X_ASSUM `LIST_REL pp xs' ws''` MP_TAC
        \\ MATCH_MP_TAC listTheory.LIST_REL_mono
        \\ REPEAT STRIP_TAC
        \\ MATCH_MP_TAC v_rel_UPDATE_REF \\ full_simp_tac(srw_ss())[]
        \\ full_simp_tac(srw_ss())[FLOOKUP_DEF,FRANGE_DEF] \\ METIS_TAC [])
      \\ `m IN FRANGE f2` by (full_simp_tac(srw_ss())[FLOOKUP_DEF,FRANGE_DEF] \\ METIS_TAC [])
      \\ full_simp_tac(srw_ss())[SUBMAP_DEF,FDIFF_def,DRESTRICT_DEF,FAPPLY_FUPDATE_THM, add_args_def]
      \\ rveq \\ fs[])
    \\ Cases_on `∃str. op = String str` \\ fs[] >- (
      fs[closSemTheory.do_app_def,bvlSemTheory.do_app_def]
      \\ Cases_on`REVERSE a` \\  fs[] \\ rw[]
      \\ rw[v_rel_SIMP,FLOOKUP_UPDATE]
      \\ qexists_tac`f2`
      \\ conj_tac
      >- ( fs[state_rel_def,SUBSET_DEF] \\ METIS_TAC[LEAST_NOTIN_FDOM] )
      \\ conj_tac
      >- (
        fs[state_rel_def] \\
        conj_tac >- (
          match_mp_tac(MP_CANON(GEN_ALL LIST_REL_mono)) >>
          ONCE_REWRITE_TAC[CONJ_COMM] >>
          first_assum(match_exists_tac o concl) >> simp[] >>
          rpt strip_tac >>
          match_mp_tac OPTREL_v_rel_NEW_REF >>
          simp[LEAST_NOTIN_FDOM] ) >>
        conj_tac >- (
          rw[FLOOKUP_UPDATE]
          >- (
            fs[FLOOKUP_DEF]
            \\ METIS_TAC[LEAST_NOTIN_FDOM] )
          \\ first_x_assum match_mp_tac
          \\ asm_exists_tac \\ rw[] ) \\
        conj_tac >- fs[SUBSET_DEF] \\
        rw[FLOOKUP_UPDATE] \\
        first_x_assum drule \\ rw[] \\ simp[] \\
        rw[] >- ( fs[FLOOKUP_DEF] \\ METIS_TAC[LEAST_NOTIN_FDOM] ) \\
        Cases_on`x` \\ fs[] \\
        match_mp_tac(MP_CANON(GEN_ALL LIST_REL_mono)) >>
        ONCE_REWRITE_TAC[CONJ_COMM] >>
        asm_exists_tac \\ fs[] \\ rw[] \\
        match_mp_tac v_rel_NEW_REF \\
        simp[LEAST_NOTIN_FDOM])
      \\ simp[]
      \\ qmatch_goalsub_abbrev_tac`t2.refs |+ (ptr,_)`
      \\ `ptr ∉ FRANGE f2`
      by (
        fs[state_rel_def]
        \\ `ptr ∉ FDOM t2.refs` suffices_by METIS_TAC[SUBSET_DEF]
        \\ simp[Abbr`ptr`,LEAST_NOTIN_FDOM] )
      \\ fs[FDIFF_def,DRESTRICT_DEF,SUBMAP_DEF,FAPPLY_FUPDATE_THM]
      \\ rw[] \\ METIS_TAC[LEAST_NOTIN_FDOM] )
    \\ Cases_on`op = FromListByte` \\ fs[] >- (
      fs[closSemTheory.do_app_def,bvlSemTheory.do_app_def]
      \\ Cases_on`REVERSE a` \\  fs[]
      \\ Cases_on`t` \\  fs[] \\ rw[]
      \\ fs[PULL_EXISTS] \\ pop_assum mp_tac
      \\ DEEP_INTRO_TAC some_intro \\ fs[] \\ rw[]
      \\ DEEP_INTRO_TAC some_intro \\ fs[]
      \\ reverse(rw[])
      >- (
        imp_res_tac v_to_list
        \\ qexists_tac`x`
        \\ fs[EVERY_MEM]
        \\ fs[LIST_REL_EL_EQN,LIST_EQ_REWRITE,EL_MAP,v_rel_SIMP] )
      \\ simp[v_rel_SIMP,FLOOKUP_UPDATE]
      \\ imp_res_tac v_to_list
      \\ qexists_tac`f2`
      \\ conj_tac
      >- (
        conj_tac
        >- (
          fs[LIST_REL_EL_EQN,LIST_EQ_REWRITE,EL_MAP,v_rel_SIMP]
          \\ rw[] \\ rfs[] \\ res_tac \\ rfs[EL_MAP] )
        \\ fs[state_rel_def,SUBSET_DEF] \\ METIS_TAC[LEAST_NOTIN_FDOM] )
      \\ conj_tac
      >- (
        fs[state_rel_def] \\
        conj_tac >- (
          match_mp_tac(MP_CANON(GEN_ALL LIST_REL_mono)) >>
          ONCE_REWRITE_TAC[CONJ_COMM] >>
          first_assum(match_exists_tac o concl) >> simp[] >>
          rpt strip_tac >>
          match_mp_tac OPTREL_v_rel_NEW_REF >>
          simp[LEAST_NOTIN_FDOM] ) >>
        conj_tac >- (
          rw[FLOOKUP_UPDATE]
          >- (
            fs[FLOOKUP_DEF]
            \\ METIS_TAC[LEAST_NOTIN_FDOM] )
          \\ first_x_assum match_mp_tac
          \\ asm_exists_tac \\ rw[] ) \\
        conj_tac >- fs[SUBSET_DEF] \\
        rw[FLOOKUP_UPDATE] \\
        first_x_assum drule \\ rw[] \\ simp[] \\
        rw[] >- ( fs[FLOOKUP_DEF] \\ METIS_TAC[LEAST_NOTIN_FDOM] ) \\
        Cases_on`x''` \\ fs[] \\
        match_mp_tac(MP_CANON(GEN_ALL LIST_REL_mono)) >>
        ONCE_REWRITE_TAC[CONJ_COMM] >>
        asm_exists_tac \\ fs[] \\ rw[] \\
        match_mp_tac v_rel_NEW_REF \\
        simp[LEAST_NOTIN_FDOM])
      \\ simp[]
      \\ qmatch_goalsub_abbrev_tac`t2.refs |+ (ptr,_)`
      \\ `ptr ∉ FRANGE f2`
      by (
        fs[state_rel_def]
        \\ `ptr ∉ FDOM t2.refs` suffices_by METIS_TAC[SUBSET_DEF]
        \\ simp[Abbr`ptr`,LEAST_NOTIN_FDOM] )
      \\ fs[FDIFF_def,DRESTRICT_DEF,SUBMAP_DEF,FAPPLY_FUPDATE_THM]
      \\ rw[] \\ METIS_TAC[LEAST_NOTIN_FDOM] )
    \\ Cases_on`op = ConcatByteVec` \\ fs[] >- (
      fs[closSemTheory.do_app_def,bvlSemTheory.do_app_def,PULL_EXISTS]
      \\ fs[case_eq_thms,PULL_EXISTS] \\ rw[]
      \\ fs[case_eq_thms] \\ rw[]
      \\ qpat_x_assum`$some _ = _`mp_tac
      \\ DEEP_INTRO_TAC some_intro \\ fs[] \\ strip_tac
      \\ imp_res_tac v_to_list \\ fs[v_rel_SIMP,FLOOKUP_UPDATE]
      \\ DEEP_INTRO_TAC some_intro \\ fs[PULL_EXISTS] \\ rw[]
      \\ qmatch_assum_rename_tac`LIST_REL _ (MAP ByteVector _) ls`
      \\ `∃ps. ls = MAP RefPtr ps`
      by (
        simp[LIST_EQ_REWRITE]
        \\ fs[LIST_REL_EL_EQN,v_rel_SIMP,EL_MAP]
        \\ fs[GSYM RIGHT_EXISTS_IMP_THM,SKOLEM_THM]
        \\ qexists_tac`GENLIST f (LENGTH ls)`
        \\ simp[EL_MAP] )
      \\ map_every qexists_tac[`wss`,`ps`]
      \\ simp[]
      \\ `∀x. MAP RefPtr ps = MAP RefPtr x ⇔ x = ps`
      by ( rw[EQ_IMP_THM] \\ imp_res_tac INJ_MAP_EQ \\ fs[INJ_DEF] ) \\ simp[]
      \\ reverse conj_asm2_tac
      >- ( fs[LIST_EQ_REWRITE,LIST_REL_EL_EQN,EL_MAP,v_rel_SIMP] )
      \\ simp[]
      \\ `∀x. MAP (SOME o ByteArray T) wss : v ref option list = MAP (SOME o ByteArray T) x ⇔ x = wss`
      by ( rw[EQ_IMP_THM] \\ imp_res_tac INJ_MAP_EQ \\ fs[INJ_DEF] ) \\ simp[]
      \\ qexists_tac`f2` \\ fs[]
      \\ fs[state_rel_def]
      \\ qmatch_goalsub_abbrev_tac`ptr ∉ FRANGE f2`
      \\ `ptr ∉ FRANGE f2` by METIS_TAC[SUBSET_DEF,LEAST_NOTIN_FDOM]
      \\ simp[FLOOKUP_UPDATE]
      \\ reverse conj_tac
      >- (
        fs[FDIFF_def,DRESTRICT_DEF,SUBMAP_DEF,FAPPLY_FUPDATE_THM]
        \\ rw[] \\ METIS_TAC[LEAST_NOTIN_FDOM] )
      \\ conj_tac
      >- (
        match_mp_tac(MP_CANON(GEN_ALL LIST_REL_mono)) >>
        ONCE_REWRITE_TAC[CONJ_COMM] >>
        asm_exists_tac \\ fs[] \\ rw[] \\
        match_mp_tac OPTREL_v_rel_NEW_REF \\
        simp[Abbr`ptr`,LEAST_NOTIN_FDOM])
      \\ conj_tac
      >- (
        fs[IN_FRANGE_FLOOKUP]
        \\ rw[] \\ rfs[]
        \\ res_tac \\ simp[] )
      \\ rw[]
      \\ res_tac \\ simp[]
      \\ rw[] \\ fs[] \\ rfs[IN_FRANGE_FLOOKUP] \\ rw[]
      \\ Cases_on`x` \\ fs[]
      \\ match_mp_tac (MP_CANON(GEN_ALL LIST_REL_mono))
      \\ ONCE_REWRITE_TAC[CONJ_COMM] >>
      asm_exists_tac \\ fs[] \\ rw[] \\
      match_mp_tac v_rel_NEW_REF
      \\ fs[Abbr`ptr`,LEAST_NOTIN_FDOM] )
    \\ Cases_on`∃fl. op = CopyByte fl` \\ fs[] >- (
      fs[closSemTheory.do_app_def,bvlSemTheory.do_app_def,PULL_EXISTS]
      \\ Cases_on`fl`
      \\ fs[case_eq_thms,v_case_eq_thms,PULL_EXISTS,SWAP_REVERSE_SYM]
      \\ rveq \\ fs[v_rel_SIMP] \\ rw[] \\ fs[FLOOKUP_UPDATE] \\ rw[]
      \\ TRY (drule (GEN_ALL state_rel_refs_lookup) \\ disch_then imp_res_tac \\ fs[FLOOKUP_UPDATE])
      \\ TRY (
        rename1`FLOOKUP _ _ = SOME (ByteArray F _)`
        \\ qexists_tac`f2` \\ fs[]
        \\ reverse conj_tac
        >- (
          fs[FDIFF_def,DRESTRICT_DEF,SUBMAP_DEF,FAPPLY_FUPDATE_THM]
          \\ rw[DRESTRICT_DEF,FAPPLY_FUPDATE_THM]
          \\ rw[] \\ fs[IN_FRANGE_FLOOKUP] )
        \\ rw[]
        \\ match_mp_tac (GEN_ALL state_rel_UPDATE_REF)
        \\ simp[] \\ NO_TAC)
      \\ qexists_tac`f2` \\ fs[]
      \\ TRY (* new dst allocated *) (
        (conj_tac >- (
            strip_tac
            \\ fs[state_rel_def,SUBSET_DEF]
            \\ METIS_TAC[LEAST_NOTIN_FDOM] ))
        \\ (reverse conj_tac >- (
            fs[FDIFF_def,DRESTRICT_DEF,SUBMAP_DEF,FAPPLY_FUPDATE_THM]
            \\ rw[DRESTRICT_DEF,FAPPLY_FUPDATE_THM]
            \\ fs[state_rel_def,SUBSET_DEF]
            \\ METIS_TAC[LEAST_NOTIN_FDOM] ))
        \\ match_mp_tac state_rel_NEW_REF
        \\ rw[LEAST_NOTIN_FDOM] )
      (* existing dst *)
      \\ every_case_tac \\ fs[] \\ rveq \\ fs[]
      \\ (conj_tac >- (
          match_mp_tac (GEN_ALL state_rel_UPDATE_REF) \\ fs[] ))
      \\ fs[FDIFF_def,DRESTRICT_DEF,SUBMAP_DEF,FAPPLY_FUPDATE_THM]
      \\ rw[DRESTRICT_DEF,FAPPLY_FUPDATE_THM] \\ rw[]
      \\ fs[IN_FRANGE_FLOOKUP] )
    \\ imp_res_tac closSemTheory.do_app_const
    \\ first_x_assum(mp_tac o INST_TYPE[beta|->gamma] o MATCH_MP
         (GEN_ALL(REWRITE_RULE[GSYM AND_IMP_INTRO]do_app)))
    \\ first_x_assum(fn th => disch_then (mp_tac o C MATCH_MP th))
    \\ imp_res_tac evaluate_const \\ fs[]
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
    \\ `?c2 aux3. compile_exps s.max_app [exp] aux1 = (c2,aux3)` by METIS_TAC [PAIR]
    \\ full_simp_tac(srw_ss())[LET_DEF] \\ SRW_TAC [] []
    \\ full_simp_tac(srw_ss())[code_installed_def]
    \\ full_simp_tac(srw_ss())[bEval_def,bvlPropsTheory.evaluate_APPEND,bvlSemTheory.do_app_def,domain_lookup]
    \\ full_simp_tac(srw_ss())[clos_env_def]
    \\ IMP_RES_TAC (Q.GEN `t1` lookup_vars_IMP)
    \\ POP_ASSUM (qspec_then `t1 with clock := s.clock` strip_assume_tac)
    \\ imp_res_tac bvlPropsTheory.evaluate_var_reverse
    \\ qexists_tac`0`>>simp[] >> fs[]
    \\ full_simp_tac(srw_ss())[v_rel_cases, cl_rel_cases]
    \\ fsrw_tac[ARITH_ss][]
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
      `?c2 aux3. compile_exps s.max_app [body] aux1 = ([c2],aux3)` by
              METIS_TAC [PAIR,compile_exps_SING]
      \\ full_simp_tac(srw_ss())[LET_THM]
      \\ first_assum(split_uncurry_arg_tac o lhs o concl)
      \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
      \\ simp[bEval_def, bvlPropsTheory.evaluate_APPEND, bvlSemTheory.do_app_def]
      \\ IMP_RES_TAC lookup_vars_IMP
      \\ Cases_on `num_args ≤ s.max_app ∧ num_args ≠ 0` >>
      full_simp_tac(srw_ss())[] >> full_simp_tac(srw_ss())[] >>
      first_x_assum(qspec_then`t1 with clock := s.clock` STRIP_ASSUME_TAC) >>
      `env_rel s.max_app f1 t1.refs t1.code (Recclosure (SOME x) [] x' [(num_args,body)] 0::env) (Block closure_tag (CodePtr (x + num_stubs s.max_app)::Number (&(num_args − 1))::ys)::env'')`
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
      \\ qmatch_assum_abbrev_tac`compile_exps _ [exp] auxx = zz`
      \\ qspecl_then[`s.max_app`,`[exp]`,`auxx`]strip_assume_tac compile_exps_acc
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
    \\ `EVERY (λ(num_args,e). num_args ≤ s.max_app ∧ num_args ≠ 0) exps` by srw_tac[][Abbr `exps`]
    \\ pop_assum mp_tac
    \\ `every_Fn_SOME (MAP SND exps)` by (full_simp_tac(srw_ss())[Abbr`exps`])
    \\ `every_Fn_vs_SOME (MAP SND exps)` by (full_simp_tac(srw_ss())[Abbr`exps`])
    \\ ntac 2 (pop_assum mp_tac)
    \\ NTAC 4 (POP_ASSUM (K ALL_TAC))
    \\ ntac 3 DISCH_TAC
    \\ `?c7 aux7. compile_exps s.max_app (MAP SND exps) aux1 = (c7,aux7)` by METIS_TAC [PAIR]
    \\ `?n4 aux5. build_aux (x + num_stubs s.max_app)
           (MAP2 (code_for_recc_case (LENGTH exps + LENGTH names)) (MAP FST exps) c7)
           aux7 = (n4,aux5)` by METIS_TAC [PAIR]
    \\ `?c8 aux8. compile_exps s.max_app [exp] aux5 = (c8,aux8)` by METIS_TAC [PAIR]
    \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
    \\ FIRST_X_ASSUM (Q.SPECL_THEN [`aux5`]mp_tac) \\ full_simp_tac(srw_ss())[]
    \\ REPEAT STRIP_TAC
    \\ full_simp_tac(srw_ss())[build_recc_lets_def]
    \\ full_simp_tac(srw_ss())[bvlSemTheory.do_app_def,bEval_def,LET_DEF]
    \\ full_simp_tac(srw_ss())[bvlPropsTheory.evaluate_APPEND,evaluate_MAP_Const, REVERSE_APPEND]
    \\ IMP_RES_TAC lookup_vars_IMP2
    \\ `!t1:('c,'ffi) bvlSem$state. evaluate (REVERSE (MAP Var names), env'', t1) = (Rval (REVERSE ys), t1)`
        by ( metis_tac[evaluate_var_reverse,REVERSE_REVERSE])
    \\ full_simp_tac(srw_ss())[]
    \\ srw_tac[][GSYM MAP_REVERSE]
    \\ srw_tac[][evaluate_MAP_Const]
    \\ Q.ABBREV_TAC `rr = LEAST ptr. ptr NOTIN FDOM t1.refs`
    \\ full_simp_tac(srw_ss())[recc_Let0_def]
    \\ `x + num_stubs s.max_app + 2* (LENGTH exps - 1) IN domain t1.code` by
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
    \\ `exps <> []` by (full_simp_tac(std_ss)[GSYM LENGTH_NIL] \\ DECIDE_TAC)
    \\ `?ll x. exps = SNOC x ll` by METIS_TAC [SNOC_CASES] \\ full_simp_tac(srw_ss())[]
    \\ simp [REVERSE_APPEND, MAP_REVERSE, LENGTH_MAP]
    \\ `LENGTH ll = LENGTH ((MAP (K (Number 0)) (MAP FST ll)) : bvlSem$v list)`
         by full_simp_tac(srw_ss())[LENGTH_MAP]
    \\ POP_ASSUM (fn th => REWRITE_TAC [th])
    \\ srw_tac[][lupdate_append2]
    \\ `EVERY (\n. x + num_stubs s.max_app + 2*n IN domain t1.code) (GENLIST I (LENGTH ll))` by
     (full_simp_tac(srw_ss())[EVERY_GENLIST]
      \\ IMP_RES_TAC compile_exps_IMP_code_installed
      \\ IMP_RES_TAC compile_exps_LENGTH
      \\ full_simp_tac(srw_ss())[domain_lookup,code_installed_def]
      \\ IMP_RES_TAC build_aux_MEM \\ full_simp_tac(srw_ss())[]
      \\ rev_full_simp_tac(srw_ss())[LENGTH_MAP2]
      \\ REPEAT STRIP_TAC
      \\ `i < LENGTH ll + 1` by
       (IMP_RES_TAC compile_exps_LENGTH \\ full_simp_tac(srw_ss())[LENGTH_APPEND]
        \\ DECIDE_TAC)
      \\ RES_TAC
      \\ full_simp_tac(srw_ss())[code_installed_def,EVERY_MEM] \\ full_simp_tac(srw_ss())[]
      \\ RES_TAC \\ full_simp_tac(srw_ss())[] \\ PairCases_on `d` \\ full_simp_tac(srw_ss())[])
    \\ full_simp_tac(srw_ss())[hd_append, tl_append]
    \\ qspec_then`num_stubs s.max_app`(fn th => first_assum(mp_tac o MATCH_MP th))
         (Q.GEN`ns`(SIMP_RULE(srw_ss())[]evaluate_recc_Lets))
    \\ simp[] \\ disch_then kall_tac
    \\ `[HD c8] = c8` by (IMP_RES_TAC compile_exps_SING \\ full_simp_tac(srw_ss())[]) \\ full_simp_tac(srw_ss())[]
    \\ qpat_abbrev_tac`t1refs = t1.refs |+ (rr,vv)`
    \\ FIRST_X_ASSUM (qspecl_then [`t1 with <| refs := t1refs; clock := ck+s.clock|>`,
       `MAP2 (\n args. Block closure_tag [CodePtr (x + num_stubs s.max_app + 2*n); Number &(args-1); RefPtr rr])
          (GENLIST I (LENGTH (ll:(num#closLang$exp) list) + 1)) (MAP FST ll ++ [FST (x'':(num#closLang$exp))]) ++ env''`,`f1`] mp_tac)
    \\ `~(rr IN FDOM t1.refs)` by
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
             SIMP_RULE std_ss [whileTheory.LEAST_EXISTS])
        \\ full_simp_tac(srw_ss())[])
    THEN1
     (reverse (REPEAT STRIP_TAC) THEN1
       (full_simp_tac(srw_ss())[state_rel_def,Abbr`t1refs`] \\ STRIP_TAC THEN1
         (Q.PAT_X_ASSUM `LIST_REL ppp s.globals (DROP _ t1.globals)` MP_TAC
          \\ MATCH_MP_TAC listTheory.LIST_REL_mono
          \\ METIS_TAC [OPTREL_v_rel_NEW_REF])
        \\ STRIP_TAC >- (
          rw[FLOOKUP_UPDATE]
          \\ first_x_assum MATCH_MP_TAC
          \\ asm_exists_tac \\ rw[] )
        \\ STRIP_TAC THEN1 full_simp_tac(srw_ss())[SUBSET_DEF]
        \\ REPEAT STRIP_TAC \\ RES_TAC \\ full_simp_tac(srw_ss())[FLOOKUP_UPDATE]
        \\ `m <> rr` by (REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[FLOOKUP_DEF]) \\ full_simp_tac(srw_ss())[]
        \\ Cases_on`x'''`>>full_simp_tac(srw_ss())[]
        \\ Q.PAT_X_ASSUM `LIST_REL ppp xs ys'` MP_TAC
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
      \\ Q.EXISTS_TAC `ZIP (exps,GENLIST (\i.x+num_stubs s.max_app+2*i) (LENGTH exps))`
      \\ full_simp_tac(srw_ss())[LENGTH_ZIP, EL_MAP, LENGTH_MAP, EL_ZIP, MAP_ZIP]
      \\ `?num e. EL n exps = (num, e)` by metis_tac [pair_CASES]
      \\ `1 < LENGTH exps` by (full_simp_tac(srw_ss())[] \\ DECIDE_TAC)
      \\ full_simp_tac(srw_ss())[Abbr `t1refs`,FLOOKUP_UPDATE]
      \\ `MAP FST ll ++ [FST x''] = MAP FST exps` by srw_tac[][Abbr `exps`]
      \\ simp [EL_MAP]
      \\ srw_tac[][]
      THEN1
       (Q.PAT_X_ASSUM `LIST_REL (v_rel _ f1 t1.refs t1.code) x' ys` MP_TAC
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
      \\ `EVERY (λ(num_args,e). num_args ≤ s.max_app ∧ num_args ≠ 0) exps` by full_simp_tac(srw_ss())[Abbr `exps`]
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
    \\ `?c7 aux7. compile_exps s.max_app [x1] aux1 = ([c7],aux7)` by
          METIS_TAC [PAIR,compile_exps_SING]
    \\ `?c8 aux8. compile_exps s.max_app args aux7 = (c8,aux8)` by
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
    \\ `subspt t1.code t2.code` by (IMP_RES_TAC evaluate_mono >> full_simp_tac(srw_ss())[])
    \\ `code_installed aux7 t2.code` by metis_tac [code_installed_subspt]
    \\ `env_rel s.max_app f2 t2.refs t2.code env env''` by metis_tac [env_rel_SUBMAP,env_rel_subspt]
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`aux1`,`t2`,`env''`,`f2`]) \\ full_simp_tac(srw_ss())[]
    \\ imp_res_tac evaluate_const \\ full_simp_tac (srw_ss()) []
    \\ impl_tac >- (
        rev_full_simp_tac(srw_ss())[] >>
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
    \\ `subspt t2.code t2'.code` by (imp_res_tac evaluate_mono \\ fs[])
    \\ `LIST_REL (v_rel s.max_app f2' t2'.refs t2'.code) a v'`
          by metis_tac[LIST_REL_mono,v_rel_subspt,v_rel_SUBMAP]
    \\ res_tac
    \\ pop_assum kall_tac
    \\ pop_assum mp_tac
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
    \\ reverse (Cases_on `find_code (SOME (x + num_stubs s.max_app)) (v' ++ [y]) t2'.code`)
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
    \\ `?cc. compile_exps s.max_app [x] aux1 = cc` by full_simp_tac(srw_ss())[] \\ PairCases_on `cc` \\ full_simp_tac(srw_ss())[]
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
    \\ full_simp_tac(srw_ss())[closSemTheory.dec_clock_def]
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
      (full_simp_tac(srw_ss())[bvlSemTheory.dec_clock_def,closSemTheory.dec_clock_def,state_rel_def]
       \\ METIS_TAC[])
    \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[]
    \\ qexists_tac `ck`
    \\ `s.clock − 1 + ck = s.clock + ck - 1` by simp []
    \\ full_simp_tac(srw_ss())[bvlSemTheory.dec_clock_def, closSemTheory.dec_clock_def]
    \\ Q.EXISTS_TAC `f2` \\ full_simp_tac(srw_ss())[bvlSemTheory.dec_clock_def])
  THEN1 (* Call *)
   (srw_tac[][] >>
    full_simp_tac(srw_ss())[compile_exps_def,cEval_def]
    \\ `?c3 aux3. compile_exps s1.max_app xs aux1 = (c3,aux3)` by METIS_TAC [PAIR]
    \\ full_simp_tac(srw_ss())[LET_DEF] \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[bEval_def]
    \\ `?p. evaluate (xs,env,s1) = p` by full_simp_tac(srw_ss())[] \\ PairCases_on `p` \\ full_simp_tac(srw_ss())[]
    \\ SRW_TAC [] [] \\ IMP_RES_TAC compile_exps_IMP_code_installed
    \\ FIRST_X_ASSUM (qspecl_then [`aux1`,`t1`] mp_tac)
    \\ full_simp_tac(srw_ss())[] \\ REPEAT STRIP_TAC
    \\ POP_ASSUM (MP_TAC o Q.SPECL [`env''`,`f1`]) \\ full_simp_tac(srw_ss())[]
    \\ reverse (Cases_on `p0`) \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
    \\ TRY (full_simp_tac(srw_ss())[] \\ qexists_tac `ck` >> srw_tac[][] >> Q.EXISTS_TAC `f2` \\ full_simp_tac(srw_ss())[] \\ NO_TAC)
    \\ full_simp_tac(srw_ss())[closSemTheory.find_code_def,bvlSemTheory.find_code_def]
    \\ Cases_on `FLOOKUP p1.code dest` \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `x` \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `q = LENGTH a` \\ full_simp_tac(srw_ss())[]
    \\ `?aux1 c2 aux2.
          compile_exps s1.max_app [r] aux1 = ([c2],aux2) /\
          lookup (dest + num_stubs s1.max_app) t2.code = SOME (LENGTH a,c2) /\
          code_installed aux2 t2.code` by METIS_TAC [state_rel_def,evaluate_const]
    \\ IMP_RES_TAC EVERY2_LENGTH \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `t2.clock < ticks+1` \\ full_simp_tac(srw_ss())[]
    THEN1 (qexists_tac `ck` >> SRW_TAC [] [] \\ Q.EXISTS_TAC `f2` >> full_simp_tac(srw_ss())[])
    \\ full_simp_tac(srw_ss())[] \\ rev_full_simp_tac(srw_ss())[] \\ full_simp_tac(srw_ss())[]
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`aux1'`]) \\ full_simp_tac(srw_ss())[]
    \\ imp_res_tac evaluate_const
    \\ full_simp_tac(srw_ss())[closSemTheory.dec_clock_def]
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
    \\ fs[]
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
  (* cEvalApp real app *)
  \\ qpat_x_assum `evaluate_app x0 x1 x2 x3 = x4` mp_tac
  \\ simp [cEval_def]
  \\ qpat_abbrev_tac `args = _::_`
  \\ rename1 `args = z::zs`
  \\ DISCH_TAC
  \\ qabbrev_tac `args' = args''`
  \\ `LENGTH args' ≠ 0` by metis_tac [LIST_REL_LENGTH, LENGTH, DECIDE ``SUC x ≠ 0``]
  \\ full_simp_tac(srw_ss())[]
  \\ Cases_on `dest_closure s1.max_app loc_opt func args`
  \\ full_simp_tac(srw_ss())[]
  \\ Cases_on `x`
  \\ full_simp_tac(srw_ss())[]
  \\ srw_tac[][]
  >- ((* Partial application *)
      `LENGTH args = LENGTH args' ∧ LENGTH args ≠ 0` by (imp_res_tac LIST_REL_LENGTH \\ fs[Abbr`args`]) >>
      imp_res_tac dest_closure_part_app >>
      srw_tac[][PULL_EXISTS] >>
      imp_res_tac v_rel_num_rem_args >>
      srw_tac[][mk_cl_call_def, bEval_def, bEval_APPEND, bEvalOp_def] >>
      srw_tac [ARITH_ss] [el_append3] >>
      `&n' ≠ &(LENGTH args')` by srw_tac [ARITH_ss] [] >>
      `(&n'):int - 1 ≠ &(LENGTH args' - 1)`
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
      `LENGTH args' - 1 < s1.max_app` by decide_tac >>
      `lookup (generic_app_fn_location (LENGTH args' - 1)) t1.code = SOME (LENGTH args' + 1, generate_generic_app s1.max_app (LENGTH args' - 1))`
             by (full_simp_tac(srw_ss())[state_rel_def] >>
                 decide_tac) >>
      simp [find_code_def] >>
      `SUC (LENGTH zs) = LENGTH args` by metis_tac [LENGTH] >>
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
      drule (GEN_ALL unpack_closure_thm) >>
      disch_then drule >> disch_then strip_assume_tac >>
      `lookup (partial_app_fn_location s1.max_app total_args (LENGTH args' + LENGTH prev_args − 1)) t1.code =
           SOME (total_args - (LENGTH args' + LENGTH prev_args-1) + 1, generate_partial_app_closure_fn total_args (LENGTH args' + LENGTH prev_args − 1))`
               by (full_simp_tac(srw_ss())[state_rel_def] >>
                   first_x_assum match_mp_tac >>
                   srw_tac[][] >>
                   decide_tac) >>
      `LENGTH args' + LENGTH prev_args − 1 = LENGTH prev_args + (LENGTH args − 1)` by simp [] >>
      `LENGTH args' < total_args + 1 − LENGTH prev_args` by simp [] >>
      full_simp_tac(srw_ss())[] >>
      Q.ISPECL_THEN [`s1.max_app`, `total_args`, `prev_args`, `dec_clock 1 (t1 with clock := s1.clock)`, `args'`] assume_tac (Q.GEN`max_app`evaluate_generic_app_partial) >>
      rev_full_simp_tac(srw_ss())[domain_lookup] >>
      pop_assum mp_tac >>
      REWRITE_TAC [Once CONJ_SYM] >>
      disch_then drule >>
      impl_tac
      >- (
        qpat_x_assum `state_rel _ _ _` mp_tac >>
        simp_tac (srw_ss()) [state_rel_def, dec_clock_def]) >>
      strip_tac >>
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
              metis_tac [arith_helper_lem,LENGTH_NIL])
          >- (full_simp_tac(srw_ss())[bvlSemTheory.dec_clock_def, closSemTheory.dec_clock_def] >>
              full_simp_tac(srw_ss())[state_rel_def]) >>
          `args ≠ []` by (Cases_on `args` >> full_simp_tac(srw_ss())[]) >>
          full_simp_tac(srw_ss())[v_rel_cases, num_remaining_args_def,closure_tag_neq_1,partial_app_tag_neq_closure_tag] >>
          srw_tac[][] >>
          full_simp_tac(srw_ss())[num_remaining_args_def, add_args_def, partial_app_tag_neq_closure_tag]
          THEN1 simp [closSemTheory.dec_clock_def]
          THEN1 simp [closSemTheory.dec_clock_def]
(*
          >- (full_simp_tac(srw_ss())[bvlSemTheory.dec_clock_def,
                 closSemTheory.dec_clock_def] >>
              full_simp_tac(srw_ss())[state_rel_def])
          >- (full_simp_tac(srw_ss())[bvlSemTheory.dec_clock_def,
                 closSemTheory.dec_clock_def] >>
              full_simp_tac(srw_ss())[state_rel_def]) *)
          >- (full_simp_tac(srw_ss())[bvlSemTheory.dec_clock_def,
                 closSemTheory.dec_clock_def] >>
              full_simp_tac(srw_ss())[state_rel_def])
          >- (full_simp_tac(srw_ss())[bvlSemTheory.dec_clock_def,
                 closSemTheory.dec_clock_def] >>
              full_simp_tac(srw_ss())[state_rel_def])
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
              metis_tac [arith_helper_lem3, add_args_append, EVERY2_APPEND, LENGTH_NIL]))) >>
  (* Enough arguments to do something *)
  `SUC (LENGTH zs) = LENGTH args` by metis_tac [LENGTH] >>
  `every_Fn_SOME [e] ∧ every_Fn_vs_SOME [e]` by (
    qhdtm_x_assum`dest_closure`mp_tac >>
    simp[dest_closure_def] >>
    BasicProvers.CASE_TAC >> srw_tac[][] >>
    full_simp_tac(srw_ss())[v_rel_cases,cl_rel_cases] >>
    srw_tac[][] >> full_simp_tac(srw_ss())[add_args_def] >> srw_tac[][] >>
    pop_assum mp_tac >> srw_tac[][UNCURRY] >> full_simp_tac(srw_ss())[] >>
    full_simp_tac(srw_ss())[Once every_Fn_SOME_EVERY,Once every_Fn_vs_SOME_EVERY] >>
    full_simp_tac(srw_ss())[EVERY_MAP] >>
    full_simp_tac(srw_ss())[EVERY_MEM,MEM_EL,PULL_EXISTS,EL_MAP] ) >>
  full_simp_tac(srw_ss())[] >>
  imp_res_tac (Q.GEN`max_app` dest_closure_full_app) >>
  assume_tac (SIMP_RULE (srw_ss()) [GSYM AND_IMP_INTRO] (GEN_ALL v_rel_num_rem_args)) >>
  rpt (pop_assum (fn th => first_assum (strip_assume_tac o MATCH_MP th))) >>
  `loc_opt = NONE ∨ ?loc. loc_opt = SOME loc` by metis_tac [option_nchotomy] >>
  full_simp_tac(srw_ss())[check_loc_def] >>
  srw_tac[][]
  >- ((* App NONE *)
      qabbrev_tac `n = rem_args - 1` >>
      imp_res_tac EVERY2_LENGTH >>
      `lookup (generic_app_fn_location (LENGTH args' − 1)) t1.code =
         SOME ((LENGTH args' - 1) + 2,generate_generic_app s1.max_app (LENGTH args' − 1))`
                  by (full_simp_tac(srw_ss())[state_rel_def] >>
                      `LENGTH args' - 1 < s1.max_app` by decide_tac >>
                      metis_tac []) >>
      `LENGTH args' - 1 + 2  = LENGTH args' + 1` by decide_tac >>
      full_simp_tac(srw_ss())[] >>
      `(&rem_args):int - 1 = &n ∧ rem_args + 1 = n + 2`
           by (srw_tac [ARITH_ss] [Abbr `n`,int_arithTheory.INT_NUM_SUB]) >>
      `LENGTH args' − (LENGTH args' − rem_args) = rem_args` by decide_tac >>
      full_simp_tac(srw_ss())[] >>
      Cases_on `s1.clock < rem_args` >>
      full_simp_tac(srw_ss())[] >>
      simp []
      >- ((* Timeout *)
          Q.ISPEC_THEN `t1 with clock := s1.clock` (assume_tac o GEN_ALL o (SIMP_RULE (srw_ss()) [GSYM AND_IMP_INTRO]))
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
          `?v'. v_rel s1.max_app f2 t2.refs t2.code func'' v' ∧ res'' = Rval [v']`
                 by (full_simp_tac(srw_ss())[] >> metis_tac []) >>
          `LIST_REL (v_rel s1.max_app f2 t2.refs t2.code) l0 (TAKE (LENGTH args' − rem_args) args')`
                   by (match_mp_tac (GEN_ALL list_rel_app) >>
                       MAP_EVERY qexists_tac [`s1.max_app`,`args`, `e`, `l`, `func`] >>
                       srw_tac[][] >>
                       full_simp_tac(srw_ss())[LIST_REL_EL_EQN] >>
                       srw_tac[][] >>
                       match_mp_tac (GEN_ALL v_rel_subspt) >>
                       imp_res_tac evaluate_mono >>
                       first_assum(part_match_exists_tac (el 2 o strip_conj) o concl) >> simp[] >>
                       match_mp_tac (GEN_ALL v_rel_SUBMAP) >>
                       metis_tac []) >>
          `s'.max_app = s1.max_app` by
             (imp_res_tac closPropsTheory.evaluate_const \\ fs []) \\ fs [] >>
          first_x_assum (fn th => first_assum (assume_tac o MATCH_MP (SIMP_RULE (srw_ss()) [GSYM AND_IMP_INTRO] th))) >>
          rev_full_simp_tac(srw_ss())[] >>
          rpt (pop_assum (fn th => (first_assum (strip_assume_tac o MATCH_MP th)))) >>
          full_simp_tac(srw_ss())[LENGTH_TAKE] >>
          Cases_on `(LENGTH args' ≤ rem_args)` >>
          full_simp_tac(srw_ss())[]
          >- ((* No remaining arguments *)
              Q.ISPEC_THEN `t1 with clock := ck + ck' + s1.clock`
                (assume_tac o GEN_ALL o SIMP_RULE (srw_ss())
                     [GSYM AND_IMP_INTRO])(evaluate_mk_cl_call_spec
                  |> INST_TYPE [alpha|->``:'c``,beta|->``:'ffi``]) >>
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
              pop_assum (assume_tac o GSYM) \\ fs [] >>
              `!ck. t1 with <| clock := ck; code := t1.code |> = t1 with clock := ck`
                       by srw_tac[][bvlSemTheory.state_component_equality] >>
              srw_tac[][] >>
              qpat_x_assum `_ = n + 1` (assume_tac o GSYM) \\ fs [] >>
              `!ck. ck + s1.clock − LENGTH args' = s1.clock − LENGTH args' + ck` by decide_tac >>
              srw_tac[][] >>
              full_simp_tac(srw_ss())[cEval_def] >>
              `!ck. t1 with <| clock := ck; refs := t1.refs |> = t1 with clock := ck`
                       by srw_tac[][bvlSemTheory.state_component_equality] >>
              full_simp_tac(srw_ss())[] >> srw_tac[][] >>
              metis_tac [SUBMAP_TRANS]) >>
          (* Extra arguments *)
          srw_tac[][] >>
          imp_res_tac evaluate_const >> full_simp_tac (srw_ss())[] >>
          first_x_assum (qspec_then `SOMEENV` strip_assume_tac) >>
          Q.ISPEC_THEN `t1 with clock := ck + ck' + ck'' + 1 + s1.clock`
            (assume_tac o GEN_ALL o SIMP_RULE (srw_ss())
               [GSYM AND_IMP_INTRO]) (evaluate_mk_cl_call_spec
              |> INST_TYPE [alpha|->``:'c``,beta|->``:'ffi``]) >>
          rpt (pop_assum (fn x => first_assum (strip_assume_tac o MATCH_MP x))) >>
          pop_assum mp_tac >>
          simp [] >>
          DISCH_TAC >>
          qexists_tac `ck + ck' + ck'' + 1` >>
          simp [] >>
          pop_assum kall_tac >>
          first_x_assum (qspec_then `t1 with clock := ck + ck'' + s1.clock - rem_args` mp_tac) >>
          qpat_abbrev_tac`t11:('c,'ffi) bvlSem$state = inc_clock ck' Z` >>
          qpat_abbrev_tac`t12:('c,'ffi) bvlSem$state = dec_clock X Y` >>
          `t11 = t12` by (
            simp[Abbr`t11`,Abbr`t12`] >>
            srw_tac[][inc_clock_def,dec_clock_def,bvlSemTheory.state_component_equality] >>
            fsrw_tac[ARITH_ss][]) >>
          pop_assum SUBST1_TAC >>
          disch_then SUBST1_TAC >>
          map_every qunabbrev_tac[`t11`,`t12`] >>
          qmatch_assum_abbrev_tac`evaluate (_,_,t11) = (_,t2)` >>
          qpat_abbrev_tac`t12:('c,'ffi) bvlSem$state = X Y` >>
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
          drule mk_call_simp2 \\ disch_then strip_assume_tac \\
          pop_assum (fn th => first_x_assum (strip_assume_tac o MATCH_MP th)) >>
          pop_assum(qspecl_then[`SOMEENV`,`v''`,`inc_clock ck'' t2`](mp_tac o GSYM)) >>
          rpt var_eq_tac >>
          simp_tac(srw_ss())[inc_clock_def] >>
          `rem_args = n + 1` by fs [] >> fs [] >>
          disch_then kall_tac >>
          qhdtm_x_assum`evaluate`mp_tac >>
          simp_tac(srw_ss()++ARITH_ss)[] >>
          `SUC (LENGTH ys) − (n + 1) = SUC (SUC (LENGTH ys) − (n + 2))` by fs [] >>
          simp [] >>
          qmatch_goalsub_rename_tac `_ = (res4,t3)` >>
          Cases_on`res4`>> full_simp_tac(srw_ss())[] >>
          rpt strip_tac >>
          imp_res_tac bEval_SING >> full_simp_tac(srw_ss())[] >>
          metis_tac[SUBMAP_TRANS])
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
                (assume_tac o GEN_ALL o SIMP_RULE (srw_ss()) [GSYM AND_IMP_INTRO]) evaluate_mk_cl_call_spec >>
              rpt (pop_assum (fn x => first_assum (strip_assume_tac o MATCH_MP x))) >>
              pop_assum mp_tac >>
              simp [] >>
              DISCH_TAC >>
              qexists_tac `ck+ck'` >>
              rev_full_simp_tac (srw_ss()++ARITH_ss) [inc_clock_def, dec_clock_def] >>
              qexists_tac `f2` >>
              srw_tac[][])
          >- (Q.ISPEC_THEN `t1 with clock := ck+ck' +1+ s1.clock`
                (assume_tac o GEN_ALL o SIMP_RULE (srw_ss()) [GSYM AND_IMP_INTRO]) evaluate_mk_cl_call_spec >>
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
              full_simp_tac(srw_ss())[] >> srw_tac[][]))) >>
  (* App SOME *)
  `rem_args = LENGTH args` by ARITH_TAC >>
  full_simp_tac(srw_ss())[] >>
  srw_tac[][find_code_def] >>
  `&LENGTH args - 1:int = &(LENGTH args - 1)` by srw_tac[][int_arithTheory.INT_NUM_SUB] >>
  full_simp_tac(srw_ss())[] >>
  `t1.code = (t1 with clock := s1.clock - LENGTH args').code` by srw_tac[][] >>
  full_simp_tac std_ss [] >>
  strip_assume_tac (GEN_ALL (SIMP_RULE (srw_ss()) [GSYM AND_IMP_INTRO] (v_rel_run))) >>
  rpt (pop_assum (fn x => first_assum (strip_assume_tac o MATCH_MP x))) >>
  full_simp_tac(srw_ss())[] >>
  srw_tac[][] >>
  `ptr = loc' + num_stubs s1.max_app`
          by (full_simp_tac(srw_ss())[v_rel_cases] >>
              imp_res_tac cl_rel_get_loc >>
              full_simp_tac(srw_ss())[] >>
              srw_tac [ARITH_ss] [] >>
              metis_tac [no_partial_args,LENGTH_NIL]) >>
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
  imp_res_tac evaluate_const >> full_simp_tac(srw_ss())[] >>
  `(dec_clock (LENGTH args') s1).code = s1.code` by EVAL_TAC >>
  `(dec_clock (LENGTH args') s1).max_app = s1.max_app` by EVAL_TAC >>
  full_simp_tac(srw_ss())[] >> rev_full_simp_tac(srw_ss())[] >>
  first_x_assum (fn x => first_assum (strip_assume_tac o MATCH_MP (SIMP_RULE (srw_ss()) [GSYM AND_IMP_INTRO] x))) >>
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
  metis_tac []);

(* more correctness properties *)

val build_aux_thm = Q.prove(
  `∀c n aux n7 aux7.
    build_aux n c aux = (n7,aux7++aux) ⇒
    (MAP FST aux7) = (REVERSE (GENLIST ($+ n o $* 2) (LENGTH c)))`,
  Induct >> simp[build_aux_def] >> srw_tac[][] >>
  qmatch_assum_abbrev_tac`build_aux nn kk auxx = Z` >>
  qspecl_then[`kk`,`nn`,`auxx`]strip_assume_tac build_aux_acc >>
  Cases_on`build_aux nn kk auxx`>>UNABBREV_ALL_TAC>>full_simp_tac(srw_ss())[]>> srw_tac[][] >>
  full_simp_tac std_ss [Once (CONS_APPEND)] >>
  full_simp_tac std_ss [Once (GSYM APPEND_ASSOC)] >> res_tac >>
  srw_tac[][GENLIST,REVERSE_APPEND,REVERSE_GENLIST,PRE_SUB1] >>
  simp[LIST_EQ_REWRITE])

val lemma = Q.prove(`
  compile_exps max_app xs aux = (c,aux1) ⇒
  LENGTH c = LENGTH xs ∧ ∃ys. aux1 = ys ++ aux`,
  mp_tac (SPEC_ALL compile_exps_acc) \\ rw[] \\
  pairarg_tac \\ fs[] \\ rw[]);

val lemma2 = Q.prove(`
  build_aux n k aux = (a,b) ⇒
  ∃z. b = z ++ aux`,
  mp_tac (SPEC_ALL build_aux_acc) \\ rw[] \\ fs[]);

val compile_exps_code_locs = Q.store_thm("compile_exps_code_locs",
  `∀max_app xs aux ys aux2.
    compile_exps max_app xs aux = (ys,aux2++aux) ⇒
    MAP FST aux2 = MAP ((+) (num_stubs max_app)) (REVERSE(code_locs xs))`,
  ho_match_mp_tac compile_exps_ind >> rpt conj_tac >>
  rw[compile_exps_def] >>
  rpt(pairarg_tac \\ fs[]) >>
  fs[case_eq_thms,code_locs_def,pair_case_eq] >>
  rveq \\ fs[] >>
  rpt(pairarg_tac \\ fs[]) >>
  rveq \\ fs[] >> rw[] >>
  imp_res_tac lemma \\ fs[] \\ rveq \\
  imp_res_tac lemma2 \\ fs[] \\ rveq
  \\ fs[MAP_REVERSE,MAP_GENLIST]
  \\ rw[Once code_locs_cons]
  \\ fs[compile_exps_def] \\ rveq \\ fs[]
  \\ rfs[ADD1]
  \\ rw[Once code_locs_cons]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ imp_res_tac build_aux_thm
  \\ fs[LENGTH_MAP2,ADD1]
  \\ simp[LIST_EQ_REWRITE]);

val init_code_ok = Q.store_thm ("init_code_ok",
  `0 < max_app ⇒
   (!n.
      n < max_app ⇒ lookup (generic_app_fn_location n) (init_code max_app) = SOME (n + 2, generate_generic_app max_app n)) ∧
   (!tot n.
      tot < max_app ∧ n < tot ⇒
        lookup (partial_app_fn_location max_app tot n) (init_code max_app) =
          SOME (tot - n + 1, generate_partial_app_closure_fn tot n))`,
  srw_tac[][init_code_def, lookup_fromList, EL_APPEND1, partial_app_fn_location_def,
            generic_app_fn_location_def]
  >- decide_tac
  >- (
    srw_tac[][LENGTH_FLAT, MAP_GENLIST, combinTheory.o_DEF, sum_genlist_triangle] >>
    simp [ADD1] >>
    REWRITE_TAC [ADD_ASSOC] >>
    imp_res_tac triangle_div_lemma >>
    simp [])
  >- (
      simp [GSYM ADD_ASSOC, DECIDE ``!x. 1 + x = SUC x``, EL_CONS] >>
      `max_app ≤ max_app + (n + tot * (tot − 1) DIV 2)` by decide_tac >>
      ONCE_REWRITE_TAC[GSYM APPEND_ASSOC] >>
      simp[EL_APPEND2] >>
      rw [triangle_el_no_suff]));

 val domain_init_code_lt_num_stubs = Q.store_thm("domain_init_code_lt_num_stubs",
  `∀max_app x. x ∈ domain (init_code max_app) ⇒ x < (num_stubs max_app)`,
  simp[init_code_def,num_stubs_def,domain_fromList,LENGTH_FLAT,MAP_GENLIST,o_DEF]
  \\ simp[GSYM(SIMP_RULE(srw_ss())[K_DEF]REPLICATE_GENLIST),SUM_REPLICATE]
  \\ simp [sum_genlist_triangle]);

val compile_prog_code_locs = Q.store_thm("compile_prog_code_locs",
  `∀ls.
  MAP FST (compile_prog max_app ls) =
  MAP ((+)(num_stubs max_app) o FST) ls ++
  MAP ((+)(num_stubs max_app)) (REVERSE (code_locs (MAP (SND o SND) ls)))`,
  rw[compile_prog_def]
  \\ pairarg_tac \\ fs[]
  \\ pop_assum mp_tac
  \\ specl_args_of_then``compile_exps``compile_exps_code_locs strip_assume_tac
  \\ strip_tac \\ fs[]
  \\ imp_res_tac compile_exps_LENGTH \\ fs[]
  \\ simp[MAP2_MAP, MAP_MAP_o, o_DEF, UNCURRY]
  \\ simp[LIST_EQ_REWRITE,EL_MAP,EL_ZIP]);

val IMP_PERM_code_merge = Q.store_thm("IMP_PERM_code_merge",
  `!xs ys zs. PERM (xs ++ ys) zs ==> PERM (code_merge xs ys) zs`,
  HO_MATCH_MP_TAC code_merge_ind \\ rw []
  \\ once_rewrite_tac [code_merge_def]
  \\ fs [] \\ Cases_on `xs` \\ fs []
  \\ TRY (Cases_on `ys` \\ fs [])
  \\ IF_CASES_TAC \\ fs []
  THEN1 (fs [sortingTheory.PERM_NIL,sortingTheory.PERM_CONS_EQ_APPEND]
         \\ res_tac \\ metis_tac [])
  \\ `PERM (h'::h::(t ++ t')) zs` by
   (match_mp_tac PERM_TRANS
    \\ once_rewrite_tac [CONJ_COMM]
    \\ asm_exists_tac \\ fs []
    \\ simp [sortingTheory.PERM_CONS_EQ_APPEND]
    \\ qexists_tac `h::t` \\ fs []
    \\ qexists_tac `[]` \\ fs [] \\ NO_TAC)
  \\ pop_assum mp_tac
  \\ simp [Once sortingTheory.PERM_CONS_EQ_APPEND]
  \\ rw [] \\ res_tac
  \\ simp [Once sortingTheory.PERM_CONS_EQ_APPEND]
  \\ metis_tac []);

val code_split_IMP_PERM = Q.store_thm("code_split_IMP_PERM",
  `!xs1 xs2 xs3 ts1 ts2.
      code_split xs1 xs2 xs3 = (ts1,ts2) ==>
      PERM (ts1 ++ ts2) (xs2 ++ xs3 ++ xs1)`,
  Induct \\ fs [code_split_def] \\ rw [] \\ res_tac
  \\ match_mp_tac PERM_TRANS \\ asm_exists_tac \\ fs []
  \\ fs [sortingTheory.PERM_NIL,sortingTheory.PERM_CONS_EQ_APPEND]
  \\ qexists_tac `xs2 ++ xs3` \\ fs [sortingTheory.PERM_APPEND_IFF]
  \\ fs [PERM_APPEND]);

val PERM_code_sort = Q.store_thm("PERM_code_sort",
  `!xs. PERM (code_sort xs) xs`,
  HO_MATCH_MP_TAC code_sort_ind \\ rw [code_sort_def]
  \\ pairarg_tac \\ fs []
  \\ match_mp_tac IMP_PERM_code_merge
  \\ imp_res_tac code_split_IMP_PERM \\ fs []
  \\ match_mp_tac PERM_TRANS
  \\ once_rewrite_tac [CONJ_COMM] \\ asm_exists_tac \\ fs []
  \\ match_mp_tac sortingTheory.PERM_CONG \\ fs []);

val ALL_DISTINCT_code_sort = Q.store_thm("ALL_DISTINCT_code_sort",
  `ALL_DISTINCT (MAP FST (code_sort xs)) <=> ALL_DISTINCT (MAP FST xs)`,
  match_mp_tac sortingTheory.ALL_DISTINCT_PERM
  \\ match_mp_tac sortingTheory.PERM_MAP \\ fs [PERM_code_sort]);

val PERM_IMP_fromAList_EQ_fromAList = Q.store_thm("PERM_IMP_fromAList_EQ_fromAList",
  `!xs ys.
      PERM xs ys ==> ALL_DISTINCT (MAP FST xs) ==>
      fromAList xs = fromAList ys`,
  Induct \\ fs [sortingTheory.PERM_NIL,sortingTheory.PERM_CONS_EQ_APPEND]
  \\ rw [] \\ res_tac
  \\ fs [ALL_DISTINCT_APPEND]
  \\ fs [spt_eq_thm,wf_fromAList,lookup_fromAList]
  \\ PairCases_on `h` \\ fs [ALOOKUP_APPEND]
  \\ rw [] \\ fs [GSYM alistTheory.ALOOKUP_NONE]
  \\ every_case_tac \\ fs []);

val fromAList_code_sort = Q.store_thm("fromAList_code_sort",
  `ALL_DISTINCT (MAP FST xs) ==>
    fromAList (code_sort xs) = fromAList xs`,
  rw [] \\ match_mp_tac (MP_CANON PERM_IMP_fromAList_EQ_fromAList)
  \\ fs [PERM_code_sort,ALL_DISTINCT_code_sort]);

(*
val even_stubs3 = Q.prove (
  `!max_app. EVEN (num_stubs max_app + 3)`,
  Induct_on `max_app` >>
  rw [num_stubs_def, EVEN_ADD, EVEN, GSYM EVEN_MOD2] >>
  metis_tac []);
  *)

val _ = overload_on("code_loc'",``λe. code_locs [e]``);

val MAP_FST_chain_exps = Q.store_thm("MAP_FST_chain_exps",
  `∀i ls. ls <> [] ==> (MAP FST (chain_exps i ls) = MAP ((+)i) (COUNT_LIST (LENGTH ls)))`,
  recInduct chain_exps_ind
  \\ rw[chain_exps_def, COUNT_LIST_def, MAP_MAP_o, o_DEF]
  >- (EVAL_TAC \\ rw[])
  \\ AP_THM_TAC \\ AP_TERM_TAC
  \\ rw[FUN_EQ_THM]);

val chain_exps_code_locs = Q.store_thm("chain_exps_code_locs[simp]",
  `∀n es. code_locs (MAP (SND o SND) (chain_exps n es)) = code_locs es`,
  recInduct chain_exps_ind
  \\ rw[chain_exps_def]
  \\ rw[Once code_locs_cons]
  \\ rw[code_locs_def]);

val chain_exps_ALL_DISTINCT = Q.store_thm ("chain_exps_ALL_DISTINCT[simp]",
  `ALL_DISTINCT (MAP FST (chain_exps i ls))`,
  Cases_on`ls=[]`
  >- (rw[chain_exps_def])
  \\ fs [MAP_FST_chain_exps]
  \\ match_mp_tac ALL_DISTINCT_MAP_INJ
  \\ fs [all_distinct_count_list]);

val chain_exps_LE = Q.store_thm("chain_exps_LE",
  `!n xs. EVERY ($<= n) (MAP FST (chain_exps n xs))`,
  ho_match_mp_tac chain_exps_ind \\ rw [chain_exps_def]
  \\ fs [EVERY_MEM, MEM_MAP] \\ rw []
  \\ fs [PULL_EXISTS]
  \\ res_tac \\ fs []);

val chain_exps_GT = Q.store_thm("chain_exps_GT",
  `!n xs. xs <> [] ==> EVERY ($> (n + LENGTH xs)) (MAP FST (chain_exps n xs))`,
  ho_match_mp_tac chain_exps_ind \\ rw [chain_exps_def]
  \\ fs [EVERY_MEM, MEM_MAP] \\ rw []
  \\ fs [PULL_EXISTS]
  \\ res_tac \\ fs []);

val compile_common_distinct_locs = Q.store_thm("compile_common_distinct_locs",
  `compile_common c e = (c', p) ==> ALL_DISTINCT (MAP FST p ++ code_locs (MAP (SND o SND) p))`,
  simp [compile_common_def]
  \\ rpt (pairarg_tac \\ fs [])
  \\ strip_tac \\ rveq
  \\ qmatch_asmsub_abbrev_tac`renumber_code_locs_list N`
  \\ qmatch_goalsub_abbrev_tac `MAP f (clos_annotate$compile ls')`
  \\ qho_match_abbrev_tac `P (compile ls')`
  \\ qsuff_tac `P ls'`
  >- (
    simp [clos_annotateTheory.compile_def, Abbr `P`]
    \\ qunabbrev_tac `f`
    \\ simp[MAP_MAP_o, UNCURRY, o_DEF, ETA_AX]
    \\ simp[ALL_DISTINCT_APPEND, MEM_MAP, PULL_EXISTS, FORALL_PROD, code_locs_map]
    \\ rpt (pop_assum kall_tac)
    \\ strip_tac
    \\ fs [ALL_DISTINCT_FLAT, EL_MAP, MEM_MAP, PULL_EXISTS, UNCURRY,
           MAP_REVERSE, FORALL_PROD, MEM_FLAT]
    \\ metis_tac [clos_annotateProofTheory.annotate_code_locs,
                  clos_annotateTheory.annotate_def,
                  clos_annotateTheory.HD_FST_alt_free,
                  clos_annotateTheory.HD_shift,
                  SUBSET_DEF])
  \\ fs [Abbr `P`]
  (*
  \\ qabbrev_tac `lss = MAP FST ls' ++ FLAT (MAP (code_loc' o SND o SND) ls')`
  \\ qsuff_tac `ALL_DISTINCT lss`
  >-
   (fs [Abbr `f`, Abbr `lss`]
    \\ rpt (pop_assum kall_tac)
    \\ Induct_on `ls'`
    >- (EVAL_TAC \\ fs [])
    \\ fs [FORALL_PROD, toAList_domain, MEM_MAP, MEM_FLAT] \\ rw []
    >-
     (fs [MEM_FLAT, MEM_MAP, FORALL_PROD]
      \\ CCONTR_TAC \\ fs []
      \\ rfs [MEM_MAP]
      \\ metis_tac [])
    \\ fs [ALL_DISTINCT_APPEND]
    \\ conj_tac >- fs [ALL_DISTINCT_MAP_INJ]
    \\ fs [MEM_FLAT, MEM_MAP, FORALL_PROD]
    \\ CCONTR_TAC \\ fs []
    \\ rfs [MEM_MAP]
    \\ metis_tac [FST])
  \\ fs [Abbr `lss`]
  \\ `FLAT (MAP (code_loc' o SND o SND) ls') = code_locs (MAP (SND o SND) ls')`
    by (rpt (pop_assum kall_tac)
        \\ Induct_on `ls'` >- EVAL_TAC
        \\ fs [FORALL_PROD]
        \\ simp [Once code_locs_cons, SimpRHS])
  \\ pop_assum SUBST1_TAC
  *)
  \\ qmatch_assum_abbrev_tac `compile _ ls = (_, aux)`
  \\ simp [ALL_DISTINCT_APPEND, Abbr `ls'`,Abbr `f`]
  \\ once_rewrite_tac [code_locs_append]
  \\ simp [ALL_DISTINCT_APPEND]
  \\ qmatch_asmsub_abbrev_tac `renumber_code_locs_list N XS`
  (* clos_known *)
  \\ `is_subseq (code_locs es) (code_locs ls)`
    by metis_tac[clos_knownProofTheory.compile_code_locs]
  \\ `LENGTH ls = LENGTH es` by metis_tac[clos_knownProofTheory.compile_LENGTH]
  \\ `set (code_locs ls) ⊆ set (code_locs es)` by metis_tac[SUBSET_DEF,clos_knownProofTheory.is_subseq_MEM]
  \\ `ALL_DISTINCT (code_locs es) ⇒ ALL_DISTINCT (code_locs ls)` by metis_tac[clos_knownProofTheory.is_subseq_ALL_DISTINCT]
  (* clos_number *)
  \\ `ALL_DISTINCT (code_locs ls) /\
      set (code_locs ls) SUBSET EVEN /\
      EVERY ($<= N) (code_locs ls) /\
      EVERY ($> n) (code_locs ls)`
    by (qspecl_then [`N`,`XS`] assume_tac
             (CONJUNCT1 clos_numberProofTheory.renumber_code_locs_EVEN)
        \\ qspecl_then [`N`,`XS`] assume_tac
             clos_numberProofTheory.renumber_code_locs_list_distinct
        \\ fs [Abbr `N`, Abbr `XS`] \\ rfs [GSYM EVEN_MOD2]
        \\ qpat_x_assum `EVEN _ ==> _` mp_tac
        \\ impl_tac >- rw [GSYM ADD1, GSYM ADD_SUC, EVEN]
        \\ fs[SUBSET_DEF]
        \\ simp[SimpR``$==>``,IN_DEF]
        \\ rw[] \\ fs [EVERY_MEM])
  \\ imp_res_tac clos_numberProofTheory.renumber_code_locs_list_length
  (* chain_exps *)
  \\ `EVERY ($<= c.next_loc) (MAP FST (chain_exps c.next_loc es'')) /\
      (es'' <> [] ==>
      EVERY ($> (c.next_loc + LENGTH es''))
            (MAP FST (chain_exps c.next_loc es'')))`
    by fs [chain_exps_LE, chain_exps_GT]
  \\ Cases_on`es'' = []`
  >- (
    fs[code_locs_def, chain_exps_def]
    \\ imp_res_tac clos_callTheory.compile_LENGTH \\ fs[]
    \\ imp_res_tac clos_callTheory.compile_nil \\ fs[code_locs_def] )
  (* clos_call *)
  \\ reverse (Cases_on `c.do_call`) \\ fs [clos_callTheory.compile_def]
  \\ rveq \\ rfs [code_locs_def]
  \\ fs [EVERY_MEM, MEM_MAP, PULL_EXISTS]
  >-
   (rw [] \\ strip_tac \\ res_tac
    \\ fs[Abbr`N`])
  \\ pairarg_tac \\ fs [] \\ rveq
  \\ drule clos_callProofTheory.calls_code_locs_ALL_DISTINCT
  \\ simp [ALL_DISTINCT_APPEND, code_locs_def]
  \\ strip_tac \\ fs []
  \\ drule clos_callProofTheory.calls_code_locs_MEM \\ simp [code_locs_def]
  \\ strip_tac
  \\ imp_res_tac clos_callProofTheory.calls_add_SUC_code_locs
  \\ drule clos_callProofTheory.calls_ALL_DISTINCT \\ fs []
  \\ strip_tac
  \\ imp_res_tac clos_callTheory.calls_length \\ rfs []
  \\ fs [SUBSET_DEF, MEM_MAP, PULL_EXISTS, EXISTS_PROD, FORALL_PROD, Abbr `N`]
  \\ fs [SIMP_CONV(srw_ss())[IN_DEF]``x ∈ EVEN``]
  \\ rw [] \\ strip_tac \\ res_tac \\ res_tac \\ fs [] \\ rw []
  \\ fs[EVEN] \\ every_case_tac \\ fs[GSYM EVEN_MOD2]);

val compile_all_distinct_locs = Q.store_thm("compile_all_distinct_locs",
  `clos_to_bvl$compile c e = (c',p) ⇒ ALL_DISTINCT (MAP FST p)`,
  rw [compile_def]
  \\ rpt (pairarg_tac \\ fs [])
  \\ rw [ALL_DISTINCT_code_sort]
  \\ simp [compile_prog_code_locs, ALL_DISTINCT_APPEND]
  \\ imp_res_tac compile_common_distinct_locs \\ fs []
  \\ conj_tac
  >- simp [init_code_def, MEM_MAP, toAList_domain, FORALL_PROD, num_stubs_def,
           ALL_DISTINCT_MAP_FST_toAList, domain_fromList, LENGTH_FLAT,
           MAP_GENLIST, o_DEF, GSYM COUNT_LIST_GENLIST, SUM_COUNT_LIST,
           METIS_PROVE [FUN_EQ_THM] ``GENLIST (\x.x) = GENLIST I``]
  \\ simp[GSYM CONJ_ASSOC]
  \\ conj_tac
  >- (
    simp[GSYM MAP_MAP_o]
    \\ match_mp_tac ALL_DISTINCT_MAP_INJ
    \\ fs[ALL_DISTINCT_APPEND] )
  \\ conj_tac
  >- (
    simp[GSYM MAP_MAP_o]
    \\ match_mp_tac ALL_DISTINCT_MAP_INJ
    \\ fs[ALL_DISTINCT_APPEND]
    \\ fs[MAP_MAP_o])
  \\ conj_tac
  >- ( fs[ALL_DISTINCT_APPEND, GSYM MAP_MAP_o, MEM_MAP, PULL_EXISTS] )
  \\ simp[toAList_domain]
  \\ fs[ALL_DISTINCT_APPEND, MEM_MAP, PULL_EXISTS, MEM_FLAT, EXISTS_PROD, code_locs_map]
  \\ rw[]
  \\ imp_res_tac domain_init_code_lt_num_stubs
  \\ CCONTR_TAC \\ fs[]
  \\ fs[num_stubs_def]);

(* Initial state *)
val clos_init_def = Define`
  clos_init max_app s ⇔
  s.globals = [] ∧ s.refs = FEMPTY ∧ s.code = FEMPTY ∧ s.max_app = max_app`

val clos_init_with_clock = Q.store_thm("clos_init_with_clock[simp]",
  `clos_init max_app (s with clock := k) ⇔ clos_init max_app s`,
  EVAL_TAC);

(* actually, this can be made even stronger *)
val code_installed_fromAList_strong = Q.prove(`
  ∀ls ls'.
  ALL_DISTINCT(MAP FST ls) ∧
  IS_SUBLIST ls ls' ⇒
  code_installed ls' (fromAList ls)`,
  srw_tac[][code_installed_def,EVERY_MEM,FORALL_PROD,lookup_fromAList] >>
  metis_tac[ALOOKUP_ALL_DISTINCT_MEM,IS_SUBLIST_MEM])

(*
val compile_prog_stubs = Q.prove(`
  ∀ls ls' n m e new_e aux.
  MEM (n,m,e) ls ∧
  compile_prog max_app ls = ls' ∧
  compile_exps max_app [e] [] = (new_e,aux) ⇒
  MEM (n+(num_stubs max_app),m,HD new_e) ls' ∧
  IS_SUBLIST ls' aux`,
  Induct>>fs[FORALL_PROD,compile_prog_def]>>
  rw[]>>rpt(pairarg_tac>>fs[])>>
  imp_res_tac compile_exps_SING>>fs[]>>rveq>>fs[]>>
  res_tac>>fs[]>>
  Cases_on`aux`>>
  rfs[IS_SUBLIST]>>
  DISJ2_TAC>>
  metis_tac[IS_SUBLIST_APPEND2]);
*)

val evaluate_init1 = Q.prove(`
  ∀mapp2 mapp1 tot st.
  (∀n. n < mapp2 ⇒
  partial_app_fn_location mapp1 tot n ∈ domain st.code) ⇒
  bvlSem$evaluate (REVERSE
  (GENLIST (λprev. Op (Label (partial_app_fn_location mapp1 tot prev))[]) mapp2) ,[Unit],st) =
  (Rval (REVERSE
  (GENLIST (λprev. CodePtr (partial_app_fn_location mapp1 tot prev)) mapp2)),st)`,
  Induct>>fs[bvlSemTheory.evaluate_def]>>
  rw[]>>simp[GENLIST,REVERSE_SNOC]>>
  ONCE_REWRITE_TAC[CONS_APPEND]>>
  simp[bvlPropsTheory.evaluate_APPEND,bvlSemTheory.evaluate_def,do_app_def])

val evaluate_init = Q.prove(`
  ∀mapp2 mapp1 st.
  (∀m n. m < mapp2 ∧ n < m ⇒
  partial_app_fn_location mapp1 m n ∈ domain st.code) ⇒
  bvlSem$evaluate (REVERSE
  (FLAT (GENLIST (λtot. GENLIST
  (λprev. Op (Label (partial_app_fn_location mapp1 tot prev))[]) tot) mapp2)) ,[Unit],st) =
    (Rval (REVERSE
    (FLAT (GENLIST (λtot. GENLIST
    (λprev. CodePtr (partial_app_fn_location mapp1 tot prev)) tot) mapp2))),st)`,
  Induct>>fs[bvlSemTheory.evaluate_def]>>
  simp[GENLIST,FLAT_SNOC]>>
  simp[REVERSE_APPEND,bvlPropsTheory.evaluate_APPEND]>>
  rw[]>>
  `∀n. n < mapp2 ⇒ partial_app_fn_location mapp1 mapp2 n ∈ domain st.code` by fs[] >>
  drule evaluate_init1>>
  simp[]);

val FST_EQ_LEMMA = prove(
  ``FST x = y <=> ?y1. x = (y,y1)``,
  Cases_on `x` \\ fs []);

val evaluate_add_to_clock_io_events_mono_alt =
  closPropsTheory.evaluate_add_to_clock_io_events_mono
  |> SIMP_RULE std_ss [] |> CONJUNCT1 |> SPEC_ALL
  |> DISCH ``evaluate (es,env,s) = (res,s1:('c,'ffi) closSem$state)``
  |> SIMP_RULE std_ss [] |> GEN_ALL;

val evaluate_add_to_clock_io_events_mono_alt_bvl =
  bvlPropsTheory.evaluate_add_to_clock_io_events_mono
  |> SIMP_RULE std_ss [] |> SPEC_ALL
  |> DISCH ``evaluate (exps,env,s) = (res,s1:('a,'b) bvlSem$state)``
  |> SIMP_RULE std_ss [] |> GEN_ALL;

val eval_sim_def = Define `
  eval_sim ffi max_app code1 co1 cc1 es1 code2 co2 cc2 start rel =
    !k res1 s2.
      evaluate (es1,[],initial_state ffi max_app code1 co1 cc1 k) = (res1,s2) /\
      res1 <> Rerr (Rabort Rtype_error) /\
      rel code1 co1 cc1 es1 code2 co2 cc2 start ==>
      ?ck res2 t2.
        bvlSem$evaluate ([Call 0 (SOME start) []],[],
          initial_state ffi code2 co2 cc2 (k+ck)) = (res2,t2) /\
        result_rel (\x y. T) (\x y. T) res1 res2 /\ s2.ffi = t2.ffi`

val initial_state_with_clock = prove(
  ``(initial_state ffi ma code co cc k with clock :=
      (initial_state ffi ma code co cc k).clock + ck) =
    initial_state ffi ma code co cc (k + ck)``,
  fs [closSemTheory.initial_state_def]);

val initial_state_with_clock_bvl = prove(
  ``(initial_state ffi code co cc k with clock :=
      (initial_state ffi code co cc k).clock + ck) =
    initial_state ffi code co cc (k + ck) /\
    (bvlProps$inc_clock ck (initial_state ffi code co cc k) =
    initial_state ffi code co cc (k + ck))``,
  fs [bvlSemTheory.initial_state_def,inc_clock_def]);

val IMP_semantics_eq = Q.store_thm ("IMP_semantics_eq",
  `eval_sim ffi max_app code1 co1 cc1 es1 code2 co2 cc2 start rel /\
   closSem$semantics (ffi:'ffi ffi_state) max_app code1 co1 cc1 es1 <> Fail ==>
   rel code1 co1 cc1 es1 code2 co2 cc2 start ==>
   bvlSem$semantics ffi code2 co2 cc2 start =
   closSem$semantics ffi max_app code1 co1 cc1 es1`,
  rewrite_tac [GSYM AND_IMP_INTRO]
  \\ strip_tac
  \\ simp [Once closSemTheory.semantics_def]
  \\ IF_CASES_TAC \\ fs [] \\ disch_then kall_tac
  \\ strip_tac
  \\ once_rewrite_tac [EQ_SYM_EQ]
  \\ simp [Once closSemTheory.semantics_def] \\ rw []
  \\ DEEP_INTRO_TAC some_intro \\ simp []
  \\ conj_tac
  >-
   (gen_tac \\ strip_tac \\ rveq \\ simp []
    \\ simp [semantics_def]
    \\ IF_CASES_TAC \\ fs [] THEN1
     (first_x_assum (qspec_then `k'` mp_tac)
      \\ strip_tac
      \\ Cases_on `evaluate (es1,[],initial_state ffi max_app code1 co1 cc1 k')`
      \\ fs [eval_sim_def]
      \\ last_x_assum drule \\ fs []
      \\ CCONTR_TAC \\ fs[]
      \\ fs [FST_EQ_LEMMA]
      \\ qpat_x_assum `_ = (Rerr (Rabort Rtype_error),_)` assume_tac
      \\ drule evaluate_add_clock_initial_state \\ fs []
      \\ qexists_tac `ck` \\ fs []
      \\ CCONTR_TAC \\ fs [])
    \\ DEEP_INTRO_TAC some_intro \\ simp []
    \\ conj_tac
    >-
     (gen_tac \\ strip_tac \\ rveq \\ fs []
      \\ qabbrev_tac `st1 = initial_state ffi max_app code1 co1 cc1`
      \\ qabbrev_tac `st2 = initial_state ffi code2 co2 cc2`
      \\ drule evaluate_add_to_clock_io_events_mono_alt_bvl
      \\ qpat_x_assum `evaluate (es1,[],st1 k) = _` assume_tac
      \\ drule evaluate_add_to_clock_io_events_mono_alt
      \\ `!extra k. st1 k with clock := (st1 k).clock + extra = st1 (k + extra)`
            by (unabbrev_all_tac \\ fs [closSemTheory.initial_state_def])
      \\ `!extra k. st2 k with clock := (st2 k).clock + extra = st2 (k + extra)`
            by (unabbrev_all_tac \\ fs [initial_state_def])
      \\ fs []
      \\ ntac 2 (disch_then assume_tac)
      \\ fs [eval_sim_def]
      \\ first_x_assum drule
      \\ impl_tac >- metis_tac[FST]
      \\ strip_tac
      \\ qpat_x_assum `evaluate _ = (_,t2)` assume_tac
      \\ drule bvlPropsTheory.evaluate_add_clock
      \\ disch_then (qspec_then `k'` mp_tac)
      \\ impl_tac >- rpt(PURE_FULL_CASE_TAC >> fs[])
      \\ qpat_x_assum `evaluate _ = (_,s')` assume_tac
      \\ drule bvlPropsTheory.evaluate_add_clock
      \\ disch_then (qspec_then `ck + k` mp_tac)
      \\ impl_tac >- rpt(PURE_FULL_CASE_TAC >> fs[])
      \\ simp[inc_clock_def]
      \\ ntac 2 strip_tac
      \\ unabbrev_all_tac \\ fs[] \\ rveq
      \\ fs[state_component_equality]
      \\ rpt(PURE_FULL_CASE_TAC \\ fs[semanticPrimitivesPropsTheory.result_rel_def]))
    \\ fs [FST_EQ_LEMMA]
    \\ rveq \\ fs [eval_sim_def]
    \\ first_x_assum drule \\ fs []
    \\ impl_tac
    THEN1 (fs [FST_EQ_LEMMA] \\ strip_tac \\ fs [] \\ rfs [])
    \\ strip_tac
    \\ asm_exists_tac \\ fs []
    \\ every_case_tac \\ fs [] \\ rveq \\ fs []
    \\ Cases_on `r` \\ fs []
    \\ Cases_on `e` \\ fs [])
  \\ strip_tac
  \\ simp [bvlSemTheory.semantics_def]
  \\ IF_CASES_TAC \\ fs []
  THEN1
   (last_x_assum (qspec_then `k` assume_tac) \\ rfs [FST_EQ_LEMMA]
    \\ Cases_on `evaluate (es1,[],initial_state ffi max_app code1 co1 cc1 k)` \\ fs []
    \\ rveq \\ fs [eval_sim_def]
    \\ first_x_assum drule \\ fs []
    \\ CCONTR_TAC \\ fs []
    \\ qpat_x_assum `_ = (Rerr (Rabort Rtype_error),_)` assume_tac
    \\ drule evaluate_add_clock \\ fs []
    \\ qexists_tac `ck` \\ fs [initial_state_def,closSemTheory.initial_state_def]
    \\ CCONTR_TAC \\ fs [inc_clock_def] \\ rveq \\ fs [])
  \\ DEEP_INTRO_TAC some_intro \\ simp []
  \\ conj_tac
  THEN1
   (spose_not_then assume_tac \\ rw []
    \\ fsrw_tac [QUANT_INST_ss[pair_default_qp]] []
    \\ last_assum (qspec_then `k` mp_tac)
    \\ (fn g => subterm (fn tm => Cases_on`^(assert (can dest_prod o type_of) tm)` g) (#2 g))
    \\ strip_tac \\ fs[]
    \\ rveq \\ fs [eval_sim_def]
    \\ first_x_assum drule \\ fs []
    \\ CCONTR_TAC \\ fs []
    \\ pop_assum (assume_tac o GSYM)
    \\ qmatch_assum_rename_tac `evaluate (_,[],_ k) = (_,rr)`
    \\ first_x_assum(qspecl_then [`k`,`outcome`] assume_tac)
    \\ rfs[]
    \\ qpat_x_assum `evaluate _ = (r,s)` assume_tac
    \\ drule bvlPropsTheory.evaluate_add_clock
    \\ disch_then(qspec_then `ck` mp_tac)
    \\ impl_tac >- rpt(PURE_FULL_CASE_TAC >> fs[])
    \\ strip_tac \\ fs[inc_clock_def] \\ rveq
    \\ rpt(PURE_FULL_CASE_TAC \\ fs[semanticPrimitivesPropsTheory.result_rel_def]))
  \\ strip_tac
  \\ qmatch_abbrev_tac `build_lprefix_lub l1 = build_lprefix_lub l2`
  \\ `(lprefix_chain l1 ∧ lprefix_chain l2) ∧ equiv_lprefix_chain l1 l2`
     suffices_by metis_tac [build_lprefix_lub_thm,
                            lprefix_lub_new_chain,
                            unique_lprefix_lub]
  \\ conj_asm1_tac
  THEN1
   (unabbrev_all_tac
    \\ conj_tac
    \\ Ho_Rewrite.ONCE_REWRITE_TAC [GSYM o_DEF]
    \\ REWRITE_TAC [IMAGE_COMPOSE]
    \\ match_mp_tac prefix_chain_lprefix_chain
    \\ simp [prefix_chain_def, PULL_EXISTS]
    \\ qx_genl_tac [`k1`,`k2`]
    \\ qspecl_then [`k1`,`k2`] mp_tac LESS_EQ_CASES
    \\ strip_tac \\ fs [LESS_EQ_EXISTS] \\ rveq
    \\ metis_tac
        [bvlPropsTheory.evaluate_add_to_clock_io_events_mono,
         closPropsTheory.evaluate_add_to_clock_io_events_mono,
         initial_state_with_clock_bvl,
         initial_state_with_clock])
  \\ simp [equiv_lprefix_chain_thm]
  \\ unabbrev_all_tac \\ simp [PULL_EXISTS]
  \\ simp [LNTH_fromList, PULL_EXISTS, GSYM FORALL_AND_THM]
  \\ rpt gen_tac
  \\ Cases_on `evaluate (es1,[],initial_state ffi max_app code1 co1 cc1 k)`
  \\ rveq \\ fs [eval_sim_def]
  \\ first_x_assum drule \\ fs []
  \\ impl_tac
  THEN1 (CCONTR_TAC \\ fs [FST_EQ_LEMMA] \\ rfs [])
  \\ strip_tac \\ fs []
  \\ conj_tac \\ rw []
  THEN1 (qexists_tac `ck + k` \\ fs [])
  \\ qexists_tac `k` \\ fs []
  \\ qmatch_assum_abbrev_tac `_ < (LENGTH (_ ffi1))`
  \\ qsuff_tac `ffi1.io_events ≼ r.ffi.io_events`
  THEN1 (rw [] \\ fs [IS_PREFIX_APPEND] \\ simp [EL_APPEND1])
  \\ qunabbrev_tac `ffi1`
  \\ metis_tac
        [bvlPropsTheory.evaluate_add_to_clock_io_events_mono,
         closPropsTheory.evaluate_add_to_clock_io_events_mono,
         initial_state_with_clock_bvl,
         initial_state_with_clock,SND,ADD_SYM]);

val init_code_def = Define `
  init_code code1 code2 max_app <=>
    (∀n.
       n < max_app ⇒
       lookup (generic_app_fn_location n) code2 =
       SOME (n + 2,generate_generic_app max_app n)) ∧
    (∀tot prev.
       tot < max_app ∧ prev < tot ⇒
       lookup (partial_app_fn_location max_app tot prev) code2 =
       SOME (tot + 1 − prev,generate_partial_app_closure_fn tot prev)) ∧
    ∀name arity c.
      FLOOKUP code1 name = SOME (arity,c) ⇒
      ∃aux1 c2 aux2.
        compile_exps max_app [c] aux1 = ([c2],aux2) ∧
        lookup (name + num_stubs max_app) code2 = SOME (arity,c2) ∧
        code_installed aux2 code2`

val chain_installed_def = Define`
  chain_installed start (es:closLang$exp list) code ⇔
    (∀i. i < LENGTH es ⇒ closSem$find_code (start + i) ([]:closSem$v list) code =
         SOME ([], if i + 1 < LENGTH es
                     then Let None [EL i es] (Call None 0 (start + i + 1) [])
                     else EL i es))`;

val chain_installed_cons = Q.store_thm("chain_installed_cons",
  `chain_installed start (e::es) code ⇔
   find_code start ([]:closSem$v list) code = SOME ([], if es = [] then e else Let None [e] (Call None 0 (start+1) [])) ∧
   chain_installed (start+1) es code`,
  rw[chain_installed_def,ADD1,EQ_IMP_THM]
  >- (pop_assum(qspec_then`0`mp_tac) \\ rw[] \\ fs[])
  >- ( first_x_assum(qspec_then`i+1`mp_tac) \\ rw[EL_CONS,PRE_SUB1] )
  >- ( Cases_on`i` \\ fs[ADD1] \\ rw[] \\ fs[] ));

val chain_installed_SUBMAP = Q.store_thm("chain_installed_SUBMAP",
  `∀start es code code'.
   chain_installed start es code ∧ code ⊑ code' ⇒
   chain_installed start es code'`,
  Induct_on`es`
  \\ rw[chain_installed_def]
  \\ res_tac
  \\ fs[closSemTheory.find_code_def,CaseEq"option",CaseEq"prod"]
  \\ imp_res_tac FLOOKUP_SUBMAP);

(* TODO: move to closProps? *)

val find_code_SUBMAP = Q.store_thm("find_code_SUBMAP",
  `find_code dest vs code1 = SOME p ∧ code1 ⊑ code2 ⇒
   find_code dest vs code2 = SOME p`,
  rw[closSemTheory.find_code_def, CaseEq"option", pair_case_eq]
  \\ imp_res_tac FLOOKUP_SUBMAP);

val SUBMAP_rel_def = Define`
  SUBMAP_rel z1 z2 ⇔
    z2 = z1 with code := z2.code ∧ z1.code ⊑ z2.code ∧
    (∀n. DISJOINT (FDOM z2.code) (set (MAP FST (SND (SND (z1.compile_oracle n))))) ∧
         (∀m. m < n ⇒ DISJOINT (set (MAP FST (SND (SND (z1.compile_oracle m))))) (set (MAP FST (SND (SND (z1.compile_oracle n)))))))`;

val find_code_SUBMAP_rel = Q.store_thm("find_code_SUBMAP_rel",
  `find_code dest vs s1.code = SOME p ∧ SUBMAP_rel s1 s2 ⇒
   find_code dest vs s2.code = SOME p`,
  rw[SUBMAP_rel_def]
  \\ imp_res_tac find_code_SUBMAP);

val do_install_SUBMAP = Q.store_thm("do_install_SUBMAP",
  `do_install xs z1 = (r,s1) ∧ r ≠ Rerr (Rabort Rtype_error) ∧
   SUBMAP_rel z1 z2 ⇒
   ∃s2.
     do_install xs z2 = (r,s2) ∧
     SUBMAP_rel s1 s2`,
  rw[closSemTheory.do_install_def]
  \\ fs[CaseEq"list",CaseEq"option"] \\ rw[]
  \\ pairarg_tac \\ fs[]
  \\ pairarg_tac \\ fs[]
  \\ imp_res_tac SUBMAP_rel_def
  \\ imp_res_tac closSemTheory.state_component_equality
  \\ fs[] \\ rveq
  \\ reverse IF_CASES_TAC \\ fs[] \\ fs[]
  >- ( last_x_assum(qspec_then`0`mp_tac) \\ simp[] )
  \\ fs[bool_case_eq,CaseEq"option",CaseEq"prod"]
  \\ fs[SUBMAP_rel_def,closSemTheory.state_component_equality,shift_seq_def]
  \\ rveq \\ fs[]
  \\ (
    conj_tac >- (
      irule SUBMAP_mono_FUPDATE_LIST
      \\ fs[SUBMAP_FLOOKUP_EQN, FLOOKUP_DRESTRICT] ))
  \\ gen_tac
  \\ first_x_assum(qspec_then`n+1`mp_tac)
  \\ fs[IN_DISJOINT, FDOM_FUPDATE_LIST]
  \\ CCONTR_TAC \\ fs[]
  \\ first_x_assum(qspec_then`0`mp_tac) \\ simp[]
  \\ metis_tac[]);

val do_app_lemma_simp = prove(
  ``(exc_rel $= err1 err2 <=> err1 = err2) /\
    LIST_REL $= xs xs /\
    simple_state_rel $= SUBMAP_rel /\
    simple_val_rel $=``,
  rw [] \\ fs [LIST_REL_eq,simple_state_rel_def]
  THEN1
   (Cases_on `err1` \\ fs [semanticPrimitivesPropsTheory.exc_rel_def]
    \\ eq_tac \\ rw [])
  \\ fs [LIST_REL_eq,LIST_REL_OPT_REL_eq,simple_val_rel_def]
  \\ fs[SUBMAP_rel_def, closSemTheory.state_component_equality]
  \\ metis_tac[]);

val do_app_lemma =
  simple_val_rel_do_app
  |> Q.GENL [`vr`,`sr`]
  |> ISPEC ``(=):closSem$v -> closSem$v -> bool``
  |> ISPEC ``SUBMAP_rel``
  |> Q.INST [`opp`|->`op`,`s`|->`s1`,`t`|->`s2`,`ys`|->`xs`]
  |> SIMP_RULE std_ss [do_app_lemma_simp]

val do_app_SUBMAP_Rerr = Q.store_thm("do_app_SUBMAP_Rerr",
  `∀op xs s1 s2 r.
    do_app op xs s1 = Rerr r ∧
    SUBMAP_rel s1 s2 ⇒
    do_app op xs s2 = Rerr r`,
  rw [] \\ imp_res_tac do_app_lemma
  \\ pop_assum (assume_tac o SPEC_ALL) \\ rfs []);

val do_app_SUBMAP_Rval = Q.store_thm("do_app_SUBMAP_Rval",
  `∀op xs s1 s2 r z1.
    do_app op xs s1 = Rval (r,z1) ∧
    SUBMAP_rel s1 s2 ⇒
    ∃z2.
    do_app op xs s2 = Rval (r,z2) ∧
    SUBMAP_rel z1 z2`,
  rw [] \\ imp_res_tac do_app_lemma
  \\ pop_assum (assume_tac o SPEC_ALL) \\ rfs []);

val evaluate_code_SUBMAP = Q.store_thm("evaluate_code_SUBMAP",
  `(∀p x y (z1:('c, 'ffi)closSem$state) r s1 s2 (z2:('c,'ffi)closSem$state).
    p = (x,y,z1) ∧
    closSem$evaluate (x,y,z1) = (r,s1) ∧
    r ≠ Rerr (Rabort Rtype_error) ∧
    SUBMAP_rel z1 z2
    ⇒
    ∃s2.
    closSem$evaluate (x,y,z2) = (r,s2) ∧
    SUBMAP_rel s1 s2) ∧
   (∀w x y (z1:('c, 'ffi)closSem$state) r s1 s2 (z2:('c,'ffi)closSem$state).
    evaluate_app w x y z1 = (r,s1) ∧
    r ≠ Rerr (Rabort Rtype_error) ∧
    SUBMAP_rel z1 z2
    ⇒
    ∃s2.
    evaluate_app w x y z2 = (r,s2) ∧
    SUBMAP_rel s1 s2)`,
  ho_match_mp_tac closSemTheory.evaluate_ind
  \\ rw[closSemTheory.evaluate_def]
  \\ TRY (
    rename1`dest_closure`
    \\ imp_res_tac SUBMAP_rel_def
    \\ imp_res_tac closSemTheory.state_component_equality
    \\ fs[CaseEq"option",CaseEq"app_kind",CaseEq"bool",closSemTheory.dec_clock_def]
    \\ rveq \\ res_tac \\ fs[]
    \\ fs[SUBMAP_rel_def,closSemTheory.state_component_equality] \\ rw[] \\ rfs[]
    \\ fs[CaseEq"prod",CaseEq"semanticPrimitives$result",CaseEq"list",PULL_EXISTS]
    \\ rveq \\ fsrw_tac[DNF_ss][] \\ rfs[]
    \\ fs[GSYM CONJ_ASSOC]
    \\ qmatch_goalsub_abbrev_tac`evaluate (_,_,ss)`
    \\ fs[AND_IMP_INTRO]
    \\ last_x_assum(qspec_then`ss`(fn th => mp_tac th \\ impl_tac >- fs[Abbr`ss`]))
    \\ strip_tac \\ fs[] \\ NO_TAC )
  \\ TRY (
       fs[closSemTheory.evaluate_def,
          bool_case_eq,
          CaseEq"prod", CaseEq"option", CaseEq"list",
          CaseEq"semanticPrimitives$result",
          CaseEq"app_kind",
          CaseEq"error_result",
          closSemTheory.dec_clock_def]
    \\ rw[]
    \\ fs[PULL_EXISTS]
    \\ TRY (fs[closSemTheory.state_component_equality,SUBMAP_rel_def] \\
            HINT_EXISTS_TAC \\ fs[] \\ NO_TAC)
    \\ res_tac \\ fs[]
    \\ rpt(qpat_x_assum`(_,_) = _`(assume_tac o SYM) \\ fs[])
    \\ res_tac \\ fs[]
    \\ fs[CaseEq"prod", CaseEq"option", bool_case_eq, PULL_EXISTS]
    \\ rveq \\ fs[] \\ rfs[]
    \\ fsrw_tac[DNF_ss][]
    \\ imp_res_tac find_code_SUBMAP_rel \\ fs[]
    \\ qmatch_goalsub_abbrev_tac`evaluate (_,_,ss)`
    \\ TRY(last_x_assum(qspec_then`ss`mp_tac) \\ simp[Abbr`ss`]
           \\ strip_tac \\ fs[SUBMAP_rel_def,closSemTheory.state_component_equality]
           \\ rfs[]
           \\ HINT_EXISTS_TAC \\ fs[]
           \\ first_x_assum(CHANGED_TAC o SUBST1_TAC o SYM)
           \\ rpt(AP_TERM_TAC ORELSE AP_THM_TAC)
           \\ fs[closSemTheory.state_component_equality]
           \\ NO_TAC)
    \\ TRY(first_x_assum(qspec_then`ss`mp_tac) \\ simp[Abbr`ss`]
           \\ strip_tac \\ fs[SUBMAP_rel_def,closSemTheory.state_component_equality]
           \\ rfs[]
           \\ HINT_EXISTS_TAC \\ fs[]
           \\ first_x_assum(CHANGED_TAC o SUBST1_TAC o SYM)
           \\ rpt(AP_TERM_TAC ORELSE AP_THM_TAC)
           \\ fs[closSemTheory.state_component_equality]
           \\ NO_TAC)
    \\ NO_TAC)
    (* only Install and do_app *)
  \\ fs[CaseEq"option",CaseEq"prod",CaseEq"semanticPrimitives$result",PULL_EXISTS] \\ fs[]
  \\ rveq \\ fs[] \\ res_tac \\ fs[]
  \\ Cases_on`op = Install`
  \\ fs[CaseEq"prod",CaseEq"semanticPrimitives$result",PULL_EXISTS]
  \\ rveq \\ fs[]
  \\ TRY (
    drule (GEN_ALL do_install_SUBMAP)
    \\ simp[]
    \\ disch_then drule
    \\ rw[] \\ fs[]
    \\ NO_TAC )
  \\ imp_res_tac do_app_SUBMAP_Rval
  \\ fs[]
  \\ imp_res_tac do_app_SUBMAP_Rerr);

(* -- *)

val chain_installed_thm = Q.store_thm("chain_installed_thm",
  `∀es start. ∃e. ∀st code res st'.
   chain_installed start es st.code ∧
   closSem$evaluate (es,[],st) = (res,st') ∧
   0 < LENGTH es
   ⇒
   ∃k res1 st1.
   find_code start ([]:closSem$v list) st.code = SOME ([],e) ∧
   closSem$evaluate ([e],[],st with <| clock := st.clock + k |>) = (res1,st1) ∧
   result_rel (λx y. T) (λx y. T) res1 res ∧ st'.ffi = st1.ffi (*∧
   (every_Fn_vs_NONE es ⇒ every_Fn_vs_NONE [e])*)`,
  Induct >- rw[]
  \\ rw[chain_installed_cons]
  >- (
    qexists_tac`h` \\ rw[]
    \\ qexists_tac`0` \\ rw[] )
  \\ qmatch_goalsub_abbrev_tac`ee = _`
  \\ qexists_tac`ee` \\ rw[Abbr`ee`]
  \\ rw[closSemTheory.evaluate_def]
  \\ qhdtm_x_assum`evaluate`mp_tac
  \\ simp[Once closPropsTheory.evaluate_CONS]
  \\ simp[pair_case_eq] \\ strip_tac
  \\ Cases_on`evaluate (es,[],s2)` \\ fs[ADD1]
  \\ rename1`evaluate ([h],_,_) = (res1,_)`
  \\ Cases_on`res1 = Rerr(Rabort(Rtimeout_error))` \\ fs[]
  >- ( rveq \\ fs[] \\ qexists_tac`0` \\ simp[] \\ simp[Once every_Fn_vs_NONE_EVERY])
  \\ imp_res_tac closPropsTheory.evaluate_mono
  \\ imp_res_tac chain_installed_SUBMAP
  \\ first_x_assum(qspec_then`start+1`strip_assume_tac)
  \\ first_x_assum(first_assum o mp_then (Pat`closSem$evaluate`) mp_tac)
  \\ simp[]
  \\ impl_tac >- (CCONTR_TAC \\ fs[])
  \\ strip_tac
  \\ qexists_tac`k+1`
  \\ first_x_assum(mp_then Any drule closPropsTheory.evaluate_add_clock)
  \\ disch_then(qspec_then`k+1`mp_tac) \\ rw[]
  \\ fs[closSemTheory.dec_clock_def]
  \\ simp[Once every_Fn_vs_NONE_EVERY]
  \\ CASE_TAC \\ fs[] \\ rveq \\ fs[]
  \\ rename1`result_rel _ _ tres`
  \\ Cases_on`tres` \\ fs[] \\ rveq \\ fs[] \\ rveq \\ fs[]);

(* TODO: move to clos_annotate(Proof) *)
val compile_append = Q.store_thm("compile_append",
  `clos_annotate$compile (p1 ++ p2) = compile p1 ++ compile p2`,
  rw[clos_annotateTheory.compile_def]);

(*
val compile_prog_append = Q.store_thm("compile_prog_append",
  `∀max_app l1 l2.
     compile_prog max_app (l1 ++ l2) =
     compile_prog max_app l1 ++ compile_prog max_app l2`,
  recInduct compile_prog_ind
  \\ rw[compile_prog_def]
  \\ pairarg_tac \\ fs[]);
*)

val chain_installed_chain_exps = Q.store_thm("chain_installed_chain_exps",
  `∀start es. chain_installed start es (alist_to_fmap (chain_exps start es))`,
  recInduct chain_exps_ind
  \\ rw[chain_exps_def, chain_installed_def]
  >- rw[closSemTheory.find_code_def, FLOOKUP_UPDATE]
  \\ qmatch_assum_rename_tac`z < _`
  \\ Cases_on`z=0` \\ fs[]
  >- ( rw[closSemTheory.find_code_def, FLOOKUP_UPDATE] )
  \\ first_x_assum(qspec_then`z-1`mp_tac)
  \\ fs[ADD1]
  \\ rw[closSemTheory.find_code_def, FLOOKUP_UPDATE] \\ fs[]
  \\ fs[EL_CONS, PRE_SUB1]);

val chain_exps_semantics = Q.store_thm("chain_exps_semantics",
  `semantics ffi max_app code co cc es ≠ Fail ∧ (* es ≠ [] ∧*)
   DISJOINT (IMAGE ((+)start) (count (LENGTH es))) (FDOM code) ∧
   (∀n. DISJOINT (FDOM code) (set (MAP FST (SND (SND (co n))))) ∧
        DISJOINT (IMAGE ((+)start) (count (LENGTH es))) (set (MAP FST (SND (SND (co n))))) ∧
        ∀m. m < n ⇒ DISJOINT (set (MAP FST (SND (SND (co m))))) (set (MAP FST (SND (SND (co n))))))
  ⇒
   ∃e.
   semantics ffi max_app (alist_to_fmap (chain_exps start es) ⊌ code) co cc [e] =
   semantics ffi max_app code co cc es ∧
   ALOOKUP (chain_exps start es) start = SOME (0,e)`,
  rw[]
  \\ reverse(Cases_on`0 < LENGTH es`)
  >- (
    fs[chain_exps_def]
    \\ fs[closSemTheory.semantics_def]
    \\ fs[closSemTheory.evaluate_def]
    \\ fs[closSemTheory.do_app_def]
    \\ DEEP_INTRO_TAC some_intro \\ rw[]
    \\ EVAL_TAC )
  \\`∃e.  eval_sim ffi max_app code co cc es (alist_to_fmap (chain_exps start es) ⊌ code) co cc [e]
            (K (K (K (K (K (K (K (K T)))))))) F ∧
          (ALOOKUP (chain_exps start es) start  = SOME (0,e))`
  by (
    rw[closPropsTheory.eval_sim_def]
    \\ qspecl_then[`es`,`start`]strip_assume_tac
       (chain_installed_thm |> INST_TYPE [alpha|->beta,beta|->alpha])
    \\ qexists_tac`e`
    \\ reverse conj_tac
    >- (
      first_x_assum(qspec_then`ARB with code := alist_to_fmap(chain_exps start es)`mp_tac)
      \\ simp[chain_installed_chain_exps]
      \\ srw_tac[QI_ss][]
      \\ Cases_on`LENGTH es` \\ fs[]
      \\ fs[closSemTheory.find_code_def, CaseEq"option", CaseEq"prod"])
    \\ rw[]
    \\ first_assum(mp_then(Pat`closSem$evaluate`)mp_tac (CONJUNCT1 evaluate_code_SUBMAP))
    \\ simp[]
    \\ qmatch_goalsub_abbrev_tac`([e],_,ss2 _)`
    \\ disch_then(qspec_then`ss2 k`mp_tac)
    \\ impl_tac
    >- (
      simp[Abbr`ss2`,SUBMAP_rel_def,closSemTheory.state_component_equality,closSemTheory.initial_state_def]
      \\ `es <> []` by (strip_tac \\ fs[])
      \\ simp[MAP_FST_chain_exps]
      \\ conj_tac
      >- (
        irule SUBMAP_FUNION
        \\ simp[FDOM_alist_to_fmap, MAP_FST_chain_exps]
        \\ simp[LIST_TO_SET_MAP, COUNT_LIST_COUNT]
        \\ fs[DISJOINT_SYM] )
      \\ fs[LIST_TO_SET_MAP, COUNT_LIST_COUNT] )
    \\ strip_tac
    \\ first_x_assum(first_assum o mp_then Any mp_tac)
    \\ simp[]
    \\ impl_tac
    >- (
      fs[Abbr`ss2`, closSemTheory.initial_state_def]
      \\ match_mp_tac chain_installed_SUBMAP
      \\ qexists_tac`alist_to_fmap (chain_exps start es)`
      \\ simp[chain_installed_chain_exps]
      \\ irule SUBMAP_FUNION \\ fs[] )
    \\ strip_tac
    \\ `(ss2 k).clock = k` by simp[Abbr`ss2`,closSemTheory.initial_state_def]
    \\ qexists_tac`k'`
    \\ fs[]
    \\ `ss2 k with clock := k + k' = ss2 (k + k')` by simp[Abbr`ss2`,closSemTheory.initial_state_def]
    \\ fs[]
    \\ fs[SUBMAP_rel_def, closSemTheory.state_component_equality]
    \\ Cases_on`res1'` \\ fs[]
    \\ Cases_on`e'` \\ fs[] )
  \\ drule (GEN_ALL closPropsTheory.IMP_semantics_eq)
  \\ simp[]
  \\ metis_tac[]);

val chain_exps_semantics_call = Q.store_thm("chain_exps_semantics_call",
  `semantics ffi max_app code co cc es ≠ Fail ∧
   DISJOINT (IMAGE ((+)start) (count (LENGTH es))) (FDOM code) ∧
   (∀n. DISJOINT (FDOM code) (set (MAP FST (SND (SND (co n))))) ∧
        DISJOINT (IMAGE ((+)start) (count (LENGTH es))) (set (MAP FST (SND (SND (co n))))) ∧
        ∀m. m < n ⇒ DISJOINT (set (MAP FST (SND (SND (co m))))) (set (MAP FST (SND (SND (co n))))))
  ⇒
   semantics ffi max_app (alist_to_fmap (chain_exps start es) ⊌ code) co cc ([Call None 0 start []]) =
   semantics ffi max_app code co cc es`,
  rw[]
  (*
  >- (
    rw[closSemTheory.semantics_def, closSemTheory.evaluate_def, chain_exps_def] )
  *)
  \\ drule chain_exps_semantics
  \\ simp[] \\ strip_tac
  \\ first_x_assum(CHANGED_TAC o SUBST1_TAC o GSYM)
  \\ irule closPropsTheory.IMP_semantics_eq_no_fail
  \\ qexists_tac`(K (K (K (K (K (K (K (K T))))))))`
  \\ simp[]
  \\ rw[closPropsTheory.eval_sim_def]
  \\ rw[closSemTheory.evaluate_def]
  \\ rw[Once closSemTheory.initial_state_def]
  \\ rw[closSemTheory.find_code_def]
  \\ rw[FLOOKUP_FUNION]
  \\ rw[Once closSemTheory.initial_state_def]
  \\ qexists_tac`1`
  \\ rw[closSemTheory.dec_clock_def]
  \\ fs[closSemTheory.initial_state_def]);

(*
val ALOOKUP_compile_prog_main = Q.store_thm("ALOOKUP_compile_prog_main",
  `∀max_app prog n a e.
   ALOOKUP prog n = SOME (a,e) ∧ ¬MEM n (code_locs (MAP (SND o SND) prog))
   ⇒
   ALOOKUP (compile_prog max_app prog) (n + num_stubs max_app) =
     SOME (a, HD(FST(compile_exps max_app [e] [])))`,
  recInduct compile_prog_ind
  \\ rw[compile_prog_def]
  \\ pairarg_tac \\ fs[]
  \\ reverse(fs[CaseEq"bool"] \\ rw[])
  >- (
    first_x_assum drule
    \\ rw[ALOOKUP_APPEND]
    \\ reverse CASE_TAC
    >- (
      imp_res_tac ALOOKUP_MEM
      \\ fs[MEM_MAP] \\ rw[] )
    \\ CASE_TAC
    >- (
      first_x_assum match_mp_tac
      \\ fs[Once code_locs_cons] )
    \\ imp_res_tac ALOOKUP_MEM
    \\ qspec_then`[]`mp_tac(CONV_RULE(RESORT_FORALL_CONV(sort_vars["aux"]))compile_exps_code_locs)
    \\ simp[]
    \\ disch_then drule
    \\ disch_then(assume_tac o Q.AP_TERM`combin$C MEM`)
    \\ fs[MEM_MAP,FUN_EQ_THM]
    \\ fsrw_tac[DNF_ss][EQ_IMP_THM]
    \\ first_x_assum drule
    \\ simp[]
    \\ rw[]
    \\ fs[Once code_locs_cons] \\ fs[]
    \\ fs[code_locs_def] )
  \\ imp_res_tac compile_exps_SING \\ fs[]);

val ALOOKUP_compile_prog_aux = Q.store_thm("ALOOKUP_compile_prog_aux",
  `∀max_app prog start a e r aux.
   ALOOKUP prog start = SOME (a,e) ∧
   ALL_DISTINCT (MAP FST (compile_prog max_app prog)) ∧
   compile_exps max_app [e] [] = (r,aux) ⇒
   code_installed aux (fromAList (compile_prog max_app prog))`,
  rw[]
  \\ irule code_installed_fromAList_strong
  \\ rw[]
  \\ qhdtm_x_assum`ALL_DISTINCT`kall_tac
  \\ rpt(pop_assum mp_tac)
  \\ map_every qid_spec_tac[`start`,`r`,`aux`,`e`,`a`,`prog`,`max_app`]
  \\ recInduct compile_prog_ind
  \\ rw[compile_prog_def]
  \\ pairarg_tac \\ fs[]
  \\ fs[CaseEq"bool"] \\ rw[] \\ fs[] \\ rw[]
  \\ res_tac
  \\ metis_tac[IS_SUBLIST_APPEND, APPEND_ASSOC]);
*)

val compile_inc_def = Define`
  compile_inc c cc =
  ((if c.do_mti then pure_cc (clos_mtiProof$compile_inc c.max_app) else I)
    (state_cc (ignore_table renumber_code_locs)
      (state_cc (case c.known_conf of NONE => CURRY I | SOME kcfg => clos_knownProof$compile_inc kcfg)
        (state_cc (if c.do_call then clos_callProof$compile_inc else CURRY I)
          (pure_cc clos_annotateProof$compile_inc cc)))))`;

(* TODO: move *)

val make_even_def = Define`
  make_even n = if EVEN n then n else n+1`;

val mcompile_length = Q.store_thm("mcompile_length[simp]",
  `LENGTH (clos_mti$compile do_mti max_app es) = LENGTH es`,
  Cases_on`do_mti` \\ rw[clos_mtiTheory.compile_def, clos_mtiTheory.intro_multi_length]);

val every_Fn_SOME_APPEND = Q.store_thm("every_Fn_SOME_APPEND[simp]",
  `every_Fn_SOME (l1 ++ l2) ⇔ every_Fn_SOME l1 ∧ every_Fn_SOME l2`,
  once_rewrite_tac[every_Fn_SOME_EVERY] \\ rw[]);

val every_Fn_vs_NONE_APPEND = Q.store_thm("every_Fn_vs_NONE_APPEND[simp]",
  `every_Fn_vs_NONE (l1 ++ l2) ⇔ every_Fn_vs_NONE l1 ∧ every_Fn_vs_NONE l2`,
  once_rewrite_tac[every_Fn_vs_NONE_EVERY] \\ rw[]);

val every_Fn_SOME_mk_Ticks = Q.store_thm("every_Fn_SOME_mk_Ticks",
  `∀t tc n e. every_Fn_SOME [e] ⇒ every_Fn_SOME [mk_Ticks t tc n e]`,
  recInduct clos_knownTheory.mk_Ticks_ind
  \\ rw[Once clos_knownTheory.mk_Ticks_def]
  \\ rw[Once clos_knownTheory.mk_Ticks_def]
  \\ fs[]
  \\ rw[Once clos_knownTheory.mk_Ticks_def]);

val every_Fn_vs_NONE_mk_Ticks = Q.store_thm("every_Fn_vs_NONE_mk_Ticks",
  `∀t tc n e. every_Fn_vs_NONE [e] ⇒ every_Fn_vs_NONE [mk_Ticks t tc n e]`,
  recInduct clos_knownTheory.mk_Ticks_ind
  \\ rw[Once clos_knownTheory.mk_Ticks_def]
  \\ rw[Once clos_knownTheory.mk_Ticks_def]
  \\ fs[]
  \\ rw[Once clos_knownTheory.mk_Ticks_def]);

val val_approx_every_Fn_SOME_def = tDefine"val_approx_every_Fn_SOME"`
  (val_approx_every_Fn_SOME (Tuple _ vs) ⇔ EVERY val_approx_every_Fn_SOME vs) ∧
  (val_approx_every_Fn_SOME (Clos _ _ b _) ⇔ every_Fn_SOME [b]) ∧
  (val_approx_every_Fn_SOME _ ⇔ T)`
(wf_rel_tac`measure val_approx_size`
 \\ gen_tac \\ Induct \\ EVAL_TAC
 \\ rw[] \\ res_tac \\ rw[]);
val _ = export_rewrites["val_approx_every_Fn_SOME_def"];

val val_approx_every_Fn_SOME_merge = Q.store_thm("val_approx_every_Fn_SOME_merge",
  `∀a b. val_approx_every_Fn_SOME a ∧ val_approx_every_Fn_SOME b ⇒
     val_approx_every_Fn_SOME (merge a b)`,
  recInduct clos_knownTheory.merge_ind
  \\ rw[clos_knownTheory.merge_def]
  \\ fs[EVERY_MEM,MAP2_MAP,MEM_MAP]
  \\ rw[]
  \\ imp_res_tac MEM_ZIP_MEM_MAP
  \\ rfs[UNCURRY]);

val decide_inline_every_Fn_SOME = Q.store_thm("decide_inline_every_Fn_SOME",
  `val_approx_every_Fn_SOME b ∧ decide_inline a b c d = inlD_LetInline e ⇒
   every_Fn_SOME [e]`,
  rw[clos_knownTheory.decide_inline_def,CaseEq"val_approx",CaseEq"bool"]
  \\ fs[]);

val globals_approx_every_Fn_SOME_def = Define`
  globals_approx_every_Fn_SOME g =
    (∀c d. lookup c g = SOME d ⇒ val_approx_every_Fn_SOME d)`;

val known_op_every_Fn_SOME = Q.store_thm("known_op_every_Fn_SOME",
  `known_op op x y = (a,b) ∧
  EVERY val_approx_every_Fn_SOME x ∧
  globals_approx_every_Fn_SOME y
   ⇒ val_approx_every_Fn_SOME a ∧
     globals_approx_every_Fn_SOME b`,
  Cases_on`op` \\ fs[clos_knownTheory.known_op_def]
  \\ rw[] \\ fsrw_tac[ETA_ss][CaseEq"prod",CaseEq"option",NULL_EQ,CaseEq"list",CaseEq"val_approx",CaseEq"bool"]
  \\ rw[] \\ fs[]
  \\ fs[EVERY_MEM,MEM_EL,PULL_EXISTS,globals_approx_every_Fn_SOME_def,lookup_insert]
  \\ rw[] \\ fs[]
  \\ TRY ( match_mp_tac val_approx_every_Fn_SOME_merge \\ fs[] )
  \\ last_x_assum match_mp_tac \\ fs[]
  \\ TRY asm_exists_tac \\ fs[]
  \\ intLib.COOPER_TAC);

val known_every_Fn_SOME = Q.store_thm("known_every_Fn_SOME",
  `∀a b c d.
    every_Fn_SOME b ∧ EVERY val_approx_every_Fn_SOME c ∧
    globals_approx_every_Fn_SOME d
    ⇒
    every_Fn_SOME (MAP FST (FST (known a b c d))) ∧
    EVERY val_approx_every_Fn_SOME (MAP SND (FST (known a b c d))) ∧
    globals_approx_every_Fn_SOME (SND (known a b c d))`,
  recInduct clos_knownTheory.known_ind
  \\ rw[clos_knownTheory.known_def]
  \\ rpt(pairarg_tac \\ fs[])
  \\ imp_res_tac clos_knownTheory.known_sing_EQ_E \\ rveq \\ fs[]
  \\ TRY ( match_mp_tac val_approx_every_Fn_SOME_merge \\ fs[] )
  \\ fs[IS_SOME_EXISTS, any_el_ALT, EVERY_REPLICATE] \\ rveq \\ fs[]
  >- ( rw[] \\ fs[EVERY_MEM,MEM_EL,PULL_EXISTS] )
  >- ( CASE_TAC \\ fs[] \\ CASE_TAC \\ fs[] )
  >- ( imp_res_tac known_op_every_Fn_SOME \\ fs[EVERY_REVERSE])
  >- ( imp_res_tac known_op_every_Fn_SOME \\ fs[EVERY_REVERSE])
  >- (
    TOP_CASE_TAC \\ fs[]
    \\ pairarg_tac \\ fs[]
    \\ pairarg_tac \\ fs[]
    \\ CASE_TAC \\ fs[]
    \\ TRY(reverse conj_tac >- fs[Once every_Fn_SOME_EVERY])
    \\ match_mp_tac every_Fn_SOME_mk_Ticks
    \\ imp_res_tac clos_knownTheory.known_sing_EQ_E
    \\ fs[] \\ rveq
    \\ imp_res_tac decide_inline_every_Fn_SOME
    \\ fs[] )
  >- (
    TOP_CASE_TAC \\ fs[]
    \\ pairarg_tac \\ fs[]
    \\ pairarg_tac \\ fs[]
    \\ CASE_TAC \\ fs[]
    \\ imp_res_tac clos_knownTheory.known_sing_EQ_E
    \\ fs[] \\ rveq
    \\ imp_res_tac decide_inline_every_Fn_SOME
    \\ fs[] )
  >- (
    TOP_CASE_TAC \\ fs[]
    \\ pairarg_tac \\ fs[]
    \\ pairarg_tac \\ fs[]
    \\ CASE_TAC \\ fs[])
  >- (
    rw[clos_knownTheory.clos_approx_def]
    \\ CASE_TAC \\ fs[] )
  >- cheat
  >- cheat
  >- cheat);

val val_approx_every_Fn_vs_NONE_def = tDefine"val_approx_every_Fn_vs_NONE"`
  (val_approx_every_Fn_vs_NONE (Tuple _ vs) ⇔ EVERY val_approx_every_Fn_vs_NONE vs) ∧
  (val_approx_every_Fn_vs_NONE (Clos _ _ b _) ⇔ every_Fn_vs_NONE [b]) ∧
  (val_approx_every_Fn_vs_NONE _ ⇔ T)`
(wf_rel_tac`measure val_approx_size`
 \\ gen_tac \\ Induct \\ EVAL_TAC
 \\ rw[] \\ res_tac \\ rw[]);
val _ = export_rewrites["val_approx_every_Fn_vs_NONE_def"];

val val_approx_every_Fn_vs_NONE_merge = Q.store_thm("val_approx_every_Fn_vs_NONE_merge",
  `∀a b. val_approx_every_Fn_vs_NONE a ∧ val_approx_every_Fn_vs_NONE b ⇒
     val_approx_every_Fn_vs_NONE (merge a b)`,
  recInduct clos_knownTheory.merge_ind
  \\ rw[clos_knownTheory.merge_def]
  \\ fs[EVERY_MEM,MAP2_MAP,MEM_MAP]
  \\ rw[]
  \\ imp_res_tac MEM_ZIP_MEM_MAP
  \\ rfs[UNCURRY]);

val decide_inline_every_Fn_vs_NONE = Q.store_thm("decide_inline_every_Fn_vs_NONE",
  `val_approx_every_Fn_vs_NONE b ∧ decide_inline a b c d = inlD_LetInline e ⇒
   every_Fn_vs_NONE [e]`,
  rw[clos_knownTheory.decide_inline_def,CaseEq"val_approx",CaseEq"bool"]
  \\ fs[]);

val globals_approx_every_Fn_vs_NONE_def = Define`
  globals_approx_every_Fn_vs_NONE g =
    (∀c d. lookup c g = SOME d ⇒ val_approx_every_Fn_vs_NONE d)`;

val known_op_every_Fn_vs_NONE = Q.store_thm("known_op_every_Fn_vs_NONE",
  `known_op op x y = (a,b) ∧
  EVERY val_approx_every_Fn_vs_NONE x ∧
  globals_approx_every_Fn_vs_NONE y
   ⇒ val_approx_every_Fn_vs_NONE a ∧
     globals_approx_every_Fn_vs_NONE b`,
  Cases_on`op` \\ fs[clos_knownTheory.known_op_def]
  \\ rw[] \\ fsrw_tac[ETA_ss][CaseEq"prod",CaseEq"option",NULL_EQ,CaseEq"list",CaseEq"val_approx",CaseEq"bool"]
  \\ rw[] \\ fs[]
  \\ fs[EVERY_MEM,MEM_EL,PULL_EXISTS,globals_approx_every_Fn_vs_NONE_def,lookup_insert]
  \\ rw[] \\ fs[]
  \\ TRY ( match_mp_tac val_approx_every_Fn_vs_NONE_merge \\ fs[] )
  \\ last_x_assum match_mp_tac \\ fs[]
  \\ TRY asm_exists_tac \\ fs[]
  \\ intLib.COOPER_TAC);

val known_every_Fn_vs_NONE = Q.store_thm("known_every_Fn_vs_NONE",
  `∀a b c d.
    every_Fn_vs_NONE b ∧ EVERY val_approx_every_Fn_vs_NONE c ∧
    globals_approx_every_Fn_vs_NONE d
    ⇒
    every_Fn_vs_NONE (MAP FST (FST (known a b c d))) ∧
    EVERY val_approx_every_Fn_vs_NONE (MAP SND (FST (known a b c d))) ∧
    globals_approx_every_Fn_vs_NONE (SND (known a b c d))`,
  recInduct clos_knownTheory.known_ind
  \\ rw[clos_knownTheory.known_def]
  \\ rpt(pairarg_tac \\ fs[])
  \\ imp_res_tac clos_knownTheory.known_sing_EQ_E \\ rveq \\ fs[]
  \\ TRY ( match_mp_tac val_approx_every_Fn_vs_NONE_merge \\ fs[] )
  \\ fs[IS_SOME_EXISTS, any_el_ALT, EVERY_REPLICATE] \\ rveq \\ fs[]
  >- ( rw[] \\ fs[EVERY_MEM,MEM_EL,PULL_EXISTS] )
  >- ( CASE_TAC \\ fs[] \\ CASE_TAC \\ fs[] )
  >- ( imp_res_tac known_op_every_Fn_vs_NONE \\ fs[EVERY_REVERSE])
  >- ( imp_res_tac known_op_every_Fn_vs_NONE \\ fs[EVERY_REVERSE])
  >- (
    TOP_CASE_TAC \\ fs[]
    \\ pairarg_tac \\ fs[]
    \\ pairarg_tac \\ fs[]
    \\ CASE_TAC \\ fs[]
    \\ TRY(reverse conj_tac >- fs[Once every_Fn_vs_NONE_EVERY])
    \\ match_mp_tac every_Fn_vs_NONE_mk_Ticks
    \\ imp_res_tac clos_knownTheory.known_sing_EQ_E
    \\ fs[] \\ rveq
    \\ imp_res_tac decide_inline_every_Fn_vs_NONE
    \\ fs[] )
  >- (
    TOP_CASE_TAC \\ fs[]
    \\ pairarg_tac \\ fs[]
    \\ pairarg_tac \\ fs[]
    \\ CASE_TAC \\ fs[]
    \\ imp_res_tac clos_knownTheory.known_sing_EQ_E
    \\ fs[] \\ rveq
    \\ imp_res_tac decide_inline_every_Fn_vs_NONE
    \\ fs[] )
  >- (
    TOP_CASE_TAC \\ fs[]
    \\ pairarg_tac \\ fs[]
    \\ pairarg_tac \\ fs[]
    \\ CASE_TAC \\ fs[])
  >- (
    rw[clos_knownTheory.clos_approx_def]
    \\ TOP_CASE_TAC \\ fs[]
    \\ TOP_CASE_TAC \\ fs[] )
  >- cheat
  >- cheat
  >- cheat);

val kcompile_csyntax_ok = Q.store_thm("kcompile_csyntax_ok",
  `clos_callProof$syntax_ok es  ∧
   (IS_SOME kc ⇒ globals_approx_every_Fn_SOME (THE kc).val_approx_spt ∧
                 globals_approx_every_Fn_vs_NONE (THE kc).val_approx_spt) ∧
   clos_known$compile kc es = (x,y)
  ⇒
   clos_callProof$syntax_ok y`,
  Cases_on`kc` \\ rw[clos_knownTheory.compile_def] \\ fs[]
  \\ pairarg_tac \\ fs[]
  \\ fs[clos_callProofTheory.syntax_ok_def]
  \\ imp_res_tac clos_knownProofTheory.known_code_locs
  \\ imp_res_tac clos_knownProofTheory.is_subseq_ALL_DISTINCT
  \\ fs[]
  \\ qhdtm_x_assum`known`mp_tac
  \\ specl_args_of_then``known``known_every_Fn_SOME mp_tac
  \\ specl_args_of_then``known``known_every_Fn_vs_NONE mp_tac
  \\ rw[] \\ fs[]);

val renumber_code_locs_fv1 = Q.store_thm("renumber_code_locs_fv1",
  `(∀n es v. LIST_REL (λe1 e2. ∀v. fv1 v e1 ⇔ fv1 v e2) (SND (renumber_code_locs_list n es)) es) ∧
   (∀n e v. fv1 v (SND (renumber_code_locs n e)) ⇔ fv1 v (e))`,
  HO_MATCH_MP_TAC clos_numberTheory.renumber_code_locs_ind
  \\ rw[clos_numberTheory.renumber_code_locs_def]
  \\ rpt(pairarg_tac \\ fs[])
  \\ fs[fv1_thm]
  \\ imp_res_tac clos_numberProofTheory.renumber_code_locs_list_length
  \\ fs[]
  \\ TRY(fs[fv_exists, EXISTS_MEM, MEM_EL, LIST_REL_EL_EQN, PULL_EXISTS] \\ metis_tac[])
  \\ fs[EXISTS_MEM, MEM_EL, LIST_REL_EL_EQN, PULL_EXISTS, UNCURRY, EL_MAP]
  \\ rw[EQ_IMP_THM] \\ rfs[EL_ZIP, EL_MAP]
  >- metis_tac[]
  \\ disj1_tac
  \\ asm_exists_tac
  \\ simp[EL_ZIP, EL_MAP]);

val renumber_code_locs_list_fv = Q.store_thm("renumber_code_locs_list_fv",
  `renumber_code_locs_list n es = (k,es') ⇒ fv x es' = fv x es`,
  qspecl_then[`n`,`es`]mp_tac(CONJUNCT1 renumber_code_locs_fv1)
  \\ rw[]
  \\ rw[fv_exists, EXISTS_MEM, MEM_EL]
  \\ fs[LIST_REL_EL_EQN, PULL_EXISTS]
  \\ metis_tac[]);

val syntax_ok_renumber_code_locs_list = Q.store_thm("syntax_ok_renumber_code_locs_list",
  `∀k es. clos_knownProof$syntax_ok es ⇒ clos_knownProof$syntax_ok (SND (renumber_code_locs_list k es))`,
  rw[clos_knownProofTheory.syntax_ok_def]
  \\ qspecl_then[`k`,`es`]mp_tac (CONJUNCT1 clos_numberProofTheory.renumber_code_locs_every_Fn_vs_NONE)
  \\ simp[] \\ strip_tac
  \\ Cases_on`renumber_code_locs_list k es`
  \\ qspecl_then[`k`,`es`]mp_tac (CONJUNCT1 clos_numberProofTheory.renumber_code_locs_esgc_free)
  \\ simp[] \\ strip_tac
  \\ imp_res_tac renumber_code_locs_list_fv
  \\ fs[clos_knownProofTheory.fv_max_def]);

val syntax_ok_renumber_code_locs = Q.store_thm("syntax_ok_renumber_code_locs",
  `∀k e. clos_knownProof$syntax_ok [e] ⇒ clos_knownProof$syntax_ok [SND (renumber_code_locs k e)]`,
  rw[clos_knownProofTheory.syntax_ok_def]
  \\ qspecl_then[`k`,`e`]mp_tac (CONJUNCT2 clos_numberProofTheory.renumber_code_locs_every_Fn_vs_NONE)
  \\ simp[] \\ strip_tac
  >- (
    Cases_on`renumber_code_locs k e`
    \\ qspecl_then[`k`,`e`]mp_tac (CONJUNCT2 clos_numberProofTheory.renumber_code_locs_esgc_free)
    \\ simp[] \\ strip_tac)
  \\ fs[renumber_code_locs_fv,clos_knownProofTheory.fv_max_def]);

val set_globals_SND_renumber_code_locs = Q.store_thm("set_globals_SND_renumber_code_locs",
  `set_globals (SND (renumber_code_locs x y)) = set_globals y`,
  metis_tac[clos_numberProofTheory.renumber_code_locs_elist_globals,PAIR]);

val syntax_oracle_ok_renumber_code_locs = Q.store_thm("syntax_oracle_ok_renumber_code_locs",
  `renumber_code_locs_list n es1 = (k,es2) ∧
   clos_knownProof$syntax_ok es1 ∧
   co_every_Fn_vs_NONE co1 ∧
   BAG_ALL_DISTINCT (elist_globals es1) ∧
   (∀n. SND (SND (co1 n)) = [] ∧ clos_knownProof$syntax_ok [FST (SND (co1 n))] ∧
        globals_approx_sgc_free (FST (SND (FST (co1 n)))) ∧
        BAG_ALL_DISTINCT (elist_globals (GENLIST (FST o SND o co1) n)) ∧
        BAG_DISJOINT (elist_globals es1) (elist_globals (GENLIST (FST o SND o co1) n)))
  ⇒
   syntax_oracle_ok es2 (state_co (ignore_table renumber_code_locs) co1)`,
  simp[clos_knownProofTheory.syntax_oracle_ok_def]
  \\ strip_tac
  \\ simp[backendPropsTheory.SND_state_co]
  \\ conj_asm1_tac
  >- metis_tac[syntax_ok_renumber_code_locs_list,SND]
  \\ conj_asm1_tac
  >- (
    fs[clos_knownProofTheory.co_every_Fn_vs_NONE_def,
       backendPropsTheory.SND_state_co]
    \\ rpt gen_tac
    \\ specl_args_of_then``ignore_table``(Q.GENL[`f`,`st`,`p`]FST_SND_ignore_table) mp_tac
    \\ specl_args_of_then``ignore_table``(Q.GENL[`f`,`st`,`p`]SND_SND_ignore_table) mp_tac
    \\ ntac 3 strip_tac \\ fs[] \\ rveq
    \\ simp[clos_numberProofTheory.renumber_code_locs_every_Fn_vs_NONE]
    \\ metis_tac[PAIR] )
  \\ reverse conj_asm2_tac
  >- (
    reverse conj_asm2_tac
    >- (
      qx_gen_tac`m`
      \\ specl_args_of_then``ignore_table``(Q.GENL[`f`,`st`,`p`]FST_SND_ignore_table) mp_tac
      \\ specl_args_of_then``ignore_table``(Q.GENL[`f`,`st`,`p`]SND_SND_ignore_table) mp_tac
      \\ simp[]
      \\ ntac 2 strip_tac
      \\ qspecl_then[`FST(FST (co1 m))`,`FST (SND (co1 m))`]mp_tac syntax_ok_renumber_code_locs
      \\ simp[] )
    \\ simp[clos_knownProofTheory.unique_set_globals_def]
    \\ simp[clos_knownProofTheory.first_n_exps_def, o_DEF,
            backendPropsTheory.SND_state_co,
            FST_SND_ignore_table]
    \\ fs[SND_SND_ignore_table, FST_SND_ignore_table]
    \\ simp[elist_globals_append, BAG_ALL_DISTINCT_BAG_UNION]
    \\ imp_res_tac clos_numberProofTheory.renumber_code_locs_elist_globals \\ fs[]
    \\ simp[Once elist_globals_FOLDR, MAP_GENLIST, o_DEF]
    \\ simp[set_globals_SND_renumber_code_locs]
    \\ simp[GSYM o_DEF, GSYM MAP_GENLIST, GSYM elist_globals_FOLDR]
    \\ simp[MAP_GENLIST]
    \\ qmatch_goalsub_abbrev_tac`BAG_DISJOINT b1`
    \\ simp[Once elist_globals_FOLDR, MAP_GENLIST, o_DEF]
    \\ simp[set_globals_SND_renumber_code_locs]
    \\ simp[Q.ISPEC`set_globals`(GSYM o_DEF), GSYM MAP_GENLIST, GSYM elist_globals_FOLDR]
    \\ fs[o_DEF] )
  \\ simp[clos_knownProofTheory.oracle_state_sgc_free_def,
         backendPropsTheory.FST_state_co]);

val collect_apps_fv1 = Q.store_thm("collect_apps_fv1",
  `∀x y z v. fv v (FST (collect_apps x y z)) ∨ fv1 v (SND (collect_apps x y z)) ⇔ fv v y ∨ fv1 v z`,
  recInduct clos_mtiTheory.collect_apps_ind
  \\ rw[clos_mtiTheory.collect_apps_def]
  \\ rw[fv1_thm]
  \\ metis_tac[]);

val collect_args_fv1 = Q.store_thm("collect_args_fv1",
  `∀m n e n' e' v.
      (collect_args m n e = (n',e')) ⇒
        (fv1 (n'+v) e' ⇔ fv1 (n+v) e)`,
  recInduct clos_mtiTheory.collect_args_ind
  \\ rw[clos_mtiTheory.collect_args_def]
  \\ rw[fv1_thm]);

val intro_multi_fv1 = Q.store_thm("intro_multi_fv1",
  `∀max_app es. LIST_REL (λe1 e2. ∀v. fv1 v e1 ⇔ fv1 v e2) (intro_multi max_app es) es`,
  recInduct clos_mtiTheory.intro_multi_ind
  \\ rw[clos_mtiTheory.intro_multi_def, fv1_thm, clos_mtiTheory.intro_multi_length]
  \\ TRY ( pairarg_tac \\ fs[fv1_thm] )
  \\ TRY (
    qhdtm_x_assum`collect_apps`mp_tac
    \\ specl_args_of_then``collect_apps``(collect_apps_fv1)mp_tac
    \\ ntac 2 strip_tac \\ fs[] )
  \\ imp_res_tac collect_args_fv1
  \\ TRY (
    CHANGED_TAC(fs[EXISTS_MAP])
    \\ fs[UNCURRY, fv_exists, EXISTS_MEM, EXISTS_PROD, PULL_EXISTS]
    \\ rw[EQ_IMP_THM] \\ fs[]
    >- (
      Cases_on`collect_args max_app p_1 p_2` \\ fs[]
      \\ res_tac \\ rfs[]
      \\ imp_res_tac collect_args_fv1
      \\ disj1_tac
      \\ asm_exists_tac \\ fs[] )
    >- (
      disj1_tac
      \\ asm_exists_tac \\ fs[]
      \\ Cases_on`collect_args max_app p_1 p_2` \\ fs[]
      \\ res_tac \\ rfs[]
      \\ imp_res_tac collect_args_fv1 ))
  \\ fs[fv_exists, LIST_REL_EL_EQN, EXISTS_MEM, MEM_EL, PULL_EXISTS, clos_mtiTheory.intro_multi_length]
  \\ metis_tac[clos_mtiProofTheory.HD_intro_multi, fv1_def]);

val ksyntax_ok_intro_multi = Q.store_thm("ksyntax_ok_intro_multi",
  `clos_knownProof$syntax_ok es ⇒ clos_knownProof$syntax_ok (intro_multi max_app es)`,
  fs[clos_knownProofTheory.syntax_ok_def]
  \\ fs[GSYM clos_mtiProofTheory.intro_multi_preserves_esgc_free]
  \\ fs[clos_knownProofTheory.fv_max_def, fv_exists]
  \\ fs[EVERY_MEM, MEM_EL, PULL_EXISTS, clos_mtiTheory.intro_multi_length]
  \\ qspecl_then[`max_app`,`es`]strip_assume_tac intro_multi_fv1
  \\ fs[LIST_REL_EL_EQN]);

val ksyntax_ok_compile_mti = Q.store_thm("ksyntax_ok_compile_mti",
  `clos_knownProof$syntax_ok es ⇒
   clos_knownProof$syntax_ok (clos_mti$compile do_mti max_app es)`,
  Cases_on`do_mti` \\ rw[clos_mtiTheory.compile_def]
  \\ fs[ksyntax_ok_intro_multi]);

val compile_elist_globals = Q.store_thm("compile_elist_globals",
  `elist_globals (clos_mti$compile do_mti max_app es) = elist_globals es`,
  Cases_on`do_mti` \\ EVAL_TAC
  \\ rw[clos_mtiProofTheory.intro_multi_preserves_elist_globals]);

val compile_inc_uncurry = Q.store_thm("compile_inc_uncurry",
  `clos_mtiProof$compile_inc max_app p = (HD (intro_multi max_app [FST p]),[])`,
  Cases_on`p` \\ EVAL_TAC);

val kcompile_inc_uncurry = Q.store_thm("kcompile_inc_uncurry",
  `clos_knownProof$compile_inc c g p =
     (SND (known (reset_inline_factor c) [FST p] [] g),
      FST (HD (FST (known (reset_inline_factor c) [FST p] [] g))),
      SND p)`,
  Cases_on`p` \\ EVAL_TAC
  \\ pairarg_tac \\ simp[]);

val elist_globals_sing = Q.store_thm("elist_globals_sing",
  `elist_globals [x] = set_globals x`,
  rw[elist_globals_FOLDR]);

val set_globals_HD_intro_multi = Q.store_thm("set_globals_HD_intro_multi",
  `set_globals (HD (intro_multi x [y])) = set_globals y`,
  qspecl_then[`x`,`[y]`]mp_tac clos_mtiProofTheory.intro_multi_preserves_elist_globals
  \\ rw[]
  \\ rewrite_tac[Once(GSYM elist_globals_sing)]
  \\ rewrite_tac[clos_mtiProofTheory.HD_intro_multi]
  \\ fs[]);

val compile_common_semantics = Q.store_thm("compile_common_semantics",
  `closSem$semantics (ffi:'ffi ffi_state) c.max_app FEMPTY co1 (compile_inc c cc) es1 ≠ Fail ∧
   compile_common c es1 = (c', code2) ∧
   (c.do_mti ⇒ 1 ≤ c.max_app ∧ clos_mtiProof$syntax_ok es1 ∧ (∀n. clos_mtiProof$syntax_ok [FST(SND(co1 n))])) ∧
   (IS_SOME c.known_conf ⇒
     (THE c.known_conf).val_approx_spt = LN	∧
     FST (SND (FST (co1 0))) = SND
       (known (THE c.known_conf)
         (SND (renumber_code_locs_list (make_even (LENGTH es1 + c.next_loc)) (compile c.do_mti c.max_app es1)))
           [] LN)) ∧
   (¬contains_App_SOME c.max_app es1 ∧ clos_knownProof$syntax_ok es1 ∧
    BAG_ALL_DISTINCT (elist_globals es1) ∧
    (∀n. SND (SND (co1 n)) = [] ∧
     globals_approx_sgc_free (FST (SND (FST (co1 n)))) ∧
     BAG_ALL_DISTINCT (elist_globals (GENLIST (FST o SND o co1) n)) ∧
     BAG_DISJOINT (elist_globals es1) (elist_globals (GENLIST (FST o SND o co1) n)) ∧
     every_Fn_vs_NONE [FST(SND(co1 n))] ∧
     ¬contains_App_SOME c.max_app [FST(SND(co1 n))] ∧
     clos_knownProof$syntax_ok [FST(SND(co1 n))]))
   ⇒
   closSem$semantics ffi c.max_app (alist_to_fmap code2)
     (pure_co compile_inc o
       state_co (if c.do_call then compile_inc else CURRY I)
       (state_co
         (case c.known_conf of NONE => CURRY I | SOME kcfg => compile_inc kcfg)
           (state_co (ignore_table renumber_code_locs)
             ((if c.do_mti then pure_co (compile_inc c.max_app) else I) o co1))))
     cc ([Call None 0 c'.start []]) =
   closSem$semantics ffi c.max_app FEMPTY co1 (compile_inc c cc) es1`,
  simp[compile_common_def]
  \\ rpt(pairarg_tac \\ fs[])
  \\ qmatch_asmsub_rename_tac`renumber_code_locs_list _ _ = (k,_)`
  \\ qmatch_asmsub_abbrev_tac`renumber_code_locs_list n`
  \\ strip_tac \\ rveq
  \\ drule (GEN_ALL clos_mtiProofTheory.semantics_compile)
  \\ disch_then(qspec_then`c.do_mti`mp_tac) \\ fs[]
  \\ simp[Once compile_inc_def]
  \\ qmatch_goalsub_abbrev_tac`(_ ccc = _)`
  \\ disch_then(qspec_then`ccc`mp_tac) \\ fs[]
  \\ disch_then(assume_tac o SYM) \\ fs[]
  \\ qunabbrev_tac`ccc`
  \\ fs[compile_inc_def]
  \\ drule clos_numberProofTheory.semantics_number
  \\ fs[]
  \\ impl_tac
  >- (
    qx_gen_tac`m`
    \\ Cases_on`co1 m`
    \\ PairCases_on`r`
    \\ first_x_assum(qspec_then`m`mp_tac)
    \\ simp[]
    \\ rw[backendPropsTheory.pure_co_def, clos_mtiProofTheory.compile_inc_def] )
  \\ disch_then(assume_tac o SYM) \\ fs[]
  \\ drule (GEN_ALL clos_knownProofTheory.semantics_compile)
  \\ disch_then(qspec_then`kc`mp_tac)
  \\ disch_then(qspec_then`c.known_conf`mp_tac)
  \\ fs[]
  \\ qmatch_goalsub_abbrev_tac`state_cc _ cc0`
  \\ disch_then(qspec_then`cc0`mp_tac) \\ fs[]
  \\ impl_tac >- (
    strip_tac
    \\ simp[backendPropsTheory.SND_state_co, SND_SND_ignore_table,
           backendPropsTheory.FST_state_co,
           FST_SND_ignore_table]
    \\ reverse conj_tac
    >- (
      fs[IS_SOME_EXISTS] \\ fs[clos_knownTheory.compile_def]
      \\ pairarg_tac \\ fs[] \\ rveq \\ fs[]
      \\ qmatch_asmsub_abbrev_tac`renumber_code_locs_list n'`
      \\ `n' = n`
      by (
        unabbrev_all_tac
        \\ simp[make_even_def,EVEN_MOD2] )
      \\ fs[Abbr`n'`,Abbr`n`] \\ rfs[] \\ fs[]
      \\ rw[] )
    \\ match_mp_tac (GEN_ALL syntax_oracle_ok_renumber_code_locs)
    \\ asm_exists_tac \\ fs[]
    \\ conj_tac >- ( match_mp_tac ksyntax_ok_compile_mti \\ fs[] )
    \\ conj_tac
    >- (
      reverse(rw[])
      >- (
        fs[clos_knownProofTheory.co_every_Fn_vs_NONE_def]
        \\ qx_gen_tac`m`
        \\ rpt gen_tac \\ strip_tac
        \\ first_x_assum(qspec_then`m`mp_tac)
        \\ rw[] )
      \\ simp[clos_knownProofTheory.co_every_Fn_vs_NONE_def]
      \\ qx_gen_tac`m`
      \\ Cases_on`co1 m`
      \\ Cases_on`r`
      \\ simp[clos_mtiProofTheory.compile_inc_def]
      \\ first_x_assum(qspec_then`m`mp_tac)
      \\ simp[] )
    \\ conj_tac >- simp[compile_elist_globals]
    \\ qx_gen_tac`m`
    \\ conj_tac >- rw[]
    \\ conj_tac >- (
      rw[]
      \\ Cases_on(`SND (co1 m)`)
      \\ rw[clos_mtiProofTheory.compile_inc_def]
      \\ match_mp_tac ksyntax_ok_intro_multi
      \\ first_x_assum(qspec_then`m`mp_tac)
      \\ simp[] )
    \\ conj_tac >- rw[]
    \\ conj_tac
    >- (
      rw[]
      \\ fs[o_DEF, compile_inc_uncurry]
      \\ fs[elist_globals_FOLDR, MAP_GENLIST, o_DEF]
      \\ fs[set_globals_HD_intro_multi] )
    >- (
      rw[clos_mtiTheory.compile_def, clos_mtiProofTheory.intro_multi_preserves_elist_globals]
      \\ fs[o_DEF, compile_inc_uncurry]
      \\ fs[elist_globals_FOLDR, MAP_GENLIST, o_DEF]
      \\ fs[set_globals_HD_intro_multi] ))
  \\ disch_then(assume_tac o SYM) \\ fs[]
  \\ qmatch_assum_abbrev_tac`semantics ffi max_app FEMPTY co cc0 x <> Fail`
  \\ drule (GEN_ALL clos_callProofTheory.semantics_compile)
  \\ disch_then drule
  \\ disch_then(qspec_then`state_co (if c.do_call then compile_inc else CURRY I) co`mp_tac)
  \\ qunabbrev_tac`cc0`
  \\ qmatch_goalsub_abbrev_tac`state_cc _ cc0 = state_cc _ _`
  \\ disch_then(qspec_then`cc0`mp_tac)
  \\ impl_tac
  >- (
    fs[Abbr`cc0`, clos_callProofTheory.code_inv_def]
    \\ fs[Abbr`co`, backendPropsTheory.SND_state_co, backendPropsTheory.FST_state_co]
    \\ strip_tac
    \\ conj_tac
    >- (
      match_mp_tac (GEN_ALL kcompile_csyntax_ok)
      \\ goal_assum(first_assum o mp_then Any mp_tac)
      \\ reverse conj_tac
      >- fs[globals_approx_every_Fn_SOME_def,globals_approx_every_Fn_vs_NONE_def,lookup_def]
      \\ cheat (* push through clos_number *) )
    \\ qx_gen_tac`m`
    \\ TOP_CASE_TAC \\ fs[SND_SND_ignore_table] >- rw[]
    \\ simp[kcompile_inc_uncurry, SND_SND_ignore_table]
    \\ rw[] )
  \\ disch_then(assume_tac o SYM) \\ fs[]
  \\ fs[FUPDATE_LIST_alist_to_fmap]
  \\ drule clos_callProofTheory.compile_ALL_DISTINCT
  \\ impl_tac >- (
    imp_res_tac clos_knownProofTheory.compile_code_locs
    \\ qhdtm_x_assum`renumber_code_locs_list`mp_tac
    \\ specl_args_of_then``renumber_code_locs_list``clos_numberProofTheory.renumber_code_locs_list_distinct mp_tac
    \\ ntac 2 strip_tac \\ fs[]
    \\ imp_res_tac clos_knownProofTheory.is_subseq_ALL_DISTINCT)
  \\ strip_tac
  \\ fs[ALL_DISTINCT_alist_to_fmap_REVERSE]
  \\ fs[Abbr`cc0`]
  \\ qmatch_goalsub_abbrev_tac`chain_exps start xps`
  \\ drule chain_exps_semantics_call
  \\ impl_tac
  >- ( fs[backendPropsTheory.SND_state_co] \\ cheat (* distinct code locs? *))
  \\ strip_tac
  \\ qhdtm_x_assum`semantics`(assume_tac o SYM) \\ fs[]
  \\ full_simp_tac bool_ss [GSYM alist_to_fmap_APPEND]
  \\ drule clos_annotateProofTheory.semantics_annotate
  \\ impl_tac >- (
    fs[backendPropsTheory.SND_state_co]
    \\ cheat (* every_Fn_vs_NONE chain_exps and clos_callProofTheory.calls_preserves_every_Fn_vs_NONE *))
  \\ disch_then(strip_assume_tac o SYM) \\ fs[]
  \\ AP_TERM_TAC
  \\ EVAL_TAC);

val compile_prog_semantics = Q.store_thm("compile_prog_semantics",
  `semantics (ffi:'ffi ffi_state) max_app code1 co1 cc1 [Call None 0 start []] ≠ Fail ∧
   (∀name arity c.
     FLOOKUP code1 name = SOME (arity,c) ⇒
     ∃aux1 c2 aux2.
       compile_exps max_app [c] aux1 = ([c2],aux2) ∧
       lookup (name + num_stubs max_app) code2 = SOME (arity,c2) ∧
       code_installed aux2 code2) ∧
   clos_to_bvl$compile_prog max_app prog1 = prog2 ∧
   init_code code1 code2 max_app ∧
   FEVERY (λp. every_Fn_SOME [SND (SND p)]) code1 ∧
   FEVERY (λp. every_Fn_vs_SOME [SND (SND p)]) code1 ∧
   lookup nsm1 code2 = SOME (0, init_globals max_app (num_stubs max_app + start)) /\
   compile_oracle_inv max_app code1 cc1 co1 code2 cc2 co2 ∧
   code_installed prog2 code2
   ⇒
   bvlSem$semantics ffi code2 (co2 : num -> 'c # (num # num # bvl$exp) list) cc2 nsm1 =
   closSem$semantics ffi max_app code1 (co1 : num -> 'c # closLang$exp # (num # num # closLang$exp) list) cc1 [Call None 0 start []]`,
  rw[]
  \\ irule (GEN_ALL IMP_semantics_eq)
  \\ simp[]
  \\ qexists_tac`K (K (K (K (K (K (K (K T)))))))`
  \\ rw[eval_sim_def]
  \\ rw[bvlSemTheory.evaluate_def, bvlSemTheory.find_code_def, lookup_fromAList]
  \\ fs[closSemTheory.evaluate_def]
  \\ fs[pair_case_eq, CaseEq"option"] \\ rveq
  \\ fs[bool_case_eq]
  >- (
    fs[closSemTheory.initial_state_def]
    \\ qexists_tac`0` \\ simp[] )
  \\ rw[init_globals_def]
  \\ rw[bvlSemTheory.evaluate_def, bvlSemTheory.do_app_def]
  \\ fs[bvlSemTheory.dec_clock_def]
  \\ Q.ISPECL_THEN[`max_app`,`max_app`,`initial_state ffi code2 co2 cc2 kk with globals := [NONE]`]
        (mp_tac o Q.GEN`kk`)evaluate_init
  \\ simp[GSYM PULL_FORALL]
  \\ impl_tac
  >- ( simp[domain_lookup] \\ metis_tac[init_code_def] )
  \\ simp[]
  \\ disch_then kall_tac
  \\ simp[Once get_global_def]
  \\ simp[partial_app_label_table_loc_def]
  \\ simp[GSYM global_table_def]
  \\ simp[LUPDATE_def]
  \\ fs[EVAL``(initial_state ffi max_app code co cc k).code``]
  \\ fs[closSemTheory.find_code_def, CaseEq"option", CaseEq"prod"]
  \\ first_assum drule \\ strip_tac
  \\ simp[bvlSemTheory.find_code_def]
  \\ fs[EVAL``(initial_state ffi max_app code co cc k).clock``]
  \\ qpat_x_assum`(_ ,_) = _`(assume_tac o SYM)
  \\ drule (CONJUNCT1 compile_exps_correct |> SIMP_RULE std_ss [] |> INST_TYPE[gamma|->beta])
  \\ simp[closSemTheory.dec_clock_def]
  \\ disch_then drule
  \\ rveq
  \\ disch_then(qspec_then`[]`mp_tac o CONV_RULE SWAP_FORALL_CONV)
  \\ simp[env_rel_def]
  \\ fs[EVAL``(initial_state ffi max_app code co cc k).code``]
  \\ imp_res_tac FEVERY_FLOOKUP \\ fs[]
  \\ fs[EVAL``(initial_state ffi max_app code co cc k).clock``]
  \\ disch_then(qspec_then`initial_state ffi code2 co2 cc2 k with globals := [SOME (global_table max_app)]`mp_tac)
  \\ fs[EVAL``(initial_state ffi code co cc k).code``]
  \\ disch_then(qspec_then`FEMPTY`mp_tac)
  \\ impl_tac
  >- (
    fs[state_rel_def, closSemTheory.initial_state_def, bvlSemTheory.initial_state_def]
    \\ conj_tac >- EVAL_TAC
    \\ conj_tac >- EVAL_TAC
    \\ metis_tac[init_code_def])
  \\ strip_tac
  \\ qexists_tac`ck+1`
  \\ fs[]
  \\ fs[state_rel_def]
  \\ Cases_on`res1` \\ fs[]
  \\ Cases_on`e` \\ fs[]);

val compile_semantics = store_thm("compile_semantics",
  ``semantics (ffi:'ffi ffi_state) c.max_app FEMPTY co (compile_inc c cc) es ≠ Fail ∧
    compile c es = (c', prog)
    ⇒
    semantics ffi (fromAList prog) co2 cc2 c'.start =
    semantics ffi c.max_app FEMPTY co (compile_inc c cc) es`` |> inst[beta|->alpha],
  strip_tac
  \\ imp_res_tac compile_all_distinct_locs
  \\ fs[compile_def]
  \\ pairarg_tac \\ fs[] \\ rveq
  \\ DEP_REWRITE_TAC[fromAList_code_sort]
  \\ fs[ALL_DISTINCT_code_sort]
  \\ first_assum(mp_then (Pat`closSem$semantics`) mp_tac (GEN_ALL compile_common_semantics))
  \\ simp[]
  \\ impl_tac >- cheat (* add assumptions, after proving cheats in compile_common_semantics *)
  \\ disch_then(assume_tac o SYM) \\ fs[]
  \\ irule compile_prog_semantics
  \\ simp[lookup_fromAList]
  \\ `c''.max_app = c.max_app` by cheat (* compile_common max_app *)
  \\ conj_tac >- cheat (* prove ALOOKUP_compile_common *)
  \\ conj_tac >- ( irule ALOOKUP_ALL_DISTINCT_MEM \\ fs[] )
  \\ conj_tac >- cheat (* syntax_ok for compile_common *)
  \\ conj_tac >- cheat (* syntax_ok for compile_common *)
  \\ conj_tac
  >- (
    qexists_tac`prog'`
    \\ irule code_installed_fromAList
    \\ fs[]
    \\ fs[IS_SUBLIST_APPEND]
    \\ CONV_TAC SWAP_EXISTS_CONV
    \\ qexists_tac`[]` \\ fs[] )
  \\ conj_tac
  >- (
    rw[init_code_def,fromAList_append,lookup_union]
    \\ rw[lookup_fromAList, ALOOKUP_toAList]
    \\ TRY(`0 < c.max_app` by fs[])
    \\ imp_res_tac init_code_ok \\ fs[]
    \\ cheat (* ALOOKUP_compile_common *) )
  \\ cheat (* oracle syntax ok *));

(*
val () = temp_overload_on("acompile",``clos_annotate$compile``);
val () = temp_overload_on("msyntax_ok",``clos_mtiProof$syntax_ok``);
val () = temp_overload_on("ksyntax_ok",``clos_knownProof$syntax_ok``);
val () = temp_overload_on("csyntax_ok",``clos_callProof$syntax_ok``);

val compile_semantics = Q.store_thm("compile_semantics",
  `¬contains_App_SOME c.max_app [e] ∧ every_Fn_vs_NONE [e] ∧ esgc_free e ∧
   BAG_ALL_DISTINCT (set_globals e) ∧
   compile c e = (c',p) ∧
   0 < c.max_app ∧
   clos_init c.max_app (s:'ffi closSem$state) ∧
   semantics [] s [e] ≠ Fail
   ⇒
   semantics s.ffi (fromAList p) (anything:num->'c#(num#num#bvl$exp)list) youwant c'.start =
   semantics [] s [e]`,
  rpt strip_tac >> qpat_x_assum `closSem$semantics _ _ _ ≠ Fail` mp_tac >>
  simp[closSemTheory.semantics_def] >>
  IF_CASES_TAC >> full_simp_tac(srw_ss())[] >>
  DEEP_INTRO_TAC some_intro >> simp[] >>
  conj_tac >- (
    gen_tac >> strip_tac >> rveq >> full_simp_tac(srw_ss())[] >>
    simp[bvlSemTheory.semantics_def] >>
    IF_CASES_TAC >> full_simp_tac(srw_ss())[] >- (
      first_assum(subterm (fn tm => Cases_on`^(assert(has_pair_type)tm)`) o concl) >>
      drule bvlPropsTheory.evaluate_add_clock >>
      CONV_TAC (LAND_CONV (SIMP_CONV bool_ss [GSYM PULL_FORALL])) >>
      impl_tac >- full_simp_tac(srw_ss())[] >> strip_tac >>
      qhdtm_x_assum`closSem$evaluate`kall_tac >>
      last_assum(qspec_then`k'`mp_tac)>>
      (fn g => subterm (fn tm => Cases_on`^(assert(has_pair_type)tm)`) (#2 g) g) >>
      drule (GEN_ALL compile_evaluate) >> fs[] >>
      disch_then drule >>
      simp[RIGHT_FORALL_IMP_THM,GSYM AND_IMP_INTRO] >>
      impl_tac >- ( strip_tac >> PROVE_TAC[FST] ) >>
      disch_then(qspecl_then[`youwant`,`anything`]strip_assume_tac) >>
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
      qspecl_then[`exps`,`[]`,`ss`]mp_tac (INST_TYPE[alpha|->gamma,beta|->``:'ffi``]bvlPropsTheory.evaluate_add_to_clock_io_events_mono) >>
      simp[bvlPropsTheory.inc_clock_def,Abbr`ss`,Abbr`bs`] >>
      ntac 2 strip_tac >>
      Cases_on`s'.ffi.final_event`>>full_simp_tac(srw_ss())[] >- (
        Cases_on`s''.ffi.final_event`>>full_simp_tac(srw_ss())[]>-(
          unabbrev_all_tac >>
          drule (GEN_ALL compile_evaluate) >> fs[] >>
          rpt(disch_then drule) >>
          disch_then(qspecl_then[`youwant`,`anything`]strip_assume_tac) >>
          drule bvlPropsTheory.evaluate_add_clock >>
          simp[GSYM PULL_FORALL] >>
          impl_tac >- (
            PROVE_TAC[FST,full_result_rel_abort] ) >>
          disch_then(qspec_then`k'`mp_tac)>>simp[bvlPropsTheory.inc_clock_def]>>
          qhdtm_x_assum`bvlSem$evaluate`mp_tac >>
          drule bvlPropsTheory.evaluate_add_clock >>
          simp[] >>
          disch_then(qspec_then`ck+k`mp_tac)>>simp[bvlPropsTheory.inc_clock_def]>>
          ntac 3 strip_tac >> rveq >> full_simp_tac(srw_ss())[] >>
          full_simp_tac(srw_ss())[state_component_equality] >>
          metis_tac[full_result_rel_ffi]) >>
        first_x_assum(qspec_then`k'`strip_assume_tac) >>
        first_assum(subterm (fn tm => Cases_on`^(assert has_pair_type tm)`) o concl) >> full_simp_tac(srw_ss())[] >>
        unabbrev_all_tac >>
        drule (GEN_ALL compile_evaluate) >>
        CONV_TAC(LAND_CONV(SIMP_CONV(srw_ss())[RIGHT_FORALL_IMP_THM,GSYM AND_IMP_INTRO])) >>
        disch_then drule >>
        CONV_TAC(LAND_CONV(SIMP_CONV(srw_ss())[RIGHT_FORALL_IMP_THM,GSYM AND_IMP_INTRO])) >>
        REWRITE_TAC[AND_IMP_INTRO] >>
        impl_tac >- ( strip_tac >> PROVE_TAC[FST] ) >>
        CONV_TAC(LAND_CONV(SIMP_CONV(srw_ss())[RIGHT_FORALL_IMP_THM,GSYM AND_IMP_INTRO])) >>
        rpt (disch_then drule)>>
        disch_then(qspecl_then[`youwant`,`anything`]mp_tac) >>
        CONV_TAC(LAND_CONV(SIMP_CONV(srw_ss())[LET_THM])) >> strip_tac >>
        qhdtm_x_assum`closSem$evaluate`mp_tac >>
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
      disch_then drule >>
      simp[RIGHT_FORALL_IMP_THM,GSYM AND_IMP_INTRO] >>
      impl_keep_tac >- ( strip_tac >> PROVE_TAC[FST] ) >>
<<<<<<< HEAD
      rpt(disch_then drule) >>
      disch_then(qspecl_then[`youwant`,`anything`]strip_assume_tac) >>
      rveq >>
=======
      strip_tac >> rveq >>
>>>>>>> origin/master
      fsrw_tac[ARITH_ss][] >>
      reverse(Cases_on`s''.ffi.final_event`)>>full_simp_tac(srw_ss())[]>>rev_full_simp_tac(srw_ss())[]>- (
        first_x_assum(qspec_then`ck+k`mp_tac) >>
        fsrw_tac[ARITH_ss][ADD1] >> strip_tac >>
        full_simp_tac(srw_ss())[state_rel_def] >> rev_full_simp_tac(srw_ss())[] >>
        imp_res_tac full_result_rel_ffi >>
        full_simp_tac(srw_ss())[] >> rev_full_simp_tac(srw_ss())[]) >>
      qhdtm_x_assum`bvlSem$evaluate`mp_tac >>
      drule bvlPropsTheory.evaluate_add_clock >>
      CONV_TAC (LAND_CONV (SIMP_CONV bool_ss [GSYM PULL_FORALL])) >>
      impl_tac >- (strip_tac >> full_simp_tac(srw_ss())[]) >>
      disch_then(qspec_then`ck+k`mp_tac)>>simp[bvlPropsTheory.inc_clock_def] >>
      fsrw_tac[ARITH_ss][ADD1] >>
      strip_tac >> spose_not_then strip_assume_tac >> rveq >>
      fsrw_tac[ARITH_ss][state_rel_def] >> rev_full_simp_tac(srw_ss())[] >>
      imp_res_tac full_result_rel_ffi >> full_simp_tac(srw_ss())[] >> rev_full_simp_tac(srw_ss())[]) >>
    simp_tac(srw_ss()++QUANT_INST_ss[pair_default_qp])[] >>
    drule (GEN_ALL compile_evaluate) >> fs[] >>
    simp[RIGHT_FORALL_IMP_THM,GSYM AND_IMP_INTRO] >>
    disch_then drule >>
    simp[RIGHT_FORALL_IMP_THM,GSYM AND_IMP_INTRO] >>
    impl_keep_tac >- ( strip_tac >> PROVE_TAC[FST] ) >>
    rpt(disch_then drule) >>
    disch_then(qspecl_then[`youwant`,`anything`]strip_assume_tac) >>
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
    map_every qexists_tac[`youwant`,`anything`] >>
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
    map_every qexists_tac[`youwant`,`anything`] >>
    spose_not_then strip_assume_tac >>
    last_x_assum(qspec_then`k`strip_assume_tac) >> rev_full_simp_tac(srw_ss())[] >>
    reverse(Cases_on`s'.ffi.final_event`)>>full_simp_tac(srw_ss())[] >- (
      qhdtm_x_assum`bvlSem$evaluate`mp_tac >>
      qmatch_assum_abbrev_tac`bvlSem$evaluate (exps,[],ss) = _` >>
      qspecl_then[`exps`,`[]`,`ss`]mp_tac (INST_TYPE[alpha|->gamma,beta|->``:'ffi``]bvlPropsTheory.evaluate_add_to_clock_io_events_mono) >>
      disch_then(qspec_then`ck`mp_tac)>>
      fsrw_tac[ARITH_ss][ADD1,bvlPropsTheory.inc_clock_def,Abbr`ss`] >>
      rpt strip_tac >> full_simp_tac(srw_ss())[] >>
      imp_res_tac full_result_rel_ffi >> full_simp_tac(srw_ss())[]) >>
    qhdtm_x_assum`bvlSem$evaluate`mp_tac >>
    drule bvlPropsTheory.evaluate_add_clock >>
    CONV_TAC (LAND_CONV (SIMP_CONV bool_ss [GSYM PULL_FORALL])) >>
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
   |> Q.SPECL[`youwant`,`s`,`k`,`e`,`c`,`anything`] |> mp_tac) >>
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
*)

val _ = export_theory();
